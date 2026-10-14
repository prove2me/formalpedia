-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:05.905281+00:00
-- url     : https://prove2.me/submissions/916dfc45-45d9-4a95-bf62-37f0d5536d30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 366007194 ≤ n < 366187050 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 366008444 1250 366007194 366007199
    0x603180304120b010b1213050c09040305070203060a0b0a06030f020c0106030305070b07030903020c0d0f02131b0c0215030405150901140a1a1507060e012c0d0c0309 72
    0x40800141004008246050b4403160550030007941000040c0c202c4080031108120304e60000074500c0700c0607001421318148501c0100341d42016400c000f03c4500c00e5600c0350f407810030b010516031b000c1c001e840458003c500b500e0360b030f888014000c0d0032a94140d40300c0d034014500b43d0003048068082d17407054140234565000940b900c05c805e00410700b100c246800485c0450f0020078100240304c0d03084c07804c603031068141c18101300900190310082d5691600011452080c800855503008102e44202144107282e4090006121604986091405481c59492901d2500e030701c2080340380c165221b041116602d40c1c018084c4070b122312b180c091920240c2d200500c00d40f2684038076500902a0120180000e11668880c00005441d0300b0301010444052006004419001d04000056142140c0308030200c0407054125580c021000796045105214007880038003a1030940703005451a0b8295040d0400b44800780d100c185407036900e4000508070490280c0000d815082c6d4055081c19940307a0046610041e034a02074240410b64a5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 366009694 1250 366008444 366008491
    0x70809011103010f09063f0b090d0315030c050d0302010204120c08010605040519051801021605010608030a090e0705040b07050f0c04110a050f0c0a031701051504050603 74
    0x20b00a070b0203440c50308041c0c0c40404c060626132080741c1c0a40004003981e500340014818003c8882c00301c0c15001c159854030011003040205050440c8082a802480c0540c035140c481c035280d40b100200700c4c0600c0440c3c01c00c0c0d000454080140c2d50402030300d500044140090b802c020030b110407500e60b04011419507500304404200004c1b090000305105218210202540741459806030a4605a0340201d028500300700512454a5801c0f030103e5001d9201100011248d0ba01314600c8000c81d8480c01c020065440010100b00807901c20108041850080000740305603541c1e141299928490307000510700245d4502420321076181c607001000c0d0401b100340742c920306040d222003504000c0c1e448940101e415900c840341984d040d0360144044406100c048500300300c0c10400c0c0101e60240e00c9204610420408001148800b0354600800d0b1a520050301007251107070150703850090003850b40101490440501c01d00002514641a0031a5485c2c1c031120b6625800c2a291000303101440e0030240203402c001104155a00040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 366010944 1250 366009694 366009697
    0x80f0a02040f090b0a211407050105040302040b04200c010615050a180f0f080d0f020c13182603060a0e270d0306060504141011030a090501110d02060708090111 70
    0xa40c80c0003281b14402d0312443d0031414185013101c1031002e0b4101110410090780c1010a59003100c0c0c06480100e4210681e02c0050024a080916540c40d00c40240d844079801c2c1ca0100903040300d688800081142a0315075545101c88511000c1d001c0010b20200202e240d128841e072140400e2216001030b44224680321050724400e180f00da00045010088a8010000d00000300103042e0305250f5070804042002ca154002500c13443d440c02e0030b41c01080a2050342c441c480c8950303c0140450740f130302200c0c0d44140d090b20348002c0d440070310040c40d04084000140394400c41608070489005080007808265400d140516169583d10010f1400c2404200a851107501d60740c001869017040288501920501011040c05070480305d564000e00c0c100841804103102c1c130321041d60003450100c1c0442d0b060008080d41c080c02c40d22401c40703040a60301c0e4000407440a08007504202c00e541524003d80310604049840d0703040547e00c08480c2000c1c0e0040e030101c804206040d0048848582003521040081100c0a105007078940300e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 366012194 1250 366010944 366010979
    0x3040909060c080a090f02090705091905040608030301061b03031b09030b090c0603041407080d020304030c0501031802040903021015080607050c0303190204090903080f0a02040f090b0a 81
    0x350380c1c4403120b03020000e900102d01a07010001820400400ca81c64444039059004407100a0050081d0804582c95234040e40c280c03081c01c000205156181c501c020b807030441480142c0b09040c007031424510f000c2040c25001c01501c0c1a1146aa1501d4060380004219086004036a805400b0f066440900070a0322382046661803540d012503c3d03807c11036255181025030389500500280880c0c100524002c259910541100c1d080b54000c0d0a0b0b01d0f01019280741581003540e95070110303070345101e9030804106e00340d0040040c0040b20701417040e50b400640d54100650540304500a0054803004840c40310300145425480140d64900920488180b03480200c260300450708490070b04c1c0300002140381d003000300d4803007040b4842d840405864050304010a034a030075541c030b010260040c6816440715030000505200307641a1002003020200c184004416420301424801040c0c03507030301c1c40002e2000011a11103031070007103a04480910700f03107440140c0361180304001010f400b000b140e800f074402400025640000e090300b029 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 366013444 1250 366012194 366012203
    0x2100908070804061110020a0c0809031504120806030a0f08070303060902031003200a0509180102130603180b070e12060a1407020106050d2a0f05120307120c0503040909 74
    0x4070103507845c0b070003031600300d071041c8004090740100b00d80e82c40a41d002e03600440310765010400f04c0c2c079800381c000000e080078888200800003e8540c1c040200388400b0701d001d000340700000c1c0c4510701c3e02c3d20b440081c181c6400440740081c1c16690601c20010001d4010002000294081d150000f01252164028406d9070300c00c0c0d428103410455540305009000080b0362000039201c0e00301e0034518058500e00801d0301000c2d207200c3c0300e205110080000b442c80c0d5a000b203071000000004021582d5400d010700c3d02c00e5907000c9014903c00070340307440203501c1d03503905251400c03a20300e400110314081a91542011540f180c549584103030000b689160890f176001080210794001c0300f6000000c03408001a2041d4054510010000b00440e07040c18000c04c2030780c540ba10b00c040065040010813554851401340201d20403100400303081d500115220004d5650040c9035004113030307842259042d048245c20038101e503690040d400003030010000c040a46194900583c001c405e014490810740307003007658500042044590001c410703103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 366014694 1250 366013444 366013457
    0x150c030c03060b07020a030204020a05041203081014031b0102010b060f070515011d0a0905030a0e0306011a3106050310050409030804201c061b0210090807080406 71
    0xd10054150144030040e00103520040d05000464001500448447c400a40600d03800030702c03416000c1c45030045401421507040b02c80724803c800c0c40c0040c00c0d070342c0171128640d60343c24041300440c41844461032030425000007002060013000b84410301c0c01c20403c007400307281950341e10202c104090f2070310720180180b900400001034070f8980c142401410919a4400c40d40100c603a4801031240702c180c0591502e52030218900e03900542d503a03c01d040014010a84e02500034440460214500c3e079100c4c4000288240980c00d03036049980e11440f51086000210754800700d43c40500c8a010703c5103031540b00400100840070b500010010440c9a41001d00ad01d0308580c001400000400110401c6449110700402007035408000d905180e44005120f5180508000c2920022181003510400c0c2c00300214403010000780420002c0c00751032f80f1205102c024400c210b03045030400c40d0b4032030341c4441ca4100e040d04200c2c0e50050325480c80346007000790040c006048103c40440090040b10b0100700303114040c10180c0640d80300c69 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 366015944 1250 366014694 366014711
    0x607110c1810050909070618270605060903150402060f0309060a0b0315040b070c02090702030c12070c15050c071710330302040f050610090b16150c03 66
    0x542035010301d403c000d01820641044c400700031300001c0e11404488051403c844010b51021499080c0703081540440b041311007801d0008180c1c00c44410558808104910410141e42d507081401041d018900d45503615411160840c1001d43c0400d04081d44144024465840d00c80c400b5045003440e0410f50381d903030322030303216408004070440075103c0c4200402c022002000120804000c0c0342c450724004000401c01032281021583c0e03107002e041c501604a900400001a601d04000001e5994102140c03c141a2080003045032051044130100c80d2401c0c1c004414040080c00e00e025170000c5100e10070751700c003000f4080044200303c6505011000250000d07142c1c03900405560040c0728688109001c40c542450710344141d01c11108814a81e101ca0310240400010840816180100040440e0b500180d000303400e05c2c400e04540c00c00c5901c400d100b500101c52140d2002e290000442d001e81c40340c022040502010080c204400180c000c02c0b0202603c0355919000074207a41c82c08400f178441126126010980381c0c01d09 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 366017194 1250 366015944 366015961
    0x403050301031211100f020c010e03030a0c0305011404180609061b020f0705010e040204030506130b130305041806050d050a020306090c130b04060b280305090607110c18 74
    0xc44154214940000794031054101c240c0c80340c2a41492001243d0f603180c0c0304c4400c1d03605805844040d08e240c0001c001c0b100c15503080e641c0341c1c0d004a0300507070b0b40c0e480d000100c0940b030b000384541070603076040c100c00982400140d407c1c00000e100000304403592404000380c4c41c2c0043c58900841e003e0030f00ca00b60105a2401c5440911980000c40d5240d50a42d0460500742582d110300064400403907500340381001544504801260003842240c0000d0034034001d4100304681503544100940450b407040280400c60703034903440702e41d01d48880c480000707001500410081150700c0043d400000d4000420400181d0540c0e81d1000501c0740031240e4040324903400441c0e551056250501440b6804002c00c405026034200b03500002d030b1001c8030b440c00585070f260350701c0406019445990140d8080d010b800001540c5110285091804c052042c00d0342841032000344101009a200c0d01a090180242400802e11511081c609a5a407110a000040c2520800040b150103a40b082c1c0c0e46051046050400405810001e01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 366018444 1250 366017194 366017213
    0x616020d050304150503070503070c0c170c0f0f1003020a050d09050c01020607020610050904080c010c110d0e0901030b150a0b0a030518070e090f01050711160b090d02130203040305030103 82
    0xb082c1c02408170a00420403941c2d04981200e610080618064042107054604028040580c1e000300b13288025440380c400040c0720000e500f024602c8226000b0740b0f2084a00c040110142c41c0099181e0000c04000c401c3c82e400e4081c0e0081c01309072130142855414007070041150011608040fa042d40c4580c0290702c6024a5601070254980000e01c61001e40710030714050b4604c00503503009115042c005d0481c0c000140500c4a10380985040c940001c000f07004005c90440c00401c3d2038082804500a40206400218517a015940b203084a00015141684a83c83c60311002d20a010090032804d800141542198580e50350a00c000080e14101c1092600ea518418008045800060013806154242007003aa050640090341f58204c030401e4260403d1552420000703802c01020140c000c21644c00c01d001e00078115000f1192030084001d441c1201e8441c2e24260225510400c1441468103244041000303020302c1c204500002212400500807251201103280e9180480c0c0c02142d05030300241d404070050082090142 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 366019694 1250 366018444 366018479
    0x31214010f12030c0c060306061b050607110c0409150e06090a0f030221090915011d300f0d05030a0506042a031b0507020616020d050304 60
    0x1241528a9070400040901045140c014002c4030b9100700c2d482070415100d500c80000460340017480340113880d07540d2406030203081d0f2070003500d0201d9100003000c3c400ea00c1d03200e001f507036090700714004100f90f03100c16205841740c62502030603c1d8240945800303aa0303a0789403402540030366482009500301040388499150304903800f04003080c201d90040010701040c98000500c0c0001e1681080051888401c0ca207000d81c50302a080c1d095114a42e01c101c04070116682d0400540314540055402c607415690f1000303000800300d44911014041070820001006408080940011015024008250f06001c01ca0511031086000007031401904c011418200000f0040c0100f220700704041e40141994040d020025099000007802c2010703440e9a0703000100351396a16002004020038120081d20018804a202e074401c0d40280d000d14040f0703081071013100d0361008111404203811a46c1d47c8071810180507a007045880d611003d8190040e071005c0ea02500982e07551603103110f80300e2190008542d105d14040c0c007440c0009110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 366020944 1250 366019694 366019721
    0x3010911090703020a05120c071a04150204060816030227120607050d1806050c19080105030d1101060f0b04140d030503040b0403140a020c0405010806010b070305030a020c03070312 79
    0x510000e80c1041c0c002c0156040c7c0140c894001045940d07100d0b01003038901420034040d01282241c2c500f44042c00742076041c180110b0042a030b501c40400c07841d6491040c0e1086e031280800240d13801e8005680940c41544101143d522813501516000450144200c0c06030075101c0441c071910b05204e81a00c0d413800c108a0300b01070300420040d0205140210014010b03000b20501403134041e4980191002c0001d040100e404034070303031000f8200b095003081c0506141c0c68211494500c5500790052a41e4806405940c000c4d040b10030003402040f40100b40031089a0083c002507403400346640b1410046410600c0b00400c01c0600003006402c1e480b60300d8200043c1e00e402d44a48000e00814088960300040381e40300c41201e034800c1d00856a80a252038620f0f046804103642e41181e03031071a1010448403021a404288100074003c129401d02169889003e400d0f1104820b02c19000500e90030084140040c1c001c0018640c4038141c400300605289080c1034450556000c00800c40c00590604c4400009081511038018190340e0f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 366022194 1250 366020944 366020947
    0x2060d060e100e010605030712110324090c07050307061a03120a0815010203070b0103140c0f1f1b060501032001090501050c010f0e0313150f1d0301091109070302 71
    0x200402c02c840010f060150404010002000544883c0900d2032480e01003d410400c01030301c000700803000955001600d5258841480c0c2010a500311050160f01c0640f03c0001e10311403042e00d0351589601140c0c0300702c40880340d500051000d0800301d06184104240e060f01c400c2840401003181c03003007508285928600c01c144034030600c842c11205511550b01d40c0d200a074410001920264400180e1550085c603900800124001d0000301c10000c1e03101440c0100341d0340c441128000c0c2004020414084c002c040e9540d003002400c01d004610220704002d540000c0c085081041c02c140c0d03070000c5050300b4800e049055410039265001041000240d9494149209003200404000781d021030008187d10307024170406042080100d0004000d450030b6000c0507800740c00103000c0000c108040e800035100e8221948164641440010001d00d44400a88841240c410356884400d80c92204000359440e0080501e41c0c4903d0894440100041e01c00b40f08041078580560810516a01c0080411910242c01058441003600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 366023444 1250 366022194 366022199
    0x702060f0c0304060617010b041d03120a022106030601050409052109060d091505100e250809070f050a030b150a0f0815160302030a0902060d060e10 65
    0x80300d4000c190426000c04146a40362518102007025148a400843e074076100d03042c0030740f040901580190446c007016182844a106100551440695400f54140312078000300450140e0101e2014001d5110b088034800508000485151510035415840100091440c0b0801d121081c0350400c03032280104000c5405000c3c1c0542da075a81600c4042078107a00d01043c4000c80d1203104d030010030094030a0148040d054030707119412900d5901c050003d0800a1b2a002006200003660a8050050f83c0c42481003500c000c00c568504090707900c8043c0000c000710030f12668815110708855400110b03412060459403802c40a0403e40a4141040c869070320824644201c2d507010403a9440d451a803004070707500040400850755409130045400a24581342c44d0f031080440c1030105600b00d03155068420790b0101000c40e081c16003104070f03041c83ea400a032000b5a80040413584a1000c0340309070000d65000fa4242c20200e0340c4611a03000c0354460700510089607405480300000d0044500079100545c1c0125040e262034034182c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 366024694 1250 366023444 366023461
    0x1111b0a02060909060a030b0718090501050a0513060801060905041217190e06090322050f13150807060f020109111018080102030709050301090b0601030c030b18010e070206 76
    0x4103030f4032124010780301103001941c680d40e8190600000c5401001f008404c1c50a039070001c0441e0408607100050201c092400b00b440003141c0300d414143c540c060001c2c40301504010800c00250f200381c0d541c42c50640c8411011640001c2800f902009141428000c5000c1c181407030500e41d4902ea403910801000300c03038407019440300000e640e003540000103d144c860000e00c0303006040c80945504c004440c1988a1002800f0004400100601420f510b440e1781c00c60b00c24400a01000049052050329070101e1069907504151a005000048050410b0b03000a000c1c01e040d81e045a00c1c03001503100441c641c20075803040000a80004420100720b40c54802082121026558566118140e01e07025001d445440588480c0c540034104c075004106180b942d800c03010b9a40c1141c02d020754022200400065414400054107040500608506070341c011569030451f910301c00118010100f41140b0410582c84000c9890141c80b0080440d980015400b0740f0891503042009051101c0c40c05046c00046510002c10003c254 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 366025944 1250 366024694 366024697
    0x40e0714070b0408090a080f030a02070f030b240907030c02061303090911090913062d2a02030909010608060303041401030b040c080906010f0807052101111b0a0206 72
    0x69004400586840d04400424042a9143c07c03446c614440c800036001480e8000000d400007482c0c90b801c0310842034403242c00301c6071703480c079448000c0400c40c968000c01c80034061183d00c000ba0345290032a442c0005120300020740d44c1c800c1500d041c00031a680e4a91a80250b1741844056800044180d00040d400c1041d03900910343d0001f0300c508811705071380b0f0a21303c2019840c04102d41d620f90005210003010b040203401410242101c0c042200e940e85440026001c181040c2100d1171038166404000c000950984d0b00100034202540c1c0e81544202c0340a8443c81034002c0303507001c0340c8000c05d40d8011511407801c0b07000d01040c0c06068100400b40206603041061640d0000200c909883c5ca0315a03000508000c6001030b0090086131465981c40390511022880907540941200d210392800012180c2d141da030389041d6843d004541c0507048080d00b060105110700d003050040a40009014007010600c00620503003242100e46803d0101404000041c0c10680343c44c00400100d01b942100c405032a03140c0d07055000a045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 366027194 1250 366025944 366025951
    0xb0c03090f07210501020403020303070c08070609050f04051308042607050a030f031701032009090303061512010303050a14040f090507170403020c03011d0a1103030708040e0714070b 80
    0x1c0d24903c41003000b001b0f40649000319400b0741203a8179030b60f051405c3d15080d0418051110188a111000150703503205050703c40841d1009405041091036017020302007d4040144100850b480005c0c0c0240052944001003001348074540550703000c5042c0c2045c569102c1c1f1000382800a503444804288610754410951000300c9a00c0703000f42d181c5400c545001d0340c02c0601c1d6154450041d802c00000014810a9000b104502413811485036a484060040000b003150130b0f1101c1c4c80b507034400c1c8001540341c20f256101061b4000318009840c2080f0014615003001c00d403d820403030002c4c41c08603555003495003110b8091041000b4500e054105820070040e031038050710074840d200140e52030300d000c40c1160b80124040d420301c003499200f0048174507240c280a5a2280001c070824007039880c00324001d030341c4054860121010310884001e04114030321074640440c04141d0a065603854042000300100180110004100414400300c0e40505450305070340240400c00a2401c1c040324110410001002800040b01e442c0d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 366028444 1250 366027194 366027239
    0xd0e030c0a0e0109021c09030f120c09050f040e01092009011d13050a060603020a05191211090103050a030909050115080c0d1e1d1009050a0b0c03090f07 67
    0x6c0b9800d56402d142c0c4548503c01c00c146d1400c0c03801c40444189541702220302411a480d4070381304522805015500100d0b01045801d000140b0b220a0610207407a0400500c00c40d440d000b000803070300354040e590b02030844207150022555038200807558144079603c0400f407801c44100b1203240c640e540c035114540301204011140d50240d0191700000491711440e050200050039040022039030b0819880c54601d0080c05030f400700741e01c107001080000642d860240f404100d40c00881001d920820726118540d15000c2040200300e92004e080160814142c8880c440107000314000d50042180c01c070780341000303444030616400020107981408014080510390062100f08007240345018006681c4a01c0a22001e018210401d070b911418441025404540401a0b0304491030002c0708202099452481e43c84414404251541039001074944d81c04644050b80482501c900450580c0e182c4807103076942071030320b02007120384408401700482070008206040125030054040c5500a1283d141071000071468400c14041041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 366029694 1250 366028444 366028447
    0x41a27041509081b0f03090d0b06030c12030d0b150301050f210c1302090d020d080d0f0e011803091401090807240306060e01200d0e030c0a0e010902 65
    0xa281c180194080d660030340c1c014903a5030700c5002d20b0b48121300080c403a0052440c3c91003011440042000048100d03138860740001c10b80c032491407555441c820000c000410055050060100c28840c54075180e000b166914006409150380d00c0c1410b0608084071446000c19000300c40302c40300303480041c0f000300c100c03815500212a445892000e403000550000400d034100c3c40d2f600900c0045e284081070004640baa0410125034146a01d10309071204001c174011010706c1c943c442c0f44c0600380e4025080542a02e95030034040d950707251410030340d160714109607040b0412004415607528121940c0031020300c40c0200014101d900c2e03e41d1101c032518020203051080c01014071400f0000c50001e40381e8000d8031100700a0190740240c4901c40da407071421072910020071402e46240c02c00025080b403a24030910899040c1e900984074030036005c1d1140300440e0200070340c890780301180b09159200c10448400708001400d41300b082e07540700d9550350b0b19010b01d41000c41400d0300c0c45c0580742c020024402844030710f01e1241999180b84005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 366030944 1250 366029694 366029723
    0x30c0b0c010f0e0f0d080603061b0705030c0714060702030604060c0e09010f03030e0312040b0d1d070906140108010302060901031b0f02070f08030711010e041a2704 72
    0x3140100440d0b801485001c3c60062212081c0101191100b0802c128105035400c4403100e100603510144225401c0303074103030000c1c030014180a4250303030b2022402080d00f1036142850360341d589841c82d6900141e12400343ea403020b6004c00c00c4c0340070010010020102aa1480d04103032042d808641d0360390780030304018412070700d07016071840700c0c2e00c100103803124040c00410020310307540d413507030184819050741c0800d03000911440b48520b1641030004484000d45203410392a07181624268468030300b5000341382400300b420745a03440300c0089490301d4600c100c410415005080714034904011a0120740c40340d4080c0c141040e0700603c40040b81c0e0440080350450f0b805854a56643c06031000480c020101300d01e0240010044120030303401d180c0e000751800c40d071030b0003038085070050303619440501c694012501c250f400d070b94420414000041d4105900100001042c14209600c8840200190a650084001c0320044403000070411092820705ca03808030303644e0807422604416030709030020307040100d005101a040340040041e2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 366032194 1250 366030944 366030967
    0x201110c06160b0606030906043003140109061409042603040303050601050324130c020c0a05040603030f050309030f0a050705370302162706030c0b 65
    0x300e408004008080c607507940401150000d204141c0350055a1008031400014090704103501100d0040d8981c4006040940e00d5580300c601c0307400134030482c807010340221103440b80c01d4242c110940d18864558801080c825551120400c8413281680518542420321408110f000c61429026102c01c60690f84520141c0c2e99042038544440302c03400422202100f80c800c0d544d01a03a06024500452013a036041c010b03a11140c00444140c0010b41d111003c0d00658110a045000d200051214210014011201ea000b50103285000c44c2c03002d80750400940c001e000707440e01c9850300d043c008014060807142041501e040d510014036500381166840140003000000c1000e1840c03c2080e40c40341e015043d8030aa50b15080c41c070041c6140c000354411101d41c8241c00a418048000201c3d14845654400302010b0300400540c030244400c0c0420400d9095010759001c000a00e29205842c00192040410b1035142840c91540c40f849d660700c00e0019980d0341d182030300038400281c0758203030141258800d121068a65411001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 366033444 1250 366032194 366032203
    0x150916050f0c03070b0405061806010b0c0c0d1202150f0c13080d0e04050a02031b1b010e0706020f1507050d140a0506150405180a110301120c050418020111 68
    0x40070b50301c80420301c40c0c01c10413000750345849540716001395282a200c520180c00303c02e40d0072840c030316503401c1700b0014081c2c40701071800f0b08203280200040360105603903e0082403040f4a85101a150285040071041000b6010001040b84d20807001c0300d10240d00d00b401c031929200c0c4010305202c80c4203000042c0742c09034000c400105406418410155148100b20007806002c400c09106224012030428001034141b400510949115032041012000d0000d4032410220b044e034030041403104414064480030340b111009126040c0e00050303550051041e10306208029140050340c1d00307070340074031b40c8900d940ca40309a0791211029044616814180e0b1110450140c41c005841c802c80310640e0040004100a640450380e00000e010304000d90740c0a00e040d1401124040c140f0450213180e401000d06106c02c040c0302d02c241c0c81540c0c40f4516800c0010030141401c00030b00380d17a20170b90014840540002c020b074244045d042d02503004120440c1c0410211100709800c01d414514001c003e8140900d601500392003180501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 366034694 1250 366033444 366033457
    0x5030904091b08031213050604030c031e09090e030918040f1a041b0503030405090a060e070c1a130f2406080f06040c031e1a150916050f 60
    0x107880002c03592502c03080369a0b0741040410b141010a6200414161001c100e181a51103410130042e03d1a641c1d16101901c3e41c07800075204804000484070340c2c2c80c40c0d1741d403882c9110404129645408009140400801c2a940e501502800c1a00100441c003550360b1500c0310102810500c44100c00b9039540d44c2400341900543c0b25000d0064520300c00c5404051040104042c400c501c210300f030030520004040304907031046250082c00d4155000b004103000525042e1840c5600911100c00482c1c6561241c01c83ca401c0403003905c035140410000341c004001c10840036904201148020402d0b03000b4a01440b240d400d91880d01b202a10300311404001206214001d01407050040d854810100b140b02c0d04404a070017048988941080c0340141000b16110380404a03855014070b4001400000b45811521442d140001d680307041c124040c01e0049c0c0d000000c1405102c000001a1909013030780d10f25203200025080e004844400d4822404141001007460340d0003182605155107140c01625070031940c1260542c2d100e201c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 366035944 1250 366034694 366034733
    0x30723160218010b03010513090212010203060a1208070b1812030a153c091a100c0b06041d010608010c140406080703020d1a100c0503090409 62
    0x2200303103100c049200c03249140c920a031544160000d200d01c8074102010280144031219504100422241c50103041d21245000070403000200e0035000d0703001818105150403080003a940100800a07249094402a0020728000c010821413071340b96a154000c81c441c03050002c00d4044460302140041a0010581a0080c204005c40d0708007104070314440419002100c910000608245192503d0044441e101007101e000140c6618040610002d90603115981d4016104102141c808003c0c40000600100c0040411800000360340c003c483d0215909104410114012041d0140c100906544403117000303040d80d00b01c40f2a010039211500010081d01d8621080d003104141049080020b0303c040d440001141c3e807002c000c0154060307080d0141e840f011055110b4401100900003007060724000c42556a1110951500600c0c00024031a1102200d092400400441024401520940c20b00540d131101c100300c141400c80585050b03549582e92403140121a40c06140c6551440c0b04000314608c0201054020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 366037194 1250 366035944 366035947
    0xc110303131403190209070311160203070605160303090203010f020c0c040e070501050a03150531110702041802150a140f0315130c02010c02060a0e03030723 69
    0x2800c441039200800303000d200305003410754000342c01910340001c2245001122001000500082c0e400300300107120700400c21b10038551541000da104500c81c5000703040c0401c0d00791418660b41c003540140740c6031644c0382d0802c000f40a020004106540071013141590700c15450b1401007100c041c80c0c40480d0145c084e10060302c4649001060111807201b01103110302c2c0e89403090710100508000050300c00c0d507400207880350b280415010040c1084a0744250002903000c034040b030f403401c202a0380e54080b8030305103041902c0388800350800043c040c1005a00d1040b809560709072205028400c0ca140483c0001c0c400d14400a00c140d607281c0701e01030b500318101c100038407440c1c00030f011840307540a50940d00e550b9130200b10103900250144000003c40e06010781034802270a260481ca5003160303034250201061054000c1c029901007450b00e07a02c1a41c2e0000d0151198162803640007144c039043c0c60030041c0c03810708003920341a070090070104203a191000010607070307500124504e440807a000781c040e0080c0c0c43c0303080c180000118910 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 366038444 1250 366037194 366037207
    0x905010f051311491a07030c08070e030a120801080706090305060a0506120a050706020d0201020702030a02010c0201170103061e1b0806152d0c0604030c110303 70
    0x406604903480305005801d80014407810808120307070118a03d0307003e4855516030094035070903040305a502e60304910020701c0c00703030802d484400320801c24200407040710804282c21703100c00314058062256402012070f0400b4482c01e520a100076126460080c0b81108000001c03200d0040744c0c0d803c1010b001055040b00407850004100701c0c2c024070f0f0813024010039100388200003000404071321500c0d948044a070041d0141c00e41e5103550611030060400038100c035074054211246030340700c040280000704405220340e0081c212580703000e002904225540c4510420359105001202c05600d02090811400d682480c2015a59840b8401a2060f104100ca14801c008a40002104000ba10351054038607010383c5411001c1d034000c4101c0c00054071413a032038480002c081550030145003400341c0c0b15160000402008028a40f0118418208503007122002d00440d000003481c3d81d4100060040c072425900c61410024030301200b404807950381d00001342c40142042005446841808020500320110041c010b041c1c1303590700d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 366039694 1250 366038444 366038461
    0x3040e0a02040503010608030c06071202040806090a0c0501090e04060c14040605090a05040c1b0302070b071b06080105030703080307020a0c031110030b13020f090d0308090d0503070e040905010f05 86
    0x10050f010b003500941c0307081c03004100c01c1000401c0d1500b030070b100e00007400c0c150740e5968100c9528917003034a4598190307000c1c440418024014040c3c24401c2070808001e10b00e0384821f0400f41512641e40c0e02c0079040c800c000005205202d450381c00c1c1680309810400102c0c06001e0403a0450b0010b44290300a0100320000c82c01240880d80034006284600c011143c403001c030b40c0c4400810007110317024503070f940200d40880750b00e600c503070010207910705140d000380191080c00c1d680c1c1641d5505640700140071200328440b0364500e5482c0f103004041d44044c0c400361524041e10740c10500460395030707070741400040d0a6007004400198458800c02070582d00b90740c40041848500c1d41c034580b0701556070001280520501081d004031603003910a2040951620006010704003030200007440704000c0d401003000c0404410100300f01c0d41940c0f609540855918400c0c1d41d0b221f013514180c0c4880f401e019a802c148410481c007041405922544480c1840c0040c40c100c1b03000400c070403c5c2c50001d00510300d003112280c1d641c0c100f41c00c020010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 366040944 1250 366039694 366039697
    0x81e011706161e18090b0406090b03030f03090106320108250c0204051512010b011713020a060e01020d1701060c032003040303031a0906011103040e0a02 67
    0x428002040340d00c99100e00b0301401c40e104114640341c001441e440449015001c610840ca40b1081c05410800224898a0014982c40c1e440743c20450f030080c6c84498080c41c500b0244a007200034511b5003001c20074a48881700003901ca10444414458004020020410000c5d0a500c114024030380c0d40c10030184d81144401011080c0018505030303440c0402e541283c042d0354010782e100d510854041030f4103412812404c200c2103000800005007010018030800e0400103840390b00c1805c3c0507103020b0803800c1201c8040300030060074031148a540c408070790500d280c0700640d9800681c00a1662244442400103564031107a400900702c140c1006540054081c00000d800d0780c1140e00304a1030b0000b0b034260741105440380300075105000803061003a00603202800410006224403d01d03070155100e032070403810840301101440c0100144000e603805941000504104040c3c062283d4080364500b000b0744d42c0c1921070079000400d1041c1c0204148e06210030340091040030030050040724003612540c841614141030815400c4002d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 366042194 1250 366040944 366040979
    0x307030806131a01050d062303163503180f03030a080114030f030f030a0510030807030305040201022d071e0b07060209040c030c09050609060a081e01 66
    0x91600008200c0c2d5a02c5900034411441c6543c40d199104401c004011102c0c0e0f803101000d010941d907103000100c0c5100003003803441310b00c5900c1d048506c0e0410728842010f052241d220701180c0d900701d0451041064141e000703103550070f50b55039416030502564001d81c07042c108400002c1c80303050f60200040729014011010124074034a44103071081d100c0d20038944241540e91140b8854074001c50210700c010840305e801c001c901ca40244005e801c5e10480e40e402c908591464000d1541100105e101101b0064054040d1081c107520449002d142c01d00145907803550b5080f8410008040c1c101038441c0b00003000e40e402088404000c004480082d0300340c00c6080c00103441c114001c150700384580100200015411a40c8001c0b00f6603c03902d0790300325880762600d5074810b41e82d03000310400c0340c29540070b01c800f034100e5496200704504100d079501c02041d18001000010001201d0780c010901c504010720443c09a40c84401c16140c410825003070050580d140c0070064140a05c00b80140c001c400030040010a2070340304500c28040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 366043444 1250 366042194 366042199
    0x405010b010906020a0b06030c060f19030204030c03020906150c01060807090b010e09090a06020409060e060109030503040909021c032003030f150d230d03050906010b090a080307030806 81
    0x4031220030011100701003039209000040c0d1080c4400b1020410107008030f42c00280040c1111407090240d40401c04540110100c210384000c00310303000c191016001e102e121215410f1408500d014255604c3d2068207c15000180c020f001101c0003501c2600c99076401000c80244d64071090300c0c0c103402c50301940a01068040e60340d140c060008006480386d4503006818070808142c5501c00d00181050901c01e8045004140100340d1040000c2c800c00718030b0307600c0100041c294081e408074000d070a00b11420011200074110604100001d5400c1000c120040103440070b85406a201259031085400003d485c035041a115203102144c0f141800201030300005103151846900c41c0c2c09201c201e14000319512404102c030041c5010042000185a0500c110307802c440c3d2000042c140d036200c6800c1c2d25042007200700c091755100c0100c1c090803540503145007040f120701c054000385004d11862601d00d40881e01c1d400c1c18450510308100c0407441e0b1000d956100200300140030782d1800c49403186402d040041010300e060f03c9560 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 366044694 1250 366043444 366043451
    0xc070516080d141e0906070f0501140105010e095205070503070803040213020a1805030a21030e060406050105130506010e0d06150f150305090a060b030307060c08040501 74
    0x80c00b0620003020340b40a0f6a640d130311341402c08841110205240d002c9220740782e00120410041001554160034100118002d01c000500c0b000068044002140c040c0c00c000e0610129440004c1d590b6a0300c40020f600400c0d040c9042401c0c0081070708031442c81c1c940c14031241100e1000604481440c2104802d0240d190307040480c0076428001c60301a600c0744036950015141c0e820400981c00450709910045400c103201825080140c00340300110f500b2030b00001d00b4000010340e46c112004081d16903401c0b80002c1c1c0001c6003e0201201c0c40d5a8041108008084044401245400c2881d00d103000c0e900500c00c5e10400010707a0301c5403500f407416000404090107443d01c101004141102441e40720f202d9075201d0401a151510742c40152801c01075100340801046a0a540b1341070b89020060080c10720b60020300d680c046902d01541001c9503a5101c0100042c03940030103140104202c000c810006500001c039800100011310448501c0109080d803042072805050305050080003003806903c082d01c1807103180101c0003003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 366045944 1250 366044694 366044717
    0x71208130b040b2d0c0102090301060902030601121a0907050a020706050a0f0305060a030804090b0117040c330903050f01110301180e0f030304030f02060108060c070516080d 76
    0x1a4201e000e6401442c0c210b0f1010700507413107250649000214101c6480e02e640c240341c6220f041001156222003040e88459401040d11801030402740100310141902440941c1146030103030000344041c2e52070f8910700c042c0780c0340c204a4000c03045148461105800107040054540b8000d80003808039802131441d40014410315000003086841101540d0100e1482c1c1c0e903001512a004200b20090000175200d039a006c40c1400c07000001864403402800182940000403071000c0019001510344a81244c2d00901018001c0802c0300007468910702a05881d010820510807050420004243d51000c02202407068600008801c82d03940003d0540e00700c92080b412501c0811011000b1400d8031301840e001042c081c018801030100500c542c0c498403080c2c1d0300c0315000070f4103040c9000c4185000e207060418400d0341c20002c140400d00d40d000c4205d145003010390001b08619403400d051545d40d17090051481c0e204210114600c010860203205a9012903098405050900e07190302105d501d400b082c0b15044041203802000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 366047194 1250 366045944 366045959
    0xa030f09030506010e07020f1e0c0f1003110d020c0a11030d020d0503060301020f030c03071b030e0d0c03020405040312060f0515070204090515060a09060302030307031107120813 78
    0x218000d80b0750110181556928045803420301c010054000c0003940101c00e00010744010401c503030913203203100e108142c40c00c845600759541000c0e01c1015690082402e051003c4981d00c84002c00412581d19140c00641f1155a21242120307001d00c01c9442c060900024007854000b4002481f070305814002c1d401072400014900400da0754941c1022200c0140e08145121003d150141024550180016002519004040b01da40c416913004840c4d059003400040203109001d5403144102070492a041c10501e84c01c0400d07100680101900200c4901c02c0076020300390820403074440051801181c0c058024002da04080c40c0c0a80310400400c0040f9110786460030014001881c44550801c60700c000e4500c103189424850b00741050381c040360050381c10689443c060740c0007820800500900402000c81c3d100d890070620108021007030030313901080b0b270135040074824000f69030003000320303040b1960504242140c081c00080c0c080c00c101050703101c1044c100d85500b5850600c100711005000e082c4181040006ca181c86001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 366048444 1250 366047194 366047207
    0x270c0302120406091b031a06010f090e0a1104030f061b0e0111010e0d05040306150f0e040c05090c0d1d0604080d0b031b0102011a060306042c0a030f 65
    0x40c0c02044040c1a000c03502041c0d4913441914a640a00c0c405646641c08400c2081e001c1d40780d5004645d150601c1500200c1040003548041d00000246022039440d030030303141c9c000d16030003660007240100c5c818100881c000c210b00d81d01945010340301a4600c0c2e2100c3c0d403410584e080d00303070700002640c2d41802e01c83d000381c04201c805020035801c105901c0314200c0c01030700c2d00116088100320040c11100d650300c40913107243c0042002245800c803450b40d900f550340c50540c68100b00751116044600084001c0110601003140054903040907140030b04101c50042d6910300b0b020f0300708041d0354030864115040740d05000c402810600181201000c4160600944040070002e40d08e85c84200d144d02d005400000c0450009600f6000818145040c50808204410782c000040d092400c2c0c010741212524480c60880915602030140303981d40101844044130741c03000c0101140c0c3c0391000a001364420369444405148961619194194404903a1030000382080840711455541400740b400341e001c0b402c2080c03210700072841200c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 366049694 1250 366048444 366048457
    0x9031101050a06030c0b090414181c141c060303030c0905030703050c06220f09110313060b0a0801020d1d0604030c020418020303030f0f060f0a05090709270c0302 71
    0x2445c400100d4031307148000b0a2504103200d542c1c0d1154481c0c5d5000d04590340001d050b40a2106600001c640081c0003852910b000c6c51524114511159075503a0011213405c90604a030f6aa40007403102c1da24039100c0100041d03094801c0075820450300d000310100a059041c0c0c00600c507403d864071010341c440c1d1070700201640e031411480300038451345c803200c0030031000d04002c2c02404160480080c030050090031181d074a030450360142c11a40340101541000c1120503294014100140406800c491a6081038058010b000c03698400142c20a0303100e030400001600c560544400406000d0300031034035210301c840401c0107409955221560742031401c0d016840b150010406074040e80d850b4a03403186c5440140e00307101c003038002c00962034600340c5a01c0220002d601e0030b01c02113200d140c010310103c0040c50030510007401050050440b6004a00045103504152264040c040564408403100822503a0345501201c01c80310785c0d001050300318040800a1004141c1035900e1a000c180131809000c5095030041c00c804902411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 366050944 1250 366049694 366049703
    0x210606040b09060a0302130621021602011404090608060103061b020604030e04060e070e04150807092a0504060e0f0612040204060801020a0207080105130201020a1e0609031101050a0603 81
    0x4010b042078034948100109810052800d0141c14444504c800c02016070484d0710030b1740412a130003611a0080c0e0301003207600b80c800d200d0b00c08504281c464050b0031459489050020b06012985180031414080c3e202620010200c000e000d000d481d884600035a2284801e10081b10344900b000034055520f00c3c100c00240014030164010005561144ca04443c001842c00d03503160010740c3d0710b9021900c8076903500614865461a25144040c036403075001c1c0004c0b10384405015140b9151078805000e42da1010030f50200300c034106800441e40c206600380d50b01c204104c4001c004c00244c00d10882c3c00700e40d90800c024104031065038840940c150220300501c8480d0a00c100302503400708040000c0c45581c0001d010322500280007a0001440079100c4140c10308a074058180c48001d80d010f1001040301d43ca007400340d04d90016101068148800c03044e80040d54a9041d400024224015189100044907454a194140381d8100c0d40a00c44030401c4d003000f42c064614420350710042d500340000641d540d903a502413001182c3d0710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 366052194 1250 366050944 366050947
    0x10e15090d120603080d0b090a0603150c0e0d050a12030203060a030f1118160302070f0204021b07090c0807030c021e03090603010314070617011415210606040b 70
    0x400c0c01c4900b0b00c0165031144078260b03642008400b0130310369006030691a11003603002680d8040c0c00e0420020300c50060012100303c1c185079050001400c11000b100d08070b030203441c0200304003210040c103403600100400e985d40c000e5414400340c0c0902c54001261050700f4010f030030301c1600080002c07084040c1e20048032000e8120b40d41441c100700042c2041c40b034204040c002c1c020481c01861883c000780101d116a005064806407000c20f008101c1e058108085a252440c241145062000d0781c4981c0785209c40c050213803003154041404040140d0154404801d50045000e590081d034a86081d0340041c00301034130038400a0600800180400e009100c1c0054500f84d54000344026120392a50701482020301a40d840e00b40014030900089403503850245001e10700c5810a200c05000b0b0300d04451800071641d200808214440507149800405600c400d410345100b15803d490054034000840c0220f4001c10050107070b100300048020318442e00c20b07805500352035941d40351038507034943ca410440d15000724081d03070310ba1000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 366053444 1250 366052194 366052213
    0x403020d0e0619020c12010b0121180f0b0a0b060d09110303070f1e0c0b03040303020405120c030d0f12020c0c040e0d180b0d09020f030105010602010e1509 68
    0x3409003014a40340003080a40360403003a000c41c114248522000001585c49100c83d03140d40e140c043e2213400d108401400801114905000003000c200104150307403107078185a20842050211500540001030741d2850007221000315103003d03500d0001080040c0c901d21103010120309401400d0042c001020300080082c4e0a00b0413000035400104911542158081c002c0a43e0440da038609001034640c860280d4015000d800306401c003800c10018819454081c0641c451000001882181c0403609450a0500f11600d95965180513402485036800c600e50100a0188140c042070000401400c0808141c0a962005031105420385d007050b0201c20f18070204842d12180ea1403c101079002d000321051030800c44480c21812000700e81250040c4691403c00d811071501130600c10b810861500300010145500031407140307001180c0e03080740540748800c00c90319101c0590720155992218090140d01c0028020051541e4680c0081e00910654844042500031231412124111025400a00c80c041c1030303024101c1402d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 366054694 1250 366053444 366053447
    0x6090f0115030b030f030403031e091a16080417010606050910090312050403031404080a030516061a01020c0618091807030803060901170a023615090403020d 69
    0x107003036450a00806a603008201c515a90400032140da0b0314003400034660361070850030010300103c1c50034003440f90527036410848000c40750301107000c02c120b0b6140f03402910501d18104450040b84948106600207000261484060240e030a00510480b1400140055a00e01c8158250f00340c17001c1d4800e12000c584244804100d0b03080c1340b28402c201111910386000c0198490713840584098592403844001240400c06108058100214807400002204082d00b001d00e0802c071569a10a4484003c040140100c2c0e030740c0401814801c48074100741d10150a016080400d800e0b06111142000c5140c010f214000310841d45081c07540c2100d00720b4808041c1c0380c22425000040c018010301c060030000c114903e001c045413030828141b1131540654440c0c056190b880c102441041006030061300001d100c1c03031100034820340b42d00000829050840d4155030000a4151820000e20903800603082007020200f41c600b842c1280511140092081011440c0c0c900c21513006014031400e01c9007101e006000d81e011802d0040d41c60b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 366055944 1250 366054694 366054719
    0xd020a061a060408010207030e09040c05010c170705250e0619180204081606020d030f020405060705010519090f1e0606030614070f0e01030b18090a030806090f01 71
    0x3101041c220651401018041560303a032050740042080e03540483d2180800d680300c0603030360480c4400c850300c101900745034581c00d41d800b50a00c6200d0600840ca445602004000752042d041c1c0b40da600c0c18580c4500c0c00d414043e45444000d08402503288030414245030362240300c075005044c1c4a0003401e40c0480e5880200b4007850301c3c00c05003840140040382f5000640a00c1e403800b619032401041c81e0141c0c50b289865413181c640175200c2c14442c101c0200800900000f82e001401c0d0078a0f0f4414a00402ca00702440340c850000d10407030b0400d5030010000a80034050040541189000340350b08010072201e207443c2c1d00036000b2900ca9290082c0340c690f400c0caa29000c103045c41c80c0b600c00c4c60f00300c400c15601e40c40b107942d480040f11075a90003102c1440d22040184402c0400202c0f0b00c3e4002c24504002c07809441019000340700d0b8200e03191244c1490f0ba150301595141c0c4400018060a8880608402d2175050003405256140c10600e030440010b24154005038603801c00c14100740c0990550321011038140d00300200071521 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 366057194 1250 366055944 366055961
    0x7030809030f120414040b01080402010305040f0c0f0e0a0203041e2d02040e2803051e031909020a060c08091905030c030c0f010503060303070c091d0d020a06 69
    0x9031103000c80d0005000003e0242a02c1c002d54030818955451409500800341003085d210117100728585401c1d1851a6044550154030540c2480d000a05a450b8038140441082c1020060030786400c0660200b43c2520000e4880d090740d0101100036010340c1c1e101d007148243e01c0211002003010318035020049090714480c01244000c1d1240000706817405002d14111004106a000541d207194014801403c0d0f0500e88585050179031010050301d4118582c21108480c807a1851895101380301466100003414031920554111001c50200382461224075420f6580315003003035603502101300c03c40400a405031410b20501c00200e40c003400c2c03501d0f140d281c001c007902c1120550f517096600343c02c10001440c032503450100005404e419240401d03112403c09044c545020680c0390194000c2e40000f5403200b003660358103814454580240b0384665a41d40320000309085004844005042d40105100402d00e0342e4150080020912049402440503407205000d0f65580c021403290790150700012030700c3e4040b032410307009100c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 366058444 1250 366057194 366057199
    0xf03030507110604030e010905240d0906180506061807031d030c061023040504020616050f0c0406030b0f0c311502070b0a020a120e03060a05070207030809 68
    0x455060300c8510b900300281114220000f6001004a00726076030091410ba025100a940000200070121058402c0e5080f24042d031840c03903c04103007034020b007145821210740558450380500c0000210942c83c050442070201c2120207003e2400012002d0506590129507000c60b01030581541d2250348041e001030403030401d41c003e401000800140c007440d0400c0142511a0600e00510451910bd1929081180c0799002104020305403410342e201d84c0140c0d00c1a0384007040858002403d92580e1001940501c6a01c030540650071400d0031003000d204000c200150840c0032a0240c801c003c802404000444030389000041c01c2c4446000410007a1350402c03d130680c0400080f1441346018040711210600b040900d4454840f884207207103030000c090000c855803000f000e02140c0e041d045584101e000e1b4682e0303400e0144240c84000895655045803013000882c0c8030b260400384408031410f03018401040310b46102c0500c2d00a01c600000700d03400c0c0c002846072710300c5440d16a010388074643c11a501d05016070303c900e04155 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 366059694 1250 366058444 366058457
    0xb07050a091a0a032009040b13050117010e060c0a030c0c060e030903210306100c0605040606030203011b090b0c070f09060501170f040807022715030a0f03030507 71
    0x141c000314a44500b0302c001d0002e4030203903c1d1400f1030300c003c054039543d91410880c541504000d00002141c102a1030844104075000b00d820000c00380868407a94402809801c0c050500b03000140c01904600700c014000303613210080c880305240b540255134410098901d2003181d802000b034840b1080c0f20340c0c05032a004406103804100c00c2d203191140829580b0342e1a204841c0c2c2c000040801403494100401c2e600384007103946406501211060030032440c0130080265000340808803500700300c98800c1e425410741c50b40c0080c00700403d00b070a00f0428010850740c00100d00940ca0020a6840d90550303603100e917900c00c1c69540d050001418040401500d410104e01000c452080440120350607581185600140c4500d41c0c00080c1c0344c0c50070000400d659039a056040ca144480014001d0083d001c032499544540c00070006aa141030070310200341076010034036044850070f01d07207909950800c0904000c0c03030044404260307043c0000c02407001c0644811561354020065100e0001c1000003078040c2c0c02c442c1d0302044a040c000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 366060944 1250 366059694 366059699
    0x1f050702090604090b040c0501020d020606090a0513050307050604061802150a030b03060a05070f1404050f0d141b040c020303040f020a080a0305070201140301060203030a11090307060e1008040b07050a09 89
    0x11691710009480071905401152818000b43d6070400c10720844041c1807004180a0500030049480e451002d414690700c00d890b600050100701c0c10740402805540d00c10200c03540c5444a060150f16484d0a4804484260401307c4a006400340c800c00e41c82e8940c0c00504102212107401041031b1540d200d20325803024180c0380c500000e01d0380e90911a00f0312507042888045611710b403900340240040800400801400081c0b61620000100c2d0303401c0c0c60030345005030780d01d403405102000002c0754400800c100502845a0764500810280003040000c44c3c940e48100d01c0011090300402c01082e5003c03202800d006134014400a80880e2003180d680100e1800600700003c402d8031784120509040030b0440c2940030400000d2800119648600e41c004048100d11900307045504141009490344000307860f5404040d12203841610079100c810848214540090866940507a90900038124004101c2d055114401d50803081081b41e0140700064130130b070b50003c01e4100d182c0c2e50040581d00e540001d00c075002008a0000003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 366062194 1250 366060944 366060953
    0x1801111f050a050105010507120e06040b0708092d0d080f040305060717100b031f120311010204030506010b031005090406051f0510030f0b040f0b1f05070209060409 72
    0x804004034014081024a40300c1c000e10b06552060b0320041c10410700300120000f080000e03141c00d80b81e03105840e10489580310b0400140e03070340c007440d04003600da030702c0004150080004580040568200035650282d05220f001c02c0f0300442010110031240a6819010341c2c08146040410040f54510070300c800344c10076440c02042401034016820841c1c080d840f20041c40380807500198101c0120600305054400c5144c41c501401039040503206032006004003001141c0e180d48480c03100e8030303584104808540102e0307540d00c24002000281100394007040a09021120038403040c02280c098075080f100400701c1c1d0740303480804546584002d0562044110325a80070036a56154580c0e140540c0c090340c408034990802070030811040502c024842a814170a1030200001d131a100700507030381d95510f03040c0011407481054081c0041c0a444ca14141c0c0300d0b01d400241e038000040d9074014003507004107031011a24010700c100c42290381c0c8420408140420428000100103240100c450b1741d000e01c0241001c106500e40f03a0701c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 366063444 1250 366062194 366062233
    0x2240c010c050405181e570a0c050304030c29090a030b0606070b0f011d09030403060b040e03030403120509030405011d03010b0904120e0105180111 65
    0x70024001000024200310525010039021040c00048244c041c07141000e41460b000d0040610604002e0343c150f400040048219140300104140740da0341308451800702d84c031240800d040407034480c01d403d461980c0070452403051000007201d240341070340c8040c90083c096405955a00900707000f100c40c0c0c407042002000084007001580000c00d407010b000e2480c501003010500c3c59007016081101486821300c060384c5550b482c0e082c0d05c0203da81240e0103403c280c0300c11002c10110700c40c403040902840510024012200000000d060407103a500c2c018410200c14401e451481c1d0a0540350410341e42e00500051000c0b4801d43e0000c1c0c1210001800011386495103550740d03003550030885056004c0350b141c0d900c0e00706500960203100c0d40b008043c40558a810f04000000e051a6003000000b4070540c2d50201043d600e880941c49082c4c40ca0009180c40315500d05071404545000003081c0d480000740c0d20760006040e5501803425204006c0d480101d20400c40402c100466000784100741d00034481c451840b2511004c1e0000780c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 366064694 1250 366063444 366063461
    0xc05030304110621070201060902070302150c160b06030c0a030b1801060306240905100608040c0909140706020606090f07140a030c0305010803090a030b1803030a06150206010302240c01 81
    0x413503000520740b10380c020342152000c3d400309190314010084680040d40c04204202c1940002d480d54185882c1d0501050050281c81c44150044005050000620a500d440d0510580c070480817101c2c8000302d03c041c404030380304500c002864400f10101280d0354880c01a000e44170f001020000040b010390360340f24081a00c4500c011042180846282c940c52000088910000340620000c00e10141c1400c0c0741482d154081880340904002c2403001141c200081709850900401c039241c81403021407208e042c120284a18182d59120a1144600014249002184aa109503070092040c01c4940c0d0391981d001034070100406140400034403070101410401e410000e0001c001d00d0360740c002240180e00d0030103022031780d060700708100646c01481419403c0d0b681003080d0041c0c03940843c3c0c058442d0cca044040200141c1e02c2c01e12001400301001b00000d60203036505c60b1084801130007081021401d005070030f80c1c8a42c020b000103900700900780b0300c4044101040100004820900701c6151601c8540e4400600f101c0009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 366065944 1250 366064694 366064747
    0x160507140906030105250302040302060f03100f080d030203040204021204030e0a0602030910030903110105010308090f1c2a03050114010b0307020730120305070c050303041106 77
    0x9450102403424400211a800b04040c0d0080041c3c0c1010b0510004c1081c1620701030107600100c400e4011524461740569000796400340407551510100309001c20240c00494130007144081c142c40019400041d9012001240c84601c00741540210354081100690300040080c1d03041a0200400490b0740c2c14829440d00c00c6010341d850700050710b8110200700f82032030a5440101158828014034459940c0d81021802408007030a00007203160407498113403120140e100e10b15a0a501c2c000000050082e010b00801288004640403044e43c00544104804401c8016a1078000c0e220190590001021a0068440005d400020864000000e511101e1b000c01540040b507403651076650703100d540c41150407258003400d861061386055140580c0002d603208200c0c4281c00c2c54046081c0043c0c507403400422100c00d0b01c00011000e510a01c01030400b503803409000807203180064505400610a11700c03800852880e04e034040040c51440d10f56889a543c00c00d104400c02d58000302c10801c00c640c198060f000010000003c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 366067194 1250 366065944 366065969
    0x230a0b0406150909150e180f0706080115091203030506030c040f140f091207110a121a060109090e120a08090d022103130204020d0902030601050a050a0308160507 71
    0x140104003059680101c8030135074000700f4030000d0040681c0307118000d0f4042c40308414080e222840080c86448c00489520119007401600c4000c01c0e65680200100e0503550f40c40440f6440c84030b1362500320303010303a03551203282c0c400d003205100080040e21940005400020080480303802c0c03940c0d44d0000b400c85040d607000001840e9070b030003246001d016010000b035012440c0308440756646000e624241d220f42d030510625003407181c006000000c00070030996005a041e0080e00c0c9218494170780c420140090603448013501c092001c0c0d410445580c103c4c0c01e201e44a030b103041c0e547c2d0322018a48100035028001c044510400740c0181e00310701000762030010140804010b25982c802031400d10500e11800d0401c00b180303500840d00007600c0311011048a24802c13050302c803102d104669030341c1d0380d41100c603c3e8411000020351280c000a1071011101c00341d00720f01c28150080703080d2005642d03190200280c058091181a411440440040020a000300080e1911050760700020441d82e0380c3d560307080c0c10f03c50b40b9040705400c01e20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 366068444 1250 366067194 366067199
    0xa140307060b0d020108130501060e010605030106080a110a12091b0e090606030a0201260403081009021905070323040f080109020315060310060b090103230a0b04061509 74
    0x10309000b0a140000c06441111008200350002008032800a003800e0101503c060044108802544018003d14110709403018030750f1202c0300100150300a1060000145100c0040740070200b180c030030f40c5c03210a00c40c2e09440c601643e04e00242c40401301c0308000c0d89107641d99110403010522001440940f02d01e0907800c4338003641814401500d038440548244629444042005815100050003404858090914002c0880405000d03614001c410f42441882e401c1501480708040c1c210700b44070f024207102802401d107540c403400e64808030302891590407021500b0751102c8080f10f00960041c0700e607500910b0140c460340c0c080f000031404005040000d40d001c43c400601005080144541c0310003500406000740012107940e00007030b540700308a407940324050000320046140303a0780820501000c2040d07140240080c95880004811390f1b080001a1800310382001d00c112440c8c8140b807200c0094488801a000007500c41104e40c1d0000c201000300250003e0396160045000701400e0351420b080d408030b541f000109070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 366069694 1250 366068444 366068453
    0x603031602100c05161d090601030f02360a0b130905120a09030209160c1101110f0105061206040302070308090114040b07030909050c0a050d090f050703030e0d08030708090a140307 79
    0x2d080d01420042924180011f400021a00f0340c1142c1d080340e06840c00001c10b0000032459a103140000c00182c540d0130f6111162402c003a05c00c41c01001c140110010707542d443c0e0080064803006000c042d440903003040c25908110342903221408183c010f0701240c292811000c0600e465512034400c1c2000716901d44410000c601c1c2a1805c0c175032101060140f007c400040b414050306400600d50300800340120b04504250591003034001c0c803030b90b44142c4120b03000e110305004258000c1c542958124026842040008800c580010704a806039905030300074801c40b40f43d0340b200301c042d1304000e5003c6c0c108180303441c1440207041208041d00141c00c40d40b131100c0d0f9580203072501904104039680f088404078140389c02c10910071008802d848030b031180d42c14910765031031600d940300009200a02c1c00809141e042034049051042c00691001079070710030b0b214030015108010400407903002200e401010140200700040043e0310802a241e0080740000403211803011640d100c40100840c0c00e41003410342e2001c2885824031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 366070944 1250 366069694 366069719
    0x130e01030b090d0f0507021e0306070e1302040b1215060403150b0109031709030a0803150a0e10172d0709020c0c040504021f170603031602100c0516 65
    0x160b052113840b0840d45200645240113120000c1d00c6200c1241070203516030700026560b130703070307200021f040d0b540500d0100f0019229400e5400c2442c043c0520304601c200c20b10f1a4400c40d02038070048101d8501b84440c3c200d00c4906884011f00120418070303c0c40c1d01394455122040504065849135070442115041c1c0d5210404844850b042c060400101c0c24040000c640a4401c6d0550070ba102003081d0740d0760000d503000c2031410341c40b00002400a03500004004442505080b0080f130300004031824094660b5610341e5100d039800590b25400307490005141008846400200c14885983d41c0302965003c4241e4030b00d4040300c246540000c00d800c8071030207508018030018441000608031500d4114104004401ea40d0795440c51440e60602031540e0700c2c040307401d66070b07400c1c2c00e0039885001e150707400840c10510b0402810803a50316100c006110000c1b002c1482450040147c0b03525441c00380b800c0804000c6030b0208803465208011450038064501010380c0418004d20811040c8111214440340041c07030a40381c20f00b00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 366072194 1250 366070944 366070963
    0x30604091407060e0111060412051305030703080705061b040905060409120207060305011205060103060c02160605070302060a05061e2706030c01030c1d010512040b06040f020307090b130e01030b09 86
    0x55400c881f007080001750a00f4901a6516203629105880350140c1114003d5602c40740c01540d031610801c200041003042d00740003000c90500c502c003a968540c4a0f895012420392003200c04d12013101080c0001d012003509a0f201e958400030084c070200c0d034192540c91390300c060f6512001c01d0740142c10440040c40000d030503004442c010904145000d60708452174441c2500c2c3c18040c000242106d490782125400c0501c200007011006001c0074400507420303584c04015150340e0086c0070450140c012140043c9d100c41440c484c1d54403d1102510503115861031340c101442e0704120407005030f44500400e40c000b81e40c1c20f00e204214008101c0350040740070303401c100c0c3c2007504c0c00e05504241350406042c417039542012940050043e141c413030382c88492076440c03084400503516406504c01541c1240300400401c400c1c800c9121850f401410159010070074644500185c009a2004940034404681c5185042000c48002401071441c951140700541200e501c6503440911940280d00581d05205180d091200e41070003070140c042c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 366073444 1250 366072194 366072227
    0x80706121103180618030d0b2b03020705040213090f111602030c1c0215070203030f030f070201060819020604080604080a270e070c1406100911030604091407060e01 72
    0x417109031a80d13130710b40c2d40c1c8074040192050326201d28070a00c0c0d507101d0111a0290360159201840760350918140b0000c1c00d141500181e0061044010000c1c5c00d0505100701e9181101c44591aa44103041c160f101015100300d141000c4c110b60791b0907000028448810280c4501c4190340080399a041c00f600405280840002450344616000054045403003000b1041041c01e07981500c01da51150700c0c413010344207d0700600c0c0010f5018080018014840e04420000714451141d035a02c1180580721444103e00b21042801545581c1d4802e0040c3c20480080c81000f00800f48000c107124541503e0307103007190a00b40140c070121a441c07800b16503894101d80001d0030001000c2d898142d050310145035081c42d141e07810240709041042e4006004a42307600c0c45039003440d10b4160800d41c150f0894140d00040c07a9502e90407102442600342c402c1d8082800d1200e03000350440600403031189411901c40c036040000900f007440084425030046024a0400002030000ca00180340545030103008000c074a00142c0401900b6403e0340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 366074694 1250 366073444 366073471
    0x3060914010b03040b090f060405030703140702011218050f0f07060512010b0a0309080307020a050d0c111c050708070e060f240409110d0c090807061211031806 70
    0x2e40d05107420b90358004c1d00003103c000b1a0329410803050503c2c0b0f0703912000d400c601402d41040b007800400402040a1480b035902c401d1110304a00a10301c1c907025000b4004e0000c0d40040740c01c452280c0981101100750041248840d0855065460b00d01d03046c5113102c0000160802203611000400510086000b000c0a08203103180440c3d0300040a03892405010350048844c0205034500c1540c4a42c1c030201034207604c602e0f00396690070403501c042d603030301c0340340b10300312101d1060a540801c0c1505c900c2004806503401029030305144109010040c88509800d210107a03409a110454003080007001107400800000c4007809850b8240b600d1480084001050140103c0e00c10b03a0442550302d80d103015085400810b40005082075100d001001c1600c900d50110f40d845040407020310600440c2030048c094a00c1c0e005081000700d090301c1c000c1c1c82c9411144100b850f5900032610400203907000b582d03508007031f0b00c02204c001640003040101131101e42080d10803126026504001485101c2c1c02c01549070011100408003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 366075944 1250 366074694 366074699
    0x1d030c0a110301060b0a0807021002070b0402101b0215190906030509010204031a1902030c04061d0102120a020102070606062001050103051e030c010e011415030723090103030306091401 81
    0x4011702d02c51517402c0c20402071f400d000540482c0c0f0078000669000801401550303500c3e094104100e40040a40e0168071400c14019100c9501d40942042082e001041c580c0903e4103005800308a031482480348500c00c40982003014852100205600305110b0407161101d141d820309182005003113420060110a05130310401051000c03071908040002406c40800f1415255658850b50f411040745021050b035083d8000300501c0b868000000c00b84c0141c41c019511220131002c0004826507542d4020f1200e40560003000c8407074403051148000340200011703400090f11300107c946e01c0e8801c6400582c4540009040d01c1c011140301150840d900c005004088000c0c441941151100b40c0c64000c04803003a20300c0c200c00421010307292014820740381000071640007040400c4c200301246002e080b0340c0c62180d0702c00076002c00145c0f1440e00e8140005495a0140040c08040d080803d0351586001002d031815401d84000c0d981c20312a654030070020b000c3c4d84255000320744a86402030384415283c000070b482014200e0403005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 366077194 1250 366075944 366075959
    0x60c071d0f04170c01090302010f0c0e150325032028090b040f03031103070507050f060403061e050c281103071109010b0301120201031d030c0a11030106 67
    0x101e40d0040d0304962500c141500504102e0003900c140384c2001001d5080080c0079007419010343c02511413502291003845444450a821071300b141801c850640c0c070a0100c002210b841c044000a944d200503984100300c5000110f460b02c0713410400c2c8254040020b40ca0b04002d44160030311030403840c1c100210818050404041080b140700c200d60f2903014500c1d4104080681981c0c9108041c0b20380180040340f00c465485850307204a0b01050f40740d01043d000704e14040840ca100c11400011a91315a0700300d40030b80444c1d070400080021800111950b1544814180008008680359100c1d00140d000c820440003194401c40800d803043d510020060301c0202d0061148804258040304c40844101510361581c05001c0194803c2d6900c880610104255210210b000001c0020940c4c0801407518112101e0724660381c0c070f11174102d00d4402405004546041d00c01354200650007500301c010300840c4440705503c40503c3d003489500d186c000c004040400d50000d081102400b0202c10801c0c1040800d030006e00c046404c1c80b12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 366078444 1250 366077194 366077221
    0x1205010606050a0f0c150614190b07120c02041103090c0909121b030429040b09120f1c080105040b090705030705090d08070b0901140c0711060c071d 65
    0x3031020f02c50580c0760171042000a4842404030740035002e00300115510b85023004560006496010b0251110b4650850351414145501d4100c840400540d8580543d0f5070717031084214414401b000074408440040030050743c890146000c1d40d0041c4100d1912880c104003c2480c0411000d95140030321030100900891070400714514070108070700c400240d0344259644442071050220301ea000c0e01400045804a082990070314000130380d022441035062038100d00d2400d60454458ec0c07186100151041060381454240101c1038000341c82e885043c0c8480d140000601c42c00c1c4002c041c055079080152000c0681c0441c0c0120a2038054072080d0340800c2101001c601141e030b030002c0584840c0c00c1c000e011001a40c45440b41040316603402c3c000c2d000c0b0265090300d10380002c1c2604902012200941c00c0d00025020040500c130701040700184130000400c50b183c80c50203015641c4142e0041e10000705020084c84d07282c4581000301035001403503000b000d48510b040350444e804481404610096442c41c018021082082c09 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 366079694 1250 366078444 366078467
    0x90803040b0f0613020a05070507060e03061b090904110a06180f03080a0e03160605071a0709050f0a0902040b03010806090f0c060307201f061d0402010309020a1205010606050a 77
    0x1300581e6085040426038060180c9a0018518402c2c1e84020400d5035000020968540058040f12001e4840c20601e004040f1050050803240700c1c00e001c030400070304d01040746541080c041e0360292050b1a83d00041805103600d0380220001c00c5d0700c08060040010041d03c9040140400400d4420b0242035654002961003010281d00c1001b00200d88030307640d543c06000032100344880e0071000310f507990341e0343d40a0401c2d0403010058500701608405c60040d01800c1b03002c144104110340d03401481506000030015030603012075400784c00444041300821301d407200d840100040c22000c03800c6901d0b58035190800e4503200004141136201d4000100347c819007035000a94904d0400221080b80e01c99480ea40c00702c3e903640001d001d59200200c484000e0540c0f03000400c0c54025600000c000702100841d81c0101c1041e22910722400fa42c2510b0010902c00c0d0311004483e43da0000d105140104004079180c000412602a54011000301d10481011100b0800c09214120080c1081e00301a070400030300250251402c3c8602 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 366080944 1250 366079694 366079729
    0x130201050d150e0a1407050901080402130f150816030b0a050a020d0504060906060501020c0105041a120103200301140c090f091303020606150415030f090803040b0f06 73
    0x42c080740310690a0a480d00c40a080d0320200a0305520708a16041c0140c010289109042c010410101325020310940454882000607120b024103510b0302e43c03c2c40500b200d41d11039000c010f55540c03d81082440315008418a407125100074004245c201881641003400703119441110440302e035001c200180040d200d09502240b803080004003561019500c202901c16042441c00d22490042004100701d110b900000b50b85025110803c8800e40729401640d442c00440000360220304240300c01c1101d0128243c40c03401080c50f40003501e0808a42c07510014a44da000e1f00100c5840c0d141044909420984440d1881242821002444058504404a039240d0000381070034000182c00150344000341c903080d51a5441580207041c010349407515802e00019105000d000f140140541004600149880c803204070548151801561410f89020071400c01c010038007008005250f122188000c6001851084401d00c038020820203980385807500d04440440d02c014152900310304c2140a001c13080e00e483c040c01c0c1c03918508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 366082194 1250 366080944 366080951
    0x150f04060806071b02060a032702090109020f0705010c020c010810050d0f050c030703061a010206010518100807030b041103010c1709070308040b0a140a121a06070b0708130201050d 79
    0x2804510081540c400b41d0203034000c0000101f1100c46d5615600018822032071444001c107600e040c8801150340800c0d014041e601c504900f0040c020030456900901e0160100300000d481e107180c0741c0c1c03403d082d11847c502d480096004042c10100030b5800214941e0b01514a4400c440d805041000240d414800c80501819001000240c8020480c00700b2120301c8584008007104d0380903541e03103882d0f0090040c0c400c00000c11088804c05200d00c1d4000107406e8140d0710010702070f07661145078107200c000804000303159a64801341c0810020f1289000d02403a000345002d5001e180803841c007800d14016003803d00c064640203030b251100c15070b16183c0c801603010b01200d00200e05100d5454140300c4516100e003a80000e041008005400036030821414010120391402d5100d4528101400c1001210350003900b800c4004545405454620175089502103110300031301c0c1d03460113003a800714000f00340d554000060446480c2030060510035580d0b0461072080c2d014500c11550b0048007056400200301c0c1c0940024080e100d901d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 366083444 1250 366082194 366082217
    0x19030216081902011101021602031903171b0301030302160f12030f0908010e0307021207290403061805120f0703080a1803080a0c0c020609120f0105150f0406080607 72
    0x481d401c1404800c5c0f0000007591a24100e643d034904c500003c0740c080b4402d10072010001c000705d80d900c03804190607405072900c149401c210120703103003010802010012440207862410b0038007e90603010b58040c2d4001c0e401016041c103803005040c0d418071a0340040750100c1e00c0a030300304010741e4505a080300c11580340c64543d26465841d181a100b030742e0a600142059420150b620700c1000001000d02201c41c021a0343c20705001c042660035403103c1041c050141204a080c0354080b40e202040600816032807460109894156283c0f1544116102c600740d406280c0070301742000301801020003031000440d003640d000700e140c602c058900302c8007840303404001014013152000098100000303501c41c030b000c410400308042d0650300d1890000c22a0000319603110f0010305e488009a241b03440f41c02d928655581c060141840d200369a020000c0312001445440d51611548040e85d11440084c02014021041400418403260715041044440012039044601680c913040b01081402d40020b2800e421003514105000b0020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 366084694 1250 366083444 366083447
    0x90b0907030b0a170c0a0b2503090302040c050c0c030606060a0c02011b080c1204030f02040902060d06080709061710180b0403120501050f010903030503070507051903021608190201 79
    0x5416482014020803003044403429007008282d091170303080103e035001e890640f40d8050301440d014400700340750700e4005111245c460039905042c2c45001c03400782c18038240e000d03602c0e400581551804480c08000500c0030901e0b91006004103c18007000800b10050401c510f00300740401e510380200c000300010000040340c81c40a42e40200d81c0164801c20020600c20340900504002585030300040001c0341520400080c03901110400381030310280c07540b04001c0c501d0501ca40c1c00b0840a000603480682e0300210400121944490902c01d140041001d40301400e8280d24203281d0b4400c503011580600780c910120a101c02c03d5010220380110004403510340020032482030019003a2048040d180100003a41c03600600042c5904001e02c0b1400001d800c03001d00c100e83e290b5061141c404622404a4040341d028032080c0002402400503650298152500908000070b41e2506403404414402510205001c00032540a16a041c00100040315050200980c580c0c82c0c405150b698240d2001503040d2000e40780c1030074045a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 366085944 1250 366084694 366084709
    0xd09120f060b12150915040507090c030f020a1206060f0806060304080403020d03050c010507090302030d0f1b030503091504020d110f040905010b180c040605070c0504110a09090b0907030b 82
    0x450380c043c115034044488a458444008095542d8090343c8500c0707452138155070501c81c0e41c6210704d500202904d0b005240c54403c00180844860319800d00d6194641000380750078a1000d0300c41d03003101d82e603400e58041054900d40211015600914200306c0100303d41002c3c01d402550307654006030250b40441e500e0303503a400c102c0d85600403904000d5100c00410100d40600d6031120103051040c2052000b004240c64011094840c041540300094040c2c00038022040010300403005008180b20780d0400040f98a00000d400c0d007003500b91041140401c01c04020702205078001c001d8401c4603100c510300a00d41c0c0c2010380010749004103000000740b440007001c41154643c0c07240a00743c0703214000541305000c0701d113082c54460b001e001a5141e0300c2c025602402140c0c00f404c4150f030303100c0c011007565072100d01d00b80c01e0100480b419448868140d0710320485040000e0783c4e449a2250070040c10711003d0640d1a8521908000e104401031342c04000b907a400c00004c25000d82e81e04044640180a9040010f030709041d00004c95440c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 366087194 1250 366085944 366085969
    0x5070507050d0309030b0a091a0403030b0303040b041a032a121303170c03061005070804090212010b0a2f070807060216080607050c07170d09120f060b 66
    0x3100b04540d00c4410503030007034150300507648594590700c0b40e6668009100c04880c445032001e1b192502401040c490824260300458204e4000d2601040118500d40800d10b503030711580c400814070724002410043d00070010011100d07290002c001c90300d50705001040704101540411944840300b81d81e4155005801030400f00d0340603041e0b0000658071854508001060f08640f0320064022070008820407402000c900071080c4181181d10b4144d085444050070b0044003081b80700c04a0621604200b10381c04640e24070702800081140103809607407940f528030144185041a4081c1e401c0c41001d201e4016032680152000700b175403400032054400e00380f0014003049501c10400c20f0222a0150801c0840c4251011441c202528059000c481d0f8180d000040c03594014510311a111441c0c08c1000032608403849103000340311300e40e0448110340070503499952a50203100b182c162426aa40320750311100c0340d030b03030000241c200510f180503280b060301035207840d001440d04030040b0042540d9a50b8826099a81d9518041d0b4007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 366088444 1250 366087194 366087199
    0x5060a020f0601030f060c080415020d0603080304050a030905031207060b0a18060e10082d240609010308030a0f020f0708070b1f0909032d0305180c010507050705 71
    0x2c20b5603403810920607100b00c188096034843d003890510320809008070742c1140640d900842e0304400342c0e8490541c4000303400441d8049a81d40c0c807a20000081016000030710b014501910141483c0c40742c0e440d014004050a0340120300030340103d200c401d03010b00b90303806580616401c0f14010490b075000000041c0611440d40007840021580034884c01e100d0100d0b0b01203425180862031414182e2225000c260524066120b0114544c1c044c940050101e5208405502e441c0a01c0c00d8030801b801e0294003940c02c00154400050765100d038840311800d24180f4496241c0c00803400c2d20816080c0d41103813a002c400d484000c0c0201080f03034a5180100380800680c1c11075400340000340c1d0087d200c0b8814030303141721150b2105005031816054200032547d920308081903240d03801c0842521010807490400900094629040141c0030302600081c2c41d506204071510610644c4100e644c07130074806070095000780c100c03200036212143c90102000c072030300c0c1410b00080300f554009090801036281c40003498424035058490308001c2c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 366089694 1250 366088444 366088453
    0x607082809020a08010e0c03011a01050d1413210f0f090e070203120a0c05030601140f13060219050c06091516020312070302030f0d09020d150612080405060a020f 71
    0x3200c413019030103402c0410100d0252150144000101030036151000348040418480d240c41e1000d542c040c1c801031084007015400841c24552041c070201000008552000158203030107245000c201c801d007072030b034280031542484c5010001c643c0d0000304811103c51000c814000c050002c7c60300749010381d481100405a400c0d1444052401d654001c4d02c942060200001e4414240b000c921095a80e000b040d080e00000d54500b8119a40c08004480080c10304e04446c0d042e80c3c08101403880d14280c02d00074803103c8960b4140202091034010700030300e8940c100b4a04c401001114400000107000814401c000c00700498100d9206c00002d0300081440c80c41416901d00303624001000404815100403440429000700c00390350801110104ca01d080b44200d4000500503007007000f21050190355032000d0084480003140025041d80164040b98940f1074084003500c18203400f900d0101c4070450340c0143c00c00750421801c42d401421882e594810f403400355001c0c8030302c52a40131808060030703842001034142c45103440d81210b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 366090944 1250 366089694 366089699
    0x30e0a1511030c0a05090105070f0f02100e0a050919050405010501060216031101050d02090d061a040c09410406091a040b1c0809030607082809020a 65
    0x56045034802039580e80450500300c401d400c030000c207015688105210b99200389000d498650458444e4031107140141804000e00c06207011407000920b4000d510300c41c0c1c014100300d0100c3e0040003880c00040a071041002440c80600c030854a0f10404081110401e540241142c1c03240d072482c40f0002240700701d03098614640350400c000d21505400c050f0499030070340c003995402d054501113040382e002c186c000906000c80f0046480b815510030002446551040d0f040103003030071403181c00100c450150140c15282c903603c407009850382c0b4034924408000740c072048804104456100c0d1026001e03c1c0b40d031054802ca416280b4110300c0303c098404181c601201456201021069081045154007040c400958012464200c0c0896180c405115021091009a1090000e0000c1c0703020480601042c80d109500081da5100c0711020f04c3c0006246a040d610039494941ca4640a1042c0b500c1c041c00200318a04110390f2009200c03001c4141d0000d40b6094600501c011000c180c0450058084c04107524025002242d401c0d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 366092194 1250 366090944 366090953
    0xb010c24141b0906160c0306020301150e03010b01020d12020c0316030e06040e190e0f030c160b04030318030209150306090c060901030c12060305030702010f020d050708030403030e0a 80
    0x81d284034621180d01080a2403282d08a5006806102080d9400c80010410000c0900c4003100c10100d0703a00c00d0304100364907616a501c00f81641c000703a01c0391000411604102540c2900700062040820003034000704424244800000d60b600385d500f600d1014070400c41c1e2030017071903d40d40d0101c1301d900022808403a661980d80b90800c00c010008201a0000b800c03161040a1a1410b00d0441d002c4030840d10020100781c03106910740b8030002e5072211107080c50759140c041c0004030301c007800fa00c61b5030000a00510b4490350ba1028039820103800886007151100c81e40d509100d00e0000900b5a42900c0d090300e051000e031540429410492a00d82d04065400103c1d2030800500700794554203040301990541c16103a6a441e60b07604642d4540c020156158089410b0100104a5100e5403007908c030221145061b1000b0700b52444400e0440d000c0b0741041d1740c40c0c1c000254900655801c010808500703440c5100404000c8031000b0000c026000d1914010600325001000c00c0925110b60024406281140d059604c0044a440e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 366093444 1250 366092194 366092231
    0xb10020d211a15040f09020906190801170109080d0b15030a0903090509040c03110a0504140a060608070e060d09230f0f03030610021501170106090b010c24 68
    0x407152003200d5503e2140d140d110380ca070544084400c0c84005850385424034030381c10043c3d0082c0000541100741030048485103080400e80503144020b9445403455541042c0ac00d030700391a50806281c0503030703050802c01c80009003641d081314400001d48100090844030b40c80002d4071506034004820709550301009006910520f41d0102400e24880e4440d590313038594400c240010044201e4000d0700306c04544108001042220840c0314841000501501509071960300082c12542c0c4100c012240742004420807420031081d01c0748801420190034880d1103443e21140080c1880304416515000b52000311740b140d04100540c0100000b581e015800c100704244000300081a500c21004132203107880342208206c400000407402a1400d00d4403c0a54035666a250502800c2d2003514468011442a000101c1e42c00508541c1c00d40a03207440c3d40c1001019041000880c251086e0313800c08550b0502c2e00c64880c003103a810a1206019550243e2824031860342441350705070700101c1c1c4000086660a02c0309040000200302c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 366094694 1250 366093444 366093491
    0x619021606020f06060103060b0a1409060706050a0b01110619021903020903010f0209030a061a09041202010c0e010c260313020405010807030b1308040308070c05040b10020d21 77
    0x1300c5155a5405004406032052445804401c0c0d400b0030010185501c1101007044c43c1a04100c95403914044201203401a40000c1058034003076502d1303040c040b2400c200e0003100d142110034a480300309407125505040e21142c000c2c2c26001188074900c014072030b008090b01a518412040b008600348030342c1011014004e540441e0b0024840d51a1540070418110517101380c40340d40740e02400922075543d69545000c024446420104841d40c1640c003a5002583d5007212a0b108910901da41041a20300038000385c04d640c001d043c41030030f101a10004022903680716080655594020050080302c0300d102c6603050625034280380080c41e00c0000000c0000121032400c40284c07445c8255805c109aa0361400300c65100c8a07a400002c3c0504010400700b680d145010300c0c00c40c00e80c0c0c01200b030f140c03030a5500d90741c1c44107641c48203000b150b2040d00c12808100d24a02489106044041528015011800840001d44424071540c0c140184100103400c0e2201202c80e11810100e01034800c001c02542484105000c14201d001303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 366095944 1250 366094694 366094723
    0x30b090708010f051c060504050a031106040305030f1e010303200316061e1a0906120607030c02070b0c0102190212040302090601050d0510030c05030a02061902160602 73
    0x9001155065114150180c120340500c00314611150504041140d074488a81001c03203001c41c12031120002c5a00c5108443c0503510030402803031140704524010303102c801181200d0880d50010b10401011981185c200c86e44081e03100c0c6070002c1940c4070030242510107810101040031200c443c00100070141c115050080f0544030045010b8090b0300941041d40e44e1144603e150000e0b84e60703041c08000038085401c4200b00d0101140c2c3d001004201c140400122080b080c00f003105015900d06244c41d900700800450b800840946112628450070780d04607589181c0608031000b0590b580c0c0300f04420910912100380075194803000c40f0386c0c1e08001282c2601139003203804401c404800c3c9d0307181d110304140000307003103090f41000a00c1e65050a113560208210080d0007015241445801c01504c540d4080d00e116803031040c42444800ba0f0103900358100851800b1041c0c00450007503108a1400002d603551070103403030200860b00c400c020044610700c000c034200085200144448118142e002c50560b401041542456401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 366097194 1250 366095944 366095959
    0xa050606040f090f1b081005010311060708090910091a04050114030703080c070f03050313062111070501090305120c0316080a0e03041e09061505030405011803030b 72
    0xc1030b441c0000c4a40c80c41d03009100c800024640c07000501c403142c0d15101241d01c60503c80010b40e559903800d0400c80c8514809501d17075500c20040c42040912010340c03224500c140d4442d41020020754a081d03440c4100c0c001e0911541c65040000c0d805181034820001400304d608050140001641c5a482e9817040216280c1c4075600301030001c190f0141180340b400b040100200209400c030b145484d031070388942c842c1d03d07522424000c00c1c6c00032810000a2038420004c511a82c01142d541b4110400f203803041c08107400000c00c02010441c00003044007010130300b105214102c0b50000d1107981c25440740da203600c22820010140e50070144001c0616800002a00320001c01d5001c01a0f2a40ca0341c3c030100c6c803884104c80001050203a0f03a509d400042c862040c040c0c0c882911840003d01d054bc1101503855034010f17030301c01d9821105450b00c0e9281c4522000c921801044101018041142042d003020341f8101020413070000c10001000040a02070250099034408015420643c034a11244c02d00034050980152140e019000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 366098444 1250 366097194 366097211
    0x212010c091205120309030903060411100e060a03020a091d04051b10050a030e0a0b150a030f1101051b07050f01050a080a0c0c050102030f220305040303030b0d050a05060604 76
    0x4005882c00c0c1002e6106010b0010803911451031005900301401d040410300c000c0c41592800c1e1001c104041c0154095544000502031000411041426189944c3c0820480107072480042e01c455051700c0d282400c50401584943c0d85540c122400c0300a40c3c451004c84400c85c06142c1c8480c203e140c007a010380c0c0110190788044044c81d0030030b6850800240020f0300010301c0500c96a11030720600c0070f0802040b99190100d0713102000940c4501d06035107400280d07446680e400620080f80c002896129010a040d55265006071540d11110440d110000d4050502051200b005805a04c030340304a511000c2c525042d02a80d03d00301c541240c0e00e00342e0380078003030103485207a1a4a002d0342c050f00039503400c05100c1d82e130440c480c0d844103028000342014190038800e02c11a4514480000e4080c000f0314420644940291682d1400c2035203070920f4800032110f502d80308115200301001c04d5020f412039041c0c0f0b8144c100820101c4044c03001c40c01030381740e100b0050654014100d03080100034011a029001704e000f203405110180707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 366099694 1250 366098444 366098459
    0x1030f1b030c09121e0f060507020124050603041112010b040c09030b133305010501051204140c04240608101406070b010e010e07050715180212010c09 66
    0x3e07141d00800002006003c44800007a020745c8a965545007201d0014130100340b541d9a2811401c03c800c403c58250f503c1d0403c01403c6942482510315140469038040c0305041c2100041c002411a8001da60081d04000002030070b201007449051300c2c060000e041201d107a06011503290007080960a0741d407159092040c2034070501d220b84980416242c2040040c0895103880312441d003646415201210004080e640000265400302900c0340519001c0114030320070b00a038840301c811100140c00c128184141401084000d0200c540c4541c1c3c01540a41007480440c1459491b515041002c46c010354010300340403000c02000b402075a105502d0284008054015803921802d0f030350f030340302200e20341c0c0c802910f1102044500b9008500b4245003c0150034549800300f02d444900300c000098004200986076200104a503d20748090744c1d6100e0160301d84981410019074610004041808160900c25262078401926400f8900407000700f40e4014811540000143c0e43c660282100c0480c0a001c00c01c129800142c1c203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 366100944 1250 366099694 366099707
    0x703032303060604050f041b030f0f0612081303021c03080603010b062502130203070210090c051002160608061306080303010b070f08210601050909011401030f1b030c 73
    0x424000f415941824100701c148840c1c5d070799081d40150701c035031180c135011600710b01c01202e0500c20651390b401040c1c99000d88006410358401c0c556907142a8a001d5041180d0003911401040050344805200c4e501c044040044103001461340012354030240810a14900c0020110013a060030700ca07842e0380e035160703441400301401ca41900302859040071041000600c45066002000c1c2582da0410f050480202d00fa0040741d1612036103046819015400414042c03150b404216040e19032903d840280a12a104d0342d0f907040721281c40c4a03080c004c103072001c09041ca45000b0b010f6859882c882c82c6440750001e0b134520380144000d005a034140e000d00740043c6100022551030241100303440b0150011403444c5d1800071202c8a030b030711440003514072186e1100f1520008020340020481c044451103101852001e51a001d4010300000e8102418040300308900c5c031442e21200d40650468440c20b02c82c1d4041502c50700180d01500b0301c50703901412030345065614202e0881e8100b4400b0f4002440c5e030100a14086050182d03842c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 366102194 1250 366100944 366100951
    0x90204060c11190611010e0a0c09060509100b09010512070c0201080108030a081b0912010c08011d040b060415030c0f060f02150613020a0305040201140412230703032303 74
    0xf00d0588190074000d4901904902061580b040d00004220f6aa075003007a00740080c03000116101030300c40000704465409409110043c0030304584505003030402485190900741c40344641002c80c2e001040c03807412a03000390b0a8072100e00d40e0100c0c040301c900c1c0115001703103400c0003503808901280b01000045106500003091f5070203042c1c0c9465119240e25220b0380105d0129203a10200c42c03814040040c140700b521548190540400d0010010500e1a803100c0c020b0300074107051b004011a0700e607000803e10320248045025800035001a458209526860045000b034081702e9010445014084400001c102c1655901c400b290864540180303104d885240c102e40921346081807900686c0007041d292096040095151b421000c000c02d9000d2140380b83d4140c40036a0091800540030a80e1340e402c000079542c00804400b16401180c070080c0c0761608248124408440d50312024003200e80c24880d00400e0981089105480404801201c2066607686001040c3c10b00c40d200000414540d15198a0207030482029a0300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 366103444 1250 366102194 366102229
    0x3060a0501150804050a0c30081b010b090118050a02070b0130030e031e0d1b0209040b0412020601030302060402010f02030d24051206010b13090204060c11 68
    0x5546100d8084031000f80207441603030507010341c88031200044e41e801c421400805619404000d452101c00d04030881c0b00036580414900d01c42044400300080312501240c502d41d4642c036200740321202078440030340144520507015820804c5000041102004144880002d8100707003010300055070703030310312002c26802045002003d00d0b00840042c4080c20aa00b540b040803d211100621000f0070242c61030840191140c05802140c0c00580040140c14240002c4407100410202c03204c01e00c81601c100740d40c40260301284010451002d241301e807001f80c00011800c080f42c0041000b9041d082c14181072410360001e94088a82651744903030500c0160010480071304076034041d0044c01d902d40c0c1d40c0d00103650742c03003030100194110301017002805251142032091051004001e00c0300301100300314001281044036140c00061040c0b0b10409041414880002c1b41c07419079001c5851103803203529954640781d40f860203400001801c2d00102700400d100f90b001e01504002c3e8091960001850b0204040c00805081080840c0c2d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 366104694 1250 366103444 366103469
    0x11506022802010c0b0a020a1e08160c06060305030904060e011a070305070b0901051602011a0f0d08030405030702041d0d0e2106040210080106080109090614040b0603060a0501 77
    0x60060382200c0d0761905450041c10560140a25541c0f407000c0040c04880781c00c00d65901050703046000380e0010005000c2c903984490f403055201d8850001d0501c03034006120a954032948035011703d640303103d1421107400650040003888040c2c0c4034500507480b9000004d4241c0690b203002400140040701c00102e604a541d805c448410003c500350034218250300001c1c0580500a040051000140201c0d14a52182d4800070000803a400c080c1c400c0500401030115100840e81044510084072506a0704215100c0003142c10390b50034007040b4045244540c880c07201070070342000401040180315020000303100f0309208840803c00050003a000d218a044a946000711680c0940c51441c0450b00484201c044c2010040c640a400382c00c0407800715407080203080200454005805000031401e000d903809107002c0045c10503414540c14458000c007040c1c01481680c120945030030b083c00601034a644080d00c0c40040d03d12403e507518050822490081003580c055000e40305940006281500c03602c6021b05803880b883c08103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 366105944 1250 366104694 366104743
    0xd08040e0f0601050708090d0b0903070b06040507021e1e1506010c0c0303030b13060902070203010f0b1f0c0510090212060408040501050f090607030f020d0c0302071a0c010c0201150602 81
    0x2140184c0042e081180c10201c0941654045040410060310a080ac0801183d454046141c41d40003000042e00302d40c003a5080100b400392450b004500d80503003070006d00d005205036400000340b0f8a45078109000501845602046042c05900411095040300c1044c929040344e40350740004483c4400c886102410480080b00140b000900c40c0e0007402a040005001414011480468000b260300030303800f542e1144d500060700c0b021030a0a0041d0426003415001c100113a1445601095042d8206207184520805103c1c042c1e01d018003c006444010350888125000e0010992686004062501c801c1c0d2007641e2007100c0040c400c400064140c465075000765000c0c1050315010065803282c0103403202c401c480d6001c1c403080700319031948000340c4040c9002e0f1340c44c081c403240a90750203030038907400c1103500041080c0c299915021940000c4c5481c22a500a491044818403841c00303220366000e00154400c0302d50030304416060040c0e05400000000d00308002100c101c0c2d5888805a03650703401c44881d000d2070121007828 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 366107194 1250 366105944 366105953
    0x10e07140102031b010b191406130608061507061e1a09100504020706050a1805061f05090403020a0c060203090f04150b0f0c070f0b1210050d08040e0f06010507 70
    0x41d0041002000003c1011511140001d000c441401e807880c503080d03487e01040182d8000c0f83c0c0800c945640036103210b40385c5001e03002c1e980d500f840140035000612109201150a41d10ba000805002d00032a80309561900c01e20302d4140003901e503080c8002c0050328180c544481c40322451058003052003165841090f003010001c24414810001881030112103441f10700011562220300040c41c90303074071581002a803450071400e40000c507003076180000001c08100ce1408001603000410f207401c21004940703000002c04244400c1d065088580145401c010702c0001d00040640000c0c2c28100d0134810655070380c01030703160002240c0e28001e0f911540e03400f8442e0080c22900741010340c81280c850081d070f003900c2d013441d0300c400303100650764082c0143d264074003000190380c264070f9411f00681c4084c007408a030760584035140844000e81e500070b0409840d00d42c03012401040c002781c0c4003100c00e80200806000094203035030340d04200c4940e8025124510318078100000044c494070300c03180e480d4460318058691a0a100040c0c44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 366108444 1250 366107194 366107227
    0x50901030902030f01061805070203040302010807080c0f07121707090b0d0f0e0319020604030503010501030506190909030e090601020d0c0501060f0f05100201110f0904020417010e0714010203 84
    0x4003a605401020b4202403101310130f0142d07001901000d140c0e2050042030f0b10155045510080036441103410611080c80182c0e40426401d0b04000103250041d50394680007400c0c40d15114042d81c00c030f000f400001d210000c106000520fa8600101d54030340c0c0c0d42030040d540e520003201c682107c01c400082c6030140c0501c040c5074580007421200301c040c400010000300f05014842200c110111840c43c903800811190f218a004001c0700201c05c0070307031000d080d103420150740141c690302040c003c15060640768070000c1c0440d00c840490916140c6402c1d014544c095881200c0c1c0c0042220402c1540015508201e9070700b80c1c00c100ca242c1d4010b1006034005d0280141e406411103075091081c004481a5488040c0007495440c0030116501400109a111008174540010800d41c05140c210460135641019610034a0107018015221920409029541e4031441c9800280c02882150041c25031f8804004103400a12015800000320251943c215031714187c41c0d1441d0311001e040300e9869801a841046114050003440d00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 366109694 1250 366108444 366108461
    0x90303080a05013219050a060504030c121401151703120a0b0a1208030f1e01031106130b0c0705090c0f1b1906110a1b020114120f0105010f05090103 65
    0x2100b4001004c1c1c1140021004117403200f01c0303c0718004441c0240b240346458000c4600074441c50402d103140501d55956454054400d100d06a03200c03581c08490000c1c401d10000c40c0882055000c0200180c1c00600da0a40076800c041c00f40c0c1021450020b00400303060f0b0008211429034880c40498401a552105c0e5034001d40400b0045075081203403c1d800050402c60012007a00b9071f889554626203d20b0820311007001280d00911200e08a90746000c080305080034102082c0c1580d40018204000c1400c52004c518148110b8150300d903074010030100041c01044036000780403000b40540c1a0707582e184c0e032141041462103041c2e400302c00e8205c0410180305007070341c0e001c005c000c111564035100c1c1401041c3c50021b0b0400608000303103003511000c18860010000071340b00e030208401c51503507500d0030120400d80060207032440e0000307000045951020441075a0040a00c204480124402c1550300d000b2040040174401054507001901103c0d0400401c1940c01110814110300b8182d4800c0d040908110044010b004001d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 366110944 1250 366109694 366109769
    0xe060123030c07080a08060f0d0f1101020111161a040209070309050c0d08030709060f0c140709020a020a0606050901050906040507120c0509360901021603090303080a0501 75
    0x20403c000c00100c114020342001c5006844801d80b80c50442c081c08a40304203003542c544500a019140d00c009016404594003041e001f10a01104841c9000182e004119954403042865408241c4804400c10444e031000039030703c61003210780030850a1110821a00c0e091720b0081d4000000c4000510403031295220744030702c81c011421901c40c51140300c00b0607448802c0d44010345840800104021901c3d030001d28441c01811185000850312400010050010702412402811440c0e00742482500c020100030002c003401010f0300865942040c02c17000380d5036030342400040302c96508002c0001039614020040364101c1d180030701505c0f06661010100f01c01030900401541c103001010801148a00e1180704010440da1b05803103082da6406840200184103048500d100d55045589111410034122100030048450010742c0c4400c40c0d888101d5914064005c6541d9101001031403030316030b800c0c540e1021010003142c2c040c5e2144903203a2241c01a91042d80d0003406011103500070f0001407604c081e1424840301d602a487e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 366112194 1250 366110944 366110947
    0x30a0812040302072301180f05061315020312010608010e07030b0301021e09040f090213020703020a050a03020d080702061303050f13090b040b0904050d0c23070e060123030c 76
    0x10b0714120070141d4030141c05c0d0760200c030804090041550304000b81d1180f8402c0c90818583c070303a14001070031003079440a001e00d9014820120b500d4508500d81c4070600085d0180c101c010100303040810009580b03800107003203030154489180002402a0003503101605a4840000c000226500d5600590240074016659070b00356508001c08080b64204503290440141802c0155555007109800c200c10341d05d0808940c1c5440e85880c034040300580c0d80e0008030380004200304002d41c0300d44080c107003a8140320f144080600f072401400403401c100350b07010541e4018002a03440d4401c0b5500c4441040740e0326401198a4800d0b406002d00d0b11000c01c2c000c10240050508118001d0700d44241103c2884141c04d003903101c0c500064940000007500d140c6401008225102610860740500e425103c05a80c0c228103030910061110fa0f020b52001c3c41921080c2001560f002d46407260721101c000c03070150355040c00b8800d440c1080201404160250312a200d05a00c2a074032211451380c00f00b14004600b165070003c1d0900c0f180180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 366113444 1250 366112194 366112199
    0x709060513080615030d02150a05040503090604090b19050918032208060705030c043308040b070504050303120604020403061e0501240309030c020a1203020705030a081204030207 78
    0xb00308281c601c0784d005001c86807101c1c0452414075140c14940703020701d01503400c81c11864010380c8200f800715602282c0c0070400f00f0140c840b400c00f28103502ca25085150094400140400c0c45d054a405ca0040c00105a404c41880d142c403056151400116000c0c03150701c51002c00200b00c00403400d42104041d5403d1205591400700785601012a401b108011010305400e0141c0400034140244000366200c8950300f042d918602e04065174200c50302c5070780119080c000049040c444001043d0560b62214405200752126110307407060003078a001c0040300c0441e60016004009860325111b8400d0700c1c1200e40240086040005c60400502c1e054801040c80d6003040e0300b40000400320b5954010310303e4840308000b618100e82c00019420080e600305801c000005c03919124908a6025080381c1811030342d03803d150002c2d01c0b074540d103803c0f2165402070728065445248000c0209145540c08042d00e10f241c4240c00726020180c0e1356081c15140d40c1700f0080030300309a9061099040d039020321007149500c60b1091058881440c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 366114694 1250 366113444 366113459
    0x5120609151e19081c210603050d27060f050901020c09040303150f060203090d060f0e030a0215060915010c06020307050a08090c031f020d020408030c0c090709060513 73
    0x540f0300034940004200c1c0008005581081c0301500d50310010300c44176220190300c40d401600b04100c248074a243c3c00005885a910f0503140d41c005006580d00c80b00307450004902100080001440c03203603900704400c42c5c2010280080702070010404441007902c0340c4002c60310b01182910385400082c0e4185c194010311140362002e50341d42c0030081c4541d100c1e8030300143c1c0101140c12030380f000016401c040303180759101a0902400b90000140e82c640e0000b22100d001769091440c0030030141c03012810300c0c8600740c1400031074131683c9030200c041c01c0c41c009030764200c41c40c3c000c00001c110110b140a440e105c1d08200000c0200317410646c803208107110b10b0010304000201d481c4030365501c0220307403044034400005a40803070f401c041e2950044103d07801c000c00400400c2c165a405000136100c15a500505c251400424a4000070070751a80586200c203801d48c00c00c54850b40d0300d03640140c99600c540da0400d1140030700100480b480c07400480550058055a480100c0d25050400644d15640000158240c5a0001800143d403c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 366115944 1250 366114694 366114709
    0x30a03140c030705100c11032d0d0b010f0309020604090c05041206050609010f030209150f060a0206040515040f0b07020a12020a020111010221060f0901030305120609151e 75
    0xf601c1a00245000310001c1c00300c1c81140d0041051504218070070130310311400b400004c143d07604000084103080200e0100500c0d0050107295400754000e82c4c002080e1556100c1155000c00c00b003800c01c3e2130b420b1801d41d05c860100d08840c04d0040c003e50189040c48180a80d5555a003c0580f505035801c101e03183c20784401c0d1804507410038010881e1459241c60030001c80e07040092800380105200c0c60907985003820743e4002080c0c044003e00074000f03604140000d10071551921000c0525000103460700d9030701c0da11690001c1d00c400d01200d06840c1c510800100b4400c03002d0f9801c200340f01c0d0b034008510f42010150f03030b6507209074124080e008400f184030310751103230340400c40d81c4170460b00171100c036001000c0d035035004d20014119404500028610342d2051048a0b0f00700c0003807400c020307200c2410302e041040303580b0503001a084a910f41c1500d43c22910000012040641090052031500301d40f41201c0c030103540b0b0304104075807210106d881c0304004103030035612030180c1007240e4800c180005c0d4224a000e0b02000c800420406c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 366117194 1250 366115944 366115957
    0x8030f0f040911071109070e01260112050606030303130f170f032d0114180c032e06030f0e060a200414120f01020408010207150b030a03140c03 63
    0xf01c4a00003451420007641c82840c0c1c055120a46140200b840c143e0710140c0b480700364403880c0381401010294440302120342c8084400386612100080690358446203000b140040c01041150705102c3c807c003040844c900007055078411035200c84c0d221640b07241c590b80c1e4105031014150464001907618448400344158001500c0340380d042c41c980e00d4a91410100744200c00c092283c444585100754141c458009040741d10f401c0c15140c03a590005020600d050210303400449955500c0d080480e58003c3c8490741d004c600007035000d60384d8403c24240402403040e401403400c102c501691003103040c06108110345400707608014409541ca0b54009260160300b408541468403c660548801c2d58909450300f41004030307000c0c120400c942092140c2810f06040c60f20303408180c440003040c400c61a440110614610070001d41794112804802035407503035600c118082c080c0d0011340b021944030000441e408450b409511605102190040041c16010904c0e10161154070404c011111040010842c4002d41d01c4208010b010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 366118444 1250 366117194 366117221
    0x2090a0902042a141e0d050c0a1b0c09020c150a021b16151b0b06010f090b090402031308130311040c0e0d06020f040303080105041b080103080a03060e16030f020408030f0f0409 77
    0xaa0300c0311513000600c8890200c3e0940900c08a2b0403109010584032403540c0143d5004140042e90b42810f004c29602d440c540340c0007500f40703040c0401040880d074203c2d0081c1400c507c0004c0c0400b511412a1082c03a15501ca80c1d110307112283c401401049003d004540321601e400c26414000755000c8015608050070702080000c1c2d84c200150030500245583c410000b503050300aa140c014202801c10030785941034030415008038400c039000f001258400010450200e1240d511646d01075840c8014a40402e03000700b070744020348220554054103640343c18580110352002c4100e90314021500a03500c10055051103440341541c01e55400c0c01020603002d003a000605c040d44c06031700e82c07018644c504020003007943c00e4441510049241c001c080d810980d0040380d603d054951040702680c0f102c01c1c00b00110014a000c0e0b003d100c1c0d040801e01403108007040604150f07100c0034030365020720014508007015020781c4980d12a240c0c1d02e510420007440e00d0044200a00304c3c0030f41800555140c50b6507420200d050720140055603a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 366119694 1250 366118444 366118447
    0x2202060c011a040b060a030509070b030405100e281401020d060e0901060b07080307050d090804090e07151b1403270d02090a0902042a141e0d050c 64
    0x40706810b015500110000b07003180c05201000b01c0102280950180d003d1040516483d24007040c01a0014000d034006400d490414a80781c0c902820701540c0c0c1d2003c088030a05041c68046000d00c5410042440000f60500011744016024001214540001c00000c00d80d03801c083c90600d0940480c01780002c11804040d038202042c69800c0c1515110602006081101280e2402d002002007014810684981d20740000ca40c43d100c0d41c030000261428403418409008181c5800312003401c2020841c098000c1e1881201c0400c181c0c40c0d000e141c0f035500d0a080c01422000c0810f0001c02420600c10380076558140d00c50f1140e018031001c1c50791000c0f0501d541940c0c0a8803030f04080754884100c166220a070884015401d1030040200003880400e03c64105180c0c042d00507003000c4001026090260030058190f0307405801000f40701d9090005044151f00c104141080c0313480c6006800c40644120b4840c24689104004070b4500608800c841c0f1140400c0745403880c0640c1e017448860702132851842524803900c90f500f000c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 366120944 1250 366119694 366119711
    0x2100e060a0e03131406071a0417031b1608130e0702030403150b0f031b010e0d020619030905060906070909061809060e030a0507020a05030102030f2202060c01 70
    0xc00c00d545258100c2c10266009000c851002c0ea044a180310480c0d40100360a101302c1c14240c04a010f51144900240034000d0b0300c0704c00310800c00c1040529100c1d9002d02c1e000c0701724440001c01c047d120310042e0759a11030003110500d9a04402800b00091541e81c0b071381c400300e5510780010380ea000f6054014007100c5011511a160230810600d880b40116030203455840070f9071800b4119a10f00c01103c0c1c0680c0394004160343c1e40302400464548520510a03130030700404440c0b10b1b4815403c2c038480c607100c02c28030f103000070860440d03103445080071503134000700a9006003820708001448001040c3c4481e4204072004068a444461003c9001400814040c4661602402040c0b500c1080507144810740d9200c0126146444e03400c00851001c0c62142c0c120301d0034684040b40101e8181014809419039080e40051070000061034803c06402800400d22244203070f400c6403038030342d5460401d800c03030004403000028070160400088803641503540160580d0100e0052100f8000c44c0d03004118160441407807103501d070390b540810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 366122194 1250 366120944 366120961
    0x1210e0706080c0d09021804062f0d050a02070803010e0916031112010e0102040f06090e0103020f010507051c030f0b3304080d020c01080a0c050403020d0302100e06 72
    0x214000c0c0038681000b0110382044400007810307104140004400540e14643d04c1c04550b24100380e44810040300291080c80d0400f0300b4600018501a0710065159003085020390f148a10205001000205880130340c6c105803015141901920b4003c280c110070315030811240b0006510038014601a1005a00c880c02518040713028607d42103a02c080e0790030000000030100000355004e040e504040714152807030b00a941c07030424958090b00c2c0302c2a05091a50010401052005010203208111142c0f5a950018075548104103203000c0d1083c0002f079000032028500c0c000550140004004152181c1c04451648128044504d00681c011929034002030b1280c02d0800c0c1c001690113803941129049691110b02401c40d0303040d0b0440030f021262816101e001c02c9150580591900640300104044016601941302ca480c0094681c1600924103000c1401440810039490b802d105108001c1202e45603145882e00359020130600d81d0b20780340f080b030443c400e111008810504500a000507100407030000d000d1401c20028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 366123444 1250 366122194 366122203
    0x309064509020301030b01061b020306070e0307050103140a020309121201140303190e03250306060b0307271d09061e060d0201030b0307060c0303060b210601210e 71
    0x101c610100d00500051011400d6201c1d042c5c112243c43c1040c20a1080040160340d82180140029605004600c1048940d5810440d448030030031049040e684401e031528019422070b0a19201101050400c01c00078280c803160383d0086400c44c0324102191100c08002d0003054541e80300005d03001e071084c0310340c0040143c180254030300815040110059401c3c0030130030340c0521806030401c4c0140100100144520410b0300c007445a101044101351950080048501c03030031041c491244804c4079540d1030103500180070050030095a002d0321240c0e58203051070442107207500c0800e5012010101c1c08036440000030300030401c10102500d40c030145c03c07112440d01c0d0104501d8180403000b8004040040c91500b098440c0c8040c2e88030a5001d0350807120010900d12a0004070300400c1074041c0260188603200c00891210b03080139424401314860743d01440499290f140e1000f007406143c06910710b078a118002003230500c2450036000c0d030040040c54544450341e4400c0c80d50004043e2006000d452980d29184518020300901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 366124694 1250 366123444 366123449
    0x5010f060b0702090402100e0d06050610090503152508070e060405060f03090304031a090601050414060103091406010f210f0f0302010209093103090645 67
    0x204514140300c003540201d13102c6800100000c5c032841040071420805070040c04c030040c5280c000742082043c0400ca103002002000103480ca82d00c201400c40081c441107106002c0ea40548501401034014105010f4130201c50440160a01c0100340f03020480741c001b00040314981a00383c08a5170703407001c0c6003404d0901a00180c215801c02d80548401c00c0280000e4403204221400003c070060700c695665900140c45055009580006000303240050001c01c1014031803100d103005c0e0803400b00b9550b940c2d0384c802c00c02080703503680c461501c0359000c040700080c038640c0254410315400b40521250082c40302200c11480c1804801d07041071080b07880441c42407104106406480c00d4407a1000003804140b0319030303120076081c5040c41200602034002182d0000c20036100390182d4554110140130300070740d402d008003e00301004d00801c001a090032004a4850741416004140e16000e8141c1c0b00d810269052030001c0f103d0007003103d05000070a4152403032481e079405282030306000c6101d0600694501d000c41c03220004200c220b6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 366125944 1250 366124694 366124709
    0xa0b2d101d030f0106030c18050906060603040302032a1b090402061c060303030f0c0509090c160c1509051203040506071a0901050103060b0d051005060a0f0305010f06 73
    0x160360180001e400106030518034151000c608a030400c00d00c0000c0ca0184108084030203035090440c0001048107d001c80d100f41c50350f144c006000b40008614110031a00200e598500603400800895123a0074240015a00f1030b0103841940d01c2e00360007601d09604c004001508501001c211050342000720824802c01c0001d42201c00311505800801001602075a005000688244400202116584080000282007100c0d200003485240d585e8140540140306020015178110b003817080014400d0311403002c4039000741008224481c580c540034100c1c0400d40002c0000303c4502c0f0160302c01400b1401c9061460014401d0149405a59001c00b000601c145a50752101d40181b01811100040c40f0021080d10150780d010f50f0002d0320349245040403800c02204207200c0c9000c403a008103000702d107481034020b82d040e80c4c0240342c140040c94a500c14040345601c80300b809001900001075640318202903400054120500030400500b19031294419405400d00351310803211070b076480c400819074003080d006250081c107a4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 366127194 1250 366125944 366125959
    0x60503160e070201232a030a0b09130318050d0503090414090a06020307210c0f020606010504090e0c060f0d0b0102060402010c0809210102130b1905030a0b2d 69
    0x226144101c170013071300740c1c80281009020800035000c0e0f141c0c2c4408098400142140c01404036a81340c00c03441561081d180b401c40141000c030121524101280c0060203440d001d0003d010001090f10300b1941d4a003031051005052070308440c0052070f6655112031040040c01400519070b6804542d0810080750604078241032000090010080a8180401e01d095074640203c80540d0320354a40d102141c04100d440d01c40c820511402030070500f152100d81c01908000c6807500d426041e40350484060303941c1d101c22070301503000400811042c8210340703441d00300000000b4490b003128202508100001c0c110b41113002c164180c20004208091090300718002c001e00ba00b1b00f07002a11541c03c054000800009010901400b003080010320441d50b901c480b010400c1ca100003011440410000046080c041d42c0f1205444040c010a244045992104007045480039640100a0050b0307000c0f0b85402c0e03540d07400003015a4100d5a80b0800b22686840d112403d0b001052643e81c1000c03400441e009105601e61000a03490080740c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 366128444 1250 366127194 366127211
    0x108100501050a060e10030e070e0a0e120a0e0d050717060c03040206181f020304181505090c07061104090501120201082a0705030306010306060212030a0c03060503160e070201 77
    0x8012559001034a004c1d50500d12003500646c0c1a00038002124402059100e240400030b940302020b200140501c4a015090060241b0358500e02e55908200c4080418500100058a5410301902c3c0413a20a00c0181a4024041c4140c07101e90902c2080d038000d2003801c0c820610125401c1043c0891984840303903000590550420350003080041c0a103080b404a40304c0c10210480d0356a9038842c104104240360036a91920360000717a4000d4482d00244502d0318413441071886140c040350f06008044ca000d81495085c1c2440d468007080001150010f0a401003643c01080120003198143c02100e25440c1c00b4002c16580c0d6150401c0c040441750160b000e82008000c086914005030b030b00250701071f040001a48000a40e1007a5246510101c000329041c010401c8000381705803c01c800400074510540302620100a4695207500690b15070b04908150f520fa9001040001e484007080d03449141d0b20301140c0b50003c1c1d46a203c001007450310b0200d10218001001c0c0c070f1010082a8911000b803540000984002e20a000c4c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 366129694 1250 366128444 366128447
    0x5030706020606130216122c04020d1b050a090608070518010203040503010c084606050a0801020d1a030a030305061807111c0f110a0503030108100501050a06 69
    0x70050f03e214424079244002200d03035052901911940c4201d500301202c11400c61404001100349400c0c0603010540c46018100c00b4001442c80b104001241d904450103000c0500801c030080d400201d940e00816640c1c80c461a14040341040c80341e000072580c1741d09560f004081009403035600203a114004011146042000701984038066034002c0c100d103512942d402c140030b40181d046000b42d8101903090340c42e04445116540e400f8110501039815a02161194103101c03102c030580180b641c1000500d21040c00e02c60b0b0b5680c003400f81c840c05080c0c161500140711030b280d20000b65203d503903030b00003240c0341e4011075540c46149091098200054003138120541c00031205000c25100c82440c5800750925540303400140b102d450342909140d07554680100300d0820305d40705201800e000c0100c080c90006106801548003030521030035841d1800700b450340714000d800103450022a0003002c001c204c6020360285500440000754200043c501820340d50f0041c0400860040020f402c54505920003441078007040e10070827545 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 366130944 1250 366129694 366129703
    0x10f09050c0a0507020406150c1b050f0112180309180b0a12020307030c03060903080108061e06030a0b070f0e06090a030615030503030705070201030f0504050d0f0908120406090503070602 82
    0x5403090f00f4040c0d00d40c1d0725400000c000341a20360060110b0704901c00580c8450768081ca200035098414103c4210031450380d080030088100c0760141582180c812249047e1560044000c80d0f20980394900201c1d003c1c11400c6481490780d01c40d001280403075240c4d1001e00070b20039a517071051385410109a00300200d03c10322001401000241c481ea4080305030b403103625403d6485c01d01501c0301440d000320700274900c5541c0303107441401401e075158160b0000301142c002040050011030f00318000c6513450b20000400b449000d0f200344003a005017481c2d9152081414440000340c1e00d80c0502d20822090316500311003420712030098800603102e007100d88221410490015a651104404425070350000c0300010960a400ca00761140c0c010b42d0800760a0340b00c0403041001c01684940100100d40c403e0341c0a0001d1510b400c01c10041e510181c80c010700c150000080781400c03a104035800e240e018882e00c0d00f803000b00d80d0b83d10301c1c40c00d00090003510600302100040a1090310b4106000c5c0000704000d43c010f00c2000d1900030001d444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 366132194 1250 366130944 366130957
    0x10305042f06070f051903091406040305160501021204060c142a0103200d110f0409050405120415080a1d0d03060905060d0204091a090303010f09050c 66
    0x203060150801c420340d124203440c4038041d400c000e0035a0b9030b01d0702c40c1c2c140350000d02c460b40130482d114858000703449100d039411142d0001e61540758540f07841c250304025a4800c0d4101d04080141c01900900c00080800d071704101c00100000b2440c1c5002c82c140c1480002400e10f18080920078048000304030802100ba40a040b4403c00c58000306100d0b0031a004d030080d0350900c066100d0282250b20200465003a00b110040d0848804100344c80801c0745c030055184402440705545a40100d2100038803c580004000f50030400031040151450b03440c1038030b010440811500503030001e040d105d907640308100070060100082c201c8030311404842420705281180300401c802c9400151802c011180c000b2600b4a040f82d001601c031001ca00a103520400c8856210b607644441010b510000641011400502d5003094490f01340104006054000581d110b6003d10014100c2c844041312603c1d0030350b400d400190006502d060003080c5000c09107a41f075140c285030341115007a507088200e4452828051003001c500a108031100e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 366133444 1250 366132194 366132233
    0x3060709050315060f030a0818030a0201140a0212131406070c030210050c240604150603111b01020c0d021c0c061d010605010908030c0c09060a090608010212010501030504 75
    0x100c40d40c4d80304c04146500e41c460034003030301482011042e8003046002409414061354580d810f21902c040c043c02c0650701e45d4007a0029011503041c418100c411000e10009280d81c0380c2600450380071862488011180c2d500c07080449915180e805020b000d280650005103c101e00106c80030b41c1420010b8840c1d502245140c40b00034482c2041c480640d201601500907200040c1c1c00300155008038003602d09055a44043c8070a001500d000003001400b10728241c420381c903d441b611000007000504048080d03004018192081d10306040c240303c41c074070344072110b018219070080c10800075031158502c2c0d4406107091560072611b810340d001018103890291082d42940b400c2c181038500340c1c16a1016050020040c100705441c00303000004101100444c800c150464411a81c003a62012134066644555541301d000300c2a4100c101e4014400320b40252420140742600303c40001c0441c200d50f582c0d610a0422200030358404400c0382d4001c21502014110700c00070600400d820b09060046103419904c0078400d103005100640c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 366134694 1250 366133444 366133483
    0x50c090405070917060f090d021e03090303130f120b0402150904021801020708030f04120501060e0405071e1206090503131806091e021e040e06030607090503 69
    0x8442d148109058001041540d02c032182113100c1035009601c07454100d5540c01d1301c034618408200104400a1600d00c88410781d80500840510344807220259501e01031000c9051000f4000040b0655090000700080074284002001491070400491400c06250b4842d00761208844c0300003003c09d40e080405540107a0407581400000410044128540913040e0f0305134001c1d1005c90441d40d40342c00c01c59007448200c0301340c08a030452a6990011981c030b2080740c7d04501a010300784000c00000c04010701d1116405e204400219959440d420707441b40c0700320200c40640f420303400390504211400b00402e11050454400012001c00707810b003280420402c203000c40040c4469500c407101c00c14031030b050050711101000e0420700030400d40e0f01c0020317514030301400c8003814050340b40401c0025420154441c2d0550100128044a081049200050000e40141400c401042004c003a9841d07035001c8580100301420440d8210120f03410034000381490328500401030414424007000500007684c00282d0807405005400c442d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 366135944 1250 366134694 366134701
    0x7030b071103180d0605010308131509030f0809060a02100605041103040803100f1d0f04050d0810030602030106120c08040206090d020d06110702100c030f05030403031506090f0504050c090405 84
    0x59504c0700307505005043c440c5010008000c000d88000100b50700140f6610000103540c660b5000010240e01035529400b15030909403c000044807a665001004d004058680c200b842400c08179429a2103c040f010058100c0070030700e40001242e10400000d030005503405c10101e10710360003020803444058400b60040c00040000303071900442d02d04440141c814940e4080710581c0d100500103c041c41840103400340608880044c20380d41c0c00c4040141326503088001001c2180e02c00300705555401000c1d00350300380201d40c00d4000c0003058541c00258000c0159a4400c0310300c1c8012004c180464a80d5201c0c10204074019003440701513501d130401e45201c0e01d0200d6050a221107241300190056184000081c80300c1e0030300501c030781c85015910180040034029103100b612a00d9224040f1106101392900501080c40701c100c140a031841400076541c428401c0c24001100700071003a0603c1101c1d141d50084000502944c1c2c244900003c51044000a0000b51801e0016060064404c5454055214094001c17036440001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 366137194 1250 366135944 366135949
    0x5030f180c10051e0903030403020f0310090f0309290d090b01080607090806010e04030503070e0409241515020a0b1e0f0601050a080907051207030b07110318 69
    0x100740e903180004149407416602810007a1594001c03020030500d206001c040c201160100c0c1c0110b511034000140a0b528003815a070030000050108406d40341c147c03140100300745621a4a1041010306801303914040d07040103041c03030000c00c1d442068009030000c200220a10f00c20410071020a052000f020301b0454035031100b501507a0090100140c040c00010b4a940005100d000104100d8007070f03a596580c45070840c0c2c8940205954020a110740b40b41e0031498000200401c0c8282c01858200c802ca107414101c40c40d508000074140c410888040e200503c000b400840100b40c0510328071701c1c1003040c8100380401c0c0400c80074002c40c40b2072880b1319000001290440e01000b8424018150b00d194065802c40c1582045407111200d0480791031700d1200d24180b070380460700035180000d055104890581d00c0c98500002d032201110b0801020300a0100f603c5203070b402045035511002201030080340d42005142c020718600f00301c0d10f54100070700241c061101c0c0400910034098080201e9039410310790009160f20102c0b8001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 366138444 1250 366137194 366137203
    0x50c03030703090525080601050a1206020d0609020d020306010e090106020a0807061b080702010c0e0a03110d05030a02030c070e04020a15020f0106030c0e07080123010302040e0f04020102070605030f18 88
    0x1184181c403070300b8985030206191440b05c155949001100c28580e241e03814409004034601803440e11b00040b8164000144c815001403040400c06000401c070195914901d0050780c202691244100341c0120401c546540e00415689004804031101000c0d0351402e08042d40380c0f10701002c00782503c2c03c005010320502040b81c0021510440100c0074001d2080500f00c0201441000e03145407005509000401c08102c0c401c3d003001c422540010901c0d11101c0c0795075100b0048030300340d140d03568014035a00403c8010400500103013840c6c45d80c03500996580c40c0d03060702b42410901aa0424030811007014280009610380291441c1a642c4801507003050007404102079181000c4071440c20303059030900d6400b0080106030000d10044800351401052b0321303141d420056803141e8090140000c003856600c80440c44c4e4030404400203103402e040c1401032030541c84408450240d141151407404c0c03a030f40b1000384821542c3c104095401044189005030441c00d010320008500d40014110311941e52203c00c80700314440e420302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 366139694 1250 366138444 366138463
    0x90b090a05040803072a1a0a0603080307050c01091b1d09060403030518010c1701060e030a0821010308030f09030301080c010f140a0201050906061c2d060b030d050c030307030905 78
    0x211240c201264914000d521f074036040c101d40401c3c2010b4000718091411a0003000107aa0b40500c2c09800d41d0741d80d60003220306812616160100c1d40d254001480462a0036101401d50b951401480c0945400d010240c9220200070841010301c08200c020070064900100c0c03c2900076034186004686030320341500c0e0781ca10b010001100d422a510301080201d1064111304100030800c0c8209100803203a03611f4400b900c0e00d28600d07c82d5605070704132401d40000640700314010081280c2c40f0f40d0600070341d4142c0420360039030f0800f600704446449002050100289034904107a6001000000a500d15810040441d441d040b01c0c82c1c055050000500000c141340b030241407031445032000b5801d4a501e8030b95451000307001c0c1c101651805214041e200200300181404101e0904144505c0c10302041e1151954802a2003d00540d510303000104c3c0601445043c02c034107010f00740300b40c064003001c20710802483c02c141c1405100f050342001d010081110307001d58040401981c0d484842802e00103161551400d15504240108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 366140944 1250 366139694 366139757
    0x120906120f0604052202010f0519050705120c12030901021204061a030706200102090301050711010f0501060c11031c030218100503011a04030507090b090a0504080307 73
    0x80200311550854120386032042c070341180e0510150f1152004000b00700084042c2c1d0130350500d40c3d80b80d030000d940182c602443d007031560701d05145840c00c9205a20b030002c0c020741c40c1d580090400100c0744113001c010004000611104410f01f0b280401c0004801e80d240c0030415106800000880010304c20802175040d2038004105200c405c2e083e20b000d28041c170081112404e07202d505c00c5000b5034188a4180021700c0815546543c0303d500c0c00c84d94540210840100c40349500807159000c1002d0801e6403070a0040c58003610317150300c690100100d500003040c20755101701d107000540b0746030000410450b40c1c80b105108080d0f0b004032200c0040c2d941c00c0d010030f0402056002090490781c1c0318000380d883c1c59240d03004010022054030080c600c507824104100511003c5540175000500c14001070080210010b5001003c002c1113526a00e80307075481ea07403d400c02d400c07584a4002c0c030396111518011800c040d8960b40d0701001d0303c4410022440e096440c0c009900000c0c0185081000d0710000710000740c0070100708100c80d40c41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 366142194 1250 366140944 366140977
    0x31603030908070b0a14070f03090c080d0e0a1a070303240320090f04080c070312021501120309140109090213030203010b0d050d140d09050f010e0c03120906 69
    0x1031309198421103010388034405120310f0211542e0f40e404490a000e80100019690402d520701850130444c0a004010b1040d030f00c1c11582100040e41c04000c00c41d000344e600040d260301044042c0c401c100b20208030581c0c844030b0680c00611101c1702c1502000215406c142c4d044c100010f807040b000302e0040740000c5107428a0030038804038501100303001003810070501e5640030b018501c0c000d4802c20700b8050030341e0050b1072a01b03068000c800400c0000f40c42001800725219500112000c103981c030303140c045207107800e81c071400090780001072035100c90f11501300024050000240341c00d031041c656031b03002071401b016841503007198182840641c105a04c514502e0008002d0441c0940d00c400151200100c5680b01d440201d01c40d620300612412181800e0b95605140e94018002c0d1200050511095912130a256922011035104020802c00d9030464420289804d0042c00180201c0e8003015074242100c2109008101e154024031200b0000c3d0780004103044c0d140482414103403034029060125400d40280710703801506214 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 366143444 1250 366142194 366142207
    0x602070501141b1f02090a031403070b1e01060309030203030a0f110414032503080f0415020a050105010501080610200304290f07140a140a03090512031603030908 71
    0xd401500c1380c07183c00951240b041c01002c0c4001c82c4501101c940e00014400d0040002c5160b215024806401d0300d0181c0b450034040391340b00108203501b19944000380340904c01c00000000740101e03050150099040410000e9680d44001e560f03800010a080d42e0300340c44401c81c689035100750b042040d91065203690140c40d151503040c0b076150710301e2042019010307124889407440d5103e00d644010b1448000510001d08460458807460503d50000c441201000707400c10000600d2802c4070403140280070340b030b8054161302420349442425190181e01040c10440b140d030500040d40d45400c819014020981400030036400c540e0317030b0071b55040002d030046910390102080000d4a011108143c0d00242c42050035855254000900e00c520f030300420f0001140c2c420f040c000a030000e409070041691445602c4100c900c1e004442c0d480940e0070559181c01d2101c3e403c811400c00415800c112200068082101c04100625481d100d00d80c1d6802050880780d0b50b801540c4030b80041c50b000c0d50080c0300003900101101d40d20030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 366144694 1250 366143444 366143497
    0xc03040f02041b2001140115210605030c03010b10030b0a0305060a02031e07050a0302030601051b0304060f0206061c020d1203061a071208070509040f0b0f030304060207050114 77
    0x81c4690f4520348240d03034294a009841d9130601c50641071200c18815031007145d081060403c00602034008200034801c1050210003266002d884407070110300a010b000c40c4807810003090500b00188002018000c0e03040c01820111640e4030960038020081c64900042c080210074009028124181d20142180c06900e0070b0050000c4941c00646c8a122900c0e0800e602200c5030100010f2040102c0711040000d07820b101407294584250010b64105505240880c00d210301896040182c0b045480c511415610000d4200243c0e900500b1a040910313a03400501104e140c01d501007049400407030754221041c001e51000804550712804504941030304280c07060200812120081c00070880ca0141c45144d0801d4029080840038030400c5814179a4000702001402c2441182503840704005801c100510009200d0352080f61101d200e5481c00720b50a010209215060b002404419500f005006000f50410030052040c6600041e587c0c040750000c0ca00903100b0064240c5040c1107000d41000392041240022070014480c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 366145944 1250 366144694 366144707
    0x30b0903070204240e0c0d021b010606030b01050d0207060914060709050603011805071421071403070507020117070810050306010f1202120d050307110102030c03040f02041b 76
    0x64400d80f0200070002d01d0740215071200c0c22140e490910f404085a062150b0160340c0203454100c3c1d1660308490071319600a0302a02681c01115400c1040d6980800343d407042c5009000c0c00008000a041c204850a05440001c000e8859440c0051426070002100070803c046940584a419041120000448034460003151107000070b40c1c200001a8845070041640d2078000300f00d81c1201c12417034240840301c0919034458003410b801000c076400d100440c1d2017070185201d010000d0818000280e822031852050008134040e041028041108000072031940c2d12100d900c0e14101ea800c00d81038240316407501c0c2107200481d402c8100140301e610600c80c000500040c0c43c2c020042c28000c2c1390340442c5099280c1c440c4107040d581c0030248104131030710900341c1c0100a162840c0a050500360b002801d8128608071000c1d02074944404046c4c01000a140002081909540290041e03c04507220001b0741c07442c14080041007207404054000742841e5400c404c0401195942ea1003030031501c0320803003040d044960002016060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 366147194 1250 366145944 366145957
    0x10050114040b0f281209030207031e0303050a05090c010503090c0a180b01031a1012060e06131e020a050715020c19020a0312050d020d0c09150e0603060a030b0903 71
    0x880792a0700101c4603000800768030401a136419035a40300d018001c402ca40307001d0038000005800f58021207602201007118150032040c40300e00302910001e11412490f00400300c0f030008084030081442c140031b0107442003001c1081c150801e001d01c0c20603143d07125441880e05251310401c6166002c10741c1c62002565013920026075041c4102c442041002210a6005506542c1c140550204803000814020788c1480c0c0700716606818070700c6207070140350510454402002c50300c103500055000ca103404104103461800c445240300c410030700003013841400100c0d50a807043e04513a0f1062010781c2d401145451601d4030800a0728059600400c182c1d83c0034200e8000e41c0002e5115802413100c2c2c0c0503410641c446512460b03d00012244e000d49071880607461520744140901c209220321003001820001c4202820103030000c2c1201c45404030340000d000340340103806080880682d1000080c03401100051079002d07003108a407900c850003a546140c1c0c0365500740028254030b00c182c0000f0007842100c000c0c040000700000141a8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 366148444 1250 366147194 366147217
    0x2109020109060e0f040e07030519060b10050d020d0207050a030806031902090105040515190f090903020c09090f070303080f0f090d111914010f0510050114040b0f 71
    0x7081d58032008100c41c0b02c480916050b4010800c0d03000b8003c3d0b42015400000080c44103410b42d80603a03107980d80c60341050451a0004440402528000f09000716880f036041707403a104552902e1607550001001d003050140c0da480c000c82c243c1c0407409042000a43e0100c981d500e40c00030590b00b8106882ca405098002c05441c0c25010340303d80303407044110141c0070080c40300b440e070001c16441030781c0c0c130341030070400500b500510b400c20315803031600c117090301d619503064003046107401007000034085080c00034070340841045038010f01010703040c82800d501082d00404d03c00c0503850207075007030680755a0f403814a80c82c1c0700380105044994130408000005055002d01c00d40d0155851448542c000e40300c5201c1da80400700b098402c3d03151504841c005020907030141c1a00640200c141080d1134111807210500c10000300c0b2a5015602c152062103c42e1700709800788105245d030405040100101e040c441a000e1040e64980900c41c10b000b24441544600150300058400800720484895902e80695030103140b16000300c2110071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 366149694 1250 366148444 366148457
    0xe0f07080a110f18120f0d05030f041e0210030606030f091e0309090903050903101b050904060905010f030c0902030705070f110405010b0307020d0c02030c090721090201 74
    0x7100c031800c60040300d4280d0040040c0900f0100c0f0f01c580d08000d58004600d00e40d019030202c28048041c2c607040b00c6801042c801001a01280b18404051414644490907402c00c02c50104104140a1046640030303420682022050041d0705500130300c00060b205d000006503203c424200b001065642c035030812400e4410fa80d50521102c101e010701d5005990300643e0050020440d07030492403036280690b150403021406440e0901e03805076240c10160440e10707031346026000518000342c5200e640c01d042020402d80c00d64080c04109600c4c074215002200c6004040740002c1240c0002e101e0b440e0354a0fa000030000d040402e0302004a541d40350011000341c841440308559070340c076024001985000a2081d01c4c458842612042d162260076922040c001a490900311440301006c0300d202050348603131140c2c034060302c1245c41555490400040103861b1285c40d0443e6410803028100e8603005071800700c1c520303401d03580030340c1c0c0e0580b95111810300703540c00e00d2051203507191300300241008034403015240c001c0780f40e0034000e88556 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 366150944 1250 366149694 366149701
    0x90103020904150504060b1201030828030b0406050d15020c1f05180703170d14092b051206030f061f060e03061503010b030a0606030c0b0403030c0f020103060e0f0708 73
    0x1f41c1c0300d000350700081d44a0a140c000400200c1d500300d009000e00b407041e45410340544c1c1c06210300e0301d16014120100001a41da880c2901060801d88220310241070700f110440760180140d66044642000801180781c400e40100301c0c0c12955000300450001c0420080081e119241ca820015004042c111034840145c90802001e01402801080c00c80c103482d04084800e0042c240308015a80301da2102d00c2141c0e6041c2d45290703000d110214054014000c00705000a4540541d01d406001c54951850880e00c1c00751300015004030301c0300c2d0032508566551170300700a803003290340e90680000d0600e503480d4030803803041c01184104041500901c0b4481407100401414400e0103450340422140d44101744541501580014041b900713112148161076000100140003103500415600400d0820041742411a10385450b001d0500810517a82d0096000d04070a400c0c49040500d16100113122007041e46010b46181150184142964401e8100d81c010f0806040320300b58504180c0c0a1505003401140c01800050101e40072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 366152194 1250 366150944 366150959
    0x70507050103110a0809030906030c19050910080411030105090f0d020115060c141b0a0e0403050703260103030c03030c0206101701140a1d0601031709010302090415050406 75
    0x284a045080104040d003040120700b1305a0ba1404081c05c0c41000d484207005050899036110b00943c46590f01640072500e03081c0c04140503c000580020700342c10f00c0000d02c000c4581c0e480d14a00b03402c0c00e01c01403401c244203854a0810340a403200c21010036030594213060404c90090b10014003030300d40c08801070440c3c0900b00c40c0e0790100d0072030760203000950390710064100c20089684151481c0517050302495081d0f0175003400707004c2c2c00d141010031105800001580c0031464001e1074000700c80700007401d40c20f40000306843c1035500180746110316040141405078088220300340040358100d04040100c011a8074242d5610313400d001e0143c00007802c0460001c2d06290600365551305c040340da64043d01203801040303040c0e802d01c10b00b844100082c0c03540300c04035903071039010442ea03504c40e4111500400c10310500040186020045148180c400030081c803040e806140100000741240684081090ba1001515103c03c031800049005c0e01c52006e8181e805410203546001c1d41c0c0700400707c942100c000725410881203985008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 366153444 1250 366152194 366152201
    0xc0905101d130b04090b09070e090d0c030207030609030206060913110f01170408030a140705030a0f090f0c09050a1418192f030c040b030c0411070507050103 69
    0x89022200c805802041180c2c100001c03048004100c040b40030568809800c082021560080401c0d910310754030b0005d0100c5480103001044c090f102c80d4000c9612440e00040300b0303684980f0586500c0070040c41c0b4a029051620a20180d009950711540c103014400043c200290360319001e80c6c60340d202d00e0518004c02c1c40120940f09411045900c0707c40a00d18440440401160440d540f81c000d05000104183d00100c0c5540515244100e10804001e600c0342001c00c814401c9440700e007a030001668801080c841829004020b80351710542504000c1604018008000003809486000a20b541111380310b0404103c8586a80020364040400c10880e5685e500300360010355145031900b545008212003c280c085d03480c03503a240d40c940200c000b00c0e0203000f48081c000c0c15004401c58156189034110b0309940e4103042001c0ba98200f43e061100301c502403040d0500003074a81003a80e20040c1b2031980c03108403030310b541c03000e1001000c1d1f2540100200007000908400c0030141e44180310444a80c0240e44020400b1340c003e12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 366154694 1250 366153444 366153467
    0xe0c0f030c031b0c0c0f01030f1d0c060909010b03060d0c081b060f0405040b0a03140a060c0207151224060905060a050f1308010c09030308070e01050315040f0c090510 73
    0x40208200b517907000501c121603002194441c100b6465010000ca0081c0e46e0299501e82000303040c01c0e20401e808459100e04041c0e035046171750700c11070082141c03e41d00d40d61801000e05541074404401c2c0e803a1a20b20001d8948544904002d141d07100e1454006641640843c44100c04142d005d42221001d020404000f0680703e504c1000303100e940c00780414040d03030409a01504094801501c2d1818083d229101e04402c02400c0c00c000e04140d2020701c0301ca0030040345004108203500d10b400103082490404004c078401c2c07025a01888100182c5d000542d480085a400c80b4508a00d10100c541a100c2c0085107041889554001c400c04a5090704000500c2d00f03000b02192400344072542c0d04c501301134864101721104c0d40403100394801e1200c0004040f50600081c0300c2c045801145444448103546189000792400340e00400c20b80078407044200f25210b0b40d0b007110459602081d82426483e41d01a83c0b00020000c21020010000da02d00e480c070781c0000960402e401c6000c0d1203040b2000c0c4400440200110703000781440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 366155944 1250 366154694 366154717
    0x10030501030c0b07110310090311010b1c080904090507060f080c070201030e0307080f090f06031b03060a08030334020318060706150306110708040e0c0f030c031b 71
    0x40d00d08025511550707004c1d00c0d003188540342c10b00c1031a6070640020300c5e182d84204440303d025620020001015084121003040e119440028131240030040c0c009084a02d11885e20b500e8021140c0c203000401c0b460070112020360a00a008000078100b07401d1060380c810150084c400441d40807035070301d203c03a4011048180319031601e00d05546043d43e26801180a170404000c44001448140302d40800119903a000e055185507803140c3e640c603851000100302001e501540000d0082000b0424410f0b41130000040c10703000e2113100e03692581c980380c07400420700d42001c0da0710000030350001105004101201c50341c0c00c444100c401c0c0081d200b96064030480c259034440e031800351026900400021400865030411080c0041c0028082800d207811a10390900b56840d090211008030b14041d010f004200e81c40c41400d00304030421900a04280680ea0380200342d00c82d40c020385155505010000300c03031103040341c11943e451a100721460340300c2c100304620300820380040d035402c80c419000041c01300c0c01901d8030050700d1420101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 366157194 1250 366155944 366155963
    0xd060305060717040f0309030b010e09070518060f0f0a090b13050702030a0f1e030c0305010b090d1b17030408011a01140a0201060302121513081b0a060f06051003050103 74
    0x180c5c0e50f4402c00c89103290048051240105000010510f0210790900070074515101030005d1401e010140e0600c80c4035003005100c3c10009071085081582a8002ca40c0000d0580d400d1100002003000074048c1c3c03403e09122a0301c175000e6800414504501e0300b10b0b400c0c1c000d082d0703418001c0300c0b0f51082c0070098500848807171005a206012280303078248140014905048507061840c80c4040c994148003026034640f0402c40401d840705000c8060951600c00c10b4010103080c180503007411226000070301e89500780800039000e01c00a01d01c00a101d100c0038510170062030003400da90304405c02205025201d41140c440c81986510f000394030701d40d80503500c01c40242003105950f8510612803405209010350080320800007103641c0c0d00c00210040e2541c552189460220300e00602051070700c010368a000000003013660340d650360ba0110f010002540341050301c1e06481100310031207141e03401e030b0511803900c2c80030580588001d0800c1d000c110400855404203003928410b40300d501114600c0c0c0800c0d02921800c0c0320051038030b40d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 366158444 1250 366157194 366157201
    0x40204090f0b1516080d1503050d2f24010314030a1403090f0f07090c11070302091f030b04020906010503090c041509021201080601061e05030a110d060305060717 71
    0x10111007244c616100381c1c4e880381003003041900c0c841187c040624460110076000310620901c10200032b84020300b4120b01c0e1080c450801c004840c02d100c5507200c043e000001c000c4603d0106a202880324030a4240114150600c5100582c40c4c281c40034070a1100f076440107401490400c583c42c0100888880342a15215180f4a907442005454140c0c402810314019016640c040c0c01c820106002c490340c0d00ea0800020701e90340d030510f0445000c0300c10012600c1e0a100c05186c1c822048407012030002c040325011908003546594040b4841011085480d90b024040d184076400300400001404190050380203580300c0e151940c44000648031884156404c0d20350b035002030b1090030782d8501f0ba00100c50074440b900722050000d507110000d00683e040701804504504070301c0011300c0680b20070010340c0c1c010b101c0741c60506a1000d001c01403043c281d907010101010402d001001904c0c1400d0390b040100d94801e0140c1080d622011a240034006150500040350340f80100d80200c0c208611420030708406a500c400d1041d00c588 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 366159694 1250 366158444 366158467
    0x20c1212270114160f0212010f0c030c020a0f03030e0601090e010606030501120f140f06010302030d080f0711010b12030a090504060807060e0d0b0f040b160f1b02040204090f0b15 78
    0x1004440c0461755401848054001a200d90134803c500795003080002c50300c0700740c2441c01c07419074440c000351004151a24441c20300050340054840030300c941080d08010854a00d007412005400b10b090060aa40f103035100004d042441580100006d25501008101d4076803194000c4040c0c9000384104048131102403080000708000201101180744500640e00c030350410300800c607003055902d900030505a00702500400039400c0512030346510341c20a240c4503185140182807000c1c5020050030349801c0010041703a86051003001d6101c91001a0020840c0e1410681c81c800565a41d00c2050b0440c0019010040019503041c14000c0700c003560042c5005e042c2c1d4600703040c011a40c0c03800c080c1e9250340c0000c506403040080303203481c807529024140c0ba0012122518060a080384002c402030404109264548948180c6036444070302d04100661a10340807034400070611348180f45141c6410040d500c2840010000703002d181c2a0b00075a00b98030b0307002003441680030900401208820b045c00800708160704021849600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 366160944 1250 366159694 366159727
    0x703140c010e010f1e0e1305130f03141209010c0807021002180a080304080d05070c063506030f070308040902030c041a0403021f020c1212270114 64
    0xd0340740380440030020841000d160460b0144c20105c04107111004e40886410000c03103010140c408640c003807240b8100551b00ca285c0005140010b4020750b500d4072808200b51103507082340382604100b0350641e150545800010003284041d2a07104082d80380c500c200328454007d00c101d5101d10041e030050b0500513a0503401c0000781d0b1008503180e0681d000b1010b4011582d0b6000c401c00054980180150740f0390b400e003001507142c08010104c6505011051083c240090001203000003994818038120380680041140c0c00d20302c1011307061008030384160103012403080c0a0200541d100d854110111044000c404113215104c0d1614040906060400c00c024040340d020758004540029516061624269503520604200900f416580c00c009000040405c15890302c014211403583c0070000c00600440e0200000c3d50b600085a152401140d40c1c02c0042c2034810b00b0700130780c50816601e402041d40c401181190a05092244500d00416048034110040c3d03540324a0b09005d600c0c0c0040c000c18605500c1018042ca003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 366162194 1250 366160944 366160967
    0x7050a0201020c1009140613110f040207030809010b0109030b15150a090e0606181e06040611070909030906110307020a0905040212030c1b030a060e0703140c010e01 72
    0x80d50b400b08000711228608000c921003c200c00b4400080d240034a1410111020500d9084007241d8030603400e100e890044072402c0c220a55200508001010303400000c958004401031a544d440740c4085415001c1c5504500c60368442d0f03440388020030038145008010340d030b00c44130740c0001b4100d500c00b107000a085a40c0d00180d8050000020080b80041a103402d030180958849907040700002c808100421070040c2d00545103421140407201c80c2c0c280398806550342018945021224411000c40d40003504840f040c90740e40074071060140a071a0344503154034021704075450b41c0e181603501d40300d0810f000500d80b10a210365003180d6030699801e141d40d03123000703801c4402c10100c003031044550104200200050383c8400482c801002200c801181506d800e004201821060142d040e055402c2007201e184210750100f41d238000b103510001f89214a40d1301c140840c3c900414180d0040843d460988200480c8200007940412a442811503103903e903d2011919119020381e90345501040304081201110340c050f411020070b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 366163444 1250 366162194 366162197
    0x70818090720070f030302160504020304120305070c080301120201120b01200c061308010b04060b03071b0209090303010503060901060302100f0c0606230301050f0c0705120c28030807050a 82
    0x41c036150b4043c1102c4c002903500807000b60707000203c1c060f410400941e011004040c00c88003103055103402e440d41d01d0051071892a240402d962800050341c51406a19000c1510390820550344d240c1d80c4071401c41e01403c20340b102c26404603042c40041385440c04213001e1600ca00c441a514000c861805080e104401c91040544200c03074000c50100c4409515a5406001103800b502208a906468070b0b4915007100d00001c101d602030b81c2826001c0c031030300038154220f940103011b81c81d2000000101101001401884500c000e500c403200d04140404618000041c2d0b068480450a030307403264440a141c1401c98940d0311009411080e401a981070060040400490004140c20101c0c525111692100d003214126042501a05554188681e100f20012410b02c803420081e00204a1414840440d21100900503c0c0c401000300c0001c1490411000b031001c042c940401c0401180c0b039501c0c240e00d09880380b154600403c1040d00041c00300c122030342854607d980581d00740c0c441d0b11700c41d12084400c884a07840103007281d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 366164694 1250 366163444 366163453
    0xe060c070605250503070807180e0604020c010906050708131a070e040906090b0c1e03090102120901021c0603031710082d010204060909091106070818090720 69
    0x28000b6030b2003568490016581d40d081c0c0d580c50014401f03820313500c000d002d08080103c1458614400c01a4201d90400c0e100c280c200c6400927501d607030003d40a88580300b1609000d500300a4080200083c1d030b080740f80250b09684800182d03a442c1c100c0400798ce0040c4001802c101607102d0f4900800b420f035850030760404040e1810442c07108a10b00031900380c941004048030120780d44c2c0e0503401400030390714a054000640000071440c019020700100c1049040801e8111482000030100304028025811584507580101c00b2110070301d0001e003800c2c000d40091680c2c81c000e5803a078921200e09082881040107995048d225590154101004001a89401400e514070003490328004156180208001902c85440c00c210786401c654140342a010000b42601c04600381c0c0c0180028032070300e034100607030a0a1302d1010f0740001d0480f2450070114903008200c00c566801940009400050040400c0104008001c0406001c3c0380680c0d24144890a030003100c68000140b0280c40709100d05414900c13404008913a0401c88 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 366165944 1250 366164694 366164731
    0x1207050a140d2c0909030706090b070807030b01090311010e0a0f08010e0309030d052d0306310b030a2909070e18150103080c010e060c070605 62
    0x564010400c1ca0308961280d00030b0800030560b5902005030b98801a03c4000785003903444075040000080c0502502c00e12070549000092002c50301082034460554201d9424808400d590401010044e801d072030b620001810300b030000c0d15450107070082103816101030b503541d0002844d685402840c000e1090300b103410001c0e080924070203542c5095100c00079000b2488549207651620120034210f071104c40c401c0314660400d0010961075540880d4085d00d0302d155041c581d9882e0b541d4040e8030702040c6410a2083d1140800c01368200710312104000d144a0401940c0d10045480c0300d0714090a0b4043c0c6011190513142841700224158201d0341014084043c080c04484515030a5a11304e46890703204070307025404246104150f0354071101c000c0d502d5000000b2801078440241000048460f01c0da00810410020340c0001040d010b26004100711440e0306c0c00c101d8a0f1586503101d190000d000d1748519540040e541c00c001c441d218051021904074054410045490300e0140d4541d80d04024200003088010070b082d20703d80030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 366167194 1250 366165944 366165953
    0x509030f0102040501030f05010b0a0813080a0c0c05010503090c0f040227191802090a030203011515030b061903020c0303070c050706080405060a09060e07081f020c1207050a 76
    0x310990880400141e00c480c244000101152044900c201c200c0341002c00402900c5440401c542e102d030440d11701984140d80e80c2c0407000c519010824000d103c00c0c00001c403022305550029032002c00901c07590500038078a07a120011559808252880d1003d9002210050054982003203e1004441c0261002d400c2003403100020b01100c10601110042c0ca4201c0d400b00920f00e0580840920031040b5980c01048504090300303d40c03c00e411501c89200a9800a08804241e4880407420700075540107000f4050380300c0c1221040a60407461090340c106d94071200a200585000b4001d002420002030042c50401241d02e1101c452540c04c80e01c070409040e82009401d0007080c0520055101c2c101640703c0c021400c0441c13403c14a8001254000020000c001d4140f1001410109070540c025005400104241c1010b00f80540207080c034095100c1c2511510b40002a030500218402101d20a02142a200c030704d810a04036050f44107a15600b8940c0e044400360080091340c410207001910300800403188040c240e42e49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 366168444 1250 366167194 366167203
    0x31315110903010b0d0302150604060509040510112704240f0e0c0433030b03150105090103140f07030809100e09131415090706111507050903 62
    0x10036a0309444001840c8025041c240140d0a00709015144c030340142030603840c000d403140320803061640c04036680c0c03002ca005660f4540241016000081210005007068500103903581e904222a8499501f05000a43c94412220a40720030980c2c00c0204240c22070f80e0b0a040340800984a40f03158820345c2c52440c9002c4902d00100301d1003c1c0c006180c0c080303140741070066044030f2941503030120b03100c02c00040400040030710200a4404641c80808900d000c400b03065140c440282480040c0422005a0702005040d40c4e45070b0492030300002c003075064643d003994403081070604400074026107401500318401000003c04180c1210f0a8142d25000d0311320135401c074018182418010741c0180c50300e1001140f01c007a80c0c50010550720002125003000e40d200700d864000b10b08005d01c0181088224030900020f0014010f046418100140452054800840511102e1040140b080c0c616071181c1c0b15404002c1100c41c040d602852010048034000c00c40d03461800103000f480140103220504104042c094259192001c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 366169694 1250 366168444 366168461
    0xa0c06020714062805220c0f121a040f0b0c030402010f0201020c0d052b060f050a06080c0703110a0f060b0d020619090b0706020901091a031315 63
    0x10b080b1101d10000e0303102240341150103070602a16000380030100b40307081a10720a1401d4140350941c04906030f640d048912005040401079501540d000603206802c000150900400360343d40624190106926540101466007103010020f003c3e41d080e21041112815120000341d00c18854000000441803640d1001500c4500703441d003884907000401400210f60304241200e00c00f1029100850034409500d6500380d0302c103280c4454905015002400d007032001d41400500155240d1108180c2c41c12040d404524001d16003031181100301608600301003041d141603400d00c01200d505607200c030380585031100f1880072648050011000e00130b6924102d514050140017001c2003e009045010303050040d0b0404c1002d6420051640b40306843c181001c40050751560261072101903d9440f40710035070095042911904100d40111803140008100d81c0c0403c0416001050004020f982c5d0f81d00c041e60741d245120126084044155076000d040c40080e5210b1045070002042600910390342d00b0520a954126049a500c41e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 366170944 1250 366169694 366169703
    0xe030c2806081504020c0c15042706050103090206042102120a02010e030d050708070602040909080d0c21020703021002191805030a0b07090519060e010c0b0703020a0c060207 76
    0xa02040012034100140f04407260f01542d00394a401d100185640e00d80c81401c0d0000d00c141c1d10300d80a01a00721060060314050800e034103030541c10034240c0c0407240c1e048040e594200186410070710045407a5200707010b0044400c0d8060845c50074a0706207407a9030300b0f8401000071a1030303e03801d1a250301e016030369994801700c0741d992080242001e9240340c000105540e00c40c041e13136406540040d001d100050b5000048a9105402c400700700c1d2651602d10f0b00102074411a84100c00607400c4c11184014031000c1d600500d8040420b02c0200111b845843c0b096504a01c1e034152601020004c00040e00c4100c681d4000f807003141c1c4640305442e2500218a445000c0380c110010901010f02050b803101a0070350806500a52100c00520004035186400c0000c1e984281141004000c2100d04010444950080350400c014010051005844402800d450b008164051044500082130015610001d5024110402c00c10340c101c1080c8209a45800c2c00b5806540065041002c11510710900004100d503032010b090b0341c5125 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 366172194 1250 366170944 366170957
    0xd17070e03070306050f0a1a0d020607020307082a030c04090f0b010303030f06050303120a0b030f070603230405070b0a0903020603010e0a0c08130f0c091d07060e030c2806 75
    0x50021b140c105c0300501203107510303142c5844501e2003a80c1c0036884e41c2d01001118080410b07085480841c12070702501000941500c100b82003c100c0320004103081640e50004244413446044007013103d1000c03440302078040d0b05074005100c100030794141900b082854038022010405e401000f59116035100f60240d200ba000296560507600c0420035602071000241812030066082c41001c0480c0052490041c0030b080c50190345080c14078164906101c0449248034440c2510251a07981c1e030050050604040181140c0c4591b04460485407021030b0700d20b01440d0041d0050a80c141403540c0b01489512210b803080a00038815800401680c072140114080e02035080818190300f002902c44041d182c112015909008584003006a511900e0089000c502d030042c04040b10649142050071543c0c20540040ca0858100800e450801c40999412120803c505086608032650360200320f400200c3c6407411645600075262000c0c00c1d02e0b02000b841c03001e03000b82d000d0403904c441480400640c100a40d2186010540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 366173444 1250 366172194 366172201
    0x91202011e0f02010608030c060118060f1d010617130302190f1511031b16030c02090106020c0d030305060a05060703020d08070503270a06060f080f0d17070e0307030605 74
    0x9080c011780c0000d10302c1000460030400e40d400c00c0b40d1102070500419107000107803a40090f81c048980c018000500c20a501c92404584400041401c0e01d03c800726131070360b00c1c0c001c800014070901c9624414110035000b140a101520342011fa40f04400594005508520178401e00d11344510fa83d9020600e0140714a6002203034550030f02d4107082d0280010002e207041454046400b1040000c007040302d0b03005101d1b42003084e203134402004000e581c0c0211081118682004148070003055000030346030f840c15000303c900e004603a07070b9039008036928860383e80c12a0300f0204000500000074006e070403c03500454010020b040241d1a00041603094100030410350050b03205c1044144619000505582c204500307140480c9149032801c1d03401181d500c580c00d580c01c0300c0404600c0500c0315000344500c150480e0300160900ca010399880d500b0003401200d0003104814040d4034120a038a01d400242c00c1d001068945a0300c58442803980c401e03181420003030040d014000b070b1040c980f010381d5080c40401c024521a15000a4505 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 366174694 1250 366173444 366173447
    0x40801050a05010f031e05011a0f0306150d020a120b010303170c160609060e0f010c0503090d08040312090b012102090a180b0f010602010c050703091202011e0f 70
    0x100302400044040380303403900500880c00e03440c041100b520307000501c880035510460b2610403890f040c1107010308294038201d0401514150000c0281c00040100c0d0041403000c80f06c010143c032000280d44403007882501c40c1550b819810314144030001d6071300050000d8001036540b90f404501d030f00d04480840d0803040742d80c018010190403581401c1030004e03002e000301e003a01e04a8424841c6226568a10f41b440b04e005641c0001c001d481d4102c10405507001788103018164409030361590300c110341c45d0041559404c0c0806800107903c40c0c810b882c42690074000074900794114140a444c0d00c0e002600c1602040740f15031005502c4822805000c141900ca000c01034200c0d85040c1520011a0844d500407a18600a044880160f51104407458110b4480c51000a078242c0c814070b4042403e480703ca000b041079030100c08200c018220b4076441c1c3d040740d0041d0020301c000741017040d0403900c4c0e209808008001c2410350005008150302508000d01003803042c1028a059405d0042c1140c0c41039450034004d002800300c1442040b0795 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 366175944 1250 366174694 366174701
    0x507090b0a0e07080c0717070516061b02091e040c0302090f1915210605010b0f0a030c050f2a011b0507051608061e040c0b0a090f0803040801 62
    0x1020034240302c4419050071000202440d4001e8600e14040b04081840c20038030111408000c50084c0c440c2945645812900e41aa140c00300b91080f080352548001000500b02c0c0074507401401d030660b074603001c2c41000e4990b08203d80e1044c0030f0405072091401c0340d0015521070388240800d0185001b0301c2000f00e440e00c1c40c810060301140080c4a51010301e852400d200048865490414191080c244089105040095a80d800038020b90142e0036844900d1045210b010b80c403400c42404034050b0009002c56070f260350303e407010741c4a03503099940c0e01101006452007481c401d40c441c280340c8880c0e18200d8500b90180d0000c400c59005005c90203d00b1040114010400701040083c4001450b4900288501d146c0805140e102204070140803040c010002001c0c130820100780f0108100d0034421520b01c620310340300d0480343c1c1d0300d00e02211180c0700404501e01c8404045000010341e44981da002c80910955820080d0760109a0071035030288040c0540c031840421070003c20748464001d081d400c0c0085864503e08141c19017035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 366177194 1250 366175944 366175949
    0x150a0608070303050304201306060e09011a0703020c0604090b030c03151506070203030703020705121f020f1c050a0c0c17070503130e1008030313060b030a0507090b0a 73
    0x3952000204100198010080d82c0d402500085500004c1e402422807a81c03401100204580c8008031445003001c81c01507600000c1524280d03a0b451807100011020300852103000e0044041159403118a0f01c000d02c0d120008041032407091040e20014400c4101040d1641c11640041c0b40d00c6868400d119240d0508111071092040110001d1541d000750008040d003850b000f03420b00104002903a40c0d00b2440e11050b0460700c201d42c0c0034049a03a9a455400c1c001d4680800c0d00a4601c6008000f40c440d064403c00955611000307121240001003d0703000014000a510821501d0f107001c1d41400a100c3c3d07042002c44403003101d5200381c800b0940d4540184041c0c200c1740c5081c103180070b2080400d43c1c00b0100701d00b0354440e040410f0301c045042e6624100d042c010f255000e0500082d41c403910f0b201022486001b0741c0c00650140f14101591031034942c0700d400c1c281d101e0004460a5100640e04d46980011034003e030800c001200f0b000c0c06980c5141e109031100c03401c2c086640c003e4850700751568245203180c00c0c0b09802d03100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 366178444 1250 366177194 366177209
    0x90c0f0405042012030f0a03060b040621060803180a060908060a020307030902031c090902070809010f0320070b0c040303140703022a090703050709050409080c150a06 73
    0x42032400e543c820b6080042150320184140559040c0070050701c82c1e040034807941c140031088940319040f182d514034003a400745030480c0c0040e007419400250a148107055030283c900984130000c1c4030221a02c550240801080e40228a0303440e900c00182002080c002021f40c4040300540c484003180400501400101c50380c460002c204d500c0c07404000390b60700841d0443d0801e000010159483d2118078040300589031020020351305000f25880a03084104500303c0d484d9011171600c8444c03180b591195901c00303e0042c5900030740880310421218032558804c803041c240d501c520341000104045989a000200007075076001a0007580300044a005001241d503c0503440034001c10700360f18045c190780e00140110140104808962808140a801c041c000d00150000c4800400007440c018070800c42c11900d6100b50313050030701400c40070300401c0602c2e1103030143c181300c2c0c0d000e0388518843c1407401c401c2c00020250b030369040d100f4503410b21a50019400034011a5072050100c5450724890802c40032500860702d03603502107603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 366179694 1250 366178444 366178451
    0x504242d11090109140301020904020301080a030e030d050904051003050708010b12010e03070b040309051009030b07030506010e0f03031207020c01090f06020a1e0f141006050a0e07050c06090c0f04 86
    0x70b8036a911004103810703141d28800040b1002071078000300b80a8000d1220459105001000100c0c0b52003000445251f4103000395280406c0e41c454030141500c485800340d10000040081104e40c649040036044543c000128100c150a455983c0e00d030076052031241c0d080b8000c5a512038945030308501d00150040982212003000300001e8041440103071340d0340301c0d81d04000d11a401c403000080505000c1e40500c0000c2101604451345514100e1008091f10b21a000c1182ca5592010110f10071511070721900f88241010303160300c6e02421101080056441d00da442a80e41840301704241200321034612107480c0115119002491071019440c00913040b0001ca410560300302480340e4041003401da00160a03032510f504070700c0540d000b0141c2c3c20080945055503002400c41c05a580c5a002007105081c030f40d10510030140b0a507400a03003030050540503164248607250740039039075403414021440b451418035044016400e1071490000a05896030030644102d0302115142c0151640518908110800d0a4180421078080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 366180944 1250 366179694 366179707
    0x907090e12191e0302040603060b2113150b150c06010b03070e030604050a14070536040302060403020615011b0303180b01030c050102010504242d11 65
    0x105000325404070080c111228403410201e4010707a848610a2280a185003c0c0500b010024020394001e11940001901e0490009001d481c180c0980d142c1e1050030041c0c0f1846080a40044403459000e480e01c1c1708405118190f0002a1041c8151035901c4210040402e100c00725400304844940c8504102c0d2a05034200030744001003001145413810740e2908000f0a849440d107000440f420102030450f5a014407400091000f44040080d00964640c81006144060300040b041107449030300b5131144a80000348044840340002a072100d8018803a580c0b0316180c020741e800000ea00d6103003400c0c1d50070303000b60b04100280000d169043c819554480c0100804140c04071803107000070504000680c0107035500d000b4074400c004062080d040011106010742a480714200a4140000800801e1004641d070b0001840006060350040c00b84a01c1031360010350241035041820f03c1c0700000101c840d01103908513a14078030401123003248941e03423400250283e048260b650784083c54100721100c2c900c2940b07000805001c407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 366182194 1250 366180944 366180973
    0x41509091e020d06090c0b0708270102030406030b0411071202061003030801050108072f0f0105092e0c050c0d0908060705071412090916051e0d050907090e 68
    0x75030902642c080c9000805c1740060400b440124626001a504050300094084c20301c43c13884058850161602c80c1564001c0710034070700c0d15000f801109121301680061104001d0503010350b21030b0000c401e002d8404503084030900402030041d0301c005011a400085441d00c42c814590401016034401c81c1c00d800314040e10f05644000d4080101441101e04010303110340050107461107901c850409016144411312036030070100588608844d03400b014400351040c0082501124014040d0900079842c4401402041220420020b44040e2030f500301c1e60194480c1741015022030252041e811903a0450b0342d85034950300c0f684025070400c1c20704402d240811405140500c251000464180d0f004031207401c00c683c2d5600c1900d0700124510103480500401d0003a5842e08080c607600c04003c00d06668100c1e8041c0c407d59984040742d482992020100700003d00c1405140403072003261521824040c1c11050301b6080045807009070301990313012200c007060345d088580100300b145c000e03004490301c1e107540b0006001c01480362801c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 366183444 1250 366182194 366182209
    0x304060503010e1f0e0a020909010608011d010f170307050709020a030605102a020411030108011d0d1b0605042001020102211315140a1b0e041509091e02 67
    0x3c8089584203000406c1000815a0423540c0801c4082c1400400b503070340d01000703820b0803024403407222045891400580d080e88581e1006050310202d41c030002c441c1c1d09200c0c09091601341a545140181310400588011520820644004001d00c0c240540d45585c50200181a02c000b90700a41c007800c0e0380d19504030256000b0018000842e0302e448000b425a420340084520a12a10000ba401038604410080504001e10003141601c82000092104800010101100d480500d43e003010940090200c60701188c4150000048440103066020b022903642c1c40301e0080b1441030768100c480900e04500c8600401c012080c0f2040004240002c40c1803c40e1046030100c90800c0d124180e90a03141500040c40008030041002c0c4490780021082280c81006024400106003150403499401c07404000030711500041d005540309603204052003011085c214800380e8580c14220455584680c07604450750f5129419500d210080c00000f2002c10031003c6411b001d580c1c0e04031001c0251403a4200340c008400350302c6492 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 366184694 1250 366183444 366183449
    0x120f0a0f181106090a09052d160201020403150f11040f060e0a0e130309080a020f040207231b10140c0a080d0e19020901091d0304060503010e1f 63
    0xa4070299110b09040083c645110392020641e000c030911101148404050b880b0314410b240c03103111603c05940800714805000b15201c10382c03c200000720001031040302d038108a1045032030a8000235003000d41b42c0d030b01d091481040402c2031500e996102c801a000a00d0350091004507030404541c14a0103040c1fa41074940c640300d9014860502008034989985522800801001031422282c542034509018820460740c49034560140d00044602d000400c08840200b00500269401400080b41103166000c2c030000c1d4101400540300500c0c03040401c03109200703008050314125203920213080c4002c0d1425042030400e030b0f5040c9140c0506c1a00311042105908244000580d07050300c01c00f00d4460800151a514003044410003c009030404141141100e2081d009690709281071343c00d54800c2218401d01a24845d80d0500107944808104010004809036a01810751300f02102d0025040e1f00458211503e1a8056480307040000c1000004003c110040056180c010000d0285014611400e0110050f40388690 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 366185944 1250 366184694 366184703
    0x906030123120c04021c09050a0209011d06010f02101406041505030316050712081b0114040305211303080c0301080a08030601051b0607140901091505120f0a0f18 71
    0x20307030000f0722118118160040c41001b90b062000440f140384c43c0c5d448109203403007213004098500c004a140c840001482e914054030303170001015039964400444040340c02e507800301c0650040502e01041d9151074015000410060501e829060920744248003c88014a08d540c400079901002400341360b8010003100c400d40d103072440300e1134150b03a141440fa040c02403941c03240a0100069901400b00480407028041e0549420751035a0110768058505003a207030b01d0b074601c0b420b070103280b40000e001a000d00d000d80011143c89404044004550150b4041c0420580352900c118542005c510308140e4401c4009502414280a20f0300350b500d4042c90710f48da00e040800007403041d800800052096403090b81540c0d20318141d05000c0742c02d807580d0450103480c0c0d070b03080d10107500003601c006800d89545e03031038000c80c1c01580042e036442813128603100350350f2940104000404200a0104014030640142540d407038000d0303c644554658074204002c02c5d60403100d039031012140050401108099840d07005e4a00803840c0c1e0030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 366187050 1106 366185944 366185947
    0x30f150303020307030c080d021c06050d0b040f080d0f1a040203151c080a020f1c0f050a0e030d0906270b0c01020906030123120c0402 59
    0x6600016016900030060031002910481d148819140558403050030100c22040550a80c1c1c0f0100c1c0d1106107199000c05401345002d24840c0d04001e00d8119140d800680d0a59594541000001c2019100001c824043c0040c0719541046a85100c441c6008000d92260003076100b0052004611141c140301c00038142da050303414036200302c1c0c1c000c9100a008003034403030041e002c002079100c410041049076454113a244001031007500244c040d40c038098018100b00140c207140c1601d411284104484a489080e85079040e44c3d030080c010f460660350314a8110340d207034071112060350b10740b01c1c0980c0030b0f40510030b181c0759042d810340c0003210038181c1c2c0b8590307980580341d1a5030420341c025030b20303111400c20080300203481084203140201c000e042c0c80032130f14009401c0500c80000075840342c009a101c500716800c2c4100c02c00300020384620440310084210b54402c041380d4410701590303981d035404000600941e130 = true := by decide +kernel

theorem cover : BRFrame.Cov 366007194 366187050 := by
  have h0 := BRFrame.cov_init 366007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 366007194 ≤ n) (h2 : n < 366187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
