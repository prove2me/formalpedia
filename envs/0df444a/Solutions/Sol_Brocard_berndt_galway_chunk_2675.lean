-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2675
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:24:37.157023+00:00
-- url     : https://prove2.me/submissions/99e20fa8-c2ae-420a-aa24-568105fb2ff5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 480935251 ≤ n < 481115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 480936501 1250 480935251 480935293
    0x602030703090306020c0a051c021006030b060f041b021c0504030825061a2409120a140a050f0c0924030105190b030106270603080f0a02 60
    0xe8541d0b200a0228290f43d180c1c3c0094128125203801c5108651403100018001c0000c284042444080b07240aa041060000d28001e14040d500941504060080001401344514140c110108803902c00450b9030441c0464010050001120201c840030b0384c2c0e60081030340200b0303446100304121503020348203030103600143c0341d034821031000600100e000c102491309419004c00c20501c00e42d200c04880103100c515200c1d40261240b402e5080c44981c09182c0e01aa42e2401d100020503d112000b03070703924048900241030880740540d00d80c42e4000d402510341d003a400724007880600d1503754041410015039120401d0f4039612584a18222203030b104121032540c48100004581240840040c01c0080130790318400c00324910f441040c0c901c0c006111002c2c2c0400c1655080c041d0612420b400c1d0220b41d1500d0040f80000e041e2028201e60718041c5c0d2405c00280044a80c3c015101c012826040c4416415541c2501c000c008010562003c2d00841d008980509600a0980101004030746a42100c455032071561003524951 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 480937751 1250 480936501 480936503
    0x20132010b0304020307060c0503041806090b0406060f0f0e04061217031006200d08150402030402091b04120506060406170607030c2007051216181b0c020a06020307 72
    0x382c0011ba041169511a4035184607032481801628242560390b005c204d88014250500f951080e283c1000b4040c6001c01d20408400090031901403142515008006e800c1c0d8415842e403400308200007941095040c000d407407805108001900402c00d045d03440c101300745040d1001e08100c80000f2170219502c01000c51005030f83c0075209840185021300d15000b0165400d500380700c442c06203490000140210702c1e8040c8000326908040b0b0300c805400e860041c001401c600c403107040582c8114814014000503850b00e01005502440400b40d1224914440710003c41c54051680201718541c088654074040184c04a1014011082501c09000054031800010328801c89002d1340da26651041000a4030b0a2090300001c1d07450700c1c06c2c200305480d0644a00000582580840c500d140d81d032203820100002e00301803440050a5881c2c2000c0d19501c5031a014241c1a2009446a54405204d201107103c5421300d980c0100d01000641f001645055400c46c00580102240d1a05a200e070301d400900044050020084030301d19 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 480939001 1250 480937751 480937753
    0x30809040c0309080c06060306090f12030a09020d050d17160f0908010c2705011220030f060405010906050f0603090a050f03070501050a020406050f030601020132010b03040203 77
    0x50450a01005004041d000010151030702d42c0600031400041c01412100356444c0a095907141c850285450701c035001c1d00109a99028490300c19000c0c602150048841070305541d02d42d80c0341c842288950140c1f44c28640650300410804424080010019804102c1038180c1c0340c614410280c0562070100e920308a56660b0300018000584084512071224040308040c141000d000a45e1514200c07030869400c00942401304407036003015040c075210201c813200b60f01c90b1810350160b000c1c104000240100c201e6a003d800c0103455807001303501403e907189207055100e8203c075400e882e8508550380d61030790041940d810b40200c0c0750100100c0c00c008580121401e480000d084918640b17400001d004580d8030082c03002c492070050300340003400603805000c605455100039000f141c031022241171003404c40b90098041e080e9984104010059a60171105481c4050400b69207142c80f6a54280142c1c090400f9440f0a0b0020f0414901c92040b44c0060080301c001045400c0e9104030740e1380b03c1c02218124403069038081d501d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 480940251 1250 480939001 480939007
    0x10c05090d021f02010b040506062b0f0f0c0f022e020c030403030305090601090612020618090c0c010623060a022b080c07031707140f0304110a0308 65
    0x8034204a0309010541d4406050480020303103905004141d05600910440141d4440c00d1a000d00e00d464044c80f50480000c840183c5080824540c1c03020505600442d40985a42a4440708078072440790300c45c004290942d402844030b0301000b4801c0e80281102c08500d8081070018000085403440089e00860350509000c901c130a80381c20741c01091203240003c1480e001590200a10100c845003800580300441c803948004c01e0702d0410b01341c0b8504008058001880742d41c58a03100300300080c410031401d100f82750143d410540c0e8012000807088140e1010b00e400d074100b590312043c130071030401550040c8810b1070201d0080000540310011400b40e01d8110f007800e2000302c04850400d840d890f10000900485040d801111512103004080a8a2000d0040c00760302041c01c81800076601a081001240c0c8541503840c02c902d031505555000d0004205d03551010f1104601d08005805540180c0c400e4451041d40c106658581c00100503106190344102d90841d0010b03402e52424005080c00e03203a030001e9991001c41c00b42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 480941501 1250 480940251 480940267
    0x4110a090c090e090307080c060103110d2001120911240f0a030204120813060e010f03240e0a0b10090608040201051b030a0f05030c0405010813141e010c05 68
    0x583c040702401810840c0020440e8800050070b8800806016103020007425540d0326500f4008410324120202c1070141c2c1c0680c28620010301500f0311024401d00b14070046104480b030000481d07800030721f5102000440c0c81d0400c56014080540341103000b01c8811a07064a0140340d00e40300d100803414000040e90114814040807445001d45805450030810361715006003099510310075000003111416040d602d50b0320000300351009199207000c0c83c002d4072544c142000702c040c40b44002050300e079400e040d02040550700c480c04900b0703c09000e0884881401c0c0103070142116220384c4500c0000e00c05607108500e182c5400740c1d0120074182644444444000350320b4414485203070101c141c5145000400c01c81c1044010000210080072100002480240d400001c540703a40308100058a008a80d502900902c1300500400000362900c0b0216010b90b0303c20310b89000d40f83c079500d483d24103410709884010080c8140040100b40603900007060128032542d00c0c1c20012000c4601d910a089442c88041000003032804c1150741 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 480942751 1250 480941501 480941519
    0x19080c0d060e030f030907140f0402031e15042f0c0c0d080a030f05010e010b07060906020a1e090503101a13020301091a0306010e04031704110a090c09 66
    0x1052181c06800c0100b420358460302201e0550740030410410400c6404018400291010000300f400307418941800074004c0074440018a0b550703050315003280308580000015040c5540303003140500c403000728507503451b550410048600d00003034220030807406645041c0300351005140a080078603a03142503940103180704c0d040c03440100203a4000d4594200c1446070840a0300f413501c45046002030180200c500a4440d07500c80700080541d9200b04858211605080050181c002c003003521a044503c0404090740d1f55006140942c0903180110029209030700c0403500ca50000d80000c220f680c444207259902601c82103500781500c03481043d00805d601a0f01074882d00040349016480a010900303407460fa001c2d1302406c40c0005000c0b0b41040c5401030031070b80200040001d804079008404584c00c0c4003000d80c620716114000b00b503036100c2c140314400f4603d64031004038092500404043e007541c40c522a40c80c10620349030508140024003840d0f1940a44171100002807004c000f8412002003214503a100b112080c58a4504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 480944001 1250 480942751 480942769
    0x207090b061201060c140a03050a080c18130b090a0212010501021b060a0c05030c070e010609080a0602070201030603080f031909050a1b090204090516020c010f1b0b011419080c 77
    0x12203807050170081075130400c4407c10014007018881d5030b03406c1d130329140c21200410b00500544401001041031044001c51b098004130726042520645188612052414220016000c40502a5080f64a4109014402841e030300203103100d5995404031600e0b40d07640d0004a940e44c80b4550400320602820b003440682d40fa1450003050501d03400c3ca086a54051540c6800e81141c1c407071580740d1800c1d44007600070841c81344001c0c2d50131f00405243c1440f1400c07500d00150300752500c4100b40c00500c0f00e907000500808580c040c1e031241002d1a00303c3c001940b00c070141c1c80308500e141d100380c400707190503080302060800c002d285010351402c2d0366002018001030006603403151003500c03644100500105915601081d014182c2c405000104030000c00403a150130a06410360035002e196012208640040c2c45001c1145d03040303141c03030180310340a04c2c3c080703400b20b020302010640c0090180000c10305c0742080c0c000030b0320280721101160b444400310390000400b41d1094504405c6865072060740a03640009460312508e140c5080c40d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 480945251 1250 480944001 480944003
    0x80406030902191e0e07090e0c1204030c051b0a0306021e0d020a1d10080a0b041805010c0c020f0409030302120901060e0c0f03060409060e010c0207090b061201060c 72
    0x1003600f00420041540d1001820350020344500d1a100101542130100640c3c0300300825884105100030b00704800000c10707110a41c01100c804801c2d0300040b50340003248400b02c40200d950403a1101e140c1c24240b60050010f202c0c1e041c25036803440b9542003000103444201080b0032019005081e422400c0c61642c90002a400a05d081720841c00000056400b160300d2030010250b46070099001a50360103480d8000d0040ba0074580c138840809460782c6040502c0d120504800280e04841c180400c581d0b0b1040d03480ca01a141174100a50070609008074014a907009003031102c000c038815002407010000ca01c90868180b03282d42d0b00698494422985000da03400c00754018804240a46800b6240c201c0c844854804d80c80180d9071054140c0d954030b0100030030182c501d41d440d04200d8030201c0901e020b8506130501a07500000e04414441c5a07102c2a5108000056010a0b645020340d0300902c200310302c100020b03450306214800d01c1d80c0e180c20417542c6842468900d00304c1e0311325094509042c42e035034200501241c240342e040360 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 480946501 1250 480945251 480945259
    0x504060207083d0f1b0908060f13080a0305100501233901050f15040c0c0219090c020d0903080f04030213021e0c1504020102120d050a0b030307080406030902 69
    0x800030f0140d44182c0540c0240c1000d43e0008a00c00d500c0b402500480c1402c40d40100401581880a00c45900c02040460b0040c1c20350085000d02d0700e074250880c01988001400820b651310001d44120300303a816800403413103a00400d2072011010340e518019100c40c40a8a0906500d04240c2c808030030040704000074001843c40c680c110480c0c6105008080d18421b1a010f41102e4100694002540481700340201d030760040c4150301059043c24a2000703241c03160081000148115107900301040c16034412484451039503001014480c9064241070390340c143c41038034002e12007440c0c18540720300d217064000030320101420203540c0c50715140c40c9181c82d0541141c001041441008000f0400040036a0713032002110108922107400590350582001030788102e150400109410701c0301400070b00e80e01c0340007051001c032605584010030403030303620361004074204030417558060300b03003503010500c0c0801024a602c0688540c0c0320481c01c102d1090410700b01a83c2c0d001d50940200007480c20407050042c148690010740115101078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 480947751 1250 480946501 480946603
    0x6090323120411060a0302090f0312030f0405100f05150307050303070b0a021308070806010f0b0a050a0c0605071d04091205133b04020319020f030d050406020708 71
    0x21001404d59404485000c00098002c100612580f405400404032010201c000b8081c0e91807410441c5641c3c040103050104030f0140000060a10030b003442510080e951586040001d08031113000000104019207880302c01140140080041342000501d40069410060041d81084400da0702c2150740325008018180d81a020300c10314150000703000d013600142c60f46001601002e410082c12524010b0140d00c1151480300b03801e0200424a400341c11581c0034421860515a220303000b00040c0c80403c10520002c0101d80307848200040d043d40700c0c00740c0101c903201484100030131131114104802d58900a801410042c4403640440036580144010f01e12000700700210f2502c99954000f500c00c0c01940c2075040008000d40c680d680e00a403502510640218002c4d94040e014102900841d6403007a103094598009000c150322941550340748000b515005c01d00a080301c001d480c0c490304c000d205070014415903001d8030944802107494400420300d01a00c1e04100c00d50042854070098000b101c1400034110030840c6640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 480949001 1250 480947751 480947783
    0x20625020303030c07120513030b04060b0904231c0807090e0a1d03130303050d110310031703040f150204210512091c020f0a03060903231204 62
    0x10b00195200e0007a40700d0564070b40c1c9807810801e040f06100c0b4140010410304000c0c3c840024030401d001400e03603420116540d03007a070301c0340341c10001846d440c80311581c4045034004100401400d4501100707104401c42261184940b20f1150950b40c00407040100c007504111103102503014403540401b45e20041525103cbd840d296508105503445038141c50144c101c548542030f070071441c8200c000c0010418208002035150441c3c61107010340c985581d0200030204400029460102c0d1002c0d0840c0c0c1c083c109004005a0300d003400c1400301c0c1e00e1240c1b032004468459103107503c1030b0b01481e4402900e10440d082904200c2c40c0d000c583d43c407407802c01090301424080b5400e02010a10101040101400321421040395110004c10300340207151594401c62461114000c20003d502603d841e1010211820f0440501061910740e100281c42407003407130780b2580c110f0046000002481584d400240d2024013980301d0402ca8240c591904803400740444100d040c40301b04000a40350150041c481c0c5500600132071021560001c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 480950251 1250 480949001 480949003
    0x6240506090a0308120123060a0809010f06080a06110f0d020901180608090f010e0d050d020c06101a191b0203061306060b0a0e0112020f0307030203040605090a0206250203 75
    0x410348104480c0a001030007d50740182c5c4003060500804948200000e0300000166148217100c0500100580b100c046110307030009401c0080d0107201071800f400100c1e15005965a141c0f020141903819609041c4106000004481201d100c036a07540d022a25090300740050f08040e40c000307035809042080e806104c60000c250804a18041c00a640d202c40c80c9040500c510f5251401c044828416030345040014201e401340010b81e0006080e00c0c0c10040d85821403001400024020903072500401d01694007040fa902c15142070030015190708d0390f00b03c501c0f43d41d0315042018034041d151a6040080750059843c5041d4040ca000260382c00c0c030405e0301908104a03038046424450309880c12082c02380d9402d03640781086068050310004d441c199845c070b410880c3c01000100410461440b4905010103040030b031010110303540490b0703824800406034664a080c801b20040c020b620071141510301c0340c0f9000204603414400714410702d076030341c00401907401d06802910f02c0000352a030f94010390032501c6030030310301e00140c40c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 480951501 1250 480950251 480950257
    0xa1709150301050f0312180f04060306020c46050d02010e1002090d0b10030b090a020f040c0f0302030c040914070806010206040804031209080a05070306240506090a0308 74
    0x4580440c4544951405060007100070309032003441d00c00e0700710302d1040408910000c02d0f141180d0075484400c0e28148600040785d01d403011816050f41050a01c0f070044144a07054004100f600705003011641c03884484492101032803034600d4645081040610110b003004640148070541030728103161080365003e6540d0306891f08108044e5840135135142c1218039107095007400b24140402c02c080083d8a405048000210000d1f44d610000f05481d121401007034440805041c008095940144070041781d0908a0221760754125400049114034a90030300a892410039004090700181103890391000760340e4081041e006900f0007401d03119040014403001034507845c41d0041d071801d060740080070070340d6060000004050a100404003410b41d4081005e100024030b00781c0403101266004100303641c0941c249002159010041c3c0e00c008003d10400c8000710510402190035000c0324411101002025600d12100c50544407524040310010b940d220100050f05207200100003403072005014284c002c1d2680d80c0c0e40c101d90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 480952751 1250 480951501 480951529
    0x14162603190207050f030c090411090f09071a0d051f0320030c0904290118200405011101020712080a05010605030412030207030e060a0c0302010b0604080a1709 70
    0x2520450710005a10340510054024000595560300001190808a0f54600c12100090b016003075560004051118282002407005401807404105003052034540540c04016100d070300305400340c0380d40001d0607211800e095100fa042c2240780c50a0600e1403121400600c1c00511080e98200714080c000c0c12919207070100d40c06148100300d0715206e00301343d021417468012500c1005020f41c0c41301c1e074030f0b500350380c0c07820364866000303501c808090851112403c0140303000400d02100c016a04142d0300100e1910407000700f07000b1152051070100a64100340ca0700704200851001d900c01504020081800694801c50314500148524800549005410307600d58480005020035080003a0015042c8400c2c4401070150600511451600500b1414561a1030700390303000b4031034440c00740b582c009400020107000d0311000403111320080013a074403843c01100252040144d40000c50055103040c8405601c0e00e8048296070a4079202c0000700402e104543c0c94100b01c620401c0607003050070052044200d5540d950540101c44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 480954001 1250 480952751 480952777
    0xd0506010b040f0b0a05040b1303080a090504140103030807052d0a090e07050f030618090f071e171c0e0a05010203030f150f1203040314162603 63
    0x103e2a01c411104040306541012031004420006035940d1948401910107850306414002e0740c60000a802000b800010303030009020782c2d8041003000049070041100c0046074070659080c86020080b070001068440e00b400300030b02161b01c510104510a106401505040400010030380310701d01c2d00f800c4103102140f620360b040046070002034140606070742701140340000c020030085254142050b000252140c09510030401c584240400003130394507901e1940300d02c2262031003484a025030078480d0a5903260b40c4080c065003000d20603034100044204c0c1a00c507280589229500e450441ea042071200c00c201c800040b0700d88024070a5866081c18042c0041500d4030040a80e121021081c2c0214203002c100c2c151036000c1c032b040d03410034020011080310f8907401a50202524140880c82c4140d200010000c1c0b101011141e080514841c049141c41d030000010426203014506482e000380c204c0b25220340d144902010310a035509045000c0084642d00c114004151100c80e0071201c00d038940014141c61a00850920614 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 480955251 1250 480954001 480954007
    0xa03050105090c010f0e130209040903030b0f0607031d060702030f0d0f17070e03030d060b0d0e030307050706020304050c090403020a0c210809150f0a0906030c08040605060d0506010b 80
    0x20b0340304208541000348400303090100e14100241c4000d0501c0070809822401000c0d03401105420000a0741243c43c0c180001f0410030000c800d03420010700030109090500c2c01071030060003810007440d061060f5466540d1594801501050071300c440ba41c5a510407540e41d8000d0014400000103907028080246881086401405005000c4038010910b40c4000e0184080c45120710781c0038546901152a2580301d1a9401d010a8421078113000c2450f601c1420750b4189914500100444d074028200020b203c0b800d08000140500c03c4000c1049860744019185400403038002c01c0b12400055030ba4000d90b9001e0b0003482501c1501c0f4402c00032601000003124202c0c01a004060740d1410002c00781200c03009000500a01e4002100340000305070b45540c0b410029200420110343c264569a5014250003141c5c3e034403030b24070307191560440d400c0290f4008180b04400b241440304d0100e802031003440f925440460b10781d0782141e43c1d119611040000c04000d030103150843e402c41c8410000c1001000214020b00c402528156 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 480956501 1250 480955251 480955261
    0x7240506040209090103030c021503090304060210020c0601120f02130c1214061203160f021005120c180316080c0910030803130c0905010608072f010b0a03050105 71
    0x8541004100e907100e1881441016650f8a400707034100d054a9041c20080790b0b40c2603a000051080c02821600b07054a80c000080042d02e01011015204550f10364085515008040703c003001a0f0054010a56007030340130200402c029055544150f1034580904149a90b515040d004505c1c000d4644207801c5034261030b00158000b480e8400792014003080301e042d081002d94000c078080355200f800034014034401c1812041c0600190024401c40344d60480d071406642e4012814a4010b64000c111107041c1d10a030710303100f04001003501400403144001d02080c0314204a680b680340c001070540010340d0598505045010840c803d44040060001c072540e0841e00e45200e9180812103480d0000101100740140e0440080c0900804000d0714002034030380c0540c1c15030312665411445035524002d244094020403584400091411540c0c1c00b25060310200c0c0c2c1c0c1d845043d9240041614880850500d41400480900504a460300b20104803400340300b529001080e4612003038000340c0c1d410065001501d0903503565040c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 480957751 1250 480956501 480956573
    0x7050106141c030903030e0105040503150a050c0a1e14030411040e03040602120a03110a0c06050114010203090d06020d09080417010506060d0c0504090615090920070807 74
    0x390200455a103546802c602035a80100450140c0c0700040034814038030300f0b4100c168001c10603200641405822900903202d050814405d07a003068440161b0b4a01d0f01d00410031050b420000c54981d1103c940f100c00c0381d112420120f003103241001a04004000381041c58080300d211101c02940914022907030251030300710074000c20044600300e600c20175080e4420481009081c1e00440c0300003070342868100d683e449806550080d005054140030020910303600141d244c0b01190010420b40c41a03000310703401c0040e030783c0340d5140302c2e6501030907242240543d2060111084610b0010f0039480524030848001d03003841003c06c4048140d403400c040c22140381c3c01c042001e01158007040700c00c0c465004200000e0100c1d06240f0082200c62080f40c50304000705403580c1980703004501a40448009100c4003400b00841541c5598200e8504071110a0b040000c0441800058080e440d020706411018901e45541c0a510410b034009280d90280d00700302c07000217082c00300001060214001046e03007a031045000c142803140c3d06d409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 480959001 1250 480957751 480957769
    0x1f140706020d2d060807090b0a0504050711062212030b0603070c060b030c010e0d06060305030a030e010b0909070b092e02190803010e130c0f05120111120c0705010614 73
    0xb4115003481e1110410064200145403c01c88031020030002340320703c400f0041001518a40c0000390003505090a00c00d4966100c000140d91a040b18145c070080d440c0c0c160701700c102652002c1c0656410b04680055004541e0342000c20b04144502c0c02e0000d00c5440300008516030790000c5407400301080711010360780d05018a50044080340f078003c5000d00300045a000020f040c1d0140718200d10700413030110500200308640c0b0750148000e5a00101140d4a40d0392012000303000d80b5200b00581019403d015010100c1c1c1002c0c0007042c080c0c151039000c5d003042030801003011a103810001c05640c0c80800445c0c20115051160848103443c0c8500c403041603e100e0070340c0040d150005809000c603055400100f004041182801524156040c8a20043d40c984a885100c21010821390f00945100100403000500000003c1254201d86007525800096066607a0007400c07a03400300c0e91080c140004105074008441c441001991004e210341041e400c002803512082e0850703550b03421800c141008001e00f040d15203045120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 480960251 1250 480959001 480959081
    0x1050f130312110f0d03020903100510170307050d0f0215132d120903021906030b01021603110312030907050906100203070609081c0501051f140706020d 67
    0x10030030320a9500e10943e40781070f003c17802c400305540880d008500745d03001e000c49070690f251017105000e2802c1084000308211541d1003000da03140707000c401c1052203900200680c0c41c05604200600b4480d041c0020a81d410360001104204500a00200480601100760590301402564032001c025140b546440c0740300344045041c066241c80640201d82e040c1c0045d0a05600a580c0004001d00303084c4441d600395a032030a5600000c2d0704c030040e00c003019188040142198115030340c80d64284005001c65006903140d9810603d13600f0f49214075030091000c60109045000b21600142c101e40100d211404a546c0f25041a2001c5202d03070000d010401082c0340c10011650809401c071044144070000040c081c1d07a034419000c004120a440c1d21400d0244004403060390589003000c0801c100300b28070705a0340c4c0020300090081078800c0300500c40400c0c02c00d90b40d0000e400301d01207680b100b1081f031b0701030354645800e030700120022508990200220f00b0408044d0040613a03c2d0900400005180c0001000c04420b1100d900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 480961501 1250 480960251 480960253
    0x130314010c090b07030f021507030b011e0c2411030114150d05061f020f0601090902090402120f010204091d0a05060606070c050d0f020117010608010501050f13031211 73
    0x180f00400e183c108aa81d201d80c9400d221800100380d610070f900701540d210702000c0300ea4220040103091a0580c000214020003607135075050381c0308001032690440c02115036a02c006414040c0704400106441c28240403503c0400301440045070a4412000b5101c14070b54000808102000410002c03503051290180345104550980100c54001d0185501e03002d0b03208420324042c0c4600100d030711030701d4184c44240312100310208082282e144420217036988544290344961072042100000d8038103028441e071602103600800340300c896119a020000621043d401c00303070803400b55070862282000c09200400c000c0007554000b003490b035103464400100280c140185486d070b0b0010103844000510204580da81314070202c420588807603141c100345080110541045402c00c04020b09002440f4504507503a4245100b44d03140c9912500d84a80e1740304142003846820042203098005004030741c0200054603c07030700f8002e4011305090581e1400642e8203942e6105580300380541241038900ca42c400455010311183c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 480962751 1250 480961501 480961517
    0xb010f0e090d020c010e01030b03060a200408030d09020a09020d05070e06130e13061104210804030305280c020118121101180b0301062a030c0503130314010c 69
    0x241e0081d444003841325409040003064044401c150b8000c0c1d1100c1c50205016040760414600034003420010850898030704c0302e4103101c0c410204a28003010499040e030b0112400307582050b0310704000a02030450711004a911214020740422030312403600c042d102519003102c0101c0c403800d0095000d031051001d52507003800392500b0094405507200741a8058200c9100b000b1a1016503142403104200700c0103003a00510490506d42503480d0701180700054016a5440041440c100030f00706280c07034400d402620001e090700000e00041000c41e00400260140c2a424540c030880f210004a680682010f20404076000c518051507410940d41e106524041c3c00340000120b60f080f90500309402d61040d041305008190181d288181c100c07591064140102c901e0080e181411626280da01500c0d898100b40140c40002d03598802000c102c000c400b0380700042250320b90780c42c2901e1042d51801c4a44102c80c50058035144000c004002c1c005501c0222b80317009500541d2014403a20706030032000e01751103040440c401002214 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 480964001 1250 480962751 480962773
    0xb070206092b031d0109050d06180c03050a0303050f01080a0f02033d0911090426040608100f0e071106010f05030607020f030406030c0504030b010f0e09 67
    0x181100d203158801c80704001c640c06240500c030800310714241c0c00100802c0d20811403041540280040b8078004c1d00d0010f200020012030011942d50400d07124543c1c3c0140d10700110004280d095000004905a081001030040c07280d803184034000f56580d00490f80d59205080040a0507414801d01d0341040c2514410b000381d5141c086215541c1d801c16002800381c65008410008651342040500f01345a460040020141040c00d4482d6100c440d01e417100c5080c0702d002201c1c0464291601c00e03900680d50091a016003030b9100400d2040c1d40000420860320a040380c03044900048100019010040356110440e90f6903007007080050450f003001d0261041864541428032090411404a8041c0c5030303048541d2001e035940d90000c07030f00c000d8a030b05552110f0140c038002040e0030744004090010349009404848054076041022a03640c018504079198640041c8401d01080d8461b401001401080340340203814580c0b01d46504841100c00e900503400c094080c0000c101c00450744584561016050020b80030b20040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 480965251 1250 480964001 480964009
    0x6030c030c041109041802090a0c08070311271309020a1e090905101a0a2105010f0510150f05070f080a02060609010503190602130e090709060b0702 65
    0x2815180521594075a0108024140303c18140e0702c403510020400d001c07443c018480a40309034a0098143d005030003c03800540108040d004402164100d5a0b8021507607032a00070032001440070b0f8007a0341384c1c41d00c104003a280c070070030a04902c40042d1181c0c0b00e11000780681c07010000a10780c00d443d910940d40c24111807001590301c414030b5008031801c40319440102491051a11800081608510801490002028180603000403000701901d51080104001e031078a91018507a94001c01040368012038055040c01110300d1860f06003040c00543c038400c11010040e0340c42c9825103808a10502d00c00c0e0350b5008124000201c8141200100480721104030018540d100081c000108115038405100c03002420340100620300e4612804980c1081d5407607155900c042d0000e4403143c0a807075882c070a52401001140c40d00d0003145005403201c0700c00303103d2420a55a951000650080d188290900c5680040051041117a035030851007000e54102402c20715003854205402c07580d441c0c001240e032000610080d00180c40f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 480966501 1250 480965251 480965263
    0xf0c01020a150b060c0c0a050402030610030905010f1d0c06040305121e120604050f0112061d0f03040801061e0506071104230c070803130f0b10080606030c03 69
    0x1411824611002c0e0448038000c02500c412481d0a82080001407406030440001c03070302d142840c0040328040c0e840c40c2c1d170308100300c103900050f40d62940c4030907800e0709e1105480c001c0d481b0040d03503440341e8008150f25101c00c0440303046401d4040015102e04040360640c02100b401d00001000d09811a00e090420b401c41d2a00c035652604401ca40c421210000703a525100601421134400ca1179520802c55a10040c000d00c0c84081d603003d07900c45000368104408103080b0350700c1d000c2803070507507400d1942643c10b200c82d6154500074060454803400340510a20038500e00e44400d2000e442d42c84010340046559600c0c0030741c0c40f42100d059520040c85004143d40d004030800d120008802150301c122042038813002a814121848079010340f040b41e00c2880d200d0014003240304070b0115001e0301605441000c299480950f02c04191198440c000d165500c03c0000a022985241000c22401d0007107604c08440c90065030f90404403502036039802024141a0800c01c07a501e010451541d1010b016005021280004c101080da502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 480967751 1250 480966501 480966503
    0x90503070f0804080a200307150323070503061e01020a030507061d010c0905030303090c15070605071d01180303141c06050114040b030103081c0c0906020f0c01020a 72
    0x10740c246125109009000090301c010700040d0342a5100c0002074a400c880814006a2410004420444681c600e2902049000856503500003802d41d00310710000480c0103105007182c0000800805000340000403151040394881d6100c1d49401e5500e0030704104101220b020344142405020004420100d141d03400310f1010906541410941c0d151442450710070084c0c16440803c021009603205451000b80d01504000400764240d05d48000040d118018503460744012216002d150b0300401c4030110904169004c0c2503650301d60300c001400c001051781c50606455080c1c4d1040e002850300203502e004076104108600f1b52043c00d0800d28040b455180105003260340c10b00c8042d092103000e00451190101020485548295140410021780f48403043c0000816060003954001002446201c590040c00c20840e4185c0b400500c429056030b195581d803440039031140c07074150100110071300030000044042c01409002d040c01c0d00c50580b42400c046000b4902405000104030781d41c0306042013a01d603600820761807201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 480969001 1250 480967751 480967763
    0x6050c07080f071a15120d08010b030a0908030a02030109050a062319064a010c02040612050606010302030c180d0c030515070305061f030f052809050307 67
    0x140c0010300303000e80000c0341081d0000c1c820b8032000401c100e505103c501d81c10b400320b003110a1036401406c448007558032805445810046503441006000102d070000166030b210404d050041000001642ca40c074154109580c0003003002e03004401805944003a005280d0b10580c490702c10040245000c11030348468102c04c0b1491050000007260711456101c00070200d58017004001e44442030b0b0342e0751900800f409d00c092424810514202c88842c940000e4003a11514261420007008042e04081d42d80095105c18800503070500c0000e02c80a801611103010308002002d81120a4481c40c2d050300300641416001003c40d4101441041048100ca10720000e0790000191f00c41c50004c8944139130f0200c1c088008200d40548628140c28002042010004400c07905c00b04501000d03405403928982503082e1181500c8040d40700103040d5003034140b019207801400640c0d84500c0e01241e400079407244441120740a4403410981d10400000f0000440d207103842030224621800208180f8805444468a070b000c0e1070320040c0a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 480970251 1250 480969001 480969007
    0x30111030a020a1106100612050f010e0a0221040203210301091d0a060b010207060c03020c060309160f06020c01080402130203061f033c0b040e01020d020706050c07080f 74
    0xf410320920304041c09100c048111075190400500c05107120001d8804c82000806004041000032024041c8038098010059400c0e1142d0030000c43c403104000c0282800e07001d990071301c8180003080946560045000303041c075000a0030300b0240149403c24492100d00c5c9031400c4030611640702e55030800308981c1102c44122001a20001a0302d080916400141801c24144910f003400c00510407554000000781000b40c08440b111a9580b0058608941c48e00014015030082090b00c3d00500f4400011130340010b504040c2c4031292403c45c413204881850741c01680030300240c000b0a001d41a0108440222420309080c902c40520b4698002042c0c600d0b020021842c40c0c0e0080042070541d20791030680c415089a40e12190f80a4024100043c020000500c140c42c012807090070303040548515050784110b011019031404680c10242c0d090002504c00d180030301e500203a03910400b0f0424503081c4040c01003000e10360009a940d0201d0706000c02a0f89010700011407500c0d003081584009400741c022640c9020041508940f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 480971501 1250 480970251 480970267
    0xf0603070e0a0203060423040b04060902041409010e072106020712080604060e090d0e030f030d1d030301050a03060c020328021e0703110604050607050d0905030111030a02 75
    0x428282a540004144081c480500c20118125006948179040a540c10005110421056900c0740055100c1103c0c418440006c81c011510341d10345a80d10038083d95010403000451703400f00b000c56405003000c041c030b48292810302101990a018400400b40010002c100e41810720703465902e0400031220780c100c0041c0342c0754000c041001c580c06950720580c000141d441107014000c0082c10741e01c01103600314816464820007007410804865500e024625403802860051075023801610b40c40140c0619982c5442003a104000c80b50007007000b8200041800350108280c0d0300c001904011b5092400d4002e0380d90824001030101d502c42c0c0c0301c040d088039007000f000b00c0e111000440076800d500c00c0d9800650b00d40300e4445a00b4900c806008203050f10422a405c690000c00090303442c104a1040f03014401660b00007960800102d40f2030851040101ea00030304c1149029601e00010340b0690090b84101c0341070b040710310f00300c0c0801e42103000103006040507402071100d05000da00c00001480010002e1028907070100d4001c3c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 480972751 1250 480971501 480971503
    0x705150c1e1b0f0d0905220905070510030902090615030601120b04060306020a0e0a0308031f0b13030210080c1207020115080c3a0519061b030905060f0603 68
    0x4070088078072009541e540c48003d103d858980380560503100c003182c50104006070030704042442d00d003011901401c110504040224040282078a490240c0e03651044241c00b168964903480c506501c4045030b00c00041010b614814808944401001c11384916004064a40b0300300d400c2040b1b950041007403800310707401031079000510024040c003204560000c0c50803401004101043d40100110b07070300b54440c880b100c821340b020002d102495010040c1403d4081c40480e802889840c02460748090560030b9020868481640c84900e80064084001c1361010030010015800c0003020f03542c0f40e90281c13402c6002e61134400480351882c410b003075100904000880010b08543d100f0342c01000100d00c40c0d60b208030070780d503584820707a07860325000d01ea503100344030320310182e00c0e032100c0500c05140000c1c1a00008216004c1111380340000d030003442c030030340301030292191200800c20352088200d01c1c548529030009980600f0345114964a0602201c2020f00d4581412040406c40000d5503503400103040e1700d055120b0749c44a000c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 480974001 1250 480972751 480972787
    0x6030f1b0c020303250b01090506030c120703022d0603010e0411040b03060a050114101b0c1d010603140702031b070f08070e0601020d08010e0a110705150c1e 69
    0xca000c2101d17441d10140c070359480040002c0355800b40304680d070030b80d80350b5003860103da02c16202540c2c550700903000107441e4201200b62004102d03000703003543c1c10fa513600c0d00880c1d03c01c9203001c1c0301c2035808503840c2211500b840f0f03410b4085404509494003419981030502c40450b0b1140904051700d050006400c1041e20340e19900700c011042c0d8043c06580503800d00d111020060305080c003e00b0f9210110400c10052170501c0811480700080c076566104642420b0140d1583c40760b11a6016140c04840e08804216500007002000221840c04003c042c55072601800804880c020a40c102426840005004c141c560000c00c0d0780280b404009820002c5c0e403100076051500400b50b01610b800c0004440c000b81c0030720041403040032640708565107200f664544004a03111031081400e200400e0b0000010700035003c60820159000b81d0f11680001c9100841c3c441c0c00c0d00c1d4100b240e0071510b070343c0268105c49407106007840168010004101e0700381418503100e040c3c07009000d88261495810008030b001080801a8a01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 480975251 1250 480974001 480974017
    0x60f07061803030e060a050c0702130e01181406041106090414070c030e030a020105030711030d09080705010b010809100209060f03010806100b0f04090f0f050c030106030f1b0c020303 80
    0xe007940903520b180150242941680d114045e01031a40000e4600019006d080c0c8a259285052840c066280e4208200c90001c0b01404400300d9803026450000d11091050440068254844034420380080c50810003211000c1c120600e503400000c144000a1418006081107403422556640c4070700851020070000c20a08004000700043c090511030450b800641c50f80040f40070307594041e0300d0f030125030515981d10007440000380003030780400014581603c2104610561b61281040d80c2c0307002c0755014a40280c1d43c0080003a10300d03040014218040050034030803070070203010a003043d051034501b04050544030844040f1f0b5200322070b0001040003255648a00f20340500911000342901c0756140c1d1207050343d1341c50480700729a4020b0144004202080f0040a50325101c4192910500e0b00e41409020301c060004c80500c4000f01d616040d00300c944295034002c080c0714811703095030740ea1a0b42c03401d03900030b06a8000d05907007880640b8202c030030f2440c401000c00402c554400d900303102880541030b00c0828694030074015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 480976501 1250 480975251 480975281
    0x2409060516020406030b061201020f070201030c0c1a0f090a1713030c03080a03110705072102060307020d090909030e060a1b0629030c2806030501030c060806060f0706 73
    0x2c80071040260140441f8024401980c010030700211602c0c00c0ea00300e105030140e41c5e0f0612400e2200b0001580300780c10484282c4524542201c42ea07400d0381d42e151068400308902c07100c00220034100a00c0c2801000c85a6100041100402505203140c80e0380c0c2c01c80c370b03103440001c0405d840042c001d00c008030158500c0300210380c851403600707002d0ba8a00703000585801204c14400042d0511100b4800c100f4924240d50308d15412102500c0603138a482040c6280c500c0e0b0004c074a880b0030100a401c000350341c0e100041c5201e0245600a00540d107401880127046001d82d82210381020300e440c606101095000702110b0100400b42d0700b241c1c0e2100350000c280c609820b48084a0b0b500b614407800c61041080719001880c485140d90418074683d0881c1d15900592800d20703014682541c842c031307112a000d10308501480451001081c4501e548064003c104c001a48260000720205e40c41d100100704004600d00000007d203624a0700d40e019003400000200075218400e55001400408039426050211a83c01b482410050301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 480977751 1250 480976501 480976511
    0x403082a040f21020901170106030204090837081b07050706030b040209090412270810050c0909150405040c03150c050405060703030f0e0724090605160204 68
    0x1000c54000c40209003d83c5880c0d02d81d40c0c410300d00002d035203a450710415600400e502d0302a803c210311841c0205045c21941c0c4590f40320762000025071510300c6040c009030b0241c900d1700d50398640740850b03c000740d0a20f0084680511010040c40c40d070702204011841e040078500d0040c56a031240b13203100c00c0d01000340700c1d030b817040e90310002c0d004007001400a0f03e1404c840007a02c06025441c0b80030108001ca0050402c015006400c0c08005000203c843d146049200c3d0b0b281422024000c140107101860001903a503050760041e900c405114018040001020381ca02c4403000f84800e03c0c2a0703c101a041c010744200700d0164048101080140e150b0300107020880a01400400042c54542030011001190b444140c40c1242c10101041d000521401900c04680183c0c07030b05032400d803800003800815400700300107404241e610b80c905540303c2d6842c0296442a80c41100078030b11107080440e0310760480c01c60300c0030050f03980c02e1500341301721660080300e00d40c01c803112030501c640c4420003030151021560103000003e600078940 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 480979001 1250 480977751 480977759
    0x41e03030b1809120406120b0414090c13090519030207081c08071106010509060a0305030408010f0b10081603060e070c150e030904020c0307080412060f050403082a04 73
    0x81a0a44500700b04011a4028044c030b1940c0001071190780110000604901c110580707484650308036403201c4a0140000500e01c0b030048072a550071400b92184152600020310b01004c600e402c20342650710b101000420880020750750703a941d0b03558024200381c1512602d1b5025000c14103009010700070040500c1810380d0809903034281d041c07401c0824107440e01d02080ca1200401c00b085d03c24141d41c003144011500400c0c0381e0342400104140404000c00d802d9200040c480d0210025009001a2000302825400450602c8110035440c055800b1324480320301a0001603202181e03d039200700500e421004100c2d054407075030700c081000c03000351032941c2015070074070b0800c403d000b00c20307508c03000d0401100e0162081e400c420f00718a4100c026a503070382d2505020366005014681e998034160f401021005040c0c0112071501e80d0030b030350b61101a00309a001200c558060b010b03c0c010700185000f40010009100c80800c15460140d801811502c13000e81821381c0083c031213101d1001c01151110660200c0040c0c00700a0700c4e1655 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 480980251 1250 480979001 480979039
    0x10e03070b011d0601021f0b15040305120909014209050a06050a03180c030b010e0903030105060a11010b040e0f0f0106050306042d030309050d08041e03030b 69
    0x3031154042107025003408210a1030521686401818164041c07c034040c039030050040c0041182800b02c0c2c00c599100b080c401c15030b0f91201ca0140c0c1d40c1075000340076207c500c3c50901d142000460000310100c80d404000303007411503030f0340002e490540d80450010909071008082e0030881e02140c25102d035501c020900d8800c010b80112101031429003055451820842c1c445003400303410b1040344945400310f1000e00040210030b020350000e000bd6112004104400c1450344c8a00140c5c09003540150b48031040c00d030040c4100150044603039030105c080d0008601e503514142c0443d2131845a07200440401c0012010040c54440070342000c112098014400e0058600b85005d158661240405410300c0c0d10a5008901d56010f0600440044840c001d0240c072241c0e581d512180c034a4003054244001d82101c07040342506030007400411303441140c0079941c0010281c100d460698608808e8180c2d0006000c3c2e58400c00c000148a0f00000e02e05a12039001c0309201501807805901600b04d601846510948c074143c45400500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 480981501 1250 480980251 480980273
    0x5061804030c29150105030106270e0106080901060302010509040906180b060f0d200622051e0a18020f0301090f05060d1502181c05010b04180212010e0307 68
    0x8000c1100001500c40c0070940c0e032130100350107100340480c00c20300c010000d25020307103441c80d032182034403900542020a600b042c0302d8040041c2c001d044140030b02001841203a60025040b40c0c4021400000c110003400c580000c2c0541c010315031428411900c40e98180104036140d00200401c1d02e0580120301c00300540d280540c24481c04841490041c1c612110188562070500d101540d00c50300420b0140c1d5607044400200c18900144040c1604140200301c012043d00e5440c1d0020649a000b403060001c450900d01005013040344600940c814402001302d543e0140c0d03501c001039040300c100000c010401c02c48040039070003074047e26130904008031011000140c0030446400082604444003010441d80c2e542c54200304c240d0740c1d0081c025190f01b092000b2011480003c2d80280a04000d601d281200340d425000014044800f410001c45803100d03503005042000800d00400c2c0009100312420310030b5114a40c0e81c84980806101d020780314141040d101e844800d400e60040c000034400301c00341c0303544480718140b1420000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 480982751 1250 480981501 480981563
    0x4080f06010806070905060f0703020c18011d090c04150b3001080703291807090e0a061e0212041202060601140a0e1018080105061804030c 61
    0x8003410f0b001401c228800c0500b0700035141c0060600c0d043c8000012069400d4201031400c50070b500c41c010100d07030b83e66251021300703511030b5066200d4003d41d07040c5454000303900003410405000000d04410300c440041d021410040582040e50001007403882c01860001100d001d510003c0c6004002031400030022540724184081c10361400c9506905c9400c120349969800e00740b203821801d8110901c14400210b1950300d800400b500c00d90540b415520807615441803400c291480701c2000c0411403405030034907060000b880180180c4800708440c8a030f405450351200e2020600505165a60900380b046000394a8152120120151704548941c2003040e1201c8000e010354064030005004508484107500c000303440303442540d040c0d403102000b902502c00504290021a9004144180c404c03500010f510347c2c2070303203104544403036403030614183c0708000489050701a40c20004250b41000104055902e5401c02019000043c240b030700d0b825035450404484080e24140000d010202003400000c4e0301c6100061311200d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 480984001 1250 480982751 480982753
    0x503010510081c051e09010305060111060121050f010e070f0b180d021203030613060b0708130f0f051206370f0504050d021f1104080f060108 62
    0x1603160550340c010044403910072071140d940b18080c0c0311607501800f1116503d00c4610b052980c24002c0070066100c084030000702e218000280403070740d0595580d0500a0703940190b002c0c280b4032a46107214190320745501050040c4103070054090044400c07040c2040c0c03042016600001542c2e14194500c1c90705000e480c043c244080c040c8100c50000c1154034201a00302d0403521400111441c100a007040103190480304845603a014030340e0000341000d0385815281030300c90302060028696a1400303a040048590006240034000340c81c244c0184651180b480480d204107801005072922050089084d8645d94040e801c5150340400480000400c1c110f8600c1100a0300d0045520a15000c1c03000003040d602c3c2d404540f80500f5078100109500d52603213207560b03007100983c1020300c0502d40d07500b100c00a05a82106c8903503040c6550301c20401007401028403960492079102e1019140c0503040324190f00080703c80340d100301c2c000c075030b11401105400070944c01c54008280084c01c0d01e000320382c00306c01e141d2641024441c1c0502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 480985251 1250 480984001 480984011
    0x70807050102150c0a0e010504090212060a090c020a0809121905010c140702120f1501051003020405100315030b04030c0615050a0b03060604120b040c0506030c0702012102040f050301 80
    0x83e02543c64030300d921030a014440142811038911084420711401989241880020400840c101c00785000030481c444c003180ea400300d18100321051100040741070303200440c680e01d05180c804486038041100400310703400c00300f01c944070118071700000c28034904002c103001c20f071280780c040080340014201c003910b803980144002c000c240100d540c00c6c1c41c003040010100c142004104219401031078500044208580ea10044071108036608100302d03d0000c000b014660304500000042240b031900d0f29511000440d00e1500307500f810300c0d050114402c00b0401c1c3c11f500038140c40d000c0102c600b00c00c505000e030096800000249641c1464140540f100c100113130300b43c50b06424003206140d180e503041c604104440340a0b0045015900d0040030600941001e060540d106e102000000740704403500040c8503005001d92040c01c810708092400c110146001c0c1c1c481801000c060040010300e40015069600094081c02c4c4400020000c130540300c680f40b800300b034640782140301143c04500a00d40e60f0344142a070740300b0303802006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 480986501 1250 480985251 480985273
    0x40309080606030c09280c0306180e0c0904060b151c051b0a09080a05030a12060b0702130905100f0605060403051b060d02390607110f070807050102 65
    0x1441e41d24981c499500b1200b01c5010450495803003030240c0f44149440741c40001601035600c0082a80c1001c822100000d482e080140104e02c4d105000c42c0d001c0f5410ad0b01040711890f110302c80380d00d46081d03c24441c840d00440000409024254110504400000785002c1c8064040130b403002042c1c000000f00b10031804880c04e8580b000c405407040f03a008014020101d40191f84021440c100c541c000c580c000100081c80c0300c00120310030100700780d18140d80f141010310748038000d4950090504114070b4054514900301801009842c0c10081100c10b810380680d0403140501410b810f25001d050308150080451082c1520f07401a121194030480d541e083e03a810620007290b5070001c01186000354000a003280c2c00820a044c80f150600d54180c030344900261456040c809540140f10890f08580ea61007121240c03004000f1032840c94540d04010040440e0300b41c011040d5040e940f40c0c0d00d41008049030140100d141802d110000d080064940008014084618058032072005036142c00035407007040d0140c4503010303202ba = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 480987751 1250 480986501 480986503
    0x80a0504050c0402031003051209040c080118020a1103030f0123211c030203040308100605160c050607060204090509010e150c070212010c1805030d03050c0d0504030908060603 77
    0xd0189030010014110b00c00640100030080d44040c0040a400080581c004000340c01440400e440341c0c049014542c03910159010300054440050320781c0208100310005200b03401003500c8070105505046401a141d10350031106480005214050400a10001c01044541d14a0000c440c0c142e64901e1140041010301265080045030711040c076a5202982c614044152980080c1000101141904690610200b090b44141c00d08800c100344000076000410801855040700c070790398100700419000303601e540c85c000b80100140150155840090006890704050094050040f40030300300c001c1526540c3c070a540b92640c000c0d4802c0c4540d01845003050f00089106030103100c2d2820400052010309800f0341d0070a100182540002d0050004031028800c01e40542c8400d1002404400810f0000802008036600074140f460400310700601d120340403a003800742d40c40c0410709810141c142d04000c41d640d150304014080d54010030b030f441841140780404100500d64031102000c121481181594000d4942e00241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 480989001 1250 480987751 480987761
    0x2120c0d0f0228033305100f08010e010312050705120d060f0504140610020f010c050307020c032a0609101707030908031506092d010512070c081303060c080a 69
    0x7005100000e4504001c2c2c845e0188402c485501e08070340030300083d11000000c85803030004020301c000401d00032500701c80c56000816240503044c40100501c0e0366256998000003030140c521580e00300700011802d0001c12100300b0050150000e4000070365100c054543c24107004121510914500c080d000e400001d2505240c03148201640e8000b42d03d010913034441080c09850a0261001c1c0114800d4408041d04d400080c0315602da0640d8550b00c00b5680c0c10402e0307000386001400800280300c2d17000965010341810721124410300482c50f100306905400c0c8000d00284050042d2101245c202c0c4000102040c01c6038018848000a003480321030303000c1c2d903e0718482207086548110380202118001c1000c0794481128080028440d18000c002620300b034000c1001c240b060100c4100071041038050302c0c141982c090000300000341c018081c80d09034101000001a0300078684043c4c48407080c4107000c3c003030306c090054810413251204150070702007507490390702e1404400501200381e04000180303c42020502e1648580a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 480990251 1250 480989001 480989021
    0x2030a0809180c1b0a17070c140f040c030e03042402070b0f090a0504090c0f05010e0915120304060f080a0b060703180503010603050c031002120c0d0f022803 69
    0x41c0d0f42c2031650051203034480c5260540a400300e0f201e52070078240002c3c1c1c000b5060500720008030f03000303494070740a140c0140a480a50019108640c40456420081d21480341c100c1c03600d0782c116000300f200c102d081001c1c1c004028841c40001c00303010004d40444c101800000311018420490b1a00100c4074070310074103e071911014010340c4070000d001c01c2030082c0c03403108402401034000d000b414081002c1da6003000808a5250040450358102444400c20031003907003513007a000400d000e0810b44d81c031004081c00100c0000d401000750021080c804603d0078075844194a510820740c03803004807991151501c0340502401d01840ba0900003402040018036040c00350300800c8603982c001b0f000b660a00368165410f5032542e861010b14114079074074010024003907a00f40078400c021400b071806421006120814581010210984d100c45507004010848080140701903540d40140008501c0d42c0720b180204c942e4000e08111900e02d441540041900d091100b800e080003e0311040c2d01c03008400d80910b549064003a9010320034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 480991501 1250 480990251 480990271
    0x901080d0305040c0e1602060109110f0309010b06120f070f0c0b0a0e16080601050f0a0e0703180308180a0c0909020406030602040806100b0315010507030c02030a080918 74
    0x40c004180241c01c4207411510620800c0f152030b8a941d07040c40d00f14011201000401110031301d2140742c1f6014000b0310f0251030740d00814404a421100c8015080c803800a40b416411000000104a28400c0d8030103200c1004c0100360f550394070303c070900400e0b10560503030301103610031045801b246542e0f01803884101c03030340ca41e0745a900780e00002c0d4680c1045907400400003011540c896121701600034ac1403204082005a03550f100d94602d0406400c0e0340780c220b051304018080c0d428030b00c807104903541d82c03040748086903a5140340c40d880c4d6445400c11800351441001c440d1243c0c5043c135845c820103400c0403034280301d50000c820404504203403c2d50240c0d40e841016014002072107802041c40760710455000154094009031001c0792140e0f499440c3d2040381d00961106086802c00020301c183d08c84001200c4005200c3c1d0b00c9000c0c254240300025001e07070006000a81d050120004062041500400d0034074000fa4006064810010890030b098185030b210304842031140381c6e9082c1030410900201002401211122 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 480992751 1250 480991501 480991513
    0x1413030602071b08011e020a170c03091009210c0605010e04110d02010f0327051b0604180f06150903060b04020c06150411030a0b040c0503060904030c060e030a0507050c090108 77
    0xd101c2c18020340c450108c0004001d01210501e0812110400703203405802e01000403952403428038076440c20720070101c900c0300c402400d100c1210003180b0490f104046c45008902924241c0014031426105030f0368a200080c0401d0601c0c5c00003988800611a06208601800012446c42e03840c008108a004041c00000d0220350224045848144650f200c01007540c20611100880182c1e61540c0c0c40350622080c0c00c440310360003d1b0b0340c00d48211030907455440c03022058540d9424642403900d0040d16084405980640a59507c16500c20810540120005082c45440340d00c0c0d00c0a2a14000c0041d08180402d07500700d400d1090144440c1803034404c40360b9612255000e882079131610f4119081544140303052580c8240c5030000c0c04148144075000318000d0084420000381440341e07405000c107481c0300302503504c2481000d204004140d00c031808100c0e40a9454075114481414501d44074005200d890f810300620311021031407c42c0035070400c004100460055049826410b00c003c00c00c01840024010002c090b0805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 480994001 1250 480992751 480992801
    0x801120b0601091e050f010203070b010b0d02160308060a0506091023030f04030210060308040902031f0807050a150509010c051c0801090515011413030602071b0801 72
    0x4180075007114052601c0200b032680d900500d41c01804648a5101001c0c00d02010011803a100107401400c1001780082e6043ca82c0a0300d503210b1031081403140c0480c0c07810004500c045010f890303044400d500c030107a08500b1381003a01e050003005044103c9000c2d016107140d82010581c0d280c440d09917013001900500c2a0001c1c01c00c4602240c4900004650849107100d0f828000c4070000d4480c082e620580c20b503c1c01e4001c0d45003d0400034178284440709600c1200d441c000301880842c2c04001104c0541d8405040580d490315001e20120000b42104501100341d046041d02003400c0ea8042020b00496a003220f54582c142e0301c41c0001c40080680c1e00120f808504c0402c011911035004118650141e8040c03015204684400d8100555602410790344000042c0004018898001248512074010603940010b40c082410880040d02b840e0407140e1503584000081402000c41400b040d526000c6c5038046000c4d516500d5510301500c0f69503c3c0b01d000c1e2103a5130b80d03641c0851410070510417161000c01c1e08400ba621102c403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 480995251 1250 480994001 480994013
    0x80906090d03020715020c010e07090e0d201005190b060909063f0a0f03081918110316030201050d0b03060f040c0504150312092d0501080112 62
    0x213100480d1144640030b910aa110050f101400c101100000003007600d8020010013420104580c00c98800c140c83c0904c030301c030036000014a15080030003e007456401c1e0590f14466000900010021120b04d202c0e00c05c4a03405810a5081140100061600002c010701440d083d20191680c2d400c0e40364004000740203101c41c42c6005111250400d102900014030f147d07103880b11080c1080d40e003240c80700c95140904154043c04107000f02001691800c000383c00980310306d07924440c030003c41031406402c01070f803540030424116002c100d03904402c0e045030040010624142c82181000e00080b0709503141000c03030200c84024140481c0d4448800002e00ac4414154159401910315400003040400342c150b03502242c56203520304004d018003865031206d5030246864103281c814100b00c0c50703030001801207051225920f10701c0c1c64038100009881d40000948400d901c0350404907403034009940038a010711402c2a81403680f404461144190042c1c80c0090340a9603103620040d44c44940c00e00c95010119100c0c001803002c542 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 480996501 1250 480995251 480995257
    0x6050f030a09020d0b0f01060503040b0a0f0b040c02010603020307051801120f020a08100506030c011d0d0506041505100608040210030e160801150b16060e03030a0c080906090d0302 79
    0x10400c8800290080300c3d40205421000081003201e4540e018001e01c21244903540d4094018910f9140c5945149029914815402005400c209440703850f1a4101070000c8642c010603442e080240c0308010070f000042c0028040c0c0300d0740c80242c1c0240542c1c2ca012a550400b0780e600500ea2030f0452075012681d10b4680024014a03840c54156a4014281907007401a81c0d40102c500050500c00c0080004a00b03c0350b00508640014108501c02c1d030204a072900c190b41c10509081420f00343c40045101e08168101044e13800c1500b01004040b801418100000c0000c102c085008003204402d0130802951000c040440c0c800903806039001003088600010018a41802540d03146600e034540494101301c90f00585180c05181500c0f240000c048100c1070181c4902445038200d00903c11901481251600c4d11501d02842a9000052105141e084100912a06420600c540d086560407640c0d80c1c60040002401043d005640c240001c07541c101041003c036000a001d4041e24001018000c414112642034000354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 480997751 1250 480996501 480996511
    0x918130212030f0f040602010506030d080a232706040c0b21180f011104030201110f0f06070f0c02010f051c020f072105180a031506050405070906050f03 67
    0x84420040c2d032440d00c03d520301402e0920012980755403a10305021000e405e45000800741c40c0242e000b56102c00c40a03501080598001c510394900095140310028540c00310b0000c2a80382c090500e5940a01c082c440c0000d03034031107400d901a610b07a600d442c054074005031540c43c00d0318040c0c01c1d90380260090140002e007400404010365842a12504c11101c84102010b0300012655250b0f034007690000c1c02034400c4c1c28003502440d000120020172485010108000043c051804060304100c40306040c981c3d400300800030200842014011109481c10f0311500c6583d9050032940240050314820903401c0190080599011490381610380d080080f44a07142218141c0144107401d10790309248002c0011001c0710710040030000c43c0608140da54490600b8010080c1c44a8210740031010511f03a0501c030b031070ba880340c162145c9c0c00702001d801200c00703641d900044a1903420340010340343c0030030506100d0959550323a200d40110b03002a40e061001d0b80d6491400c0d5520f560521528011440801c1485482040000196800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 480999001 1250 480997751 480997753
    0xf0c0b01030308180d081501030618020c120706060504111603120b1008040c151d04020d05070c06060e011424030403090603060509040f0204020d0906020c030918130212 74
    0x40d140c4c1c03440b4513000c404040600800c4040e014042e150031071150185005100782018444030745813511180d40b40f020300d000c1c1c420881e0b02103042040c04c0810701c01c0440742440c03000d055031113883d10300744007004041900c01c80340324614002096072007203d0b02c420b65540040480c0044400b0703d55490903201c6048035800e202d001307940d80501589942d118400744207000c07225550032005240624080c0f090210300d03002800e5008251146030503160784000c2c03500140104c1c0d0500040000d0100c040380282c081e10880410b200c2c100002c11203110f40c050074043700c0d14045d1000b0f100e02a9a00c41e801000d030750078090494019010801d03815141400000704842450044424120f400e801180030010f41042d80d00b140000c0c0c2e446003c00c07102d90b142c0140c1d806010100c03a001203505103542d40507280c00d0440e500038003490b000300d0120200d042ca030741300c4203035035800c0340c01075580d0761482441da9101c0d40644e0b5030a200315072002d013221100d5500700e103980c0318108c0000d142656483c507400308007880c00c540483c0405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 481000251 1250 480999001 480999031
    0x8010909030e09010801060e090303060d080c0708030406050901020d030501060914130608010902120601082a1e1219020d14150a0b0f090a11090a150f0c0b01030308 72
    0x100d8440120f101d00a0146074000510141407151101a042021302504a42e5100f8400e0184960381d00f9509c0001d00ea0220410350323104140c00300c041c1801000c1d40103182c07501000c50000784841c1c0100040610001c01d80c242c0d94090300200c02503048803000e000e16000074400d40014000704a08011035101000c000b00b9a00d4008000d010074410f94002d0b40081145035110507086085043c48044001c2c411103040c050f103030380e42c1441c0700b50f0740d1542c11402603003107443c806407100d811544a07114511541006440c8101d0000c460703100c50410794107208102e00a0b12000900121800b0101e904005a00c00b200341c0080d1a0480c1c08000340801c043d141a40d441d0540311006013000c4003006800000300c610480300d141480c103d88076108844003c850f0034042e0365500610449a9503003020540d00c140e00840011b54040042c0740350816000d180d00362a00003044100c089001b0000b0000303110358005954559140036440b8800721030720118881d0041800400740c00503c00603002d546520741c49070001d5000700b8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 481001501 1250 481000251 481000277
    0x80a021605010f0605040b101b02060408011407090807081e0f061e1b090127060302030103150e0307030f1418030c1909050903070c081506010309030801090903 70
    0x300f1504070b0b80722001e586035614410001814640500350810104035103650390b1071001000a400d01b10030905c601c0d01640c14420290441d5280c02c1a500907080d02002040100b040c40781c1d00454003c10f40b0000045204030030f0014080b00001407003002d440d01701d405440d80000840317401260720b82a02452030503021b0b030302d1b44e000b40000800c40a071054a580c0c01540c02144045580140d1a1025202c00c0a45210a14142c0000c0506040340c03e098400e1801349042494100e001d44240d1a11083e610421100d510000d60340b98150051410f0b00d0041200701c9105c111211710508680c2800304064282d007050010b040800d0203850303c1c0c0c09242c501c2c00c2003040b00002d401400e42c10b910000700c1d240084440300c0c602d01d00e400c080048144400040c2c0361010342004c0004c0c00800d4240d14230910400a4031000000c0e070100041c010b44d070491364484035508016480b8811355480c0c0d040503891000b03108001340040da056100b0300a0700c00c07041e09078032180b11300c1e402c0030621005003c0c41c00c019024020701000080f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 481002751 1250 481001501 481001503
    0x1b01020a0c1205040608071107090c031a0306130f03090b0a0f030b030c0105032d04050d020d0c030c1202160e0106030b010305061f14040f0f05060a080a021605 70
    0xc20404180da540800d24400e070720349054265410301090003000420300c414840e00b500484c9031b5030000e6080c20943c080a105130f4446281c09940d0b00078803501030600303248040d41a0590894000300c1404940200d48112040606540d14400c5809101c1505005414400300c0c6a4116440300710b4002d00d060101242c940142c010950310480307000000a4008800341207659252003030b600b503048114080c00c405961000020000e01000d00701c980c036180804503d0302d50301001860900d1921a00d1070000540c43d03d800c2c02c40e01c2c1e25800d54140098001c84802c0380b41e10384108203071181598541c803441014406038554600e02110401c01600390b1040d609420050490100c002c1d00510000c101c405141d810000d0050542e100d803081203051600341414452aaa40c1043c3c40d20109000c44880c607400c003180c1805c46403038401e04030440d182e000000c0c0c08668440e0039041101965a100049000a0b1380d4405011b518491140b044001410200200340482506d400030701d06004243d80c0c40000c40d0b55607e9207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 481004001 1250 481002751 481002757
    0x30d090305070b0106050901120c0e0a0b040e0906041a0a06030f060e0d1803120e0603010803090a1205060a0509030d06080304050909070e130201030f06080312060402031303051b0102 80
    0x54000c01d40c0450034108000d00d0b00200c2c0d02410740e030b1502509101c40c400c006045011001022003541d03440307001c3c00d0a618442e01c44203038055402001044c846503110100700050780280528045002200c0024480c0100021028029a130007100f20384501e20a9078000f902070406002020701075102c0c800040400c605170079410005005007000201c54003400c102c11315103d03070702900200380b25140c2e180160800fa04922001240d07041044a030400c8100501158621918842a90b11131008800030400043c00009400d4109040d100364060303e454020028022692800091450f4024000200d517001e182d0402500a08014101c0342803480351203100042e035110380c1003920b19500100d0100107a2800d0228182c0004425003c0c00600b404c0c00e0004058074001441c3c64440c6003440d404c101107902c2540013101044000b1000c00c046906c5403001600c139400381030845088000394001c07400724030b420b100326401000c00c442c0341226100d0760343c3c090f070300d6412854454505072404050071103401c1d028001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 481005251 1250 481004001 481004003
    0xb0c0114010503160612110403030203040905010801020304170d0605060c03070c0b0f0307051c11041401030b1e040207060507020c01090b0f0a08090109060c030c111605060c030d09 79
    0x10800c280340009404800005a000c00c0c403a0303001292411507001c40c0c0c101c140a0341d01516000301c2080b55803819602409a10075424501400010004140340d230101c00390040e07500f0030109000d1a6a0355024600b80c2c001698058070a078a0103d0862070091000014103c2c0700c4912400b040d2036903240c2c0004d100390401d0b50b1804c00f507007001400c0010845410100009440c05c03121440c100030300d80203000d0741e9000082c500000e110000a0a0748050100000c00115400d03200c004d024071102090340240350b41040c0b02c0c000d6440c044410200144d80207025500d003001d80500041c00d11000b1000703820343c0918000c0000d4100e80c1c200082c0e80410300d83e0103158440c07845a001400b0f03000d44c403800103021314040d0b402000b100d1818084c2d03201c5284e0300022118102e4403483e00800613100c846c4111b00500c0e04807070013070810703251100c2039489541541000d40300786503039200d0243e9041b09108943c3c98081d000c203110054182c1ca2001d00071441c0c4107025100120400301100d0409025240050481d099040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 481006501 1250 481005251 481005253
    0x2031603150b030703120f020a1719021f0c0c0206070f020a0519141c1103010609021201180603020d060605030c0d1e0302011b09090605040501030804090908040b0c 72
    0x40c0341d1901c03501407280c03100c0069008181017451500e404c00022031184c03a400400c00881c100d81d034a43e1007008030140140d00066525000b0b507080c0504445030348040020b0202c1148041c0d4280b449001040540da0031442d04507804402444150403001880380e01c0c5184288442c172059000035841d148090200c2910440ca4a506c03a00c2e1030040040000f402c0d1b0003244110800500c4850364682c025801040700d45008600100307481500006044003403d031245030015040760700503001d00c203844008a03100c54080d03000f0070400b500e03041a88181e21681c2d0030b21581200c03900040111980507204900c62401701000082c1142d140d03800540700700d240c058142d4410b5261807040c0010300d800d0180490820003244e010f01007000d141e40e9802e00011144400d0543c4e081e0f00340c0718080c58000c1d0802000c20741071ba078250f6426584002c2c0038107400342e41d0044050032442c049000c45c10341042e2058034107032a04040900e080510300b41c074920260004032022662004188400030b46020078401810740051244 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 481007751 1250 481006501 481006523
    0xe150f040803180a050604030f05030403080d140f090312060303070611030915060954030406020309090a0f0c03050618061012060f03030e130203010506031302031603 73
    0x201c0344007403a0002c0fa441c49840c0c4900d04008642e101412541100c0d0301000707081e0a42a40c1c14100c1c214003079940090400030002500e60460301a6034030454002c10600e20b005a1354a0315110074000e242d00300e9801429074410400c04140b9410808095401701008048a01c2e18030756903941e07025280c640042044884000c000c1c0081d09200f440b42400b09582103454006903e0188000350841c000070702001c011050260507010300c00181d000b03940c4802e42c0001c401d030752031407141d03510103e0a045896034101035030425500b450b521004070403101111a0b83d8002c60904900100b080481580500741302d400f9a034601030070149190a008180b240c0203640c40c0011146080b04c14007c0309442c0300d016940c0000c42c41c0c01c202540c3e039009a6501d5600c05032514266070707090207050ba0000c010503007026200c1c4400322070010030540c0c0017130107604407030b41902e1095201e0301b001d0702c070026408203004203540074000780001204130808490411100d40014125250070818813041e030111600d50304261408008a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 481009001 1250 481007751 481007767
    0xe0d032003070903110f090f0105041109090610051201080c040b1807050a1809020304060c09150807120507020f120a080c210106020307031b02010e150f040803 70
    0x140c5103500018581060320301d50301d8240300c0140881440c2c000140001660020700e841784c0c8680140e0080c100002e0541c0703544d4200f0010328910a04248542e0344242d0510700c0c181010221082910820713030b000380c0809050b4440c1c9041104c6000c80604020410409100421590408038800c40c001c1101d20043c00902d2407040c18401903803407030031000e0b00641e55942e100c2107030107217440c0103070b4480c9103490929240c08000004503103100390541000b50040074180c1c0400e1101b100e900440c0a03030302c41c20041000001141041c1c03080f4185200303002c19005c40f0030580c0000390141340341c558080d0341480d00b40105800c80007240100c410585004006920001e910060a1401c01c15140d01c400ba085500d41404102c1c82e0003803106100415400c2d12280118044c1c0c14101071a0181c14001d8042014003100d61316014001d6503504030038019070010b1011400c101b520004d1100c0760400c0e41c2c0680d50f025940100c041840f41d030706020195001d40c00c40030800d180312004643c000e000035200c2100603640c0d0f4150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 481010251 1250 481009001 481009031
    0x30c0711060a020319020f0102130504050f0103020d0312090c23060301081f060b19120212220c140909030a0203031602030c03120a050a0b1c0203010e0d03 68
    0x10490580e0301a0404000c0010843c0c0c000081d9581300038000c25081110701074001c12803e15050f408005002d600108030344d204504020701c2d107025500280c2d0300f0003141d503c0003604039180300c3c02c0c840070790000a1030071000d0209110766154080b8194038000480d00c590b9030382d15034606100a5022041042040380700180c1a5003145040c0c8507240708444c05829541131400041e1249011204000700ca0701d40c08404000c1151a0041c00003440c5c00740442e9140c541c0406100141102805a02c000920340c00600013082003500c241c807a0b024046c1e11803006992503840b010700e044400a000c68412003030744207460000341c142c9034220140641030350a1441000c01c90522002e0134001e810036113660414003a00e010507600200703499104422080c1000346004c041800d80c01c6205065421a45010006030058410410007500b80030b010001c008110541e02e0307251180c2192080307a0f1299110400c2d20030100d245604680000145000070000150902041c105500d001c1d41d0180034400b10b9141d41c552050400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 481011501 1250 481010251 481010273
    0x70506040e0115021c230d0c091502060712140123010809060c031003080d02090a06080402010914130e010c110a05061303031113230a150c08030c07 65
    0x42940000e1007202c090a560f07800e919106419102000722006060300e4103140c5a58000c000003d218226642e111545040d001400c80805600c001c25142d600c0052941c00c44ac4040340d09031165405000951642c01040b50070300c6028856061058841c6149030b00e1100103c4054001d11415065080c80d907200303e40c201080f0301000215061015030002c00c07181e088042141071340604141c49140d9a91303a0b04550615001c0280c002800b041004034414076405c000390700524000d03204489030009a0355651040742e0190045400070b0002d100380707100f003014518a1404685169004004100c03224070320641e0380885400d40354000141e0b45070001c40c21100e03086039186051903200c0020b0403c040441c1c03600d44d80c0b084003510070041034030400c050ba01417500c268800c05020b40c0420741a03980f450400c00201e41d1202d04c0c041c180710f05900c0d1010456440040080d160351001c05802030260518101d0100c1c2d00300d01d140b00c40c00a01c010140340030002a40100118412001200c3c03d42d154045030038183c192030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 481012751 1250 481011501 481011539
    0x207080706050c0a020607020607200310020a05191e170c130324060e07091e0b070516061107080d120b031e030414030102030c09060c070506040e01 65
    0x840c0030070001d07020f59000f003080700d0a507805444080e599901440820803512941030b0207049401e440a11000200f9640e42441405004a0444190310802c05030344c0d08030300c500c44103c004a4020051030800d27075001000c600034030101d070900001c0c403990f0413401c1d40720784101c1b820030703000404e46040c43e1014007214a000d03421030b040c03500c41030410200e110182d440c0100c500000e059200d451104481e20350300340c4081043c17000795520500c0b106546102e01000c03031406032030050119071030f4100812848a032041c04a0740d041010306040b003052419540340090b40c00180240da0030b01a0040b0210340c0d0106000e50f100500c0141d660310749610b500540e560608100d41c12200c0250840c0013000382040d44920b41d10441e03800041c00107124401c49000920b4544100d502e4451805640b1042d545c10030040090320031a01140400c94401c4800d1040608034801181c01003183c20381400b0b800c910303040082c0900720751502d190440f214552500001400e640143e40002400c1707445c4401032102d8035190b618000b045d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 481014001 1250 481012751 481012757
    0x9041104050a05060d06080703150e0c031207020d0c0b09100c03020703020609060702130e100b0916110f01061805040f241b030b0909030a1b02100207080706 69
    0xd061070005826402c152161034400d60020440941420b1940d1210004180b81e070704a82c002640c9240c000d1140d188034206c030100900d450005101810f01140d07000142200402034410301441110380c0740ca0b6000000240c5c1c0080d0300d8814540061080c06021003d4000350010680381c01b0b007541040704c3c0314103040c0310034108800d50b11040300007a000a48041075950444005441d10f8158010070f000c0e001e102d101a603c50000c500107860504180d00029102c0e90320410348409030450b850070416507480145c0190849924800180c01c020310240318151000c051404503281e03480491480d00c1c00100c5031610119035034686003000b50360301005014600c0081402c1c00c0c0136602d841d4a400b4039550390050068141a450b80044c1840d00780c050030310a000c000d001c2c08022040d00b038400650052140b158283c00b01c0d03d8141b041c100c2e45441c04806200d480c0020081d454051107480c111000751500100c2c0158500d01820302005a03038005510140b0941c680c01000190324124456181031010b5101c407089c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 481015251 1250 481014001 481014007
    0x9040f060e16080f191505090606040609030809010306030b070509102c010302160b090c0a0803031f05090a14073f1b120b06030105040b1f05090411 65
    0x200d07007040f4440e500c65400e2100e80e0309070b078400e8540441d401e024940740600d186030138251014445007581d190150350040e1244c054940e60302081c00158443c6014004c08903d0304541003000510940041c00694018500441c525640740c0d9083c482050a0700e1440200d4400310703000d00d95041c000aa00710076246032a20224400c0ba05051021902e03d4114407044841d507210101d000d64000d8044400300c00d440c803400424a034450421900146042d22001606d0062840102082c9400e8080700140c6001d580918956203404001e840c00c9c841007469107402069014001510703569680e4541e00c51542d05402240202c864014503a040000508640070f0103001214200d000020a800020f00c03c2090b403885101284107501c0850581004501c0804600b01030565001244018a18802080c240c945400c1301002c03010020988801880c0326401002c18401007140d443c1c982c0001d01104005010220300414007101b06c886c3c560303080b00510110300b0000e00514035041074419548030f47c2c0300d6060241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 481016501 1250 481015251 481015291
    0x8090d05031c06060f0806040e07090c020f0c01081f0306020f0a0813150213080a050a14060609040b0402010e1305060a08030301050d0b0c04080715030f230c09040f060e 74
    0x1c0d0175480b200c801001078100018002da140c96000301241c0720080215150b5640e20b200800141c490401c4070b00050064250128102070000b44060948038140c40d400c2c81039030340301004100d81b95070300e02c00c00083d08151000008100584000d1221020b00c0500658074481420081c041c100050410401c0c021900e01d042c0c0815401820002088408000560383e0282e803003030b0035443c8c045500001b40ca406041d101908108000580b84451881010310810307900807180c0346621080c048500540051094001800180c615055150f00500c14140725076460500804100b0384030a581d40000750700e42d10800d00c04076140c082003000007050300c18021440c1d50705080106845000c52000100085460740108952200c5403041d00c01402c42c0d8002c859074039070b4402c2e4100b540307030707030340e0a8200424503100081000003028041c0015100030b0ba0001d414038074525074560300c4070b1401070822017001400c0c01681d00e142e81390700a1385001020804003103200ca04084404408000141200d29003056884080c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 481017751 1250 481016501 481016507
    0x2e0305060d0c050f060c010e03030a0e0f06061512070c0c05030c03100e0c031204030615050102031813020d0204090b01020a032c041b02070618050d08090d05031c0606 73
    0x40640320f0640c0c29030440000302010901900804003814060750070209000c80c0f20740c000018500c00c09100c14180842c1c1802030001d620b0307001210360f03824035410000c0007400505100e00c0c000c4501c288004110700d400f50742e082c440c899106c01d9034102c00080b04e503480b210034840c0700300041c0d010342401c8026003240140440000c3d601c044903034080b800c0c07607162001510084401d201240c01a21301030140c805080803004d18081c540d0203400f045480501d4420503018038400c124828055070410780040d86800b0300d8010701d41210800358034050780302c19504106000507031240003900d0701081861015807141e05040c4401c0a451070a56001e0441d484034410002007980300b50540b2211600c0d101c00090080c8c41c0405071100d10601c030380b0070703002418501c2c1600e60681d81aa0120403010075400e1310301c11500c0b81e500311000c09981c01400280f20482e8401e01561803c00b03154030340030703110b82146460490140b012a21000f2889400e40300c0d5000032a003c450b46035411820354812040140800020381000805 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 481019001 1250 481017751 481017773
    0x22060305010b0a14091c2001050a12110a030b0102060a2c150403050a0e0102070308030a020c0a02030d0816170f04020423010501180b0f07022e0305060d 67
    0xf0b00400c01c0c0c2a1507410511103820446850000142400c43c9101010440744814844c6010489420803007241c411007101809a0400b0100340c1692000d1a007000d82e042210440a03a00310000300c0c80e03440440b01c90009002009040081080d20081010340d603c10019090000003042468124108000201c003081e42001e50030110341c2c80c218442c02404200d2a1034509000946960300300064002440180354014015140d27010f082e85d0380e200050726a1004903201c15040c80000c000c1907040c0046003583c48140c010300f442c040d1440441d1800405500000c2c80d000180300300001082c2000203004c1880d05208410140c07078000c0c00c2406a07840912656511138000404540510710103001080c11551a9040f8513030315280d01d500c01525a4031a107103489014000c1c481c05020030010070311003065910301240d5104a82d00c2100f00c03428509145805203ea0f40b00740822039021991004161812406040030f00380c50700310310b404140d0502580c1d40a002c580300988118840c95807207070700e000010842289 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 481020251 1250 481019001 481019017
    0x18041103070b1204060903050c060411210a2913230d080c0702042405220903020f1609060f140d0809132702100f09090222060305010b 59
    0x40050006c1c22410102c5190250100100d032a004801c1030000388000f24032045034034041290f0000100031550a44500030b480a05617910b25082030311075502107050b1074a00c180d03440c24005400811440000c0f011000141124840581611600300c4020302a00d204105500c09601c1c5c508811480c2885405544445160f0701c2d1040100c604001a170007440d00f41a140c1c5140d02030024448100c0715001400252214001003222910707030400007991746442c45171095041c640020300100714441002d0305001d0450800140c042d031240c00741c0402c0c221010055003e201040313440c4074131118100504c2070195000341d84125401d201e4043c09210308900c5103a9030440010465580c0000c0b03006203003404050041105070fa40c0481203440e20701081c0c07003542001c86c00b2a48074100c030340072644940d20041e9401140b44007070f4100d8400402c903100a40074220790f500301c1d040c2e401c3c1400c41c10b035208013000980c0d1084058480c9074088202e003803000c44200c8598006850075003010b00c0a0341c1043c12644c028024444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 481021501 1250 481020251 481020263
    0x7170c0304030e1c0b0c0901143702011107020a06110709020f0a030b091620240a060b0306010c02060913050711030403030e0f18041103070b1204 64
    0xc04681018000c0d900107490620180c078007074540c506211190100120f002054680303030b100700000340300926448200c2e40013034016160141c0703440b8543c1d145142900f10984c2401c45c4d50401c2c40c584880842042040c82c40e01081c00b00401d16030480c01c0c001c1c03c1d2030b4140f0388924001d009200c4440107943d03208140082c1c49103880c0940f541a51502564605072440c2d1164400501c0001d180300005409801040d140c00c8540b0240940c00c404428004415400c030313000b18064020070740110301c50703210340c6046200c6044d000c408024205501106420458201071103030034401e4207a40000c0660b054400151f12106a201c1005010b2400394103042c00c1c03000924881c1041840c0c0b0000c4111341d40c44080d2000740402038195000c04801c1e2000324024581610107101040031400c1c541c4000d00f0000440d01985d80c99512031040d100c00c0c40512820510b0a562039510445098490380030301d420001c3d0500c40c034080d000d8080d400d0a15018542080102c0c0c0008141001c200481d41020b19012441c0380c0081c1d0201c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 481022751 1250 481021501 481021507
    0x10207110f01021e0f010c0c1109040c0f091406090907030204270b0603071a0a050306120102070b04150902010c0215041a03061005160209150d08030f07170c 69
    0x70340101e040503880442840e800c40000302000c808000003e000b048001c00e840200601c210803007094588131200c41d4010448007586442e030806003458520b25412611600f2031080c03158840c0300015100400fa00855285503880d201c0c10303515154021504e4000710700352260102030410160315500c80400d0b0001a000da51144120714a4045403103040c80a01e092038013500c900c5002d85080713150708600760b519a20910800001090300c425040c050100015078100c60351a0000900f41540c10340c20007400325a000035003c0702c550603440280000d18200307104802484141c0b80c00d1408a4103481801c9266480b1407030242588011f0360403801d59003600e6011a611940e81c1680c00c440c4c0900e10660f040f4900448840e081703140302d5540c5c1c402031400352200f25221140d40c1141d54086581c0e0103078050001d420071191407204003604205d100c40c2d81090061202590000c42ca50100302e40341e141e201c0850701510000b04100c40300ca407e058480d0008111301c0d112036048002c800402d0240ca02400f07540c3d41400c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 481024001 1250 481022751 481022779
    0x2040e03040b0703030f0e120421020a061707090f170a1208040b0106020102070c0509041103010501180509011b0f0201020d1b3905010e010203010f0f0801020711 71
    0x410581e03000b007289848041c1c0d908a9450700038040c02082035041001c0e8180681c01d284008041030442ca43c00d145000d2030b09040c130b030251241103441d84103040601f986414181d100981c55000290001e85100d4403030140043c0307581c101d01d1015100408080800106000500c081c20308240d500341140c0407004a01407213600e1000d804d05107014898000c2444c0003860b000511240c000e50b000e8419400303103c40c940e007a80d031040c0c160700307034401d030700004290200e2140d05009030326002c402d5980081c00340004184034030703054000c0fa00316503003078010440c404000c0403d05002c40c03ca015096001c90382c0c40c024010943c005608031070780310a00040c1d500b4803031140088070340c26200354140c0300481040c4105018044035004651640380300140c41d800000d00c030203400407140700941480e4210b000d0600a141e010780d015104140314023a4081d040710300d55221940b076602c61030240051800ba064070700c2000640d40c80c0038245045481d4660040c100c990040c131000000c20381120b049584200c05907036070f00c130034000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 481025251 1250 481024001 481024003
    0x8061305031806091306053a11091515070b0411010c06050408031602030c06390307030c020708060a11120f07080a09020f4b0a05090402040e 62
    0xc4201041d0050120756036800c210f8465081b031703404c81b1007c3e10301e2224103500c800a0603403842555401010065446001d4880c030108d6221001c00307d00918034040604802000100c03941c07000d0710281c0d15010810841403c624044203540c1018010040152030041c0b1681ca94840c004010310250a03800d054107c03818a13409007000c5c0709c2c83c50b031043c0100034078035080c40c0c15201e0f0703001603852050b55651043c107108894000812252007801d0400105034541d5070340d100b9400e104140f4440320103044050144c00900b64030b00d09100140c0e0011103141d80740c0c5000600182218944010281194491002080000e0011903c1e0b6008030f440f06000c0781121201e900402d140c45029190000c1c00c21150800480d040e900c003582d405030031641c2d079241c5280c55102c150030030f445d40d212019520281032800c0410505e0001047d622810051414403030000642080004481c4100320f050156034034020301c8002d60401081608004e41c040b6109042203007000041107039044014002400341d1b41d0343c06400780500d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 481026501 1250 481025251 481025257
    0xe0a18020a050c07090603030e0a0e0f18010606020705030f0d08010938010818100504050a0b0702070602010f0216060f0f15080c041b18030b010f08061305031806 71
    0x2410011503d21580d0f400b4004001e06c900e1200340c000490f04083c2010525000c1c0e1604200c3c0d115014400c5191101d05440c50040406000d1102041c40045204100d42d420b02600c001040d4a0300540b4580e40b1300428541030822026864849421400f12000d40c10340203403550b81541c200001c00184540500f0036240854a00035031100b07c143d90001b0316105030180101d04501311003ea80782c58064442c80030fa0003040c1161524001c041d000000c4202165089622250b401401217045942ca041c140e01d601001100036998000142c000b100144072442c0c090041c40003040309035004510b001088411103440341c11070a03006207840d40300e02c80358209105a80024000741c02d1090200701407880c100c2c041000340410f10800070345025516038004a482d1511412041d01a0404408101016100100c48000c0240c000450a08141e64048003181c0d6240355980a4000c0005451140e401e00412500d4410000d0030511043d20200c1e290000800120a03a800e00b540021011104003c0d2000290340d80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 481027751 1250 481026501 481026517
    0xa080c1014120a0f0f09031b081b07050312131203050c0d020d0306050301050919020d0c0909021f09030b070504091a090601050403030e130209060d05070e0a18020a05 73
    0x111021080c00400e0145a000e130310b0301c8040f031004210841003804140c1c15036100d110003070082201d5406440080f03102803d0200c6040c400e0704040d2501072602030030301c940700604581c21a03541c071003582404141001c00180b20030003521074182c2e00b0400305c901d24202c00c2e00d06004001c0c40c003079041400800c06002e01c066541e003143c6482030f144c0d02ca1a980d0002e43d02caa043c120307440064104000010641018416140122107542c05800d41e5010700310741703928410748508126040b010141540001c10b0244c0c000c00c011b080c84400105028205004001d03038003000e01030900070481c1c2e0b41050718010350403100c0070088950046100d00140c0d11150152043d010380c0e441403180500b000341c2d0318a500f410071040418038104595945164407441c004541a0141e400001c0101d00c03030390141d015900d007200240c801040b0b801d4000d880c000c091804907031160071481540000c280c5440034440c82682003501d0703400d9050140c031100b85491030000252507c50844c007004101d16800a9a211500c3c4540111a101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 481029001 1250 481027751 481027777
    0x11713060b040b0d110a0504092609030d170f0f0708150a0b0c010c05040e15040216060f0b010201020906300c04060e01030b0f010e03011d0a020a080c1014 68
    0x2260417820507280540507210a2440343d04c581c103021440303140c50f02c152141070b9000806400d8900c0c50f02c10098800380740c0315503425809009e004001d22545c042100e0034002113180d44503c590b603a481c04e003e40914029100007070704e000e0b071010045d81c035038901c072600d9000d211381c41c02c04035a40b212079404107801440d11519800007020100402c80e104643e0062050702c2e0030000030882c10b0350400c0300711017a00841c01202c1c841c02d00b4101040e510303000901f1903280004000c20051a01030914907207415151070f00383c1191103c0c0c07a04940c11300c6d94036512a2602096082c0001d5290400d03000002d0341d1407041c1c1842240100f4010584c2c19981c0410070006000c00034048000c0203400e00c01c0c881c0100ba00130303210742400191071844024640d4400d0080084101002c0c00c620707014844200150340da40c9001400da505507603226454001145689042c2444014510142c40341c0d424500510007602810303006000640c0c080e012070351035501c1d070f011400c0c440d004030303e00720038940707009050300c00c081c400c81c0b20318640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 481030251 1250 481029001 481029019
    0x605190c020a02150406090e04031e0306031e081e04090204030b060a061106060411130303030f0b010302041d2e210203120a1206090b011713060b040b 66
    0x100d55000500e051155000b1101e003105100011480703403461240c0c0c0200c0c00040c840741010031030304004625070b9030810700c01e04090107840310b00b0700001e16044128800340e00098903403038100248540601325044c02030701200d00302034002407501c501000e4800c0e1044941116a001e0300c40155440c45401d45000c0c0c124030300c06654955072802c2c4510190010b0b109644200341c080400644107004400c04020350200d0005090b2540e640350421005140044c9030b6000c1c40010082c0ca8000100c020f00c0501443c0310741c40010b01003a004040700109c0362012201c0c0d06261040000388440c9480c121000b03ca1105c000c8200d406130307521030088549507200700184064201440d203410f641c42d80a10104291019001c04000e4044900c80c40581d030703145010003a4154008001d802280b46100004004821603800e01c042801d100c440364004407005075200500c1d80b582c074141b0700d50070341c1d201d03408080f1060300c0201210107040400c441c60701008400001808155142404110b0340c640790003110441c00d0050003a08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 481031501 1250 481030251 481030271
    0x907090512010902011701140d0204270615080a1b0e070306080c0d080703080a0e0a08130b0f04060f090e011205010f18030305040c081e010506060f07060519 69
    0x1c041c00c03d0440c100e021070900c00c80c500108110448080c1210503982800c0c90310800d19046c8080c08080d803c003641c00607240d5200241ca054001502c036840c080c2d1b00c2c04680040070074182002100d1106400262129601d4010003892500042103906030360008008114141c0420030070500c9040c5030b014000b0300d101442004060303034040d071044007100c03000c1080c0c034001680030781000100e80401070300901c044070500404010a100d520282d030300c9001442c000480c20103c4801c00e00e4000d502104840450300041d180b00203244031940c2d00c2c0142038644202e42004504440400940101d000343c1c0100300e842e0002c61441881040c50300d0003031188840040d0346e561a16104401781e14040d1068590b503007405506e441c08000d41c400d00c05000c21111210b40140600c0d03804030058080034100b910808c10520003c81c40620610100342c11804011801c1344080c244170845007135444c024195403207100d041c01044201e14031070085510319035021200040e166070b803500c2c41540108040e001d500141c40c2a40c400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 481032751 1250 481031501 481031503
    0xd060906060c03110607050304200301020301080a1104060518040302010609060b1914030c0d06031205030708100b0d020306130f0b0310091110050708030f061314060907090512 77
    0x1c40294001e41d00c044c4d00030b040041803a0b44210a8071100002042000003801081c07540c001c4c41815a80300300c00000990b489400203080e60000c1e00070780f0321078000c0b0b01d500d01040000c00d10745030f00c0001a207041c01300d02c2c5403d0010b91501140c0004224064890f40001c007010300c00e501a8020300302e049020010107455018100007034008040a03160ba013410b4840381c80c80f600480030b106004a40940311813441e035071135407080c28940054036100c45854a85c82c0100c0050152100303d07040030820b9640da600ca1900c48c02c014850301d0b001d0100750841e1048981030041e01e440070704441901c03802810150b40d80c4c03901004168501045c541c0303007a000d460510b0300001560250401480d480e022021100c604040303940920446e005214000c2003a00b00c881c0743c00302070400210000305000c1b1802d000f8100103160710ba176100c5500440d1261524818241005028a05600d00039410303489001c04108022903180200c1c0086405030140d84500402c400080140e849810100003408000d803201c41c602019541036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 481034001 1250 481032751 481032767
    0x50412092306090103020d02221706240d0c090e07060c0b130c1d220609020a05030703082a03040303030b0604090e0604051216080d06090606 62
    0x2410008040100000e080d1410a40c0001030308400000c1c00719880310340081200d1a80304140141c14190244400002409a88050070b6111045136886a440f061003c2d40032641e0303019040509080144020300202403c005000b950000001015a48000d018904044402105900e407580151038034004020000c4450940040345c050060903c0400e406039056a100c002602803040090451424030011402182e0400e401607520500440c90b44181e07100c00d403500d00541c01c050020300c1a440c80c42c1c804440b035206140c2c014030700041855608030a01043d410851034900281106858200100640d030320300c811140205801030480f0703821369030b030305e0300003801c0d08171a144890050a110301088144081390100707241d005e4440140d4585400d40e03500360001c0c04c103075428503003018003440040388541d100c0c0708401c0c0e0001c1800080696160a1908600c0c0c16280e1451008000742800a05000c02c24111540700c81540b15000541782d5030302e80708070401000e040e40401032031400e10400082c55034010400d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 481035251 1250 481034001 481034033
    0x210c0506070206070f030f11040b0a1404030b0415061716050a0302030d18030501090b04050d0905031f020702060d060e010f060f0305090a020d05161d0103030c0203100504 75
    0x3528201e9560381400d0703854078800c803500782c046110003600c845650f20a900c848001d82224070005030251056190701c0194029410544a4a0000134400b04094102d050002c034041d0860002d4980f41c19550303003240d454006000207000480340310b1078101c1100d568000002900140050181980391808415030300c69450b200b24001810861011445040411086080d690043c00134140010b501c942141c2c582c40203e0b51882c802910b040200c0021020b01030f01c1a201c2c002c01c0c0002c074a090600f04541014004d4410300141704160408100a80740480d540070350300a9500c484c4241028000c003030000e48144070009510000c001088608006164410002e17140e056005d120207030380714002200e40300c400f17019890128081c00384072290341e48240c02080d48041d480d003e0751007854080c2d01185c0c0f5040ca010080715542c004210b000000c0003808104002407002d038490383c545942036405c4001d4400180030140070442d80b0750244d01907440c00c100c680052081d041d001c200914040c01c0103d02c21080c081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 481036501 1250 481035251 481035253
    0x30311120a020414010c050c0907090e07020d4104030c091a090438090d08100621090c0b1c0b1c1b06080a0e0106030b010909210c05 58
    0x40c40c0403552040a400206d280c2c0b11004283d52010700040060000d002440708040064143c03001c20110350300080346004066070b070001c118001b07280e40c001d020b880041485902c81c3d45d2001d41050301d07041c10343c1c0701045002c00c03260050700842004028003841c800c0780c2000d01216800c8400103440181c2d82d101802002c0100c0c5040e400b500003104010306084c0607240a050700221100c1281ca000e1001c40300c4200b0000054220714105000030a0350384100125070a51407500300160720341005410038103d43c0d119655140500f411410304502421184a5820180300518000c0c03041d0015107903948011140e0f074010b5042c5511950f00c800c03090842e4843c20040c0845140f901c10568441c425000d10283d10714014981c0341c0e04c004031602c0f06d4110480762820350316000101c05043c030300345030840000c0141c038a0b6540d2079064948031508009a52040881c1082c5a2511700104041001c825040d41503130028580031900310328070b05107a501c840c044480c3c01e085190654107840e032150800c80482d0300500c204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 481037751 1250 481036501 481036529
    0xd15080a050c1017040b07210b121c121808180603060d03081302040203010609060215010f05060a0504150c02010806100206010b0703050d060f0303110102090a03030311120a0204 78
    0x14074202d90616011044d80c090110341e0f800726000941d0f0f50605a445506071400300020038030035135402d1821114910700c80c1410340d500a080f409052a08030382d0b0f51445c800000b4038480c08100400090060140450001c00c800100207440c188481d07002034842106140048101d04e119003030420240e441000a8440c40c0c01d41044400e01c0c0c108482600d2003000d004000007683e40b1940c800703840750360700101890341443c80c680d05607006030350f02d1000d035002c1e14060762003001403070038490082c0c80d00c8141844452140d0180c4010800c082c01b9502010a80d00700741c038500c1e00d840402e1030944003401765800c040003080c0d00e0070081c4506940302040c40d015a0007682d0b039002d80e850300750510003550107410038840107030001d03401844480484802000e0191007231070041c2c81c1c10044d0380484101c5100c2d8101c0044003600980801c20b2640c441c42c680030300c2007000000c5161100d031400140810324617120080074180c661350000f1020b0000015290003400840c2d107114503141101038072009601a01504d10f46039611 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 481039001 1250 481037751 481037779
    0x6021c0603080a08040503090910140303090607110112020c011b05090109140a0504060e0417031e04020d06020c06010807080c06030c090a1715060907050d15080a050c 73
    0x54020340e0300300ca4010807082e1404074102c00032681c8076401041901d40e40b10400c07c1c0344140d2608036219100710049440701d400381e03040007509149101d00100c103911a40c030502c01e0003699552203044600050303000d103d2052402d02000142c442401c030501c81d28403d03201040f100000181074001d030000700b4803c0401c40131040741a2054940d40500b1102c180050391108050040c1c10881190500c0031100070058001295640005800d482d000c1c3c000b810481001418042000031082c00b0b0003003002c0c0300c040e00b0700f5840d00c45184c000b4400d42d1440e00b0401c8a21002007400e64030341c52165483c081d00020300355600d2012240481c1d41c0d000a00c1082c404e481039030800240c1a8011541000b0580e006140d28610746403240210565040060450703071000c0080700000c0c800c110061410240a240d10151840c0602c030452021400c03c000c0c0980d0145906001b0462030316072110850368118858840029003045501c036020b010350303c6400048040c8600300703805090043c0060b41810582d000c0790344482d607101c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 481040251 1250 481039001 481039057
    0x30f010207171911011b0302090a0b1e090d06090f020907020706020c0918070806040605010e010b030403110f120909010b09060403030c050c03060f04120c0b0c180d0602 74
    0x280360103400c0f40800c010341c0c2c00c805500c524101100000004004203002410051482031020b51100b24070203e0341c0020b1840c032608000d41c0d0300c401815240c414508106000241005280d403180000c0d056890024084400b0303076400c440d01d0000c030b821400411400750240750401001e103c100059124004001c001804248009000d03001d84241ea8040c0c00e1907180b0006200e488240581080103040c07000d85901c4024100f0020000280a030b40d0042444e0f05103070038010116603041c0c02100c1003140780310040c000910004e00b240d4200c1e505140c6400001c1c41041c3c41801c00c6000180c000f144c1c010300d1520450010400040e218034441120000c4560760b0f5009010040d210f00001140c20a00a00040000c03d010701881c2100c240030300140d032003440803100001d0400c00d0440f24490182e1009050000307102042005412404d81424a040b410314151030303a2940030300042401070480c8000802074030713001409082d00d416810242000b85450b4072490524040e400568207095400f245111800001e00703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 481041501 1250 481040251 481040257
    0xf0a080d02040f03141c1b0201020a0b040b16020f030301210c09020406030e03180d03021501080d0e0f012a0c030b09011b0503070f052217070b0d0c0e030f01020717 72
    0x5000d40f90303000402090007800c403881f0b0030400141e0540c065100d03564040381d5680b5809102c2c900c64105c01c3c1041c503059007109445e8804105400465100031101560110300004581c1900c031851841d185a130510704250034403020051000342503c0b00c4010006981034683c01410945004c1e40b82401550341c030808540e56401401c1ea10440c0c24030b9211003c2007810600513900200e40203105507011075528032080300c062482a0b01c8012160712100401e1f50041e48590300c40d80c014801c403400e59251800500003082c0c0ca00130211080c21060903000b0358407503a0303840800082540e00191a121030740e503e0801c0400040c0446103594103500b08602101000d103442a01c03039010f01a0f407552420358907500b1080703861a5801c200340050090400c0703100340f42c02c4144010949420300700d040c1c451250411844c41340c1031001d4032400989600c114814031101d0307103400640c5c18075400c248000840307402e80c01c0125840c8000e0242d041d0503019840462046d01d01c190018a206070245c11281c0c8c4802200e001400988 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 481042751 1250 481041501 481041553
    0xa110105012102091302190501120504051f0e0d020604110603160f0e1203030618090c1c06181a010302060304110102070e070906030e0f0a080d02040f0314 68
    0x202c1e21000c0c51006160484c07080e40c00440c04c451704440d00c03400f40d001c00c501c0143c4061501098a026408000c4d039a406034280c0d81010b0300c03404c144058101036a80720b0342c9940703c1400b0b0f10420f540030804001160254041e402485a0034200d0b0300114000c040a5240c001c16034099031154040ca18543c15414440300302c1c0c0c0103070184980c1380928480e000003180c000c1c140c00c52050030004002e104440503660405965800f42c03002c0c014641da81003460401920311400000b901000300d4180030890031210116070ba1610b80c4080e100074200b240c4040c5480900400300e03000500319858545e11403050121580081c0d14648200e400040703000a140c420302c01c00b8800d1100039808003040000500203640c3c08070142050300c0c18012600c0c230645032034000301c00d00c0c0d0440300700c4009200135104010b80341e4140103607000c941c0d0241c00b81041c1d116048085840341086030003d0214040019040105101a81240c000b08407801828101c10344070710344034036951041000115544a42c000d00d100064290100540007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 481044001 1250 481042751 481042799
    0xc210b011407080412081603030608010c030b0306150607120c03090f1505210103031d010c0f020121150302040507170402120106091d070605070f0818060a11010501 72
    0x11500d17107034aa141101c01448122100303c01403280e03030f142c045130b8100812200e00c40d89011500600b8095403d003181c20310030300b02c4201030908481c401e181d02e0115485402c0001d190f00350080555000105403644181c00300104808058580b82064951001d4011400ca20030b540300909181e40c1d049000c002d07549401a19076481e01200110345160040c1d0084c0b0012041c0340f0011407070030f900160313544404000d80c0141e020907488001d510200240142c001ca08040c242001749000b2196242c01c400108a010000e0500140e0030004c240c0000c0c4610510013600340110910515481c00e400780c07060f80480c48102d000d2414400841e002d58016104010035955942030010180d075141c00b00002d00c0c03d118456502c80d5030340c04c0080b414183c0c900608065200140c003d504840e000341e51945000c6903544200c003001410310480e8000340580500e50007154012113010348851030300f0749080c0400c4920200581c054030000b811108140c01c502804850f42411000300900ea98840c040c2e070030707410744000d20b00c0e10f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 481045251 1250 481044001 481044007
    0x206010e0c09010905100e0406170303010b0d0204051002151b09040902011e05120f0603030d050405010b1f08060604050a0513021209060a0b0f06030106030c210b01140708 75
    0x1a8a24980140107102c00525140c05103540e180e010601d6040324495140000728405074506a5040c980248802082c4c03c0381d62542c000c0850b1091074a030301043c080c51205450025030301c03211981640668000d40002007980505400c0300710040d40d5804180c891011608109001807190901041881d218035034401202d0315001c019000c02c00182441041203050140c020300809428041700c4512036144e40c15185c50f41c1d40c01c040c011250410b20300030806100084070404210f9541c4010041d41d510069801c00031401d91103500d0b0442c058400c410f016500709645102c17003040d414100c1842e1003c4105038a50404c1600c50b401400b94621490141e1500b1900401c4208520f042503130554141e441b18581c01820300c0c2c1d00801c000071050042c0c0f55000300c0d9101c00140b00f040d140f0380c0b0039a03940640031220901c1400314507005c600301e40414450001455600c1245440941c0135456444de001c0b00c40310070516031002807662030000c0c1350705c90055000a607441010703640410041c08503011590403180c0f09003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 481046501 1250 481045251 481045261
    0x9052508040c08061602010e0606010905091005060307031b0e06040b070c170a05070b0301050904060c120e1e071a0a140f030a0f0b090f130f110f010206010e 69
    0x2034005010300201ea00c00440c07000094082410f0003118010020410070080701000c4140080c01d54620f10000c0b40103030040d07414000981e8100c5050f07800c0780c17410307512004150f1703a1501a090f0945154440da8015500004018000e54140d014505041800707032400c5107074458540c00c40b41140100c0a13203820a00401050255500160103000c5451080b10904e0344035440c1c00505114192200c0c80d21010340c0000e2000003000001d201420141c090100e0b4030303040d98540000030b80f4543c40508050250b03940d41403060071032031081d00210100e8544120511800082c0084580d0b102a09a08880c101c2980510b019030780f2804036825080700c4d01c6c1c4900e9a0107503058484c155840d4000d44030300c002c0c04200400c2c2502c3d800c2c02806810389805000c061601c0785030440c41041030b6030040c0d80f4400d2507494100071610079079031408400d400040300003c0904030f40d40c0c000c0d00760283c000b44102500e0701048d100716108010b140f40c0b000c03804180035191503504894102c01607036158004e0241162102a25002030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 481047751 1250 481046501 481046507
    0x30417011422050109050709050c0307020304090c0c120e0f0414180106030b0106020a0308060a08100509031303050604020a0e07320403030503150a050a0306050a0b100801090525 78
    0xc2c10310028000c6040140c8081c0e54032400c542c41c034001203590b0740000d03404100e0b202d8944109940094034519007491442c0c1140e0081d183e03c11030007a500840d42c1daa03031a50106110f0303515a080940d0040d1224640880080e02501504003646c100d481140e0f1842c1900c59403c06000e10310198007500c03200d0082d07499130f406103c03c424a2a0313600001e5962904004041410342403994001c21058001d403078050210f080003800400300810f80780c0105d1805404110018000507030800d4600354400005050322403114443c1140b044c908900140061a0000720a004012039501d0049200b203403c2a04550748121510202c14100c0390b1202040f40011040c4124001030307a03400200d10040301c990121924400900816080b40c3c1003500054000320410039507040c41149002d400d081201d4900d003440c9401e0000c1c2c0c95038524080102895101c1010401c00405a007000600101c010007003041d0300841c4500400c6c440c030901c51003081d20b0406c0040388044480da441c81c0c05e16008150301000c8100c85003029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 481049001 1250 481047751 481047781
    0x1401020a02030406030b0609181806061807110102030106090801140c12042a0501030c110d11010b033403020f06030606090d0303061707140d05120406020304170114 72
    0x204d41101c0200803088c3c01e96a0160113404203152040361601508007180f81c0140800300ca0100c800039480312051010726030750312000012005101d43c0c84110341d5902002215000c26103d940c10581d130010001080603074120701c0b00700a5614403c020410009905a01e28801d40c05440040d503586040044060704501100b03003560080c092091001d00c950581c0704a00740302854401900c5040d600c000500080d0b9060281c21000500c5184c81864001c5078090700c0d0b150480001e810050101d40c12110441c0e003030039004902400c01c01420b40700c40803c08070458100d5a0315007070030310b10742c0044c13220400c0c10040381d46110241c0e40c000c2d140b41e40900b00001880a43d502c081d010a82c02041400805203940e01c10b010302041c0f511a54010130040e1030302c01d85615034203040f0349003c0981c002400900400036200704221451904481440702c480c602d081c03c41c144010140c0384001501d0004011400340e80010080085444420b4410040c01074003400c54221003200c205440b41326102804034100000c60515 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 481050251 1250 481049001 481049021
    0xf030807082101090c0509010e010f020a02120102070309051507080a0c1b08120702031c140c21070b070807030605040204030c05100903051c050f0d091401020a0203040603 75
    0x40740740742100d0101c0c9a680310b800ea18403600d02064420051007000850b00411444202a040103070426149a0020b0f0604e84a02c03150781c1080b4602040c0070a8038402c1007184809500a425001089160500301e4043c1d03002c070344180c0c085984907600042d203091040c0310600c940485400036080c044560340e030f058154040c042e54002c02c24100c00060124040124001d80c041c84002504401443c0000132810078a414040c000000000c0c458403000d610089180c3e1307041c044519002c5440721081200340d6520929405032100c0ba040803940205541c000189200c0d02614511010305111000040d05018400da0720700410a000190119a40318022500d00381c0010b91810013107005070f2234a004c20300b00c0c0c00a5005651108031a0000c00880c184095450410712a505c2c1c62568142036032110b80d41d40b1030b44d6020300060b0b207862014010365480750060f20380c843e030804404c6035600c2104c02c031b038005001c904400b030313400c0440360521002012051089801c0c54503d078005d07600300703031408400750000d10360710701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 481051501 1250 481050251 481050263
    0x90f011205120307030e0c091b031914150a120308061f0509040f0603050303011703121302030c0a0f05120f010e0607260a05061c050f0111040f030807 66
    0x15070500140b010202941c49a041580d00041c00318294507218601040c10f040c141c0100340700c40501c911003c80c0b544a070480626030f440940d6a40301c104458003c000b1000002494900d00340110411a80c02084e01d4000d2818030702e55111011550100114070703901e48541d00819004100c0c1400080c020031410f80e029034004c00a5031100d614085070741c1d1580e038910100c0c0000e480042c84d89850b00e07003403080c4e00c11031807684000c00c0f60314291740e910703581c83c80180980481ea10203150a034013207040400c221401103030007000794030301410304038026840b14050a104074403a0041c404090011305003079948500b00c606040f1208140d038038000038010100718265484025000f40b41c10191009024007600f0707100351484c00144441d03d03000c0c40040c03039611022000784006501981c8440541130300510240c020035140000505900c030100083c00f111042d051301011000501c2111090110120384281002b412000920440107261945000c078403480c0101d0b19480320401c02800481d030360f60003800d201c503c0b5035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 481052751 1250 481051501 481051513
    0x3230606010503161e11010c05030c0d09080d0f05010906050103090c1502070801110a141c0213030203061e090115030b04080f040902040602120307170c09060412020f090f011205 78
    0x1c000e6600300805d544604002c102d490810b02031a0900f4030500550310319502e030050960400054002e4070388103010320159001d032984c04d1081409220401c6658200044504004a0400c9048000680801d01c61200e0040c6040d030000352650190091908450b400540038981a0410314244154003164600e04214420b54038085283d0009101e40080d644840103266101c56a40380300405a60710130a41c600c11400500c00046108804101c3c1c0f40d084800d458050384407c0f0b0113000c00c80f00341c1c113540045e500d88108400d03c0200340b014890403000000f45840000c0542c7d41040792400e07294007140b40803c030441079100f04045004c2c0c500302a045441980c50070300c2c2141c0724440006a40094120303200807940010100f000a0301000600c0c540440c2074100382c02c0d45000c410140170300ca462002c03040740102030380c00110900005022100700c00c5000700400d44503511001e40501e201410720040303000302c850160344440c501e000d52615110f5000300c0e1440701c085e0300b002e91991820501c580101d485100711 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 481054001 1250 481052751 481052777
    0xa0515012d05130603020a0f120809030102070807080306010f03111602040e0d08101509051306050a1e050a0305070b0a171501021b01080a09030215010323060601050316 74
    0x4581c01020101c83c2030101c2e82500794010008920b400d90b0242d00000e225802c1080541401c0384078015290b004010303261280949400b0901a102c1e6aa009202010014000e010400c400000c0c40c042c04083ea44e200c2030003202c010a400b1905540d220010008040c005407040800260345041d600d07101074404074440c03040d00c00d281e25007410140d080011540240c00c104460401100441c01081c500340002100000c0301e00c0030b0410f0005000d01d5009906420314085d8002450700204001c10016001800c442e966402882d090303076240c2d94010341d80008841c005000c1c50b000803100d003581e810501900d01c1610344800c03440560300000243d0244904c1000020241081911640c4500180100030860040800c00203060030304100d207203040f4a50f4400a000d580c0d0f4083c0340d4030b92001000c840010b0800407400d0591502c0502c005040d6904554000442007000008902000140c40f12201d9008041d81c050151200412190140010b5040c400152091a0440e03885062521800c182c1e0340e0103d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 481055251 1250 481054001 481054009
    0x80c1005040b040b0c0d17040b0c091005090406080106030c3308010e060607030c110105070c0f060e0901080a030516020402030406050f070c03091e0b0c0a0515012d05 73
    0x455403089840040100303174084a07450900501c1c102ea407180c50320300b0070740c3c0783c1c40142200002c010f40050140a0f10400140c0034400a504585400c0e0001700320008040d01d00314020f00c60f03445203420b10b0049050040c0001c04c248140201400c2d660312107580314001d42004202c404095614000b01d00c810034504d07110345042d45402d0824207144080d0b581c0c200c607605042002c0c5480802030560707400b4050402011002c60340c8001250b03030595000190304142d1f11550700480315030060310f4000d081c018540c880043c0d5080c000624000b111201c4c0c485040d01c0f0b2066040000ca00d9003445021655000681d150b00080c2c0300700000e10b071028041e003c20005080d240c002c40c0481e00126001c554143d56441440401088041d9040e03010f049441d0407000b4030b038541c2e8014801d03090b6128100b81a003250598a41d0ac040340070004000c0c085c0200c030151210720340381019580350201f20040c2c4060003210325800719100c080e505941a112604050b290868410458840f00d0103500d460181031800c6140120b01030780d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 481056501 1250 481055251 481055257
    0x6030a020a05040f031a0606190c06020c240901020301242a1b050d030c110919060b0f1b120307120b030604050c120a0f0804061701080c1005040b 64
    0x2c041c800d080c46d90816080010040e04001d410f00e44511414408040101100d8101a10303480040c900301c03010100f01d10f010701c042d00075174650004038002e0400002846000c0c0741c502207070b03140c04001050789480340b60185080303110178090b003481c5140000c000040450465007000c050b0a113894444030101d146501d4a1181700c0c404000100c01224541d440f0034420020b103140002a04490121695440d12002031000c084004004090128501411091081c030340041c5815203800342100f8910b141484098100310b8000710960407039403070018041184e203c44c40540d1002418070600921740380d000a0b42c0c0400b01034180e5040c54a10444419055103035801000d507000f402d40713450340700c036503917900000a040d03c00308611503000750300000030031011480000316104250820342d041e60a81d40c911540904140324194085d0010f08185420010031849100070011280e03695250507549901c1a450068484284168a210ba00c103aa081d400e503d041c0140c011500040d062503883d003561103a00340c1241d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 481057751 1250 481056501 481056503
    0xf140f09030d032714010606020606090f0f060609042309010609050c03010611070801021206090a09050703150f0614031507051c091e02040e0c06030a020a05040f03 72
    0x114040388480c850308040000c011024a54101408491042401d40100c1640401380414115800d50b40b41d042c4590a0b44d015075030420040203001c0f150305c07901c01a588880030340305140034000c090b0000f44000c41041c1d04500800f01c0d0019514030f5100c2004101c4c1d950000101158800da448616201450682c43c004146400003101c03202d0034641340303044c142110041d87c03009502500b0310041010880b13540089a042d00c0581c00d01c125200d00140f410707854403289070040c00481d0b10000b01c01d04109400030f0524442c1c0380407122400103541c0c030082142075840160005001e80d00c03454040c00090150042c024440702e19040000d20301446985034419100250b01045c00980c01280da8a400d041c2403152451020582206e4046401c088000400301d00c14522071655900d003080c055000c108060700714015203500004000b0941c095058286200f03001c007034080744254901040c0c2000d00e80003003100c85007280024515415551441220f0340039500041100d42000010480414001c0344200200061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 481059001 1250 481057751 481057777
    0x7050d0f060807060302070323190801030209161205090c21010e011415030705150c070812070b10050307030b040302010c05040b090607060609020c0a0c0504020a0804030f14 76
    0x80c2c94150310714180b064581084081500401a120110790410b080e040354602500e0741d40390020311206401054000c008050b401103107007082491640d5409200c45060702d000312491256511400c024480c845e02d4221040c0108030305130700b02e18045500e40d1009601000c10b10a5400c66084000041c90100c4985000000d000d50614281d800007424440c210041038650001c02c14480c0c0d0710802e24118074005c1000c1d610041024611115071014444c02001301009417280d41c02510008951107140c004a00b50040e601c20200b00050110001410000c8240790f240c0b050314144943c0c0707030031005207001401c8003100340b5100e00008a03901c0410000c8010b50195640201c1810540380084c25075100c0907071031080100c14881030091241c4241283c590b65412105c0c1c41e039401c02c030724024002d080140c0c03002810034408604c002c030b00c1c0c4010403180801440741c0b12104800b41c42c3e0302080128011005010b00244446c00080d0000740a10140301881c071070782c1404212108481c0c0a964940c0c0117a00160807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 481060251 1250 481059001 481059011
    0x220513090f0507120b0a09020f0d0303060e0c09011d06030a0207050a12030c0f020715081801090312061a030c0708070f0602090109080312070e0103020c031206101110020307050d0f 79
    0x50006045045d500102c0d10f420510200715260001100b0081e855411403203101e080c1c5401c01018004d6002d00b00a000c803214019251501011010090704940640790108101aa10782c90083c2c61030952074003828010042420764490030665030003900a190100e50910a00c180794000c1560108603e1107403215640c0416540c01b048401002c002c00c484000c002d542c0841020f116904400400148002d540c0c90b042a10f0340d42e8070107200e0001004500c6400c15460206600281540000f80c220302c103030501c0d000d00c511655108011000004403038059145607061020410384c80d81000281400c50041c10b2490400e0215100c40300e601207420710884d0348550004050500e541c1100d1050028628000610704010469000b00c40c01c81c0020307e43d50400a101ca2040d10680c003d6040d00c500742d2101c8112038036140c0d582d540c0c541c042e00a41d001c910036601040225070551040c00080704404d250f2002c0d00d03400881c042c3c1c0d140a500060a0001881000e106401503404c01d8862500d0300d030300008000c51 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 481061501 1250 481060251 481060253
    0xe0303010906051008010501080a02191e020d021009050f15150402070f060b01091503050f010b09010c0b07030f09260901090e0c090a0308220513090f050712 69
    0x8100c8089a02840c0204d48801c0d4626400d600300c41c100c0d04440081c02c15204035500c26a445c7c6c002d100d086240c2d41907058003414902a95030000c07501c6108244000d0180b102d00004034181d82d90201c440700e050043e130104031981d0320320f07120743c1005991a2069044989004580b140d060070041500c60043c40410408104408440216000c3c1c03002603042d1030442c03800e0816110010080b5200c0c2002e44816164084074143d64401e8000c08024a0300045068041110410050140c10191024241d114010300007050600300541110804e0030140c442030300481c02ca64402a00c400001c06c40c01c203255482c02c2d8200c0d450b884d4022400124402d12515403e80c2142840d8038401e07515002840707140c001032009280598005e03d9000564a41d041012019a01e030810b90b0020b1103000602900444401c20000c00c2110000203003d40100c1c0c80f0182d42c482d040301c054504140c42c10301c40c280d800322038000c8198000429501a08815000d400446000c030b001d0b451b4907140c20100d0344001d460311542e00c1600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 481062751 1250 481061501 481061519
    0x4091208100e070f050913020a0309060506091303260c0a0f020c130902060d090605010501110313030b06030a021e0307050405010b0304120203071209050126010b0f0d0e030301 77
    0x10094a6848005002d50500300001011907005405103011720100213924806a613030441c40c3c81e40010848800d540d5020007100c0100500780301d0808503103060510300408c88600d0311080b040d02c40e031080040c10401c0207040d1401c607030703141a1459255120410400b140c4c212a1081c4581e445040405841541c4200d000c1005088800100d01c41c0c04642004e41105166a40c0350007111031081c4800f0f0100e5106040d00018140388264800b1500940c80e002185040218a41081d81260800d880c0c00e1700110415904a440c0d20070507403501d03130b4030b1016401400001c007204c900c01c4d00720030081e085918035401030f408100d02c1c480020603500002001000860146000c02186001e0001980d0502040d450641180d02034003014000405203940c240400d0621842003080d602c2d150b81141c07821000a00c00000501241d409004040c00a803105000d610b040c900030040c00034402c01109501c1e00c0c0d03880c01c0d04040c8190803010240c0400f050410900520333000d1390089400756440500519900d500d044070705 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 481064001 1250 481062751 481062781
    0x213051e040f031d03060a020d0f1d0c09040f03230d091103031c0e01020f04090f0609090f11060f0f1201061103030703020304080708030c0a0f02010e1b04091208 71
    0xc0c04182400307046044e955180410740359000072201d203015032180b80703400b00d0001400c002012110031914000c0321781c002c00c1e034006040c91500414020340740c140c4003170001c4c40300080003184c0280a0b0b501d006d00720b43c006845110101054a03080b6030030300200e505a04c0001003503110504810f0b040c0d8803943c200c014081c200c074000c038400380218025841c1c83c4160001114641e10300001900035945c9040004010f4021f40480e4190620005255511510303813440b4401800c1442c240350055150140100d0b0702c903518400e0500980e0040344405102d11143c1c0d8000310221500152500b1040c14810344e14900d45401c0030340001a803480e101c50300c0b014a03841040c3d030303640140d109000700401e2803840302890a010080742e03000242442e015a0b269113a081000d0180704045d0002c0100000204100c0c8000e0301d075016081e0090b05507141030380e418102804900707807040034070482026000311100d800004403141c0480004000074002007004482a120580b8900d003d0002c0c40c08100380b0400c1280341a001a41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 481065251 1250 481064001 481064027
    0x8060301140610180b0a090608240609030f030f040611060402060a1407080d0905060703050903040603090302010b030114221e030c151d06040213051e040f03 69
    0x10040d094904040001c3d10f4031030105550081c45400d620020042c0c1456031100b010b880c0f60900d40b581c030342d190100140060301c00d20800e000135108601040c4940f0411064120000c400810092084000020414070b030740003200440c1e15100f402c040144000e01030006d031403e45000300801c2c0d141c2c1e10700b0102800c0f2180c17802100b5100e4010000300401a0f0b00ea0050780e827445e41d14030b42501d0f0b0707400c0320707a0240c00c510444c203000e40604008030f04040b44046075005440034621402c182c0b2501d4945030000d03020780d20b041e1280350042d0414001400b81c180f1903400000854000d100204810761140d02003400c580d40040740c1c0c40003a45210400007448110108441c0602482d07802c5103911801e5210103940e81ca40b4241d0312602c00300d06042130f040c0351243d14150300742c40e0044100c03440c81c041c0341c2c045001098581001e0540001c2c9070001c0d404d5050204600d0711940c0c000d40002182e4002d10304090003050300500414040c2d002203200074003410700d15002407190b40320381480e00d50440f65080182c803490401e03003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 481066501 1250 481065251 481065281
    0x4020a0906122d0309090c14180109031e03030e0a0222021606020304020103110a020703030810170c040605061213021c1109160e22150f0503060f04030c0c030209010608060301 77
    0x2601c8480108d0100868491018820400e49070300c8100380101d4030541c1c6540080e150044016211890302180e0740d07080c1410340b0903181040a500e040141e80e480f40900702c006580f10a002c100c4401c2d041440010b2003901c00c50b00c034014030300244540000380c1291041320680b9a01d03404000c000455030144281d4038400c4616210b10300380400041c000b541c8030f50502004081102c0c10700481c445c0c00d00f0300101005050720051511641d895009001c0c1c0d111001d039900c52103141403000018803030924034100d5000c640100111203c954450340f100e80f0360300b0391000407600981518401c2d80e900f01c00003082d9074810b20030112100c1c1c42c0c070024104017031108058110020f032584c0c4541c100e02190405990001d034802507550303907040302011031880310359000200001c00203424201345403040a500302000050304d481101540405440740207040d5102c404071407007484803043c1008540800d01501c030700d8014601c1040701801054890b80411101d201c00e0740860301003a6900140140c80c0341c00e0055408440090b2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 481067751 1250 481066501 481066517
    0x1b05120c1302030f04150b1002210406050a0516020d140706050f12130506010801062103021e0703020a0b0406080a141603060909050604020a0906122d0309090c 70
    0x40f04c500320103c00030b80010001c0c540010004d0450f01e07103400120208600401400c2d03e81103090b800b035282d03414501d80425051080944910802000051f41c042e02e4003a501c0904140907084140c486a014a030000d2104070390070540001030b0396042c0e4607c10107100f8955258009002c91450340f426171103801600c07d111040c0400c00d900d0380a0000d590700100b02446142260322102c8036490492010f4001400b071340103544c004226080e0540004007156804400500c02c800545400d4245d9814041c000300141c002c1400c40c5495881c3ea41a0110082e100c0b00381d131246641c907400500755410307540c0320003200c013800300e000c1041da5040340550754000c3c4803482c00e1005611f50444101103075002807502c1030300a1404460340c20503110754010301c003400c0c000408001e06203590078069684c410071501280700d0b01b030b05400807803208142d0082c841203c22194408a88800035034480e48030104144820b060f000d088c000c0c100310040c150002000407070081e11001e0039907003001e42e103c054800700300c0500248140d0b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 481069001 1250 481067751 481067761
    0x1c03020f15090a08071109090303220209011a1201060801180b0a090c0507060501080105150a0821120a0e010c14040b0d0e07150807080903071b05120c130203 69
    0x1040765242107501000c1c8980d41d40e114501842c20000f241b00041d0130000d00810003045000c0007000798010900703089100d4000c4400c10221102c0d2006170030003900501a4001000301c04c030a11001000c60800407415400c080750b00c050349900310f000340e06c01c00025400314010800301c1101018ac2501c043d403a28203001d60803600d008120300400601ca2110302e556101c0e00c42181d43d114100380e13030449078800014441565181006400f1309000e4409010b407483d400105441c2d440c040940c3d401701c2e04110050310720300001c8a9114031011401807041c8418004210240603269903400030351288501c170900050f20384800b44c0d801e007190350040200003440451a900f0306007115280564046419030301c1301c2c940c0c3d00c0d500b44150000c0d05016512501e284078948000c940c003546030008000c01c0315140d403404610b130303950361045400c48015a0700c0b03901ea810400111022030f007000044ca00c3c1158030040da00786241c1d2000403e00c17800490400070542d802110004c178462605940396214288505e000398158201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 481070251 1250 481069001 481069003
    0x30906070306060926010e0a050a02030c0916030b031f15060302030709120f0804060906030b09060a030605060a170f0f0d0e100e0301051305010b03070b0313021c03020f1509 76
    0x60300b580c00884071020401c02e01050b07400d4120901084498043c0d5940c1c0c0d08c1c0303280642c1d0f64044600304074403900811005803018200002e00301d104039603c003001c020380100c0e0f00064005142c0240911741600034220801c0110406004c1a07850381e1900c1700000e080b175603ca02150303021107940c10100415004000b0310440390781c02807030f501c2030390b00c40710003a881c1503000d20700360320898036090b002003a80d080807c0004500e80c1049000007100e01e145c6081c0005403d0004021155408444841c1e009400343c4051010420340c0d807189d81c0c401c50103400b424466031128006501d00b091540100341341d03070100000c12843c0e2024411030044148044c0109020344210402400d0780c090195114000c51488540c000000e224011840c12004090000c00c51401c0080d0100504041d4400a440a60800c3c0b801a440c0c1400550742044030304d591039080c01c6482d11400402c0c541e4490380705a038030403008240d5203040c5a528603640c107003500c07036002040442c0700310800a00b4541c4803002c01c07480207881410450240c034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 481071501 1250 481070251 481070279
    0x10140609090c031e2b0f0504180207083a050603062805130c080a0b0c0903010603080c1612050a150e011514030313090c020c060309060703060609 64
    0x1130b80c0c1140741d2144100c840c0b440c60241c2005030341c801c00c182041c15480c40072103241c417207145140b6652020080f400c1200140c0742446035101e03550381c0e1045002042c07100b00c0c84d17901800806204d45410f030b282032100c000b50b181c08184403803090b46000094031015080d020b0812142a0489101010f000700c0c076040001948803440140290f54580340410750521101d43d80704103080d80e060020040009050001060740303001c001400880306800590804940e6540009504161903840b06e50100ca90b40c80140306130040c2c001b0640c1507010b40d240c846c080b0001c0d0300b07500505851000c0c14000c111002c0c40100070003100115038031020710205000802d00100300c000c81c0640b05190040c04600c0310210201e00350008182e101000d000a500c0c10200d1058100da01d94500d044903080c60400d409140380c1010191248954240d84c54050000f601c09c02880c00d46801106148115005031040c910707a0700e000c180e8561044803400801e070408010000c01c15010321814001c1e0105140245143d400c021a04074600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 481072751 1250 481071501 481071523
    0xb0a05060922051e19090302160308032401021002070203031b0303041401021303060b04020409050727051e211b0405060d021210140609090c03 63
    0x59400140041d468444160300e140c40b001c074604010300c0b1654080140001e100565142e07103d01041c0303103520008400000643c3c05104101550985901180002c07401010600ca0480943c0035070200c0303070f2031410104d071100e0040d4044c140362541e81c07074617a51140040340440c102c0e9450245001088440382d90002d185080a400c5900050b5140b00c1400024511300950035654040c4404a04200707a1030b4021000e140282d120340c0351452011200c450203800d07401224021702105160340c80c10004144d5582201850460103440103180a0302e501140c030945074100c3e002404030b80540000640388500ca626030500c0e03400a100c404030707107040c00c1c002010381010030300d200c040c64008901a94590380b40c0c0d81001c0c404801c41d1491907802c0e0028165a165507034035040c010b1021440f803410b105c90505004507480303500000c1481145203010750030006075091004105519108a01c0400005411440344103803c0702d040c1070140c11380c80c10808001d00a5401000303210f441e007082340c1011316502c0004441c6403030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 481074001 1250 481072751 481072759
    0x30e070b0c101d070510090b030a0204090f050105030613140319020f0102030105010813050309030d0206060f031501090903050f03040804090501050103180b151302030702160e3c10090b0a05 83
    0x5040c400702150208140d0704184240100001400920b8ac03e0380e0040080300c0c0d10141c01d00243c0802502e400845009114150f0946c001c480000c80c046c8400880024045c42246014040d05001d00c100349107800c6031002d58555101c2c4122041c203da010031089040790711038030003545190305200c002804a40090400214500344802403020001e0030300c191008450301900302d07500546185402961490103a8245024292141c6005c065080120f20300b4240d2a144044c0c9580b0303407801950b02d005080550055041141c1400311540007020310b00194095802030140b1b680b0b80341800940421a10182c2c4146e050601e001a07250301000f0010030b001f021a0020034519003941c6130040501021040c203040c0380d214030301d16803004080101c4e6000d1800f5403130a42c21034940d5102c40040b40c030507052034060f800703e02071440006000703403c0003803900320002a5100d0280c00e44005800300c3c017600300c140c0e40303859000100d1400c204c0810301d01c00601008103281e14040c065030f96010041120442c042c0107a5000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 481075251 1250 481074001 481074019
    0x70e0a09140a0b0c190c081207090603051803270a08060603060a02040608040219081204031e080d1a091e06040c0e010e06071a0406180b07030e070b0c101d0705 70
    0x24860180280d59500d9881500030140c9d00d44844001d011700341900400010900d0000845c9002006503511800000500e00540c94040e5103800b51b101a52183c04240074292200d1200205403174140440e001060100002e000f01d080078004c0604100000741001003142c07041c0000c01980da40105020b402c40e40648920040007038405801d121001c194005607214820402c003481c41a54807001030007100d00910b00390040e4001c200000c0038641449601508650003404040b01d043c0c4158001c1d0032210030180303241512040c0c0c401180714a03008980001d5052070700810100da490003541400c1d4404011202040100207401002c0d0050f41700c070301c000341040500354030302c071880e10b90008460a183d040381d8004080890308801241070700c0b040302d081b05d201d4100380b1540035540d01406001842036011448580a98035480210000c0c51040000e001f140b084280020704064200001c000c65028580030b02240841d410314202940c4003000010b003948450340f0007404040340803461800762003003181c0d1441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 481076501 1250 481075251 481075253
    0x1524060304150234030f080c0d0903050304030e040603080406141303060605030d05090105030a0218150d06060507020303040312020f030c070e01050111070e0a09140a0b0c190c 77
    0x1190242d0410520464800100804880040e89225150007264840d03107051000c21050640300348000c010040c0440e65541c810140540928505e80e0b200184800307490914030500c040000361400c03094243c022880c00414002499400354895003c0d04041c0d03400e004d4549942c0d200651b0344200d105200810540204c410b1454030303024101c0b039000c0702404041e44641e0316420240001d00c018420148244200c1740501080c0340640f0507034500007016128607041d640e4042581c00694004904240c0d0030900f43e0402400740c4d00c1585154154000c0c18045803255040e002003000c407a0103400c840c080c480244142030040c0e0f000804c0300c050301d07070004003490f42002c55141680f0303002c500e07500c07801d6a00010519045440c00000c0d003c0c21104000c10607485a643c2c1c000640744c6842007152400e40c0c0e000b04070180710400c0540707803260300140a600000381c0440d60ba2600320840c1b0032401d1011442d08108841403e000302e800c03030950000f1040120754940300d00b5264040c20103030f00d086540b0921401c011240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 481077751 1250 481076501 481076513
    0x30b04020c0609030316111015030614010801150302090a0c0905210c0f0d030305150d1505060f01081b0f0d0b040e03090f0d060f09051524060304 64
    0x1401a011041110b005081c2407490f103071641c00031110b0466981268403d040400e11030544d040b900304d00390703028010492284a000c4040c2c0344940140a501d40080d000000203001845200355204404010404550400e00000d081d110110b000c03203210442441c0c24400341c0d9400c02100d4000300c0c10030001680b00c0200c0425164031080d5440b86a10003105441480110b00720b205503000d450900b01034031400040c0d00100702019003d1080f450b08946005120b2000a000b64445074000b0001da251230204181503000481707544141d501200c21349a1a074004903015194010030b5040401121400401110080001c0c00ca80d0000d215140c407004003403240340d503c11100c084519000401003695a1040108070181c080d040c0b80c030700940a40c0c94490050b041764004400d980c03007804000c090110540e5031100304264031090034816910700d42c1c0d070281c01240d41254842c05400521807000303001440d205070384d14040390000802e0b041025010412026801c90545821041c2c1d1700c0480d2084d80f640c407581090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 481079001 1250 481077751 481077757
    0x105031002070c0306090302030d0f0c09030b0414071413050112020621150f03060105090a0b150c010c1701031104021c0501060809101a01030504050f10091110020d030b0402 76
    0x509507903d0406c0031000c1c980c0c01302c0281140d10484c10203101d640100310500b011170742201005000518180414000030707034680081074009009958510134840e050f0849410044158402c034100190100a8102c50070050061540d00121310401c0096614007403240c032a1490a41d00240314120004103500780400f120404010340e00452088070080c5048500f200301c0840110380c2c18030401d445d0100030410310b40021994140c450107002400d050300c580100101170720340501102c0c3c0c48004a02c0300d100a001000181405481880000c00c24030741c050740c083c00b6a820750741c40002d00540400140040727a60804d24080c00d2005540040c0e4814254040b10442d8401d13503413200d01d050070b100001403c25031024550740180c06050a0f2900f00705618828401c4030b0250311036007000132000640000c40d602980c02198010b01a03000d0382e90103c0c0c0803840c64201503032040b81915040d030703400380c07030023070048c5011880a9403000396030321105c2540750000070b560380a000070702c48200364458082c2d0240d41c840c2e4050f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 481080251 1250 481079001 481079003
    0x50a02070e1e06030309010c150908070c170303041e0f0f0f020405160801031e02030f0105070e0f031f020f1b010b030102040f06051608030106030203040c05090105031002070c03 78
    0x164411900b4902c100c903038120600a051080010004007051152501000725405020147c40741818071903159a03440c9580e111401020080d546d490000740030842000040890610502d807001906040c014201c0c0e52400022240b54035078014070070040090a02c000d40b05400c1c0e51a1400f1110a401d4649201500000394000300038684010160007080905d042131806944220f03410710441d0345600107a4003607640030020fa00000c01d03003001040450350756000c044020705c480e01c681100d100e0680100c1d113080c0c0005001103036a955802000900c0c0d45c003190400c1c2408003110300c500300a0a036800242c1c0c44c21b1024190040b01c4403006150881c1c0040d0741180c000d0001c4007840b43e110072075194078072600180c0114848095090003201c80d4a464180b007100e0955400c90ba03480244c90900d00110303040e41000c01c409102540c0b040800d404204200040e50007021070307603030259581c5064901086582070300da1065020322400c50040c4030564000c201820846611880140c40c0c3c0140d041040340308001d540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 481081501 1250 481080251 481080269
    0x4060c050f0f10053d08010203060f040e1011040602010e0a020d060b03100e0102121e1618090e1e0d05070f0c090b180708160509041d10110a050a0207 66
    0x20130000c44003055205d614080d002c1040d451510380d403941124240c0c80300700c8600340c3c0304240000c00701c000d141603440901026003a80c04c840f2094040c00b01a421600d08020740341740144041020842e05509026151800707450b03501034000d000d07081d404143e01c003860100082c652501d880d145501520100840514156250020b010309010309420318000d5200500d1001401d01e0b000009001100c03a5540449480b031451403c21143d0714841040b4030403403030400c0c080c10000400c880a140c00120890040680801c80700010000301e4403c40351301e03019404100c41b41401488000c01d5440d1004540b1007200c4074182440c65407000c0d946030032900d4018452008140051150011a03860341c1d43d880300004503416600d20f084007000c410030000200003111301038005a15000081d680c845207a49005c504105820511304260b06540011b05a4242c8180e40c800b06080030010014018208003401a411401100300b0401440141240080c4500c60049041c00340010b0545e00b6039100b00b00c05002801c02c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 481082751 1250 481081501 481081561
    0xa020408061503160f170109021e010c080d0f051501020c10050c0303040c0e011a03070e0a08010c12150f05091e1008120301050117040804080304060c050f0f1005 71
    0x1015000300385d10980640011401d0389441013528403814452000f0b40754000380744052211490318040042c039064040305040218203508200010541e034040c8c0b9488100d901c020400061107035040d011680300070800006010001d0010826980108681440d00e03820b5625004282041d14169100d00c141580d10810780310020822091100c11000001550401450008266a1215207170726410b00c890303200110540800100d003009005e002d0350488080c01920b0007400c50380c1c5003409030840b90a048850046440f1050490040f64244240030514181c17291640110303003000688e180b00b410901406003d0f05d6005c0104044203400344814060ba00c07440b0700111245022002141c0c46941c512031004244190000c0c004032143e04d50035241070307440683d03407805035511401602c01400c0f0003420540b040001000702042d17009081c401800902010346038420301c2a0942703002031404800d401c0ca001c154110140848600801013004c0000d00540d10303001c0783c1c548800215010480f206c1c034416442d4800c407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 481084001 1250 481082751 481082759
    0x140c091306081509123a0e160501051606050a090602130303090510050904150b0d02070b0a020c250503070e070810080c040216020d0303050f0a02040806150316 70
    0x8603c01c82c800c220403c1910034492600854582030701881038000900d442040009446104090a020703c0040c446c00da800c1030300e0164070601c11120342e00800c00131900003240c0d6004c01c2221306414001130000b03180181c07500700103c00c40003007601c40d100d000340310640300c3e00071a020701c08540000e94240c5d0800000c6503148549800240061420320044002c0f44440d0303000640c40c07401144890030380110f6250350703150441c0c0d01c00b0000107201046504007680103594001ca0f50404032005804002d07014040186e031242c0c1ca040603000c0010050242d101c5034010007000c2c40662010451241a601c04e800e17002c5608154900d05e00d002c42640c11490300341c4200400002ea00340302030811030145129850b1b00c40d940d11283c4003240c07a034406018424030355110103295007203030505074000c01100c214a040c40c4442040340d4001008400c1c600400e83c00680c0360400c0c003030503503282416542c101903440421850240751000080d2207090003801c2e221101c1e604a2000c9094405221265100003820a081006911 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 481085251 1250 481084001 481084033
    0x1e10051f08060603030d0509030715020405120309030709020915030c03010306110a090510120e010e010c260c07050f1f0e120d060f031401140c09130608 67
    0x803036224206148141800105031001007003a501a490140145103040f100a40c20405070001801c445941d10081146401040d000114001d03007a581000140e5100e140c0402c004444201280031038041d04100180751080c0e034000750030802c44a400e01c002d0384460182e8001486800e03c881c80c0350680800108019061a4080086060381d1084808014030b40391802c1d8038a69001d034101282c046024200203000c00d282c2141e1035044000310f40351103c07900c1b00210f00e000a94000602c20032180c2c0d11244040340e800b50a02854031844002c0c43e25112525905d14001086001d80c12089140c0d04c0180100d6910b04455040760300b01c82e003003c210f85900301c41030100356440181e01700c04014001044911885902c0c1801003c0c18000c445009003e18542d54003030000590210307408912081c0c1e191000188010f6001d803000041d80605110046881003020303085c00d41d10160040603420000c1e40c02c101101e10340c902a00d840d40d0090310450030003440112148002c10b007070340201e00c0c4c0344544582040d010700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 481086501 1250 481085251 481085281
    0xf0a02010504051204050906040f15091a030a0302031909030206070807150b2b06090302060910050606040605160b01120204060506041a0706061806091b021e1005 71
    0x4440d504030b442251307416522800600490240c207920842600101322149800d070031920600924050005d58291a180b054032540c5c02e075400104c605444050101100101c0700f44840505001c0c1c1c054422007205540007900c0c2d10600340c00d141008990060001ca0b140329014a00245d035000d00b5a80da554101c0c20300032202c3e00402e1040711600858201c20b0381d440641d0040130750314038028105101101c03400d9075083c1060012075280d5459070105010901242c0c0d01d02450340178074000c1d0007420080c00d080e500c05003400d04a003680c0e00c0c10b83c10b2130107100b201e0311000101c504981e040e180458480d64007c51510015180280c090704002011001080350703c2d101204140091003141c041280c6a03580060003402d0003581f0581e942c2c0c2c000402121407e40f00d14008098482c49224000f820b070b03441d5000310441c91524014030380c1683e40c0c3c080500c0f209039640b1811207401c440c4041e0350304111000000035566480c1c1c10703030481001c4188030099201401000900a80c48040e042804a460b0242111151039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 481087751 1250 481086501 481086503
    0x70e090f370309150519030b10020304060c02010f021c02071d0105030c010302030c0712170a090b0604111615061514181306080f0f030d0b060f0a02010504 68
    0x2801d401c449002107004940c1c0a00542e4035440d6501c08901d02800e1240703103080c207402801440ba0401c044114180b1102c2c00d40001926074400180c41c50100e0240080c01c21529018010b640c42080244030310b07500302543c5c110403a4246000400d001c0d01400032400e0a211800d030410f03c803203107000707094515004a566802d82d884940401c80c485030400c05e01c0301c1240288501501034000416142d0035500c240c00644d8070440482a0130b140150390f0766044400300701e0b00c0a03e4002200c6825480c684201403c00d030743c00c000e005a003402011602d488204103600003a040d03500c039646e500483c1c0c1d4456100c00a58100400180d9100464207407424184681850102c3c3d4100180c50540045102c0d40c400070480c44101d45075480300c40306940c404600c4041d600c541c100b90030180c4c1d40039042c10565039850302000c0c2030640e5200800e03480e01e02020309251222404500440c1c1c1c10142c810b0a01080c00401d41d04010310b000c02c0814425401c40c04112144074070510000c8140d0000368404056805401c1a8001c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 481089001 1250 481087751 481087813
    0x5061b070605090106050f03150a090503040f0e010501120207081c1805060402090a020c030a0c02040605042a0207050f041503050f031306080112060b042405090c030603070e090f 78
    0x3c1d04143c20107849e5894080990b280350004008074100765060703805100c10a1013001206c1c90581c46030814620701c140d96000302c08441040006015a592084443c079400003240d4096003083c0740c0390394066407400384425441e0582c80c000e4a0240d00501ca81081140b040b0074000690150a00c1c20846c0d11180e08841c184d004090703c40116008032058400c0b2824038248002860415000410440341940d03181d0059030b029440e4400400d2542e11032040d07410828001149514080c802000e030117514541002c0c0fa025900541c1040020f900c43c8201c00b141034030f00f03c40002e03c186c0c1109508100141d00e400190491003240f001c03040403e800401442c3e01130460005805555440c5001c41c0d10003000d026440100d8040c0035044002039885c0c105e042d003110000c0001c10451a454541c182105000c140300e180314208010403c650b041c01140325030050074030143c96145140440100b95213600c1d0303105e82408000c803c40010208081030120407207030314445c0c00341c0e00341c3c5c094010b690200c800d124540d00c0c40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 481090251 1250 481089001 481089019
    0x150516060608071d040c170a0602040e150f0105250602030a0e1005042301020d0905030409060b03040b06090c0f21070f0903030e040e031c14010305061b07060509010605 74
    0x2101410102c0522a9a010b801c1400303407801c2c649800d4048111f003407038400c980304022502001603c54006000504411164140c0618154565040300003120480074000d801d0202c1800c1c890741d0010441d068880b584a1686141c1c45030001c4401200844038007400051000c02030003050000d0b50092044003080b80d00302c6a420300e61048450403a00d05035001440301c5e994507211305c0ca02c0707031001107507034201715040005040658646030103064500007a412503294000144c14004005584a000042c02d01e0520003030540c5015070f2805101100a00303503902c0341c041d040c0010841c5035500203c2d06180c8107202804d0b1035496142c0d80c0e16404040e404418075007a4030a001550841c46100900344550642c0d80394403c250ad5902d0640343c8004d01d80240c0e030442c1d10744000e001c008604100401c1c012110b40c0c50040e0103031050b403500f0b044881c1d00071003080704041e0b1001040400d1000038403030740258911144100405502004e91b20901c130b48a03008040b14241010004030500643c401401c5030f03c1234941e910 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 481091501 1250 481090251 481090289
    0x7020415090506060f03040b101d01030b01140604050d02121015061418030c0d0807140d0c0803060402090d06020d20270d150b040615051606060807 65
    0x4d80c602881040c2141400c00f0300010300840c5042c07460b9034001042c540c02810603611512441308828245600c2400c02000d980101304100d081803005006211048045803240c1120000855074400e920420307200d040080c0420f03003503551340e4680204aa404200301c5280c240c2c4812010064882404a2032400c6400e840c001034a81c02401c4800500c8a0f07100414608007d0b02c3d00f03c40005500d12003640c15200e01c2c221100551a0040c0051505009a130319503203414140c505080310104c081e4050701e4507001100308000c8144c0000304111055403103d4a15201d58405010800034040c1a0f901c40c0d00c842c14400700c0c420300000340d00070030b0306640c10182032020080f6403040b08002400540c80307000c40002000341031480c0a8900f001104100144808e4103040f1404000601c803202c00002994810500200074074026020311600600c01e0003941c00707012040c5030501810304a8203503200c0c0000d110300026406200310290142c00c0da8143d10040401000e5240d420352903881d1050b00544501d0007001344040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 481092751 1250 481091501 481091509
    0x3030e041b1e0e0108010b0304061b021609060602070e0406110415020c1816020a061109090108061306180c0801020414060903100902030a0b1302100309050c01030b01020307020415090506 82
    0x448540042c5c45810281e460040c0f9006c0c80d82c00104192021541d80207a81c0d600021048201c00c0c3c01c2680d4020240104032082854942410342d00801806203410400c00c501ca1f0042101c3d003c44007107a2491005903a40e0410102621120b003009050160010380466100316808400c01365180d141e08440080301c107401030101c00d4102d00c2c06c3c40d01c080c030403030300140d054000300c2c040c40000c4e007580c41a21030001ca0741d40e580c0161082545514211035003c00c0041550820302003207801054018010041801c01c1c04c00704444100d01c48000d440280c850400c1c01311810b90f200315040d00c55000007094105a03a0b40d140b58003e4100703028000203030344451803071201e078640340080c0c85030a14000d001c0c0c034200c4005040d20f8001d00952504a80500a01e0440c002142920708000d20075074840c000305003405414410013481c44443e007005402d062030180300401182c400a0f1003582c0c20000e00303001030780e8824400140d185001d00c40001790322074100b540c0c1540150003080c80b02d003250300c0b0220900081d11644208 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 481094001 1250 481092751 481092767
    0x14011517150c16020306100509070c08090103052d01030510021e030a110c0d0206161b030918020405040b0406030305070f110915090c03010f03030e041b1e 68
    0x2484555907002c50ba84a40e100000e080c410500e034260b03a0350700c01641c0884d04080044402c00156074005104000d03c4c00c10721310700c583c4018a80b5040b01408050380d25986140500b2030403c2c10181e5a00016280d0905151300d1303e00d401c1c0041c070740c200f0301d584405841303010142400112001e020b60300b030700811403e20340242c42c81806035031100b8404480713807201401e254100400210030503454100d9102100c03d450f00a080030154200544508000c40a000c0c0c64618003a207500b010075000c00300c0329a000d502c103042ca82c0300324a0940020100304d5074281200e4007046900718035000c064031400071040d15507950052046900c1600c0a004142d0401d0400040720400c5c44060041401003012000051890020400451150744500c0115034248085007030860200e440708000d5243c4c241c0041c580c504417a0301e0b40d00405009805240d581460300708640710440c0d20000f402c0c441080c21840c0c140c1d80d40c0d041400840f44217008490302c214a100010b02c111408214070340e10040c1a50382d8098141710340e06d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 481095251 1250 481094001 481094023
    0x10b030a02060706020d0213030c0e011d070e10170c03040309180e01020d0504020405131101051804050403030912020a0308060f043b060415020714011517 68
    0x905688500ea4090240a0344048801ca03080c0f6801c02c120010b02400340301a111254a01a045280a040d45414040340e1400c0c1c10101c10310308003c00402c05140c402c403020b0b407106a5131074107540903101c108081ea080044841e80a5028003158410300320141d0001a42000382e80d0509414280c0c0c80f0490354030507a00c02914060002254400103021501c0102c0d010055145095030005203041442d00c1d1600b26001044d0b4450000d403640c0a020951809001d90350704802c6a56140c0030b03c5100c1d43d54600300d0f043c0c01807814144040480c4010700300d0300703100421404180c041c0083c45145031520303005000b00f4002404440b86100c0c146152002c0e840040c1c095031290b03068803600110f0b104d86040200c810807401019900c1511004040c800301d02d0b600700100ca4140980003140654007a00015079010900d880350440e90f40041d007004003149848801b8a240c80502d800140d030b907055410094403000b03078210510800c2d1309242d0401081c3c5020405003045030644018800c407104c188600f82d4036040c60201d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 481096501 1250 481095251 481095253
    0x80726030604110f070807050a0b1e010b0a0e270a020306030d020a0804060c0c080a030806010f0e0d1b0e0c22030203060628060201090c08030a05041e17011508010b03 73
    0x15805c00215540014021580114102e41260340269a0b032010b090781142c01e00c030190f840f00302400d000072016183c1d42c09441c034004e4081c20000b03c041c00034590104545114403e5215143c6681c424001c2c80f00038494440345080000c4528080000101a61080e501640240708507504800500e10115201c82c056138441003840c6441d01d40801140d11264209017034a02c20025007000901c4c070800c00070211040c0c401d448040080c90520000361510700c0192584081c0920314104050680e14028005800d55104401482d915402100c40301d24410a800c442c80801020b424044945d47e004e01400701c40d50341d00a504818403c0900b80b4141901e28403000707400d40d1082010a00c589405040c0e46208002614018a18140f0600c00c09071104160700650150350340394081c00911242e000494040c251200046103030000103c4010042c0c4103512400d01e00c03483e001106000151409158030041084403588449410382600c443d00820018000c42500c480d410030000e44190180100100c2000080c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 481097751 1250 481096501 481096507
    0xc21030103080702060d020a0e09010e131b0504110301090f090b0c070614070306030506010801020406051905070b0c220503030412030203040e040c0312030b0d080726030604110f 78
    0xda20441039800880342282d2121091206e04440c441610207009210f109a0f21020900c143d0018000640c070b06070002142454410100842078030f0380c1c440d00c45c505510130340c17002c22410310700c04400d040105034202c02e80c0301d0700700f05800710003c81502c041d40c140d544100302048890400b0b6802401c850030f8a400030300c502004000684029442c8018080d00d500400d00031600c1c030741703400d82252102005c03507005010035076824062060040070403075640504400c100031403409003400d00c060b0180c002d0410795954180610485105580f281c3e095404156012202c80018145010512150341241108a4000b94042e03254145001036405080403194040c01031403529080c1802050200e468800c15001d604c01000002192465100c00030f2056000b055414141401d40c07400c180419190000081010b09200441c003d6654070344e15401d44590000d001c95076440c03c3d141081c82c0b820302d108480648484408003800d1002c400c00214800d05007204c08000119448522280c240609210140204418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 481099001 1250 481097751 481097753
    0x9100f151709011404140f0a0803160210020703231603030b010908070312021203160507030903151b1404050d080c030a1e1e0c0611070501020c21030103 67
    0x11101c103500252104008268004011004031001c43c041e50211034010710174021030000001400b00c0c0c9505015080038010034419529004c0c5680400381a16620030031550b12108424000c1150072001407a0710001e540342c407214140540942ca181000314100e003903010201c0603020412003190000d076031a000005c0508169241103008000d021503040c14040100da0100300003504010305001140315807030b0b05692600000b002801d000320f1440c0014108401c1c428456045036017040d40d0741400003850600e445a10504046412030142e60000d800c030071040b54081d054a195400410050708071001800040144801c01c44400c155024840c1c03000030240800c3c0258908a60303400d100601480c800ba0910318100d103050f00b03640c0170003040000b0540d0021200032030038042000d058600c4450070800d00c1034107800c804504035810b1244450811012821200400a21340d000344130b4080701112454496046190040c000e500204030200240b1501c2d1452000384e84d4400c000007a68074031060076086901c2c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 481100251 1250 481099001 481099037
    0x120c1a070203100f0e0f0f2b0c17040801051605030106090e0406090506090703060f0515010c030309050f070611072103110a060203060f010e030c0118030209100f15 72
    0x480d030134100c548030000a80b44110401641d07064008102c05401040c544081c41450100c1c0705108032a403a014400426500d644100c41180f50a81420200b000c05c2082c6080b860500b000a100c00d1920004100032860700015800103106160102d42003908155807039041d10302d80802d120300070002e042a1018042d03000c4203150544c01c0761003041c000c1140a11a0398071410217000311441409a841008100103015850041000e141c91104e42040030b0700386400150714480c2e94042c03041c180828900f401d010944282e00410641c0d80080c03d640040d0f085090090b1115400d100714070000740840d030280103002c0081030342c0c0202d50009000f01b01c01088540340301031b142c03c0f15800b58248084154074644000c41130241c2d16680748688401666403819404000030600310011040c10440c50030001182c2e91800580d05071001000d0070041906000918042c80864071070304001d4029103040113001d140c0040c20503e90603503615860f91401e80f501c510849400040e4090b020f00061010b11400d205840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 481101501 1250 481100251 481100261
    0xc030c0f040c1e050a1202090117060607050703030509040b040e0a03140c0706020601031703280f0204090203060406060c05030306040c1e021e0c0901030209060307120c1a07020310 79
    0x34883c00c0001d4a8860280d00da803001410000c0100400c2000401c03c0c00203901621302e201b00f11040004504001e2000c4c0000d1141030411308156407140e030074010135425524401039501a6070300504450b20345880345402001c80d08440c40250055044c0b96111426142c47d0041144001c40d080060000210701e440c11543d01210500020022800b04075140c0f1190003403040501030030180d0000c2c00c065246242a170106504500c1300481c1d0a0240b09000c245040c1d4018989078154581003041c4000c01c031900c003c000c01049007000a200e01c002000609c201035900603502c500d408a07410440035960310b205807160f200800c401410b5410800004907280b030a51720843d061841c510b0003d851200301a001000310030a104001c1c0568000250034581e401c1c0c11003444004090322002d04100744e44100421070408040c08024400c9020320000f9a02c0d850401140e0018410941d03124070282590506410100450081303126529204d00d28820006000085620305a4064010001c1c20349040050000342 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 481102751 1250 481101501 481101521
    0xa0b0601090e190b090a0510050904260408010212010e06040e1e031e130618090e0c0319060609020a0813111504060e040b030a020105030903120103080304050c030c0f04 74
    0xd03031340c4401041e02d03107800400c5440382d80701d00700000701c0b410800c40e8030b0400740040d448144100d1a45080000059000300101002d241990140c5241e07a550076502d0100e005a03044882658404100925901c0c0c54404181c129405560301281545590040c442a5610342c01444481c0c1d010f0101d1750301d50000d211000659000c41020349041c00c4181001840180342168480e032800301c0031401441c425100d4155100400050600203080c40300d1310244129007070300788140034907950756035541105100c0074840b44007500d1000341525001c4d540700c21104040200542d0a13201b182c034091012540759114070880b00581015107034018039036902408081c1007400c00b402100c060200300031169060f03d8000741d0b42c0030792482100c03464540341090701c010091803800115511a609114810760151030200d103840f41e042c1c081c6441552541c6803a0b00c0e0f0b01c4c40c07003051765100311030100c10000000e0280880c05980200d02c41c85c10364602c04d00d0182016135907001080c045a00c050b10108120007440c19502c07041c00d81c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 481104001 1250 481102751 481102801
    0x90b0c1806030c09271503100f0e0d020303010f050f030c040929010f090c091205010603171804021303021c03020d0f120f02040b0c0a0b0601090e 64
    0x111180c04120190010383c1e0908620201240020480c40c040c80a04000000c406420a00300e030b05c01d52100d242c11001d001041c220106044d80e0450303850078171800c00d0103000304109015100d0441c00c3c8400800c0c00000d41aa41d00a0716010041c1510110403a4102d521a00715031002a05182c01c002e8442082a052507061085418100c080c0e1154041e00300d10b64010100c00e150b8882106000722a10000742c042003c1041075401400351620b45640282a80e00c0c030140024a11010307075003902d01d880c17590000040310490240035010880c0c1504100160b910071001d182e4078040d080180c800714014070b05401c500c40c0240034803110f2030034140d015241c3c249810381085c862076a40c0c0c01241b80c1da9510030340013000c1d0403405920014160100203244c200303202850804024248040002c059944c41030314043d64039101c0e0041030200c0420740580d8050810381401035900e581d201819079645c048051b0032154400400000780c410360007500c1c00022110094100c507500c0d6507005103c64001ea02503100c0c085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 481105251 1250 481104001 481104037
    0x8060d050c0918010903080f09030405011b1e08040603060b0a0c03030e210c01060506031b03060a030b070c03021608030f0c0102040306110408070503010b060904050711250801090b0c 80
    0x4012401d01880745d59500a0300c6840c580d091003020b8240b06d0720024005805a441004108103d0741d00222000e2050300c450030810041440e4549280404160030511040b001c1410100c0c09000c80c5100a104492040d1000c0220f00d50703c49901d0014050a190b01b40800d584e60114004607000f600b1408000846d107081e90b17100007808951801d40031481007c000c0442e00454161500c4000b4030505001d800101d0380c150552400d080581c6100c20754000080e1040400f0011504548504071100b000d190b004940b04550b01d0640d4005010745003801c41175005205018100e20710700e4405c0c242c1801d607000340015514006400e4685580e9034032480d045070b00e82d076081200001040c4d0390303c6050b031180200b144583ea110f1a00c0c1c80c042c0b5000c2c107904064480d1345091050a0103946450848a10303920a0b039000c2883d90390304d10292000e00180a2545150242d0030588004d11300740e80ca20001401459020340c00301c0d817a80d40040c02c070781400300e0080c04a14170718003180f0503889000c040d010985041e4900e0071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 481106501 1250 481105251 481105291
    0x25090305030d0c030e01020304020604031b050a12050c09010b0d09030212030c0408070801060f0e0405010b09070509010315120b060d050f0a1101031a09131b0608060d050c09 76
    0x11440d840340c04103103242d0b966207005090069050042d030324000e0301c1e02c2c000c1d170075420181c0000c0c1c1248624031000340315121782800e9400550701181d200005082c01060b14080c0e43d65000c0006000b0303020351080f02d80c3d00032401c04102600d0107001c0e1a0584d2800030615080c101c050400740020140d115054055120740b5484007005429170f80110710503007840c0c3c540c640b10752900c040760f480c1403c550000d0700540d0418034144170344c040b0f02e442d080c00c8075002404010f140d155800c08500404948644507081201d41c000c1002503034011008101a800c2079900b00041c40c00c912003248504800d014480d0b03001c0303100350b00002203150031441175000310000341140046403e50351040c2c034220500088a201c0d400040c11081440710802015803452000e09080c0882900080100c600156031700c0320502c52407110000c40c082200d00048a106658400030f803c0d00c0b60b58050041c1c80d00c99261040200003009a0005005030138155028040c1660180c0100205c24842c000c107c0c01c1140141101840300c00309034181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 481107751 1250 481106501 481106503
    0x7080a0f060f030c060815010320210c070213021b07030302010509010c050c1c09090e1b01020d0816050d05010915090c02190c1205100b030625090305 66
    0x1600a2000c1d101682c030a07440c40ca0416122100c940c4503400b40002542040f031070100101c21001c483d40c091a001903039540c2d007200c0c07400365150410809842c84000c142c0c07112136401e103603660030a440a840030003002d0341d520070300012500c210200250080300100180101e130889401070300318110010002c40004101a6200349040d0f1150701c02e60060303460303c0138003503044020310070340c2141e00d20b61070883e103810300085000740d542031803a2006452030844195091102d21809402010784515401401a0704119003840d686034454507440b9034076030000f16480410740c00094110346824007a01c80c401340d0740d0740301e80b075044168a18045505200b400c1180c40500b0000784911400303002c4545001038010703075010391400800c0d000d800c5100710368079002220101c9a00010701e52281c00b00c58441b0345440540d0314001900100329030000b940140c2c0c1c80480c004102002c030300361003042030060742000402000301c20580d4a40042e542c441541e44e514001e40340c5800c46030710503004004e15062512046590f940c801e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 481109001 1250 481107751 481107761
    0xa020603040305031023010507030915020d03110328020d091a0f0606180604050a0803030403021002120a0b1f021b01020313090915020301080c01080a0e0607080a0f 72
    0x2c40015000204020340341c0400710f9150060101100d458022001c0b0100c07485121400c05c0b00f60303042c00404908403041501c62000c0a000d0b060010204403c0d02c1440c10180d500e8500404200c046030030650050302c004041d2003503d100f02d03946004801c00b002103001002c03200b0154000460030316000c12000c000d9002c1030007003139032480c441d01051740749804a20002c0002003010341544141c400c40030034000c4c10f1b40c907901520f55040c044c10448007134028200002e9284d114079400103401642111001481c0384001c4055485107000381c00f60b80c2c0034003005440400302e01c11784a681e5450b0031040c0200c0e1800480f527022044102c4050300c42203400d101500000815100d400030240180d1106078000202c90191f2540459481d080c00114104151030601041103842c038000c801704142c0d20074115007441601520707075906000c0d6103011592542c4a000b40307500c9070044261785011407a10400300e9003c6166128010b40344408802411403030f02c601d101190030501c080c02c4038203900e40750022585580c00a00c56 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 481110251 1250 481109001 481109003
    0x601051c090b0a23060120062707080a08070201030b04020309210a09120c120809010206060a080c0f060c1002040806071b03050a260712020f07030c02030a02060304 72
    0x2030b4094904250000d050300e8511180d09080050100035000740002c075094580c01610908004441e0800301403c90b86d01013040581810350b2180c0c400b44880c1000d030500c5003c4206030382c40d605070030143c2c029501c0d80d906a184120941a80000e00c40304c00302c1c10703441c0540343d014414940440c003888403800103000d0742c00507140501700d6007000100d40d0581c14000d030b1070070107080751841d95404c002d10840054803802d5507120303a040d03050010140d9820804401600e0000d130840c00784505040303101c0d0070840340982140c0011805881268040341d568500f40f06072200700c800340002084503000b00000c1c810000c503000b0030150410300a0120035122070080c08407190601910360300581300e0f8644000c09240081c040c103030380c040c094102c98803400c49480c00e5820900c244c041c18065903d11102c20222820000c00403a180c0d20178100c003139008070007681c42603140949007640c2d81c1e20484c45105000400c074843c1219180c0074a0081144100007030061102e85044c030f00017800da61048a06030080f82e03c9900c1110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 481111501 1250 481110251 481110263
    0x1020606031533010e04110726160302160b0a1101060b18041808250b040b1603110a0c021801030f02180709030b06060706060807050112050f0601051c09 67
    0x34492003e507886245140840d1741120188190450fa1441094511071840b018054410b51484000c44c030303401680c3e01300700760300031200c26940304021848440b480751443c1040300140118070b0803415807070300030913004255500041200e140080c402e0040e20000030010105c0159503c4a0300080c0044a4030054074407a01400822100d410480c03013084202d0b40481140b5100281805202e804150030409450001d051640d281401c002c4541001403d6000c0c0413001b040d421021040204220019124501401c5401c010072a1180502019070984031500e5000103800f500384040b07000300d0b20600450001c1400500503441d2500b614290a0180790300740c009a800803e0f541991701103082c00c1c80008070010300484004024146450000c048898074800500f003104050041581540c601044035003096120034100314265403203404680f906098480c1074045082030704c02030300b003140d0360044601c00c004000c800d8016988030001540d003504030300030840d4120340380d8407100c242402d00c1c4030b41c40905000700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 481112751 1250 481111501 481111591
    0x318030c080c01080408041a0f041d0901090218060112090b06101809020d0e01050f090c191e0b0c06040c06030908030a1a0a060518010206060315 64
    0x94110301e4800344002e101c0c1000032440802022950500c280c4043da1203c001c604d079105050162100c45000e4000a0000c40038005400100581c40815a02c4003400c4081f22407a10354618402c1806c80d60f2201e400780d004001c00351100825690fa4501b1540041e05041c1f030f4082c040b035103100700e080346c96140d000c440c0c06080d04140300c40c91402400c40d1207800e000e460405101c2031b030006d05086d48002881801052900803030044500c17911070b04401d00d146081e40003044203107403a402c0030702d005034150b541e010140280d01440c60507041849008807003200c50420300302803e02d002d90100c045140f00640b142c04014000d400314031007070f4003c0148110000f450081065041c24100500301520740d5004005045c038040364007001440c01d07010780343e201e000c4000008619522802c9401c11008580c50180e01c070003641c42c0441d601d83c000d0041d043c034052042800c0f01c444098001aa5599026984a545680f0010b40d6000c0c0000c03a031403481d800076403145c8040c3c00703000c1c03044a10110b1702c8401c20112181080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 481114001 1250 481112751 481112759
    0x20c1203040606050a06021c020a02040905060a05010605041a1e131418160c0204020406120b19180905120301050108071e05070201020c031e060a0e0d0302070318030c 73
    0x2600448024000844005603914031b483d00180d942c001e003650044401c03407603003501d12000d40240000c650344e94000e0010300c501c200d81c0c034003035454076011610001f5203403a000010030b280d0b10800c10342c5c0c01d03030b19000c510103044495000c540380a80c10440105800c00840a4800703030405608000e41154520151036a4059003060643c00141040c212030074014020b402044064074254a000ca8010207810b269540170155403030100c401d01c0200ca8040d4205000050008806a200c450350002400b0b4413030030054000c0b00820003003201651400941280c0115201b072085003808050140c01d6150b01c4400a0000b03241d80d2020f0600141004c1000c20300c20100040259517004a00c20340e1101091400a45488210103004403401d50714220340b0801c9008110b030000c40e40200300c10303041d10800804403030818421006100f400707000c0c9048940107004d80c5006c030741001981e0050482103001d56020300340a10600004038000e400c04031065081240115070b104115184081036402703140103190440416040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 481115107 1106 481114001 481114013
    0x2101b080c0d1a310b0a121101200703031214010e060301060b070c1802070f2f0303220b0c0d09050d15090204020c120304 54
    0x2a0140310030520168101c0040c000804980719840c180c103c4d40f42c01100e8240303074100c0d030740111100c42c00d210856882c0c000d800070803070142200d984503175548000050280304403c10f813066100c040501c10256403017000c2e442459840c10884d40310301540c1c6080303a501d0f0f240307100150810502c0e03103070048413075130301d412440d00c1c040c65101045507540c582950b0420f0107400c3d034032a8401e600c1c0c10000240d90000d02d040d105020380000380d840f1f4203868544981000352900340c3c401445035007004404001a909001d980043d4050880e81014011070000e58a01c2200c0e0998034401040700103442c540c56030008111203440000030080032144041c6804400d40072155049280045030220b6000008100004c0320f5070341150640c2c038115000c0d52002440b00030310340c0100107010016500941451032880340c01004a8502c068030052a040500e46c69900b0800d08000d01804000d0000c180024020 = true := by decide +kernel

theorem cover : BRFrame.Cov 480935251 481115107 := by
  have h0 := BRFrame.cov_init 480935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 480935251 ≤ n) (h2 : n < 481115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
