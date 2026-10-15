-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4647
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:17:19.164144+00:00
-- url     : https://prove2.me/submissions/9156ee47-c732-40b6-a000-941c9974e4fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 835611510 ≤ n < 835791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 835612760 1250 835611510 835611533
    0x15060313050d05180a030b18030403020d11011b0b1504021902061e09030a08060111060f040b01290c150405060105120f071e090f090c060507030813 65
    0x98550b20503844102005500b00c801030601c1004040802034401a420a1010103510762100416052034900054000300305100002451109141034910b05aa80e400141c15251140025609002c030b400003910382c0c0d0f80101c804a882c00c8a500041d941c4d1400d40c654903c00840280400548284100c0004050303440354116208d888220070854260001808002c1d61088210340400c0b090804401c0c2d8008607900703041b032a200e104802d0040d0700d0706201034030850321040e001e0001410b00c533003141003000d040410f103d018070030000c0100c00c5046140608101d0700c025010b910042d450328100a900e0300c0040146002c220300b0481004540e80c41f61100050b41c5801c4000c1d0200c424440c03920140b1041010228100f030480d40200c42d40c09408000789169070300c81c5801c060f00c8800b80e002003001c0048000c0c3c1081c424012082540040c010b540c3c0d00d44010030b40d21480440c10703403141da03607480b00104402200224060019894174a080c140c0580e000b4110b020301500440e52080b1101030b01c0c00300805003850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 835614010 1250 835612760 835612763
    0x503150402160b0a110313030207241d0609010804020604090c050d0c0f170a23160509010207031103010e03160501050622020a11070f08060a020315060313 68
    0x21595030078a030010300b204400c0d40381c0456642c009a0045404282a13010313455540d000d080c04a8034607201c00452541c0000c51300c0c411000c0d07000d03a0800103041d062200e404134000d2200c010540c0c061a005e200100380e611b444400440035289000c0e1050b1680b51002507030940c0d6401e0922442c152198000900c460141d90b204080550903e1020b42c0800d80c001c000c1d00041200c0082881825494141038841d6070700041580002240d02e02c10300080c000301945190006231317007070002541005140803090008240c00070b005030401030605116004000380d020045104580c41c09908000014ac0000d403a04007610000e00091000060200541d900798480001702c00d00b102100c2e1b85248004400c110102d403208162215403a00002440f1742c00c2490406801e000402c011581d00c80032031000d64001d4200c1a005000c22141c0a06484207000c100000000b070302901c0328504250780b5020b074041c0340c000014101c0585500500602808411100a00c0440e8004840c000d850340da41140203003d0f000310820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 835615260 1250 835614010 835614019
    0xf100f2105030c0d0206131a1503060103110f010906020304090c020111031f090204300c0b040f061110090f1b0e0a1802010e01030e03120a0b150a050315 67
    0x1564002140b0014144c0e00c401c2640c1c00ba5079a0307545454466000740104107020300000342c0c401d10440001404079900f50300480046c1500b602a091001080c039100c802d8004540d6414100390b0200700c3d203000001c003407001c842480c1245420b82030100094503070207644203100800b620740b110440032500039000403244804048441e40c803071802c42030481405020b4001104001d0f51002c2c00300390400980222001c0c0c407802107035030701d8100c00c5c244500c1144452410901e40c2070b688126050010b90502040001000d007205903079110741c00c1102000e0802c18651151003400914105d040400102041c280000c511001c0d0005540456083c49568407121800c02068902ca09106aa44010207285001075814422031060305a459608201c101c1d201001c0f50a80541441000340041d0310480081c1107602c03040c03401003019480a042c5501e950040740c40d0303000401c03640f4208a400c0d0703058843c01c3e4158004803440d15000020fa03940e18458070902d19040f00300140000014091040c1c1544180a03240180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 835616510 1250 835615260 835615267
    0x50610031109120c3c0105040905040f030327170f040806092139010914070e010b030a02090915090f060109050d0203070b0703080f100f210503 63
    0xc80681d2608445813415201d8805581201c0c40d40d68095039585090070113030140041d94010015a0784c21a004044031410058200004a813001d42405614000c5204881d503401c4407141d03140280a841540202c124aa00001e44c3d14521007084401105c031950030803030381c2d518a00c0d0100b0101c2135110301108031040020006e00058004c0c40056260300c90840c40d419240b0504442c030315522200c0310403007102c40491090003c403220969018100408a06c281130740c060300344c0540490b400208030100c40c95a1659900c140100744001c0100003005460804090400a401d000a0b40107280041c0102411400d01200150608d0102d0b81180c0d00d50074010002c01942c6001b8800503170610000707043c80d0084a40002050a40301c641000d240910416124050800d0500702030010b8140503c0086c0d9261180c40700c00600046114001c202c9603000382d44001c9680b900d00303003007011880c005c1d211040745030500008002c0400700304001010790b040f94000403841d6803e4800302c1d6131040840e80141c503e01000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 835617760 1250 835616510 835616539
    0xc030105040c0608010b070c18090c180b040203060607080a030b1905042924070809030607110309060d0b0a080d0e09060a030204021c0906060509010801050610031109 73
    0x2040c1c1d000c00c5802c0f41d07a4400c1d460381c075100c01850324011280020290701e0714820521030030301c4124520141e62007042c00001c5400c100c0d22281780f030b8075499110410b41244021020005002070180303000030384085e103080d45907042050114881d886003101c00340c144c400c0810546000381c4a40c100180208005140107418503801210035800380081c49440d110302e01d400d18034401c03840100d2811048100e55841410010030380404d00404429280c03098080012414000000103200b902808490340150f07826071f140c81c204020b062504102425890034011b1400e004001c450300001121040103054445079150a0206002c801520b200454142c0c050200640480c1945002801c031802c601c442c3c2c0c8943c0c4204011040c00240c60003600c009401540008080c00582881d4004001c002001000c0702800200c10484d502100c01c01401145d4954035070f00100003518004803100c0c0901281e100820490814400280c1002094040582415120250005500c00800c299024044040c02800c8034030990f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 835619010 1250 835617760 835617773
    0x40c1806020c1f1e0207080640110a0510020a020f04090809100e150910030218090721020405090c031b0d060302130507030c0e0a03020f030c03010504 66
    0x71039042c54002ca00c0d107064080c0a00416070a0100d6110684802c46030719481c400c80c05444c84601d100d41d05501c1010400542c40408002e1180318000388075040c0d585042c6032441c91342098007007420702810341d0488003064181119200003000c00307a100d6a04030f240c02142c0b01150180d4055807000d5409884180f0300d036030213a004150400510700c01c450079445014081c080008070340000710090440c00e0103200408090414020001c0b8403180b9082089180514000184031915041071001ca038150101d00310240342042255112a1000b5041c01e50625410011030301d0506a6004242d1080080c100461241c50203031003e038001000d1410180302005280b001c40c80a50300c0340c820f5a0007440e025000402040f40481624002d01c403c1419041ca112a00348850743c40d0882041002c0943c0c1d41d110010041c0c0c1c80f031302c031340b244c1d40440b0101203014074207880043c0c11960304810460512074501408403007956515034401c1070300da0446502e804d008000c40445d1410b81294401a0550300c1c110912051101c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 835620260 1250 835619010 835619023
    0x18110301030f0611033102030706050d14130206071b0b1e190c0606050907030516020a020a092007140f0109080304060908071704090f0b030c040c180602 67
    0x40c0c1d80c02e2000d0780800c0c0f20100b41d07102c2140d200c1c000120044000e240b001500541b0b55854805101c2c9102d020204c1c1c000a0825145902580100380002030038001039545005121500c010004000e11503d04000b80340188500e0903c020b100d00c0000899004001488070603803080b111030185000c02070784480020705540d004140c0150440e440c010130705490080041292012a1a42c1c2d1080c121000c2c41010b6451004400c0221380035510740c50081026218403464510441c415500030030541000c0d03012000b0300031851412011504501010800760301c6a09415045650030000044e0706400c108010313400f01a080d140341e91b400e50025006080c041c1d411082000800050144c6203032a0030854082d080b500c00401c010082c0c00c007400000d01141c4141d12240100c0c1c040d4529030703d40820380d40d0f1068010401c041546a06402041c10302490000780f00c1c45030120307150342c0200f0410280d81c0003c8d0340c44102001e414425130311002d08041c1c040c8607400303040c4510003840256a4064035000060b4403000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 835621510 1250 835620260 835620263
    0xc0d0219090c0e030309180915090627060606032a070501060819063201140607020904080a090b0f0405041a21032a2518110301030f 58
    0x4034a40300f12061460080220f0740ea8400003040703030f8400030a424a8852000006001410307500810006079211300c041580c82d8800d01c41c600c080c000f2458131401000c501405030140403c030b038400c414005001c0fa33001500680142e4116120760300d956405144050b40c240c3c180b0701d000380c40c008504000301c503048840500006441400240038a07a10b914903180c0d01e4010788108902451140d043c240820510713404050011520007151100400e4891805003810001c5114244082190010450501b6102003000040303070842d585447c029181d0002600340401501c0940300c5840002d0400d8203602882d407001c002c08100c8082601c45800300b844a4264225109950050742090286c1c00e41c01c030420000c0e006020020202d01d03818100c440c814450b442000b203c12a188000c10800f4130510420000383c0f42200400000e003201000b5035185400c050394000c0303034000b802c50600e044003c15412004c2e50241c0d03501d03211907820b6141e5107404801401c018070800000100010011040c0002c107080600500e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 835622760 1250 835621510 835621517
    0x504022d0a060e0a0e06060f0705240a0c020c010f1d0a29070c120309170c040605040e150c0702060715150b0d020a051c06030b1005030c0d0219090c 65
    0x8a503245040100800c0840d42280c0c040c1080000588208982c0d0246c88018041d2045890051111a051041d64501504bc3ca10350707901104100a0250303d0241c514040300c2880501460381c10740c00043c00c16101d40450744148480b06214900c00c00648504100f80c9000904c1002400d03a03a01c1503450700c8035403401140c07000307146107030294070041c01324100c078012070b070280701ca9803524175003181c20b103400086400450030081240f00001d16125140d6010021104440c0030300701f10018030b4100002c4903420360020340914100311000301c50080c040b6440e042240701205480c07083c0d0307400140b5411381c4200ca0000b9844000031038207a00388002140100081440d50b8410800c071b01b00ca01241d480da40c80c0d481010400c040c100812045a8550b801800054106050043c1407170a019074102811003d00010818540c0e6108104240041c180d0712607000000500405851030030b200110761188202c00c2014011241407040340210344903143c121400d40d04004268514945520340c01010700074500040001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 835624010 1250 835622760 835622779
    0xf050709060804050c0d110405010f0609091505090402030a051c032d0c0903050f0a0209060105040e06060306060f0703091403033c03070509090a0504022d0a060e 71
    0x1800b40301403a019542002c010024071034128100500310640034070850f030301c8140e441c45140503165405511701074400b042411409a040c0030004041c1d820311750008a106081c0010103020403415500402510b100341c03000b1b50103588038001700746800c91201c0000c143e403044000e0b01d0407401c040410020503450998080c0007581c0300c51180e00540360b03085244e214140f00c900b44c2c1005030480c1e0348500b00140d201c3c10090312259807600c0c0c0d941420040e56011301250004420f02d400c524042002582c880400d0074010b04040c00c100c8500c03c4d209004049a000b040000086103040c0d45240a8411040c45e110301740b43d40c0c1020780341c01071465040b4420b10b041f08035002000e04041c40d010090303814900701110781c0100000e03409100d42c0302c503020f0042d9036404070000308003410b0221031000451041c10140c490710f40d034641250a00000d80401050800e805140005210060340ca01d0b0703146d0300c103203803491201d80b40103030f600e540d00203085104d440b56600100220000894035003201c00000c0303190341226011a0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 835625260 1250 835624010 835624019
    0xd0c090f020306010e0f040e0d0207030b0f01120b0402040b0d12090b16060b1807090602060705040608070e0f0909010b01080c09010807120e0312040210231c0f050709 73
    0x268002a83c8660209045244805290400021683e03801030010310200d0314000e411161800c20030780740140d500580024005100b4460800c0c06039410000d403084018803585003c40d4000c000762071101c0101402050804070741507580d02c1c2c0001c4195000105200c1c0c10201c5032902c000b000d1507600504011404071711000074043c03003490654151003003440000100004541d240300040c012951582e074010701800c00c8211640000110340e10401064460481701030820601900e0454028044c40030440e080106010080e44028200d0b00076031542002240d550301c0300f0025054241900082e074008210301c1c10000c0000d01500a0074440c0800e8849046a8541c6c0440403082d103d4400c51a004c40c0480000c1840d45104107811050001c1034500020440300c1402c04c64215803144204a0101c1d034803505000951801c02d20395000c0c10110704064840c0c6070301c25207892582091403103c1b5480400802c4202059811200e408840d501900041010080c0c41b60520024032007a903502000900b060b50204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 835626510 1250 835625260 835625291
    0x3070203270310051b070f170c1905031b03070212100c03060b12070215010603140a090308010b13050909010f0e070305120a0516050a02031002360d0c09 67
    0x45c0148031340030302c011200581030182c91300760340004803c4030364044640c01c0c000880c034181c4035012042104a40e46039a5110076038034500d0445868401005030b1402403201001820000c112428103600103101600290000d087c0381c00c40c012000065041046003044c0140c018012810340f0f65404c076075000f08181140f4400c1101110300340d005404000c20204000c5043d2511540d201b940700c1040c0c8111401070103810043d0000e00c0080c1d01401c0400e0b00d07400700c072201e40c00d00c02000e50b101c1003c0004000450301c940b801881030b801072103081c00041c00054494480d50743c80803e50081c08018020400b039090036480c8030300801d81800da01c2941d1345030a4858000c800080b40200c226a0080c0007030000d48100c044880700d56000740340040504c90201706000c5410382c2b0350011030300035014002502c0498803500505007400f00c804100501c80d4030421050400c080ca2040c5021001c411100548103d001b41e0402d003440e41074040c5032907204200e80c0300785c0b0070802500701003020b81d0b00bc10020300c02c5001111044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 835627760 1250 835626510 835626521
    0x403110102040506040b3f0105180a1d01090c0503060108030a140d0612150e2d030d1104150503040b2a0a030b010207120507030803070203270310 64
    0x10fa40c810020402001407580c0d14020341420b817064041700407038099006032a100100d50a08020040030711900170817460700d08410041c010701080d2403a11100e80700200045500000610b44045543d0300d044042030000c1018040c182d00705800004c008418840c00c01c0b000600d44ca1141c0c1d0301c00c0c41000008180d0000c04000d90700361a9064480306008100c0000c159080e400001820450790741d0b0303040019622068250b0b0341e481e40e014130484210202c1c1c10000718243e84d01c40030510100d90001456094004540200c4074440700c1081e401600c80c140c90210b2070451044010458942e404c3c04040c03190400350030b000b802140c10a034041000748818500a40791800202c50281c6a0311032030000a582c07040c454032099416040e00c0c000c8a00306070201c10546150414a401c0c40065507502c50303c40c0b50750b010000500070b00700140040f00780100790741c1d0b5a5502c1c442c500004113031071400300110301562700070400d88d16a1a45407581680c15030441c200d036144001c0d0f01c0d15a40c441d119250031b80700c00c81543d1051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 835629010 1250 835627760 835627769
    0xf0c0e040b031914011104031203050f1005061818010608010608160f0c02040504061e05060d0303020901121e0f021e2118011d0c0904030c050312040311010204 70
    0x10600050103500c135900c01c9500035003041e02954070307201c504010040701e00040024504c10f180d190741007100c070200182181c00c010a4031188280749000d0000506044110070201d40d41241c110744ea800160b030b50100d07440d01410740540c0291000c190000494140081036058412036540d8010b03580c1e0f07909044a40c40c4060381d6807041c88040340e00a0074400c0c40380340050002071080c140b0070002d00b2070364041003c4550884d002c0d2a00c42d520500072042034800a051014461002424081740c24030388009481ca8490078401018540e0001720007849034080c0003401100400203108002c400c2081001850516021040030300c0d023450310340c02101480580c801e940c036041c4a0aa1040808603155a044c52070340840e0101300701da00a020001c90782d8051481152103a024030900c640507005090b2250700751250503800d13011145258644212071100003825101c10482140c800c551354441d81015103c081c02c80030b019086000011b45d1140e000206140b00d0b0007544284c0e90740b9440150216200d00300d000324050f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 835630260 1250 835629010 835629043
    0xf0b0627070e010908030c0c0306091f0506041b0e0f0901060f0f050c100e010c02070333020403050a0507210f06060801150f150917010f0c0e040b03 65
    0x1041d032031441241c00b03002202c4181441c0e18100e8407050700c1072454000290742149980036801758034030707402d0500840340c02c0000390004101c49214180c01c031a82e020100348140c0345540c1c1c3c10024070a95680d80000140b400c000c00d040b07140c0c40d004103008001c984500ba4503402401d20300300fa0b84885c10700744ca25904a800603629071014000c107200445e814448203903c002080700c1485002c2c0b01c40e90910442c405c400035004e001400c8200c11a034a802d40f61494101c40a43d08404402c00c04078082a07042c4d5401c40d19a012502011324041440580085020b0000100c51010a020040080006560440354000d0080740e01840c0d840b00c60043c540f5020340c02100d80721182c007019002500d4988000b01d82441546c0c046003c0d6241c51429003150880042c86240060b000000c00003603440c0c000c500d02515002e48041d038542c2061340c0c003400926442c2700706207110b10603001a050103642075002554050f001c2005119000c41031500a094401d01c514241c0f01d1841c00d0341c0c82c0e80c580790008400c0c2c001d114440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 835631510 1250 835630260 835630339
    0x10504140a1d0717100510021f0b0307050406031101081b030412180501091406090909030417071203050d021909080f0613020f190602010501061b031d030a0f0b06 71
    0x4184101250f200704000c7c21f610420b0120320401d1400f50804c0300d4004aa64005240100c0c001090719210f0182c0c41a4051481e102d000e0000c140c200100344002d01080c202082951184031201d15216180d15105510f10400310500c800c10030b80f500e0b450300902d030503a15403c0d02c61a5407001c1090b0b484620070b403808030b000c04104101da16101a105608008010905810034002002040844a0844108100d5000001c00740b1590300424000d02802d0220001414118109402000e00300e020700c5015092201c00700300398610710403580440e80c0a152240103680194003400c0080c11030180d5005200d561300441260825100002400300e1088900c02c11a40c0d19011035028491003083d41031115400551201003640c81140c00f08000d8010035596000103030a615048004182c00201c0b00c680804251504c00800425803044024010518031003490000004a0001038501281000300811001c40c8503004020b010040e4070b058800c0c881600c01a803d1204d6817a404604003e02c2d4881c0078101c20351 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 835632760 1250 835631510 835631519
    0x1418040e0d090e1009021204030f050a301b111207170c0d020312150108040b0c041211100201090222061205010c0905010e010504140a1d071710 63
    0xd08400c1e4018422510401c49941c45d0019002a80d0080064034283c0304040c0c240420940d100c074030351074014907e2420504210002c0c0e00140032414801c0050413002030384900500b03050721940030281c00107064200300080f140e42c0f1030030401841e041841c01c012904e02c40c2207410240c80820300c201d4032610000c1c0e603442d009181da558610303514202083c0320745400612002d420314008019860450389280c00541d22401c062644040d209401400394039288a240e0044000781d0b006480300c0d4102e0351248044400d984c44101c0070300c10740900e9009029211030000d204082c0285031584007088401540c404075a60300c003500a0b800c2e1900000001d40001d50307040b600810070b00b445403d90000710140301c04180c407030740c5400d0b80700140707040f09007561541d56400e1640b00c41e0703400042140c0140020700300341403a6600000068001e000364414603d519640e4580309c1040c0d0f40700c420040207403800404044415585040f20300d600241200c102d00821f207800f01b0b02d010310707626203c101d01c68041c0d00700361000d01c4e042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 835634010 1250 835632760 835632779
    0x412031b06051e0114041806150e060d0f030809160b070c1e05010507140a0303051e01140d030e09072304050f0f010c0c0b0c100203090303040f031418040e0d09 70
    0x115800030381092003031f100320000542140207000c203007030070241b82c560b01c103050000c0c010140c0f101818007446080011000360000b81403c2480252540500f2300d03140685d10560103e08144030380300095841a003111003c200c01041300c02412402d4000c41d16600f40940310441401030501e9420030180c03102441d141004250300c1035008150b014481c2c0031480000d858020550320700a0003442c2100880c0d00c0e103080114070740b4154801d030f40809102c0c8e660007040d40340499508220058440060150280666203824540602d25035020640090807143c15031411100083c55240320610000d5541c140140e05007040082070240c40c240c843c01060782032003c141100300701d200d001c0c80c0003290611000609110100310601720103c0104071507504641c2d151403840b003030307030802960304d4509020601c1802400b111920000c02d40f6401503025000e5260000300d410309555030040c01101100d8000c000904202040c406400c0201c1c107041034405122030703080d64188548508107410024000380c4501c2c400c1007000305d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 835635260 1250 835634010 835634021
    0x5010e0304081005090a081308031603120b09070e0607020306011202010f020718050a06170c0f0a030b0c072303040603050f0c0a0f09170c09100305030412031b06051e011404 76
    0xc0c0726940c8541540d64444034156044002d0034110f84159000d0bc10500d030f0010082c0c0b4151300078101c07c00010b171000002500c03481010b07104504104186030f00303c03610384800e41103c5900d9002000c030f40d182c2d0b80d208a44260f07124001022400658010390b11030145000103170450a65040c1254443ea560015514100400000b0708201c0d280d13440d10000502080814507443c210f00301e45014040d94610703001448408108034a04500501913201d003000854130b0491080d4000143c200798513aa004a810401c0116041c113502040c20541e40c5250f00f15010004018811a615600c051000c0ea5a00c886246844000c8418408000d810400070300403034811040b43e0078642c00303414030300403068584003014640300840032400b0643d4130a1a03481c04900c0c1910b41d072580260482d21f0110468119a201e03500c0e8003c500c900d0000340c641d80c0320ba804150042c0c064210050722040001111078550410f20050b040075146003d030a2007034520041d46003d500b00075416140103c0c80d00c0103074103651041c40010031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 835636510 1250 835635260 835635277
    0xa081207110d0f0f0312050412020f030a05040504090501110f1201060e06030c0904060f081f06060203090d0c1d2401021b030f06160801080a171605010e0304081005090a08 75
    0x32100c11b5418500e01c25104a90166024404610710706507007820103490729100f1342450700790794070900a02401503403003400c89043d0340d000c2c1c1c0c02003845801440d0a50141c400840038030078103000852a085200102c0c009030840c4201ca41503280c1c00d0361b940c003003a0798055904c8101307508007004200003016004001c0092080343c90107407000480c10354030030500c00c0003002134100481d00e4120319007040c1100e044180d0b5180c0c1905a003010820540b0b02400070b03542e0f214600b80725000d800036602180030b002c6003004080042041409014919100307106c11000000100c82d044080e1910300c2c101400d8241803000b40d20403420680082c26440c40d500354842e440340415030a2545480b0340104a040020144402c5001c3c0394505009079050801d01c102a0101e071058120003820361000101c0301c0410007040500051622030f100260f0740d42c00e1000b4508400210b0385003c1c0403503080c07113031412070040000014811103800ca4113403000f9041c007651a8064500594855150780d11030409080499005001002d50301c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 835637760 1250 835636510 835636517
    0xc060601022a01030911090c0c0c09092116050d091d06041512050708150403020a030e040207081303060b0103060f0e0c09030f011e09050d0c020a081207110d0f0f03 72
    0x981a0070008031f116a00711413081c00508081006c24041c07a042142c12000e20045400038283e00e0200070941c1c1d0340b19100b2440100c400c440502a0b180d42c00c0c0e50490740d0b07011024120070314022007400d040d03030fa0f0350f08600c0c2c500004828220005400a41c0c01e9250a010595904548151100400c06c00036000003020040c409040010020303020b441c5440d0100d40794401c001a007195880c2c403080034240342d4622009904004880704000000e6404140c25190030b0341130920210020b00100032800070b0140c40d0005210640010344441d0a50900d00d4100440744241e005109002814004500f540c03600e1042122010b4071110074082255205201c5e030b03001a0400b6030320705048084001900d0300b25100701c403080c10f940da158552144041500c40c0c0800054204003030118808079511903030381700705002c6040100642c0303200314411980d80c020000014801c220803900043c0b6023882c03a52445c0e1002908071044001203000c0c01407420603d440118554100301a80b81c80000d40e02c0710003950460b80411400c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 835639010 1250 835637760 835637783
    0xe0a11060d230a1e0c140403051f0b18061926010c0507240204090c021c020a080313020a03061406041b0e13020c060601022a010309 58
    0x8a40700c41c40b0b00400381c1c40018071061400440c201012440001624010700c0e0340c10710310711005003450781251991000d07141100007800c0000100031a5402c5001038035003401c11001400206110000650320107102a0007207824416812011031806c0f0b40071584029003088a56445404107100340c80103e5010364040d1131030180b0301003401010009075198100c0002080303003106c4000c1400e000035101038542c00100c0204144413500038040d08600504000405165041c2c46200150080004a10314000400c800750740b41d0340c0350342d01240580360102c0800d006218100304407404603d5488003180341e80ca69005440c07205103c0e1030310345071684003d1a04107940064030a0500517220148164015400f40b80e001440080c5002024806a0041c001c54810341c10021000007170292400b20003100032a90034242d01c00d403402004100c0c0d0301c7c0fa00f080c0b9501c081c800300b0f517600164400301d54036105440990980c1c2c0d02c0c030361444074400240903c1d90b101403121001c45140742d295020b940700b0304140e1b004a041040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 835640260 1250 835639010 835639027
    0xb011b050c0301090302010c09060201020f1c020904050406050a180b070f05161101030b0609030d1d0a0323030708180103020d050a090b09010915050c0c060c0c100e0a1106 75
    0x2944c2002c04100d0040c2c0d991a249006070b90b101c00058042c001901c02985446e030040d034848002c2c0144420b0541100701c80c0c1d8a244030700d0143e4111402581c01500510884c5001c2c24800010a000c0312030110850030240e64410581200c644641401e03840102c40200da02c80590444850384204680c200340b2104000b03400300741c10051110307400c2c40c0c032440209101001800006003582d00d40c401543c00360000b408034100380e40e130208004800081501d8600d0f0055260f880c1164000d04030410540c014071021004400e02c0803c10b06943d000d195503480a28001c44562410303600c1c8240c0b20080c066080520902440d100411003912040e00145000360519100342c0c0260121482aa281000e00f5654001c400130010016505071340004540001c210110468482000e152490f480c24070400e0340d81ca000588000700c00007030300c0702c1d0300700041140d850389420700300c0c5001070340117206440b501e00c03401d00c02000c1604a40a80c243c074040d804003800410541e9503270320244076140d140803940840d06001848 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 835641510 1250 835640260 835640263
    0x40c0524071b0f030515190507120e010605091503060711150c120a0218062208030301060e0d0c0e070c150f0b0d03230408060109021c0b011b050c03 65
    0xc0d00b0f060410102c00ca241d460003d01d820f030505a00403078055500204031151b0300309851501d150054103c00302e62070f0358003e000c0f1504a03070101401a140d00d041c0d048054040150700000580e041507800c811241c5948a00c0c015056411920961691107030000404440c03183d0281241ca1040c24101e441140801d06003528402086824589800000c50182d051003100780b526504400d104400314078003200201000300550003009050700441d00090020201040d05250048504580c1040c03030f240ca0301d270350b1583d4880d8020f2003a1000143e11001006903442e1000d8008003076030388689000708480c940040780c16a040000e04038400c0c807050180c00d501281d038210b0119174126059500103100000782100200721054452820f0060110b60203e90000e0b0b002000c0c0c0b0404500d0901180303000c0f1041241c81039520a0340c00941e01409800c0002880e00c019030050003c40400b07029010707880c4800e040f50360480b480100150b0003d03006088100e001d40c0342c6c990075a0414000d006441c404040900400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 835642760 1250 835641510 835641563
    0x403110d0f120804021c0507061b02060c0c01020709051e0403020c0904061d1b010e03161d0906150906030304050d050609010507020303070207150e0315040c052407 72
    0xc8001c5100203081200b10b140c1a1401c0d0b407106c4000002900b00085500e410342d0740c4080e03008050511000d030b40d851980c21071007950305046550061030903681340b45061415840b06106201180548100c180c0030440988038007a15200d256544d02c207110728102c0400d030304580c4802034815002e500880482200e02d80b0b800a010344514003444012904851441003c440c0721311206170450140c1025000115460119200c2e0011340f030300f4039104080c6058940041e0402665521582d00c445400c400060040a44207100010003c0b0720781254481da03681c00800c0e1104000c030380307215252240c0e01c0240214500f504559802034000360407039003815101e802082000d40b01c1c06090721a42e01002c100503215400b400b406910414a2001d14154100180d0103580d0305200e0140000541d005100465007522898400482c003500800b2104002d1a08245000440050340e081d1400c040c1610302241c1c0c0e041613010260f090b03006050995035955103249030f0041d900008001c0f5202c0100c1c55070217000004147c0c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 835644010 1250 835642760 835642793
    0x1b0d0b0a0909110108181507171603060b0703121e1a0f0103060f1a120f09120903030702060304021c080d051311042307020a03090b0403110d0f 63
    0xd500340010000c001500343c010041c40d540c80320039180a42c20000348042800c0e41d14001c0a86c08240c01d48238084240c0382c480c2116190f1184c1040362341041484800c0710f074601401101503d08000407a2202001800c61042220180215807104603284000045a214011343e00510a0001115100212540644849070307031090386401c200780c00551501d015003000c10064424202040100d2409540c800a00c18034416a00d0b4800d8000c046201282d240c42103803110107040f012010300e0b1134a954002c09442d001d4a000146201f001c1010036010540021100b8100c4020011810800c2c598204012035200400132078001e003800c80c04010307241d010522a070000340308100e903c0d1151005074642013161001084200445065401800450030343c0d2120000c1210964003c104031042c10416911106030042490b0356000c6902000b401ca5400301c1e040001d0392007a641c640a50350781c2c030150400c601072030001900208000c83d064500c1e00c0c11a0000790102e1061000d0900e90034a03890381a03400b503500c4107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 835645260 1250 835644010 835644023
    0x3010f0b01030b0a050a0302060a020f0a0b012408060d020a0320130b0907050d0209151e09060406180902040e10080d0e10021f141b0d0b0a0909 63
    0x91031540d5038060140854011041e260100c00e0303032400000403409001488007900035900040e104100d0b81c401d211074030000d400c8900716a0b01d50403500c0d2140901809100e2000c07400f00d040758009108284101c00580102d8581e05c00c100b548644040001303901c014902260b0000070300b03400000180104c0c40d5101e1180098195100d5491501c0622241491248840c04030624003c1402501c0d40c0b920b50310341c0c001100c0e1403d1611101d5200004001f48685400f296004659012140e0791103040001004c03a4581800e031058129494000c810303180c02032001d8258070850501050200d50303c00c4892600700c1b060b4030404602d0390f94510680c0207c4c0c2c850781250050321041c03401c00c403071130003280c40150060030341d90002d02c0304220b403000040112040c680950b1242c40014803050b149031003000060302c3c2041c1800c0302c0944107401d803104e9004042801000703110303585000c0000c0030b20b101542510140415901032614003c61005c02200a01400c0c0380c10383e101d400c80e1030214a0001c54820105894071980 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 835646510 1250 835645260 835645271
    0x61e030c15030a060f120b13150608010b120a02090c070c080705041505010c0308151011010e0a050304060c060f06090e0609160e04020a09050f07031a151803010f 71
    0x300040b013501c060707800c556000160b094042040c102c003000d0f0340ea40305401ca402c4030401d85803440422005001c80b98040d16880200d500b440340131981d6031000c0e0454901074000c010000c0304c20240101c140c44841c5841c140d4200e1140d810150800b030340c071242d01043c060311441c5401141e541d0100000d1841c0c00200555010070010300c9141458807a502c40d280500c10310308801460580001d080955503103008041098050118020a19010514a6590300200030200d40c10340400300130603508280d94820920f6092201c0d0b400b0154010808a203035036088005946480e080c04000d56035020740c200d045541c980d031945240c0d2800a54403e100c003600820102150034600104111318000c405003000300c0039041081740b0b0030704248001c0550129035070030713000c4c240c650388600006451a041c1d0348030800e00e90900c2d003000450809054410304c80c4000340c904000030b250144281c16503d40500915811801c4e03480c5400800b51b0001c05007601100c0000020b0307580303034a10b01203030940301145e00310494141c80e079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 835647760 1250 835646510 835646521
    0x1b05070e0912180402070201031518050f13020118030b010e040212011401050d06090b011e060203040e06120c030d08100603090f021014031302010314061e030c1503 72
    0x60040b40c220000c48102c150404141d8582500420110042c041c46642d0024080f411a40260400c5171040c10307090000c03519903a1144c2200076012203d2802c00011318000010f03500280c020b03981401071010010060403031ba020360040d214024131122024800031904000000107140401e01e90203002d610586803880c4c00c10348140b00507a00318141803011070341460300001c210001064064111030301100c1099a0328810305100b00180a0420003030004088403002054145485442c3c41740003466918800000d0381c6e0344000c036120f0141d40900e50001103514049406854a8000941c4108100c0700342c809949050700040d141c65000082e20007c0790051080119002004480740002c00c407608007440381d18208d80c0c9032030a04500860091160003103d10704100d4902c07407540c0040a41d81c1c420b50655905214608502c4500080c4080340041c2c1044000700e5500844605107000c2c180c0a042d00080202000158400c0d002c080130340c80d054440c9107608071550380d0300e0440c00ba90138461802c807a03690405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 835649010 1250 835647760 835647763
    0x17010b0a03050c07021f030908040801060501020f0316021e0d0f150603080f2d0c060a060b0702240a0503010905010b070807030302031b0a0807200a031b05070e09 71
    0x9101048481c414006540036031038001c80c64103d43d01008100a804503202404d500620008c00e0140c0b10440202d00440d1403d815401902604e400740c0868500c4021031014580d24070420a420201c86514103018006007802c02a06028080d1050040c8107100c188001c10070401c0c0720a0103a0740b1000c1e0b1142803050008004000040818001c000d000690854481d070000d071103000c001210b448000510708048000250503600703252003c14171003c0c1441814000c5500d50006043d40b030030340c06410302140321510b00703104400849080c0b640460074107443c0c0e020411070044403c21019084604214050101014002841c50600c1c1c0d4a45980725410240c203101100c40580011901c0d203001c0103c0e9011500110a881c4103540c180b8016a90350b5801045058446d2680c0344501d992002144500c005a086003c0c60722629480d51404141e10340c0c130b04218442c4010445481d1543c20000740b040100340700e001807803c17980c40e910074000454000d41e180da240080030391020012800c0c000502644150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 835650260 1250 835649010 835649021
    0x1b0a02011101150b0702040b0a06080f15011e0309121d0607020f121504060c0215100b070203120304050f0d0509010206010509071110150501030603120e0117010b0a03 73
    0x1440300c02082280c1c1043d0f00c0c031503010040d0088081032140400c000045581f41c2c3c100c18803441d0060074000600f0303035829001c2c00c19041610709414003c03082c0c3c001550b01070700e084000345120050b90f40464400c4115040c80c00e034601c1496000405071950721040c04951810800007030000700741e0b15020304007040300c44031180340d5400c1d03034440c0320324800c01170600503a4078401f120740c02c16011625035a04003a540790352460031550450805d10400c20104000c144201a0700501941d0040d4094900c12466080440a010300c11140301307001013100c0806000d540380e2400a011028400f81c1110391000c501404207107a41c00407070f0110b032141d000d41c00e40000c40c04140314517400b10082e81000390400030103200103516114140209406200c028000a092605c00d4007000029900e12095540c02d65403405030328040c004c05140f071049229106000a4254800e1041c0703002c498101410b5940c4482455080341d0414400c0903545c10803200d1301c0c0030042d0403204800c441c0280003c603101542c550000c03001905560 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 835651510 1250 835650260 835650287
    0x150d14070f0f03200306130f050f01050136050a0b13080303010b040e04021804300207230307060302030a0f0b1c0524091603081b01021b0a0201 63
    0x41c1003402d4400003000d443d44c04106500400380080e141c0e5a03880c08600850005d10b00c141c0a50b0030007002c01c2d80b0503100e500080c0244542001c1c40820f81c0c071200199021213038981d845810081880c41011340820070001904443c4400a180211a941c1c1c40000c4e403034191500700b448560300015500c102c0c0318448001900601040c4050341c1158944100c05a00e1b01461194a0101680c900040c08540d24000e40d40780c440741c440b60352050350515051500c02c0790030001c020358030f500c2c08407440103220030f80c008840208510b940c02015042d0401c5100400d1516150038000c1d01414484601039555040c40307200080d000c00c0d5001038981c03030402150401c0d00c50440b103c0b20704500d05110360a10352100c6690752034a034015403144a6042903031900c3c0d80b40082a881104035410249044400044008105400362aa800c22140c0c108103501a4403030b1440240700041070702100308522a0310107403104140f102001c94178001828601005040074040c20080c100900580001c00400304541c2c000801081c4c51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 835652760 1250 835651510 835651517
    0x80d090906210821041b05010206130f11120303100b07030c020103090228090501210318030b01180e0c060301060c1e08091e150d14070f0f 61
    0x3141d00c41140d40d0142c00801029108482c002001081580024039407000d00070000350303000d194a0701d41031a160301c181088143c250202032080004840d8400991640940070b007185080c0d0b40303080d6989000610741b14000840f106440004120456581c0030388d400303c8004441c0c0615502c1c0b51400d82c1c8014500b036900a42060541400901c0120342d010b00510600c6a0a0030300003000101800000c84034061440d070108005000ea0081c04400d0000201104940c040c52041c425030f42c03078a80c40760325400d00340c185003000c0106004041c0864130a80d01080c50b4620503441550480d2651161503451000341c0100e100c844c4845001111010648150700070400301c0c1002e485882c0301c0c80300180303083c4010b202e14410880c115849005100d941b83c00540c00035030280d060b54503080140303044009034012868242c800da04e4540c9900300031001d51034a0800d110700404510000c000d1022b0108035800545469880541d40c15661804d491488401d5000b401e65803240788111750f418a0003050b80e0045001c070f030b082 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 835654010 1250 835652760 835652789
    0x6030d0f05070201050c010b0301060906060e010e1f050708030a05040b060102060403080103061505120105010503281e1217060109081018330e1506010504080d090906 73
    0x1a1607014040e10801035091070130f85c1d41d440c882410903005d0a04a4000e0340d02d5480e0603000940010740b80d0003541107078010345416024001201c0155000c0700340550294000c4504254814580702400e0440c4290a150501034104940c03921880030a4004949800006640d98107101c140407000c4002940130109100400140c44c01c4e6034004c1c100101840002c15064548013205095244001004050800508404141204144c2c0706000c0d01c000c0c4903c600901030301031100c480c1030b5040000d40d40201e210880308a40041541c1e00916807900040081c100d01c90a824800014039601c1c418005040719a19114040308112200041e0321010748441d05000c003603d42040a25400305401e103030001812000500c1d4140ba68448103000840e941c018550521036200702080b00010035013642c0007002e44140460340b420000142e08403900300d21206080e6012423600c90001200d05841a440340703061416908059803154014a0881305091010109500c4001880900d071148501070091141c0c91880d1701 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 835655260 1250 835654010 835654037
    0x121c09030b101203230a091403070302011d031618110c070e0c0f1909060e06090907110f0f060f13020d0c0f0b0304020f04111605010b060c0606030d 65
    0xa4414201d6801005d01041d01112424203007040310050b11901e0a920741c41d5682d241c004000d10301500c90061602e425500c00700c0544604001611005503981030b101c6149a01f10000c1c01c0b41941c5001c09420780c18454802001050405000440c00a14007110103420440e0031034002c60950700f01411050b5440e0040c0101440c0c00c00000340c2604440215030540141e40340c010040c1c4d00e17441504902408042c1c00600184841845100c0b41000724550342d810118a0715448102d9081075074150072903024009109052040c40d00700940c94210300c080c20030050107210610304908007130071070000c0301c0d180d017118003007094400c414007130103030310240742c0b0032254081c500711030300b144405440700700607000708001c440310002c03c00080c10000c09000400c441c0c1e00042d6075904140b640d03070702c1190200e0040501030403007400350400e401808105010300782060705010b0785058604071102442c5054ae51503403989240c140780d4407840010441c0e5488071002d03001928207081403501d880b80e07201d840c2c010410000c01210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 835656510 1250 835655260 835655279
    0xf050a06260f03280e1c2a05011103070203120c0c030a0804050102011107120309150212010f1e090f0906020706050414030a0207060302030c0403021809060a02090609121c09030b10 79
    0x1904032246201c01b2080b10103038113228000804404d94070f070013001c4140030510380f5684014004100c81c0260b850100c40341e90072986030b07164016614025010380c050301007a1310b02c10484000d80a15860202291070f216141d00c0001e251600d0424207070f42009000800f40502d5078203000380400341c101040400c0c6081202e548081c26090303482c07016403c042d0303905002010804582c00e404111292800e00755125011401d10321041c0400307105440c841e0041100010304551240203c44500b01020180c0c5100d07440e0900704009001001c0741c000704169502c00c004009400c80c800b030b0240354010343d400512132a06141100e40c1c1580b408405019a0007400350446095001600300c06850140c9000750300c0c0d840d011405030030f900440d00b0080d0f000d80c09402c0c001c26200c011500071700c9140345e070085070b802d40c4681051b00228817844100a030089020003001c00340342020030640303a001c0d40380c004941d83c81042c8050001c2c07149040c900340c00056050b1a04000340708070802031030b800030300c0812070102c203a20300002700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 835657760 1250 835656510 835656529
    0x40c020c060d1103013308061002120d02040f090b060406051318020c01150f1a0f0309030304050d03020310030605060f060d0f050a06260f03280e 64
    0x6031068800090411864080d40c0082c0706103e580030a0948075611000c0e2815404030105401c0200d41c4036144415649500d10100e4036540540d031114541c5032180010702c1100b0f440704484500354811090220920b030700c0d41c0014007600d240301300c3c01610395041c050300401d840c02a91004185608003a200481c030b594180480341100c1003418100d0307035800a4445104494501d6001c90040324100c000c0c81d008404580003080c0b02000a0000c003c11221100c040c4004031550084502c05580c80e00140425641043e030b2540d1480e2101c1c8039400e01d0b1102d02110030303c1d40112915010707500007009010030403100b0000c420f00d29040d070505608500d002c001e46800c400203448003806464a4101054041d2501d2100002d030f00000303082e1075907450243d02c0c00d0028240c02800038604510348000105208468411b01040d50b40d00b030f22444180b1249400a0038000c13140e800c0701958010f8089d04d50700200304100401c1000c00c1400714040014001800840010011941c01c05000180480c0c19031603968040c41c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 835659010 1250 835657760 835657783
    0x51003020a0e2a1206180c0d02070c0618090509060a1109030d0203032208090d0507150906080f070206010621020d022a1002030a1b030c020c040c02 65
    0x45041c0d5940740c10030001c95518548aa900c828100a101c0302c10524480080003013082001040240703494500601c80e81040d80c0d405006410f020101041d04003914000038a1407410108000d410305009495180000780b075503200d41d0105912034865442c40703001300340040051a44040c10015071408503007007601c03400c1c000d2102d039610b50740b1581d44500a0001041c1d0b0315411014007202c8180c0207940b00a5525801036030140281e4642c048604000a5008409012103501c100c6007030030114000180024080c1d000400c544034068100d012803078410281034404080c92564455601914081c0040d1035940c018003480d2801100e50100954140c001a149044824a00c0c001030011805130031600c91110711918562202c1c0001651003e50100381c000d030108441c0c0c69143e450201e0540340007400d1020641c07203401560006410b0740c0c4281c1c401d6020b503038031010b0450081414401c0b462004040d0441c035442901190b521660038002d0340d41007200b640036000070f42e0200150f450201c800307952158003042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 835660260 1250 835659010 835659029
    0x406080d0804030c1e03031509020a0e060702040e0a031710060215060307090216120507050d0309050a21080a1104300f140303010e0a1a0919051003020a 67
    0x141300204241100036485c4016803103420701c04800685401409420010214000c0361151032010072075101910032104101c4203525200c41d40c01d0a5400c1c0300c00c0d5000042c045e64401e5440c00b802080c11414400c840c0164400c0d600c542c03540240139403004060034084c14800c1340340c1d1100d00c01e01c040b54000170440301801941144000a03982c1c0340000b0301d00105038004400d85400800d80781015050703081c02c1d000b501e00c81c0101d40c0c141d4094200071107450254102c003030107036845280a2a50a0300a0388804080360107501958280307141c1c1d80701c4403011041d804400764103000c40c02d80248066840300b0790640002c04c408081c80000c3d1988000300300c40c0602d002c0c20042d1160a917900105401046035007004090700c003610b00300c1d92801c1c2030104200a1811080d692800b505031030101105c3c01000309c0e4140d500b000c21030b4606807102c400010041405905240b100e00c0039008c0411141e6503103140a2107a0710041c001c2e4902c074900350781c0c10240c68000d0444409171200a505000607139540107030b80190342042c072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 835661510 1250 835660260 835660277
    0x215040f061a1c050f010c0206220501050705040302010e10140a0c0f0c0f06051303060b060705300313030c02030a0f0b18030c0a12090b0f090406080d080403 69
    0xa421401407240b006072a940302c440003800c0e1164a4150758141d8071113000c0d0b02607440403645e6122a500340e501c0e41090340c0058004200040f01d0000c000314102c8680c2240001c02d400c4984c40d0f68150071184203895030740201c3c001080801c1150703840210041c0c4482d003650b10300c1304e014a1f80e01c044c0ca82d0000040c00b400c009400302d0102070417445400881d07019a0445184210a0594140300c04004260700841a07640d110200119003a4012411100003008910907000801d2454a40c00002c1030345010941e4060020840d01700130030340410800c010084004a1919081000d201c90300d40740b2030b19000381061110a200b004501c1241502c000c2d43d2036014280044900310a100003410b00110000042049403075038003280030301c013070242c078030f1303c5000c0c0c4540841880c01c40c0c1101c55500c3c01800e100b80e209601c40425480000c02d950f400140c0d03510181411249585c540e0040f06141d048504010350207100890b864110345050302602c00104503040191802d48400a0014000480100050140070004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 835662760 1250 835661510 835661531
    0x2040821180907180f060807020609060c1e030f07030e1b0603060402040b0408010b0f0108040b06011d040e0a020906101d1f0e01031424041104060503070215040f06 72
    0x20030795520480b062141340d40c11079481d00e140070fa550b81d46000e94000103100c000000c1480380001261801801d01c42c004060030b5071042c0610f8038a07480100200c510300103015901c0f044241100c003840c000c2160110701c03500c40c03401440041c101d4008800401c01d030352001200c40c0e601c0c200340c02c00d620348407001d0718203a94070358510020130003030310903030380480d00341e00e40060300140040c019448509118801c4a83da020100c40d07000450302c1c40e00540700500458051404a00c0c558050356610352104000d002740c02c80c00700c01c8800a0202e940ca0503050542d60001c00b84001140b03052052a0f03400f035411901d100065030724a100905400482242c200302803d82d081c1110030383e441c3c5407540300c40310700c80080030201072642900a0071640100d5455000ca410080c3d1510410940c41d00c039449100c40c4a0010314140540d8008000d412440074141d4025a450741080620b2000c48010000f520681c0c4815603030b4107020310001d207014660591403220b4550ba9046c031002500010700c1109154000f6000300b140f9040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 835664010 1250 835662760 835662767
    0xc03011a060f160f0b0903030c0301061101090507080c121204060c050c030118060b0907270e0a060303020706021603171201030507090b2b03050d02040821180907 71
    0x1030101c04454488080c48000400c00341684c0741c003c080c49101c541550f80c4540c5401656400300762510800e250301400144089441070200c420255008000410300f000305841d0b45041c01010b800000360341d007003844070803183c0c01c0c442c0407981c501201e2001010781c600022681203541c01a40980d401300014548000103001040118151090006008200c540406484600362496422086800508020401e440744c0f4001e044c040c031504464541c004403454001e0130140d42d45401400f1791081300510f2006c1400ca049480c0e81c1e202d0003540b0300000b170403401d40c10301929010040d88030320304650111a440c3d82400d10307902039104480d4001044c80c8404248030405010b8090380b00b142d0b076688400b80c000410302400044000840c0c008040c02c2000c00f10103028000203000160414011000c0c401d00a40c903102c8041c60a08898003900c0e0950400c0c3c041711800302030b68416070003505140c2c08051202204607400626400b0040e5807c0d603186400580d0781070900400c4001c04003407050301a4030000740034500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 835665260 1250 835664010 835664017
    0x61507050703120e040c0c03021b1305090c01021507140f090409030905040b03070e040803040f0b0c04050a0506090904030f11070f030b0c030123060d0f0c020c03011a060f 75
    0x24403036030300300c180c5210b120f004009032061041070344181c1c107000514403110301800c0c202d6121074141c4d016000155400101c1441e500010b101c080d04041e0040c00760072100c0103481103034010f00080016180f1720054400092070400710a040e0070000d0308550912031896000425200c0c0700540940d8281c40e2038009002600501680c1e5200380c0050421111508040d4480043c005490084504105009504003030642d40c10b00c41c014441488442004540030a106102540d17003e0300c01c038215a07040106a44800c090b0000f61241c0e011103c1c00314044c8030500d40a41c0e4207001d0a8165411402c00d800980051150903020300081c090201c2d152035230032907622450f218603104100c8001c48500d10340da181c041c101408d50b0301c4180c99003070802d80071400c80210742e41200c1c101c406010700301150364601c1c0b42682c038213070300386070110390210017044138810006090041150f40f0301100300010700010440000f90400c10002420741c802c0e49000e00600ea150000303012a00042400c0c0e0b039443e1103007103600b8a031610f0710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 835666510 1250 835665260 835665263
    0xf030302130611010c0f0e010516020d0f0605061e1306030b01060507050f430f330f0203040503010e0105160c0b040f061b03020901110303061507050703 67
    0x303007640428071980041140e00703110001c03002049521069901290341200341448940040e49a10308410a0340c40b840280c102c00d40d00d0034009081d031980d50300242c08805030300c000f00d0714070109001090901c80d0758420a98810b0080d10100c0c22031a002903260b000d42c41e40081c16100b00e000308811003280420f640448085d640c400b09100465844400141098110220483d002e2080300c0d1010179206020842e20300340b80c0d854502c2000407403a42d603506140c0c2c4070315000c890100050001400301c402850800002880c1004102d86c2203820003454075500302d1413406a4802c003400404007000fa03c0c1035800c2d480f0740301075460140d00403494894120f00b180700d107900c865410b40c20601c040c464078006500007800341101406900c0079040060054440c1090b940001d0480e00400300001d0101e0707001141280c85500c140f0002980030309051880700c0c81082c103508880080d9000c1142c0300d06580120608800c0e040c100021410340c034051000980c03640400906070120361012580345c013089010400d4070041c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 835667760 1250 835666510 835666537
    0x80a0c35030702030f1b0d020901060f120c1e050901090e0603010e030d0606170c031b04080a120206070504080715020309120105220b07030518030c370f030302 70
    0xb0a101340c170b41d65801c000a501e59803000c58051110340c0c2c94040341803c180c0b0f901400c81d1007940e191007010b0b16260024013040045c00030342d00c402c801e0708059115010341c000c456203540358101300e48005003c04ca0001150201884010820306580341e811100480c103e55003c0140c007460381c0c030400428050000c101740c9010034400407400c2c4030408081d0f0400390545060b507455045031440a0080401c41d9403d590640c1c002208101180c402c08520286031203c00c41100e8141c40c0c55901d94040b480c15141d464155000c2d210094040f205541c14050342c0d803c02e03418a805801c007410701e00100d40300d0b91180326a4150105281d860b4111500034800d540003e030004050855a42c0e8030082640a0001180c0301130030140300100790002c102100b80e488070070720b0300070301000c2007691015829002410040d2000c00c41c01c0206034040c0e02e07007004000816410380441c000d040f00c1407031214400445021010340c180503c8150300209215104a000001d076641c000328856007009040c2001c1d8000c0c86101343d45030b401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 835669010 1250 835667760 835667773
    0x2180f1f320f0c1c200f0c06030a150e1603020304030504060c0c09020c0f070b040305190303021c05040b07020d02060106210501080a0c3503070203 65
    0x11500304802507150755440c803840c41c80072102140401c40404054100c09240d1051155441c070750300d41d0026100c1400150f0440d81c1480941285200b030103004d0368014006aa002521100701c15081524400c4d60704560083c01042d400d1017215858a0090190358010b1401000144604041d5002445800c210040c200c2d01683c071841280100a001c890600c00004039081d0482564828800c50344582d4056444030300b040d06207c002c40d0000801c00e030175030b200700c0c8a60001ca210103041c40209040c1841c01c0090520348101e45041c1d04021071580280700740740b0144010404510701003140c0c41291550285450000e100d8503050b4028000c40a40560800801318445180314060b404980658000c4902d1101c5a64000e400c03681c4100340c50718080140c0000c0010002c0318010486034025080c401841d403c68012b00c905d00003212000d90181d90b1030b6001c2c507001c00500924508542c064144c1c0300281031b10103003850aa4020442000d540500f00581c088a91384018041c0152a62a540182a100c0f03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 835670260 1250 835669010 835669069
    0x606010c1e0609030206130809100c12032f040611030415020c131506030209130e01060f060906021209010c120e01110d120203180a08070b070302180f 66
    0x38031038820f0850141c07040d04045603420000c0c10700d80015580c03115440d0320b0200c051060000b46050a240c180c140100e01842000003601ca10010b02401d40e00d5800007041c0207008801500961002581d40c0d0285000218403d0002c10a0468068890609140703c0d8580b40c01c050358030b1842103600100e014400300302c2c5000d20550200b02d060403520100c44d0480d0060314030800004459014100419070603203000104140c40c0a900540300070040248011040e07219212450161002e64103e840e41d655240014850a81da1641031b001425040c45c05054035030401201a5a509400b034a03900951b601260b05d80440c0c4c424486803940580c80b150503001c40311300c000e010302100c2100d092a40443c4101240280b82c0800060407040036482d951001002a641001c24000750b00c0501070071503d4600c000c40c00369014042200c50700b1300f84141d6031503075501028180740c00c01d040701038411010140100540d40448940070402144041d045035410302810a9200042e51015003001c0c1005c038001580c2c1c03544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 835671510 1250 835670260 835670273
    0x30203120c1c030e060703050106050a0c0c0909050a050f06060d24090809150c030717070812340f0215180f07080712060b1807020f060105030606010c1e 67
    0x584c00940c01c000caa0542e29465400c0e4280d1300c1c01d001b14000107006120300d040d068411080e40004d02d000368205200c40351588031307a8082d00c1060700140e40390342c4041525005c110301005002850b480890140040b42440300000318426001440506015544c13001e0b1010700c001410029401580d490003003000c6049880d010132283c0001c02441c2c861038400d146004840c0b600c804075401c400818001e1403500d1070301d9680100c0d40c0d00189030f1124002c01400704034001001c070002010012035400d404c4000e0326003070f41e541065400b0800504958501c8066441440551901284001301c860500a00005401c08104d1400095410003440d41d501c550503c0942d0320921400d0741c170000c8900a0362109134420040c1a5603202a00c292010381d40045400c2100c108041900d01d1500c3c4108000709609a1110005100c3c41809001d8950f0444400511105c00c1e010000101c2007005038000c0c1c09150300d80070000c0d0300c400001340703524103002c50364a81004000414a0078440114107581c0c004101e1060b04164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 835672760 1250 835671510 835671521
    0x90b130629091510050c0f01091b06091a0702011814031212010902090109080114060a080a120f0e09010b030402040c050c10020708040302180609060a030203120c1c03 73
    0xe014621031004100e0303c0981505007010324801600000c0640ba0380c000c2101ea0f9442444100d000e0701440107000350115082c002e016000b0b0280141481c4807901c58680e44036220305602440130301c00640d404205200e4200300d00d003200058402c1007516031460b0b000503100c542105a050350f121740386940104031190441c9124025100940884003c0c82101c41400e002d40304800300f040c507083c03001004104109141c0c004050041c0b0601d08500c2d4180c0d81d402c9142502d0340c08103c900070700030300c0003002040c0c100601040c0003085001e0007403030641000e03215620003824071700c0214204900a4401c1c04018050110101d200303401a11403499580d461390340100b00d030026203003280300d0b07410a100c60036410310802c10307070f082480c81c003015010f0b5103a0040d540c0c0003507010984c11034460f0002c0c00000301580d10101c09080501600c0481d00240c940107041081d104002054244501d40d03001060002d40c8001400308a0441112015540da0710707e80006450104000345040b000c1d80e00c05034240c16941e264001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 835674010 1250 835672760 835672841
    0x150e060406050105192105030a0e011b0f0b060f0a0f080c030601030c171614010e06210a0605120a0b0105010e010f230c16050301090b1306 61
    0x4000326625001002204c3c16049050040c01891400500c5000220700403d548041070f200460b181307040036507e40e425600009003181c045110440e8440301560041008880440400a5a060840c3d00e42c0c070101c801003407c00144c4220030000000740c4c1c98681d000040f100600081000d0001ca0380d49444019400c0c840c0115040c078011452281260300b030004a95050341e5004601141041c207224120042c202c040c1c1044669100300140392506103a010900400303403030980e81400540d0302e183c0000d000040c0310350341e50740958800c1001c0010f100d00d0b07800c00801032141c00d035000c0d0203032070301280c0c04003912940d0481640201c1e25042111009000581c00e80024460b9046200580c0c0e14001987e007255044043c0b80417852a8024108292081c0c444121000e541e01c3e5455040c1020400c00c00b40b5002002680740b00c1e800078115055031404914400005c2c04102c00074804a2810394a40702140000b4218003031005000880408010341c54004100c2d00c1e010f4540f2807030710400581c89004c4800d41412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 835675260 1250 835674010 835674023
    0x120602031f32030d050d021312030e0d050c0d0f06050a061707031e030309050a0c0906081c05090a0b031302090a0507142d07061103070207050607150e0604 68
    0x402825400510503800c0300d0b002c018040d103000303814107100b80d03003a5201c42140142c0c26802c001038a100007a00300c05c00c015103500d40014407541440d20b0b0141c018114102c501384502c990003401c6000940005140c541414141c1e10400504500e140070000c00940190040000741088200900c1c5046607001c40c08450250040c9000f00c0a0101c01030703110426030201404200b0300d40c2100403540703070009041014034030900e00020154003a0315045c1c240303a80780b0011200090043c0c41001840c0d039501480c0050410140900034001c2c0c24220710011002c1030070540180900481c500b804d950756150320100a240301c2c1d2aa590741c0c900000410002e0f914528100c0c0710358010741c0030070321111180c4110740c42001c0c140c440d00c5801c0600c207120403c58000100c0840c0f0220f84c01d801a541c28100c1402c05140d9403c00c19885c1c0f01d80c020b25124082d901c90f145203a03162202801080340303a941c001055006c5031004c3c0d800380e9071243d07503062840c039400100662071507850600001c586040e2000424911884c042d50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 835676510 1250 835675260 835675319
    0x2070b030f0603251a121e0a1a12150f0604140c07020d06110711040c030c020303010905100e090c01020f0d051213050d0807031401120602031f 63
    0x68401c015250804c00c1d41c0003166401c400d0018113441c00503103a04400310612681051030480c03011465400440311545c000f07024071200340c0c000e000540700b1a0090b40382d05c818000001c06140d4080e20841c9156602e1082183c40742c00302c4094018000803100c1d20040c091540640340190070030a50a0007516118003035858000100150051900568003034008440b0b0903140a1980c0c00300a048c50b2007007425201075503601c82005101c4410402090720741e105608402d000f510f01c2080004480f41e9a51400516042c002042ca14683c041b0849041d64035100c00043c3d540c441082204424041390049400c10420005101070329900040d085d101d00000d030700316100380e0400301220380c4400a82d600480030810500980300001c4001840700da00524042c1010b042c1c2d442c94850902d004401141080440c1d8000d050000c0303240e02d0b00a00b44245204103982c2207a5240804000748404035000c081d12480c1d0100115401000c0034694805070a00c02401d40e0782e164030307501c141011042344513504902e0035210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 835677760 1250 835676510 835676533
    0x110a0333060e1e01030209010e0405010f0614090f06030403030b0312091e1f0c050109062a020607030207051603031116080c04090f30031406010e0102070b030f0603 72
    0x1422601c0035080f1660f01c01c1a01d1003000190080d4211102c054107000c1590207090a80c1c6030b82c810b8038005c0912808090096162a40141800480c0700c0d0a16810754104241c0100f519500020310721a03c094440c00d69a585a0404400900440082e01d504d80200b43c854035404410002408000d02c00300c801d580b1151042c6503100c0400507c1140940140b401c4803181c800c0503d46003050f0116081e0300744245ca840c1542c0d201c90860b110076008a540c15038840303800c8064030b000307817000c03050581e07070320301e28442c0120f84601940c1c0b030800620941c01c041d000183c40c000c00406010301b84400c1000825410100d489140290020050499405180c0310300d2207010244200005444201d0b100c0f240a42807503060081404040c10f00c508051b01c0000c0c090000d4400034440380b075080554400b41009404ca017080c0c80d6010110354104001400301070501b28015052003840328016000780007401d02c01c00315820b480040c2c6c100403803a030013009500004010440503034a000d0700684182021800c0d6100080030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 835679010 1250 835677760 835677769
    0x7020105130201081f091506080f2d0a05070806030c06030610110d050a170105061b1c0302041a03010609030308060103022a10110a0333060e 62
    0x4950414806805000d41000b550180365440d4002d02040c1c0070003000781a0072850f40e40c40c50315500c1103100940d140c1d03103029801032540050f0b002c0c001e107103040961030030f200c0c1c1014004540a8a1010f209100614001031152410070f182c1c04082070f0820007031a464000f075500000d01080310001d002c10407400024403145404030384130280c00c0f40201030b10f00390707100d400a0102480506200d00280f04403628500d04807801001240d2141b900e0b96a26569030490b102d00404502e0003980c5551802d07408070041c482c594442007903400444183c4030040c0012880c00d4040c0c074081300c404898584000100541c840198140c0042c4243c070f010707048582a088100110b140d0b948024400c240024810041c1800042e00c500203141d04901c051501504040b8456041d4003140c4000c14450101d40024802108035002445a480c0505c3c51a90411040f0310305981c1c03003020711036000044c0130180c2c3c5420042c202d16801e040d40b0352503080f01840f0005804e0031401c1124090560140310041569041c0c551002e181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 835680260 1250 835679010 835679021
    0x7021302130605131d1e0f0103020d0614130203070e010b07030f1809020c0f0f0706121d060403140a0c120c050f010203150103020405090f0c0d050106090608070201 72
    0x103015021201500e01107080b225504081110042002ea8070340c0020800d00034400b080c880300b05848052203a00b0280034120b908035202d01442c0a9851150800647c2c494030b40450741101d0f0150b03900c04441c01249001340003050801007800f011000b0406006642c00b03a0040320704a14403e0382210315442d00c1da40c2250080c80c091240c1076105804100310000684108481603e00440b41081e05240d0740c2003814915814090b0000c0541a43c0410824070900003013044a010350201c8010f004d08001e5001a69210b0f41180030340350500401500d64260b41205611080c14001940d681074481d0015001c0183c6444056600b80d001800645442c0401150001114003540b0580c1364241103014903079410b07000c0074070300b0360910600120800c1400030400621404610250b103070300042c0ea070301d010204000c03000c61000f01241098814001800552260b106054000841072400d5403655681000c007100c522805c000d02d207603903040c000001030f2107070481e521205075200c1c2c0e284c0c02d04540c1c0b404401c908030380303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 835681510 1250 835680260 835680277
    0x80c120f0a141302120715030c03060501031a0405090f10061a040f05130e0f0c03061303080a0e03040b1c0c110d0c08090d11030c01020a03020601090e1f0207021302 72
    0x1d104181c1401403605194007038080c0790784401e80d030440d684c42c5907c04000d1255540040440d84480e04d48000e1079143c030811003d00001d007420042e20805095080003840e4050400f80265a92804100382ca481000859404112041110410412905084041c107503602c03540d01d0000c1c6608605823001e03280300698007a6405040c503200a1032030541040401300d0382074140c0c64820358901261704c844c10305112180b202100a0014800030400c1c41c2032600c1e0040041c01180d103100649002000241c0c00340404d0f401003008000426640e0b45111124198401d9a001600c81640040e09038010203140640b00259441c28004200d1102a440290303140c0341c1d903410000d00c0e034001c20110605580201c40c08040d45001f0141c1034100b8003d500800c1c482d509490080e10508400d40843c4850f282c00c1042c180100300c280b0140030f0500726540c02070351701d9406004202900740c441c00d6888880301304124000d03040052502d080803031100c2002c000003e40c001d1100740d004848450b01c000c0004a80d0080740c0900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 835682760 1250 835681510 835681531
    0xf0c0c0c080622060605100c0c210305030604060b1918050f12010603140f07090c0905010804051002030a050a0b040b0a0b090d05060702010e06070201060510080c120f0a14 75
    0x380c031500b06422641c4202c21084800c5545c4000210706500c0305260600b16455a8850409108040c101340c80e2089a65218021410040b928000d03400844c480c01c603407840d818144251039480e2200010081d2410742c100d100c042d680814400004034210038a00720400040c7c070382f4032414408100c0c00305441524001d80d0340250500c5525989030400c5c0002c0706c8203150391400040c0c05074481d0fa0302d4030714076015600301d020399010b042140303900310b0184405001045007400c208200c070544200600545003511982c0d050260a41c006800e1040500086044401002c3c0440d81ca00e001c46013800100342c1940d00b5016a4a0200e00d400c4c2400c081c403650010000c010b00200320b85144c421400c80390f03409031400c00d81005d4811142030000c2c804201d814000e074226000420071341340c1245003628011008010204581c100001080161907041540d05210b84a20340015503a0b00c29002076043d100710640c8070074030400e0400f04124060746c0c4c3c2100d8083d12600714140b01101c2d807501d100c411000709440441c000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 835684010 1250 835682760 835682791
    0x12020612040302011b080c0703210510090f1e0c021219080612060a020a030f0906140606070b0606070f02090405012004080601170c06030a0212060418150f0c0c0c0806 73
    0xc28040c0080030aea4040042c4004a4400344060203000d45206030b810131454107c0150a01c86d00055004041da003003000340040000d64001c800c0c43d200a20001f0400c180c41d0307039503101c041041d4400d0000c518800d21300030b6104d40c0c0c1c00381e500405a001c10384403250000035406801240c0b05103031800c40e0404410900c0c1c02840281c50b070441e0a0001c2d80803c111005050380e543e08104510700300e000f03041c64103020380c000003a501c01e10401251794540003400d2500c40c0c0810803502e80000c01c01d00c0c000c1d82000d010b80b0340755258100303881c1c00500c0b031344205e1010358440c3e00a170801003000b81c15044008460007600c00f501d0328000c3e15400a08500642c0030768802c40e080900144580c1900c0b440130f0001d030b118041256507000802000c01c8055005035101000756400040d0340c492140c00341c0c01c03d900904c1c261410065010a40b4440c4810060180020302e2080c00c10b89900255049070803016004c4030014041243e210560f0001d0410480c000003103d00c520400c20002d0700e141c0104a4902c980f4051528816 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 835685260 1250 835684010 835684013
    0x40510050406121a0d0f050601140d08070204020f1204021018120c1d01090506030c0901030f0609120f120203010f0b0a0c0c120201110706020712020612040302011b080c07 75
    0x40c0c180a0783c2d04c580c0804400303a020603030f540c9070654003034540900040c49900d41e85081007800c06a050700041c8910081c02c60903480d503110003102d0710000360041c0c405a11903940e440007030040e1052031051100039501241c044580303045940328034040e620885540303444d900003100c1507501c0044002c842c404184610b101b000204601120204454070421440148a440d001c40300400280e054203540214202001441542684d20500ba0031000890050031104d02103400204051814080180801c85401150040001035042960030329030004010101689010004000203814150540040c0d02e00400d14000e494920072241603403182c1c1e0800581e14141141c40c502c540c028484101044403078030440f030108a0900111014000e456080401944a800014520000340c1502d040035041800200500c940028060084403101401248040c105000141d00d038024405440ca000000a042008055040d03010300d6840b0724085005140d50314a880460b85414225a00100103004012000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 835686510 1250 835685260 835685297
    0x11090607030c0b0a022505031c1503031d09090a080703200a02460f0f0617070e011404050d030f08090c0d06020a180b040510050406 58
    0x8006402824036400c030081a0750f03030f41035000045801d41d0032540d010548804181c103406440b1604801d881020543c0c008980b19103880344113508400101b07035002c080c500007041c0190802c003507541c049840d2100c0340d541c03400d001e06514081050104007c240402d02503480ca8101c1c05140103980c00d000134150b13400190794440d2290b2007504103809100c01d00b949065181000c01e102000c0c40900e070050070402c0f0700303031042c001101256034400111190b40481d40c5d00a12f40d000208808415406c00a41071800658000001402541114201c8801d108000c1030480300f0001400844640e50340e1a141880700400d4660071314000d9520500140c2c0180e1103103002d42c0300f002140881800c03000103914285e07459000410700e00d410b90003140070030440108443c1040e000807550f5881071010001c0c190102844001403c0203e180300024041c0d980400e00e000c919201e402640b80b00b02c550000513404945031450038165030000d1040c54881e9500d41e0111519500c00d030281c0f0102c980300d449000031241c900380081e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 835687760 1250 835686510 835686517
    0x1603090f0611120c0702100c08030a151203030b1003140f06011806030b0f120703080c0a06020301180b0a0e04030309020d05030d0b040f0c0f0804140318030105060301110906 76
    0x600c910b202840200c000c20383d91019580280c02448800c1d60310f580b00d105000b2507100358584d84041c44062041703a804182e0103000c603030b070120100e400052007000b002c19040d0301030180e402c0643d0842140c0c0009003055010303489546184402c507113034002145441c10440030394400484000c0a0702c10301020640d140c48040c6256001141410450008000184810340c903c4007580f284000a444001c1018181840300e20030443c840150307200100780390728100c0f4a99422451000601101c00050300411031082486114055a40850255035a5956524403e00c585c140049110312501d0480b044640b494400d40341002c450900151110703940e030310348055001700320b9070764240c1e080310b0b94a003868000307541440100002c0702c140304009a0582110305002c2160000340840c0c0c00d02d880c05102042003034201141c0060140945013080c0d0503981c42c500a42a000034a014001e2880042a04d0304894019a00001d04110660081005941c0d6104040c240c80074000303160020b400401c105e144c01d04058004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 835689010 1250 835687760 835687781
    0xf060a15030e03070809100305010e0c0f0f07032307030206070e0f220b19031b09090c0302041103190c050c03040b090909151302010306120b1603090f06 67
    0xd030081c5a2400b2a00b15408258200d5007200000780070002c0340740001100b100c41c1720915040180f503060820503040c150010f80080c0300e0502c0440c0035104003501030100c4911417420002207440c0c40441c076000c1d1801d01c80d2800711481300d50000c160101e0801040a4821654040d4010700c0c480d00c600e502510a041d09854094000007002980001921000e14428450740f0303030ba6414060ba04000101c000b201d40c080401481184c0c81180004d070101010160000c1d40d0300030446171000004007084103004000c903030140a1075800c05840c18144241004503404130380c001e440030300000030410042100f920003140c03503644044040200702240a01c43c0e1102c42d4196207410700b5441c04100f0350b45c15140d034005910122944000041c010058105412003d412003404401000c5650084c0070402039404010100c10031422400b020006581c03094110900a21290080c40a6003e1070b0034030a900004c00c0b2289528101e00e58a00154284607100350442c190300038840c2510b856840e5039060103005100355 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 835690260 1250 835689010 835689017
    0x40209040c03080a1d04060305030f03060109050a06080105030c090717091e0f150405030a1209140d08100602030a05131707090f02030106050412061b020d03050f060a15 74
    0xc0440011400c2000341035484c415220310001100101c03c040b1094002d0b041301e030046d4203250041000901c0003042e2042c409040e11043d480b9603c850040f0b80c01c100d0759001540c00301c2040c00004406401072045816104260b044d1402e2400d42400d00504040503954070000a0543e4200c0780744200400f180340d00302150009903100289c2c010001801ca62a1544602c0070b07420a450030032206070100700d005e4820440302080180c928003071f10360716268010044070310140700e03140030390072003103101c503404844001c1d80089413501e060303064900381b03a4800d0711101000c04940b14602246072040744400758403c80f981d686c002c5240440000f0110f07447d0300b000d0940070304403042d0036011070180c0d030a1840c040241d40c444018503070302e4944414141034850004039604a980b041006120725a4407070112410f40f002807007000d07165042e6142040c024500003e03081c0300e4056504443e68080d40c08642c000340400150740c20b01150b107501c001341041d1141590810750007030280d10300300000811181b400302085100d04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 835691510 1250 835690260 835690283
    0x1504140a051e1f0f080603061608070203190c02010e03061b07051e0c010207060905090109110c010c051b01360f0302010204090609050412031505060f03090607110604020904 76
    0x20500c2c09240411411000411a0960340940312680882d40961021040f40140081d09200c1e07081d079274482e80b40581c1e0f0104603034900058041c600810490702c00310312180c1d40d40d1462441410003441d085401c001240001e0845038a410031b883c001810794001d05420b0b45090481c05c0520042000d948035000440300740c020800b00f00340c01c041180c65820203c107020702034020108000c1c0028101485500314800f441600c02003130089840c7c1c02c40c20307411340d80c1c017070000120181018000100343c066000d04403803035801c1c02e61818409902801030680e20285414007818645600c40709401ea5800210b01882c822801c41d400c883c08407003c403200420840881c41c10703000d80301c603181d1746607011801c4826009030390006420082c03403140d48038440003449502820491420565245000301c0822004032080688a807172000c9070310f0303c550600c07009000040010345d4900c880704010340326800803502c10150380180000141c01e1801a81620340078503000c8080d0100b907603940d007008180b01018005850541405 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 835692760 1250 835691510 835691539
    0x90a051c3804050d0503070903060216050c0f0321070c12050613120c1416030501061e0306020d0209040519050c0c100e010b1504140a051e 61
    0xa44200c040d10301903409010980004941407514030102a6114100c030080c10200404104041492400ca801d14a0310990b01e403681a821030b50101103800241070729100080d0702002c071520006010741d1521600a5401901c150010002000c684c0c1c04140d4045d0031041d41c249004100c010405003455180001500785101d0741c84025900740303580c010301c1454000614082c00c1c00410415030341e0222410a50a00c80c0c4146d03075a600e42d000b8486150360070721a0074440c01080080303a4101c00355104c074681c00c4a6445410f110640b100032030b10300c415501540384c4803011a800340c0342903800c6180f0150304924054903181d80e4585009500600080d01403903400c0c0403684945e9168059a805600900b00302c041c60419903d60a04031107015040e6203294004012594401c0c0000c540c9000c3c42501020000d1140d5000008602401451003101d070300c017941140304010402e484000c1d10590701304030b003d00c03012800300701800000c801c0b6009060703008185103203001404d03000c541c0000390000080d11040054020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 835694010 1250 835692760 835692773
    0xb12060604080604032105010311060901020a050d120509210a09090603060e16050f010f1107030c080d050406020a02060c0c04090507060e0f0a150c0503130e010b090a051c 75
    0xb51011000070302c0080b0130500b594070146d4844107402c03c0c02d134100300551565a03508282c0500c1e21b00b4a020b6800885daa0595a00030b00669a9141d0010151520054417032002880d5003022b40d0480038140c13511000c10ba40400000340303985860702c0f020406d00c5d501c0c11030200388210b0700608814001c04c2000940861701200c20702545004600c01c0c0303030108241c500704521a05014500c0d10700400001021010010790b034820840f4882c0200a00b8281c2503150100c0080f101c6111149400c0042d00c140d140000c10007004802c4401218501c1c410354002100c18141143c4038899441802c0050344550307841e50244c606003000300003000d498001c461541e00810080f5040c1c1d00d80c0c1c84c040da07040e0440032042060315000b03142d01300610405c44140340492800000120700031154001d0030100c031040c80b108141180585501c1c441c003a0400d0880c0e4844681ea801540d00c0c9441d4001c2100158844000080343c0d0283c1003581c0800030014414002d80d8108000d100c4001c103501c4828146096000850011888 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 835695260 1250 835694010 835694023
    0x1051803041226042601090b0a0e0708010911011b1208071106130605090102070201170a14040c080106051203030f0709090e01060f0509090d0507020f0603090c10090b1206060408 78
    0x240c4e000014011150175000841c3d58042110007442d80d0524110800068041000580c000401580044c0500d20001c4403441c08880c0d4018407103d602e0200c20f0014040c1d01045035074941d100766a0703a14060500c0a10b49076184803000c0081005085007a80100301d4011410168808800e00c0d203010884000c03034a0394a4120f0984151030309081e541920024459203010381d542c000312400c004d43c43d001503031780005c0008645460a5150b1b00055000c150702600c99001422200702d14101d01089080c1410800b986008a1056100035840c0c89030004540c20b1500300043c20122060283d410b41c0d071046070841002c1780c01010241009160407010401b40f6561090303030408091900009601c9060000c0c401a541950700440d00c580c421004011020800040c12884894a0329115441e101c041c408203c00c58040c50303542d540701c1ca0100403c5505000000e520050ba8804c580c008206040d084040e607200d05103006580d4000300030000f104160700d03516503468218401034143da14007640c583c42a0f00780364 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 835696510 1250 835695260 835695269
    0x13140301140c0a08010605030903070303150503030708130905010e04081803060c0403051b03191a0103060902040c03050403020601210b151302040b09010c080d05090105180304122604 80
    0x580214649454644c80f95070203002d0001e0342012444c2d801c040148550f82e00882000504047c3c58840714500300d45500c00e030070b0007004090101d9444810380e01c0d00d03080c80c0d048809180c406481080001820030304901900e8100d456603188070340e058480d501c84481070f0780851a503950a82040c00c0161550b20100140d5100d003ca40c41603988450031450558282990300401d10600341802e403080f0110344d00030441e64065a610744078a076040c03000e8038010a505403900f05901801040300000018010a074125400c940d01c02c071020031240190b800c058080310000d880140040c0d2080c07006200d410041350700800801c40103110b274484210103654020481c001183d00591041d011130f04c01e60181040701903401000f410101c02d508040c03c003160f00007140039000304203041201d04014902403200801c21110314a404640502c1945440d1700721902034203065481d40c1c00d2002d1181d6165221401000b40c40c02c4c4c50800200807003078803039529441c100075480340951401c03165095030768001c10b100030300610080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 835697760 1250 835696510 835696531
    0x40b0c0f071410091511070806010618060512150a09050a0207050f0712150f1d21030c0d0219021b010503011413060503010e0303100503031314030114 66
    0x2540d1010070f1044805240301c2d454180001c3c501c09214809490805d010303010003903d0400905141c60000c586084040d500140e6a401804004a011580126691003d20301c003568034180c5551240200c803c0e1280b410103142d640c50100c04588510441082c95041c2d00c00208205205500c550800e130445074195115140180d0000e120f0003041000e10001042c00c4258000e030140387d2500b51050b01e081c0c040140200301501016502041101d103600c03540d2812100c420800c568050b090b410135040310003501d50721603449184800107100c1656030402030741d282c1144005013103442c1c0e80d98021664016402108a0503000e1142d009448508466080c81c00340ea90300038880551500010300b048402c22a08604109040005020940b92034694440071202502d0748402c01c26988641c50041150383c00083d41075003001001000c0450000c059030060b000480c284035465500d404240ea688205d030626590305501030410880c00d0210255151a0400a000880d40107040701840304030354400c1f622655903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 835699010 1250 835697760 835697789
    0x15060810020706150e04141c02010507030b06091008090a2f01030212040f03020a021003020a111b0108040602130f090c2d0201020c06091e06010b040b0c0f07 69
    0x14003090b8020715861052051981310810304140030795419800083c00a0007920f03032002e0a002c0c01208103c58804e510700d003e00651104601c0600034007070282074490705c000070308003a03c1201925210084070324100000f00b4041d841c2146200540364000002e10400303660141c0c13041d440102c0c42c2522070b02c0f801040803001140c40380314900e55507540c50175907600d141010700c14000e40e142c04413409051500b1036003220b60071050300d42c01c0c68228a001c83c012002500300980d2800c1d075815540640250001001d20b445940c071400b501c14240780d46000800210a4070001d88803190700c01c3d4007800c00203400601540001d850203290740c1e0304001001c101c3d4031075019105030960030480300150344625403018080b894001c1c500410500442045e404071840303000f06c0c003170959814070b20600035030455862050750000d540c1c9600d040b240e055121110004526024030011303000c5071b15030f440401c2c4541038504000310981410309041601c0d8040e0001018021188179196082c035464030b0400540008096021741000e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 835700260 1250 835699010 835699013
    0x1a04090602280912050f0d080a0e0a0c061b12051c050906040b060d060905010c02070812040b0a09410a0308030402010315060e01090e06030a150608100207 68
    0x800c0c10420b0586482d82d03102d07182861154440301003011030301e1074109601003c149061040c109002225500704038441d15a441c1e60f065001800315101d0444070004215603840700ca000d41d01c50300440c8000b00f00544000b0140320701c81c0690002214100d008451407074055480d520f402d440c14203412900b0225030049034500c144203900031000b440c1b1003a88024416400c1031880d007aaa43d1000c0c3c1b0040c10081c941e40051540e450f0308800d10240c5070002018413006400b802c6c014001c0c40340030020001401444030100b0402c00000d11100c00042e00c1e10058600741c0f406801b44100d42284158408016032030800190f40c85140608502903c4126050f1b82d104160343c2c02014130180350001c52142c1000c1288162a984e100e189105c2120f4110101c19030302e59036071004800406144107901c0500a5402d008111560310000548490b0804c2c0c0310f20403d2074984000341d881c08400c80e0b03600e51547c0240481000102c0d170f00040c5116040d001c40219609469100040c10420040714025080382d0228442c0c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 835701510 1250 835700260 835700287
    0xf0910140301030b01031b060f0c02061c0614010f050a180e0c030709090b030705011803050105070f030b1c080703030f0e0f01060504050103020307050105160203030406051215060d1a04090602 84
    0xa940b05907807d0942200c5241c503c1c054030038070f50182ca8105006202d50740c581991203100444180001d040c44a0140c0f500d9610b08034010300c464020380404000301d0000e81107030350141d0002078941503180c86240c204000a0b0040305c0094689284030350001400800041c0620a002081d000f1003400d2103040c0c891800810090006100340d000c4410b440c1008440456a10013040c06001d8504c280b0303050000b82134440800ca414140380d4001005c42d0318003020001201d500c00000441211140e8040c00403070300d544100900404200340381c0340ca61200b4034081000440003030041c043d00b0320030706002c21000280e02009080320400c014055040d04402240d48030382d1001e00c2180003a100485040140c0d50450300401e5903030f07400c2e00406051140c005a00007600d940e4406d5a03a036a0750041c1100e9841c3c1c0c0b1000d00074400d400440028844c0e0300c000b4045034009542101d00f40c09600d004c1c02e12418402c0c0d0a505c1c0010340740400041e1040c091386040300d007240d01c6502130000c50700c1c021700340035075644038402208 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 835702760 1250 835701510 835701533
    0x1180908072906130f0615030e06010e010302130209031f1e200c2104091803020a170d050408040510051603050f0d15031103030f0910140301030b0103 66
    0x184060070582c0802c4000c0d9039101c1800d03180780350744034001100080c290050000342440d4205400c0003a0b00c4400d407540552507080300100c0e10106042e103140d43d9035074402c02c00c244001e000081d40412001c407440710308115980a00780b8140001e007201c21035020130001d050340c10b0030142c0d207020250300c600c050500e1410000c541500b01810003010003403070404000c41e04c00c4447c5542c074902071080009045440700d00410450740f0031070031a03081c00b405810003410340c409907129110b401c1e800390030b21030382203901d05103003000c0340c103541e010b4011700602401607440040c402007812022800900078403403005240031501c03030a4800d07489141c0041c0d446040204000100760440d407000b0800c1402c01c42c02c428440340350381440545a050408c0c0c3e803282034444040b00640207040b092038545181119546030b10004200389011640144854005100a0828541c4038803404195061024082000301c0042c1030406123405003195a240900413544200560072243e0310a0b401907918007080030040c400d0016440d600d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 835704010 1250 835702760 835702823
    0xb010e06030c0108041106040803030108030d05011203080613021b031e071a1306110315030303060607142107051b09011e0f060207031703040b0118090807 68
    0xb84100d9030b1520000301110401070004001004009401156856900944000e0440c40b01640d440e0340e1280c0034190340f50044003031a109142014000aa460305240b0006811501030303560740c059030345000612002111002000741415400c004040c0403205600d5000500c1c418040959603404083c1901d6880c55410318522003922400c00c15140010000454001c40e03a1982500c0728850361026035007142c8007107100d000f4240340d09248102e0006085034000b11300c2550201080e0304e025a14a084c1a175a001c11101d15170014410803030310022400300448151651403441c1150146000c1010704131641300740c8101810351000c0072880008001c0309101c0e4240041303807001940d00e003803d01c1000828043d810f109080103c0e0b03601098035541c8032071074109006003a030f4568007141e9550303500000350389200f1484250b40600d55411050b00102d90003003141e0188e86c01041a1035640d00b0311441c01a00402e0508101071103948001c0a400180c10b00e0162022500400844090700c0c004d416410b40c03c008031a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 835705260 1250 835704010 835704013
    0x90603051b0306070f03090b0f0103030f14160f120e1c0b0f0601050706090302060711010203061e030f0a0b0604060602030309122d07030e060304080a03020a1205040b010e0603 77
    0x121500c1ca40380050803507402a840d140000c01c40d44185001d900a03d01e94101601c0c2d00c10000030003665802d4a03850754101c0e480390741c0e007a90b800300b46001110f03110000380006400e18410080100034000d0039401090242c05024442100801d65403090700340c01140d0a03440c041900420a40c00500d08481401e0003200d844180c0780d2042915034502181000080014040d410110045940743c2d1090b0140d41c5800c0e0700090030070030784913542401b0303648980072151840010f40707480311017036524018000e41c2d01504d0b0190041c84403400c50454042d15004864032141c06219203030045244d0401009400b118601407004030480307041200c04d01040d03c03443d80144003594410002d01056600c0082e445e200b00c3e50460089480b42100c423852920b010100c04042c0ea1000c0e5a00c46051000c24100280102d51094858000700750240040c0407160004507800707410401c080c050403039214040d03001040224642d20303103064200c0404014104860041e14142d685807030102c010701900718889000d03508002c0c201c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 835706510 1250 835705260 835705303
    0x1512051005070c0c0b0304061b030902031b0f240310210f030c111809060a06050105040b0309070b04090911010201151703040509070f02011503032c060409060305 71
    0x101c51924444c441d02c80c2c42e1950701c00000040c14400300e035100511a6402000b04804c90b200820001d0180000d40e400764864003a00d044150343e89a1004030010944000c1e0402e51300d041c0c040b08010405202c804000204002a00342c145000c0d01a00118441c0c0284680044a81c1c102000c3d401c02c12011349400c00e4445203268190b01198145005203403455142c9402201d8254925280e5030f0980710416294201c0301000660351090041440c031751081c0600800c4030155a28104980300b50380303042c840c20b8041a41000148a99040d100c000c6501020760003c4910640e80d498a5080903400f55105905481d40c80140104005143e00003d003082070900c002d00c021342040c4442d0400071901c1c42000c61044440e0805030f2448814007c1e60001c000040050343d0501d005000603040c40c0f001c2c0300303440040d4640803801d042d80c2425140d00302501e0305651454207801240358000446800b46454031041941031580310915900e00b4014005854103a501203607080c6549070045c81c05d50072460140c80d441800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 835707760 1250 835706510 835706513
    0x180f030a08010902070c05030f0d080a110a0807030608070b09041505010e01050a0c05031315050304150e0f0a031e050906180d170405010f02011e1512051005070c 71
    0x1e105503054030f412040c01640d50400e803506229940443d40030b180c15004000c2046540140410040c5d11200151295205582d8080560088902d20361446205031024402e14a10398407805400d94040c0e0503007400102c607911041c0c40c0340740440d00d500000d0064030004075500d181c00c0c1809500500c100c80000804010b050400103090840c095514904001020900594840c810b2070111080c0390000103517690703007542141105031302607103001c0c1c4500250241015084107101e1011280300c0c82d080480c401c2e0308454110040050040f003a100e140340c2c0b152103541d1400c1103044c84504c0500b4825220030b003190034083c560002e01426021200140001807050754100c0c0c403907504075900c50125801503400440c07800c00183c200b580710036001d0078801c1040745900c050380c4040f00410658500741c0302c1c07450301c0082017022070036203000d0300103102d04900400344003652180b15044215a8100c04800201c40703600d540e86a5000308070942c0030388181d840041d65856070304031803042c503421088a2602c46c003a45140d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 835709010 1250 835707760 835707767
    0x21031205040f1119080d031b020303151f18050d0209010510020f0303040609020f041e051b2a06090d0e040b04020705010e010609020c0709091406180f030a 68
    0x200003010708901e80b0000000302c03c1e1348043e1490350240c04000d40842c00c40d11416003030b41d9400c01c00305c1440801e1070402d45940381146281c410319143c3c9203900461543e41c2d41c0d858050075044414080303810061103070080e03060a07010912481080c0e207680d2000c144d0100485c03402e00e941c24a40c0040d0145071402601009a141e1070b5500381915420344034000000d40345d41040340341104242d03a40100d0700001c03040c0400c0048a03082001180d008860041c8804200400c020844591100400340300030740c41d01e0b00350726802c03a420581c0d210f60048411a41001c5450003814940c0c01411078425030032807000305042101040003031040c4d0003808001401070745803103684941d64800b1092414241300c0c0408a0015079550b0b41c001044001e00940150345440151608502074114a00140c03800d5003070080c0852541d01c50302c00e5800507101c440041c100c45140c4219031000f4800c0f03010907a042c019590303000003846010402136002d1074088460f0301c0e04181a1b82c1203410540314184040268008002c1070f60000c0d407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 835710260 1250 835709010 835709033
    0xb04050919050705100c03090602060f270601060306170102092d100903031d1c050a02120303040c0806060d02040e0c0a1410030e03030703152103120504 67
    0x61070980c0c4280c100d0703040c21841c2804503400030b640014003240c11000c40c2e901190340e41c1d450348640c6410300d074251521026600c3d1202101e0380c0701c0b60750284e800500340315170410781d913030303007001c0b0842c0032600c5c500c44c011014140b6030700340c2220b408a40c8580082040c0142000d0013500491200021402c141030f04c40007480a040c8640e0740c80400c01e09440c009888001006000d201000041489420310014240601181010303c03098002c40c000c010361342440c040582000f46841c500501848002035690b046074650b41e10768109031140e1040d0300c0b14a0042c2c495182803040c008a10008586925245c5032503242d403000f80e005220550811070501c2a01d0710303100c40184c0302da54102c50229121005490681c0380082c0700300700036401001a0700005141996a002d0407002205072200000c98110080503401e03101c0220260105500820002c0c1c40180309501034480c0300c10070322500e401c495403443d0501806280c40c5044010201806d10740040607007040061031120644001400207162030b484880103204e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 835711510 1250 835710260 835710283
    0x6060f19080127081e0c07060e0406120201090501123b0a151a06030a140105060a120c02010b060f030a0c0806060a030c2c2e05180405011401030b040509 67
    0x60fa500d2100280135245c40c2a10031800c64a011a1112075035904020021151010054000c9103010008541e00c0324140382e010110b501078591040507840c0500441c0e416a030541a60751055172980e1141188103240c10564451050701100b50500700f00a070307442d074594860004680290b100c2242d0034001003059032603d1811010752000102120910310410204140002650f401980001040140b081c6644170100404907090f81e00b0460707880b402070181c5481408031010200d4a1556a24074a4070305400220b07554590f48008544145050045082a00050140305604002000700020b09100341f05a20042c6502e141284d030314184800490301911079240084105521814000000390080341c95007260203041e200c03c4003c03004c08a645101c034109001503803103038006144691544101e2644100300c8010498100708400d00c0d030605452603403000072080c003201c0b1f400c65201c0c1c10f5a1507100307503030081800c204407010400007180010115200003040c50300c503c0c81c003418444889000144111a80d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 835712760 1250 835711510 835711537
    0xc03060f0909051011180307060e06070f0218090d1b03032c2d0601060f0e09070801140d051b011103071208090106060206060f1908012708 61
    0x1c504034140241014030b40c8441404d1141001c40c814541c2c2d5200b0000c10302c5110b21141e801d498008007040548403043d510620b000291540c00110f02413500c80300421a062284000c510811141e0f804100c0904120030040c81082c0c52a08001d2000c606100707214803200180303402003424101d02c0340505221450300c00034007090380d00d0f00b0404d032260000c80b1102d2200310050300a5504888103642560340c1d580031203252108002d029140b06004402008191100d20400142040c4c0c0e003003060454010300622988020032144140c00d141c59200c2000250280c02e2540c4c034442c0359810001c46100101c11160094014850582480e01044000c61454035541c00161000488442ca10040768469200801c661042c040055000208004010b520018101c1500e407441c00d40e41c0c10550341d08850703044c4104c00140e00580d00055040ca40381e50118620440100140d031001114869000313058200e40241419a64412071003004801d82d158204014142c990100d04032703600b55680ca5001d0040e801040402c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 835714010 1250 835712760 835712771
    0x130c080f060720060108010b0a0806060a090203060d121706030d0819060b040e0108070b180904080c0d0206271507020f0d030609140f060909031605100c03060f09 71
    0x43d42083c8840c0280b00203180c0c12a0900e5850b5216076000301b42d14112140700310308002001810040108006200320401044281e00d0b91409401d08043e41c401809981e01502d0400c0420016100d0312011944002c684c0d1079010032201c0214410343c0d0301010701014800e501220880c0d5515501007140e41d40000b58484010400c0800c140391406400203070002c10003040089000710341181c0104289048a80082c1150060b603900c1a8290141c45148161082199818906010b5045c076a8145400c584a07450840c600300b00d465400c0d0403c40e80b00040401030700448140100d03440302104401c84170441c21004a04030900310190740d40c0b00e644002a410300c081410000b1901d50092100d01c481101104c1611080414100010000c04460017400c4086203800a001c00c007885a0440d51300c00c0012100c034580c41e44034207003000080b08004007210aa803108000002050000f44406019688110001c003840c964400000d01600c85200c04642010301e062800c1100d15004007030101102c4051200080e07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 835715260 1250 835714010 835714037
    0x20412020f19290c15040c12080c0d0806031519020703090608160c020105161e0209130b0103020607050109050d08150d030206071412130c080f0607 65
    0x105090400e250010650000d500046a20f2003066458060300d18910740340355034241104480d2a4025944501401d41c001900340b004c04003a81403154006010b2a0382c51542c030b0380c4440400c13201c05441d80072900b0450100b40c00075409802c2003444843c4e401428442002d1600b0310101b59150100505017038201c840d40c0c04648881d409801112080008801c20b5554980c203040280c84c50710303e4800d4800045006000039100b080310300700d1680050866543c0d0000f01225001103807031f600300301d042c074006041e840d80da2000121301c030404488403401c86216000d2084070f801001356242c1d0003401100c0d0020310344039410004c0c0c64851610b065030390440740b854031010385003071041c01003a101c08010aa03106104401d00d8087c0c112000304e11510111460080349001c0405000c12100005402400360340481c000c280f00a025031301c150b01d40032030380d04903c0c145160043c0c00c80c2d5004054948003d100d0001039000709108282c040c0340c0c041e08011004003101909807040c41ea4400c001420b4504200010a4004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 835716510 1250 835715260 835715269
    0x1031709060d0212010302090c0f0423040f050106140906071713031a0106020f0d08070c0606090c17010e13030309140c09010f060905060c210c010c03020412020f 71
    0x88102d46400c10441d01c0e80103980042c40382d40000e00041e81b0410308031002481000706141152003065172400d070103080c00e203010a60913080c40748040f018142c0b10031b041c00c1031041e10345108034840414281d40126041d490000023800740c4000284550a0340d004020503411515490101c452040e804850b820150111412021150041202ea2070020032004000002c0c001140606803111301c503460300d050b459a81744001d907515104d444c0f850045410412407043d003103000301e548aa111666041081803507503141c2e5800e04842c00c6400845169a0b10040402455400418230440f00c000d4200d00d085541044528041c84200800c0e00f0940308100046400300362080d0403205030f0590010020131400580c680c40d0351220a05911359015484003000000c01008010750075045807183e40780c0c00d1410342004140840c603806904000442c1c4140c488210446141141014141c00c0b0070502070345072202c003400c66081d81c2448400808050050109102c511000014104455030440340d6142100b610320104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 835717760 1250 835716510 835716517
    0x9052202120a0501090524040b0102030c01060303031505030f06040b0411060301060816020c0117060d17040f060503061e121903081f0b1e0703030b03010e01050103170906 75
    0x44581c1d00c0001c00e00040d0125604203c1c10f0302c20f889070620041d6102c07215002449401e2039481008090000740070f40c43e0510781c0c803001c0381c2d260601c117580c50b0142d100700090a450072640100d000036525100c1480123940c100c03c94000c0d14044000d00080301054a42598400c4050310181820440790701107801c200314000c8229a200c0d01405582c0c8a41c0e41d030001400720607080310b00c08080500c410402159500c00319a8056078a416161400125501c8400c0e0075030010003402190000d06080d52280031900040e2140e00c500d0742c132444241c0c1d40e82820007840d416201031b0b002c481480400d0090119541c0c41c0500981c02d100f00440240c4080c81c0c440001e500715407014075a401d58043d4110304a038a031110581900c2180c003980700c0104607112400342d00c100f03400e211010510b00c42c0c00303c014402c5034000002000c80c2c20201e10345d07560403a41011906013503801110101c01282d0769900044c05400c00b800f80a10b0441280020015585140c8070180c00c4040e140302841e04520018810400340d40d0501035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 835719010 1250 835717760 835717777
    0x6060408060c132402010f2a031401080c150a020c04020a0e09040305031807080316030c051b04061d071404030803040b0a0509030c1f1b09140109052202 67
    0x2400c4c410b104c1c1c100e0a03c1c0e8500790714407070001035081c000c50407640300da18042e5010039207608003d0a000d26000c0080a4200a00550a402c140e11241e00011050558500602038001c1d580a0020042c100d810044021a040f04580403900184528850f094010840100389901030380c0140e81d03084040411503159800c020929402041e00c424402416801005184145070b480a0780d010300c05038200043c0d8401103845514031543c030810000c48000c00200c00002a54441e06044040401075580c05041004640488040ea4451410000c41d45030901485000b400a41e1002d0400300031020840704080f0300400e000140130a4525601000c511070342250011604032803e9130702da0a2500d001403084c0003d0b42e084c80e8280c10b08000c10340310b0502008403400000260006d200b605545045c00014181e8204900300043c2d5580d684000d00301c48402d5000c03a031440d80c3d80c0c01d142a051a01402616003845100c1c0d04002c3c61590034056078684140d04400064004540c040640404040704068400c6c0c0d2407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 835720260 1250 835719010 835719029
    0x50d080c0c0d02070501020106050402041404021b0d03470111100618020903060f06060d050a0b010f0f090614041212021908070f05010b060a02070e06060408060c13 72
    0x2c0410095400f0070220142ca800341c0c020b010302d50307a480800c81640528084c8010002c0c8814291a40d032800d44e00501b080e01140303e0740c01075940003c02d100c0c20090fa400c00310707020176112000740148640b07158181c8810300d4030000c900c1d0316400030f00e000b604910040d003101c0100410004c5401050b8000e150011022505030704a4840c06544100306014206030701c602000100a510031a07640c112a0080d40e40030780010b00105101d968003000004840c1004c1c007000c2e08102c04101491815000d4004c1350b104e8500c010010460700044000180341c2619003545000704041c480316184859880010901110010700c0d104041d111400c800c2030a0341f08030341c00700c841128400300d4171040000d4014290f5100100c4d03003c0d80d060b403211541042c4000385000008242c103c00300007010008140d00da051000358000e40002607614141800300d406540710200c0c200251740300607001c20240450700d88455100505841160030a480e11444558a0300090041d00da07410300410800b219100000c0203200800c058034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 835721510 1250 835720260 835720273
    0x509030c0603130b1602030901140d050a02090f09060604050d02030f0a0f1a1003080c0a0507030309090b01050c030d1d2e020c07031401060b030f060a12050d080c0c 72
    0x1559a1012841c3c1030040f0380c2500a500001e290303840601c01121851640c2d009145012070a00044800f9107200d4030545000c0310034030203a51840c1540c41610b108900d9148010303510f0820800b00400a9000c5428500c102002e000300130701d58507072400361402c9480540da400341620040c80000d05240201d0140b82080c41654940c0c0305100300c000c1480c02c814011070360f00300c03440388810501c0c0c40100e0403100c2380c07103a4038801d170100000b418440003403010700d00000c1914a144443d5803640d040c41c03103e80c42540003403189241849040380c81c0c401c1c810f1492090800901c0d102040c28003645a01032180400780382e0b984c540aa82c0b520301101c0b030b0086802c0c007040540b64400456285030b12800d0781101b15501e04103003280442040401032007101c00000d40e80c0002c1840614550b14607009950040154100c3d548403400010f51480f0080178600403801c0a0801e00249040c0041c0303da21103041d4018284042501100d0b404210f0101d5071140341002e91500c0c15035980d407245040c12501c03481c04002c040388611b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 835722760 1250 835721510 835721521
    0xc030d030c0e0d15270201140f030f060114070c0b0304020a08070602031207030c2309040e010207061407051c02040b07031d01080c121503070f031205070f02010509030c0603 76
    0x1a01100711300c0300070400b0030422001321004408004001481e80201d24080046000740d03020351040801e108411203038919220303421800001c80d80054549030b07840310b0131209100f01580c000340c03000c14043c8040d00c014246506038481400c500024031554214800020208065441d00c01181c400381c6440c034119400c241e92400025a00e500074000c607500048080003140e06140300c0e024040031880703140c0d9401c5018103411007040c0c00354195011080c109030100403002094a40d4054500c5550700d440005845500f241090016652140d0018030206024030810680c590010207440e1100100341858180c4102004658001e20458014030400c3d54003181d40d00805038030050f6001100402510b0028150b0b4410041d5550007017980c00d400c500f0414011840d0000008100c142d0028503581041c226036002030102c1e040c000d0315000318810300c00104061003841008146180c03081d0007450710034540510b6403941d148107170449c100203041103800502620340d66401c1203096002c3c05c00401c0c60342c0d2400d12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 835724010 1250 835722760 835722773
    0x20705100501060c11190302011b0506010803090909010c0915090819110a0b030a0e0c1008071b0c050f060904050c0406091d0a2301140a080c030d030c0e0d 68
    0x401e080343e51088000c600c0010703040101402c40846c0c2003a50706510380307007140d00550302d03071700340c1c1d505c0d4031020303112500000128908100950081c51a0009140c0d1850304400b4800c03a600b00030010910350b810318400c480d485034819404801c840c00d900c8a5204540710402c110740f0706001d40d001c200c0520a6144e0500c07284400440301004031703c190074000044660a044c03007000c43c4075200d54050f00d80107000080011849801c8514280c07050f0741034421007982040040c04c5010f0903414203001582d0b03082000541900400b0380002c0040354010403840d004140e0354903006030000e004590081d030b202c900140a80c2c503040162900008020410300803407810640d06103c541092007007000043c001c000000c0c9806a48070a8181a481907880c000141e4651043c100070300000c000c1003038012070013542a01c840c210007441e58040d100038481650104040420850421295001f508881c6c02000e600c1b0119600010b2181d1002c04a0030042141551203000380c0c0c0004c2036542c4c00780c02819007007184041160 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 835725260 1250 835724010 835724027
    0x31a01090605040b010c0809030709110c160e1914071e0c0b0609090304080d0215070e030607080c0f0703030501030515060303030403110307020d0f1115090402070510050106 76
    0x41403001c00045a450040200743e407092000d03c2c0c003080c480385102000ca000040202411080602103031511540d50b081041152040c04142243d00c901181000518200380000c0c0c80d540e80050310f4031581810000c03041103500003d0400365120300c4c1d0b21a0403c0c000b049030021042040301e085c00101c0361030441d4010340368400c41c070010400340000c0d50401400c1e5000700d0b05804040e82006c0c42d070321141d560310180035404001070b000711020b01c01403200150f155403c008808900919a01802c504e55494140c42e40c2e03100b000d0704010611410881808a0303403000141c050b4000c0103840d0080103600c5038081c110040c49040100344c992007000481e001810b400d604028100d0303103c0d004890380340089400d69522030700103480d0164160010000f280100380709000c5c490040940206980c94040180e000800009124004440d1915080f5100742800324503506811000401d8509074442071660100902c90b00c039602c401407140e0f9022035041e060000c00c120140c800c80c41240300700315a58507030310302408594 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 835726510 1250 835725260 835725269
    0x2c010e04140610050d020301090605010f1806180b010c0c080d0207091a060d1104181d030d0c050705060a0b100302040b0418020915030717010e1f031a01 67
    0x22041c0300c1c0342100d040c001481c0c038418881a624041d00f9400c0108110318040e00c1203060303900d503486503007000c085000c7d84201030091440d00040021103181c100820001417060340c040c0708052801da03081001c00e039081c8410011a9401100080c81c1c005c04005032014070900a000e44291445c3d800811007107000107003801c00420035021980b82e50383e2599518140d801c005404601d00b42c082d2051107142c10b006020f405111040040440c0011000c01e55205a03040359001e481e229641911030100003800384100c0d0603000010b46040d00b8018140c0f09240e80388155030130800703a542d40b003881e00344051040040d5443c007a4044144c60304d40c10102c1040001d0807012410302d204610000030040c01d41d02a1080b0b90440d0550747d4524100f03440c19002c02401807009a852807102d400308207102c801e5442c480701b100908120a50280c9906107050020040814100512400081200140158100c0e01880c1d82c0c40769441c00c448004c21481c02c20f5105850155000400e14000c14802d081d09004000c2c4044c10798 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835727760 1250 835726510 835726523
    0x90604381e06040510051e0d060b28020f060906060f0a03200d02040e070f0906030f060513150902010e090c0a11010b0d08031009090302072c010e04 65
    0x2560545680c03001071800c180700307980840208420041d9091144030f403c00400ca909006041280c030308030400c50804d0544081c04c050000080108911202d841100050f11541003404d08002c1d0f01c0402d95114a951510f0a24100f10b00a6445400b4400c02a10800c0540802550114107101c11960740d0307801c081c1c0e1400d10848140d01041e0700d50600f500000c3c1180d0b04100404260f840859050442101951006030013250b103480c5030700583c6079800740c1803c9803d28401032000c24680b0007440089415500403050b082c2c140a0100085410488407422460304260002626220175502c0076804200440c010162801d041d118902c40c21298403038a0403034003c0c0c0f19107200100006c00c100e6002800c0300d40603107010051283c4501d55100300414850840c844000040300303802c060025400c0002c80300d0854142c00000204403505103101407030b0004010808007482140b0031039802944a06583c001d140d10f5481002076a1020b007208800da0f2185a1407010030307211540c455408208600c0b0854041d40d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 835729010 1250 835727760 835727779
    0x4020f04080d051e130b04031a07080603120c0106031a0a06150804030f020c032e09050a2603040f050c09161206080609011e050609060438 61
    0x603074024001c5504440d4800303100c0603400d20308a09104c158020030420018a04046000310346001030380014000345014800c0c04082d105107503255108483c0046c4080100101b25060140a48000401508220071842c02a455510307000080f401400a940041c03c00340703c41507907504114450000e02e002d01962a018820242c03070b034102c510501c19035029540058a60780000f00424854101d501e2410b42e603105844000c120a0006490065495070180348148001001505115540c1004481400a0b0742c00d2160700c0c0301d500d5283d02c4940046016080c80d90a07860850310511403001c44510703071020403a158503410300c1c0c100003440001c0071500701c80c02c4c8210556010a03180c100a0207120341d00b83e001420200514a100721a2126550a020300d007035100c10001c110b01c1002e0083c14440c4100c600001041c491518a4001d40c20140ea200202d85152805209954442a44036903001c0020784001c0fa6482903010740702c0083d0220b0151405009024200c148a82103001c18102006030440e800b840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 835730260 1250 835729010 835729033
    0x6090d2a050102100920030a0b1006020c0a0b030c0a1101090f060b1905060a0c1a07020d0c0506061903080309150606040f0306051017061b0306060d0f060504020f0408 73
    0x4440c024003011705100c01d81b102d109854500130080155180e800f4050f54141070444e543d441c4103010644000704449200407084c0b142a6041042d0f100400085038442c484510700341c2c80d540588009000d856400c440018070500807406100843d1003801480020040c2d1540c03801c20309418200910202c403040e0a02d140161103140540400c0d940c51034658940d0300380751810b4200400c6070f116110741c009003c219140c00000c1041140ba18120254110a590180c0352042000b400d0840080d644d500b48107400e2202e01c0032a00000d8800e07842482034440152003047c0e800d0101c401007042c1c2c00280340c2c400000c200006c902000c11401a1002d0782c039a08072560f1101ea08204081c01a0b000300c000c50054402d08001248058001700e070025400e1b0b003a210075949662005120440862100c3d4a503072142381030110401518842083d0790548465640c114280346000070882d2282d5120056100d40750820369186a440e98080401044020001c55075250850004076160300203114002e818003501807400d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 835731510 1250 835730260 835730293
    0x50d1b050607030f0e03070513090203210a08070216091d1906021b07260303060108070c1b06022b05120c04030f060209040c030b06090d2a050102 64
    0x1810143c0c07585440004000c0503204a900206070390f00c1550501c507440700015a03850710007144078061040940070070000c0e098018136142143e81d100c121850302c410359031400c420185030243c82443c02c00346002c61007611030280c00c9160014444444100c500c824500094803405580005c0345140364094605040f9640b001703c03515004840581e01c0901c081d5480400040c03c01c1d801004842415241c0301e030940b665528042c03030180c2942211480c103c245a940e03400a40d8106c091002280c1c80c40194698945040000e0190401400b0f440901402c012058100610744100c54003c004110850b2031701652402c1c02940d401020382e01c2c0b080446444602c2800a180d080d91504d13400c0c041d1100c6107018480c00c80c00d910703640000c00a88184030305000c00300006d8040042048210701442c40561250611420070044a00c001060710a06150652004d079031740f565005e9849a001c1100c00b00c0d0500305604207151928100402c41820309001420f205516181c08004000e40f4070aa084500f40120024000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 835732760 1250 835731510 835731517
    0x1050f0d08040b28091e05130b01033b07030c060e030a060e010501260c15040909080a020f15012112030f0e0c010c0f02030106050d1b0506 61
    0xe04034001c20007061006403441030003043d40700312a2046115038245031203044400e0455031410000115a40000c00044288044036000010455510040c19241c00e000802550050001480c90340d203900c85900d40c0c1e030003a408207101040d0400107155030381c20154010036150221f2141001c030480480c442595180004202041d00c3d4041110b8000c02d041400031741e0325144007407c080e8188907800003e80040c0b081d000d0b401c3c1601c114000403801d035041400e20b071815049001c5503896002100741c00003a288000541c40700d0b50740f09641c28450380c00d50a064844ca03100326080201c1240c05c041080d01002404002403c40309582c0e030a0724811030121070001d132195003020803010a030a0314001444200c10500d100100c61641c0d40810400120540d10340010350641c0e004400840e5681d000d10458107214090010580103540c00380c001061180b00181104c040310b03078041c0180d0795a590718002c5441c04d600902c041d01004200440710b0201d440d2546d10560501c854041d41d0b0200a0001420309044065 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 835734010 1250 835732760 835732763
    0xf0913031e05030426040308030f16050703030b060f18190501020601030b1e07110106140a030303020904020717130906060503010e072a0201081005010503042405070801050f0d 77
    0x102071440e140c035110303040c81405d40aa001c032082481c10150118103581030013040154402d204031601d80c07400d50074012420000510742c032841c0841942d10f030b5925911100b144c84481d41410700048400001d0045003460241c03a00741c03c0308180c001007054402010341f6110041c100219200424040301c090280c010524521030140581e000000600029410510642e0321044c09408407400c003e0f240c6161800903c150307a10070105034841359920750b80c807081c0581030107000070f10340700e10f500c0001601252400805110140c20180d001c1080f810303590740c7da012103290b56040260b070103900741c000f8041d82056001110000110b200c41c400054811010b0103942d0445005849081c00c42e0710300802c02c0421503004100004100b20440001381c0303002c0780c00c0e4180c10850b10030706003aa40f03100343c40054895040949400c1c1c000035811420003840c0e03840700440c7d42c89a4085000b41c40c200d800c0c42e090560444ca94400e810881c185800c00041c0390380f1010b0b05d4101c81c0308440c81800003c001d001d20820580c43d803030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 835735260 1250 835734010 835734017
    0x150e030111091507050a0515010302030d030e0c04090606050316170a110103050a0b030a0323120103020616080703080a11030f040308060a170a0b0f07050702040504020f0913031e 78
    0x14400743c802103040182036502d01907416601210055561ba90901905c0e103250107058280070014410350404001c29507401c00c590504101c20b04a480724070340c1d10507920421521079a1141040030810901f900524010403001d0111a050140d5290800c0b88201c80d00070407142c03c2001e401000955000500402601c1d0494039100000001800450141600406107900d00d5200c07412040607480421140304403601a5403001540c6010b84945958221820f80b82e450043c410f00218202d00d50030100141100c0e4110760751603603405d9140d103c500c82d400c12800502803500121b4808140f640021407a8400c2c0480181040a000c0341d00300380d1401c3c08169424513002c000400041c00280c0034040103500660010442d000165a980a0306450001e1070449000c50304074060990801c60318000c0c00f608915248032411007441e04080c0184517008202010344910344402c0890b00755124402c103648810009000500b09240101002c4000000580c044000406501d5031100c80351003150605a0300040c1c1d80d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 835736510 1250 835735260 835735279
    0x627010c031704030c05160620070b0c1501060206040c051516050705040e1b01020f03071205040f08160f050d0b06031212011e0e011707150e03011109 66
    0x1000d104000380700401c21802c5c8440030b049070010840030091085845803150f0100099800e20344000c0829515031580792049080410a00480d4008200ca030b05890040080302c0c1c40c0c1c5030012000b450081d80d500120001c1c8010340001c10320a601080407031095000c1c20500756026582c07018402101205615241402c0d018003030071140352102c1c0001c41d016401842200c00c0c8603202c2002030f00302c4a400b14200e915500c404848480701c0d030820b0150b4140c82c401d001400741d00d005a0402c076242d1250400c0180a0a8804002410303140214141c6004d49000851034541e903884440c1c03544d440e03070b50b40c54003c0c00c21415040041c040140c1c00a0f141501c03c043d00014481c20319a41e2600148005013040340d16010b04680b0790018040c00e07003d000070700c1483c01c24400d254541908140c200c00554003c0140703241c0c402c801c0c4000d03400b130f0b001c450440b0066a000b5014803803421303800f070078014075030845005041c4c2e200b0766006c010b80c04000000603103030450080000c00352022b4805214440c0c100e42c45d4000721840d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 835737760 1250 835736510 835736537
    0x61d1207030f051305030f07090e030906221e06020f0f0304140604120305071505010b0703120b030a06020d0612020d02040c050d020309030d050903070b180c0627010c03 74
    0x81001e49104003203e04903213406900c44001900b402440c0a886159600c20542000060303250700607040c81d101d21340051403900d048030001c5070052080240050482d05240b50300d6485040f4a6020f00c000c0500301c1411400307110680303226890291512a100040c80b0f6085440110000800c0702101c00724940004e52400703141c01450440c5211111960b40d2004042c0000900c0200001300740d241d8500c299a400d42d00c81452901030018001c81481c04e0020303107010300502408080d5002c4550150b0181449810b035130207541000c004d072400417840d80d09406201c07040300410145070050b1280a204140038486546c6445603068140d00b207031006544004044000c102504090784040b004080a140c9a8038010649100d28141e906c00c0d64552001c2c0d100090031400c51110b131040130381110b120409140741c0002a16480548074014059250541c40941d885d10541007c200160b96100054182034950102d010410840200e170901610541802a000040e5620448000301d001c0d40c0b648654100342d041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 835739010 1250 835737760 835737767
    0x15011106220501060f090c090b0304170702120c0108091212181b090708010506070b07050912030409230c0a03090c0b09042a0c060207061d1207030f 65
    0x107203140e210122122150000465428012000078103000348441d016a41381c0b0b0b50b5030040b101d02802d000200300c0001001c0c0041c4103140c04581d04150000344400544a080b1850016032050f110000d40c060007000816001c5080130510035008a400d81340c2040d90f545d69007a040d200c4200110b20085030304100001c4180b00020100710703810480e2004048400d0250b031030090300d000d4007407070000c0700ba81100c8001a00c80c07a0000c2d60b070354401161f191003504c9508d88008990305024030b0070000e00c07000c003c50028401c0742c42070055880703100c0020014040a078460311561b460342e00c1401003078101030512003e140060001c00c86a8005c1c10708001c00612940e03003102d401801c0d002031000e10205a202c2e06907a021070010340040024200000009544002d4001008200c03100307601c4409400182d50711040440074648400019030b001400c02444035822458154028412624001d100500e41203040d808140a5103540d44a1404501225514844605c5120aa000d600350040c00940d02c110400f00c62480f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 835740260 1250 835739010 835739041
    0x92d050106171003050105010806091b0a03020f15030a2007020609280b2503140a0e060301150f020109051902060d1b180506040e19020a02010515011106 67
    0x6001544411507213139501c081c00e413030082e80040740d07a41c85001407040003142442148081402c0c10411403001c000c400c003003144c0e8074503448081e104100304001c440c0241c56034001c44201c030410413116562032800381c240b10001c10f04034404001d010356802c814414901ca0108652603550010001801c04070fa038800c01003120400c0030310040344d10b00d00c4003100c0c44401e035240000140146180a03a101c5000c1c028461001111103070610f4880604040b100100f80c000c98220440007008403400d640d04601102960106214040a600300d9000400040c070789111031444d289001503640c642c0ca2401d80c0311300c103d080c0d801440c80a419508220107400c00e402c02c0c00e1403440014401780942d8109030204122600b10350f00482802100310349400190b913410f034000b440b0460544011000c0c40c480e03092101042c01401a8003072483d54064640201d1880f0200e406c080300d6400407100255501c0d40900e80c028040c7c8420303542c40c481205101d40c00b2101d0341c0585084080c081c1624010030383c90b074424146050151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 835741510 1250 835740260 835740271
    0x6030609132108041406100b031017072c0105060702150c0a0215070f060506150403110a051806040c050903030406031b0302040f0e070306092d05010617 67
    0xc0700103180b940c94410310080400204041d4035030440514103410000c0383e44060181880791504420f0422910121184121080d80c05031070700d40303480f65a40c00c0e102461800369041464001d07607040d400c02000b0343c00241003003903850484410f031207200e00c4444191095080c4041c00c0801034100014411420410003900c00703a80000c0014040288086220449501420110189030880d690070025401c20b0704001c0d0800e030440450502d0000e039030311034540c9040c00e8040141a1a2541c0100382d159941d4002419022008020913a0f52079591512a0007a0316031743c01540144100e80001403140b6010400503211070b506040800a42d0322031b000c110081030041c0201044c010140b02030402d54a0400c00b80c0f0180045440000d010b03800c002403507103a040304804010806004100034080000c0c8810302000b107902545030406a622604000da000d81101e070070060816241c5070484002201d4035007504c1415000250f030b082881c402d082c088040c3d803001d0140b500403948ac0c81c4d0080d8125583c1580a80c0807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 835742760 1250 835741510 835741523
    0x909020f0612041a06030a030c0c0305030406050c06010503060105060415020723030106080c0607030c0302030702040510380d0f060b0910020604030e010e06071a07030b0603060913 79
    0x603084000010103a400600d000000003044004000c10400f02220546002c140100e0f91134a03460700380c002940c1d50764084402020000f03103140070020060030700b98038070255038081d0542c0e40b12070302c80c2002031050b0012500d8049510941c5c0000a440c103010a8603416100040c082c189000c2c2000d40800d21000c0540c030f01411403085140010300300460004800312203504880c51011020200d08043c03c0d02c0d040c1e0080d51079030700940f011a8541c0c0d0b40e48100c40750641d240c181104012a1410160b0a50250f0000a908241881c003001014000c00c2160000c0e070783c1e0a05034a030301c0b080c1e107a242024040c858030340d903680c1d40700040c030101c9005a4201410400c00305100c007007800303a2801c2410301540c0c036551040100c1040403e003c2024030b000302c0c200080f2802440180344520700307500e0051502260280a505108404040c48070a44031841190704040c0c10043c4000281c1045024684c000004c59007403001925014404000345405030449005120061082c07200d0780f00c000c80e03854424580201211b00c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 835744010 1250 835742760 835742779
    0xe06130c110604080d063c1203030213270b150403060b030d2d2a0c0609030803190b1905090c07030503040f0212010e2a0102030301090902 61
    0xd104200582e0780f14034842e514894803143c60504400a84d482a0840004150203139100340b001d00e56400812084d0b01c2418840400026241c041501d00400d134204c0c240340c0c01c0b01c11448080c541c051b0024442545103414824160741d60f4240301c01514401000200300400140c010803503030f2410380080320013072001032603802c6049900d0680d105540c401d80c02254490344500303800c40545000d000b01c21a40c1c0440c2001c104c2d0401c0134910707080052900b040d550100921082100ca000d21541c03014045401082c007070401050760a81c40380d10319030b400c84115200d014403c00490710038410300300801100c1e0700895444c05c41c0c80316101040021006640384140f150759100141c1690380c1c4038800c40e0010114181120720300e003403109200541800030034101201800b0000d520000390f10508583e8402c1e004507038540740d14050300c006203031403242d5000c540256090401d1904030040210316021808410100070740190010383c000403543c0c0d08000000c0c09600240010000c4070143d401c04c0002c1440200040701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 835745260 1250 835744010 835744037
    0x10e0111070929010c120e2106010603180201030504051c11060907050913020f04020f0a030b041b050307020a0b0c0715050603030301060507020f0303040e100e06130c 73
    0x341c00603551141100340d8442011210082c900d071070b101c0c038010f80e0070700b032000c01e28888002030100680004000d05c40c03040d0020310144507200e801c0070042c914004101400070743c481c590103010302ca1203201e11003180c0186070002500300d0003403069503500800300c1441d80080c5041d070019002010000d1003030300c40e07004800921040c2d262150200040e1a010b4580802c0c1e8000f50310018034200d4024420600c0e6400300b54207216554070000810b600000c61001100e80c00c1e190b00c0410303000c040c3d8010003034006002040d40040749840320090145268555010003241146c5000c0009444030440540075604541c04100e04052156004503030100103030040f61803001c6aa0340300780c08000225044504044081020410001d4242103000c84c0c041201c41480782d41080c0001039142e00c41841780742c00b84000001c5000441d1151005450868002000e4903140ca0380c9101007a0001d0b0200e03903a000b6000001c0011580e0b20f0310328101070050b20058412080e0500c004c1e100401441059014001d0040210800c0c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 835746510 1250 835745260 835745263
    0x6161110080612011d0f07061b0b0a0f0e0105090c010305240127030b0f070918060b0409050f0f040c050f060412030e030f010605030309041a0d03081e0411010e0111 72
    0x10460045c000902450160b048124100312942e0002010040740c04035100704601d45440011240750400150340d000d850700c95050000b0907403542d40880c480d01301460030320a044190b028a20a41d40030050794141c3c0300f0400110304841c0e04440451a8144800990104162400700e2660940c0c040c144040000b4011407006080c8912808100c20708400400620130040351010080d007000124000b801142020540030305052441e001e06452175029825121200440350030100052980b241c00540c0c481c0c0328030040018180440e00d8420048a0030081100c020400d00705034811500f040100c1c4042d4140410480c00c2d010f0641010392240c028080840e65030b0040824900445c443d803140b212808484081c141401c281d0111050300742d150040800540d00c01000315500c5c58000c59000030480c481a440908018404201c00d810101c1c01e51200300309500104102d01544682026010841106540301d0903000308890081904844c80d900d260740d13502803852952440c40504201c005145540d0070103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 835747760 1250 835746510 835746551
    0x30602090409150603060606030911150d0f02040f060c4409100206100b09040f0507020604050f0303040c061206080607020c04180503270616111008061201 68
    0x30f041aa2107008104000c80b80c460000241202d080901c000311403900c4010307841c00340440c0e190007401181c1040c000144600100d0b003480c0d0010710700701300c52414207000318025001030040030f1483e08003410110b01c2e80d0140181c42480c0780e00a0815800c40c4491120001603001c04141c0c562030046403406103442154000d9800658074022100c5444883d51410425009186203005042d0740080c4103000f0000c1e04461a2001c0d91200440d8584d101071240214000b081c1c086403046030325281009002801d0741c0403030002e0146006804843c81d185182200e0340e00c920041d02d00900c1d2200090080001c00e0042c2e81c10101603402c400c0004910350303500066828030008490078401a0040c2124a0562509108480c0c98a880840c40780174903c050380c0701c943d05e02c182c003082c0d01d4801c0d0031140f081340c00d9000030b05c0501d0000080d2096031510018166000070a0148904540c2a900522a284c284c1022030280311842c003680da0301042034071003100707003c210700c000c4900d500c0c2552219842c82d1280c101c80c021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 835749010 1250 835747760 835747793
    0x60614060f131d1f080c060a0c06020a0f0809070f090b0112110405011103030f0414210304061b020604110d081605161a21040b1915030602090409 64
    0x918034a18103660814001180502e04024501d804d000510244200061b041c07141c0c2d40503100d884d5030303c9403d00709840414078800c0041c0506d00008003401c03095405044550a04000d8459400c2500c441c101d5644452040c0211a07039403008041c100f148241c9500070304160310041c1401c109400604c001e407030550320154024608441c00150810003940c0c044058800704580310040c609505103081401403011014002800d00c80c15004081e13440b1406000d842810000f8500d9104603144002c00c20b034080d003080702c054072070074900124005504c40f5581c8844454980b58041c0000b592035588804201e40c5862005801c110030600241c0000c0c0b0a4005207a00801042c40154030956442c0c0705150030f0002031100104c1d50f0b002e00c2007040d0060350242100c5143c0310720610b52a45088440c058128800003032102c0803a120109002c1800b008504443c0280c0d51071320b5404c04a0018607002d419114240d2041d4400b1611100400100c5d411394050303e0481c4005101041c6040c40b600c64034070b441d07514801c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 835750260 1250 835749010 835749059
    0x90503061609090605060d091b090c0219052508010c0804020f03120708030604020d02030703090b0709050109032d12030b0d150e07030b13060614060f13 67
    0x320070486030304481082d005044540040c441c0f5801d0602044081c0a480780c000070403078555143c031040200c400300418a00e50569904108196a808410050f01c0301c441e912016001d9184005240d10000001813443c58002000300b41004440c078030f0801d4061001074481a40300a00d1010070303003020a004003180d41d0266501d002d0341e814140100000300800c128154032079484036001c40210039208095446064022110740d031a13603185400b180c06403098101c2d007011517100104020310319406034454044140903406442c0c40d56146001501c491815015850116812120800c005109003450050350442e0062038030030550044007000c0703060126642211518000030145100039818451000c180300308945980a18003161100d0741d035040084076804d4015100c851070007040d0f40c1004013100556109010300c0707061420051a0310b605109500442d2003904003500001c8820490140e5481100003e090034079102000c1c2c4100c0407540701960358070102016a00c006821000ca400f170000c00c950040b07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 835751510 1250 835750260 835750291
    0xe07030c080a05060115020c03060c070615050108010b0a020114015d0b1f09140f04020d0b2a03040507050622031109090604050d0f09050306 62
    0x60034561a458a4000d11242e90207030300e0400100c0e5000500c0c50464000c0d1441c5c0a41c880d5900040b8241403118400542621904061019584c240f90091020f94050801081010b4240044002c1050070348035540c006180d000041c8a031080c00401080c9068550000190301035000a09c0d01c40788100b640a40d400c40e000701c03601e010a41d00003159040b04102070840642d0302000241500f542041c001360307403c83e04d841c4070000040418840b002d061440c1c00002c6090146402240d80919800e40c011404c814202020300140802c2d03d402142d45140c0490503c4000b44d61714462804800c000410503684201255050300100380c60180c8035000f00d03d14030100d031118400e00c032012009042010501c0b01c080741007007088041000030401e0720a8840803201295240052640303291107940782601c0381010500400d00104200c185c89010803928005d9444140954607810b400f52103441c00c54000e040c0340c2100c81c200343c03ca8461a4054078002207030810340056030b10340010134688030007155203082945815 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 835752760 1250 835751510 835751513
    0xa02070b1602060c04080a08031b0d0c090f14060304080715050f0609040b16020f030c0f060108070308031305031606020a1403060d030e0f040c0f030609200c010f0e0703 74
    0x10300c1211350101031556130b103142600e01040c0c00c1e990140000f0160080d00088040b51451089030f80c1d40c00e2032480c2035815519070071106c1ca03240051550a0178a004141c840d94001100440800c400044444420801c07141d2040c140500006070f00041007150480030800c040b00000d006140a5000150001000112850305058103500c000c4060801803140e0300080410000817501200558000c040c003150075048a607049050386000b01840c444500760201160b50080c1403030010741160140080012910103076a1001d12940b00e119a0101500042042001490303c0850846240c0824460000c4034a059100c80002d84490302400c0200e60036600050341440181c4c1c02100104200d01032107905145041090005101e0480740ca402001c0c0450100b2300a0750341d4074a0002d1000d160040c0c0309200f1a00305100082160039905035540c0440d14042012880441c070303118041e003101e400098499428000045c1c07515036000303041d1043e507942d00d8130b800d007645540d9802041c500c00360301c00052091a007503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 835754010 1250 835752760 835752763
    0xa1203030605090c07350706050c03070f140f0d05180c0f010e1f0503011a0306030a06020f0d090c05040605030f0a3906030507180e0a02070b1602 64
    0x7507a00480c0305450354401e2000701c52000040300d40c0306500c002808804080c000d100c1800315000e0040125848404111020400040c0014000340744290400c00042d610407035010391600003075882d2000900703074a83c0d400c0c115028140c9400b8500e2185102410310841803100400380c0c1c0510090000e1941790405d2100040c5058446480100040c001d054188400c5c8042000030404a41e090b0400401d00e03050340e15511307481c0a01082e03140340040303950003100c1c02034040d005034001c1c881c0b00c00e0000c4645504180845600540c2d01554000f0081c0560000ca51520000303900b02d22001140e010007013002900380d8490340300e003a800c00e11805031010090300d00710420080b1895a80818001e42281a9051060001181c880c6142d9070102c010400018440700c4903480501110700c2d00380c0b041803900068140c50134801c203c0c0c12901980d9052066130340303c0c58100c0c0c8a2031111147c0701520a0076a045c0004624001650740c070950301038006040c4030554840700304040080d40c10560244a404417400c10960 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 835755260 1250 835754010 835754021
    0xc111510180b1e0d02040f0f02030406020901080106020d270b0706060306060f0b04090c0c0503070312150308030f09011b0302070b180601030b130c06020c10030e030f03040c050a120303 81
    0xd18000103c0720746820010070844035164800920555640300c1d0507110700540c0e40455964080c4c070008640368034051400350000d61003a020580864a140000100e162000039426100459039940f407115441c02d030201d1a21070f220324250600c0359400700010034850801006441000d00504000c07900c149141007840840f0002e40103a03090383c144500500180c240c100031582125404040010b9580b5009411034803281c45078070051032400001100310a00da0701540c540312810800400300030500d0b050f880c0001140b12840005e00c200d0003031000070742410380c49000550000d00360001086201811001c2c0a09402c80141c810210341c0c00f04400052140700340415a02c4420344110640c4c1c100310901c3c80f59100c105220040845452000250b00d000040c072580d004a0750029401100ca0784648002c0d45800c0c284481d00c0c080c03400e51540d030301460301ca409001940682d040c0a94600455010065403a920040055032200d6210380001240e84600945100820303240180c40d1b202c2c0c0391880d00605807030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 835756510 1250 835755260 835755289
    0x6110702180a0f0b03070b0d0b0405010e15090402131d07060302210112023721110d020f1315080f28020909060a0c111510180b 56
    0x91521204c0407458500040708001d0399481c02442d070b00c502140804101600044101a42290900000088000079180120f006110003400201546104024800078480841d4040c5d4008007108400d09280036507400040280a0300d480e044250700184592450000503600550003e94005940080b0030b07100c40c501c81d040f0400319040d80042d4075011015011203013540010340301c3d0401c03135000c0c60300d60304256001702c0d0000080807844241803410405940d030103080c400e0300c103100c105103142030300d08400c414464807031030780454074945800b0980c041c820712100d01030049800c41101d0070351000b1941c60110b484206501200040313008500d017245030121944079440284680d04c40d00160803050300106140310a0991141c03c51a000481c407004403404818042c013a4000c0618014400500c0c000319600d84180401482804a00d1042c1804c540d40c800c4980da10b246a00078800e5000c1e000000d900d01ca4000b01154110811140c6849004055545004035441030560300c400800490401904e1b441000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 835757760 1250 835756510 835756541
    0x601031103070504090213050928110102150f190f061d0412050a0306051207261b0103090206310b03130203031605070509010b0306010c06110702180a 66
    0x17000716400300d0aa801d501c0d00380c1c85215110000901c07610300800848000b06604264000008034021a44c503640000c2d03007040e41c45898030004030001703500000f00d04e211940d00c00f0582d201c81d965180c1e104003202025110307612020080d42e070300e11340c1e81842c0204218a01840400903501d80b40503d0948070084180d61203a10030b241000b000042100c01c8110005030747c150400d107590305213999049000b4040c0f03410150b440389410049a164032000100c101c02c0e580f150201c24075008015554843c2103001e540c003400c1c160b12281d104003032000b4203010f9011244060501103031524039a400107600d500a100e0710700300d048446050031200d60b60020b10907480e2403010643c001c41e90404000318402d21000b48404050000c5c003e458007151420822580d111465445d400804045450a01d40f14030319071090600c148942c0002040c00e101c0c19080300d000c1c500584420410000b65078441c1c02408900342110103804040c4400380150300ca442e003e0084004c059800740c000d2400600036411034400d411001d29a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 835759010 1250 835757760 835757771
    0x325081b0102060406091b0909032304090e150f1e0402010507141c02010b1e0303031311130506030d090303081927030f051305090411030601031103070504 68
    0x181c1d03004141d058006070441c0d0041108021800c0045036a029104004003010140000090046517035000a446521940e02c0d007002c0c000745541c0101c2c4500010f0400401f440c1080100700405542e0301c00044030408905031039103800c004220910b1a08102c80c0d0000c0c9031207040c01c0010050b400745e5070f403170542080407081165081c2500024100c1c020540004c1001c0c4441c00f1104101d241041400c10b0f801508030b8030800084c1e0f0303000090103040810340c0580107903001034401c14074405c01003a507502010094025402d40d611f84c105a12226030360502520382100701443c080403034480d0655007400c014400e13004201c1c1d0409005051401c41106031207401c0205204040c000241e01480080e0070210b000f20f01030389002c4641070103000b000766000700044003e112801002c010a480c0d081c0b10524080c0d00c8071100048040c4003030b5024494012000101114801d050083c0c1c5005141241c116009440c0c0400c4c0804a0020900d062400c0e001500c0c1d03240545002c568500d800c214290180c502507809000c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 835760260 1250 835759010 835759063
    0x60507050f06240f031f1d0d0e0a150305010f0603090c0317090d0b01060f05030103030e09070e060d2906040909060207050a03080403030f061211032508 67
    0x14012801d440391149102000d070780803415540d1501c0394000e8013008094640c034400c648040b17800142003190140b052800c10048540c22282c0220205a0790340f090090321512400d500101ca210301c40c000e03003030b500511a00d0046810321003080b20302c0400029450000f907075410710106100814150340000c0405090100703071800114411034010072694016031120f000d2140d01d10a10441c021404040c0c0c0105907000c00030180203e00b84042d0403502252980c8900e500c101a003100e8504c802d01002d408034102010241036810711680e82544051285000380140c040c6000140c81c41c0e125100032000c0380d03100c011264400ca40c0301c1301502c4605805ea00c00c2145d0620801154541c0100e128031915a50303541140b0042c00758039011035220a9106050b0390140c1454903003d00003100c2034030240c00091a203c03460318120401d11504080c4c1e44c0c0790003400c41c02240d503614102881014a0125018000d10209083c40000300309038000300f1040d1003046035602d042c01c1d4114a811000300544001b400c0309a05200e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 835761510 1250 835760260 835760281
    0x60906100815190e06010f050105070201020715200c01031b0f0e150304050607140a0c11031501180b06030c040317042301080702070f06110c0406060507050f06 70
    0xb041c0750118900c401050b940c1140b040c00c65400c40084440309070416000054a100201e0081d05980113421035808281c0c5036401150390b8051240700078096406024140900705030f030320b0050407180072850300404481032003c0184030080e540d5084401b991040460000b6503815000713089048000c081c812603001608000284074020300c0f0074007028031191a0300350b203c54070b4640f80f204441c3c00c84510710b6624141031034400e44e80d203011500780300010101c201c0d0031541c0d194041200d480e031921b6642c495002c01d01e0b03103818040300000741c069585807203400d015203c00120503403001e000b0301c080e80f500a070200c50111910243e420203041c55110f100c04104005481703114800395000e407a040062003007401d50485050b2010720441c0c11400c40305034480761310405151143c0c10072480340400e03a40c1204071380f5465400d0f40d40f50101c0c001d0110b25031503803000784252441001c0300c80074580c1c03e0040310b0703001d08400080703811181c10750883c10001d00005001010b120003005660648841d040050a06190440104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 835762760 1250 835761510 835761523
    0x6070c051b03030c07030804030201170105090109272003120a11030f0f0306012a0206090f150c01140c0304150209090f190b010c0b060a1203020609061008 68
    0x101503031103080c40003005502d08006039591072005104551240351079041900b441d80007840101d0010300c140c80c0c01224007180e107241c10304031040549041004d90804410001801204500c0c1c0030554040010601036003030010403200c458003c1100140080d1a1113081d580280245549030117980721a0b45440699490012900500901e241141c1074008440303505040d03215881e01400f081d080415600d10060081008600a0310b09807500d076140707400300094442c51503042134060910a00e01c00c46c03030054140b01c0010246507200504400030382110000280b100c0c20740e0107104080410100300900c45c0c0400344101001080010250b1246140c102c00c0c40b8818030005000174245144030340c00140b0100250145d1302c80007401010310140746030052600c0325201007111030319040e0b118007010745240203c0317104500780c110040e51400c215190b40e4480a145030405044503030442c00c94030300000c682c8111904446031900c2580a804941480044149091000341c040b444500007403208008504000404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 835764010 1250 835762760 835762783
    0x8090114060d0515070f030f110d09020f0d030c05010e0102070209130510140403022a19080d0c05070602073501060605071502040b040308030c07120c020306070c05 72
    0x103442c1c00952a01d400b60034950041e8150649082450600c0840c6811031401002c103400c580d000c010488900c01e100d0f06641f100080d40c0f0f4808000c00c0501c44020072a00464442d500103000d0448145110000c2100c054666500380d00003098206400c0801800303005021b14040c001c002541040a5074001a50304000038010303c014504502c2e0f641c04006042c030040201d00c1e20000100300107a5031501c280c200800c01c840c224018014102d8003074a070102c0380010080b5940391301c6a02c0e0602d164100340501c8044032500c840d01c008130110000389851381000012809512662400c41051040c90400d180034015007046082d03401c0b43d03a0611103242c0414204802109c000500b4240d5000b191001c0800618084030000759402e01c4401708031140c10a00a24095114080c42c03021030b1104426079040340224001d00c03480c0c507420402040070a42c098003542d0002c4008401074903100704c070f41e00d175031003101d005841401140960f0484000d619081c011198000700c542002010f00c10a0313a58251500548a003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 835765260 1250 835764010 835764019
    0x608100e0f0a0908070308060310140c07020a0302120304061b03080606030a140c040609080102040b0304080c030d020d061502030a20070e0a050f010b0403210509041a010809011406 79
    0xe0310350009410210383c40b5000801155901d80e10700300104075110840b00f143c06480b90741450380072007490344900e80a010300c80003100d8658581c501c6c6018a54854001a0b03440880d1400110142e96180e8100a181c0145002541c0d203501d0820090801c20b11407180f00c00c019518416107000c03d820902c0a80d02c01002c84486590355100240d850003001c49038040035001460ba02000069028400140159102904c1d400d440560b1b80001c6820f1b4800c5005a840e12003090011030b000034200c0000d41101110b800540782040310303030300e60181260040b42c007102903141c443e1002c008245501605400c00c0f0120b101443c9070410750400946a00c10300b180840b44955002c6101c4011082486503101a05a111a5585a040542e01000606000d4680c520b030311018000004404035000c0c12a0104d83d030002e6401c120031222800d0641c0d412041d0700980030b02404102029980d0381d148185000c9414055890309022030650005108100041040a441e85880440c508600d06980c3e00e0380e00480c1101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 835766510 1250 835765260 835765291
    0x50a06050a050a060e0904061d0604050606030f0a12170c0301060f0c120e0402090d050109060e0a030906210608010e07091505040b03010905030c150f04020112020d0905030d02040608100e 82
    0x80e2101c0180452711000481244180003140410004a50640101c2c040c0c8116601611104109030310b03500d9030b05400c0e003503500c8003541800046040e84180b1040c0c0700c6082840441c001c215000540440071225070300202000801440785940040240e101e50140307103082208003103980c1ea034903040c143d88540241805500d950b2030900d907a542e01240d90120000d4444200c548145c50064041c0140d0f840454041d410005d255212590006d0710b1a0b000b0b801d90741d00422549458403c2d200e80d03000b00035865003402078040c5440701411501401c00200340002c00021013002e1400d40340c0c00d040c0c143e00b005840c5420412440007a84c0f03034100103c00c2e2641141c000882143c51800240140110240101107010110b001401407102140340c070702e503886452100c0072542d245451403820b510300b12030007030214800c0991b550620040e03502400da0f80309010720014240e4030a440c1d051031a088180d00c03040480d00054140a56640f00e501070340c01c2814400c403146410b0a0116046820f000146008010100d02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 835767760 1250 835766510 835766513
    0x30e19080f0601090203042d06020d0902180603060105060d060509041101200d0302090627090c0f1605010b090c0c21040b07020a090f0212061c0204050712050a06050a050a060e0904 79
    0x1008d110105035030080003103640380001d10302003014000c0c003a4140d11500c0b200501060354201d840c0d1041c4580d1004020b400c158ac01c0a0402140760030140c4460032155542d00d0204082c1c95924280d40158007895050001c0b1020400040100040e11802c1050a41042c1400d2101d4000101c82600c1003280c100075880f170807000c02162860160028506620300080300c217221401403100781001c02c034015500c0780103d582e410440300131407152130904880c071141081a80e0500300100c0403840d107540f2a50020500380014000201e200005981c500380c00300002070300748e000c00f00030070070007110100c00380c00e668100001444126480c092446000d444140c0001c4c01c108650798039a900c00a4000640108490300c00041c5400007504040c0c0e40004065514010400f0361274103056946080e25a942c098418205540c2404054400a0a00024030041d01c0100c9440c0c00d02c3d014003403242c001d411000a61a14040420042070140d610030340c010140c507c002d00540c0d6100345118551403040d640401d646c0c485 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 835769010 1250 835767760 835767833
    0x20a12031503020f0d2414070806010503181515101202030a06080a143703030204090207080c0c0f06070611040302120615040216030e19080f060109020304 68
    0x9800000c00b486c500c1c001452414065400700380d610040c00004001c504400440c661a441050729a640824010400141c01d03620034001144c3c446a0000441d20400c64500450310b0242c220302007a21020707407030080241c0e01c038000e1191a10304508503800c030301c0885910b030050f1064100b0880340d0425500040040c14440305a00700c54004d0040c50120344d03007e0b2590038060b0700c210000380c158502c0c0c002e04289480d40c1c800100701078070b0780740f65801640d4400796201000c61403820006040b03013810b800740f0000580d0300051010b041041e01134150555106108500342c0c3c249106c5840c1e041c41510b198600b02c20750348402040c5c0f52002c1d401080000c0c00c001040121501d402103510080d03200d100005898180c080c0850414001c2c41c00d440040420303070004042209034001d0b0b07880328541c20301c0840314078017080c860b181284181401802500d21408a01c1c1c204520300540c0c0c01048650340440420b840c0c1c007d04201c2c030350040c0800c0c00b0442c10350034940da40315244440300360061503030303041003820703044103500d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 835770260 1250 835769010 835769029
    0xb071a190b06070b010f092a0c052a090f0702030702101e051b0105090c0f0a170a03020f0307050d2f1c0c05030a0302031009020a020a12031503020f 65
    0x100080013401035a5140d007041d410a405003d20300d0118100390b40c0103612a207402035494145a40016060304d0b41c0e0503907080314044c0c0c0000041e94a03215800c041301401c41030308010405113607500c052002d442c0b503203824858400e40282ca8000c141000c3d80801c090340d0790110a40365070301da0480d1404081440e0980480e16000c4100d0030340d0060800031421441c5503000001440e142c464400202aa440484801401c90341c045810f01c009800000010b540340c90122030390707020b0b03000081000e0009512112140c0f042c0040c519400301551041c0c1c0d60509040d0100190708010509900840c50700b840360703907a6074884103000104800d00c034003400c030380b420011618081c95480404103a6481c101c07410010107a501c0081d10f04400002c5018051100554410354601c55404e0f04180114901700714203d045000354001012000c50021112010a808020b0b000810308480740d5401040f1200c100d0500200418101c1d4000c000e241c81c3c0002e00582c0c1107580654400c8a0f012210a403800c19010301007a070050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 835771510 1250 835770260 835770263
    0xc0f041805040b07020c01020d0f0927180f080318060915060604081e070b0c010e1005060d060b040b0315010311010c030504090e070509010b071a190b0607 68
    0x111164104900a0865000300c0c0302d54090031100005444460040e0f0700c9000c00f881d5940140c101d041c42002860190020506100301403915400c4180c2e11031020040800c03a0a03940381c101e203180c3c0100c1c40ba02c1140240c2e428800c2d000303034130420203841d0380d1200c2c02c4050043e8002c04100c0e01200007901070301c0400c180080d0350408400c0d0b640c68584481e0f66500c44518052000701c10107007002088032420490b0585054030400c41c0103003882104070380a958500030310383c0e84000a1041c0a40461b000011501401c030844542002140c441aa40010740c01c040d40401e000c81300344d25100070071285540740c12092a03e141c005800041d03040490010130040c00040c08100d416108034065040340e44100c1903060704032030042d070202d2864601100110b031905141000a00000c0003071005002200c290303804a080702c00000304a03402142d8900100d04204826842481c41e0100401c1c2d0f074003400b41e42a0001e80300c00c3c40c103100c03140074940380c4107244c19001d001c1044000250345140c5114280c44c1d1300103c83c400c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 835772760 1250 835771510 835771529
    0x4030f060906140901060e010b07020f0307050a030305040806150109051e0405180705030f030301030b10051005040501030e0708031c0b06070b070f03050f0c160b010f0f0605070503030c0f04 83
    0x11441c4000c11100f5100680d5046030319860034400143c1032810715201416151110402c40c60b01d1019003c10581c0b01c5404152549801400c01c005034a40d175500300130f00214071a8540b035845030710700028941030010082101010b00b00c80da401000c40d03070b030100c0c0400035200c00303c40c5c4500c4400c034040300c2100e03009000b0340203800514050030310a080d4458404041800070768022149003584401c141601d40c246840301d80b01c0ca60081c40180000350541196590041002d58000c400030740d64400a8080f00505141c03d001c5000007400b4041540e15000d050081030201e0300034071070189415002c80d52403144078061000d2030592000708025403110f0308000c55102c0f00409441d2100c034981001442c00c40c003aa0f12002050b121240d12070440d00901031980b10303240072200b000150341c81030b6080f003140d444201401600c0c036070bc1c514400040c818896080c0030301240686900000d06100320410040c1d2590000c50a1180600540000a4000084941c4003540103000c0f6209d09d0100e140010340d0045406c40c4020303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 835774010 1250 835772760 835772771
    0x10614070312050a0b0f06070f110d0b2a030610080a0204080a050d031404050607080612060a0c14071502090d08040915051002061f1203090509160504030f060906 71
    0xc4080c02c0d00140345d01c000442e00860303808030303413800c00019208455008010030064050407000c100581d943c0c3c400c41202402d00c98110340e4070350b00c0c0301591204442c414895a1851a40440300c9582d0014555003a4120025451810510005040030024800490030001309100040580000f034043e200207004c0720007100e44109480c502039890714030058401000a1400c0309200c11500c00811040c0101d4000700684002d448100301201e080100900040d00324151020b0b54030390100810031940b24080984000610041c980002090003103803440001c0004010f20104002c6503400e0302c0d14140c080c2c00080145c1e07410b160000700b0500301d41c429002c0e100e0000442c000507041c1040e00a154907071856255650310607282c0080016403001c898076200180d0004d000107202403007c0c2440c90900c21074529107002c1035a03c152251040c0c041010071000101002000c0086040101c82d80e90041d801c0c03600204400101107008086000c0c41c4405000b08071321119403418800d8550040030100e401440c10f024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 835775260 1250 835774010 835774021
    0x615080c09060109170625050a05070f020901080a050c0102031312020a05040e03040905090307080301092018010e030102160813080709062105030405010507111e1801061407031205 79
    0x803120001c82e03404150116550b840c00e52030800f000301347c40085440d1921820084e401804a610f41c12640c4d0441302d2400910311000580c7c0c03409102402480c00e100180010f44681ca440c5040040d00244141554402e10641f00e0b00d14507480c0d294190313021040f10b08159203503400043d0046074698007aa030043d2070840540c448c0b020100040007078508486081c0010789070b4009140d84d0788200380000c0c8c1203d90038001440b6002039a00440d8500c0204543c04c0d401c3c1c0c07440c510b0421a0361100d90310420100c1e10451307054403560403003200c102c003000c1100214240b800d80ca07282c80c55403005020046c507402d00003408100a02c210a61500680903150031110701540300d00c12100108030f2406407025003011544c01041d0084000f1048245540c0030300614100780c504001034905410000080b1901c28405019250589900400e60380603402e1004c514524462403050050b040044612038040d4050100140400c4d41c1020f26401c1c0e10300d014003000d60b61a034600303045a2014107541c8100c800c0e03042000740710 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 835776510 1250 835775260 835775263
    0x83a0302071709010f090608040303020a0c2a060e15091906030c171501050a0e060d0c140703020604110a080f07050a0b0a0e060711030a0f0615080c0906010917 70
    0x74400c001e1302c4403203d00e410070305d042d1014402c9128070000100000c00280000340b00340c0203044280750b6401d00d50b050b0b6425981ea0500605e1600f008244120820181100000b00c0203400c002002c5134140040101040f002080032010203c640d00c140d210000f0303007440076440f03400d611091245502d5502480c1c0d5102d800081c0039101c10510f11000840006039060481c2c12240d40b240030725410042601000e00d550019640f580003120742d20309103d000c224a42d400e854100c002c0c541800b50f8900001c44021007030303021305003080c80005266020828061540002c3c4c001404c42d4019401c0700082249021040000d90303001e0040d003051704d40d805075060105644ca00001c0c0c140c107034be41c201d640005403505d4019003001e60164052070b400064191050500d6818803030000c021a901070407024004038903a0009c68030708000040c013116041000180d002c2401801e105070842104140e2520b001145041302140d038030700e0034007040d500c1400e01701e0200348668014110030006043c40311850341c1c010007030031009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 835777760 1250 835776510 835776517
    0x1e0525050a0b0f070224040806060324011a07020a060f2a0311011d3a050318010c050d0f0501030215070615030804083a03020717 57
    0x850191201d0326011a02c00c19050a8402e0082c41219040c14150950208424103910100c0700b1025600e44880200b079842c0e9000610103015298001e08150515805051402030b1121080c1c0c048803a81454005085545030b01904482300c010f400b41c0c6519034910490303140d218a000c0254007405108001801c20f03084030001c03104071042e80b6040080b4081e4000207640020f8983d0510030b02000a0030000001e008900d6525006a0380c03000040b5031103248403d0b01d01003d800303030640c95a400907102c0110540107000514940090880120895030b088407d4950641610510310034008007100041c0b0b0070a9001d03254080307015520090041c5818000090700382d80c0b104510040c4241004405802c0483e02d010307841c1240d80c05880d8040d1b03280c40e00c2e02e2804039000500125083d0391280408042044a994110095801400400d64461400e0445481c00d50407070107030340b4180c11007035002501e06e482511554484051035502a1540c400090480080c814000000c004005411050543c5100c00c00a03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 835779010 1250 835777760 835777769
    0xa271401030201020c01140d110d0203251806030c0c06060b0307031410150507050f03091e130b01090f0f030b1b0d09021f020d03050a02071e0525 64
    0x20303503850b0b00039040112001001c0840345d07c00007008122603260395200741d103d16074402d20400f90a013001e2254242c0d070141d078015240c44000ca03085038070b00349002140c00200700c500c2c910b60034600a01920b900344900652035030311510050654901d412107146001c0c241140c603030b0354804d50400c491178960542c806c2d190015aa1203002a1030003400c410760940661071117000308669000301038424030700088204640c0704148a42c0400c4024040040018020801e1070f22100c40580510f8840c4141005c0c400e80d070400c06504005100502c2c00000075480d01c1648420000780f599003c1500404080160b900b881c041d4094035000c5c1c107030540086c0c41e00d0034005602c190b80c03103030032600e00e142c030b684000e020094040d61140420b00c10400010355480380641c0212500d6101030840c061030548500341030350300c0300d1180d000e0300560407001403011000d0789071007800d501074090402141840f15a8071a29028184016100740044010940340180107042020b03441407e019442140c4201c1c03a640322100941c150f104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 835780260 1250 835779010 835779013
    0x303050106030b010905010804120c0b010f1d01051c08041a0903010b15040e0a090f0501020306011101050903090d1401020c030d0c05090609040b040e012c03090a27140103020102 78
    0x495028942c400e8001740c0c1151030582d51005551125190388a810121040c0c5006000c01d550003d000a00955034a6000300412101074001302c1c944070140700b900900b128a0390038006002e0050004c0d035600c1005001041c0b112040b40ca80800f5858a25045e105038cc2000140c594111381c00308a02404000508032050254005d00040ea4001e003400309000d200e41401182c0207091000340043c450505066901080150f4040f801244544075450700c0001040c06645994001082220a50300201c0030070f581040d00d0b008003c80c1c9010300510b6200d010703460905204441c5840c0a40510041003a00c804000004000310f640d1000140c12541d2580050a148606400d100303402900074014810355a078210003404091814151008020041c4294154140e01a9441107811003400c409d1145160101d01c0319000e450f400c081a074410300c0c030402c14228006641c001c0040359402d032540400303002102c0148031012000c011a4041c01c49440c000400202d50760b1030001c1440c9030303180c0064418101c9000f0780 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 835781510 1250 835780260 835780271
    0x809011713141c0c080904020a050304110306073006080304080706021f020901110d0503060a0905041713030f0b0f0612071e05120105070201050906040302061b040e04030305010603 79
    0x42d02c41c1d02c0703036400ba00720400c9064091020107880d010b5842d1308107140c441d00d001031614000c100001c080741c000d0600100081c0d00481040304009005d43c80704440c00c070440081c0040c1c900188020801584c2c895520300c112000c9600e07540c0c449618070324407040ca00062050284035242e801c1269030340c12138030840131584900e0f0f00008180d800071581041c00a112291258000c000344000701c040d43c4100c0c501410004280220310100006000b241c0103400d050307551690300e061420820040f108141c02107440207183c002403100140c2504612800d04140743e4110381c039200d60b011401a481d4030386d0701c00b60011a9045501042050005400b441075080c29514111521110107009050154030003880955000c5a030a10031030700c41c05480031640500000c030b00791072900c4d10301098500d4021000c0c000305030b44520a10005035028094a81d0001d0444020902d903c0c1c16200203681d007201521f02140c0010407000030a0350402c072000c841c00780605d01100d408a04080c03400400a007004d124100000c0d2074036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 835782760 1250 835781510 835781543
    0x12615120601090b1c0b071407120810050103060b03040605091e010b2b3003090c050d080d2c0d080105090c0a110106030f1b0609050d0809011713 64
    0x145c81c0b241095001401d9220980d20740c0410b4403a203100c500340209519045c0103000c005095109040040c0e20640d491884a060807550800300e40c41541100b1305060070300c03106219015284095940c002d0304003001040c00c1d11040341082c203000d142c40c1d071030024880d007000c08609210150040d1803602000d4460003020030009180d102c071180442d011414007510070031210081412014180c100d480c602c0c1300440e00c034030480c07d420400c0c00c800b8600c50100f512205130310f05001505510200500054845000040345030b9910143e502ca5102c01c20166640c9070080421058242d140e8500d81030f8019420701d013070607441c00d083d07581c0d4070a40d18480080c20385000400e1034102030800364045e18030042030608255501c10191503422011960010342e650320400000858150700c0c541400c03600801450546030031103c03110035845010f42011040c860402000c0007140c8408660642c8682c200962640b02c0800030b00407030f0b007000e00861000c1c0840380c071410b1100300345d02c80050380380141c482c001e04203803c07842c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 835784010 1250 835782760 835782799
    0x906030c0e0f100b0d1506020d0201051e0619080d090806070e130b0f090f0f01240509060d1d07081903081b040311012615120601090b 59
    0x3c6820310002c5407122001c104204504018188078002640301103a00040f00c1c0125090301c802d9400400140c0c08908074200352a028400c11f500600500d0400144132001040600c01c1c102c0600498096803c0041c1c01481c610807201d00c1024008640c16100e5051480100403d07140d154051450b1900464010031801030150b55070880441010b00202c018280300c900350002031a520000c503030802540d10840a60360350345c000c800e11681e00c0c04c1c650aa40d0030300328a84c0c240701d141600881c1405801100c2e08104810442c1107000384010707880c04541c0c9403c50340210f2054000c0340c080940303031410030000c8940c1f008440030032a1a140b10340e0480e041a41c1e28204643d0f20000002c1c000118100700c030414001c2442800829403011826070a0102c90f00c10740003030035480d44264015900c500500750440f2982da4841070048009aa92100080014413400000910030700078080c0b0000200c4410420035541324401000c044603000000c3e0f80c025a510b00e0854050203a801c291403054011615540c030b8a0340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 835785260 1250 835784010 835784041
    0x709090b032a0d1509061407020601090c0306080604030306180b0f0f03070806100305010b0a05130f1808030a14160f030b0604090b0907020706021203100906030c0e 72
    0x10400d462000e5910070700c405a010119614980740c02982000b0f110340030a0344201071482683c000080000c4030481820520112203130b41d1a100b5452901c0d1040c030095990000d000c60550744036010020341d002d0a110250010005030b849003c260244c4000c00045c95099444002110344c6c3c1c09003000e0004a80c582c070001c80e241d6040c400e601c0b50613050b000c01681808040c040c4050b00240c12030300c1c07564403030102600e0210f040300e50090160040030b042c001c210080c02860740d200c1e0203560303104601e4144400210042107111108584560352941c1c146150300940045050210007140b485040810b41408000c0d0f500860302e501c002810000c002015030b4000344018401c0c45208006034208c46140021a401c035440f10800b820140c03a030010385003a0f80d03680001d000502030040e0001d904541d10007170040010004140c3e0095420286041040c80d40106941ca072164044c05140c0d5a40d917821041101561950482502030307140c80d00c04820010903001c0c0b03e064030b80483d424400b668503401154101d88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 835786510 1250 835785260 835785283
    0x50105030709090f0209100312020102030c0a08042a031e080a0810090212041104050408041a041d010e010f030f02040c0c0209070f030c110c061b060709090b03 70
    0x50106200b00468109035101c48042c0388600114914103080da0005010318405a4040341c44003040b507001c2041000c000614101400700d40029811890460b00440440c02540c1c407c00600c4000070004d0308008148404803182600d100036000303501c82c41400381d5411200c070f010444003240402c1c0740502c0081240e4003500419800304856203046101d42080b02d09010240c040d49c4800d601280110702d040f450b00150180704032840c45035980b4600750501c40d81c141ca9200c0c04500aa250600340320115441c00d0440341907030346040303c681d1041c66003281460740c0d00c604d50040241c19055aa1076441015000d6420b0480b0301000030780c0b407243d880d080180c00c815213501c801002d4002d200c0c03610005081903000041412402e081811880c08180c000c0350b611902210088000344049205100c219054030038600b80c01d226103084500e605d1310140107980c0d40e203040100d0380301d020701003449000340c20281c55502030188200c050b00c0c414181307120301a01c20146401450405404c0100c03500301c3d41000580c441303540c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 835787760 1250 835786510 835786513
    0xc03040602072315070512010506031504150f0503030c030d0b1f020a0c091514040b030d0c0b0703020c06060108040c2304060906050306070e030c0d08030f070305010503 74
    0x1a11580d8940c0000d50120b4400c854800400301002c0010b0001148441e405010201608120080c0310510006000c010242c006000081c00000c03d0003402e000d061f410343d00d040d950a643c81e00c1d900740001c19690b02c40e100b264018181020880c4010303ca40c1181e08503183d0070300d11a02d654a03002015100c0c05040c00b034110544c003d2145004030b1741c1e160810b4128550150000b4400c05c0c0d0920624000702c070410100d0090b038080321003203042001c83c01240004103600d490402000200388101140310f006485040d240c1c2c1c9001584140683c1c956100070790640006049032030764001c12102601c00b0040500c00d03241c00c0000c0c0c5c0010f43c4140240200c409034403502010b0002a920b0340015144100050b0040e070329122842c40215190101074a100c07080d409661124084a500308100301c19104142c014081c2c1504240b020003454400044003034001000d030a0480440b0180408280b424548031001c0e035101c010503000c2000d020420f4003d40c010f5501d08036203e140c0e604c031031040e4150f800c20711070780303070503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 835789010 1250 835787760 835787767
    0x120903070b040b0f0304060b0907030e060609010f1a1303051e1501091e060b092d210703060f0e060103051e0a060c0e01110105010b09040f0e010c0f0201140c 69
    0x2000e0580017168801c3c0300c0e03400011010040380108a03c00701c112140000f007130750750080031303100c5004000966002108903105400d42d03050400e900c1029656100b0604514480c22000280840303101c243c405d01c0200d0008648001d5807410101d94580416074084c8451070703505241c40f9004004501c0c0302ca001b00b04000b50340b05910344880c003002040b055220314000b04862110456481640c0240402031100b800a29128400e000400c9109025113002440410595000c1203600d618203019240007082110740b240040c03041a8041842d4880300c11030003c50266280220030820316601c6049454424a8100000848840f0301559003a007800b014240c1c0c2d1180080c44200c248040700108402941c5041d03c1c6016034075a1040242c81e01e8812150116841072108181940c0c04462010744442c45e000900203940361000e180e13140e00c44c039501140240d031190700080c0e803030700940c110024030100e20000f00020030710031900601d0302081c19882401035080c04c410f615041e000b40410b501038030810031900e14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 835790260 1250 835789010 835789027
    0x40b0c0c0c090a0c0f020c1e13020a021b06031005100c0203064602030a0e0a0f030305150603010b0702010c05190302060c0a2f120903070b040b 63
    0xaa60080214100c140c814080e0030201c0d51901c00c2028020114107502040361411030f00c01800313200c4038008400442d48205107c00144c0e40b0383c00d14001400180038010f90460034007006ca0a2420110f02c1503c400d800010380380c88c800d078002105000f4075100d0b0b071f9500300c903c0d021003002164481981d03501d0032050051000e203c145809146525818a01e04007404181e1031940400e04007041224403400c2603a84086030011550640c10207101070a04408200c4115078040d20008404c041044400d25141c0c0032002810b01d1140354400d00ca140e042004591180074185040541185252811800a030034203000c920941310b01d040e5041c00c80d000130b00c1700b42968208409110a60040c4200780d0400201041d00381c049442031140320410107811280101e0221242070107482c06401a142280600301004003407001d65010103072040c40e0440b60021440b004100307415005548501120a0803405040c0e0004601c00e0154024160110f054050b41c9600c2d95800300041140614441d004542004020510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 835791366 1106 835790260 835790281
    0x203070308160203070c1710020a050d021e04030b071409090103020f120d0f0e0405070c140a060f050f18030901230d0c0f0305040b 58
    0x6142088a640081003140002c00555003200512904800c4510034030807200100d41020141c105079880c1c155003d08a407100d000d008042c400c01101200c90b03201802611605401a220305080c90f10114120020394056007559100441c0151152014102c4c030b000750010714024001c041640c50301210151016002c144184080d0b08203100302c000c150749040c8003506580d41560b0464400c0f42580118200903a40c034101503a0340502c41d104043c0c590b04c00500541c10080399211000d4202900901040300c1090301d03a100094484610364011031541c54080910911040c05c941d60208540c40321421220007240c10701d40300382c543e030a11404030600c400541e04a11164100c1c5080302c1000181550b910442d02468148072541010500011804d0300c00c1a5a030241070510f540d82c1c43d01021200100024408540424808000300d44a07074440e2050911490b885450740100c1d844040030407 = true := by decide +kernel

theorem cover : BRFrame.Cov 835611510 835791366 := by
  have h0 := BRFrame.cov_init 835611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 835611510 ≤ n) (h2 : n < 835791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
