-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:55:30.558091+00:00
-- url     : https://prove2.me/submissions/bc26d903-024e-4bca-a275-5aea48526189

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 185431654 ≤ n < 185611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 185432904 1250 185431654 185431691
    0x2030412080405100504050c030a05010c12050c090d0f050106090506011101050702150c04030c0b0a0201061d0703150e1f05030706050306060a0e0d0602041404050702032205060d020409 81
    0x100e0700703c0c00a14000b00380921290052402900540e414030a0f0980c819280e9010824520898480d00002c2400c041501d40070380345280c0070b0701075038000b41000108038030760000d030040d00c101c00011a80040001d00300c1c248070003c1222414060415400c009000c5412021a00a01e0003900d003aa15120b028100650a0f400c9a500b502c0c240c00603001049074418641070562541e400189103040c0c90b01d4150703070740c0e6000f860b42c03000c1d0f102d1600c8400c0840c1c046501a02840740f200140b1044800072030603042040c0c0c440041800515401c180341d40d541c54005001e064100310806802c002900903903508101e07006080d00c12000400c080400705240e00400c882c1008100071003180c0b01c1e524bc031800c40d111001003041c280c02c0300c0c82c92000c01c50100c1a40c00142d4421041915171405810010303903031424040000100c801c04030485010303034200704c140300c09030390f0010443d00e01051181c10b0624440740d00d0107240c80795419070300281e807000e00460b408115500aa0091044a6100d60308109a00442c0041c81d0300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 185434154 1250 185432904 185432911
    0x6020d05040302180c0c03160203010b0604050a120501022a07171b0609040c080906070305040c030201050c10060f080f0a02090c301602060c0a2307060203041208 71
    0x403401860741004102402c2164000030082c458909007038940c0042e518540180f070408c91090403c05944003581001e1041c00c0150902365201c0345024140800f040d100c081600c43ca032203da90303030351500d82440360039410f40750b03508040c015210305610344a0000c44113449043c02c1c20401e00400800003856036044103114540c80c0c0c41c20140c404955071901e07004844c0008151710390441c004001f4410159501d00c02e03030381c508400307840c1c81300c0b5070030316130b400a00c0c00000901a0003414a88400d2202203040350204c041220b0382407070610380e00c90805580604010b0b00000c00302d205400c04a02007060317054404041e09980003807044078080803460312445e81e41c2d1030b10100030750050b6003400072541c0e42c0d20b242c2c010700c00151101c80007403031540d1131001400401e080341e40003014a03080000340045140095088a0145503a1009003e6401d02c0c500502003031003404541400c5c42100100d4034040205c2025a07158110f0b40140315481e2011814108007030350045608480f00c00304603619164650040149902 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 185435404 1250 185434154 185434159
    0xf0604090b06060c100f0c0908030403020a05090901180b07110303060607030e03150c0717030f0a0c0207030c0f0303020111070507030204020a03020904021b010b03010207051009020111060703020406020d05040302 93
    0xd042e211030061088590040072002114040c0911414a06266000302c12544080c1c3c04005125841e103600204002c210790801d2181360010081040540d80b0074800e00c040e03030400c540740b081d242c40e8245420300510008006160700c9101240c0241442081701d42c0a1260300316072200700c00c110f00c800c00c071500d0384412560980d0000e810311668012130302c02c0003840d0800c5000340442c0c43c0c00b401e03002840d110100c11a00600d07020000038101041111010300004804d071400c00b8141103040201454034200070043c9083d034015940c420341950103208106039070096030400e0840d06015107501c80c10901215074001600036601302250044032203010411250b08903041806451140d007140d0811000c0d500c0b0341c1c400401c050f024400720440380d5541c80100f6402c0c06003607107002d00c2101015181e0a40c1c0141ca943c9119920501016002c11004941c410740301a800100141c03061041c03005880c1261113210030400fa01c201010401101c3d0140d0040c41038482540031180d03a200e095034205c03100c0c030807400000e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 185436654 1250 185435404 185435423
    0x60206063120090a05010f0c020915060c03030916050a062601091506080114040915050c1b03030c040b0d1d0c040b0604050612070302070f06050f060409 67
    0x110315200032001c1000c0701c9040300c80810403600b0120701600800b0302c05002c000007903000400004a1030614201300c01040d081c01d05011445030311201412021650310080d0041911000050f0482058109551a13001c0144010f0b01c1c2c8a580c4042c0ea075a8104543c0c1140c1c40c8140340784904005540b202c0142102d00060000c203000e400d010040360390203030140d01b509011030f1007940100002c0004504602801e040744d00000d12600d0301c60791080c004440e0f400f140070300030844011710503074144600310004107405071004500105186440301803003204506d601c44c4a031509090291101c245001089a0700c81c0014003c0b50500041c00c2c0b503120303c0140d5840f011a001000100661a400009000707a20806200040c01500e6200341e142a00001c0d0308001c07543d0000710781c0000c149060312520640c000151040b80c00d0501300030100e800c034403c003c45101c0740004400060340c0188660100e0300e4090340040300303490702c04451a002005d00b03410740c1c0d0107441e050300d440000c00c1400c00b8415800b101d508a480c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 185437904 1250 185436654 185436709
    0x9090f0a02060711100f020d1d011b020607080301081006150e030f0a080406030f020f0901030203340305060105070309030201033201080607020a0308010e1e090706020606 75
    0xd500d901c01c03c001c840030704042c40c506000d5620850107805802c00354075a00c071842c3c1480d100074104003000081100b44007104803500310ba602c0d1009e0750300d1031641c20709001d00d961140310f1604030691541400258400c1c00011842e01700034105016504032040041215004590002c41900307440240c0145004211468800c10503580308a5416948072006000d403038600e1092141c007810003e0140701966420ba00050810001ba0305109a2079600b045110460502850450507101c0784214413500c0e0400d5004030205240c40ca1702c208001240800b40b088081900740000d14042c59040b03c0c50756000301b0320b06800141c8950083d02101c0c0107560654500c40c541d415a4019401880c5960041c0008048507100001e00c4030881c0410000c468440d0040680350700d49020a8649840200320004641041c0792440001e43c000440d1415560742c00041006955004050b180c3c0c00c10046015484049420030312400080c089000c6c802e4401c580e007510401d503035000c02c0c0084001c0034862643d800e0380c0c1030700701d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 185439154 1250 185437904 185437909
    0x1704030e040b0604030f0b10080106080705040f1b0c03090e1510021002220518040b09010b150d0507030204150e030a0b04120e0d0305040b1c05070e09090f0a02 70
    0x315078007000080205080503101c1e00c0c3c6c0d0907600090f4104442c650300300c80a22003204403140d0544000c00f003850003030150605001c1040d8071070134644035490145841e105581034054182c0c0090b45114800e0300b00070300d48040c0040007042d00304030080c04e0b0045a00e13004041040264595079606c10890003100150228031482448a04c44140b03041038114090964588200000d0b80020074803201e94024046080300c0301403040c4421003c0340c0c070040c41800800411808110101ca01507803041d0002459001980c1da100c1881c0500312b04a00640e1000516601443c10101000504014078084100304042c1e039034018250708a110303d0140c6012100139100240d28684207101d840700a043c050241c0e1102081d55554128105d800c0c0c6040303071410504032061840c0e80e401110f01c4041d58003107031203407070b94543c64030040c001d481180030304003c3c0800003402d0030307501c03040d507924800d9503402040800040c6807080c4e00901c040c83e800c00d10342c851442c200c041503499030000f6071140280003402c00707003004070040d07800c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 185440404 1250 185439154 185439161
    0x1103060d0b2a2709161809020408070906050d080318071d061203160303110309150703140103030f110d020102031527060d0b01030302060105041805150903281704030e04 74
    0x5c1c0000c11100192441d4052500320480000384022100581c40b14180100c15050040c680c004501c40f52400d0340c05c000d243e5601800c51251398015480e19038030b0f01d0749810f20f0601c60300203044240340d01c40c0400000d0111244140241028880d100c0c1402ca51520410403120802c03203154200340f58024441003260506405100500a2082c2400a51490f80e00b190361250b400446002c140ae4200d41030741c5cbc26450f070390310282d680b05c01c00340342c10441090f40c000304081c4040b060201804000000c54150019805132016a105040c144110782c0017580d211381c001e001c2d5004440500e6006418080d520007400c04c41d0428544c0c8500600d0301da81e049041174014440103000301441c0d07000490070221004039900003207060181d40a036025001c00d6040800340070a07034562800303041481980b07003140004200003146040300a007109111106949030420480c4c03440c010340006840b0707040082030100400e40004282c58072a141d58880107914100804580001d40040358082c011410300c00d410340c920b25040e807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 185441654 1250 185440404 185440441
    0x3070612060e010308040510051309020d1805070323100b04090f0b0402010201050c04051c030509060d1e060308030705030405031603030c031103060d0b2a2709 70
    0x400014a0030b42d101584906510280d2007501e60100c006020b119904102c1d0341a54086c15904040d4a440c0e07540d0800d02003d02ca521408503102d9005c141411008003907009406103806a954002a00d0814140242c9400c81c41c40b040300e440401d07131801119000d0100100342030000307010150107584010411034014041500701580d0041c3c0e40c081c1c600002e5842c070114140d0f04d02600c079060b19490644006401c41d070016000304c0021200384400c014036a280040f03061285104224103200300400d01d002e4401e4040c69aa0551140010034000c0c81031490368090b41118210080405c06104084031990440c1d100b4040606005410000104040d000e0b80095420502c248101d03443c103141881c0108000d801110101c001039220385d161010a540760290100300705e240780c0520710350b09190000440c40b5010007c010081945500040c43c00e041010100d907c01c000c00d051210615030b1040086d98503071001c4c042c2d440e01000e268a600e5000c512603496128400e000d05100c026407200725002c2e008203c00c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 185442904 1250 185441654 185441687
    0xe0609030a12091b060201050606070f0201030b04060e010810060b0c03161104110a0807030c021f1118030f0a0b15030307060c030204080f0102120114061308060f06090402030706 78
    0xb2080280065215152503404004c0d0b000d05003040790074a0b10081c00e560001d0801446550305100d1440800d00607454010248d50900b40044d03a90f10b41e002050150401e68803610214151900004154402142510144180007800c0040381d450300300e103c1540c042e10490070290740c414420020301400b81c0ca000100c3e1030180c580122442c403c8000181500e0780d070080034003400c9021403080030f910703080302c202504061217080600521980c100001e56a105000032140b0b040d100a050700203407145540a21320124202110607070341c0c1d503141d941c1040003002091035400307445907021380e5088480108078170f0001540104950740c40c0e10351703003521110800303110001949070104001110010310360b4456512a40c1d066100580c0f0359243c258264140890030a83c8019039004201c680103601d0300c20030082c19980c0d8a04114500299000402e5403402181c00f400c0b2010960b00011450180008801e8400d41c49c090504800365281020f2011440007998001d4143d0f20024040c412213000d0785180c82ca41c1000e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 185444154 1250 185442904 185442911
    0x90e04080c1c02070f0602150705092e09050909030301050f01030b0306041a06040c05040905070201111827071d0315040b0708010f091503080409050603010e0609030a12 74
    0x644a0070505042d15500026078400703403080100544448104004200318006403008900c4051b401c101031800800f900304020b03001403200901d9542c036042c034041c0000700200d0043c808403101303009613180408207420041518683d000801e450450320703842c81200303500d02460441e40382c402442080c08100e020315042c03545450b000345140c0c80421030248a2401036030416000307010700358500032585014044a0150b400c0c1001c0c041950341080844007142c104101c001080d50300c4203c203d006101280d2045000340001803070b4680d03041a61010307079118000b240e02d4840031a4021603003407200140d00424080029590016140501038220f038001c00201142140902c003840000905082d6140d48180130842c51000b4001404001e10615502a0322410000d1165050141c030b042210803070b209a00e03401d601c3e946413010b50100441c10b02c0086511080b07045d240c540b20300b180b001400040701e41d0f9000e58a001c681001c0e070b02c0d000421900494003031000d14500301ea022821503000034160402c001e51b584 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 185445404 1250 185444154 185444173
    0x40e060303070b1326040509060d12080708060613060503041b090e0c0d050703240f021809012108090a15090905090606300f0d090e04080c 61
    0xf6801a6134810400748001e43c444200038640200042000030222400750780b031120341c610041200c0201c41c156035044501c00140c0d90390368005010b17200055001402c070348078901c82841082d00107040c1d07806141d10352520f0f40305079124020700086008054252040913002282040480d000c0c2005681050140502c0f80c0c42c40c00480c001c50080d0a2607129203201555003108140f00503040c0304002c0c4120b82107035000c4e0115082e032512039892a01d80006400b011000d44000792400b00e0000100380c1c980503003814446080368030352002c020340010b02c80e0b5810010040608100c0d1a100e0b00d403605a071141030382c0f03c024400d05005400040e900203000c4400d59400c20007184140d0307c900c4550300400c524130070201c40200d034820060010b180c03507100c0c580d410b00703110a10542c0000420f845a00c04429519581012610ba0003200200d0a044042103d410300c4041c0340c18524011071070144401803441150900194120300300d40d000a240320f5503148a4180001c00e0005600000034000040c1c6403084800e00c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 185446654 1250 185445404 185445413
    0x3004090c110a0506060102010605040b0a0504021c0c0e0a050409050d0e03031606060501032d15170a0c17030306040b012703050d050309030901030c110d0c1511040e06030307 76
    0x804402a903d41e441344040210641c0d0900402001d00300c10754090100b0001310700460305000c401d00445200d2a0041a1180354002031000c05840400c04c0b5030510a000b06044003820340b40d0360203801d5006110240c00803c4a007814040c0d541010350280040001800e121000c80d044070200c07101c030354140401c011540224020f2035030100030501821000801720320f0a8005000c42e90065518104821030010410b0658000d8801d40c002060080012a00c2c081d50542481300750525000900000017031101014500d80000364101510b214903c600702c451745540305003c40840714080601140d03c01c10001d21507003096000510308500c18141252140680303110300e420b00000d10b05e001a50080e0304410014030408004180d03000400e800d006145040c030700d01046d00da20499070100d051503221b2001e201c600e84070345e4102215035008c105580080511440041034440c0f10395056886900350030f140003081c125803003840c4040d49210302d40381c40e00c0e20f00004094101302c01014144d0500040c0400000708 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 185447904 1250 185446654 185446663
    0x1050f0712052503050f0907060c0b06040b04020304050606030105060301020c0c010e0d060e060411010e0a120f0204021b01050f010b030403080709090207080a180b0306060c010615023004090c11 85
    0x5100f69100400c861a00d80915a0880401450404d590744019070070852150840c0003c58201c2c1c00c000200c0740c1d40d03500d40208014111402805400910020400040c80340204195008a400718000e02031034407414100f6090740240c04103104c02d60400d072041c20b4190f010b240b50f03a0662502030079018000300141c039003e0403522a8080b0b0106e03a00900708210410070400c00f440c0d4002c500f420509002c0700c1c03140205a54010354040e80201d45140344409050100440da0442429030081080d07550b4090441145102c1e420260804d11940c245008200130208100425051304c5441c07112608564075074508484034440a072008050049405022072000c08500061845a0090030155603d15075903900900408007000b480040c2040050207211a2440404480e0030190448600380c81e5401c4503041d40c010202544026540041e41c45800c1c4599008981408a540d00030001101a032001c4885944424000d42d80c1800001c100814841c11119910000c0044944d01e0254400b005220100d86031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 185449154 1250 185447904 185447971
    0x60a14040b0d060c0e090906011d04140703061a03030c100510080105130b09031c0e010e03041211030609060403081b0a11190c050402070503130b0306010201050f071205 74
    0x10782c04048480c041c20000c6d1303495005104580240340f01e40c5070180c44200305100800b103103046031140f0007240910141c580c0c080c0c01c84419409642c8030f59039900d03103c0010304006104045601407680d03403403114500801500c0340500000081c1007040480000744000740002840115070346108400480c0340340c0c09114552080103444000020419181410903041d00000d105960507481003000c0c02015151021079000700003030100c08501200d6040049016240c00081600c141c803001c9000101c4a890b40c10440103140900c10000710003901c070046c151140030032620380b036056214001081c0024480c40069504c0300c40e00c078002c0e90204c000300c001c00c2607500c5200e200e80000c2d850010b04000c80024403000040c001a1980c0e501c00310110760380c440d11440c507841031600c110390114400d01400824011942a034501901c981001d50316296203d80942054034064015880e2000040c0207407105215540100502e80758112034001d10400030f0090312000341882d0007240110039541040c0742400000e0031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 185450404 1250 185449154 185449157
    0x30301150c080a02030a0305061e130f020a090f090903140c120f03040501060f050f190b0f070c050102031201120609150906110a0c12050c1014060a14040b0d060c 71
    0x103a0f102c0c1b404d4000e041d68409400144540c0582540300700b00d131100090f85008880659072243c0c103414044c1060014544040c2c5041c0f140d000040640b03000f540482d1391800d540b800c000c1885510303201c020503000c0311031044005003c00d400c03450403035407113060030050320703038643d114048444441818146080c1500a00320b24070101201009101c01c00c0800e01130354001d002401d910701ca07180d04d0100018801c0581c3c8803003600a2100c204c07000c00d9901c0340030790311028220079095140e9500308826401c0f01a880f0700001d940c3c205001101042541c0b0100c1251418202c5207228110759082a0b0000c1100048140880c4d1281d0340360848000185a6002c0c2220b40c203003001c000414441500b000380c2582d800b40314a044104080003c1901250000840e084140d00040a00240302d82d49600740d5881c46080041034071440351f41c3c1090300340350803504500c905c000301014070501911081d0603c04007900b24004c64200503400304451146080c1544082080d040003804100001400d860700011101c01140040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 185451654 1250 185450404 185450407
    0x90a0911090415060330140a0e090f06120c03030d111621090e0f072007060f0f0207050f0411030408090907080f04030e0d0503030708060310020903030301150c080a0203 74
    0x51412041600070380d500c40c40e03804006c1101e04c0f402c001081c6000c0b0f031048521940011441c01c440f0351291b800c0306000040a0141500d5003048004815440001c0310520310070b00381c43c1d2164103040c0002c41d848150342c0307010700214141030106a035040a40300d48a0000c000d40820300208185031401140d001e4014080e00d8100d1035040070204a0604a0082c40c04d8014803030160010820394a0201503254002c0c015806528646c440c64000c580e0342d4070402000d02000d50503c2104805c0c00041680070440d880350319450b01010090340103946d007050241c081000350b00519010403841c00c0c1038220342c2084000910024941a0354035080300c26800035070301501e040c2d20104290000b410b003d503059802c030745507080c00c40851904124240402100801c010f0402c515829007080c1c6864141e110026140d01000756038036031800000c01080703130204840081c030900c10290300340032040e840d1003114801417015000e903203076a082c283c048402c0802c0580700d00800980628074400314409078003900d01e048103035020711b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 185452904 1250 185451654 185451683
    0x30a0605030f07030206030103060e120406020c010206101d07050c0703050703020406080c090a020c0a080304351209031b0d0207062606040b0406060c02090a09110904150603 76
    0x2519000c2d2480a64280d0b6000f1041032015a480000307032030449920400105008130400503c508169918606210300c030b80200f404202c0b00d13004a11418151803c1e4201d90076503032803011440c10b0000341c0c45007000c0c0c802ca03c6291841c2c80307110400703075070322010714242186010b4009607260b1410025034815141c54029610074400c52a16004000050a01c1d03001004038080d100009000b003480036021884407a40001c0d0390000c44002d0140800395504094007544a10345400c00054001d03802c01c20000c0d07131040d10b0ba9111040c070f0900c503140808001000301810003445400551901c540904130315178502c803c1c0080000200016a021104052240507201d007019982020f8a0107502e90401414024450200e154090f40d00d0041d101d80e00c03031041458a107888180114004000b40015a50013500b046400310301181c1100040c82c50700d100b500d0001c1c540d91640d98442c00c680d01088000c00b4041400c0fa032058524003120840c2c4c00600611851040c030741c9103044502140c500380c3c012543d03180454a0b2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 185454154 1250 185452904 185452909
    0x6150f090b0406020706051b03040605030f060405040305030a020d06150201020c070611030904111608041a180d080d050a05060a080a2a0302090a09050105060d0f020d03050708030a0605 81
    0x4000c0100301c0044a076040c41c0c1400400f0b0340f1604a0b0007030700b0802401142c40001a044801c1c69003020254106403540c2d19243c00703005000c1d90048609070440010980418407904107842501d04c156015a01d2038251389510b1201c9000c0d6000a0350000c503140c4541c0701140c078801110240c005041e45400069031030070000581420816568021818015035030009070105d5004012501c8c002d808a40000b01c0002e4071403602128042e00d02c8440078140c0080302c3c042000705140040c0207a4240c52004022803284071400203030740c801d440a0102c0c8450b036803107601d12403c00d50784503800188941102801c2001c02102d100854104032281d18099803200c050000d00e04142c200807024002c1c2c00003030000d0031459281d055400600401b040f0030f402c18502980724103824038030003802669005104c000745041004408020302a42a019505546003a010501034548841c1000403541d0280c003070b4131116029020400c40e415102420f030140308040264100240c1000000d5100715104880091800d09250a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 185455404 1250 185454154 185454167
    0x10020c0c060c3304020d03050c0a03020d080907030c031101020a0212010c1e0507030809101a1512070f14031f08070b0405040e01110c07090b0405010509010b03040606150f 75
    0x1280e006800c8080003006021800b00f0311140d1094042d00c02130b0240c800ca240850b174902c00c0204009280c0100614030082680c0851003c01c01030b0190360b16699a00c0f062202e5441d9600792000503c2c801149200300300043e08a84030103401a0140140c47c04400c103074010031841404140e262145940da491105102a044500003076069080d403070052500c21003000142c10703482601006418442d0700000200318040070000c10300d06d541c06100a000c3d8242080f01c08000030300c401c00c4544144909201c6804521143c403e403084800391400646550300d0714041501d04200700c480300c3c8208800c42500c000165050401103026080194201a000c44070610015241c0c0b07040d000150150052802040381550038020350b42912801c0314001000000c0003012030051508022482c03112038080340c02000c0303080124024046900701a4188034242e00a0104802c0b43c1003401819440103811005001c442c3c0c41102459000b44202c0c400074421f500c855800e4034902c1d041400d080011141c0d6012a801d03640003c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 185456654 1250 185455404 185455453
    0x10c0c0b0f0618091216060608030c0703120c02060412020102010b03010509100b0105071208010503061302060a0311070605010311010e040203150105031f08071d04020310020c0c060c 80
    0x1807641420341008400181d181d08084840640145910082981c41e0f40501070308081c6203280c0f426959542d0082025800030160f02c90640c0c0032441d080c4c1c000307003120003c001c40b0202203448d4050705602e4210b0740c1d4101d110441040120402000c42141c40041c0c403000000c1002d4038504400c4d070031642951000a0a5079482030030076020307074145018005400c500099003c41ca41c441000401c80030340150049941e1f01a0300405084d49000104202035590402e030101d0580b41c040d0190b0b0096516144079050fa20b400d988025000b500802c404003441d44a41c0c07001031072560201003e458110691140d2060722400e820580c0c8041d240e400c3d100b490340e00030791014070414003a201941107141802001c00b84c1844e00c4102ca040c07042c0040000c80c41502043c90940000300c180320300b0b08040d10b40100e150f880c0c1d92406503009519070308108169480704480410320980d801801401c440341d000340d2041c06504034144243c000d10030b020802c140d940c1d849001d4020343c600783d0020703c640303a14200c11000040060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 185457904 1250 185456654 185456671
    0x80610030b060616080c100203100509090d02060f180a060b0a090608030306090a02090d0b09070b040b1c0e0d05030a0501050d0b040f0804030605040516080102130302040b03030903010c0c0b 83
    0x400036482ca04d44020501c0c00665048040326403100b1391213070410700f49024401518055031000080000c41c0c040103030044e05448003510741071901c1c0e032540d0056956030303000c040c01c4c00036078070400004403c2c2d4081e02e2080d0380060b1041074401104140d007005440c0000c010000c4036119154817084441e814506c0c0c00310300900280800340b24180ca07009580d902c03440050145409070b4a42c00c001080045607404980d00d9280140681c00c1c203d04508200b503050106a03881c0c40740b8000c00e54001541c40101041d50300b5035040403d40b51070040c1c25003600000c0450b00390140000d80d02c48041c0c102c100801d0000d42d1a5106940301c585d620300c0c0c00e00d00a07040701d41c140c000c1da116218014040010410049000b644a0361000503000c0c85699403c1a55042c002e99000034401030804040000308040070490f8072600341440b06d040141d5407034416442c281d02800d1105055190341e907c040001d0700c1c080e00704100c0118007906480c0361091100c0401d080d1240032041c0c1010940d08151503041101181c1e000b0381c880380c60b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 185459154 1250 185457904 185457907
    0x50705210d1b020418140304030302010e0607120902031f0b03010b0a0b03070f05041a0406030b010e0319020a15030c0908010216020909010212161116030605040c080610030b0606 78
    0xb03070320760204110000b40068015503542000001c0c5481c81054540c84a42109510901500d0401c1055580e441804220015401d000c21465030070310000d50b141c0210381070746404c04008200c7c5010002080e4138207003030340d02d0310407100c0c03104a0100401c01030032000e514140c0850b0710f0130103000b42340c2941c080d072101034000c6183c1601003040100c04c02c00e0301e0300300000e85802d64001c0342c407a00032030f00d90103283c02120b4141000c56a920009c03958500a100f1034100b81c81c148044140d1a005543d003ea903181800e030140c010110f2040710b4142d03050141ca110344001d002e500400e031100411010b5119140b12100800c0da2030340007040d22508054050010703c031900c025850300199008884e40245104e000901400e00c000200d407410000307406481c84685a0b41490000340390000c418000d11200907174004c0810001c07001e0800b60200410a0120a62451100c00155180d0f6441d030340100b40050090310011044c1d400442c40203010302c06240076440c0027100010460642c2045980d002000c0d20a41c40b4a90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 185460404 1250 185459154 185459177
    0x1801020a080406050f040312020304061b21120f0606020c0d05031206040636060b070f1a0702061009020a1e0909230903030103050a0b04050705210d 65
    0x1507200842d001d5400d58588240c0712480a09850500c0c001c9030401840c18030380c0c940e600c3c071840c0e000000c0e100b1100d0035510308107007508034444018007280c0c449002c0d0501992031282000402d105105d00507032200b928002c000304420060f40e10440e0200880800d665490311010000c00d0340c100300140e62124100d501c8030301d2007615540c8541c0ca01ca403020180007002ca0100148480d81c0c1e42d03010400401c641d0b0846803500940d06d080c40c00c0c90b5000c0c0c0e00c00005480300900e084402c210782c451001540c040310611880c0610781d032140044803919040807602911b6889261011a8907041010302511454004014a003868481c81c45e4a06c10754202080c1d20b031051080f01041580070b846401d000d4100744081e1040444007a0032102e064154001d010850306118171701ca81d0011140000010712620511401c5c680c603610900c03900c0b0b100a20001e000e5500c20b5900c0004203119040f55038000348520100c92031141c4d41d001041c0060680840c0b9040d00c04c1110103507015000a05ca800721112052405003038428 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 185461654 1250 185460404 185460413
    0x10b01020a060507050d140613020f0412020607020414010e0702010c080619170d17151302120c0c0c0a1809230729160203010b1201021801020a 63
    0x40c2036081c09000243c5603c040f9102c207000d6070840309444c0c00044180440807103840b500c81c01482c15107280380034211382c1b02240c81a62031482990b0a43c00080d04862409141a15010000020f42d4099a0042042204030010ba882c2c0c0b04507080c540300c42c401c010342503140548051000f2002000c0f4815641812407400000d0ba0049003294000300c01c6540154a50300d50150b40540c1d0316a40018500c00c290005a054010340010242c681c0b10f80340e5109001c2081c600c084001924060f0b940d0018081510319042e118506000c10090b448080000141010310b070080340d0744a4a4203131032840588600160101c482401403060100f0400162901094985010b081100b05441100104091aa6450795400b040800c1005000a05812010262001c00d4041c410f80358000b0748030312808103640000d03089000c400d4151070740030780008070005418201507400c0c60800c200801001c9a0656884458414544d20390b014044184070b081c00041e00c5d40d1b048a41b442f58200158426070666019250080019 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 185462904 1250 185461654 185461663
    0x618030d0c18090218040f14072a05060a0b0102030c01020a0f080a020a0e090613060e0105010206010807060e0f0a090504060506100525020a03080301150e0d0f03030c0203041205011d010b0102 84
    0x42e4401d0f01d0011380700300e10300071100051119419110b02c408231700302840701c1c6590180b00c00d800b03082e070707140440340c00504181c806031a0720f06114010280d420090008419103c9035101089046041c010f680c68290038445c0b25003203034041c01e00708007c40c101c3c0d410142016032020800d0f500001041086252866009000d40200741201c181d6104201400020360381780c498009202d000181c94009010140d180c1c12003030300a40d82400303414010f00c00d03400005010707680042d80c14220b48a688440d0101d1502030280000b1180d880317181904003109100000c0d007103000d445694812400340c90002807a040400400c07440218401ca100104081400303c284100341d01003401e070946002e8034543c15094030510210301c2c003285075440504024804000000c681c0082040c00c3c41901c42a55100c08040f100010052032081030140a81b00c0c03502c0d2040d51000078040d922289120003940111303410955141ba61031450b047d18401103909944400c0280f0b0101058a074042c1c0111015000b4030041d800c4200003940d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 185464154 1250 185462904 185462947
    0xc09030c0d0201030b03120304110103051b0706060e180c310e030f13060c08040504020c070503070f0614030f0f040f020612010e0708090618030d0c180902 68
    0x41d104410710401168045c0d8000f1660110140946189120b1008404001d800c116015550145458020100f070740c0709100e064810b0b100c11801c0d25030420242e02c940784941000340c04944555032072401080b03002006124910a1031b000f00c041c1607000320119000d0404400d010003500440c9141607100307400c02504103640d101102078803400364481d0740540c0e00014100300184822680000201c03440c0c403107054001841424500200180e1041d40d03880200d80d061980c1101900c40e0f50188001d100e140342940080a00c500e02e00d045820b050313100c0c000a414101c07030340e000d101050f08040d001c010160b0059203000c2d4407803a2150f010700310304e0f103205a814400c0c4003e042414036410100014100f0800d1050181d078542c0281c41c0980b241392210643c0b4a00100380034080400c280e080020b144240300b0f482440c0b058406070040c10b590385544011651850b450780b1400b815000502810700180947d210714207020a10f42d44900700062803400c0c041d540015030304400c1e400c9004001441c1c2480d00107002018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 185465404 1250 185464154 185464159
    0x1031e0831150e010210050903031f0506091002010917030a11090d02010e060c0604080912010209011d04090b0c180105040b040e1902031003020a06020c0a0515040b0c150c09030c 78
    0x241003010f1004030700340403014411030030243c500300a10130350b800c00001075032161200d00380500082d200444008101c3d005407141540c04101001500a182080042118041201c4c000407414034100d07501c1c1c6809020041d10300c03144080100402c81b1030740d50360086411502001090925202d4200e02003420020710384070283c10320546009442d41511070900302c1d042c5c1e4400e90117440140c03e00e4541865141d01c03082c0150300c5040740001014004030184211850281d050f1034a110005001403600442c9c45240306aa40c0103560b18400400308248d040c0c9140302e44540c100c1180c6c0d03501800644000074034230240e400d04002e4180300078001c4000403002c5505582004014400590390034046039017130300c15000c1450311a030020080c008100882c180081c00c3d43e1080318041910764459400302d0703841880150340c542c000b80c5800b04000ca402c146001040f001c034071004007440e080c0ca03010940000d0340b0034510018107600c606a6600300d60720084016030041c084035452b5180032070940029942d0140c0603186032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 185466654 1250 185465404 185465417
    0x1c2c060a140103082d0403110109060e0411040807030302060603010e06060102210f04030f020103110f040306150306020a020312060d2f10020703030e0d0b01031e083115 74
    0x4081040e007403030596a0010307804d45c1080c0c0940070190105260031034801125070601818034000710303600900510f41a21015900c001644100404004c050b0500f41c1509031840001c200100e440c1c41d040c01510007550103038004299030f00340601030608440f10f031710495403150002c9060042503030b4081103121419101102d0343d20045000954180d8601c1205112892000009000400c11144481d0b012005000341c80401107490020701400c518454401c000d80c9900c2d08000600008003640e0000d00035a1002c0260342540703440b542c44004a90109000902690020803c95000b102c14040c182d8054000e540c00c680d40100c503030391380314000011980301304a41c0c03a103008075252450b5818172002d611002004402c500045480282d191756072800298006403e6400700e1035070341000302e40205c007a07501c202c00c0000c0768030303540b1107500791078103400c111014200f16103d00c40414448030241140c068100300d0070078100c0c0c0d4180101e00782e01c004080c5004021111008001d074000c0c014401d8450070f510700f41030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 185467904 1250 185466654 185466667
    0x8030f0702030d050f09011d0d0c03020708010f0219110d1209020a06091a0306030705010813060207080a0306050319140a02030609030903010c02121c2c060a14010308 73
    0xd0b400d5025040c5a8401c3c5880c0c03108110362540f040d40e00c140140180c4008014512112440f003145401d008440b405039884182900724452003880250802402407040d41c40f1107840ba0100c6d030a48904249000e03d150300800d000f05480d24040c1007140000e4241071813207111350b540b90101e84800303411303007110f060000c20010b80496180743c0e00000d10b0240d00030310782044252a400301404420880c05501000283c50004200d0182003404813070150200034010b000092504004440c441d07002010403041411500d410800180c2500203013a80d0741c8502a040d4403401c9222005046510aa204520a90124003000042c2581084041c40c00780c21a4a800038480b4a5494910380040c602c40203405210702000c100b00c0b200c004c805804c155504400a11900068140c04c9030b642030a18140301954201700002016442c401c40356480d295182e070300215103800412041c0c0ea024004480c0300c00094103560100001c454180203c5601c00a4028200250602401648284401400014424000003418 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 185469154 1250 185467904 185467907
    0x20d05072d060e1e010c0c0204020a11030a0c021f0e120f100f140609010e13020d06020d0f23090a020d03021e0a1a0406060504060b070312060308030f07 67
    0x380d01c02608000700f44254a9505081e40d40d4141d8460000032004680011080240060040081000081d501c140b44c0394825000c01c4000d41c400c0e001c00d801d01210740e80d00e100c0e52200b0700140c4601246510341d402c407420540140f02154603c00606108415009100c0d0960368121703104402c00700040d50420b01078010300c42c1c0c2d90328004c2d0302d40a00c02d40b4030410551542840c03480e00070305414003002d4810702600c007000b200302d00c0c0c03060207a950a41c0910008010f0212660000000b64458603003501c0c3c03110b031041c503004580d102c0ca042900751030241e00041c100700b08007050302441a0a0300f515000f0802540040e080822044060345d400c502c41d0880341c00b003210b0034020840d04010369001486030382102868580613560310003001080400710400289511100d50108000c0101038000d5041034001002601e00c1c0c800046c000c10445010755520740202c1c940d2168414100981060541e10303588090505001e0081490800788408640c10b0010a0001543c6081541e41040d40310380d260b90f541d20f0380c040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 185470404 1250 185469154 185469233
    0x7090b0d060b041403010f05060102060f09011401030b010306140601090b0901050405040f09050708060907031112060103051f110703030207020607080c011e051b130e0c030106020d0507 81
    0x1000c0b0940801040204010b10250f0000d101c801c0708a00030000b011416802c40291403044402d00e0142e084200012188500350000c590302072400d50000030a440301524030080120281c005a4543d0b0b03840006100300520344c0301302d1a01c2245000710090614002000a110744028012403034030f900085824031442c1d01503026070303024210040050220b00c98400030240188258081078034035200d00f48002842e0000800e4050091207050060899030b41561034640c1c59817180c1085a81000c9400a5003488000030320600b80030390700c942d01524450740080c2c1440301e40b4002800f8002080e1070081c01500424240381160401940340c00d000d602d0300444d0000809031300800c04068072400000400303404482d070650000c8400310700034800b856401c2c00b42e9071603812510202c54022070b00b141402e90302103d00c1c526025040c8102c507198142005070b00c4801d29241090261034ad54060200800180011038050107100104001c2d4038010307050443c50f450302100c40400301e07000346030400381040e03a0310401200798 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 185471654 1250 185470404 185470409
    0x11150f0309010906061e05060f0d02070c030b180307060c0302160506010f0b03090604030c02271518010909030201060302040509061509010f0506090616120f020607090b0d06 76
    0x4003912468030001e824007820111508507140307858030401080301e1113101c038045078914900e4482c0415905080a000c5980c2c41b0030b00201e03180d4424403020f05003400364001001240e1003070608458151030751819205001c0d000d086154900c8c140341010b03401c800004203441c540c81c0c006802044c0c13030b98040401e030003d200700074a60604032030042c003003000c4c018005480342c102c81900c1a040001075503041848400d00003a20103442580007000031901091180954414a40c0014000c1d501e20f01081c0006074282e54551826805103507180c204a000e00d0701520000502c3c00c203a4000e894085209030f000607400e414083c3c071041d1030351a800c8006041c401d501010143d68042c00c100083c0c03c1c070f000d440742c4c6c0b10021a0a083c014500c031190301e5890800480a60403200301d120810b20180c00c0408208490300420180c5821503070034422070f5a80701e400d2204090490040004040b0a014910010f2400c0e00c80c207039500035075020f0018403a003a03a020395088102d4a81030f28a907281d8000110306c2010b05001d9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 185472904 1250 185471654 185471677
    0xf0e1c0b01081515130b15180f060702030607110307121e17070f050c060a05061302030610050306060c06070806120705030307111804080307030605010c1115 69
    0x600108801000180b5079107000d81c14a00c3c10b405a44c1d112158283c2c8007002419a00705070341e036100e4414840650030018000900a2100c81400c01094404602c0d030880c903482c04079084c18500d515100e09000700600c04451090300d46928000d8946c02003036a03050060400f03402c0001c10442160700d00000d1082e913041c01e03400b00080d031240300f00900c000c01e080c410b5459416205070a05901c50558041d829a2010011000400084d503807801000c5d2000d80c50b050080007404030030004404950020312080e480b41d240307080d0000e1181051814402030181084e42026072510400074401150394109030860303007801d81d2078525aa1303610840070070b14500621000480b00e12411052040b141d4205d10001d103d442d0689410200780c0e10b0745201503546001380314603505900100b260801241558409072940c04d00a808081c2900d00300810403118001114142c6400c0070101c01d0104003540350046200414003440d240c2d11015017525000c10a600360041c441c850f100c0804105c1d5001503a03400d59103070381d061 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 185474154 1250 185472904 185472923
    0x4022b060207060219080610030b060702030304090603062d0b01031119080c0715051b0a0302070c120201120f0f090c0905010828020102011803030902100f0e1c 70
    0x79860300c00060341185045e12001d10002e1003001c0142d1142070800e10618004150542200e85d4a034103400920701c100030303240c001508205038805628104002c0c0001c080443e030000e105859410240102c41000e03c89070710b02558400000f0708840303800b901030403469140300000b480382285801070b40141401401106140747c00300d00c03401c1c0620150081c644800080d12500440d039910078501c800c5120790304d002440a501502110003010050b0310495000b600141a07079052415a000103005400c9a40308000094000544604021001050740b000700b200f501e2141911001c1e50001e40004812021a4900c80e40c51110350500c1c11607811a111080c6881410010325600d4280001001514041d142c1d400b41045e00024003081c00203412450b840880c0c0008141420009012100e403001c00707020b07030466407201c180071002110340780e0a8444602c00d0710005000000c0c1c0c4144915100c00106c032000b8030240001b5170084a0704440780e40441c40302240c20030384200c40c0c061545101c1e000ca05018052900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 185475404 1250 185474154 185474167
    0x20a08010b040c02010e030409151a0301060f02030a0806040906060306050106020a0303110901200a060f050a0c0e09151207080607180503030d050702010f0912030e0604022b0602 78
    0x1066200e80c81c00c000c15039041c40b6803240514280d0984100058065142d40308000c1041a4042d0794000c40d000719641101500240e610301310f181d40780841000f03459800d04000010042d064128130080c2c14030300302d07001441c201080c8420240131003000400140c0100d07241e03000c1c813003000300f0b607031003c0050765000c4070070003440d43c4810b0b0080d540e5a2008044002c28a001c0c8121800d074090020b6400c10a41603503200503201d41c100741c2c81098006602844a030b841291414000150140100c0480103004400000c451625810210696005a003c0424000645d00380065611000445a40303e0000350400746040c00034800f06905900e03807510b039842070041c00d4010030002c07008a55036000305043e0340c5441c000711881e0700010700c8002c6d80c400d00d50b0503401008401e444001c03c1c2c101960213202400001041003900c2c02030005d6980d004411110400b8084201c0340c0c0a405201d1140a0340500700100210320b00b550218a84038001400404d9610843c010b0040c0d00710b4031030381110740b9039100c2c00a40d00c0d0903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 185476654 1250 185475404 185475419
    0x110f03011109031509030304020f010507050a05010c0f03021309020f041a04032d030e270105030d030c05090d08072015030f0f06041104060203130906050328020a 71
    0x4011100003403284c0288841c900c8169504888140a0300c029005140340d51201c1e420440c016800c1724040c0c1c1404030600c9124041241440340441c0300d40200008508140407000040c1a07201d00c0690005043c811b005140c445a045d02c1c05400340c0b5950040183d94101941c0780308101d008542c010a00da10710107044800039032841c8043c008503803259521180f8068411441d22102d40c207015101e400c0c1c001d503004100442d00c282078440c0510400f8105459080148004449409121034440c1064407414010007003030804002800010020f07107000c02c01000c81c46801040c80c800ea001c518410042d8024030307010301803c2c0e0201c80489901845d40c100b0748840144a0b01c00c1c0041c0c3d40d00911840c8010180040c8414880441340300f904074510324145541e4520010545190117010660420303510042101400120340c02003001d170100e50002c5032910410500c814001c01150000030b55541400d03001c1015480015008820344404841d4519114114000d00441d01d00c40e0000b95000c03400300e500141303c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 185477904 1250 185476654 185476657
    0x706050402030c1011071a0304030c0312020307030e0d0e0a0329090d03060902070209060d0c09050c12090703031418030109060c1e0e0f060702060a090e0114010c110f030111 76
    0x901030009842c0e40c1c658408498800b42c1d00084e0400040b1710410006000038481c412f03c0d14000e1090034000055582070400b8403c0fa0021103010010a950f150490f9480e40f040180d0740610f41146003055900b6110000310381d5082e41c0d0702c0028410311700709100c020341003110014071900c03030140100e0300214030b851a420b9903a488451320f0007010900e41000415003440074003c542415401600c0004551605410320010242421058902c422030920105454403c0c0c050784d0b01600d4030502c500d8561400d032031450340580d4050100c407407070781c40711340c04000007504040c440020303007807000c0c440e61a2042843c00f04140b4013442841d50b459480c1ca132401c030820509600007540040a0760724501120340300150280d4400520703490502060811401c03030003d1400c02140428007502400f40380c1040b80d10303804074a0a401104101e004140c44007014080358041c0c1c1006401000e00e4039845d480319042d1000030b08456489400502102c020040546181d19001040612000080c0003040000400c0390603e034107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 185479154 1250 185477904 185477927
    0x60a0e120120030103030905120f0d020105070908060108060406090f0b19060b0936040b06180c07020d030e1819020406021c02121306020c060f0706050402030c10 71
    0x400901c1982090860305500f62030603613a15484176407600d03040900700882c650011070f89061a02c64488200c145440c01d004a0402e14200d4001180300d040a50028200340b800381c001c0e0070785502004c01080780440003d20030381c100b5003111000a4448041c2007a401c0c209580102800045012060059020305101180b00600d4200380c01c1059070386038414802d591142d03c400e250700559031080340910384140184460940e00c41a202442400e80240440ca20f5104850941d49900c411080101c54182a84124855542c0703510420503407901582c1d145141c050510040d000700004402441018001d4003501e41c40c200050103c0c0c03031074091024840e005075003126050148800120343d403182111500070746003603e0094015010b03000f0703c1d04200c8206058010b240045200e420296851040c8410061006511020310064491308000700a4030788110060001c1c010300b02001062560030b02c020070f5440d000d50080c40402c441d00e483c000640381240f18030100382c0c0500d1400e130086140d504900b95030b61 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 185480404 1250 185479154 185479181
    0x114030106050406180302092e080c0f030102041d0405070504050109090201030e0706120e010209060403150b061602210d0309020a080708030a1119030833060a0e1201 73
    0x18030b0405042c0070140041741c40002e4000c003d5074049400301041c0010303070062203e101070b4019a400d015064205010f81580500c1c820b40081d28a01c00710300f800c221445d070070241900203628051800829034040668007040c03030040d401000105d41000020321801c801014000c20038844c07540c44c1e04045000b8401d54030224046860a0400c400c0e4040200c0c80c181110160788407810840070044028018110b0810790141d20355003041580096038070034010300040c1d40a021240c640b500120b03007240c125103000c01c6081c130801c401c1c88441d01c1600480d0142880c01d41c1603070381105104e585500705a00f0071a10040070b0141c0502462828400d80c1503114080c0103000700c4004462654411503552184d03000d0092038031540041000c4c401320340c010b201204c002c216500841f054004005102c20103000034190840c0024000000e1180200180c1810054468071100d82c5000b115007010100c525441c44600501540b408219903003040e008401070b61031100c000e01549032a1010705025402803290541281 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 185481654 1250 185480404 185480417
    0x30901121b2a200d05010c09050117060d2033040510051303050a030f081501120f0f050421020a030203040e0c0c031b0c0f011205060114030106050406 66
    0x404001150001003001d98002d03803d00020f10040302d07204040325101c40c2480d007201c4201e084400052003485801c00b0b19400b99120b12903c0d05000004045105460308174808509103018000946e40e01561080c040f60710442c800c070420105e0130f03940a10405548101d502c88141403282e19010f8442200002c81e085004d40410004003043c2010841c0c0594081c1d290020501c0106500c82c40c00744004000381c2080710030913240d0641d65965a403503e445801c0440c0081c11412004800d00d4108200c650480115040c50303c1c041e000000080081c00010a42c002442e2182101d03d000d909030303446040900c3d82940103015500d40f5080000d56482041a4003024500303109485682e1440031600498407035069018500d054603000b542c2c40e2100010f0b0078041e8143c0100702a60310f0341c40401c024502140e11000d8140c00c00c22840d107103402c10b10440700c641c2c0181e84001c21100fa50307074403800c1070304007540711800050952a02d90048809284c4014521314001c3d0010000c02c1141d0000081c2040f100140d0b0744071b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 185482904 1250 185481654 185481707
    0x70302030c01110705060304022214070f0503040b100909050a170f070602090109120b0601020c010905030d35010806070306030f08160206030a0c09080708030901121b 73
    0x110750b031030501040451260031004c3d00b403006180100003160014001000303903400000301d004120f6000c0c8514138880c4499940e040328449500d205503201d41c002840d05114101c4400404098610310008200070b00207c6200300050290300007801803006488a14030421a55905140032a680c5403032210586480b001c0303450301c141c0059910121404030400000c441d04182c3e19a86410103500220440d6050105400000c52001440c05000d40b085000b0710702402c0c0c0c0d0618800290501c01002a1181041401441802aa200040e00d102e5812984c40e0402c050f03c0c50003d400c00742c0080c00084910446030f0320f1564880c00070300c1c0034030341660740400a8410715200c1085c250121003003844000d000001b241401d4002c10303079140190181d4011000700703e03809405540055850f0388111800e4004941da900e495200c4e075400241c51015101c131000904040e400d00514941d2030060b50f4000e0b040000041c40e22000087c1500406030000240b03101808070810994094841510586600c50603401c40c02070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 185484154 1250 185482904 185482907
    0xf0908120a0e06190e0726120405030c01051e0307050403140c01140904090f0302011b030c09050105070206090406090204080c0415090e0a14100b0402090108040308060109030b090a03110706080f0402040906050702070302030c01 99
    0x27141d0460390014001c08d0182410b000649468000c00800c01d690250740184541d400c1440008600c15015a540c2543e140d0540c0307407410001640c21615989076100e0740310440b499800100085803811a00c0103d0f440d007510000003006031664040080602d40e80048103410140c054010082c0001d4080e0190a00441480124102d520490141000400903a0b04100c19401070009000c0d450015007014a00034a030f001180581d5140d9011100441d07002804000b080c20503c4070002c0488200d40601042c0340302c040c0804c0000f200c1c052001d03011b42c0c1e46400741c441c010421001840070307841070510b00c0c1c0e6071100721000d485114a80218080508100061780b40385001e10032500030b144140c581015548680d00c048511a400030502030500600840200c00728000c208075910642d401d6001700b00441d40381c6001421003044240a020310390080009001d5035400c01e40856000c00c00c401d180c4000d907550700005000d4040c002e805800c4500c1e01c010300054581c0401c2080c20b5034003e50031038840080c01c500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 185485404 1250 185484154 185484157
    0x60601030c08160c06110319050714040e0603031c050a0c0e090403030b04150305010204030c05121203092a180702030d0f0908120a0e06190e072612 65
    0x40c4010f0b5003201c02c000c9543d9500a062101c02540102e0000489039a40c1134049015071050302c81c80c0b10720f0101c6001c501318903903d00440f540b203c007e00e000c80c183d008032120720400d4016070082c0007000c20044006103030cd4030200301b6180c0c080300000e11003aa0721444c23803515000344015515141c1007410710300f5506005020fa20304915a0401601c90820340d07a0302e880481c0101140c248542d40903131100916212940300403807682c0698010310005030350310b10f54642000c6400e03240c0c0c403190285080480f0340c003045c500400d07400f5905a0516029980e0b580e0308460505150116007610001e4004050120280103c40d5800b01942026079542d00700b1110394040000c0b98904450010040c3e2081141c4510030350103401c80304044e0005d18000c03982c04459602c40b4035a80021103c11203c015500400002103454001d51001d540e60201405060600030302d4080d42040c40c0d1814440c46841c0d1000218102040041c4802808118042e81042d8000300c0c1da01ca02c4100d4805403181c5100300e000e0051100304440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 185486654 1250 185485404 185485411
    0x506060109030206030f06030a0813180e07150c020d21030515010c0f06020301030b1f06170403052206030e0c0907110709020c0a03110a1101120f020408060601030c08 73
    0x113004500f556200c2190414000000b4115500360050f150b203000012000800b03080c007100b504810000290510544000050045026030002c0d030801c282031030205004644c00040e28402c062060510501100c261050b1450700c800a400000490f090014001e9910512000d103084a0344039500d13648400088042e100182d41450326130340c3c2407a240d9000d6000d81c2d0041740ca44d201c0c4001c80080c2e14213450b20000c0381c200b64410742f800e52800341001844144000480a01024070b11013440540c10030000814010a540081180f2080c1c14040340900d4052000d80d40c80f8070000d0214550359030551510010b8860303510a41d4046400d00000141025000c04c1034040306a0207031840341d00303507a40e03c4126070b121030819451500380210f03d008038203107416000614184001c0d0703005040603506460001c00f2109015464813254100b403020000040403c0003030039921109107450030388042003608240007844003441d480c440c1031000a000501c45404600c051082a098a08204502c0382d290240c0700e25038100e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 185487904 1250 185486654 185486659
    0x13090605090604091713090f090b01050a0609061d060703030b1c11060d091a010501080606072f0d0b01030623010308132112031503080d0f1805060601090302 69
    0x5d01500800b81c154050124000c68540d4080601d540d69280350440b00011980a00183c0b600c01000a10180305940c6004110964001c031700b19103805401461f00421340180c030200310f02c00c10240c21002e944600c07000c1c0310100601d13031035440d001440e02074010903110b0700840c00b83c002007804d004040c480d800e145840c140c00041d40951b5a10100400a0b00c0e4444521601034560380d003a13540c0426440c103d00e640e40d0013031084002d1036505200001d0000d4030000c0c1403620401d8100721500c002254a031090100c0c15550700b160201d0542140c881001984c1700e500c058000c00c0904018080c03000810880303040b64062001041281003880d21203900c2882c030b02601e40c105401100410010b070880e0300070705028080c40c40000d20306880b4550560b1410070a4115401000b101c0311641c00c0c000c0500d10301c0001c2d421400d0410202491348406026030742d0b140300182518202040303006004089801103040300c40388880030440000750241c110030804c0180c2050360240704441c0010010350041741d135103050b203400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 185489154 1250 185487904 185487923
    0x8030d020d06090e0a06050105030309060405010c0212010c1d040614130f05040f060e06010807050123030c041a0a090b030c120a0c0f140d0e031309060509060409 71
    0x841010402a5201c455a000c03056995640003980030054412084041035107800360850b410a41422020348606800007440f9820400c00500c50f540d41604880c01c0b41d000f0309110308802c00c036000041d10f45407107128a90440d402c1c0034802d1116580110700560920010785c40724124101c5030148400c8542500400c0c01b08102c5842c1100d051a01e45200308110642c00c0001c52008121000d81c410b448040c0c8044909a00400044080214030b00822000018000003041150f04d810f41c1c2d503580720041e105590501c9110180c06048a0840d240100d18003901c00c1059503908000350301d0401a402840f400c2860316541382e82008026503a800c8952862943e0350b10785000e0305045081000d0b520160191295610800025003643d16002c24540726440c0090f00242211070600003502110042c0381080c100301d9040d840c07540010500082d55403003080c01764006002c03050510704619602c20041c105e1040315a88030300240c40c6080380c022509840055403030400b6a101c1005000542c0c1c100e1318010403103401d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 185490404 1250 185489154 185489167
    0x71d0406180f030512070c0b060105030702030d05040b160507050601210b040302070f0f03020607110f0d0819080c0d0c09091d010e0f1e01060e09030c010f060803 71
    0x2880d0401d803004000100390210104035907885941c0d098511a0407400304070007003807078083c6603207903d1069480321141c00c00042c010440ea68020740540300800310390502001001042c5060710070003e90f80300d820201c40170007550803c0d00b0203441d00074049940d882c1100340001d516064503c544203442c24194008002c20030f50342000c2032511102000c40402c14260003481004010419003000c0b20301440c00f0790081c1058600b49000664641c0c3c89030440c40e03540084480800050319444111103003150401c032075004031148140000d03100803a012210344e01c01c641c42070040a20031039900501ca4250340c4401e40310321100780304040e102c0c444119902c54407800f051110f00b00c0594130ba00400b204250602e4080c24194884054004070380b0440b030b181d8030350035041d0499030008000344100802c035012a8001e004542c07404403542e40c3d404021844101076104ca01e203820104100350070041c0602000c1303502c2d50b42460500013250b41c03604210070303103c101e40c01c4c0200d44540359400c1c824501501e075210007940c60081d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 185491654 1250 185490404 185490413
    0x1505070305070f050c06041d0709081b13020304141c0c0f050115060c03021203010509011802070c09090201030b091501050a020709051302030d030501050130050f0702071d04 76
    0x11900205594174000c51428070155601c9500802c0640540d803060344440c0c4e60b100820001d60390041c0031405003c2401c40a2043c101c0000340c100c100c045d050008510992070001154840c901c10750700442c6280080288020840d1848164000081c29802c862545041448006614120703025100100f15a6607000c0045171410001945c514040c50000c40c030310341d0301e0041071031004030781e4410400039040d1002001010360511200d0103002400c82c09504650411001036080e00061007120035050b0405040c07100d000494042d24429500040240d000c0341d55800700703034060030501c0030480c0003a207010005c0c00c007450070356401d6004401d03005e12100c90f15403000040d9400c0c0c2c05465190190b00c03824900049486c40c500410380f1034423802c80f034a45100418814146003403452040f4005060401005005d640d13446840c907900600113242850980e180a010000300d0f1691a1590f030b102401d003020442541003020010340140d05a034210b0710f61660702c1900e01c041158096103070030204200d002040c0481d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 185492904 1250 185491654 185491673
    0x301090e0114070f090b1801051608030c0405042711030115080a140303010b09010c06180b0f0901090f020405090c03030d0c0810081e070b04080601150507030507 71
    0x88103038000040d5841014111101d907a0007180e80c0c000140909060012165000c2201e070010030194240700d0800b10f940c041120b642070182e5003141008000b207841c80400709000c0c25084c101c0e4100291b182e1702e04007404103070030304d5105014550250b410b007400c0305103c0100c400907004890158510940100081e0341c2d030010b04003003480c40b907450740d2600700d076005c103c4030f1014581c010140003000740030704c00d43c51900c801d00f602e094403031809581040c030040020081080c11686200400d01c1c000340071a03801e1408600801100c511f8024044154400c035080108540c0418001e50100c2054000c40e40e030b5034441800e80f215a0300007403ca03000821140b006040c603801c5140c0141070031007692942c0010602003841c41c0c0142d60b81003001d83d00c0e00006019513402128080e00b0076580c0b4401d4640790b05012915949000000b0341c40964110002c022a050005010720702c041c0010602d11580da6958a5400d65225400e016920715181c074a0050b0200ba80920101c0c0c070307215403548449042c511981c5810411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 185494154 1250 185492904 185492921
    0xe0904020411041e03141504080c03040e0f15030f0d1107080307080d0f090206070201200d050c07090b0a0308030702010f0914250b0f0d060303050703180b030109 71
    0x44080a10010890040f60002008403d0807580354201c4ca500d54103144200c40c80e070b1500341029821032216103505401c2040340741d81c401d8014056503910100c07001c07424034500c1507500090184010704284100c280d0040c0b4998000d2102c440f1016105544a0404d51036801000d0002da455101005450100703008610850b04a508102614451656420781e42c3c103590000404540584001840ba0fa29012500c00c080c0d83c44080700c2c0c00c00c203100c1d03141e0100e8160f21420703a0180c14015000c071400907450500c044620280024020389490300d445207009012178100780060f2241d401864408074983c203143c860403c0f100c1008220030707000c5166480340740f404d51001c3c224000b15500d44054000f034030500e00800369861311945000020380500000103041400494500040d50910042d0114012156000405a40014107030a136204001d65074a01c25105940e941512181000000010b064002e805040c1d0b0902a07202c003150021400c080280d028154001d415000c1e6051006120904456000001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 185495404 1250 185494154 185494181
    0x15061202040b030103050604140111030406090602070515012303030a0e03030c0d0903020a06050a020a1203090b090105040302011407051623060403030c0212040e06030a0c03031e0e09040204 83
    0x90551a2a6020b0703899009030010f840f154082410720041000f2810340941900030710f00200000c192420b0004540e02c000340015182c640c603202c00710107000b4075504a074080b684c031404403080300196a8070802d6000f001d104624004c0041840c0040110011003064031f00b01004000e14500702025400f0b5419a190043e03841d010b200034442d402e2444010000c82c80e46622075141c10081902d54410042208803580005041240c2400100100394000400a4419920400c01c1e82c403c07138418011402044480b10141c440c0c4821010311640e40d0043d449031303004070300030703802801192110059484010015101c05000403020013942c2e0404007000d071091100d40c81000c410a2200640d0200180b0380e036070704003408440c0c00800a000403d078040c460380b400c2c6201e50000d08040820000f5000c180d008900c1a260006019400503204c2c1e42c0600031040413941c4103001c2c00d00c003500d81c100244042210032521030300c5000d011103850044d0150780c048180315402080e610840d034890742444064901c9040000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 185496654 1250 185495404 185495407
    0x1208030414060a0207151b08090f030a08100e01030302030f0309031c0f060e1b0711040c020d030b030a0b15041d0c0a09110f0304051603060605030c030115061202 71
    0x740c40307450500803640901d0040501580316100ca00341801c0000403140071170b07901840d220308001041c00c201800c409155007230030200c0003a9202e03c4018101090181001d1103400001280320005c0d80000c40c0c00c0c0920b07026482d03409032988035010210400000e000c0079001d0b03030041c894107091481207801141d02c074552405407410100410280390400c4440340704010465120b0f03150001aa565200300002481d0240403a90a03041c12001c12078021941c0d00500b18801c4002010001d100860550071000c000140080148049009009450710b00710441c880c0000d04104e0f45060768640014070902c665007001f141d14007a02c9480300880406000d81c00990055118400414040203546030f21241d4850100500341c4003030800f04000c0b909080c0d800c54900c0c140f800c030300c1003c07041c984010b88801100c0e5810b07183c0c0e80d4586007002890110208074580c5d0780d40d5280c1c070200800c80740340c124100f294030903005c480e800d040c04d100301802d0310181100f00c000c10b800c003034081204038882e011000703542000c9040107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 185497904 1250 185496654 185496683
    0x4030803180a0c06021c050a0e1810050901150e0108070c0b071827020309150c0403020a24081302090103050114010f1a09040b030f1b0a12080304 64
    0x2542840501801902c900f030030a2420801190180a500c10707640c1da141c2e032a48501e422039405081030007204048001c101c003840c81d100540d00c07000b40088a03280380b08080d1890b450840104101c1c942c0301e004190003401c011000007014010311160050f070204076110b03420390f00580401141c410b070005150300c0400c5211201c03540810080c1c40240e000711040d9844000b98400d00f4880d4809071820380c01100842e02c00d945146410005c1d02c047c0318110151840546c1eaa10f50f02002881d2440000300030b60142c21250500c0f040394000001082124420b8410342c860380d6480c26074491075100d01d419075a00c28108110013400340d11070071200c0c1d4000f4241e0481e26071100503402091500304240c004840c103039900c45100620032503854645004001d844c03c4500c00c80e00344010452100800e000254456201044100060707449400c80240d14001604480180446a80c419901d1803024a20b1402a40d101800c48950a101541078190382c0942280819001d544d508c0301c00d194401042580e60b1490031014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 185499154 1250 185497904 185497951
    0xc061d04020d0f0b15070803100f090e1506011d130c03090605060904050d0f031d060609010506043006142d0a0902010908030d02040905060301090804030803 69
    0x80d1220042c0500002a074200f009640001c980c1650310803846864a401084a4101c01c6001c64100640c4910580d4813a15100c1401d650b4102903005032088400b46540450443c6095000c2c0610f03008032411111021002044804146000e03900203000072511841f5409402682c4204164101d0203000050f00311800b00512003180c4d040c00c030f03800000b510380184100b4003100d0300615421039030880d4124040c0c1030559070141e45800c03c402c003d050015648550503000c0c06035100004001e031013101d10091102400c8100c0e10769008990491040024a0001c1014200201038505982d50114080e0410340e442c0300c16141004d441010034002e05034043c2d20000a01c560061404130300007224007445e2801c0462601d2807030040c5040140140c034034904039126480c499040303640c1107102550700103200b82003800104d0ba14103c0d608040814030000884a400201c150b0081080301e250480c104960340f2100205402d0729403c01c03019040e02014001400480c642a0055411020103402c4007101030301d0319903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 185500404 1250 185499154 185499157
    0x90d020117070e040f0e0a02090406140c04150206011406070512121e070806120a06290402070503040506091306120b0a09020109061101020f0c0703050d0504030c061d0402 75
    0x1c0242c0010b01c14840806603081c0360140c501c18a10805c0113008040850b82203c5c0d0300c01c21040c000e44501d41e604049000d04c052a401060101e0142e8020026171030548009181540580715071246401603c024064403440443c90f94182c440142907101c213035402c101080381d240c008440940c2d00303001d4145404645405c41d8014109400b018909081500d820b6058105403508041b0702d4401c07503901c90400c91000d501041d0a039015408440c04143e81203034800003490150740c2c24004004500e0301c9040300300c3c8614200355000155004070540c0d8000c80c4c08081c4001d078002c1c6c4134010950740c000d00c07050120341303412401383c0b0343c104010b0f00c226030011428400f60140e03000340e400801d50010b01e4408805202c256401d184c2d00c81d45030035050000c0442940000d1a1004034495a0f08204107400390805129081d01121648045c01c0401515800748400c0d10362100740354401101c041c82520100d20020b8042c0c1c051703074216038020081c000c5951a20400380c0c0d100d2490f84106001800001907084c081c2d96910 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 185501654 1250 185500404 185500411
    0x20f0403051506090712050c0d0903020a140a03020a080309030f0d09020a0605040b0910050c0106031a0105010305011d0603072315090a030311070f0612050f0c090d020117 75
    0x1c008000584809074480307100711026001c00d0240007001c0810114a401502820022601000004980c6e6070980c01c0d1405000304480c80000c2420300c000e083c1450340c00505980540d00840103c60342240c81c2554030f944940141c00100503030040008180400d8a05024660001c5020184c074540100f1601c518055817020030080c5001c0da94419807000d50800340c90520103070146061451515044c02d110070000d01480600d03d01c07805400c0090403003603100d04142c0303585144850090120580764a41074017400c0d011202290b04481c40400041c040d03101c0e00855040700e0b034040140c0f0b1000b145080070028080001d11054041c82501c10024280108800400303c1145510010000a9910b41003160308000c4162010f185541482240710310b51b0317454885421680d050402e28a00c51003102003904040781c40d448030740045042c03d000500240c100d001e03855040500041005240d8a07483d03070a80c000030030f5030001c0c82150148500b140d60f080c91390300e2856030f41c01410320700c0c054040310382101403092003103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 185502904 1250 185501654 185501663
    0x7031209090605041802060307230408010b0613060f02122715040909061b051b030309070e0603100f06050f0d05120715020c03070b011212030e01020f0403 68
    0x86034200584900c9125110180c24112000e00c8a070108041d890080c20300f02c580030b88181c5000011a55580c0981c0c4810400c00400c0703440065846941c075507035401d40003881a40059400d250001a00d89040d000711030752100c9070f01d981e07800b0500b8001d003154810384a03044441984078081c0c03a90205034260001c1c0803209451203a9540703180340184c0405000b02c81d903040901400c0118218152071103100700362015910402400035150516060000140130203000600c038030480e203100602c1c030a5000300109082e0a9140b0381c82c00034404120865603e10048030f50052a420580041c451004205051600104000c2c00c40e2551001da00d01e21080f150203903009446665504010003250070300d5140000c1210341142d42944514964962946034442c2c080c00703a006c01d1001608008000c2c0300781007041082c02c5480c0031500c0b0b400381d14009139241d006c2c940690b0b070b0001d10800040d80300101628006003070350107800031054060700c40c000c0d009082c00c00d110a0442d50280080c10b40d808a4002900045018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 185504154 1250 185502904 185502917
    0x27080901111504030509010c080c010509010b0a030506190f1407020c010f200f030304030503010f050409080a030f0e15011805010e160e040f0e070e07020c090603070312 74
    0x208000501624920340a900e8242c01aa0300d5031281102d081c80b030ba0b4056050b0611642d41c0090320b004866100388070900a00c403c0e4007242c05800c0490540c0002e1141c00c001008120b00e14180c020044200f22922008000d5804500011008040d80f84024054203030000c010031011103414040040d81c0300d000002e4801ca00240030016110707810060784c01020b02c2800c15800409501800410303859400380c1c50007855030546900000c03610100454030b0000151010340f41c4a08080c40d0040060f4405c0c4902180d002d0510310100f013614241c42041005030344800310519003914102c0c20390143c1345600d0b040096558610a082c107064060101044002002c99508002d6041415204034001800d84250000389444014011245100e41854008501e20441d0099441e2448100c0d0480500c04920f0341103420046480502030709500008211540c5205454006486030341c1c100c0401c40c00c071214001a0f1081021300b00074280302004a400c600080c05940c00c05840361158001002c01240000c0080e50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 185505404 1250 185504154 185504167
    0xf04020301060b090a0303140c0a1a070f09051905042c0303070c030c0512040f0302030c03120307210c05070506010e04080316120504060b13020f030a2708 68
    0x8080c40b460340509811103101c0d0900000e01c0200d80d001c0360702d000c000d00f4000300c0a00311a14140a0040d00c200d800c040044803000510b51a0144952031002e044800000c81c0c3d6000c60303101030044104241c03104ca542d8550f20524900701c1001000d500803000c00d0864040384002080d2a100c500880c0d115030030517200d0f0b100041c10b07860700700061a0503000c0000c8a42090061040582c0e018129180300c5801d0301c1c101c545040c003401d100b8104207035000388501d20a00001c000444940d110b0700c00781104e00071003da601d10112503041c036840d204240c1e2a08544901000010003c034000c0c0250070b011220f03207894140000030f800700da108561843d02400d0102d000400c101040210400c030542c0980002e290012090606a0303030401710b808041c0100c4d1105491620f00d4580b03038850500d030a45034184003818800c50510f0704140e13009100d41e030400fa000e03060841b0380e030b034640419000b12403a082140f0111442e5681d4002c6210090034070000c4041c8030160300700c1040201c2c4080c1c0c00380350b42a01520030a80d0b81d40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 185506654 1250 185505404 185505409
    0xa15090221120301030804091d1605090901230c07020d050c040501052202090d0b040b091c02030f09061306120b0f030c0120190b0f1603020d020904050f0402 69
    0x600c1d5a1140c02c520400050001980c614161801c8511001000c01c800850000710824141d800340750280300c0c4610a00040d12410103c03035142145c0c0180c4100b0300707540310180d08900f680c4d61030707410480340c0e409100c5041406000c03d148590203050740d24124241512a40010301c0140c550030140c40d07030303030140c1040211803400d40300d118010b10044440d941c00609142051207484001501c040c00a980801d03c5090f640b250482c0001440d4000201901d5190610740b02e80ca610702a17521407060303c07404500d142c201e545800d0241c0c850741150011401d00510030349000183d407080c45102d40002081c420f014218002881c1103015006a0300d42c401c4203c44100c501046071510820b5900c0f50821444000302d685001c5500c0a02c004213107030001c000400c41071004c00c6043e8000c0d10104c2441000700d80d41c1c01c04412405010264840c0b40510031030340754521800705c00354041d40c56155103900d410100440d103019038000e000549a9241c05030412903044001400c58004540011041961908000861 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 185507904 1250 185506654 185506663
    0x4230309030615091603020f0415020609060108070b0d0f0501061d01140702091305030301060e01110607050406051b0304120b0708151002070e1005120f0a15090221 72
    0x190030343c1542070381c0da03003407100144050901034510408502ca02e0b16070900c01e48280c0480303058a090004090390b4690311003071a60105c003210f42050041c0070300c4d400f00e0b00042001c07401a0485000000811032582401c80e003003540c0e4805500012400d680b07454240b8100064001c81c1e00801c0c42d901c51a054080c05000d01030b06948280b00c030790400942c40020780240705040180c0d680184c05030740b81ca8ad16038600b4040082c0b0741030b48502810134030010000107a001e62004413004810400ea90302c040b281c101c00441030781c4107015503143c000315200780030234040030384580b000e40010300910070795502e007180c3c0e1000d10b82140d0140e003041100c024400070356401e00000e601c015030030100034a00600b5520349102c910680c1a20a04800d1041c0310050102024074420040f101c05080e4050a50398142011001200401098030545006008144142030185000702d05407005003050030141140d80100c0d541c4614901604206101d001d07520b035282e03400344c0c56104c5140100c904581c0e00145168581d6501c5241 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 185509154 1250 185507904 185507911
    0x7090e160602071404020d1a1503130228060906090806091e1501090f0510060c11040912121b02030d05071407050a0c0923042303090306 60
    0x4500034030804000490b0300203080b8044030328000304002c020b0b1004000030040c2c070072100c44600850420b0001070102102c3d606101580710201d5a03130809111504c81c5400c00d01046500d200c201405050301c10150510005403444c400e0300d200320142030031404804110480454200d2000249004024454070f81c03c081484040c01440000703140c0c3d0300e40f000d6420ba40e11250b82013519428800f18000044d100c04011f031101c03c0c101495071001d150784074490080201820b01e4200001c0b030030040490b188003040d0781c0c00e2080e110036541341b5045101a484481080c1c1442c404a41c110303550b1030010002c65040d60b2482c2e00620340c1d60b29074000202e000f00d480b068a001380083c0880e91550503e4258840d000411290103107031560010466550380c510544100c40c0640c21264040c00000d080e5003080f0022078507103041441ba80c5070310b6900d5101c807030f144212500308060501c15202c0e1182d2401101819510590092098003050080d920810b42c542c50b620b0902444210340e0710110b2010820316090101591 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 185510404 1250 185509154 185509183
    0xb01051305010302030c100201022a0c0108070804060510031211010b0a0807060c0c0b070302030c120301120f21020c03070b030f0103081c1503120c05031902010b0307090e 75
    0x30a50444c0c0000e6110000c00c000300b40b003401485050f000c00390003074061b50103808031049940d140c807c895580c9411500c01c0858111140141e88040f007456020f46000390241d103207603542c1c816559403a600c1c0380040c030000d0201c0c5610700c8040400400900028117001e6111403039521400400076201826007591200c2c0d88292041e000080240081080017980000f155050310f00304d41c0700441c90800030000030b080c0d0080305040c00001410018035400100506024540c0c1c001c0b58101650603805602c580020b0064000030b48070300d4424400308036625841742045000307600440c1302208010800e01400d0110f54804056005000b8000035450144107150041144ca201d451070b51400d01056030180d201408001d10207200890180042d00b2088103000d40d500c3e01d02030800034810209600034a180052004441c10000c2c1c82140d000700d0702ca40c010b00c002c5c1e5804801541031032098070f0280d1240c105101100115940c03020610215941004040c0081c204c4410004400c88030448045c1006e142e551000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 185511654 1250 185510404 185510411
    0x27090b01080f092a12070e0114130b03030d0606081603050c070b1b04030503030f070f021c03020f03010f06090b0f03060904030e10021506011403060d060e06040b010513 74
    0x58000780110f100e81c00401a101d001034201900013a0500805103d5425078210341e5000c1c030a021407a0006106081c1d82032422a006176a907034114020080b40c40140342c541003c002c0741d020000b0b00071070304040008140101501d0a040b420041d9100f03c519540c0050300142004052001a5980d4241c0818204180c5814807244c58184404c0b44244036103100105103852600004100d2180c580c4281020740306d5100c80c42ea625902c0c00d20507500d8101b643d0401d00340c2c0d1910040741c503441c000d0b0381d48190031040350054060080b200800e0803400710b00045103002e00d602004104045141c12001314068103c402c40440500c1c00c1ca20000c2045995400000707000d82c080001c034492161031801d403230740840103c80110444c1d0720b03442c042310868080a0060b0300894004a030403034050700403e07078040406c00980d4042c507595a000044410258060f400300c5000381c1040464000d04100f200c0100840c0030b54000301320141506842072400e0011502500c07032501000051106140c800b003003100d260b00025080c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 185512904 1250 185511654 185511661
    0x804060606180b07060e100902030d0c021c05010b03070b040806060306040b011a190302030f060108010b0403031b02100503040302011103040209010e04150f0c020601080a030f27090b01080f 83
    0x600c0e082c24940500c1c0110310b008140c420401c42c494200390300100145003501c000c000751105e1000600206a0100e101e4041c09003081e00360342c4200d440400300c2d90001c28910030400d050644940c4a510110155450b54890b6018000340d2800c0106030010640074034290341c1d0302e180c07040c0981080d0000e04054425000b100a10001c00c041482031815541801a8044541c0002d0905280d80c0b0544040b9942041c070101c4801178a50154095846207003010030340e0703100b0380c4c683c0011520510240200440204140002e1010034451548006100501401103a94008a400080c00c03540d41e481880001100007081004140d4280200240c08000042450075414540c0c006042100b0501500203248400c9000400f4020140080c1d200c02c1100f0408010095841c01c25401410802c00100052b1080000003c0d001c4e41c001241c040302c80d0181e540d95100040030b14100d407018110748038140303403194440c5040c204260501c0920020036400c000014400348010000d442e6820080c68002180c4206040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 185514154 1250 185512904 185512937
    0x8071701020426010b09010e04021c170a090b0313050f010e0d0c020319050609011a03070905040c0801020c0106090c0e0306070f05040f030c06032f0f12070804060606 73
    0x5424800d000318800d055460f9503001c481c01010100507096100382c0b54800018800c0c2e4040c0313200e02032402929904010050322118009112060100400d000074140c4940c000440c042c3c0a0800484d0340d00e42502250340d1810280050f400c26036404044245c4842c0e20707020000c040000d004810906c030700070301c40440d20700e0139a92200100c10f0401c051100140e0b54500715503040c01121600450b42010f000d070b4138181e05044e41d0f00c81013100d15084541c0313086030b003540c10030441c0510007a94a00400403c103190400c0c004801030040039104882c5111000d0011680040a0020700800201c0304000541c180c903210404095170040329024003403080b268042d54094802081043c1d00007481d04005044a90b048012620b41c8220381c42041d010a50700c001000b00452a40940111034140d50148013801c1003c0e18000810201003080c24900628624565101003181c06800602c4802d0012030410f10200754000c0300d944100c51070000a417010003040704210036441140050502880c1c0b246440b89910039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 185515404 1250 185514154 185514179
    0x1080a080a0305180d0306060f0207030c09020c15040506040c0f0302060315060d0c022104050d0b1b1206030d050c070b03040204020f161505041a07020a0c080717010204 74
    0x10004040e140e800041c2482001c842d1103c4001801c0c04440200c1101a0300400814090041000141c0701040d24407202b0303c001514020749030807000d45000c0d90710f0501c1c148001d511000340c0803803a004101c100742003400c4a03040148268000d0010704451314151030b02c0f96980c10309800c14158901c406009102684076542903903405980c400d02c010184214000140042c0501c0200c4600c103401c0c02030064001d940030899101000c1680030104040e0f4440300c102c0140e0150340a0660009224045800403507541a202d9803c0304150203c140c0c0d541c10140074020661001314100c02040821050004030b04041001483c9185540b07032190038034400d4211181c5070002881007102d254808070204065640307aa044401c0d0b502083c2e1207960f00c074040158001d050228200036107a0015001d0320414121281c0211482070f40c5c410580460842c003424040702601c4080c00c1e10b800c41c8250b0891400007800c042c2114003400400004124940c50140c04481ca20400d0001440301d034014082000090300b081c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 185516654 1250 185515404 185515417
    0x30e040b04060305101d0c060a0f05090d0606030201110a021c030509060c150c041401050d0e070e090c0a0812070201120c0e10020a0c030209100b03090f010501080a08 73
    0x44000c80c8229105001034054529900040c10074040c43c080ca0010440652002a0b00725100304400501c40314009034644604d0700a03201070b00710000f040030714061881140601c004145500300f00341403110300c0011488050700e00d1400c41c1c81581d510414015582c10001c8005900091070052608010a03804103040b2912141d20358614180c07020720324100741c09103055032000800900260b4540d1100c04c4601c1da54907100d940c08144240b0100403c12a4610000312416103141036040f5030955802401183c083c2e02c041508504196aa030a030107184005104010041c680c0402920081c14030600c01c03800d101c10603000c1446501e10420401c5945004554240e000c0108010140c845202c0d00060787d10181800e20740b003005141210306140680c001c40c00040203807041ea104840c403000e00c6000c1ea5541c5041c4806011142801d001308018a00517014a522120300240205102e9032007461004a410581d03d010b240d801c0034002c902002e10900c25035004060120092081c00b0080d04c0b0402144a000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 185517904 1250 185516654 185516659
    0x1202040b030d2c0301140105011403011212090816050906190b0906070c0602010603050d1706090601090513093309031b03110615100c020d0c03030c0b010501020604030e 74
    0x72800001c00c50f40541403246100001340c02482028107103400c46c030340080c090090782d011a5251026441d400302041c190b905907001d2802e806500c9515807508000c01a600d03640c0750400680c807170003082c645000e015280e0f0800907014009401c508140c204a0f0905000300313040e0186007020a007000c000e01592030101114244407500355268491004035649202e440000b404c0d0480342e01000514550551119007140e0080c1e003914003a1182c0f8100719000001d9840a8a0481012020030254030305004030303c2d04002c0506266500c03a58500100d02080703040582c07d82155951240b0806000144030b4041071031200381c0c2400d0b814980710b40305038049074012034a00f450959030f0703605404040c01100c1d18000c4002280080340d17020311500e0002c14500d129140011140109400719942c0d2080304440c400d424801032200001690315003084a40703020505040c0da06c20503106032640400d0303100150f400070314065901e408a080407800c14200b0240182d005504642c003880811011942c00741c400fa040c80b108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 185519154 1250 185517904 185517947
    0x4030206090f150a06090204030f03030b03031305010f09080706030623030d0c1509060614010804030219020a031b06170606030103020904061e05070f0201330806011202040b030d 78
    0xe50355404000d05c1c82d60803202c01c50388001004000c0c84108072410101030b12a80e01404000070010605440c3d00401e6000caa6142903a0428403440d1700038030706010002520324020703045a81d100e88281c94203440d0b03070003480403a03503c1c2800e01c40f81e030411550640080c02100e0080c0108917060219a440070346828010800c1a07502040c0c04002c08400d0035103d11003121000d1142d1170a500303040005000500c40c1642001904482c22055405203040b5803042e501034014219503101d01d090500d8090405030226803103141d80101000040c80809142c80c44940d00030011440b600349903002e4030448403032641b0b210911010003005910f03924042180e040d07030360580700042c0544540c50b02d4800f8110a14140c0f06941032131864100c1c4002da6400702d842040181da90511881c540802a401ca07040c004000340300c0b1072541440840c845000440f2800c241445100300c28141d6214412400d01f03000303800085411002511038000d516060181080350700b03045000c1c064071304807040080c110503009043d80c5d520421 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 185520404 1250 185519154 185519161
    0x50f09041403070f0c0509070c02090106050d0207290601020303010807090228020105101403060606160b0405030309011b0507120e030d050c01050106053103120804030206090f15 78
    0x7018815109420750104421181c801c0d00d18120b040f0030380354050140a200100005810a440f9540c029413403500030f4154400c2d41d081c40380460355680422440c0200503000c000c1200055a141d0aa1175450801c01d6400040f200c0c100b01c9041100b00604964110350090005001c07520010030100304039140e03813900507031b504917040c00c0304800020004011059510041c18501d0907406401291144e20190000280c03161903110401c95500c189400b40d0701907021000149460070150020907a80120b0300381700c40c0024040d80c2c1c2d4400303154210b5040310f06400100c00d0045c001c10900070b0070320740c1001d1110788021900c0345000410900071154003130a110007000d41c02c214507001c3c60110340f9254028041d14034a240946001d0000ea0040b151aa920b42c681000000e415101d2400c0e243c86c9000307501900645880640c0b07290311541c0320b103a101ca200340c00c02800000582c140c80101040300b880d4984030151b00e41800e0117414007000a082e145590007500d00c42040450200c1c0580080c40407500a1582d80c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 185521654 1250 185520404 185520443
    0xc04090c120204060806031e0c060318030403210201051509060111010e01020421020105161406130b0604050105130e010e060a0213060e0904020402030414061609050f0904 75
    0x1c407490070700101c1440040d0204116a000004074840c11040e01200e030b4000f02c0500d484002c8a07405d9440d0410740140c000c1c0d4280e443c2060085800428420f590000b0000c0e07400c034a410360780581e008031404c0032003000d52000310001c00c2c514076145545000801451600f19800d40745a002c096409204600e00d00025469a0042c50403040c00d0305a074000f00080c501d1119407a000b58440d0084402440c0440840c17020500c85500200700154113940300740c1010840c0510071510380d8607810403251008000a0141c45840401c18a4850160744683c440705288908015002000c0035040a00541c10040144100c2d00d52845030140310703040c4c400000d03000341080e8a030b80c010000c2002d5140213014078810701c10240c85503005000c03401c0914180e210a1a0389500aa43c1002801a41904510084d0001e0003501d09a03000c0c561003409000340d080d0790303203101032510300701b0400700c0b2040d0144461202c00c8408a600500306806003900f960707042c1080c0740d000c00055200300014001400360000c00d00e90328914 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 185522904 1250 185521654 185521667
    0x90607140d0c0e010215150409021305130213020c070302151201030803040b01060807020613061e1a0f0d02120c030304060504060f05210403200c0f04050c04090c 71
    0x901c24503040041005601c0014084981c21041d103006118507841172410300d062032040e40c042c01c020882d28000380050380c140b002038800102c040c1d034003500041401180074424065207100c0c44140e80d00c40b1101c0c003540304000c09041c18440c11281e00e481444056001c1c0d80000f010301c140c903012960140e800802a00d00503484c451408014404400d40f0000410003169101031030203103101700f0318008181c0c5c94100484000030203e0305040142d224001241e000795044082c0b008d0180104000302d820203582a00c0e511821146a4002c0280d5603a002d00340e6006160b02c507412000821036820b03207400320300ea00050002c4a81c00c400303403207110076080d90b03980306008000d0405495001340a0302c0e1565581c81014040d40c000d03102d40000300d66210f8200710143c0c0b145046400180748510300c00c50381a58114845e07002d00009104400b401501c600c000f003170300d0100c1b9503071400050850081201d0003050040c085d00d99a2240c80c40c0c0954204002d00549141080075901030f52500000040d0500e413601084852 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 185524154 1250 185522904 185522917
    0x306050f2b0302070509060102151b0403330c020a0213020403060501030305070302210403081305060d1508030301060c080a050d0504140c03070b0307050c0705030102041706070809060714 82
    0x81180301c100c901c100740d00030491034122001100c044c0074564908006980310034803404c005c0f1607804803500203404450010944040040c540c5c1d185818640c4956400038840202d80c44400034003585690300045280c54507028007210441c50081c003415128207006980e8403c4004001d11031020103030f014007040304aa0546004680000c428481541c2d02d0902038204c1d0b21001069005000342c121840000d580190784076182c50b0701003413003403609285460301315458000c0250039071400c411030400940d03542d5000c00741500341424903000510301c980804028914903d44c3c007030f40c082d4109100401c2456002a00c0881c8250001e40859440c4d55445003151648107501c058002c161501007440148106c2d02134030310450341244101d4000b40c8485041565441442c070540ea0030440c00c00c00102c1c0584100c0280c031500d0941411504066103078800282a03030030603005032104208101108480040811180341c0009032030400d221a0b003428032003075449a100410400912041403103803074a03103d4003005c9441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 185525404 1250 185524154 185524219
    0x105031009030206161b0b310602030c131401090609050319150606050d0b01050304121101090807050610050a0305030a141b10050c09130b06070f0507060305070306050f 74
    0x403440701600d0300d006007030f0041e100090500008c40d441c40903104600040300d40c110b40301b400c85003200601e554003000f030742c0001c0071040b001c101405243c24207000743d10624054001010a40200d46010b40010070b541080e40c810001c1007a072030b60802071a140842c00c40030000492208803002a942c4c202a41341d401d09040302d0320b9891401c40009032455100001e0203002a032020103000a0002a00454140c013041c2d40180810013440c514030883c1d400740c103400f000e04050000209030780b00701da01c80c94680e800007101515142c00020410030280e650080ca1805400201da0940300107045885455580c050310054805020178110b1883c41d100040042e40c01c02141030f42c00a813480110150180c4400208601c440200c2c20a0301040d40580a50240d604407240944001c482c2d181c1251180c014060800c1c0712504140100b05107400f041603912000c030000d015030002c1c02100c1c50001c0080c22600010500c0e0209444d01d10188550342c1c0b04a185046658100e40202c800102c3c0248007280d0a010340c803141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 185526654 1250 185525404 185525447
    0x7020d080c030304050c0406140103051f140301271716060209010e010e0d02092d040b160c080a09210b100803030106110c030105040308010503100903020616 69
    0x105411000004500c2544600309071007810b6401c506000a550440c000c951080442d012750003100d501c41c6d8481540400314407050340100708480021a64058141c1040900f1850b540c0b504240382002d00a6070a05111110a01c158003111240d403181a508600000e10052140c140d050b40b410440003070b03503030340107010702002420200f92424100950003580d40a01260b0344000b00c0302d85600481081c0c0c084400a04090030006c4280d00b003110615000f090010005449a00324090b44045c610307040300400034210062590906c1c2c244030404175402000d18003461f5400000d18450380d84644030150142d4001c0905440c0e040410095a1491483d041011049001e40d14030710340d0010181c00c074501e64040d00b4175260944402280d02194815405281116482000104071039032080c07540c0c99194243c0c5041d0b6a13202c20100c0000c0c00d581e001d582c25000035400d1030040c440c92600340304004402449020030413101d41c10340d07400f0b0340b2110014068103980030700d50300007141540201500e904520001101e04e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 185527904 1250 185526654 185526667
    0xc0606050919050a1a131b030207020306010b0c030a05030601030b03160f06030b06070809031f09030f0f020a060c0e0d050601090501080708061909020301090b07030f02041a07020d08 80
    0x244040100030518100c103040c10040350160805104e144a902d20280c00440c142c1d09500a10503004060829081010358800d80f880d445031f085845c0f00068002a5405655488980105403034071406810240740c4100400400c510311301c0000844840305403174200b0548030b80d04d000060b0f00400240c5a00740c0c050043c1200080291008840003081d100651511300d03400d45c460404404546806200640107501040184081540e54002c2c104800c0010121800542a400314800f80081104000b030795a4566945204140e0000c9542c20202030794502300300c4d0003440d100000d40d5075a0600014050607960703120010014850943c07000c16110140a01c460840760340b424581c1c2c1c0109100305180302d45014004181480003003003400454140070014480c03510713100300782c40360849135064804000e0303078034540980142c070b0a0160101c01802070100703241910f0141c00140130781e5594401c1000c5a8030400042c060012500d000f22444801c0183c40e603280c2c0814400302e080030840f00b80c0500a2035020410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 185529154 1250 185527904 185527921
    0x4110904060f0c020703050613060e0d03090b06041416050c01090503071703060123090d080a1d10110115120c05060307050307050c0a1e06060503030f04060c06060509 73
    0x184001c0c0b141003008110400d141d803412030300d9003100e001c014902e0b04a180800d003c44001400c60003410b000c1d040c00601110140841c074a06001ca84031440070075101c0181e141841403007205140d20503001c0d1014000daa080c090552442c607002000d9800c1040721040a900780c510810954810303c0c4014000c0105250134100203540e5041b158041741c01020704284100301050304002e49005d02e5042c0c4078042030882903c031081043c140c1203040782d2f16050900154100365500404a20740500440e0440d83da2180300100030200d1445600d5060818500b180c5100070f601e03001c101c4010b00b40c1a207072401342a40240034107400b412549400c031034500c0c11940702003091180e8a8080c0ca000d882045116600f9644e1018005180021214100880c0013031000584881c06000180007515104d0180c800204080d65004825104d004801280d03420441c01601004858401c0d40081d04003100114148080e403c542202886540684010060484185010440d8580101c0054607005048010300d180c4070704c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 185530404 1250 185529154 185529161
    0x100507090819081603270602100c1202070515010306020c1b011d210f0717060628030503120601080702070311120114060301111602090411090406 64
    0x5040650203107082c1e000407a0103225691039499445820b00d400c1070703a00c3e504d03600c000300742d100c0941c14002c910401c40031100e04411003540300400d512126941d60b040c600001d01d01001d00c0203400400d468030400c80c0c991703900141510785103100e191004d6514100b80c03800904006030007840301040d820352000401048510b07006046807800741c4080710b12189c0c40344100e15801c0580e10010740894200d180112007100038401802d00384c1c2c030150100580c1c04030603140041e4600384405c410019040380310116141d07481440440c0040c800d40024403003402000e1541901c404c406400c03141b2035a44402c102080b84001c0e40d280800b10511080c8005182da20b0510946941c41080c1d002410b5406000051540d8010200c0900420741a8010700e4031314195520203400340c00641c901a4017a95130b04110b4841ea00034000e511030b00544003e12850b0f414038200349400c0d10f180301407080d80b00009004070444041c801c2180d0313041640440d240d43c103070744031400c081102d01c0ca4407902d960054482c10400c4140300c40c030382 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 185531654 1250 185530404 185530409
    0x140a15050a0f090b030a0f0b072609010c09030203030f0d0e0706030c2a03030c0e10021507080702030a031107020603070e1206010605090409050705030604151505010c08070510050709 80
    0x1c04c2c44905008020561980543ca03401414800c07604040404a40203041c01c6a0060443c1055090340300c0d9000207002d0800300140c1009113601000402108070420b01807019032038168213081700b015041da400241c8a00a0707041c000e0003041c011403820f0044801d6080f9030075915420f07095692041d05d801c030040c068112882c0c128085200245141c07981c03221500030f2400864000802c003c1c512541e43d08401410341885c0c40d000f045554200104d40d40d442800034034042103c0d40040100030078806e010084042c000340041c0501c00030404000301d403078002c8115030016443e480c001450b0403407000d070740d10507000b4410040d4100ea408410021141d410400c01111640102c403c0380404540d610f84d03c2c5c2d100300c00d01a00303001074414003407210030f41000e4009036070041c4540191991151030b000420710340f90048809440702800c600c804442010a40f1545401c04006a4049038150411001a1140700c80700401822244001400e00600109014212040d156100144158103014200416000e500d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 185532904 1250 185531654 185531669
    0x20f0d03021c140412060f050a06080f01092a030c031a060f010e100302070b04060b2d010c061409100f060503060705130305030d1b0201140a15050a0f 66
    0x1080e030701260f8026001c095005081c001c08914040c1449095500e60116001c219400d035141c0ca980903010b1114000c80344560140351002908518205046140961400c00b00465903d0981c080c004110030840c00992508240066011101092030481c66010141d0018141e490410b0001c41040840d58128150110040707996186843e031170200001178070610200ba011840e200f05103030081c03d00f0070790744144040900780182400c0716a21044180f1000300d40c2154402d030346807840c85481c54580b62803102e06d2454201ca40313a01841c4041080004050460b140c148540d0003032070020400c2c190003c4d10180c1c4640010100c13410300c0d281160355580d07052110f020380c50030004680d840c440079115482c1100d01c000c0050507141c80e142c00c00e407516801502c003070840040e07008021020400410042c151040234240004280d038145080d5000444640c1090f811039040c618a4045c41c6207032103816802811400b000940d00001d130f0b04004101c1c0e89075101503000350387c640c4006070300c0007103220a0301120400e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 185534154 1250 185532904 185532943
    0x29030f03072f031b010507080d0b0411070c0303030b060c010e0a02150705030906070201051b0a0b2206050c130e0402030706050405060f0a0309060207140c030106050310020304020f0d0302 82
    0x1800007070440ba1082000c4590560f1003a5412407229000021440211006052007840d121881d100e0541d190300c0640d00742001615600c1000803400c0c14131810090001c141a00c904040c0f050351200018411448080c040540754070f400c544564814045a8501900c03030020004031019207141c6454140502c0264450f0b04803040d0303080b400c03803110200c4001030b03404005540303081c07144020089582c0092078203a04012007400400f03078120000d000e100c1e160700c409005140c0d410580c54030131300c1440300904031001d04202034403500902c0400c1141c040d8203580705201144c10b9403545840c000d18005c010b0f070b94a04c0000c107013002411500149015000314001d8003521121900c2d00b80564580c031903480380540100c030810489034144502005020305400d0b501c0c000c281e01e100c40d00d0b20b0040c1d0b0021541078a1810380e05603002c900c03103003c1001c1c0741c0303682c0207170001c1c00b10074034140c002600ca44121046943c040c1d0000000390855440c41103808403a40d00030121003107a00a41002940da03000c600c080c22240c4c12 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 185535404 1250 185534154 185534213
    0x108060f0c033c0702060f060105070308070e2202180f0a05090a0f06180c030606020712021203030403020a02130e0c010c080c0d050a030b010329030f0307 68
    0x3501048902c100c203002d880e070a44070301004016030720795420076901100c0c032190090f104100b190302c0c41e07503805003400f5402840c5505040000e00340b256406001903051020401c603d0002030381100e10242c0c4192941000e058140a52000c500c14501c120a80b0744201034001c108100903c141e409403074800d6404149440d19030340c900501c0300c098502d085250f40401444002c2005d40b8101d174140c5d80c844003884000c40c1e48590418002c0035584917400403030034807600000980002d22180b0800107a801a85002e002051920390043c0d12540715000c1c3d94010070800003004295250a45d06100314071102003125501d1400381070007501c8011184080b80b081280071091202e066a0340900400d00752900c0c0503001c240c2c8a040151446130750402c0031a1000030601c00000140010b00801d078407403286840f901d03541e403801c95000307049805501d05103050500d40b09460400d00541d98903408402c0f4203199030701d0f03a001100006031610000d01085106d034840000e6160070020001c040000c0000c0b46202c0220078803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 185536654 1250 185535404 185535421
    0x130c09021306030608070e0603031213021c110103050601020a08030405010b0a0e0c0306010f09081903090801360206032409011d1f0f0e010602010207170c0102040e0108060f 76
    0x8013903101d040ca203030b4050401801000e80304008290400b000a0449181111248442c1c9064600701e07451000c0d03442c0303600b1003000d5003841443c06c5038040c9980c1100d00110341642d1452103104010100d00d040540c2d403000940325034002c0040120355034000c20819102c0c502403411a010300a0108264006c0c0494800040c01100e1400d41030302945064040e2401c41e81c0707240044030480710310b00c044401c0054265001602c0b010900001c501d50007102c000c103404003014200a4207042c52079100c3c00e90360713141c020300d0200c00030f00d40007044218403030280d500000d1a80031549052034007240c0c00a980400000103115020303110240201c19511007405103c2d4000000301040540310091240e15010000034141040000f0101c018a40c4414402c20034031181c816140881d02c100c0594003e9603002103074074402d00401c00081280d0340103107041d1000707600d014140d5a0701c81c00b0b48058170211080b104c01246e600440c0b8400e40507200507000c60f014603100c9603504d16a49070b5850342178034662241d0303941c03502007070286 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 185537904 1250 185536654 185536661
    0x1506030d020a030903080f0d020c0303040b160c11180705040603060503030906040b0d0e0102220905010f05100e041a10030903090b090406150203090307060c0b0a05130c0902130603 79
    0x31034250b1104c0c1c50082c41c5444550081d80304c441c1c15041807408201d401d2501800b407002d0040c0c112582c0040d600c0b45042c1c80c02005580000d0507452050180b007048142c03242e07020303c224200c5a84901e240b8920301c20f0303c0c04195600781d0341c90f54a4000a060b8200300c90107510102401c11290340359414020550345205054481c4600c000d11500007004200501c01c50f92032400410380041c18800004600044045550032a0420141000e0701e5140c006007500119001ca4500301500c60700200700101c1d4900b020078810503040d84562070040807600000c40070030740145442034203000050f0084c0700c140c00b05040513081092030400316205d0044401a0250184240b0031125481d07415168600c0c02420b2a072000300d03036080780c081c7c0340e4030a442d14000300e0b981c051100b0b110f400758490b400942d00e4145030030400d414000203403c00420800781148610120791794003141a0803001211002030140c5841362003215003d00e690b805010104010000200d030205c40d07009119035070344405102c400342d07202c68049003903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 185539154 1250 185537904 185537923
    0xd1d0604150c170403050702090a050a0e151807081504060e1606120612140111030405030307080403200d090504110418091506060e0105030402030a0605060307081506030d02 76
    0x25980040c83c043e00c400c0b1202290400c1c041c4c1011414403100d903001444119044400703030320310340d211400d010300c80300c80f4059200c541b0208805820740f0724046a128000d100014290b468540d56904605c0c1907007000d00c40300000d1301c4001e0583e901c040b2612070000804209641c03c844e082c0c504851030560801c041620f404032010048501c2c2090301d000403c460515400441307034441941c9003800a56200076084104a1512800304c0d009120b2099500d81d00315501d40504401111040040100040c0044100c0380d0000807400c1110703550320345081c00c40d00b41c140100303034401030540b2150041003243d0010300380c252000d0070740c3ca01d20308540b901d090109991400d00b00e0b5a401400340804e20044c0c1c507052580765404800b060010340b000050721070710b160021084882a05541d164000e00c0380951090910000d03007020308080349981041e502007540c03201c42e018040c084550300d45c00f141c85590244004001003110108440001c500301406101045c001d0f20254402d1041008200c807035400030030110078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 185540404 1250 185539154 185539157
    0xe0105040509040b0a0f180c080a0305040b0c190303050a0c0908100e030c0106151206050f060903010902120309030123041b03020d0809040c110c060d1d0604150c 71
    0x2601c1d15039402131400381c06071142010039100c8200030a407603101e200d680b4203411031004224158411f420907651070f004940050b40d05070000404071021a403c6401c441c211203d403509a50360f00100341900d4188052140b042d51500c032405080c00515034180c00180c0906030000c000c00c0041802c0105485001543c4180035450b001040285044a02a40b000902c2c446100a50b450400c103010b0542c2120000d401c400d8001d0181c105410070280d018808011102101d10200300035400c0a00240c1f40035030b15448144604400104e21031070382c03020342101030102e42c05084905c1c8948222141500ca804c440c88041c040c0d840c084000c0f0003910f0b00411070001d003860194500700b90311141c969010f8100c0c030360000d41e0306030383d0780c03800000584882400d1004180598081030702d47d0341e8070040005462070f08856404000e0151141103520b8030200b130b8074030202030441c0ea40b9034400340e5500f040c0240402d03048618914001903403006a80d46c0c00b05000d403059125002e28070520500c207462408685141c03100e80c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 185541654 1250 185540404 185540419
    0x30806040b090703020c07090903050a1403070e060f090d080301051c0f0b090f060103060213080109150c030b1206071704080a0c080d050907061803031704020d08040b0403030e01050405 81
    0x743c07418001c3d8002e010510388071b0141da4440d91110301c0300d020343c0c2240318224001000082c042807240e5000e001c001090b402e000040346103003000c0100410451f001842284111400141d100a40001d2801ca51140c00090b01288503140e580c1800c0d10380d40c05c248100740c060040b42d546c40c032070f00840300b4000449036031244030b01e403144031513450301e00070441c005041e038110748100d000503c2000005c0008078003e5214100c0035a413080314000c2c2c0c0005014540c41940f0684c1003d002c0b0300000d0f482c3c0200381140c50042c60009084a5450b0308030040e00752504076581110110580011a540108100344606034540340c0b400c48015071540c2000d002c008480140407550b051142c044180c1c860380b0340e0750b4954060504141000321402580c011034105440413505a880b00d80100a0399805c0031075200000b141000f42880c0f54a5910041e145108000e4112074010500c1d000800310360307d0302c203001503844d000b0348099140c1c1d444150141c1240c5c0140825004101d40c101403600c258400c4d01180d00b030310005003010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 185542904 1250 185541654 185541661
    0x2190503030c0f07020a03051f0b01080a150b0f071205040509010b0f1b0d09171b060c01090302160b160201030f0e0316110402040605042d06030603030806040b09 71
    0x1002c990021056449010020000e860160703941c185c00c0d001540c0110060055226070074071000d41c7d10040015005064140600302e50702c2c0c2e0f00111484d5004c480124081800e6140c0700c100b481e485580d030001a0010b4001c41c46c0300171484040044c004040c401c1e12030403843c0d64900015582d40c002c51080c03039440b04400d401482688040d03c00707858040207105020381070421880f0040d02555010f600c030142984013095420b890340c0c7c42415800202415026280c240140b0340003e43c44d102100807003111200c144848580c1c688601c81240e40447e4003a000b000795242d00d05e0001c1d11910350000703444240e40045404a1400146000c45e5211031400d40b0800c50951150b00560141460700551269a6901d1400c80c3c5a42e009000130160b070f0417414852541c542043ca8034207210b01804000d50b000364030500c81805002d400008440556105035003a41011404004548038001c007401312103a840700da0400010b20f10303095041b540c1901c0c400c0c2c842035a2982c1345000d020440d07030b582108691107802800071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 185544154 1250 185542904 185542921
    0x1c020d1106090d0c06090b010b09100c12030b030708030409050f07030c0e0f130906021306180302090c040801060603050a0f180b060a170d081602120a12050a050103030219050303 78
    0x18044250305c52180491b600d2980c0d120451410007d9000c9642001c00043c40c0b8000e14001d04001212a11800c02c4000710f4000c1d2541030b10030a840304031600b403540e1002d4481140d5030802141008051030001c0303d59890300c031403502c00508000c0d2443c2025048520200b09203d0103401001e00c1c11410340e80b0007400041120401451448404e9030759007180b41191440f0b0003d106009101d2a54002ea0300540c2d40c813000841e580c0c0d004001c3e030050081260902c440407001f007006e00c2c0311003180e404903095003013a210b44040717001c58410350b44100700b03561801078000782c000c5c0c254001ea4410711b00100100000c001d00001d540a40310545c0600c4010b96200b0b104000007410402c10b1504540090b101c0c42103140c803070322401a00c44100084044d294040d00110009942c410030b51540520983c02144e07411601c0030019681d010400c0000c0c5031085c012440c0d2540d00c0c4070300b445800c4920703002014422818114410b0300100000c0c04280d005004051030f0040141518502c4080c03198000010f51850b070300c2c2d026 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 185545404 1250 185544154 185544167
    0x50a050114331f090803070c090911180105030d05090619030e0d02030309070b040302090c0304060b2706060a090b03040501020403061e050a150510021c020d1106090d 73
    0x3018540d50200202c0140310b03449a042040d040007100c5812145814585005440301949501c403c005038410044940020001442e4104071424420049a02c03c2c9900e840407481c030210350225041080240c00c4540e0110102d1224100ca400390191814820213400450b5941324032000320303400590070040c410604000d40710340c8d01c0a401b18a400908035003800106030034051040c0d02880140c0c4040305108104909000300001480d0b04452240b800d0b00d10340c041030643c40002c190102c59840407001400344241074015612245006145070b04201c0014a0f9040c8074545600c060402d041080003ea16420184100c841052032034880742456032074411820040d83c00100308480c19502440000001580c0c0d001d603500a07000025811180c50003d1009422950002c00002c0118100719007050041c0340051001300717071502a0b401044010b1002400d03481c00b48120071412a5a8100c0c0c3c09100304c0342c0c013207000f450b280940d175100ca00d14058005840c1e035401040d03803500d003a50002498a10094040d28 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 185546654 1250 185545404 185545471
    0x30f060a031407030606240807030f02030f15090402010221040305120910180902090105070507060306060f0c1a19020f0703030b030f06070525050a050114 68
    0x2004051030315100e82d03401d40801042c09070422580e010b01c4080c0108001e45c05208003800c44d50821811003403030b100b00d80081c1d841f41d000c81401e014010020540c10380c443e070058a070074511848190340d80d041580b000c1d9481c880032100c02000078600d201c0d5640624002c0203040c001c5405a00422081d804d21f11940001040c1c20038070004a1400c00000000901c00d001c0081456144800c4070744071121780091040100c503c2e691601048208015030140c03d2003210f40000b9906035003001611100c007000142e44600c51900054103502c07038082c000840395032580011065907582d540f000e07403a035007451040d500d50000f590002d0002c400a03e41c80000c03030f0001ca00c0c6070700c111100362403030f9800b00d90407544040b640a42c000100c000c0000840e0000e15402d4003a009040e0b20030741c024181d600c00c0d51041511140c0203482c480400c240001c07101d092a06443d5a602d1890609007070302407110280c07400c0c9030750b50f41c7d4401c102c956500b4201380701091181542034500c00c1c03c0105c1c0350300300c400e1949400009030700317100e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 185547904 1250 185546654 185546659
    0x5090c070b0a0207060509210d020f070b0108011508030711040912260124090503010c0903020f0603070c0602030405030d1103180601081f0e01020a0c1a0c030f06 71
    0x144001408181c8515403180034000c0a03500590300c50390740c1440030540f14010031010701940030182070310700c8416949000300081e41851509444100c1d40d11080082d104945085425030030102e450400d100c1030002045c125080704008104882c001100b8400c000d003144208003254006202c8100400e201c90703440641754070014000903070025030780e940f4500050751100320400284451040d40000d81c541d81c02203103102000c0005240ba624010304080c171021401e14440841407580422000c0714028605080900f000800900a0400f80706004000c204188030a078072860071343c3c02f103186a08001c021640110038544d0307006802040fa4840402941c8003600c100c99900c402c00c64820f1a00c040e1003172075201511314003c159241007490110310844113030790075820281c004030300402507d45e00084c01000c0c1448031440c3c803c1200c95007904d1009000d40c882d031260079400050000c0f00703140d0080112614070320912201c0b2001d0b1200d081d002e1070700070840d0140440041000400c2104040309030a03540407200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 185549154 1250 185547904 185547907
    0x1003241404180609050d0e030c060316020f1b0103050a090c05010503150a06110f07060905010e03030c03130f1d130609020a060203090f1f0c03020304080d09030b010b070c05090c 78
    0xb143d44810803524108010348150300040328010030554001e10b541000001200188840000d25002500c18072002d40355212080c01d511401104c2d40c001d002001c2802508025a00303070f03924900d100180241d4500039503001a2038000052440251803003007520050300490b6640d100b5080074010740d00b40e40090103a282e1802c140d0100700702c6d5a111007541024207510758698050b039640c0d420140ca0a041c0004911940e00828030a100d07030740d804001c000c203d90092820030030844450010034110b1050b100115500e010000e54184011080c001003011698905040c900c915031f55403a50341100801d01030b88500810307840c0401c0416200111a030302560061100040d00b2003141d0010707100341c905901c29400350700041840b1281d45000c0c02010203441050318403401804410100d013144070018240a8207106420400209051081003a50050300e030900442c0c4c0d06100259020b000c0c1101480100da400200b1070000c01d8403180b14080e141081d51204c0c401140b00e013010204094100010100740c3e50420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 185550404 1250 185549154 185549201
    0xf090b070f030306060302120606090f0a0e060f1002060109090c0902070b041112100c17010e1b04080a12050c030409061403120d05060a051003241404 66
    0x914000410000e0300c41c40c1911036541a030718019040d50415031000342414814005814080700000f01107600040843c0c040e940d8210b200005102504400701071a0000f8a9072000f0400300220040e1074000c00e01118030210b520f0342c01040141074000303491100700603084140100013140d056040b440b2140d200f40c842842d0b0329294038034070080740c1040005803040f207189004e00080c4807040007010a491010707515181040340400400d6900c031903510101e400c0e180d803144071103122481072002e0101010385504012255075149200641c410080d00c3c0e0b420151185010442607852000807601118250000782c642a00709171501d580c0381013100c68a030180b0100f00003a0384070210500003000900701103c0e00148090800d0b0011840d4001e031080e2074001d42c414960010b880c0c5100054400346000b64ec0082102d980ea1800700b00d8088269111680001c07203d900c00041c642c00d03421003004c154403404c80703030345c24440c020542e50007048034403600d40c010181c0080902141000e800a400709400c0c01d900124200c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 185551654 1250 185550404 185550419
    0x10f08040c09090b16020d022a040c020a05010f05010f0b090406180e1207030e060d02040306050a05090c0d02130c0201060b0a020115060314060603060d06050901050108120313030f09 80
    0x1441800c0c11134079141d00c0410401545040b0350666007001003840108a080d081440195a40402c0b001100350b0420310310040b03030318203141c160b5003840940c086c0040c071140054450181d03503001d854904031060f500305884c80200c40c080b803080328100d1f844c4400901d44145000503017a00703039001c22480d0350403580300c1001086a44040e203000982801004002907000d00317015940c1d04007110383d440050750075020040f01d004254081100070091000700c1d54290360b0501110004002e110303940c00182924113107000c00940402c6940014441c022403400c0d21070180220b01004004410000c0082d4088110b103843d000102880d440954100e21070300000592681f2030994045941100b0103650050b0344a43c0b070000c46500306075001c4010310350307800e05001c2d00001c1c0042d0340301c07080c0c000c01403030007024040000b5009907103e220400d071154108604101a043c04d50ba558040c01c024010041148501910307810480c0b0000d040b80d10541240a2503945c640d080e940468584d100d02c5603600801c19510000724806 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 185552904 1250 185551654 185551661
    0x30c0e030a0b070908011407080709080d050a1101020915090a0302120f1e03030103021005070b10030209060a120f14070b0304030f0804050c1002010f06140901050f010f08040c09 78
    0x81e4040e00050405107041d0708000c105061503004140c041e410061f0410840c850000318a8000c4910304082c0007070391700c0070303000c4407a6189070380540c600e41700d074220522225400000038642e001003a81e41c0300c0c5004400000d1401e034440c1071516604841455850f90214014101400b5810f0004100c51001641c07500015564800310840b44502d41100494032040710003046140341c2483c00d144400744550b41c1c069120303100c0c0814840030b40282d0314050482100b5100382c04980c652680031170b50b040c031401c0000c0145030071502c9000413405803d000000c908070740340241804046960182e10740d4490802595905000c040c0c60604540140401c50000e0740e0250a12240d0702404000900644a1400c1d04005140d2840c15000e070061020303c1051201064020500d800c1e4094295020314240e5a140130072801132005d2030f030b224078107803400703001040c0e1000564400c410040c00b100d8a4800781d0f01d950400211065007402d4901203006c01740a012528083c44000768003d00840890b840581c0d6001000280e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 185554154 1250 185552904 185552923
    0x1206122512052b0801060c0c030b010608090106050405061e0d050601080d020c0409031e1103190201060504020a05031f03020d0614070c0c1a0405120106060807050c0d030c0e03 77
    0xb9504600c8041000440e000250000308800034a41c40401c0c996001c003030142641806400c08101100303003080305020321009100300856020751030603169039403284020103d100c01d44070b0100550038010005000d02c2d15026040c0210001094a01d51000c032101405030000c03440e207138a402225030f4900348081803003400400e0083c440b102c040e00015008000003400c05c003189580d41c0c4203e1404000388082940a0303070303182c0790140994900408c0300114a0070748920211442c5000300c0d2000280071150b509500d0000038410015800912140d61a0410402a8081d4140703150000e0320501c006480b00c642031180341d024410000722503108944a40118001541d407000998500e40c55840d92003024200c1c4140c01d600074602d14060421307120032795032284c640c0658491403035100d01c42007034040c02c0b0201c0c0c0c0c1110011f1400800c9100312038440500103002c1d128600c98240420310321800030381c059005608035000d07035655a01600554080100c160010721b000052072040111416802056803010000c5205 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 185555404 1250 185554154 185554163
    0x603060108062d101d070906050a02100c091502010e0c060721050711010c0302120d06121407080f030405090a09060207050c090117030306040c180b1206122512 70
    0x2e910f0074000f441c0d0120001e058175090820b01d14042040590703105030348a0607904285002c44e0b96003200c8c3c034128501380b050791555511514203a0500d2005801c141c8500854500080b90001c810124000b83d00b00c541e0388000307003000d420840c01100c0c0e41c60448000c1404c6485241c00c0381c051019810710507c1e2003100e062000110b00c001400c40240000c01203000781e440e0302440c0451119900d59802900d6411013003060714000c03404200c819611074148c1007280070300602c540406007220702c0d050012810006105243c1c5901481d00c000c2101480491031070300c0d100b00d00004516103450841403101034a001844420920b548591243c0011028002801054060001444000e80400410800b00b6042e07201052008042ca503000c8805004002e680d40310f5003c80c0c001031080131700b035010303103409154100740f800000c11020085072003455403001c2c2c891503a4003948240141c1c0c65100344a070f88070101142c66210781c4101c861100100c106000f4015180c240d22880300d007585da42e0303446103075443c1080044a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 185556654 1250 185555404 185555431
    0x42402030f0d020a090509010b070201080405100e011505030708061303030b040c0e120304051c170309070305060c090604090e1006060903030215151212120402090603060108062d 78
    0x21140c3d40e2282e644009046d0440d020b12455241c00540e4040344102100241484140c1c0002410303c042406056011a500c1500b8003074a440402042e008003603083c0c5540304249200c0c0003244c5d80c1400160f600a07550b05000810346034890700414030207000038880440070151504d1021107252a14005c0c010281541c2d2203140c1d40040d03000400281c1c01c1454085101c0c1d5106000400c25940c1d9000d500c0c4100351111800e880444150a02004202e809040d004003004000140a0309410014495089901480a42e42c940d100c84040b4203017072040d1300302c99900c0300050105000f1005e9a07404450611551811070b5000c1038207a9420064500e00e51100000c21426001001496018005202c60440441d010303c05807629180c43d0100e40d4440348028041c001018080c030b8203d1040001d0650b44042910f400d4684d100650703109000b11044a040f17025441d000c0200e26182400280207040c0d45100f4050b08456a40090300e020405500d003054140703040030040c051002c4a01c11401c4e00400400d18a41d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 185557904 1250 185556654 185556667
    0xd02071b091d101805060f060a0b03070e0f1917070801020304050312060607170d0608060603070e0c04090203090d021608061f030213090b0903042402030f0d02 70
    0x1048a00d90004411119032102c07401080010224000f11501455a00002d02c40c0c50400c08005041e28440000c0c00ba01c01d540c00e100440c1e107261145482400304841070035019441c0c04148500d8001510214081a42c403000500c40340340038904110200005002d402d528045005813010b024820f91201c0211000c2d00c003945507090052040ca405000e0140096113503052582c0c415035644214250300d041c090445000c507103039076030300c0701261402500203460404140342001000e6141c1c2c0540c1c0301c1c015443c50a1313400a0a0f0030042529403040b00002e019210482c90258a009001e5005107000d4010104010105d0500d41d2407010318042c00900d4028080341f0b01c0e0000c0039107042498036460414030480f1f0410040314100081d86035110016110701c03090100c51030b01079201358003180c0000794860f20f4401516100c0325141e00250540e030080d400c0f44419210904015103d121b18000d840101d510358003a11101011b810b8803001c041070902c110392519000d0b140d80c0b0301e15085040458801e54000030b18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 185559154 1250 185557904 185557919
    0x27020108070e21010b030601030303020a0813020d0b07020c22060506311502010b03010c0e0d11030307080a110c102a0c0f0608011205070b0d02071b 65
    0x1a641c0c081503034108241a000040e000400e510410100c010007080d9040c0d00804441d802c0d0800c00000380040e049440551b180d10300540a07420213021140010f41c07010001d000d00300c07401c201504154014000c40315220041d110320303021010040990003944252401c45445031035210700144840c040e100040280c030350300c0c0d02d260241c4007103038080d610030710302807002041007440b51005d840b0004031002c42111542e02c815120300c00701c0340d03640602c0d039046401003071080e41c0d074040d00400090303101100204035a009150098910009414600f600540e00da03286500107542c0502640314000300034112824101c066803424a030b507000858400c000b607400f40340750401c0e02d420451b210711039900711401c1c4c04103044100300502d030b07804c804040c8941180f0f03110701100f081c2c0800006020f079038000d8802440f1540356801650004050310a5000003547c8800003e03d0203d01c01c1040d5085074800b0146c200c00c0e280061181c0d69803c41411903030f060390b081112a00054182c01405804505500441e4090745407228 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 185560404 1250 185559154 185559167
    0xc15080c09040b0a0819060e0a1e17040f030b0a0608030d09030309080d0e0706080402311a030f011e0506011704030305010501030b010804030f0f02030c0304090b0a05010c0c0513270201 81
    0x41c160212792110441d58005500a00d4440000038401242080020207003004580841080c4c907034000c1850000d00414658450b04401d03054a0040c2c807890410f46403c200c000c12241188101302141c1c0003032115140500041d001101103d010b480c006c41c2c03d0801d0349420b40c150b4480d0481c60306480c0d84c1c12406890840c1404180c00822044c100403095143c1500402c284000d88851032000740c00b174a10380280c001403111a1803492509038010001202103c03504c0800005080041e4405e204036400103400050502995507040309501d9008007004480d00b0480c00b130712000d4176580c10320801c007000041044200041510940c0682e6000c20203500d40741c0050200d0f80303650751071810000e80030204800f00fa04280c01c10f80300b04442c40c051800f030048607000c0b0300394007859200403040d0100017070004512403c2d800c540f0f08548112542d014281d520fa0040d40d000c00c0a90300107141c1070343c03031408000503c2d1681c07114030001d030314281c0400e800c50944101d1501120302ca6801c1c102c41c0c508072502c02556440b48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 185561654 1250 185560404 185560421
    0x7080601080d05030a0b060f0304030c17070201020703112701060305130206070b0a0e0a0f02090915010e0c07020913030908010204050105040515160c15080c09040b0a081906 76
    0x2000b41c4001c03201600001c005220080040200e19202e00c0401d1090f1202c40440c0d554081101c0055102d04242c500244581c0011100b035501001036001d8075000342190301250a83d550580040030000e00e10381e148000c400f9090344143e8001d10005d000494002c1c60103800b540400d229100009640c1080030141c11100d014002c0b49051840c9124400107848000440d50b13180d41010640d000c51b541e000f400000b40c05918a00200d0b0b0061890780c0080060700c103052110184201e810001aa41e03280c000b60f82c5e908581d030710841c030842c1c1200401482d80e043c4c0800f40c208100c1081d082c5081c15a401040c103807042601c2d500c0d0b00c0243c008031101450740c064100406031044400a40c9040c1c50680000c0c80c5002d5801131038400c189001580d800090308030120b80740341c2c44002d6144016030b21410040340b42074940c402e1f544543d420380c8103410030f14801c2c083c0d00d210310341c1401c0d0a4104070141051200a001c81358203603400a100500208401c0320810144080f154444982c41480d01e80746412025940142e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 185562904 1250 185561654 185561669
    0xb070f02070e01030201170a0609020408070f08031216020c090403120b04060b1806190206070f03230402012705010f090305060109112b23010b0c0709050907080601 72
    0x200b00510040c2c5e48000c420442150080007100291120740d0440c004203043d9101c140d40d1840090b00245050b40450380703c04840115203000354495852001d07544034458200e22070307800f505c1c04000400700c0001c520740c43d002009601c1211441961000411002541603d0a5011510319810707001001d8043c083c0c2245650151800e1102c10f2403c01c224510740114105440103030880501101103450303040a8a5030001845070b01c030303101d0409072800707500e401003a50303240d0004a43d103c02c4440903000c2d0260141c0034800880c543d220382000251022101e401600c12810080034000301c5102d00c03040200c05080c41090b1400c904818a814000b4102090750715110050028810303040002c07400210319181118214000030a0030561162040c541d403044040460b00d41c1ca00100c2006030b4804181080c000d4200c41c142000301c5641c1500d01941002c4da2004d500512003c1d900603c10311284401405c03100304410301305c03115280c980080400380d03202220120404d501407402041b9190b02048083e0041140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 185564154 1250 185562904 185562929
    0x20a061a09070219060c0c05070b090114030906010303030b04090b071106090f03030a1107081602010e06030108061501090801061403101803030b030a082b0b0d030c020301090b070f0207 81
    0xb41d0072084c08082036002c010784080d548030340e1940d016024000e51041654050f003036480e0385490713500200064012240d1940015426211a80300d80d401100702e900900c01d0000a080a030700c0e643c0e0480103001008a0a500141c072411407100243d1100445400340c665621860416813581c1103203841c0c0300000b03040c048154850a041301c0300034404003c50349c000c80000344c0400c0076203d00041c5036540c4a080070040500900103078054203201d0542c4000403052007665030411415020007040041d00080c000c0380c5468101802080b0307206604401e09461000605007880243c0c5c1d10b110a508440179644010414552026201400c1c50280704481745001419001c01602c0c6940c1c400c0802d8a03558400141030554a01400440d90b400b0443d051070300c1c1d0302c42582603407012818007000b000c03040040300d0b0808143c420784404070704203103024642003442c02501d4441c101101d600c2c12104c038000c0c3c40c02642c044d540c0e8540c250104a013221003905c82c0340d05403120811044201c070b000740b43c41e03141da0107403d85005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 185565404 1250 185564154 185564173
    0xb07060231031b080f060708070c02060f031017030c011506020c090403030f1a01030c02010b100c06090b040b0f010e09030d11130303120b01020a1a0403020a061a090702 74
    0x12a40000066981200030040e0280442c21030f40c0081d002a00045407074031030500103500c10b15000403480d12482e225aa80c0c00305448a09090302c0300f45c500d0750003e5000c0801e10000304201ca0040145034820300305001ca8001c10341d20142d02015085013810700d45c2e150000502000054000d000d015070085040103a030001c14a440300003074803a003d0f1039406106480d030401041c245071103500240c892913110041000441c0c07040c000e02c181880050b41c2c2c2408a0306010780641024010301ca00e001e448005005c0360018140f042c03044a0500d82031a00b200e0003907a40f15080081221100302c00c0c0300318428400080e5608104900c1c0d180c00b43d05134400000281e0305001c10408243c084103446007180480804144040d0100500006003c3d03880003160650340c00000009140e88800248001404541c08000d0b040d6841c004903155210843d01605024003450390b5120074201c4000da80e0b200317000748140c0d450b0390b1a0342e5504007a81d107803841d203500170006420280003038948907210340d800c1003003800100316070007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 185566654 1250 185565404 185565487
    0x100b060313060207050a05030315011724010210110306150406090b28081906050906060d02090a14040507170a0e07080f0102120604020c0a0f0c0b070602 67
    0x70501e0350028142d40d0042500b808000e002c0001c0d4800c04c2d88103041c0e0380c40e450441c0010300c4c0c2c11180a10346e0300040f20003108a080d090189040c80c01544a4100300e500c07100088030b030004050525038560304521920901ca5019025445070442141c00c0c018100d6580c01c002d410010050840c810080d102c1c00100030400c0000d8200d40003030112580d941c1c15a465101d51003103840ea1218402c00c1142000c8a2003100384a1030340103000510500c60290001d0348030146180c2030303046074054007a20380c01500389000b1449034276000020308150310790a003000d0301d011002000304410382c085501000d910403070040c03a0150303440d0a010311036214490f4504000071081c04802c4070880c0501502d080c14a030f07942c40700000910030078860f6001805030001100d040c1c0d8080d9400074000d6114002140720111940d02146861900707001b141d03415240301c4014113100e83d242c2c8a0320300d4400300c5402210782e03401c15240040c0f0395182002401101e802104010388034528064601e401e114012465001c4450440074181000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 185567904 1250 185566654 185566681
    0x609020903071505040e070f020f0c011b05031b0a1104020a050f0711040204081509070302010c0308180d030b040b0d24020c120a02070e06031005070e12100b0603 71
    0x9903c0c0381a070030709031484000c060310785100300c0c0c10504080c02140c0c00c102840d508485154088400d56086502d070843c082d00309601c90052603079450000344051103404408211102e5504081e000d02c0580b0f14080c06103100400c206007007690030156412004025045c001d124081515802080c2d80541c580700003040000c1c0140303d410748031221200c010852009021420554100ba5a0042e00c00c40d41d594656001d40d5503642c4001d4a011748010000c0046c2c82c49401140740c1048a5060b102d0801000103981e0940340c540c0b00400703003070b00300042c00d244a005d900304000e914110a000c1e180003c1210100040c041501d019062507400342e55030b03451840000c1d4041d83d8035182014181e0084c040000c01441080180c840d41320302606510940785080da054407610010f2402c0c02c116000c41d5001591104001e124840c00c03207103590b054000051a0700440d079180c000e1a8000c8140c90019120341011000540c9007514803640c030303081e910a80741007044ac4914811418841d40c1203c02ca400c0d450403003001a5003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 185569154 1250 185567904 185567909
    0x414010c170c090904050106050f030106050a1401050d05130b01060219060c02120f12010501080906130f0803090d030507030207350301030f0c050d050307061508070e060301060902090307 82
    0x841c5240c074000750140d4089000d0312095038008001954900b81410058081c08890154900c0344014001720041d0389014400c410032500060015490340b03150107401e503601c5c00d0f2815103e0500204101c64190420644912032040c1c443c43c62500e401c0466041041c00b0b140140c000c407080d03601c40344e0240c41e004421b80c45229075550240c0302041a5290f050202d05180031200485410b50000c240742c1d003d2407100001e0a903c907485440c03d41641ea860004486448007562041400d0700041c000c1140640c0a894000c01c40e8010b0300d8100140080340e44080071b950003154090b000d6007020b0100290749a03d80038041d0060314a19042d8200300303803602e410342401007054401c4d183c0700620101e0369081d80880e0008484002210300a5200e6a4a06001403e942485411201c04ca01c940e07000c100c80ca40039601100180c0c0280003541000e0035a07913014024001c010205081c14a01840005c030a803040080d08081c0c002105d58100a0030180140b40c203492441d0402c0c807003280180300b0a5595140010759404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 185570404 1250 185569154 185569187
    0xc030e0f010603120318320c03010b030109030503040f0501020720040c0806180907050d0f0507050907090306021804050c0a0215010b031f0b070602180915010507080c0a0b0414010c 79
    0x148221200180640c42c120811f02901016664003c4548030002207800b01d03a01805a000384070014080040500b05c1c0c40340c410080104605002080c00b082e40e0115140c0c0369031080e40014541551611106451106440e0710500c2c65040700008a031381c106030003449001c115600b400207031400e004002900c2d0903120150b4841265802000803440141003001000600000d03041c0c0c2881d44150070b0110b840300002601b51050700c6070001c00101e80c1402c0b99000d02c110f0301d941d6505001410340c1d6854002c1e502419420304280100c41c841101d40d81c86d440380700c0c001c0710400d107901e42e1842400e00284c108014030f10040d25642032100104099203e4400301d80e80039604605083c4800581e48680c80d00400c01e4202c03103840c00c00896101c08122a641c0100f4060741f9940740150300f944000700b0420118421a00c42d15003c5001464030f0240d4003074409085514422080780341082072070718481d03117000b00c01e14041d54002c0351503050000748500b5111100ca9460050020302c00b4070810000584002048010b403070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 185571654 1250 185570404 185570423
    0x10303120c0504050a0305060402101706010c0303200d0e190209060111100c080c031006111e0106030309061d0d0314030f01080f0c0a090c030e0f010603120318 70
    0x11442c1c81201201d0181c84000c0c142a44c031500c2e402d06c503540f40c000711012401482e50700d800c1d8098500609001d6503880c950941020595640401143d25002c1c8001c01c806054694903801d0381c003440850701462001d0701200943c0c58038851a00f280550310a4414407450f600604202900c100310030b2100b040598040d6043d01554a41c100101d4940e0010341c80200c017801240101e41d0189007d400c900c640151990701c5030100c0e01c41100c840c0307040c8030540d100d10030040d00030400c01015005045091040c50000c0c25101e01420598030001850240c80001c181655101c43c14000c150304a00341201500c020718240000c000d80c03034401281e080c460305a05114400000d000030401d8822a49001055007811285442341040341415802601c20300541d400e40c05001c40c103138104d41c2d001594000362080108040c620524002001000f01481c030a08401c15881c1e8001c100d54403c10000c040c03400c0c148000005841e4a181040003540c0309032203101e010036080000480484500c0007105024682148144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 185572904 1250 185571654 185571671
    0xf020c03041e0302090103050105090d1b0f06060b0d02070c06050a09090f090f140c0f01050a030f150303080a0b0108011401030e0a0516051c120815030304230901030312 74
    0x121642c1407980c0c0f00035840b0310400b00100400006403c0140500a40c0b400c403072120801a01c195041208420740070120712205007640003244140c5d4104a109028250025800c2d0300c030072000c6801d034041d184c05401d00d0380006080040082e5040f900700200203a03d807050a00d000804010452410707407003080d044079203c0c22030449901c242d50103130720b2465200d508400390391903610b8403200c140700c3e20f94451405e000301c80c00700c3c00c1d40c00c01c03d880740c40c80181659010300e000c8055409400910001000240d141d5035403100300c6a6a070b80c0070040c805540030b9180d282c840d08c1c04d280140d0a4a0b5000c101c1810400c80500412141068101e6010103c1007403c01049400050007010300d840201100540148208065601c044460303a11070b0301130702c2c2c0a880088007000d03003013124030706030941000c003d14045074107201803007417441307042c81d44d4001585080d07404080e59043e0000b8a50b070010307001419910310000000301e0b0040c0440b11500032040039507c0f4003542d895074601800e00c00c51100d010140b00d840d207181e03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 185574154 1250 185572904 185572949
    0xa140f2209020703030b040c081b0706090f14070b090d03030903230306030c0409020f01030b13020301060f0306050d0b0106030b0d0b16082a070222090201030f020c0304 74
    0x84034058000c01e4411925448070b070900070050403150003c03a02841ca07103841065410701c91800c40d4032540302c0700405009100c54015408065200c11400d80d800d5075a908100700184c036122111451a014400c89040c0e588040c00e403030308100450340310052010003085140700340d03105e4203020101941c0604000644040b1400d00fa038031100a80415503150b015042008000304071a0042c500850b42a811290441305d904184000c840074058044c0d030040310340281c002158400d0700000280500a400b8a00d901d501640c0c01e010b0b13070401e030002c1000c100072610340c0003080d1f070511510005243c00c0f030b0750a1144466451300810b003030043c0100b10030961601c0703030000c1540b64030824400306948035100c03995600d46000c20040c1c1d024810103502c00281d0a201140088854003442242c3d000c1c0c0390510804101001c2039210700d6400031130226041980030b9104490060700028a075040c6000600110309009079100050407144c0160911a4562052020b801c50540c00400d075005d03110f80c0030401890300d010881 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 185575404 1250 185574154 185574217
    0x80615100e0405091b0303040311041a10020706021207231908130b190305090c0d2004020309100f0e0111070c0b0f03280507050a140f 59
    0x11465005030620050100102c000500305d12510400c541d800c0341803503204101034880c8100d200150042040d0360803901a454650310152505a504401c0522004600007080d13005c03415010540142c1c01c0840c0c100070a03601484000f4003c1c00c907001c09868114581c0d10500825802d00400e040d02248a00c402c208581c02c2000e65001050005000c501c0c4080b46081c00c550703403240000e521088001c1c07030002403940d02d80090396440d001c11413040078444806e800c100d00400b40202019014030030350316811696107440c480c2150344e03406420352280106007034188510420350319401d00e000380d204100b045412240841c461304000c00c1841d02140800d40e07110b0f03910140c00f03241d600c1d20f0f95518011092101e0040301004000040c4200d400a60040c1c3c0e6401c40c42c49400741c0941c0345906c410030000901c410700076403411214400400c0c01c5201c414074101e40541140e10450b441c40118000044403000d554004414407091840c9511075460004941d1291401c2c0c02000410348494881c0d40162a1840c020740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 185576654 1250 185575404 185575427
    0x609042c0f07030210110a080d1d030f0717091e01110606091302030a0209070f09090908070b0a09050709240302031207141002070606090506010c110a0b041401080108061510 76
    0x900035150b1005510500003003510100200003801e0b0b0070780c2b86509200210980f150b030750030300c106c0c58101501a00d4400104050003484038980c4410007540240303039586e00d0340000c040703103c1e000203c04020440001d01100254846011140d000c3d20030001c4698500c0381070746c0e116501c1441c030305d02004180f001c21b01d03080140d44c00a50100303c910030001c080e680300b0050801c18982d030b5100c06050f503640c40138400700d409026014200400421410300418030602c851034020361016000030b00c0030710b42e843d640d0501c203440d000702d42000c0c5c881c088103600792103c600e81d034480342e07030140341c2d841c401c0c511350002f80c1c1e40183c2c4041008460011404006001840d502c02804a000e1810f80d8803101c461128030000b0361000c2000c88140380740801c003082404a91007514070600060315103100450f005d0300d6031400c1c9410b04034444c0d840301c4541c0c80428011442d001810041444074000e000c0e400c0900300260203100c05810150306035005208210065407400980e1030121007e8444090100300310404403030210078070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 185577904 1250 185576654 185576663
    0xf090206070f06180f1209050d050a26041412030304050706080a020304080a031109040c0905090f07090303030b010e0409050c01020106060e01020c0609042c0f07030210110a 76
    0x452807a092110300c941d24a211031041c2c00812201390302c13480d141d00200d1852405000107040e01142d0001034a280780c03d2100328a00d08018100568450018810705d810141c101c589821a07005c410030841e940801d0180d02c0342c1082c0e0319a040402c07c400903124083ea1260181018a5921741c0b64103484038000080c0e002c00d8001540c0c4d4900e010304006540305103511800001801020008104103018404d83c1d001d00d60050540b450100c0c14001100549507103e00400c401408214080d11a6240e03c140c20381032080e512120710f081d15000420080100c010901c0780c00d40c032914104291a40c0c444500815a58035040010751000201c0040b40c0a803420f190907904a403400311000c041c001c000605002e0202c00b64000c0c44015180c0b60216141c2c2041d96103a4056401080525214030700f840150070311400c0036000140c6030803942100a200104410f070f01101600b00201c01c41107103c144444c90384800344c034005003945443c41d4003081a003800e1b0131100081083c01603407841e4419090107000000f5802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 185579154 1250 185577904 185577907
    0x1210605060705240705030f191e0506030a0803060d0c03050d03050402040c110c10022103062b0b0c0706060305031c0e030304060c090b0a0306090b06030f04060f090206 74
    0xa500d8810b80c0d5045091410740d4500750f41c89640890009840c410b0311171365003543c5660442d262246603d0000c0d2024002c80d01d280d04141900864001d00c0c4500304100540400110501010300c01c0c06048401c0076003024080e030881c042100128946004598000e5002d858654440180d401d00342d00d01a0a908003d01314007400c000c25000b6270741a08007078081c2c2d008a82c204804019002c080e80c07880c4268480c071440b50401c2201e1021441c0615001191200900580e003038901022462000c8494140084250410105c02d020300c0c1d040001d88511200202c00302e000c80c4100c83c0b80380c0d071181400660003d01d00401c2c10700154482c000c2c2000d581d070050b800310f41800115101c0c541240c880c1c000b2412607036003c80c5c22400c01190813480c0a001035016880010307524540310798903001c010b44010400e540030701014040c009022264000102035040003030f40c1c00180d40d418120b0320001e5554103060240f00c3c90043c000d00c21041d01c10300d600307131700103a100034005246a07244201c00301070840b100c00603610050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 185580404 1250 185579154 185579167
    0x61b0b06130905280b0402010e01110106030b100602070e0c0327100f1a090a09170301091a013006030305130e070203120901090b041a0c04050121060506 67
    0x1030024880080004c0030214401c802e0101010010100109002401d21140d240100b8050750040040050306041813400e5060300600c40001801d4941507030048613680e0001042012110f112603100020300f91034405001e41a1503d0340c085820040a0302e065482000080821303141301041001640e40b82c98040d0a01d48402c9400b0800d80350074003003540c640d0ba40e0601c04911081e21451041d0344025510016409038004048148040128024001c00c1c80070f1342d6070b00480c040703408107403400d5100206148440c2c0d2907040154071810b4851840c01d20950041e0b0300c151500903a041064618046518010802107100d112030007016544c8040c440502c00d8642000402410351002c01040b0442c05151000300880e42c80c10032091401c011164100180c0003400012a0005184121fa0700010514004504649030b41c41d4222032000039542103c0d40310000130203904d591150000d0a074000e05c0d1900080c00d2a03c0d160001c1e200800665540500700c11000c03004801d5512903000002501c4040e00c8280c9a16 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 185581654 1250 185580404 185580413
    0x50a111005090d2019060b0301020c0303090c0612040b040215030106020115080607050304150b1804060b01110c2e0507050f0a030e0409030302090904030513061b0b061309 75
    0x11402d003044000250413000f460080c05019010110505610303005100c1060810031041e880c0035500401c80c2e089803a00c0d0030305855074090002e410000843c42c003455403410721080c0342e45030113002c8241d81c0c0144d90600040c019007001412055000d900320038a030205071380340e1000400e80d022480114017032280110010803901e81c15480500084492080c40b00160f4544000c01c7d0780c0c580445000001035020000200043c1d070340b4100484100f56148041250211000010f100070602603690382d040d00c60800300b100307002c543c1c0500c1c00d080c4003e00744400944c04002c182c50312060042c0040340155040c0c00e0b83c082000303001030100403180742e00320f000c60820f256480082481d0302c0407005036081d04c1018403c061004000c0380c040c0e031095150b2145440c1c0760b125000d00c0060030000d0f90503800e1550034070a5075410b4840051040c803d9110b07554440d40d031519a900d0790708680c07281e00803004000c1021741244456540c151100e2406030000799a9081c1e070346005c000342140c0c0b1521015806141044080c00402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 185582904 1250 185581654 185581663
    0x307020a021908070b07080307210504080d060e0f040b0709170309010f1403060d0602070b041b0b04051522030302060901050f070e0d02040213030b0402120a0201050a11100509 77
    0xc40c8480d041d134455039134a00580036a405a400040e103418010004a13142d00e01a01c1c0c28440c0209000024184031484030310300e001c4800440701a508084001021080e9101500c05d42c0f000c0c0000b032100489030b040c50620440100d800030001400c0d10301c11804184c102d4040e850b1000180440e071070002000342104080c03500c070382141403040d001c28909803200e440365000310740360300a2405000b00681180e03503800070480c001002d080150703003065080254001250388045a903118038001d801d13849945541d00e10740c6043e000198000160303404140710a1111303951381c068103051141a003201e151150340700c640102c0d400e032035050b183c200d50022260000030540c01103065445258894000c00090fa40c1c03174503034200b8101c21a000800078500381104a41e6141c6044517400c1c1c10b00103040141452004030300312150103030b20b410a680195080041004625181c06c0310700c0c1191200b40500f600646950019141e80520040f1a0902c0301c032101c05103030180704100c0c1850100902c44184020704020714229203a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 185584154 1250 185582904 185582909
    0xc0a2306130f090c0f020d05030c0f0f0304030905031603030c0c2c06010819020c07170312090a03050313150507080402040c23090103020c0709050f0a110706020307020a0219 76
    0xf2a030400200070860341c02682c20701c5200395282c010385505079580f0022202540022b00390790795400203101c0c4907004800c80024190215041880c40d903607042505001d841e800d9030f503003c20702c203078010301105100301d00e0301200c482144c3c0d06003081074524402e460004111070302604441d001c1148a00c204207008c0190362a51480003800c076154140b9210140112820f244c02c40320350300d80505040e040c440070110323540105902ca500c41d094400c2552545842c10749200010034050440d03101258007094200c4c0314000039040041c0b80c00511140400703a0b00074086000080c812500760610822104c00d01008044040610081c10b404000d42d24121034040c0c1030328030a4505074022807404a845a0240c0668800b41c1c1d050b0b902c407840d0145826042c084031803030f84034000c3d00381055000e00110924540400840011b0415400c000c9858030704510700c06198040144810601401c259086403444000e1040703401f0150060070142c1c0d01d59807282e05910b0300c03c0c1200c00a4110303c98640c4100c0412405003c40113 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 185585404 1250 185584154 185584169
    0xd0603020a150906052208060109110c0615010c080f030a061202090c0d0b0a030f050607080709030308040c030f0b06090a09051902030a0b04030f020c0a2306130f 71
    0x4031182c0707031101c8045600c11001d010010a010880501c08140607030b0107456102955810000782940d080703d224105151a030141000d540100014480b030261030040a00000601003c40c0c1072050764600d00d96100d802514614004c0a60560b00255910800b000030a098105c000c46694a00c44200029150b00844556410a1501101042d190103440d0034100c215001810f0034640d446d007401c03d001d50707481781007400740e01a030f111010341464444200710802540207070410f01d940d0b0b003a070030082e05040b0010300c410300b0000048204044070b41c20074240c605503505483c08aa841e52146406800700d105034002030609250342000500b00314079000d18910440301905c4540c125110f00e0107180a803006610010599004040d80411a100c0000d401c08494001401ca80980c18079403650080c0010a590039400a059000e205a4070764041000c0382c0803c8d001d441b11f81010f482d100381e050064080301400680c0324194907240f83c4540c3d51100b9502600040403458100c9581d403403003010001024898900c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 185586654 1250 185585404 185585419
    0x31801030b090f060406051806030c011b061e020304080d060f06090b0702130903080f09070e041b03060609241d07051314011b03120209040209060d060302 68
    0x44554800d0141103403000c40a000d541d940e0322000c9152004560080555411681e1411b0004880d075aa0549404191514400703d6142c2013442c1410b0404042c8038a41c0d0610403413180800626100760411a000741e0400c1700014491055540c0d01c11901c082c0c000c071120f0a0010086c0014030442130020b02c6601400d001c200040c641c1c4221410460f40b481c402c803404159601d801700404010750b8010310015100401a00d5242e03c1030503d00115694188143c0000b02c0e00ca0400001d540b001100a400030304400c0200020792030b00e4039110526400400040881401c0c0d04440b0000090b00e810302c2c041c651141d804d106440d242c0900d1001440c6d004140c4180e0003195209000c01101d07502d81105071140f40581d0913020b0316002500000e07040260000d0104a01000a611424443c980c2000501201300640c002c1400100004000a11042c0141045c840b10200100001c0d04483e000c0d01c040d0040c4000342c0c0304d185490000d030090007103482850700a0000910281c00c000c0350781c4a442035034401c03140f20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 185587904 1250 185586654 185586697
    0x1a0708090105010b0409021c021803060907080d1d0d0318050a0308040501050c0a0f0f020a060305070c1106090a08070905130f0303110412030804050606030307110f0a03050f03 77
    0x280c02d8403000e2040d02202d0804000c1400030541c40d07001440350081540840e84032041c450384003001c0b42c0c0822150320f100e4244d8194403a091505100d1540c00080441c0140344081c1020780d242d4442140454007000d07c148880d000180000f1203810540000c002003120b6000030712803d01410461083c140d800114072801d80120311460020481020760b0303000301c04541071500b0b00d40195484c1d03201d51403045507445200e11610006243c90650b80741544035001d404800c603018410301500a5881e080b800a05090a0030040c9082d031000d006d03801c00350000640d40900d003041c00403d030320780700d03446510750022940c0c5d60100e0485400035402088420f800010003059464490315407242c3c4003400010400c0742400d6461000c83c4c8290080d040c100c4000300324601e840c0d611160b031507201c040c2c40c408a002c203a882e0108400c1c4402401840d85c000d509a0142d440e11400d980da010001d01d80b1007004d4030030511880030780c0c003a403543e0740c068001d140c1c48400c46220b1551540314070f0f541d4200620491b03403610017130b040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 185589154 1250 185587904 185587921
    0x9050d0206070c08030402060c3a14030a090201050c0f0105090f0304060c03030e0723090606030c040302060c0c09040f0c08010c09090903021f0c03050a1104150c1a0708 74
    0x281c43c10690800314480c1940c60b20b50802145074018844000d4500c14a100d040925440c0e0515070380c1461400540032140da904082001c040b98480015010322003800300390715009405604495010341d881c1c00000e07080c03403240300503611801415500c448a110301c1e1503c07046050154400f42c01381e1609411562070f080b400712103907030b01d10490086034002050161b82c200000d00a4104904504052080d201007035107425018021741002c5500f201054441600b6010a0a03c2d01d40c0542140d01500c60360f03d1403500302100315880c4107521000f80036410000e0a9007102cbe10030701c105603d00d18018500d403200d06260800324030001c1828000d0764451490980011194414400c0416000450700d4170404985844030480042c012090207030154014900c1e00b120440990784120303109000c2e008001682d121000d4018221390700180340f101203615002284011410300e00682e41200e1800c0761842c0c088003105030449189400800c0200207542142004600641d0804402d101707034130a80d60680980c1c0e40d99007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 185590404 1250 185589154 185589167
    0x8030a09050717030723030712230f070302100e031309050405060106080402030c032b05040308040b070201110303010b09040e16031502040812070210080403121a0409050d020607 78
    0x800c00d00da138010000080040c040c90102c004903d034240c815806294440105400e5901c00700046400074a03d0740b180e42c54582208024400720482e42140300d08040701c0d01007281ca84900c0440503009100800e401c400c06200304502001400c541c4420b001007400040d00b96503d0b0003040c0b40490005160745c01156460f544d120b000d10590f0000d000f031031307180d203040c000b91180b08c0098404c2e605402441a08240c1e40c030100940d200c542904003000000240100640190b90111201d0104200c4200000c002191406081e2000c2e81c02183c05d56980d03050310302c01650300d01401d084c0030140f404080700014126444202a02d94664180c40502c0400d0103c072015807101542c00c418210010038110500103c3c4000b00c0170002000e0082e80189440d40712043c00b49480c404241c0b06029110010b0180c1c01c60401808800c9110180e0030a00040d06081e5005454411038800d040103403541c5011240d1407001c600c00a62444001810070058994a405c003503464202c811a0b81016100d610086414540300c0c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 185591654 1250 185590404 185590439
    0x506010c0807110619230c03070b0a0b030a060e06010509090d0f030e0a06200307090611010204050d050d0e100c0305032d0406140c04090b04060308030a090507 70
    0x40c01901d840225a5000a4036a03141000f070b40020b8140104c0d11001c180f20248110606030b62034140415a00c816180f444120344c150219141e4006c1c848481d000400005458403d613010f0700c154126507409401c01c0043c4858103619905224100c1c5403014020582d000a5282031046c05480760b507030b01d81003840404c1400b03540445041c2e20044903010940c1c81402601c40c4800c40d45000b003038500d6100041c500d020703405c00040d55102d5617074541180031414411050302803652009424254941900c000d400940c05100350014018110b0340c0010443e030030742c1128058031f0700614070400150303d418000c1d40ca1208103104004034020503400c424a01e40025103000e030450944c2d0303011200900fa0f60850780c80c0c1010308040d005214049c4200300d450404190307030083d20907120704000c3e9403915003001c60507601c06503a420382049100080c080308006100072101510700406000c42d0302840c0c08046401404158006000120702100b8840c0e00300098003e107400380e0140c0d003111b50301c07500c17403200d1184ad8003c40f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 185592904 1250 185591654 185591663
    0x150608070b040608040c0e15031b1c030c021917011a04020f0c010204091e0204060207030b090a060509071401051606110c07060c060e010b22020c070f090506010c 71
    0x42c04100401403140d003403140c0c024400c0b490140d5455450309080d0800c20152400542c42009550000071810b0401c181803a01503200300845c40c1200910205541c6000080213006050101c2e004409041c003c591480320b466000d0228544141c3e8064809100e803454010144480700c02031814990788814040c196494458814610204000d0b4040100a5200089100801c10300f07021281046800384090801841440310101701c4d49100003820000340d10b5442500341852040c070040c0b0009a00040c00016294010402101500c0d4110f0480c980070081d076004015605100801004600c045107075021a10021207130a400c054950040d9444e000750711501c542600e031520000c02180d480d41144500c02c03030520303001745041e4601d1001421b20803950000350202d190005910b003000503078410201108146c10080080c5040d440004030000e40a28890309050381921407408085d0540c1d0403500c170054458111825070340e5401c00ca440702402c82c458842c203240f4020008005502401c64402a01d610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 185594154 1250 185592904 185592907
    0xf0d141c051f0e010504060b040806041112010203040303060e060a1805060a0b0a0914040209030a020d05030409090b060a0608061f170a05040c0906080a0209180604150608070b 77
    0x1060601401040014680740307540789003210b00c0c00e074002036a00d4800607095034259004035604100500065a041e54800c011045040100300032581d4085501c40d0404d41c40228044001800d400181e49a200d00b110884154400801d01c403c040d0150701131400c8914044851825541e400d0801a09041620400c60721101d00d1000401030665a030103694410f070001d0400c981d50341c45030303200c82040d08811a014003042e034000303061011041940017441a08030480e015883c1049400220b40c441c20014002801240d07040080c00130003c0500039900540304c6200108040d00c624100410802030039188607001e034a500c000843c2251160003001d2103414080c12030700d0b012000c001408500105c8460403010440ca10050405411203100424001e07124143e0100300e50400341404000c40c00a5030160120515003601040b054402203050f065282d01164104415034820303603030780346441240c080700703155000e1030b8204810881c06007204100081e0204013000384e162034200706035841c1c00074002c45048020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 185595404 1250 185594154 185594197
    0xd06080109050f190f0c0b04030506010f0504020a09050103021305041811030d1e0210062303150112110a2c070806040e1009050c040c140403020613080f0d14 69
    0x400250207030700c05101b10762616a00d03641c0c00184c017213600603420440303058000000401101e4501400e0201900c01241c04516140100300007030003002a510546051507000304aa03c0c0640002c41d4500c000c1401500c140311000c440d0308600424000200200d5500701d042c0b20200c2e0718140020600c00c0000c00307490f5050701c042d800c40c480092a40701c903116411449114032480b100802070081100404000404141c02054810083c00202c07030f0f40500fa010350312111920030400d40307940c446070440705803d408184000050030501c40d84403100c805140c04c031350036441c0043c48203003022601360f1411071750007501d1203105d0010036068103c40c169031b240001500c10012402514080c0c0c80718005d401c403003040f1103c0f04c103036440d0301058440289013554179400483c1080b940b1300b081d0094070460003d03480c0c040103000c00d01600580340d015a000180c081c03103022615400f0298032804440140c00004111540c810a1841c5550f0300c849003110000050074554107104c3e081100303402da031004030020220200108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 185596654 1250 185595404 185595413
    0x141005031e190903032304050c06130f1805010b0403030203090f0d052409070501050d090309081e15040206030703151805090d08010506071203020d06080109050f19 72
    0x100c003500b4405840403003084416500e00342c0c481c1c6501d5030320a482c0400e10482c00380324a401d505040f10030748003000c1c610042000142021400300c08080044810365224000c104504403028000d8000140340b80e4203404c0403441400300c00c00c00c480b0603005401071000e680c8070034042034980114403008002d030303000344041010f03481d11071608a078110010b050081001580d03200c3c685000d10600044401448061000003400d00f4240b58940c03003034a00c401030070803514250000701144200c18280d25119512481c1c4c82c20148150700700c2e0020000e40003140d40039034150b54520007081e90340410942c00c2c0b0980c10000031344926054850f109980081001781541c1e1081d030250013a09601040c2c500203119800041046d078050001d2040d01450104001070314600069607074500940d000000f17051049034801000940d40341011103008c01e0740881558844854080164043e000303441c00ca8042c14105000490011815404082038074014021030340d04401c090010f503225803407c50842c0626140150000204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 185597904 1250 185596654 185596711
    0x60305120f1303150506010e0102071a040f0b0d180b0711070e0a0b09090c030c1003110307111507050306040b0d0209040506012303070e1305010614100503 68
    0x2030401412a00c0d010607030088440c0b4280e650800c6a0710a201c82c4183c020901c68482c26510580c00e007001d2000040800000c0e5640c10b5502c20520749000064800a00f0100001518014654140300c802c0307094441020003000c0d0808486c03100c14510740541418021800e008084025800215400494540c40402c840f40700d0118070880251045038000584605100700071840703100c0c21840051a0f2a11808102041c1c1c4003614110607544078900443c8650307000b20781c50403964800c07102d005084000c0d5174190081c012000e00d8440340000401009001a0000654221034a000c4240d581c03c00c3c00c80041d40d0700d0b078001d0b41c0350360000724240001403503070070f1582c0a140c480761300410007241e00016600159103040100c804403495081000104100d440c0403150f1000c1c1500c2000c407a9581040001203035441605110707950045600301c011520850108202c500307002d81100090107060b032216000c003800183d401ca0103003d074410301c107150302480c418401c0e07900034442446600410402481910b440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 185599154 1250 185597904 185597917
    0x20a0509031006171c050901090e0f070306060f0c170c0109150b01020304080a081b0d0c031b0302070902071e0f030e0f011205041502040306020c0d020106030512 71
    0x1446410020a00d05036400c2201540c0409402c00206100f0304150418010044540340d01031158444031485640046a00301d1891085c41803400c0c50300c4942c00c500403110301a0315484013048544d0743c000d2182424603420700c903200304810746040c80504d541d484220b4480030304c3c0001200042010740c1ca680015500e441e06400d281b2912000342c00c01d80420b44180c02c440c2c0b0400d0031112000001d6200a000846000e109a401c03000d0003e582807070f10300b503840d0342c480c018920000d0070000d0000790700919081c444100e00788803006000322000c4140c644006804090ba415040c0c010804042da0b403400c0e03060480e107003261558564060817403070b80341074041c40103508100801c598100340e101c50310002c100341c01d00e1180e10758020078468640d11160309002d42940041c40c0e080d03015022041c1807841c0340e60070520002c2e400c1071568000641d5074442c200b203000c51030070082404000e8000240001407201c242c02030310350038a4403410780e03105a121500a0303080fa41140300091240d004502d03e01194215000038181 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 185600404 1250 185599154 185599157
    0x1418090405011e02180108090a1106070605010b07020a05040c020d1805060708040e0603060f060f181f0e06150a09050414040308060901030b060d150203070201090203060c03010b0409020a 82
    0x151005005002c0d1811800361070040b405642c0030520444400d140717107007051268030a0038400307101e04001040c00d844500c242000380140c2c1d01c90000002c15100e100403100d400b034010303100304030725612050f51449981c030281041e1711907040d0580c082424036040c0305041d28208150002e080342e5040020070ba588040d4070034110002001000700003880e85a142c002e1445910400e20f040e500d50814912800d5808013070141ca010340d01c000c0402103040351b816081504124211080301e45a40080e002842100d4251084514081003c051283c0020662100801810503d03e1889980d450340c04100040f9001c03201641d201e84629400c4103a52001c100501e50303961185000ca248646032404a010703103030485116508240810100014107600c100c055400060440c0d11600c9545140c9030890320030000341c0001d100740c4400384001c0410944111115a24105c400c043d0744901d85200d0181c02800152400d034000c2c011100040c1a41c10301d00d007107a050702d8000300c03d075040a003803220250082d0001c152600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 185601654 1250 185600404 185600411
    0x307080a111b10090302030a091505031302031c05181e09040c030804030803240d030e010318060204030c06020d080f07052a010605041112060619030b01141809040501 73
    0x185460b0f15000390101c09000c0c0d0011a9203040100c00201000c0241d4001c400248008000301019540720040b00d801135118100303002c0b40b5025000090504a8481e0917401f05042c400f490129550483c02800076008030410880010300c0100a01656000248030000300b001d0012007c5034614040d41180e40090080400c03184d5907072a0780e81e0003040c0e8032a400540d04000d001c001c1103608074040000076012004010070000049091020940e14404504014103109681c6068051648240c0c09284130091a01201519840c6400c101e0000d40c0310307000541389040c106202180460001525500394251a036903500d40c1d540c0c000c9101d030080000340803502000410414100c02280c21080d50400c0d45082080c6000c00d030b13301d1813440c2101c04a0744418025800c2240e08030303000a050f001d803941041d1030303840e03200d4987d2020b0004d0064407521b1521008c40c0c82169083c12043e030315501c0196100c00a880c3d159441e008100f1000a60241c10241c0740200703551562020282040a100381c0c100d4401c80020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 185602904 1250 185601654 185601673
    0x4211709010c030f0e06180705030a08070b010f03020906010f0e1507050c010509090103060e010b0d0302010e0601050f060a03020c070308070c0303030f06030c05130e0706020c15190807020a050102030c0307080a111b 94
    0x1905092002c2d000b034330103040100702e0506100054130f00d10b005102c5040301964891175640415000d5078001c08150601c400140510500303030049600c0764013410000c00100301c0007028481d004081d08114001e03070b201d224001e07a00d030242d40a401140c100004c004e012100580c1b0b184d903418040e003070083c086e5105549801d00f070741c1c1c1919103d10b01544540b00ea0004603802500403000380c50300905a20003403144005c469001c0c05602d849c800c4400e600c8444c5805692200b0280301286800119407000300b105900240ca03105000d1021640401d40e4426907040c0071208481140340182d440314000a070109803045002c00c13492401c0342e000c400d50740c032668010403505036000203542802c240350f1144002d600710039072807413062800c1e400010700f02c90004611410702c203151015280d41d4403401c9100044c8402c80c40410203090080001c11030155000009640d07a1130030508440b0140c100f540e121000c5207000e0701003401d4681c03034000c1d40c41751903050055030304010051091146608040b82114094010f41640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 185604154 1250 185602904 185602909
    0x50d030509060d06051806101115070201090308180709180b1f06030509031b0a170d0501170d180b12160804211709010c030f0e06180705 60
    0x40c1181c44144107001400310310704403d001103500504101c52807001c00e0703810044903544400c208c25181983c4d142c0990350070700c0d80c80e00078035060015148080f44841c080c108400310341d05400800b802d40c400da45400c2903486001c95403800310320760340205a0030f03004040c0600c0035000b507610203200c4411505507122305604a403200d0a0707036074060784c24510302086013410807400b4008010920050440e03141c10072440ca000b46145491740a0034645d0b1a00c40240c0094000c0d1403410044a01c4c59a00146030b080361941503070041d10664081e4100d0f9a140d814000002000042960b080d45140452030103490108000b030800c68541c413640001d2007440308482004a265060040a40b446c0d003000c1166403658204035120010520203680c444040040385000c0ac800520801e03560500720030740c0440c10342304103840c50003038492042c0c2c640a0f1100081c200d0070030880403815000b4842c64035180d00c04018280b1f0010030790f001e80c0d42c5401604020790094001c68101c011028000b0240702e00312054450681e00c5400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 185605404 1250 185604154 185604157
    0xf030f0504050705010306120812040c031b0302090c07050303070f1209060e101104060305060d0204140414071a031b0307180807060c06151e0305070915050d03050906 73
    0x10306070350b154041c0000f80074958062041d4409016900e0305d0620082c4e00c1e40d1540c0d02c42c030034204130074210402c80c8003140420018958100c0656441170300c00305902d05002c2c3c0d0319a07941952000fa44600c02e030002260744440c44504485505401402561942e030324100f0592305c1c5078281e001d07907042020261a20000c05032500c12a4139041c450000450111045087d49150000740850160442e01d80540005545504c004480c00c5401a080201d41e1b42c1d50040040c443d10030381c442c0650401e00b0b10803242c987c1c003042d030a864800c5108103c1504135001140a190b40d560040c010348003508411141144050550800303560710000415160170015040e0703084441d542c2041e10f2080210300d601c2140a420758020700880050b02951f40180f400fa8541480101421b1001c034000d004c1660302d00388442034001e0051008050002e900b22240e40030100f104030440703102903100a42d024051550086080308103401b6940250001c2a103003a0101c1c04c0c8005c0040ca50402d01c021810b1080800900c0102d844900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 185606654 1250 185605404 185605411
    0xc080301080d02010b031b0d11090406060503100b0a05010311040801020a020f0609030f0f030703090c06090815040f0b07111c0f18141302030103060903091e05010f030f05 75
    0x800b07450050032108000c0e0955600d03059503403281e00081072003941107a0301e82d0403095882d8115050a45140c040c10b209601c0b80003054001d8000c140380c4204002e20050381c200078210b42040d800c60b40341510410091007161084920750358020440e8008004641c80b03500141700c2c0ca038400227014035103561600068220703800a024a0090707004190307460a8160140002540320102c6000b440c035100d40b1191109c402d1107003910720b502000c00030012030320700c4d4820350069061540c006480034225840c1c120160201600f0711442000e481644141c1c1718a21000500701d00540d0b0280c42d070448110290b4034002002c10090003802084813000e40c0c3e000d4000704000900d200b0719030052070380940b010310344001c01d8401016001d40612000101440c00d40400c0c800e030f242100c00d044140d0f05624038107000200351180b800300e0b00f10100d0004c0f00100a1204c19880801d00501c01e45075001c1040d55a0740d905102100d0040540711100e0007003041040c0e5000f2854411280450b2800044106241c0c041c2d404035101503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 185607904 1250 185606654 185606669
    0x90105010f06091a0a0e03030d0510170303160201110d0b0a0e04030e090711011a0a0e04030203040605031509070809060a062102030106092f0412030c030c080301 71
    0x5000401058030024500c0c03018046502e44070403400e0502c40070988902c20014110308034071000036140017140c0314450385400100c0c0203041d25034403c0d40400200142c94103942000c49054096030004581178083c44195005000e84059419680d494001904890b40020b914055548035a4403000e50740710031004118035948030b900000c689000300e00f4010178840d5074001200000c070000601c00032a03041240e41d003034148111641d11069407000001c07582100303901c1500c2465070170b0031f520380e46188001107030b845a20800d59000c6941a031380e590721183ca10003a40d014001da0820081403019910440c002c40d40002c0581808040b11030401c085120b600040b20f070b4030002400300c41803040d904014042c01d6003110702e00300c05026190400120520742045000486c042c8203094250400b1510290812001041c007004200b004090034100c40f03400310240b00e4411010b180c0030490210700b41d10b110a9400707445480c0070311400311803540e8003620341ca02c00b45004d50038410800007050004c1e0b0860300842c041c0000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 185609154 1250 185607904 185607911
    0x40b031f0e070813020d140f010f090b070513031211060a1a010f020f06070302030610020304080309010507020619030c02010614060d0c1106070903021c0f0602030903120901 76
    0x4105405610030003a00210700300441c190900032242e500c0880940c2041c82100f03c451a01510302c009048207400410042140d41903441000074210702003140d6201e980d0945c0240700c00252a44013600316415030200801844040d008118a5445500689411940c1d840e840c003c25443e40c0b5580c040c4840484aa80040e010004045c04044148440d681104040e0f009020a41e1010880d410620325010914100804035182640007072081060880b4000e00307509a440300e05000d54010b000c0d6008980ca24002c03050040b01204040c800011241100c031500302542c180b240d001c00454465008000607644200c0901400240c42118078031400440c4d050345001a5204c40f601c030203400e4801365071001c10001564800384400e40c07280001c030b13045000c1c1014001070841a06a054803080c0b0701044d0b646640c0329003400c200400c0d03049805c50341580d0007101e0190a044864195200203030864000030314485e0000410400195650060b64015164a054034282a1540d014044441080352608100d170b45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 185610404 1250 185609154 185609191
    0x50106060f031a060927090c0306090c09190212010e0a0e0a060f27030305250e060c10060504180b1603061a1803010b010c0204020906040b03 62
    0xc001d20165003800c001d0074103010380c0c2042a481c090110010f800b50f80907580000e0342c040a40e03100c8603402c2c5131a18900600d0400c0c021310800219009048462081e184255084a41103180005402c2e110f0f001690082852003200024401140c1c4023800781c2c1d40b040c4200402641030f012a0020300101c10316005c1a0102d0b603d0001480c2240601801d14001035292003010744506202054104043d50002c502103030510460321030b1030081904004000341c080e0042c1010303100d8901100b2004100303019940038040f907190354088a0360000801409e040b403a01e19402e02399038034002c15080134403c00051089082840702440c1a04011074066081030180c0d43e56001d0159140510076140030f08401c030700b87c0c405010155195203031150081c2400c03440030428241400700510a41000016203001204581d940c1407800181800f908030076400e0140040952060046040520409116000503502c04332081065002d001c020b50051010036006a004c10011a901026038029030041c2110f1264903004007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 185611510 1106 185610404 185610407
    0x81005030c0108061807170604152106060f170a0203071701090210030506130b06190e060c16080c0114030c270a0626071b05010606 58
    0x440402c006000740e011800030300c111f461400c050b00f00e88408040006448942e10307007031015001802c0030001d0303440c2c10081074403507a00710300c1c4040c008110b0b484100c01d0f0b4000e0741208104002c0d0b001c0030421040515034464480c07400c90007626000c403a07540040e803111f0701803195080c3e4000da9868110002829070110fa00c40f42d00a015220071180440058041c003401c44000744504010822a007042c442400780680c42c45006203694a04100c0640d00301e00c0c0c40781b50190380c0401680909070921a142c040040c00070f0a4000010708100061001d1869480c20a4220b18920380007040701c800e8a0760000c01c0076000403480703610315480342d490925035082c80c014400c0802ca42055016402c0441d005040c4205005070107454043d41141c850900380d0b500e002019880f1580380e281c200300441891a403113810b0b040011071a00340725007030004805941600c0d64403015200d1303035500c3c0002c21019 = true := by decide +kernel

theorem cover : BRFrame.Cov 185431654 185611510 := by
  have h0 := BRFrame.cov_init 185431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 185431654 ≤ n) (h2 : n < 185611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
