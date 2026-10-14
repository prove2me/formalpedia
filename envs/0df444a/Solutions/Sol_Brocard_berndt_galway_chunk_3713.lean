-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3713
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:48.529355+00:00
-- url     : https://prove2.me/submissions/abce7d3a-1134-4ca1-beea-29a8daeabd5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 667625899 ≤ n < 667805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 667627149 1250 667625899 667625909
    0x9050412022d0c0406030b0402150301030201090608071b0305310605090d05011a0a081504030509010c050a05060906330604090e0a051b030a02101b08030709 69
    0x4062120300e1140d8a40c0e1207862140004a00300342c258800890100e070505640d15849a40306240050200410007038031555402603009031450b12005020034401c050a200038000680801c84a08040080c1da1103142060f9010469240940d080e1803641001c8141851400f0120b0202d54080340000b1011408445001406c08e40c0081141da0140060004152100f50003290104030000594840030f4a824440504085e07015000b08080034110511400744444035400500c00d082d141c0002a800e00001241d0180602090034a605601c0341c1d0340603034040c1d00c045940c2d414440e4100b8544041401484006016030049014001c1850011002c5051050060240d24080d000040700d054642c011214441000300380b6217654a0b5400d1640050001c0c040c03640a10100c5007421068622100c0100e5140402803050301200c22100f203000d0321800f8894800281c86d007550100b01d403100907140c07a005c0c0840c42c0c030550801c00e4032080c1a8450ba40003008003801510410000018131a815620aa001e07000300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 667628399 1250 667627149 667627153
    0x2070f1a21182a0f061e09040605040204060e014e060f090903170c0909010506030c0702040203060d02030d0f0e100c15240819050304050d1403040905041202 69
    0x1403d14102800d45900441025014500102d00380c1c0c1c903034941004456040b194101801480c800c5406468029440b003640907000754104500001e09040c0340c0203840c2507840584404240512001c0119140e80c400815031103440c0c421140c001c41082281035144507600942034030b0b1644901b03004103040540c0c490010074000351400608020a1041400c00010b5445810b0041079441c1d241c181281c03e956001c45c501d260038286030034400024404030040c6103421003035480c1d0001b680e90317208100030b0340411100604441c100b0011200149801d0380255400540100441740008140e0042440c01c0e0300f40300820081130450841401d115004a959001c0110842d500540c0b5004a200101403044490b0f008041d41c20102c091460104150402648402034810316aa01e00344000c030310308180b809116084a0340144c0391201c1e40e0740c1e9070180c02d00b161500030000394685403401c801d11000201d010070646003003180130070b400300a1501b440100002c0c0b0b0400004105410641440c062a19900c00340c030040d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 667629649 1250 667628399 667628443
    0x703020711150a0f091d01061205010806060607020102150c0c0714100c0f050609010c09080f03071b0e09011e0b090604050c0706050103050d02070f1a2118 68
    0x1140000103c4040890300d00d000000280c80b510180c511000d03942004140700e10314460f092204402c0360b0924101c511681e22500600e4400044608549080c05030302c0c19508450002401801c0c09001803122a106104540d2144400241c20380804003c0e21041ca040000085460500900b001044083c00d501c3d0f848004da0f1024000081c0340300d104c21480c2060108106118043c49036444444c180680c000c0d09450300c0d0b2809017030842c020407a01050b100401c012400c049118140083d032a00380c2a0084001c44c9004000d486504540b584648008d0404031081404a900e030f0200c52454003480c541c400106459031b400c5200d1403881e02e2118084075252400c10644100c0e95556407058010909440c009400c0e2034070b016401c0c0a214140d40541882c1c1420000410400c0c000340c2480b9600143c1d081d12505500d451031407442c15500d01c01c0d105121a1040410001d0b40003e00924106030b49143c41820607045000c0701070350300c2040760800c42c240150610003110305420301ca80440c140c11250075500e8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 667630899 1250 667629649 667629679
    0xe01050c060415111b1603080d0207060e0f0102090a05010512040f050c032a0f1f030912050901030f0203010803040e090f0f06070e2b06140703020711 66
    0xa80ca4008001808003206401d2102410b841ca51103a06034030085031200e507640200c41588402045e038031001100504c100324402007022000d50481b015280d1081826181c001c3d4540300e40040d4020000943d00c0541d21140105151010810a1124010140007503181d55a68040101c0d11160b50b101506001c81041080542010145541d9000390310004440310b80c072042c00c28618103d044600c2c0da0300b40c4130310b0f00c0740b0340c039101034820454040c41d940e41c03620302c201d8081051014100d00d80e0400750700400c00001c01c80c051107000d450041141c4441c5000109280e064440883c1400b81c1c0c4021000b186002800ba0f410b940e141c0541104250554402e5155514084d9036590f00e00c100c0c4202612049104007040e1000814084010411741d140304440d0840c403e01c02c8a91550401e843c030318003080c4003c030300031a60308201098100c0c50002da00c0020b007507100090f044080c1c1e0300d4824100d507a16940c2c42c0e10301c0c0420700c1c072003240c0c000c2e40155001601d82c01c951074241044502c08000c10702c2462000c01c0c1e000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 667632149 1250 667630899 667630903
    0xf0f0309062506060f0e01080a080714120f041509050a050f131401230603061203160606060f110c010c150c020c0f01050306010f050901020a0813060e01050c 69
    0x6120b400107804030320211803420321100002040400206003a0a0110008200c1a2500c054068030f07a01d06000302c01e84d0340d82c00c901d55281007001e0010101141131111002048405002220800304038041c2c0e0000161060409485e50050503a01d000101c08a014410f604803140301d003030054003e042001031070b414035000030420a203510981d40301d0f0308595070300c01f4141c071014140303503200e41c44040c10310003104204a8400e00f54801d000300142e02d48080c031a0040c01c0185880340741c000c1c9015160a04e941c03100c03014030084196029104802d84000c01c42c114400401d15003141d8264090783c0002011402c10303500070121100c0703290584c100548400e0046e07500c500402d0005841d40242041c0400b4000351038100400d90710b025401180f2803030035080c08485034001c20030500d0a038003181c4120f110000b107070041d28580400c3c3d61240c0001c0b0345604801c0014050401040782d4901401118084802a907448035558461043c85100f01c40d0383d02c0030007803c1d4025900980d01d08090078594101900181141c2e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 667633399 1250 667632149 667632157
    0x807030b040509300c01020d240306050a090b0709080712020901300501090204111c09150e0c09010902120c0702010c0206120618010b04120606050301050403020f0f030906 75
    0x85501c408111030010284030145090240d403a840d600a4a42130540e01740d41c000d42140c022811154103042c2a6844246040c461240c00d01c2151035030080c6a05545036103004280080c1174203c0c03d40d072000c0107408220056030b07141c45162955501494282084c504c0b80c10b0900540c45036010101c0340200c2d50060756180c1200d819030b070809415807101590350105650403103d0840d181800200088110244201900000c0c1c00300d0083d0340a120078128002070145c6c03403040d03c80ea4900789030052844103146aa540213407402d00d01986141c440000074203000f80484403400741214865224a6070042d180c1854000640100101c01d021400e10444141525503840e009000303444000c8000b842d441161300500b02000c0013170700600382d20b807940300c081c0190010b1002070351142d2044080200700210f520440e5007090590703030030088190806241c44000c440e052001e030b0303084400c03640700c5c0004215034500f440303001c0c410740c0a41e008160660380140c00604081070f580030300c0101e403c10001d4044a40b522070031a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 667634649 1250 667633399 667633423
    0xf020307080d0b0d050609070b1305040b0a031b080705060a0203070b0417040308030f09070320040f0e01140a0506010f0e0102030c1005070f09030f0602091801060807030b040509 78
    0x540e940070782c0403200c00918108000950000042c081881400000079180d841031500104540c3c0303850715220340740d00d00d0066060162040c44404d400744124100307904106051100500b4a007003058a030303a24040200e10300c05001c01d00481c0204100070307055003000003800030031098900b685400e00c8104001d440f481000005050101343d0004035041040f8141c4c080d924884005056488640703a18140b0f03055402038070f10f0540442602d011405480b4007140c51740c126076005441d817001c030950403060301480c0a80505a9405a0307100305800303500329030f40034540c0c040c9800350000601862420300b0306c0301030340060b01c0c2e040c2092034001000911b0760004440c6502a145e802d080e4a90152800101c0c075501c601c01c507804113400351031400d50801141e500a0303406620301d500d901c2228a507603203080340d44200512010b802528405251000b003141907000703255801000e004502021500c900c0907840324001c2c1c0c048000100814100096240d0611071071031060400c403000d00107401c10f00001c075502d43d04101a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 667635899 1250 667634649 667634663
    0x4050a0e0c0f0a0323060a27060f08070f031212020f0d0605010f140412051c08150f01050913061707090c05040e0a112505010605010f020307 62
    0x400c180c0140002901d041d446101480b5030341c0e108400d40280600b05643d02c8091101350181c504202040c44403034a80300b508080c0c4410401c524121181c030305109280e508c40c2c1c0301c40b09000444259240c1e8010b0a0240c088801121110761402e00a54540f40da0365110344104011082d0600004125017000e9100d07004a01c0d01d80f05a036000300d2680002d1041041c031003681400010400041c000a401ca001241c00c2600c50204c00c40001c0d0b07003503e55018100054094040400042c40305408080d064810103000303200702c03507c1000c10009105600c0314005588085840e0004205d845825100c2c1200109415242c298220500ca80040c081d80121641144078041658200c1d0718904168800030050519003208144041c181e111240c40d01071500452940a0400c420703819000e004000712000c85100e1741c00184250381e8054545d004249400b107003c11000204036441404048d402c00c5503200c180c08494464180e035900d020342c01c4034111f60000d030601c0081f540e02c541658010003038846054010003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 667637149 1250 667635899 667635901
    0xa14030720010e010c02061302040e0c040e070e0105060405090a0b0d0b01140f0306010608180106030813150c08090f040b060a030e15040c06111c0f0f0504050a0e 71
    0x11081da08900540034400300303440d0a02403111120015000103803144141c1c8000c201c050703c2d141d4102d0310707010f044508020241c0ba0308013000c01800c09038003105500c0030b14419500340007244e2001030180d0309001002d4515a00c41c21050101e840c58214240c01031004030740c060301e800e1800c008282c0c040340c004c2ca11206941c0e100300119003625030768804000264030510341c100c0c07503071903a004400010101c2d00d91801580070300d10342001d50600141c00d9041e01d00340c4d21508141e0351244200310b13455400e000142165501c4440000c0010140300c06402510980c50780b01d1102410039000084049018601c0c00070803d440e03451101081c0704408032078628038192520141509a40003003006002056445604100d001805e50420b40e4554400c181c1070110030b0988013140811820180000790907200070b0844c80302d0389030400405001d0b8151032482d000320425240c0c103120000600224884110703820010446504060080e280e210001d12447d85803400c14500305410240450101d0740c0c50300a410440114130 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 667638399 1250 667637149 667637161
    0x603131b05032a030a0606090f18060507051204110906090f060907090f0e071803030210050411030a030e09100f150c02190810020403030807030c090513090c09020a1403 74
    0x34103c0324120000d001c40c0e590254514004004144078401c0b0040c051900e4540380c107001d5940200344101040030081c2186003055140c0350010000a4200c009003c0200034100b0722a643e041801d2207140542480310359410f02409000d02c0c01c500900da507100e4071080040050302c0746030b241c9032500150169000d60041da20024140c03152041a080446045005900041c6252140c0c120354840e200580e81c003508041601d0500c01d41c4416404020003580140140b80350903c1d6603070100e648a4020303100c2d41d0700c032042c1001090500c20480800e0300055080014800e0500304440440c1d0084030b0007a00d14105850b015071030f15040c28034050920340e030100c0000d1400b01e03413040344901c3c0995001411028240d1070414003031082005481494040d004160038a04905201e10a88048075010340702c40d9610356400c03604900030000b001c107406c1806104600440d00b51240a41c404812404d00b2001075074100c0d50508900c034200b2a880301c2a4036004010f80b9100c140d0140440000c0070301d2400b25510307a141c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 667639649 1250 667638399 667638463
    0x12150917191b20040609020c0d112a0901060203190f17041403030f010f0e010b2505241f0303120204090216060c0905010e0d0f020603131b0503 63
    0x603c0260740035007842000328a45e840b6034010240d031040902251340c40d203400101514290b4484034000081d13003000036280303601201c2c20004c00d5090580d0070780001e00c80c3ea400006103000400e0304114016440880c0c0351054030940c0321071505084190502040b0b00e03441e0707074000304000e402441e04800c685100000c2010400000b001690000b9802d05407034680c0740275048021810f0091081d41d14078448801c0c001081040007040354181d440c00c1404514240404514000d00d0764581c03000485c406010454802080051249510000719082c9034902800000120306001c02d020304a20000403842a00e588101d0500301e031401142c0c0d0508140f84c2d040034502d80040217000c0c03a8040c030082c42c00000c88211050b00349611422151003a43c04000721503010300100d1301e00b02c0901486011500007401d1204500d0103d201079001403080c9408101241e1079400302e100c80d0401e4406006043d1600c5050040080f0803440754107058003504844111843c100c000790340c40b10804d4031400300035107080c0c002c0d0107002c02c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 667640899 1250 667639649 667639703
    0x10c0602130905070f0302040609090209010219030203180a150c020607060c020303010f0902090f190803040b090a060c031b0f0b04030c060c0912150917191b 69
    0x1001501c1c00c4699a90158000034040c103d032a240052485c004c00e0035041c0c041d200f138030183d40d82079940203107041c20a458000254404100716043d40b00725200b02080040c101d5100444c00d1095024617108c02c070107140318840440c504070044c442e0205010070b001020300341500c1d02081c4041d02e00502c81050342e0000c52818826400003030f1505050004010181d500000114100c4c0c03007035044021040c0c0d40303140100481c00b4040c122580555039016103072080c90203c01c0c62181d449400c003c00c0145030b680c0600f91a56125905c1b2803da824080382c41003c5103000801d04004100d00c0c109110b0350b104036034008000c04040300b0710034012408441003d09000d070610b480400c00d648450404124101410094040094941300312147c40c185501e9120380d47c0303e0f4415008482442d880070781d50305281da07100559804500f00070010140d9580e410701c0400c01041c0c0c08803408620440301640c5400d45034031461012000713131101e4240000740e4100c040903849051444100c5070400103480c91200f141801c0032202170 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 667642149 1250 667640899 667640917
    0x60f03150c071b030510020304050619020f040602070f05091b030c0418050a0c03180f1109191506140705100203070906090806070c03210f060801050a0b060306010c0602 74
    0x2e62401d0008107010f04440403080e40d02400c22120b810566250940c140d100860f001005034002e500442e440b00700420243c4882c1d1100a405814850200c1440100c3d8002e6070180300140c0c00040100310441c100880340c8054001134540c1c420a02e00b42d011152824074450b5016100b07000080000d11103c0c003882514017070092510007c02d01c0c1810080000a841c09488000c0c455181041d442c50340e078020b100341413501009003005a000c14458403a5040420780d05d1050740c8003003c9503050070742e5039075841c4100e2065501c2c41c503902144801100750411a80104502c51032040700140510905812031140103050285158261340e40381e0301d04d05242441d54603812280d01c07500101c14060400d8001c45244191800c6030759886415a40303400c0710365070702800c1d00c181c008903200400390000700780301d40015010310007000113090724505030700b0740d060807102103803901e002c032955074482031003030040c28004c03c0d41001035000b0a100036090800000d445200280c503007414000000c03450801c000c0c150701030b2040d0704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 667643399 1250 667642149 667642163
    0x910030b25080403021203070302040e250c020d120c1205030105060d0f0f05040b220b0703051008070e0406060501020307051b030709060e010302010f050a050301210204021b0105060f03150c07 84
    0x41020380c0050003139044ce008074076001102c400014076042c1c6c064404d030200800c1280c04451a040100103449140b490303001070f46c1010007039041c036002c11340503000310b510401c1030f5540014031215410410750003140380c5201d50806c00108010400ca035507101c145d802402c054000080d6400e0702e0681c100003840c881c0d0b102d18045051400708014808103c150074403840500c00d02140350000d20a04262131402d21900504151030140071032a1180319902095100f0000b00d241c284140d1116070040c075018541c1d000060041407042048100700950041d07000521080c0011410240569102612680000300049031080e0110502030607550400c04400149458641003040548680070840e10340f00074002a40891103000c0b030a030100c3d04c20300031961540c015948003030569003000c4481c2710a40603425015544040c5941901c0941e40f68401032409401c0b4410051400e02c55030001c03070039180000c00c200e215540310b00c1280840d880100d17426000c401c246081010307564030441003080c14050030303c01501c0b007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 667644649 1250 667643399 667643401
    0xd0905011406130605060d090503070507030506070905091302121e070801180b1b19050d1b09090e1e03031f0b09120c0910030b25080403021203 63
    0x100d00014000c5019000076030380c0409070f01d880c401100603201c1a03c181a0170940812107035403a10b400b03a01104c1e030144101c0c2a00d1514156484aa1030024950002c2d2840c0d044103092246882d00b001841c0d00030207003514400c100f85484141075009061560010303008080f04a40e5944c0c80300103110304108150040100b4405018008c2c1241c0c1d5041a03028154081d86450140380f5003c80442d2122206030f440b4038440b06070b94952080c0c07444000c0003109451800c7c0148010112042904041c0c8a14949540c0700c0703850302500e40030320060f00d895441000d00300c2100c038440f030310701d80d40000d090040d186d2400c0b01140e509a4401894606548121102081c0c05081041364100502200860142500038444950f0300408008900304032428841c050612100300840c24060801c81c07136945090300407070203a4556005050100d820420304490000c00c100501c207007801004112421160045034100c420440005403803078620000c80000a410280809030000904040c820402c00e0140011042d0032501c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 667645899 1250 667644649 667644671
    0x80d06030203072918120a0f0f110409121b0503160b10060906030b040216050706031404082506141b130306020904060905040503122a0d090501 63
    0x80035100d2442d802010b6100d0b14071500604d40b11301a1280f802c5000421041c100c4100104400c424883d5481c00b0a0302540580d103012425861400c0003450060300041d1824820380f80008034036800820842c4214030b008940340102d120748000076106821424038000880c061070b844c02460281480081c624480020125940c40200860584880c41407586c4032241e19200082ca05800391401030200268681c842000010b01c01e8000c11044c25020300300528000034403200c8100058102e0065603e1390003142c0c00c22070706600d88513034254401c5d00c3c0f503c0d60042c1015542c00e441c9224142c0c240c40e100001000102850042c5c0b101480f0b540d40c850000c00c11307560501c0d195101e0940487c0c043c44c070400503004141e22101402d045601000c2c143c3c8921a0150442e60340c20001d400c8813040542143c7e0b170310400700d4404282e00c82d070340c05640103000841d00c8035456a90900c0c1c450004100d85189000000203500184503400c804841068011886490381c00c06075200c07001302200500980f00758288031000341 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 667647149 1250 667645899 667645919
    0x3011116060606091401050f0c0d0e100e0f0d0303061805090d0f022d0102040308030103050c0402090a170a0b040b040302070f06120f1409070e06090f04080d0603020307 74
    0x18031184030300303400d11100341d45002c190303200300d468481c408900c1429140300b81250320400040a040c078109a0741414000184800c51030b15001c504030b140491103145506246140010002c0110704e0346160440b03401c150803012440c5070200006007406000340c82e0700c0c1410035000780c00150182080140e05030400658880700c0d03002d003400380c9280c5000c0c091065403045440c07282e4a264441c810301e400520300410707404d00700003011602c1500c140c040714021280d4201e0400c02c0c0020002540206000380e101d50460600d1400c0000381e0344c2c0140319510400c40c49100da00ea028141c0d044034000c25034401d1908411480d5030070812041c0c0d00030190b54407581000304000e0008840b9000380e0007030b0f0885090030384900380407801801c180994030100345e8940d142d06d044203c03a00042e695400b0303400f02088803c4820111014004140d45004140e041080284010110b80d0840759003d102203e4000082c10032942080350010050009400c52200140801c010507040d0041002143c1c06000c40d06c9899a8106400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 667648399 1250 667647149 667647187
    0x30a08070c0b0403021507050a0b090a14010603030f0c0303112b0c0813030504030b0a0209121504061109120609010e1b060307140c010c0e01170f06030111 68
    0x2220350070200c0010600407924020f450660368098042d2085452075200e22056411581d000c0f1458481c1480d2000060030100c4120f0107454901c004148642c0395284c14036050300c0006144600b0f030325144003080441d90201c444051a58242003c880f130300c02d241011000382088010124511030300050107002908400d0507059640c5100d11342c95150621405207109403216100700d80c0001d02000301003620500d420058034000c522034141140340903901c2d607500c0819401103030101351a96000c1a542c80c9428014000117480880301c0180180100f0b120100f2000da030301600280125907236001c1c0c1c050400b004401c0b910300310307801050074080076561816156900400c4036000b101d13500f44428458003880005070076018003100429901080001e13418041c0d40c1c3c1008110504105c0c9666543c0207980900300248014050303400003250b031008a44011f80b000c071034103188504001c503e421000b6038014408c030482c0c1044406c4c01d2444140c0369100041e000d040040618144600d0028821f4442c1d0b4000b410302d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 667649649 1250 667648399 667648403
    0x2a0703080f0403121a03011b02010e03030c071704054b090619140102330a060b04143307060204031205120114150c0c030a0807 56
    0x25012551065034400025030181d0b03006010814588818454141903041441c10007a0095285e4007291204006425540e114010440c03114001c00d000d003c043d428000d460880000300015491410640c60a50f0382c0e220b4580b0140c41050102136450841000c00300704d4005060040100c0001d01c0c0d07403503806041c400d1500c0c80c4a45400c21070a14101044500307887c80e50b44e4000c1c0240014001e680041c04050710004004580c440d0202c03004400200f6140d07000c1000d4443c08900496a000510000e842c0c500720040010882084141d210500745000c0d19400500c041c000314165241c6801c1d1101c005484107411104041d0408907020407020350085000c04160001c4940702182041051002003154501040001440ba21108035660f01314001c02002c481e0300c00e80c40145040d980b80c444a80040c950815400002e00010719000c00041080a4501600107610702210581e080b82c0043c1141d211306000910b11071000c80c01c1c4185042c18403011003140e50260940e2042e070303020300c1c0c842001da0100b041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 667650899 1250 667649649 667649657
    0x1b1801180e270d1110290d020a0521060711160e07180302040203160315050163080601091109030f03091002010b09040b2a0703 56
    0x1a078440004000d415510b01d500d00c601a220107000001c044820349420b0210400382d02c40c9100300356400e000c038420702c0701d0001c10782d542401240203c80100408141060864460304130003066401581ea00030000044613002c55000494900780c94050142d40c410024000d01d6016000410454603009010440381340210b0043d1144102c144a41401060303160003000704218211000800300e50140744040c003150700300b641549a5698a90002e0b00f42d0384100c507450395465051303203080d6842d43c140c01010b82e100d801581206026080000091180152548a00036084000c0c0347ca00500c01552080c03008400718289818200405006103842c41048074003a000750240c5940c40d2036072200a88410160b81011001d05056460410410054501c94506600703240d0100304c55503040e501001820152074014020395154186070041001b90000340000c8015641440101e03400c0f9603031810390703560082d8011035042036511003000610000c0e00700b1200301d5940305403c09c0b02e00c074041c0d045d0152940034480d80d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 667652149 1250 667650899 667650931
    0x40c05040b030f15060112090503070209070e0d0209131514131a0601030b030d0905041512061104120302060a0f02040b1803031c0203040b1b1801180e 66
    0x1c107150b40c030002003040c580c09801208480700700786889803a00f80c00020515000840a40c0107911004a4840c403a0407510f0340d1001940b141103040110700f6540c400440d00b400080440030320049681c805241c82c0092090410000091502000b90620b16032581c10080301612100d908030f10100900b440b0b240804400e841d400020014103000040302c28041c0d2043d856041003203541c110180c60b0b10080c0c403072410b240d210f48003507180c1d440c10000300b50b9181456480300c07500e034a04002d100031074508030024034449400701d00078030100001c0b2031951140b5901080000307007681481040052801a600f00401c1110284490030605500250301401000300d90401c2081c0c48188610300128810f5200d0300441620610a00c0200306008485040d00306000d0192440d00d02c2c3c55501c8400090105e00c900781959000c024042400b07035000b4160341c003040b1071410300c2d03405030a8180c1c83c03100d001d10004044c60026281d02400c0d50391284a510901058150060821944a000326a1640011282e0603014001c800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 667653399 1250 667652149 667652171
    0x604110603040816020a0504021909081b1c05070807031203020a0c030c0203010f1e0e010209090c0705010e0613050f010c0f14040509010609030b09061509130b040c0504 74
    0x5000c4a01495201103c0c40c40c1044803030a50030038490005080e030307102858000014140e00c031030004100c0306a81e81100820111101805080a204c90300204121350291250844180301d481c3c00f00200801140d46800349130003042d00e04403500070410b000384035005d5410700040d1000009640016280704900c01303c24030110210842c12802450405000500b0160516002c0307405040703104095400680089202e400c0004c05400ba220800e0a01c0c1c0c96640c016074110841c044c0788034044401910100a510300701003d8001a10140050130030107503000b0006600040000950000700075000b0401660018680081c9416a2840d014401d440314020150010030203041031050f800803c0352a2501d180b0005080b5084440441c0c00e80301031640801004040340070b0751070381da040340204019038807030800d03030b0952600340f0000b00050704222180c1c2c004010300500b1446017000e82c88045041d141c0325071960b01c00072416405d5501c1c801c00303000b000e80c2105200078000c01d22010000c0e0742c002e03141448021111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 667654649 1250 667653399 667653409
    0x9060e0609060d050f070c020d020f120a2102070b0912190606030204050f060d0b180111030702150903071b03020d032307030806040c030605090718090c120e120c060411 74
    0x2001f0003980541850f28003001450100074890b070b6641e028010800504080203224a0300c032800c00709403003800306041170040c81c060703054202020b503031300344041c1100c9458140800c0b032500a404c00144908519214034900c0c041c10883e407281c0d40300c0400d641403c0c7d5407900f080710040c91036000c140d000314184000a4a5081da0480d8180580c0018201c154814003544400808200140645881520444100c45170034000d0040200751030482c07800b56520b003400c6002a01c0d21510017080c0c04481645010014120008016071342e0f60745d0003c3c101444010520901d6000d10210b0300000d50041c03180c0804414540d01a1000e880014400c1a845002414050143c01805841d1008001801480002d415070501d03402c08035154040d420081103d80c0c40e4000560340400803640c000004120620344035030641030308584002424046030401045011031002860340b21220541034800f40c85060068500c80c0400c10280c641a10900090302c0f6507061410944030102510191100e541540701c0c40c45031300d84 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 667655899 1250 667654649 667654667
    0x607210507020603040209040311070e01050306100f060f0302190f200c010e13110a0233040528020306010510170c121504050702070609060e0609060d050f07 69
    0x140f24034110b5640e5401c1024441e0001c104070104604011284082c117410440d2030042d05010325034445960501050502d40350380105005500f0030708440c00c0242005a8820b0400e0700c0140c1b80542c418941e41030309802038424900c803903001d5211069401d0310944e01140e484900325150f942c40e4800400c044a08100f074880e00304013002608850341d021225809419081c803001409480101e118201000d0881190000b000980301c080d80024814496039042c0010500518086085018031030015010100070348210290a02010031801040a0010802501e0846001d986090704904032074a80020b050950540884c040d21460707001180c4e51174444445505000603035034801849080a0300c07440340306005409620861001c00039014141d030320403c401e02c61000500c2c410460544035040c0700803190028002021508080070501015070311404480448007607142a09115031640002520307132013403542c0154030080009040d0081a602d42105200c4d4462010100d550f9407088070076190004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 667657149 1250 667655899 667655903
    0xd110c0414070c030e040c0504061119140307020301060b09042003060f010908060109090c06020a0f110411030a0c0e0d0816080904150302040501080102120a05090c0607210507 77
    0x2400c0001112540b0805a03240031602a18101704040f04080100c1c00f110302c1c10752a440010700024050100340e4100310340710600c0314000300a00502d1046180e0000101f104803004141d0303207418a895061450400c1960000f5400034001c1020903903840000201e0340c4601c2005020302e040000e0401107024480f00c580d21a0a0390070207901c1c0d0303030701d0300c08100d400e000c040205818450a00408505100204081800b130a140c090006220906044c07149000442e58001e00841d4061207444000a01c5440106025984402255002852807001a02810704110361180201c40441045400b030080d4119034000303200760f118907407010f40300d030b090008440565034080c2c10008200101d00001110350380e40320030340740104002d0b07013401e0181c0001001e8503001000601100720364041403040d0310307051082c203004080ca04000c52422503c00046031030018000c1403070b10b0499890000414052060020807c401d034024070440e6111054a403003100710074030210462440704500308008610380204219100c0d2a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 667658399 1250 667657149 667657181
    0x3010b090402090a060b0c06192309010e010c080f060a0324060b0c030c010f2d020708030705030a11070305121b0a030b09061509130e0d110c04 63
    0x80e4642d000c0c0a040c0d04090401a003103035075107000203500000c40000e402c0015001c03000e4101400e10042d5884405003040003400c0f6140b810007801c031f448074002112150820200c04003a1260b4070102010300400c803103083e0708035650030700000c2c9007055800000140b1400c5183d04401d900d0302c856081c04486401d501004001000480003002c0300103074180e41241c3d2008080700812000e40350811000076400103070340b150307666001081c07058400d1001e000f4594941581941000854040005502120f0781000c04448480707003a040f0914420b00c036011035100c2500680318956908007060002c02c1c0354022180c1000082c81c002c400c006980245084500d0b00750150b0300c0d541082c0f10100f113120b8401d80036060221440c4c01c814040701000300b0038082c01e411101900e0000f0001c1c3c1030420302c502c40300000c101c580300c2e0340c071107194080390f003a4242a01c9100c0c1d4181d642e064011146d001200040c08021358540080c07150709605218140d00000c0740209030089004d0b5503524917044184000d54002c2e5285400380 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 667659649 1250 667658399 667658401
    0xe070224101a0405030d080901050a05250e0a0b09120f0c011d0d0501020c07060507020a0e130f120e100c0b07050403060213240203030705300105010e03010b09 70
    0x2ea2074149001c912954038603030074035165a07240001e28002d104c00d20480440c04200400c03078910001c0c8035161b4405401d0105011a00e0004a0070011145200107440303074024410600c0201ca01c91590b91600c0c40000d01035000043e201c00007401e00382c100c0141684559540c48612440c0040401c502c2500c01300400200308441c6042d00540b0124040413080300d4500325106580c4139996180346a194090040d000141e032901d1108800b41009402d41101c010b109003080584016210040000c04903901082c2c485100d841c0c445450350741c402c002c0d0020b8801400c0080210601250184815a04680c1d40358a00004100c000703000754071502c07111000128000745041008600c803c080e55070b1041c2e10f898818079060305c0b5562401280c001c10070b00d850010b0075210500256a0706e025001100715812804503015070001c10083d0360384001022001041000b043d541c04c0744482c860241c0080f50804420004d450b82c034403a140ca03a940c2446a580007416481c214802d0341018440e040d070101000c1c100130b840f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 667660899 1250 667659649 667659659
    0x619030809090402060c061323150c12070f02100501050108040b060f0d0b01050a1406030408090f040f09150b2b061401150203031509040c0e07022410 66
    0x20068000f0010b0f44c01c00000c00c5011803503401800201e2154124480c0f02100103030500b4529003110440c425100c000019444c01e20514000080c406454030782c210100309180c1d111811a1507a0141042c113070b00308200d030000c1c00034480d00702001c002c000b000c0343c0c2204ca09101d17141c800d406444003840b600b03000c81e00d034001240100d16041061a80444090300e40c0b214807264001282e504000e40c10213480070805040107201501c0c050080d00010140c8500040c04000c1c10310000e805c91202800082080390001141c1c4043d0b01e40b90354140510000a100700090743d001c0342010040c0a2f990b504840c07900041e00c1a48003000c191062000502e4083c010340000085c01c2030301c1c98111640c4003440720340281c24192200042d40c0e07015001d5602181180050103500d40944e110340803c043c404074055400500030440385d1800fa0f4600c07052503401b1103514065455504002c0b45a10140d04807140300e4000408020300e00f500001e61060301403076000d01d946140340c18070f25081d10711003d072500d01c442c080041c0c0c03c000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 667662149 1250 667660899 667660909
    0x11030106030c0810030f03180f1802120c0c010b0d0b0a0e0703050c0f220209030d020c0102060f130c080304050a090605102708060a05070221130810050619030809 71
    0x81072180c10910301400c8000000d01c03891420368080f0100903417080c400d00c0310000c0450040e104070702b042da06505040d01a50030014001b0f004180501e03174000402d0000071140301350406400030340301600c0d0404840e014109402c00c00300c2181c04101d00c03070030003550001107800080d5a204582c1c1150150a00b21402020402507a82220b6143d9218000b48d10b180e1528410103582c650301d00c42c0c40801a501d0040c18203050402885640c41d00654010900c4144c80307980110710745070f2155649403201c01c0740c0c0e18a4003034021640e48440141c0614860580401c5a00e0004020300690344100c0c1d19803070711581c8500c2c0000b81c41c094040c0540203a0110403480d00c070b80c05044071203444081800c1346a0904035500b10000c0d442c83c554400c04250784400144400600244111a080011480581a45510140742c68003205825010541d0394a001030031103d220307134050b10100600030700d00640303222419004003803000c1c110640d40144a801c02540201e4001d0403004043d040b20750040119080c81440b1040103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 667663399 1250 667662149 667662173
    0x30d03020a05120c0a0201231b040314010905010513051b060702030d0f032a0e01050f07062304030f0f3608031804050a0f11030106030c081003 63
    0x10061060500003c406060300000581c460900c140a50b07807505e00c0c801c0024290b500412a29a40907002c3d680550b0412a607808568401e01d07808640808207111800a00c40d441194405840c0780408000c004c00c044c4190080305215015100911017030310340c1d5040024280c5800d1b0000d000303610405c260000300c401060700f106c80f400010481c038101540c80c0c000c00e0410b449800d03528001040d80740088031035509480f601900b43c0390300001444080000e41d03070075000280351503620305001c0f02612840460303109000302d4010b0680401241d445094518142d0701500d5414686081010038050352001c90f402c1c808218880c030b0301540d45113650551058156604107403203c0c1c24042002d0385a1403104a0a1018400015452200360034140202c42c1e010401001880c0c0108040f904104000c0d1709241c0500311844024008640024040d200c500c260300091024400f04199241400407015002c0e4170000510b04860f071903101401183c40c141e0b4211101c6c601124003031406d208081c0280041900c03c0144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 667664649 1250 667663399 667663417
    0x20c06090d021c1a0106030b0a0b0319180203070b0f0912030f04061e0905130b061c091a010509010b070822140109050625080a0206060f0f030d0302 65
    0x599200381c0c0e035000b0408600c403a013640d070071050144402c0d0904a106860380100102d1804010300c580704000030b03d00314083d11540f00803c50200c08111504082c0e02c950460203112001003090b2402222040c03000101c425090f807003801007000c0040c0ac404003200700d90400b000f240b00c40c0d06d45200001003104152000c1170051302444144022140e4a408000410103801c01d03844003110254084010441004400032800130491208000c20407034807000244421070b42c0700b0901040999180700800c03e640283d40296032000c0403980141d5652040303a00c001c002038080c0c40a04840d460780f41e08100c43c3c580a12078150405030314401080401d0406018214882c42048140d01d00301c8001456246050140410b0300d819200c14810060004034407070b42d0458541c00e0928407045460000020300e180225000100f924002d41c444c2003c44e04480ea14031100c540c4510002c1d01d41c0d42c4208020b545803c00c5034058040d00b9503080307020351860002c003a0094080020008e1155100380281140690030400c0302c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 667665899 1250 667664649 667664659
    0xf091a10050f070809041d0a03030b0d061802030c01080405061b1c051909080306060a020312010f2111100504050a0311040c0e01020601060309030e0901030605090d020c06090d02 78
    0x210385081c1c0002c03401003800038014882651034020040c2004200c4444a40108449180d040800c540850228140300a290903040000380e0f81c0c56407020602c03100c502600180300030701d401c5e440c3d8a00700f024520301d054240241c0803120740c5026200199680d030b03001d40300980300307901c100300081340203540300d29040d020b08964100d1030070502141c1100390305200e02004004101d80f9102041940d0b10150075140e1030310000d54051000e003001d900c600342540700141c0010b000340d1000440300f12590080080394441c01d0b003000c0c0b0424940e03440629102c0344019000384101c5488840b03201c207018244484003c401e0350454081c1079082407902c10013216035160f903a140180b16042c00000b030103075075158605005501444d0070070002c001d00c0003007104031210341004800707111540e003100b20503980c00141d1906484d101d080010300501c480c1019aa0242c0c01001c0540c0060303581d0001c010805141c0085000349890000c41e0310b1002c0000007a40c503040b0407004d454015406215802c1645092050a44582e0010704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 667667149 1250 667665899 667665907
    0x10030b1003170711061306030e0a080c150915010905181e12030405070506070f060f0204080c0420070606050402070302010203040b100e0f04150608070f091a1005 71
    0x2036a10820040c8007031100c002030307002c40c4900501140c0c0019030424202114017a141c0003d483c00d1003c02451030103400201a6a4080315000442c1000020080c98006040136160725010302116542c2d501c0030311003c00c4482020101ea854140040c8100b46105524403c1c4291b0b07013443c007144c004002c0140314440901d11b5000903581b0703281c14844600108000740d541c00c803148030031300c0310703450a03a0403580080380d9002041000302140c0081003480a4440842d907c95803640f640c200403501130102c50001d04000c1c039062a440e000142ca41c024401c4442c09002c0e00c6060040c0d000b0041240c005c03008007003a55241b2480340f018101e0400080280910078840040e40c984c6070408242283c0040c075086015030740c00011700040c028540d80b51540b080c10010720664140c20900c008506881c00742c03140702c10600c08008207040140c00207401c0c88003040c0c04405c12034180d46400c0c00d981e030029882610103c4004900103e0701c5034140c09910040030203038034400000321340d11092005603a515601401008010303c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 667668399 1250 667667149 667667153
    0xc060c0302070212010509121201050d050f0106080d0e030d091503020d05040b0604140c2a0f0718110304020607050a0c0909060f060311190b04180b0910030b1003 71
    0x4074280c1403c1c0f240c440009964508401032134170304a03004070800307a141300074042e271076055011002e13442c10346e41c007690300c080c00c1001454114034001510360081415400d104c004100b1031800114850402c6180d55900b050045000a0545612220f031240f0001514040244008042c00e5100000c18942d850300604c1c1c00580d40ca494200c03601510200d0b04a046842442080c4c40c2a0080c11048000000c0242c0c081c00d08110281807880740024102c1c0c082200310fa01c4150991a00c8494484940070b0b080e21650085000c4241e00d03100c05010b20b60b00d02c0500341d00000d003540b071449520714031100304045926649a88d001c10100f6000040100c841d0700c600b8501d0703400201c000c82e0040c0186100080172071440603514040d000c0d91521403580c80100c0c9801e40400101d111201203030100c0c0425503500044001d802d040fa48400da440e045445140c0d800140040c1c2c60b2580000c1159502d050007040202914080407c040a4403c0c0c03882d0305242c031110301c18008a0760080d1503e4000010388000d0852070b07070b65 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 667669649 1250 667668399 667668409
    0x80408220509011e060305072c041b0905010c02030708011d0c0102011e020d1b1710030209010e07020f010f1d0a0b0c0a0c150504120c030c060c03020702 67
    0x544014140c0e1061001081182425000b103400b40c44c2c0700005040803610141240c800348541c0c46118105520740c400700360001c0c01041d4100c0300c2101c42441801c084e0751a030f425059110a80e84080c060380c030b41f82d20744c1c071038440c0a0002550f0244a41c2c41c19445890440115030ad51903820301a42d15000705600011000c00920440303650060700c0c0c9a4080d90b5007486000703424580300010203070559040c01c1c1404660700c81107400c4801d40d0454075006844015110750700c401006d04070114004901c500a901900a0b00000f00c110f83c07202c010b000725540d68500381003103512581444000e4004900100611840c510814411361018052044501c1d403030b400381c1c595081d140004034801e00c55075034241e45049071105102e8480403512400080200410f90750700c3e0729541c500182154241c103004034810328541e21451854039020780003000301040300500b00d80c4038018002558116140707880b105019001e14000d286034801203800d41c8421200318141d03120030000e442c001100c0300c10164200645401a510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 667670899 1250 667669649 667669687
    0x14120109050403080a0207110d1509030527031009330e030a02060a1d160905180a0605130f0b0709080a020f040e030f0f03160503040b07080408 63
    0x201400129540c02c25003006030103480041c01440c0b407540100500004541c0002e180c0030000c4064a0b0348500d040e807400c0040091000d04c5001c21400e082510820a066008014203d07181030b1b1040e509890940900c0451400c031071032802034054000641a681e0441282d000c900418090203c40e43d158a00b540e0350081c603000601c11350314519444644a4450740907108005040d016600158605040d445010355580c600802100005403100400174040c18407800340003018146804232001040b08031854190100d2502032403941c10b182000240d2942481c1541c010241c1c405c00180420326a1615604003500c002042d22000000070110240011160074000064501460034003143d410508402442d04040303a000200e40d50007143c0c441c0140c0d40c0d0000d00440d0b8801264002001108842400c1c01d600030700d95525110400418080700307903102c031001144540c1d154a486104852080001d03110f60006940103005a40b5500c0014401401080d07600d4101d40288901400d201c441c0a6074048005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 667672149 1250 667670899 667670909
    0xe07031502360621071e0302030115020303040305070f1b03050f010e1b1e09090d0207050306040b060907020a080c07051c05030703050d0b03030f07151b141201 70
    0x2109445040250008080c01e10705010850f011403510301c501d1060b07604084c43d030764813444a04400b000f0520075801120103044c000c40750100c10413400e0380c140024009402c01d1280301d0301c144e4481100020a403010081b40c1c8155455210182015070b152540e0040004610040320520100100744800e5160340c0b42c1900214480c01c01404840c400302c86d0182503070b00f07035018002c055000d0241d0840f4074003140c020203042c3d003040d01c000c010805400c0c000c0b00180082e0041d180c00058480a00c40e02c140c02140001c0c07a00c1554003180e11030380c0d69000303259071600100e174003400603041140441c07079901d810700d00b094104c4580e10485141046a40750340c40c45600814926510340d020f950108450301b09000405815030744202480000d80058440c962a44140030009003049030004a07192a54403580c0a1004228041c0840340c803011a4459441c1c141d0001d00151105180040c40703101d95003150141081c0554402e41034851071510103010340d4414049180c4241c020024081410802142604ca80c000c01c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 667673399 1250 667672149 667672207
    0x71e0506030a0c0e0f0916030b090106090305070812031306020723011409030306090603210406110d0207050f131a1c0804300303060602100e07031502 66
    0x20420000240c02c904d000305469010300c4001100c3d681030358606101947c0b01e20340c10f20b00d0400b221980380c118010b11407800140d902c03420344000400d5403540032860784240ca1040c403c0b503501c89c0e1106d05c0a40c0d01c120b10f400c00600d42d102040040d007441101d4540340307140c510880000d828594a90369481c41c0d5030042c01c0859200803501b038000825074090107840d26611005004a0306400e165004c581c40e0b01c001001e8071f001d4a8024003060003920108411070010b4000030090100c1d11a11224489681c0180300b0040014042003000e6400840408c00030160000c58005040c254030300001d01000c00f82000d440d03a4803045515860b4803810103405058100c1250041c810450b890240c00c04c08454290048048054800001000001c44080450b801e80c3d641003d144d046880c03400d0760a0140d50716108012001d00086034060400d80c15410a40c166541d503000e451406000c2c009507411039828605900d02503012103c1040801d60303031341c840d80341d882c0580d0025107003d00c00340104803509020909140300c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 667674649 1250 667673399 667673411
    0x1020313060c0f05070807050c090705031e0c1204050c04020a030204030b01060e0d080d200a0908030a0215090304080f1c180501030b12240105060a02071e0506030a 72
    0x2400380b09141010416007040941c522994400406030300074280001d090020002d0040f0174020704201034440024010f20000c0d0300e10f4100c10040840d0415900c1d07031407003071520700c02825043d11541c1c200e1040c40540003980c03d040e4668044500000301520944441c021500090f986884c1e0f40001c1c20085416100580c2c4d940c51450840b1340004164800410000f110354070385925034503210380140c00e44c0c0091180b52211106200340004101d60f042c0c0204068941c0980c906c8035070550042d000e0344c985920b03400900c81d81c2e1100181c9178417600303242200503040800e032a40d4103100c0e841115040440042104d08050f101c12901d82341c418603080c03501c0c81c3d03808800c404101c500d00d01d41d10108100c1a11b0820b04c00c400064001500c401280a55414952201c00e0b00c1b103962140b58002c9004001c201c201c604440c01c1c403400e01028604c180f92820904030350400401c03070f8280702044412040d413a078020300e2030b1440d1041402e985220300040710100b0b070bd2030300009881c2e65580b002d9405040d50741c00008031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 667675899 1250 667674649 667674653
    0xe131d0c09010f1505070503040503060f0115080609071206031202010501080706144603060b0c15060a030b0708061c03020d14040905040506090f0f0a0201140c01020313 74
    0x2041d805a0207040d4000c0381d50018080b1851107008010500c0d0141031081c0c03103160314039045055010716000250584100342c10420701c050314100050403203030400c1a4907074240c04410b0403142400101c031800e400018800204010714400c007110703421040305810010f0001e4603944e4180e49a1029541c01d80140e455500501c0b00c81010f000480060000c0d0901640e0b000360345e105c0c9440c40c052180d83d11036400784000b00c441e80805944034200301024000d04d60404074a40320a00465004090242000924182c0089458986001101c2c10903000000400100c00c0501d010ba180f108001e02a03604256210000070010701c040d040c240c081d901036180c030f4015107486014000c80035142c0f950000191402c0b00c2e000c02203a00412509000d4070340d4645a40070010908904110744900c0d8810f54580c1d01d0041008140040415064000d940340c000761003600d0300c1d80400030380e1031049080e0861190441c0106000560043c01c482c0c2107a200c4041c5030381000000b4800300c0c00c98008494002d0070381084522002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 667677149 1250 667675899 667675909
    0xb1b010f050f091b0103020f0c1c1416080903031e09091e190e0714030120030112050a06050411090601090f090e0102040b21090d0e131d0c 61
    0x29000d0002e000030005880130030046a203070500c2000f46414198006103030303950110031904036842c9180302802c40d030303101c101c5008220306100c04884c4140040d1841c070b032654290100c1170868075030b1070046070b81c1c0c20642107079110055980e0110541952503c02000500c1007102180b0301c11440c98501041951100b444000f80504148001c219842603e0204103c01001c10000000e50304542c58940c100c2e02403c1101900c401450f40000480c0c41d845084400600501c0000d0316180d810700950090040f00c2e983c110b81c52011b036052249120401041c40140103102610000c0c1c043d00c0c3c0581d003103810002c2d55454010464806440c1a42c066080c004030340c4481c02c0020a01d40c203d502845d04030403180c0743c01e10388001039039580104038116480c2d003202c14400201750169009807001e0b214030341d1784410041a94135211589100c4110900e10840020300340703003001c186003007000b40d16210840c103407541c0c03010865109420701441c2c0a0581d0b0349010f05044038082500ca46c45c50441008000c03112040c02000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 667678399 1250 667677149 667677151
    0x60d090c0303050c070f15030b030f1f110301031110093b0c03060f060702180609070e0f010c030c1b0501120b210a050d030f0608010905070b1b010f050f 67
    0x4103c0c9944c1610421241d9044584803c1c0d51f80546400601d401d142800a4202060392101c0442d5110301c4507111914207649000c2d00345280300a10810145121510b00d00550009100c080c1000340d003601400c2c02400c141031108801d103102e1400d400ba0701e403540441100c011403070001440c861b071030f0310041c0c403541e44018060346040501c14050080d03180c541c000c110684401000309005d0209604600403984500701541c90403507009020040f802c0400b01441c56484003119020712030103100f0089426a030003140b082d6691f13000074140c0080b4240b40c10042d41c000c0c22041c0205e0422403640044408202c2c8400c0c80f900043c000c2c0c41c0c81445038035000c00146403103124803070000c0712403030890200d410380e98900c04002320343c50071202c1651010b1700c03a03089410200701000113807030790081c4603000ca0410f07410f41c000e9080c070040d400100011611118003a0890302202802056540065018402c615010300605540c400300d003103000344c4081d81c00a0754203660b064030081002c142c480c1c0a1041001200000c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 667679649 1250 667678399 667678409
    0x102010207111207170604110901031515120302010f0b120318030f0f071d091e0f03070609060b030a0c03110a030b070f090e0c0405060d090c0303050c07 67
    0x254100041901c50395040d0076a4003515214040c0c0940004000d0030500210009281e0010500d0f4000f1030384601e40e071150002c44041725081e00040e923410540c600005243e06a03500072008810054512185a0007441c030350021160103407124000064402007000964049403080d400444c0740040c8200301c070240c03481c0c045040d1081303a080c510503407080b00c00000c0d60481c42c07000881034020242603011908040201861941d24007504241c6140300f580014980c044501c0405981c00600c038400300320480c0041910200c6040d040f003001502d450380308441199070070380b0318010f84000e02c186101315441c551280da82260754580702d0203142c042c0002442a2071a00e0760680184c00c030f440e02961500403d100b00e01000700441142e94080703c090700c90400507c0590381c006010130032030605000c05400d0440e80e4010380d002030003040c80030802c91020801c0a0103050b0ba64042820903040004100d071941141d10800e240340e9842e1048004075641c00a80c40c001c5000f600d403107070307241c000c0c0820381c1c185101a001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 667680899 1250 667679649 667679651
    0x19030321021c020936070e060909070e0909011a030312130609120314160f11011517120c06010e09030912010b011106060a0603092109030b06010201 65
    0x21a0711601444a0b400030a010b540d5005941c2e500302c00004281c0454000c1c81c44100506038611001152035401008600c401140e01503200e03690f550007214410b140c0011a904620203000304c0030b0074201100d403d504001075040ca0114010b102012aa01100488030400140c1d1a800441e02200002c3d5030340f2800070060300031358505500d8882202d1140c402812a08440209455003010720485500c43c0196560156481b103140440f0b040c010007403c80704510035449001503022848144e42500b550701595080d8843c044044070940055840045903070800901355280c0003c54504410080c0442c013402c103044401310110316000313031a443d108154840d80c922038002c01c44420f01010005440c0d0444001c20704011442c1d592103400d50440c000c0c40071681e00701842d003840040c200e0381900040c0c406042a6035001070707500943c0783d2642d100340648602d80c215228240c24403140c4c0c0300760451072000d4050f910a180c681002181d2001045813034800c000018651a414001c10440f003603119000082440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 667682149 1250 667680899 667680907
    0xc010e01081608070c0c15030f2306030c0a030b15060408100c0c02090f150301020f0301091112070509031b1f14041e15020307030c021903032102 64
    0x2400b4100e40b0b56250000d10140000280300305109125040341036500101c0200701c2075440d0410b03804940c12001c0c0e000401d042c0168208a08507911840442841020710071030702c00007140e514810500041c3c0841d40600414007011030715110032815000641c40344202030307154600a0102c4a0540601150b00c0c401c00042004014038500083c2d51200d10618803000661a0554801a1850000c0c910001d404c040341e0020004c0b441309441440e441104d801d1400720f00c0400c1102054200c1c820084400c3d0780f494140018010018a903000c1940d10612460180c03902d590420b03a0000341008445000c00611b00103040045401c06008040040302500100700404050100203121856820705c6200c15013410001d03502e11170302c205120f294a003848a13105a172a921a40540001000f42c200034918246150340050f0000c0e0201a10b07000c1c81d0f05501031410101d55a9003196040c56078042a644440f400700035501c04940e543d102c0b40107520070b88420380c1c16503001d400f56440d40d404403101450300344140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 667683399 1250 667682149 667682161
    0x605070c0209041119060e0f060a050f03060a030b0103141005511806240705030a050c010c02070501080127020f09031006120b04030c0506090c010e0108 67
    0x72986401950109031130080f030705128081803103d1003130b134541000900500c00000713043e9000f00540c54400002d585c90702d0300c818104103114051140c1700319040020b100300722424003540c010700a960060300c003c0640503026682d4403100018842038009941c0100c80000c100d078104030070000d104804030f094806120601e001c4045c0604031350030030303400e001d02c048031501c80700c46071074482c080359000c0c03480c101c0303100c8089215140d5412100d40224850050318648486c210026070400102d10541c40104003c07549202c0115044507000004a41241d03c0d2040c825580007070b5090000d003051840a9903000c0c0c0301c064012815003921000d140c55005c1d0340141c0070501c0266440100107055442c60105c00c9804024003d8035403181104400b0316140c07602c040703184c40404650030004c043c1d17442c00310200c1e07080610b40c0706007508072590742c401c1c444c05540a410741e000207083d011307031242c2c024040e042a0342c550444d40c5401d42860740440d08021590030031081001d1644e042114800c5034202803030842a1441c1034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 667684649 1250 667683399 667683409
    0x5070f060e030d0507020d020a03050c011103070b01060c02131a01080c07030e01200109051c0f120c050f030708010e090c0609090405070f030605070306210b04030207050a080a0605070c02 82
    0x403034070f203000c100300001c0075025500c8407112411141da000c0e0aa0017619580e0801e03030303110714801d0501400a00e111101c814200300c0081900c0b1299000f000c181900e07440d1010a4503000e040040890700001700e0b01c40d6a00d504214800c100e4403044842000d0400c05020000500824008060b0304500300c041c404a0042640012206441c4c00b0a08003036044030201070301440d1400c3c2e170780045030982d03091035496410404081855805c03c26528000590000d10b11002c0e9110420040d4010010f101d00441d55408134280c2c00164051001c0d0907c9454550061103a0140f07a00880c5c1400110b070500004008154414a210381d000e21707120041c1080c1080304000800c0341c40f964661911031288a0040b5044c05000d0294000901640140303844039175492030003002500c4102d80315000300349400400680a003000c403840c0c070f12100d001035640030100542d481104207580a04140d0451003a4000410241c0300c443c95140503000c0a001840001d0071490b295042d5072006100c601000005510100143c0750 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 667685899 1250 667684649 667684663
    0x70306081b06040503030423010306030b0c07171b07060f020307240204121e0b040311010608070801060305060109020702010c23010207151401081b0a1205070f060e03 73
    0x507007030001c24428100400900d41d4011501300942c1400002400100140240b03c000c515440380b4483c0c0341c6010640c00194110381395484042c0850960340000781072034075001e00034503180f80306204205488495050382c1c1d03030300d800c80348055071110b11302503844882d03050400094004007804c0c6022425070302840b00094403070141c1c01008000307100d0030300c40f840381c000c01140c210a16056190304546950b60755500001104510720305881c2400310110400c50300c0702840745141c4440d04083c1001d0710b42c681d84e0703048a484424a946507515540c42801040c4c800e8240044002000c0c42000403031070718214209141040010f078010054644104903900060340c100082003051500700d4114080c02640003500b85c40c13050019103003015540700007520340401420601250415034411010800d40300600f480502c07030003081c002c1540f0781d809140e1440040ba221881da0401d1000649420300099481804030f0021034076100c05c43d05500300401c1400940b4030181c032000100300381c2c80c2c855490820900443d481e001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 667687149 1250 667685899 667685923
    0x60a09080a050f070b0a062103020c01051c0519111612050729091902130b0a0b36010813020607060c030501060e09180f03030c0d0507030608 62
    0xb001c5202d604010701d8105582141d5004014041d0038648400d80f88000d151600900c40c4000c0d400815050000c00003c002221a07810f40003007410200348070041d01c050300841301d2241e0440340318406040da88a18040c2a0140c0d03504840140e036407004200c524142e0700100c018123101300007807050424030300c5808055603079140c0100c00500800f60b0780801311001d100380030014003c0c52101084915075000c40c480c1e110f108144816200060b200d50300890b031900c01d01601c0c8903040e200070032080e01501e4801411401d803c0303100c1c0c00080025401c000b02d400e21111354069541c654002c10740c00302c3d42c01d401d4440703240401c404450002002022243c40760044407070a400e030420400b2800101740803020044804c00e19001407a4a499051500d8810060a0202031010000e81400c0000410317034010b444103806031100401d040050ba640c2034800748050003a0041d00c2c03142c414611f40b180110002c0c4011801358240312222030f515541106244c00342c82e0060b00300006c00d03182c00e50400040c0b10200e40142402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 667688399 1250 667687149 667687157
    0x41802060a03020408061602210a0e060c07140a080a05030d050415020403061e0b15130506160605070203070b010603020d240f0e0103021503041502041403060a09080a 73
    0x110510700440c020b00403500440e450b407003050107000c0900074445c0b5040140d40c095080f15031106a0358040b10580d08050701c01e09d46600300707000c615a4030f030194001c00c444d1407028280318240780985501501c5c03c0c81c194840c0c0100030300d13400211200d042c0001024044c0401d40d006004010301e039502c0d159a0702c614902c1011003691017011a00300701d6000790803041100d040d1419906c0e01d0301c2e81031030002010100d03003078807160011500c0c401c09103000b8016041114401849000810010300c101070380b50340241c0d0034000b8840849c0012416544a0014002e80009070504210b01c44291800070106c860180c03c010965005102c1c850000b142c03055081d05446803880c01580b1030a0001c4034102400e480f507500490551922548101d000401843c0c3c400c481c50406114120341da16404450100806c3c00045d41103214045003c01e580c101400558005128800e8a0003c464a01c12213041f80c12603084003141d85034074450032080c3c3c681007042e650007580705d0b030080080d51010b5550741114400d003a841c500f40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 667689649 1250 667688399 667688407
    0x9090c0a0306091d3f0f120402030f010219200703050d02010c1d060f12040b040212010209090402040b010504080106080106081204230a1d041104180206 67
    0x214807940040d0000c1a07059001d02c2464400351070f25214256071052401c3c58464101c80c94182c2410f291030711500702072904400e03019904558441078030a4154034484103010100000e0b10002d501d40000c01511a0905400000f41020302c105818201522110180c40e801400305800c0d00c40e04594801110300c15084c0580d5064090102011507884003c0220050240310301c0003041c0f0102080d01c070f000640a5008000f4a040180c0c10344100d2600c10300c01c0344000f0910b142c550b241c00d080004060b503101007000d03282000a00c84d142d4081c09021102101d030301407164140401c60501440c3e01c0296507183c2d0003941046000c501090030b2180061000c1d00c04e5403603400c09041640982d0845004d403040c0343c002d00000d070315020740c98060000c80c801c1c00482c0c41180307031a210040d0030748103407003d64544400812200c90b0031a01ca0341e444e0b40c1c14880e00e6100b401c40800060070002031442d4643c0c1400d10080b035009141c58240711020b0416002c44074021810003044065000c100780d030122020b070741225030b01d4036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 667690899 1250 667689649 667689667
    0x3051215041409250510050c060103050706080f0403050706050a020405102d020a080903100f0b1311040b030c0d0c0801030c05010504031e0201030906021317010209090c 74
    0x400c00d44191241c11a2401c140c06120010aa240c68898003403038003210f004525505000d1180c03400c000c800000600c2c8003006200c0303480d042d600c080d404102d51501500300400c035003185081860a920460782540000801c100040d08020f61550001c0d180100d154103182c2034a000d01342d031207490401803641b43e6641c0041d400d50003d60595014000c00f5000108043e0280c4010b003805200502d848151079030283ea100d0003003040009108045666400b520070010760790744107021500038030303022a49801820101c52082d001c51050359921f5210a0f4042410304051043c405105503107621918018206002c20304000e8070384007107404444c244404d00e0382d030b99074140220403180180101001d501d42000e504019180d8331100c0705042c1c03170083c0101d24889580700c005460302d100710300c0010000c80d858a50b0b0214019070200d043c02507801810003040c100782540d140000c90380f00c0b000340620641207060038840300c0b01000001c2800342c2c1100085182c4802d610004200c440c00178503041d1551400200300705 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 667692149 1250 667690899 667690921
    0x15150703180e09070e0f0730180506010f1409092e050906010f15030b090406150611061b0c060a02030114010c05190206130602101812050306010302390a030512 70
    0xf034942d40b88c5004110318100ca1841080270014a4415a080e00c82c200000c140c821811160104135040c45000e810070710310410610903041d600034a1200e06004a41c81c4c0400c03045802c400c100e010140fa000a00c02864914858045900c0903011000c15800940140640f0403a240d154041d500c410301c011490700682c8400700c02600901494076003203504001032204000968201c001b05643e24240701c0c80240d140d00c000ca1b84d840c50419404200d51042022038240740e41300102104018880000502d096010030f82145407070400d851594081c4c2e4008010003005040b120f00e00200402441d01c21010400762302c1e03070f9503105842c0003403a440010308440c200842d501d15089881d51803440c1420b4414a43c0d410001c0d455926411070400383c281481c00ba1384541c1b10000c80c0755185070384815400e00d521003030ae00c1101d141d00000e00090500d0307800c0002e01654001d1320701e030450002c1075070b0100c1d66941c00c2c0c081525440d41c041d01c21406a0b480900c8a40001e074110040c0e42608800a009064942d02e80030490 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 667693399 1250 667692149 667692227
    0xd060203090c030f0c030105010b0f09060a171e0108030703050706022512140306060a0c03030b0409140c150d0b0d0b090615150703180e09070e0f07 65
    0xb560510031150541030b051070200c3d4000707007050300328000c014607a40d90200c0c01c124420460521040da0040010103203e140c003401a00d414006440c0440d40e180f600040000101d00595408403160b54540d90031000c3c12420316664050901d40300a1400d002c81399034003405a0184001c0209110b4001c03600e8403040140342e800400c0411400f45404507100607042010039001c11503200ca002803120342100503034041001c200e0b809040d02911041c50000e00c0d4004071400310104504a040544518000d426980d0328011821100d0103480e0040659140c03080983c075000c84c034184140500105241003403050404405c0d90070350098604041202101440010304490310705500510705000407050000902001920520450340140c001c8203010040c0d0820410140c10200f0000301801008600002481061035500007030140c103405520580342c40d42101c5008c03003140e2900003984604000c1140c05004000d1540210070104184241d003880b8400401d03031200100c0c040f10310316440305842c6409410b81e52074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 667694649 1250 667693399 667693423
    0x6060604120f0515010605030f1b090d0f02041d24061c120503060f04090503040605090a03061a0306070c21110d02010b012006060d14061918020d06020309 68
    0x13440d42580c6800c40139013107400684101144280f405c000540110598800a4203610b022507054280031000003007005401840704c049400907100b418510041c0c450380a0078102c98080c094800ba41c02c10503044900e06150f4034003012210703c20810044083d0b00140046070402804e9808403135480c400b0030703280441d2050400007001410412040302d142540304000d5805201c007200d0b07011040c8901c0c0100003d075040c00301c0261042e00100030030015070b0702480082c0000340b4003400e4001010f0b900c4d11031004452081544180f8101300341c808004130301e02030001c02c3d4800840c1c1001d581011950300c1f1300e00301d40d82130b1036900c10b41c0440c2d8a6150b0141d000d4201c400300602a40116207138032844038802800382c8000c010050200e1207410700318030380810342d03412401090740c00e0f00107081319a0340204005081c9480c0388240c3d40503040c074000c3c14012a040c48224407a030103598500e02c031000007a4902c0c04540303020701030444c10005480a5001a980c0300780f4201415000280981c481c1c562201413400c20b0f0542205e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 667695899 1250 667694649 667694683
    0x9041e15050406050609091f06030203031204020a0b030f04230d171b031308040b07051b06032403030412030801030b0c1c0c021002070f020306060604120f05 69
    0xc00050300ea550030451059100c0c00c01404541c40b12014404000d9003501c590030035800c9070a0350449001c40c0c552051202980b070300049211517582e00071034115072102c181c011884e0304020070402541032181c00c00004082041500349103150070390b0740c09004400500020200c1c181d10000302d0004113010f0021000c1024842600c0401c6d403066805003644020621100b015a418400140c1d500b04001901c601c60054102d41031540d6a4191400004044c0e000d044854032824080802c003210404084c015192182d4010a00611a0718050700300403264182284120000c20400c082d00c1d11400007452906031984284d900d0110080000b402c500030740d0090032003000a04804014594004405070403240150725560468407030b0400d01000d071161601620024080300740c0c2d000d0b000f00f03d601c00142507101d03105440d1501c1030b000700c60090764003c8400359411108004208154a001c1c44019048041140d44503e0716160110508490590001c00703820139003118081002d1240601c0303112920504591 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 667697149 1250 667695899 667695923
    0x201150e160309150f15093b070605040f09020a091214010e01020d050903040302010801150903050d0815010c1104090f1208091b181801060305070513090209041e 71
    0x503180000c010406c58540e88078607a50340000e00034810720a003034504011502403060340c00c00b030882e40003d00710080e08000b85c086c0400300c54410300c1c00b8442540070700943d903a010340d59494541401e882d07200b280c100035011441000f0340c0e540b075a00300c00700c081110102ca002402d0001503043c55401140107139100001b41d420880007800c07a8030103600401c140d11800008001e90703111070034119540d00a9010081c00704a0010041c0411034424128110b00642440c108280c60b1b245d0b40d40c14100800300c48100040385981091110703040c82d4a4880310407500070f00e0003480140c0c994840903244480348802d9806240c1d5480c640c000d000100c003d150f817444d0440a400c160030750b0b035103004015040c110340c6030800d801480c0c0f046050344840354212426030b800801010b04a078408132070040000002d00303842c0d8103161480351100311000070b005e044025400b400242444900c0c000c1401100083c2c2c8200d0750003585420034400041e91070b01d41003500a500100c000c0e4401c10b080d481c40c40001001e1340c020745400004ca03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 667698399 1250 667697149 667697171
    0x71e021f050a0c08090705010e150c010b090115090e061201020f0706150e0a0c110f0f060c0a02120906090a140f04020a0f2d0201150e16030915 63
    0x508000e0189240d40410400140d61840460310312806a43c08021798000391006c100343e40c85908154074182c8001d01c0b680c03c01c01703121035419041d40024880380081c0d445071129440d5203464800d80e07004120141c00071440050101340103142d86d0175406810b80c52100c3d0f00100d0165123907041a002d031224803030021940c60040c442501c5894000351000c8941d242000d0388001f110601c0c08281084418419503243c007a201e40003084043c1c00105030396001c115085055480d81d1408221941004080c100602589408003041c1420641c0c01489814040010460043c0c0540e001401e079844400c491016605e603214440003c0c41c07440742d424450f84c0050041c00114210981500000c1185000c82d9040321448440301800306034042c04012001280c8110a5240c01a0041403074099125030050f404c42b110800f00031603100b81c1400d102c0540180e560300660100740300e840d00814054500d01c0f500d00b50078030300440d51076024084c0c0ca400c2d80401d520b5180400400040e9003410702c5000c2412804d00501d0302032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 667699649 1250 667698399 667698401
    0x100c030c0c050307090b0f04060e13030c0602040e1e093f0a020c0108010f180b06030c13050307150f1b150b1504090b0a08011d070e071e021f 62
    0x112686a00c07c1c2c20f4501010f8007894148150012105580005038250340d0320307104900440d100b42015000e014a81d030344100003810610050018010500361140366040c820741398400304c1034030302005c41681c1c844000d11103040310024141c10f8003008001c10120052a5003909444d90300203070340244104090304100003003000c03103001501c03c189040e0308940200016000440305808c4c00e108141c45140560024410003403049146440c5540001c0c0118040e008180030800651080f142105180b602081c04062440003004a1008101c110000d08a590500714100545045040550248180d14214a02d514081c0c02e102c021200c00c4100c1150041c0341d81480d0a0340c00b050307145c581c1440c1c41c001140d0007a03d00002410300101140d000182820b042c00d0000c0000d021510905a0040c498640011075441c24091010407255114403410a04002501c041c6003020940041d2800500c0e4810016050350144407290a003004100101041c40c1102d002e82c1040c42100e81101c09540303204e15440c0107101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 667700899 1250 667699649 667699661
    0x5180c1516060e061e0601050c0309030708030d1109030322120b0601080919030f0c020901030807020a0509070206040834050c010c020303120405032205010e100c030c0c05030709 78
    0x403d01c00d440140d551042d552071a8150700602030071414211002c1451540300b01d024003810012642107a24200180000914150055002c0e500d41e80c4001a442101403090040044c41d2003401c026505001c222000039483e4010151104040c041c01c1018162981c20504507000a200d40044c45c05c0340d40c050f08140d403d00e1002c4a49d036000c90322800114608030030029110705d86082d4000c407a5400c1c840d9540403101d4108074401c11040025a14581c009a0fa034110300794020740c4900f0000e03689101c0d51061002a0b90941c2c4103a2140c00d40c0420003a0301a004210107600a43c04400c040e503444000c44080c4100891a40781c03402c000e401d1021800403408108110704c840e0080085a642e8039403a4011143c1000040340203415800034442c115454865403e100d0700705104105803428021300c81c030010404404810300c80b1510088a104101a5070069a052881c0d082a50f058800042c102005482e508071044000c5c208000c20b55048184020865803001030440241a07e00f0a69a80b981c400603040f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 667702149 1250 667700899 667700921
    0x606030b10050907052506230105030c18010314210310081f0207110619030605060f1605071a0403140712140304090f0f05180c151606 59
    0xc00d020202d540e00340a0002e440344002605c00800b006e100304410801c0c00c85000c24100c550303607260084d01d45040e444042040c074186500b007084680c0c0d0300d00401c05280210068203e8010f240c4909110b00b042d1904001343d0550350020110040c0303048803c0d071545040705080281c3c568404410a018020801c3c400442c02061104080ca0003503460724902600c4d14020354039400003000709140150441c155401810701d481c05050740300000c000900108170a80e0001001810500c440814154040d801d885404040d05065800ca03040803000780255207107224400407008040ca1100540c41000341c10004c803800740061200c23100249a14104240e1250002c0c0030854810600031400130034498002012012075910b00000800029a501d034a0050b88180d11240c440380000c003c0400c05800c54091904098003000f400102601401c9200c803c0b20b0300076082c4040f910520b80d007010040710004000d041448d04039004801c3c03242c56005c6003401c0c81204081481e0405510400c8203000f140e40c001502c2c80c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 667703399 1250 667702149 667702159
    0x60813060204181a011b03050d050408070b1b04050d05030d240e130b100305030c060a0f020715020c03070b041505090f06040f0c0506030420010314010306090606030b1005 75
    0xc0c013a030403140c012110100103400103000b0b00c15000d01001d508070405901d8000d00780300e89008203024412054540c2144d065490620004100e01007040c030982203580b20300c43c604070000400c0c52180302e050b20b1050303205551040020b02100d60502001b40125004c00704820000c12966240c5940260040901d881e1100300c125503200001e12031002e000800d10440c0303035115200c000151030b0b643c80d032503240162881d040d0a01c550800300009070108006c0c82c0190100c0c00819152402030410400c1eaa003990100302c55a00506c900300008640035045e4285060040000d40c5502a4045161941c0170341400500300a21040a010034031441280864158038012400d00c0169191440135564a4200c0b0700710328507030310403400100440e160694140c66a03100b18404e40f2099507410010b611078006032010382e11210007020904442840c202c0643d060326083c00c00340200500006d403c089010b051201820f2180c486950004010956200c0c0000d1740c1d00103207a0545040200e01c003c0c00304c5060150074011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 667704649 1250 667703399 667703411
    0xc1e32030a03080109050a1e0506031902060d0c02160b04030b0a05070516080d020c0c010908160e09010905010903081b1305130b0a060c05070b0c030406081306020418 73
    0x9410003180e000800c5400d9101c4440c141d1030480307444006c000c004d2010031001d0380c03403079141031700c4580604600e90005e2010340405d01d07081c0103040500340003020345514081c506540c015130058641c1016106105118280081c03006450002a4205110040703514850120080c000c43e244411002800a903070086100c03030216907a025a100072201e054a940c00865810300803040e2603541c0610207402d003481981c1e6241002000c3d4814170036a00140303030000250f041580d18040c6942d020303031408000c21241006010b00000b2503124500d110f001d0180882c41d980100000d45141d409402c03007214907601000801850101c5d0800600c2d0030825103081010321240b40180030543c00400542c0d00140701c82d410114240e1904040145101018040c058466151600c09940f540d45451100084c680c0c2d80b03941c1102c7e00645409410b00103141c00c52206020144020444050004141c2c0c05903642402c110b1580e0b00d427000150248542e103007004101c00d0001a01054003042180060803040180d001071200c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 667705899 1250 667704649 667704749
    0x10e062e140c06130c03080a0314070804030e061e070c06140310060e180a020301080f010912031e090c06140c06060108060a0503011404120203070c1e 66
    0x5188510030040c00b855011a0100d81e82c04003031003460011511801c00042d94135900c0d43d0310300c00381d00585150004a60b6501c1801c100040050581e6030202140c5800482d5142603a8064450381c10741c01c03480e015a002148665451886d403407108100607400010a0b00e030521460042d241950a0259000040c0d113808192101c10218042d06c3c06140003e5240c03440c0d600b810f074229002c0744008151a880000c0300c2c3d200c101c900420075024001c070440c2c81c0c007680c0c0e581001091850091000031001c42030f0b2401c1103a1020420b81c2c20035803031264980c540072078034569002480d0350085120780644085403424040307404020b030400c118001c981003904e07a0300030b280c54a242c07040c480c0581007080660340c015500040740d96116210541c0d110074000c0103400721513119004a402c40c2d000c0c0c0a880240c49465003840248080311040000080380c40c030040d072900319a6503c6880007035441c820070480c6400f040d651807512100b4050600a40911501d40007041005012032000c0342403c03030b410340156800004409 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 667707149 1250 667705899 667705937
    0xd05191409060112080d05040c2907120905031006050910030f110406091d1603020d200909010506131112060301060503010e03040329010e062e 63
    0x1c4a80d129102504080e8030380341c0404003913100c1400854025000700103050350004d0030300c40c0a00480c001c9440403800307070500c0380f0051440382000f0118203e0f5500d100085401c0e4112040301d507038581c4600554031101e10390000792070070102038221030340c075009003400c544811803103038411808c42c2c40860345882c140e01c520042c4e075030b00021408094043d41164008001181c40304c41a14907210b0054000241940d40c0c000c401c045901e00510900c200c03503030181c180c940000c00c002c1c25401c1340c082d8000d40c031007a02e5980024291410a00f00509010480e80000303490038410040760f100d00406400303940305160201c012400ae2804035041c0b40300c0c030300d00d10f145005801e542c4540a0580c0740724840c076240070300024180d00808030060110354150f407501c8011a00307480038000ea01d4040c031404007d5446908500e00510f40e21907020030088070141400480d6501da0707440060b541151032075408601c503901c4583c040b507807101c601031191621042c840e03200d80040c1428130b0b01d000c1e20065a51030b500241d603141c49000e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 667708399 1250 667707149 667707151
    0xc0d0306030b04110a0e180f0708071703071e050d020a0804061b1b0e130809280e071409030703020909070315090c05030d020a170d051914 61
    0x10b003001c00140c0001e000034501c102c100c504284000c01203104196a08400b1041c0c0e20200d501c500807070b0303410aa540740800d0030012881d514a0b03100103426124203081542c1e607104241d100e0300c68100d10880b40121815005e00c11550019003045a078800d0f034910301200320304800c140c841150300b03200c1c1c079036407152181c40031a412182c2580700c645070740351600c0c00108842d44400102901e003580c900503507040008200c0010882c2d00c405031507080c81850b24040d9a02c04210380189a400c102e0740d1883c0000000b0a00011240808000c4681da03d00c50240024902c1e95460401d0411201140310404103440d11540c20a0344241c00c00d56a180c48c400b07080f5800140c9000c4c480d074890f01940484c80900051a207102000d80c01000802220740341039680d2100c1810007d403010f0015803540d5540c02c1014819800b0030040942000c0d002464202e078200d60003541d8144c03144016086045070030401c0c4018a64908407075419030003042c1403100f070400818040c00031401d0180000b0700fa103026580c20400e00781170041c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 667709649 1250 667708399 667708403
    0x1b07051b041e020d0b03030d0911122a0d060605090a060f050d03030212040c0503060606071a0c0f070b1e04081b0a140c090a1b050c210c0d030603 64
    0xe030744481d4504840301c0c044d41018480c42c1d2455120003040c412034400b08080d250192050202140e45001d070300307002c003021100000745070041c6c0413800c1c00c01c51040000741406001c081103510180b03240c254241d4403d1020360321700403540804c2481c03c400030301c459504040160cc40440e40302c2c1d041d031100c602d40011209984240d45088034650401c000c2e03442e00300300558000b40603080141c604441e084145401d030004460403220669205411b1003e42410003140c6d0780400709454252505a007900c80c0303540070040c400e0302d03080351000000041c0f0000c0c00c0819240b048c03c03410700990311990740b450804030b806411a072030005c802e03e01c58103001030005881d402c0d0189030400d401928100060901080503142ca0000d8107d45c8182c001c10400240c40780d06031480b481d0340b00080d0901c21600c104000000e50050810011141080c0c030086005010104429914016040c00350f0307180302854003103007415403001c0a50300e041850951511070f50b0904008025400c03003e01aa2000800e0301d1068045075198000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 667710899 1250 667709649 667709681
    0x306030c0f0406030c081e061e040317090d020105102702040b131508061e0102010f0e0307030909090317061212090109060e0609091b07051b04 63
    0x2034025080c0410103400184001d0404621507840e0b40307420401c401c3c6580941e01651020781021034042844040e000c15190580181c49079003803008103024011a030028680d004252040898101400f802e400c3c543e400403c07054850628021001c0e60701d0386020807800d40954200740018034014007018942040c0d40764083c10706002c012030b680140d46000c01c2d0030180301a030ba003000007140020003040680305810746c590304900d41e5400c01606483d01c040f103110034414000100700344605680c0f02000d021421540d0303040d018060400c140102d014146841c0800c80051402c408142d00c0d0381c2c00b10050060301d01a485050072a940d4004100c12a81404000740001c2c004100640c10086050380c69600701310000e00c3d01c02c0f1650409420b60601c0128035422026540020314400c455800082a400400140c1006000649170710045400c030f1003541c21070785c482d807400c07000528494079107492402110b00315091a901d411261030b061355200d4422800313000c00d00c1c24112540040c5854010340001c41c100c0b0700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 667712149 1250 667710899 667710913
    0x3030e0f030f1b0f010e031e03040203101116061a0105190302030c04080f0610051c02060901170c04081e0a021e0d08090a06050a141e0307021011030603 67
    0x180e03000440c00345090050390003150295041d134203090007201480102d0310302440d520301e031098041c1007030f240001107249049024010080569004601c07500000c107a9480892038005401c0e01c3c0d2010300c04d86601c0d81359101f8410004060190702d1780401c00150751110349101c3d0303402c04001940d0a01404c0e2000c05101c061541001555200740c001d183c1101340c04401c9800c154943c1003050900c0d100321010703080b580c0102c0810021040c054142401400f0a84070748030a0108030003001c0b81708041c41c40c0a40a4a400a41208164480c2d4021804009182940305031402d0505400200d0340c424480d0f41084c1c8902c203880284078604426540644180000500c44400e0701da0034840c5010783c2581e40c2e124034201692600b401e4880020b1040100d20460000703680b140c8a4080055006040d040134003040000c3c0302c0f03da00103801c501004080901c0ca207009840315007a80c20000d81e01c2c90311240317595030100801480f4110343c0000d800c00101400c240140486100c1c1740318407000340011a603150303055000326 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 667713399 1250 667712149 667712167
    0x905191407050f0603180313060e0301061514071707030f0f08071d0a0b0301090902030f010c0c0312020c03040e060301242309070f1409060403240903030e0f030f 71
    0x800e48030146c400390a89040011654000641c0041680001c021409484160056240038452400900a440c0450200c070103100340042c0220f500c800103805810000640009020f110903090607110140b280b440d541c2c0c200d526005086081c2c000210000c60011450003c10b00c0c041c91456200b0500c07503407011100440412610800b2058414240d0801900003003c5850004100114080e00b2154404030750b02c0303120703c10f1514200e6944010221a458007041502903548045e14100c1c894140c0750241c00c070740c50715581ca8003d1241520740c0c00f85110001d000683d0b00c0f44147c2c054030401c4110001c212008581000407006c0b10344ca00000d4000344107100c10722104240000454440300c0e800800c40e0016110801706e0300f10801a0707007000108000000190071140e10290404440b1407200b0001c0c20024400d000c00c2580c082c0b0f00008040f4082d04400704030440e4040c0001d107aa001a0f07000b842100003508004d001003084022291f1a405038094002ea1120000304444a403103190030154a0074001e8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 667714649 1250 667713399 667713421
    0x309090601030b0904030f0906050304170310080703030804060e030c071806120c0e01061b0303180618060f0b010e19170609010c0f02100905191407050f0603 69
    0x40c04141890f9840a50b0300c002c1d142d000380c16229034403d884244004183c1c85010348000660346c071410400c00100300700b00026252242161141c2e0003900043e440361140106c05046107003a40002daa41c0c07251040000c18180d1000066024030301401c0208403406100304206d0b1688107040c240c09090b808840200540807900222200043d061840005c44a490303128201c2070040f40c0406075000c02800748c0c00e100c41942c0700c501500511850030500b50a144c01030801075082e101050103018955604c403005816042c0d10800191550710040c100000c01490340b020907200d120020544416281415000540c98213100c0d810100f40d0585030030118030700704000c009015042c40c4043c1382641d0b04200000303110a00500e503241c8000524050101032070900900f908440c25641079000b0010748108004a440d004107c0500d030310030b075100c0420b102d881070502500e00070300c1c200707904502030307101181205001c2c0d9a000f1090340031300c2c0d10944007216901da003004405034500e5491540031100300702042236a281 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 667715899 1250 667714649 667714651
    0x6060901210b0301020403051e0105013b0901020309010f021303081c0608030c060924091501090b010215011d191401291e0c0f0106081501030203030909 67
    0x203945000c12000b0301d450200b401d90304240e1040703540d0392085855005090151503610103003000c00c00200310135858180014031680c0030003402401c203011a521800100c1720b0010344501116001102d440c01e003880645207000398800c4030541000c0d403038a0028034008006000300c8542d03014844a0210700750841c0c5034032200341c0c8000f003030043c080c203807601c10f050445a82c01b80700010304999000d1a11240900441410208001c0100c500c41d00a0703604034070003182a440e002803041040346001000d0b5500c1403030328074245010b00c125042501c000300000e0403c0b001d40010103400d00a030700340c03219072074682000700b82408203004118040b14081c8c0b00b422660200100c855001d82018810b108451a040c0300da401c8602c509800c0701002c00200052003000c030f00c0103c0b80082901d61211501c0d102c2020180c50842c000d407800310500030032094000100f480441c040c0c0c0e10300030341241a100c1d42d103042d0000701d000713000c548640c104034040c1100554217040030980090403650050051489c01d98003100b00900000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 667717149 1250 667715899 667715957
    0x311040b04060801051524030f07050705061008120f04030323030a0617031206060c0c03060a021b0a170703051c050601080603160909140616030506060901 68
    0x1680d408006101c18090117524050500c100300080500069814000c2a030b03628201da280040800000b001e80d04d0441c0d08403980700c1001e502d400096100c1140445040c8101c80300542148070342c9091000c4400000c03a40001c07990503904a550a0030070030313040030035402480c6050040d03941c28441040401d0080c4013a05900304800340600d1481401c084940c640d0700160303030189481365202000e218244d81c040c458180704403590011414582034a100c2642880000d10040c01802c000c100800204010000c14140040003800c2c3d030313014505180d0180003508140f175000d900c285d01a1100f0071071480402c00780400c9400c83c2d078610000000d81c182c004031b68011070007102042400c200c80e050300c40e01401c0341500c6076226040070030b0a0610200041010801030499072081d080348901c0700301041500344030300031244520700c08205401079040034001c02040ea0384420243c01503200300715840d000564040c0740403009840401840d1210020701849000344100c0b1070109035040d0300070700400c407810111440b541d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 667718399 1250 667717149 667717151
    0x6020604080d110406050309010606141c06050d0b09070905040201270e04150c09180f0603060c0906080106050a0f050313050313030606090905060106051c140f100311040b04 76
    0x201407100c00d114690180d4805c50000e400402404a80720b030a001d207000400c0c1c54500b00c0080300002c6540179161103664604580300b070701041d40c0d01c1c11101c9500400c00a25004280301751001240c14a480c5920080700c0c0075070039001d0001c2c0851800036500c54540210303010b9407852081010020b045540d038801c1c003518041c03244001c000168080d00150054840e5110703001b040c40c2034000000503400e03503840905503818411015014800c3d10b141040b15011600082c40104807040c111030900010045904060032080c180781980f0446a004440c94086941a54030030b00160b0f41c81304100c405000b40c5c003030f250008803ca140f405040b44200d01558200700c002d051080e0350225a0f80c0c061031507100e080503040c108038095080050003107a01c5004028500c1c1401070040c00300030340e00d45071542c0e070501800c8140507000c6900e207400044018031403c0480094000c0107d901c00500340c407100e003400c440200c02072003440002002408000086011250f200a183c40407060b41c40402c00a040603203440e80e041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 667719649 1250 667718399 667718411
    0x904060905190231090201120c05040510170402270712110309030909040f06060b1207020c0d11031504060c081308030a020706090218011e06020604080d 67
    0x214109000b10005100014140112415240f040c07000150201c406608040141c8501441d6000d8020300e5103652038a0351381c00128031500b4030058444040003040c80e40305a180414640145800000400a4800817178800304c03110450304088401803054058180201e12110109006051004907960000c049039000c220960750310001241c6003004494040009400000d81e500c0041144200c503042d50140f05030619514000301c0095880c410410380502a1101d2400601804459203090b8078181d8403c2c401d000d01542c81072801c030305030000c042c1c000490300c0000c0424509400090108074440000c0d11290340750841e07858880427030401c0a01c05400d03000700000e44030307007005140780240300754480c2d5000166000681c2d0001c007202e40041c28480c0445a040d51400440e01c000203496004408100244e034400d040e01d410405030101003002500900c682c1c08146d000d0a042d401c4905803591010790b9801416101c2981100302c0080c411344015802c118041008503030018001d080c040c080302404101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 667720899 1250 667719649 667719653
    0x417062a0903061e07090602030304171b0a051204180c02070810091208010605120907030804060c030f08060d0308150a030f03080a06061d011709010f0b030f0c09040609 74
    0xd04201320341c1844034540090445512401c5110141c1d004100c07498003045e00340c20b041c4c0180d92480007600203030820924845400300c0e2240503045904107210011a813440500e02c03440c00395141004981210a402000c0c5c00f0010754680340295011141c1d50140002c492034171108c00001000719648034070842c01035400200300007400300070944010343c62010008109850b070821300c00541d070081e850020081490b0041120603480419120040388945207060742d900d07003103140d030714184880d40020041c881c0810300044880e0025a81840140240c8500c480304141d80e404480c2076004541d003552002c0c010940a0100b842120003d0340b000303404000008070402040090f43d880d000d60b10440c8c00149010004040507032042000341c101c441507800340002800d00074050b110301c894a4070612000103000081c14568481d8009801d0006c4c0d00180340007608000301801e01070f0618a40568600d4100307200c03540720b410000b50000c00580c03280d000e400b40150010401c51a000d0180054a19075122208000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 667722149 1250 667720899 667720903
    0x509100309080a1d0a030b062112040e07020f120705010b13020a090602010506010c020f0136060e0307060819061404050c0304030806060d150b0417062a0903 69
    0x20300300311240c03103560101035541c90007900c4480051074140500006001000051008500e03a03400000031501d10b00c100f0449e10f6000d00b2103600045a800900c540300400045040050044c01aa40300411141d200d41c5d0744401669615400d814610b896403090703407400000c41909000e803480034171540001c541c8111910001f0352407204080f201410990004043d182c15811071500c00050401303000034000740c58410006041e0540c80200640a00c00e0a20403003402d0b0310500b819420500c3c0e1411b01c1000022030a00300314101500c0301001c460321070018002c034105000360014454054010001e0a009061800440307468070050095810700c2201e0b48034220a0300f20b400307854090302c04062000c810700c066070100000d1300d502030100c2514400800038003020a600010056201a00b901c05960701d0701040400c01c01010b0000e1144805403440c41c000c40c1c40e0358032400034003c07582c049040f614500078803441151a682c081d12484240710380c0f00da82d00c021f01103004107064a0207180001c0c1d4107180440011078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 667723399 1250 667722149 667722157
    0x8091b010819110405040e1b1c06090c141801170307120203031e01030f0b072a02090c0f030a090602040905010315050108030c100f090c060807170601050910030908 72
    0xa9903c800128041c01981010310500c40c0390031030b50004100b041c421000800c40815034800d182d0180072201e218030381703004118140c0e09030b55600080410180c1c01900300b10000f01703074034025010300c100c20300c0d544022440d1850b1060441c910080c05841240d00c3c02c032801c0c1823940076aa90001d1800180072290102e09014072481d544800303500990f40d83d180520b41c07600f060403402c1e103041d0500403203c0103001003004e01390308001c01c0764020040600794884e45c1c001d0300da0300031910710070f101e46031a1007203c0701445211401c00d85a62081d80e01d21a15207506205803d14010302414003002c030810300c0010207900a0750401c20101d030041c2001458680c86202d01415248241c1081d2030038404806032450500d510b00c40c80e0300502004018600700f4119440c09602e441040d00031030401c9482d05410741e282c150590008180d2071b403003d1105007483e0b45000150504108a801401044042c00301100704034212500c82d100c0d0005035140e51030100001e0410050410700d070a0901019542e421040010300e10500030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 667724649 1250 667723399 667723421
    0x5060316030f02040b0f09183c0601140d090c080f011401120c08030706061a030906070c061d07090c0509030a021c050d0f08091b010819 60
    0x140315030804141000e07003500c000c8160788841c140f042104004030602541900d144c82400c015083d0b9070040322000079003d00703146281c1322680d00a07005020441d9904544030000365540c0001e00308450700c0b8480038981c08110102d49a007000c140e80014032a612602107900030000e040d00e003900780440c00304000d00b150703101a0102c1e01c018000c0821300c2101c00402041036412051002400000401807010450744c87c10321030044808114420801040b81902d001e102502c1c081040329115036442c180003015003032030b1040c8580341e40b40410008800304003404a07442418210020941d58585850440c3c1c02d500001d416506280d0314141001801004034810406000c2da40040c0040c0e420404110b04803814100b0000520508000d40340e201d40b80440c0300350001e40c0440340d0050300c0008414003900c41321510360041c030368096600039420b0079070044150350340c0b403207181d44a8806665401e4507076a1001e541703016840d0920250102c81003076200303941d207d07844009503049201c014116640d10080d1500c08dc01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 667725899 1250 667724649 667724671
    0x303040305130510090e0901090204020f030f0112050d0c0305090607030e1203040e0c0903071208300a0c0504080d020606030d0f091a040f060503060a0801060612020c07050603 77
    0x70100040281410780c06003100700ca800302e44c04610b88018024082910462900750203200014032280d20030f40c082d011b0503402501c00d40d9112200c8450444c903034411100490341202100c00840e509200009015006621000410f140c000c0901c060310b840071400e1088040100c100040f00d800d80b40d80e005040c0051083e12030b01d010403d000200502c41908025550302d40c1c0c800e000c100103c120354012107802c04c8807070716119601ca50402c0070908024440c5c0040044014030002c60f81000310b004028819541040224581c8040000d85049844a02d13200f11140a0200d40480c0e00540c00c0e80c0300000304103076802c006240640d03c50105051003010003070440942c02a904100841c04c080c011a6100760386498200d0b6002840d48015040b90400e01581c0440c51580405001350382c55042107034080c0510318490a001c654440f0010581d601c122081401064407940001e149041401080180d90b07d6440d070450380d01d0340e903045000a4022064181c194864590006810785a01000318010b40e0b004003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 667727149 1250 667725899 667725907
    0x13090f09050106210f11030102030c0c0105060d02010f050901032409110a0f050708040305030412060c0206010e0705091f023a45091406060306120303040305 69
    0x400d9401c450f0b480e0712460381e104044110606040904503c03504150b403003884010140d9490404000c043c041c480815050342c400414441041a040080d00301450044000d015550340d14043c04011030411500038080303002103e490380d02c107014a0103031688417018500091000046a010500c082c500e00c1e03140302075a00f1020138130101c015409488032044941841c24a400300892000308001030010340c6004200c80070805a0400c40074508680013190820222521030b80c58000c00441c0700203c03142100c02a1402d18111049800420824122502070b01c14401603070303942c0c0c0c0c2500e007640088403055103e15056800c000b40280c040a9a009280315402440d0080902908610a400c0842c5030f4000c083c0c0103021004407001240e886c890304545280c00380c2d980c10720202c0400801c040c89007280b0f83c901251a0030791204800f0b24659200b0051b4003103010250780d00c0d00c010341140c1c844030220480c0c1c0070745400240c0509104000f541c21040182032071070034102c00e40019045030401e89003100080e078009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 667728399 1250 667727149 667727153
    0x32901021513030806010c050312060109080d080105130603020913110612070c0f050105191d070b070302030f0406030608060a020c0a0f0c1d180a0206070813090f09 72
    0x80115042404007000c280503003010503481051440d495001020030000f40000740039644610075000207c1d81c080c0882c0d45540014004c2d03c0140c1c001c41c0c0301030008003541c0c0c002a6440e0300042991291b0703655120700c44203908220030700140066039280c0f8652240c40c0c900000050300c480f6000d510854101454644000d55440d00e0f006410805040512840742400014084071f0964051500800c1c0d030300301110560f225142071001900b0101015115502e4642001040404400207540b2408810402c11007c0700003006004803500c01c0d5101d1005600c516803d10201240800612600b80240102c0c2d051071201e0300380300105e50040d00800002502c4801c104034640702001000e4019000c000194104090b440036555504030180002e0900601c1070108414002560840d1010b000440c03100ca04100da292030503d0041016503014100f800c0000c4280150b030b5011945000c040d0340100303054070300b4006031680115600900301849400781000c400061040d481d1181e1240f00c0e040900108004680f4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 667729649 1250 667728399 667728403
    0x501020d150806070e01090b030a09120f0212090a0f06090f0b090108042909010b01080a1103070507150f09050d0804080904021e07080408070f05010909050703290102 73
    0x1a00c201ca081c2003410020b1000d81400300b0b03603680c415120302e00800c1e000300b00c0004071103c030540e610800355604008280b26a0b51500d8110700405030143c4500705d40840e699504031001c801111081006030498401d22040300300c14801403c101500501c1c806403140c480c08070064103d2280c0c000b00209010810070800b00340140d50000c010f101d00a5410f080c12450030020b0011000240010301c001c02d0310301200704050509646145810056510440c20325086041d40d00038600004024041080c4c1d2001400d550300034015086500000c04000e801c64890250595154001d0401114844091500c90310300001c07038450f002080901d4200407602d02c4080c10031a08118140c1074040420410f2020040490070000c00c40d02030010030740c1e00690341c0c080301000c0000603106003007040502e000000c14001b030040034805403081e200c5107000c2e0342d40b141e40c8051500301d200551040c1c50200748006803c111070743c04d561100743d00240e14140450f5007207510119100c01c20181c41030800d86040790080301c4141d641 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 667730899 1250 667729649 667729661
    0x2070507142103041401020f0601090c1d030706110304090e0607081e06060f0c1009170a0c02011b020619090b04030302340b03010602100c0c020d05190501020d 70
    0xc0500c451040b8640b605250307071a403060b4000d028041103e8400304a00c1e91003004900425070441d41602c0e059619030602e071001d0034100d45c10350001803041c001002108019401d00109100040040c29101d203003600607613214550009607400c40c0000c1c400011400054080e00f044450841e01a1055240024010340f007032002820200c00d02001040b51500550030440540d0400c104685440e1946109900780301e680c45010210800d5000d0903010403500c0c012500300c245414856003081490560b000f00245003806907204034000074001500c000d0141d4002d017010301c2d01c80d0341c100c0e00d00350755442500811001e502c11204023003d9604108000600f0f640101c0c1100584914030070b43d403900d07103142c60003551035010003446030000c0c000c44424089510100000044044910003503a01540d0f0344900303504a8200b4400c2a0160040601c1091500418880c4a00c003058645800c040744190340c003441901840325a003100c1d58490b94035a1603210804101c008062449203001680d12051940140b0554903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 667732149 1250 667730899 667730929
    0x1905061902160e070c05070f14030d030c0c0303200309030901030605011107090e070e070908010b01020313090504141b0f1203030c0c030706020d02040e100b1603030207050714 77
    0x21054000c1c040190f5003400d0607005901d5141900b07884d40d103400e14a04148903540040801026101c0014540100c0b0000b0f522822044040d9500800d90f9003096099030102030902c000540170424440001c0c1c040c1d802825116008034951004031060341e81002150b0045d608101158401305200206682c0360145001402d02882c00070306810071212042d13500c2d88603005440c03c4944844210403103100030020080207101e244954000c0f41052800074054000901074142d107542040401900c81d400002201e2852484c0c000b4040c1140c50301c10044001c240141040703a0354050f44802500003501000151b0517000e1204a41004502c403208106003004001380190084144103071100c1d1052000c01079a902c00f03030010342c0580e40c520410080c3c0c01c42c880d0b548000c0c0642d00c00b0800f45102903040e4003510542c0d00303680703840520303443d6841c042d01c50b80c02c41e11814080050810070301916003031154181150601c81d08025040c2025030707403680d04118640d040084409060100c6402600e484400245941c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 667733399 1250 667732149 667732183
    0x905150a1809020607020406120203061e07111504110a05010c0803041e050f06040c1e030809030309040501090522051b0109180c02060603030906091905061902 70
    0x24034181007001c2541c080d4203240522551000d8607803c0d03481c3d8004461010341d00030070800140f5290000e200201914450903030091090360300180f0703440f09844a00300034184084036900140c0c1d0b0201c1c119403801100d0b0701d0004901408040c0700c50718810703001c1c80d40601e10403850000690540c000b0700c42410219841a4100074040022602060f8554101c0c0d811a400040c181065403000c0b14042c07a00d000e0741c2000b003051203261408802c00d08007046690140e881034000340740c0c0c2d03582c402c111101c41c8510200001c139042000303001c000082020004010350140507060340e003420810b030b0014003100d8003640f01402c402c0d01e403000c01410380d181c452914481050141784264200341602e0702582c84642c1542081e480071400b0905c151607015084180c014590550482103031181c55029a014103440701c1c004001d813240b00007240c103030b203408016103400d8940601181d092401c84d204120a0b20b43d4800030700000a05104042080c0d103e4030018884400c5c002070070032280c503401400070b2030174215000a03c0c0113 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 667734649 1250 667733399 667733419
    0x5010e0c0109090203061906080a06050d08030718051c120513120201030f1e111912020c030f030f010f030b010509090c0a0f0e090307031e0203090a090515 68
    0xc0d81c1c020201c1c00643c0c110300d40058917a039440000ca0140c02c4030320380b9621010f030030b10f400203602270740030b14600d124004041051000319610801d0188150380580014807a01c0b003480019a4030380f0541a004603645400300c24204240d562001c1513038000002080c14405541d8a0000f01340302c038002c103801d10032045203450351030a44507007040240445d0b036005860f011381e003203181d50045d6031203900128510b40814204112411a04885030a0303010010342842d407050030801c00198003260700e406e8940c00b00d441c0310a00f81c0c1d82c44c0480110b95945420211500070360b400d00a180001c0b000708080d1010407082c086031540d038200703800d4112480324140d000544a1b44080c006000184829800c0717070442e0170507582c06074903480d02c4003030fa4103200d0b03110715030364002003ea0000940148641c500b1002c81d40243d0b82d03035040d6292000e01640b03a1242c0d20000d00030070350204007001c004088034201882c0220784d1054074240407a034800600c10174003c1c6d0105484c6a1038206000001050000a2040301004ca50f02c06c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 667735899 1250 667734649 667734673
    0x2030a1707020304180207120804200f01050d06030c1509121a060301090212030306120c0d12140d050708090d08043309060507230d020415090305010e 66
    0x504e02c5240100c070419501101408061651601941d03e996408900e2410810302440010400c4c3c000302c0c0e003078802078140342a0428104000c4090a82044090b205a100842d40401562546c4c80390140041380c41e074903240003011a449850003406440c1038a0356000e50f0091050041496001d40c001000c4005840c0b4080000f41103034840b5920900d4480e48044541d4502000900509200301c2c06908291030503550030f291400071000354442c40044602c40700442c08039010f075030303608028074069801c000c1040e102404203617488025006032190b8036000f41101d081d80e58182650300408c218045c202e881d4028031030030039044850315a00c218100d0041900304541d40c0024140780004d80f000d000721002d0710094841c4105010b03440b1921000007a200a00300d04000c039107000381082602901c1803171a080c00324414520440c01040b00c114801c0c02014841e0300520084003543c008070145d030040380e00b00b00000d03c0082c86440040d4140481e11034000051a6060a9082d0f0300741c201e05880341c0d0403102202903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 667737149 1250 667735899 667735903
    0x801020c0c180c1e091c1e0c03060902061e13062124140f121b040b040e0a12230708070203031911060609040227010602030a170702 58
    0x18804c000d42e42c072000c11031241070102055115120006410402070044c2008440013071038070000c3c151040044500304118049445901040b0040080c0010081d071001c101003042504410b01190000344501c0c0791244042608140781c0c01220400c17503a9602040c08091031104c006240000c1440c0d040442c2c849600c80038800b400700080380039032007a0784d65903155801c03040e01103d08070f10600034142a00c102a2144041e40a404078020460310803060454402c41ea81000c03480b0b400303610005401003005981280c0300100c0c000b565001e0982282c0d480d811007005503228050540c01c60b080304088e00d81e0203041c0c10190200700803038548006001140d03040508803d07038288001c0d0341c8881e6034030702034841c4198603051095101c2d84101a5151001141c81e0b81040d407912140c00700790b2103175155658004414140b081e00d5041c1112b8440e80a654280004c015003485140401e12034001e18201e2110802e00c400004080b100307800000050307201040054001d50012005400700200240381c0c0302030318110790025 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 667738399 1250 667737149 667737157
    0x40c030b0907052107030b10031b0503030720060304060c021e0304090902010210050f0601090603060b0f071103011e180b0c07080705060a090c38040801020c0c180c 72
    0x1380004104992401c064009220040185522142094a0f4140800c4413038640a40740800c1d90140214410071640200c8030f0412400c4580182c007842c280046a1a00c8510400b1096044c101000d00301003441359559100065101d1071113035000045413200e40800a1070040c00d100c814041d007100e01000780d400311002040d1270840359080c501081414980c80102c8c10b02c0c0220002d180c8850401c000d1001d40d040a25107244a99003e0fa00c0d6101c0a5032a8011401e95403c0d00c10000a62403c0201c0c81d61414020020140e081c000ea0541084440007008a0700316895402c580d00c4180d0030f849004100802d41c001c100300c01331120000582d41001c0e464860084402903c91542d145e4000f90311000c2004280944503429000f409440141c0350406410011340b0301244101c0b180080c036100030aa5110781810268840103ca510440082c152915254040b40030042460450010702000078503100900042c03039504280c50141510083d0f440c2071012044809c64043c6003c0c0d2214108607a8080071340a507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 667739649 1250 667738399 667738429
    0x605070209180a0b04050a03030e1203040b07141305010e0406051309030318110a0b0a0e010c08160c05130606021f0605100824010903030e060f03040c030b090705 71
    0x140e01039402001400c1c1c0750102c020001449014030b1000c1006000002c1f41841815010307403014031501002c040e0081d00c40c604074611511400050012901048603644140e03440700c65401c180c0103c01401d8400e561a400520000c05400d5101800703000d60b50307114003030001d1410180c0d01032011904007400030b49142071b01c02d503641001e0f41e101815400e02d8441d800410104034076802c1906268420305100380701c80e4046211030300480da00d800c005040307821075007202d86441042d03840450140480b001100e00300585041a0781640e0b00340180ba8081c0520103c40030158460a0310601c0d031460082407006070b924540380500c0703103803520f2410441c15401080003c6d80c1c120701004010300d03405c010701c210000c0c519a0022500a8a5000e24201403600411418010382c02c50701c0d115540005a80d900c050001032044007400107015050800000380141c12003212a20300802c0d460030b011210444107429001280c05440c02621090200107000d00d80100039008041d4001403c041801c02c00031407800e901c44019 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 667740899 1250 667739649 667739671
    0xb10050306041d030c01050106020307030f08040c08073c051315060e01020613020a050f010203041805010312020105010b07020607061d0c0f040504050a0609140304080709060605070209 81
    0x8030181d40b40d500c901a00000001c2800071910000c10b26a540c1c2c0107081103060542c0b0380300000c1780345030000041d03401260341a50341d58811111030804075080600644102e038450420400411050402d108880c0507200c84100ca04880301229408114441003540b84170501c1031b035a940c6091284001d801ea025107a068540c040c115040049950007441c44050200300203809031404540a5840501c503460f90320260f0844072241c41d010b484404004200100941c4005d0f03802d020020f609181c124454940d20500569040c00d603100441030402049200d000c0000d9a1403006008201ea52070144a9405252008010560610034001c46a11540ea4043d2080c04080b85003410030032303181c1101d410100380001c4014150780805020f6034a401609050307210360501960900c990900c0d20499203d20741000003060b01035002d07210a001042d0b80981902d01d20046681103140041c1080104000e1140f400188452031030a401030040300c0d882d030050010000100300c2c00f40036903039103084290440d00b1044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 667742149 1250 667740899 667740901
    0x140a2d050702101811011e0e0103020d1b020d08190b040216030207050112020901170406140c0a14030112111215150a0509040f05011d010e07090b100503 67
    0x1406034680343c1910b203000301c0d00f03040c01d003085074000c0740180140500381300744160b000c6510960700541e409444541090008407819800d0301100d172154220401030401070400520348802c0c5000072040d039502c02541000150b00e00e004a040d50350401c925a50300c030080c80d144502d030a00d007a170700060349640820060f0042d20703210b0000041d51590304555441d041c4110341b594400c0c007454082d44600340c43c41a0350105541da07248200991032070003160201d40707050703407007400c0000000051031070034601600a4900030390b030f11100402235a03070010480c064004405060740b1000001e40052501c00021130b640e00703110050004214401103c441d13a20702903400741003040d4009800000c600c480c42900c0304004280302e9105c1cbc9102c200400c5e00c4480c02380221620390104c8101800a1210a19030f80c880e842d00115034400003400700b08861109902544108001309100d00343c0700300c0c0144140c244400030240c1e55078482c2200206000c0009600400e10005d0500c0300b41d100500003103041034400289014494000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 667743399 1250 667742149 667742161
    0x70503120121030e180a0506091006020c012f0312070314060d0609080307051305030f0304172406030613080f0a050421141203130f020301140a2d05 65
    0x5c401c0e03003a13205010980c40800d280040e02c0d0b5010309010303122117015131030400104402c41d0301c008040341952010740041c21020f2841d001180c0240f00054080c10645c8a2200f0030f8042d012405420014184400119207504102113001001d41c000780c1214141860400d43e04c1d030384a41d19015035401041118007107680100781c11b180c0f000d8545404024080000003041041c41608040502a40100c8500300c0c00280d485406150382c1e4180450581d00036070040c081084086a81c202101300c0d20b08000070b40310401d107214030200c0707035198045c442540c2d101e00c041045441e0400300003865004514011286514416854501d0203224040c803612509000042d5400c602c6e000340300f180c0051481c560b0518100005907561041c0d074440c020121501d1086405010411400203112280c000004001c103107140c40e001920808034200b0042140c2400c45c0301040340250b40d003841600d24105180041354038a1403d260b0b503004961400020b4807090540000247c1a80c4214582c058911218000022661a25 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 667744649 1250 667743399 667743409
    0x9080a030c020310050901060f09060311090702030c0d0302030708130c060509061201030b0f10230a03060507030e0106081f0c180b07030806010f020307170f070503120121030e 77
    0x15405880e81854140a921307481588030404441c6045045c0d0740407912110112b0a42e003062002805508104000300c20502c2d194403d1a0007404d1790044a20b009002c8a00904044c0e01125040120703074007008212485800007080707580301220481201421440399502e64000025001c0d1000704000461202060b031561383c12204401d00303280e00300c540c81da0b5130700d4070030f80809007100c2c0603146070a800c000c01c0c07450624104010541d08480c002a829901900e00380d240c80d106107804550200074090000040307142481018010b1110703640115900383d9a40819003035848544c4801d400b0f80c81104541c0c00344080740c00b990f00183d803600700414404402241203a41028506205032990f00c13902c400a10018940c008015651003610f0300e03440d030303541c5c0310065545184141840c40540c00800180000580b005081854291b030041e81d0340c2003183c958441d24003600322080072a00c60348009001010000f241010a006041c512207040c11801800ba0511300902a100001d051004404120b4541c0c1d0761 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 667745899 1250 667744649 667744663
    0x8070c080d0608070315060f0e040510140601030606091203030f0b03010c0c0c0e010b040b131707090e06062112070b04020f090714090f030a03031b09080a030c0203 72
    0x1021006000c030680350311005440313841c0c81c801100e103c088010081c1c826070707080c099101102d41c001c4c02030601900e815201c055501d001801100c0501803142000030000880c49074003050081e41400c0c062a140100026080f20401d42145040c400340300070411400035007144113600e4030703450700c2d004c035102900107044c2c805801950351441d815400c03c08040743d0260310130312440344d460040d000d68294a5940049200c01d01e400e02404c1c5000c44100300a2121040050003442c04244107031003440c0b102da40c0c0c40e190700b038600e22241c1910380707030020841040707140f605018001c0141e1920028121a0a19000041884801c140c0101d421203440d010600200000e003c528541840094100e0340d540b1986841d583c420703400c407000c0b403140d0300038240d001e81800c100833030b10f114031615201c24800c0c40c0806e0401000b80c010346a1075a0007003014046c013005840512800c40f03000c1c0309450105e5038a0002c000401100540f680c2c07c020482d407154108100400015100d03000354150401c0340032110240082424901 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 667747149 1250 667745899 667745917
    0xf06020408010510090513020d1b0e06121b0f0a1d040210020d0c060203060f180a110a0e0904030507080c100b030114240909070e070f08070c08 63
    0x88086800680104107402c0740c0d11420082c1140800d80f6240c0116400705c0e10141e400700410010341314201c005041403401e80d00b000d802109011450102c0300d060101d20040c0d41c11102c00300045400b80295401c1900b4609061000000500024412542c01c2010070040c40f4446210f5002101c0098207030300c42000d00d10282c41c45070304070542c2e40c103d10840e0200d01c9090f40d089020f4000000b56024030307031011500f4001103580b85d9903c81c0c0d00303510b6107480b8080c0d08050a00c5610400310100c41420396560004000126a84120580c0524264080008480c507010784a540c000301002082d1030300f540607880c0160300200300c510300f1240d1142d050444040c024240002c040d4440099101030012000030000d1a0042002d000e0016030449001d15003607d4000502c0400c201c160b80210f12018201a080c0c40c3d18404006a4206c4406550014210303aa05480c0085c00d508040e83c241710902004400552025160400c2c20b00d0002c2d005004102402c010030070000c204010211808000b40c200491708030395 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 667748399 1250 667747149 667747151
    0x6190f0e120f0417030901020c0a06120b030c0a030317160f080a0b06040305150610170903070f1a070804150e071e14040924090b070f32070f06 63
    0x43d840201d203540754010206c250143c400c0d02c1c003881c1302c0d02d44601d140f030a48510b680e410341d4001d28612444c0207000405105540b40c0600d0340d4940c2c00342ca60221060082d07001780c0e520020b901a04540002c0000c0141c6044007a00c0071014181c804d9400164020b0014034a20b80150310790b542001c0c8000a04103680c1d25a40b01d20b001900105000000420030b040030031180d4080d059484110801032a0340ca03603050100030400d41090441d800c03c03045501c4d50320000c41c8054034604419551204402043e17641c0031035080703801e201d0203801503e508901072b81c880c03518202a1903034102900c4070f0745419180040e0380c015644400d401c051500040c0300e490000c016640021944000000c81d00c030440c0100d02070403101e082c1c40c9540480610303041c02000c9030207030084c0d0141c03584490350080c2030300c100b13079900d201c211280c45001501c00a234480c52058420419943d8400990141c00c0e0000c08180c50866550000403014028041011406044c101c0c26107611050a07a0f4415618082680155501c0050065 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 667749649 1250 667748399 667748429
    0xe07030c1701060501020c04110f1201031703061807020a020907080118090c1e12080904060b030603070927050c12030a020712020402090306190f0e120f04 68
    0x48044540c140c19582192039180c000101104814201c2da5648215401680090700704211410594802002c0000d6118050701e03041b0031500740c4031701e580030022651020001c18010414080c080311500352101001c4101403650910b40001600a041c2501c0d07035400101c000003003443c0500800a441180d603014008075000e2921040140042d4801d11940484e000e400c100c01189101d21322034140310562100f50a80a00d0505001c035407140d0f4140000480e159001d40b001c240780200850141c4981c0c0f140b5041d42d520340d401300034403055445a0b0b01c0440901c0c0306000340810380d9000316886c810707100e02c0000090060110800a0106507000c04402014400c00c03a00700700f403103004038844554010a58040c03201003180b10406070303a0b201e800b0099006804c891001e00010038000110700520380002d0026043c01c0c5158002420140155003000f50100c4145007034184d087c40f0300071058483c45418040008640070180c036901e070070107010884031041001a400f400310b0300e868141c40103032102030281016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 667750899 1250 667749649 667749653
    0x50d0903080a120e010c030b030706020738030426030c16060f0c1205010f0305030a0807020106050616030906110307060b2808070e070f08070c1b030b0603070e16030e0703 75
    0x8050b03a0070400d00038040e064012410600029000c000c0702c10348041c085115030801c0c503446c43c400c6d5503201102001010342c035041018280d40055030040f80200e40b030700c0c085080304898170078120070b0511151030090103004100c01c6c071813c5030136030b213104241c4003000341c9015980c0340c11300081140e440c10181c81450410000b29903980101400b00900791a00100141d9888294400c444112484010304030f41c801c008031440140f0440b0030541008107400041130741794903480002c1e081d800103c51106441c0b0004400c1c030030305500c406a81e0040c500c0c2d081c1500d98501c074120703170750b00ca200d284e0002d00515203492400d2040d80b111448080e61000700702031101010130041101c940f40d0300f10320074030b5513301c82e002d004100b03084107c003100c1c0200102e03250204456007918054440000082c606030910941440c0c0d0070114001d54208220b8055400c0361509150540c5441c0d41c06a1001d45094007940c0010300512980c0545201c031038111400100b1146d041c0900d1008038013901c800d43c2818000d010b80c43c00082 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 667752149 1250 667750899 667750901
    0x403060902131d070512030a0507301e1b15050c03040c1a03070f051903060515040b0a030203060d0c060801090b030615190e0c07050d0903080a120e010c03 68
    0x440f01c10041074070350017659001005186410385c03140da1a260000c024030300c0c16030b004e10f0040243c1403184802261800c260f4003020714164000101c001807048121944040c10343c40030500c0d40401c803090300c2c551039084000c80149102d000c1700010306407c0c0c203040140184824855480b0460300041024005031030724004d5054140c1040e14115081007400d400414092240c01e003c45402c08081c18950a40e030300d000040300c10041c0810820f0522100300444018500d40340d50300e0342c0c0c1d010181ca0104500d0314000c14841724100c0c42c0c1c2c400d05444801e000c2445009080e43c00c64525000307519025850703440e0710000130840c4100134001404041c1ca10000a120f5400c15502d5049440102c420440181294240b40c0c40e40030455085a000042c0300d2501c03894607003801d904c000106109600c031102030710f401d150351907000162440401000040303011002c2103403c00116607202c101d8a403003e1064515525220180103034100c0341e00303200b00c6001c6040d01e401554400b401100c3c511000388100024200050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667753399 1250 667752149 667752191
    0xc03040f1403030a0c060b010c060f060303090f03030c120905031015170309040906020c030d05090601081606260406020d0501080304050a06140702090f0a050702060705040306090213 80
    0x2001c40d011901000385441c010040d94130100c0d0075225091400700903660500180444000c2905000c09412500042002446114000720f84003800145060443c200507241001c43d80c82080d03141c041500a000081c0d0200c10781c11082e9201c0410070040c69072a205440840c1c0c1c1c1c0d000503070988550f1030100d020a42a401407a4000c8240b4200500c0700c1d201c105419000000001e0b2110741d51081001c420103007401d61100104600894005040111404040e411903001548040e40942c56038241b00c09440140503e03401002d10383e0041101440d544140341034480c0e584121401d0100861140e101071000c03060702e91003481c4441c22042c3c145402d1400400a40201d280fa5418526002c00410400800812074013554001001403240900c2c229003240d41d469094040f05440405100400c0140c49820347c8500654010060803400d1420000502c1151001884e800455102000f44254141c10004079001c0d17940000c03021840240c180003180614452000c9404c2c0e1601d0401c0814174901c00c42412 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 667754649 1250 667753399 667753409
    0x2b081306120c0c080a02070b1917070905011d1518040b150a11010e060f070c0201090b22060f0e030609030d0b0a08070305030a0906110d140c03040f 65
    0xa035411000d10030314801142c1c03414124402140c1d41d1999000860780e0b010103400900c101344116540592200a8207002ea04544119014110000c01e16144a070b04581400c1d8400900c414071070141c904208010007000d00c6114140c107005515203030100c42e8082c80001900c1800103040d0408210700390001030995400041ca4542801a8200034141d518007402020000315000b0402c0350a645024a0b140245d4070880d0f100382407108013074001507008000e002e40c0080400460107000c842c41c184000f804802c000525410401010320704031700040c0e802a0420003600c144011075900e4208403c140c48001e640c503840740c484e400c1213200c0080c4842d4058009035040302d00f655001c041e51900d44c02d01d9900c3c0300a45513031905030400e10010101802a5021410802d40188040c5002e540e0b24440ea0070054644c1080c0c4544d040000d81000c220382001038800105800e103010010040d22610154450303200e160040100201400a083c89000420540d4800500503090340d07038556964070b581300d503200d841c815 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 667755899 1250 667754649 667754657
    0xe0c121f0b0306031b010302070c150f08010f060f110f0f0d020a0c090c020a0b13020f090f04020907031b09030209090f06040f29150303092b081306 65
    0xc003140210800341564080c3c0c0d0050011302c450859814041c48030300c040400c09041550a00814021410301303804400140100222500110802d00b03000f0903915004a0400500084200402034025240092821121a40340003906030304034920442d2480c0c8408030b8203100d4402e02000e0300040c080403a0b0484500a814202c5095820850060f0b80340e15107010040c00070a100310082050204d00d4001c00b0b00c625251041c1c0c0d90003041d694070a1140c02d4141c40c44091802a0b0710f00000714240002000011401128070a03074614040d08071401100f4000c00c001e004010560100c0c4005010750030040381c1c01038002c5200c0300d8584d48400200f69005a1005a106000100125010342e802040c0002284034240c0505040e070341d0350f211121458030302e5a04070f820810b107400a2101024059860565554104404001e42404012042c8c6030452500252081e00100611a560b41d606130080544191011744074240041240d10390b034500c000b092020b0304411000072400e681a462401d000c0c01d43d900360719 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 667757149 1250 667755899 667755961
    0x110d0605090c0405010c140703030906030506011407030c15020412020103050f04050d1803081219060806060d02030f0a0503070b01080106030c05011d120c0a09150e0c12 74
    0x1082080e91101038602c15203000e010002440954480c6010000c00c0d40101446995042c0301c1e649249080320702c0d8000e8001031100ba2051090a50601996401040929140203042c601c0d030003040c443e109270100103080c0180441d00d0380400000c0c40d059035044004003401c40d100c1d99114100d0a604850403005c900180c501000078043c200350910550007650000f00138003002c22003100685040c1c920280500703100c050410000009041c10000f40450070100d40140c074141040c0301d06002414224034002640c6080075002d016456001500303603801070046600e1000d5082c00e002090800d002d0f0b04103a022401401c169100b800740000041051b2407103012007052680e6141480c2e0708076495400010501080b0f040100180c0d803140ca42ea071304500c044500702285542480000b616200c0c0001c590450740c00500c2c401000340381c2a040d0000810781080184803248078005110f9074860240540411903500102003208035244505441044001400240d103500340401e074030306050f015030164075456036102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 667758399 1250 667757149 667757159
    0x18010c03061e0f0311030a0b241815011421060a030305030403030209120604030c02030d03020a0e15041211030721110301110a03050901050117100b0a0306110d06 71
    0xd207940c2e04550b02e441141c0c3c002401d507a241c140c0121100000340d03141c424007070150040340001c22481d000e0603060556410000200000d4580650000355080c410381c60350054000c050f120b10600740d40508158500c00c0c44810900040e0341c045294031042410a0010808410070b0038204981d03403055956183c03030100e030f130360303003000c00c001c440c412700000740091010f002040010f40130390058020580300402c407148100f964505035103804002ca8054000036043d404038000c3d410207100d8107528207040d26041d4902501683e01400701024503401034010362082800c03550600c4980145c3c0e0290401c5119080c0072401400d001c11345c00e20707000c0110f00c00d001300311001500c1e0102c2000908044100c01d202480d8401c01d803200c015404001071205e80654036050740300003500000c3c2c000c00804420380c80008541c00c0c607441c1c6500b1184140c128041e04000d01d04003072a034060002d542c2c841481c180344c0202d803911010000c1241d46034903901c001d081d28202604036020350701c2407002d81000e1084003000c1117841c0c3c0c1c07a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 667759649 1250 667758399 667758449
    0x3051e0c010215040c03080a030c0e0108151c08120108070608070c0605040c092405091b07140709020d0e0606060f0a09050d051e07061718010c0306 65
    0x844880d40941e01c07107410a0b6844246241941d482402881508400c541e0703a201e5601a074841024580026616914141c20320340041103d40442001c0c60301e20914034103011320380c000340c100d480c1c02032044880e000c0c2c81c030300d0031918810b110041d50b020407070980740c0c80748600000705400e0a0054a0103405120f10100349a031040108522488041d42c0d05c0e1400c1c0e1013512400020400500b094410810707481c2c000c10707601e405000307134101d0606d580d01c02c4022900d90504042c1280c0d4175004284145214400e010310281d0389201d840c031501c1c2e003001e02c503a2920180b074406001d58450b91680c0040c01013a00000d503258040e400781c410744001c9030f404c2c041c4592864205840c0c4000320b1780503a010509001c0821001e8150000c9e040c000e81c0c9040c01c000d02501c40c1d0014a1040600b082203401d60700c1655142c03016401d03c2c0308403041c500841c004100e80740c14001c0c00703800c10840f046540d0300d1380c21213400103c1c80566820002c402000240080000e0302c04000e0003005001a4002c0c000000c0705089001390410f12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 667760899 1250 667759649 667759663
    0x30a0506040515190f1803050d060e10060f0203070f0804030b0a1b030c030e060f041208150103151d0f060303071a060301020f130509010b0702030309040506011803051e 74
    0x484d1000c000310741042100f12008001ca80e520750032443e5101d003140c3c42800c050203080c0d0018020b03202c5e00d480d002101c941c0b03420b84034a5000141c2c0c1100103014408119200c0c400787c030503100315040100c4580300b64a4120301c1c6001e680005000d021542e0614024000000001d20580c0d01800050480f69a081c501005a1720080f075060000302d01191002105407082d80107120084592502240d2880000c104504c1d0450a4030501d02c80d01b00c0c8000e010030000c220010b40d803a0310850522042c4c1d8985503001d01d070342d4144158401d040c1078075100301e050000b90405250f0003070300700702c8480c28816107604041d1038104000c5a2000007451204081007040c0313030000a80b046a54031060341504400200c910303e460500184c407413038041d9024444079441c220810080c04241c02c01c4458009a82c0c0340c141040700038081a402014480c1041140a015860200071121040020354010465032100c00040b00d56051307180f080103017400c61140c084100710380450520582680004089881d40040081e2611a16 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 667762149 1250 667760899 667760911
    0x2010e0109080c09060109090c0302030105041802150d06030602030c0a030e011a24072406060c02060a0e0301150504051f171204090204092306120c030a0506040515 72
    0x400f14005074260300e03242880c254005410315000401c0c035a69010901901d01460b00313140881d402100601039030400d44540654400702171600c0506c0c079942d4003c241141e001081c5882038600003e502040b152040e0440307801507500090440d6246054000420302e03402090201e00020709005000c0ca15850501481c1c60341d00102c1550f207900c000610070401c0d0007c8a20003807803540707282094403107000c0100300a0038005004800d0409101255102054807407034915401e800645040c40900c4065440040141a141d0586001d0f640701c030400000c1d0b90700524000c104d5855800d00c1034000783c215205086104841e410388082c0070350b803603e00300d07441c40d44a5140c0722046150009802c01c00601d03003844440551b20031005560340741e00220342d050216071268120b900311f141c0000d030411a50415103e201002c1d061340e080021501b102c952640d400706400341c4018440e8a1000e003035144140e05200340c2010700d40007011100940c046260864644408840c10342d103500504980b0b0310349080340380c2d8561241d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 667763399 1250 667762149 667762153
    0x7030f05010807120212190309060f020303070309020d0c03060e010f0509030a0503041b1e0506130302101701080d020607020d1e0e03010f1406030a080403060f021603030902010e010908 81
    0x241052201c244038014540706903400303d2005074403910461b050040c0c20740290021105c14044d0101c1c10080c020902c0c5500c40810030084a505d800b10b1503012003035a41082003031801040e80c0a0500000756080715419000d03010540c281030000c100300180e4014111107003110020f00c4000080c0c0c0c1070404841d0102c86144007a0401c01410b06a14030450041d90302c64442c1d41204580c0f100c078801c25010040c00c1d008549003101001d00640c106070010141001040c3c101d50003480d080340e1580c03603000c440d603501c8024015030784000403080c907c0c040c00c0d4102c4613660740c00300c4200560f03540c0d0b0f000b070392504a29802f0002d409180c010646491006c0b444c0790035014161514200e400e514403586c2403283c1001110400c11010914245042d6800e01903d510140d442101051000141080c0412603201a120030301c00c0c3e0055071540000b50159094404482e0028000100003622824a4020744a030f05100d202c2140f460b2440d10405070180d2104200720300030f030b82d10071800c60190015101101d8500030b01d4016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 667764649 1250 667763399 667763413
    0x4241e030c120203011104090504051908090d0c051203071509020a18021213030206090f0a0b090304050a030c090c3b09130b161b0501020408030304060507030f050108 73
    0x1c03040b501c001d030705450310290001407149800300f0080c030b00d500260080040e80703845601b40310a02004010f50b00c8100c403151440031803200e01e980c03035071010b00c01c80c81014000c0500d50754601c144407400c9401c200401025010180403400803000035180d6010100440d6001190018440560564425045821340c0640341c060000d06100c01d040000100c400c0c903019498003000803010b2442000802e500800344001000d89801440c58003900702034004144180d07690115981c901d00d404005040039501d600003c03241002d0712402030712420340c451070300826000740c0400c40010400120a200c02c084901e503500030400e04030701d804125813450b580741890010030168a0002000403556200c1e038504e80c6030860f0034820411000100318010002c8400301d0010030400c0001040c0b04a403540e083d8400c1581d030b242010101c1c424130242000c6000090040989445050001000425070445019086da03004481e00da280c1841e001001c3d041c1120388000281c1082e1034101c2c0d0381c483d03020b254140c5072000c01402c0300e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 667765899 1250 667764649 667764659
    0x50f06070804030c06050c15071d010c050d261e090c0415330305090f0f010c1d152b05150907020c0f04241e030c 50
    0x940c0c104000c2500e956400300000000030ba001c00c00c3c000280307125241c03075464055081109003000c1e8803850700c0d6003c03060102040243c5d035001054403080c51510419401c25500e8030012034001d900f0403c01482842501d92002c99540c011440b43c8501c2e9074a90001c12a44100008441100c400d645c200c001d000700c142c0f01c840c0e81426145042e4415105800c03900056072520001e01583c0140c0d00c49804d1000340201402070406920100802c4087d039182021440d415404052143e5a04007455003015962004a07003450800c1c032803000c1d9481202d0403102c0040c41100315034000c000040b84000820386000805640304500b88001044117002010428200182c3c3c0e0071910701d034460810f12005074030440c200d186e51401080c0907604030424000006592500020a410214104681500c1506480c04110b0b42c03e60020b183d5400d00030586504110102c07210200d405490240d203614221201a10b8694140f43c04021141c1210311044844440c1d44210000041985450001030100c11a078201444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 667767149 1250 667765899 667765909
    0x150f010503071413110a0f02060c070c120602090d0c0914090d1202040f0e0a0506012c03100c0c050601060f020d080907090513110a0e061c050105090a03020105010f050f 74
    0x9880310004041003180c0c0b020040d1174650712402208012030756041c0c40104255042081681c414a940051807401b50303180c075541101801c1e0310440780030002c0042c522041002c281c0588480d46000341c50020840310a02d03040c0300b81607990040e007911a2601800c50b443c0e1000401e240e000d2004c64026000c84006c1c801d0407280d01d0342d41c603820a401c1d03808200c0000e1040d1030040c514000d09400158000e18101042030b182510340191066041042d030450340c08207040181c1071242071114102064900703641400100781040d0150000050440c9480d600d0659031340c00400101c4410311603c242c4150f6a01c402003920541b00034213036900142d03c20221050064000c02646400ca1441001c540310b4903510074440040c4c91086172015424034404a81c07104120401f010145040d0088814941141c00d10511800c6080010103880c450407242e07048101c101c001c00740e8074640c960820024451413074030700b0913240e0340c2c0b0301030300d00f100150f2a00d0300000364420050710800683e00001c201c2c884100040c01088 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 667768399 1250 667767149 667767169
    0x1605070b0a0b0a081c090f050109060503091501030f030f0c2d0c03030519020d05030601080403050c010504031e03051e09030c07090903110f070315020903150f0105030714 75
    0xf50080380c8440c0104202d0400c104414903900109184074810000365001440413070a0b43c4203d100034070b8400140a180e8208a616081c0c503000c0c0b802544036580c86441d070f490210302200449541024100200901c03507100001d285860103510b0700d508605d503c50040ba40030562030000b030401190150aa8a0304200101c58044908a12aa0f42046070291244080c0032120703403084011810000d461000d5404026421541c140340d400a401001c105d5440608548002014a8104240300c400a801c0501843c255980071156030001c2115140514010307203100c0032071030b501c0c80c51500400e050700200c5c400c0c01002d01c54065070010f0a1501d50000000c03800c080041e1850f099400140012407515100304200307802401e20000204600406d82400f0f49000030300220785849400c22030219654490008501d01265841001b240050521183c41c2c0028010901019454003c400d180120b12810144d902e006c2c0c101582d80d480aa43c2c1d4004141d0f840070340b840707006a01c10f40e0b201d00c08418a002d464103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 667769649 1250 667768399 667768421
    0x402090f0702012004060e060415210222091e0b06160b070e04141b22031e0f080325050c0f070503030915040b121605070b0a 55
    0x1007a44000b4201e001c0c2e54259051440c4203805000c14100101907007c13086200d800415650146402e00f80360491600b8a9400841400d0040072681c2e030007004000d02c443d03040551010310841d1100650600d2210300344005d141001104007518001c03990940a104101606d0012800c10b001070056803d4400a4003251000366440103040c06001c0d130300c50116001040851180c04580344070b2801c00009880240c0500c0442d00851402c0b02000c600c0e0140c8440358fc0104125803004654200100e40800c648201031a80d451407580303090303034a2900303a101010006c0d24030031200083c0204c003203007400001d0901824050080c60420007014081350b071b00401036400104044c088801200405001d9201a01100e03144e4005113001524401d4481c0500410000c000e486003d44002803800002955230300540c050b0522400116202c445c0c0b50310150215801040820220b984408028085c0440c00100725a080c0314058001141070505220b901201d030615800b42c6500480d44031030903a0401022070040b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 667770899 1250 667769649 667769651
    0xa0e07050d0203010b0a17010e060c25022d04091a040611030c0d0b0111072c070306050315070903150b18091501050607020103150f031112060402090f070201 69
    0x1120342944446c003a40002d885204103094281e00740384c0d402400c5803030001c0d8041d000d41100042c4201280b00200b1100701c01080c9903040190350381141003440d113095101000f5400600106001c44468180004456502e607240c4003100f1030341c4000500c02617581d4108001d18518403402c40c0f403912111400901c1c0c100d4010035001a03026040e4205160036881661400e00840010800001c4800700d4001c01030358070070a18140c3c52118081044995440084c0900c40c0c606841c41c101001407001d50701584407211141c2001551410928000390041406010340c81c0030707010740c40f2504003120715482554010420703543c4500881d40355403600281c2d0149800c100381c100e5210020341a42d50307110a0300c2110209150401025824584050351400000f9406032408800c120010400755070703403c00751480c0390340a00303021130241c140e044010400c8803e90802d8012a0010b03001009024500d90262407503101501d40e40d407805503100703503141d0340c2c041168020751010f01c00c0f0000760240140a070032500a40c107400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 667772149 1250 667770899 667770911
    0x3061508030423010c0f02060f070c0f0f0602060f010e060d02040e0d1805090c030a020405180601090603020c1903020c03070b031504050708041b121a0a0e07050d020301 74
    0x1895055500592041c01840301070350502e8604011440c0f000d0305400c00b42031100d0b8086099403a0392017103440d004007900c1080049502c0882c0141d0740c0403607400d1035000114010f19500d6072041d98003c9003500851203182070101010441c64000240385005a00c1c0d03030f4502c10180e18000050000e9400100100d42040c9568500001a219802540c2c80640b080c00034101d25140ca00008210020400c0d0102d140d0004007020881c54440001e40764101c10100741003540ea41c1d0702000308001c1d118a41c440d40d08403441c40c2c41c60b03040100d2600404d010b080241da07650111652204200c1c180d00034030b4240c90345904082a10360100d01808081d9540b03622900648603800484000030f030800703200343e100f0b40003a04000100000640303d040751801e1144c080b139041001c0d080580d070041904200400040000c0d45608501255880a1a2038001415042ca518410f080303145803407900c0c1c1c0d150307440300310a100326403011171000c940a004a400114440e4018041c0324a04010820818400f01040c2e8140d56500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 667773399 1250 667772149 667772159
    0x5062704170708030f0c2d070506010b070311060103020f061c021606060509040c05010518100309030f1d0d0c0b0f0a0909060501140903030c10050916030c030615 71
    0x26010340380d224001c1030003a40300d01c0e245001100080d002000c412240c00100a00d44040040c1e04010301c07440307c02000f100f9545c0942003404060310a00b800036103c0d11880c40002204a02800145006840b07079079984203e501d08043c682e0342c0d042c01e020096019072030403440481d905200e005445141c01408801c00c40c854010100e000300e80c01210700c2c550b003a0f4014000b5007404030b140142c0004142c16122210b56181584030211320b0381950081e00d0401500040c001d005000c00c542e81c815445000308080d210b5111000007074010403c3d580308501003a011007081000710b000316035004418411a13407485460503010704005840046082c06c43d1041060781d40070810483d0315014089201d030402046039a0484540041c040380300543c4110040d6083c40004e02050344c2c0003100d040c0d1119201003043e121742500c0006400c601a1440d0341ca91441401e090000e0001d00b5008240600100010780b01400304100442030751091501010f4041101c0100c10000201c01ea88241226220004104c071129150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 667774649 1250 667773399 667773443
    0x50d0b07020309121c02070e130f05010e061e0907051c0512030109150b04090f090503031009060501050a050f0703170103030c05060a0b0117070905180a05062704 71
    0x108a041c40765901544002258540402400c1c01c01034150001f082010303d05800030524800042002c007141821142060800845050440401c4d50200081c00181c0b0800300c120303604c0780103d4007807500d6180b00540031242507846070712600500840016080740c42c1030505100700141900c9608407802569040000403400500c43c009845032104452aa654940901c2d2030588a6415800542501c00c401c00c002038822082142c040741c43e03e0710040380c0450405010002090304400c050400d010000c01c0284412a01c0860400e44014210420903e904d40d0011640f50180000382000303d14100b20600525841d0000ba041f594824a00b0241c3c2030b40008515030507c0080e0300880208a269140200700034050110030741c07042d094641006900304180009000c0c1c01d4011081403200b41050104003003501ca400c0c100f01a0034042d08244180e001c65210707102e200b008030342d603940591401c00400c03005d00d840700c1124a005462030003c0c01d10b10220505001c0d13a00003034411175282c201c110f0232150301c03440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 667775899 1250 667774649 667774669
    0x20a06201305090a05070804031412070e150310180e120c01061e0b0304030e0303030106020a060e06040807151b05090414010f18020409110910050301050d0b07020309 73
    0x1d1111111030900d0030003803111245020341038140d41810f14081180007903110005603405501407038a20880c4464002d400b42d513115501000c20603001c00070400c0320943d00202d140319040d9095524070a180c1008805844c2c5000c103a42c50313040103404d803000700144145145d41c0042034880000008519207080101c918059030704c054085001c40c0461900d9600400b0b12414004150080301c50071140348898000d4610b000318000c41c44d0107036020011406040c0301c4c1416151800e4003804495403941c4902000c1e595160010044461500b0722a0a0490404c0400c5080c06942d20884c03081c2011290350350001100701c40c100e1414000d60b80d07284a2074000792390f422841c2301141038551a5071644110180019100300c076240300c2c45001c03440b004104450b0794000355012076052100c0b0312410300c400c0041101030300c119401802c029040a1024500d00c3c8040000c0c02c2c280d000b183c07649099542444141c88600003486000d9021900a10710350101d20610541980202c03548180c0389440721060020340d06441c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 667777149 1250 667775899 667775917
    0x30115050a0b04050f01030207060e06010609091d06061c060207061e0504030c1e02061c0e0a03050909060f09091e0a080d0908040e01140a0510020a0620 67
    0x280400050426000e40000380c40e0b40c9000914260900001c110b80344d090180c2107040640c0003612105125041d404030200940003004c1e60140d580d100001402258680070b4818658030703110041c0240280c0448d51244103a1381006440c80790b65400401c010f0080b0190b4006200c050a912100000d00510080c080d0a10948000500c2030802d00d41080440511414440c40f616050521001c01c0d040301d0120140780d0700420f030903c20720303c8003102d032501c411600e8020b400c41008100200035440c070460130940754900d01c030300b0004146a01c8180342d6807005c600c800342c040f6100b0402d03001d203402d103040d20540c0201c000c0c01003c6030325031900109440340d104440300c0700700340c002c10381542010383c40005030303029869014000e110405041d140e0110b0f80c1f0480500039212039850102404010030803066900a040d103000903544c0c8d40c6d440f014000182c40f4414803e1090640b2030011071207142141030351500724103076070092a96208903541e05d0700402038070460308060064906006c400101290090141c40f0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 667778399 1250 667777149 667777181
    0x120a08031006021506011205060a05060c010203061f0c06091a0c0a091e05090604112d071a070201090c09020901091d040f060e060709030201081e0a0e0304050301 71
    0x640740160081c10322a40460444207185131600b40325940c1e90002e0201c5200740e100e41c00103255199580044c0e05c150b41503000da60001004641140c0c0220198040c6d031184205940000a101c0d040d800180c400b84901c0003c00407800e186980004110b1a03032114a50700d10030212030144a4120340b8500c0e0000080718001c0c1140b13000105002c03655030040c08040201082681681e03014080034402140c80e0107800b589015014480003e000e0b03075a01e400c20f080000d0070702411a40c0780f00090903001000c80203c100c1405200b41840c916581200400b141e4159402a000f000c1003600918041d000400182c002400c41d92603042110115002c0741c03140d001417a00d0000183c1d42c0c1981c600242580c1890303800200052207140580c400502c039400e100c1d82c460340c404c00b130b9810449a07290400041030b012070540b141e4400c1c0000c1010058020b06901c01340c900036268002159249004100c04918008040f0003011403000407034907041c050340040300c1001c50a81901d0820380c0b900e000c40d00311a04090801c20300c0e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 667779649 1250 667778399 667778431
    0x90319051908031801060b04051009030f0b1e160c060e060106030f0605010309051207020a03080315120105071e020709050f06041d121608070c0504110414120a0803 72
    0x500460711a134400e41218002d01034145401200311007802213201721801000342030489054581300303c0858000c0d590101d00361000c034a40d814008500d030f40032a40c000c1c0d14080d215080d400007000c00c0902d4416000178440c50303103003085004111102d0030302ca03c00303c03030050301c1e207142c000b07480f10904c6018045c00c01d0795000a1070210350ba040704190741450f4426030500d1301d001034403408244086103181803001450b010035500c160034400b041d600003032540050300c0208040709000109032180c441c945402c0c4103d98650703240080500d02c50803900305892010108003480c6070310320b2241d0145100e560200715801a142140c0e036524103030003905e1040300c0d0b240c4001010010001c3da450144a440180b41107446940200c1c1105040079a0728030191300c04000c9040c0208001c45284043c6d2215150305c1d0f402455181c803401e0a00d482d1101840364051148500d0400d1500301d4091000800c1c0c03400c0711504101c0706007151040c13042c00000c040003c050803442c0690907116000c02c09400082d03011f100074000705052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 667780899 1250 667779649 667779661
    0x7030309030806040b0a03020402070812070f02010f020405060702091909050102040f080c030d0806030a170306041a150f0c0f060411010f09140a0f06020703110609031905190803 78
    0xb11800c0100054491444c01c0c0011100c1d07140c030303030f0310200781e03a03042d01c0059030f404d05401c2200d00b0f4015288a4102400344208101070326910031180550106650000d120740390220300b449050f80141e0194540040c000c1c41a4009440e0003030b100d541050f4480300400d06141030008444c1521f011260980b0130743c0d00018208403829150b00340b03c1c010a078110161860700c010700002a00c40c81c4450303140041081d40004110107607400d0100604036a4401c0700c2c03072024400d800301c01119030401c450861046190103009101c1700694551a680711a001344504510351800a2030740b00703508510b5400009460501902c003685004110005c541c4406900904e12481c0c1460240601d00b00c2800d02ca0400c001716240b2500c0c160012030241c1903070082901c2c1d4001058040100303220341d0303003540201c2d8041d030680c200040303003070300440d0307841c00d0300c2c010007505940c10b0001c024080d1030b118a00526030194000c4005440100070403d2100601d4412016500301100108608495080c125001c0c0c86041c000014000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 667782149 1250 667780899 667780907
    0x1407260309030c0d11061605011a06190c0804030506190b0303071103031c0507031505090406091401053303060103120207230120120d020c030703030903 67
    0x4009010a8000c600c0c25824801290b111403e0078205805000500414001c000d40c61085c001c42c0754025003540c1d02c540c00300e00e0a00321803a0540d000d842c07551900d001001c441a100b0488424010003400061030018903120040c40500300b403861030304000c40c0248100000c1e9001c07000708000e50081c0000c06a42c1043c0c000d039403100d02401e40010256260820b03696850714080b05441600743c0007440200410010740200b401c500c51010109695004024081c85607003e030391003240a00c50543d41003001030240c6107410768100c524022a0f5001d11701c0d1380007800090150308202e0529110300512107200f0b074241c40c0d0a0035501c0c1562903017030070b02070385144030303800341d180c00406007031440011001e5500c010150110782ca031807041c0070107803141d0365100c59141c01c140200017040051103024403ca0898949441048800300c42c10001070006070800000c080c0201c45081d500c05090300c60000c1d11070310300300c2e40142c401c641c004e80d202e404043c1c00f440b0807401082b0910140620600a4901040c02d020030310b8014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 667783399 1250 667782149 667782209
    0x60c0c0319020324010302060304082206020c0a0602030f0924090f0d35041d0106080408040e0a0b040507390b0603161d0108070605030a02071407 64
    0x6500f10b0840d2041c030001d03410b90a113504407501514115980e841d81d0030301170304500c10241110f50451542e1000948030b5074014071b003401c48045500343e81080311710340104209440244600f400581c8140180260401228010000107000614a1700380b0b51042c00c941c41c0860400c0e00c182c80440001c90304d000e0f41d04098440b5003240301300312070300350f840310780c0b0756824440c18540c804a01d00c800b0700c3c440040303440c9100180e4400c5a0300640d049901d0726507815100c0550212000c40200040ca01c0c0c0000410703601810245000d140e1010703100b402c040c1070001c03501c083d075001070220f00182d46550034508141c403140b05050059a80d42c0e5601000649241a100ca8000092050714a541c140d81281496101301d00d20b0b0302c0483d880445102d00740c450301d00180c44d1031103044d803440101501e2900001c0b410400d205034244103900c503845040b660307038078141c0503101d001500c03810021440400000700034022641c01003170b81d1441590130115004c4024007040c90075036690820700d00b0384482c0d01141d1200901000302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 667784649 1250 667783399 667783423
    0x3080a15080a062f0a02070e0a1505040b06030f07020a0b160e10051e040b0c010c17070c02011b05010e0d09050a050d061d01110d0c0c11060c0c03190203 67
    0xc08442c0580c0712041040103038a000c054134618020070840c00d0140b09001c028010030440f11514043c1c20290789401c000d04540b0340c200d011a4101500107801c2c10b09000d1a084801d0003003d450840d81e0f4840341d03003107150009004d07000318081d0103200000540750320034982c0541c0d241d6007980240782484101500109004150354403445842c121180415440011243e904046180c000f40c02c0508040071061402990004000c141021034005100e0178158003c01d0a106541d43e0070708140a00d02440481c0300c41541c0040003d0340c441c4110b0003550050b03903408040c0703100c4c554440ba40c201586074982155020303200690980c01030055a1030300c6920441e00400b42008940b29800e20703103013000090300c1c040000001880300d03480d05c00e420b1030103910800d8108500038810083c4114102000560081c0e4400c44180044500c0d2940d0390792541c0c4203d0942d286141d0214802c904102008100102038020705119032091080406014094909200e510fc2c451038504600303503c84a18410981000d4a118034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 667785899 1250 667784649 667784681
    0x15180f07080c09030703120903050a29040b0a0504111e1005120f0901060503120706060b03041e05100c05070501050108061003060911090720061303080a15080a06 71
    0x525070f19a80840d5040840ba07000b003030060780e2401010151100c014582c0050014022140d40030705110700d000d1900ca400da0007108000841021120041d04c403102510050041100540041d210078900d42c00b2540003070041c0c0720741c29500b041c00000740340b0410071380040a4038203151850103111b00380001d02a201006a0418074140300700c40d803945e508403500414a444005804010a84030130080d4800c80203000007070107a0b2403200003241c91100b96032240404503030181c074114002414806840503207005a6010318601c80765150703101001c1d0032001b821010b4529019207040f0301142c00c250b120b43e030094a61902c5603900c7d0100d42c1411404c440c0c1c1640041e1054004200300b20341e1100c2c035145881a1390f031000300000ca69409081c00c0c46140030340a1703000e40000c5031000744001542c2040702011040380c07601c0c1c5c9104000141c0d201c0d07a102d080c00c0e50400c110b80d465602c4440080c1c01204090f511010000c0c001800e45202c1543c4035811030a41d00204a9800a101c04400d00010780900d110031040781c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 667787149 1250 667785899 667785907
    0x9040f0f0f0533040e0f0f070f060c060b060c10050a06031a070c060c030603110f03030301210507090504050618120a052a01061d15180f07080c 63
    0x420304290418120108203016107440d0f4800c074800c0441c940ca16030000c040d00802250314902140c0d903481140e05408201032150b40300f607020a03080020850700350b8550a0300706012a00d80001559403404e40042100c45075126030322a0510b803682c0c0082c0051018030401090040b130400d09010031a00040c1565200f0f90070304c401400805d081c00d004500d04002c0c1100c1d096070350b0341c01c0012100825031000040c40581860b24804111f85e068202e0400c0e42d015113195042c41c1410310800c02146600107c45426401c00d000401400071039a0b098000c6030407005034500700c144555205414420280c04c140111507480c410b120a020307041116a0740440d8580d120703001c4041020f5455907912600c041d0180030040094602ca03a9803141059800d90360248500d407424911540d4000d4081d40c42030f40042c2c0540c070305140080c100625000c541902c5260030010356544c0c580d81001d58143c0ba0381c80450f6081b810302c41d0782c2e4140ca0b040d104450320840c0c030000c6658560030700c220020700703c0c0c90181c444501050148 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 667788399 1250 667787149 667787161
    0x103061401050f0d05090c010e0613090b0a0e0a09031709120304020402040302091005011d012c1804060b0d0203060a1d151f0b041a09040f0f0f05 64
    0x103250065032024201161078048155000700d540c882d003c1803005850a10080c4004d0f0b0308006800f41100c40241c07900e41c0300203417210501000340a691341c40c10200340701441c1009005210340c8100c1d41d854020346904034498440210707a00c0c40000380e5800c0d10281da0307003c200c01803551115030140c1e28007080740d0100c42030505414440c1c0d55510551141000a80040420f0840d0b031954121801594041c00910701c40c81c00b6810340700075440511420740410268110b8008440d07850f246444500c005031602c052040741000300030401c0d0565400400d402072501e255003482c0da20582e034030303111241c5188032418a20307080c60403105480500c0d14007402200350441600040e50302040b00c3d6407016190f2000034000450068490540301000c40c4c002c65401600e00038196101940c1140344164140250480302024140f1204485042c80c4200b0407100300600c0240f080403c01a1000041200f400255042025a50004088500c86482c2d0070400da034803803103545041400c2c0201040c11503844010010340c0f42c45 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 667789649 1250 667788399 667788419
    0x51e010203030c28020309040e0c18040c03051606020d0507020907230a020a1406010501050703050a090906090f0c03090b0c0901120c11151e0604020d0e0318010306 72
    0x107800c0c1901400f01040302180d100041c0455501d40000c018200c04100140c01c020351250f000503121350055050081a141500000400c255801406080d00404c07840c07000c60044421406041120300c1c616204c80040400c2040003800910b00006207041c019519181002e494008100c56480600006200c01d002580e43e59140d20b601914130305244016480480380102d01c1c075001d0240c0781040f0404201d02c20401c0d8009600480e0610800e110060303680c1003001c2c50f603166800d200c2d090000700100700301070000784500041c0011341030303d081c0401c007241c8502a8006540c025001030074034a6403154000c0654105001d5401c1c80141802c08218040c0c054991a03068000105200125240080c40c06200d92203500e44226410422000f00004a000100202030141d5592000314601c10380d40328080700140e0901c80e80c011010801c080c900101c1c1042e44401001e801007846500c1355003408800382c0081c007406210000800c1034081e6646e50815416a424095204801410146803100901c000e043d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 667790899 1250 667789649 667789651
    0xe0c040e014b0207050d020c13021905090303040f030b0423060730050a0c020f4612020706050403150b13090506061507020103050628051e01020303 65
    0x2000b0b18036001c5058118410041d201e4054028400e00c9071161200f2007035404aa01301c0002d5044440e1610352808420201c180e00546241e552448001d05100070f0b01400f8400401007428064156400c0030b1340e8240f4162440510790040c0c0b04004100100700030480c1c0c5000041054195001c07030000d00e1085200d03a40d48040c02003c079810f100181c4144800001e0305181c1f2400005071041e01840700440f46401000391000b41c5107089001e0606044000c000d00201e84d44141d0480100180003059103001b0b400e2101d000070000c0071300c2040312611001c00e10b0702606c120000c40742120f4420311000341843c000513404c2601c0c000b00c0440d001048107020360741d4001e0031030b03040307903002102800101c80349280d2000815038021100d41c0702d003001003481100001500810350a9000701d0a44810f6aa560140913807050036500074643ca00041000800643c0070740c0c02182c2154001d8034507611a44051150181000044448040700e02050f03410080392510986400c070f5608046050042020103100207542c07800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 667792149 1250 667790899 667791011
    0x11040e1501090801020a020a02211f020702090109020c06070201180609050f030a020d171302091308030a020c010506030c032a0a06031a090f0601030e0c040e01 70
    0xd2030100505403a03224034540d0026210f0301c4021035851541c010040e60fa1340460034201d0158820394080700424410100c1c040700b08514401505004001428020220851000e98880558280f0030100980c079011222070103010104030041c0e503452042081454124024201340c03c581c1440f941c14415003041c0c0c81000425032141011401a0941c5002821314a89920b6250503220100b88900d40304da00192001481e809500e840e0354240d410b0000e88141d800c00c0310450707840c02c154281d007801428100005d80c1e00c8480040d10030b4080d41503540b0451258001d0750701d24022500480ca44000300d50070b01c00c442d00000c00301c1c02031250b10302d0701000c83d17104c0e0010b4054502030300c140880404512034134080c078003031900300412030484151103c0c0c0240050000d2012601d1004034920348003207606040982c5402007006481d4074005a84550046000d0030940894902074081c0c001d00407419100ca01880498080f80d4001064840c095940c3d4403080c0ac164072412840000c02400318506102d038405121141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 667793399 1250 667792149 667792171
    0x80a110f0d051b0406051009170105100b0a02160b0d060f0810021b06090d09090e12160b13060525080618040b1005220c030608060f040611040e 63
    0x40d0411000400520307142d41b0494201480d40c0311698500c0d48400d0300c074241d8031f011001c1510448a040141d08a5404030746103000c40701d4a241c103200048508010b09002403061040b0b880040d002d1900142040075544420140e801c0410303541c1040d9800d0140d5409404540074403440c0e03d180c031000c280c0d40d18000c02400203640e80040c29800380045c490200000e03030704440488184d41000d981d8165174010140c441e60003c2e54100380821250b981d8041c000d11401034000909141134050030b00d0b96141d02902c014030345030100e8501440003503405402640f0074051621101c0e61200c45092610554400904030301d4102109240907143c058428800e02d040c0c2c11300d19020a2654541011440036100c018504041c42c03403110030441000702103507080b40704030705a8558010b183d94070814050242e200e06c0041980900c0254005c40c1c81c1c4041d03214000000701072401103411650b8007060340c100314080c0d07400600d19084400704018840c85000e0080201c0c5220100ca00d09850070407001503041c1c010300046100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 667794649 1250 667793399 667793443
    0xb060918090c1c290f090c04181202150c090d02090906040201030b0906030a1e06020a0908060606121501021002221208160309080a110f0d05 62
    0x2100401a01e4000d0102400c8244520240300c0451010001c00e4000c03036210700000109000400c8050315004c00481c40307a0110303030988603440c3c070b034014036002440c01681c1c0c0300b0000032500d00d950740c0c028465080c00011168a0921290901c911746007405038481081d540305624105448412184190b0701a96444030187c555240344001602d0f1040c00340040e602c0385982d42480110130000c40d903140500d200362405c0080b00c3c00f280c14041018402c6810982c150402c640302004110040305012a05da001c2218103100000c594410303040340c20421751540001e481c1c5601b030001140402c04e454010f00e044032900c0c10f001003628421000c0400030110402c40b2020745485003564002c010540c440404c0050654445001401c024211440c0e0b0500200c280600c602c001000040707021602256504954001c1c03621024020105040c2c0d16074408078100110a400000d2501081c0703c02c0aa00344551140140c1d11a0001000b000140089810b8440c00c44000300c2400240002881d00340f00b0320884040d000d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 667795899 1250 667794649 667794661
    0x33010510110c060319050a05070f0c030e0310060303140711040e01090c090e071403061f0f150906020d02060411010e060706020d0509030c070302012f010b040b060918 73
    0x7040e45181d040c907000f0304080140a0b0070f024000c058401c401c2044000c10441d0742e607407000c00c00c0e1441500c0e040041032403000c800708003170311031001041107070f010b401c280c0361041d20100800d1a20601018030111155562414020550300c90002000030414904c41c5080c84c04030744070403541034030b05105e10707100c0d55030340c2c40352111480e0070742202d550300d40c220340b070005c13056a547c00c51405401c0050f044a514021440b001c48c0b103180b0500811070507800900280141d40c0c4000107501306240d4100342242820001c04000380d041b0320b1114203000307400382d1103405041e1179401002030700c1c400882c2c00c5401950884030002400d02d80c00101d0301c0e48140c1000c4071200030075000d40141d4544000c0c9581c0350300948005412424001282c000f01005000400104001d60721814100c3d1030340910200f2810582103440700b00b016600c1002000f980741c2d608901e0040d00e129200d00c0c03850701c9200c60100b13481651500c0540d2414074113441200e0314008140c40d254905141c1800145107043c101c4054550002c0381c002280e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 667797149 1250 667795899 667795903
    0x3090b070c0e04110a0504090312020705070b070c06080112021012230405071202090f070e04022704060b0a11030d0e1f18030f030e3301051011 63
    0x1400c0035155240e0b20704081c1810b24084003000003481c021800078000260303a041c544121005180c040c0d0b928001c4c51621404280607600100c0150380f135114052000c40c41100c1c0700000d184a0b40b164081c1c914191401802509802c1d05a02c400c0211040125880c090384600d4210800522580342100c3c3d0340d640302c0000c01c0188451031202803041000c00507000c4c01080b581070280114007036821510415900d0803420020105004000d411840e40c6001c0703407103419007074007003900300803542004406001c0103004141241c100c0c051031042c90480034041c1c10340100480900e0618001510144100e43c2806520800c03031041501c103904100200c011400010380c18401c2da1180780320900e062080d88030003400350740d036110f4820340720000d40f41c824580250750b0281d10800c801d410b030302c424170b01c0c00001a440642d50407000c1c60007a002d1584aa003902407111080c0002108088407210440180c01d01e4284202080010900c640c180c0840c0d60050085a641204498507006a860840449204180803038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 667798399 1250 667797149 667797173
    0x40605060901060512040c0b0c1515010915050d14060f030606061602030705030f030a0801090c08040605041e03120e06150603091011030a0b060a090614040e040b07110a03090b07 78
    0xd804200409c01202225000c12100074080042c0c0c149115a00d404540b910042e50360480180840c100d00340400640291801350079881145040813803e255003044d40c841038030740b44801c4500105441081040350f14040311001c0203504142e000700600d140540224039188a00c810500808980c0381884c1e04541e82080808041c08024094444482ca04d861441d5650080c290320408241028000300d03940307909114002e81d280c00b0340d84902007a101c2d41c9882e001010080d00680302c40340820620316060150078000701b030961113a0b5070284c480a08521810071504030111a0740c00e40c2107a002d02849001015082d43e86c0c072401c50b407803681c2e901c9544003589041d00e4111802035a50a01e1582d041c0b20102ca00998801c60020f4400d1101900440800090b4030031320701c1c0305c4080303001031105112940c481e00d01d03101d045e40140c1c10140b0f004e4460b0b50380200c400c01194216241401e800400c4080756001c41d0201107044944000d08949011f50790150050181d805110503240020800809028031401c0603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 667799649 1250 667798399 667798409
    0x1081513150e010b0f030c0f040b0c0a05060106030911090a0207151e05040510090302120d09020411041a0a02010209090106020c04060806070e01050c0c03010203010608040605060901060512040c 85
    0x8008050311414218001d040a209081c821440e000c000101458008100e600c286000d4919500e9980c4040c1d81c41c80b82e070003441030b030740c00d02c01c05000104899015500916484105000030080084145421460089c0c1600300f0340800d810600e1500000f00c50001820078110103c50322401641c407030401c24024000d060740034003e007040e10000b05070048030307070701800d081d030103001f02c07030749481c44c20324070581a02c01c2998000c10075400b50f41503040c0d071509030740100039051181c17046d180d165111001089485d04481084c2d100d0ba81e55514000c1145403e1103050b0548054100250403d49403159007050400700c01c0e0800d46031300b4006520f00c031051003941190210040103014880350f50f11140c00956404102228034004c41c5402c501090420001900603c900034558819000152100c011181504030100507216407081c40c8150180d55800c0c00514081c000981d00c0740c1e51440d00e0704082068501c05050180120003000040c0120380c1d01c101101d410203079a10564615468030701e000d4102511a5000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 667800899 1250 667799649 667799651
    0x11109040f150b1209010c0503040b06010c0b15042007030c1103071410030b03070b0a03090b3d03081c0f05100f050906120f030a020307021e01081513 66
    0x408070f03800c030880e405081111040c1500c03841a44d50409814202c851645110000c940c0910005c0c0018901c8206103502c042c041c5003200d8071508542d0303804040b882c00c0d12018011074900a401c49281001d21818074003850400c8640403002211441c40c85a105182d0b020f020041c03000e4684080c800392040c00c40c802040134040358170b013079641c02400015a14000d178a501c0346919002c0034140700c2c483d0251400110005014020301da1520341e0302d00081e8401a05102855154100000810840c89030b02c0d00c00e5041020803144e1002920440c581c0c06d0600d8810400c0e120880c130300e0b1404c070030080b0715041038942c0800e800faa90010145d40b1885094422400e1250a0401405001141541e003020b4002c003a080f5400f0a04c6489440541c1110460b010b4183c0000c102000900b55180840e81070100f84207240036666070641440070541160301040d58140540e20005a000450601d01b6103022980405201e0100701407002000070100700026000740c2c80a41e060484080d255102180d42401160780c0f00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 667802149 1250 667800899 667800941
    0xc15190c150504020112051b1b03030f060a0f150309032c0405150616020409020d08130f15031e06060903050c0604080d08100e01060c050f011109040f 66
    0xc1c01201800d030440d000c80c0081d581c1039805440c142c1c0360141902800d4081c06121a26403030b64001d8007140c110750b65200001e560051000710b0a0420710080d4040e0900b00c042944a00d03101051050b8090f440d8410f602a04182d4410000100905605c246440d0a80307400309a00119050450304041c0040181c213800c0d00800248888020b0148641b01481050b5070900035551161448000210b030017030200d0f0003400800039076151007011440156928801071002460003410b40100b0702515094000305e4038264006008801242c07101c0c0c0c5d5000600d5aa03102c460018141a1a40c09000a400700c030340074180c0f02c1e074201d82159001c0c5010400c80000341c000f049040d46d110300003480c0b0b4415200c01ea40d18050f02c8946c0c04182031580440d0103039a4044010840c5041c0c03200211000360005158a03c000d800081c0451002c00340d00400d80200311075540c20110244600f8007d0900b480c200d040000c41c0c0c9090100a03819140409a4805503011100010b4401c0340032098005064001c40b2210045219a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 667803399 1250 667802149 667802183
    0x12030906060108070516080f0d140f0a090f030c170a02210307080f250c0b13050d050d061e06181a03040204090f050f0c15190c 56
    0x18200c0e2249400f40e807560003640304e0640a03038852090001c00401e86a03d000c0c0c61000ca01c0300f4004003400d04003030541d0b501c0e00442c4004001214210079040c00c01c1e500d060140316100c00d41d40165a0482100c1c0300400007001240e485105c10350701c10000405000c00c08113141f06000c514200144240ca010003200e41c0e44002c0b1400940b101c180c911040320b8441e03000403111003600034000792441810b0340e80750103c040c3c8804d0200e000d011001410354000102c490b044031b2180000c659891001d851076110654519601c0c80c00ca10518030003440804095407200b600b001060300015048078403240e900700b0681d5211840d40c488040d207240d802600d81c9518056081075041140300711001250050764602d02005240c01d141c98200c0380510883c220f00148500b540c000c07441c024021508284001c10009a051150b510602410f010754030a40d8982c0007143c00303000c030340ca051050b9207090508680283d21660700360070440a038001c007412070714503110180c01c1d90030403405011002d44144d0030a00c41c2c040c40b442c507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 667804649 1250 667803399 667803403
    0x9020d02180916030b01050402030c04080a06020a09140f060307050403170c011104120204020901030b030a03030e07150219061103041515060e150f0d0203010f05010810060f02120309 80
    0x981c0e003064280f05202444084403219031002043c2c80d40701025103000c1c1d10381020400a0b41000d4902d10300301602b08400200c0c03034810010078142900c2004050384648403c84d01034490007140e400109070300001003c0c8410365079841c02402c1c0311581204c803136840e41c407544400c82e07417800750390002410b00704405a071003503042c4a84082d1564070b140000038031640d0382840102e5458080e51061514402c84412900018605600034004548040c9400180d5a81d0100040c0c600000c075902a0042a030741d181d03003c103822041c000c7c0d40240c403d05040103500d0b08405402569100803812200d51082072103174030010088660015510400070000310f075180d0904d8145011101d110710084a15589003411188540d001201000e08941d030f25150b07465801426000c2c4807520030304c0100210200020400009905081c001801c4801003010b1700503181d605140428107600000c0d0040c605104000c01001607811035500303804162245480d14280c444541c880680c0350042c1c1c0b207442c3c8400c1d58007204204d199080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 667805755 1106 667804649 667804651
    0x60b0d1a0c0f03010e1801060b0f090f0604060f081302090c0318010f0605090a05061516080a0507020103051006050a0f0509030d030204050907050c0703030309020d0218 74
    0xb0240c800d20391a48260440c2540d00d11050a011030360340e10714409500c0c801642e0003080700c0b504281c2c030a811805411440c02512000041803201a103400d001603591030f1000c1c0003680c80e10745800c0c000d40360f03a80126603100001c0900002690083c0e000400c0805160081d0900b04162211002902c083d4001841150341c1c0c01c00d9801c00c5042c21092040700000081c1c080d000030350b01e00b05001c00c411900060a407041c11401d05040c050b860383d69004071030b00e80049200c0c41d0fa9070007800314005031b6031303809207009488020085200c004240c0c00400514529200340d804000c01c2ea1602904514107025010709000114240031118003240584c4c03064000c495103003010f600300110f520000e4a08404540c807a000a40c0200d020085810300181c45500213030182407050828800c9078920b40d441d03810f480003804044d07c0b107521b9019234591003910903940303402403c69840c00c8030310600c0c0c10070040 = true := by decide +kernel

theorem cover : BRFrame.Cov 667625899 667805755 := by
  have h0 := BRFrame.cov_init 667625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 667625899 ≤ n) (h2 : n < 667805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
