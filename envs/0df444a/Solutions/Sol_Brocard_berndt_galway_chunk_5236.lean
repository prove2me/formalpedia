-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5236
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:11:44.442198+00:00
-- url     : https://prove2.me/submissions/c7539133-f852-4c1a-bdde-3a4c7d3eb6f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 941546762 ≤ n < 941726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 941548012 1250 941546762 941546789
    0x3020a1103190b0a0f0606020c01080a0f022803292b1205031e1b130e0c090913141606120207081b070911070b061203090d0312090c 58
    0x1c03206100e203d480e06487e4070390001c22504507202d00554070302c43d00410400080b0b445801440703d454aa0000d04000001d000d00c10703055404030fa01011b000c810307218107402098034008021038800c284c40c0f4160880c1c0c240d9203881010a1003100464900d00019640001c81a40322008140d404800081c10f4051405070036054a945d21210080f100c91000340d0307154441040003012108003005051100b41c120b0810800e0080643d01784240311016004048440303800d100001003004114180b07408540d000d40c4024005241100880c00076440c0c400c081c20102050507020030303000030011a10801c041c40407600f0b04491115005070030741c548a0220b4000c460004100c96000c158202c00381c02510030043c0d0140c13249090480c0744446100e04803007a80031101510482c0e60029640590b40f02c1d800c0d04042001d101e42d0303140c4483c10a03150740701c0701411881c0984013801e90004034040c0481540d00446040b280000108018101151601c451b00340b030a2001703203455600700421015208800c121030443d504c900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 941549262 1250 941548012 941548031
    0x40b0a050f240a1503020c06090a051005041b180f14041b090207050309040e03070c0e07110303010e041a09120f1207030501080106050d03020a1103190b0a 68
    0x4a000707000d40c0d89080b58009546400c858540d0403140501004016103061441990340c0007100d01c10500f08a818042580002c80c020980c01c24041d00d030b4010070070802001400c441c1d80e192656810b1a062807003d81c0d40d584c001c03030200a90f168103050b14459840c0da4240701611001c0c9001079034035480251101c9031906640600e0008280600944403400581861480e50307030352030311242e03805080a0050225081880442c20001b41d10180440c507008900541d200d025900a0000f107484940102800f58070500405001801c8521000c0036111600440d10080d225418260364502101c0c40030300b2540400310020500d110480e48a6110310b00030024500451020b400741080030301d0a540c1c0c02d610382c00085200d50510344c050010301c0103081c80301100740b400d005550141181e81e42070f03c0340c1c1c00080d01c400041040c0d01c2d0034003c60002d131031304903401954400191f030043d550703502e203001c020039081c0c3c070002461007075a0030710241c0c1c003449103031444c1503012600345042032502030100c6525440c145442041d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 941550512 1250 941549262 941549281
    0x603190e010b0603040209040f02150a020c0f031b0a15030b0a05180406020702010516060c0906030e07060c080d09080714120d1d0d090e090d09050d03020114040b0a05 73
    0x308580c2c001d006146142c4a6030280900000014404d0700c4031440c0201600050703c0d410392030702101c0c486610030354070b03014080c03030081c200050481c2c558030a485c11404000d8030703031300403491115100c41c88840302d9508100c0320200700a5100ca602c40c480c0b00c41e542d034144210540541105e03525210440340042a41e445030104440d81490b031360851750341d403141c03030010b80010900d0303004041c3c0c2030050400c3c0b4100941c2c030501c4064404420710031a151619105407508a50b040050100600103d0900380400c1e4030a6070141e980300c00e14820481001840800d2400b8810b07a201164480095000140050095800d10039040d038010141145c0703001918600203c0100046a020308441c0f104140794035001c40c40300c103000581010741c2843d030b610207050240000360501300801a105440b68441c410100e2410342d20203030105005000c280550040080030840c10741c408240c005407503048a94091406031418124014440e1442142624401c5020f10061018961503e44100c1e4001c80c140301c29580c000b2003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 941551762 1250 941550512 941550521
    0x703060b0a08070605130308040324090816030c0f03050a0f0507170f0909040c15360b120a230402040e10050a020a0905010c0c030f0309050603190e01 66
    0x103804450304419001c1c4081172040004001c1c5148100da4441d20703589980f680e2115074070a030300c101c80101050300030100a00055090140406c0110740c2082224450380f5114180d204091500481410041c1d0380002c1500400d0031041050304117403e44607072201e615018110b68840e805207400f180c60001200100c40c0300d001224840c0e030f4007065060459001035100c1106811501034440c544c003007070000401d503495440c8a98882c0740103107044100f962806401c41c42d20306c4410300100400584c41d001c0008049034506035640c0401040074400d1040c4c3d11440c00100003140e40011700c0c0c107000021001040b148009400b8003460062004003c104c007043c410704148103d102401000c8120700000401500d0b055101c03102010400040d07034034405452220b142143c00483e454010540d000c50464820340d440024007016100038202400580b0441c6c482624081c2503100003062600c250400c03104040c450b0321500300800c00607142c0340d00c904112100f48000349a0903401c10f84189444040328880505004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 941553012 1250 941551762 941551769
    0x6110c1e0105090f1203060d02040f050106030510120b060607020d05010501030b0f01140111030913050103060b100203040e0c0d050118050903130614130e04200f040c0e030f0703060b0a 81
    0x10012804083c05d003030b40f01e81000701003075480f02880d01d144002d40c036140243d8607000d50b00d000001d420760403c1c034081c0c116880031702010341d02c0a0500b410f0110084040c01c0ea9696500058095219614800010766521400000030741010b00509841c041100c15000703076040e203100711940f42d4942e0310394806d1141d443d024400e94068105484601e9040d5005000958803050a40140d07854075170041c01060b1100656000a4020341d521801001807180034400c0b200e030840c049501701140d1a41420082da24003890003a008410201d03004142a19840004c0381d12425981c0310900c10380d03030346002500340c0c14030482800c3d42d00741c14040081c040450100440d486c000200603200207103400e200b01101c10213146000390419100070442e610342da200218042c002008000d860070907e02c0c0030319140900721000d5070080c1d40c104155036842030b41d596102d03089083d81020345000444c000700e0700c9c0407241c06030b000c20303001d0f094012082c80d102604001300b403c005480c081e450038880782c40c2020900040000e17921 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 941554262 1250 941553012 941553043
    0xc100e0705191715011e0302100512012102090a06180504050d0804050d180e100302030d020303010b03040605041b0e071704020a060807050f0307030209010305071b06110c1e010509 79
    0x7030050101c185a00359101c0260410418006c855840e580403540c540500441c2e039000c07880101702c03141c0e403083c4028594090016400c11500c0842000b0040ea8104402d120085c82203043d680011501c281079030140c0c0060a034403000741c03144810082030030010301c01990243d03214010191071462040c0900162801990300030700030300750701010034030071100d40c0c0e8280440d1600101d80c0c280040c524002105090040030000550382d001031461040602d40400c00030000305542040c0010090141d4560581e0741c880d4001502041d540c1d07403803600818603100c0d5001030002c5040c40c10042040190030580c64030800503038071000900031980516000021044800035402001000140240d81c440d501d1550401c24900b0881e0600501110180b81c58004a03a0b001c0041c1d030200c1e074400150b030f16009154000032103040814560b0b20b842150081081e0050b00a0055503c0d003501018588401c02107601c9191400c00395403074501d88109100304007030348003e107010a60078080400d04140c8081022000d4a4a40707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 941555512 1250 941554262 941554303
    0x60305040f020609040b19050a0608010f090b040204091a04150b0f0a0207080601060c0302060a050c070219090c031a0402030f160c020a03080a02070b0c100e07051917 73
    0xa81c03c001159214000241e0895100e0342c070480c003911985030038142d110000c1c4013a04030504000600c403460505074095800c000c2184010480c01c00070079500c0c01503405e1000049424501000441c02070720032680009803a615048441050a40000311140400000c42d070034000c030303c400200306a840115014180e13440c40100881c4604120703010041c01904098010748060aa0700c1e540e084c10042c0c00d9101401180c00346059208042d07040c090a030340004005010401400c00000c03902c1c287c00f038020000d0040c603100c13850040d00700441c0ea845004204100085c408555000e00050151240d030042d17401954184004c01411b1400e4000e491040000d0401c24045541d40c09020b44485800078425081c8005c201c000b00140c0c644406080141d401442007983d14500100003e20f066000c0d031002410b8901441452213264000c518000d60100c003c0c4007040f0003215103001410b00ca05030f840380303610030342810342c1d20200310301416105c1c115903c3e03d1468070ba115034100c4a40d112034110080041c45d0150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 941556762 1250 941555512 941555543
    0xc0207051519090f1412030304050307060b010f0f0825020d1101051e040819050307020c241c0606030b1003020906070206070f021525050a030528050a080106030504 72
    0x861406082000040c20341b07416182c601e16890459105503002d4500d07030000074000051080a019010180e80c0a20740b640c80b002000f540242510440340703d0000f04000d0001040141b000b4000351a404d42c1c40804160100e42e40200203907407409a03070030b101c0120b580410349191001041c4181c500c107c080380c1000c03c0411210400811500c0000c0080f114610140b01008902c54100350701615880c0355110190b413420704900207031500003c03103403961103030101982c030f501031000c0c80085d0031051140300b90894480c0e0344500907110920404200c8020503180a6001074410751503005202086801d488216080300159021016441200f50742d41d00081c08006141c010f041140c001c00300540107219008032070350389900007a414001121300f130900e01c4021400e6600408804140b40030b40c400240d00101c018059640d05482d0a400240941801400306d4000c1c01030351190364400344000d600382d403000d607003800c4c040150043d04410041c5000440c10800429400c0c000d1007254000c2e6001060300d1030b504603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 941558012 1250 941556762 941556779
    0x112d01020708031b21010e010b070309060315030605100e010e0112020d08090310050a0c05090d023001060602011109060711190e0a0b0d0f03030c0207051519090f 71
    0x4c84004244030420020b0000c0c05000030720011829542c801c0c07134400b55140c221422415041a0010300c00c1c58010481180020b81001c65041150750505003c25404000f040000c072103c030551018200f11f00b000100000070300b1031131096003621007a00081c080780e44c8a040d0010740c1142409142c22040d0381034010400741c64002d401e54100740c460490340d86030041c1c0c0b1020078209092240c510300c249441c0d20038042103440902403000d0328191843c10074104170800002541000c0c84642c00303801040c08550f60030080d180000074100070300d6508016180710011301c0c951030007002e10b4447c13070005528003050f08901c02084802c0340c55681000300301c0c3d03052a41684803e11042581c82e00194004003596644800e01800c0101100038450b101400c00381c0e1520400d544249c408031950341d4840c500d81080c0c10000f690308480c9603401a01464001503107080070383d0603440c002c1e042d0081c542c0100c8401d0702403102540c0f14002d180805d480d0140444201c00403e0650310040305008440c00c3d04001003003880800c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 941559262 1250 941558012 941558041
    0x9090c0703090b0306041e050702070e0c070b060a0801020c06151c030315090c020f060a021201150c0803190c02070b0d0f021b03071b050a050103020703112d0102070803 74
    0x40300184000b4801380c2d09130300e5a44501c0310340c11f2240d100d0b8403103081000050301417000400030442c0e030203084a64542205040050300c03a102004241e2018440803801070f4880c2a00f0708064000d000086544040e9210083da84820807600150300005141ca1000c8a04041c941c110000504c0c1d021603c911082c0e0f902917001c0d03d80f80391000b40c0e0303500d1224009031080c442c0c05810105c1255401070a1141940d607480d03810060010300710300c0760900400c180d6880c031240c10030b03107411070780140c51298100940c0035040b150705a108101900201c0302006100c1c8800381007894000c0100d00322002c00c00c102e203030703242aa20303000346d032045924000b4140088000b0350700310780007400d5958100c00c0c0189818043c0c1c42100c141200280c40100d194000300d030349810488203404890f2034000003042590420700d0035002684040d1103003e501d0405070086140c00c1014001c9040f5110400010140c40a1050140c45003c0d080b01e10101c60442c021580d00f0300c0e0841c0810303c202e034a05504a503213070f4503550b203c3c03a0004944 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 941560512 1250 941559262 941559271
    0x90402070506040b18010203060609040b06040b0a26040b04110d020a030b010305070807140f13090f2d020f18100501030f0b03150c0d020c0309090c0703090b03 70
    0x25020000180012401e110140c840ea114003000300050401c60104080a00c2aa504200c9a8810002e0000540d80c46007614050181120302140712003403000800c0b80f5002d55407200c90441c00120f54455020703009810101500c15020044d00e01445d108800081480c050700c000d0000300014000c600031402c0747c02e10880050000e0201c4c1c1101c50f2580c045013103002e59900c1035581d500307000c0040c020403409110b07101c01410303408028200c45c0d050105452840244211162255007549903003100c0761100301032100340360790401c4100700034402410410a9000ca240302150f142d003c81c56032200d6282a440d03081039900000503810460500c0c1e41c28009004100c5040a91100c042d820410764410742c03d03109071240e40307441100c406072450800050150f403041030100d2002410b081d8845841e88002a202c000c071910620240026112001080c030284901000000325038000903a060b82c20b880000102940001513035149540c1c0d0324a40c40d008240541503000340099107940c3c040101e03c88410295410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 941561762 1250 941560512 941560519
    0x50705091504152601030203100e01141608071d15040317210f07081306020c0313050d0809061c0914060a1b1206050d05070f140303070809 61
    0xd05498140c8141c0e00ba0500c0c0740580010303001d103042e4100310308070301d0002d4014500d0f0440130119411a0b0009496a0460400d290000d40d11090103d000704250800c0e079400f41c0c04242c061903400c0c404510924600115035540c081100400030445a5124030182080c240c0030300e8000c441d0103516820020070801c401959542c0b00c0b8203000220100c0c031101c3e03402c241c000d0b4030700d28266201074001e0305511040c111111b9908609552040011400304001e9450b072011540c544440c580e034619058a0641d519404081c101c3c92000c1a03a020003540000101008001408001d0307400c0d07a50020171400c0c83e15030100518050041c4150401e07405c020014084100c0e02d00d00320f0810040f040310031011900e0005040d076040c18094400e00b40660244440d9810a040315414003045400002d0154101d603c01420410080c44524202000920b0741c0588081c010081400d40c180010303003030442d52004a402071015085041800064403140b4011901a4000103001356041c00000c0e00c4e40d48254000075440c0b0b80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 941563012 1250 941561762 941561767
    0x5090c071b0909020a080106080d0e040e1527030f0901090e0a0204090c050a1e180b0903060903070308220b040f12020d09050f0103090b0c030106120507050915 70
    0x1800c003803401c9081c05001c2c1d046000803002c0b402c0c0100040c0c00100d504c04015645003010510506001284164040c0d29600b00b0041c140d103d0000300f00203241800ca001814043c94094000300c000c48000c00d4052500c07504c084006801901805220074800e04445845500c10408008903070b010750090500418141004000c1c542c6d5550004a514000c4a030409116400542804080c0c2940300703003210404245055410304001120181c01e080c0f90150707107984400100340c80b4038140d100740030f00c150107030308140c07920281541d03000b0408054100281c450720038000c00c80000c01ea00000070036540742503010740c0c1305030081c3c90f50803c008178950520000c00010100c2c405c0d41003c00c0110706a94011480780b2139091300c100346400c01ca611700840709911003c6403c42c100348145030f5440020217064075011541100e0f12040000160000c1802c0a8002d040b00d07a01000c0100321299040618121041501c82901c003400c0b0040c0d420442d00111100404281c050203030b0901801c1c00101048200f01030341c070091 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 941564262 1250 941563012 941563043
    0x4050d03180b120a0506040b0d060603140d0504140103061d073b04232505030f0405010605030708071805040f030c0309090606050d1505090c07 63
    0x11508062684140c000c540301d001041000c1c60785084003002000d101c1542800c01c06241682c01100d83c01a100740c2180780c90381c0104016941d554409010038000600311000384a0500c0d00d100039100e9403205441e10840e02d0890076040e400840c460b42c9902e0184d0b101e44c901804d012603298501e01c1e9105560416959210114030707096289155041102c010341c413020315140c50700e4002c2803004040c440c0316103035035010014400c041031100c0c01c1200603000d0000c9680400c600010900510112012100c401500103c5002c0c0652046125001d841c80e0110041121007000110780d9614448440d800014401c20000c1d110a59852249800c04d10034400070074021340e40d0000a10b00503103600700c591160800f1104102e1723031011500c0c4c0c100c007111101040c0f115140a8503417100e07000e81c00070094140092500c06908142c03184059034090710b0415410421036455580c000e026402c040142a40c1c60310706441008250b0f080d000c050b088a400402c0c8025540e83e6503058006a0401d6004451800c848180c0c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 941565512 1250 941564262 941564269
    0xa020d1b06031b02010902060405010f02010b190501110105061c050a050106090204050a06020a08030403051e0d090b09011b0f0c14030c01060f0317160203010504050f0c0102010c170c0405 82
    0x110010070003a50b0220b001058030902028003031010300c015042d1780c90305a0031300c0162a00c00c01d99003160030034207118207072841550f0f042c3d02401038500d400f45c1c4258034080f46560000301d9585202503982c280e032008000680c01988500b2604150303006a408036040c050312000758420b100382d02155108806458000d0440c1e9a82d5007074079516004030707500640204040c1714900f40501840d00030a0302d03200800c000380741611030010340d101c043c2000d020048001844080100e1034004014408116084541c0e00c28400c400314004040030001120707004d501a010031002503050040709a1244002201200342455000030b640003120620720714244800019207402007144194070341005641030000d1036a483c00c9480407421150b441c1c0041c00c0300c1800e21030620101b00f4882d1030100c2c012030316410703d95481c410800b1210100e00351000035415805d01d0b0810040020101d40000441b00082c21105011145030042e403e07200802c40b0342d400183c1c00750519100140c6c40300142e4001c1110101c2904c0c154551020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 941566762 1250 941565512 941565563
    0x1c1107030c0204360b1302181b070302070e101805090111220609080d081005040c051e2b020405090708070f090605030c0d2d0e060105030a020d 63
    0x314014120300101c41c00e0007103105a00ba800603d001000000d428031f580000c0403951441d407203421104481000400e404c21400e819400404d91048558603020685002540c3e66480d00981e12080412008181e525000020b070f4410303184140000441e00d43e19882d0003008204c0107003101031940d2982840448550745600524107560501c4424005180d000e610500710701c070b154403220800100c083c082008410111f20003020707001c0c03490500e070661100c918500c0030010640045601a240000070b8182580001c010f2001e000400c90101c00c01f5155451410b040c0203d8960a0ba400c041c03c09088000140d411020041d080111005041c55150004142c50030022102c03980401d0502083c010316503040304401d00141218a0900840390409400501c140409010b40106010106d0350400004043d0481440138070301901501c2000c40d00705500c4000200741c02e200f0199403a08020780508200440e0030703410303a030b000b9005140003041c0744c0c2840a00142d8020640b00400f4a141464546200104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 941568012 1250 941566762 941566841
    0x605060c0c01030e06070207171203100602240114011416150e0a150f0e03041401050c150402060c03031e01050d0f03051c021c1107030c0204 62
    0x7082094036010014040781c95507801503403aa400481000700301c40d4009106000d9552240200c18240141400d8924201c900142e40340005004010480c511001c07400020481e4829800c27200501034a2494005d501c04268403c16140c0c0341c0300051003036070040a4001c00d01350042c50140007921038800000d4003500044c00c8103d04045240d40d000610455900300c00300e4100442c0100030428901c0f0469642d5840c5507002000d102e240448501400c41950180a107400350034014004910b480d0680d58696009001e49030220403031602040140d403041050714080c15980c0700030950303d01c1d070403103402d50514024403c80c1c0c00070003040903010100090000d14060000c00d00c6050044044e94500c058840050300000d01844c4c40d0500d601c0414050301225014a416090990b81c0790007040510303c0003070041400c0c2c141e9600005405100301c0d41c000043e103616000e10b00c100041c840c8284102c059206003100a80000c42000b89400135180030b40c44070044854203010b03c864640c55020100b5000c20124 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 941569262 1250 941568012 941568037
    0x51608040806060429130906020c07030302330a1b082203050304030c032006040b09010606050d0b01350604180609060905030c070f06020c060901050a03060506 70
    0x740115402d160290980c440ca28008600c044400d48605546006240300c1042c81b80c0d94500320721251003c80c0d8860404180c204400755960060030685a80d100842d01c0101c0041c45140c6a05004c0300204071803100c400b4405101600148007001c0741c503007065000e040c515141e0b50742e0081c40248400480580d16091807902c80040900d0306c031003141c1d41014022200401c4c03083c86040c0c080000da00c24100c0f54060760504100c104104142411506a031f44111411449240c25402009036800041c126104501c980900c4019940798401d1909840140c443c05012135414001c004500d00d20303411035801e2450600d040098508101c030b444043c0400412990951a0620882c0150602e40c41c00c42c0e0388070380c0a49051081804852104004101c0301001505095030b0b0700301c9904004450300407140c1260404202d80d00c8104c030b034206948035062480783c2194191000c0e00040e442c0e00208001504640051209040805203001510140c0c0208c007500101a034a81b004519036860300301070040c035007040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 941570512 1250 941569262 941569273
    0x160c0801060f0e0402010503041109090703150903230706050c0702040b030a0831060216080a02010503010e180d030b040605090105310903031b110703030516080408 72
    0x824403801c45070715030805510004005801c0c411240700c0361206410a80c28601980d40e55102c0c1080142c4104d01c4640641c03242e03290040c0720082200061141c20340780210740d0350488074900b0101c08100c0d404103d008000c101c03880580b011100e803011041e84c402101e0100c19140c4041a9200c4045440440d00c0d610641c0011500c032095017000e104d03425010340250010001c4845030749a03c103003409a406500e081014480004150458041c190b1000c440314058443d14079880d500e010b902e45800d0800b510001d5054040050781803070010310302e1301085e010b845003440d42e401c10880b43c030900d500601079043d08040b104c1e030322402c0c0c004100103a4004403541c4e0001d8600341d0182040180c40165205034031440c080310040c002c980c2e030b1481110307102e409442071010b0348c041002240700d031320702140300d41c40818178040c0031800f0306405403c0f940b12102005850712040b00a4034060322030810441840200d540f081c1d40500c000390050000301100800340c2c11030030140100360303900c035504d91042d0001c0c651138000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 941571762 1250 941570512 941570519
    0x30903021f140f040c05060c010e071211090705040b0304020604080d0801050111010b0114090307030507092a020a030e01020c06040915121e02150d05090609010b1003050408160c 78
    0x40c94081c6030031403440750500c94241003917240c804031002e19000c0c4900c1200700080b400c051590940c000d56940d0b0204045e10070701d513078a00e0011465244103009a4551092841102c0c0031318003034907824401d10164480d14246420700031310090383d41009000700d801520030003000c034600f40708010200351002c003580c861041d981403000050241014501d5007000e03a0412a226690744c0e00800800d0520f603130106000d031110301e1000043c0c0382078a95400500326026114010490483c103820220341c2c0f100d01801403003c4903c025001d00c408600650074801a0008150300300000d1140100313000d00c100520485001000e4400041d031180e00c0703907001004050b511101406c0b0b024204502c4002400301705100000340b01c0c0d46c0c944c0d040340110700310644510802c5141200456503030b100340c8150001c0c041c826603162840920f81034010303d01031301d450007284140e0700010b003003900500551103001005818840610ac054078190054070340600201e40202c2e0030f000f0a010076944003001d0004d5405407440600b141d00c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 941573012 1250 941571762 941571791
    0x40207120e0a051f0f0f021e0a08040b070611040b040b030a0b090c0c071e15050c0115030605062b0206040b0c0d0809060103020603150d15021e1306030903021f 70
    0x520795900c1c424450011700c900d041ba40c002c5151500c100d510300f240c91407040c0318141c0600701105081c005116500200300803461603814005488800d10400d01000641c20742440030f0340d1809a44588402c00c18100024030080c007425000c0c5401c42e844800c0400e00456072800240070300c500315000c0340201801700700000d038918100b111800810348800c504207271040c1c0d05c442c1302075148280250444140c2c1500300d6044503208904030380741c0c10004030007002410034084603410f1892541c801503c0b10780c10480410300034948002c0740310b6408281c4943c24034001107840b01401140100c0c60aa901c01c20600c4006810400e0700b0042586d12407000c0a40215840881c010b0107080001d4000380035039110500501c0140c6031030048035007140b403240301c1c03100740c648590024208419201c002400c13080c429101580b8100d840c3c000c0c00c0b140c40070491449404090382c1c200052401000c5050648a801580801a00d4020b9000045960013403050301e03442d02d02115214441c20400c0c034102002903681c106191041d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 941574262 1250 941573012 941573027
    0x6090b0703061d0114060c0706080412020d0c1403270907020d0503070507061805011407032c16030c05100c0809090705190e0a05040207120e0a051f 65
    0x90b0402e90700c0c0f0441c0c80d22100c0403403030b08140241c082c040324200c0180e10325030364401928440d55806049036841925007d0007018400e00303071800ca400368070480d054000c81c1d0011030219080030301d0307940713610403003400e901c1e101421898124183d40c0e41c0805c02049001402c81c1c0d80e40d419030b1022030074915003201e440341070102403d001000002190401e881002c40c0c26480b90450340c003d01c0301d28220b44c0715141810600001c100d4403070035205280140010004100c0e064009040c1007424030f60b41c1034075907039488068080d58a5641504c81340307110070b5140504902600380b900340301c100364821501d030700503600d4001244400170780043d82d204d500c102e401c00c03040c5080104011205198038244803110030540d1100010701030130f440325214a0b5854009181e82d8841d8091754024580e1032014186030146040203041c07440310705440b5018540c00782010a2600745402141e003c03c2c0d00035402d104601619104075020310a480d001580300e442c203200080e0941c0d6038080b00d2085a192143d1038100c1325080c130702401c50b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 941575512 1250 941574262 941574269
    0xd020604290f09010605040c02160f14090a0b04060f0f0b1303060c0c051f0e0c1f0302190807080604050402030c06071b03030c0b010b3406090b070306 66
    0x4294205040307074000114402180c2280302d440b81500e0b15103542035020301500c026086580c01a16102074500d01660004440f8100045010420320302902c074600c2c414104802d000e0301c46840b02c080c000c6200c074101041c00591000140c0c00c000703200c2c14040000340554406612900319080344c05420300010030080148070090011009891600195004500442d8024800a0030341a84c428200502782d002c1c65040507079645c8401a42c5d40015052240d940c1e001c886d4801c0321085140c440c1000210706c3c00103149000b140c008100305242d543d003688554000b0304514919041607024400e0b8281e6107a42c07040880c0803c0d03da200c00449152a0707800501c00f40000b0490380c41142003000788409620302040c40c5240381000d880c3c5a69440d180c0c1000038802c8002d00e20181000e000e04000014164440002207400d440303032001a2059a132090801040c0c02944175941282c100c50041003108a603803045900622001c0c0100080134120392903100071100d07820ba00b504c58001481c10080c081d030f414400c88014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 941576762 1250 941575512 941575553
    0x4090c08011d010e04080c1f020d0e0a020d08031003290604020307090905130c030803010602070503030f030f1003050d1d03070e06100903080d0912030605031b120d020604 75
    0x944c03400f06568485400030b030000d080d1420004d0b06c0403940c14181300d844040c4502d10003d620031640d60301010029480900340f441e96500d04041141c9114001c203110819940040c50380b40e441c01251135030882c070f07400075101080340482444000009401c0d41100300c2d41c920b0380c0030328031005c80010a800d00c00150051100e48114410020000802d801000d48001d9440e44000090165954815504d017071001e060082c00902c41800c00004000d020801103041c2d800035030a94032800d589805042c1d403800b0341440070038605010301c00100c3e4004610201c5502001c20190360441554036110641804100e105181c0001c00c0100140303a180280015103c100e04140d0003400d01901c0c144007001d01c80e40103031100340318217941d00c1240d5180c1c1c4580c035808041d42e04802c9560380c3d0b0071840280c500416164508507145006880c40b8054076000380304da00708030b8102074003038043d40a0b00340c5101036041c0506200d47c1e0014100051561031482044100554800d030f4005069608150620180d003040036924500c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 941578012 1250 941576762 941576819
    0x1201020903060105100c060903031e020912030a080408130512030d0507140a0e0d060c020d0e09010e070c061d012c0c0603070207090534050f070804090c0801 69
    0x101c07170f94060140300c815504200c001445030132903d4203c001c0c01c0c50004400440c0b00940c0c02c6500c2c4c04443d40100541c1c003048502d41c1c81d82e8080c0c0e01483d10f80c080c44405001081c1c0c2c2d60300181c0032410000040250141420008039801d40320400150036002042d4209034070341c40455412069561032240c1c641107102e07030400318044d00301011500350512403003151500b08000b11440a03516183e031520041950384c0039a0600204020311301c02981c4580380228900062030142c0c1c40051400d1030003030b060580300d85100350700b41c0e41e548250990799420740450407103d0b40c0e907600050481a80440d02141080d03600000400c022000741c01400c2980c6001c103600610500401030721401c10000142c194801c0400d42d116900c035585c4000c142d090541a0f0b2050300020308050400031422084070401400c94602c0c0010048950183d0400103210504412240400c504001001040c0000c80240480e83e1066400a140980310000e030810740726100e20700404100480700610004442c1c0e0a0705440b00c981000c0c410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 941579262 1250 941578012 941578039
    0x30e0304032d0b180f06010617010906061d03032205011713060b01120507120501060f090b1b0703060c0f1d06070c08150108010f0207020f09090102091201020903060105 74
    0x121503140c09000214803d014440701c1024140c1170144040e4a9044001e44400f03617920b00f409050700743c000024410011980d400869000058401c84d03003500c0091703031907682d04900d001601246e00010441c0990602c020700424115042e14203082030029000c03440f02250500c0c1c031002500d0403480c1c2c1389500c00804002d00300240b10040d5a4190056034200d100454816420740c01030300c20307121140e507240f52141000c04020900c3e4100103035141c401d017013000c1005180c0c2c1e1110b00712000421a0404000521524000c10030903204002030191031604840004d44a42004840317480c12100e0750044a240f92544254501c03243c010f0401140c80034a42407030943c203a6144400b181c2c45251082c10b0340f20f01004941c44051100401d01040a00021030071240c000c844c54405049049092040005542c20980c3c100000c0c1d00e640242c0304442d07070141c0f100007213040e0781040140652008210301600d41d800d010060280da50f4841d900c030052004000140c0c0c621410381414100031058008502400c40c001064 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 941580512 1250 941579262 941579273
    0x712090c23060d0c0c0503180f01141902010b0a080f01050c030103050a032a0501090516060e060d0e0a15140709180905070f090501090b1c03030e0304032d 68
    0x31205107003043d10024003401003800c2920b0446040c50060300f50f2101094254801c52400b821401d0108100e4444008040340d00045601c84908403d40344880310030700c540c501c140582508814040450700000c10055904008505018600e070700c1011103034400405280070500a01c178603900481301c5c00c0c00038659030441d05c505607100701000c0b000f01001552040784801c0d401c01d00001c1e04c01d03195811604800b2407141800d40c060441d0500c117852134001e200440040c03001e4241b80600f2642c15485e41000c8061603000c0101c550001112180b0b0583ca482da0391180210500c820384c1d0140c0b1503040620040c55a101c0c55040b1614401c6143c0340026580500c01d942e030304522444200e07070006515648800c02c1040c0d01300a01022500184140324951010135860102155002602c1a0183c204440d0b0390756042c410070b4541000c44150001402400142000300103d0382542d110701038100032481048101006185610551041d100c4003660315421158039500140c1c0151a80955444c1002c06440c0c1c851 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 941581762 1250 941580512 941580517
    0x513020904050313030f0201021504020a060e1809011d120715021b0c040e01060e010515040806010e06100c03140313020405010b12060d0b07080712090c2306 69
    0x20384281052000602040b200b041100c142c0800e60f004801e013581c0d28902250740c019552030403405801900d1501ca920090300e624a482903400070051701d155490014152111039040410b03030382013440f50001c6900000c03000c1e02d050180386550b00002e135480c511130203480c0d074038a20000c4007620f400c405030480030b140b6032405a4030402d4000349021101380200360b100e4000d1141040c41220b031054a003250b40000f10204e0940c5400b01c007600e0911400c01c4081c40306080b0380d00c07170103602600c007114401800541000307003c0031205100700244d5454507032101042071070640241e0045000ca822182003003410308080010300c5401072a801c0260507000d41daa40540901c1a03c10038034401c00004c000180c4014090104010b090340207001009a540c441e6051501070380702030100010b110160000c1880d904101c180d00c1d42c0150044826400303074542003002c952172507010700500c0c200414040c000c0481c0740c5d03910528080503c940ca419020901e086c00c0c81a403501640800500300b5403000e900c00d55030f29003804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 941583012 1250 941581762 941581801
    0x506010515071e150f1d03191404080a3e0f120303101a04030f0606050909030702031b0303180d12110601050303030c0a0c26040f0905 59
    0x81030342080460255591a01d40d0301d014241020348000b13200c4003034041e80b0031800668504028414081140505001c1c089134410161080c1d00801085d030f648807500424640307030080c80c60f00340c00e44407051200103040d0704641c00c00d540d5908078641c9901080a40391f00d0040e45082d04150040c011000c0c0500703c60300c03070344020880c40802c1e41c100c041c005a07100351030030350904030040c08189440600010035a0b250403c680a011490107074101040784503d1565810403410804105403410b81950b4070b94100c00c81405007110201d03102d603001320b410755070f065103d80310340c44200c01161100b02600401d480c01c81022001c0c902e00080c98a400e400e92004000c88451030f6064104010311410707503000c501c8c42c68420401402c0c545031103c41d5500107030f00180b505102178082e411103110741d0f01c0301e003055200d100a07545078800f00410008074207654058400740030143d000b05038444042401c2e082c420300491088181c6500c0301c500050078000383c034036614208094a6040800c2009240c03094078440b424040d1070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 941584262 1250 941583012 941583023
    0xf0c0308060f13060906060e0f06091918050a150f050d02150307051905090f010e0d0501061503140405191e051c05030601090504050c040905040f050601051507 70
    0x2103070040a4507107400c07811100f8009002040525680d900e010000c0090340104000100d4558031034402d4074041e03140200441d401881d181c03401c0d004004111010404041c0165905407600c40051350f0f1081e1031030140800701030003000c601d81c600310401070300712403441c1030702d00744c16150404c207110602c2c060700c03e24180d500a6400c618068400d00004504015000e101c100c00c5100100308030cd020b5100016102c011310f50041001c002030f000350265950301408a600e508050b090a00181c6580b05207940c281514000d0f03c056094152a1030303050030b4445503004090f902110140042c041e51349803041e0f2041e203104148030141c0b4106030707807401d40b20100c5c1a14090040384190420041c442410695032910200c00190100b410407840c003a80c466070a0035181c00c0c0510440131790034525020741c003201c1c85960141c0d100402ca50400c410400180b10141143c03d040342e0510010816072413912a45000d103005d240d0b0002c01c54940d10305103142c0708050f0051805150482080303214052200e00792469035a100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 941585512 1250 941584262 941584279
    0x30f0911040e0c03030d06030209011703090423040b010501180305120306030c0a0e0105190b0a0c0503090a0308180301140408160f0602120a0c0c152a0f0c030806 71
    0x400342c2514058090b912280c1c9408000380e01c07005911282d0201d42107d20035504101e90703070380e90480000c1202c441841004240c00400c580071182c43d181c0d20280d8400800c50940c0e101d040c411040c01c00484080710100c07203021014005001e5036800c040801c407842e140e910700300780e80d90440d510300ea100c0110b0000090900380200101d11659424060808560b5001d000031842030350f54990841c80b07142c2841800c0c0586881c042c14640070884e10b480206440c810454140b410041c0c0608980030703180088161003500060200006641d1181000c0c001140110261a20380d40591345001581e041c0c110b0841c4240e240465241003e40c2034140164800d4001460648521410940c64005801098000c0965940f804044204003565001d800111141801c2101c1c0c2d82d04c1e2010642203480b045241d1b00407405010610002941c60a540280840c0350b10b404202041a03002001c4941c88400301e038050016070000c2102c01c0d6501140d115086025880c040d040420780d610f018017a03100c0078000a0091030302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 941586762 1250 941585512 941585531
    0xa020709090c0e04030c0b0601050a0e1c08030a061d070e0105070c0b040e0f06030111090d0c180e0609010603110f0d0203060c090f06030f2e15030f091104 68
    0x74007003540188000001080c3c1443c2600e8000c0c810b0590740c0301101e040640c4000f0402c1544910181c4e20745404a480340c0b41c120385490100b190702d014640800e011745100481c1d24001458034030140d40200d0350103c0120350982400e0200d601d80e408681101c07000c0d079000003045161640031049051481003801c107140c0d900420704050710a480141c00100074501e001400260300e2140c540281d00c5600504030b804a9600e40c9410542a00e041021001c0840400c0c032641c41c10380b07020810040720a2180141610382d65481560300c0d4a4202d04c0e078a4040c0740c2d612004004100020b2004640c0504545c0c020089035080d50385070042d4514144440d4002c048444809440780c4958a1460400750000c040b29070510344403015a401d03a02c502e0415001d2244003020680341c0c100320094038052110081c52201c1d80e9038001203500c070380c02e0b440e88450110812008161125440d45080c2001e40044802c03000c0c1c3e40d90510014081c2c0384402800d1003c64a041d42040200d0301c02018612005421540031604440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 941588012 1250 941586762 941586773
    0x18071b0804050108190207030c03030f02180112180b01030c0e0108030315060f070b041101050715050a060308123102010f0221030f010605070f060908121f0b0a02070909 74
    0x44500101e0049200103421008c0c103400c10116598248695424040c8001078007941c421381c01030f0038884081803030360707814200c036076001c2c0c00f80144017241e50380005900842d010300412070b441c07240350903124501450014814060202c07900c0c009010441441000b5514100e08540d41c0c1c4801000100c42c030002e0641522aa5120000c80300d008885103519511403030241040442c0c0402907908079081c1100055200343e55000e50240e880e0241c02c000180207030600d00c40c542025240050080c103038540d8440d07020000400e1180078100e0008038041d40180307458403c0c18001700c141180c404210055080d074006044d86541180c070f8142541c20b19000024142054083e03240408201d503442882d00c0102403802503410803c0030718810f0208000507111643c0c0e540041c0c82c603114001000d802c518054404202203900c80d000024454403446403240740900401d580410303e0801d513044e003445a0070381084204401d08403002c0b0b001c1c01090404514012804201a541d4901c503c44ca1048544481c200c5007400b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941589262 1250 941588012 941588041
    0x1912020706020703081303080414040e0111090909100216050606010212161b090903021507080c03090c03010f06080115150e0a030f030305010503390f18071b0804050108 74
    0x10380c008e0800351110344914035210451109501c1d030380554601081c1700c0915005002d081e0100d02584039261405907407905104005000920984c0e0340d2050306100411550306200401e81c901c600881c070840803466291090034500003400d40360443d8003010540d403114a2300300c120b4a0252031000d00607600c48c142e00d03155900c0810301144140a403401d03800000c264000b500f20800591080c0d0a546159200c075002d0120404142e809400050b400f00015804841d000002c0d034000042030101c56035560303008006400d40303111000fa40d98542e1508020400c218090180010102e080000400606d007024001705010070600e040c54100149440d8204a6440300078407a4051904804100d04448071410064045d00003841418024030903540300c110204083d1003c0100d20203e0410b6103c1c8204900c4005214404150025845020304414038120b694051445200300b12002d0490206e18000001400e014101e0742015800c0d4004103543e40095036140859081c0c0c4e07000d0808104030b8507400c2c0d1580c500c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 941590512 1250 941589262 941589269
    0x9051c0c061b0908071410020f012901030207110609013e0604030507120509040e06070207050607020906091026010518060703050402040b0319120207060207030813 72
    0x3890100d255240d10240c1c400c0e40e030910320355200c81c0c0f040b540c0d91035440d5490403a441b0303440c500e9544214000c000d02d400380d5070a403200c8103481101c86141650b0809401c640d044440c3ca01c5038018180c61141001031007880300817107242401c0031820302071680c40750382c6800c100c00403540c844c00307000030100070ba41c0c001c0c9584c805520900c0150103080c5140d60308400907441400007409149102040d02c40036801c001140c9100e5940b6959107401c00308955078250040000c10801001d00c0320900007031059071240d04c140095000c000c0300070b07c11800c184102908200741504950b019110400680b809600d41d4059140c010500751640800c690341d148000e4408409500114076032040300d0402d8a0280312100c116400b10100300081006449904c0c0c1003140e4400c2090310400c1360070003000600341e80c1c02984900e41c8103002900125190b404000001d0502400254000c009103691400c4400e101700c00305a110583d0360f40c00100348141c1003000107541d070b40b0030703200c010102d05000880038550303090000361740001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 941591762 1250 941590512 941590523
    0x20303070e1c050a02040b09040804090207170a020d0e0301181103010f0213080f060105010801150221130e10030f08090306040b011701050115052d07031209051c0c 72
    0x4180040c680f032078562080f4802603100340d04080704148686484030341b0030300a030b501c03841d00ca150030f203004080c101a402010064803403100c2010340e4900c02c135800009100f10b25069014041391400648041c0218000c2055280207a140c815404060381c010200c0c415580d03000700c0d00803000140e0b540003d0141134040119207030300c1d00100d04162040c194100d4042030713610300b20644000c0007090380b01c955030700c40901c00c990000e403807540100070304901d05d0648210008a03105480090442021001044503882441c1d15011000944007600c2c45940703031040080c2402d2580c000e02428950600309210516000c042d1903160f00d01055400c00c840c94080302e550354000340c1600c400f840c1c0307814807030301d184024801c040c0003030303418541c0300302022040c8501c5040e640c04104030780020058180840e119000450442c2c1c0e441c001f04a0404008140042c42203003401880100e0740d101100e140041c0300d03804001010311b94908240305080017450206070402500c000803001114000c00100840d00c0c0c0d0744104d406040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 941593012 1250 941591762 941591809
    0x709050f0d06090c090b0a080f0303040632011502190b19050a06050f1207090b03031615110c0d080604020712030c110d1407050f19021807020303070e 66
    0x1c20034007030780101424060465100050782e85d290008c0d515001c4100b21030656420401c00907002407210341c861948191640741444803d520704000300442030500e04d224680f000c0d404010816020048100c040244c9144040c1c9808482803848802500c46040e00402540c140c8000a4501150240c0400182c4007480140090b0800f02c501c2402002c00b80144c90042200c090000d4003814000381121808004100500300c041c60040740d000200082d111103603050108224103400040b94034001000300c0c1c099002071011340b0110008a0840d20035600324a1040c0060082e0340d55807101141c0982201d10034100b1840664075000010700900c50703040d0062070a01c240c0c44c001800d940c19440090444016200e0041c1411016450356903442d2500c1040005408204400c82c850000c5000d001c0d1244244101e90702c2d01c2c00400030a040699800300144286568014003066240450304000107010450500400e03040041d0300a451340f000800c47c0c418080f002c0350f103107001d8440f03859407040c01d800070070102c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 941594262 1250 941593012 941593019
    0x1401140c09090606120a092103020903012a050f0412110a0b04080a08090d0803042d1518020619030605040509030307110f240709050f0d06090c 63
    0xc0194201c04019805041010300082190038003004540b50010514000309050769503203241c0340504401482191300300b0f00342052001151480240446e0300b0f01a80b80542c03240d0341c4000345801c551441c203814001c807401080140c245486c4501000781c0c46824039200740e41d03061800b210043c5108942c0310260840c09642120280001b112008003803160494000590301d948034102d03806030099004030010b940100f100d010014050b80f004280d500800342200d2103044140d01c0324035494008540c1683c070120305a103880441c0300c049044400502501000c401428a03a4898069540280404d00c40b4642d03682c1424100042c072056100303d4030b9008021a50b203100a40404c2c040c2d9400034402d0001c41d04021000c2500d01e000c2c000c6501c2880d06000841c1541e807000c404032407140c0400403031917041c0a003280d03800c0e0200c000e0054181c50b210727014480c49010403032a114400041c0041140d41000b254000901c034540d2000c2c490048214200c0c2c8810380d812081c00c14800504029800030840c01c0c1466000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 941595512 1250 941594262 941594281
    0x813030f030f031d0714030a020d140f0f060708090307060510080c030f0a1707050a0305040521210d060f080d0c05030708180301140f160507140114 65
    0x944901030507650a000380c0b600500303101c130702003000d03a451010b40d0407107007040c005810034003001d0b80c0c1c0c81c100030121017000703880c1d40206034245684941580c1d0581030b22641c01918030100812540440008c0080c103000f8061005c2039255074002e000c3e0350401c4062030204040040c2042130710a01d58100404000c682840c01351054a10503d2003683c0650240c070101d2000c501c1c1c0821214003a03844100500072001047e990060f8006940c10307800ea044c40140016400702d2010451011741131300c0798443c559118140401c00c151030b1203030240550440ca1170b400c402608040441c02c10301c100c4044e0450f10850007082e00d138001ca07000e002518101d0340d1178030000046000400306201c00711900101a11004110010304440180c10641d010b45250f2041084500181c407110081c81c0c10b19901d00028030103420580083e003982c401018050300104031000380812055012440c541003000d000c5400321413151804060540c3c021248007400100103d20b4001c0200006c0d08075030804101c1d940c40c084c0038601507a15 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 941596762 1250 941595512 941595527
    0x1503091605010521100b07080d1a06120901020c0d091508160c0203010b1c0311070f120c0f17010606050a08011401020c040f1e020301050d0813030f03 66
    0x3428942148800005040d4000c50840d1a608581003070f04103402c5040b2156040103001400083c2d550700602c00000c1c100700c400001d022403034070400c16195101948840030040d201d100c140c0f41054042e280040c03c1e1707540da58040b1900d9142e00390340c00c1c505a55480c0c0090090041d000101e04900401500280f41c0b50300100d038034241e0b050605441c0c603010500c4002c682c1800102c81080758640040c01c00b4980b18005c1100c01a4035100400202d8450810004919103081201c85103807503031030358900402059000703840001440b5068009190180c03800e1002c05681c0d0f95485110b00501041c4030710003d00a04914100180c030000302c140480c0d41c0d46a030320f641c0410703018850360700703e52900b030021661920820031502034441d5941e0307843c55030342400848003000c081c101e20581940300740e80c800300c02a00c540c0140c0c0400071070442c0004828400001c0c40b004c441307a0148601101d4410070040c42190b44031242d0b4180180c2010039903895141c146007819400768542c002821025038144602c0805034407012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 941598012 1250 941596762 941596783
    0x50405040c0e0a180f0c0e12100c0e01020d0e0604180f0603110319050601050112020705120a031103060d17041703030412030e0a080d060f0b0a023306150309 69
    0x1005c2010a45030450b8800f11205100c6410004240000030a240c2c64008500d2000c252008191140c100e10138500500300c0b500b49003000d002c0b440aa800342180d40e018004160251001d00f03004c2d0041c041c040c0040c82d64030030743c0a09089078201c1418007620075019070007400000340310042040740f240c40e41800b01c5901c0c6200c3c3c03010710030310800c19074500c52018098003074036082d0b0101c0200309d030364203160056032502c3c071000ca18100c0170b13802d00c64040441c9007000142100100a6005503983d0a28600103080c0d82400c171030000844010014040162a03008100c0103203600031800204440311070700001d440381309503400004000801059250300300c1c00803000714002c0d8891090241500b035185015030a0702c130000060442a0011100c1e03101203806000280340b0308024a0000a0a6446522004450845400c004022400499810b4415030104080204c140c1441003c0c280200f042c900072a03007100c106104a00030b00040301040183d211000c00044403c0040c002640300e281004109954044049 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 941599262 1250 941598012 941598059
    0x9220f050c0427020d06090609030c140703080d020304020d020a0608010603050f070c1b1703070506011e1e090501060305060907090b0a030506030f1504060f0606050405040c0e0a 78
    0x10030083d620b0034008002c000080c00c00c0d00e00418880c86400b04800501e0f681d0054030900c0c3c6032030311000003036080d105210400380704c2d4588010740c01503801e0010303031441e0414040380103074845413060000c1001e034016140c01603c03031070000d40d590b5603910129890b0f80800c80d000b908403014002c040340194001a203030307040c0d440b02e40e0200310f1955015218514081c043d01c00c40d0110f6001002000452810340140c60401c074056042c201d07059807003000300d40c03011000e14541d0080c0c00102e4400e0030008180000c0d401409a807045a995403a02c0d501e000f403103800383c820045503050203d0320038020010702d002d00c4010420101304002c0780d03959000c040c001d07200c215905d40c450a07000d0001500940904010810b403914200501d040c030003050003c2d4002c100142801354980300301c000c0850000e10030040c0e140e04d080002140034550a080c40c1400a40c3e00c0104000412800c08005003c0550700c14181d80843d003003107601040800c5614001da0b02c6000f05a02c440d042458604046038991104405840798071240703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 941600512 1250 941599262 941599271
    0x50301170a0c1e0315140a050405060105010f020a1b0303024305030307050a02010906080c070209042f01020d0905150304080d05040302060609010b070209220f050c04 73
    0x1030a425203415290310024180c10100d4400d018503000074000510144a41030315520460b220744030782c511098100380018070161144a003081000b8840300251304000c8428082c0520300301907461980f900b405001d820304214580da050700040d84200510340c8002d400000d0200104001c2c039a81400c1d074814082078002d84509500c4041d0f078109011000c03242d0200c84094004000c45001c00c0c80d9060f0f944010400420400201080302d58003800104101c0c2c2c802c20050842d07031840d10014000c0501640a0303810f120000080044000d80c0340c0807a076865a0480f0300c211a85d5451619410541500b859103044500140d03495a01d130f4500c1c1e29103c440d130f40036001c03150072640c140d200f22208103a40c060260442d400802c824030b034544c104050b6030818031441c03101d410000c8103064502221411281500181c0c02001448020708200e21814058031440b60340c1481e01440c0d402140b000ba1000c4c1c400c000000c0301c03070400714001011482c6071070720795402100503403540c0b0305051450359090340b0032646110f6851b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 941601762 1250 941600512 941600549
    0x70b011409040b1518160305011a030105010f030e1b0415120213060b030a05150f03150711070b180904051207020301090609060c0306051c170903030a050301 69
    0x20305010340b049912103119902590790100c00c1c66a80413024180760820400a030f20b800702600075214030702ca07035420707483d0090040d0482002400d44038183d001c5021001d1103a042c42030500054101c80c156102800c121165543d20b0008800030b044080b1000c1080c090001e240101c0e56000810030701c1100c08640c02c1c0f004c61200d0072004032902e031380d03c0b9a00307540b0415030284005081103c0e0361020b0420265000030b0b5117980b10741603000da5104891304004c2e0782d607400800103518507089c051040c0b00303001c0c0c070143e0a140010012035511908091010b110340c01250008200910134814461510240030941e00d8a90ba184049521a00180840003200c2071049050525040c0701c641d0610680e0000001c052000e88140043c000d80d1052030140e805540f181d40c0040032446a014295030b41c2d118800000c3c440303000b008028100d034000d800c02c504c5a10742c02e07510500c0d06100f059100d00701ea00715040358003011407000d01c0d510610503410220781600020540001c01504540958104c81d80c1440b0000ba0002c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 941603012 1250 941601762 941601769
    0x70809060601171312020703140303010302010f0c02040e0d030f0b12060609071e0f020d032903010221010303080c0f030c09011b0b070e22020702060f070b0114 70
    0x85403540c2c0081c0c1030400b9400254200359105811056071025007005845645030764030303254000c000300d20140e070020b8020401c000412100d07220482c4000051421541507600003020010340e51403e400b0131140003a403106554540d0311010000f403699044034803034498000d018015051089403203060030f151408840450900315140c0380485818005844680d48400c2042860384000c1d00040802101581810b030a0102440008031500342d91950b00e107603100c20354020328198004280c64109410f040300000e14087d80a2103550540c10390410f440c1c6c41c6070b5000400d00a01425965003058490391000703c82001e035802540b41139a0080e583c8400c1503603a400b13000080e01c01c01001002544e42000001d2a0410070350240c140044145003d104a0040f00540c866500a910066a20142d040140192140c118581014080058540784080040003400300810319510749040031441c0c00107910070865664a00b00c4192810f031400c0552a00d146040c03032183c48600340641c2e50f0707002070060034114518 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 941604262 1250 941603012 941603023
    0x11805010302090412090f080312070e01090302040e0a05030d1b0816050304020a03120908100c0504090b0a0e1303140304110d020a08070303110705040b030a030819020d05070809 78
    0x9402034032190310364a451390b483c0040d004410b158010031001c1b5901241ca080c0400160005050403001143c030349400c44644a140c03074010308030b1001d100c4041c010701c0c556604490482e0460707030102c0380041c505480021882c01d051a540d0000d2880c0800100c4543c007551030786c49a034181c03550100b50808224444015a4540c0054401c1000380c0da4407400e5000c458402d070011540903101078010540c00d9070b01d94892984000300b500000c04034403440d205001005040081a00c000703580581444100b5140c01c000d02240b08a029071428140c03107480015441c3c5800100c00b0080101b403010032081c1c60001d0b0444030901369028200c0c0060700890083e120368103440c090b03900583c0c00000d00001ca0889408100c403440f17010404a8000800c00b10001e11540c090040708d00450082d162100707803060288215040c4169604010f10603840c00b1000d00460300d0020340e0510513076141c10801c426484d650103170840130005044032800c2c1030000aa03d0920305558100c18003072140760325202c2c0b968880e40c00c00e40d00c94 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 941605512 1250 941604262 941604269
    0x601020304120501020706090303020304111e150405030303192004140307050913142e02070804141008010806190f020c1f0e1209180f01180501 63
    0x140c0c82804140311001281c0980740e40d1502c0f40c1e000514201003035550310240d501c0070000b034001c2a0701104200920604098202c1048411200340800c048000d1481c440301103020070140c020f02c0b040400580300b4640408540c003600000302141d03181d14152400e42e0803403100e540c0030b08000381442c144a00c090084141201295144d50703280342020b0810708c01c0c0c025118000f5041d94144980b880014031910780b00e00c0180248503201100c1000c5509043c07050510a41c518120021b6104500c0d09100d85118042da8900405d1840380c1c12240041080b40000b03401213160140043c03500040006101c00809441d95070782c2c030280c849440c510100304040c0d40000c4248101034054014200184248180a40e001c400c943c07420302c00103010003803140c034008a800001e42a281d82d072004840c0c015a0013104140701d0810981c0c2414006000300e4a4900d4a40d250700d00a644400c0010a00e1041691101d01e0500c51148860040019240204500803051401c0c0302d2100b070354103650303003009403401c4501510307058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 941606762 1250 941605512 941605517
    0x30c03030225050f130c032003062b0b0106050a031415100c06090f0201020c0303070503090906061b060f060307060903020f04090b01060804020f0409260c0d05040315050601 76
    0x140d8a00300c01d102d42142c4d41e000941e030104141d640051805424452034070343c0001c0d5a00042d45e414580e03540000346240c8001440080d10a100701f1110b81d40360714005140c5491000440d0712500780d030521398158402040c0c02400000684004100c03183c1c8180a41448000ba580500510b43c2822603000c0c10ba50a0743c400300c1d619910707a42d450300e50920561188034400b041c5049840d517a01c03901d90f0300840b27001c00c000710340c0ca82c0401034200541d80c1c10070203810303003610840c00f80d0300d010815a80c0e0b40e680d2242412082c01032045800040041d0748000554a103421040d007500c0c24544481c00054039188100c400028030101c00d0302094150800050800030340e03480380c59541c041070450f000c20600311902d01080d580301d610b0f00310a00004414000c030070f00804c080e444608480c2410f104011422248504590240e8030f40704881e004143d10302500b4011000c041d5034401351140d2800910744602c50244620204e21a074441c07406161f6101c1c0c001c00c1202c1c000e80200040086020b40e1030191079069415500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 941608012 1250 941606762 941606833
    0x9060804030305040302071703091219120309060c03020304050d0e031f0e010c0c0512130b0921070f080105090d11010209031903170702060a09050f0601030c030302 72
    0x34000d43c000c075002030007030044452440e40c42c50701c2d0710003040ca046803c1c3e240d0004145c904140c00c04c020600141c2402001400c40e040100c0100d42860403002000303402c4425001d502141309018cc1d001c0c903245504034006029030500078101074040d510a507030895003403046a8424101d1b80c413440f0340c40102ea03002005004045005000940c0001040f86086803142d40c48208000c1c102c02481581950341c41c944a80390700702c0003800c100c5d0625031044155404e160003002400d03605000c0345031840541d2907905c03015440d800020082402d81a400b11801140340130380e00d440e10901000241c0c54116001c4402d20100310303072119481800d80d0b10658500d4160341c40318901c100c10390302071001000c40c0c110200006081c80004000280b81c00c1924145c8400c50300354408000030306500c04812056070543e280d0300d203030390b080640d4000e5031064000c09100c1d14079640c41404041000501c41c800d504a0720004070351455840e400e00c80075508a5220440140c80703441e08202405000c2210308140c00c1800d030302c120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 941609262 1250 941608012 941608021
    0x910052d0919171509011e020a05120c04080c1f1b0c060306061101090b06210102030108010e0c0102071409070c05010e0d0f020102040302030303240d030c1101090608 73
    0x248100b061081204902e0320b82004120a8a455071804441c0034540c01000894105128031010b0840901006400d074100f8945031601c58003d0714840000c580b480300142d1302d04000008a0785800380700c17041c41780300200c01d05000b16000504003500540d41640103031001d03919100300b0010380ca4010301000c118480914800c2e8400303030060380c00040102c00034109e40803440407665002d6402c45070342c10190100740c1e580300c18080250b00425100354540b901000300300c652400c0d00c807240e8400000b003d80b0b12034034940518001d201c1c2e40c20300c60000350404100039916561500c0040d40a030082d0703403090f4540d10410341c4031341140d84000707410422501010700000c42c1c144400d0a204002a0007083e0809000200c0f41e03c000107030342489040342d440c0c2911301418800b00d0002006060040914060b000c580c0180030a0000d83c0e00482140d420900201c081c460541004840c40c55066808000940c0001c01d21912001d05400803041c06926200307030022106848040d0055603941e01c01d000b080001855000081c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 941610512 1250 941609262 941609269
    0x1110d0e270c03010e280c090b040e06040c0918111308010c17010f060c020f03030c1f1b030e10180204141501140910052d09 55
    0x20300d001002a9079030740a115005810415245041e40e0941c103548001004111104000f03190741e420815074024440180b604140030321140c18040403a00d81e10780d4030b000740c9009034050076001d40204440c0d401c1c0303911582e50305038a43c00701c0d1086070054015814000702c091042d22803c00382d01518803e2400304c07450380b904800000108022210280b86440c03c00030002013026000c0400020000c1800202d2446c00403080144000b6402e40001600c1c603050300180b100d10f40c1001d02009881062910104680003800007412060345500390700d8050000046e1540383c01004114000c9480340e600c840c1c000c941402d090b40c8110350ba440794a001007090b032070348800c0c414400c0e04030454000c1800100c400e10a0313510041012074500b108807011190004043c0c4045003001c0c0110002016584d0911125282c500d581c2e02ca00d0039845000d5041140b03082050380451100d00075200d0400d005007064030401c1464a018025074002c0c1e50103195084101c036920050704110080400c50b0b0003028100e400d00303c559050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 941611762 1250 941610512 941610529
    0x1203011a0a03091709010f0c051908040f1508011401020705040b0105190f02010f0501030b130503071718030a1505060a080604050c0405091203011211130b01110d0e 72
    0x801c000c041e1206800310100e2032001030f00f00451060003485588007244400500920242d001040034011031809000108401040801d200c01c580d4540318a52100c03071406220511a5030401b00c44520100c074080303000040044280e1008400f85c980074040e0f6225801c5005000384082110b0040e884020240140d04107604282100c0c0700c1810000d08010f81d500c100b9080603201c1003490001109164400d0b43d86509000703103c04520a602d00300025419504c2c1d21098281c01441c8903032001e15203e20b8010001b04004590490303400c40c12803030b0320a403441c5030800070350b0105040001005646040741c0c80781c82e010403010b0782c45030f001034400981d446d0294071501400e8000c010b168000d00e003000004034154180071841c42180325030b010b0700030741c842c0400f048100d030405489038610354002040b1303113030000920301200d040d20050502070034020302d240303451001d40c2c605809580d0080030710910124a04084d0300300400683d000d890300d501071101510310303e5035282c2508c40b9200041d00000040e4450400480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 941613012 1250 941611762 941611777
    0x80a06110d0e010903092723010f030c0f0e07140c0d05030f010f050d0b0a020904141801051302010c02181f05010e0d08090d231203011a 60
    0x1502400c1c181d00d8914641198524000020380d81d458076126010075134454060006400904440015041440007030b0024001d00c503600c14089a80d801c040601c5102034058145880110340e40d121590384914104a40b01300ca48400c079200c8052071404a0000030001003281540c2c103006500c0f141d513a80c500d0071107108a445a501d0b5a00c4820440182804001e004403242040701d0f40b42c050343c0e401c0012590850307200c142d0084c8e1202c2c6884a0034825a540d5a0040c088680c10608840c26501c481010200170b208407000039910070701d003603500310411001003140c034843e0443c54400020070400542c2c450903903030102c40b01d40c170803188401010010b600803001000d0140c0080c040a1454101c103d90548124007525048401460320704440071000d90f01e10440050a42840c00521001a4101080020018000c010310003070000c541c3d01703030b26280d00e1216041d40307030032914032081048040481c290108103c001c40c00240152406401040007580c122030480b0308801c00c04840c000e44000452080d0040781 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 941614262 1250 941613012 941613041
    0x51e01080c0d12090506040f08100e06010608070e040c0806030610030210111509010b030d05070b0604090812010603020c101107060504080d060801020409060510140a1b0507060206070801080a06 85
    0x134800300d59511604040c01c00380c0303240680440c42d01d003044481440e0904685458001c28188100100000d40105955044441701d060441c0191036100055520303020070101d01d03400501e0b014001e07084581c0701d07008074010b41e820303011740c0c1c10f648030800b1014003d4803074003000e500021418100c4005921403c041c11000160405840305240321400b22a090034041d80d039810300c0d03034540b864140300e0314051010440c50f069078203195241540030b0340c0c1c0e20186c41008001503c0340d40d85240c0c100600041c40b0880b8443c58940034218003039a15031a018000350000e4051a0390381c4070340e41e10402001ca85220b444080704903420340a0500c14296102009007070014000c80f10408140300010003282580508006028241c0c00940c5039420805420b0490342d02d0303031115115060309140e48803a1600107103220030881043c220140c2c0d490401c1c40c00c0e031310f82e131280b44123624036840c0344060804d214002c923140060f15656400d50307009485002088503662002e00405281d5044030500c5000124168014040300741c502 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 941615512 1250 941614262 941614277
    0x50c090a0b03070c0506090a0330020d02161208060a050d12050c06010f061706090a360c05030312150a05120105090d1d040f0906051e01080c0d12 64
    0x35503855040034015101c21f607403070784081025010190402c0303114083c860002c0c9492031b130100007024244000c040700c42d10005150300140d0340800110702c1c0c0454000700500280c0041070b1000e071800c0790480501140c0340c00081c0803840824550300e41201707007038119500103060041c04421030300c0d03595291031070342449400d01c902003265101000d000e000d094005c011040e040084146000c9000c5c240b2050304040341c00042c0795004001c21075480c4e002268210040c0400055010100f440d5613002d2012400c40c0361116410300d01145a40c078440d80d43d10340c00ea12801880035010f50358001d1580c0ea01032512000380d032800e25800a44e5420015407540c0e04144010300070f42d407095803100422610060141940b074580d444104002c50650704018407600d08859241020410b46424404800103013901c10071803261741c81d400c02e85a890010b0300b006520a402440800103820040010b00d1144172400058562034110740002842c1c95010441e00600b0202419840c0785200782d0355014441e1101c0944401800941c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 941616762 1250 941615512 941615537
    0x13380102070f320925020a0c180f05090318040c14210a05070e0108010b0306011d030111070c0605040501120f140c0406111c110a050a03030c03050c090a0b0307 70
    0xa0701e030001c0c00707558400400904185e0031800c5941405610301c1000075907101d1000d520004000e0701d141c0b011241d0200541800502c00309080d005030010140004009040106100c0d00a00100040c18074224010202c80f0b0310190000380019074502491180215444404150100f0190001040cac48801003110501d00c2c0e008401c0d14001c0c24060f1103203803072965154100b011241c0c116100c0340da4030509003003101c03c5600d49400c10700e035880000c01080c1080300c900c0c061150003540e0181d001011000800034060120844001a95900640c1040d1018000c22070009942c600030012a0180c41041c0c2d01d100200c400c043c1350801816040b4a054081591260000c002e40750100049015000420241da80ca5191020043c1203c01455198a4030780120444034089c603601c1c044402c1e0902c050810120ba20b40410000d4144035242601030503a010b0141e004040603819031000084292a40b01000285c031210115042030148540c542e401201080b024490350001d08059035000d603107440c01c0c4030800f4a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 941618012 1250 941616762 941616769
    0x24090503030f13290105300106030b0f0402030d05030c030703111c1d190f051e071505090d0323040b03100506030613380102070f32 58
    0x10020405020a803d0894207044e03000c54810302c1c0140f00031598400c1032001c1104580660b11070020310594000ea500da80700145030203400100085421160140c110325021280307007014081154124401e018041501c19036600030740960703000d00040812941184d0384c44006074028981080400c000801c184154011000d4074010040b000041101c081558484a0054074060f91a00c581400680000700b418401c244000035880740c041d00002050b00c8114181003850601004540f141030321481030641200000c400030307002c17088540c1d420b80e0401680fa00017084405000700907051f98000b146019040100748141240b60303801c02d00d0303001200380324040c6c01000421707401a4411030b2010360220030419141a4511128002c00065400b64030f1840c1401c0040d2a4403062060211300e43d66410300f182181d02610b41d483c451040d441440c3c402c0030b0740c529005510304107003481540144030f070140200d00202c100d40d48908071264040740690420034940e40444442c00e4078130022a51034410301005007a070303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 941619262 1250 941618012 941618033
    0x604090c06030c12021e030c0408011118010c1a0411100f020606040b21010b04050f0105040b100203040942060905031b0102010f050424090503030f13 66
    0x4180c400280901d034501026143d102044c041a0440f403043c4100c011142d001188080e5200189403125900d85c0c0342d04803a20680181e4004210543c0307860780040d0310209450042000c0300030103090880300c4030003800440e411070f140d000003452425103d00c4103140e2035441d007041f6040b034464411039030341d41189004500b10700700100c0c038240059840884403050503018800c4940080080e101844416642004940c030703210f140000900302c0e03400801c0003d0100c1c0c203600000100303000800501041c10614040702080b40c0a000d0340c1c1c8941c0c600000c01540d46030211108191400c2600518203042c1340c614604001d01c02c103180780070940010009152644501104070042500705941a440b0f8407009541c04001c0003503401c04001d1010841c41400150b50000c1c070504c4c0700e8208034401c040c10100c440101c2c0074142a000d01d5083c28109030034032081012065a040909540c86100c0901c2241070700ba400580c2c0094001074040e4104001050304400350040c2a6844401128001e00c2401c4641d40d03100c3c02c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 941620512 1250 941619262 941619269
    0x60106080c13510305091c1e03140c090f0105030a061206050f0903040602030d050a0612050c030c180f040f0506041a010609030305090103090c09110909090a0512030604090c 76
    0x41039a03101000002400f448072151035081c1c82c0c104158500403d00c15075a5108030362459091124104e1001d14502c1106a170042484050744d501c3c0c407624403000a40074059042000d40ba0b0950003001071950803070381c2c0648400380402400c5520360103441c0c0056503594005083c0500c8540c503840007117142da201114444240e845090f00040e5860104120215980c0107800e18880381c000f0081004015400011765413008041040000e9541350420203c00801443d4421440e0359074110740390301848004905019400015000e94500c11b0045040000d03440c60410200d0b59460003201281940035500e00c0b9640c4244074825009141440d0f442e11480c000303088400300e034060301403800c103220400008101070040446080c100400740c11554064801e0013103520f124101aa0740d4800300c00e00071034400c0780e07008124400c1708000d214942d6402008503804140b50310b0194480c0350101d049035000040001d09950054040d01c4140030512460030035900281c01d065005844000400100d2011022071005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 941621762 1250 941620512 941620619
    0xb1e040f0e0a1103010603020a0611030412030203130509010b16080708070b01030303060b07081c060317090405250809011b0306030311060411040e030714060106080c13 74
    0x65000b0f4640401c2140349100a40d000b03904140d02000180c840d0464941a10824141300c50244040900189540941e41c0302d105441090f13400c107028940c0200083c001c0140741198541c25a0320398041c40340e000f60a105800541100300b00c40b120405030542d8010000340700b006407900d0410280c81c1c42c07449030000c0f2415100525024010004c03d42c05200c0c22004151820300207003003800c0f94940040d0ba00070f1000e00240312440b80d150fa082420b03241d21481c040c50740007405150728010303136101074100d41002c0400b90081d460f110110b03000918881c5080d501c05000c891489004100413421504000b000e800810f00d507481d406100001c40c0748100c55580c0020690700082c0551650a008150310501641008140c0001c0c0c144800b240d002103840c94002000d0324007140745411103049600d1440313020006025030f4200e0411040c5c00b1000f01da858101d41040e60b50381d0042c1c0b240c03c4600c1e554441c0c07a010b0780041d01411030030000b030300b8100007440350100d8030314810500c10b003807403418400c400038a4407002e003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 941623012 1250 941621762 941621773
    0x70807091401080d0807050924030910060b04050409020a090f0c1b030e370504150602030d09080c06091f061a160510021c0b1e040f0e 59
    0x140d01d40040340701d4014292807004080c0c044400c8400b520380e940c05420700c0c08126001801802c5030311040c2c03884012914060701c081c0c040d450408180c1d6180c00c2510303214407a00840080d08180c480344c3c020b01c420b6600d07513030103240307130502e000104401441449012a0040d801034000a0346891510609882c1c040f41e40c1d000c9007403168004000c108100190004406030030301e6041001082d40540d50021030344054910958203800c0b800140680590320403d071039070708881200728100440074003076102155000e44080c0118400010340c205044007034000d40700164024022446408c8131a0891008240070301c50061501c0d02e101d000500b003620490310440746510541c458a14072000c1d0400c2691004648070400c416403c0c0003403000c41c0a148111101044804101407103800020045190b80759803000440b400400d4102003e0040c2d003024a04040c0f6000050707005400220a0203000460003000f406070488021412095240d0305915491070380060b6242969240070070188101c7e801403082d03400614 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 941624262 1250 941623012 941623031
    0x7020c060a1d060a051206031c09090b0139060f02090f09010b07020103020327060f0a09030905010f140f04050901120201021911031e010507090e0604020c07080709 72
    0x81a1a0070322545601601c0f04204620400760b0084c103880011000c00c413132401b1307a2038072400246050388650440c9402c428520341180c0c4c25070071001c190102c03242003500b4020a507050006441913141002c5081056000300040c0302d0041018803028032240030300324810860591921100115075180c205041e03045c1c0e00041d4241c3c1d6140580c04214800800c60700c0c45610f40c101000d04905000b150802810b043d0044040360031403900c4c0c00040c220209038004080c0300c000d141c1107a940c2d81d00548005512080907030121b113091040380900c8512642580f2074903a030f103143c6001150140c103071691130410440b040013050101c40c02d0f0402001000002481140caa50500040010421040c0d024003190041c20359580c0050741c000c5040c168240c91503150709021071450410f0924102a4030180e075041c080d1035144800e08201d40c81030109e004c0100000c00c81940c03110f0094411914a000c0d00380301860b4140041c0e240d1410b60010039045400d002902c101598503c229468044d21fa04020520394843c8402d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 941625512 1250 941624262 941624297
    0x603170403060b0301090c052403041a010b070c03030807170910060504021903022a010603060b0906030a080d06092f0a0e0f04020f0315040e070f09020307020c060a 72
    0x510983c0c0044008025031419541c030070300388901038402d5030f00651a0040c203041c110030fa694201802c1c03808024403a668941490002d03144901c0c0a0601200001e0b0000405d0f40350469054511155021880900c1107041d9141078805100c02002c1504100d4807005461414903100700c83d5000c2c0301a04020101382d892505180103503259504540c1c000c51041c45607100903540d008800c21608142d003401a40c031581000448508801030042c49000390030013081e880910740541c8194100c9010324410401c1e00280001c00c1462001078824640c1036002d4140b50020480043c000c00080241c0d00c400941c0e07907a1040d03100255040e2a108440d007601c4443c0b4040d80300070781c50008440510581503903142005002018107440e6248400d140034071080554440075845a5040f202d40350407000d282c81d00c83c6003203100f4650040304100c6141c090303401c00704461581d21001600205817071500e2900742002c1c0c141680c800007034200411903821072169100700f0300c40d03407144030041c1481040c9a60340c004958144951 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 941626762 1250 941625512 941625521
    0x90207050a0c0b0909010b0a050c0a0803090d050f03042301140402100f080c130f0b0901111606050c0c09070f02010c0807050901181e0311100e13060317040306 70
    0x3c8800740c020800e5040c0c55454085481c10340320441c01c400c1e142d08856038115600d024854681d801c51003441d640001b4008840055481802c200c4100e580c042d89280e0115018050304003800340040c41400031400040c0d80042c2c8440151032050161803131a419002217003961501440b9100900002c41408258140801074403458212403c08a9400c031064a0060200d20014000818140d000c0342446240032640d0701880100300740c4800031440f60711034480e2540ca07800700d4590382c04284940c550506509010440c0300b09007001d41c00003202c481c0b82c1002500d0319445802d02c0301c100c0c0185c1e04547e490742d03280ea4580f8014102596102c0300c1c2903400d84040d003121108000304052290760010080004e9000e0100e4840740e10070b180c0500d540b0543d103240f61a0b6070160700701032004000c0300000e440001103c4040c8044034001d05000080d11034010500503401c5403a040b01c000904000c072a02c22a091040290301c940300c1d0500c0000303625a4903101c0315901c0d00c0b201162503608000003000c1003400081e01a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 941628012 1250 941626762 941626769
    0x10e13090303241710020a050d150e060f0a03080c150a02160807080c1507030f020c10050619080d0906110c10170c0705060919060b0604090207050a0c 66
    0x5042041c180c80d5031402c00c00c52468812100540d501c01c13030148101030706014000030342d10384001c155100e00c1034044c09800d5400c80024200f5241c54642c004051840382403890080f82c100c210303481d500ea281d050501480d0111442c4640d0489018800080001c141d100100414450f00d400f5200311051604040c01c50007025260f0782c0b8490050000000c0c10040d100d0041d40203a1004025a0360140d600d84146540204103c1102c980100031080740c0750210034012501c11041d80ea820000d0740101610302d012030058140d60030b00755000350a0028003182c154012900034070020540d580080d0484003041007607000d80c100c00142c3e0400d01c03401d66071036045500c200150080c0e04111071102001444540d8900c04020480e2060140100c409141c5000e1220b20045404c01017041d1003501c0e160803030300256803003040102c03514403d105c000707100c1040124982c080b01c40c45d03c86681c0003001035160440038225224113240d120301c00704030000721300d01d0901c0241003080c49070707000d0080701d1000d042100c0301840c80e51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 941629262 1250 941628012 941628041
    0x1c02070606050105070b0c0a11030316080606041d070c02270f0405102703020319030c050a0c0503040b03130b06030105070507081e030403081b07080a030b010e13090303 74
    0x1e0800014130304501a984520184121f540300d03401c0120480300d01940030103c010500002042c0102e2103034030046806500e91680b40c4000d5620342005002441c42948240200404201000200c203805528183c1d00b00000b80743c03a00c032440e20368000807980300c641d41b614072044c07500043e1913100030201070480e54050100684100d451401d40c0310385480f8580c03511326003030a07a61400d080310801900d0f00c202d4282c1190b00c6d90b06405503118076002e5a00c1c1d004203d05420501850101d21000d4880d0043c2e801c4000c090361a2030508921f42c02c1511105151201140c40c1e000c14400403a1440110b0084d5200b83e42403250b4103048801c50420611099024051600a90404007040811a008400c456000d58000c4009039543c1c140141e4071803a13840b880c0501091300d000010f010505510461850181e0321803580c00c0030407104c10f2035614142c4119040200341d004140b0000d00e80d607000b170303108820141c13060501c0c1d0318402421000814a448966424807090f80e00c01402d0141036140c412800c0224108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 941630512 1250 941629262 941629267
    0xc030109080909040f060203101d040f080c071d01090e0c0a0b0c070509010611100c080c0a0e0a170c0103090b010b0c07030807120305090625051c02070606050105 71
    0x262106401031041d41a140c0c0641c03c031401103010045441c000010349900a14210346a04140b502592441c0c004e1050190200b00c41032640c002071940c00c405809542d00c8802104104200d42c2d034001a07800600145032640501c000001d4000c400807043d45e501c1c2d850080f0f2090640c1042005011110041048400f42d809030340c1c1202140c5a900441054812040b1175a850b00800b4104030f24008154000f150001083c00000809607040130320003c0941c2c000d4262114100000000002c86140f03034008030004402002080034126003100034203c0b1001860b1110070920b100d000300f240c0740002d0b40845809202d400000005100900c540098030100b444d09103d121040e0b00c1d440c6802d00103014403240c0c0b07500040d0301b0902080804c50b0034000e42e0710986c400e446103880d0038665144585580c809010a00703041c0040c00345000440c485205a04e15a00c8110180c0000e00540e058a020a011401e00c8810849203040b00300d01049060b44100c460700140c3c1c0c1d03100601d0040c0a0b6556640020f060100c00d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 941631762 1250 941630512 941630531
    0x5010921031b1d1503071403070905010c0204090b0907050102010f0c120c0c0c061214010315090c05030a06050103201309050a0803010e060405180c010e0307080f0607020c0301 77
    0x40101c1151140b0b45443c0154071100b0244025031903400c155007165104ca014000075065207030b20000340d4886d81a81d11a0b43d00c400040e010030059100c201c44060000b03000100070700441d03000d04201e0903864005080011032907201c1d0f640c40c070045420707170f511101a806510100403541c0e0901604950032903001d420301880e00002c0000e809400078015000c449511440307a03e02a41c810040d00f0b0301c1c00d42104140d00d55560303602011304166400c2c0180d001e65410004101051407144480504983e440300f1003100f82505100440300820020700210b8110301e0f040c0c0d0005407690100040394074540110000900e552441c9801010015000d250041d1500304c10448815640e0380300c0134405080c00c521001c18407044070300d001c90034040d2510008099010100010400420b2510701602c100c1040c0c80030840e64a94a032a00390451000890859039440505600103a52003035014101e100c80141c229044075480d00d4095051075182040d140da298030107008c20520036030408c035801210000350001c001c130154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 941633012 1250 941631762 941631791
    0x20417100e0f0a0f06020c120403150504030e0d0515010b0a020709091a040804080d0302180f0f10030605030318030d08190507021e0709061e061b0501092103 69
    0x2040f8025080c07614050f0303413209006560f01151021456501503500f5501c5041c0c2ca010aa0440d000030744a413041001e01c000040f0580c446c0e140aa030b050f8940c1c019420200c01040a10031482030100c41900440c0001e0789028492104580685000f5141c5c9448005005c40240782c024294003040c0854141660340001c1000c1c4107215030000e48002d00200c413583c031814222100e101e140c0c4242518400e5130005406280c3c150301034402141041365241010040b201001414800001026400007441c0302e409003a150034840d0280013201d605020034441e95950000f800c54002d101184005044000009030714035061090701c10100060408012a082908481c0c0c0e5501c2c502c140d15a41c560795401007009103000300b1001683d000740f0760140209060520981d521200c003403040c1120581840030205202e103601130083c461000c00716010062038a08841100c034598195030400160841e2481500030840078040c0144c182d0080006654144801980b01d803c8000d45070300a04051826a01030740c400c0c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 941634262 1250 941633012 941633023
    0x105040f1e1d0321220c050a080c03072d031a13030c0308041a1f09090503161b0305031e0c060a1a030d0306051906050f0d020417100e0f 60
    0x1130300c01c1c80c040f0090fa200d5440701e510341c01a5a01107244004c00c2580c00400035010240360a58805480c042400e580e10002d096861408101d01589500840300c10321400c41081c860485403810208842803584488941200040c0243c00c241d031401c58883c1007036070400034082c4032074200b1400d190002c550202a00e0042650504840003420000900c02150501842005c040c0017806007030000415418046812246030501c8002c280500d90b40c000e000442d03030154407440c43c1880d0010051440c00301d80c07144003110810400c000f03c950304c0006104201150b155042c100142d403181008590b42da500400f20284005401180d8665480405c240385da81da00c00324007580c00c1110a0008980204603d5030744442c5584a0501d0b80c052042c600e004c0c0c10030713a00d6080201201c8d020790320110301a0160492a405601c1405140080740040040740f11038110300780203001044201d040141095103d68402005485100b848012503000101242c0040803d100300410008050000c282d0140b0010900d038481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 941635512 1250 941634262 941634307
    0x110910050705030d0c08040203070807060203040302060304050f010e0f0c0f0a0504090501090213020d150302100813020a0303050d141014030309091003031b05060105040f1e1d03 78
    0x10001055200c20400b042040d11000d103a03028003401035101e1268020706010741150280c0c4648170700704000078286d5001c1034074804d1b210981d020b18500303800c3d90240300b40d65101910488041c81248143d0703105010a216440d00c24428a001e469044a040401031500c150482c0541c40b542d0310500303a4420fa039a40c0d00810443c0c0050b900030a4034026401c1c85401003280301c1000c1c0d040f000142d00e540d03a5240d00e600420752540d074128200903500300c42c0c6004001c3d08844c08004c2d00304441d500002a49401420059808820310f000c1d805214803680c089581c8400703e80c030071400700340d01180b001c0002d00385000e000e241b0f00715066048014589103040171411509440364201120780d002502902381c03401c3c000c035045020050010000750500360481140361000b8030041e0001000c0710749280b09828000c1038000e010740c029008220300c0c2d0800c1d0801c0f00404d80d02c1600841d407690f45422100004554980d81c0e900300b594580081e80003a4414422840010182071a10b1600100041c0c103d0303060012803031412 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 941636762 1250 941635512 941635517
    0x110c061008102d330e160c0f140709110a091403160e04031b0f020415050405040b07030509031315050714030703120b1c0204111c110910 60
    0x54121007004803000b800301040c0040c0a1850080d05241d0011200401e00d84404c031003102d0008681e650b58910540c50192011411031458011000c00180329456400a04e0301400803200c0541e1a503803190006000450110820707001038000b0070a48100d17202d404004202c205040386400b089020042103041c4074011000d40304150340c1c883c003483d101080201c0300c4124903a03038418841c0d2902d1143d03000c500100c400701d00162608a86000b9800e1160a60702c0d0a5400000600041195801c00c800340409540c20071007418070803400101540c0358002e683c0950b00502c914045c034103080784010245d81000781950641d910401001c4d8500c1c1201400804403a8100c802080300c814000c01240d1911941f42c000d0100e500704107281c0b0914002000411302648203071161301c0d600960307124002c1528000d410341070344141e5200d403074403030b130000c10100520780d0348001c000040c0034015183e40360301c03600039181101c0701054400700c0741451030580c4100ea0100c02d9024101e4140644030001034002c0310350320000400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 941638012 1250 941636762 941636831
    0x6090709180e0c0406030501021b010618112106030601060207060203070b060312130f0527130605010617090106030c051903080a0f0e04060b0d110c06100810 69
    0x10242e041c4a41030705194000c1003407001c1035607424418081c0d041140807002c41c580a601e05141d03408140300d540100c500b16440b442d01407040c902034500800f05032000822080c810400d0707401142c01c000c4003070110840000303022140e0078100145864002c051300b11406640c005102400100e40000c1900c42c0c495002d00e151070b050f52404042800c12551004800492802050008102c1880034119003a01c40030b101c4d0300c910654071010000c0c503050700741c07080a10301c900e9108944103c40e0391003102d51207000309020002c203503010707510b20003200d0090703002c0c200054004c0d0841c0c81c4880c1080d0b905401c0741c0301000a001c4142552104002c0900b10700c00d03648aa610b0400500c0c0c00300d2540c500f04011500408019110140031201078040823582c2c0300c642c0054180c0440500c1031038279100303510541d101c8204050815860045000041410960201130500f0921100e03244420030040c05102e05c004055548a1500c3c2104e460b14101c1154200c0c00741c00d0602400c0e20403041c0250f2000d0540440042005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 941639262 1250 941638012 941638031
    0x2071416050616050a0f050d080c0a090515090a0312110a0c0603091e050102040e01080d0210020a030e0303010305010b04050606120601080406060b16030f0c0b01050904021c0b0609070918 82
    0xa00c0c290f05100014543d5080c2400360741804000b05122304a907502d5203d00c2c1a95403100d00181e00c40c895a0443c1e80418002c2c1c1c0240464244426001031308401c07960710300d11b40065100000d0481e403050b401240e680800b00c83d40041c0359449020019115004001003c0700140d5903a81c5c0c480450a00440017055038034011102403000d03141c440e0003107101d4201e00301a440c2c4c0904000307000c2d500070700031087c1c0607446000000303a00e100042c07407121050b0070341d02400201001c24840006948810703909420591102c643d601644020f00c0250300842c4110000a1288802d806000c05e9640c010042842070300180081c00444000048082c0e008000340781100c116039591030820010142034222030038109000c60649548690000d8240070309009407980d40343c11a104a00b00d41d00404200d0052881c103145004100a09100f96a40d40040c8010a4241c0d103e4844008840072041218181c820000742c00901140d42172504440703800030458a44040610300708000d0a400b140c1c442c0c1c0d94450143d0306c1c8001c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 941640512 1250 941639262 941639273
    0xa1a03160e040f02100203090301151d100b0a090311150706091e120810150c14010203070203030a1401060e12100e071a121f030602071416050616 64
    0x40c0f942030360041c04640114007500000759070f03400c0210043c1c001d40c80c08035056030b01c4490b904004100c4824080070b041f04400a030000c0300320720000d01200050b4484580c00310310400184081c014101d19642e03410b48051071400e00d807000001400c402030003000328070000036140f04050203d0b00e030b0940007403010607840900c1c6090551050b011100c3e40c0540e084603090400c01c607004549a00d510b0031a0ba900035a40c4803910106403900752449015100700926a015034654022503441701428012600f1324810401d40080c03501307980c42110004016000007080104050180c4580080784403039281e5031541d581445806440c1c0155202c805108281600b44500318803810015400c8000c0114030501c0424a084100780d40d9900394040c951012004010040214244506803007040c5130720b041107a0f10340c9801c841144551101030842a0898201070040041160f070300090148034407510034401c0001e13011030b1040c00c2603d4406103c0c0411252202000a40d9070701d01601c40f03002100c46249104400751504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 941641762 1250 941640512 941640533
    0x606101e02100504060b0108060f09070c02030709020d020910090602030331050303070f2a050f031810031e02090604031505070306212006030a1a03160e04 68
    0x1400722038102030801c1300700801c41c0c0140001c041c0a0300d07506429140d82041042c0003691a82c080c0e00042004001081c8510400544d1600750010b801ea418580e110340244003a0790061040307182c4a500003580e030083e4185200c0d95091901c6c08e10780800000d05100009480b8400500046048629020071002c0c0001d242446540005600101c0c881a0b0742c0b4900035407260811200b4801203540a0100302e066405401030b00d010306a245c00c410f07100f4130209900c02c90100c030000180c640f031040d4010f1080f05241000108491010703010051400c01841d402c100c01104542802130400d4140180304c2641010100c44406450112101580300d140c4500400c90f41c1c0555480039000d21800008120b07100c02c1d941c0710030300032401031b5018031906071184200142100f055001b4019042d02c8003040011943c00551161b00b184440800400001035a000400b50381040c0d80e072090141e590104805201001d81902181d42801d40144c000039218207a5011600300303602c6803010f07200008c400103080001c00b400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 941643012 1250 941641762 941641783
    0xc060302090109051e0103110c06160507020d0c08120f1903020904021218061e0c16120f020f100f0b060f030405070b090f01030b01030b1c050606101e02 67
    0x10030070004160051003036240403030305d1074a40400e26006212001ea18a001110b0640080c0c00c02401207403a02440004041000070840042000a200303540c0160b40e81203428644500840c0762054142c1400709882c204401d089482c031055504001c514190120380c0d09032088a2401205000b9419040b80d003034010b0f200f0140030701d51162001543d01d0400c81596502c0b0302801218010329500e043e4400040d59640041c3c60101e0b034881051554200100302e400002d0b4046020f0040d00d00700030714141c1c400f462640010080790b850b071f81d1001c010441644801c202c40e50201c01d10040400e1030902060580b142011007002e2a940e80345e0918050456954211100c4000081c0940382c0e5604201315050968000381c4044800d801014000655440b1001c1039a0700841c00601180c2040c40c070b00019001010354981c00c038141030301e50046e0207440c3d54042e82d009040c01d42181c00c0311041810720340682000300c0103003054801c0c80f41e02042d02d801c0d40c0c00311191030003104072489611100d20741c010982c5091140e81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 941644262 1250 941643012 941643019
    0xe03070305030c0d1404060206010e070e040f050a0b0307060f0f02030f03070f1701080309010c142b0311030a0e1e1e01090f020907050c0a1119030c06030209010905 72
    0x80c2003103c214001010304d000340d41941d031080c1e80ba00304c1c10f03c9030344c0e44114400e020042c3d1062006010740035040103030a400000d24140401e80d014071801180c155401030008562040e034400400408617070303a0150400c1000c044000d00056030811318040c24100c039008a0701c041040c440e116070345e203c0c0208115000c04229281d2961a4034059030024941139082d0003050025000b015203900d000f42038040343d41a075202901445c206040386004640c0c4610301441a60f0001d0710386040c000346001441110b610046410400100e0900380149907100c115899030042014902454880211158000d507a0040c07031406010822020300880345281c8000e0202e040d01c851213000040101060010300a1900c450421030000c0500c0502101401c0b20310590010301703a0000400c100700107181c030070121a03201c1801e0030300b14244071200160524042d641c1c2e00c102c508080c04982c4000a00d011061b04244000001145103c182180e558101c40d03140c602c1141c00741500444c4040e0580c0c02609040302424016 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 941645512 1250 941644262 941644267
    0x90621100e040c090b040b041d07060f0203090d020d0f060606180303020601090e0a0c08030405091b0304031809064203050a0b0d08030a050a05010b04030f060207020613080706030b0d030e0307030503 87
    0x14a0038413006148415000780d520a003400041d0300c42c0200055108607805370007860a114800060003281141220100da00c41030465400700020100054010544d01411001625609094000c0c02d0307075880e03511a40340c180d81c8a01c02c2000940c00940c160545900c50404250300c0344503148180f40245900c0e00a1003070001c0280481c502d0400005002103590840c2c0c92605612451419000c030308600602200f02c1a0070030001c0c0c08a8001c25000e11005500b0300503000c070643d01c074007280480d2000e0b0080c0d81c074124156840c07458003001c66400b0141c0c0f19040290184440a181c090114001040703549041c5500ea000003902810281d00204d016100640407116242c010f1a0a04c09035000711078402040340b0f081c01080000c10103202e028144c0380c09502182ca400e08544400c00c20900d80391007211603d07020498400140c440c08050454140e03261011000c80381400801c0e81030039130903001801010328041080c00c0c2130391900426050607416091150a0004442c0802d00300300e40d80d04090310030f1200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 941646762 1250 941645512 941645531
    0x30715031418300c03181c02010e13020309070503011a09130609050a151409060c0c0705060d06060207151202030a14040503180105041208090621100e040c090b040b04 73
    0xb00c01082015130043c00003204250b86e070204104a0000e40c00071980c0c01040340d0000040d401178203210710303c00700200b126000003180380100c42640c2c4111004040c640001008000c2d03401d0900640c8500640c038910107030340f0341c0b032070003c5101a80000c0201c425505042040307070500c01c4660207130700ca0750741040542e8418400c0742411821f80b15505084e805217850029500300503005010f1107401181080050705160322001e807811a1904074000003192070089840018256807000001c0449546001002c81e40d2458140080c2c00c01803503603c000c00629410a403d4802d0380e2002c2c8003101d54200440c01a01c07a1070700f440590091036070901c40c40c11000d43d50188030500c6000006000c0607080700304014002c40d010401103c15008521406a07001441a45400014050f074080c140c2400040d00361070a00b540c440040112100340242e98030550803c006004480d01d40480890140024000302c507540d04265449500340540d9104134a0b0540c1d07a048912004c2d940d41c0c1200c04000f40050051248820 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 941648012 1250 941646762 941646787
    0x10915050a080903120403050927090d050307081311221b1205040512040b0c10022104170d02031e0601120b03071503141830 55
    0x100c50641c003040c500c0000038400039000040b1804c900346100c143e0b4260b1603075a019542500030509841e801504008408000a000314075649005070703004129860303007070003d4901e003000e5041d502041000f404100700044290800071310340e000402d808001c132246105060903081c0440c0060700591150421034082c01c2280420700341c2e0b5420460780c000b0404508004000580400c0520310a0003265155610000b03504003a40100d03071250055044d80c69210b64403426444951154001007a003c034041108200d4507800c02440200c100801c8046142112984072400c0414100c05560b01541349100080c0420001406c15680207950710741d015110142020003501a41040b035005008459101200f04048160035a1600bd24011703140d60440301213582c1c500c0060f1210404d4290144640c46001400400020000940c60350720f541c0040c4168405034001c210110241810b41d1131504c102c540c10f110307280803461f60250006440c1c20b81000c8100243c3c900c20090400d0302d0810904041040002c102c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 941649262 1250 941648012 941648017
    0x11011202030108060709140109060804170714070515030a0e0f0d02030a030b0301090b06090c0f0307080603061806191803030b09071404030803150901170d030608030d0b01091505 78
    0x700ca80d101c2401c02e0742c81f101106050943d19003034600040424074104095400384a60390f0300540505094120f010b00ca0310600e03007903030101004860800860307250400c00e54051111801500c4125200b1161a80e00c498000c000e00024028290203030391901810011081082152660103419080c1d41d049400c0000280d180d400040d00307400440d0070200d6a24880c07406104900040781d00c03040070002c40d21400705100344a08010008044070700100000b1040c40c01c0d5001452203000b03580d840c1440740c54200141420840003804408100556030070388445800049002d90380003013140a007030b10380302410284001810710b00c0e01218660340743c001b4060905601d83c104175800d0318140c8502900d6102c0400803109403c0803100c1c180028000e00c01400003504480003141c102c5e40c00440b112424611500003603010000783d0100401c0580c480e40c0c140b20071010b1140b61498001801c08118540ca44000c2c56100d105e00b94480341e090384c1d508220351240e800307070b0400d0000e4609440180310f0342c80d0424020300140d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 941650512 1250 941649262 941649271
    0x150605031602030306031b0a03051605100503090a062708040905180d03020702210f072106091b0b04060801050a082122170a0201020a1101120203010806 67
    0x20801c1c12182084a40000226402020060014007884503c68550000c0158904c4c070941d03c101e55410000200d141005202e203000c0c88000e103180060b20704020440c9000d00d407401d50041c490240304000d0340900103c0ca01a0044e0081d10201d07140c240790f40d2801500103529103084501e00016443d400f1300940c1d0010b0020784145050401c004d0325000304030407203504900040b0582d68400c41a04500174406d40182c8040d45c4050008001c607400604036440702180c402c100302890740010f066514048003049808014000040c030320f100b900703c0304400042e1100c081c02c0984400e8651140c802007181c4074030011000c07042c00c62182c0b191500e9100d41c00d07803640240b180c03138006581e8400224451038264140ba00f11010a0001d000700a0803030310090b801c1d07080213960702d4232010500c0507003500380d00000b41c0040d00c1002c20800f0403040c207000b040f284540360700000c8020b130303808020820010307600010001e0f801900311035440b45105010300101c0703000b0320441c200e410b040d0000c00000740c800c07400035265019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 941651762 1250 941650512 941650531
    0xe07060804110a05060a2d02030d0606090b090910080307050d0905060a1e09030c06030b1315180906020424020f0319090f0f1d060d02040b0415060503 66
    0x2c08844400b040b080440f075001d00c40d0300160400ca0b503001d003030041d000300070340080d21507a103c4108030303910b010b6991581400140015810004e9004940401c0e481130801078149802c04a0b0402e04040c01c01c0d400340561b2401600038a0f4050104d400e45442c104d601c401841070b24200c035902d507100d01e0b00300d85805d1b9030108080810700e8000046282e01e0b02d01b00f92010484a0745d01e222030311030011703082d100745c102980041090001402d4040041043c07508510040c0641d03403000315883d025070061100780a0307400000000139103803412215083d150520380320100d950184403a0310346a003c3c1d403170f0001890b6500000f00114400200004d000000d80b0007203036400c0d289105c198280150203002d0f0b8441000419160081d001007140c0100317440d14000e404101c004e030707180040c1c85581f114040200b05e1b91310f802c500003c0754290000c00200c1100c03040540b104640191101042c04d10402158450b504010b00030322130f688440c030f1500300d5107442e440000c4280f4600401d03821966a14002741240e4402d5594080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 941653012 1250 941651762 941651783
    0x50c031e0d0905100e0f090c041e0b0d020903190b0609160f11031b030408011d030427020d0e0d030608071401020307141b0d02061602040e07060804 65
    0x4a5020b500340700d085032000303061030001c0740700518215800081d5410960740200480140402912050075042c03103a01002c10035503640e41031480d900c15405c1c9062080c2c41204c03506100340002c0003080103444128007c480c1c007584505140d00004c1c1082054040e02001a41422201040c080c2c0141c165000742e60903641002c0c681c81c0da0760300f134015028002c082d0000c1011074202002c2d0600c1416a800b21000e4181600d0030800c84010007013402c110f80c07034501c500b0350012a06102d044070078850560704003009801c2c81c804030041c0c030450392a0f00507803040d481d02180c5039800b44102645054803444800926070215685c008034010400188500d8100403404c2c03082d441c000b034109002e407181c007040d04d04c140010000185014190b8540c4040100e405046000038418080004c03e0700c0f1154003003008032409013140c520740781d09820400c1d030032200e150b1144c10711313403200c2002d81c5585040722000703101300c03080c4025030310540085000341140c0d41c001035040c0700310340c4005055540b0012241c0214858080c490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 941654262 1250 941653012 941653033
    0xf0702090a05070503150111101b020c010f0f0504090c02030a1719090f0203070609030b070201050f0f060a081006050103112803090b0f0402101812050c031e 69
    0x2151403c071095004a04c0820208100311003140590341d201c0c03414034107280e00003101c405640c02c0251707141c0c1414420340c440c040301000b1805010b203c210210144000c0100030000b4000a044019008036072080c00b40c0c00c3c220703c1145100c1e60458015118886050124445024000756664000c036880000120350300104d400c01c0115142d05030082a04081d00c000c5061030110000062161a00848190410b4101d103001078600f841007100612580d100e0004252950400c0c6450b482c0050000c41107901d050304000c07a00a5400680385c101c1c0302000c2c86c5602c1c1e6600740100d0b0084407540c101c81f01620400f500450025402c2e08544265002030340c050007803150b1110204040d000c0c2d003441e00302808404100f200e2042c0410741b02084403140c0c0c5408075002010391181500500f054404400000e007c0c800c100a6040291821400315039502e41041c84140b607008605400355280120258458a80d44840a001d000c01040c0b6601c1e03401416211009292603120300c01034403503c40500203000c0c00aa40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 941655512 1250 941654262 941654281
    0x906070306050310270c1d06030303040f0203100f0b0a060e03060f130b13020f010807081f09020313050c1e060f040b1603120b06121b0f070209 63
    0x6045800103402031120742d40c5070300060702030100d890f68a0000032841c000f680c0b51200c007181d941700380c601032866200c40c242001d80c0f5000415002450220741e41060081c061581c4000084a50040e0000f07601e40c000003061000074107200c00134030441040707418041c60b0719262896030f1010051034021102e0040642d0b8504040c0c49118400d840d07254180c000d0030002e00d04041009409600054105140d10301008650780d01017605030a842c4040070412804188046060605c9541844002420000428038040500800181000f17018800506039204018403014114a000c000741140c8403040d912442c1a9a034508929000c80081d58607101e851001b100c5030921014000740c2c1c5090040c0c42c001c140c040782c18402e050340301c81c202480046007000002500124040501601e11080c0c0c8280250740040c1401030440401111504801c1d1520b115100e06075a02004c44d4042c5209100f030b01c0243c0e44091140000384540d4142a03610751000034200094842e82c001011168800c070b60f030804030b881c0e00040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 941656762 1250 941655512 941655521
    0x90105060d050a200d03080a0c08090606010e030f0307050f060f010f0e070e120a11041104050411040503060c0a030c080f0103030e03120a0c02041a030303160207081509060703 77
    0x2400c00d4000440c07403808070360310105100184111300c910382080b07054003010a24050b1215000d4000030303003400510141403d0f071700508a042c1c2c0039140038241414598110b503111003021f04424107020b000c00c000b10301900c050000d00e2030802210145c9403504160708096850302414081001e0602801d00082c111929840c1da543c140d038030703911a0012650521204440b00000908100c0c103200940500303644541c1d41040090005007028041d0004000e40c0c40c000400c6800c0300e1800348a14148021000c5203880c0c00c081e50111181141e0202e62041c000b6031001c0548243e4110a0301802203408110440e45650010480e00c040b81d5130411160310800d0080b108408152a80707100340d2100c2004001282c441c500280c03d40744010107030b4240c40c181000452645d4041c1b07500001043c280742a58003945440c0c803424042100e201c02c3c5150071800c6400180c2c8030310005005001c400194909030410920812144e005000070034201c8a80c0301c40c180c844c100c4484110746103002032050400045e200e0b4441d001c0e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 941658012 1250 941656762 941656789
    0x4050117030a0c0f0501062d0302060306100908010204060306031a0114090402041b1805060c071a0c0a050a0b01061b12030b0325060c0c1202010302190809010506 71
    0x2841c00d252220720100e43c044042d42c4242d0b0040400c040920100e10f00381b046400828206600f012001180c5900700c0180040101182da03c440244003000940c1b10314007241c0e030020044540c0004052525820f444881300b58114121070762002c00c0100d0200c3d00740c2e22500030369000703054000240340e500d02c00c01001042405842c8000b038040300500c0860034004152500148020700100c1e03100881c0400c0e444000f48100d014000130003103d025181d00c40e04054038030140034240c80051034407038000819950361219200c0d03c44001072040702711110091350000d4800c448800b1007038070340300c03240c40c04d009984112008094428008400000408601403145c025220b68040c403880740413410340e15001000c405617082d640a140d00d4003c1480103560a12100417102800f43d99507019003c4e42c0b2108103042015001b0f08107014208503c2310100b2024650041290441c143d37058505200e8030048002e03000d40304a0a04d8480318440150401c0d41000500744200c5201008000f15038903d810030000855030703003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 941659262 1250 941658012 941658059
    0x7050601093c0e01090605150307060e1507050a030309060b040603050d080603071703031902040819020414041a0a020f160f1b1d060a0504090302070905010f05040501 73
    0x2081c0d48149502191800003002c600b1000081c581103981015094401484045481035035a4080040b1490440303204030801c5400d400600c03c082c20b00101a00741800c041000784610700c172952800c03e10881004443c40d4651010035110104c19078680940900041002260041d0030301d100d80703889007054801c0d501220380103401800300340350384a401d07182850098a05501402101d40c0452a103400d179421302801485d0718010f6503607180951007105144444d100007045240104820000c807180011540031010846090f40e56001040c0f001500070803c0b8100d241c0d45000e01d404101c04e03c98494943e00c10520b0f0b0103001141d42d41c585811404900c43e14142c003281c0b000c03d00c031503102c04041c3c03010030050612608002c0d100758515220342800c504103041c2c009041c00301d07910600c56080c3d02a48880102a10b1141c201c041c1040c400041511406004071406140e0310342e000000c0c0f500c204852801040b000108100135619000305c42c0c141d005501880303020358107082c000110525000050182c140811 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 941660512 1250 941659262 941659331
    0xb0103022106150f0405070c030809011515021e07090209040b09040b101e12080d090c050102070b160f03020f1207020f0f0907140706020705060109 65
    0x194200020000030101910681c40c0e034a03144001d024040200901540b02c01c049219580024003c0102000425407154003550500c41070001c0e043d009440c0510b9030740d050401d090503507610007071980100b0320b4090400810115160024001a808444486500c905c0d030a481c0c41c41226540c003492100d185104454a52140d0b500704403c0314264064807402c1c000900114900d0a0040004c0c0c0035141070f201940c020034290301f445100382c0e003407000400a12940140342a514070800308030b000003206205140d10b103d19019641d04001c400300032134012041c50030040042030031074101092030f00080c0c0112805849201c4001c0741c0444c40d03c040d03031140c2d00032007085015003c841c1e85148000c910f0f280d0807000d40c81501c039500350b500130a0010a454950400d0656280d10a900421070342e01441e101030303070203041081c0f508200c42d103940c0c00755903020515040403c8111240034a188c0180b0400c540a0601d03480841d480042000110344141260101e07442400101007152804840707000740c034510f10420542 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 941661762 1250 941660512 941660519
    0x10519050a05070204060f050906030f03031308070501180c090e03031302030a02090f0a0f0605010206180f10091b05033414010801060e061b0a290703090b01 69
    0xc100074003161240e4a0400e0814001d0350128059458982040302c502555a4080c4075a007060065554064000c03001481c012901c6000c0e161a444090700c8424135600c03c640c41d20502100500f2903203502d070b10900030032800d80a00c5014100304c800040c201c43c41c0d1008580001c020115009907d1040d0210b0003840c41e5482c3c009201840710403140c0c041740c240c05181e032801d001da0364201e21107100d03803d09450580c0c0f600e00280c2c0442120030700f9221500c590301d8140300b400b440c3d0740015100c0d40004080b1040301c50032a084002440d0403940d00c0601c6061050070703001e440d03018103500880c0030b003486585911480c0c404850100c44150140c01401e4050303200e0341800780354030a0042d41c02e03038440c03804c04940007911440c031250181c142950490314101d00e42094a817030a503441210303540144240d240c00301980c4841c0c400264203104116052000c0c02000c01d8442900800f4000450515480003816011099040e0030034440300f88080210b800040c91000200e4481c001d00507140c880ba40400c041e02e282e800e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 941663012 1250 941661762 941661767
    0x30702150603071a0408070801060e0a02160c09021201150c12090b070f050c090f0112020604120b0f0c0705070b03070c1515050d050303010e060d06090f0c05010519 72
    0xc0248529410f110784000000c40854841c48001d8598198000380d80e11800d103108189820119884541140e2416401b002195152002d03550002d80b5036001581e10b04005881c0303452003001c5800079203c8912210001131590180c0d0040072824081d12030341247e6a070360449234915091812007200810042e2540c440003405280c440d0b008040a8100808259110b03a140b00f8181c104040440f4070a442403480c4040c00401c00c281d41c40504200c40d514401e160220b904401380300b061207110107003003000c030560003150f0b2410309890140004a07050040e0300000d04108000d0017040d100342300c0180840000c10031200b80c001c1100e10140d00100188541403400405640a900081c0070340300300202440c0c85000100398400181040e0714002e00811700031908400280821074070780c0070381d1003050b11400c0100041d078003006681c115196100c1d40e4409a450341c3c04100f03001ca41071401411a4580340001e000c000341c804440c0d4440d40210a40842c00e80c03240015205840f410380b40c2c409200d00d180c0036582c002e2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 941664262 1250 941663012 941663053
    0x5150313060e03042102041a03070b0903010b090c0409060e0127060b1c0608240a2703031a010c121206080c090705041802070320010b0103050903030702 67
    0x103800a049925295131008042c500e440d05c150402100115000c0820a40c034090142e046212418902d2065031005840020740c1c3c0c0342a403080c140c000c0804100b124482e40c00317511002e600c4402808040c0305180c4034020001c258803c2c0640419207241c0400441c40000740700e44903068070320381e0341c503010010b401000740307006400380c80d40600c4270989490000c03a180045070082e20348a40b04c07011120600c2103200d2600d003503030800c1d00b1018840e0711001c00e45503101d0200c94019210f081040390241942c55041f990409086040b10409503030011640f031421152011035200556400303560b0401070350301c401001171103002102486030700003a5081d1110000c900310b40e40042003540c0030f0900381d01006032011428255079050b484880641c04c1040150700600b00643c0f0030341d00441600e041d620f490300380400107204038001840608110f41c0030601004250140e414280005810800c04a00f41e1120039041d010304051191140000e0030a4040380d90003400005481c09492560081c00441c80056020003204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 941665512 1250 941664262 941664281
    0x90f12020f0d0503180103150e042109090e0c21070e15180f2205030f04080c090402030c010f0210021b0d14090d020d0506100515031306 60
    0xd86500ea100041d942c070071141c1c680c040e2059024603111604d802040b0f040c4101188918103041c01d1944405202e600301c903070b10b015140d1041503500704c0e80b20307810000040800e4a81080440303102402036541030b90421000e20403105410010322000300300d052119215240403820740d400140364220b040303009116041e00c1e0030741c0800100312112a542c40300e510364038030001c1e14000c07107190387e1712401e00d41814a4100e59910f0b1600b10041001070034803602c5120708102c0104544111412a06190301c41c0000d81003e115094015013181d466400d03440091019500510540d4100c0c032030002c404000381809031615105130313001806001130004000056035061a8215640300714083c00114070154101c030320281044042c020803060908980d2060705107000201c45807901404402070082c070f08070401c0003c0710703980074080e9005401a02c0c01d10200b42e039440058401403040c040c6104101d48426a07070001400c41d0030403204031403d00c440500f0000e103440213030703641450868058802c2b000b0803051740009100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 941666762 1250 941665512 941665519
    0x50711010516030302180913021212030408040e01051207050103050601091205030a0206220204090c0302120105060f0d030207120c080a12020d0e0f210106090b0a06090f1202 76
    0x10109a203541207002ca012950442c04254041458007036000282c0041224400c2a95440e800382810100c80e40e07040c0d403401c4c0091007282c0c44e4200d40d100750f109010b17007400c00e0382c000d4a2944034145803400c400c40d41c200d409800f103020002c03030001583c1e242c0b411029031260039040191982604000c0110083c10307006191506010140a0000d00c1411001d280ca142030b0260b000fa6844201c11a4000d0070032402034192801000c400725100d4041c0c0015490800c090341c11100000c1000300c61400068040081e0700c00384d400105242c116002c000190080c0c0c2c40344104603120121601d1500c2000580004020060b00507802100103129001980e6075001405000748050741d8161756600c0b42d2440c012822008540d040582001100300c19010000460001c03103034105050405408004034160b8004151420303c00d14441405204a9510640c80004080404000d1210a03110f4403010701601e01c501101d40100c1e096100000c0b41407045564030151418112041407091030701580c5d20b4550368004c41640e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 941668012 1250 941666762 941666767
    0x10b0904110c0d1101141e13120809120f0403391806031a07110607020705090108162907110f0d210306050406062106060507110105 58
    0x1180010420030f201e0640c5651142c2002c0501100c250964200d9900089074042074002e210003a04181002d90030103941404400c103035036034240104540e131002040900384011054400010030360000f0340d14481c50001d4211783c1440d8100202241a1040003200840210300340410700005450002c4c0b0f040316503046a50b41c803401c3d08034040500c104c40c2803414100b0780340110010802d40e40c05130b4020001c1c8800303642c00c12905142d034440102601041040c84046410000041c1c901401a00340c0c2403848080780c111807040c0781581010f55124100d00480d4400c1a103400001031111000994400da800d0407202c0d609050b103407094202110102d03030050004524241c10603080d041c54107020303002240c01441e000c20030310003141c1030294070012030525a02503020800d041e00801c62903404c0881e4020200c0b201000e4864404d0200d00520141d0811648541082c0c400210300da80007805100d0010001d13803440306420310440c2681200c1d018410000451428005200400c013a0142080801c4040c1030852 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 941669262 1250 941668012 941668027
    0x240d17030109050708010905040201020c0927010e0f010207050c10140c03190e090712090807151805060105100504260c0a0f231f0215010b090411 64
    0x104280c109801010300301e0b99500c2003090240c0d00440700c500400c3d407804104180e0500b500002d44640d0302c231a500e0302414200003c00c803072444401c1041c64040d00e54110a244a6001184c64041d00e46a0340510480c450159070113000c60741032003141d080b140c1c0140140760503c00e01042c403103400140d00044c000c0c4482c2c41c402141040d11031004001d5180210085d5a940d110691620500c6000550840400018503203807070702038586948003900a181c41c10120701e001c50700400c06000c6d01d4000c1e0300420091010880c0e4040140b02a60000400400041441400030320798080700b10940700f02d0050100c1c0c1c0304200400c09030400349e91401d403ca85500d800791500f500c810100d003481d211400120681104016007500101c0180a00300030300b0022030b41c60b0000c42c5020401009034400d8011b0000c0348018081c441560000c4060280301020050100f02000304605624a64441d40d070101501600a1003400100c01582c11040e0341a9508519085d01b04050b01c0284001803040390440910020f08001c8030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 941670512 1250 941669262 941669303
    0x150d23031303030f08040f031d0414010e22080904020d021204140f030d11040305060103031808010b06030f0a0e0106290c030720100512240d 62
    0x1098007444644102500c0c1e03241d458018120f03109040304100f00100c4105100000b60140380c1484910f81501e010020903101000d00c0038114070140c0c00030350107480c01008070b0440700981e60103412a014000b00040694504000040c0910458200d6010111003002c05000a03e007102500c080340c00a4001410180c030303801c522040360b0101d100c2c41403000c61641080100f1803030500400001c0d0220f005000d44081e00c0e0b1115035207015682e22000e03802e891700d201043c80d0350040d040c2c400560b00001190317504d50b541d0a029106401800810300d05410311003021428020500900043c0417014010a1030340c0c1e1000642c2a0814000e0080c40d03074a9100c0b040d80082407000d00929002c0c201302468243c0c855103c16207406031182d18194418111402d00c010300f4a500d012050325650f540040021b000c80b2280d46001040080400080350303c40d40301110f107445079030300c24041d00450807a400c200c0c07120b07100e00512a94070308410000b200300803940700e000046400e2480744100720030312603013090328003a503151882c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 941671762 1250 941670512 941670517
    0x1060b030c030103022d010e0111030304120f030b0a030605040303180b0603010b010804020d020f0d05070902031806060f1509031e150405072c150306150d2303 70
    0x400c400798501200600651514017100314000342c0d80d00359a4241c0038003090020305840c81e20f440b607040c420150514516030740507902c0c51484e8a11841901e0b900c0c030741407074500b8507440980e2400c4002100c001c080044a8040d1082800303c20000304103880d00d40ca19a00c16000d058000d00032010561180403201000f50503051000c0f0072413080500d90306e1840c15505144c02c60710030580c014104040d070020301003d45c8071282d51605031074064990f80c403a10074440c080b801700780302c0c90001001481466000200c06240e03501031402002141c0e101c151f03280c5070301c220503034805003036800302d40c0580010040000c03441c02106501c03640c403c41641c0d0b410039080c040042d040409010142140c104100b88e03003070140d0001c0c044242021014403155082d8201a110181e80c4d00d490701828003480d0fa40000365031082d203d240403c01382c0c01e000c10020070384c1c6801c054800000d00c3c03140d1044c0c045c0c031581e804540d8004034407100d4405800c001c0c0580c100c40106458a4400d01068001d1940e03645643c01402d1110070103000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 941673012 1250 941671762 941671771
    0x105030106440910230a1409010b0906040603050c0d1106070c030204150b0a0f031b1808010209030309041e02161415060118050306010609081e0c090901060b03 70
    0x1089040da10f00069000d003420f002407201400d40c0d00d4142c040007032600d01c2c1a0400c02c640c0039841e01c680390340c5400c42280101101352030034909448003010881010b50540146841007802ea941000c0c54a412040c0400d0324079601000b03005805c5030034a066641490000d070000540503071001c0c00419400b02c0460841c1d44600303010745103101044005c0c41136041901841081d117000810403030340c0c00c1c0f0344016103080380112039501c000c001059190090980c401e1300f00c1900865818215040050207035030290074000c540d220030703003243c0c182d14000031a1138062094680c05207000e000b440c0f920745940d00700300051111344d40c00381034501c0013000a055000c0e140301803d0880030202c01c0f012450703981e08048007007075001034154415038450121405000364580380c15800c05800e0800e588034940304c808131100480682c100701d0b003500c6010700000b03485600c074a10804503003c04042d61490508003000310140e0322050000c13501a448404500c1c1d05041210226911540000c000540350f45c4400000f8603a0f8416503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 941674262 1250 941673012 941673137
    0x1a0106030c0327020d030e041b030b121e0f010501080105091204060909051306050c0901110c03070b030915011e0e040f110f03010f0f0b0105030106 65
    0x640040641500c2041c00c1e03000c09416003101071254160020140c00940c00090040317046845210425001e40c8040c05481d20041080c420a460042d0820000d0715560b2110700103420000d20340110305003214813503c11840e0f03002800c0c200d44c040d0024003104aa00119440b00c2c800c680201ea140788083c840e15010340340e8040081210305080400c03902c3d0141e40c5840001502d0104420408107420546117800c0b50741c004000309407603a840d65103c02c0100d0552010308800e080500300b1000210b448010180458242c80b840c02d40c181c906011583e4000f4030505c80e40680c0705000500c0700d0b000c88405950b100c82d41c0000c48030ba0700c5041c1003500000f0801e80c0b056038443d0450740020403152202c42003c01400f50308140e440d1074a03040c0c0719040f41920307140e4094040e4034000e20100a6880d610444112404043c000340020403140b550032004004900e0403200040c41d1210001c0558480c40889040300e0041e80d801c3c20b04400c40c4040340c240001a405022070803054841c42c65489207503907840c5070600814 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 941675512 1250 941674262 941674271
    0x150501060806010519080601090b0c06040b01080f0304050d0507080f0d03050a05220227010e0601030209090a0513020d080a0212030709032d0807050111071104091a010603 75
    0x2025107440400742000c2c0c1840301c14804c0d502c140500c8804001a041e807483d113501641c50b50001a26900ca25411a0f0241e42000600c40e51512000400c18040c910880c51001c46130398600442d500d840002525480c80c0d0000c21040206117009001a00824021025a44281d984010303042c94001401c1c0e980119801c02000d004904d601071141a03405120807034140006d20301f4100e415042d02c076000c900c011003070740090f181c41551100403100c2d04510f1811440b50003800c0380d001400250001b4810042c5040c81c0400291346540f1034001c2e0b9080f04c401074613a10094541d27250700c0d0080c1c40001c3c0a1466110061601c802594170741c460804414090f41d40c03980c0d00c0317080c0d5000a00745008004003401c50032080080c409203e074082100d60450b07800c0341c00200b259150813645903c2e0489440094506820850b01d0800d11500d80007c1101d503101da0000c00580c0d981250104140c02203040180c216001142010f095081581001c2e003507510804140061200700340c0c0000c00e942080e080000025540c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 941676762 1250 941675512 941675519
    0x904020c060421270b130504060803070b07080a0b0a030b0405010b09010317130902190f0c0b0a020f092d030c092205030f030403090509090c0f0d150501 67
    0x900c07100900314100d0003143c0f10032120401d409441d10304c0740d000c55a0203201c18146000100d00b03000f54900078000722548507565003411200208058032038042d10744034038030342500003407d041c00004807034020354054000d08155641a206540c044002441d01340c0ca99207170203040d0081c0d41c0f1850f4460255204106001144c00c1034141142100d1500007001d004180c0f000050000c14542c0405011952009000f1030b41c42d90400182074958456030300006103207001003030001c01a044002c20003480c42c50341d0350300c0000464565044903084c0c008030024049000e01000708e080342d0b10680017840003c0d10303849804e02c0c0801040c0800d4542d140d0201501ca01c5401c2012a01044000f0072610b222050881c010483d00b00600c0008241c9030000d010524559070f01840c0101c402214590f146203035800c5070640391503c800802c18480d0b079208a4044001030755003400865a450000c1106000f00c40d01c000800a48011030180700c1009440190940d004214603800c90004070180b103552182641c129020032107514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 941678012 1250 941676762 941676773
    0xd0f06032102060a05070201021e0c1213180e030a03050f090d0e091012030903110907050a3204031101020d0f141c0212010503070b0d020f0904020c0604 67
    0x5a402014050410340755500000c240d00081003500007000c2100001e843c2c640d84000d03070080c415015180344481c00084100300d4015448040d0078541000030544141420001a400350b900ca0485108244001407809200000080180c4105003041c40c00c0006c60700000070301c103032031a00800d42e080c000a84038400c008804c03c180c2010f540145120b001000c10001c0f181028080111f041c458034000c404140028070810000305a050003425942c10618000001e4100100000001c0c0015560003c2c00a1b4100580c100407006520035112680c1d02400c0c2080e41d1011200000384009982d1020a214100c24501030b1000105a006482415007aa80d07840c0d031602d07900c1031640204042c155000202c083c06910303000f0540000390040307880c18400d03c080c02c40714001c1c1e5004607040300701d00051081c1b4410940781140d0081002c0082e003140a51240ea948040595410b900e02400300c4804092005143c50440f80e0007414120000c0c08040b41031010b02800b1904a8000c0c1903d820180c0c00f400a2205105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 941679262 1250 941678012 941678033
    0x2203050a0327230709020c010b180a0c090509043e090a0b090f041a070302040e090d020d050d110706150b0924070c090501050a061806140d0f0603 64
    0xf00c946080800e149041c00006031903810354800d02841940004d13503040c8400080d84920520000200904007600d0720309004442d11000f1905c4a003024a040c04442240b4091b600280c120341000f00865002d030384030741d241400b8900416038800d600700d403540001c010a0000018000545110031360918006440e0704001d50010040d0011103140d18107603c960450710b6201c0e1113a8086219510040f171fa8983d40341c4040341c0303100c1c920040c107401020001e05c01c0340359068004208882c06200100415250131603116182c100611600001d41d10419005000c28080c030081c02014008143c0054020060491841940e00c102c4040341d40d50340c0c848a005141480c01400000b41901d49440340c1410150404252410f08a0341c00c02201003200b603002d03500c0d4240b1011104400c1d4007880c0e01d0300b240da884100c0c501504c020b02078544a26112440810518443c01350000040d00c034481c0b4008952514205030b65601a40c003100b080704004021510030704010303001d0310f043c0d0700c2c440c400010040d1460034080c00d0003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 941680512 1250 941679262 941679293
    0x90a11060d1514180906070c0c030503040e0a06150f08090f100c02010e0a050a02010c02131407030617030904050c0f12091b031f0f0903050903062203050a0327 70
    0x404d0203000c1c0803c40300001003660b407240050400300202d5110b0b00788040400056070009040344400200071403400490703000d00b400307020003220038043c0310303184c95000142e14202c00b40080021400940f101509201c0c2000c160070440040a0360050302c02c00c0030700b074200040c00d14002c074090380381c00401c07856660910402407000c00e4040542680f641e25920240c440d0400b003400390401c01070b80403020545da030b0111009901c41442d00304201c40500300e0107050760018210b5000340031a28240000031421a5940c1515000500304080c51034440c0ba01c0411009000250040d60b49800522881c0280c609000040c43d0380c00c070280f6282d100e0700d0071000451508041000d00e20021500125805071610009031a030501c1c2094814a0840c0d2001c2c01c120b001030103802c01c04003a4605000c040d0041c1030700800280341c071401c15000d4500d1945c0c6d0092000c0c000d40700090200c44210722065040100344984040c10540d80c5601d40494001e0b060404010525502d401400c403400c841c02d161001c1201d0a611489003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 941681762 1250 941680512 941680549
    0x1f1511060106021f051b0703020c01020d050306011403040f05060c0714161401110316030306240516020d140c0411031504090804080102070209090a11060d1514 70
    0x207002011100111210045a4001e0740d05d403a00c011501c4241d22180004604155a04064480c030f220b00f40207588070f4507a5240c0c6c0c0135008522910b0364003842481140d20628040c1c40e1900607010700c07841e11240c0c3c1c1c00104181c4843d200e07c03121000142c000e02c14140901004411140c461140303003040f00454001c1900c081e02c40c0d00ca6401c0908990402c00807804481100c80b40d110507050b4200107989207210071410301c0043c04002200c04000c458000c4104982d4041e0390100040c58541d12904114104100402d6115210610b0f80d14020310810041c07031450068962992030641d40c0c0d0200f42a42e03a1400101d40b000e29142004446130b604100004032003004403400d001a1640d42180000e5200103000d1086c4448028172256070383c0c60b2608800861a84200c1d4250344e55600c020b10b500039002940c1c124481c802d8400410f80f0001c00044004519400c903003039114008001d820407681e940a03410900419803a01c3c82403250b0007003030329903070300801d000300e0003440c0600600e08001c2805460300d44000c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 941683012 1250 941681762 941681773
    0x21908130f051509130c2607030e01110412030216080a1505060109090b180c0309012009010f14161b0608010b090a080f1f020a02061f151106010602 65
    0x40e07698840c00e803094140d44500016100007446402c4507d1038204209115811914618407141000c9403150342c41503a55540400404a04460b1305090300d103034125640003804248002d100c01888541c4000a1074401d0040390450410b2128041c040700980c2d04c03101440d00105021024000e101d500590740030205003042019240c05400648110404d0164142460350741c01a48442c1d00d0740700c0a070a0038550801841030518200800103015801111a00155400c05a1455454120141a403580d184080381203040002081c01111140581d40d549020010b03100c0103036181051030300062810969030148a0b0320481c09040074140300a00c50742c42c1407420281082003001ca9400701c10075040d00e0f42d0758981030361380071100700086840d1440d030044140c9000710458940d41c40e41c0014070000003801c0b640c4480360308050342e81440c100c0c05030850703010240c4c20240024087c10500011400d4582008038420042a200e828078000811640820400301c1c441c03156940c0004820000c0500400e040d100400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 941684262 1250 941683012 941683027
    0xe25171c03022802030d0228020601051f140c0610061d01030515030610060f08101809050d0215130503040308030c2b140601021908130f0515 62
    0x8030301d8008540426440f40310481c4450584280103c1d01151804070083d9207400d003050200f50300f00080a00f0444500344164002c140c9800814414125a030040100c0e4103050340291224000c94202a40d000f002008030000d00280c445101810a81030307414001c1c100f9144c002d0603c0c442031000d13003150702071000031040b07415280010314854189100a203808685078480161080101e0058840030342c0c1400340d041000603c03410543d201d8102d0b000c564038848103940e4404155408101604c080205010008051254148420100d02c00c1c5240e07400000701010740b901c0703060400301c2100b48500180c0094410720401064240565000600000c21a05201440c0c2d543ca03501e10803440300803d003010100024416070299005d40e41d00ca2811510740f8402d00c0f0700d901101029040300127001c8111b1424141c00b180105945030248511410380050034076038000c10030941001081c0c41c04486c00c00003000b0b2400b40002008205006081083c0f4112340329040004000c4643c008903103002002070f0500008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 941685512 1250 941684262 941684287
    0xa0603050f0a09050d030f060e130c060c12080402010e0a0f060906050c0d1b120903020424031511041401090e092a0405071e030e25171c0302 62
    0x90120005c58100000d4540507078a41d20040c0109612500101c004c500422201400280503406d0483c4074221028405444203015110807010706405000c41ca508904546540d00800040742c0041c01418140c5006010400140506625420881140d51111380401c000c5800108502c00b0307015a04109007440e03555001d99542c0c130310400b200010070090b02c100000b4401c1c00550400d1044e000745002400804a003000340040348184000c0f40940d2030a04282c0c45822440c0170440f0a01003000c0c8a070400303255445180700c001c80101100c5020b42c0d2104044d0044074448014001050178214282e41c084000d000504058046da11a800c28280c49040040021001c43e00c40c07180d42c0c2c1000c0361015130b075103e8084c0050514104499422074904002e029805030007440c0210f074540710000368203050000d01c00031029542c4448040000c1d034044004107049984002601d0094031460b14a42511542e804034900d06028482034115650414680c1030043c8900340720b40e000c0c00c0450b04042d8603010040650 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 941686762 1250 941685512 941685523
    0x141302030a0c020d020a0b0a11220e0f011413110408070f171c031103012612070233030106020f070e010b070204060e1e060312120405010b0a0603050f0a0905 69
    0x1883d03042c0e940c42701c0b003003151145015900d2810b0407042500b00440061200d110020040c0500100407986070000303a03503d5844038026044e210801c181d40030b00c1c890103041c4801d440501c4040602e0980754100d43e00c03a504008c010708020032000d0300900041d031900c840c80c10004200e030407010200c102319400d500061400160780b82c0b60200c01002c0e051503000c8110880080001d002601c45061000000044114011400d4407030304d99142c007861817285890b80b1030f6a0f80c079804040740010080c00d2001e04050304d40000b003101425403002d55400029400c514480e020030101d448003211070b5010006100e8154100406500040c09500802240d81080308a6481c1c000522603888004c00000d640700031900c841d00040000e084e110f0070541141805518a104821400301a800c800d41319400581140780004d2041c40d14020820014a813a203102c0310030b4001c141c01130003600c26640f2282031047d26102d031007910004000c00c4e82e0000301c9080908110f180d0a40c080c0101d11400d0910b0400004110041103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 941688012 1250 941686762 941686771
    0x806041a010c0503040b0403060e011d07060e0a080d05071b06140a120f270c030615080708061602010b030606061b031c06050a0e01141302030a0c020d020a0b 69
    0xc00c82c041441518050b49148100d42100350f080502007000020405550029a4824201e4000b40b00b258900e64010b8032034041036030304080e5a88945020000c640c065030000d0010180603001e08040c0740c4a000c92840e04035049001e40018800142040502060885420b0300013180b8024000341841c1000040544400c0b64200f5002c02000584900c4039000c2e984046510380e8845050182c0c030071a5407100003d00303000c101d0070003888000c8443e0440a81074017140385031075031142e4a1100d1605540b1408000c002d007480128403c0341018000c5002030041142100410782c11005000d0340c0741c4802840d070000d40b494950b00c10b683c108072a0728419030b80824221381c001c4080d5286a125440c0b00c4102e040d01c3c1745a01703000528000024020488980c050140003081420b0303005102c0e0f20791f03660520030210b800340b10b2110501034180c0144801400c480d4150b04a00d0300801c1481c028420301c5103c8100c2c0d00070fa80c8200180d6071441c05044964061102c1d41d05942c0c1800074100c111440c1e1201d0000d142c0081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 941689262 1250 941688012 941688017
    0x20030418061d150607150603020906010f02060109020f130b1e0708091905120a0501061401080703090f0b0c0306030610060f08040f0f0503040801051609060807200109030806041a01 79
    0x903c203100070348400090b5400136070482c100380710207005101004014000741c041a4003034000900041c0c100c0d4090f040360007511545500801c0326a21745a40140250050b440ea004502e00c05c00020641c01c0310040400c2c054002c1d843c10542e20f510008041512503403038491601110401d100c0751002c9002c10096a1901d202560003003c00843c0409150050400790005588920284000c01c0348100010340c540503036115000800c203d54031500b4009808051540650000d0005000034207410f2203038011022084c0b260241e6108204c0d556030b200305c1e00c0d034212040412540c0100c04c01c00146020801141c00c12802c1054080d02410441c00902501d42e00d0310b2003061201003c041400c0006450162491507084020100361701c0306c6140a50726580301d40309030140d5608000104400845500100c000034070281c850100302494804152079442b0000c040c442400842508110010035409540c00c003194013000000d8100582d150203006802c0140000380154a0b08000b03800000108200055245090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 941690512 1250 941689262 941689291
    0x31204090911030f070314062e0e0c070515070509061606020d021c0b0102061602030c010501080133120507120b070e0d020d0320030418061d 62
    0x80c00e080c1c1c400400a580e8a406110f132089107141540d01241910540e84a0790006a1581221100c0b0344c0e1400141c41900c82100c40328500c1390094240c82c2c0a0840e02803c9200f03d08a5a5814038020b0f880000c6403101c00301440000c0702000c12a060200c5510f9003a8126450f1540c00c24181c000d0031406811201ea009410029014294656801c01403080c55486581556038010011103c000f039000104c3c10032103500c401031a001589114003440c12034681c182d0051179550344d800d0a080150310107103848010340c041081001310341d908c01e00405018003c1c450001c03c00d190f0401c0640c2502c081c8220030180000c2e05511040c000d40d00d0308000c0700326040c40c1000031001e01d060070014101091940b010040209080d036410400904c911428400c6080340c50300c01c1d01c4e6410782c044c8101c244514200030350040c1c405180a001900820030a00d0401500c2020b03035114440b000312a241d079005401c00c4440c0c0c1009178481504a8181c040c1c48041c000b00c240c0c0241c07901c2d10044080181ca4040d00242550411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 941691762 1250 941690512 941690531
    0x17090624030f0f0d110303010e040605041a07090807150c02060a1403100e180a0b07022d1b030706030e010f051807090b010203041221020f0c03120409 66
    0x30010424a1219101034a075043d04040405955010713256900c80410701e007640030302c001080407090701d0484622040300c0c1240e41d65961504001c0c400100100d0b600121074111043d5241d81072642d07889050749442d0200840d0030100102e1800400d607001c0791010912070030328503010f6400b440307021805a05503001c54455800300400d8031340031040503008014107004000c10011982e090030f2041140c100e0514003003142c490346109058000306100c10503861b4881d030b11000008024003141d43d4454618070640300d421a0142c048403528001000403849002c40340c0c00140c07600d005100300303680701d2842d02c280750480e001076010a4031020f583c4150011f0540e40c052410400300c007900b242d0035505010743d04002c18a006400394181860b2000c00500c68842c482c8080388542003441030b043c11000580082d8106858100030703406899400c80c0403074070504400440054880b41000381030007803040e0340141411f21900400185003c00f43d806e07d510961090345014490400e4004503401d451110302d010510740310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 941693012 1250 941691762 941691769
    0x30b120a0201050c010603120f030e0312040b0405011407180503010e1e0c100c06140c2b05130215041a1602030a060f14010b0a2003070317090624 64
    0x131b1a440a489031800041c502c4550380c1c0403151000c54072454070104041485605010740d00c0c010308410304180030030140464041480c0c01804c81e80b1500c0b0700b0022403041400c0c604070001c40816140d6001003846052140f003041c810b8170800025140070b40c000c004d000304400081750384141c83c0104116803907103680c1204030b100b414001034000f49009810302c201740c072100d040100b4030b0031002425664030380b8181001031640140c2d9000c0f070048000961050405402904445450016001d050ba013111080440c00032690b0b2030050a202d040c60319450b81240c81d6a00500144580c0144490b08022003000148001c00d03048005605110004001c25151940180428140c481601c00650301d40316450810040104a030400d4002d20010781042c007600070f20b00103e40d012070080c02098009a801e0007090300c440c1c40742c26180e50b18030810003450140c82070605024116840303014258001905c001c074100000115440e0f103074010155100a100c50b141a4280c26140c0c8900d20102e2003076115000c000b00140d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 941694262 1250 941693012 941693021
    0xe0a0b0105060a11010501061e050c060408090a09050f0a0608030415030f06030b0421090501050f0c03040e0f01030201140313030e060c10200403020a06080402011e030507030b120a0201050c01 84
    0x4d82040003041503507120075000e84207084207075441c09d174000c807101100c80091241701a00d07246000c84c0000c0102e5211175451030102d401003540240c001420f207600140b01c6075180266409160846800040b80c180003e81605032817568100200710740c000c200400451900090203a0700141c140340c0041c034154220682e0000c2d1039180c7c009480844544144010701a00c2d80c1148100700f01c89404c955004640c0728151039580c2184a8240420b4040c04401440c98512001303051110300350080d40d00c0c2c503464040c0c00b01504030030b844804010101034010300840d41c1103852414140810000907046140400100341c8660305000b00030f081140c0301d00505420703240c3c08283c950104210b0700f569010919001c1a400410240326800c01c07c3c1e0b0320080c1b40071400f00c40f008031801c0c3e0b03402807c02c10301d00d414600141e99251000d00f04a04006030f2281c0e41000e802118038000c074925090341c01080505154100400707070341042c003078980300702c6512088502c40d01c00010054203590342800c025448a11401e50a401070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 941695512 1250 941694262 941694287
    0x70501180302030a09050108010b04030b2e030b090606090105060d1b1715030703031b150603021e03100c14031305071508060d1104140a0e0a0b0105060a 67
    0x1140c4014000826401201804003003071590390b0990015038034001111105020310a10075612400c100901c0410070303440d5590350020840c940e0464541002c0605208110200c40203010300f000a0020300400c40c201c0c6240e034002e0701c10b10040555041c0400012506030040c461613208040c0024490301d010600d401441c0080b071030407000242d22201d07070005003008034042005604880040002180030144c90001d03510180301400807c031305411742d0b8080ea9500d824035920b907a100718a145440009010320781040310b400c1c011801196903807952052110404040b00040702152400ca180362641e100040c42c461600014040450702d055260f1040c0c0320508004000c007000040001000004141c4504a0303105030f100d881110702844e82c07034188490300d0700d00c060508001489480030485034a0000c1c00407030f03814014068078041202d140d0000e4103d440903004500d84107905000c1003118405441410200c41084020707092460440d42c0340007050605006461141501099481d2030300e00c10b10b0002c511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 941696762 1250 941695512 941695541
    0x319110312090319080f0903120406210c170606070b010e0f181b130207060609050c090f1003150609031106180904060e0312060f0411030408070501 65
    0x2078444003526681c00354000c0341c0040c000d2040e81201c02ca202c490021105130542c1201701c880c24001a00d0031160140d000d8034019905100341c4643c40d0390740307004000a00080100c1e032604e0200710750306010b55000314000f0701c020804c94581481058025080001c210a0000c1041e40d50702e42d40c0e5640000340c0f5401049406080881a0000481c00a14103100702d4000d15030200708088a03035800c060b8549140c1d01182030106038001030544054104202814105074100428103886502c40e5040e4000700d0700304a1065540c2d13511044104085c1c0c80c0b40c403038039811141030007030646400b000d0008107410801240d18240a5407120a0044400384207500c0203818896182410401d40d90f1400000d0182c1203e00055880240e420f61041c040d1801c5011281210743e041d085070860301e200c4040100c0d40800030420740301c4a440b045e0206201600340000c00c5415100140c10355141080700512034032160100c0030a008a1404a0b101c803280b60200580e644540d1244616a40e10b00500c1d000d0b000d403587d09910101c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 941698012 1250 941696762 941696773
    0x31e0a020108360105010f050105120403030605091f050303040501090b031924060315210605100f05030a1a090a08270d022d0a06080f01090b03191103 66
    0x300f041c001d02c4401800c01030030f4002e03c040d03606c9a1142a60103018416540030079400c01500160f0060038080ba43c2c45400b81c10001111591103011800e5000c045407800b6455822a41c0340b49241e144840410261809031f000354206070170100080c2034a212170041b810084000f0000591156080891550320302d1452402d00c24601099820854080fa900b038640c030b010204032002c51894401e1042c19030b07002d10b90030b00229551501ca4050340d0b140c2d948100c204401403d071070801c0414141d0241a0043e034080c00a480050302e0f0251948915085400c590300c41d400442404011503091b45064180500c0e61548090719160001081d143c0050010006c00c15940420b003182015a10851040c0c0c03641c1458000b03560084581c104585001445002580010340c030078082d1126034840106000188003800030030400c0c440b18005091844564040c0001071061400c010308000d02c2901c20340144515a0180030301300740000060780b964082c0703810440740c0b00d8804070882800480b0340900710b02c3d8006425640b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 941699262 1250 941698012 941698081
    0xc11040e0f07080303010609230d05100908030a1107110411070f030306141009030308060a0e0f090c03070807150302120702010c1e09090f29031e0a020108 68
    0xd490717410900c02d52020580c1e43c500000d02041c69104162002c1c007103600344110042003c2003090031500c85030259502e20504c3e02c040884a828402c3c4a4564041e050b490b44238a4103200b020300f40ca142c400c980c24440707000d1140c0000208142a41e000240b01241d01003401200160250036034004c41e0006403427450080f40726428150154042010303991100041d0200c0c00208041c083c1c0301061034001000034a00742010070101e4441c0d600d00d40c1000004040a098560b1040380070610502501d506040300b213541c00307000c017140c0c0401c01c0480c405820b0b03001c0c25680c1d180c20700046d100ca180f442080d0311a0b080c8a00d0b8404d03603109a04407003003103030303285003910b00f82c02c0aa0000b80206562501000425003001030741c591501040c1040e804003c460b44c9101e0550f0034200c072940507102101e601c01e1190b448502400001940c03600040d03210344c480700e00307034013000300344041510740315001902807a03850aa002d8110b2400c004540359401680a08145205490350302c11200b04c02940110002856458107524 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 941700512 1250 941699262 941699279
    0x2190302040306110f031812070615060806030a060b06190c110405190e0703020904030221090d0f02030709050c040305010f050112140c0613080d0c11040e0f07 70
    0x1001607900851003040040c4c02410600007038426070140c800b42c19000d10008004100e08814a40000368080949120b15140800762225030400f0750103c03411078030b850030740b10400c41001d9007000419092915a1150400c000460b072586201903000d0a00c0391121406d845a484040441c5d03d8100660030703000a100b50350000038008000a8412945007904003440041440c19001d1640201c3d500418a40301d100040c40b0180100b1800740813142a0003030030300000c00750390b6003800144581c0c000c0e000340800c20380c501070800c1c00c0f0100c40da1808034028207116070b809a48600c819099504d0340410b04138400200c1c0d0000034034000c9240d020520f51800c2c0300c1040042011130010f4001c89104200030300407842281111016604240130f030400c091510540306001c1111105048440d2001c0000d0354011210103010481ca40c2c0909500140e00b002d64078101b220b0b003410414400c5240313070fa180c47d800720000340c3d070786840c8201c1c40366800c0c1c810b6844815210460500b4444030a02ca86020100c03010382c2e9070341c1d100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 941701762 1250 941700512 941700517
    0x2010605090c1216050307031a0a081c02030a0c0b060f0909010f0b030a0b280204140109140907050c0f1c0e2707050c031315090b03180102190302 64
    0x1440c2680c403c080030071840207401081c10550046030b1102800d42d0b541c1c101c12030003810540c052000c1164200305021140d100d07840001d000d40700c501c000e0300b800031030300314880003160010070794800319070082000b56a40c0d640549110925030344480509195100c0000207030391400040769095000e281e00302400207401055000b000d0f4540d0700d02003400200b15900c00c150302e0300000d41300500340d2000780300010610481130700742c4004091180d0440c2e49240810585800701d230015000040d07603081c0d00403007403603d41e040440e1034003c0c11810504e80764415100007107185d4140203001b08091040101d03212b60740314000d10420046103101d100300c400080803200c81d5404815000c039071101060f00d110000f4100d0801d0700c40100b0403515145a01f1019008041c0d81040013801048030040200070302460a0800d420b00080081c0c951a42440c8541030800c0d00d04107151000c2c00203002841001001044580080f00540380d001c0d883d0a445002d01c16004819406846144070b90a2404400c132183d040460b0903502 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 941703012 1250 941701762 941701777
    0xf1709210918100e0705301003110907110a0b0601140f3708010e01090905120a05090904030c0b150f04270b010305101406060c0a051006080c0a0501090b070302010605090c 75
    0x115070f5015212504180307000001c40c00080e010741512812b030200340c00e204031030b1340d0402820310381007102d100c040d40d010341448002c240444440804000340310349582e0107c0684d6605182da1316240c9003085400840b1654407030351510b4201d0380381e10448544e4408003005980d42401503441810449109400c004001c000d003401180080e030090740000c42c0c0014107104001e0341c9540000100107103804d0b11504103068001c0c0a0300401c1040070461600240c6410000301d00980c82a182e1001c215460710b002e40e01d6150040a0880901003101c80c0354203035440380300c82101102c0565001400c02d0480c520305402c0c5843c0040030752003281d51800a8100303c017000245040741c2c040d000b40e44040121000c131805031480500c40f01080002140400c05900d0014010105590340c001180c0c804009941c8042c185501d0102400365075982c1e040403c0740c0d00d03080c0800c010f00311048401412103400c2c280041c0089030140218855240049001c03807c00d4002d5000001412005140951528001d12040300703c0d8010728 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 941704262 1250 941703012 941703097
    0x50a0803120903090307030201140c070611150f07180b0c061806010305060712021902030c0c01030b0d0602030403091e03020a060f1709210918100e0705 67
    0x7442c604400720a0b0f03240d255005010f044110300c0c6170011108003080d00c0074092904010000b00c884110f040009500815003a254140c0c44200081e44a08111048200c80b000041440801c00c08458400712303070354489542c1c2032003103034207440f03018105400c5165003148409500000d0641002c07100050624480c950600419400d200322400041e120042844010b1650b40880c01203080f090054101c0c0e0034480c0410801810448040d4542c440800d1032341c80714015800008500b580060305202c0b100e00c002081c01d045c0b1840f1110004a0503a508290010701802d5000c004a02010710034841c0d0740041041c5005c00301c5205004c0f40700070303010a10b444101d1007a0300003100051250b000381c2800b0002aa20384400d4643c8104142900d006540289940c9084c01001c8111401041849006503c6406214100d071503100750b00612000d402e8039507001e451580f564041222401080c6d00440503107860404601d9151039140382601e01d0f0007444100f0079800001c0314004034081c80b0f81c884a07880340c07046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 941705512 1250 941704262 941704297
    0x6090105030d2102160f111909052a0909010e0601021f180308100b0c030d09020103140c0711091e090a0803100f050136050a0803 57
    0xa00405030b031a19064030141c0400c02c2024a2140c128a4101140868007004009803410202210b192001c1e42e03464021188004a0380003071080c01503100b001c1d2910b9505550103c1000c0e240e036003420740c46025118507210241c4400000e0841c800042104100c00403400307415031124504803a900c00c83d04907546250142000341c000180d44001c0780900f030700510060300a00060000600d1540100703070a02c818085081d207420f0701e5541a010b00350101041e900079603501406080402d441c1d0314602160f4032260201d10709005010f490b10003c002c888050021441c0017910300d1503440140d001d40321040105501408020800c68410103203401402070510511315030401180a0040103814481582c0c1311b014040c207226000e018400d100441900060744208451004419941e02d0249500466100309080c0511300e08000a01c030030000c1c6006000c09007003400c8131030b9104c07800520700e680b614449001c46e018140120714006c1310060a0003d00340c00703054641e0b050b8403500c030107940381c0c0400004810740a04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 941706762 1250 941705512 941705519
    0x8090c04150b0a020717030d0e06060a180b030307060c2c0103110c030a0324030b04060506011205040c1e0509072109050607030c0e0a0504020a02100501030b060901 72
    0x144101280c40181501e0046482c0c00c0102003880e68001480e00320541c4141003010510803500c540555030784414000541d0b032680c5d04499542910b40c1000c180b2040c3e40204d0610286545010300302d01550b000d08608031807028800d60200183c04428003c603007501001400005100e00b07904440d0480b101500c0381c100d503514907802c0006a040d060320701480080f40074001c0ba650740c480c2c3c0110128100900c07072603050101c6190490700b19800320a0b0100425981c5c4108050146090380c2c4074040e091100e00c00b444189103440703a4814040c0108002d061a0b41c800000d0082d03800b407002c07403041c40f101b031000300003502d440e19101503014040e0040542240300d8038101a5100043c0000c10706884001d03054418545404400f903845158455403a0050790351070045080c07401d21481828603440c051750040c40715040520004e000c484c9100e900c1340402032940400701e100d865401d1030380c0842e1002e90f40141d403843d400700c040342800290b520b0307210356900300000002480311401ca000d0007610101d0b8141100d0346d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 941708012 1250 941706762 941706769
    0x9170a060b0603090c09060406090608032805030a090c1e1a18040924050403030507030608030a0f020118110301060e0702060114031f1e0234020d0308090c 68
    0x1204d00000c55482110203030800e04084910a401260241002c07440f1170b19030700d9403000d40322240c1199159a0020540d09030803840a2034141e5100700450b441450135000950040c2a0b10000300604116511400c181042000030300c0480c0040481c58108107250441d00090700c14042644200300c05410032580340d40c40007141c4000c50341403074a0001d0421041c1b00e04001d120191450b840107542180e100311100060190403e41c0080c0d11011800010f0203140604e00a0103c0718060001020035103840ca040c01100c0d00041114003000d403500b415802c600b108901207001d8200103003408035000d080710301d0000308045402c825002d207030102e0092100e1910340d070342c03103407024000c07504100181c0c00315004000f034150454603da8064000740982d1b5060041d641603140880c0e005140c00c0d09680c0c1d54101d04480392803584291012340c42010150315041c2410308050030305e4103201002e05031b2990171404503146104200603001459010b4903050340251f42d401d000c0c0103120221100d10280c090700605000514 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 941709262 1250 941708012 941708017
    0x902090325050405130606060f081f06081f0602010e1207020f12010603061521020127121101080a020f070b07030905010f0515010206011a0a09170a060b06 68
    0x403462408819062800b000c01002d00400380c92001594603400303c0c4004190140106005000691100307500a11450002071a5000041180031049407110100f00940400402e2034126190307441e0191050719103028190403060520744c50a0b4140c4002c3c0700281c000e0301074000408241080702500c2d0101004005400d040c420644002e500a10151203480545001c0c0010f8018486c5580001480360b1265507807821644c84945045200540c20000c200070011825002900340484208001803809540040c249010764140c50801803124103403491110080141000104520070216949480070304108041480b000c0c030782400100c922000500206181c02165a000c0036070b11124034040c07154403802040b00016280700c04142e1620340c0c05010071001d00406800064601002950f42027807a003010221001c0854541950000001002181190200f402e00c0105010000fa90307010090001c64007c0c2c0d081d01b0420321a0401008154061070005901c0c0e4264412942081452590400c020150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 941710512 1250 941709262 941709313
    0x5011103130603020a180303030501050f0609030c0f1c14120406020a030507020103020f130807052b050307050f0d03110f182d03160503120c031309020903 68
    0x350910000c0040c0c92091340106010081e9144c00f24a0081c09240170000000d50350054000070b8548005200c1c521f00440d007500c01c401c04036540c510302101c2e00c011907100d684001400340b0403024902d01280a4442c1610411100e118541e03402c181401d0f440c02d14240e0315800094100b0388180c0d000e406100700c8a00445050783d1554000b0654012140d0341124a607001030310484c1010380a2000d010300c086200051300f40e403200c81b0b14094286080100940c584209a8042c1d8461100361801800801c6654a1123482054000e0084c3c40c00c542d40c10401d103184a102001086840303482d2200603040004a4505548041e50fa0103009210314079035010503d00417201c1c1900c822604010150b602088201051100f00c009440c40700c0d0007900710410082e5030710707107801e4178032000c022000305400d46001d02559590074000c520f8001d01606080101b559151060304a00c90700800084c1d05485802c00c0003620301407030811028070944da440320203000181d002152158028400c05544500f03000d00404800040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 941711762 1250 941710512 941710537
    0x605041e0305160c0e1501031a0f060903070b12010e01050f130f060b0f130b040e040b0a020c0d0306080d08091f090b0705120a0204060804030825020705011103 70
    0x41214865061800d82101070003184c900c1c0621500140301390017000b4031441003401c4800610320315a504005015071350200340300502151610301c0b003541981e8030000000244021340e040f0f51560400d40202e8600441c2d40c2160400e08004580c8194400540c0041810707200c803620312240d9070f6a51030034801d80d4041040099400141918022013003a820342c000c104030116980045802985c56902c21060360207002d40e10080d81000560320415047d20312030900408050f482e262805281c04010300d80420050030003083c55000101040e0f00e080140c058070001100001504c403400c0000d2000341c003d001e90f21a110780c07401142106504039004240103480740c0c1082c0050300e44510120035450010030580074a00c04030369a810100d02184110313144070320481250304c581d0741d02d600f040d101c8000e240004144200c000d004000601580d64041c94258000f58941002c201d60f88a155a950000032400030520703585003003a00d240034556000400b08200c0d007013a2504222610783c0d21040f5240e2280c000c103400e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 941713012 1250 941711762 941711767
    0xe01180b0114180904030206092506050901120f05071d21121c29100c02100e120c2b0c060f141602040b06040b070605041e0305 56
    0x10b045a0300004004080c0000c01c41d510811003500000c08445083d601500107078041d00070020080410003090a000140f40c80d8881007c481c0c0480941c44840b9009507000c02801050f0013009034044d84d440d8901d40741035901070102a45c040d1083d03009140454880c000290301d135424050f1850807014021201030068040800c1c032030242083d92460303010006541a6101d81c080c4a0810100740c000b6026481c17481c11662814500d207209501035074100b660350b04008080000181c0089540301d00d800711048241d81303152070752180102c180c03910005c01502035002512400310800f4250701840101d260f5104a0320342d418501c0400d01c15603500c42070540190170451a100b00b085140106001c0702c010241d8a8100b124503ea956424040c0c607800e07440000401c078010320318100d0b00c0c0c014801018041c9026449070800c51704100100c0701c03d480c0c0b000a4050355444003000c000b6140c0c0c2c0e0454000e00751400741c056840c0c2c15441c188008040448041d95083c08001c5c1e8580d80c0d8154108403a22160103030303907090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 941714262 1250 941713012 941713037
    0xc1c0509030601092a051b06010302091b04060305150402040e070807210209121c0801061d061809150f030105010e190b0a0311040e0105070207090b0105070c0e01180b01 74
    0x105d41a0700f07051301e00103002052041e000318003007007407000010217070303010144c503455142d403060055625001d400043e84460480b58000c0100384803003510100d030388a15010402d41c0350708890380403402400384400c3c0c20a000042c0482c040085a101c24040e0748030307560b00060341d03454150071074030a150121b5542d0079007400b1005941c651b41c02d40142c05d01c0c40300244030440d20361090030380785d142a20410030b40e1903e00800301603404058010040398010302c020309280d2900040e039065071001000b4080c44130302c948004030722610310451201c001001d100024029503000d00b81004405205a034a8070901d101d0070105090001d1414180180d078102d0340f00305071106d202d803a00c181120080c8140140800e1070f5540e4401031031156598913461000f140590704031048016004180700a03640f21075945040c40c0e04200512420aa00144000441d09052030010320300c3d1203080100d80030b11500c4005031118806560100744618102082412980c0e600591910301d40090380c1081a03c50045102e8003061119401e02c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 941715512 1250 941714262 941714321
    0x81509070219061404050d090902030609012105011406030d0306051e0d0501090b070f1704120207081002030106030c0c0c14060f070b100f18020c1c050903060109 71
    0x50703040c0f04400c0418051800c10b1044201081100d060352180c1c0081440682a50407440c45000780603060300540c80c0d898642c000c01e10201041c4107101e020304440c5000c244101d00d10604c0d407801036000c1c0080c0b140322084c0700c03a02c21940c001c3d90218481e020311050b0240c038034024420304085031000340c0b2031b07510300441e4501160240c1d0f81c21112500080040c181900080c0d0a1040b5521184148019621401e2074000102240c020050b19000e01c407441100d0050f88030014401d51344507503c40581c1c0250310400f5800c0341028811b501103a8207229400b1101040e60b030680240d4141d4469560400c6269000710702150816180d080c050501c0d00c2d00c100c01e01910b041c1009030001d1401c0544250311746100b0103120f6049621609060f507003140044180030200200c0281d45c002001503410740c1c01550b003890607910416082140c118411917001540120804003800080800d0568900c07003805803ca00380050120340c41154103074424003a42c0000b282e03007582842002038554051080810300c4082c90182c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 941716762 1250 941715512 941715553
    0xb22050c0712020f060f040b0411040b0406031a06190e060a031202011505030601081b041506020f15070806060a020a02151312050c0603130c03030815090702 69
    0x1840110404101c4070000c15144118444644243d42c018404c2024411308039040803005402400000018014040032803102d0000c5034201e80c2003259001810024800a0010101d08604da5009414910000305003d030030142440d5826056940303100d1940c60000b003119048039103a40d00039942c0c4282040c0a020f0308400000da1010000d403003411a1900c030b44585007054000c800010040c3e441d264031070b500e401a8002d0b030008cc00290003c01c002d50500031420303141d00401040305003007110100106c1440d5100d800951003001c2094200500507182c01000b03441d0f454880140c04a481403c094140f4005032007455481041346a544200c0380d00c2c0c1e070041008079880920003c04520842c451100540d0314a800303180742540380740a0340e40d04d04a00003031040001c5207520402c00c910030f46141d440428000700d0076280c4400115aa1a03980c0d441002c4441c0140c94458003600f040000b51001c420190807a0505000703c0174040c1c02d03451440d16100300526250111500030058002c00a41883c56031500300d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 941718012 1250 941716762 941716771
    0x1090209060a141c020901030e01060b03150a170a03080c0703211e021306030e0703030c05100608030a091e031502090303030c091203030c1215130f0b2205 68
    0x2103c40c941031981c100a0343d00b140c042c0e070641142d076002038a4000e40d1b8051240c1d0042e80b00b800c000f408072030b00d89841004503020041410a80c2041d010000b03004d0340d16010b105014108920300811040c12500b4031a58a01e44e00200b00d000c20304031030224081c81c2804042e501007690664510480c8400501110038500d6a507810f0602d003521001540212941a00040d00c01141000c1c01615041d013807412403400790842e4403407001d06280442c00180c6a0021440d07d09036030305070400d9485921076140180c03600820100300b43d201880c002d404219000080010120b0026130754803280280c0e200c010302c18160b405c0d080304509000714240b0400018065610040e25101912801410a4200d80101e42564000c661a10196400003091035031407400360749038101c17034a08030021425450f08100c150400e100300c1031000754000c0d40d100040c15400d0201500300040c040541088481005111014003601ba00c464040c0003e0411010303000b03c0c1070820240b82c625000211441c815207082040200914020b00b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 941719262 1250 941718012 941718047
    0x1f0c050f04141f1707090f0e04260a0e040b01081b0c0d09030506070201020406140c07030602071104380439020d1710051905030601090209060a 63
    0x40229400315032910b0f4030649000ca0721111006070b00110613840012004020406009100704103024010520b40b0407016203800040010707040d1a103080030120b038a05c170b004d28040c521102c0d0f1003004410341a805410610810b1310b0302491301224904000503507841e2116140010610300000306112480c41c3d65040361010240e03528034040b88003400c40e041c03c1941c1c580030040381200d0380400802c101086440e90048440c0300860800f420580c000780900344001e5040540c000200742c03a2014007040c8104401141e00c04011503980c4040d1810000d24119084054411450202c0f9800c00784a07440400d6010b407c0701d200c01403a000c400020318041c00030948626002a6a0042206900d42925525405406500b58051004494a074400e1060300482e10482190803844100b4000c1e50400c81d018100c4110712070744007684d502c20040e8203100c951984460b50100300d20342d400c901c18085006000a842003030b8140c2d1440e0381c03905235200c00e034892816aa030308840308210b911074440c424100d40b80b01085c680d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 941720512 1250 941719262 941719279
    0xa062a080306040f2a0e1e150c010518010b03160504150e1e090f030a080a02120c190c11041d162c070806040902031f0c050f0414 57
    0x24030981c1e4040b9500c155164401d40c2810709400340b21b8001c801c690b45002c04443c012806003c400800c0d074243c50402c503590190710001c4806201604050985540d220385030b008101358509480e05032142400701103441c105501c2c01d400030090b420042010080d90804540301140da81c81c0009000082a2a200280108040b01d00101d0407142c0685118080d800340f0807080031105004007040d010f814040d08200c80c507407100b880482c1c01400441031700d28608140c1402410340e680c06000d40f01900c12100e04600202074034040000100c0d04102400103200c559407004c0d40d14040d40800e481d9000500800350001d421a00d8000742e5203000c2d08082c1604204074031000c408500300d1210782c900062694a142c1c283c0405000344200280e000b0540f121640026242c00412900040380130f4004010301030313104200402000401c1c544454001c0d00b000760303014086032030714202c0d400f418029404c0035140741000c50900c1442850385c0d00c03074010b80c0c0301142d000b12814070b007500d043d035a50340f481c545084a68022450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 941721762 1250 941720512 941720531
    0x818030423040e0316020904020105090405250e0303041a07020616110f0d060507260f01050102030403021005030403140706020d0b0613050904050c0a062a080306040f 73
    0x114031060540c0507540d0781484240e280d010400080c0d0756401002c2655510a001d41407031812048104c0854540580d000d08841d2614001228940301e5208900c1d0428141410320210080e03422682105c4c9400031580c0c1d48451316454226240381c903002d4001e0f49a44244010301511381f40c450300c5210040b8198681b8940281070740828000d4010390a0600c84000020804c0182b10381003c00300442002114017070442000b60000443c0600208400341c60740740d840c400208024010149181d0714118080f10500000342060214030603001200c0c43c0d4a00340d400e1000003841d500010a44050700d40c02810702c1c14030300d483d0200721940d810050013a000c102c46091048213504040380107004c01c03409030b600503948266108944090300d2511170014080c00342005454440003130003030140241e8404903001701c010748850803c10310f803c6042d440c03194008030380c0000160040e00981511510160390400d101d60311000c0217900b820b48541c2c0c01c003410071801000010050715082c3d21203036040e4402c00c8000b404800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 941723012 1250 941721762 941721779
    0x20403050d0206070f021c080a09061d0f061e0c0d050c0702030f0703080f0a03020f030c03040512091e1207090203060a0f0b04120201020a14011a030d08180304 70
    0x780e89800001d070700600203000b00c041d400381c1d800a03401c174180020b00c0600c42c3d056070940d14420f520703540c41c1040b0800020401d4603015401007402c20740c00c10b405000d0850356940d2000c83c8030007403160b60118803d030711070200b0044000c542d0078403614030000d02c42108805018041000d80000740324800341e1504010b2252a001a131207018012154010019211603240c8141464940c0019111b1081d40c0220020000225501e0803205c1c0703032a4802d0700c5922000100e0080c2e010340910400c200c4030307031004400c10001c0310038a0003552213980100225040b040300c00c44038041c54070569804940060300700da9444039003640380700d0101030480d01030074094100e03409001250400280d50400c00050742c00000b030180c545429a85030000d00380103280c3c10f03880c92410f103001096101c0d5100c0c0e0031514000441100c2560300030300c0303031001c01c98001081c0746214045450542c001d240000003a84a0038060b24400c2d11414002100003007281503403140b4000e6141c140004501d26100d0381c1c0a000741c401008007040454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 941724262 1250 941723012 941723023
    0xc051005010f05181006051305030102070b0f100b0304021912060e0f0f0c0f04022b0c1d190b0706020310060c0c090902041409060423070308090402040305 68
    0x2c1d407116001426060004000c200540540c1c4848544503000078170801907031501c0f528048449504116680e0010a0000b002d48446580403981c15440481c650b4103104d10150705510504204680300202d030780c0d018187c81c00642601912200100c14030014006041c9880c007034585200101124440310ba95584000c0e040c1000380c1c080f80d86945980180f03125441c100010006a4250b4024081c07800151803d82e40d100f525050b540e118803048124542ea9881325811070382319007881c4400203201d44000c0000107004c0e11074109080c9880ca070204418203240310344051011b01c455071130b41804200c0c1607000c1020b61a0850321410316144903850001d00840c213000105015481001c000d038803803520400320590641580e100005220340040000d0009d154800004155a001280094841030301e00105000304100c2102902480001d400d00c50a41400110244a5841111540c22000c2c0328541c8542440b40c502c60f8900540c003480c01840003c240ba005095403900c0034000508048c1c0e25111989050b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 941725512 1250 941724262 941724269
    0xe01060e0a0b1b0c0102010506030a0201120b1906080903270f030d090614030c0301061107050a06030519090206030a1e0c03061e0605090d0204180803340c05100501 72
    0x14852084180343c01c0d041405100c0020400740001c1102e071405102181d160000500300031304002c010900ca6844101a920183c00d414025080203809804580c034050700c0c10403401400e01180c0074000242611000100b10307030401c400020b03041c20031621001c100201802c004140c543c003041140780c8014649003008a80f8131f8404603a503000d1618a0315901500105540b2a06c0e003c0c20820402c1084e40000513044904403803141c82d100d01d201e1001401ca41c105005134000a500001010300007805a41c5034004d41e0003040c2d80d240343e01108000324950000c9600d00708000350004020f00010f49544000c1c1c1c04a41c009110b0a0034140400c444050a4112240c215120011995a482c14013454490030030644114044514100405052600180c0540248c8514510a20012403010308540399904802d60310540800160b00440c49840c118250390004c0710102d0140c1009900c201200052007813689000091103807001c8601c1c40d280341225040300085c025030b107e102d06a1018004107861154078001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 941726618 1106 941725512 941725537
    0xb1b07030c06080f090d140c0712060c0f08070c0605100e0a050106030c090315020a2003030403080606070b15132a03060e01060e0a0b 59
    0x505026410060001c0c100020000d0342981080c516805415603070a05601036a92280041d50307800c0480b5010b00203416040b41c0500b400c03a0b0300050078403c4181050b90201c0f034490038006078400e1842c00460f1204c0e40c55945d581006c0d484422403030310941915056000b0300f045400208140312020020b8411940c68001c1642401c10007178a01c02402004a001c0301460b00307200c0600100130074495040400d0614002c0403a962090303901e002175940c000804085445030450000c000c2d0014040c02c0e0901070750011041400e04018000b24540344118010740c0d03645003d1070300a005180150455000d10411700c903900c00102c80079040c13980101103444400503920002c000071340310340321020324501031403500c0444944010441b056242002510000000b20b04041c0011011600140700d00301d02041144014048544286c0c007104458070014801420309444410031340541e840000110003 = true := by decide +kernel

theorem cover : BRFrame.Cov 941546762 941726618 := by
  have h0 := BRFrame.cov_init 941546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 941546762 ≤ n) (h2 : n < 941726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
