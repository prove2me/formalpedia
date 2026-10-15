-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4786
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:43:23.268993+00:00
-- url     : https://prove2.me/submissions/429e64f0-47cf-449d-bd91-c847fc2d5cca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 860611510 ≤ n < 860791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 860612760 1250 860611510 860611513
    0x109120b040c0902090a03143a031b0f1209051b0105070b01030f1b060c0624050910030b010f0f05030c0f091009020c030714060f0403230301060c05 65
    0x407a200c51181e0240d200e60640d0f11b801c420350318000c2020417122080c9409403068041a41c038520300c1900304240c0001e205030568420100c505560102c1c4449125034480211141024090940e0190b02c1e001c80318104070840303051082c482c84221206101e500504142248034408224010180c10920341d581281201070410403000150080c003580544191817900381d0114510000707a086a5420080c210044030442c4c440c0e007184108110120101c4290380030300400e035504910490141004000e03601402c04d41030241c01410b01e0b466003040241d200380142c80b415640200c5603120148032440c005490360005e0034050700a4008030b004014401c0c0041190703a42c00720083d4260301c03202015200c584400c00350b41d0007200b04144a4403400c05402c0c01c1c0e0f20104140101e0401561020488180d074005403100005070000100c0703004111070707070f01d040d505040c266005100a1070310055905070124007a0001e400c2c018545180c4225810703410310500e440280074541c41d1656510007001c0c0c1040890324003120035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 860614010 1250 860612760 860612783
    0x80a0221040f12020d120c0501020a0c0b1f0611031b01050f0a0e0d0804030509030a15150503060402010c050a0f08040302090717011a0c06041103060105031b01030b0109120b04 77
    0xf6101d00884032655002404070210040540d1020050b001522480040c80810281c28003c10703028800b0340342c1c2d044039031103840241c81c81d450400201c103801005905110f00c0c6250f18414070880840a000340c130580d08003001c060004401091550180f90484031200d4032446d10401170740c0c4107411140c042c030038825600d80c007034a803d8010b07015031781016803111285d4007144545042c06c0c840d015154105002b030600c24540f280c0031020904050380d0090545055084c0b02c007655000156204054010110030b00c0900801d05020000e03854230000782020381004540009201404018850071203030300d0344440d91401552841c43e001819030040d2000340c1c0304035064070010305a18000c05151805580d40500300110b41c0c2010040d810120700a00180240101400031610011082165a014a000307440c440554117914007090301d40700050308000e01030340142d0034406406404080d454007050090a000c0b0701c1500c07a03001240c000c002070380030400020021038071030248100155000d0081e07010340d40b000385 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 860615260 1250 860614010 860614019
    0xa0b0f0603090d0c020a08010c1709280c050907020607031505211002160204150b0a1b0804170f010e070314010b15040915030f080a0221040f 62
    0x280000c42e80c200e0b85800440d509200140b113600307080703801072005110100b02038403800080c0c2159080b601410114146540b0485041561948a03502201c02c000074582c013030070b00000d100d201c1000c1c0c54544441e11000407071010007000701604000303041c000d80300909900e42440000d58501c0c045c0c8401c804245000c00031900032518002034010b481c0c001c3d000005500f0101035080094601c070400318028003490340d00803c5464980000d10607107054000e00403115507640100011200d45820703200d1f00300b994038000c00030590000306640343e900280c103245d0708a550b108100303071299440b403000070320500c00000c0c0400da02c950140611410048401240d81010144498a00301d07843d0000901c401d500c0f02a0803c005040e29032948003042c0c146001040c003006020204148070242c0d604052402804501440310200500c510603000040c00c040b15206032454032a040d01d284088806852007070002080c01e5901e000300203d01340b0004209010b46280321381c800408454215008015003503a01b4940000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 860616510 1250 860615260 860615269
    0x40e010e1f060e04020d06090b0703140c0406080f0702010e0303010626040512090d120e01021b0607021003150603061a120f0916080714100e040e070902030a0b0f 71
    0x81694101c1c908210291913540030415400c40c2144100c401d292030b005490b0006589441d817901035000c546000c40e402c4444c2c0c140c041e005000400038010180107000812156a202d1416900b011101106403a96122048128058281310b03265840c9480000000180c1c158030988001c11030070010b0020441142c40c2c08014880e40094030043e0481d4408117100082c0c4400c00001d0281000c02403c000805036643c0c0c681300651154500000800e0f8212120032665030107214422417050b00403035900b2440580d0002480501804001074081d10009419406540c000d40c0229820a21040500f158954425004019020307600581d44251118091583da85900105940d4040a103ca000388555244180c40d400141c0080003034045d8400c0000310004262401100d401074030004000d460694109a0344900362004054003070700644601e005003c01c01d510192407074000400f00d03030100b81c0102c040e00701032401d84c10b45c0254091502c00028401200026480701c5801001590404004c22a800030070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 860617760 1250 860616510 860616521
    0x90c1205061c29010b12090a0b0115111e0f1b060304021507050d03061d060907020708011805060a050408160606090e0309090c04150e040e010e1f 64
    0x715600c10303112819000643c5220803901040c045501c21076000e21219400b580e201003a408403100a0340003c1c05909403081d40b209984c0301000d040100111030b000d603282c0d10800014450391482918200d55080d215100320030884800f622402269020028910005540340304003c4001680c801c00b81d1001210070f001c00c00964038100b082e1140b19148041b42070295590008004030f0b408107030007103001003034001d58001c0c0081c0340c0928001d15004281c81c001404683d03460f001904000302444200403c0744080341001d521100540f40d8400644031410164603146041d0411080c41d400c006502c0d0007500d50504002d01c7c075000c1d40c11181241c8481c0310f9081201c005070340190840004000700100b6280e940050394119105503c0011001d07990700034041210070b15801d29916400c0080c5040c443d02e4580c894540051000800a14052902c6242c03078000c1492000700d010b00601c2c0030103148036035496204800c1c28460700000d0000035801e007a2036407911105161002c5039108064802d41941080c03168 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 860619010 1250 860617760 860617789
    0x70809061b0d020d060b0304060f14010b070c050306161e020c21190203061e060409030e120d0206010801020c120f072001020706030905030a0f020304090c120506 71
    0x408202901d400040559032080103003145a43c2c00b008000024403103032207900000c017007100c0301a8036400c281c43d04005403030052020012150405001030204801d4803007079411103030280741c1140c0d00c513140d1901080854440d0704c4150700d405010700300b125412480340c140b12460400c1d91440c43c084071017156a4100d481c045050001030380844202c501c43e082c00003400c03403a603038292594045100481121460700800c000444180c236404283c800071400c040082d503402199807081c51401482c0703c0d84912074200e0080c040c511858680e0120818180104034000d0444800303000c5080b80c001005200759038a883c000b0060040c443d1400000741d070401071080d1044075108001425820740d11170a004603e4011096000401404010040c0042d43c0a4070910300c01c0b1b10b21490840074001000060304140c0c03c1c0e0b1005090508148030303000054408400c4490300323051410f00c2000340140701002c03031860066411001c40343d8600030501c1880340e003112480701890f03d0040e003841a81d6a22003440301420700d0407030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 860620260 1250 860619010 860619031
    0xb030a050604020105030c1c060302010f02060906040b0c0708040902120f01080309100509040f06090c1d120a0b070c201f1b060b0f1f03090609020d0b07080906 70
    0x104005600c100011900702c007d03030035078604006001001d104000000b4120044255650a0400440d40c1143e0481d43c040300c18000360071070340303051300300d03161100030040004003d0791407240083c0c22480f100d003d465456400180f0507403215120102c2c40001e42c006580c2c441c4060001000400103010041c4e610306990510014504050701c00060000c8400c82d0ba5400042c40014440324009803514442c44000404100b0040b400616000e000d108035542e0404203010443c140070800e41d60030f07071800c2d0603240d60010b5581d4070307550100100d1242807034401d41c00140150b0111060065a540c00300e6460020307401007565404809a00d812480326603c00385070f15401041250800181500340b4030b00c00510585420000f51280c000c8426a1299440c02d00803a402640c0d00364040c0780341842e00d1745074034460f0155960243d1200d41000c6000d81901d0389540010151200c0b030410401c2031903002000216405065040209098648a000b402040341c1b04000070300d2103000a200000c002400303d000d00903008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 860621510 1250 860620260 860620273
    0x1306031a0301180f060902040903050307140a20121b011b1e031e1406060301050a03080a0e04060905092e0e150103060212130203060118180507090b030a05 68
    0x80d102d4811a072043c100b0f4817840c1ea510380d4032000d0b0300c403401411000b903c241e9800e03a40c0d01d00040013506660b83c0550fa003480034424004c030000c0c1d580100c0e52403005c02211032035803610464000751303624015918419904d42200410244001c14602c840c0150100c4040001e00c2240032425040c11130102114544000034400c1c20340392501d510110a94404100c3c034640031a0703c2420052864002003410300352144650f441c0c0344508102264140c01e90050001c6030028695490540015001c0510340005010000d00103459803c0b14015100700704054006081400700565030504600146070840f84400c00d4010124031199008e0031403001c4a0b10840c08480084187c1d45118910040581c24225007280c0300d10110f0781585050a0400d40c0218411200982e41380c41b800c41050710104080d0001d8400c0700f41c1e031000f00050b90040b6515064900c4020b000d002e03100c01008840c090607480404c4080e580d5a00c00e072a0511001041220036260005400c3c00741081450038990f40c0d41038698040c20640000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 860622760 1250 860621510 860621513
    0x120d0306080f061e27032208151801050c040e0604020703090b0f091519050301080a120c0f060b03010b0154080c0a15030e01021306031a030118 63
    0x1564941001261814800081d1640b0741744455222202d40740035298804038245c003d121184020f480a4038030100c107a400030f45007400c202d03503621100c41c04460600c0c42100140d804006200b034401d1008d1000001c1c03015051660030303225284c1c4540545001161020001412814903008407840c469251382c0d07401444d0718100c4000795075003011070f13108410001002003051326559042034040c9009042d0ba0300d40c1c2c0e81c2c549100d443d440d8107100010400c3c09070038001000707007640c0468100d034a150019240c1c02121039010040303c1081e0000002407201c051400600c00744940c90b8050600304c0700550080000103250801501d58480250035030400e14021010300d01100d481c1c20201d20941c00703004400491440c1d0002c01400310301000e044000a0f0b00701c40c02009414801c20038000485410382e91100a04e082c01c0050703070441150b04214040c945c0b00c550301400d10900750f04664100300301d0390f0505034403503ca04008001c0d2407000800c80106103502846c49142c43c061091b4009080d5202801d918004035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 860624010 1250 860622760 860622811
    0x3060e0a110d020409020c100b0603041202011401080604111c1709120a2a090b130f0b01141603080a060302030703030c1b05011d120d0306080f06 64
    0x51414200c0d50003424802c03084000098009000941400d11026845507120b40080e40b41880c8950a100038609140d5501940e032200012280c0058208020600c2000c075800d05070702400301c0000001d00000e0300000040d0103000411060b008502c0380103402e4020b000a4100905c1410603072010600c03841c0346100c400003c06491407500c1d0304508210950404451000168408480c0700110513244c120b070301c00004012502c90240d0910700c07400c0c900503028942c0502400c6110260103064446550340741440440d070760f119800c8404030b100100522030301100c2d50485019001001001d40490406040c02c00720408039020b68042981c00c811001821070719032002c80b0410f42c06400d800c400307540c0340e07004405a141070101c203000d940261a0780e001c102840c17074072902480c2d107611050001102040e082c0820380c1d00030309840c20a80c660031800d602031a00710001d0030200440400c181c0e184145540c8804064040d08203c0441c0d00180603505808500000191184411100000e4040c020b000c40540102c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 860625260 1250 860624010 860624021
    0xe0c0705060a1418070618050a030606240e0409031e0f030e060c18150a08150906030a020f04020d060f14090c031b09100201061712070210022506080703060e0a 70
    0x2401075094400d48d803000400c00c4240c0a1300140c44803912040180300e2601d04000d5001c0308402525003041d00c0d085500c00401c1c03d00082030b100c2c030135a290514031050500c1401303107022010b0b00813000380108100c01000f9080c28a0024420042030078101410300300400840c2035441601c2569207103150039180c03c03005080c411442c00041e4800f00b00c2e1410741e42c0300d0b29000a004416555280c40c1c42d68244140c81c01d801c034402c512541d206407601e40400103103403000301e0003441c001c2d415038888414081c94800035001e8010001c44220381464603800061071390b040b0041d4011600c444001c04502c40680051040500084409045c1b5403c200049060069000c1000d5801014103d909080541140c0052041840402c4410040c3c1d12100d00780b003070310081080084240d0400b0018031524106c4136442c120340c00380c3c2102901c1a444451910403e1b8000d00011200d2514070009405142a01843c109601c0c814001c00c00007074694000941c0d114080c1c419241650f030100071040c040c4e40d90011113005800f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 860626510 1250 860625260 860625287
    0x1d010c0f1d0a030503120a0b0d050c04050403050f130e0f04020108040b04020d080304080307081602100b06070b01060c031e0e0f03011407030911040b0a0e0c0705060a14180706 77
    0x18010b400001041d000e10240216480014100c00b5606100e5091415100c15409881c4580700600c0801d00185c3c000490300e020303143c141e8010800b903556040c103484601412400b08030318600016a5a42e8908211000045d2480910344a2407a284c154200c15107001c1100c0090104000c440440c01007554003c0c51503000384000d0400200d0320156a41046a401c180e500322401e24001c401e1040f01070304440d2a1760b1100082480c180b0a000d8054000e6407050308444298403d540c400045989440d004125030750316401031403400703155035503113070080c158410204103078000380100781000d0450f42520300c10300051485580d080d0310701e00325008014520b040050b2840d0f1540d40c51208002000d6204c0c0003c0c403841a030b8800013105682c40c14901400080340302c400d17110320302e000312a40c260707940d03000701606940c0b4086c01c2800594031220034420901c00d81802a01c40e1154204009038040940c0200341c400b480a140011144c58030301b03100c01b4400021184441d2a00424000d00601c0d10810008580d1b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 860627760 1250 860626510 860626519
    0xc170a122016051c082502210702060a05030103020a1a0706020c030d060620010501030b0112081e130b16060c0302090904050f151302130f1d010c0f1d 66
    0x244c00f41c40105440b001126540300109041c03000300080307a0745031860800d9103c03010701a03564814130204000d445d0300f11140d14907090039922032210156200b8800b515075850f4003a107c81d5440d204100040c1c0550000d10049220301d02c151008102c03142e0703640c100381ea2113040914440c14220955224800f9402100440300c0b240f10900414825480700c0c001c42c0b008102036142c225801d40816000c0041e002c0e84141c24020f0303030400c4010000107c0d101c1100381113071900f5081c010803030102d1034450302a1181a004007040102c0408014030300c0c44141c0140f040f03614400b05428401d42e100d9216520703001b00000e038a1501d080700744610100d030203900b0080fa1100305141c01468511094001000510241c800b50703401e6104404002d0100300030091240d0300e0310010150b0909140c0800c040821036100c250003802400415203007501d2182c150006121780031040d00510280007465916940f8a88d482c0c0c88802a41c00c0003050f0140078050580350b2500352107507507141e00007040c124810f660980313540d80d0719800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 860629010 1250 860627760 860627773
    0x90c150a05070f1509050c0f010503180c0901060e030601060f020309040f0b100905090708160e0112050903071208010515070f05151f0b09010c170a12201605 69
    0x11342d18001500062404200c0022058124108903203030041020005018002e0388103642ca40c0e030b801205803a40306000c0702d4000c4030f0030b403d800b026041c2440c1da4245a0030140e4070001183c4d16030410b000403884c0c0001d41c00c0300c01503079035001c0c01c54022b511450003038050781040201000070309050b0800c7d0b10307070001c3d080d012603d50710403004110b40c40c0f03c0122100000c2c1c0028000c4c4030741e14043c501150002182d141a452030b00380047c0800c20004051704520900c500805051000d03406812400c110803034000c0200b200745080429191240e2094030120360300c8440381d008062144c011044903050b10743c09811082003910140c03000a07030360b1040d80c01341d070010400c0c0700250010710100800e0300c0100f101114880541048020b58503071035447c0f840030140c45003580c5c0611200d281c050540d4400c100910700300b9020700d1070382405080444688403000c2d101000003040c00d101e07a0442034201001c20081c104101d00340780d900c00c4103c4480314250f1200c0c07a00003004021800b80749400721112843c010800d6964 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 860630260 1250 860629010 860629013
    0x300b0604110c01150902250f0614010513060b04090c0e1002070f09110703030c1106010311101409220212040b070528022103090c150a05070f 62
    0x2141c00c507401850300c40c0c0d15242d80244000c0e142d12560b00400410317209500f00000000c501c50000b84a14071411034041210047c0b0a0107032447c1c0c0240d015820800c100300000c00641d111152580074020f00340a140100740d81500015030303118040440d40703004206400e00b0b080240c0d04000d4060550a0800c00c10402c2829100e03a1f00d441486500002540040c01014a40042800803407042d60100900c00e1400d200046c0014290080311001c0d580340c5400a2450300701c1005840c007901c22020941d0341d108010010080042c0300c0c2950f41e400008031405501c4e040311800840d04402c00513070035105414184034056840c14410034055881d580220a00000103400c03654800700d800400c0c01c2c01e4200c0c07002d02484207200c1c5081d4410b800080d0792605a103013080c3d8901c407040b42048094042c2c03841c00f14480d1050001c2c402e01001c48081c29100c00084010301d85900c24803260070981c0c068205018486440741c2130b1801f007920040003103503804018106103628400766425004008140c032200c0220b6078060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 860631510 1250 860630260 860630291
    0x109120b04030e2403102301051303051e010f02040518040501110c0105071e0807140408010f0209030d02060613020a170408071b18022104050601300b0604 68
    0x150b1004c59076a42603101d280005c16280181c50f5a0311621401e8101001e0b03080102d0307104800450244207003001c40c2d40e18a1001c034140d40d903e1650019203203001d8022100bd001000c2c9000f0440c410f5800000c4c0311003031761800840100c5c071039171141541c0030300424040080102c0c0d010500307070b0003030140c000000c03680302607411099503900401c4410582c0c0d5445007000301880d044455002c1d000c59a05400342e911440a2004c0c0c90514058051000e0011524080710358109200844014003c260024800040000c2025010b90016126203100f40180405503a0040c8005005842400700400c04c581d8507900908140c000d610285400081220b040c0e8802a2001c04106842c0114442c1200c140d443c5d0003810316100040034040658aa02008941000303155402c285010302e0148002005a44203042007490190a4000400710906403c110400c420720070003040740c0e4100c6510201c0d0b40c40f00751007141c3c520400603a1002c03034808405074400e80e001140940c0c00003580050003800020b00b0360b461a0280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 860632760 1250 860631510 860631559
    0x3030f0e03032a130902160206040f0905090105070f0813050703030e01030c14030c0a02070f09020c07060e03100c1808010507030c08011508130c090b0109120b04030e 73
    0x140b04820084800792060003070f0104901011804401003414810803803400c065014507449440c4005401140343c800794800a4080c180040d8000c00d9507176140c2c0c0c0c1d81994900020603105030455146094001041541c1c18012603100f00640e1380c500501201507042034502c07000c05000c11881d48001640355001035001c200030f00c00345010341c880d004421318000004082e102d480060750100274a10718071b100c1e020000c805990300136690085482d00ca86c01d03400d04034a0003449610680c0550040000000c0911031603000b8481d14002c0300a45d4201603c5041c01d803240c03a021032101c0d405a124002c111402d0180303a0010018460524060311184808801c5541921043d0440c0089940d2217051010040d054401d440700702d1a2800c10400540c501752000c416004000d80c22000e03c5840c0c5c00060090000405002c1d07101c6d80002c84261a9459003540d000400c9601122404244007080100b811503201c840f05142c2940400c4c01c0b842a9540c0c0c1d400c94103c0d481c000d203141c0105904495480c0e050501d90386 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 860634010 1250 860632760 860632771
    0xc0311060705030f0a020a090303050a0c1703090f071802090a0801090b0a060815060607030318050703060606080408090d260904051e361b01050f040303030f0e0303 72
    0x12543c0b41d007880040e5003000d4201a11011400307104229500d4045e82024801d070072070b60503080098940400301c2041d1f8a1084000c401042340c1000007c103c0c1c0c4004400c040c5018110b80c03412200020504801150f90b1695402414111000b040320050303924003e400408040d1400340003208411342d9001c40b9400d44081c4c1700121045074107001000711a42d01440b03014010041c1e14010300c403030070010300040c408100c094070a82c0034032400169001498002d403c40d40312000c2c81200e0200342002030500984580c0705004c02c4915905114000030b203a4400c680c003078002c80c1c001c0009460880380c082009507103200e407401140c1c1e00740d07200800380c802c030848140000d070140c202e18996a11070340c00040004880d0700502c1405150b50100c8603242d02e41c9100300440d4000920005c6103808012402e10002035800f0100300c480403681882075010802c4040b0b00031403059020703500d03c104c06803810b0054505016246442e8160315041c401040440c0c801d40220003088034810000035140e4087e41c450b82103600440c0e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 860635260 1250 860634010 860634017
    0x4060806090609070c02120708071d0c1213050a0c0b0c0f120307050c010915060311010c111c08071a0901090b0406050613090c090c0c020307060c03110607 68
    0x1000001e0420312a06a0700a90840303c1000d20b240070381000c3d00c55030705204040c1c050301c0e180000c440009000c00c45a00031380541d02c11210417566850f002242c1400c1003400300b01400b569000f0842c0544040140c0b05180d0802000800300d03034461901000d510a081c2003520607108010070040401c4061200e20040c14200d1581c0c1e0307489500d08141850b0130ba2a441541d8240d1012190011909500b401c2d660001c0d014641281d0b12907003294003502408003514094070312112031242a4000c14240e010030100c0e4420300d85841d4002c44900191200d801000380a0705000d886c0300d4001d00c91410b200e0010141d115005032213600f05664076445000c2d0840c20301103c0740009607807022140951030071840e610407030303200091180001e55500e801c2c2c6020050002041d0390b03203540103e030031591a0501d9801050140328100310084190400042008080c42000d010340d01d800d4410702d07840d214102c00054550090004c008080c40e0030b20465070340510781429000c11130f03550084a040e200c01c0c40414002d204594 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 860636510 1250 860635260 860635277
    0xb070207080c03072313050702010902090105010201200a03060e160221180a05030d03090b0108121c1e0204091404110d140d020f06131a0601030209060406 68
    0x2801c4601e054064100107102e984200130800c802144110080c4145044c05c1502c02d90f140d03594082110903c0750081031207464205010805c030280d05500900041d4000c881401e03517030f642d40c00160f08a4018139221000c0b00c2e0441c00181050b0078200007408040c0301c42c50001078a6a540040000b200d030141c8200324602910385028540359070411628441c154010b5982e10440329000b24481c1611408880c1ca2911411907031000c550b944000c5440e000b008040c1c20b95944504948008000f8110407104454040c80c5000104645000040c1e2a07003240004042514280805e0b590102001c01d00c2581c055480d207851020351140904072420300c038181029805600d460800b003000c070945038100107490308000d851307003000041501ea80000c401c00c54151414110765655080ca56000d0f09001501c1a85104089801100650001c2c994030415034100c20b0b20305946406160f50f050000d00341026002c2c030b0b400790b1b5846101c09001e50990300004141401458000700d0808150b45402075030182000c1110b24 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 860637760 1250 860636510 860636519
    0xc140f0a0f061410120c0f0603050a1103070f0e1c03050307020105070806010e040203041a010f08101b0f02071508060f01020c100c020103020405030703050a1b050d17070b070207 78
    0x303000300403400c3d0200f4030401d0f003854041c01c01000061684940d10706028241074074010b0203e00040d81014000d020000b20f0400e489001c054042c0c8000c5d00e03005082c0341392000c0126180b20a005a9000f80340b41c3c0d0316032200c00c2075424211002d914a501d81035000b405414000c07940001600303c007035018072a460b610380700c1c5445000a421900010007400604c07030303004200802d580e444048490181c0085400588030f8441c0d05041c40301d0300504426403002412003002052601c142d039070360012504664104c6440c00e8406640384103440010031011818006400c08184641c080d0b00d0702c0c05000e5091044a6445039a11302014103c2160260140400c214100f88012030500d00728911200c1000e0004142e40300c82080420011031281c4030400811901505030f10031a0301c01d4040b40c0045c0b00040449080350340380c0c10410740361013030203d04407410066034800c2016114080c100c03604961008185030b03255502d5440304140300000f0040e81c44c9040c4104450742c00504064a0796014403003c1d401000068140b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 860639010 1250 860637760 860637773
    0xc04090602040527070903020108040803090c03010507051305041109091305120a0e01050a1205090709151e0e0a0209150d05090c01020f06180a0b16120902010c140f0a0f 74
    0x182561007000441c000500160341c01c0ac50240c0c215030710a151944c3c0c1d40e1400003040c24008035050300d65155003000e0a2100e000d9002003d009010101c5100e042c081c0d80d107808100845610368400312034050240310103d00d51810038842540003a110f200d4100c0343d445030780e0300c9050882440342c02c014118082546c6850540c80120164004070a0828510b45000e8150150020150340c4440503010389800c0010301c40300c400c0c003013a00101b5490005000c85000011000d00e440c202d0300909841607007c0f280801c8000407800a001183e2510514400341c0d143d040701c0d0000381d031050034607580082e489002515000e0104004060a80c1c081e440003c10f0305200c1447c2d030910300104501c2d41190f01481c01401426408036082c0c1e0080c8454114404803603d003003a072070900c0083d40e00078116600402c10842114245010b010380301000c0c2c0c0c0c03401e41c0c4008807404d0204484101c4c402030300184500c55100000360760050000c0c220b252034800c0314405003940b000b0a18009400c44102d41c600d4912a440c000c0002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 860640260 1250 860639010 860639089
    0x109050a050a020f0d09030908030408030711030115030f0302010228020705270603070b13060e0a0b0a080703060b0310260a030807210507021e0c040906020405 70
    0x10002c10940c601920200104441c0c01010a00e21105603599841410140184403070401800e9030425242c68a90b6004500d8407508480070603500d0b001c0d00c502084503450184100038211007034014a403041e90031b548490701c0da402201022800d41d9420050b9501d00703011070080c900b0101905007220116540614001d040405680c0308900a00001320b0300365901c0c1076015480085805680b000c1010380d2400c0c0005d00c0d00201c0d034421408502c0004e07046a003000002c140c2000d17281d5907212841c0c50098039051200a884a1080c604401000d100a01c6064850840c5076040451840c1c0424841d2310707030080c403c1d554030580d2488950014410304000000502c0e001484002d42c0c3c6240e224507501c1401c80780d403501071750748004081110307400008207218000e42c455100031050503009a44402044100d0004160544601c0050300c11117070f24000e61040294545240b9000c40041c0c1203441282d4240406404101d004940d12034003800041410b40707992044210602071092400c07500c9405e4002c011030b419 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 860641510 1250 860640260 860640271
    0x1e04271401090209060d020c032502060d021b12041e0e06100c050f15061009090f06090e010b01090b1806071a130c063209090109050a05 60
    0x50411551003049945100036904480e00382a000d0795130311056002070303440c0c0702d03030000b2264052020980112203600003018002c46440214900d60515512101c54145030010070000d511000c100034180785400103802620741e15000300003c00710030200031000703800c00e9114050704100c6e4030003040c20000700a00310640e01d40e6400c80c3ca080030182d41000030b0101d8410340100742900515940801000041c415142c0c000920f0f040b0703040d141c172a68419103d41c0c84d000d854507404c0071940e20340e012920a180040303c80d9030300185900c84204440c076080070000688a1a801106000c0d9591070019280005019440e00701d90194000901c0c0c0440c900090f02031640e64103c0d004001082c031003400ca00209a10322940c0c4103046404680324000351078030140c1c0488000c4441a00403950050080b1aa01e041ca01d0000f40e01c80d95002c8a4180c5400049170821020300d2100b00000311081d0304035880350501301c010050f140100c1000e02e807410b806c01254048400b03038044441c103580c980030406865043d104194008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 860642760 1250 860641510 860641589
    0xc09090b151c0501080f06060420030f101710051b12070e0f100f050d020f093a1b030303020904110a0903030c260403110607121b0215090307120201020d051e04 70
    0x1c01c140e42201da4580fc40a10900701c20350340c00c04516105150b203001c0200b0403a407001a03590368081113480144900540d00711011030302501d40301265240ca545649140c03400540001d4018842c0703c012580c450311442d450050203c00c1018400086c5107000401e511100039030069650320042c028400b9101038506440300001d09400701600100c901b00c040d5429080070340c00045040ca080c140f08076060901d1001d1106c03110450400810140c060300544038114013200e04000d402030030141c042a6210b580c82c4100001c1101c50140300090107140d5003602d0501499111641003400c010b818103592018030300105049020a0070800c010000401480001082e02c041d402c00d801685c03900f40508101030381a06003c8081405181042c0c0e1081c4a000d04c0d40042801c00042d05000c92080fa591080341e031a4042d000382c05010581b032040e0b40c90002c0c1e150341070740107040c9043c807002c0460700707900702000c40c200c000b1040c1c20005d5880c01407030107040980100d00124016540460300404514500341c80700d17249 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 860644010 1250 860642760 860642789
    0x201020c09090d081504140103110a0e071b0b010e0f01080a08090d020d02090408030a0f0b0312090105160507050909010c09090b151c0501080f06060420030f10 70
    0x48410105502008610ba828602400c0c2c40d40c05c00f500503010810351180d001850003044503d84900440694120703030107540f10300c0d030060350901401700d116254007503000f052000d10b000c5000984648500450805c0416200340120440d641d0f01540c504280e020108940d040000c1c0641104000010307801010f10000401410303125036500300311802411599031162440264450540d1a6a12100b41d05a4000c145083c1c916091410301680e40054410000710307894040000c402a88a00c40d210003080001c0040151940c03d00001d441036100e004500e040243c1400310345940130034044055232141c86907028015803418030043c0010010010590352a9a0400f00342c00c500d10341000150080d500c0714a408580580a90042400358102c144001c1c09900001010964050401011503030911807803400c0c450381e43c1e43c80c103032035035520820b118050b1500040301003801c61600ea03110310781d190029803600c055240511500c81c11900115020700b104c10640702085244200d5103945400f4080e028103540d035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 860645260 1250 860644010 860644021
    0x6040311100c050604020405100306050a05070206070306060e0f040207170c12070b18162405040303020d05130906090e010609062702250309140f190803160201020c09 73
    0x68134480030b072019018030350312070220303840c1c2e608503000401640e00f002c2d0a00003420301810010040104035041c400600814000c04d0f411442030241c01c0465001c1c1da0361503101d03c9403d0401190f01d80241e081170780260300300b0001c0b0008216082c600031002190310b5843e00e0b1444000040d0034030340c40000100d0206410010400002c0c02401c0d95608250120b005004410342d032880c0034038001801c00f800111170360000d00041c0d91380e03100311500c0411000d9200c4401150707200302d05131041c2c041da020040144e00030100c080c1000e0b02ca07030064030030368099442141d031956440704000c0c00c41e032254200d4081952903c14030420300f002401030000620b260501000554500201c0401d90307a80e4402403003101d540c80f5607075408102d0a80566242a88001c80040000150383c0e04c06800d898410b012004110401e200040f180028903000b0041840500040c1d03006003410200080c1814911114002141821010507075034001c0025098000c10944070045044d010f0002a1404400303141251048919030308118 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 860646510 1250 860645260 860645263
    0x100f090519030b1915050a0b041d1b04031a180601140609031e060108070e040305360a080f0a0303090309080a050601150503070f050d0b06040311100c05 67
    0x2c594100c0403610381910707500c2d299079160142c8420100034a0420306560040544a5481e004444003141c00040c02540e0b6000306007107008a100d01501e80045404407484940500d80036607200d82a140340640c40543d031030301d1950b181c00c01c0c0c05c107840d141440d45a0340b030b442c000b03080059044080f41801003c1c400d1415013041d07595005000b00c0d8005681840300d0081d030340b01c0c00251b65003a00028241c440c1549507060403555811041100e90a03032103044000200c022010540e00e0a444015940050755a80c5440c02e8540d80e00080b015a41d02d407200c8090440b000030101d0000103501c121041c00d04414142041050301c82550b00610103d030466566002d0300c0600203541265503a143c00c000c030b403400f168141510a0641540f00d01d115020300308d141c200b0000003283c054117941807900d0020110748030b00c40480e00c0d40411208100814003007000c0e11049800390001d0105182c5c11180440d40070303c44408500e15030850750003160706900307c00740c000c85c9140600007591045c50740e2801054850700c98441c103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 860647760 1250 860646510 860646559
    0x150b01121b0f110d141303140d0f0f08070504081605040b0114250c08241302091801090f0c050117040b060409120c060c0e0102032502100f0905 63
    0x5130140850f1010f01a0304d5060101034a100740c0321719507a148160b9681c1490094103945a00d80e1149014502c0001e071304a000d0300c02c0000440c3c071030783c824084205c0003000343c0305c4040c00307021002801802d01000070201c20400c4031500c00701007a040b9000c414130300010300047d60060200c1b681030040c0350002148100240d4155440c10080d1454a140c000000100100d4000c14410103001020003540208807940005080444041d50410b000c61100c4014410f01c1743c082c0988800e40702c1c0c2012a05030f0f0261400303240650300b1441d05030b5080d03001c641c25450f003801c46460746c5040790214103400081d401c2c0079100c0e8903400104002c1c01c00119400d0b104a0700d4402140c0100001c0144540101003041610740b076011140d1a0f501030740100b60441a06000b0f032211210320007c45c1e00c0d900300206445210b104a09021031514182c005500b00902c580f015200264401320501a0710040f51110303000d640c4d0700c4040c0e000e1000c9031703d44110680304658000c00c9000c841d00440e0280107540850700000f41c12010701d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 860649010 1250 860647760 860647783
    0x112e0306181802121605040207020f01081807150215070c020112060e040c0503010f06140d0203010e03130e0f010503070312180902130e04150b01121b0f11 68
    0x105196208034420600744000b401a4100d0740848034101c1da688001030020700404102c0d00883c0007170341d03101003000303910a40314029006155201440000d500a00a2540003118100a05601846910190314200325507200d600d4a440c1062107000c240e4051015041c00e4440d010105100d18140e880038000c42103500c0024104140d039254628050b0155000304050403184a940d0328a0038076007088003003030203540203951180d482d000c1854103c5010b88140000c8517803142c2d205600c40349070403c0280c20b0440c0d50060360155250300640803900018402880211075082d400c100460605000030040340005010400d003621142c0140055130300010850101c2ea8840d40d002250000a40200ca0800ca4004515180c140e4000040381c041c0c02500582085da40001c5c000d081980d03103021000c1d170304030240c8003e02040c00103ca0400805080d03001340d085c00301c041c103282c00c005901c1d0940030100d0b42180100d403c0e00407044441c4410640c06400d60490a50910340b8503030410444951070388900340e00c010b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 860650260 1250 860649010 860649059
    0x2070e0c09030a050d1e030c0c02010e03120409090c05030d051603050f0c0705040b0a2303120a08010503010501150f120b060a1701060c0c03030309112e0306 69
    0xc400d0306a5504003c0400d502c2d40c09015566141040c64001c3c1000b1303035003241951040d0901d558050010320921072034100f491950350786203000d4101c1c0c0055820b01e528104240c0c25001740c0209000e00c102040081000345080c84000032402907c0c1000700e00580507400991085d04510075552405030720038107440d0b19248400c4000380c9000d0718070302034802c0c1c460710561290010000c05c21000540010540300200c8000b540c0c240a108482c404000c0c00d810306000f1b04402440e032003280ca817600245801c88490b414050229080d178013203c03840402e180c1003440d25400207034a120041c44241400c0c01750394010034481031101c2d048e082c82c0d034000e065840d0000c0c00e0410003800e440c45032206070741500200000750f03014000540d00d87d11500010131411070b04070710000b0329104030000100c071032140c030070001b000360002d922400050039590101c0142901100582e500c0600358211130141ea101085006c041f400da170100c08207481d14121400740c014031040a01c043c10310341001080385000da1901140710215081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 860651510 1250 860650260 860650267
    0x21b1008160c0f08030a140c1c0213170d08071202090f1302070611040302010c03140405150a11060903040611070e0c040519050a0b07020d120f030c02070e0c 69
    0x21002c8a031003042002c090034640c040c42e9940c00344000400158024076141c24280b0002c507040300c0d08910030500b036401e0450100100034003d8640c45042c0105410358546901500c0c0c01c41e805218030030300d021600001d24443c4614912101102c0820080b2190052814050f2a6160105020704095041582c0100c0f42d40c0004102119640c0d0b14590f14030180010110880092246000700080d000030f0000c8692515001305014100c0a0b08103880451754140d440d05c00d12403c0d56000c440c2c900401c1e0559070a00030901000c51039548034400c1c040b0b6038002c51952525001071a8000b0045182e40340244001e4100c9001e00000710004000c65050700c01504001003181c00da910802d291241c158040545484581c0134080c401d0f0700c03480280112081118010b4101d0030482401d01d90311881d00c5040e504c5815004100202007051000e441210700003840c07064200381d180c407001c82c60f001c41120307032001400c031107441c8401c0c81c0c1510540d0092b04c900d1006005007400d05c0c2198280080144c83e00000d0807010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 860652760 1250 860651510 860651551
    0x7120c05030402040e0c0a03030e1305130609080d050c250c0302300105010f24081b07030819090b150d0503130510030e0309120106090903021b1008 65
    0x10441032071a11406058014030548c0ca08000f441c8185828420744142101d1030155800c040070302585029840710b503c088109501984d80d0710007800144422900781c04184044500101c2900c91284500741560130107541d84034948810412490f0900a00c0307614500080000c04600d1800d14802a640c1c103032501040c400c80203484102190307992141d21604202d254000c0c030581d4041d04043d04031020311042c00c1005031603415001e0b4408808040890380c0726507112140c0c4082c819503905410081c02001c040342040050f004089540c424001a800f1454020500c1681c00200b01c284050301c1c10700d0070400c00c61391203aa030341c0041c542c09090710154404060983c2429600c1d501c10810413070703010040303130340c0d44d04000094001c5148038821540b0900b000b034800c55a02d402070003120701481221005c0c500e004800300c2081402c80c13041c6100380103991b0715003001c5046201341c81010f090a010b90010101152441c1c81d205140401c7c119440c0525101074a0040d40c41d000090141c000141c615122a25800c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 860654010 1250 860652760 860652763
    0x4090204060819020907020c010f0c0c0e181b030c12011119020705030d1e0e090c040f120b040b070c0209010308182e0c060e0607120c05030402040e 65
    0x7140c1220640d401410300311403940342ca201c0c1d640300280c03084c0d901d04400c0c2d40721902a07894000411800740072940803803010b00c43d0b512804040c0703c070314400c21200c2c0d40a521a40009540c1c07108076403480b03038081080c0c0d4016628004000c14140740c003000b00c460340044c000c000825124025501028002c4503521010b03443c4900c20741202c3d442180504c0416140c140e014a101c0038610742c10008005401081c00100716410082414402d07600b1340d0700c54444607207600200b100e80c54015100e943c00c004612075500038a03500c00e80501e001d00c03030158070692646d0030981c00504941c803c0c4d001700c00c071100da00ca0140006807824400e640c4242c00296411180d81d13860002d41d0600d50084c0000d500600050022041104401c09840040c620030f51032480040c4800c18444441080c083e00103101c1c1900c0d0700a01095107050000c01d0000e01403401001c140d850340d035080152001021080803540190081001d001c2c2c0c882c0003400a03401000c418000c0c400c0d0751134060305500c80500007034000d5071107000800c038082c1d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 860655260 1250 860654010 860654021
    0x615060f13050603070e1203131206140f090c01050408070b1e0a050304030e0616061d0313140d0b060f180f010e010803070503040e040203012c1002031504090204 71
    0x7400340000e0b44c0d82c6406500284400b207983d0040384031b81c00c041e11070b040841000081c3c46810007081000e0340c940d0b082c90140c05680f038005408444a40c0c484009518000d09911250f0151826103804129810061401d40c100f140039060141002000e10040101e50000121030040341c0704400103558640d41031a04060117100c108440446420010f2000101d95004000310312035806551210700c00510300082200e58841c40d140a000d102030196100042030781544a07100218080c0c0500c0700000c9aa50642c1c00c64000c8020b0500f1200c02100030041b00f04020203600c0c070b005044500804594040d501c2c0204500080e20307488c05141d040551000700c0d29a43d5648080a0250400014524081c0542c00d03400100f4002d08900c02d801c94000210194000140e40540745e12201660805080c0200703103521410060080c3d0b0f0541d2035101e04800c07100803110b180c51080d80450654428006000300f02d1406251020710700d8414410001c000f1100303100240714852510031200451521050300015010f0b14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 860656510 1250 860655260 860655269
    0x23030123091203042a0f0f050402160201080c0d06030f12030203161b0803090f010e0705030a03080606120708011d0f130501060b030c071505010806060d080d09080c0615060f13 77
    0x4012010100e01c2c06010200d1008841d401087c1c0b40f041e581780c1007030200707901608501c4101c02850b82c001d14010760044022507885190400d510b800c1580c56040c00054694a03130094131381111071300307444040c000d031640744003a40c1a05d401c0c00d40c910b003840d18264810200c0300788003804112944408200c149511052aa2140d40007007002c1e4580c01c020740c4c00d54591718043d0881c00f4640c64500305052480002c42d5100c12214010050100e441c1181c506035401c0c4001081e117075010b030381000b84600c4800070900c25401056a91f81711041507040c10950408400303000307aa3304401040c40c04200b040c0407244070443d0b12000822160381c00d04000e207020b5000d001c450700008903002000c4200a41c40c0c2c629805490524090782a4490b406000e40c89801100c200780222050b5800c480001070980c10103442440700140310300f81c0d2610b016075503290801101c4900100700c82c04400020880c103411001c00c096a0060503103521038503e160b10304000b407541c3c40341e02d0040d000b1903c0460b45050003000560650001c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 860657760 1250 860656510 860656583
    0x507021008010501110609060c0c0102040f0305010605030d030b09070c110a0e0712020c0606010807050f1912290f09011d010e0f012303012309120304 66
    0x20034000080c0c00038200340121400907038004007203507034810001420703070244072054007808030b41e191940d000010740e00c14480500e840d0b400300400a20100f10360f1202c401035001e10300008025051100301030800f20352000e294101740c00c00303141a42e650703244065076412003440e0409081240d007600d00360011002000049511203450300d0b000070406080e8a00c0c1d8818085580e80e10400094803050404030b000305100112644c2c45980007868a502a00c3c00c3d6800c409142410381c1400b1180031600e60320340c03100c503400c442160800704401105400041c107801110350150180041d6018544401d20070740b61800112030019201d0100783c0d40d40b105200c1d42052100a454200c2c15078695558204483c002004180500862000041d030a14008001030240e202020313000380a07481c7c1050030400b10301c581e8007025042200c1101c4582942c09228040094103803020350070245003100000203a5170f600500e14100c5402c001c04403640d886280045942c42070307000e010180403207a80070105c07000f04030030125503030032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 860659010 1250 860657760 860657779
    0xb0d09030c06020d051b0f0426030301090e1b01020a150617011a0109050a0e0c0d024e040c0306020f18031b0409050c0301020316030e0102130e07050702 67
    0x884c150360405ca110718603480070110b0441b00d4114141c05845001000c0c0040f44040c042404005001024251a907650582c1c000301054440441820356100382c0c00708103425076070040d03152110424801c0880c60f507001c1c6a5440000c40c4100080d45505008800801c200c0c0c410000c1041003900c3c1c1d008a028010800c5400c92003141454210b00a00c600100c3e000120300070484014650b114442601c20780700b01030186a001441e00c1003811b1020700c080d0032704185003014027103000d003400e99102400c0b12850f0035000c043c9828503950320b800569408588100404010380001c5444a02c50710707814904925508514203a42e00d601f400200c05802e42c000a100d2400000e02c00120300e41e15002d0142d4202503204158215140030030560f64201079001e4041040d91103100d0a4940b8165001c440682d0140302507c910210748000070342243d00c11a0140c00d064901e0710007194145d4544a00421200300100031031908610a4118500d610280309050090260000180f01d45110350b00f0f640c8070340d5007d400f00d181c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 860660260 1250 860659010 860659027
    0x602010209010e0613030b09010225300f090906080106180504150906231902041a2503200a030f05030901151206150b0d09030c0602 58
    0x207980a000068001030455215901e20302d8001c1c219408034a002c612610084d01d1941e0301002141c0081c0403a034a175500b0f0141d880d4001d6050001c045a100183c0e400490305050300e06404407521504142d202d40010b150f441500c0c08510b07004100c0c4811038105100c0c10404020101d0b80301c08150000b11596040401c0003881c5941500000c0c10740341069103640030312030700c0c40d521421600c040301e0240c50810000100310100241360b020300b500f00c0c040e03a000b142003c000d0f46c5400c00c040d4000d49582d00400241e0401c0805212007002500643d02e5840940c43c1c28035100030840304a050300c6401f6101c48000503502c1103612024100d400c030500c2d4100b000f01c125480c1c2400350001c41c50309040020240e0a10071001075003004105170021591549a00e4189507a801e012900794200030100300682d0f5072080d22480d00c95030b09400400030f14181c550b442c52000c1a00d01141542d030b1740132000b968800803001c01c0c080c2625000580c0c41c1c00e0041000002e0104281c1821600c07001001d1025180902c00074001c40b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 860661510 1250 860660260 860660263
    0x6040803040b1905070f02130209060304030c0204050a1802152a0c01050903060a0906060503150a061406030c0c2a0a0828060e0115031109040c03120c0c0602 69
    0x126070034458550402100b940016102c41c4160000241b0410101c840f150062610103482009501114001030900c00300d4408a10142e000380d605601242191400400b1031420340280f83d8013448411b000d00c41d1008051841c020b244159100134401d0f02c100c00e004c008082c00e41300f130700d1602021419a50840d41c100050503141200c0f8481c415031030003178075114109540034004440015101078024181e41c1d0b83d240300341c0c0060190020445100d030311350a0002d482d540c100008051140c0c15505043c403400d1070410031003107030741981c0409610340080c42d2102c01035032079000b034030350065071101042d0307440303e805404504026600c040d1102d900c007940e030b044812504c10141c00c0c0c080e800c03e88500010301d071520500e03030740c1d9003071070401d400b85c108580801e00d40715902016481c465841840c022a0444500b4401c2d4259501c4082a1041c075036948000c00511880c802c441c04c4040098074201c40c06c0c03d05481701c0091109038040589040b600d90042e1400078400c6450706040780d00921248007054981d00002d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 860662760 1250 860661510 860661517
    0x91e06070c031203050f061309150b011e0206011203020a1a06011215090b04060909060e1501140402070f050a03050a120204150c0203071206060303032306010e06040803040b 76
    0x5a0303160116140f001000b60091055500424203601080d03c0359440c2d804103c050305180315440d04240c1c40e1481240000da0003079a0b80f80b10031251b072000c40e02e01d00110004200d9a903004a221409122600c09848640c01240e01340c15601402041156211075003001e070719041c204040201407403111400d00501c4284400e4030303800381200340e0300c071141d09240c1480403003600c000e00c031420030050340300342c04008050b219072240c0400320014001041059a640101044442a4106451032038487c8260049580f042c0071000300c14050031080d004035410703c580e108144140e8140b19001d158005590303003d100021181302c0f13405510800f11100e5610740d18006007160041e400d00070124400d150f081203007264500035103060740d50354009000600c7c070081c3c0444040000540503601800764413030200c1c038034515441c07070040c880c00707160301040b128518a0300500302e0300314407108564400240f2246200f204842d1925411040c00d00e0040e880e2011280000d80c288544c0d808042e02d803000081c00600802880040d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 860664010 1250 860662760 860662763
    0x2010c0311060903181e01201507020120090105070f23010f09171312050a050c0904021806030c04020c0616020a050607031812020303090d0e0303091e06070c03 70
    0x1503020702491080c003014450001034680c86c08420002442ca65209100c4a4000301f4404840c1c0850100d002c02d4505041034010f5800654a0740e20401205603024000e00f03420101400b030803441310841c160045014001d030b40680d1304000000035400d060244c5107030803002440e0400b0401ca4001035154042080345490844440f440d4244105280d03440740920680c413042c0d8100880004440308510514804d603c1042900c5203029840000304d031300c1072411691001b4502c00e01c010202c8400c1410950324090680d0800c034030610746c000c00c201c01a21403450107881c004203000000300390307103078500042e0400c1003072041207400038800300b00b505034140f00061031070040040b1092030b009114481c40480e100c48595501800641c003144c0410704030341c4241d201e40d0310507100107026980c0038460341c3c50743e21300e44030103441c807006a0010003409030380c98080c0221460b510300b0341030401c220300b103072000702e503d900541e0b030201e214002042c1200c066500e500b90010366a00007c001c641c0d240e90703525000049061a000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 860665260 1250 860664010 860664037
    0xb0313060e0304080d030b061210061814040b03011b0e19031208100e13110f010219020f12210c06130203100507080105100504030c0302010c0311060903 67
    0x80c01c081000031040b54107494543c4007803d8500f019281c294060117281d2076594200070100b08035180d24101d81d403124010040b00381031a0809280c03d2004081c15180d0807205904071403400704124040038100003881e851350a0341d020404408140010340100075586c0d89103183e010300884114011303441015a500024111403211032400600c08850132039a950000410440d000d24860301014020030056501205550015a110f6100c02c5500031541d03042c0c0300717803c01d0341091010303008000460034486d5030410241c41c24642904802c0000359078807504050044040044081a010f41d10b64078030203c1484005008034180c00b42640c0c80310382d150201108070891000b540d4818078a0310342da0b403c032807034508458010196501c03010680b44081c61003c00482c2e0511405c904400171040ca801140c1c4107040f1a12070104942c0342c00309109038070f80001381500c20400304110900c00038402d01c0c07100090703070380a1a00c01c001c0700341d80c0f90981e6020712142c009101881402d0410054410020007003540314402038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 860666510 1250 860665260 860665271
    0x24080a230d0203040f1202061b100903050702100c020112050c0904150608070f09030206090a090906091b050a0b0307140f030103061104141e060c070503070b03071e090b031306 77
    0x30240f140d56004008d51141c1c00300840d6081c243e00c40384a412840f0910207403450100040b005000f1524002c404802151000c034002055161240514507041c0641c1000789045c4400c0e40024140080c1c51140318240d65604042040600c241081d00c03007150000d8803c00842c8000181c81c9a19407180c4079840c00a80400009140c040c800c08004c095124030352103c1c2e080c0c0d4116820840140c0014658941001c074071600007030301c0300d8103014a88815004483c002000070050810302885400c0c015540c4001c078207014204143d80b5515840c1c0115104011855182e4a90400407601c068003002a81c80c48440420001c901007042c1004504030303441054104003494500101000d9070280d8485c010f22000301441042072400e0424107210f11120300c403030200264000d00009010358024401c041100e5005e444140001d080c2000104080d1170701c102d60a0440c40c240800808192505c40c0c030104240701c03000683c1200b03010311116000b40c56540c068503220700e03207a000000c04080c54401503d0607414007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 860667760 1250 860666510 860666519
    0xc1f1b080103053c10090807020405061e01110f0723090112060c0212040f0302030c0414041b0f03150b010f021b0607020607030324080a230d0203040f 66
    0x421000c2000340d10f000a0303101403141e00100415013140c010540e0103402200d441001d81071a603c591982035102e40005511110280107001c00c0f40c200420090050400603484654400c3d042e4004403200824a0f0030205103a0400b0350030304008030400d090303100348503940d404500c00c1d40e10403c507052050442110700d02d007003040e01040300a4070b003841194902d803100300800c400705041c0e4111401811503030040300d0910000c0000c00301c0c140c0c0603030f10810225048510600440c83c040c0941c1c42c4102c81110248844141d0442c0c1249900700a003004112407141803070108441c5c001200355006202102242900944c0d03402d10601c1c40180c207054441c468600824044590b01a0361030320700c40d049a41c020441d40d000300c240c0c82c4160b4140002e01d540030005205902c01030391103000410020b0b11a0340c0124802308a041d030801200c03007040e05104d007850003903414480c3c0100050007680641d0018007170104405002d44c0d1644e18103040d183c0300c24500903014a42c80c1c00c0e8002004004542020b421010255584d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 860669010 1250 860667760 860667793
    0x909040f0224090d1a0103081309140a09150e060f0f16030b030a02030109050106050405180a200306071d0a0605031f0e0106030f110c1f1b08010305 65
    0xb000b5001001d0300051042d0003c40c1000c03800c543c2018440c80308182643c074814900e81408209034401c4034021000940e0f1102650b0b5480c8543c02480392040602481200d0f2828030740c10503009008600d03140d900c4d24a0001d110051654030000002008100070320700e2a07110b080c0d02d03444102c0342d0908001c10900415045940b2490103403244126040c0000200d0a1590460242059071405541442910702800141e40c1c00e1044280b4a8441c000003e14a89000280002c2d40c0c0010301002d0140c40c2e45920031091940400c604424503400751114600c4240d80c120b86840a03050048a50907100b40c0c81084074890300000941110080100d11768000400d10007040000d038030074050785001410a002080303c04041c450030880c01d11000c245800e1582d21043c02e031050000036400300c4006900c40c4903000030792005124400d500c007111040d02e41340c0794405030529510394908910194001c1d5002050541c48003580c8268464507004c41e041c400d0140703c40c80202600402e01098400c0e000d1282040c40c103241 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 860670260 1250 860669010 860669059
    0xb0a060f0b1206031c082215050a1e0905070b03161103070b0f0a05011409060d030e04020f090f030c0f060a031104150f02010606230909040f02 63
    0x202000700318038024840c02412a001c02c0a46003640501c00e107040142c1c42c46032040c8602940409994581e51803a0080c044a04003c41c0c100801d40c110206074000003042c601c0005d8040340e00c00c45030228264443d580064004e02e40c0c215880310141c1459400318503011107070003045034035000d14200c4035002e459001c02d088912094440c200c4003da83c4290702003283c02030f1040012103410a055904000300e83c4c4034002640b80480b03440040e2030b40e100401c070608006200c8c80e03002d02075011100384003042900c080b910140c0050a9940b02d803a80c0e602000c00c16208072007600b1321802c080d100303649032054030b0b51407006038015400091142186180e07050b680e0500040205460100810380b801c010012810300000342c0c80b41e03007403400f0103850f070200f14690104480200001c14181021f040c42c50780c00c0030010115030008407080110f9060032420800103610600c1480d12114800c80819101c0410031b145c6a40d1048107c400d811103c504104002e014135100b03581c2455000f0b0b150f0408100070440300081001c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 860671510 1250 860670260 860670269
    0x318040b091f0b211e060d0609050303130203060702030703050703030b131506140910030506030307080705070e09061b03060303041d07031103010b030f2e0503011506081b0f070b0a060f 81
    0x26020b00c0000d61b00e00d880c42c08a11070710b019074800540315040c1e44403242554130840f81a840030094070018421400c04004841d070007042071020b50708000c00d0f03650041140c41040c0b005803c0503203070324040d036203681d5045820700007801c000c1042043d4034100200c1a141c03140d9200d524041280d1800c1c80030b00a2140d4119500c1d244020500d0081c04203020081d4010f0a000c0c040c250580301c04d0282c0c0c030024840740c00419155004000070600303586005081c894152004110002e1500b109082c0015507848013108114680c0c1c042c50309132640d031407401191660250b079001005d8007041103280711601c804400d07282d004d022240e40920400c0c9244490352148d100a00c030f9514071b1030040001904200e085425982c000c20703894002100210701603100c00c100c40014a098541c52508441001146000d10516200001411074503420516140000e0b004c104010300304400c2944180045034025202e00440782d4010346500c4107a183c96041c1000008001d08840006055140003804200001e03100700c06400c96 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 860672760 1250 860671510 860671561
    0x60e070c0c081f0c02010908070c050a060c350d1a04020906030403230c150703060503071703190207090b010806060702040f0603140318040b091f0b21 66
    0x1603115100f180c010005803003090304655880e9000c0d03000403204e80052541d24000c1c1846020740b81000300308217000302c2684c03006040c041034480800000c2c80b441400b654410b0081102d09680e070808070b01c100c40040591034003d08070000190107501103c01d80c8291016400a120954031039280e6060100f01d00c1a140c000e94480c10901c00540024072507103072800005941c1c1d4000861120780b41120095802c400c45a10541c1c0250042100719550205584c0e13100035945418000c82e46400d0120340c40b10700c1402a80503240c641205201e548600301704465030588800300390207403841141c00c0252682028040c40c9241800d0207071041e2698803d4400c18029200144001e190801c554200700042010444006156071114070000c042291042c4416110b5604405036a450404101741c1c07404c411816001c6224910380021106182c0303c20440b1584041e60200040c21658024014491060140d01103107101d500007480011807080001600d41382d903104c0704142d903203854282d81011803200f08009a03901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 860674010 1250 860672760 860672803
    0x905100504170607080c0d020f04090b030c0414011a0c0303011403101406040c1b05031317070608190603031701090b01020a03050a17040f05070506040815060103060e070c0c08 77
    0x1b98070b031100800c071a0990b484014a071022080f810811600240c0c03045103099035404009480c0c1c1018407070150304003800c90381008010024904c240ca03407041070082d2850904884002c40001800204545071000c07008212505d96944180c21550300c00401c861a009007d180120b484e50029809412143e00d005820301c0305030784d56141403000402032000d40104101036501f500030251885850744c82110301810245a83ea000000300c0020000d869010055034010711162449031100400c01c0c2065604915198034191510848107040d8801c0c2d62103010018500304001041540051409400206a01c11184260b9a41b00b608084900c00c00c907150160304100300c071300006442180202100b0320036080c045280c2e500d40c11250101c020803503007151103000c101d60350710600c8010040d41c8000c00c41200c5c0a8509402c100540740c680b031800c3c041d10241080e10f40820840d1b0301940100000d00b02c00e0305d001400346000e1800400c0c0080c1c44a080e030700a800003401140e2f946000c94400e20000580120444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 860675260 1250 860674010 860674021
    0x40b0c012c070e1005091006030c0f050d090215030a090b06010f1b0201140a0305180d020d080603101103061906050f250c080d030603030903080307090510050417060708 74
    0xf980005021194030b0142560100b80c07640e591100074019400c0103003c8031020b00340038024040315228040141070000c041c51010f910f5602c030040304c0c040700030780c3c40c0420b0451061002c10a04401040111404440482000903290040e4810241301b4000c8034028400d0f21003c0040d1099102c02c1c201400042c82c0307251150355851050005840c2034810714190640d0041076040e09041c1d08195031201c002034075141880012400c15000300011030f00d0340064004500d40c0c060280d0b40e000c061040703005000385100018587e030780071310a03c68046d030700540910514080c000d0503c0711b94011034205102e4030590049032280c1454100e950141c8410f03445141c42c01800c0d407502c1001e90002c8000c5000c044044003001d520401c091104036221b442005010801818400c4040c01c22802064840405203042010404298045080e4080f80d40041704540d9039200e00c10304a07441c50441c1c01c0b498000340801c991080d81c81d0b01c1802001280d90314880c0301c912101c514100b603115041075507007000003460310001c5031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 860676510 1250 860675260 860675279
    0x409080f070309050a050d0618120e0111011a12100c0e011b050c01030f020c070f0512030c0c010f0509180a1a090a2c061b070f03110102040b0c012c07 66
    0x1d111402c540110383c9560a965401c1c2b941c20008540b4000034a0420300c0041c0f03507003211140c0e0000481000a102c10206034002e05035004100010f18419021540d0443c42188284013100848407000c07000e0100b0030140744003814010802c3c100e140050301c0b000e141c21194440105081c00541d02501406030000410011000b41c94100142e142141c0c0c00c000240c0350000400600000704002c030001983d061a2200b04040109070400840b4150410481402c200c003020030b40040d5807109080c1410032501900040750540034140905801600d010400d0540750503240a00740700c0c503590502401444205502242d5000024440c1a00120040302050048556404c0120851500401248410621000d86008910440d940480707600b11400b841045040b000402041a10b002082450440950369840452047d4a0094100100100319914000d02034040360018030212120365103130920441c08900074118901c401001154142c40101100b010084141c50a0000d9002c3d0601c0e9240400341c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 860677760 1250 860676510 860676521
    0xf090c14130f08060114090106080106050d061d0415021804020d1b0c03170903030406111c0f0507090609120c1802220f140409080f070309050a050d06 66
    0x88080201d260800705400750070410000007041e20f4001024194900070101c03401c6800c0114043c00b900081005010031600400b903241100c00b585003095032984542080c100500c3c2d1170300003203078003c03684039280030308a40ca00c512402903000305503082c0300714001c0c14258200d20810300c200c18000d45940383c180d424503066000d4051440c15284c0840c3d00c000e0000700310b2040e1601d5821101064408150109144d4407a41420352070407501c400f62480d040100c5c216a076400020401031815450750f45000030103180d1070980700c0c035411420141020a100c8400c06014228048500a0b1a803929000071040c612454242e01150a00d841d41c40481d07003090504030700e021005c04140d600a1064900241c101d01500203030040340c40170000140c941841c40450914950b03a809420028000d0390824410000303200b1094046480c1250015a903030024000309002c1e002142c409070001c0d00108010311840440380091641790700c40c6da10740480c076880f04208905048030b401425003024413101042c002504a074441d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 860679010 1250 860677760 860677777
    0xf0b0906150105130806100e090601050616030c020a0f1a121909080d0e1006140d0c080304030b18031611010522090605042901090306020a090f090c14 66
    0x1004c2030f12000340b1440c12209803051035040c0540d000400559041462041d0800704402c060151b81d4904000119607020b1405000840f40c0f901c01c0c1c0c0c41c10036015061890425034040c105007485030366103d081d1141e4000d072144c0c80e0001d02101d0212400c0d020581190041014140e034030300d41d5101d007122200440036207451000101d641b0705140011441da10003801065001c480c01055501003c0c030141e0130070000303121514009081203000e02c2880140f101c00c40d08034405541c0400303018500c0c1099910034015902081107400005004000d10004042040c030480c0b160310029180d0260709452a682d2040c0802c0034240c400c0c05001c14000f5002020400d40201c0500d403035810440c4a060014105200950740c100c05800b81508000206190040070003c00007200c081001d06660914404014082800d1030810100c0c51909081607010303094040180d60010b01c21900c0d0550300c80c018020010b03502980007003450701d080010303640c0d1035070044401010807691003119114000700d030843c0d5600301005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 860680260 1250 860679010 860679037
    0xc0e040f0b0d110d0803090a120e0a051e090c07060b1801090903030e0615010f030c051602030a0b0a14221209090c05130b070c1811070f0b0906150105 66
    0xa030b250105c0c101401943c0103402080140c0102d01142c5030610314042130440b04000d0154603280240c0da99140725000301228426aa030304026007100d00580081503440f1a0150301440a0090007000c5843c0c030041d040941c4183c004000e44c80481041003083d585580c00d15040041040c0103121009443d0044000c0301e109043c00f041c00450181aa401c000040f984604403000704800060300c0d680c45100b00000041a040c2001071f52807011008006109400b407005441d10510504c500310340f000c01608620a81016060340c441c00d14804440141c00101001000038071140c01082c034045036030345000170540c0c0e080020305030110079a9400d0300740c4050031041003c2c420300810000e000007050280300a40c0b401540c0300c230b60f210000c4c80c032410780707009603080b4045409080c08200002000140440152140c071a003509120f080c3c1d02c404006020000c40109a01e9404110300c2c041051020314462440d209207074160aa40d240c2d61a60350b106022510840c40c1030381d02600480e9035004200400709c0cad541105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 860681510 1250 860680260 860680279
    0xa170309040903120c050a09090b0609030601030311010c03020f09040911090a20070512220e070f2d091e05150c0703080f0d0c0e040f0b0d11 62
    0x100040c1100e04140b000c1d00421280300c1800c1420b10984602c9240210170f0820341d043c138510f0a401880c0700414001e41070610754601001906580d50307002d40302d680c00000c084500d88e603103a240050460303c002600c1c04240d0f0803d01c0c000091800788c02911406810440d000d03060002000410014100d2501d00340e5000100702c0030781440d0344440001500c56501c0e600c02191008203458030f2141a100311103081d4910b40d042c0247d90008a003c04c4114803540740e420425101d08000340c3c24104518412030071a091111680d00241c80320120805920a8040e0303103890543c9440e41806860a921001d0740600d082742d8190307400e00c6c820300c1c036442d21742c0b0707000314034001421036150898081c81c203050220070746061181640030851841c0044c8243c1001c0c1d840141242020806814960358050354000140080004290800300f444190f06039a4056981c0304140084400e03514083d1000038041580c90141d4205440c2080c010101e00071521700110190103448800e1240d00d4030002c903449008000d50001c0c154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 860682760 1250 860681510 860681527
    0x19081209072c220f110307081516171501090e1b030a06030f11100f140a050c01090c090f200f0f18010f0801081e120f030f0606090a1703 60
    0x70580071344040c4202030100c54205100d04051412065611002e207503400650207405080a606805820007000e01682a44003c0c01c101607a4020b030709180e001c01211142e04020000c2080c5010102100003a26250040754480301c41081c015404c4924070314078500e0f1a482e60944010500541c1d0090a0341c6d0006209601d940c1e40303a0792040c00240580350108205c0001040e843c0981075403099054509000c03030202e000c9100680b240c10b401000030a0040c000c030703480c00034030f0040084604562000d4001c02044030b00c1d1070721042c5100a03000d0402e4103450980403e141e90b034a841602c00503055036000d0b14406040c03240c8918103900403070156111120a1011141070f48625014020720924001b034000742040980004045a464400d810104160301d8010441c1210118050840207a03034880901120f041c1d50410b031429010050341800d6075000640345454049410143d80606014041035005444000400c00c503809401903035544942d945008015041200000c00e10200290080ea404c0c010007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 860684010 1250 860682760 860682773
    0x1602010612060608010507050304050a030518150c0706021207110d0215031b03071e140c1501050301020405010e060a0e060301091d070819081209072c22 67
    0x101c0e908940680d00c0f2141803140080c01e010f0103174460498a0010304500e000e4641380d545016400014081c041d00042407041d40c2170515900501c1c20b000f40541c07900c90544038412210794401c840118080c000e004000c80c1c198804140941c542c00041d900508003803442d00e804c8074040c1480031255001030000302901c010784070000180e8130804500e81c40741d100c0c40c01d4100b480200c40d041e5080e10448108200b00001036401040c51100d901c0071459017002d1f058070240c290351032035070070b0f1081e034020401050310141d004000800d040c030000c02c000c7c0c06a503039986e43c00307140c282c3c00b95015160100700744405c0328030b9030304104001d4605c014491400203060400344000c202c8640c800e0308181010f41c1c981c0c8043c211220344079200c03110500a940200303070141c6800d402a8681c0745940c00b004044400da2501001c1c0409001511402c551801e440061343c18400c00d0f40742d8656075480b40d4140704481e204200403036071038144002070020508014001503940c90300c8070400c45004003018095804082000c0001c60f50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 860685260 1250 860684010 860684039
    0xd05100f0b0d0f210c060b210105010f05030a1203020c07030c030f120c12110a1a010608011d0c0d060314070303090f0f030f2a050a0f08030316020106 66
    0x2919160515141904080300c1e0740c00c081310310000084062001254070f0b5480b4284481c12a04504005020812000020030741e00c0b0400c1c8800d103440c0e0307165a4035660441940718604072520807a113842640d696000341620b45c03840850260241a5640b09400f441c0d001e50020301d00e0210000c10340b40c260b9100d0b0b640543c3d800b8950402d8881481402c425000c016001c2e81c131000343c0b001d6041013401100c1c02d961300d02070600311548410401a0b11000600380c040704102100e9419404000509107095640c0040040b050901c10310b000500d007040002440c0c103042c13818020740001d80c8078060f1303580c1d1445040e005a0340403048120364203544240003c08602c980001c03a11514504c00640360f2149142070081100307030b4a030000d44521440500410040c2d070004c000b6022a40c0c8030303050802007210b03410040b4565424103c400c80e4008544400012800f100e001c1c0c0c401d564084801200e040d0b01c5c0c0b000c120140c14180200e81460303004201140b0601c040c4050a4000f40f00c074400403402e82d844500c100100759 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 860686510 1250 860685260 860685263
    0xd0f12110106060806060a0e0303042111010e061e0d0615080105030715180b0a0804150b0a030f02030a0c1806121214090405150f0d05100f0b0d 63
    0x800600501102800c207005072001019113280640c0d481c2003c0001403200c2c81864040c5050158010790a02652014002d80f00182845a07a00c00e1450040080500c07030014400e040320081803032901c4201303d6002d804c0041400102074805810640c514045c0c00191085041a2100c2c4d8024400154a54a103015450180003000022080c0d844603001c007521058040c0c001c00d2081c0c00c154070500c840400d40440d41541042841d1004006d0303103c000000503621541c02000e246800050380c0855590091500e50040f0702c00c2e51102c50107409140e500c02113501d415005680000720032400c1020ae8030828010904070300090640700c12a0b207580e03502010300641d50100d60204c1d1004400d40c0351079803500c1040000c0c515400e24005030b140310741c1d400580541141d004030030300c0704101100300000514002c2c2c80c03440300040c00401803800d0040225041103400084180b08a4003c2000c40580c1001e050300303070005d41e100d401401000706210344007002c4c03c4804880d000700ca80c2c6407540803d9a680a03903a68005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 860687760 1250 860686510 860686517
    0x7020c0301050a0b03060601110d0525081c200307030b040e010e070608010b041a0412030c02120c0906040c0309050105010f08012702010507020105072f0a080a020d0f12 74
    0x1896031130181410600000e00b8036062061002c40544611000701d0003161080480c6401c40d40c5461030f208100050400d5541e8004e2801441441410485180018200c03007401d8103c5440401030041200240e803040354650701c0b03c01d64155805416803120002d15040b030918100031074100e2051000c1400c0343d0b40d1020748910b6030745542540715001c4e400d2154202030f100034513285007258109a10344001d4880c900c0340e1900d41c0e860b60810519451500251005000c00c110740b040700484a0030005d084428445060744103240f030900001d035220b0005062980e43e40090034115041c0d54044c1000001d00d60604841d06254540d480c0c40000348007881a42e02900208441c0c3c907086081550481c03c6440114000c02c0307401142e551500c46549520f82003919a60900e480d42d0380310aa4401220140101d180017050b105011814044005150050340030340c6540902040c86000e118082004910492040c001d017a0030800c1100c02504100144c1d0503558080c0715801c404440340e90310002090b010b4624003000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 860689010 1250 860687760 860687771
    0xd0606050f0d0224090a06020105060423040b0604060503010608071701050708010e090a141b0a0612090609141608010605090726090c0315130b07020c0301050a 70
    0x45140259001e12065015558415004416404611034456107551201c040f0040000c90340814040c2c0308480280e18050100a1501d507600d01c040d000c0c01c1c060f00c0803849181440c0501d01d017103282d000419a04509c80543c90711341e4840340c0b125240100003034119a002611a40701041c80d440900803203005100d010001d003525403800c10a00a20b03030b108107100000f80d0505092040303140c2e000b5509815160740c00c00e07c2203aa00c030414000c0c03a09407840c01c01058800b9008011502500204081d5001c0030b58000041e00340f219a802c1008821031400307181c02040c0d0700d070710301071000ca0340741d0054401500c544000251386d10642c5422205901c801c4e1a10050340c4a05030b5031143c402c10f006000001c011000003480598200300c00602070010041c072010400028011440c0f01c182c2528008041820b81200002c0f1420580b1000751606105000075010f8401c00014031b00003120807810520413915018200701101e55583c662002050240040045101e400345007001d131341d02803003803502070714900200248 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 860690260 1250 860689010 860689019
    0x207120f0b070927052a0a020f07150f02060910091a0a0207032d11031209030405210706052101090906060e04030e040b010c0503040306020c0f12040308030a02090d0606 74
    0x150748000307204000c80400d44680e80307000010307482d0611120a06501b42078940403608812807802c406181480e1b024414500c0c0024105010144011000343c144e540601180f6180c0041e642c0d91019a1042c10342da1000300d00c0c10658030268808440c0720321070948881d0100c0b40391b4662081203800d440342c00c1000c0d8001582001c0607040580740300320000c02c0e50b18420200d894905001d85029000012091200c2228403c44404080c003c42e00054041d4a1208650030031040070380d520b821034007a0b07034042c1d47d4111591600120b19011040401011300080c00110b040841c200e4154002508540c5180e62400900251400b100302031406030000c4034000070130740182c2c241070f002c1d43c000c1d9014500c10f400340c10074080460740c4550303403c240b10000d440c0030030a40103100040301c40300c4582c0030141a81c00042000300401c5015001869014108401c030340c01718014003c00351325242088042080d4602c00c00082000900c45d0015543c4080b982000504010000002c11032010310f89000b10743c05640c0708001d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 860691510 1250 860690260 860690339
    0x60406050603150f071b050303040308130b09061506040323011d010f0f020301062c030703031d011b0615090507030e120f0d0e10021303030207120f0b0709 68
    0x4d2080040c180006e0300090754403074589078480a80080d041001407000a004a1074800360b1080342c41e40701c0c030102140d18101070190748600095400342286140200c05500c43d141c403106450a981c2c02c8010803030005c0d040c03c0401c0718038020000c070300807039500c0f034002c80d03407a0310b08180307501828110b440080350880c0e0b440c0d084401c03240c3c9840c030340d031200740706100501045034042141113143c44542c040d00c1c2c8a10042e00040e00032440445a42d40c5841541c00220801d42d10901d902d150300c907248500324090703c004006617507107012204071074441650002d0b40b4011407290703000000c8464070390012000d4035032260413500a86408403840d0000c02d846441d240d6100f90304002c2c0043d01203030940010f0030203000300c10302030884c401c2000541d4507540301da90241e00c49600303004452614100c0c5100319514800c01030700d12917002f024442a40903018403540001d44203241c40400d0385440d4095104643c45d02207556100000c0005800c500c20002c0c0b000c03000c00d003034000d089804065070403c2203840410317000c042c161 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 860692760 1250 860691510 860691527
    0x10e040f0c0c12030912030f0b0a14090610172e0e09010c0e120c0a030609150603082709071e0c1e15020f0a120e060406050603150f07 59
    0x610030580341461440100b4003c2c030702c0e942900010300d404103c0480c02c05800c0c000e42034040707606500ac1001e10700001c3c074510005071500c0c040003d40c3c000c42165161820020b00c9252034202e44007064034000c903c3d00f041c90307407807055030700c40810500c080001908002410102d402d5504210307014003540070130711050612079010750740700c015400244180580343e40000d0940d400744120602552440e9034101c1041c806203c034407042c0b540a0b0500740c58030b0780d03400d0030005400b01071400d0300e410302c0741113503186940e900f070051f002581c0d080305000b4942020303050f040a5400c1d0400c004120942d02048103043c0d956031501c010701404a507682c2c038080544910074058074a02c006d10742c2c070500101421440006640e2410001041090700c881a4030381002e007072130003110300203100c01038a80e48001002510301121601500c003c01c441c0d6668142d00715520074440444090a0207410650701000024000440c150405544510058180c4e0041ea81811521401082c19940882840c1000c002c00142342d5108a82 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 860694010 1250 860692760 860692793
    0x2619060602030d1103060f1003060b1207090602030a0206071b0501020d0f051e011e081905060c07020d020f1c030903021f140a092706060e0f010e040f0c0c 68
    0x58174510704240c0d0008042d0711600000134040c0744600602482d084c000da018600420480e40407607500d271400e08a24500c001e044407040003003298004c003c1511440042079680700c20041e00100003035101c2c1003058541003940001007414070108940440003c00c00e0016083d019004013010800410164110301034810080622810010141e964600c400d004414603044820003245a40504140710f03a2a035542d0f425008100e180c0b00d4412a102c140e61a003007499601400342c0b05440c03194071255015143d40c8030320300c0040d500080c2c40c464100949001c0b21445806c0348024008400c0d442e004131351404c0101161000d40100e200301c031042080d030804024401420b92401010305524140d8180504540c0d4a036540780c0070f0b0640403506201c03d40c0146a140060840103802c40300014220000c0a030748070b003080310964110705001c80040e03100e004420040c4180c030300905240d0440320202c011a141e89500c0801544180c423003560030840411881201020301950b520255011030700e0030403800c0c0c0e0300203548 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 860695260 1250 860694010 860694041
    0xd0c050d05010915031103070305060f040302060f24040b1005210403020307140109050a210806060a0509030106090f020c15090a1106210106030c2619060602030d 71
    0xd003514000a46803940b0180e9038072030651543c0c115030002091034110b0035027004105214903410311101c13000580140c1d20440c400d508445244d500c448261480c0e00040d100b01100d408084800c40d00e1300c0e10520310000c10302e009080000c19003d9a00081c0242c00200e400b5800301314001106c196503030049000350041e2a946101c801c0a0400b0354000703540707104500c00580950020880d5030420384081d001003080580200c00c0303400e003151900b01001c581c140c410000622007405e0304a02443c5005000131440b8034030051049083c00d08070703c020b840310342c071800d03400740c0c5556075000109400c0407a101c0c0f110b03080100303000103072180d00e24070741c4074a00040111050b21081c401400c105008000241c1d01017040d61260f00c0f085084186408600c03140244241514221012841c1e1071031840300100450484945540500c4030901c000d006803682042110b84c405103407110110b00280040d4084415040b43d004000c03e2400c80c043d0600c0c0c0101e40c0c1d19040500160000580584054598002c100030f0442400303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 860696510 1250 860695260 860695271
    0x50109120206030c0c030f0a050a030e061303080c0f0c1006080a0f08342009010b031003080f0d050a050f1303050d0c09051c03051803030d0c050d050109 67
    0x1000120b080c0401804108000000521081d8003c814002d980384114080440707521444025030107030480d00b00d4002c24000a14169200b41410400039905000b0000d2070081000c0f10b400c0d460858007044002c00d00b0615440401c08011000300c800c0040c01c100221070090561407150041503c20748031580e220140ea50312001445c008074640d6500100a66031007040382d640c0c0d11108a1020181e09550748185410f40c030701100c0f400f55039100100103040e03407040100944030840318118500000f5251211900010000010b00250002000031a0483c0003070b1411043c0d01e940350b80c0c0781102d60008106441c42440454641034403102809684c0c3c003d0340f558811710003460120300c800c0d0361107801450704110700303101c1018030103040c003030011a0040150b00300140400903a01a000e400d0b401e10348034540c000c0900188601518400f0305084401039410760381d0a1400310b10320b4101c22407213aa820500d50600007000391240100c024810313100800e87c1c94903030940702c03680e602102d81101c4050303208200007800e11 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 860697760 1250 860696510 860696513
    0xc03180c05040c091a28080609010b04060c080d060e01030c0905130201121a06030a0c110a11150c10061401030603020a050d03050c070b0721090605030a020c061005010912 75
    0x4080302c20301c481c441c5c03c51500d404004c20254a6030103070400c41000f000a900c001c0c22982d5224400074481c4a003950450a1640c2c4e900b4010418403d070b100704000544189c00313000014401600401000b52801c03000704100e42c89080f508400503007039008a1301ca201600041003488180d000385548040d0358212180b1900c12600040e04402c4218100032020741d517407000309008020504114041c040c003416481c0c4034506820000028030201c7c2c074513000324030805d90010308407000007183c010030f9a000034a00701040949013030000040700705d480d01f40702c11018021030210440410030100c1d60300203003c0100c0d0306440c002e01801101943c03040c683c1018204103050025881d8190381d8002c8500c2030340e06603803001807828211094004c640f201d100754001c10100080130074401c07000e451b001d40540300a800200c000080c0d0700503880e0000c2460b000c80c884c044100320a50240000d0b40e4060603181c8c001d0b2922060a4000741000e600b04c9042108503440c117000d01055a00c030140c0e40207800650144600b880e0745 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 860699010 1250 860697760 860697779
    0x7050303040b1c090606061d0609061e0c0304032109060f0309020d06061d22060e010e0d110109050613060b030706052107120c03180c05040c09 63
    0x164054454042400a8041402031a6400b15603d19403896003c102500319441d0420207003519100c0c8500044032507200ca04000c00307212410034450030081c0543d290000003001c2c04030302d8220131000342022007100070110a20045400400c41010024090342d5a98154500710510750344c3c4a100101401441c1e00300002d05400c4002d10b010341d030883c10800aa1401000d08401420781242e00030340040c1d04410030300070000280c128000762080f4480c0002450121081d00b52000012159200d850074100000308c40424165040251b25000f01c07804510303100d0180ca29425240c212708102d01d0b0381e1010082d000d009071b0025180302c9860f00d1030b00030302040c1d8940e2121079440358094116042d12814000c1c00741009800e500542040c00c0c06015034840fa640c412002e00b4680100ca03e21100d501b502c211102c1828180445c03c0c4038100c3e03502c43c004100ca0320714410008059200c1a00c06040e90303040403400440c601060381c41e141c0d01c29902503101c9810001840b00784e074124200c3d241489003807582030052141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 860700260 1250 860699010 860699017
    0x7110a0b040608042d1a010b0c07090e01020f0304080307111c030e070807081b10080c07230d0e091e07050706060b0306190320060d05131407050303 65
    0x20003c141c14200b1400c2c803164843c04803022504904240500c0c980c43c20004504040e030b8021381c2d81d1b660070710b041c0e03a511400c040d02e20500394081016007000070180700608459208181e11844030b00014240415050051480d62041c1d03425070310028040108240c03035a00c026507801003c0340b04054040314210382450310405910544000a040d102e0074004601007081000c54003c0254404a840ca15a52071038583c44100c4c07100010285028029104154100707180e0740c2c0c428034620381c1d401c41c02d43d44000321041d19401681c0120386503094996045000143e01210240058209001c0c20320b01030710641c042c0004204c10403560050300c840c0b0420451480092803400e96042c070341079407044e0303540311201181c5038800c4403002482c1c0307071078024041420907868029522489040e104892440707020700c0c1c40100d81c80d0350300c40105404c1e6860b010700310b08030f000c80b0f81078000300000e42210304040d0201c4032101550380c01c031103000044189018540600c51112000e0400800d942c0c09400410304000100e5120721 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 860701510 1250 860700260 860700263
    0x9070b03011203050f030a020c0d080903030121021002030c010c090b070206070f060e06040309050d05070603021c050f0f0c03150904080405040504050601030c06030605031e07050607110a0b04060804 87
    0x600b2201041e041c540034900300d414480c107640555035a45040741c51040290410002d40500c1d00c900c1200015250180802d80d00802d00140198110307860200b48a400d40d0f00b000f08410f24061320f0201400507151000031800c2c0703420540256446200312203006007110303240c14a4000300503252608120003c45841140ea20640542d5500e980d01d0503400e0a10648030341c1107004011519150303000f10b1644010031800d004d41d200f0b64900d2007441d03692040100c8a055803e02500c41e401c254010004e45010750b000303000714a500c00070204010075a4009200311002141e041c1c031031035481c000701300fa2600e80b0b409007503205105102c0b003803c6007014102d454031178200302081809001c03420081400e01c01000291401002c005005008a15003482c3c0745483d01e5081c881122040002c110102e0b86502a01545041c0d80015000b4510748240c480b54064100349080303100d0490281d491701080644403600201812401481c120f2034483d01c0806114200342d042d0f005646100f410300c414001c15a200840c9500300d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 860702760 1250 860701510 860701529
    0x1e03041206020a020a0b0f061f021e19060506090a020a05030f190911010e090112111306240e090403081b03190f150e0403020f03040b1209070b0301 65
    0x41c22070640aa05d04014100d001c0c120300e44440410050440c203103201c41c0315000990b0402070b0480e08441c0b01411030040d0340c0c0ba0300980c1002c101040040341d0030031104801400c25041f80c0d4180f03d49000f600100407101c50550f541a03d07207040000c0c0741444450943c005240d440114a05804c800d00100f503808041c04040b000d07126075010400e0007044100c60321004100301010044503643c2d242554030100035070b100c2c80c0402c94007003140001d840c00e041414100c501c2d2103a00c800d0180c8075900d24001018043d00039512181c0044085004942031090300d01504c481002c001683e40035041c032213240701c4910074003c100004990403040c143c45030022180c2180c0c3c123081c142d00d1511a29200d03a80d014041035001c041407c00300411400412100d032904400c00e5801d010845080c40201c101c05441031010340100d201c100c11401c002ea0303144d2144080d401800b900c15204444506418141142e000d07a001c64200c1c8008140d0713004480200710020b0704002c13844c0080021360300d003203c42085030005208e502e010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 860704010 1250 860702760 860702767
    0xe01080f06030d3b0102010b01032c010e06011202090a050c09060901030f0f150503070b0415110604080301030b0f160e0102010221010305010e0615040c030912021e0304120602 77
    0x100c04020001050803100104030a050720505509101348001c1e43e49a2401503003000c10200c2d0365406032080b914540550850b18101c100702404000140c20001d0050706659681c0034001101641442840c2c007803e210108100c585071580100903072450090226062207242c80300307010788040080c0486205100c1130744c0b00d5440d08400d400503402405440080030040742007801d03203024591a075110800c09003a09050240746a1254107040d51810302d03000b00c1104010811040c80151a4000c0d0f0312850f440754a0040041d40202203001d05003101070303804654101d804401802040002998190b01c00911410074156181854078004c0c81c04881c1540e8040c0824049114402d1f4400c0d01210040491582c0140842d8542514826021002d21007907686501e40520261842c901103992030040300b02c3d000c1c0d10945119802080300410f5548222400d05a403144600001614000c00008404207500601105850b2940303415a00c0141500340b81e95400804c000d2150040e692640150706030040c80068a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 860705260 1250 860704010 860704037
    0xc24020c0d0311030a030c08070e09011815090e010b0d02030d141b250303050a030b030109140c010e01080601050d090501021b030c0c010c03080a05060f100e01080f06030d 75
    0xc034940310f50200206804001681c14180783c150708640d0b060555581c9004072541c40c254200c8407600b841103519881103100d80100300f5920541800020102108000182c40b440010f0142400140d588070340b1046440e45564211541c0c2071081d01d000f500c2c2603d95410714880783c2d002907100c00c0c00c00603407818400091460400074004205403a02440c4a400407074040148a000944c2d80c0ca5841d0020354040c010410107141003a0111480c0480358551615400c0a606101c203401908a407819250950351340c0c4c100342e01080d084022041092403110180c0071101c03070302c00018044200319000b5030600c44a176042c01410f90b840000c840c0754191030280004d10584a16102e80640f0400700300301010740c11060b01110f0820088020015803820742e0031130341c032401040015980c41a066002a010407400800101034101070703003140744c2c00303031001308144400d07100000041d000407801200303c1c00007201041301c4102c0f940c20440407074220211004001447c540040065034030038428440d40100b00d00600c1300341c4d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 860706510 1250 860705260 860705267
    0xf0a1214120f070c140a02031e3301030c0504051503060109020f04030c06020c03061f14010201020c101a01141605120a020a2f0f010216030c24020c0d03 67
    0x610305c1e804401000384051102e61700e5030307a010548050340709010712038941c40e4010158210900445055001d13000a1070040c404d8140f80c210415010759050700c2952000114164000041c0a1803041139811062410401444121b48005185408480d000c201d01c0c50750341d80010300075045640c510405603440059020000c55406140d000800f05120350380003040040d000b2821112a8100303074101e544c1513503005400d0040f076050040e42d000b40c011200040c03000d0a420b07404c82c1d002071ba0600000d46400900785000349410b505000f03280880395545544c482c5282d040281c945060030034601458124a1903d092080f4841c81104410780c0f88000c0480c1d040110a01c50b0450030400841034a40310000b001c0042c1d10780d41c10620803640d43c48828007120020365004009607420600155100405020000b40300c4d0810103c1e0f03045041d446901250040c5840032041c680c0918030504030305590500d011080400302d650a060070f141014040c1c400d54856070b0016115100c003c00312070003051607000d0700303095 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 860707760 1250 860706510 860706527
    0xb06040b010306210b06010c11102c01090602011401230d11100305070509090a0227031207030c080708120f15120703060e0f0a1214120f07 61
    0x30f469000148440e031240c51003d44c0582c0b00f540241648000c1760780306001150300260301c85005165050400c000c090f142451035501c5041c2009d41061700401d403c64985c10900e5041000d11020300510392032840107540c2c41050000200810b000a02c281d1010001c00c0d0201c4605014102500e410b42000c0c215868814514414440010304480304180703003403d125019101d4040c13824022002031401c0d405003486849007510851080d5111800c5c00300e03c0701004284100a001410038640900c4000c2c006c1341c0041903000544000394105c0c801d00002c10916040c41b160a401c0d40072032105120b0440441d41180ca032014080d03014010a984000c640707000304080c05901c600e01c80d41e580300740401900104040142d8069100d143c50002c3c442100700030000d018400003181034454020004c20000150309402c44644040c0b024143c0f110b084009031100d142882108096030000c100110441c14541c11002071003100b0f10480103145000204000802d07402c4025005032103144000c80000c0c3d0403032096440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 860709010 1250 860707760 860707769
    0x50405010b0d0c1a070317090a051207030201050f0f0103231b130c0210020d06151815021f0914030d2306010f090e1f05030a0b06040b010306 62
    0x15421840300f030038000c00610b894090808502407000038a00140e005005486950f541603842c480110038410080c46481ca014044038900d124001640c0c000410034840b42c0115850241c40da5280d802501b0001d007540d0024065514840c2c0310b4003401420340c408005541562b410003490521210280c1c0b18002503800f86507001003a01a01031101038a121074100c0c10241e2104540144d106880d160219003142c3c0c40608401c0940d2000b144070000d440140c0280840390f041c00c20002d0210765525294043c1d85420304008000340940046418806600304a1006000581d01181e80080089406540c03100c50f82044a660001c07110b0442c80c0d110720b40c103c60103403035101d0041800721005003401c0341d41c1d401980720803081508040c07000103100510742c80c61000b07a41c000059034441d00c3d030f07400550f0071b01da60480a404100c3c0750f000201d04420800e09950003407051240d90400814040380c040000d01003a00441e1003500045401030202d0035148511350000b104580c000344010072400146c0041176584e11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 860710260 1250 860709010 860709019
    0x90f27040f05120d11090108060f060903030d022109100911030d0c0506061009030609050715020a0b0c040303050315011b0303090c090e12161a16051903050405010b 72
    0x9404929000c20000d0040c04c41680414409552004a9402103005541006000440700f40001c2c07168034000c0400c0943c01c001130800da00c0c1240000109056034854242680a142c00107041030304d024407528000600ba5100d9580001420520a0144c48914039200360642c1526503000b442804015032503258080402811600341411190028001181e4803034203452a000d80320016030642001107014441c900950b56410301c3d20300f550b498500070048203000b65000cec070a01e4404508074120b45242c084441c2a90001c050546043c076241c40340e90002030004501c00c1c0280001c000281c0c1201c1507a4000c1b0300a440c65510080344801211030355aa04022265941a044180203158140d444084001e00910180b40c19a440707240c03100c03e4074404040d0001d5544503a900c401420704d81400350001103d42d007000109e20001c1e80b9604904042c1c0c5140c41e0401c42d1901c207020307005840080d51f4000407028101079041044a0f8041e181d81c0b0b44601d26a42819214000142004002e50191110020081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 860711510 1250 860710260 860710273
    0x901050909030d242603030c2212081210120204051305030d06090b0402041a1e0318010c02060f0105040c09050d030f11030c0a0303021c090305090f27040f05 69
    0x3c001c040085c40301d41d0920009032410922903004803020040741c1c4241c08003121103240038240070181d04613a5012401d084030703203c400000700d16140c00b40d482d100c00500a0311031684404100e00048080080984411034800344403130200254800c1d00844491113030101ea00090710f680f90004a4103107050100e0003002404005040500c80410b50b0201d01030319840107003000b00c2180b140500c0220300c40d034015035010f80c0380d002c503420b138071955000184500044240030181e0704005410ba03404030f400a40b000d6402541504408000590034800c1d50f403c04140e1004000301c2c205081350040d031200c1805018080c603140c02c04001c0d540d00440d04000200f5024058140c000c00d030741001802009074014080c000303040c41c111102208400000c4e43d541200c268003074601c0c0501907400b90025440100750074040c1b001140c0003c00c0301034038819007031864041c1d12480d40d070320301140c01c1121079428101d2180c03242c0c40d403255503011405e0f42d15550f00304800b20301001650342c5480c00e282c3c200e40304040d4001e025200780b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 860712760 1250 860711510 860711519
    0x3060d06090302030d0f090b04022202040321021501050f150f0a030e2e18050a03030b040e070b0f1306020c0a09021804090305041e050901050909030d24 67
    0x1004150b000c3c0d0075a07003003101690083c1d00c502507c0b62800040c180d145054040340c09841c1c43d080c00540d0505500c02011100b00d2482c142c6d099810590041e107214048030b9880880882d1841c240120740300a101a0a1201c07111003590100081030081c140100514420b074805901c4a00d21028400c885001407915454152070915160307207c0500200024207142e41c0c40514480050300791801c8480041c1100c080014140e00e612080481c1c071082ca00b50340b281c107408100b6003103403c4160418024405442610050300b170190640f606031150134043d038680000310010b2702e4082103c1e000e691400250b075640e1004026860403a0040c86a420220820018002481a0000390105802d801075405900351a9505081000c90140b010302034031103c200010346c1e01500e03180e4400328003148241046410243c4900c003820400f002c00102e401c48050340d2006101525119032190f00510040301d1500c201d1906070b102070784a005400c07220074035945415880c00d00641030744080c0c840010540c5880b45040d030303d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 860714010 1250 860712760 860712763
    0x60b03070b13051503070215070e0901090c020111040f030b060d020402041e09020a050307210f3806031009020f0d050a090b070e030708010e01020a0912020a060503060d06090302 78
    0x1d00c50303a84580800c6800c0c01c1072800600507a4400c142030703000307031448550005103a8080310000b84049c040005d003c030b5034040c0d5518155964081e04180c40006060091404040c1c00c440405480c0c0d0b00d903400c140820000407883d0803000094030742c0320548140e691119004210300d00c2d2401c0c0000e5002d4004100440c010203029600c1c800c9000e041100c02c1c0941d5580d02c2c24003244101d0607944c002607810400540c1c2e141c082c820821903004107a070760b0214400010a20012600041c1624034240c0d00c42007c1c034286c42c0c080d0071004084a10101c1c03041441c05800440fa04506442469030251501000280a58850001000090003610340a555841003020b11a0095000b00b41200e0400e29110108800360741d51300c0b0704131605612040740071440c0c541040a40c2d111203546801030341881903403808a8903034070a0041c0e21b4652801e030009038a50040f800080c0100707625400c040081e0100e03604d01c20250b51045020350407501c05c1e080c070695a450302000308411084401026040c94209540034080650 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 860715260 1250 860714010 860714047
    0x509040f023d0c060c0207080c01050316110709020c01060320090712020f1b120a02031801030603120c03120207150c03270303050c0c0307060b03070b 66
    0x200300c0e55000c1e0100020782d024444070b41034400c856002c807098016202c2c6124078030485580d01c81801d000808450341d90703429003525004a121030058200b80400c105d169010002460300b00b009082550952400c180030100820252102d8000c00c15101c400c2d0303c0c00b0a0600943c005820004015940c40ca40d20325a1806010705120031500c4201520f50804c2d03050700b81000c0080d1020050012a09442d640e80403a042c0d8181400c510f2101e030708100e2048242119001020b00740300c41c1c00c00304051304190756090300300300d650900e140d2902d0307081002d490b00b180c0c04406c98101d9444100d20390096003201004038001d1816070002801003050142024003940c011180c109402d202c1e0342c800020406004025040e8001c10300300a103028610798118207401b506811840342020b4900c2c00259241b4002804144002c0705008440110448041c01d028194580580c83d07000c1d0900c5d007162320305000c4c141c06a40d6071090010117050300d0380c1d0703c51011995600303010801c000c01003104c41e0b07600e03a4040d440c2040c407001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 860716510 1250 860715260 860715263
    0x603050a050d120501031505100b040909050105010e270309041406090a020a0e09040f0503030f07031107200d170a032a27030b04030305060d12050a02070509040f 71
    0xc02c20941d22401803030351300940b4103803544224048225800304a9160260001038801003c001e0082c20110302620003c005d80010101d8860202d003407201c0c0e05103e404c4030010b80001c01408111000c1122800950b841da1950034613665488142c80d00c81c030711980c114024000001c1d809801d0000da0940b04d802d9032403150290341e01302c800030345640303d40c0e510104900c038111000c07010490801d1901001d1500c2c40140f075026019040d05491411546e40302415175204491000c490300c0c0300303010b00001c0c0d5070500c1024110241c500c10340b4508002d82d12994061f4505400740c2c01c24103042030882c070ba5500d40f582e80d00c1c0659888440b801d0400c1001c510821950001e49205000034030702001c00c03900c03816426521803001d0903101c18510400784c8000884440990f4a4524100035514902481e04011310310b0b03071401580100c45081207414645002800e0349e00152031070b88030700c081e69228004036401e1100f4044070710807418420368030320f940300c0186c4c20301880d070380101d910480420807c01441309040021110a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 860717760 1250 860716510 860716517
    0x6060501020115180b12010603080406091d06040c0302130e0601140f0409020a18060e12061b0a020a051609052503090602090d060b0f040b180a0603050a050d 69
    0x500d2043c200b54911250b880b0f191540c0da0b45149061403841e80d64420f050205020b0302c050100031503000e0490a45055a004a5540b030b00000c08000c4598006000c00142854240c502c19650f4a410249521113014000c684181d55800f040031403c3e01941c1142ca0704021644490340c050350760b41c0d0300d840050003207a066010410765030403c003501d00084200c0311900030f91146e150403e402c001e01007009401848411050003d412000204102840781020082400c0c2c1d07204000c0c1040d01d000d000c0f40c9481c0007121150351380500140902c5009901a40211154960094ac0c40301c1c400e607002c929100c01c00d01d001e0003a02032803800303001140d403282c010016101c10020a200c503031030703004542b000c00c0411b0b20b0703001880000c04500e4083c5072082d00001d01c90b40c0114009400c0003c420000351500e2030314242114240c0d5100d00c415580d0509812144104104440410024200d40045001c0f04481307900294201c66150000c1c0541c0700c035500c00c0d8041c60308a42140c1443c00ca0b032902c1a43c810b504100744c00403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 860719010 1250 860717760 860717771
    0x22a0c03100e060a051816090b060705030d0f021c051506090d03260f0618060d08030903040f06020a380901060b0a031d031204021504050409060605010201 68
    0x8403502405802d0305007020760018010342d80c41501000c010203015160f06054462080c038a400e03030340308014400c600d013128003500344100e1908040b442141c0440e0740e1300b4060351040c00600c022a4020050b0f4805a03c0207a0104407400c42050840c000c0c03180c00307013007940d4054154481c40d04d0403096019511400d2103000300308241903e4000c0140c14044c8803001c82d8000c02c10380c5a000044e101d1810108034100323081725102e44a035904104c1006000032100402071584403010001a45483c0802403004080240007480509103000850700405a21001500d1840004080f9248880810031280100400500c40c07002035141c01c4002e482d2403c04c3d106076104280c42d05d150b060a02200d510030802c109040695059101e640095202808010403c3300306560303c050004071100e40b040100111016650000b0b4183c1c03400000c4403031501e2561001030380b60f0090140342c030003580000440d600560100d0315600d0268680030920140c1c4141c1d000181c006003401c1402c41001490381140080d6082600280310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 860720260 1250 860719010 860719033
    0xb190e15061531060819060b09010507050309060c010531030804051c02070501030c08060618130c050702040c110c0f0103180f05071512022a0c03 64
    0x8100394080c1800915100070484008100d0141484200c4005400240011141d5024054904042c1d540c491008a2a17090030441d00d00040c0602012030070011004000c800d00780000d50440e4015000c1c03039818058005414020f00104106443c0c050f50001c00709581c996400b00021b0180400b43e0b0341842c81e02014181440c1ca0015452040c035040031144440480b10060700c0c21941c0da04040e10a40d02805243c08846040f0300d00e111540c104501d9400900e20103180000040c2142c0310402888200b12500c014049079a40f6081240c0a1340f0780317481da0403100b140d0000020f665041808a5116582c0350081801c00d058100000c0c018075402101c0c2003010300c01000044e00c59080700307501c801140d04079828205051504c654940c0070307641c06144c001a070000440030103802c0d41000c1410345440c801c012105080281c01c12031b8401602907030700701031400c4060a8000d04607800340302459244a40201d82c8181080000d40c20420031031500c003807402d0240031424010b8403030001c000c80a006e406100c11105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 860721510 1250 860720260 860720269
    0x1008150117180f1b010e010e0402120f150d170c1608190f320a0506011e06081504060306021b06010b0d1a0d1a091204030b190e1506 58
    0xc2c0900c0c520104c5002d4080e071a00115550761600c010503040c03000300d107521007068480740302070125620642003a401d54100b484480c01c0303c1400a1a8001c0c144000540803001d0704da182c600d40c0d645500503560b00c080d4056008491460003850b400314030a200307590b40382e1988925a25402e0449802c1029140403407201e4402206401d03011501805143d00381c075040c00000c04c2e14032000c00b104448124402e00e03108020304420041d160490301159030384100c0500c018010306010305801030540502c040b014007200c41c81c4007201c400c070344109800e0050b910000f481c03400901c5c0c200e40812400038400c101b502d071240340c100004d420502d50410461010487c071400402e0010348507041c0c81f13080030064200050482c50002070040e90300c1c800781126461354840ba09880340c1c000d050403070344555003039070007500c00d00ca1500fa886801040c1030801e80c043c0003d0b0315000700340411241031382e8102c2c640c0b102036559000b00c0041503088440d401e0689107007130801c003010f0323038007150708011803501c3e5070a0405501d41a00f0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 860722760 1250 860721510 860721523
    0x29041211030a0f080a0e0d18080d0f05030a090b04080a08160801050d0f1205070506090d08040b04020d240b01090311190306060f06030b1008150117180f 67
    0x1800440c400c00c3e0960196409207408540c0301e244943c012036189886000c181c1031103c10f01da101c0104109118030000c50384e01510b40700161000600908034110548002802041e984020340240800000032542c0135040f5007000d014a078124984c00c5080c1071914014001b07520140d01d400010304410081115018048070b4050001615980d0080590901040043c003009810084840a06440c1d5000005048080001100e2015240d06807601c8150424074140b8200170507100751900042d05013410590801100c6400a8201d40c2c109040d5413284003050f84052001c00250000b4443c03071a40c04148501000000f061582490034003403d0180d00041da0a441e950100802c4035581500801301810b241c0e202020320190320118040031580c9494100407602c654001d000304c0501c0600c00d1101c0c0d43c060251100e00c272001d1351038165007e845000144504009010030418244184896415a100350480101d01c441c500c0611244d00700410200d001c410851440d400500482c110b4500042000c00d02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 860724010 1250 860722760 860722777
    0x409021f1707031802060d060f08030406020c0d0503030a0203330a050a06020c130216030302040e071416060617030306040c0926071205060f0604050c04032904121103 73
    0x3c801207040e05501b0484960410314090201c40e0359420b000a0b080b0b1b40c1e0300564005c00103e0080e5903150304048000307007000c1d1190f00c801d00a0701d81403002d9002840000403a680a02d114030016108c0e219081482c0c21346440c89505601400000300b60740e1107600451114400d81400c60300c131040c00396180300340801c040e1b45102e0310b0003603001005030b8078030790800341c0000d500f441c3c26581c01490015445058020580d0204094000070340c041020b001900101e1030480c0c00103054149040d0707988003030a00900340e1284a004002c464604482d907010440580c2080d4054a0700744280c04071030300300b118595503a8000300c0d00d4600c61801c00001041d81c900507035240741900e43c45030300a088a075445101d014506807031021108580314080d00021012200d00c9072004607841000901011f0a04c4880b02900700300203494140304c0ca1404050000802c0c44508890840ea800111840d016103d0034003251808031021441e0515203481c0c0820042000988004a80b240b058440c503100350200440103030349001e031008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 860725260 1250 860724010 860724041
    0x10f0b10051812070303020706020f0102090f040213030204052806240905090103030305071701050a061b2001080912040909050309030706020c040b0312090409021f170703 75
    0x9501110b645070400d112032900c0901140c440c0c48a85000c1c0d0700d44220740d031080e00141c001d40030038404a0b90502001c220f6031583d01c000e50900d85070030001b40c511900301d04801e04c0f80c1d5001902840c4170f0b81f0461020000c6400400c20040c503d003a4000d07011100c00b00c64481500f4000505030309111000744500380680d01c0100206001c450088511043c040c4000b0b111028443c10754800540c40e07560010150107180710b513801050320304216070003429005c2c601c10741842e05c078005401402140c071030100b0b110454505242400c00c10126600b07031500b40f92644c002030800c051400710a801d04810601900c4140c2d801e1b40c4580041e80d50741c3d08180ca40141290300000410104404c100181c5240c000401c3c080c010010740f494400002c000902d07041c801d9003c140560130070382c1c40c24141d141c144103200b41070000b600504030480c407003104805640302c2c40440d240b24660380c049240c2591114010282c1350342488a050003650300c0041d0140180346030b100e0030311103034034641c1c00120818424010071900700300702d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 860726510 1250 860725260 860725267
    0x3060a0e010b070209100e041118061f0909060b04050a0614030606070201050c0312100807030c0b0c031c0905070918030f11011a0306010b03010e1b0f0c010f0b1005 72
    0xa007084450500601110500e500c0c186c804a8402001c5561318000d510500c032019104100100340581c6401d0f107071b001180b488074502001003030740f2900403c09074030003411403413851803230000000e03150030090340c00060320103103005004900d40449000070070039078001701d03507604440e50b0740c000c102c0f00d03a0300305042422455028404500d00d4100900600b1406105041140c14145e407140c445107980c00006a0280403800007003072202400000010070702814810018001303550440d1500c2c0240000740c0704620703500c0000a070900c103200b03003030081c1d805001400c013030b080707210100b420080b015100e820400d9400d030190034000121340303040788500602c1082086900b400400180c41c15190818400c0000e000e202010303401c10b007240c0c1c0c01c2c030070030f028600142681c0c00e10207440c3c0207152525805030044d10151070108018400702c20f0ba40241548913854102200700c404060501c411039000b00c84950000700742c0400c18501c03800381900104242c0742c8142041164180074000c00c0070310107058a60101095080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 860727760 1250 860726510 860726513
    0x14070605120108121803240f060307060c11030a080307050c0c043c0e0106170d0e12030708120a2f0d020c0a060203070f0810211703060a0e010b07 64
    0x85200d1030481000505407050000382000402441d91066603540703070021494100440340230550041a0441c0313054004200d00c80c2401800741c440c1d542c5030805010b50040200700303071080d81d0812030701600070b50209034184c6a04090001030056004600f8074003040c0103c1c4200c50040c20603109981d030007440340c24600400e03280e000da42250310380392801c0d14052030500d0724a800740604038000c031160900303160000242076241003030b030300180b043c0c01543c03030016000000040c00380d950001c07200b003050104460a101c0c541400f40c1c0703c0d01d18031071000000c205500104503110701c07084001c1158402c3d04501814441a83c0b1244142218845e05441d2030401101000c090089036400000d802021420000107140030b58240000d450190109000c07142e00d078000080184142d48281d004501040c0c90412100b541002c0783e41001e60240380c041c0a448074410f09110506806a00c0314517030341074100f1000038114612940700c040980c8216038486c01040c541d0f04c0010100b0001080d18100c0c0c040180c1c490411005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 860729010 1250 860727760 860727787
    0x90f020d0b040309080c03060a0903050c0a0809040609141b070515070801080a12030510030614011d10050103022503020a0b070f020c300a0213110306010305041407060512010812 78
    0x5180c0e02f41c082040034040b212044104004800c103a5001e000916240c412200c2080162000354000640d140e04115400f40300d071480340b02c4503401001d420310410005542000c41d16460003104405042c81c42090143d00b4040c50004099000310340c0381d80e490303005a88400c0110360f00c01945800401d44505600c49404051082c0d201c4e03600002e5608100e1003070f59aa171540016201c0c98600790801b4a8104010400440c01c2244c40b04001201507020101b4901580c07680020f50162184a06050b0001030740303040002460300c0410a0401e0032440584500759040c000e640d0241c9200880d125122280425141750140251071060041c80e4000e006d0000d06509001004100c1c42e141000c0780080310721800b003c45255408031070104804018451a2440c2c010810403284080d079000103140f4041e80941c49030f045500701ca900550a0801150688451401d52200c1459111110560103003030340102d1410f0344440104900c0301c208003843d0580e44c90b00d11842d2549200f109035003c0c80f004101c42c05030140c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 860730260 1250 860729010 860729021
    0x3020909040f0c0b0a270602190c0b0c03031b0c071a0d06031506050d080f07020a0314071a2521030f140402030c04090f020d0b040309080c03060a 64
    0x30400124244a13a1140c000301e05402c01c54081c400300d1602d103c2100d040c0d0b410002c0e86002c0c07808045212101d8502000603407544920106906c504480c0483c0d403040c0824505400b005080c0c010031146c2e60750140c00e650b6120340040e62403090400c245a40f03034100b4030100301502c80020811014240d1546890512410b10300e80c50259100720009103c2460503410700d1189030300441c0150701840e440e1064015400864107da008140710340030490300d80c0042009001610f90400841c40010350350b0040703000061403c10f155000501110000300c07007506050012500c4402c4514110700403e800000d41c0b26401c2d28002c0c4541d140c29448031860813501c0c5007010242490090080c00c000e80701340300002e4103990b081032031105800440d482c0c902c060f044601d507205504101c0b00402500d1060700303080e030005e9290905500b0491042e03880d10b5040080c0800c2c0d08412810320340c01001001388031780c0761410941c0d03d54110343c2a404030f0780d49207001444038804500700316500300080180c41c1c241d503041c0303d0200414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 860731510 1250 860730260 860730263
    0x70201031b1d0f060c0303071b0c1424180111100b06070605090106031403130e0c0d14040b0f090601032004050403110106170703020409050a0f08120703020909040f 72
    0x901d9580c031083c4076254000208240c00d42070003d10780c0d919040034080c001401400203075104c20004510400440c458540200075544024465850854290001240c800045000591100101020b036803180c42110052003a824500d08212001d800000152400400c421810600d500641d4810349041e445601c810080e07000244154100b422030349520046078821101200c060b03558410038418080344060020303403102d0300002586800d415844000d20400782d84501a0ba0580e09000303d6059225501a511404c4415100704502000740c28a036203240415101918000c5005011134a083c0442000d54891141e410040a00381d2842d07541c80c42c900c0c15102c250000c00c2681111600341d998a024a82c0524069074511024004910003182103c44a5010b9032419448049080040c0000305408007102d4040f02d0002d6000d003681030041c1420b40d5034000901d40d031603c038584030030400380c60090b000304907102c030030440310750740e0a4400d50891041414179a4018015000900001c6200c0301020b1581e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 860732760 1250 860731510 860731519
    0x30902132c0a020108010b0304021e0a0504090819050a0914040204210b070201021921020406081e040804030b1b0d02091801050d080d0b03070902070201031b1d 70
    0x68440c4912a5020401d050104001d508003489910a640e40b0000e00d5014000101c10030f071543c00c20341d0000d158001d001002c03440c5007051801070012582c2d0650014010000030780140403210032485c0c503032120351090302d58058203d0040704450700c8500c10001e1300c00c8106a070f112040074900705603804a809510003003c584c065000c00c070100f001a40382d08244c0742c1c140300480e035000110746441c001000d03e0005082408582c03060060521411240001042c00096410003185140203540c82c0300b0284440b0079550902400006c1c001641035100b81c1d83d0f4401c00c2c00d48a51010890320034090110044190780107490700400340024804a542200d1058001c14031a00d40403140800804c42c201c1c0e41c02c80e4910400560b070200302c039040c50a0080c219401a1011118030a1943c10900020511801c0c00e802601b110340120301040030306e125a001c40d401190050840706425603c01c482000ba500c0000101c3c0000c1c24045402e1103114064603848100646031150030400f0251001118440d66000c10264031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 860734010 1250 860732760 860732801
    0x3060c2b05010e0a090b060f030a050d170723180405040c0617190c1b052119030f0609062d0b0a2f100b0103090213 51
    0x358403a004800c51440e00032500410298940141888601402401c02c1d0020f0f0406070310900244410341420342c01181180c001c00760303010400200b4502800100014118442c1c00b0305511620780140300030030b403401d03035803007003103440e503c0b02c0c81243d540d40c400d00c80b50420550581e80c9030302c040f640d40291020362102514900c0c03000e410000101034501c207480940f1004242001070203059440507403801d0078141c0100116150400303074040c0f6000d03900c101c06094070ba540d070b05026a50324410070521106540112a021000f125802d00c140c9404c003010107880070300c46800c001e001130f0031040b003582ca405901010f009000d114400003500905004510f0415107542d230340d004030b00c0030341d04d00c1540094814801505440300c200211204031421960102c0f1404c141d501c800c120808062044400203c1d0350b10b8180c2404c10040282c2d0850460f020f0848010b0705120b59006a4003c0090311800d00c1c41441d00c1400045489001501214100e81700039400c140201e0350780c0301c00411500100140103000003100305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 860735260 1250 860734010 860734057
    0x6030606030a0c0e130b07090503160617060105130602010f18030e010c05070911030103060c11100b040605060403060203070201060510050a051e03041a070f0801031101031b0203121503060c 83
    0x5c6e00c050840e00310313012070843c0c101400703941404c00503040d24948458440321060705040020308040c00000c1060540382101000600503442102a1004910300c50070311500583c0700c15001e4040d010f490720039690b45140a40d007401c012800742c0203400c00e507050344803440c0400301d00c0011200c110b8982d2090720544160764000400c00348034811041d2011000103801d80729411403801d42e083c0d915543c942c0f020015242c0842c0208040410141c4402c003044100050401c00f14001c10b000d070a03190b10030f560062000c200081802180d030004c0d449861140d0003040025190742c20482e499000e0405a00091801c4c040f066000340500002e0001c8520292f444c4111210002d40004a5004803421a041d00a00c03075410703c3c50501171305507500f0400900f00008030b03000f0182c00401054051001815010341d01d4603500e201c2c2d0290340240503502d900612555440502c0002035901d5000d0004240340c07200080014401610005400000080050281480340c031081c100100030b404ca064210700300344d48154082d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 860736510 1250 860735260 860735273
    0x31a0a030f05010b100c030917072105030d09020f0301110307030b0102010f0507051c1e02160b010603050603190209161107120c1401020a03030203070302040504060e06030606030a0c0e13 82
    0xb403c2d22603071890841c500354900200b10601950003500b640341e40c627441c1e5101c0c04000c55180d060300c079040d040f01d006a140081144140381170740000782483c000014101584d28594011f61082c5000399071315142907021006041c03c031801c3c2480800d80030024004100701e18031940052540780014070011603044514103603541280c400fa5407070800304900056a01d09003d04401c00244041d1205040120b030400c6a00318406000410102c9030342e0b0390020344600841858084074412540051222100d5a101c240103801018241c980340e11074172407500c1001c909000445046180b40c1e014008650589542201070507503030701710446906000500f516a5890002081036500504001350f81000804650610040c0c08000350808030010004c0503403070301181d800113500b1416641c1494016501d5640203000c800900980d08002d50060a2803400126000b0518034140034900c114241d5000741c88040805680e5080450b005001d000340c00402c2100c1c0c041051a154004680400c24040b03003a69501c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 860737760 1250 860736510 860736529
    0x918070b0301140a03050a0b0c040815060a090b0a0b0702030f0f0c0420070222020a0e0a0902121902070f0f0606141509062503031a0a030f05010b 64
    0x1851031011004201e0484600203241c60000306a40726804d0b242183c48183c1c4034285800085c0c40b01010038080b41d800100382d03046070028000d84068515400d005110800c90700c0d000c0c1c0d042446a410030a000c14544041e10485403072500081080c480a032030a011402d07960420301e010b0307905000d02880005d5180c4184010584d40c0300003006000700940c070000704001c690905250a110908100c803210162a00800f100c170480d404440e40c02c000525102d8981c503140842401c100c040380041100d40301190044003c1d06084402c65407102101e4440c140748089004181700400021864004107032515400646690002146000949003040985503c40e0b9002155000c58100e21040021400d2000d241301c1c2d00301410240d0329144420351150001105010007480c42d0a62041c0060501031030341d121000c40c0e105900135504a0030310700e003201e1111035507402080b003500441c2c2820525162401c13401822083d003600108440040da00750b0b20340d0b840c109200c04d4201c1e140d650321020240707199511600e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 860739010 1250 860737760 860737769
    0x1022a030c060f01030615141309170d0e0309090c0a0c0203010c050405040b0109081015080a0302151803040311040f14010f06050909011403030f041d070c020f091807 73
    0x21000b0b113501d1072822004a500080340302c510105449000e0004403000302190b0468002154082c0c0002500300880c802880c5000c4028681866141e194420310103460291140040e104803c028164050b001907480e88910302c0843e03131191540b400601165500006005c0d0500c42d450000c1c2c09408560104c0d08444944074010040398001c1420846450940907001c503180c42840e04403482417628181c1691080504400c50b4140c1c4c82d112402d01c005460ba0321103009019800481c0c20511301400c1c0030b500c4128103010201d03800d50380000a01c41d21a140042a0005d0308074000358a401d1550302d441003242e01c18051030758015101c800426140146009c1c0c008070540400401c10360b549405010703051082503901240500005000da0081990f400105074111002c0303001c4117421100e07100c000703411071103201c00400303c44001040103c1c00001d442000c40c028001d01c51524203a0303d44078002e8401105070031009610030002048501d031403c00c0010150007840744030b007803030003119007440090810308542c03c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 860740260 1250 860739010 860739031
    0x10020c100c050f06010f03060c18090e0102070b0a0504140a0c09110415020d11120f0306030f0319030501061b1202031903050603060109110a050705191a01060201022a030c06 76
    0x2018814403955104821149d145418461a460400c00c280d4522602c00c0c441c0000e15955082c425540e51001c0d0102c444072a0b022503000780c2c03403a1074401140100402d550560f03010b1402c00320b60a02000008041d0952a08004100100381c41c242800c0060228052262000b030024403001400442d0f1070006030707413629203801400d01c040691400a00020702413003401150f6001c80240300b030200c0d1010445003440f6620190300d80d243d680401103485c00c1d01c241800d000c24440064100400c018070848410a0340c3c40359420711050f40d03181030480c0ea040e405a200c0310068408403003400000c4544800c4051000c490041d02e08102d4607030354118022048400c0580801c8d260410480c49103428000ea601400c400308080100300000503540803079000e01c40480c01407060004949060040402100e8160f1300d01c50300f0001e41c964a45444280d02e504211207800403143c0e0381c000305c3c940d8018020b039150041420000c0b00449004d81800c40e09181145040707000d03000c200510b2840080c00d01c01a88582d00810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 860741510 1250 860740260 860740289
    0x120503070219060507080702150f07111e04021608030a061a0f090607050a0c090e0f010b03031e0702040501080102090307150e0d110a031110020c100c050f0601 70
    0x502c0701e6202c0301c10400300c00c02c506803014000039130048241ca448540140c0c0f255201d90380b520200d84800021070a2401c406008103a044001404000600c0c0191041600240d0030b100401030005881003c41021500004824190814206540a04280b80c2a21690340001141d51a07807001e5074030650b05800890b4540c0003d01800343c007800070855103031281a001d8685046c6540c0302c1040d018150442c4d1107200000360100c00e01a04016819103e81c0101c00e800c4115a10801100140318035140305403903001c2c0c81d800007283c103030600c15080b8100010b00030310300e080752083c00c0720347c01450b43d00c911072405400d010314005601c0c2c500c106406042c0ba88001a680d108440400d46000c0131980200300160310501c2441406034003140014038900300791100d0740281020302d0141c2450300d4443c5201c1c7c0050b19038800005000381091180318038141a6204000b005d20504220303124035039040c2c1e581e0040303410480941903911030620031000d01d000710199205445a80052820507100707074401550801444c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 860742760 1250 860741510 860741513
    0x80a020910030f060e061302130b19030e0303130b060d0f1a010f03080a03020307200a17180904020d1a0933060301020d0c0903060509010e0a0809060412050307 70
    0x51003000c0180101c030110740700c0c0d40786c010001244045080040d494a0f0740204205504841d450b44143c00b81018144c04c6446010181401c2c0403660500d1702d100001c1e05084030081a414040122070061410104103d1541c000d07440e251001b440c09400f050f000f11402004601048001d2010b084207442a080003404900c002c00c40b0240f044103800c035a8841c540c00c24200700144a510882d01c0c902064100941c0f60f684500c0245d440307004a0004000cd06526512292148008144070480a21a5129204101005044e030103103004d580c004011049011151400702d262143c02d003680b007440141503d0b40c80c0f407540c0d140c0322616622a0440418400301d01030003120581440680c102004000d01c041c080d440004507000d4110718400c0380c04040a800010071000c2e00c007901110000300d0126014800e01d06401c070024022000c0f8403098a09914102c0811900001030090802e200200c0000306a0381a6940300c00e05113030701c402d0b01c06034007250410002030001e111286410f11280600013071034988a49 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 860744010 1250 860742760 860742791
    0x427031e020f030a030f0603021221180f1306080607090e06061204150203090705010e0d05150709120602271011030705060108061803090a06080a02091003 68
    0x9046403400d42d00050401d140030340b030000940c1c41d404114500440d222491140420051140c0e030006504a400301041e180c1400c0d00190038010407000d0440e01c2503002c0b1602c4c003104079000f1450081304d01c0b403440200500a14104441400c800703001040441d00c08847c0d1990b00c101e40081d4404482c54116608000301180c1008100d4000d0000700030400c42c51a02400081092083c4d2004190081e01c200118080c8085105009280d0b51120421981d83c18643c18142e5503001d188031b00e60025040c807101c21003e0500f030074541e0300f4a5000c4d00800581d58600103106401c0c03802090300040268030040051490560090540050f0058400503500d8424981860000721a0908401001c04080c10280740c2e0322001480307100c15401c4d24020104584c8c2c0413045065204048028155120b040000300300c00030045032540c002c00c441c00e800d806526032542e945499024415a281d07010901d08010410b050042c151207501c640034800041c41c1c40c1c1c0020008018107003d43d00c43d000a035a45904205d503912 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 860745260 1250 860744010 860744057
    0x1608070f090b01050706020d022205120705060304170f12041e0c090513050f15160f12140708040c1707090b0d021f030c08070e042703 59
    0x10780301007840350002c1000060036521803180018205640002c0c80410b00095605441180441c821030080c58040e00102c0200c49500d40102c0e4802d07061214180700d99003001906004541010b00700381d003181c0e9141c5a180c40c00214a0074030028000030040001c60011400051604c0e4900342e400034041c4c10103003072065041201407500317142607241c203c1d4280411024080c00c1c088410011002c01c50380ea40c0c000c02c102c2e400b400c0d000100140304015000c072241401080150365121042490341083d07888000b014442d0f20041c4000d4049001030501c0b110080c4109010b5160039441c0e0000300e2010034108040f1070094040f20074800091442060000300070303c5011450042c07402d0554500b41007a010700c1d40b40c42c0c50307aa1042c0c80c3e409591b444805c059449411031492015001032550040000c01c14204008103142346984000920b81584004c1c164043c4240300d0040c4025521002c0e0358411509110060107441169464100c00c0b140d00c44014403920b4080d509944607035180c1e4040307103607840039401201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 860746510 1250 860745260 860745269
    0x5010f0c0f021905010605190e06010c08181809030c011a0a050609190305210325091809031403070c1b091b08061012020c1608070f 58
    0x12000240e0950350020b0101e00c4043c5502005200c11100d26140e801840b660b484603030440c0080f03140d10b00100350a000c510032141c031100d080c07050707640c0c80b001191203c81d0600010101d03c41032160310400c40c0482c07070355413100c0b10142c902c1d03d5184411600c440004400c03140c500c055800010359000c804420300500700546215580322a0030b60b03440300003451b6004240039503030007082c0102d0780384020f642e02414030260b0307000c188540408680341e00b4040d807034a940d40c52030405201c5640140e0b400707080220449100300424044448039008001100c0880640341ca03408041050098010800505102d8882614206900d000400c0921440e026003410301181807800c900009004000c1070f260495034001d50580d01c0400500740b05001c50414201950540108140b40d24103481a41103001c100c3c035202910300140c43d44241a501c0004000152070440c1c5c61000003070b074202d2100c0b030a05143c3c0290a1945c180000d5400c0c41038601205005010315501001150744440802c00c21121002400ca001c2c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 860747760 1250 860746510 860746517
    0xa0e01020c060a030f0b040c020d1b0807060c0210061e06180b0714060c0d110304020d02011218050a0314180f0a080303070c11060a0813020114030405010f0c 69
    0x101070701000038850300806003ca030603d52502c01c44412880d456000104109005104118003008540001e584000f4818103c012a01620101c802894081040c2c0350740c40e48002494600003241d43c0c2c441c0038104040108007948900b89403901d01d26090f0103600c2c00717804601c1d001c55000c0e458110380c1d0200416903001d0303401c1c490b218403104500d0381c1c4290030005507882103481c5507643c02107113000c404444010052403018011502440400c1448100906c200985140c0902c81c22403607007098010f030b00c03042c0e400a5000d980503e0190040d4010742c12618a17074600304000401e42d06031481200f15510b01201200c0540200110008040c0c000b401c0100d402c1041007200e091883c498007100c010410000c00900c240c010741c288442e2a5200c0e44800f01520000c400d8a440b410145c00c01340060803201c100329028108030b201c1d903882e800c020f0b05481c041d40455a41d0146074540c1c542d440039140402005a0410112410b07492009402900444c00341c1d204000006061159844030812a0740780c0364680e040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 860749010 1250 860747760 860747773
    0x1505040b0c071a040f02060301090b040507090e1b04080703030302030f150901170102070c0b0310050415060e0f0a1d07020610150e03061608010b04050901030f0c0b030406020a0e0102 80
    0x1003090380c240042c102d0310202e0945242e485504003170030342c1e0031a410004d50215001002003850742058024a40c6004103840174496600d0f0791000340c402d68414080d09290300c0b2601c6c0020100413105401042c044141e48685182980f10407000d070030320320180c0040d00403980000900200b405041e85031a0f11402010780803584214401c00182e1190040c03084000e02c904040500d0188030080d8101c590141d4414040300d03072a50b56003660b4050341c00c1269910103c600c1c00030000f4090134580540c400800a0700c44180c8a0b030305000080d42c402c8814400d998100801c181c0b10300300b5031600d8281d42e0107440f140030510900300ea090489101008028450b004641111040c0001c880d40442424265010516201d400c581064001c44003101c10448a65061140600b40309024042400781074060300030b640d481400f82c2c0c844584000ba441140700346900310952400400c003003445400440b0a2a2150301ea030541182e4801090095030400e40301075640d5940001c07811800c80d00100d00c20310081007070024284 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 860750260 1250 860749010 860749013
    0xb2407110402040e01060f03020f0712021905030f070f15050f1302010207030303020a110607050d1d2e110301090b040920150f0a02010b06190302070f1505040b0c07 72
    0x907070344d9040c40386070b0500c10001000004580250103a54107114400005504e5aa050518202d100302100400c0098059140b69a540c090b000307509840d83d64114005521b0550b2032520054160700118081d00c26207801c526802c001041c080c0d10704c4100902001c080380d10304000c0c01d0324141c0075001c0c2c840801d904100402c800142d801049100c1100d816040060321402c00c410203907401032111120039042d02601c420000e40f59040b4024001a400782c683c01c0240407800c26000d021215910901d40095201103055490a50700405002d81e030032050304550345401d44421b8050a88807941c400701ca5107080400140021040782c0300350314600504540c04d001c420748039210001042c9520b4040c9811800c1caa0b61500f07180c0795045a40580c0600c1d10700d841c0d80e00a9011406c0b40c4c1d801005031a0010350814a002c42c241c42c21500390703034007500800021040700e91013200580084d406000e081310011400035241000c41c00401510000e5410140045801d107001d1a0000c0388190007400e120003020b080c4150030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 860751510 1250 860750260 860750279
    0x90803030f0f2d0c0405040219030c031505091f0e0402100507020d060f0b0a030605180d0818011b1707090f1406040305010c020a05120f030403030b240711040204 71
    0x560f66040002c0107031094a40c0e001182c0c9170322813a00096080790002800ca10600840ca01000030135245941c100401600c4103c1101503508400740b9050307119112906102c68500b070b010540c0c01c5040e01908607610a4510a4180c2c0306040382d02020600c20f900c0c0400c0254100b59000310761642c201c1c0340c004c1c907002140d030001d104004a0080a000e69994402400b0051f10541c420038480341c1c02000140c2d0940d0320b1074018041c0804840002039041c0e800321000362100001007400300391a00b0703142c0300320b69542c8074490b4070804440c103d800401c0d03480b18006c0c25083c408401c08041c0813520380d02d0700340300c180d0060b091200c114040c00d01c004005c1e24680410000c0c000361584e00c2501c1d142c3c81402c61003150b820001d8014001c43d00040d010354a820b81e0403180c02c3c0c0001e40201d9103880b840603a02d2601c003000402c0280d000709800a60004410400100080e2084e841303106c000000824008180d0040f4040c0c624000b6503400030112582c0c0007400f07000388074624500c0c1040341004c403019464181040d1105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860752760 1250 860751510 860751571
    0x1203220e09120d0e0f06090a060b0402071205130906030b01030318051005091503010f03050d0e01020a0b09190506100e091903021e060a0501120c060807090803030f0f 73
    0x3207083c6035543e51200d4a510709200005d00d5121010132101d0908020302c2081c2c0760085103408490403485c1404801103070030b1034000e0700d5589411030151038184200c4141a616030340129480313075002200400c0810045407500c02e45002d503000c0c01317001e0010740c11450090206c0a074482000750f4100000d108021650345c0c015141d10640451403d81d80b0b07010410701290021440b50038013454244007000110315082d0000c4440222401001192480003420034255124031514070442e00581141c40c981000c5421180003030b410014241c1241e05c51100c000880c1c08254003110212410780140e41880140d11981d034a0f10054000000301600034207101c403540b075070380c101811038109400075801e00f4405d05000f40034140c0300c0c2c80b49540d182045001091010740311202101c40416443c50940042140e070550525460926440445a40f045081040c1078400d01c0008010b00d0402800100204003101c0500c055030050603001c21590150a18481402c40c00348004c01e882c0813881c0c01c4000031074030dd4240a01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 860754010 1250 860752760 860752777
    0x20d150c0e15160f1e15021215030708010204090c0212030f010306020313150e1c0507060504030212070807030206100303050d0911030d05030f060303070510020d0914160e060f1203220e0912 83
    0xf0f5814545100010ae818500d096210362103551000c00c00140e40901504004d10305082030782519002803d84a0960440c0400e032440b41c481d040c0480140001002a40250b03009140d82c0c8484810b559a42c1d26108045a11015181d0703040e159070842c281d8500810a10940c2420425204001c00e84100028954000c000010341920740380c2010606060080c01140d200f1011200410703030303454070340c10403c0080d401400210010b01c0340800150300118407070314250a0742e91690f5030314039202041100e00b000c1e088014040e01c0009898a2800b15650100151a190805502c403540c40c0c0c5450702c1c0c20403400300e0040055000780c0007000443d00007400423030702000314600e00e40c0043e2035140c411250801059003900c0145200b80645002c0c4110400081c4030647c00c42690b00f01c0540323500c0741003140600c082911603942004e015005000c0034548203001a1901c454070342180d0824600e40110107003c029102030320318036100841c00380b05440031070010540c0064001e000300f40550522400300c416100740c016 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 860755260 1250 860754010 860754031
    0xe011124060f04090f0b07081b18060414040e0604051905071d0906070f0f03020d090f12111204050d020d150c0e15160f1e150212 57
    0x154641e03181602441864800f51042195040318504186020080001600c000b84680c00103100e551050121501c100c1100f1a03002c0342499511050316140c04c0f00526061902c0e41d210b902c0c0796601c81e0300142c0001c15941000341c01c860011030910040740c801c010950300c00d402a10400010600008139020b016a010b034081100349a0360030701d03d05140580d04580c8009413032600c40714080c045009400d000d01801d0041d1038050300c0b030101c185c0344115200003483c0410004480c2c02c030854020b6000c1c000303000d044135010a440540f65181d042c07003004c80c070003191103400c000c1d810f80580360300048031142c09011600402d51121209040e44407070041e40301d05446000024030050864440d511054500e40e401148001d400034580701d0b400c00382031542004000500f505049007424a00380486242461620442c5850b050303012040a00d5468590b6041e1110f00707410124500042521a00612608203010401016801e51500c990f48011368188038411034018041e2200701d074001041c1c9500940002d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 860756510 1250 860755260 860755333
    0x7061e060509012d080304080a03080105030109030210023901150f0e0c090904030806010e010504121205071403040e060406051f1206090614040603050d0509030712030e0111 76
    0xd44181c144e1020703000041d0038000400d0008030414000360248101c0c1c80780d20b49964682c1c0b945c0a1508036000700c900540184c5c4981d0300074203461402e50040030b07803440100107120101d0310f0804550b006000324805000070700240a803185240c0081c8100801c2503024000d9401e01480c2c4441000030001c2c5d4000c10408110410100b40101c1c8010116041130001074200e400303c0c5003608020303060f4081110428045142809000200d611400845003600c5102801c29181130306501c42101c0002050180001e00c070080100c80c0c007142c3c0001700b002d1556104401550f50b5814082c5003494058007504103805a81010014401c60f80c4d03481600600c101104003c0da82c004080000b100d240802a8113102e86034907000700811414a20b41188003a200d60b1082001c041c80c84800303002c00c981141c4005010343d040581483c0d0340c14480c400074040602d008084600f41038035141002d500105a45044000c41d03034002c40c02045582000d01c0c01880e40c9154090046e1424211880444400c210100c0c5203451191 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 860757760 1250 860756510 860756579
    0x5030718020909070e09010f0b070b101a070614070c1203060f1503110c070e040305040b0d06051009050a12060e010f022502011e020307061e06050901 66
    0x56042e5540d500004080c4046401c0c101c1010f0038904c500d840305800f41034008004196106414201421140485022450103040c0d45a185a206001c0c09204000e4050100095010540540601100a09080d841d035491152a1040403a4001001901c1d42981001048003541c3c0121140c003c0343d4105841440c03100106104900900882e0442d041c4c2500031072010812404208103c6006003042e1410405206090442e60f840e010350244109036a10080c010b000085100440c0e80c1c00611078200356041c50f44500811106800c51909150031070f0303a5070401c01842ca0b02c0c0308041c2c40000c02d0b04100c002141084003085810000740a0104040381c80301c03a1030200071090340001510344d20300008014061540d80844003030342c0701400e54407803800008400c0c0d40c044645449030180ea94140c40320000c07442043c0e0040200580700035481d066000038455040421920b006294040010301012010383c51a58460800c482841d003126000d50340f10340c014010303c0959000041c5001c401c502502055404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 860759010 1250 860757760 860757809
    0x603030e060a120501032301020f071101140309030a091401080c03060105041e03290a1e0e061911030f060a0b130501080609090307150627050106050301050307 70
    0x1c40030740303500b40d0f2400313000100b808001c441c400103101e102003010304507090754800203007070f40540b501c4441905000c00c4417400280040d000c6000240041c1010700c01c001c1140e00c91146038000f00c40210481d0400102e800d00580c0c01707914a405000200a103140052002c0c0000340b0005005100d02030180e0004040742d02603001c0e40a560080c02c4441452614003103c2a0308050142e8500c0b080300c08000c10301002d282040b2400c5461543c003820001d03090350303607900103102000d041c20b204103c188d9155102603106450362405620030641480d4001c24080c1803a81d038005049442d0140002040e11f400c1c1c2100324441c00b0340480e0740040e400702850403243c48800c0003034858419a8084294400005440c0c005805070340b040700e0403160240c1740c40d81d150303407141c0074401107a000b1640f400c0d03642c204001a200103a5868001d8041c1849402c00041d403a071900700c40d524840c446803c0c8102000b8145d141c3c0d503404814041d8a0251400345400d9055500d0030020903500d0086003d0107284090311120f0301c910544 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 860760260 1250 860759010 860759027
    0x70e0103091b0b18030307150f1e02070c271505300304120201050d091e02041803021507021614010e010329030a08070605190603030e060a 61
    0x200d01d42e40720042035452101c889654011840d010141503e000340019614001c401c0c4e8607503a030001a100c5402030300d075880c00c0040a030968041600d5664041a080d038444c585620107200055940040c3d90f030110341041c15802810f41d1084c500c0c12034000941c0440c0003003040c140b850300101c1001084030003200504c0c204c480c0607500016006209440101814241104c0340e85e82c41d003006405c3c050a2412900c899220310550080391700c0d040d41c0d202c1e40300041d48501c0040ca200159240009005480ca5490120021b42070400300901c841c0c044d03d14096180c1845541503a0007002c0c0d100126001e1540c002e034540d40c9502040d601d03141000c0001e180382d4001d01068854000d00b14201c401140c403491003540001d42482e80c2c50011340350182e1101c4550007486004030000444000c038500d074222144000b40c0e00c0058042c83c0e0180071340c80045000900031001351112601c03c0c0c0380400daa2410480554070032810741840f00c0e0007414120208003080d004076441c1c2900a060324801d503554140503050b1245070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 860761510 1250 860760260 860760293
    0x50102030901150e04030504170c10030f1802030a1e12020706171009020f0408070f0501081f0905060a0819050f0102090114130807090203090d08070e010309 69
    0x1400002084107024040d84041940400340012004a030385a20030103c1030141158020082001000103200366414900307900d1400c28003a00f00d0707841b0360150000c28108903168102c503010036241c180100c400180350140325200310b50848e462500c0c200e250000703aa1542800d0024001d0b0b411004401c9444a2141c01a0350f4180c220900d1007603081c44200080d0703502403501c00c020005080000315014000c0101284c2c4c0100f0300254406081400c2c03491950080d4042c14458010110402000513285001d04c19200140640300080340d00340d2401001602800d802400a8004107104103c504a50a40c0b0b0307411040c5c41e4080c000244541d204404520000c0554000040c00d1190761049000320030072100c1001e15900c20010f49444180c0c5403a5a403d078051100c00c580414103d55031030581c0c00748000034066140d8041d41c1640f0003507039104500d0411415400c0004159000000c1280f01141003050030000155031800c299a0b180410006044070b2501e15031300d04060300d8500300d500340102c17000801c4905 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 860762760 1250 860761510 860761513
    0xe070e0c0301080d0c0b0a0507021c050c0706090608040f020f0405180d050a02070b090d0b0906010f050114030112060b1e01110a021503070306080109080d0e1204090902060705 77
    0x1400c01004111440e0400d100c0c0303039010321070f00d035644400c07611071540394074250b51042c5544e00e40d4480c1c08408000d000c00030441030071445980400401d40203040e110448105240d02c455071348032040496181408555003110092015005040109561041000780c0c800d400150610b80da00d924400904004000000d10b0f900900f80300c2400300c002c06248482c1e043ca0000e03800c9407803100c0a1441038800340160042c0340f0141c1c205102c104840d1000400130409490b0080c904240b03040c05644003007007420280c070508059840b080050221601c8040700402501c0c007400c00b103140000c620501c503080d00c01406a1203800ea80c0040d4803040141641010801010041c080d025034604540c240e038009544801d420300044201e0120384001e5404a10887d156402074180301c0e40c0100344801442c01d0f80302605040405a4601d400116884284110720320725206020203a82e8140000480c000d680d6110000c00b06508007000304e0403c403c00c00c04072822909158004900f5903e54000034003030b800b4400014156 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 860764010 1250 860762760 860762789
    0x301031a2509091406031e0c0303130e1e0601050903100f0b190b0703080603240130020f19030b0907150c030810031b060e0d0f02040e07 60
    0x1026000141d01d4107807000b824081000c04e00450390301c00013510507a003d50f096009450300c4002c0c0d80000e2800180f006ea21000c840e80c03c400c290102e450350380008081e1120429006003407050b00404040542c00010070240301d1680d0304403d0808402520240000c0c0c103024000038440d070903450501151009101c00c4c94108500c0d880e900700c01002e000c0024110b842a00f21511a0103e0f608601000080d245580c80b42810600306e0358080e1040b2802070869581441441c0036040c507080407012a00000340fa0100001040d403510104601d15200307041440407a02d2004582c1c00c5290b08400e40b100100d804032116410000d480c00481c4038920142c0b4024664648640b0102c24041c440001d00d0040b01d08034101c036a1a550b50002e80707401d1300005c4103140015105400800844c1c4240f5266420411003c0d01311160741d0383c0d55a540c0d002104000b80507800710f503200c0c03c000321a08035032020081c10059801041041c100d550f640c250f070036658170080c4555642d0211940c403443c10003030003002d400702820f032584 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 860765260 1250 860764010 860764081
    0x12220b07050c10020f0303060402071a01060f02060c120402010f09080f03070215090a181415041a28050d030c0c1a0702060c0a080f070302120301031a 66
    0x8071908070341d58050044040c0c83c0c50160040c070004600d4031082400000c0c5003107850741c0c801c00020303501c14402614418801407081d1103140d0300b01103980c02811603848201041400f07140c0070741070602c020000300f034443c0280184000c0044010405900c50b50919040035201142c02c016200c00f1078a030030560b0144107840a64900090010007000464000c54142e840b011003041106d0171031203a0006140c0112034500104003d007400913070f8000c5d4903072111020485441050818802850071100c404e0021103030b02031f0340c0003820b20344a0700c1004040c4440000c031140d0141d0108004191082c2d22180d1100800700011070a00c5405070180a008014803003a6034801c0d0f0b00380105911300d44401900c06068081c40018076184003105085e010341180011402d00c01142c00304001d0b5081040412114000c250a103000145548010320403011280903554548a8a00300240fa1010792148142c05a804000510102d5203100d2502c1c48581c00a103c00107641d50141c2c5070070088008004c0c8446807401c001c2840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 860766510 1250 860765260 860765263
    0x702060904021c0c09050111070b04170c03060f190504030219030314090705090f070827010c08090c0303180f0a15051827090a020a230312220b0705 65
    0x1406c40e0000d80e122800c0401c100031035600e4401a2140108102040000304052000c02c40c05070324410b2024113503100740c1010341c0480d0818404445070310b42c0c00d08820400400381100c04445940c03920704501002180f4060b0b50207540d80b8503a0180c09242020344141004042c400d030000d13094503042e890b19410504100342031580d1000c103406001d1003054048005200c80600807541e42c840c1c0950755032204941c0ba001c0040b589542078200d070422102c1c0c0c1943c00c0340c00c1c03c0d090003000c002600f01e5a4200584c0b40c5221407030300b4008501c015600c01d41007000800c0c3d0084c2001103120303029a0444050195084800c0000d1f041030f440c1d4131400b40550488030300e01246410001800c0354610460f072441ca203030911001c010003040e600d40c1044804041c22500309840c411800100e174002000021500f00f04400d0300080d0030041d8561012080c402c00810304117815204401d040d0700d805041d002020070f0825200408200d0007518404120103000e000c040680c20001c0900e0001007011140c0c8964404140c00d186 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 860767760 1250 860766510 860766527
    0x13020406320906040b030f06011107030b041e1202060f01120305070b09030d06080a05010b030307081b1c032f0a050313021005070501050c0702060904021c0c 69
    0x31000c25514801c1038010200008072089507940208903840c0c0120700400001940c0041c461203401000611002c00c040d850a0011806044000010303041417600c54001440e480c00012020001c1c1c006a00c10000521404141c98000345c0c02a4501d00b0380861b50481203024a20344030203400740c0803150151184a40105426028140510701c42500381c1c0c8a0194418213029444003c00081003001b101000c00c614030403140e0440b10b0b80007607034500782003440c0a10503103003030303404c03040c41608982030003010040240710b90a042001903020b5820409181c480b07440070b00465290010b00140380c910305501982c1401003242c00d00803c20b071006401c1030404000d0050040740142d00c003540c4101c0000d5001d9180c00722641d440805107070840d1070601e0b40c01003101c1580001c0e001c42c042a8010347c02c000140d80b25a0f009500443d00e545e181c3d141d503481e003082800e4640243c140b80004204024240c0582c07038000854800701420f0b034015a440410b04001a110070036891000b228070306c0d0000e00d00083c0c0c0d104000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 860769010 1250 860767760 860767769
    0x2e091208090a0305030c0a1101111c1103070f02030c070e0f06030a0b13140a0303150e090a0609050307020405040c090b010212041a07150c14070201141305130204 71
    0x1044401d03500d05a07025516540c114000c1c02240c01440042c4032080b0303041c01030110006524143d1603402040b0300d203a003554140002c5070611013022407120580310f000c803080c082c0d20344003c03c148011081c61500f40000d10000e04000100320100700c0c00c01c01c0d10300810031512003c0b082000c889016030b550340000c200c00c409648400341051142e020035624a00042c5005840c1e8114100d03414a440e0200310070f40d0012080070440d4480b002c0101480c00312000e00000d8084d0303000c0d80f00400c0134010b0924100d202c225503040003801606c03610a0100c204800901c0c28406a4000000240c210b918105589180100303080207620a0400040004026943c0b640c40c040b90806101409400c2d000001640c50304000e010000c10361109100410489102050101020304003001c240c1c90050340c0e80310054070242502046148617111802140c1c61980f01c86c6c580c294070b50f007410301d43c01d01949034002850a4103108d92506840404a444031364071018008070f100410008100e110061070360a07003100a500148075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 860770260 1250 860769010 860769017
    0x15020615010c02030606090a0609020705060702070501020a210e0607050106080d09050f090705070f060605030d050301060c0b070207090f0509010b04060810090809060a020c030708030c2e0912 84
    0x9880500d500a140c00800c0c0b03640100946065a14002400607c0200402c0e441e480c903150b5034006003c0c0300a02c01044003d00860181080d0301d090880646010700660240d411075004807848408a00300c04403402c0c3c10400001021801603960104607048031081841c10790220002a908013007020541c040d0086032401802e450300d4203404e100c00d545074902c0d441040e8210a020000c004185403546d4055840620703418243d0074510251241d040451614508803001aa5120203100c0b91908012113650b08940c1d00d402c0b899503040c071200400058000c10002c245191140100b82c3d40c1d4002e01000000d00303c0032404021039080d10f80300c00050141035030b40e07074895480c2c011491003d00b09800fa02040c0ca02007030017001c0026a1860000003068215410f0b91040b5040c44484016a03418008080303050440e8010555402c45004060401001da44607030242da10400c60b143c24802d0114040d42120300e9149036249503c0b505400a0089140c0b0a80ca01d030386160100110401c02e500c40860070b54846540c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 860771510 1250 860770260 860770291
    0x2210703050f06010f111501180b0a060509060310081f05180d11010b06030103060c020c0d030909090f02040207081e12010302041e0f0501090c0e1e0307150206 70
    0x200320b400d2840190f03079003800903000d0003500080d903001d402e1180849030140c040390003240d5019482d1811510070b8001884101c100d00c000c01100706a8040c000c1035140445540c1a045e140c03031005092489034813113090042101100007211441220012070042003d08151050380355088400e60780481c40b4880d0785c901502d414007090014003c50305034160541000010f2404415080d401e82d074001341c03a50340d0416592259481343c0c1c10f40b1004090b40c000c0d4416880824080d1032100c0117418524281c500341d015200d501c01080101b5804054102154941c0c1c100061105050520720031403e4040d034044e40080c0005115010803210600821200300d4441c212100901c2c03c84410f80980720f102c44245205c9001401440545056442280400303c4e25481800a41c1c40c4000c5d041a1002030801d1403040c0e43d200010004082c25000342c0b00810120310380a403a1466960014211164000a4054040301648080039584081000300003400e04e0811a00c182c51403140d00075a60304044481d0001c205005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 860772760 1250 860771510 860771521
    0x50102090a060c050601060315081b090601080601080412020709050c1201080d0815060d18060b01030e281a150406180905120c03123102040221070305 66
    0xf089018505a48900540b8079646800c0080b0003502c030040c294070b03140c400454006450101001101601c031228440106142800c4d403c208150900800030307818008200204505aa41300980a81c026072104c030740e035500c01c030680f0300f01d04d00120798214852040c42d100c01c0c40b80d918000350241540244425103e101c1d40e0b20b4440107505e0380c000040f0880442c0d980000b1a6682448031200480c07100e024052a040c4100032112030143d401c1c41142825041d0150219428005140118030700d0030360a00b81480001c4c1c0035100540d880000c3e0a045011010244c103443c00d400fa160314008015801150940d05140050b240c0549010143c51084888000c441a14040d0829004080460f14240e1b01d000010000b22124000350500d408200ca85019074008c002070f8219102c0908204880d401c0215114801c002c4540e03600c813400b800b40028441d07503011010000e0038076480d4441140c0c040ca0080300c070704014408100039020f03c051100360900d000b0300c0703100039001c2005040e05c5030005940900050b1201d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 860774010 1250 860772760 860772767
    0xf1e0509040f09020d0f3002010b0a0f0506030c0d020f0a09050f011b0212010c020c090a020f090d150203010b0c011d06060d0f0611090a301e050102090a06 68
    0x3c40c3c02034100310800100c6000c90640340d400390481c1d0045900180003000b11010a1050081740041703420f0080c0c034052112607035424440c8190740d541c02c0e03400e80200e40c1031002400421102e0305c40c440c429400000011140391068040d216503180e40081503481d41d201c51201c804580025042c00c00090b00c007980000c07039103003c0c3c80000c02a40c068554140d004800910f11607030010000c010303a0402c0d00707000c9220303c1100910604014a1440d400f83c00740c000350340200714000364043d180c0d07085d0900512544060300e101c00d0450f506c14004481c82c50440003a0b1804034136030303910f80280500d090720210000414006ca0001090602e203188002c00142d80c2c440e400760300c000800c1c000940694019800038200d41000145040914028440020600680d60711002910b041e8406280d02120109921405040038031420000e040c00c0150045246820f07411a42c2081e40301c070901e64520b020303040c030700c0500007080c90100e54000b401c0c5202a4200320350404c2c2f800307940401d1840d8002d2155100000d0180e20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 860775260 1250 860774010 860774021
    0xf1d0607090609121406240d02031024030b010504050c03090a03081807080d1b0b1504020c010c0e19140907020c100c050706030203070507030f1e0509040f 68
    0xd0f403500d0820900f001505186004204000c45020110701d001d00c0c004803081100e1480340106e40600034000d90603070030301c0c100501c03068062405201904004401a90301083d80b61030201d44480000b0414001d03504044441d030301d1481000303048144100802403210030140380f0b05035030301507605110a40310a02d000645200032182403c6a402512016000070310600b08035400401d800544100e044c2c03200e6100703082c455660b00403040750b031010b000040703145e0700604030407180c13086041c9003032040c4110f4440d803d10510007803a007055000d1030150040250341b56415506000da064000300000c0183c075101801403218079414a00c0740000d203a01000401c020410f013000c2c1c600f01a00284100482c00901c4078a140150000c8154013529030117001640311200c0c851800c1d00b850b42e400824488a04026040c0216604140101401002044400f40d0003104450401e6894581504d012144220444d1122824845c00e0007440c0b20a4109140590200c09442c140f10308940411401418000c00303821038a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 860776510 1250 860775260 860775269
    0xc2503030c020105060901120210051e09031504051509100606020f06010801060b0a081e040b010e102711030c071a04020f12120307030e0f0708060610030f1d060709 72
    0x25810422320041c200240c0802c0102c0441c01d069003445007003a40702e40080214104c00c80000004502c043c42482e0401c4004100d0b10360f0002080b0078101501c40170345620500c41c4c01081c0304c1851001c05c0c5900001c0065a4451118010400003a03480d03482c000d441c1c80700d034500820b491107600000709030500c040c130a0718103c0344184445803500081c55030540d600712001b01130134882c0324076802444004807042d2507244a00e10401c40f282e880d6040c46804445880003030b0400c48140c02040b400d10030303864240000017003903000c14010030107103442030b107418054006917118890b01c59011060000001800001e04001403290781085042e8003070680003030740c81034101c0d40139610014201080c1d98030b040003010101e1940401c0c041e20003041d00c07007000c000d0035802a81c420000039a9088601c054500502c1040c410070070f200041e241181c03810a0099680c000038014500c5940002d1036141d00340d02903032090821081050013800100c50704801c00400c10f4001c5c0c1d0104403809040d001481440c410f60076101070b08c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 860777760 1250 860776510 860776529
    0xa0b300901231b09030a080a0f09030804030b0c1306030506030c1504060f1103040b030609061206040618020415050a21120507020d240e03030c2503030c020105060901 73
    0x140d0301d0040148448026600c60040042c0400501c141034078240015a0340601a6100c150303100f10800c80203100d4044d200727610301004400182400014142400c88003260f4210008010b651141c1a0b144414462941084a030030220500001c0880e0141c000341e00c114400c0b000d030303801d58542d2010b02045504812000603189401c10050010500450218018594034603003503411900d007008036031550703126404c04240d80b0004020081c0074a0a0191076902400a0b9241e000305010401c0e62079881034007400c0203085a4413290901500200c42d08903007212500100103001285821560740603201c00c500405024612135540410f00c818600031005058295030500245d914140e02c1d4008419a20f80d50001080340801060001d03170b031040301c01203095000702c2c0c4d071180d0034840031131202d480d031020041d0200d80d50034120a6058010080305895000700602c0146035078000e410294400a280004800c400c1002c5032080c42c10f15a03d030b88041d00040c5a07030001c111680b5420704004061200b486842d404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 860779010 1250 860777760 860777831
    0xb090606133005011407050408030a030506040e1005091203091203042105031e010807090527030d2d020c0f0d020a031d0a0b300901 58
    0x2496a40c5845802d850140c403108104041071840c0d080c4608548410360b07540c0c0d102c05174800c08050aa18154200116040040c6498541045280c90703000c1d0311141824190380e10000b44040d06c45400a4100c802e50342d05442c000078582c3c00001c01801c1c166036401c0c6074801d403900100780c5020001101d025071084030081030002105901c540b2141e000610843d454a00030307080c000c14840030419080031036040d40701d6070f40340d01d45100b98000500840012504e160070700300041041003008140340d802e81d409131074045401c0c3d0360902000c6415200c09000c034080780c00400980b031500c20110103001c507400260390a120060b24919403044070340202c0c0700180b0f6442188141242d00c00141d0040c00b03641c3e8018150303442c1c425801055400d1040d4002400301580011541c0010183d002800f940581890318142171840c0c4004042401c07604c1a004100d10302c90b000802100b484070100d45410100c0868003c11180811002040d4440f00141d038076112a60030500e01c914503181201d80c40d0083c00e032051035a03d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 860780260 1250 860779010 860779019
    0x6090e100f050d110301050103030f1106250e0607050d1202040f090906200a030e060c16030531050111060c09190b030411011404031709060d0b09060613 67
    0x1448111044104e07101681c0204d61580ea031000c0c001c5d54001c40c0030ba1100e66900299550141030342100c01401001c0c1e410840400c0b03042500a4080b01281111405161980480060a0b103816900c0f0345070075804030b03022400c1c6040040006004030103d007141e9420b5080c0210030046c2069019074041c0841d10180300c0c506000e0107034698000366031170f80105c0c00440d030201c82e2280400f0f00302048140840d14200041d15082d8039030907029020f10314180317000410385440c0000c00c82156000d000400d0307120103014044e4000303040c8100300f40d8414104c5c0c40402e1240c1d10340b00c0c0760803010829030220704518000e850340003d0558094205a03400c0c0302c140024106664607125140019402a80203591103403211000c00c1c140c00d001070040c0050122004074039500c0c1007078100034084e0242c55010030304100c1d81000103548070412a05070707421030368031485441c2d0014981007041428050501e01903040366012803125001d54241d001601500f41c00c1d11480f19030348a81080c010340d441060300051050550180400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 860781510 1250 860780260 860780269
    0xb12010603020a0c02100c0303050c16080912100902030118020105181f020c190315050a110c4204060209100507050d0905090f18010606090e100f05 65
    0xf81d00308035140c44041305540d0390000310088040540c1000003400e04c05500c041580500c00d4a07001311929a001d42000c40140d1504204092103900806030300000c5580e08490720750341c03028104503100341c0035035020000f0105204010800f0b007000341c0c429800d16001079003112605c140c1c0d8035200d8041e55250700e0008050f00d40b035404a280e00c0d00342d070001d06869104c1d210351401280411030445a9001c1d007640d1008100300030584810f580341c10003141400d5020000100f42001190020a08180c0410959280c44400780202610420b01d6082c000000e412064184081802c10140000803d102c0414400796500c01c1038a0000e403203842c424481c00c010003040e449841c441984280301d000c000d890a0781e020003103240d1891000c0303018045800400d21800b005810700c00e240b02403c030ba01d0001903242c0352600282d4000c402800d6a0310344c071740d4034010444411010b801c04801444203c000d1060340ea03280d00080c21075030346211341b0039100f01e1900460410801c420030307101210038104240241c03e06000800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 860782760 1250 860781510 860781517
    0x106091e03050d03020a17010806180c03060c041e05010f03020724061a19080a140106050301080c0a050a1e17060a050903090a090c021002030c03100b1201060302 71
    0xa440803400e000000001072010001000e03036640c2c03035030090303100c1034920405414081591842c071008240300006205103000094040e5003c07086202c0c11001c52010081a410407500c660010f41500908081140303400c00d100060040b174000c070010b10211007c6000c580200c2100303010382800100300207410585e180c4079070083c124172409080014460b01c2c01c2034802d03800e0504e00c0201c46407261203100420803078543c02c94103020001d444080b00d10b0400ca500603504035594403e00a0b05014840d0045071a04040c3d9124101c41841846925032950f102c2d003029109400900c126011440341025802050600307207503400c00c641019260050543c104650f500a401171010100c0c8840c038803c034005030b544c401060301c001202030721000d032042c1c1c24120404030a9400c001e0004525a001b041051b1150316140f81c1401114070051380041c4003440740c1c400f24100320010b03c050030308500200602c980400080c0040d40200d154a2001030f015668001003120f50048009240c00500c0a100401400d80281c005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 860784010 1250 860782760 860782799
    0x6090412080702030f040f06180609030803041118060a05011b08180603010b0403030314010b030604050a020d0c02070f050d0f11010507021806280302130b030d0807080f010609 77
    0x591781404401843c4c8422a0402c0e4840d030284a403042c01001400d4110014200444440346d5042310141404005400c039051440000c10035480040000c3c1481000203903480f0414005040c52442c911008080c12904000c1c0c03500c030720421203910005140e41c00780d81e501ca200012034000801081558032178108a03004003202500c001c1a90300420010340d0b4440065001c0c00d041c4004544072415818001e085030000d0307044d03940320092580103110207988001520b0b8000e5080302c0108003030343e6039104071010340966054101700c4e07404c0c10794a048990b00890f2440644c0d292210306100240d44500b0030903d03281ea070401400c10351803422a007000c1449141c0c0d20200040c181031844c540320311940400c822480412240d00410020400d0000134170b004034983e01035840701101c1c01d43d00150420920414061440002e00c503491103110003100c4681c1d07030000207450200401740c81065075035180107048510122406000288000c002401401d4003581e46810703540c841d1344110380e00f414000629051102c5098 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 860785260 1250 860784010 860784013
    0x91206280b04060f0810150b0a09050a0603020c01050a021602120f07030804030b070201110a180e160807030903092106060303020f0c030120070218150906090412080702 74
    0x80c2001d554807140140401840c00c0219035003040c0c6402152802e01c1102e0072245411414585203e403080507410b030103420380b460b80620075550511a00d0a4416030050b44c412074200207003203800500c00b60558003800800310004020300c400d90720308400500b00e104500705c0361a601404004140075080030f410f1074817a00d11000440700c040c0e403040740b4903203810301c0747d4804c664100c0300190500c100017544a803942c006a8500091000110b00c003081c10a03802001105410403c042c42000411118000c3c40b00040140c40307021002d40c104800301c1d40740c0150490301140410074450220306514424812010307102c1c0c05644014805080040d8204100c1807104905000c10540050b0004100140f05003001075100350014480100d031300300c20750708040702f0009040c4030340d15040585450000030002e51040040c2d040540b60f603051584005920345103d03181d05060040c4160811111300c0c25015450010502180c2e5100c140c0d4441c42048207880c82102d0017081079400c1d09000115a0052040d550010750600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 860786510 1250 860785260 860785271
    0x3090c080105090d030e06090a03032013060201060e041703100b0316020601080d0909020a021c0801050a0905042f0d03091503111e09040905010209120628 68
    0x401801e69038241d40d900b045800401c4c4a82a07240c02d4483c4c0c0001c3c214080c0509021302d07142c11200c0d240d03800e040d00a01490788405c00f00c40c0840000d038060b041100200ca4054135414103440b0010408000c1c041d0101540c83c0090220b010780950540611450b800a140c80fa843c801c4486510140c0014014800142d003203803020a001030148043d61180d9030850b0381c8041c1120b10b0100924048040e808030400d90040b00319249080e910090a0096420003100580d9a0156020403403900700d51040c6102d440c04071500c0c508000d03600013403060484904480d030325000c907200c40319482101d10582c0e001307140780a40d0702e500792003400e00030b100c85001d50fa1a11900701c1011840200f03408a0f40f1003c200c1c00504240c00a02001100d28110000308000e89410081ca44880307800080c03034400c00c00e01100302103044413144403000150086418544015000340f041b0b15040c580799000c0c3d007007808118422a01c0080c0d09404000c00a0558412180c0b03410011803155401c3d001e0202000c51f02405c4003003600d50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 860787760 1250 860786510 860786519
    0x9011710021315050903010b04110a03020714030c030c010507020105071d0d060e0c03060f090726010f050105130c05190c0212060f070305060102060403080603030c0708010609181203090c 82
    0x100103003284141c3d00d882d0180c0d0351181000f010700b1030b00303400c49842c0304501d0f20840312200c40d00d22090f100705001c03508006a4078019403c1413258120203151240d05444000b0300d50101003800310180c41c40280c604000c2c0b02a4540c001e00383d0903100c0440303c040005201810480d4000c10b01d81c107c504142c6e000d0b0100503580703000d480d001c0c00d58985820002580d8400b080310411410b0400489031301c615130200d481c500703081c595119a1294081d200f40b80554a9070b145000c80121b44125484245401100030014900204230000c080c010901c0742500c1810191001041c0d51841e02801c10701c22003990320030b460203800708807a401c0410403106450421481140801c0185c881c203c00c000641c000c40010070492a00c0882e458007040000e00c5101014100410300c00c4698002582541295150406d00c032965180b4002c80d207507025013000e00156201d01240020300c03d106500c034030156101440e061285100070b04000f442c0402d8501c0042c05010003014441318240302e9440583c01910824441498983e40d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 860789010 1250 860787760 860787779
    0x8041101120b0a031b0b0412080c12070f110303070b010e0a020408070b030402040b01170c1b06040b010303140a0e0d050703020603041b050a030206030601080a020d1a090117100213 79
    0x203982044030b000e0090040b0914000c1040b18031070080600c1d1b0041c0d40f0301401c1101c50700f10000340d410001c0062101003001550110b040c4680c0388040e407034070100ea84440e02400c107034014600340c006c159802a000100400726090200443d0404c5170801c0140100740d00e003003040d0340403010040620960960a100110701c00d2014000c01c002422180c3d2650b4890600380104003c844610201314140a10502d21080120100c0009584000c00c0c9440360f854421030440a801780014481950302c500030344040104000030342d004079059034041c0d42d51400951507013030b0a149130f00c240003240000c03d644555580301d920305840c000a0040c800c806507404242d40c0e501050084e081600c003100e18982500c140d411048101d02c0320700061104488242c09103203150003042652202600b290304000280c0002844074506404a41151340c3d0b4810400560341503451619005481002c441d104810660001410707120300350f00c203121403400c10090140103544d411440d0083d8010828000480e042e2980010170955 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 860790260 1250 860789010 860789029
    0x2043303020c0c2b210302040302010f030e030f1216140d15080f030a08060102070e070507021914030f01020c06010e07020a21200c121c05130608041101120b 69
    0x41780800714080d10381100c0c1e0200120f021030160b030405105020810160782d00c01c4103540b142c070840c100010440f80000c0c185040d0311a100201d0400c490020b010406040344a016501c03541c80002c0e02280c01d0034a100894000072040f100000d881410f00413034200000a91049100d6100c0c00e40c0c000c8481c0d620450241412102100380d61140c01c046141805030360050701444d8820001d10103805001d0401107009007008002d40180308208000c0750120840d15082811405d0300344040545200590b9a117038145403110303a1058070700034081e260911813800014000e41750798016140140115030700b0082c040c90150350007820601144503812404010400d550b0040b031505c0490712002044c0303488400050505e0000f8404e20328a42500d03100a030241001140c1c48240403800c99600003214041c0c00d10030702e000c6422042214031651404400c500c01e4205000f000c0150402054480340c0c2e6603040d0580350f200003128050b04410491040015540c4038101c8000c90b40d138040f00020f00031510201184c0c2d13024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 860791366 1106 860790260 860790263
    0x602071203080a090204062702030405030708030402060708030f101e2106020d05040b0f0403050412020d123b100302043303020c0c2b 59
    0x1920364000541490b0010424001c0b41d4a030115018111800008c45411100d4040d01c81c040c0b0856000342d80c400c5801201540c1442920303141c0d042030b1b034002802203034000b204010071800602090007443c080c0c2e80ca00f0580b00075151240e20010000d1185c0c00040100c10420000c2e184074084446d86800d40f40120701854441e603001c2d10340080715450803c0101a2400031440e07070b4a140d01940715500c070b64043c0c850010b81e030f00c40d525040319a00050f280500003480c104414006c900e99403000203a90751010380076450046e600e4503954000c071080e40341e8400140c02d0b0703002011030307600b803044c65054a0504241319501d800000c840301c000c1c10145580f203021b40002405802d02c18000d42c1a28020130003498000685c07004c182d06244040540300749503092116015824603583e05c6482500c0c2c0c10505440202480c030a10410412440350304c01e00c60101c09074079202c4d50f9216111850144049 = true := by decide +kernel

theorem cover : BRFrame.Cov 860611510 860791366 := by
  have h0 := BRFrame.cov_init 860611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 860611510 ≤ n) (h2 : n < 860791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
