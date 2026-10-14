-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1826
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:48:55.98699+00:00
-- url     : https://prove2.me/submissions/4fc84f97-fc06-43b5-987c-147bcd09ee08

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 328237410 ≤ n < 328417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 328238660 1250 328237410 328237423
    0xf0e150c07030e01081815010e07140301050613120f050105060a0b0316031104180b04050712020306041107241a010c02060c070303021005010807050f011b080c01092a060c050f 77
    0xa812400390700301d604007000980309c040e002c0c11000c01d00c01d607041031020884010050b40d064400658065480309030340901c0400229644c0d201c1c3c0d6988120f00340360018016401502e190142c040c00080c026900c0e4401408070011003807240341c0e00c0210500205d0203914980e0076040c0c8100083c41c2c0400e101001d136a0912495005501050070384900b090250381c08280d034060030301c00791000c6034108420303d8511000340401d0305030440008100d60000c0002c100e40d035940e0200b50000001180c4680b6011546401c0412240341d072110309103451044107803186000d007400340d00c0080f1414a105214030401c80019665000784001c106c0e0300c078906004054070322104006940c0254082d07801010f0340d0706860603210440d90180c001074841d4000070024046038407030b03a4915490100030720303107034031030840b44c18500d443c407040b01c0e00040c40160700041c04500d00d00b054010701d0309a07000d40c5601c8001c038040714211006140d09100034031500424a42004058094860700b00c0e6903001e28203a0f02d62023002c01c017160070504c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 328239910 1250 328238660 328238683
    0x200706030209120d050a120e0109060e0f0109020f040c030b03101b02030405060417010906090305030703060621050c0d050103050703030923060d0f0e150c07030e010818 74
    0x80c0d01007080c802624000c03080c1803503031158201070034100c0e00c00500201140708406c2c0c40810320624610304448801c1e582c0c40042c00025030030080080da44039141c0f50014103000f0510384280d2140515100c1314410602c9025091580141320310440c5205100b0b0101074145040080289030707a0307240d0f40425450a01608282f1034800c900041d00041c80d03295101103619000c2c0000171907109020900c1b03140c0780c3c50100d40944080000304106001010403072030240100c0000141494185030040d800c154010b00618000d180c0c1d43c41c140015912040c00f11503000d0b02d40030305101d23030f6410b680181184c282c56200903084458003840e41d20700310880034810305072003080e0710480e07081e03201c8241081030651011500c1c0c013410100d01d076410684103640c4100c09042d28404103e10500d400071307141403645041d500411414004100134805c000d41c0c0440c0a07220170010b121503105000400025450201c12004c40d10115415280c100c034911848004542c01c140080c290628500596094000381c1c074104040310940 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 328241160 1250 328239910 328239917
    0x18061504330815010b0f0d060305030a03091707050c04050c04171b040b0f3c040c050403020a0b0a090909061d0d0215130803090303100e010510200706 66
    0x41d0301e040e0410345001c0f580042c9201c554102c01c0140503002002c0211a246000441c0c1c0070340b1203118030700035002080e165100415900c4002100c81519401d50040c1d4010f5015031100050301c0041d4130846420b2241c0380008200350001314070710340c0d203190541c0042c1c2c0003051115240d007015154407091440c0465003528002c507500c840b0110244c91046801d1550321241074030284002c5886034003086040c0d101d03420040c458806400c00c8030060340f621001ea5444031020700300a550206c11010480c4812045c00d1650003542802e6480020501410450b0100d0794050005014503252005044007a00302c0d41001c010000d40c1c003000500c80c103c1d80501ca028600030100001d82881030450403a10000074451a0301c07a801194503807201d10b4011808003038410281900642c5962504c0030f15035400884c0b0300042c0711800100611082c40c00c000051032040b000311846200c3d10f0348038a85001d03510b00c2449283c1c0d0042e41100900700c0c161040c1d00c07980785002200210050f041c040b051071418942d980d000704001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 328242410 1250 328241160 328241261
    0x903060106120609060b090f030c03030f040e060d081c09150b24040b0723010501170610060e040209090f0718080a02102618061504 58
    0x3400300e8402d0600a103020002000050316041b0351200a001e0071944a1040004107421440d03a202801903446050008003030725a101642d000c19000780d00700340540418010b003940000c0460400300c1c440d254150b0400c2c48141441c0800e14141e24800c00308003104030301074440c5400c000042c10b940c44d2405201e824000423426000d050300b480428480304220008002d0185500500c1c12401000c68059590072500786030381d136030b072400e2010f14500b108158521210010b006803041c00e0b019403003d41030714036944400035121100c0c41000d94950080d04c12450503082c681d02000300500400c0c0e840c0605101a00c0582060010800264840700880d502c0a40707041030820081d08607400018810f000c4100c8880484950508c2d501e47d60b07500341207030028010008100155142c500807000b803501a00000c541c010620705280768110840425a003800d1803010300c4001d68640703000859031a02c100c2e14590003503000c008110401002d00203156401030f6294020148050401d00c013500440d0200713200b040000d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 328243660 1250 328242410 328242437
    0x50709050a05070c060e0307080c06060406080d0f08060d060e011401121709010306030203030703020708100204050f0904081b0321070203032a07050a0c080d0c14030903060106 77
    0x555000616103072010303192104103e085600801d1015500b0f401100018100308852480c9295108002c40507110010104902d00743d071100042251084905481c10711059640f24403c50781c07000c0c440400304c04110b52016840030903218045443e032080000389881085081c1d0b88401d0222664106500050707510381d41e0085180c01040c0401c0d00420030701c45015000101074440341254000c8112884202c000003980d5840e503880383d080766002e507800800340c0350b0350b46841c90040d40d51440c41c411b1811500079054042c40440300da2017030300c00303c8074045d04090421000b5800c100351354000410031a80740e0403d0010003940030840361000c44600c10003006507513071f80301001d44985400004000300c541b9000442080403c0c1d40c0402960b420441c161460082c04090583c3d4070001460028807482c00c01c004584907091041c0000c003114120700805010741c0c1d40b502c0300708864940c80c00c04000e0300030810710419400000d502406120400c4003c40c1075034242041c10340000c2c101402a40420001542ca58a00b40d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 328244910 1250 328243660 328243679
    0x607080c06010527090a0c0e0916050904020907120c0306050f12120708041d060111010b150903070306140702060901024f08070e0405030306040b0a0f030507 69
    0x90151004484440a4102c2d1100010881445403201d80307070340b00040e01080260304208604440250b10207e4500e2064a8410350180614120307a510080d200f8040103110580c66948401c007600c1e070140c0091510740c0d0f00d8080c0003400034060444000c100469000050f5102c944c4541c40c8500e05e1a500420064032b010300b0083e02c0290b280ea818801c0f9204161400444e07400204a0491803002d43c5a45e141c01d11130402d40100d0049034820400b221941e84040648034899003070900c13074507090b254480c91042c000505030803110041841a00b2582211402000130200c43c0500000d0200800300c421003900d80d501c5405807044c0340059420340810b5010f0254594040c4002d40d44011407800031810328502442800b61400160f076004244980024004546280600e012084071100541c0340e00b5100c81e41c0d07041c8020b01c614451410b1034008c1d41d1020038980c08101105014942002c01141503440e45c5c810040140158201590700c071604080c00117100d55030307141c2d010085004401400010b072501c50350a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 328246160 1250 328244910 328244923
    0x80607030e060f04060b19090203013002090c04080102070c14061303020f01090806130201030c020f0307140106030f060f0c0c150e03090d06060f080303130b04030e0607080c 76
    0x2000c50b9000201001104006a0070b415032094016201044520620f00444c21030151041d4140c807401480d503000c40e00704100d03001141250028411180440306112055029015104900c0c1151118070328400c05442e14051040c0c11000c032807070182c54a0340d100e152a08a9000040031507048000c80010494040a000c654000000035542c40e0301d059280f501c051840c061600000b80304051040e04d00320a039128005a001030130801c070403240c50342400050344200984a10080340040c6c02c1401c505449803022518041c03c045000040d400c05071039981746c40340061181c2c2064615961205d00101048c9140e18880d002da00802001404121025404098071141d5201c0800e10800c0120540095034402d11044600c1003924002040720014414038110300c120762071591310080c444503c2c01401080d91104d400c491000000043d15039480d40c21980300d0004499003108408074503201e50100350540e4020368894442d20700350300004582000204240c21650094640d040b000ca0009030000d0308000c1c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 328247410 1250 328246160 328246181
    0x3150906030c0603111603020c1309050c01050a051206040b040c05120109060b040b0c0a0c060509040f05010506033d18110306010c0c03021c20060d110d0608060703 72
    0x7840700c0d8502110b1785849200700c2e0001111240d04580c50020700d8802d100c50a0011402001c40c603501540f410b0f58009000c00110981d028010500802c4140d0b00660880e00c0c0303104103840c1c45041043e030710300c00120940e000740200c3d0495180c0050401a80ea648503030340f80c1c108144c444948a41031030801c800414416040038405915102081c80204080d80607034045500c010403856841c840012614101905480000d003050702c9080081401500b04010384801d4130309403400c1001c480d0110744501690020711495410035010004122915492108141d81d1121030303080380c0303045541200940b02d0f0b64820f01c1c61000028101014001c4501c0002409880c0c0c405034010300250340001c00320351540c800a40b60318180001118601d0401c41000810401160014040102c800606540d9190099134101c1100c1c4002041070610441c40c0302d0761104e41e0014094495400c0403480c00315580180427566041080030760034004001114014052107024100038001760503107043c842009029035030007140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 328248660 1250 328247410 328247417
    0x203161101060303050f0f13060201051506070f020d0228051302032e03060f1401050a0b040501050f120a0b030129090c041e0608070f0807080703150906030c06 70
    0x410210740c1c01700a6800303400d841c0c1d400940e20440103484400c84c0c0304034400c54106ca40064400a41c0e9030301917010510403100401d5800b0b003600401c0401000348600c61000f0142c120f0142560301604140005000305407001e09041540412480307900581100742019409548040d0018811420701e0b02c6580302000f4201015401c40c24094508911400c04507d0109940d031007000d69003044000b114240c1c0290b40290007000341c50043d00c2c0321000350500000c5901e500c64035000000383d5050441880042b0748812060301c0c10300d401c1c0001102d00342d016a40c0145040000e118059088401418481c003800d0031560006140100105144c00d5841c0220324546502014018000c46038034042102003491040345e5421003661905211071841c003a41d001200400c030f04504198072041d080100106440c0c160b2a015084d6460b0350003240c40c1c007043d6a442e00016103072004134864500440c9480c1d0000081d040210344040f095290f40001d402590254039010303100c0e40704000340400c446c01500508841d15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 328249910 1250 328248660 328248671
    0x80c0f070906060e0f0613080105010311190611010b0a06121401050a2606040b010f05030a020d0f02220606090f08120c0a0b0f24010207061b060203161101 68
    0x11010700100c041c40780030350240305c018600302030555030380c0101c4140300c1c001c0f2400d190b4991104a8030f402844240012501c504105070500c4c007600d08800c18501e001c19807031400005a08001c1c00301d942c10001e0070040c4040d034994000084030341e40e003050140600419941c00041004030180718041c0ca0f00c20b500c0c101c4481103840180301030307148c01c5180000d03201c1c1d602503012040c1140003240242c062801c4484560300600082c00f0800682c0c3e8100e9040300c3c0c9000c800455191a90201502c84d0700309a0001c3d845000c0e07051500005440c00301003d151800208060007508040e44c040400c001c0c800d12220140759180300c1844415004400400a07114100381e001c809400d00d9911582c41290a084032480c141c085441c113819042080b0350011580c0c00301300f00382c940c00d103944803034404641a5249008080e00d10408030580c1c034908000307251080140e00074080ca82c0740075404e0b5074080300421740d40000070084a1900c04205580010340c040e10b5454284007000501200003400c00c0f80c0c080c5038078030342c0c0d0410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 328251160 1250 328249910 328249919
    0xc030605010f050c0f010515120705030d080c090406030501020913140127060617010909020d080a0221070204060e0903030a0510031b0303021905120a0c080c0f070906 73
    0x500d000107040c00c2d402c181e030b03940c0201030340c541c9480d00700001c038840d030340c00c2808010a81840c4900c05481c0d4900b540c4004840e10109542c0e41c40310381502610340c0591040c107011140c18464a00c0981180f04400e46510b0f10114101040035900f03a60810740d01603400180c441c2081c1000c0340c081750390400d0b80c40c04000c128105402c060346900b062048000c50f46000c80c140031150117040342230050a0703007204100602c030f65500002c3c000c00c001c107000780c008402103000060421180c1c01040143c40e40180100005010740d0b43d400c07856042607101e8811403044415050000004403543e6690f80341c62a2010307200c3c03003544100016180303981c0080c02c1400c0d1002c103000c007410000081d241c00020540c00841c080da160306000c48504029070010348443d00d14509080c54030a141150305c1900c0c040e0b400d440b0044c0c81c490b0b50b0b17900e01e00c0f034407c000d000c0e5008020080d0740e5400213002e8042c8200742d20300240d03040b141d80c07a031000340e80104019000c1ca03002000403042019080010308010701e0181d205003e8075242 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 328252410 1250 328251160 328251167
    0x80108030702032a09130b010b0a020a030f1e030b0306091f0207210503190b06092803140709090c120309030219060e031c0c06150603090201030c03060501 68
    0x380c2031080402a1312520a101c840340050360040802006408404903151100107911810420b90003074801c84136410001c6010010f038000c40301c458401d0303001010820182e035000c55104696010040c01c106880804010003404040194024003561b64040341d10325080301014107200717015044a0317440d484106031492240402881c080c0140c007003c401a1100c050342009031030b80002400307503010000032040b14400360341c00901840c05503620404840c0000000341640040b9010081000e0340f10b441400348050911300b149000702540141101e01c0c1220003145090f40b0150fa803504100c40e8403400c90a4043d0034601008694001c1810f26414025040d06480388004484940500b0308404a1010214149402031040358011a400740c02c03c0d0041110560340007414903d0301072100007981d60403000d074040c0307400a0301015030140c81d200c1c0c00114850720010ba456a00c040c908564094441c0c1548452003400141030703000303200c2030f100462182c03010300c00141228170301c0c10340c40107051a04800f40b002d641d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 328253660 1250 328252410 328252423
    0x20903070501050c0102091804150501030b180115080120030709050409111908010b03030c030a03180602130303030605040509070b030705070b090a02030616050f030604090f0303050708010803070203 87
    0xa00b010744c0e5031038806411601a1107007203201030300036000c6031803410b243d00503852003807280c0d004014103d24460070148407415a5801c1c40054003500d01103001c500125501440c0f0a1a241102c00000f02400002c9550a0781c0050360f10641550b55203400a203844645c21480003209405901002e14510b480400680321031100d0240c0c60003942e49032004010012208171032110f403040100100c0e800b00d41e13090510b690650b9070150440c42d5080c10362075443e6040001c1515400107100002e1410610072003000c500a00c003030080b5000a43d1911003800101d0007610040001207542441c11081c00c2c10b504024080c1c078050350003079002c3e610f40010041000380c0031400c4000e8403800d2000c555641ca81e170b54111540d009005002d05a40d0007141844480031000600103161442a420348429a0b18020000407a00c41d44480c1008140f0801ca100200403000c4020344d80140c000f0b10008402005844002d0b60441c1e400045010940e5082444021604001e003580146803a200a40c9442d0841d40403a86489 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 328254910 1250 328253660 328253669
    0x3120512010909020a030f060614030106030206190201110a08071812030c0303020f0f0304110603100e190c03051f05010507020f040f02030c0a03050f0f011e150207030501060902090307 81
    0x3d590b040740c881107554185441e0025a000543e030341c0c942d002800c040000705201d12400740c6008048403c0002401c040c003c200459030024001c07800d010800071040540b94100401d40115540da82801c840d4541d00f1001d030030b100650381d48003031036403170a0380c8007420000f02d5001e280300c0b91071071100400100c4810364000e50802d60500e0600a40f288a2406902900603a440312510100c0031481c0c240407031000340658899409892010010b045260500c0318034031003900d081c000300d0514082440004000d6802d240c0204405450011903000580804221484d01c119400002d441e0001d00450f2614600ca40c00c07810b55020303400c04100d249c0000a00f03548582d64000740603924152001e0110f5540c0e602c0001452041d81d4159540e103081208511150b001c903143ea00401c1c600b0b00807640450058110302e12030807449503183c80c26400c19510b00c1800340c28850f04030581b40b41d81c4c00824109400c680340700800125030010007585085203812401e44215070422410140b041c803140d041ea40d00018464103c0303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 328256160 1250 328254910 328254929
    0x191a0c071202070f06030e06060411090613120c0905092e0608010c05030702070b070b070e030f0114060f150307050702030a0f050309040605041404030e03030702190312051201 77
    0x40000760142d040c809542d00c10f8a0b0031410080006101da05504a00e40c07040d5682c0580c0e034556510701c1040101d4580321260084218140030403035a50070010f00900701c19501c0a01040a20340d118030032108503003500700841d030084000ca010050508a4000c00b504000480003a14519054203047c006081100d98210040700c4407142080c0711450a500c980c0c00741c50004001c1c0035039040844040d081d980107032800d0380140710304600050200c0d41101031b2549140d100f420018640c460800c102d40525050b0b51065150060340d00c1407104140034401c0400d0300f1490f41a20070245440d0b0100302c2c4004105070320301c0c0180e900045060079240680200c1c1d51000f103500f44207403034180030f0003c20700c0d0a1400200604016050141800b030003400405070141e07017006c4801703020701603c48040c0401c1c0e80d640b842c2c1720300f01d0149401280019004000d05901050061708413410244260000341a00701c2c40b1501180301e46201303c0c244240080e640b06a1420b03601800c100c1d18080203410801d005403014452910350 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 328257410 1250 328256160 328256183
    0x11030136020723032809030c0906030309080601081218040e0604050721061a0306190510050d02041d07060c050c0907021f061a030702070504180206030c040503191a0c07 74
    0x317940100a0307540a945c100285000c81525118442c0052550b030109030b010614280000402c5980019114141c4040901500c452041c680b030a064940061303c1c020a1021b0425020015440f1031142c0005004444014601400c0c94241070b030902103544c209102c0e02c01c0c004072544031032448500c444905640a0400195003c440c299400c002c080d19400f00d500d03005100134400782200024881d920011009c0d810009611807060040500c1081c3c0304260308003040703c900d0340161829a120700450070340d401200c549080410381050504203960401c0c404646600f01400512004001e2028100010341d03041c41103080550000c1d40d030707c1010f0a2032114640840c0c004a0039401600080020452101c54242c400546183c4d03140036002291880d00500c14080c000600b841c050154030141c0c22051005030650703204d50240401580024044a10b02b1402c01000520303840410003140c4010010541e0070100503581341416115100740e00c00245171170380505200500080800301d40100d9030111682a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 328258660 1250 328257410 328257487
    0xa0c0f0f050d08070f0503060d150b060409270b04080a14031006020c0406030b0c0a021207050a020a0e040b010b0313050604050c041103013602072303 66
    0x14202862400600718080c65424010081d00102e10034095040c0e504c49525200c00807104590f6030004985280c0c0c00200303400c103003005c22100408000f4400e800c1102141d911403441c081001940580d2020300300035502d144211101c0c0c912584003200f04070703c803401d9030904025180c1c0c588003d0003800103040c0110008028840030b00880540c500c81c00503003082516841d1000c0c010400c4c1c011407041c480540603814600c0d0451905200702015240d10000864060704c8035901489070f50003c030400c80030352050014075440c4c40700c07100c00b43c00102d00c14401402c5580c0d036441401640700003607008155840000d014000001c3c0300a0180d415908140d042a4503560361010104a0500460011701140250414481406804180b080031810282d40c24400f0381030140c00d00d40c0f076101c01d00c2415000d00040400b103110384004008c01090070304460101c0125044415400200ea2086800b03d501c500303401e01a8400e00f41c020000108031641d03101850801410241802c00c00603031002c41506015141341e03911 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 328259910 1250 328258660 328258673
    0x131205070b0c0345090403030c050f1321050607030507140d050901050610140a261b0406080411030127020306090a020a030b2701020d060503030a0c0f 66
    0x284c8203841c0f1041e80444042c0c001c52003200300314021150307003801e01c62028402000005a508903840b01d0241c8501000d503510b4600310010280f00e00c1c6402040001c00c000846880c0c0c00024082244890301c031800814500fa03620118aa202140038070f031915081201e01c0851000320750140d03c0340c001c0c200400c0703035501ca0a040302c03041000080d0311004803020403c00e040488641c082481903071441c0c000c03c110b84905c4200056845007050303500010b1b8520088160074480030028050150f000d007007a05551074600d03041c5800c8041c1e494070500b072490020410041045000c903100075243c04450b05407419080440042c01d07803400410280c04d40560f9900c400385500c00f5407085003070000b00c0c00711700d1a2485e5142180d01c540c03c2c00e40140d129114600c04941c8175400807920700c0400d54020803000704603241d039440c0b00806d00700800034542c01440004100b010003184201c9980342c80c88a0005988801c00907a5404503143c80e00498001d603c2840300644094001801510301600103621040d01142864240d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 328261160 1250 328259910 328259917
    0x207140a03020607080c0d030612060911060a0c110411040501051303050102180108100815090106080a0b0105090928020310060b1c050402010f030902030a02090c131205070b0c03 78
    0xd400c43c10010703105060040d000007a040e004142004e503842e00c0d08003003007201502c40d507004810440c0078442245000814640c48a0f624600c21001c2070407816101002542a0700901c4084010a850701503500801100c00c0b208003030765004035006c114080110890f044180200c3c007031a8140308002800c0d0744034240d050390210043d40e015000b956640301c002009442c000f0043e03013160210f103403c2e020030318407441d81b039080094030b0b081c60080141018803005981c1c10348001d48028850f5585000200b1304030740a114000105d0301546000915500d00340078440e91041c02480c2e00302e1074100c2c401d801007040c960406010b0848028002003080f0100d4000681440400503041815500d4500d000030310000c518042c1600c03080c1c4001010000c241851402d0039642c00722030007400101e00c5030080056078020f034000c0306402e002600319900c500355540410140c81d402d944000000d44049000928108040c0750b0034041c110918200240d000c0c01e0792101c3c0d4410b40790040601e41030001c2001e040c1d802081040d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 328262410 1250 328261160 328261163
    0xa05150a030c06021006030503070b0403050d05010e0114010f020d26130c0f0e010506031003080a0c0b01080d050405370302092809020102010b060d0e061005010207140a03 75
    0x45102980c0d82c0c645900090140e10442c0094016141a1580070119104500850360400d001c1c52800046540302c02a8020040c811000e0140910002004451510131307039000e0140c00f0009041c55052080c6410505c003520480340c1040081503440007016400300303102e0043c01650400e58040c04084006507000c0840031211500a81010104031403120360a16001d00d1601855110880648440d048001728805000709400c400c00100100802d0510400070759003c40011591071032681c4a90f10050681d10000c00c220004a070550f280741400745102d207040c01018072070000d0001f01c020390b201500600440c0b140310700c142c105481042c60141442400a02d0680250700c0e034011180c0800c1c40c01c0c0d184c9650006034000d2448500203514800030302103c00310251142026030b900d03a4030b000b810000e0944043c00701c1c11952620035200c400d8580201504581c29080f4000c1250034200503010b00d0701c1c0c0c00800599014580160030800c0e81d0700070911109032069007007020f9502178540c1c042614003030145d10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 328263660 1250 328262410 328262419
    0x2b0b0f01080703020912071a03040b180703080d090204050105060901090b030604090f030804060c0509010909150806071706060301260715050c010c020f1905010f060b0304290a0515 79
    0xa0000004902003101000e448c01030b00d0745a8500305030714100506000c200c80c010719044051004c80c401039000002644001c500070121010a9201c0e038031030440717802a0188640454035803103035004600d0f10b401200e02416042d100a0b0403c484900000d280300294030a4084100000001c50b90b1600e9507080380e05503540180e10701c1c001064030703d401440110200c4041e183d85160005020015100d842100e031402816981c00361100d0070640c841e0000d005031a0305000044810750002040341d4203004003440b1b007845481e6804003401e1062141008040141841e208440800050000b0b195400900414810902c4d20310505c0b840320101c640741404580040000c110000e4510310050b80c030000a1803100c0b4954000d10030a01074444c140d0b51070f00d06803d6140d1a0f003201100f1303840f040f250800c1600f014028030000c16810100c0002c4811907421390409800003c0003c01c000501c11800542d204c2c12003070b586000d8911028503801d0704000320251001c10210340300c9012468101c100c2c220f45812610082 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 328264910 1250 328263660 328263679
    0x1809020409052103040b01031101170f100603051b071707080913140c0d061a0a0905220903050403150f150501090b0c01060b2b0b0f010807030209 64
    0x141266a64440c8200722102102d8440080580b01d2840a40340251b50000c1d03200000d90171340d1740348405a0155144103040104000740b40c40314286400c2014041c40004e6070b819401d00700304018581403d4030790484018581003906001d0590108480d103c00540503000c981e4a40c555440c06621a000d40c010f00001c0740004600101400502002071084500c200d40c10000030306c0300d604800c10344225064085000114000188480d00071200511100326007000004541d42c440d049a54140718200f0034400c800c201058a100164000e4001c4020303040c201c03401c8014030380ea03048803202c01351107200800c81e076900e4820b000c0030540038805940107180d101e141503950f22090f030f40d080010000d44140410319800c0c44203441010408035610800e031b480c1a075980c02018102040c3c030f401a84500c110041c80e46d40c0300800102250504040c10318487c1c0c9036040c0002c102191150500d030181050101c035050318000031001c2955440070b20880142c030a0901001550740d0600a500900070001e40e80c0d000300d02c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 328266160 1250 328264910 328264913
    0x30705070c0f1d13060905030904090507051201060f1a2a0d030203010b0a2601030506010303030c09050d020f03250f080a0c0302090c070602040e0105130e06011809020409 75
    0x5504500c25100c15010072841411141002e43e004402503640d203009041c0805000c000c5007107604059041401001181d140a801c980403c0c200d90111a0039529900562014002454046008800401550020310016041c400d002d03072901024030031110383c01200030090f51700ca0300700400d5684110880c0342d003404402c02c3c0d066030040609410040c000f1b5010b482d0b074a007441ca00a1003503906813000c020083e4100007003888144c03a205500303a044041071208c1341c1c1003842c9200f04008180a184104c01400d000d5145180240c2030b107904180105c20b11482150030f00803902c444c1010090180c044a41c83e0542c400c4401103421314076040b10401c126070981c03248049030b0001200d190110340d000000c92010942e0b0700903050b10f0302c986010042600340340c0d030020400b602c1c2c14055107400100c140b9a081c81c10300b07984c1e41d1070103d0f072245d1702c496004148413004100e00d181420b4908280000c1100910000b0320070000591030f84070501941002007451414580004c0455018014841c1e000d4030401071840c06 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 328267410 1250 328266160 328266179
    0x10f0207240e030d12180b15030d17062b0516050108010e0a020c0715020709060b190305070201020d020412060b0d05210c100518160b030705070c 64
    0x400c00303800120b1034140990b81542400503080d0410b5440380d4032600d10519804e22200500003c107040400c0031410603048000c151066411405540e2000403107071120255800d00d03040c012805d41d401c0500001c01c01401030400381c040301c00d074410412980e03111030311007150011007000300e80c40c0e4200c07240b1041c000c80820054000348403840c1c0110031411361001c40d60b45d001110300500c240542005034050901182e0402026006880000402c405941d4000d440e800a2a0300041c490400c5006a110b8401044100440e118001c06014144889490f10001c001d40b04803e95041468808056482c800645014801e40c1607070404000000190f582c0c95448580000c0410200030681c0d00c5460034062141303518100c1d0a542d909a40240a88038001c00350b00202d64131014810140c9058000f0032030a8900c03c0b041c0304141007000c0032600002d2504000c41e8070400307084a4070900226a00801000e10412103501d000740072516003265183c0da1b0f5680d14003c0310140105880200764000032007000c59580034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 328268660 1250 328267410 328267469
    0x4030206010f14060d02070807081201090516020c1021050910090314031b0f0a0e0603060f0d0507091104170a0b06010c02010905130209150711010f0207 67
    0x90300c10b4555141038480700f03082c0e160360031030010b2503000e08100012a20001c85402074242c05019072000d44c201002a120402c079075100b1100d400480404100522140c007052143c10f0300f0003e1003000b0442c103078450038040e594520907022580f0440150812012861150045a8000c801100e81041c07006500ca4400050b02c1b09a400710601d0040b480c070380100690b1803081038404c42d0941da0f584408207000f4040c000340d07800580008119003124400d07055000102e4028442031105c4110550384402904005040326500c0da822441503c0400511a00740e61703000c0451080c0c6d1044500340d000084030701d0414a0882558040848141004a048941c00c1038102034003c459525040c03041c00d003840071250351100084180104154015404503200d540700f0340300340241900c181011000140c0700d50002d040010500750511b0300343d80000b248155810f040c24100c1c2c0c0713540800701607402e05004d5a07600d511030000050381030400c6407071148154000c0c400c01c8890020800c00d41c3d4030310310181b00014150740c2103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 328269910 1250 328268660 328268669
    0x4021804141308030c12041406060a0f170a020301090303050403080c070b040602030c09120102031f0807090e241008240702070e0a05010303090f031509030302120403020601 76
    0x80c0352001800000112611042c4695160000558031018903500d0700125040900b034814140c8040c080188500440781003035000d24007980f41c00303010b0386d11982c4072407138814006c000600940c17004208200d180b80103850700e030030794007414600901c0ba0700d039200d132a180003d0404040d40c5907003002180414550160b1010303018030f00075070701c0c19056510450704200740e1141200040c00c0d800c07241300207400700d030295001d15084940d1104042c0f1b0007151030700040984140c0390000050b039600005204440003290310314015500c000701c0c0e03110750030b00c0d20f150075485144601c91029820f4507880d0440d55201c040c0310103400407d000313822807200c55594124415190b4212280036608401070404500c030180012603041e6680d030012024000d81900c000744400c0000904840254030601c000443c50b4081850220311500f0b080030000f40940c03550034000d0100704180d01c1040d402c41001c01c2440401c032b212032004001a44200c0220314503001e0300d0100c00902c40d840040030606003400c103002c105075000c6002412207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 328271160 1250 328269910 328269919
    0x10b040f0b1f0c02041808190e010201180b060402090909010b09150306070e060910030218120d18050a060806010e0303090a05010c0c030b071206080105010b09010509040b040218 78
    0x1c1032582c490340b280c060003112401c00704040f0740f076580040c5400d402900c00101c2c62010f2000c50340c807559403001c264000200581e610b5500408161714164032403120810681c01f48001c0c02046541060309500c0714590740302501180c1d211000581703944860301160040d00f009400d00441d454424a500d009188001603103125040c0da10110305800c1c00b0914181e00032600402a155680711603c1c00d40c2c91141c1c10244641100092010300c4e09556514408240304080351801759980c68280010a0220088019144a440010400916078a0020f180c40c80ea514500f00900040c01c601e00d541704084071036120642c420100c100200b05c207a0f00801250044c00c080c1c968120541c1c008007095100c0c0204050b160704903480b000200400e601c034071881c421160096548840c026140d4540751060075040340c1c0c50000c54060701d010642620700d4441e032402003038004020440c42d41402c0124180340f00711000181000000300302e070881c3d9601d65004001c131b44c2000b40308542d42c507494a04410400038031040f141c8103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 328272410 1250 328271160 328271179
    0x1060f051915050a080105030c01120b04140c041e030c0303203301210215120412020a050c0f01030e011a0111070b120702030c0703050c09070f0e12010b040f0b 70
    0xd03040005540042c0b0905841e603403043c1400bc0b80041c000d2040c0d0300c3d1a17a01030b40b0780b850312555601c10202d284c0940b1215a440d40d8907420440d5583d118180c11003e0029030030103007410004190b2408202c000c0d294185080c42041c0c4e0740e00d800d00384000711812503050741c2c0102004009001400602c0c02031581804003a0b5074610f1b410000805130300824413031070004080600c0c415407841040c43d040004603100801000b0b401445103211911508480c3c58120720400980a200500084010a20402d20a8402002c0c1c0b40394135a00d20341c80e024013040c0c0d9406006142c150b40b00c50781c040d8100702076841d40c03c0000c0049166594404403110310030348085020a1481000ea00604000700e510000e481c14040601d25113060028030700400440140284110b01003400040c0e52a9018848000110300950090107040703240d20410810340b2001d80106d090000c51190910100d03040511451040c07000c83d031621119680c0300d0030602400314040070301e0388a440c00070309006884040d4000314809005803068000f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 328273660 1250 328272410 328272419
    0x5040618020a050613120b01080c030604120e06090d030207060914090103080a031b050a02390121021905040302060d0b060d0c0503060306070201060f051915050a0801 73
    0x1200e4554019400c000031007010320860504c00010441c0281c0001c03204c9190b5070b01c0001081c10014800120f036008400001003010420800c0110b4030f5100840140c9880c0c1000da54001030b40ca250460b00003171102c0160a5407a07540c604003551503140b0041d040c40c0c081c40742407134003c1d01c0c0c03980d500a00001c140416404100e00070000c0c2d41007071545000c2c103800790700d90039501c0e44102c641000008808150b1107180300c01d444081107042c40c54450302074650b261100c0d504070005e07080501181030240240160307404400107050f280c04410364440d041101184c0c503c1d240313004035500d81800d9000910704c090022040d5800c01c0d103030700034100c4010b104007940030100521400c139440c2c4070701d02c00030303500c000c0c140a0000d0031805503000c1c140310140185528034003810025010156500100c0c00d50110b0400700070010613090500905901c0000d40c402080413038140f0400492485640c040c0600030300803840000404030711288160050b055400400506064000c001882d540c0000458800207890b02c0c000107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 328274910 1250 328273660 328273691
    0xb0402150a02030d051906080d1713060f1b21090c0501080a0b030604060c030e010527030c120a090f1211063c03040b060f0a18050406 59
    0x481004442e405036140c007581d04505030182c0700103010244c0195010311010761310710241c81340c1001803810a0107011048520b500141808146400350510488403108000d178031012240081e005036400035001804c03441000c40c0d0340051003064254002d10202d400403103050f0750800c44100c01006140c54081030022071110b54001c0d211250360050402201000911056010b002c0d5550701c8041508001510f45d0079a0009140003010348091721000d6440e8030303079801503506025861002c40408000e00080c2030030f00780303841008900070003060b421704525540b0050300e0b42031003229189007140044500343d00701600c2c41e840507440095207030049450380a0015149624980e20021240c000d28041c600e00740316121030701c84160100c07509034000000c0000740000404103825294a0103c01c9502c5e00074403044060303040b0118060304098113030f00144204000130307150300e604030340c01401034800004865100000c99015941c40d00811405008000350b07440281e151b40c0b02da44200d0185c8400e0000c0e01d84450f601c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 328276160 1250 328274910 328274917
    0x10090b06030f0a1a3c0108150103081327050f04170a05040b12090d0512041b0e010e04060c030b03100504080c0a0f1401050c190c0b040b040215 63
    0x420030480b5004c0601401000d00203168010800c46000a10241805028103450500c0c107524000800030b0700341c031100016a055a90150580fa001803038028441c07080181c0a81c4c0505c0000c01035400011031901c5d03940c4800805004004183d610008540c4070f45400c1740130904c48d00c4a001c05e5113800d0006480030380c241000ba020350707005480c0440245404252880a0b4410064442845810000012980b5408000f809031302c000d00508402424115a11810704101004160400100348130f10703080103582c2000542c009902071401102c0389803c842200030003500d680701c00006080b40c000014403032002e1075081c1c03282e4410703d1704000c13100b4502000c0d02110740b44101c9a400d9402001070018074000c2c1c0d848030b030b002402041451704001245160b50300e0603111820488056a50400900c20050800c0d0034050038040c8000038480d601c0c040e00812010f005225001805500d00c40310054200d020308100c660182c0c011800300107502e42810801003101c4141c5089014140380c0e65400c00c4d07401640c069 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 328277410 1250 328276160 328276163
    0x100b0414010311030c21060c0408070b090310050106020a0c05060a14030702010f0513020102010515100f0311070f111206150f10030c0f0c0f0206070510090b06030f0a 73
    0x4568041e400d41d15200590302a100e04140c05214154200c00c07540d88100ca10040812140548140140090f00e61401c0410282c6804011b5005100c2440710210109500c400c0d218500c80458a03080e0704c200203450b140109480c2c4256900d00000480e0f09680403420a85542c02611801e004580c0c070380c00c0c03140c144110641d000c00980b804a0540803152408010f5802034407030b100108094905008187c1180c0090b00c1c0084001845003c0c1000c550302030160550158000400e00c188458030f1000c500b4812600e505002041140c550410405020fa484401c100c0e503585040764035100742d403070130074000701c45000f041d261852101400500e41c517100c42e02c0c548502d8200003800403611031308080500000c0540419512003043c85036180380d51207075417118101c441d0942e404200781c400440b018013506113134840d04007007092000c0c2c0c3c0f0000c5400480c04c41d4200d43e06940c8655150708604040b81040c2c400d0080609050a103050b0b0024810103001e0f8900480048090311a44101c207010301e541d4407000c410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 328278660 1250 328277410 328277441
    0x2031306080a0209040507020d1202040e0414070819030318050a02060915030f040c0f0b161e05010b0405100e0c0c0106051002102706050703110408100b04 68
    0x142400441d10900240b904203128450260402c40e0b104002800d0343e40c03c44903400164070030201903101c150b01056400a0001ca404118946401e001040c060b80c5801030011b005640440501e640c8010b003041081c00a2110006640b0761060381c0c10b04180715a02079001b6000130741042c7c032010002e00c2902266151035404001402092006e5082c00182d41000c00801d138031802603040c0c0d02c00c9165102c008c40c4202c81200002c2c009150503c1d26504008a43c0c100f01e00130307400108180071342e500d0700382146c0400329206c41490043d4140c0c544000c0d403c1c01c43c440701c90a85400e242000420105404c001c07020201164144447c0e0f482c482c07011980d91240c8202134001c003074000803c4103820408001c140004c0b00f2400480c516031210003140d0b45140c8400c0d03410040e40070403507004021040303103d54135100c841040c980250400e500148080042540800741a080c1c0e100b0120710824000c0d030005081018903480503031103d50ba00c500790345440a4641044100c0c0c18581c04941c40d152a00c940c034640800d540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 328279910 1250 328278660 328278697
    0xc02030c0402121b0417150a0207020a0b090a0f0e090f0f0d050f0403050304240512061c05060702150a051312021212160212090d020d060203010b09100203 68
    0x12601403213051168400c540800800000c00c0c500149442d4000300511100181214507601480d07034410b4000400c928280341c410b012160059030b40180180c00c4440400085403a844054000307001c41666901001800400b00400103d5418030b490142c4141c60310700c26551460121006d054881c9201308824001d030b00021410ba0240340501c01900b0b004003c5541541000c0d101e503a01855603000b50800440c80301c01011421480c4100780b40802c1c03001040c0750407401c1c62543c0000c8030041e84042c081505c102c0341803200b220400d210101d00c10000380c03c00100c070480d040c6a04c001c3e403541d90040c00b004440741040001409040c150043d14001c2800412040000103591252030311034074039440e040114086c490fa1100500190006408001002c46070001641420b21942d880c01444000c004195000100d1b42c082c0d00b00707110240c0348042005c3d0f40f81501500340c0e01c0095903404121500400244c030110001ca51119104003400a030501541d0070032010610010590340c901901504042c0c4a1005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 328281160 1250 328279910 328279921
    0x7030c061707360e090d031104090b040e0d0f091a0a030905100504050d030e06190f0b130204052b11060705030a0819020c1b06070b04030c02030c040212 67
    0xd11105401692042d0010f424250600d0b0307807410f080b030360049600011480500800220501203410400910306081001d142c00041240d00c5008621031702c3e840035624408a21181c0310740d048000c0e0006d0040c2038494801e03852801518071861200700ca070016814890108103940d005c80042c3c074100d00180c215042034484001100a000c0f076481c04c41d05402015a20043c00c038150050600491207540644078940020b00300030304079940524847d140d0703031014040c1302c501c00101c0c2414500720603c1034003103030145c1000b1200000d0300c00c0082450304800b0880c81406a0b61055000c0c0c07040d507208458805125416140c1d450070f40880c0c00c4072201c111000901080000c0b88030340e20604841001d8001c0381015850345400b42540c0048507500c0c0803594400401240000d903541c14207064000c0d02d800c42c1840945442a030b903456802d4800c0100540c1c11214038040d65504041d952a180d1248503905141b81503e0010800b41d20410100d0203441110301c0da40c45882c00b40240c070200348001d01c21a44540e43c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 328282410 1250 328281160 328281197
    0x30604020904030e0312040602120f03070c03020f07060c29070804020312070501150f0b0f07050102040b1315030b010c03081005040f0b030609010b062a07030c061707 73
    0x2d0411824401a107002c8a1213843c10302c0280d1519505070105629a0700d00b49000c0d003048070690040104010401401100c0c100b90000c0d00d411201c14541080c40d06410b240903898400d45080011081c841d0030000100e86600268104c10644500d0a540f0040d20600055a4020321419500034a00c1c2200005003880d205001c610750050001701100c685928000c5040b801c1e038400c600c04e89050351034900e00f030341880c030340d00a90006201e0820025062483c051f291403d038010001841010840041e0351004c0c071409405490180c889032046e01da031601c4201d90110320610600c12000c41112003404519071601a00c01c1c4020b004040e19007194070b0340c650390200e41200c0e005000c8c013003d9489810110f000d4403144600a0060341c11900040e8440e010700070103141c240001d000f41c450341c0c10038401c1d10b1030352917440c02e844070040c1c0b005460583d0a1030714070701100c1422000d0341110a20800d0800014001c0e403910b07c0b011981c0b41d464148a81d1080801d60038902c2d822200400402e00102082411028 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 328283660 1250 328282410 328282429
    0x60803180105250b0906090d05031b0f030a02040e0714030a05060303070b090d020c0d080403030513080a0b240906060d0207020d05070f0803070b07230304120809010b03060402 77
    0x601030440c0a0260407000d4400080c0a03403c4192201c0a0a004024409008004403500490034000501c1600c508500c001c1151000074086040700741000b016280348003182090300c1049000051498480c41e002d401340000350014840d030b2015080040105003418061072118a000c120103d6403840c5950301000c000241c400a0240c6406100410054002c1103465410f40d00594552000e40700101d45140000d00d82251000058440d41c114144400081c03803100c115011298982840c6888072800035081d103518166070b00007049030089880110401509004103403107402d16802040700710181d8110010040014148140c100100c440894003c0c5828000340104000e11003001d840c0060590210380f4881d601e600458080d07000102c1801071020042190000d0540070005600300040c41d10307403081150020349018144043d500c03200c40041e500b0440c510b10801800b0241e40e417030a140c03600c04240c2000000100c00100d83e08081001008180190b4600d140c00400a042e5a16180c080180c441c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 328284910 1250 328283660 328283677
    0x120406090309030803040309150e1324030308040b0f040816080f07081902030304051b0105040b070b07020d02030a022d0106080f0f06071b0c0b040b090103060803180105 74
    0x1035180b10010003e070424000f035208602c0b0b0703a1680b02e110300d0045415030004542d00c604007070201c81c1d400b560750fa440b200f12080365000480340104100c0f032450340b0701d191900c9810301c01c4450700b40b0350f002109158200032102d000780c3c8604452000c40c0c1d11644088042001504c008020280c104443c0f001e50184c023003510140b5004519052402022074694078556000071011640030f5804a412454070030340506040d1031207124000b40d0b2445c0360a40d1425194003602c0c4010600268654000c6250303440b400580e4041d00e81081503d5036440c550610b1031100c0d0f4111651401840b0310040306802c1c2d80701000341c030341201c2c0a4005000d021002810203420b00d0750040205c0b14040507400410100409000d26402041580b014000f0010610441802d014208848040c10361201003403004050b485801da0b40110700c45026404110a070349000c0510079110380c8401c011000100d000706011022070000c107041002600c04200c5181e9a40c0090703143d0003080d05400003124800d190f85800d5004030010400136 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 328286160 1250 328284910 328284917
    0x60a17010f020d0c0206010e0106051603170705071110020303010b1c060308030609071e0e01030b0301140712060b0a030903021002040609030309240e030106050909060a0606051204060903 82
    0x40708088600801c0f6001040c180403060384888641c803a454040c8040741c054681c0050030007242d814840043c085118003c96015164181e40041043c54440e91a00e1075006144000101d141071803030005015800c505415a100c507243d03a401451454116480c4c190100150003a6007540c1c42c05600171b041d43c00004d0a00d0310701c1c2d0700950440f00e1400d41e20030600a94801c103a0b0076103c0c1044818064100e40040140041c481c1101c14a00040300309041e400341d1000f00d2030501d507801c40c030000403009080c2c0c50ba1201e0b01507007006d200011140c500c04055206094a030b54410791141d030160010143c0e0a0b81c40780006803242001000080c0c1c0c801c1c0c00c90a00103000e03004550300fa1401e889680100c0e480b550051000814071a002c3c81090303400011407008201d00200c10244000000341c40c038031940700000d20303000d01c100070344a4a540d03103007074119100030180100b07840594030f0004040340d10b4040880e1000307186441c128012605502410544600d080309140d010041c1d070300da40c7c494005041e05803054090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 328287410 1250 328286160 328286171
    0x1b1206040c2304080c0102030c030910052502030f010902011b050312010603020a080604020c0d0305220c030b16021902010333140d06180203060103030f08010905060a1701 75
    0x11070000d50300b412442d65500c60156294600114036041040921100d070440d0000c200c08140000000140e60540710110360a0400c0440f50030180d07002d115809241c42000242140d0f004801304104902007418000e8090301c6810484071505400c881c00700e1383c0280803c020007800f01c5440d03801591403001d540308a0480b40b80004414120050704400d80c02200007e0b000a0810811a44240d850740c10801c2560158200842140c515441d0b140c01d070300840406a40741300140c004052281c072000c12249151048134055524200010b01060346c0c003050301c502c00d0a40c080b5a0040c008515003480d030500c1d0780600041030020004c0d100d02454110141d04142e140c020b0380c10f01c0500d0400d80c83c808080c02c0101b100758030b90814010758100d401d03400b010b0960307007084540001c0c1e111106081ca803507922950000d00341c415800f039101201d6400c00061b402d0320444002104068101c400d045440009403105560f580e600e4410100b40d8a007280d8041d0003c1e02c18204005004506554003014800380c0b0010a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 328288660 1250 328287410 328287437
    0x10504091e0203090601090606021f15031202010b0f1206010b030c0705070f24020d0c0c0e1e1b0406110102090405090c0a0803090916170705031b1206040c 68
    0x981c3c0003510502019017050300100320211282c440c410081c070302e0f4000340034056044d540c015102e440c107121940740c0c00c0d2501d4085250b00c40340d8101d80c000e136901c02c40c0041c2415440e50002e0007440c0b510040b80c000d8a1240001c0182e00d0025510400d40d000000148101e070b091079001d184c0c0c3e40002d08a040300c04400e020102c00170b03d0500460b006054581e03400000a803400c003400030303a200b1818220304064803c6181c0814590302080d10303d046200e50901c480044404e1a20b8030807031216a01c082d00c2c41030743c0010702115541010004410b0440079007a1a4a40c0701d0303404003d0b46006110300c0c0c1048200801c02086060b0040020031040c2401400050818008038049015140c0031104d918658000100280984c0380141c1041c01400311031004601746130000c000700b80981005000782140c2c1c509c144482103428455440300103804d4820804280320704288030041d110750404d8030380c120302240400b01c401c076041581007a151000404004042e05840720f0701072200410315030f00c0310010480304004002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 328289910 1250 328288660 328288721
    0x703020a060f050f010605072d0b0124020f0a0b0c0403081201030201180807052806050703170402100809030405030f100b010305060102250e0a090c0e010501050409 72
    0xb4403140c02600c0c042603a00d0808000e07450103c0c160000d4080c004180150800301d148190510380c155808803000e28000c2d5150440c804550981e00c00508180254001280e00102044040030b00d8030b01121501130001d44001c10f9072103001800e5003120603800190440f000c62180043d50380c00495402c0031078038060312515164115842204061544492080104110750384110340f07004a103880c0c0e40c02041142410811526141548102c40c483c810402c034409940c807880b42a450000646403a0140940da02c40b070291081d0410401900842c10740b03500030440e05020b06440c2c0c8981e130f00401031102241440c0c01a00d030700501500c2d01d460341c80309000210b00e80e00d08000a609074040c000080440c1e44e40c03210000700307031054515418105800c20042c411180d030002034101c07607400c50094051b800008a41525805420f40c0c0c004501d00b280c0b0b4007885100345240c0e21000ba101c0c0034000d5030441c07a03250460b100c92044203100b000d0004204000400508081e9130140818004030a00e410345482c0c1c810103031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 328291160 1250 328289910 328289921
    0x7030f0e0109020118050f06070203030f0c060106020609060403090608130210051804090807022205250207080606010f030e06151008060d0b04030e1909150b0d020703020a06 76
    0x1050a03903481c07081000b9136030041980705011070300c100d002c1007141c18035011820301110400d000f8010403020031404115607090003030f2001c003203440e081070307454110001c26140d654400780302c0c1d00058015140403c10060000c101c0d1072080780c140d114401d880d40340006c12150030000070420b1102d0140e24400000583c1c07030105001100850369200c6446d414200d2025483e0740302860058400c40c0350600c00400604407405407284160100c40180c40c078400c0c000325100600d403468031040001d04d40002c00c440100a0509401d903244501d00d40013003c801d440d0281e075601041d004610039030340f051001860307542c0718288244100c7c1141c03401090000c040c0c11414600481079135040300d04000008500410304045a00401d4034040f45000300d29800c098011448510203800068090804400000c0a0500401d51040c1030000074000c8041580c1c01084900203200b0780c0a03400382603050010202c2c001409a5603c401d48501d64202032070481c1007600c85000b0751040200328154000c0366a4000403407040c0c49203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 328292410 1250 328291160 328291181
    0x327081c061401050c0a0303270803070314090601140607140304140613120602120906040c060201090b0105060a0e06040b1323130e1f0c020c09070807030f 68
    0x1258060a10100c240b450030200521030400c20b040c0584441031800260851006030503090004030580690440110102500400050b50034414603020030070007110011031142c5420345d020000c0046480c0c104543c0c230300c1500e05449691004006004483c024118145480320007843c981c43d21440d6030f94402c034911890807825450308045000c01283e90030224120008034115841803604442c060102d4111100f405020302561014141204020a40d41215051442c1401301402850548602036503010203c8044405501c01c40000900c1801401201580e95101c840171135140e0070f000c1884a5504800c1c001c004208000c44041c075103440740001031020300821100031740e42c1e02e1241c62207003107590240d10003520f4071111404001d042076000300709070603800112a11914030140411880281106000c05003007800340b4003907000342e05030240c64a80c5040c6914424000d20a041c182641c035501201410b5422600080c009000b603842800015408142d9003030005520402400f42011140700c02d02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 328293660 1250 328292410 328292467
    0x81210050a03050d21140f13050709020307051b010b040e010e070342060b03010e060d0609061802040605030705010503130507030807150b040c050906070302070e0f070f032708 77
    0xb0300c80303403240102000f64410402341040d44142d030542d40b01d9903182a2480350f1040c00c0d50100124880c0b078030440c1102d030040900d000c9200d444070360903041402001c40c2c03100584200c7c5480c0309844030301c50600400006901c00809000c0043c6141c5440d0071904003000106080120324002e045c02007521030089080307102e4406507401c402e10400c10142158000d82100394100c50034001003010070003080c822a4041410f64941d0904205440e10341c010b801540b20041056041001c0c242e0031034102d88880c2c0a9034003c071b40a1003810ba5910501d07444034441c1c000d40b40010030400005041441e42d07121407201511801c11505040c1c2d5a80303600700190003042044031010421844541c9203802401780c030300f0800e0110f80411100c810100301030014031501e107509008401c0440e20105040c02800301c01d0051610701541c02403441c3c0000b2030002101c0403140d41c00441c40d29080c9400f0340344240302c2c00c6183c2c05092680f0381050401142e03403450000c644009c580c420410825900122100d01418804610408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 328294910 1250 328293660 328293701
    0x10801020405011713080702040905070924030b04020913050a0503030a06060f0801030303050702190609171305060d060b0a0903020a1703190309081210050a03050d21 73
    0x103000c4503030201300c905290101001d10080c4c403081d9996040a40d40031403400d9039641c462000c50040c0c070074030070041c0041c000c05400044d8400140c100404184030007081c001800e0915100a07029440d500015000315030301e0340010b0050410714180313604030701d90110501d112200e80d6900d07440d00301d03072510881e130941010080c00038520360340c0100e5010707207403605140a0350078000e2001072160005201c05400c05896401007504103001740320000e40c9400c2c00303003951860101c074105500a0f060b414821660010500007031191007480b41c003542c10300380b45040b030700c0d011320f1030f02d0100301c008c0e0403070042c0c003c50f5036440b400002d90400c0400100074013100c40d11040441481c60041084281d11684800c00c58103401c1da9240740440d010040700c040e01407442e06a40c40c0b0b00481c1048008108101c0001c202e081c0002d200410f000515024511805418000d03000b8180c4803000d12524081d2440b00925a0380f021035500709907070007040103849900c1c40c034010503c244c0b1110004420340381441455940310a011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 328296160 1250 328294910 328294919
    0xc1509060d0204140906030d1809061d09070b0304061e0c0e04110f0703180b0f0d060f05011205131e03090b09060a08040309030506151306051f170108010204 69
    0xc4c82c102c1c0319840c1100c00c540300b4a40140401d845050b5a049201085607444180714000034040428000e01044d8070104081d43c0c44c0c0c803c4074001c0d180c600b01d0f844058178900001e47c0031100010140161461901403504613141d5649110203810702e0600d00c1a4078424095004072128107102c0c0f10802c0c0c0203503441c11076484042c0140400c846d40c004003450028800c003d10604d515918080328080c9600d45004034840c000c504248041c6403458200550320840060510304940b0b501c0e0241c01c402018180400c0070580d0f440414103001074920407240031511610020310000d046500196005140003440c8810b80c1041d42d0b113018a208444401207407580a0360f2500505500c052a0b4001e041855155840c04d143c0034005110344c0141c0200c0001c00c5855030020b07081501c50001c640045501100b180c2003800d001c242c054140000030b40c07032406000b40f075401c0100391030340e400384104131240034040c0800030f9400c1031020030351030b86515000103100c0c030301e100320750008000026140201100c800050702c0b41d061 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 328297410 1250 328296160 328296179
    0xa0c1103060907180e010f051006080f061002031209030c0d02060618090703140102250c030b060a0b04080304030c1e090c1101020a0e030609010c020c1509060d0204 72
    0x414a5450099010728200318803200009042e00c203484000c0b854525601002210720041c04084d526074034294205405903081d107001e0341190f4003880031222914a85612100200c421036012146ca2802041e0600425868200394110398020a02403056a03d401c80d0701d901c17544081429a603141d400d900010f006403d26000340515005da060501c0900903604020002540c0103005840c491440b60001001c600d4a9500304400002954415038000b4500100f00350705000303420006444090002440d111003440d00401a502032440c0d01c10603c802c0c06085407581d550202009181e0340c1c0090440368041141e54418002c5c200808400000b5a030350340c1186413804440030190321812252082500a010b030344a03011000090740c507250b100042c20040f1030b0f021170f00401442820081e552000480c2801144d100030a81640c0704142c0866003030b07480d0300d03100600300e0324403000102c0180c1017904525040d00c0c0401c0010200311100e00602c0c185108800021099070000e40d2040880f41d0004040004081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 328298660 1250 328297410 328297433
    0x40b090a0915090c14090f1c0803011a0703020d0815060409050a0e030301030c1701061d0a050f13020d081902060f0c041505090d061e0b060703020c1c06020a0c 70
    0x282d464915068030281c1c4100a40d4040d54007010700c140d0304407a071842161581001c3c5182c42c23002d00c030015400541400d040005620a0003840c100c2064201840e001d00845801c584080e68980d00401502114840458002c00c0140c01c035100f04403c2d10980001e9921403026001030580070a00094034140b2501e0301d01214400602c142680e0002c1c00100049004d6000c00002c88040030003100b1507081c2000c0c01c41c01002250050a140c81020402043d41524000e031103105003202074042082d03461303291b02001c0855040300c2c07500b0707103444002001c401400c1c2500d00540461040090505250f2002082d548229020860400507841001001203125100b440241c0011034402e101c2d1600741000100ca071040c04e60500706090150000f40d101681c0c45466007130302e941e50091070811030040704481790b00251840d00f4081c03190038200007410040e4540503088070310b0036900d90002c0a69840d00720900500402490549010b140c404900c04080b408900050002003034a0b9a0010082c0c15450b20103400716 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 328299910 1250 328298660 328298681
    0x80c010e0d080717040b07110103180b0c07030c05010203090a050d09060504150c0215040501030b011706040b1201050103060c0807020105101404150905150d0305040b090a091509 78
    0xa800c182040442d0100044841040d0800c0e1030b44011000c201c0f443c06540704a6000407140c641c0016403100740007840d010010303032960913681480b0f0b07008032030419044217450200c06000810040d0125051800b124020139500d44203041405502c40c19894150880c0c2040b120000360341c0084402104100007804601e040c10001c2c10b04400b018204200141b03940614080d030b100c8200ea0340f84000d41c0d140907001c07800300b06074002c160980d010000320008039950800d100c1c0c507012900f03000d01010076600800880c403061180e13455800c0341e40d4900c0100300160030303943d1801d908031b01050504000c96600f80591030103107025000c04980d12504400c02404000001c00450440e458501030011115a01d02d081c01216085040781071035070aa100020001c0000300b0000188400d440310025118101d40c00640c4500113160400c405187c901080c040c11001c007140060000303504000a00071446a20b000d0103220201900e540083c1c3e40341c800090403603c4016010f40e1031003514070108144035032406010b1220 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 328301160 1250 328299910 328299919
    0x30c03120f020a03050d06170106082112060a05062101170a02040506151201051c0503070f060f0603050609100b1c060f0c0503010303030b0103051915080601080c010e 73
    0x4588150000d440f0f1070440070040421800003110005118aa080b00014108e106001c10100e000b17000400d000f8156846040000d00607848038030004140c0307000f8585400710a01100b0702c0c24000c5800207082c00700c0140301070b9101c00f10f444085825141d0303c01912505c03d4250003002150891000152000c005910000c1400032000d00d81d140040c0104d10305030490340c195004a00d45d252540050b483c0096a001d0001079140815024101d10704204c2440c1250010303500309070310084803010080c4041d034131600541103600810805000850038000007024070b024803c00110011804c1ca4503090300e519600541700d681c402c0c8140042d2200c08e000030030034400c206070304020929801000c114480908205c036500200c0115603103062241c0d68000c0d0403d845008400c1010500700071025001f40c1080c081600000c1c9000d42414155010303204060050552086882520550088074405010070381d00e003200516000304001245a8108900c6010700384d190080c002d0040f40200041034442c81071003040c0715 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 328302410 1250 328301160 328301177
    0xf060e0a121e05160303060810020702040510030c030b090f12070b070c0506130503120709030b0108070f17030d0608011a030102041503050903070b090a02010305090609070b0c0115030c0312 83
    0x100b070f00142200c080ca00110380c22104070701a400c00340c000705090ba00050b0300f03015011081c2c8041021703a000700411442103030104440d031078a40b814015007005000c02449032607078100504c0416180d030080c40d0300a4a00c000ca5007003044d2000c182d8203100f84e09000405a143c0403960b1810000d04110403a8003803894580101d14007003644505035641c0c2c014044c0160552111954414004244121351003103000c0c80c0782002c98146008010800100d42c4070945451000070004030326160701191100c200e03a551000e0f0b100c5a82441c081201580c0f089a0b2084144020407503500c2203000c501550006085180c000140b211120001000360007048001c14401e034410407040c000c0312600d580350815001d442c6030004a41d902d102c00907203035128000e0094650381042d02003000070f000008080b00345a100ba03038140465160440c0b0190384100c00d640601890b00b145030240a04e84264000e850080c41200001ca640d507401c180174040c05805400a035070030100c0c01400d200303001e0100446c000c00e103140d2400740103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 328303660 1250 328302410 328302467
    0xf18083106091202031c090e090312090d020a06180209270f10020a05040e010909050c0d1109040309090c02010b0a0803040b0307080402041512032a0f060e0a12 70
    0xc50366416001b19448440844544080c6449094550040c2c56050900b0410b400d108480a40d40d42000070301d070300c84090a42c0003034916200071a40010807655a0020031075507004c2d50701e660140c121412000340c60000f0700481c101580c0d03100401401540c3ca054115555000800c6406900d03400e19a0a40e156110180c07550030141c0c00600340080d00013840d001030301d80c0c9403100300301c54900c00c9030b000d02018000302c4004101900d80751b00c000c0c0d20320300c2241141c0c0458010800d010407500b44450160402103810100081d60420008265016100f40343c240c00d9035071920000c100316004103c0000c0180c2d501c031741c0c269050414100354005410718100441c28249003510004051000a100000300300b20321002ca011500c0b25004000c10805160640141030b07286d0209621107541c020b4183c0c00210220b20400000110094604050010202d104001d92503511202603009a402040319101c0d42e4045001200f1000c6c402510310520800d4224107803207029200502c50a51045000801421844040d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 328304910 1250 328303660 328303663
    0x26040314090a030b091c05030106031808030408091504060f1b170705120409050f100302090106110f010501060806010906030b1c02240d0f1808310609120203 69
    0x11641e01c011203c4466456051603810700341e100b05201b07044a2608205280320f034118003e141a5001541c0400281294400c0c060107507550300350107020000308001190124032003000509040c0380103001a030716682c012803501c146900c10742c80403001407000c0081078a419400103d12980900c20f440100f125596078568000303c4852031025070b55007400003101c03004c00c00e05119184031680b220644036240c0356a03080d1940901021114180303e26030140004482c070803100450b80a07650054059405e0380c0c2410015101c200d140c4034100141c0c031070001c4041c400902402560301030400703942c48003040e0400c2400074000c50480d801420a03d4104a00b124280c0c0b03507031507810409610341c20011f01c685004d00216403185094901c0d00002c60007004100ea1310b2aa01008184c11101400c08003d00c0124001c2c0300119014095508400101c050320b450100c1ca003080076040761415980070500303122401d00503501c81e00c160041282d2b10b032040c803410403403a500b000c010300c01400208042e4094280560019 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 328306160 1250 328304910 328304929
    0x7140f060412032006070f020f0d050d110318010506101b0204020408010c020c150c07052106040f110405010b09130e0f030d0b010504060507060506012604031409 71
    0x21442c0850300100c203000d241c81032181161006a4160b9005801c0b1303902070b940e0301ca12088401e240464895500060304510009858840004210107010640391010f03040703400b0362200440310740f4180c45c0c62040d21494901070045000314000320650211102407000f05003502c400504091059440a040345e4005800841e034001c55407408a0b5161004414030000d002409550040840c0d907203840d64004110f0340016148540d07141c110303a040708108003030140020a201b015061f00030b035000182d003046242441e032610048068240e41446008290000d0f0303500d0140119401d60f10925071584c1d00c801d001215031280403100095800740100d606040b0010000c0c410791100c80e0299001d0507140c510a40c02e5800b040380091444241c8201c1719500c2c41c2290789820002c004000b55140101e454060b6003d00c04503801c4071590b4407407608012494480a000b4500148143d0501c0100c00060a00d07449806214a0620010110b0401804c1a003401481030701074440140d40f401007040700516a0b40d4400b0300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 328307410 1250 328306160 328306169
    0x10e06180604151d1e010e0c040203040609140d0e0a0302061606060801050108030a090b0c0c060f070203030f04031b081b1528180501050313021207140f0604 69
    0x86594a0600600030f400130003071501c0d24980340702541a02c45207000042890080302c0d5484801d1485614007a012500b00c40c009015468682c0c48861041001d007800c1c5c01450340f050240d50000380000164072524180b4160090f1a11150001818603400541155014000700802d440d08003180c0c1c1160b01141c0daa106031400b045030318061448400070031180d0b801202c050b00d00080240440d59482020968076007103000e00d000032951610001c5201c20070b91043d00c0b6074106042c0240940440c41e014800c00c1c0d0700010f454040070a0410000c001758400300002c0c40010041c60800c2d940314594100040c030101c1980ba000c6128000c03020400403442c00113181d11200c0751010101072a07080c42c20014004114451151080b110b01041c0103807a03028503007080c0d034a15400080c0c81485403101c40c1c101d603404a0b80d440c0400d041c0903c1018407040d446800a903901800c0c00d4141a400d900f075400248003203c41003000e104551000a0030300810a10340c2c6010290401907a03076400341a104400590301d40a14000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 328308660 1250 328307410 328307423
    0x81003050a0b041b03030e0f0d0209150a0f06020304050109150818010906061511160e0c0405120a060605100804141c0e01020d050703020d0827010e06180604 69
    0x4181805440c40040302001c02100c9040d040760703034034540945000010b0189510603620240140300500f0f16271155241554018407001d0180d446200402d02c040310000a160400c044150101d0106269000360011300300c1078004503269480e000006024400d10740100001c243c4540c100c4074205e41110010317801444002c0307840c1c403030021449000c1c010101c03010003910107800e2400000e8041ca0000e00c3c0302000e00141e4400d880001100581d560b40d88141a240d03070303640242c2c0c00400c05e034070500048541294800c164a444d05560380006100c20b907417105850960742015560501b00038052140000410381a44c0320044090190310247c10100700600142545040c030203100b016450611204501d101e01e415164030400400d14018441b5518070340c068050310401c01ca02c44524090004e0304d13500f0303901d60b00800c0d501c16003d00840d21610040d1510034825591414009020466000c042001c0030000000410090160310341e0b2410300c7c0a0514401c01b410082034002c0d55401040d220351140d0082d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 328309910 1250 328308660 328308683
    0x60915080403030b0613030204050c0c06010b07110901032102120a11032109010b03032506110c011a121c0c06110301321905040e0102030106081003050a 67
    0x42c00d0300944910808182e00c52000580203c00e41209101501a0381c02034078100119a40c507101d6123414861a000c2101d541d10002c010010b056140d0b00a05a481c8a42050200206214003080000344280c104813000b00304211811114800040608520700082c030040074003000c00e40c1c103100c00f0301c81c0152035004c1010384444001010000c2048800640c0c08035004410001c820b0040511a038043d1008d032425400d00da0540007918002054407401e440451200c461a520000410b0040d0701400c01203410310344910f04441c4642001005d802a0b04061002003903c00c0802ca0140030f0b4107070b0502041c07090851181c075020b030300400a00d24048000f075081500d95800003000a03507403c028000010491800d101407c0220711030600698101c274040e00d0141d40c0c810443c2c11080307810700e405240c402d0001030001c0d104282e162410000c0f070741c5031054000b410350985907030108068540300141a40d290303400000402001c0d60198900c5c0c3d11004086920008034115a60b01d529030743c0d2540c01400301401030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 328311160 1250 328309910 328309913
    0x90a1a012007060c0201020f03030c0d09060b0a080d09060c0c060c08040f0602070e0106050a080402130e0a06020912120d48050711040906091a0103020a0609150804 72
    0x1644100110030440200c400702d6507103000040000c005180f049005000e5041014801c0d580001968081c0e100307448044c2c100746c80c1000307400007820080340540d81c0310b8072002501150b0f100c4414a02c0500300240150030440300810002c2c1216103658843d00130010412200b40125a13041e642c1c02c26a0740515014000140a00b072600c1207001c0c90700070700648141000001200c54000880c08103c0343e00d044d01c2e121580c3d1718142a031346802103c41403000b0440c0f00c000100140350000c480c00c03801c04a0800000e0201c1c0c8404e995140c40707411241100c031503a00045070811031400d00031500c07c0c12118401040c1c0200746001c800d000d409103400c450b21158940e103910300b004030210400001b903000c00910b00d130426400040004010001c030741c0c041c0d23150b5403107140041c03e5210364120323003845030407141d0100645540b00c1400003d044192003a50000e82c0c480308140007a2480c10302c40392200094170b4010b0a0350450042192003049540803a0901031030910820030050810741a88c2c00d0f06e05801d03c0707200ca0b5183d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 328312410 1250 328311160 328311197
    0x80601110c0906062a030a020721060905160f05090c16060203042415050312180402130f030506090a151d01020427060f05090a090503030a0b090a1a01 66
    0x4260001c40c0f103001c0d405e0144c0c044e20000003400201040b0b50868020580c0c40340d100041280718004808031541d12206a0040b8040d034002c01001882001180e0200c00e40c20548010340129800c0364150b048029000c200c1882e25510349500074000c1e0406c6458015451411059031003044001080d07250040700150a1103808130100f1098500d10b03e0003840007405102c0c18005107403401c410400304d00700e803034081524100000d0f1a1030141072030000354074020452010031980072110840b564055000c0111071910f07020320b010a0000c2c441000841c034000d0840c0362080c10050010034109603503000c0100c00340403d907864a00407010909070300018468004501101080b00d10344164083e9600000300001c401034045c0781054100790860f8441c03040358650f2000403c2d0b814500c1100d0a212222405204c0c920346038010035085a04003034005818102035407200d041d40c1044500c10310080d83c400c1c54448a082562a440c0e1001946904100c140307031505408040f801c141091034100321581c0302c2d500c0351080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 328313660 1250 328312410 328312447
    0x20d02011d3a030e06070201051b0c190c030b0a0b0607080d1d062a03040b090f0d0302030105010311031b090f090a0504020a0b030906010608190903080601110c090606 73
    0x40148456141000c02e48010b03018010819101420344680400903a0384e40c03042c460903016a40b0324460712000615143d5292140c1c0080c2c00d4060356000300d5803c00742c1d0484104008106512809140c02114610b040240500e1802800d50441500380611031016507034520456039a164000c111940741ea820310311050007410b815541c41401000f03510400c000440011b0114030410ba041e600c1e42c1010705441c004041c004a80d03050266250040c40802c00040070001c010b54003100440440307d85004840c00e040c6807242c41f00411001c41d80c004018041035074580a10507418003d0099145142041c040310b03009520752040d2040b880c40003103402c0789290746000e03410300582c0e001002d100040c14901102d40081c00c096808a03c20042e03100c0000752040900183c078031521100e800b4008603032138020141c64041c0b0061a0710300d155134203000702492410f24852401d00300d01036604c0a0084c503240340054030000607496a00029800810760078415500c480415902c29400d40701140c0f1001d451044290415 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 328314910 1250 328313660 328313743
    0xf07140f040e180d020102160b150d030f02010c0807050717160b060a0e070203220f030308160203160602090607020402120f062409010207090507020d02011d 69
    0x40d00c5078140182850414000343d100403102007070b00c0142005100070380c200c0c4108483e500d41a004031500102150341580d803198400421f0201c02d80d1031280200044501602641c02c4000c248143d01a5182d030b64240b02c0d184403482c036424a210ac5042c00080504030707003c2d800004091b4070038441049007013042c520503070304103840100100d840c0d90711510700526001801c07502240561504940000d5000360050101d01a4160b078018626280d071103500d841000305905003003214040007000002d00340000049600066000c0d07034030103140d400c4c4050600501685403002c0c00c2150b10600c4181004261003c01407191588260016a100740703a401242c03076401480c0d0081c1d84a48003082040804054100840c440c0c800041001500c2d9100d40c1000380b141d491002075070b02c0d202c140020281c207180b0703503000f401e2178007050044403000c0f5600d084d580160350040303624000681086402c06640e5030240103481184140103040a079080d001c4c803006030385504021a01d100e0320444030104c101d0301c181254000312070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 328316160 1250 328314910 328314929
    0xe21010204140103050624072a03020102011815021b0a1a070503131106160c052d01051b0a061d011406040b0f030105011d0f07140f04 59
    0x7955207800b20b84606240303182c058042824000020308503c0c040e00e00d42c0e4900704222880020340107815044505030442402124000c11282006d0340042074120014200c200f842401c0700103e05501c0020700f5264864055540807140403403040009034440c6045098503229000143c03240f00e0542652401c40d01991812451b000d5034450b6818401e038030440700700c01c1160603446181c0d910717024012a03a603c002c03941c040c00b81518a100c0c2e00022072004101d4074080000b4442410300552801000080c80c0c1a18122604c0c04411030400240c10f001e0202508111446400700502c2d002c00781c4c3c403008a4076401c40a041086c0020302e0202c3e14401e40f49608a0024042114910f85e01031070414024001401d0b2652045a84440900c09030014060b8880c040b940c01040040340d1103690a000240102c5600141e2000006150303900a880901c2464000c3c25900e001d5000464021100140c0c46070241c2a000e002140d40304100f8160340041e10a496150302000031a601c080e50b0500240b0b900881c3c118000b00b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 328317410 1250 328316160 328316167
    0xa0b040e06040335090106030b0907121104020702040e1e0a0804140d050714010216052d03031309180f03050c030d1a0112020a020c04090203071d07030b030d0e210102 73
    0x1205c15030160301a244600c82c0c951701d903107400303042c60b9640074144100301d80702c0c80ba085880001501d81104c0407002e1800781015050107210b50015082c1c400c500781401e200e6104100360402100c2d11020070b0048070f1000090200401c09494003131051180d0700a9140b003114221090640d601c420042001050700039060784c8001d82c0302c485d40c25004941541c19070041c41403100d00c3d050401121042421101e0080902410484141000013068a00085000c3d002c801002906040d2414002000404d18100e020348032a418000d5401c129461914100704011407038142c240003400c0800072441080d09030401c00d4850070340901d1a03240d4803c54100c65855400e2022405000d8a000d4510030091000d80382c8041d90010001c24404a01840c0d2200d03005901130398805003541066409995414005000d481d4416215035401c01988100800d04440e0480700741040ba00b51b60506c61a84810002c4000e00700c00c0625100091001c0c00c1e07040261711591090380039852199103242c0300701030480720310001e41d02c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 328318660 1250 328317410 328317421
    0x10050d1502030414060f13150f0c091d010e040305071728020f1902010327410a0210020303090d02060c1b03040305060a0b040e06040335 60
    0x7082c040400000700c0f248121700100700c112441c06021482120284c0110410303000d5a204c500c0c0021519020078040c07603031031100448030f4483d402030040c0840341740c8540e6030072440c0949080c4180043c100c2d070900388600900511400014403520303030b00171b074040c074001d5100c54070b9007019400612119142e9001d100f0001d0401d9440512003040420494615080018100d001c40e003a80c4811401641e81081c0e000041c10202000300340a80c3e880f4940180350016508000c8905069401c0c406040b007a81c6038800003000b010025508001c0c0c3c41c01c44400030001c804a03a06142200c0000020707032205649507007812100d00410200030181702c032900140024060320503a05c02940b02e9000740c6190a243c02241d000b01416800041e5540c01003425040207890004410440040250448048641070200f0400040481c004211039406055814800a04607441c1010001200c0c401a03070083c450b0082005c000c00311390014000c40454001c0c868014410b000b50b940084810f40a50020014482000038400d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 328319910 1250 328318660 328318673
    0x2070b04151706130e030f0c2811010e01030b2e0203040602070b030621030315100f141902010e06060f0a150201021204050a0203100510050d15020304 66
    0x1250007540b9040c082d8101d00c40d441d04000011186640c100302010ba02c54011003190340820014041c02d01078a083c80301c0c0320b068002590103c050102a5400301e080c042d080c00b54800380ca0a803000b40b007031428140c06c140d601c4c03154000150030f80034148040c000100e407240e40203820030104032000030000385007056800c82043c409446400034102c00321452849410a0740000100c9041e5880c1c1c3c0c00508805250800c0c40d01ca950004046680008046100c880d00d1040d1543c20403071812464003440c0c580c906981100c40080f8440c81c013034030a040d03e60ba110030303a0380c2000c540f020301d03049031405c80c900c0b4040020050482c405c082c5502c141070058007480300d103540d040d0300c41144007900e00251354007a160b860400444000c17101c0b030580d105032104010402c03180c50000400d180391042c0005810200c086080c1d21a08504540a40b0b90741c0084803203c0c00c6180c00c0c03064101c0a80000e008020ba810009640d001591b5076000c1e01c1d000300c2446c501c2d0014000345900c003094a00ca500740075550385c0351515120 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 328321160 1250 328319910 328319939
    0x604080a1101090b1e091f0f022d07080d0207050103060b04140d030c0609030905090f01080613050a0203030403060608190b0a0203130b07030515090c180102070b04 72
    0x3a100c4a10201c0344614540c4603014900844151260345410300304140b94410444807184d018410704401000003080381e0310b4007244022243e84442d000040e545031440064100c0c0b10212510f070840d000b0030405040000900206003080106032817030f104424078261a00d14240c0c103a04442240e01c5141e6070340800690000720308058131000e99040c000075543d9001c1031030307502403805492079001007a209560380307081c040044042c0502a1030050151125074880904a8503409415000a000b1a0042c801810980b11442c0c20807401250850550314080c2a2602d406000c1c041803550079000e6816001d00004011803016036800900b0b07039070750b69580c3c506040104050320901e005406600e4031200074448140040700c1e65900502c40a8155450703000e604000c0d44018240c0c032225801031b00c200e0114107094400ac0c400c10781510b0000c0e060400720400203100303841c980c01c0340c4a180101c0c20004204498019110900151900d61800340da011005034245880b0f50014000c9081c00f040005a1001c5c45145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 328322410 1250 328321160 328321163
    0xa0507080102040510031119180e1509040c0b030601140f0405100c0308070c0f1e03090906080309150c030f07060b0108062107091409011103010e150109050604080a 72
    0x2d1100c1000020903401e1f640c0244d200d10191605002d02c25400c035118801c0c0101e0b1344070f031410450080c040d2302c0081051029400059044202004011304240440448082044101c0d40801280b03001c0d6140c2c0081c00075030240e24286c030400300c0450040c4e4064200d15407201c2d4410705881d11040291500400341e00907100c4c880c40780603401c4106500301e004081c84000c00e50140c0c5c0b039982642d610602600d001c20340b540200ca004100b5080c0c50040750500c0d17080c2080c08001c400d00d4101196a00303000705442680e400501c0c0e0240b13441010000030100000312282d500050b215080b2503101141e000d81c05000b030a0504000c1d020001e204115201000c0050640d91720230325081020b032212070011514504100d5030150400780c440d110540b813540c6011000d03100114981101e10007503c80c0c610300c007640c1140002c1c0c03004544110602413003c2083c001c03c1000200361078002d045600d0100d075020480380280040300c50201c0315813001004d9108200002c0645809032180e41d41d66a103040d03070781d55400d51880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 328323660 1250 328322410 328322419
    0x12d200d11060a05100b0f13120308090c0109090e030702030a05030408010e07050127030623060904030519180b04031a04020f0411090405040f201e01020a05070801020405 75
    0x44400703100d80b00d80317405484000340119020b4103058280080b030b8840058624164000d01510308440b06112429020304000f1400c51111502490094544800500082c2a50300b241028142d0350364031001d1201102d4000c3d03808608203042e000310604502ca50709001c1d41501a464200342440400401041150504e00c001c0021030502d03a1825144c4030240203d0340081d04255004042814210445917845d8418039501d00880d52962400101da84070b903540031000580c40e44100c84514555111035000c4801e5a40820364580780d58005c00b64498008541c880c05081c4c007400d0244c80c03090350890402d01c40000389201041c0c685100603002e030098401190030710f091700719061080044202150107240c0c0a81041c262030b0f0a001080050201b90001107101101801782540c140e070307540941d0340102d00031500665188207508001464048030401188034606041d18045030b5165840d01c001091114821449003415000040b0700342074038401d01174550b202c3d8650110314a201940108100c580440b07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 328324910 1250 328323660 328323673
    0x1204030c0512041203080612011518050402100c051005311a0a0b06071103060c0412020f1201050412030e0d0504090e16060c02012d200d11 61
    0x5080020ba104601a051a46100c40590400070340100c100c40d4100070000d101d1103000040200150071103118920401c0c101044030010401031448500101701407440d0300050110b4030303143d000704800000c1c0d9403107282003080304501b4106011082c8042000d640315039100f030000b428414900b44281d600c0e00b080c120324000e114405411425070a001c050705960090070016001c00450b00000801c034010b008500c800e403540d0111a269564100a12a051207081c403007022100601c145850118014180000d45008110502c100d0040004204480e50304440007052488000c0102c0c00600b4100b54400c42503092605100421007800a807181d84103031a581000451400c40c3c1040e47c0d84800c101500209604100074046151560864003404041d4030440c1c0803c0b0301c8080111030425680d10400000e041100b04004540c0e012940c9603041d0b503010703101d819000600300b010702c501c00941e81c440148013001c03080091743d100c0402040c0004000070f05a171400c2094843c050005260350b4141c1c541e600404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 328326160 1250 328324910 328324933
    0x50a05010b0712030f1506021e010c0c140325060f1b121508070905070e0f010e040f0501090b120d2705063408031b1204030c05 56
    0x10016540e103541c012a03c01c0a2812824090300100710141c4a183c0142d201d4000340b6007805450507900042401e0741c0105148001c081ea01c0e9809803101140b4000703641440c001d03c400b00e5018000011391608000521951800040c01c1482c40c420417407200c021303030400078a513048025040450702c08540a003806224503141e02c50f1100440315808005032b015460100c1040c7c0306441410029086e4941400026030102040c1c3c4040f80300342941c0c00491194842541400038002074001c59800061038107102418520040001d400c4101506031681003025881c0140030550700c80d0440170340301c2c9c00300c030381080203507100c00c0001c01402e040d80d900c6004050159030404860f00003d102e2050100070340c0c075111880c3d00b040e240301c01c0c0d18550014803c0420798041c0458640e0301c1b54000d20110301c43c80c0d060000801b8a00e40c032100b044580451017a091440c40e542030104070b4000803694012000245984041c141c80040138017030182c08030713200110311450b0401003050b4000c4a8448207d015004440480004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 328327410 1250 328326160 328326179
    0x403020f0f1f0b04051602100b101d0a18060f0e041113050c03061503060907110307140309010215090304050907110607020109020f030a03091806050603040303050a0501 74
    0x140e0341c50501c9544a11180121040540c855a150340e881020108040040d0800502030303d1096450b9100400c008136080c1c02c158040102020342d040c40742090100e054540001955140e03810401d209000702c804569032040c0001d441048084002000001d606407a104070100503940881d1803601c00c0d2a10750041000411200880b01301e9a000f00c1074141a03031035603940701c5154401c1d1800b40e01300320240c0c07414208140318001c0e20710a4038115005038403031804030108030842c1c2c4441d48920030308600300103210140d00e41c1e41c0681e5000c1b80e203081241e00845a0107155246101c0e07444050f00791540e0801e010b06600c4088000c09000909900301c80c84000d2480c40180850000c4d98814030a0f4003c0100300013034205012800c0d440803c604044402c0c403c0d041c98541001e00c03c640f080300503550380e41c5c07000452070115003a09020100703400811214036190f030054000881030187c40d40705000d07405100752043d034035000000501009031403180c49040c41d10f40600900f6081d100d5440a80c148000822442d40e03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 328328660 1250 328327410 328327423
    0x7080a1109130c02010e03180406231e13140106050406020a060f0b06120702011d07090b0d17030907050f060301060f120501330f050328050403020f 65
    0x204602c0840c0310788005080242603403100007007076540301c0568100c030f18824000340424140940340031481c03c0d0050108411030783d10b5041322100290010411000f801c1c2e0318441c01300c4150a889060706028503550542d046200040d0039503001640d807082103202d401d140c21034202c18041c1c1c01c82800c00c2e625010155914061030041c100160f200722401d001180c02900207501c0c4600e800c8000400c6080070300400c00da03600284180c81848217990900401039824403860f1510030a40034400c5400e0707079041c241502c440b010b1045c9000d1f01d484449680302a954030400004c4580c0c0103c9400e800b4171601004030003600b04a030b122000340240c1c4800180f904014010007101c06000b00340a282d070f800d0a00c00d55828030500c001c041008075200000c804280701c1d100ea030b806071200c00101107100d0341c0d00038601001042d0660020246004000c40411160080103030701c031010a90410980303a81e0b070402e524801000143c00848a1843d1000b80c00030f1074403c0c2e028038000d038040c0c2d00780e44a10604500c2e9039070710314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 328329910 1250 328328660 328328677
    0x90601030201020d080c0405060d0b0f010f051c021c0b190807090218030d02011a19090506060708070b0708090d020d08060109050a03231501090513060507080a11 71
    0x7000303c00c040100b54820b41c0317071640c0525050007142c101a103c00c00308425801100c0c10504059540240721349900d40b290418140d20800d180c01c800b00301d000c078001400da0003003244c5502e205000466030460341c2456010b4400c1000038150100c0c0c59000c5019507000b8041b1501c14a0040b0340200c0240411700c0204400b0081c1c030b0500c0000c02e0305601d848000b500961040c0c1807800c0401d400d103170031032555500788608417003103500340e0011513200108200c0c01d103160001c958080c800d41c01804811400c0740000d040f0030440701c020b100020f60703a6a03100480c81901c18408024048200000c6601c00c1010505c48240500c0c0240d90340400d0f941ca0204150f5111000e425601c05a032040c01c0314085a4413980f4220341c03041c01032421641c0180d0b00d001140511015800450ba084111202030f00c0641c0740c100b640e40312005010050580f50401e101d4000a03c034107001d00c0180b0341d1504001505214440b140e102516841001045a403410410051420308240c032150b14142c14561011145041c01051b00c4008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 328331160 1250 328329910 328329913
    0xf030115090c02030a08220506180712020109030b04291e060f1e150c0607181815080a0308060619110a0c1503060603090b0606030414010c02030a0809060103020102 72
    0x244c461510a40d04c1e54124041d54018507d03451047c00003a000f48043c42c0600d90009a8003603100c40341003c941030003030503080f031581c2d80c070b8010281c00503070b07031100b51641101c2c0c20000030700c56601e90741400400c00ba40980c0990102c240c079150304113048a0940b1491064040e50180038003070342e0410b00500804805d461199002d480c1d880c11524910340030580f894045c01c03000c4644138820440c40402e80c00021841544080032020402c2c2e100400180a0701e03620410a280c1951000211200d800c6134012070302400c00c28041c00d048076115440a83c0c02030f18524032480c25103041c55a03541a00ea0340344407800c41180050950004250f450a24009650742c000780c0152040c880c91121004403401d00720905440841e00c02d41e483d4001280e410300745040942001010105c0c0501c0a803000740540b41d05510030410180340c034a400c00407540c00d800c0d158114608481d0b030fa9a035252814041c802c50300723820040d0707119441c0c1700402c6641a000802881c8025080d11121000d42e40e440b641c986807542480082d015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 328332410 1250 328331160 328331177
    0x114010e0a0216021306090b090103120807050936060306130512041509171009080c0d03020307030605030a0c050409080d11040927060b0f030115090c02030a 69
    0x81e860303000b5100c400040140a150b81c2c1090300050304244800da21038444a9031a01c0500c400c0489000f220210b00781aa0004a59450359690210584103151020300300800c50f0089000e04d807113002240e45c100c0c0002c002d01e10955080c0c001c01c0403420b9050713030180d00441d10720f2440c80d003d11400e069407040000601620310359139003100ca0544800c1d01503086419004c2e0f0f0100c090030440600281000d002c00d01000c0c401da01d24072001030720000650704804da548880030044541c1c01030001c0e0741c80348040000c901107500e196518052040703014640c000c808500071000300b10100d59047c0c0c040d510a01842d6400c0c4580783d074238414540c65009402000d0b000b80b003020f1052120b410075412001110340300342c0742c0c82c0c50b01c0c022515010455150102c1f11070102d10000c0d00304410549400780d075002c0140710000100c0034440d01c50600c150349254400901981c7c80786000c1c401c5948090b081c0030a894041c009201c0540d81d000101e021703a0340303406500e0341c062820303001010740c5200000f40c0310b801c1c410780c4900c0311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 328333660 1250 328332410 328332421
    0x72a0e010609090507020c0f0109030c0306050901140c0421080a030e060c07021806190b0307172203021c03091505060a170a121205071b08210412020114010e 69
    0x2600c2c000481a01c9c10b020041c40d0000001d4042d000c40c05c0114010306000a080c107064406a0a440300b202111410703481c88020300103030800c81400c039021650b2081d071140140e40764030701910000d0b0440c180500600000301349004420b0f0190800c1001071f064005550003030340c82da44044c0c002d000c1c2c600065000520480612482007000020640110300145150300c2c2d5001e8030741041106696400074400c2403004014090525007050b07440241c2c9001110412451030302d1180e10310b40d9203180d04001e450030490300c40142414020300140314480b00700c40b8001a1a0400103024000c1c049083c021981200d000c11414441c40d05449140e004110092449040601e400081c21075284901c1d0f45c40c4140c003c40c0040c0d80052180c04403031a0707240341602c41c0014240c40d0100740d4101c0700001c200c9801e2180580786e18840682c6030500754101940301111039115590035200c880700345a0301c045801d40d030440005200500140d1000442040c882e41d00a000746000a54070b040c5015082c4100300700c040b0a90042035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 328334910 1250 328333660 328333669
    0x303190509040917070b07030b18060f060c0c01020f01020c1c050918180a02010906031a0901080c0316120201030b0f030106090f06080a08072a0e010609090507020c 72
    0x350442000700b0210355045241c56010303128885111400c04e80100088600c2000790103a41e069004400c0e05081142d03480c803002080d01c0711241c01031201c0000660000074459034445c015075180c03003400741080e82c80310708200078155503800c0c2002c0d417405841a81071085482d03034140221102c04040001501e600918103205844140b0122041428031400740b00003c569124040e689034030f10750b50207405045042c4904100c1e16007218020b55061a0401d04100000d44d800000e00411500307603240c0022454030800b605100220001c40280d80005800c00014003403c0000d010082c2050440a07144000f091603007440d5000658131a502c848011040050701540c040e0b80140d01505000e4500c46400e10004000b90841d611034000c0000c2a985245141200e26148517580103080b0702c070f0042c403000b0030750340b141000da004036a001005500d416003c5184280c04109000b031000c10215818011038540c600c00c00d080100340104000268400030008500d0700724003035030340a4842078000d0100044080c0620 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 328336160 1250 328334910 328334917
    0x13060e07020712320a061407020c0d080306010e0a0308090f100905060d060806180c060a1b0206040503060108010c1805010e1509030709020c010c091805040507030215090a0503031905 80
    0x1065401d101c10508a40303134006002c0924580e03c00c3c2400142094030100301181300e40043e0a6004552014400ca8900d444204000345969000340c04183c0300d544035001261280031946545820580a040c00420804280e02500d807940c1c0444404000d80700140a000c2d2803010050b000c130014100e10310410540c2400801003d088044180100c3d01a8640d00a2032500744151185440c4000b02c0d0300c508280240ad00004000e440200e803420b1500d2242d100c0280040200d203540704243e120044c84038215510755049400410340501916155a5035001841c001c01c18016600f02150700398100303000e58031b0542503420640d00142c4034141024581006c1c01000a0103c46090109504121460482e0340802c126130042c05411005a5030701401088207094956800000d001d010100a080c016041c0d0907510310000c10164034002040c0c1d485007002c9241a80903440650401c070032055111000000c14014084200151000d0700ca0503a01c0080c19500d02c00c490340f003031080148000840100d4401c0009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 328337410 1250 328336160 328336223
    0x2a0307020109080a0806180702070603020c07120b0a1802010504090203060d0b100614090607030f030908160506150603060402070302071a070b07030606020c0d0213060e07020712 78
    0xa00380b0643e50b400c501503102007031311004070b095041001341c589440103201c81c4080300654900b5140c02c02a002942d00c5110703003d100c0c02e054000c07400100d640c40c100024401404520044540c050060900c22701014041d01e020024070b0401c3c1c05040400108255040e2150741070750b40c2840c1c0340c030385001c0d203009400280c2129488031082a03818003040b995000d05020b4080c900840008500c3e042c170180cc10410110744100d03403a07091210181e15524003060b110826014100a81c03488029001200208080030740100f4100012490992000c10340034240450784c85101103c3c0309440c0c245921141c0c0022441203035019004100007411800d00b0b03006024901d220b0b0045030441c84d155a2a070034002061903840c03640180101e5a0400d1009500010750403021500f01080054105140251941c1220210764020842c01040c00d00f1901c43c41802c04d0f01900e20300081010540340c6c091040c0104003a2884801403050020224820300300c80d0030328032400d80c00301c000384220303660241c0a0721081040b0707403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 328338660 1250 328337410 328337413
    0x9061b02040e0607030b010f0206090604020d02010c060204081c03140a020d0b03030d050a060614090405190c1e020111190504120b0103030212030f1915030c0e2a030702 74
    0x803554100a030801c486402030307071641c07804902241b0f0130000400c03203101c0c1d001090865001005100c801c40780840c05a0704160107881c0c48031700014500040c2d412a2415000510b0340c0e00c00100041d41e5100420740c0205c80510382c00e4084989155070b030071030582e804010800b00c1407840c400460346620643d4004d15503450b8140000c90010034080000341146c100c000c0765a0700684940400c20308110510861001d000300b4241b48440700030055144200b4055001000d020326902c00101c0c0003420f40828042001011140900c100440c0150040c002c4002c0c0401c04050105041c164140e01d006021f44001c00405800303160400d5000920700007908400e00b81072060180810000c9102011780e00c50006d114054441134840d03515500d002441c0800c4c401130490407030424030a02401c122400c007015042200608042103000500c480d00b401045212a000f03140604031800208121405424500300d4000c00d20300091541c80f0407000141881541c01908118a5611301a82c0100800c015541120140c070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 328339910 1250 328338660 328338671
    0xd06030c05061908062202031f030803041217040302030c060714070f020406030501180c060c030e01030905070509090706031505010e060a09120b1602280f02130507080709061b0204 79
    0x500301c244040da031841b1515141c000080010040d0011045140d034102096212036035803854548251a00000c1c100900c107010034145003016502c40e404180d02c00408840c2090941460301d4065500c0e4440c0b47c410005005940014040d03c0c0a1040d041c4c0d40306445030308620f08452540c450100a6540e0700c1260b00a680300008004120240f25010000c103082c000c1d40400742c41401c080845003d0303984240e0800c442501001f0020342d200c16412103200c0300b8200400c9036142850124109045508044d80103a1504204031088200094484c1110314545082089844005503640c5007481402240c1c0030075140c0150510130704001004102e00c0a1610340202801d40780c00c105980500090300030f4502d2800c8034144038040708600c50041440c1024001005030180490804003520994500d445032010074911200610010300d0000880c241d00500049036080c201503010f00a14055510100003510000040c0149001c1c04200b07041e80c203980c43d2001d60311780350f0354031a01176555504202d030443d8940 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 328341160 1250 328339910 328339939
    0x20111040b03040c08030304031202070501230601260c0304050f0f0109060b0f0918030409021902062a09060f0a020f0c040902130504080f0d06030c0506190806 70
    0x601a20160035019003103503483c100f83c20410a00d039129048981d9a403c10410f1000281c1c101103d03d080503085c2c1800340c0c60741d1071810054010800550440c00d444901d420a508100c9010030032442401d00b600c81c15189014600200d4000104104d0140d8282c644e00114107845a48070103103034858411130456810712035140b4203d08282c0d1181742076000741c0d1240c050000308400c274010319107000029240e5403200c10880e0b002540f00c41010300040d20506100c1c1c04802c4049c0140304680c080c041c17080c6e09660390002e811000303008554900c4031a0050281c007001c22000800c90090b44000000e04807103028200c02015440c880382d101491030b0703500c1b403420045040416000009048000d6154000d040138141c1800b9560800d0741c40c49800b0b205510301300010006070303100c1c102001d00401080001a256903140703010040c503c0303180b05054101801040f206143d207026040318041da841011040c446503511003c0c01341d039005000300381049040c50315003d65600e00ca584082e506c01c80003402580040c910 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 328342410 1250 328341160 328341191
    0x806130627060f0212060d06061208030108010b031908090d0b011d010603050603030f0c120304050601031703101e0f090209030c030309060a2607030504021008010806070f0201 77
    0xc01c0007250024031074403180303801c0c80740e203214150380900d14030015480d0400b80980d5201d031181c02000b443c82814040500024069154003000241207600c92001e20512141004d00c003940091094442940c20400d100038035080100702e400340c1a400c00040520300b030311590784c07002d9500301c100300b0f94221414045180c0440c003600309590003480d40c05220301207102c112910300c0481030141c0003403007410701b800309002c66031700e00000700c070108500b080080d52201842c244032800c154004a1201018001009000c1849004110107040f81d01c1200c111108448407440c1c01c0041c00101d4034030442184420040007110141f000d0030715401491030000d9469512011403440d01c4030700d81c0001c18003a5001c20a580141030810100f00408400c0b0025410907007400c000031014071840d08484100120300062040b203444103d200c1500007110001c0716502d1600d50030007030003040d044405074802c14180c540701541134003415040341a1080c1d103002c0d02c020b82d1901400c0e124150000290000c56580d4050403070300601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 328343660 1250 328342410 328342451
    0x30a0201270909021e010203040b0d0b04090501060e100b030c030613050f101a03161209050d030c030203060a0608070509210d140a03090c1e1e08061306 67
    0x40c40000000c0040003801817104810003c4108601620503000d1052142e0300002541c0440b4a81200c075a46d070a601d600c540080c2440a00442d0003904107074070710081003410b4100c2429200405040b44041d0fa4072102c45840b14403500c0740c03818200c410004128410820300042d80c0c06080503003103014000e04100810101c6008450ba018a060004240f10101260039910130003007a024800d15042228602c2640c1c052001404c01c651103450316181030403141c020030b50075641c00c5550700c041046211a040c6140c03680c407003405000004c3d00d003005d02401e0b20b02034425240564005440c031003019007000016140d018020b058035091110502c00e114540c1d450540c0209a48004046601c0c1024210001403500481e1408074040c08201400030010325100410b5441d03900541c5004511a030007424103456244990b04419440c91001c4000141c101c01d401c0c00310704640c0d000f6a0107400c00f0a10700400c4071002d460041d035804d500200045880034003a8000301c0c02c01401010300240340e600d2114610003058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 328344910 1250 328343660 328343669
    0xf200313050a0501171614070605070305010515090d080d0603050a020306011d0a050709090e1c02010c1209110402130305010c18030b1e10180b030a020127 68
    0x1001980144441e080001d11140203040030700b0146020800d003448000e0103180241700c044403c4107103a440b01c80610400c40c1d4880d242a0180082c0d0351040c8d07003403160207010219030450102c1c1c1014000102810040603074411990000748090038001400100110b02d862600c09031402071050200075504001c0740300781c034025403188000f404120171510625080200503804541c1d208481000c01065004181002d41d04c00c0f4001c4001800342c1c1c07000703410344215860303800c0303c1c2080f450710540c1103c41d0400101a0300c031280110512800c03034040c4c0c00803400c2e03801d236140900008482030310304204016550410070380d40b8403ca24035a80f900c101d601040490304454034122103c5e00da81d0302001400320a11904000048a24107007070011031056100300c4000e29031000503c145424000100e85d90600042c06581c059911103134860790070210041d040c581c0c5140101041d0f0340c149c40f40342458400610941c084030703c001e0050030b00703d07003903070015620845015103070302c0e001501c0c1c601801ea54140b10007940245c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 328346160 1250 328344910 328344937
    0x60b06030c070311010203040c0b160501021201030302010506030d200a08071101090915030201080919050717031e13180606030f181101020c181806070f2003 69
    0x10070307007400d004000c01138076115040d07181d20410500010440c05124401560003454040b9607402d050451703d4202c4800010180c015440885c003044203030300d00300a060481723000384c2c000d21240d1500401c040d00c070103202282c8400f08801d41c81220303400c042e00e03400065001c40c10068800f4200e080c1c40303010050784540001c4070601c5880f41c1025040da00084070102421501c8420410f540c80101441d15456a41c000070341803020020000e210361000b048010450013220100c4455200240390003980c820160203030055400140d000500d000400100341d5200c001012007400c801d400350303280362129038040030a400602c06002e0006c92030640c0100c02203101d0307450700c000089e8107190060060407a4030095552043d58200410030542c4240c0c0c01010403060380041c0a0007a000707280f030050349002030800d441c680212102c0c2844c0440303c003e0030418400c200100e00702c40e00030514040340d0b86a020807100c400200b030309101e410324414400c541072030380c0d41190318080c02c0e10000490b5141c9580c100ca00c104410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 328347410 1250 328346160 328346167
    0x90a09080f030f010f03051504060b190306050109020f03130c0314060703050109060509070e0103061502010207020f030c091906031709010f080106121e020f070b10030f0f060b06030c 80
    0x4820f40748101801001c6140f40030721100d04503501c89460b6089003aa01d864030120304041002d00800d9403244d4540a030040914075102c4d407407503800c0710b006070314402035900303600c1d01c00000f40243c3e0303500888500b20005403103103247d660341c2d0681600d40d0070001c000365501e403429100400000c0941e000b4520b040c80800c0240a44d10f0620402000e0300d00c140c101c03442407405d1041c01c00898550380e0980343c00c001d5500300300c80da00b0110001280140042d620200a0030b0700c451203200d01c0760f01903000b000c1840c002d41d1103c54034580c042c180360b0f54043c1c04807e26004a50300c000030f081c001420300005490076152502143e00c0e590ba80760b0410018000c20750038124400002d03910919a0840880c0241d0001401d0010340c0c1c3d8905000940300445d01101c0b1500940c80c0c5401041ea1241601c0044190321402c6c0115200c24100e01c0038040364100050403984a00c10002061400c0454050700088a92000d501400045c159442214591240c0011201d075078490740c828650381d031443d0103503201348100f4098507207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 328348660 1250 328347410 328347421
    0x305030f13020d3f0212120c0304030201020906040e221502070302070317031b12150607050d02030307031a150c1005010905190209030c090a09080f03 66
    0x540d880007411640380340901811840c0140c69800b0b101400303541165200c080102c1d491a071041c09080c2800703003980901e4101c040e800180d441482400d003090301c1d508484400d0144182c0043e184500c00c540c0c1c40004d458000214840c091800556005200f44009410140c0c00404070b400da0304182c0003829210341c17100c1041a90354150b86945c500b03001c0c405030046202101d4075200308071450500c45a500540001e5070400340340c000c11484005640c4440003010512424811001c0e40e08165000219a04001a41c140803001c0006030307441241c51134440303071160b242d04900006402280480580280092010f900420414041d4a0351016030b60003443d41ca1501445c000c045604461010402550302c0d411110340d0384079030f003c1e0f450080c051303110303107a84408404a2900d0704040400b80c19943e41400004200c49049403c03050299500e80d07400b483c2d40803c00c0c40745041e07018031070505805034851a002d2440c0e1912103640c603005911031000040314099612090115808500d20b004082000402e108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 328349910 1250 328348660 328348681
    0x510052d06040b010806090708070c0b011815032a08030d0509010f02070f110102030c0607110c0406032f040603050f0601050108060105040b07030302040e0703091106090a030b0a060e04030503 84
    0x4201c4030092030326100c14901b85c4002901c00301c0140000040103003000c009a4004c2c0501c5980b204283c010514140e190394030700e0a03040310071701482c00340290380c180204441082d000101c94010349038070910040c007d02c03c0f040350910b9200d00b02c005445490062400107101407007400200b422a044c0c034008105071514205082c2500da440180c2c40c0180d104020030004210403c1c003991846501c881200c8400d0070a0b40100e1542c01007030300300e61850040038288403045410880c000c4c1c8000d600001e951441200204000c1100c085100c00703400c00d0b055002d8000380c02e03601010404000e007041507003050310071100013180c1251400c2c1c000715101d41c00039081c032400800800602e40100024600300c4240d15054000030458000d40c45058030841d0041409003c05002e50141c50242c281136108040c68949000020081d040c2d641d019688402b492040180c1418581d045030328030741000e0b103101620f130b04d0f40d03890a200d880001c3c10030340070720f545a001144d810310007038031103000358001c1d03441c0c0c0c2d00c0c0c0c1070810300f86 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 328351160 1250 328349910 328349921
    0x4020301061a0f0309030d061706011a0a120f06060504030b2202130e010c051b060903041203030e060a0504020909010b0f28090c02070902070510052d0604 68
    0x480c031100100b4030244414200d8000c40710b81640820065803a522030091032480d500a500400c002541889000b048130054040543c8044840300300702c8032285d9894000462210a010b0b0340321006d201041941801ca000d03803282c80d48003901000000d0030444503100304040f0350f91900140009240040c2c10020700080c01035160700b0030480324016421601c182c0701c3c2c4c5080e54080c10002d0207089403100001070b210556000b80105d02440300280036040321004020702a0740318850502c641d0358003171640b0040b00000145507100d000060015071505042840043e00380b040083d0840400d603d854040e2000d903c1130000e1405055015030219850900d0b10400c010f007603005202c0101a890b11840c11401e03580c1c251524040101a514804160341000842841c4c1d03200700c01e01c182c0e1039644040000e03414050b91040c00307000e11903801d0b0341d062a114074001090f44507a800141c002e80c0080c4c1d0000e00e0f000c07036600480d0800c20801d040081a07417560b0f0f174164018000360124000400543c200a0141800d000e01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 328352410 1250 328351160 328351169
    0x20a0b0618010311040b060c0303150604033503040203151008070b0a03060e070f08190c020c03070504090f170c0a03020d0239061e0d1a010807050906090a030602030402030106 77
    0x60342850102c1c08490327030b039003c0140145444000c008a820081d00d4000c102c9000d9600812550740c680e501540a00e4800e40a60a10301c0b01c0e0302c041c0320305400030641010b5901996004000d84005240e407407101001075409071480d900605d4401000403144401c0008500031b0011500141e10360600501c007408480d2654000314020005500300300d081a070100024110b50b105003001c9400e45c880c84944800303040341c1034801150524004d4200f0700b00307800140581150004074101c40900d43c4030000d0205883d6004801844100c2e46021000052191103603201070154452480342040360f200030b22480e15001080540250700070b0146841c20310b5046c0724001c458120074012801070003201400c1d6503060380303c1c028810301d9086a110102c03036543e40070864007100e0701901580c01540882d42c240034140d20230f10018001c2c6203401840c90f100b1350f84500c0303070703c4001058680c8101c556441138281c860394820b13b00c80f03510400030480103425594020310b00780914004c110058507443c080c4141821a56541c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 328353660 1250 328352410 328352419
    0x6030609120c12050304030905100818070602030a03020c0a211806080a0f0603080a120b0307080c120f0a0b01031401050606180102010f0203041101020d0e01020a0b0618010311040b 79
    0xb4004104040e444000040a900e001640c9960300d040489080103d60045588030008518901c95560f0082c00580600700034961050340c154007a0303401da13655800d440b416015070070910080c04114000c3e4044e20000448400362860074100b662007000980d07003200c0300c07003240c03c100000c0290342d688070084003804e9140c4242a0451428000d02400a14009101607552900d800602403581c0058108900460b405070f10551141980070001d0b080c201d01e8034000b101d41e46041c91007420b07032030001034000407152114003070806d56902e1802d01070200e03942c94107014244500342c805105418104040540316000ea07503028140d5046103084403540600b40300540c4560304007418401143c2c0c0303072012241e00820f60810881d80004140060b070150ac819450a14bc640c80417007044140b00c403c404150041170260b0030385203080000441500d0206074002c0041c0103901843c0d04000041400d010150044c1000700b0782507034001040306018105409810840f0320404840a840740350601d03001e03c02450700202d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 328354910 1250 328353660 328353677
    0x40503120a05012105100c020105070e0f0a17070e040614070e010905010f170c04150503040b04021e060711030d022b0c05120919360603060912 63
    0x2504000151407500544d121072000910f0502081000c00801c4003012120b4020701240b035080707202900801c400c840020118910600d0440c15140035111001c080000030310700c801203410400ca4080204009491811a1140141c042101c6501c0c50445214070721601001c0782c038250804051544200240ca41d0082c0f204100020040d6a00810f02d10181e58082c07074941c41414140c1e20031200340c49500d003001d102003e2441400651b8035608000e01c1901c10424000495291812086802c0d110884014002d0400c0b100413600619102c80741095495013481e001c82c0c5100b0804c001031740c1c1d40c4940300840b411014005901c41a0034248150b016600b12800070300b00f907148118002c0070040c1841e2403c409124240c001d47c500c1c5000306820000340e900401120402c0c040300c6040036499000140b0b4903c14401400404c4411201c086400151151004004d2104542d02006200c0010700c1c045c1e00380344190911030100f160500c0c8980070086019800100c1c0328401070400344048000013401e90204500758 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 328356160 1250 328354910 328354919
    0x304230a1503050a02131212180b0a05070c0e06030601050909030a030207141c080f070e010f230706060905060901030b100302040603060b040e07060e0d0f0b040503120a0501 76
    0xe4030440541095030034089082c2e1394100703c0b20b000b03101e02440202034469524020420072660100c4a280c2449140041000b1801c0142070f6071020b00075004c40b2401800d60018405207224101400d061861400c1c8542844903d80e40c50842583c81d4020010000d454010401545820850f0600403e0251040012410400c0c0500d80303074492401c06c44141500003840e8000c229100b0203115407560a42c0913205a8100490000c110000c200701c0d00000880f5a0701107039800a0001001e409290a515848184501071006443d400c082c45910414001d01c1d03940054007e00b1600701c1d009001e03c2009042d510b880c00d00e8502c04840c410340100301c074130b481c00c803c006044e2a848003890550383c10010f100850360b103219400340e492400760002034000c0d060500c0041041082c1d04007000c58101140c0a100e0b52180c482c05640d00c490501c541000208800110380550505580c400f440e14005c03940d03a1803120690300c48000d281d0b02520b04803116440010700c500301e9034500302c2254110310415020b010300c1d4500b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 328357410 1250 328356160 328356179
    0x417010f051b1b0d0c15060f06080405030d06260307080d02161707030314060a06032c03030a110304050a02090606190807090603020c06160c050304230a 67
    0x5580910000c5000194610710100305003a800a290b0f004049620004000da0300030008402c809045425100d4208880400c1080b800b902c0151841c5203104442c007450f18002701c0c3c1c50040130b4015520ba0104022402c06480c071801070b00080c10700380c080d409040407464070000b21042090300c048030b1900203220b0f840000f12210122940d580d003005000d070f00da481092030842c91651098004110345c041141a41e0000711090242258a010f91400c00082d0b4200caa03140d40d1032011228250304c00801c1c10148001c9000e640400103440300c528283d4401d10100c2040b09000031800040217507588040200917210075640500d01011030b28015240c21400c16585203640c070070f40390100078480c510120020300d81d52a140280c482d0144511003806400c080d2450103000c01c03205682d0800051149603000c6080c0c0c4c000c1c003c60701240c05c20360040503256138a030f9203404446e50480c00c1400300445020500080b51040001c1c002034112122000c2900050020310043d42410070441c40c018010000c0401c1340100c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 328358660 1250 328357410 328357441
    0x106091206091a01060914040e300409050103061a0d08300403091a070204050c070602460305060a050415181a0d15020417010f05 57
    0xc0c0041c0126006006203031005a802150351a070080701d82d02d030300000e14203500980c920b0464070b01ea210701100101400034001607072001c03c0804140d07800002c00303542d070002c0208406008041c51400c04100e2916506541b6a039200b0361000911a072a0340052052000601c02c208000740c0d10031170010040944408110802c00140c005807014101140d40c980d10300d82c05c0f03400301c0d00c1f000e1581a000c012801d07149212840a003540c00b03800242180c0e40201d14000c0045e6040e510020250343e035400c260150b4200005020004c0040f130b00762006000c44e0000441d503002400c0c42e00f624801c441c8404030380418900041e045100302c1000319030000c0b8074000f01c007203155095900e080d0914005c200c41c0e54031030100d82c002c241c0340d10054020746005a298081c1d0300f200440d1094500041742d40444a081c1c0f5009019600104040e803400066440600c141d49030040410030043d10441d515180c0e11882141c8200304d8105601c1009101c0c50100303002c1510a0a205441d82e0100c800810081c034200519940d4683c007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 328359910 1250 328358660 328358663
    0x60603070e04200d0303020418060b0d0e07120c06020f1203010b0a05070c030326040206090402221409090d02121827061e0103020703050409090b04050601060912 71
    0x10140f0b03440d10342d185000d2110326005202404403400380140340340c010025441440350390504040c0b04d240c44415219809030030308884012806906010410740400014004684560381034407074030400140c40c1c880441e03c0c50030640619485840c0d2490907101070b0078065540b49400e11a0003401480d02e82a1038031041d24150340c030311110181c41d5890040140c800e0700c5428006410b40680782c3d000010582c0c03014a4644000d180b680d80c0c1e06448a400400d068034400395002907220400340451499818507902808201c85512403080d0b41200611169062901c20340100000d0460650290300604101054a0304481303c000100124643e007a0000c1d110416806140c034903c9000400d02d02c0c40c13200c042124620ba00060110030512070841e506a4505072045816000c1040c5c040000c41500d440e03030034140312581214048003002e501c113004500a40c0864400c805100c402d110204110f03c10344144080306110720045174032420641049841c08105900000400103031620034083c0452001c180304d03240b03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 328361160 1250 328359910 328359923
    0x321110a0b0a09021807020d050c120d02090a0b03041101361505030604110903030d020307031104230405010503252d0603020339030c07020102060603070e04 69
    0x1d86500d1002c034090712100350b02a50142185400c0130b105403030010103600400300c41e003c403907108044441c03e0320076000d080000b41c0b05400c005d030000042d0b542c0301c00420080c141c54400600c2e01001c0300025120b41c0d01600702050400b0301000304010049880144c2d0714081e000d003821400c00c00c8508940706281c10340502030204003030445082003101840c1a4084c09001c58070100045079076155402009500111501c9100301c2c10008400410301480c412907000810250242d840d2400c4214030502941c009400102050340c1c9008003514003050b00c0c0504040c1003d04210440075640400d00300c0c03c0f2002c01c0c59148240d141100412aa541c00a0091103103035855103410954400700c4001904560b081d800340e400c460303655002c3c80e101407030b149400c1e003031040d61074440c1001a02e940b0202c049020803203c8080e04090500b01018000b4010b103da0124080100803018401c1000c451102c0c50300140c3d40000700e204e020845908560b0180001580244280c0041c4034082c80d2564a00d48024080c101410a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 328362410 1250 328361160 328361183
    0xb0604050a050f030c060a171305060106140412080a180509062707020609190b0c0c1e01050105010912051e030c160306110a0906050d060905010321110a 67
    0x20f5031001c0c040c400029000406460302d41403001000380c06201d0201c00413508080d0500000c000032100b20580c02e107240c0010090400360300f85181a180403000c80010400b03401e0034000000d0705106060390340c00c40b510030010291120b080703034400380006024a4501e80002c2d407001c003c1c0700316142c42d042ea940c804001ca50100341c2e1003002c1d4107501d15440001020000720300c41010044400d400241c0301d030082c040b14046403801092441c0300c010031040c0c0c0500610302c42c203400114994150100181580300c100006880720042801c02d003a615142000034142d0594460004000c60341e000280b00c401440060501060b40c100f566800e501e4200d15080d1445803401c800000c00b03401c0042040c0c0f41000107000441d02c1101c95605003884c405100e04c001c44485081268000d00840480d0658030b5034001600c038070184a050a03004d0341c01d40c010001d804012591500000346044660007039034001d40c0140003284443c1d9010303011854140c10f13110410144221a000d00d020081d00260481c1d10035046160b8015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 328363660 1250 328362410 328362439
    0xa02090d032303040503041a0c0c1509100f030f060501021c05040803070b04050111210a0e1f06060903020a090218131406010f090501030f0b1c05010b0604050a05 71
    0x1100d0820030082c0091502008010400000100900585412441c0c580d580c144400211585100d5514150b031640c119003160080c0f8204480032070b1004844420807400d26030210003140200c00c0008408000940703019004110a07014440c1500164064400348007440c10140082c1d95110101a003003180300440e40344082c403603c074406a40242c800030054070f0740c400d820f05016424040c04c4c3c0b001e99295107820408489004480c0c219036500320080780140d500661140d054101d0b01c00102103a035000c1e21150549400d54080c04010300460700c04401a404a8a0490103030844440d80c2215082c0100c4580034809a1795000204084804100000d0303591551034911060b009110407403543c20034105810b5001001d1700343c000610383e5065843d003000959840300111000f0300207101e03407c0451000358060180c0d52080c0c01c01415a205040d003c6480e040b40c001003800e1702c12010b031311160004464103000802c5004e004001202908450442c01c1030309103c00201802c210748601445807420b032601c101d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 328364910 1250 328363660 328363697
    0x5060a0b0118061209050304030302060910051302010509040b09071106060a030308010510030e010501180b09040b0c0d090f03170106050306030d03020702031f1b02120a0c020114040803040e0a02090d03 88
    0x810546c05070590341c441e5902d1602079528403043e2a1003013140904024400c1c007603141c1c85190320a6402c02e1050030710403041e80041d50103610245d100d42e0050317241d41c00e0700c94940311504094080c1e10503540d6100c2c0842c0c68841c1d81c1c104640502410300c194040c0600b000800c1d408201c0c0c60642e4011608514039405083c0103500408554071148510b50034074000084c1240d01c81440d21101e44103c0341803011007101d01c00c014094408490013040d101d0401c2c081940c015818000d416400903500c0b00003010180c54aa044500c4403810044002407905101e804c010850802e40c0c5005125034200203045003007a2001035100c0108096803c00c050740412500199507041260300705594415401319264071034141340c4409040b41c050114024407c6c5413185840f54400248039000740d5100000300d00f0b011649070101c603c0072540310143d04200d041000c0990701b80000c001440113001c54801190b80f18030b4401910b020310340c001d0140040d40c2c070601c28100c45031075802a12500316410b19002c08440d41e00189a07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 328366160 1250 328364910 328364921
    0xc0d12020f06040305090f030102130b0a0c051903020c030d0c0308060d061514030f0601210b01060e09070306030201122c010b190f1a1605060a0b01180612 68
    0x1103051182d0780900c0113145d0020020715a1420980c2c1850a00d401103050609034814121740505050748802d0420100c80030201800969049160011602400b601c03603501d400c8800070a600256500d240079810144c0411100c600700105074090700400d424904060414416210060140301400300012203e90312040704032011584404100074a404c002c84850122401d8003492580300c10f44103400303019260016601003020040780061250780e0038489443c10100441010018030941084c5240c0000d040c4246036000c0d186580e104d55518098808100300050060318010505103000401c5c0b0250740d0007803141d83d0b00d10f210b19021607110486d0f101d80713580018402c00444489039030b14072542e40d0041900605d00c0c811080300c0380540300310740100a4000e501d99204003040d04502c40010001055044a040350101d1000328803810007481d034424a0045c0b0500e0800c440c183c00c10070410221881c14803584582040c20300e410460340003820413084c1240620b00403181803144e803920f100810402e58001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 328367410 1250 328366160 328366183
    0xd05031c0902100f11070b09190b070b07090f21030c020a060f030f05060603160302070807030809101406010c020d050703080715050402010c0b0c210106110c0d1202 72
    0xc0f8044010312000081c101c55480026900251050003014000f0600041120598182841540ca019400010080e059099803108101441035410000d0021121806407403114015000d004031858241c42c0240407111507007091a061100ca0000d0020150440e03181c02080031802d80c0d0400f4000c1070406841100108000071b501050320070021410a9006d103404414032520340342401000708000240080e502c0840308141c01110070300020340b01e00c4e4005920260f034040340c20018075248050b00d8505490340294801d6001c55145010300c508010100006040001801c10410485a00030000c1031119070141105040044c0c2ca14403000b55991000d222000d03d502c5011a046c0d0740d6203260604032a0007010082c2c803020061a8600d03d0200c0b140100da2045505a54540000e11265980d0ba07180401400004060105102296000d041d100c25030f940000c407000c0711402907140010080240000085402103500504940034154890000d05d8204583c404042c8031035107105c54040b0f1601c0342075000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 328368660 1250 328367410 328367419
    0x106030218040f02041406071e1b0b090a090903020615030115150818120304080d090f0c080d05030a050c0c031306080105120a11010e041103060f0d05031c0902 70
    0x210f201048005500410858246a140160081c004020020207004840c00034008440040303070843c00300b506010b40e02c6441d1168040c1c0c002085c0c80e40c60b2909001183d000f0074000342000584100a207403505c440c40082c1811744041c8003580c10361381c0007510b4280203041d0024401c01d015043c0f0142d50300b03400401d6410900190041c205075940386954a40c8511200e06022810031404075402207076509294541202c0c9500601c01010801e20b8054a80d0004005580480041c0305515030407a05e801551401030140003000488006814080032100590303010048075405455203461141d0400d00740ca0344007001d00000500790342d509180c001d143c86490695442404002690311154017080d1008041c0d030050751390b086240ea01d450502503840d2451000b400c40c2c0d8040c504100000e0401c1820f80344d840c10603d4a02502e9501c10082819a14803000d0040034000200400c0000e04101c038081d050f962045410a1080700c0645032107440e8031502d00990340c5443c45110054403c01c140d0005041164040d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 328369910 1250 328368660 328368671
    0x405180d03020301210f11010210090b040201080a061a07081323010302210709050a090606020c060708090904060b06130e2401180e0403020c13060b03010603021804 72
    0x3000900030f510901600044000300703214104507071448280c15140a9204003400200f0806444032800103801c00840307411441100c5005800c18454010b9602084c8103d09440c114103003032001500d00c0d480244401d000c945018800c002c0e0301840c1206500081080810554035601030401110038400e0044034600300748104d42c0004d6940c80c0c12074510002d5a1000c11400c031f0240d14004401764894910b03c5088041c0340004e84d40c0300100490170365000103031030a01e000d01e036170380b14003023011000d565019254480e6600000c0003143d40500488814080c1110400e180045035a200c1c0401d000e84142240a001484000b0742080103a034000e010f004d8008005c1c40d1150f0107540b00601c8000b090250324010010500440c001d100600200d04001054001d4540108420b00c01180c98001e08100801404e0301d0103800030b01c1c8502441d00c580070724060740c058840b00f40501d042c444020b00b46c50412101520303211003080019100410b603030540300540b501682d0348032443c0d54481c540119100540c3e00c5407405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 328371160 1250 328369910 328369933
    0x306070507020a1d010302010908030a05040611010b0a0b0d0f090b0a110c01090c03120c15020c01020412050a121b0b060d02060c0a02010828050a0e1c120218040518 72
    0x130b15100d048901c01d0741c40202c01038841146a0301d03405001c03800c402054050205104507070080300c0c04c265042c030f200c00006600c0c0602000956082c032a82c800601000005844620b120a9018a0030800c14189082c82101c046d0350b1034120600c001009001c1302565050700711404042c3d1400c81e080d400303420000380f02070070140c100551051080d20085030301030030000703003c00b103e8001d1094008064003e0742098580d0344aa24900195003e034007a104255820440130455195015011074400e019a000b4045404603141c4900e040d400ca011100038070410b80c0481100d0a005000f0b402032503802081240e09440c1e10000c02d42c520000340000b9404800070890710b2490b40c0015640200783d00076078514000ba280c0c400c0742030111800481030f403014100842c5d90004648d81d504000d40001062a002400810346030420b402c0c1608040d003404819900134004014903480b88a00294280c01d102c21841e09143c54150050008074850440c00707203482c1c5000560b80c0718001030b041088103900e400d0750307901840d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 328372410 1250 328371160 328371209
    0x3120f0709090b1e01022112010b090d150b060403030f1e140702031504080703031406130903110d051b2e09060c05040303031a0306070507020a 63
    0xc494200008a05010002d41c2516a000d5000c0d83c00c00a000000a450196680200207004000d075606601c9001c000d0240b140400c00d0b100f0113000541e140035100c190f400341c204030780c444c180e22841b6505424082d2281e143e41d46c81c980e600c8550300ca04100b80d4022100782c548003078a82610001c1d840000454000107140c1c01480790b8000300c041369100303011440c0400c2200c0600c0c20103a40000040c4604020000d076007100d10081030440d0004040f9280002100700c07030100c03194100d60840e038010000c01c0350b00425406010741c0c1e80000500b010b10806150042c0811040c1d09200da04144250310f4001210a0500038801d030340d146080310041e50a20701001030081c015511801070b080c0709a00032659011250404140c103058458032050720180110450500302d090681d07441c00078079241d650b01001c0d000400ba80b1030040e0404c3d13241c0300d290b103840c51414043d00b102c501d500082020001015107002d981e402050482e440462410801d4032460140040b84107000517801403011160a5441845103441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 328373660 1250 328372410 328372441
    0x19060902150702030d1e23040906050a0e1308090d020904200a120b1009020703081e0f010e192a05040b0909130f1119060203070b090312 60
    0xd500b141d581600c01c0e1000c80b60b01d00e0300d1b0405080030301101d4a820241e803107440030480c0e10003d611800200815412030044070740c0700f41c1c4101b0316141c4e071360820400f900b44041102c1c02030500091421040ca003000c121189a040007000070700306440058041050769034035550103070464010340207403154501450300000300304182001190780c258040001800345041c185080540c4e1110000c1a4202c03a01ea42e10b992001d03010781408102c0364415030110700c070000c3e440030f0203003103000703a80708041818000040140c1180304600c03103804490a400f0881400741e052021411142001c20681c00d035569481d590040055000c2c10004603814040c03950710441d5821071540c41c100c2030750b0011040280821090b9801c5c400c41c410707082d4111060103c00007a1401560869009030170301c05150103d1140da41d051008589030004aa2030070003818000f0741c3e820107200c6d81000d040501c10403640d4600f0034a002c0e540e409114401040c1010f1140081c1000809105440c00740c003c070b00c6000a1414800c808800c03400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 328374910 1250 328373660 328373663
    0x10030221040b0c0a0e0f180c0304150c0c0212030d060801020d0605010203030603100e0c150a09050f0604030204050a09080a1d0603011508040309080d020c12010c02190609021507 78
    0x1607082c0c007152001800e0000c6a09401060b12100405000c4000b1311420103422a80d003540110210f01c03030304020080310141c1d881144e041100b03d81c1c0b440c180c6030080e912640401c1041d01a49041d102c245002e8000c4085400160119040321092101c0200c1e075140d4030510300c448501504054000400b004150060403d01c004600140aa0364460b40120f030b4a00049a10a80c103501102030701c0240001c46c1d2060554030184010780c1c00303005511022a40614541400e13103111480001c0c2e03009040d501103408805410200ca40c2040310f106000015820f01682c00084e00c00c90361980030030061105070b41304521150384204070903112070039008041c0c55407190403606032000303071303035811946a5141400c2140d050701c0c43c40f42d0160300025400012a0014002041103040c0943c0c90130100710711604004205825681c0d50080800c00540c405201d032060a030340c04400c01e6810054414480d41c3c0200c0c2c0008400c11403409a038074410709083c0b042c00780445440107508051541052000031071032600030803266 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 328376160 1250 328374910 328374923
    0x6090a0b0415170d090e070203040b072003120a0513030c120506100b0a050c0c030708010c141801050a090b0705030306010306080d17100305010501080d021c0206061003022104 77
    0x18410340f18000d07121100390f00f02c3d000040c003000e4180300300141c803568640c1207078544c4122410070703032101004103055104000656060880704150185000100045d10700b20f001540a00507050702102c4074080c9010b00100d440030b001d4042100442150600900c10095400611a07803400340d4840c0e05a4464860010541d8140076800c00116030b2103600e110354045a144210035881c00710010703c2201e054000d840c000c078690282c010b680c0403541d81001000040c1142c90000100354610740c00140c0101c0700ba01410105000512118450181000c0311000240c002e080942c1e8449145008480c200070035007022505035804181c0c0c0d81031040c0000030b14840c01c0d083c6c804004898a86804c4c69480c0340501611300041c0f102800a212545000415500316252032203000075941c50390307511070945000340c0044110b03070f00c52110382004650422541085403003900c1d00401203880c200c03000b0349500c4010401801200980c0071807024030311030360484040c16881003840e50111100c0004215011007a2416500c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 328377410 1250 328376160 328376189
    0x2090a1b11031c0906150504050619030212031c021201060c050d1d030109030806360603100c02010c1823130608151e06090a0b0415 58
    0x10103004407400c0300301c491018011400d02c4031000440005240307a803120649640c854000c540022454040c0300003c00401c030070203020908020030b001c11294010300040c03199007404a40309500f0440c9001d14140c903019580b401400034100415403440c402e0402021094081da403e065428180354050101001c040b1504850760341e940004480b852102803024015801c1a01c24007c0280a19140e400c052100c2907240846081c003030001e82103607500381c0b041d0b003ca00c02c801048918039101c00302e2a215900e0204100b480203400c1c40c01720401081c840800810046800850b45607a07041140f403002c4000c1d800b0a00440700b1980b4000d01030075420b130210001c81d84082c540c2c0c16200559024400340c0304c200207031030a01a080b06864400d0908100a1a04000500c29642900c4414001c801c0981343d4031000784030501d500d448400000a0040001004442e0561900e07060001d081405402ca1021690200d168841940243c0142344c151605903009140c40541103001c10302c900c035072085420003000080b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 328378660 1250 328377410 328377461
    0x506040c05060405101d060a050d20070f0503121003030e03010e100c0504080304060c0b0c040312080405010b031c02100e250e0a0b0f030d0807110a02090a 68
    0x9010718020f6560008094140c8241030348500741107030841b031030344014072480030081011640d10307406000c40380002080041d0648a0324a0760050410044042d100280d0700030543c02201100d00403081c004000504040c66081030103400c0051f608504003030000d40409061640700400342050790300c0103c02040300303048000218601031164810101050024205030403043c0521030060842c154051706000c401c0c0f2020a0881d410000341016204035224606650f400c0c0c04d10104e0b00358003c2008100700c50800042c000a002c2ca00c206c25078103082c0c186142580c07281e00d022400342125910094241c0704042d00c088401c0294041e4400318500e5400381d80d04004070006846c15608001341c03040c07080d070158603101400007203122010103804408408900300780d10f90480103105c02040d00e2002c03070f6980300e1000f1289803901034210744109900300c000380200c002e4020080c20704c00005041070203020440640c800e01d907405001e0403080e1a03005003d4019441c2054409004068560f0303072081c00c8405510554 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 328379910 1250 328378660 328378669
    0xf06080c03100314070e0c0306010207080a0309270509010912020a021c0303060308040807080d09050906010c080d020f0309010f0c27050901030503070b0c1303020f040204050d0506040c05 82
    0x1d014426200300809a40d05681300c0d03900c208900f1600010a2041010000381400f451080c45e01503101c2d004416035a00b01940020b1415400f50403c0703003103070401c440140003c1d0b00500040704499880d041200340407901000f00c6001c40328666460412801c0c0410070203075030410341c0010140742c0b14003192401001d41050032681c6035000c2c2402500040c219000410760400500302c00d42d0588289008030382d00352a9580e45e69141c000364400341d01d6602a203414080c1c007806000402d40150246400c08003d442c2c0301c00030700280b04c0900154140081d001a1741c084c4000c28007190008c401d000d406550b074180414a44c0c0d800d80c0206e5404025519160341d9041c4000325000c2e5101c045000d40d20715541e129185005034070003000002c0d10000443c16000010780742c8442c00064002c3d0300440c090340c2c0f120181e00344070124440007000080200307402c208246940c0300412580080d82c2c4c064442520119000c00800e000384966004507600c840582c517400100000000e66901c507c0c0302e001d40c2c4940035503401c00d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 328381160 1250 328379910 328379917
    0x60a0521010c0e10030b040b030f1606020d09090b01110102040b070c05031b1003290405071e03020705010917040314150a020d0b150a0306051f03091b0f06080c 70
    0x1035104e0194208007042c00e219070414040c1c5100103000045444c040b10010307103060480181e041654000030090744c80e40c4000c80e1180000d04040c000307040100801b000040005075240140200c06903074007019032581c0d109090304114251001c0085540d00e45072090084160400c2c80200c0d505242e400c000b10755800c002c0f418071051400c1c0d19881d10000c8082040100c6404030090400405682e0340320080c00e144441541e00401c00700311044000e481c008414001540c10080c94441402051002d200c001480c0c03050b000d400004515005840d11114540035014281d0110042c0091542e500d8490b0b150102400410442e481811038000c40007000d800151103003502c012000035400d1500000d203c101164004065420301072400042c80c808040000745190181d0582d00c0c80b10401154100a050701482102c0c0504401c17901c4c82001c10b0713070301042d2101070302c004401e10405803100442030801c070380d0f80707540e40c142c02e2901c0c15003051940340c04851065142c1807095100080c0b900d004903510078100001ca = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 328382410 1250 328381160 328381187
    0x2a011122080a02090c070b010303081506030403020601061404260d0903150504060902040e0d0815150c01140a0219090605070b07140a0203040f050609030703030305060a0521010c 78
    0xc1c0402e401c0c0c0d90200224000d005044a104200401000000482400e030b014040c41c0b09440319003940c20215a003a0b0548424084903000d07070420428400407a400050b1241119401d00e8500038941525000550314020b07540004c043c1c14404c07158428030a4880c6040d59040b42610481325040e00e070003130444121010340300103802d0055043c0f84220b01c80d02600b060707038400e010b807a001c51204800d90104044a00381009012aa041039060580342c41d80301040b50740016080807140350054569000070300c62400c410075400d6498000880d200c0001782900003031620602040c40d40001c1c030b80035541a02a5014801034100c17294007000344095540512a03042c20748000e903603103c0c00c10441e95280000e040c2c0241c91242803290500c05c110160200d00c00a102c26031b026030155031030380c0ca4407035000385480590308242d11941041c001e26401da04c000a0207401c40b60980303030109854a851021902003140381d00100c1e0401c0c41c601e648407100c01302c60701c00c8081d0000d41e002005401c0a4030000c540c1488002d09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 328383660 1250 328382410 328382413
    0xf040507082d0103050a02040f1e0b18010b0a1418040b0a0801020310030b01051e0d0f0506040b1504050c0409020c030d020c0d0f0e062a01112208 64
    0x403070520711282c5041c051152040c044448070224200300424421400d910845580e8060039030b42045050502030107014080983d02401116034440120a01d0340c0d003105070b40741032940d034601041c241c0e4070305204500020b005106910705584484940c407032544003c81c00e00118200501d042d441c51042411610500440391044064280d44410400a07091403131a0350390004840c4404201c0e030500380b00440c090110407249411107840c41c81d119410780d20582c02148038610110705442d00188010181106100c2103d03804804000351900350710400d5540400b03000c074030a5000700802c118410400c20300440b5200120000c088610302000142c900071244068618000d1000b000050302503006810b40c4441d03042501e080070410205442240c0110b031315144607500c4401801411900718400c03000300441d134903145a50640b04400308559201e1001d0300f45e1010500b03c0d19190307001c2c080421081803d800c5c4002c1c41040d955110440c41e58000c040e40c2c11481c441c41e02e10f0f012186600f220030045510160 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 328384910 1250 328383660 328383677
    0x2115030607050714061006030b09010506030c0c19032604030c08030a020c120703090e070c08030a1e1d0a020117060301090f030c0614060d060b01020c1804020f040507 73
    0x90850b01504007801c101c502c1820070781c886008480c00d02446228004c1210781090582c6002c1d8020207039025001103038018000f440040c0a2511000b0844c1da000200f0380700301c1d5444410540c00c1e0301d0302c0105140840d10a1185840008159001145072560072145040c0c01d0144500408544130f24800c0d9001130100d80342c5005900040c00500245900160802c40107003404000204d2909040c1d02c50007030f000c0701e1b0340012100100758000c001c445c040d04010001c0c804519120f9805012004040130242a00d403020000590883c0d9a070080b0580c0e20400c1440103200310041c61403c041c21444440008201184189840740800001c3c1081e2154050303440e6420724428602e0b115030b039131014081f55055501d44122501188008440c1104240b007540c43c0c0440c5c08040c10800c0803034141885003011400d600c418441b640d59803c604807145500300000040e03450701c17080141d2400d491071a403190010305110040d15185249100c49100340d0003590842c4c28141d08004001c1181ca084451a0114410a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328386160 1250 328384910 328384921
    0x140403060b13020a1b1b03051015080307110a05130b0a05091501030207170a0804050607020105070c030f090f08150112050a1b03230d090608130c0b21150306 69
    0x3401c0c2c0842c05c6001d040c0300310b449152291071008110158005480c65403246402c40f025200718412184090366440003460003504000c5d11a4a0b88208100500f51540300c2c1c040b00e9981d501c0700400d00c001d0034010840c1c2c5d030002d111004e10010340b40125040f80b1500100b400080d490800401c002c0c40380381c0814212440841c000015402504105005e0350b5282c0d401f161035414403080780c01030a0113806521821818545894000d01e4800c004000808690500090024540e0020803c516243d03050901501c400d1101500701d030522143d61083c080f80486020002d5940340210704510040b00d00b295000c102c1e0788811072320481b007100e41c8000f001381d07000442c00c0000c22031402c8030100c2c002c04c403070148079010362301d4603145d554042e500d220031990b0603d0481c080d040c134420000140302d0310031824800d513818036000000d00f072600300504400c100c030441d40001041090350040d9a014094140b011a15a2411070031074000b4582c4110b0804034007810f802080108441041b843ca0162009004010a5444c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 328387410 1250 328386160 328386197
    0x381515030703090609021c0c06020a1703150406180e070e1b070b0c1201050d03080c09130204080a03080112120509040902030f0c1f02060f0601140403060b13020a 71
    0x3c03180a8450903a1800e01d500180e41304400d03e1504548000714402d9040301d401c0050b04030841c1c1e48004c0640d800658500700098100d24060b100c0a02620300c2ca0700c0343d5070116611084074103040115485454480040ba008210301c003071150b80a03551408010600c171481115aa514050280310202d081100c0000c442c80703403404604400005500302641008a0365446448400060780c616080c203001051180d044035085600ca4014141260343e0040d40800e80c80141180c4405046030011403070003c3d02d662326454000401c00248500542150303540e07070320480280c4907c1040b008400240203c000050440110810510340d581c02402d4083c403800000c8040e2216070184902d21340140d26490300c40050b9a007885101c46c500500d401825040418400700400351310a403003030210181d8802d84982946078001011980016071100102003a194480162500c0c003040f1015003104c000000d006c020401160000300806d6400e0707440c0c160311450b07030080030107a0152039480300c002400c2c440036000f501034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 328388660 1250 328387410 328387421
    0x61d010603110a021c031b03320f041b06110106060207180e070308070b160305070c02040e0a0c170105070903030c031d13020403050f0d0903381515030703 68
    0x58170f0030001040c0343c003070307601c1f2140055800c91070b404a42d0303810440011261200240482803441c00c0411885645503444d0500703a24041d024501c2550170701c0c00a810000385040c003030502c080ca0580301180d1951050028103c4000c9103500d1a030f542000b03030024145000003081c2054501400740c03880131003403000852000f0175140c420403c4a200e0140f001001c20b559000070700c089030283d40c0660b2680780c000c50040d0151000610300c020107141c01c003005125a80400010b8241e03504031808038040392007400f0700e80340240300031000c0c20407203064200048401c50040c0c011540328964009004d955600c1609485070140e0340b01c00383c040b03012078882d6000688070314070344041c10401003c084002070102c3d0100305140d60307000ea2580f4695001809106101d01004910300c23603900c1c040206140340007100010406440307844014409641101181e81407000d00505080708609400340c800007401c45802d2820051050b0f404c8100314445415412181c1000d600004c0000c6504404034695169890110002e24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 328389910 1250 328388660 328388713
    0xc060304030e060a321b010b21070e01030302070e06010507050106032d05032a0307050601050108090307110f040204030602131a0703020a020d06061d010603110a02 72
    0x200c4112082074559410000c0c00c40c05100781d80d40402215405260f040344c6505e81907980000b03051415104405c08013504803483c3d0421503075400d000d80c1e1652446805892194080c690020b03601c811404d103411544801040b4001440844082a0341c03880d00c100206401e000140040c2c10480c001d1004001081480d07812513030600d0010b152010310346a179421142c041e002242c4250003107605042c1c8000e0514a103040e544182d070310f100d40c2e40c00e5543d0039513a40700e4601020540c1d0450301440c024180a00d10300c0c840d1503103100a603555142c0500e050b6880b20424061240880e9047c008560800740020650b16805d0744a4200f04481c20403004000100d0004000305c0e070f004d0380800020000804900113041504900c0030002a0f550130f20b8091400006444414541c01e04e0500810000c241c1c0000c40542454068a6a009014441c100400602881c0c0c01030002102101a00101e046200d01541d040b10866541004040b0f0180d0301204240308103048040164010b250031200004004101d00106 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 328391160 1250 328389910 328389917
    0x130305071403070f0309092309010902180f0106030207030c0f110a0e01080c0f0a0e1e0c0d1a0d030e030a1202070314010915020d06081b0f0409050c06030403 69
    0x7010304080e0b490765104103412a66515a40094410075402c05402e0700075220300c2806000306a90284200a05409000c400920880e4200841c07480c0000703501c03a20340c0c26000703041d078115020400b80c1c812000074107846141d0214074200001802c9803082c4280c4507000d0b89542e4100441c0f81c103407a07448c180d80c000d0328255001820315640701c981c0e03628856481d00500d00c175030007841103626000341e403410034080081c1c1078001c1100d018161895901c0c0395690060341c190402c0740446480c0d2400360710402d003100c03580000c00748202c428082410040360107042a0114a00144105158100b800e0900700100071180d40003100007542100090144251441c0303003401404441c5010020303202e16196907100d040707580140c2c1141780c02388140258580740684c0034407030130002d000c0c030021551030340444143c2c2158134010a90228402110010b590001401444001c0c101c9012004000300c030b103c0301a090807400c0c8101b0656a4100180c203140c00303065031040e009005009440c1014040c4006540001e0045042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 328392410 1250 328391160 328391183
    0x100e0a140105040209150307021b09012909030a11091005150c0102070605070306050111070f120503090a060207140306040209041101090f0e0106120e0a08180603041401060b0313030507 81
    0xea4110311b014500c60f110580c010a0b00341c0826120b9035420300d14601c4503004104040040c07001d4000301100d4004101040d603101d05504034a501034016010b0150b1302c6506004140d0031800b4050056031444000804a855283c0c1c0e440d1a400c140313003001c083c1320b00343c0c00600c440d40c0c0b0f05d044404c100207072502d154007400244c03519800f41e55201c21203000f11070700c1c00402c4d41e130002413080307580c41580f400c0e205020500800085062140307032107003814248034004502d40c1d080400420850103000b0756a0000b006800c0045c0151182006900c0316261f020f0303032400b002d2304458080c0f14540020011f016036009030100102da202c070b86611800411004507035062000010300059108028880c00000b8085881184030035414101d0080c0780409a5407030122603410452a2038402d40c01103001d000d8103501142c0180d48084992000b80c0f03480c100c1514a0340813101104010500c0280d908040061250f48002c2100d6911100d40551501050301c03c6031240c04421071502c00240610014010f050142d54403946 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 328393660 1250 328392410 328392439
    0x201020f040f150f0c0209071b0302010f0513021810030203030a030b040f020703080f10090c09030c061e1202120903070212070515130806100e0a140105040209 70
    0xa1560003940710040b5214000307400c0201442c810900711480300c0d5494110401035801100503c40c5a1026001c1c4c0700d41c14080118000760b008100c40d0b406800c00413024004a40f0a08000e0300030082103030001d00940c10710000800510b047c025964605500410019180005400c0c0c0340303408000030080380800105500200240e40d041010b0300c2001c03400e03a808144011014148000c0c4c40f80304c5a071101990042c00180002030704007440e19804400c0707541d40c040564440c1d64000d83d49410764040c541182c902508083ca4660003082441602e003d610900000341d50f4810032600701c51911007010f070300707000d40140403949480307420031100340c0d11003190260900100711039281e01d518099481c07118541c40001d421307046003001449500f50707040500143c070205245c00e0101d204610f00b243c07009844580010960140301c80402c0e0a000f030021941200d62501d004408414803501e180900d9004e07803205800148262002d02900c07004160140750080d0a0f480c00381032102941100303002e960b00c07000030090f400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 328394910 1250 328393660 328393687
    0x3030a030203190e03031e1501260a060e101d09030903030d0204030308060405010608060d051e0a0201141606021815040f0603021227060906070806041a0105030601020102 75
    0x206444d0b00c0005561740b03041c40003458030707940c81040d06564901e0807041000f03140802c1c088081800d281c02c1c01c104c625906002138016140001d03142c10051911102b00340004d44c445030f440b1900f520b03c0c27030006031120703201c50103000c800102c02d02c200d00010358082200812a0000ca840580064246003200d00380b504e1b1600003801d50700b085082d550400d41c0401c0070401e00d6404074034142c10030802e5034204038079410150001d0005900420701c2d80035900f02882d0100708034041068140c000c18680c0b10002c07415841c40c95940340c0d110300b00c0c00e0740018035020020f10300e0040d407811196242044000c080000949584480c080d401480c40d003509061025031352025600e92a4000900d400d40c540032940c0d55007070450701c103800d0f2600c1d00144200351062010810000e40034802c1d0344c010421040f44d00c14140e8010400382c101100c003c0280a80c0900350a014080c0400100b42d030213a2426200c00c4050350351482032100300c562281c1340030b0907440078040f841142d501a1005541090741840094900007040c000d24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 328396160 1250 328394910 328394921
    0x30306030c0d050c2803110f120a1e0506010e04120809071a0c010c090602070803090306060f0301060f15080106110d031a0d0c0305120319020a0c022e050903030a03020319 75
    0x45d034400704240c42d047e1441c5024120f0b1509a001201c0c900307100803a5151290360782604080040c82c2c2404d5844205415101410200c0016481011503c242d030711a00d410720102c00586080300c0b00ea0040f594404180e010b4500c044c8500041c0004044640c6045070f2425800f101e058915801c250800484460180c02c1c0a0508105026117400b0001c07032808200a19206150b4801032654000344030440c16590040303019900004126100b04003658028000790040c4440e40c00074103503d140c4100061041016242d40c0402e01c82500c65406903070703a454050380d20a030005498030b103c2c2c1200741d2142c0204d000394402d06415001031103010034400c000380456000721030481c007620074214410301081040400c01004160b840186c1e602402c0d41040b1545d00011120f61030b0010b1085d4001c40c4400b03040340b0503034443d5a400d400400781112a84e8280b81c40c50300b9000d182c104490300e80c40c0e030400d4807101d00400c102c840080024004624041d036664040b0000d400c068085c0c01d05640c03480350b217140c0780c0c824000c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 328397410 1250 328396160 328396163
    0xd180f081c02030a0e1c0906080c19020a06050a0207030c0308190509101a1f1211030a0e07081f060b03090f15010602030a12020714030306030c0d050c2803 68
    0x14018075440b4545e454400318039030b4500010b0311a0716101d4465031085882c81210000e04200865031101c0031000032074042c000300c20101e0006940c00b02c1c0b49690004411030b9140c01800c00300140d0702da2a02c04000d0b846032280103000b0640c090140720010344243e85150340301030700700c3c0281800141c1c50a903000b50340003a242d9004d583c2c0100201407402510303212b140d100490040190240710700354404600000d115403c5141c1045510f4510f4124500425455283c4940c40a08010603024020101d029420990385040a82d1901075032946281c4002085c000b5240a10000c01d8040c00d1003d030080c0c0c5842c108011801c1c0d0761072b584006810071200000e507000b00b01d1500a41403004a110701107181504005c1c407954400404001044031507004012529031000381d2404000d1b0849080c4018040c0c80f42030402492041155050121190040080c0d13001d150105c041c1c81c100b2800c101007200b0400500e102801581000360200698644610114450461095801e600009040c82e0050340b0145500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 328398660 1250 328397410 328397431
    0xe0109031d06030105030c2101021c1404020117130c030803181605040903110a140f12090402090a170f010c1b0b06240d180f081c0203 59
    0x7000241403010755203000440c0416030300d40381550702d04400a0f507a00004000a0301030f0a191030b82d400800c4035215403100c110300c000000e56503002000091000303100210707404160702d850006407940d21417003022414020b0b50141d407001000c104441441c540703890081e101079440100b407403071480058100c101b008000d600400b4110346a141c45000444040c0d020300d0813001d59007000c022101c4040b041d0040c202075400980e00010342240c01d03e801ea81004141d804169a4481d01c88414100040401c3e8000c83c2ca0880c0300b80c80c0101c0c00c00c00503d54403154506412031020043c00117009504080d0301038150b0b010010030407400c0503942d0800d03602d0380194001e0004141c104d1148400400300c04d000300a5210340c0e600d0454602c0520100d01e00d0a6164410001d0482e804007001c541907554140084a00707402206442d070622400ca81c1048980d44040e030138000090421060442c0000900b03800c06003030b07030070140342d250620341680ca074007035940321302e000a00313184120a20040380c142600c0a90f108142c03122 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 328399910 1250 328398660 328398677
    0x10e010c0e0901050a0e0703020906040f030803180714040f061a071103030306090403030c0905060f0705060109180b100905100602010b040b0a060c1a07020c15180607060e010903 78
    0x1400d004009005804c640c4c012010800100b00d8404250b8641c2d520102c1c030300d00142c44000b18000100c0310310495000d810790030072074200030050225080045005440d942d641034828400d000c04903465201510811074420264034004403e0b06003600030a0500107150400941c103500e90300880450401030341d2800800d1000300394001003118824116108207411030086045141401c0001c440b818000d000400f010b448040319010f00780186c00160281c00c000b060a074a0300034116071842d10f50020760080e2841d03c42c20b800010307818102e110300d161010b41c865030485280200d0b12900501c01000e40940724000c2805000240d50515100ea24000e240c0819803e8103d443d00394024250b84003214624401c81c1f520041e01721994800e43d690741112000d0505510005040c01d01c80b072203800c255588540e06850b40301b0007141c0e980c089800345200f01c0032210500d001c82c0d84031114a0a0080d160484042c500080c600c900c60720b001c0000e068654868107000c101000920700c407a081d9686001c080f0040b84018 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 328401160 1250 328399910 328399937
    0x11010f02040e06100306030c0603020903010e0a03030c17010503100c110109030c0c05011716030b060705030c070b0708220b0c06041203020f030f04110303120907060827010e010c 78
    0x19607034514200e4045c42d0074402c03142191140c100e0f011580c0f042c8401c0c507a00045203129924203401122841c000c034000e40d03118841034140a40030304100520310000812002080200190340210309060390030180040c030115050840c4603000b01031110051003440841d40030b542d03010009000e0289018425503c80d102150039140000c0b00c02032640206060220104115100a016904966104031748001c1e40b8080310480109038001c11100e22240e0300820300043c00014480b0002c001c10a0500d000115540541c0d11441d000c0c6070b02a407030008156140420442081c00c0f40c200c10074a024480d265440503103035440101c50b6031369000848c1c0f800c0d076070884400c00c0180001d020001b20114042e04056203004407012001e641d622000300100010070001c4086820b0040d080310b042000e14020f0b00712981d42400c194011012481241e290b002840f52240200f5400d110f04a41e81c01040800803201c88182c0d240c1c2e4024800c030071030a84207455035840c1010402d9500c2401170381c140074461f4698441d11561b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 328402410 1250 328401160 328401169
    0x2060705160e0f0c0d0c120c0801170a0812040615060314010b04050307090f09020a0f0f050f0f09060d02040614030c060703050703050708070203060114030d080106020d11010f02040e06 81
    0x900c003400c480c02c0581006060030021007117030042c41c249180040d00b1080f280054900041b4210a00c10084c039100d054128150460260b5040c0c60358035071890f482d6468238544981e201d1300b100e4014111242400b00f2500c012400d4016074101d481500042001c4400706100601c0107120b501040000b511380c4910300014030280d1005025103164050b492030720741003a0120380d44092502c40d40030300719030b40d0801b205458400c2d13004800c100e0380107005104003652085022001d040c0b60007408400d220030f1100013080d00d40a481e1f0810b002000e041401d101e00100100010240000c1c066600000307902c0c0400c1c0140e80314480d0038090440c2038100c0c0b4082d00380006261500189440e440d002d94010130a00021907040420f071ba003400c0d81894890354404541c644030700c0038021420020b415100e48400400c1c4000c10b020340204801c810790445607806001601200e0a4400303218241c0541c00c04003512070403e20410301251000d80c40301c004a2148040343c1c3c808103c0c6d0040d0710200d1032240510601005141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 328403660 1250 328402410 328402439
    0x40b16081206120f06010605071b0f060206220b04020402070b04060203070315030803010306180c1d0a02120f0c070b040f0203070e10090c0c05030c0706110102160f0206070516 77
    0x74010007020b00c1303044da81e01c4955480060003040240711001c102c80c000c01041c2220300642d61240d03010b0510503956059003410003040da0083c0c901501490300042c1a50245000d03003103584440040c0c40c0011100c82c0c59a00d440c0b0409001aa0030540030051100414040e49aa40c0102d100f410010b030350703180c038190040448946400c41070000310040d00030230100e000d03101620b040d203410030170000380794400ca581c041a92401040045c211171454200151590400b200400c045107040410219540c849410500301e204401c10168420310b0180131801060b004040c00342e000e5003400c1100e00d090321644070300f100d0f030030b08850071210728007013000000031800c09210500092074090a144d42a00340300c42d000c101010300c0c0c011000003556880042d80700f184554180d0f402540c0007829241c0d0344200019498850031a03001e160089209480c0342e1020348414801c03a11408251040044800c680b0741e600160018890802c4c4d91000050240c40b0100b01c09003e0b04a481403015107031510585040c012a500c8003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 328404910 1250 328403660 328403689
    0x10507171003030203031f050a0902030702070603020c03181522090b010504150504090207080d0b0a0501020a0204021305060f0a030f0513080c0a060507032708040b16081206 76
    0x8001c46040002079000415217070000c0c5100d003410340702240b50700c500c040c40e50385a2006d5070001c20400002020b5495900550007204654282c800458407100b0540580c811505103000f00d62003000120000d0b1121501d00e2040304008000303480250400e05110455080700e80c544600c85000c5000e444941400c400d0000249801101800303100e452038000380c01030041d41310340c00002c5c11080700721504910500403180a4a084c031821900c070700c120704020405802c40501e01a0384d03880c1c14a9507009251003282e03c0f040780d005034000d01d0000191350900c006074000f0b21a03080c80c1e81550801042c6580c1d60009404032000c10760b02d10b40c03204503081e001000e84451a255080491500f41408a03810008520b00c1c6010303042480240c0d00c40854001c90b151010180c00504020701d48814068040d5054000c1d00710310111001c140c0318040e00091645030a02c40e2880100201000c1104100007180c4801410650564100420800300300f07442c4e1a081d903101c000038a00c0940700d5001c12401e480c282c2040440300c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 328406160 1250 328404910 328404931
    0x1020d29010801031205040b030a0501030302060906091b062703070f050f01051c05010f050307051f0c08070b010f0914070e01030b0d0c0e01150813081b01050717 71
    0xc8405400680308040c1808060100600d4002e00440c0e0790054089038020702007005010b5991500d0312940004260a0000328014002c07100030030505800004d12030f010381c15a01c050a030f508500085541070071140b040c0301e500040c09020041c00c120344805107241d810f40521030402001c1413501090700b02708054100c91014070605030140035030307201e84211640301c2d0b4081c20025951000c1069142c940110101c14504c81d0b81060300210303400e12640404411035800386d0403204403e40351010042e40200031440d41c180d5a0381c001606181707074450010744040301d01468006280c15880d4840e11a4041e090f08188102405540c1c00c20452800e446101d00c7e404906241c101a400d1407000100001305c140f424604168880108880c01d940c4e000d0440c000c43d13403062441e080396950b50ba03c100406c1c000d00c80c2041d051010b80034581118000c82c41603100d840c3c8140350b42d80e81031007650b074489140c129000c598513210b20445007400c841000d20507540504000e44490b0748076041d0b4940b1504995000f040c40c0c015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 328407410 1250 328406160 328406231
    0x2415180603150904020406030f0c03061802090a0c05090904050d0e0409080a0f05090301090b0a0b2e0c120815030f0d0804020d02040513030f140d09031101020d 70
    0x30705502d10201d0180030400c60381d803021901c80c1d0002174054034180c1c00c041c0546c0c0010b800d0504000b0300c80c50000840f07210350b00c140940101440d0301c411499222002940002c0040b00149008a00b6800b04400c0c401d1818400e0400700b4040108144160869040300d4991010980c55100358011107d5205050111824001c503003990362240356034050340349d0040038000c401500d00d100b03170b005805450501c13401400070800a80c2c1420048a0070300c003a1214000c1c14949441503000d420940042c5a410070004421000802e001e02800c207401101c1c0340d910200f0418100300400107001009580d0080f42d5035480b03000905080d07204000c52203940344400c0c405e40c441d021030a039900e00032403c3c9031001c2a604002295646a00100b0455491403400961107032501040240744c80300320b420f9032032450090f90790030512049101c00b503034280307200300168200c9801030040450034425074100c124001d21a2a0044116190003942420381e0030004008451603100d0341440302e0005600c100540f4880b0045442c43c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 328408660 1250 328407410 328407421
    0x60b031003060509100e03071a040c2108071a0630070f0b0a11010b0306010306020903010b10050319050c0a0c03020a0b0c09120a020102062415180603 66
    0x5896201d1100a01d200d40b1240042c500c2d6a0a02c203c0c404612240418010b2500340750303a0310345070351141100315802d103803105000680c8070b001d10f4407501c40c0d40e1080031901014100111455401620000101c003030740c00070807210005510901411b0094441da981d4900c0007100a02c544406200403e0310b8003482d1103051404010751204100340040f41610004007003100c02210203400c01426030445400ca080d02c1e038001818032051001460088459643c000b0103000ba07428860a80740031003c45580b5034405401800480d800f9401020b0004001700005100c070300300f001096013002e082c04102d012400120401144240a01c480c910300c030942d1340204614a0310040450603401102910b6041040c400c11000c10107008003c003411036600003124a801e850400013620159110907a150301418501d001e50b0100d560005100c841036605802030496595014014100c2c041886120072494982c0341c18906940c4583c095420310b4480000841c0d641c030345010610b041c842146080a014500400400c039 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 328409910 1250 328408660 328408681
    0x70606090e0a0f0b0603160f050405100b191704050703020301180b040b0606120f100504020a0e0f04020906210f040f0f03020c04060605070b06060915030c0705031606060b03 76
    0xc98551002d00c104031510b4281c081b80ca0000301c0d12080c400d601105a0100304a98022030758403c0311021142401581e68a40754108829610f03c90015584020f02148001000140405007003502030b2030f001807242004007004440140c03e842c180c031a504122024025070a0078010911000c09891003062040140c1e03075004403005d80100050f00c0d070034041c80421041e0b070750f03002203c01c4007011044200341420040b1150301031080503901d0540c01c8030010000540c3e41014000e883d960b103c3c5407105904500540140410f106c10300551070b900c140c0c2040361007407076038640d0b0240001c2c40851a143c890b00c0b442c0111844101c1000d4500c07010b0001c1d40d020003000440f55450040380c9644545409001c0d0140d01c0c060f0715040705e00b10070951040c200303180401d0316507015019202c441d0003070321092003d03101d04041c004544034805040360011443c190041c1d00c00040c000071900082c0480b6a40d18125054136040c0c01c3d82c1281c40a10500c0004003031140a0043c0348c003c14000e051500103407451410082e80c0705 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 328411160 1250 328409910 328409933
    0x5130e1603060b0f070f06020c15060307030309140a0e0705070c120206040b13050d030509031e030d020c0a020621010b03010b0711120d0206100801110417070b070606090e0a 76
    0x1c0d603464000220340301080142540401b94960001d8155102d8940d0900d0544174030860072084003a0b55080c00158035850001485003c41e03401d0b8a40d200b0a40c14014950b01241d00d001045801c030000460018150241010561148101d9a540741e02c40d5424507001c06454040c1d80004032110001030800c000d40c3d1900d08450841d0003070901181d031408250b01c0300d0b0521420780e208640c40f50215480106154000d0000c0c01e082000300e05903440000d0300700742c5004a03404034060b58004c0e4014421421030a0280d4010f10075905100c0441d0140100c07640041c0b0264403001c10f41910840808400700c0440000400b80e0261141131071150556040c0010423055010707854000c0c1210040c2062400c45840741d15840385441c4098007940d4a50301c0240b4080e50300c10060b1024122115000000580b46c1d0040c4145c164181904281500e0300346803050003850301c00c2280c80c00c02c150181d002d0008100c0542c03c0107005452250601044991903c80c410080341c012183c4400c03240c0200e2215030000d002d803030700d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 328412410 1250 328411160 328411177
    0x907020d020c180a1d1c08070203180609060c1204051002061302060306040b0409030c050d020f060f07140406020c190e060409170a030501030c0b0a1e05130e1603060b 73
    0x41c01464800017211000c604d00d005090310701078417065150f0010402c024040c505480d842d078030010780740c145040780d4903c1814001144841c1c202426451403500f04024441c07500010300036414a1101050382c5d0405540307144090300040700007000c2016080c1041030307120804d01400030f05214035194402c541c01900340140203104034000000030b00781e580d65521040c180c800c0034004221a1503585000303444a11081e800307560921400d07a401186030f00c0014221030070807a07040903118685805110b034810040207800b0106115140032080900c01c4c1a801800c010480e80c1e0050107440e220b08140802100c6a0b10340d1801d000c4000c0d403c0c0f11001908088540110301514001540400390905000803190344840c2084058000b5401c0155503054021905030b078010418500143d54989900b00f4911506003424046001c0140c00841f48018086140091a00d42482841d001d041c40d001d5a0364201504031b0310044a140083c0440303600c0d41070a5218803803040c101000900d04005201e4980d0044401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 328413660 1250 328412410 328412431
    0x1206040c05090a0815160f140f03090a0c0e10053307060609050c07030e0a08060106030e15060108040201121b05031509010303021009020f0409080705280609020f0907020d020c18 78
    0x414031659000c01210609c1140c1103d00c0c1c2c483c2055040292201d00f0550141c6488048031400b194404409240300d000b04d5004015007045441c020500105100560b101d443c1e0a4a200e04080038050700c04401d2a950304910b4026034860003072410204a40311508a41507062924040040194490301103030092509800c1c60b100c00020f44c0001010154640c00066003402007400014040b43c0580040650031751510690f040100d03220810354400307004a0b11240001c801c440403030050750280801588032002d8202c0031a41d662450404600e40010540d81c2c40011030001c00c0000000803044030400a40381101d0122595140d620b000b03644428a071000f00302c2d00e94450018045607110000065503060240050001c0b24140c1041c0c00b0315000804180c7d09801207440c00b5080e440396914481c0309182420790f030310031a081611042d0050640d05c0080380c020507000150380c02661082c040d244108207c0d802805440e030414002401c4c031801d54031150103901000382409420140c0c141d20342c0d202c1c0d0441c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 328414910 1250 328413660 328413677
    0x5031228020d02010c0512070e15070b15092a0c0a0c0906080d0918020c0609060a0b0d030203030c180616171206040c05090a0815160f 59
    0x8890606201520040a40c0d0803000208088864000c2580749001030603030000c02c50381103100404d4525114a01107800ca80b040c010004138080d008500c00b40b040719014004c2c0e11952404600c10110b0783c0001802d4450700002802c1048071524108404110101590b20b011030303003484503540080800704880380743c1845d4802ca00102e551080015507480b1241d6034103c0340b2141990509071910b460314060035240ca4240345011401c0d24000410100010752a43c6000500f40b61092624540485105865209800704680042c0790f1003081a14014111032020b451107007485074440c412213011413900c0d03004503082106480402d4010041d80d52003049920300550b64009002e0400c42d03401400f2400d607004801042c80c030082c40342c82091300e848510513844409199400c80808031b50703010ba2210801a1079a034400136046041c00d81102416a00504100b4181025040018141074a98029117120b51050f00c0c044036100000b00e1041d004040801d81d07008040141c40b006020341d400040e6241400280c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 328416160 1250 328414910 328414927
    0x80a0f05011814010e011407120f022109070b22030b0408040603050f010f05010c05010b0901140108060402090102070509070504150f022a0f060405040f02031f050312 73
    0xa40000c9a030080c0003801c0d90042c4520f00c0c1079110b0403000c0c207000302550710307125080302a40e03414400c07030042c10b00e00c4000c0c0c000740c0d0b1403003170442c2c02a0488090702019515001d404034404a140007400142c4100300020019803815807404413403a0307008003140c41940c001401003120108110880300f98690010340c14024850b0400442102c0c801c0e544018218112201000140b080c0c420150013aa00599070a00c580d071074a501500e00c901c028000d841d13074010300520411556000710b2038034010701d125200104510055000195a880303090b48001111240c1d407103061055a4000126603108404507800c6051004400c0004c1d0f85280500031240284a090b000c5004603016070141e40040c8020200c05106092078040108400c00480c81342001d0311070080d042c00210702f0700d1144420040c05041041e024034800007004030940d4010561a0448400c01001ca0651200c0c0181e01a04d2074620026959080040d403400600040c0e1120400d850720003d800d005594011880c81d144081d0fc0156548840c0d09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 328417266 1106 328416160 328416163
    0x712180807050120100c030b04110f070b0423011401050f01140a03020c10061d1003030c030e060307110c0d0507180204080604030903020f0a080a0f05 66
    0x100003038480c1840313040c000d50050b18030361401c8135508000441000f003140ca0002c400070003e521401d07080c860781014051104860b40400141e85003009a01e00c0b40c101e800341090080480c2a80c901003828420000e601c0081401303102517101c04c84040c200d203107001340030071840e030700750005030800024052901c0a405100f440041c0c6450141000c10085102c0c80d501003000042415800c1c0003450443c0c00402020f4800072040d0346c005030701c1d070a150191001140040c400391030507803085d04005c05520b100740c8440c100d03030f810f051014242015280540b4400e460080e900e402546c0402001035241d8040b064680f0300c00800281c0e10204640e00c144000f804840310060966400441e04010008000140c50410005140c0060a1980314203182e4140394041c0d070160001081c08409009618184030070805019045441c0c004040c41e1818441c0c607500c003038001401048410300d659050010 = true := by decide +kernel

theorem cover : BRFrame.Cov 328237410 328417266 := by
  have h0 := BRFrame.cov_init 328237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 328237410 ≤ n) (h2 : n < 328417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
