-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2689
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:26:39.753429+00:00
-- url     : https://prove2.me/submissions/9e313fbe-587b-4911-9c84-80fffbaf3a90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 483453237 ≤ n < 483633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 483454487 1250 483453237 483453241
    0x2040302061c05090106060e0d240b100f0c11040f0f020c07080616050d15171005010f330206070e180403030513082101090b0a0501200303 61
    0x31000c1e1042040032144001c0800884d1942c2c02c0c02c5080f40c02d40c0c8100300114401d5012400f0310700d00480184400c074082e90307441000da0319076842d0310481d008450081144565401c859091381c14010b0060844040031b00381f004d1008030f0b8820181c0800a811402404880c06807400b02c4c2e251a550480f540c10b00a2003c02d00240e440c03401100040c0d088244039448900c241c0100061018002030740300e0052091401032042e5510440c0300715150f0b888446084459502c40c0920382c0c030b902034100c6140c002c1045121034021100010140e03420452032040050740d0504010041c003044400d0509501101c3c10003d0842c80048906005070b241c91050b4159803901c0801c03003160003c0707a004605c441c480d40150b61440d120b0030100301001070218515400b03400d2060f9100026000030b004c0c1d4030498109803070310314510340383d0429900c0c014540d004000d00621700495a0001648240c540e018902400101c00107208802d100d001260030071885202d07840c1041a01201c01410700b8005504007101491901a03e40c0c80c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 483455737 1250 483454487 483454507
    0x80a05100803040b120f061c032601060315080712020f0333090a0b1e040c0f0e09030904090c0f0b090901090b1e1203040e090118030503010909060204030206 69
    0x950003505040441a4174000010320305070000711b04600c17a4400400d050b130800c0c1030303004035003250801020450511010350343c801070000310315558200c800c0981002ca190366060200003000c0c2e0309030301d00b0380c15001d001410030300010740046030542c1650740c41000038114585d2400002c1c10101622411030b094018010f202d200303031407918125031195007015000202110925040c650030081210800c1d10f6801c200b80190009502c03103090358011802c0700c040354110000510048000c0c40640702207070aa44926810031076406090140700041403501101d003500c2c94140701e00e94480c071071903104038400e80ea42c040300c0e0100310524441501429003890200c001075140c0c60001640d80c0500030651290722240c0000581038810300503a580383c030000e4146505441c0003040c031a000f103181180f942c3d2010951a0344084030004201400040c1000404160542090a100703821035610010411940b003604207881e02003500802120704656004000140c81141410144000e00503a04000e40c03003500000c40c10b140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 483456987 1250 483455737 483455759
    0xb0a150e060a050a0605391507030905100509120a02010e1504020607021002010e011e06080705010c030e010903020a03030507020a050f15090f0d030c1b06080a0510080304 75
    0x2041400360768481e0b0403511001041380c1101188900400030b4000c11410300700344548801c440030a000c2462000032420828034070802c903aa0401d5100b1664440d040c0c00941f2901c1c402915000f0106040030000750420751502500c0d1201420040b12864a61000c24070b00c880030844c0000130b03284540002d441e6901004000d01811406061303c0b180d01c110041d0103040c039000304480d40140c0c1d004242502d44005035003480001107103c070510065540e11014000710300028002c0b130b0f901203000700400e00c0800c000950381d02221420f42000c111070340300810a2005980040c1c1c82c82e8055018140100d00b9800100100e40740100360304003d4110030900700010070150400c025106040c4200d41d820000d40d15034043c01b0711841024001580b004820362201084500180105500b000c05480744a414040e42c01180603144028821400a00c480001d00107001d032a43c4400d0902425014803440c0c0d44c6001c10040080f2030180c903082070a50340d04081100034603070b0f850750001807003074100356503c3d42d0b039454000e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 483458237 1250 483456987 483456991
    0x1306030b0315010611100b01050322020307120b0f070e0904210c03020d08040c091e0e06042006040e09160303020d09060c050a0f030507210e0117040b0a150e 69
    0x21306403141c0351b40030901000a020300a4405410b9403880d045a1720382d40c55820140800c0c030f18000310445c01032940c0c0561414490030000c0d1262411022408800345800c006488000341016099103520b800c0c420015841075400c98240011101d22450780c440b1704000720800c00380050000c10003166041c100e0115081210712984a00917001c2d140c078030000e401c05542510007128010300008050900340f2048c40c8940c0650403414900f0421410328802110410803140100c940030f1455200710108000c114101f10440048181110420000307468000401d50340e006501505080c05041c500013138240d01d040010b0900c20f02d90040d0f0b2030100d5624240a0344800c2801521700c00a01213500115115000307207504444594448001c140e81e514030f46815401d0580f140f000c6042060030014000440c10800000c0040021000d41c0011802c0000c401380c007840354050140d05101410702120f0700e810248940d503511981205014000344d0b20310007100020010304a02840c0c80d41d058070041031584800810034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 483459487 1250 483458237 483458267
    0x81911150a02240603100e1018020306060d03080c09120a0c06091a071b1509060219150f020c011505131509020d0b040e030703080c1306030b03150106 66
    0x81c1520f11000038500307044a04031202c0307805512042420980c0e00d120740c0b1280e1440f10b6001035400c00420001d0a80039200f00e94814074186070788000c9034085d403400f405550b4108100302c400c2541101542d5000d4083d040c01043c2c0300401001064442c61900c038203100d20b0301034102000f0707526440003520b0031404103826406a440052100ca001003119480711203c0b140c0b24503c0e2803203030705001007607803012400e001f01c402c1c0380c41c40c80c80c8590014a00d580303000589000c0b541ca85504443c1800c0800080c5080c0054001c40c90f1b51402c80007180110319032080b5000b880714500c901040c031184030300c823140c040d101f4800c903446258a805807424070940c0f400e018106032030044450117003848004600d44140c2d61801d1208460406841d0200101a410741c01001c1411424030085050203d5900080490381900d030381c0b0500d80c1000807240101980542000d031310080b003003e46030900c2c501e8803081000107101e00070217040c140d94185c0d4085942d010809110b070588002d02c120030311b6844003001040c80301030785412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 483460737 1250 483459487 483459523
    0x110a0e190e0f0a060f090804290403020f0f010216090207232e090804050f0a080304140a05040e010e06070302090f01050d2013081911150a02 62
    0x2014030340861000442d190b080002c1526218070348681d0024000601c5040700a96610b2800c0009000600940014041c074000350f00004013400d845018181d450a282c403110404010900040c4c0c1c400d82069101e90080d5410358130001c1f0080180d241060444440d5000715099000081c200c0c034940081458a20440c1e412000340b00022681c982c5881003944140e003030304802c8001c42034021440d0b945100c40d071b451310032141c18058800074804803200100c0c250740703036100001c1c1405079041102e8607040801040e18081c000516000005840c0c0c0030b140035080d009804991a145140d48820382c040182c00c00030000c221940b10381107140d0013414805d9600040b80690b000054a00d0300903c25a044184007070030081c074400240e401128030f41e0010342415180da0b511558504c900b50310f03440316104418588080c0e95180013154518028105581c0082115403200007500311b4550010030800c06583e11841e680c0c07940410500080e401881c10220b07910030798001c01c00da03010b1540000c0000d070f20341e4030220b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 483461987 1250 483460737 483460751
    0xf071a091608150f1012060c090501020d020607031a03010f06140909030f0307050f030f040c1e0b0702030307080a03052226040906080312011d04110a0e19 68
    0x9850b0300d81142c09480f098410540000480d1001c40140d41035100c1d050b03007903820755242c45d02d040e02444c00d540309003503810076a0f480d0820030740740d003002040000d40307001d000901d1410308421000f550361000400000c00c25440d00c01d070a02042132200d03403141c1b101e0700034004c0c480c8071103000780c07440100200d1207400c10700b0080140383d41c0d040c1481d500303090203034107141c018610f80301c120004100c0980c00a884941000810080d5480c00540e00010390701500c0800c46c0c0e841e0300d05003414100c0500341c880d00410b45902d004254218109995880c0f44225140c8584803512050b0a0000030f0a6000b151805131002900090301c0d01000e0307040d404240708030030724028005a4420026800720b80b15803558010300000d10044030340d0b80341500d42e40021f03c1480440c0c03070518280d00c404101e82a01c4490380018072030b60000c602d2184480643c800d06002d01803c014040c07843c0d800202d86c21603820054400ba041c030411201d01c007035076164860400e01601034004003103501c1c2840301e0700718803100550200907125890100d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 483463237 1250 483461987 483461999
    0xf11040507050d15030611031522110d050f0907151205040c050a080307020414040c03080a02010212191505010503060f0604030215090909010605060f071a0916 70
    0x466240201550340e02c1904040c0007044000c018203e00a14841085016800100094482c060110510344805c1960744a0801d10750380d902d1001c07880f0070144190034016054002e02103000016155030281100070455982d1050300388080e00c10f85071880c403940c1c01c00c01044080788000d40388600414280b01219901c0b552842609c0c0084d21001e0b420b4002843c410785112203a003141c0202c1c2d04240504c4004001581d14070005081c0e1135540d209a80c070f60800324420b0b041d0310b0f091050b20358160282d42c8d0f10001e0f2426644512542c811408002c08048020a103030030558405d6056036902e001515010f0524100415240c04103000d205c0051803950802c031240792401c610240c0d034411100183c580324150340741c0101b00a0344011010341d40e90000018480003000d43d807210321400c0000c0f4005d104640d241d41e140c4c01d005a4420080880b10305a04100040040e134540004030707404140b907031904a407510040d2402a030340110588810f21580000424011008400700320704030310841e011080c0b44c0040e940e41d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 483464487 1250 483463237 483463241
    0x60f08040b160e03011401090b010c02030c240d05061f02060609060d080f120f010b04140103140f01090609140105041a0a1701060e0126190f1104 64
    0xc5004100500800204545114050300d1021090150810b8034101c650803010a007100d2641c071404002081171001000380d00c80d81c0c40303295079041080c81c2c005020601a0082903640c0e4882c0405406560040d140e11140c50282c0d104a070062500c00d421940c8001d540c8610020f010162200c070b10507071441d85100e02c242030102d640c504406458010b403000b0750319482080307028140181401e07001400460300c100000d81c03100007005e4101e18200d80c240c6550004100c1801c054008207621204001500140001004401543c0c2180c0400e03540290341c0e200700c00101c01070020103e0f074003044c108007828440360b880740d411301c2c40c1a41c1c40ca040c01c020203030f60791000400b61601409503010382c2c0c0e095801071000d414290004e503c6108011124001c000940002c41e00c4103900d03621420f041409942504130700402030040c90300400c22059641c07169410702a48103400c1e111594140c107007240d65a076540d2440000e10250140700c140c1f02f04003901d4030840c1407400b000711030300c001103d1880b40d42c0c01a00e0b083c9098 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 483465737 1250 483464487 483464491
    0xa020613050604020d0809060d020d150b03190b0a03060b03010e03091804081e18030c0105161a15040b030d020c060714030a0e041503030e040209060d0c09060f08 71
    0x10020b086503229a028050a220400e4041c5c9090504214a41e1a616003200074004801503050050b030320044107681404a03041c0030b050360f042c9045500100042243c80c0291b1342c10401c24040110607000501202e8001e0507802071441c0c00c1000c4032000000e210f0190321299088200360002e2001d191129a02900c03032042a82644d0700101c2c00740310310b10807628909210350291080b040c0501c1d0030201100460740c1c0104000c00c0880441c00503800010218200f520b01c003c00d8180c00402d40a007220002030b00758001c24204139601c0305180880c00501c4220a0110300303a42072401d074099a03003444c034515041001e0040505000b00e0070003802c0314450800060035130f84c0c41080c1e07019100300546e201c10013940d40c2c4059026201c0981141c0c40d0301080d001130005149074855500c500d00c0c21080581440709071038020800d0110700e1b201010410200344c0080d489646002c2c116001030342c91000700d002039803034001ca070048442c0500d04034045060130303040282e95003594816101c031880315485200860340702c0b0007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 483466987 1250 483465737 483465743
    0x5060102100908160201020c090108010b01020f0d1b030c060f050a1505150705031201120210230a09030b011d09030f07080d0e030c01060e0601090506091302041206020a020613 77
    0x800524006007500d40c040c0c0501342c8144140c5601c414402d0004540e5038082c1c11080360b1b655188041c0c140303907130100600303012071074070030080c02c208090744c10084c108003403a4020501c880d00003e1442c0405206601c2841c1c45940101c0800c0b15900b481016001082d0131602910050716200c044a8030f0b1280100d15411100b0003418800c00b804c25201c80d110641102070121002e100034404411070804401c0118003910001001c80300504040c0100040b482c803003060441400743c0340d510407903890145800480a80e040d14041d42d610030030858101c600a40590021307007100c1d0341340c00120381440c5074003048056200d592010b1195032569203043c1c0c0ca034440c101d0040407200081120000145a00000e040e43c2c07440703003600240603082c01e0400e42c195400071580c039200365541c0d541031042e481210b02d0140c00410a05e04250303400e080001184003071259001143c0700f042101c25a00c040a00c03031b01100c0140c031203d0340c080d859040a141040107900107124460260244000003812588901c009408c1560 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 483468237 1250 483466987 483467003
    0xd0801081908030c180307060305091608060f06010207151d150d0e0a0b070804020132030a150816120b130c09021305030106141011030d060306050601021009 69
    0x71340e2200304005a100303003100200c02c0020140858a607409001072030050503035490120701494101c403d581444d10041e0329414044000c881030012207400110903034001e4040040140644071540180d01c0d05155078001c4259200f1044840900350f4891098020580c0c0c080c5407209516058080091100d4120041c05603480c0512145a0500386c1b03400c95007030f4800610903940550520303107a90916000c00c803150340c04200c65200f80011941e100c54006803558019091300e00401c1f03000c01a232451100c04900e5a42c818003c000b0440c0b03d111944400a071031032141706204000d5840b127032261100800c07400302e0300d5055000e40000e0114580d00202c01e115500188682290340c07582185803c01e01c0519040d640b1a540080103d81400584000d004c95200301c415444428a007104050075103400350032040b80300c0c12004d0701c10b0b203589851171032810074541828200c190440315803140c7e00c0d6020b40729015042d60708000b000030502480d030740b141c4c0c0100000e0303083d1840c0441205007a41525030750310300180342132 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 483469487 1250 483468237 483468241
    0x11508100b1603030221180a02060f0d06051207030219051507110a060306210b04030e15030c120a0e0709020a0210020301030c06030506010c15050601050c0d080108190803 75
    0x40034142c1d01c0070085100341001070920348410a0346840c103152903202c0301c01d10151424408007a40608440b4000c420581c01000701003107942c01310b000e6009007004d500641c40e002c580b90700d020f0400d8004101411000e4172242c2d10404482c101e50791200c02e40310590048600e6001e91500b9040c17198064103907903016183c00507401c040020071690754004401075a0700450580c000120b5034070701d031071000285120780d00441c4403414950054084081c611180030804080c201e1900012400141a0381c8281c06d03041204d025013004e00400c0300711194402005100d0701c004100844108410017500501c0b44407500700e00d035683c4442600007219182010405c9543c400031040102511940051510311840c1c410341c0e00144542990000360303002a0412600d5a485240510100741e051040551008013441e00441503801c548030380e9281910300054000d00c540b40c00c001100c0343d00403802c6030722250122003198100b100740d20004111200078041d1403500d00403c1c0b100e1303d1b81d0203d4581110003a8000f030300c0d02e00d16 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 483470737 1250 483469487 483469507
    0x50f07091406070501020c06010f2c06030106050909030307030f060501050904111e1c360f0b0609010806160e0d0c080304090f05010e06101106011508100b 68
    0x3001d54030711880c1e4000b00030420100040c0003800501210341075400100150b505041d44003100c1c15690300503400402c10700c070207801400c00c0b20b4140110400020b0900c1102e03150322003c603015000f980c0040b81c00892000600c00391200c0000110320510710303a40c01b040400c10000b8410140e079003c1c4522400202d0070311100505242950001c1541007000c1e10031071420700003001d002080401d10001c0505810301017200404c4540004000d0788140d1740500801295001502550f0b00c0310200c030180121030030320b1a83c0c2c880c200d175450080c650a41c10140c0415100e85920380100a401d04403080c80c007400900340005901840040c0e0035028903041403001c61140c031040000c54180326841c0f091580040c102c554500401d00420240014180382d50156079540d081c00811002e642010141611080c60500108010100da103801134000c4402c0303842102e46480303101c00700c1d90f4889030030000c0c0060040308000500034680c211648820348051f15103480325695904000c090036120b1040b0101c854040080100c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 483471987 1250 483470737 483470759
    0xc020a052d06040518060d05060702030a0909050f0106140f040b1923090d0f060e0607020718050921090a080c0d03031107050123010801091515091509050f0709 70
    0x801b14020f0031501869000c0d0700c0752850312405980000158200280009489902081110181c80a071506015a0400d0010000c01080522406040101c100d0a05880c400b0100484450412007052181c0303483d01d4200c0a01180d0141c400118103c1d0b0030000f050045005000802207541a101c05070181490440395032800c1e403001222980c070000c08400d11f0b0003d410ba006c4c201160340108000a4045000403c603403608001a24460645d07004c40810069140e0031030089400d200e10060100f41910b806511601e0103003204a18100c008000017014017043c0110040c088017a01201d038095002e540b40c00680d2282d0740d003000b41c0d4001c06082d41c00000329002e5001740e28100c41d040081c0c0d180c407c00e5164282110318001004244d462111075907120b002d07a01a41901404000d002009100c0306540c03a42600c00c4001a022a07864403180e1500021846840400051240800c00d004216580d14001c404603140c0c058000c80a1601002c60a240448105540f24034101d44071a1078040c10200744400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 483473237 1250 483471987 483471991
    0x1080f07120204030501020d020711031207020d03030f1a03070b1612020a050d09050a0506030c0d1a0d0b040501180203030f030a0221040c0501110d0c020a052d06040518 74
    0x14182c08010000000d1000d100034803e400d141200140c5074101c0c1e26003500c0480e10708131807520a0f40200341514805103010100d41d0a9030f8122820703c0340582c14074054024001d007080d6295402d00d00800710001c43c60071103030546040300440540e800340f40c490100d170185001e0304203600090701d028103041c03001800c100010f0b844049a40100c501864072a564a85441400c5012100040507001c0812490910b8022031010b003074102c0701141140b03003090030f01005005080d10b9038000c03034540d80382060310b030403495210440c4d0401610201151045040100841205a40840705580780031740484204040c549806111980280950721b40704000c41d200c0c125030000b4000315a650742c03c200580340d040c4403141c88080c1c5141d507041d20000b407400d07091209184100d40c0c006418080c80700140c450540010800d03140c2c502490804004925240c000700e5207040d41c9411042c1c104a03540e0b00c40044c5408103030800f0b00118090bc108556441c07002c144001c13400b662250981060641c8031800000840704901c0c1c2d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 483474487 1250 483473237 483473267
    0xc020705040207050a2a1203080c070f0212150907050607030c110402030103061e270f02060c1c0306030b010614190806150403020306041b24030b01080f07 68
    0x5d10046a1034a51109500104024000503440b20b07030954022500c0441000041107022810b40b401205910003410a03900109072208102e40080d02c002044807104d640c201103900a40240c00840b500304007281e41e03140718025000125491380000340c0b04400052a05c0030b450026000908207402550300b0b451004104508840d00c01c01d4000c5181c0b140c845201940c0250b016540120302d0a9480c2e01d101210201d00d030040240a081c4403a44589c5080401100c00154070748820110440c2141041a46c019220400962000c400a0034100c41080004d02c543c0110784450340d00c1001c4204241501207640c10300c00184000c84d2030307004015a6000c3d83c003090501101d035501e180350000030000e9441a07070959001d1800b10b12040144400b40c00c08a10000f0701a200d004800d10301802d517000030b6503c1d440280000d22900c0e200068541014003a4a81c0d40280009070361b42c807105d108070496125081301000c603140001e1901c00b00190070340c81120018010b00100c010f00656841342c05049481d45011501c0d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 483475737 1250 483474487 483474493
    0x904060e040c15022b080f0402011e051e0301050102070f060909050a0605130504031407170307020f07060c051005010e060d050c150d0605120d0302030604090b090c010801090c02070504020705 84
    0x11100c2d00205d05400484502c5604c8884100d50060301c020f0030310b24000d4862401076095808000050760001c825401d4100d0300b21048c0d01d5000c004100700c070180b18245801c2d448042d002c440c07444000f00b42002d181a01d109030260380f02c254a928010a40041382c0c8140d000040283d0002c00039a4116441203401052045004c510b0545400c00320750301252035804003010b207070740e48200b01c241540b081508600040703001f01e043c6021090340720044c0c80c1b6980d28859810301000004078000a00801a005034042100162403450303551342c0307000e4031150050740269054000d05c03401107416281841064162a101040c210194840c40180640310b404940304451521401071458030031358401c100c02e131303403e46051601ea644841d01e20502c002c4e2011548240d02a03401e50288a00c0c200340800d45031b050354207d02d00161603641d4800050082c0038078400192511001500b0306c0551040402d000c4621282a01c80b282242d90701c400e858211200c01c5c41600c01600200c03010300840c5000d40040c81c10764040da0407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 483476987 1250 483475737 483475753
    0x4050a03030b030106240f0f022a0414010311010f050a111015090e010e03030f0a02040302061603081005031f020f0309010b120d0e0607050a170904060e040c1502 71
    0x148142c0c94101c1410044071840c0071054a1b00c996015144002d510124507149154003a20b52000e90b036003400c504240c040d0040d650b40a0410305900f03010b0010200700030710502561120301c24001e04a10300380000d0700c481c00b08589904165014031031030341c003102140d9182480e001c22a901114800c24010141c071480c0940030404406440c03a0003621490b074a2843c1100e00c0c1e5207070100410868403012011140d590400c44002100e07007010080e070f03601c400c2d0609503a0043c0c0e20411201e000340b14981000390700036004156081c0c03030285224210307190b510070344400c107442d20303041c501e404600124460a03038140d021116040c0c9001c01190f02079a0520000005801d00002405200e1a500111340d0030010342c1d916120102b462402c040c0320300e10094840c000d0944090221401422640420045405070500041010802204021908420303400c04110b0340030000e00c903484501c50748800e0307a10b0300c2141800700119071100004802400345510111426519103800558403030201082d00e00e01c254010580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 483478237 1250 483476987 483476999
    0x906040504050a201803060c07060e030c0706180501030924020708030a0b0a23010804020d0605151e180a061208030702010c03050919052406100804050a03030b030106 73
    0xa44600f1303070b6020148150b01c4000c01641280c05032039075030b00c039442948410248501c50542c20200d07211030b900b010380491504101e550041c41d5200f6150710090500c140400018107a52028410107260003004d002202248d40344011030640d145900c000d0502d190700e945038000c00840c0900b501c4503103000b82001d400c003902034541403001e030411540c1400c060746a02c00f5200b0f80c0303001040e580203001c0d51217403606548802003601020a9444410f42d040c0540a0301243c15035441c90000c641841d0700c598240014900711810704266110085c085005940584c42c08208800210300c0004800d000303440b00c040321680c620a8120f5100141820f07124580d1000e020540b01184151100294001c11865580b400d0400b002070071108060780c04020146407200f8000e05940100d650910364038103070fa0318400b50390b081c100b15042101d000c02c29000c446820145150000c0c94500d00c5204203401ca40c41c000ca510710311015112120101c6008101d0b03000703000180c3c0081d01030741c8480c60b82032001d80001800380e1228 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 483479487 1250 483478237 483478271
    0xe0f030c0a03060b0306090f0d110c040207030f030b0a150e130e0307050f1b0d230106060e09040f02010815030601060314070903020a120525050a06050906040504050a 73
    0x20b0400e80d00652210700c0c04030581400c1207115000307030100000f845045000c112054540c008000440c1c10010341e03d04150500900700408205240c0060046540b900985406001034000010450120b0b0501103a07003800d207080c000042c200c0d4800005140362000141003200c00104510b02142e110818030744503104081103101d0072a480d600140150b0352100c150605c0f501c0e201208039403901651117501010342c0d501959410060046054030860003c1042c0c0c500080b0404480f1600004103083c05040410088150003603011180c2c56200c0800d00c451000901c0030000341118003604078a16124180d005502c02d010b5035038000812000c99000c155444006400c18400380e000b81c0000347c5480c01d0b200c107003030000002500441c0301e041c16040305284d5404100040e44c00e11611031020a51404002400414080010300c4202c0f03001a10000002ca0b689040e4403060f80074480c0034075002140421414016421210002d40041403107040138580702c10403026100c01402c0400b169204c51240e80899104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 483480737 1250 483479487 483479489
    0x20c0907020d051b011d100204030f0305090402070209090607120212060f01050705030a0903030917070e06060408010504050616050c030f09010c0b0a0917160602070f0c06080a060b09010e0f030c0a 86
    0x210300907a40c820040580549008910884810908d20400007000050003410702c110016526050140e2075100100024000380282c0c04040e4202d4411800c002100401090061041400c1d0300c804001c404045a80350488c0103264105d0030386140c1401151a525102c00e05603400d61051420318a850300341e51f070710350031504080402c0d1302251100d0b1050041682010001014040c9000d44030140c0f080e08144560741d00c0a840b4020900754042d0116005440b44803c4502030b15000000348918245854100d644000480b913034400942045480e01149101c0e100300d0344104a5403004601b0603e244201410743d03402600120306008507410050b0002d6603d01820380700d46440e040000c0c0b440014206503401c0d01c06140c205da2400020452a840c020001406500301a009080141c84400c1c07483c1c9001200350041d0090520204e042000450305d40c45a030842c460030740360b281400125603d200c1042907004000e0309070b002c1030304a00c010301c0905002034401d0f40713aa001800c4602c81c0c2c0075007000c62200e2040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 483481987 1250 483480737 483480761
    0x804090b012604020112020409020a05090f010c020109060e030a14100f060503070306271419080405010503090c0a0b0c0609150f0a060b19020c0907020d051b01 70
    0x850800d10450360b00581c200c01e120304401c00038014070075000a5020034240c000c0c0000d06101012010111580080e03059a02070007450381c0071036940001d194050016004080f44a1103001c0c05070201d00749501c07032000000d1f2541d060716618040c0342000010364040c0100201d1507010701c1402c080340d02294100280403403c0000d603000c1c0c80d005084541d080242c880c0f0111a486290400400300026140001d60500b201c0c1c000e18001440400c80000a96408650760541c0b00180c202c01100c0501c440c0c01d0b51040701111480c200e54000c1c40e80d03a1308915079203c00402a140c001c040c08204202d50142d03000b1584015008151241c2a0070750b0001072203000d468011440c1c1130804940c00e05124410004103400c03040b000018a1204280c41c0d240c1c004490040c500300049180402154100c109070b044100a45a0301e8405900c5200c07003618440035042c848c007158010301c01c8280300c26140c288104011702641003940580041440068140c2e01507020f0707030403a5806c00b0311041c94101007200307100348100345d50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 483483237 1250 483481987 483481991
    0x1020a110601141f0c02060a1d1012020c070306020403110a150c02060703110106060206092b03020f0d02070308100b07020d030f090b0403051509030408030a08070c1a160315051c080409 81
    0x406210127407160b008005c0e005000b040702c03007116449141c1000c00d1005001c5407440250f520b1100b14007072420302c83c07950704c0109aa80080340100400c410f4400030381d010351050b03500b000169591805400013101c06801200401c00001740c0801605041005041d0a80070342407080c030340300340d203d034080c01c454030b951003440141c02800900c000e880040c44803a080307402c9800b80c601d5444226100c641c2040800d0343ca41c1c2410350019003800000c0100041d076800d01200c280454503035115041c003404190041707035186001d4612450201d101c0e8100c4050310740302a00a000420403101654040c0c9001e0f40036103c110030b010101e4030004501480760000c002540c03041001d00000030700c4401070f104035903018143ca40590028802407102e030a0000c150390284400c1d03d1b0a204a40303030fa40d03081c1d6000740c0065019107082d01d0015196241300e12030341ea041c0500d070700b414005480412044210100c90101007020500f04480300300304400c0c0351505694614040d0405109548420703941c68286951080d0300c203003545a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 483484487 1250 483483237 483483257
    0x12030801050f0102150f0702010912120c050f070b0a021b1006080706020a030c06320705030105010e0f060c060708090f0625090801020a110601141f0c02060a 69
    0x1040031249680000e000f800104951410301144e000c130500001c1c2181c1e081c0c1c2d410302c0051f140c0d6200f5041180c04541000201c16900000301000b0f101c0740d00c10035440a00760401d000c0481c2c0310b20417000c490076000c1050000381403a150355508403213140054184810b103078007403004a8510710390001064880307100e000204441c7c0f044120780001c1d0b6505a01a1040c0e80052104008807030b00494239011803503046c50007140e040724a1030900c0c01413913511151415081c80c20310900314060324500309402250421050052556011021506480309004e0940002c0420803180194103282c1140790307181034000c00c40d07410903070085000c4c7e20741346048419600003010384080c13100300101440320064808503d0060304440c07030070300b082e41480c0644840d1001c00441b4030315481d45140c8584a030308041c3c848000299031780d18107120000c00d0300a40d20f200313120b0341c0139a40001a401c0c0b1090603281c402040600492070380c1c0820155925204440840070052014540341c140c010307941d490051071044081d455400c07100b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 483485737 1250 483484487 483484489
    0x20a030e030601050906010c0602070b0f040605091b01050a020f06101d0405191407090203150a1a0c100e030d05420310020d0516051905041203080105 66
    0x20320481103220340241c00400040c00b150301e0740c041850303000700203082601c0e0945241c81c001009100d900e502800c01e420300e00c00d001210144110103401103000c2e40e403c1c00940c441400e801c0c0c8401c14004140d400c0c4c40c0b88894030300154010005800b4000050054511845d00811640c2c108135045840c0c0f20382d520031600a0000e9506081469502c02c1c501080e0206860a941d80c595114915100c811400b0005210b00c0104600f070340041c41500e80c1c2d1410345c1c00d40b50fa240b8944000e0340050b101c802ca03004007500e40c04860f0a0044d503c0d001c4600e01040d080700202d500201415961184150041a005021310f81040c2541e60051742c1841d01400f0085030395006002c5a4000c40c0c0001d000f20503a894040346d84610200724040c04080403c568400500600044081d03601c650800e441e030582602518081da98000c100d50f000d13109501402801380490380c0e404216902e1100404000e102085043c0851b8011080345c1d000340322441e0850400c68a060780346c00b5551069541c0306011800035401e04014411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 483486987 1250 483485737 483485747
    0x30c120a030e030f0301061d030a1b0602010b0906040c180b04030c0e07211805030403021f0f110a0f060b030c0a0f170c060a02060103051603030914030c030607020a03 73
    0x11803814002035401d0003104c40c1c098615100600c504004c0001e020b4007220025080055640078450083c2218501d04a41c41d0185820f80c807c00d510100ca44c030190000b40c0240180580308003030074010940e00c60307651141d0800c4010500920200200280382584100700c0c41e06159140192044d0001c0945841c0b952514840c165125080504400241c2c014805d440d908046051090310b50404c03450944a0b0940081008101291044210064122207541403000210003031080d207009403000150140c1c81d900c1e84206103985500a030015083c2c056401820b41301d810034507442031080c411740303030b00003803548601d50034240203036003079078002e60b40c599041b42c44c0340030000178140200540c1e41628581c07420307813003d0000d0141e1003004008119000391121fa10818442e114a0203c010b00850301d030000d880700203541c1c041c00d000484191003a101c00c00c3c4024461a05041240c1d490b9a90005181c202001413406900d45c3d18402d8141c03003882c0b030100b103542e014400c00348511140e600a105100c0d103070070300a01d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 483488237 1250 483486987 483487001
    0x30b10050306010623180d020d0c09060810022104060e160617011a09010203210103120c0209040f02030f010f0509070b1821190210020105130311030c120a03 69
    0x170b05600200058440e0000440c0220083c01040b26800003010150020403080c000f10000180a00450440820050816880042510354007403c8506032036001304000b041348250300c81d0060707000d030395a204469001041d002d258454815031021445c18581007007a4500800c0710203646c50216045014480031354010124544500c807211001c000794940b254a182082444a1001c022100000d64500311390080003102c0c2c2c0300c04800d8a1002400c500700c03040c0702001c000e001c00c441101e0242e0103900d02d00d100b04501d2000a070010540006034640e6600d00c0074136110107808903010700500800440c0700d0b03802c0c440e58281140c1c0103c0803030701e4a00202102e040c4401c0c2d80200c80320300001e10004400c4c00d507114884031030110070b80715101e98500e18009031030340d4800851602641d10078402031603040c0300d080e03004d6407129100782c40c032441007054100103074203951080351390400326807944800d100464850b440000884400c0000c1c0c0b8030704030180c000c0d1070a1120703003c0303400d166640006608180651603c5100c0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 483489487 1250 483488237 483488297
    0xd0c08060f01030912030c0e130b0108070801030b2d1f350115080307030e0a0803031506090a08211c050613060305060a0e070b04030b100503060106 65
    0x5841140c5c0d01c030700b010810261400c00b05982d8068503214103000d01003c40c2020320007800c0c2c07100200000381d01d4014099014507140004c000c1000b20360f2843c0a009110b046c2c03980000d501e0003590303560020100c0c40a80b804260f8280d140151050000c182ca82880b0b4080c0c48044036129183c2c2d40d0140c8224020069840846c444501e0303200c1e0f001c5400c004c480e4014400e040c07098032201010b200c09880c007400c400c4d050100b007000076900018010b5400801010181d02c280c540030038000311001046030b1038004c1e120b006040e81003000060080801c43c4004804040010410342c01d00c120318005c035910703c01a0300a8076a990103003030125901e0899260100311842190002490410005081c02c801c59040c00c1c19299580c43e54081142a600d190a501c074450000c4800c0080315540e040003070740c0d0101580c650b0344261502103040302501c0049030b8841070710716440640b07103814515135403003025110081820704246884d12020440b55400e0007110700900c41039039611198038a101c50404401442d5542c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 483490737 1250 483489487 483489491
    0x9020d051006080c0702040f0608060c0a081005010f08040c2301030518070e07110d080628060f030e0a0302010203010501110d08010302150d1b11010915050c0d0c08060f0103 76
    0x1c1003804d001203d210543c103071008900308030240c804102034000c1c1d40140400d07008140c100034554202101901090b0515514541503488035800300c100a0314038002c141c0024042046454060302031114141c10038460360102c4071141c1d6601c0c0007101e001c2a40148215000f44044200c119070b81400f600d5046501071214504007500b5042c42d41c1c3d030b40c03881d114030340148441c07600240740c4d18041ca056000c108076501c00d50f0070340d103000d81d001424001c0c1210024841c440000180d000c040410150100108264410503449410458103440c0803420f5000c1c10300305610b80d011070341040014840018814881d8001503125410403001501c00b0400030001703d241e500070101202204d85c000100c0d4112034042da2a80f083c03180700801c1c07a00c5446460308094105050008101c061101c40c800e40d002a02a99910303513807070065503407046c02e85206c100082e094101d468140c1c1c850111f541c0c030098200c00c2030071440e8035100f541c0d0184025180d408401c1d00c0442c03841010840340382003905105110007024070301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 483491987 1250 483490737 483490741
    0x9010606030c03020310031b0801090506070305010608040309140607080705060a0606110c0d060f0207030806090a0c0206060f03150c0706061d181e160b0a200709020d05100608 77
    0x50f4121050306c6c4c0700203804403050b41ca200001e5403544100c0000741402c1c0000b48000c00b080c3c100f40b6502c0000f561b1407000a0b10304000003072024451806036000315815030f20311a500d880c085030195505603004400342d0100c0100031400000d10f804c0002d00341d292251001d00b40502c0d013808281c00311041544500144441040b00d1207007420702180c18a450501120380f03003488041800d1681c01048556560000c07544001104004e0640040b6a64410340040312418002e907114200d80d003d4035140d6a0201c0035a001401082e007a00e0704c4040c5900c61000901194a00c1120803000300c0c01c24005d44000241450004031801800b01901440c80030300811240e40c0380740082c070041502c0300c4100130581c004034624010407204c1100140300f002130300d05801004941d0500a015400d455000d000c440540685840000040b180c802070240c5070007840396240c1c190400380110156a400c2c5918840702070600449001041c8018188040c041004680303000184c145003d8034104250540c580064092000c0300013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 483493237 1250 483491987 483492001
    0x70c1b1e0801051918020618030c030d0e091f060f030b040213030b060a05090720011803080c04031203060617010e010902090d050307080310060c050a080a051209010606030c030203 79
    0x2d2102800d80d2500000c0c4002d814005042c0019421000a500c03890004800002e523001c54003074000e80e082201511a012001400c141d45d480700d0880c0785010414813059600146840e000031075004107039002c44d80b00842c0c24200e154000c91190090000300f08440b01d41c0e0042640741c414511045e009031000c610380a42c0d01b20300c0c2c1c500c08542c072008158100810014240d07072a0010b06e4402810040d141e8085800d202c0704c090032905008a50100d1b0321140c2d07608000b84c11050103210703405074030490080c0038040b55407022106c00000402400311401c0c100000000640c070500d1021880065940c002802420004020114040100c2c1e00100343c441200501417503114154070b0b811a000c2d100b0040e640e2045602207102484a00e20103840d0f0301001c14284180189000118401d00030b03000d09062160f152801514180a45070019003240d0003504542c0000d085030f03009090701110f07410164145000ca90618241c0901100c60030780c81d944480c4104855038046c00340c400145060700b429402e501e8012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 483494487 1250 483493237 483493261
    0x408030103110102030904110c0c0d080a03050903070f12081e0c03100b03010e10150503010e131e0201020f0c031b0f060304030c1208040b070c1b1e080105 68
    0x202024090b0005000a90318580c020001c075125800301500074428441c10345800715054210320043e9a0341c0c012410702c107296107414010740f0700c0e5907440201107060400707890b401c03401071100a080c0701c41e43c4010440880400c0442201c0c00c241481802d14400941d20030100404d9144060b02d4002500c0c2a2002c6d44010141141d40a9001d084044000e0b1265a803149490703402c83c20354400c54481600200200e0b100220040491050711110354080c01e459540b505000f00c0e1081c2c0e121300c00003480a01c0140b01c82c001c0300080303580080e1000d89401000d01581c6401004a100213080c00b00030100303007501e008558040c403100ba1580030003005031003040829400700e1741381c0d01c4003c10b42d8260709040b91602d803a80c0e00e000e6141c070940800343c04c80b500ca180c10700c0c0140581c1007105055991800c005801100a8032916145101e1980401e010305152034540c02500c005204c50b60865405483c580a8071183e8400c40702c40d401494161405103881d000d4440e20f114500481d00590441d90402c810809551404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 483495737 1250 483494487 483494489
    0x10030c0219050304090e0304090501080c01081303090506040e0601030c020106081207080427060e011d150301050c070b090c011e03020c01020403080409050603010c141305181b0304080301 82
    0x80203a03100c00640c520b03109056101d6a000f4075000b40c80c20f11080100c0d44008081d00c144d03403040008208692300ca5407019500c00c50394424500003421030300015000d03120141801862842802d00e01007080c3c8031000600d8940080d0000c0c2580180102000302c0c43d0303414040c106012150380020017a441c10200703269100c2c40f55604002060800144043c1001000c2040358020311207000100c41500d007181041000c1101c0341d8044149a092402c085a00010111801d04990308100f103160700364030b0f4620003803c0060050100d0300840c03601d400000162028010030340304515a42001d940d542c1c1501e02181c0000e009031618185601c0300411034903a9030455089159801e4041407885804201c0340100e004e8440d1184000c4070b94000b140020802c40d036040544281c0e046500188150381d00e9009140c22501000000c0002900644a007160810740304000d001d00052104500240c0d600c0c0d002168071448030043c589130703903c2604200b04501c48070301892450302d04003807a42461800c058032205454081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 483496987 1250 483495737 483495763
    0x705250b21061206070c0515040c050114030705090904030201150303201b0405060303040f0e010603111c0e070e011212020f0c0f0103091b03120f0c1e1401020910030c02 74
    0x21025240c6c00e00800300000501c84551310075401032894030340762802804600c1c1c410a80400c7c05014802503203c060710940e44217510a5496900348002002080f505038006407042c4d09556851400142d42154045002c010703502079103414000c10303a0080c0485041b421a00051102d8022604440000a00d500b030900382c088120707008602500d032500041c0c1141f059034018090234440c0b400001d5945443d01c14281240d050703460030045d0441780c0340001e0a600c40c80a8000441c508042c2019542d145070b404910040304100841d60f0250302c4078403c1c44c0313005080e0080e542d0505403c851070304006034800c843c641408240b0192030709044a42071150f4034002076015920034420b0400c070101c640d11076442420300760340007039242c21440c903100c907490413514980c00b0503111810b2560080308aa80106400902d0204170b580380741c0154110340713812900805101003416038243c070001c84804108121403c1014000b081c00040e039800c1c0400400040d6070786d9a07001c5060608028020405076004500107044501c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 483498237 1250 483496987 483496997
    0x1f050409030918060806091f090b0f09031903061505120403110109020409060f050a0e03041214030c0718090201120f0e1009020f03030705250b2106120607 68
    0x145102c3c000e0240c881c80c0c0101c1101d201d520708100b044c4100095400c0b4504204182218031080c0c100780e0002d5824090001c1c0c540e015034400311b0030740681541155401140318050783e042852144251403070005003080d150029480d090240030f109600d11600181c1280c81c01e090f494a200c00c0b40083d0004c1008002505028a095400310340071001c1d0802c0f4001580113000b089000b51914004004000500f003402d00580781c0000203800081c1c0d8491002c460740c1c00c100460800d0f250040300350121400b2442101c071000ea0708180c2c904080d04201901c403522400020b03010300e0342090b50000d8100d010020b010100c90070012030f000946d82124841000601c458804a414410210071401030181030000482c284685030020480c05e80c181e01a00f685031007190600001e00800c010075540307000d500d0000c5c080b500548c00780003886001e41d0708a4100001d00200303140c11503449071040322a80000c40014140c800c141d00710b10380f010210010b507074010000c5a00010380c158040380c05649240007004001441 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 483499487 1250 483498237 483498269
    0x70f050d23120a1d04050f060d0507080706050a080c040605030c0702031504031121090f0a0f0303020d0e060a0906031806180302010e0a080a030c09050402031f0504090309 75
    0x58103101107002c0345001c035503040e920360496a00808030b100748820300b00054018000311509107003034010203018603004000e00d00285c03911020024411446802198503110301040007400f258207000f80001031916480d52034841c02c00e0038000e031454038024919082e2090030003003480b48940000c00e41b5081141d011041d03480f0785503440401e10b40f80111040c034180c14400c504220070154086c2c0511140201d05080d0360030384c4100324128146184074926400c0915044c824800305040c00c540b00e8035010300041c25405200d0f580d120800790105241c0007907006810248048401a81051000c1c03034014040e07405c20314020a0090040c100704031801707140c0816071181c0c0424401404080700060282c0c010a08009032916520002600c1003c20801c030050350a111402d20719501c0401c158440c1ca400c02d65a03803411807500004c4004003a84052032003408020030021070f00d511148040d610907002d0164a40880e10303446950381200200380e0180e803055080170b14400c00170f40d0007a0920b08541030384052070307092 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 483500737 1250 483499487 483499553
    0x90d14092b0501060503030711090c070b04050d020c090c07020409050102130b1b060f04110112110c011b05040b1804090510050106090e0105010509190602070f050d 72
    0x103454142294041c0c03142071180c01810300c00700014008040c400c030000c00035241c0d160103168881c06000b40282010300111245402c50504482041e800032070016100c0c0f0f0404076603030702450b4220030b40e8103564507800001390042c41501000300c403100781011207481c100ca02c0c040304000d01c0da1166400080c01142c030b1700a040c0c10010250140d518000f40000025805501d902210580f5086008602400c07086d0705000e420144021600d18010b01840b96030f00c281c1e650b2a140d0712861050800c4403810400e5074029804140000c0c0b1400110a03007030140c40784e540044810032400d41c0c1e00c265611011280141f0b03014845600001110116144850700a894203801204100758640040c0f49540090401d0f00b8541003107800718940303c0e0041e000c40c0420031030340c80c0c1504841e0184a80550350710681c0110050040f50b0080c000341c961420000c00d1120f07802c905001e050311408080c0d00990160f805036a040c01b45c2d841e010440800fa1134280c0340552101d103961503441c03030b0040d11109005074051202c0c0700c00107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 483501987 1250 483500737 483500749
    0xa0c0501060305070803070209010b090312071103100207111f0c03021c09061101061d04051e0d030b0105091003050705040312020d030e0c0d0b060d0b010b04030b090d1409 75
    0x554203c0e095400c5a03546401440d2281e000c504100d11500c1c0d00303000422114031794025240b5001028000780070ba0b00c25120010f0b174a80c44040300795180304081070400340a03038042001421041d0424801760725404507250041490400c400410700c1507907900c0c4803010400300c0c019481c1c4031004502d0200c184c08074a00b01a403e04008003660a0b1545102c2c4884001c0c170341008015084032501d58440c4200c04445038001c0c22155a40103600a5841001d02e00100c1d01c0714000144c0c10601440558058481010f5803085c072620000001d003854005140510a0a4140c450106041c0013030803c2c030704c0c0c132410100107203101d02e10b511440e0074141c1c6c8030041181c0c1407188068a0141d6400a04a400d98100f0300c4040e55800a81c90705ea00000d0821401450b00304010540c4c41b1f101001404440a5024946e160f003002d4400800c1303070780c002214203207a2000c20700c02c42c1064000e207035a09030310750f856080d0309014140d035000800c562503607403081050a41042d80003003140b4002c1d1300405820784504080c000104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 483503237 1250 483501987 483501989
    0x3070215031801050c0307090e010b03010306020318060a0f05010b040f03080a05190201020d05180d080a0b060d092a090b011b1416150815090c1806040b0a0c050106 72
    0x161940c0303008104200c4c5c41c1490021341c0100702d644c50781c1500c82d644401c0d04007160400d021311030b2850360a000400005140d80c0255402c40c840340c12100f015505034080c0d628003401101d0b000380043c0c03a02c0000d0450301461083c0c0340034245140405251a06051020707174110040e22000b030042c9030004000f0062803207401550840c882d0701c1c4100340c0001c03200c10000c2c0030350840b0300c4820ba01072401c4040380e6080c401011100000e641803002d0300e64049100402d50fa50800103000c10100381c1c0b103030014140ca90b9080d0042c80441c11f088400154055a800c0c500c15000000300407620006008100005c0d0001200404044880d42d000c0070818500350780c01200c07042c2c030300010b03800c5c11901d14800a0820a4141c01c4e03080b440000d1046910030881c040d183c034500740c0c140c403584407813180d80010840c070203124401c0654031000306103001050000c02400300d06010000c4030625019600454040e00a003031040c9240c02d1000c04503103450801e07051010550380c0b482070380c80e0f581c00c0c4042115501d00b000402c2d00644 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 483504487 1250 483503237 483503281
    0x4006050405010f0e090109210e03032205062115041a01110615010f1b050705090a060b03010e1905090f010b0409050c09040804090218040e0307021503 66
    0x407019503954408400310b00c0007070140a00f402105000900d42d60340500c24021040d410680440030100c80e0f581ca24200082588040c0400c500d140000304d075a2001c00040502d4074039034621303041503581c803c003c00b440095900114464203040081c0c42e80c0d043d4150541a007661401e402c9261505e070400e0f00704c182124040c019403c142043c504200c080174003d401a0380010070f880740b1138401c02c000041607c0e2315089442104281000c8900200740d40b0507007540d2034070306d042d08008030030003980789600c048000841012545940645024852800e144010a4000040c401300388102030a120034854580030501600741007405000000300341189901d250180304800d004100b100c0c0c2803190a494480e184418525015030a042d03611003d410b0074881e445500c0c0d044400780c2044016602040118100604141c500c443c1c144408100c540c00e510081c0107102c0698091242c810001050005842c5440c2c101c0b51242c00c244801c0015803121407402c0b00c04e01c20f40c28007640d01d03580c03130141800307520711003180c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 483505737 1250 483504487 483504491
    0x807030309050a080606090a0c020c04020d020910020607140a0c1505041707021f110d0e01020c12030306220e241315090209040506040240060504 64
    0x105058000129a09584080d15030030f0070b0f29114809144c0d911002d83c0e110340c00000080000b0103941d00c580c0707d8076107000f451054801c042c0e00d100007d0280d8005940c5404c0003640041c9070345aa10302a5019200d02440d400505010314200402614012641da03040a1903030b000203034504001e1190f1900464598001d941150302d42c019031490009080841b0119038901002d030815200041002c01d4a61440e40104208aa00182032400d08140c00304200c0c038040c8024140e0700d400191081c4244a40c602d813994624908000e460002440c100030300300c040d030085440c05170440b070954001c012643d000d881992407000002c40d1112803012a440000082c006615004c11501580404502200030444d080d03061054082c240c170380c0b03a03a0940e00f56410009208041d0000c0002a600384444140ca2015a00003412082540102d440c050040b0fa00b1030b80c0b40c008200304400c41c9000d001c010a200e000900e082001d40700741c0000c00030f2000c464510a841445844440c10190742c541006001d01006001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 483506987 1250 483505737 483505739
    0x50313020d0602030a1a030c060c070b0f0307080114100c02010c020603012d0506030601080c0904090602040608181b03010f112502010c06051906030b150108010b0a180807 75
    0x8400020741007a03850005040c10000b21a004490380d0380c44401b03c201c020050540c072030900b401c000c1c0c5603007e00c21607031700740c09512400a004101c10001d0000c0c4030804124903581d1a280782d000b404003005800c034069001c1c080f0200ca5031600d4404031071010241c3c5080689245020b800141c2e040441e1450003903110030000000303e10b18060401101401c04020b100d2039400201c0d02c800006040a030007080c0c2c00001c14000a2a04d42c450030039250014510807031240303010541000704081c0c0d40e0980b81030f030b0a00d0700010100b00d1282d12a21059200c407210f19a010141c0028040540303620049442d01d00b07903280441c0b101e0056034290b00450b03203140682c50400480c4034101600341d00742c1040404a140d04d6100060316000d0744540d56005c03034594142c0d90760f10650301540d200001400040c180c0c10b88040c12480d1400c2c040024407442020b140a403c440ca018074101190980c80c0229080d160b0401a4560040100c14000c00c00d0750044602d50506402c800e00640812210340d8903680710031076a114940c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 483508237 1250 483506987 483506993
    0x20306210706110a0506041b03050106060c170910030e010b0405040605040314030405100207080c030a0207030c090621031e170106050301061b0503040f0303050c06060a05010f050313020d 82
    0x40c80104442e400d44440220450b9460340c0781d168405203a028001d504000b0010340050604000c0805524a50190390b22042c0c0744d880d9070b401c4a0854200f040441c062582c1c40c02807000c03041182c030482150300001441c05483c2d1000c540558440c03000b12050603103c0c0610a40b030075080d00030524040d0048c00410051929003088005440c00761420350210b001c40c0d219100c9030001d101100c0c4629082001400c005d20101c2c0000005e40c0b2929083c0c0d0145420b000401000c2d005000510000e5000d03401044d16906600b0143c150a10683c01590b00320300d080400c00c5116800c80c04980c070388131383d426010300c1c0c080b5504003500c204004429442d10080104503400c24250840882d41295075003603c82e448983c2c075031500f80c501e4803007030042c0000308107404071030700300754240c80c1400600ca84100141c07406c1507070700e031f981b190074612f40d03042103000c201d000c1501107030380d9010424907500c5030044801c1c0783c841e071a0100180421911a00b40410044008005006400c420a949201542c081c14495802e09035007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 483509487 1250 483508237 483508243
    0x5190222080d1e05070b070203180105090d0303090c0308041d07090e040f03090b0c03070614011d0a0605090403050c0f0a05030d021e070609120207120602030621 71
    0x3012000006444802003210a00003420120003901a1651000c0d030300406403080c2014006030400c402c1010401c41540091012440c050180020f50000c0d6140c025101c9264200700108031882d04105c814080b80c20b0907a07441042d04022609424005000d80032801e05496004c04c40e0405400c22a000900061010710080d2080f80315540304c0c44400203484402d001c0302c905100c0d12540020200c000085808111501e0403409038622030305009803003694a0600c001c2540107088425400d0b0400b02c1c03d14184800d0f0301881215081c2c0361150a500d41c1440110540da074030715480c020002c0b44040000b00c44160a82c8003070301608000384007800391311701450018042d038800007040016008070b011180849000040f0500216445005181031220010f02e4000070b400002c17428010004d0040050302d00d00d49400100340080c01100301041c0b104030f500340700c005880091981c40031544240410420f0000031910201101da01c40300c0035aa03500c1d04c0c000500186c91803d06c009000c030210201d002c0c911000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 483510737 1250 483509487 483509527
    0x1b08012d0b0913020c060703050a15090b03210d020901050c030708090f0414010527040b0f070503150d060b040f050f0c04120b13080c0d03060b0a0210051902 69
    0x21580060380c00e0003803c00d2001ea00a00c0010741e0345902c003401080b1107601a030811548410b2001e0001000c070000c503c6481a51000d500c1010880d6640756414402d00b0140701109841082d1042000700c1400840604120311888440c4001e03241e0128003c282070b1312900498820b0034941c0216900c400090903c014030303a0042c281e6034818819401c80714030500b403134081c5c94000540483d000f529a840d18080c0040801c41d220070b601400c1c1c24001400c03030303080d0702130515001d18040c003801c43d09494480564a00d00402070104030602c40706004000c540940118410300d626000c0d82c0d400001d110501d0100c002e09903028100b540541400244000302d1070381d600051149014011808a50704c4405c1a08050b1040c2d01448005226119405010441043c0344a4210300150725220303085190345c9580391290841c0c440803e01e43c1041413004407076540741c050b040c068480300c1c0e56145400c0b00d000029680d8841c0401c000e100b030780c5035000a105a81900280346140400c1e04055558203041c0703848042100702 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 483511987 1250 483510737 483510739
    0xb19030305180f010c1101030605031b0301140f070c0204060e1305010c0504060e090603070506120711150103030818060703020409110a2a061e1b08012d0b09 69
    0x2d41c516151500d004203000603010f4043e16110303100c0c5500d40b0340800040e942613400741810303110701d00010540ca00b001400404850340e03011000260018007003609441102115003a01010b002c11310090303c1000701015000741c114205400b8281031440800e014100c5544160031881c034000401800340d4a252422003010311540007044180c06000c01520780c0c2c0941c1c0940c1c400101010303c08001400e04150040d04228010207c4801507541e0780000c101c1c0d40540f1134800603002150502c400c007900084c152020761005805083c0518a1070805c55880e24140310190411100d4404554280002d560000b40707000740c5003e4480038505100d01a019501034450b0140d5235291520076000140341006039211414607568566441981e40b0300c0040310000301b04010391400c250051940014400d108051444158000c45400034030385885e2042242c00c1040400300907501000780a882d039512080403415900e120210a030003441808881d0340401103002004a4050703161000f040c4200c02e01c01a0015046c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 483513237 1250 483511987 483512017
    0xd141e0a0905070b2a032101050114180a030b0105030d0305010b07111302130518060d02120109020901090516020706020a060b01051204060903081b0301090b19030305 73
    0x103803201008121081040094425041403909001608441004240c02d222106031300040703550100d480102d0440e89070444d8503039800046d21004442c0e0021a04010300d03805100503442e03601d4100080c0c8515034140d01504100030019840c1c00440c020388800c4c3d03050704050580e030b0599840e860641d941c06402e001e01407182c810300528901941c840d0203018144c60362010400e040c0703112581d5020301c800e00512240d40c85016440c00401b07044440c4080e00f02c80c0582904205101d02d0f04003802924440c0d220800d007410070b00420440386885e00d11044034035680c160350644c1089404800c00b0300604000c0c000075405045c0000004038600c04e604014010b030405c107031a842c49056100d060f40e072849144100c00c05604903011600200f03100303500001b0f9809060610600d4508070301c40c144081ea0086038119181581c81042c4828154841d002d25132007103132040751031084504000c2c0d00505000503ca6030000d20780b64003980100d921400703042100c0f0907028688000d40303526890041c03c141c101c8041482c50300d0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 483514487 1250 483513237 483513241
    0xf0d09030f03090b07030207050306181c1719110a17090c040608060a06050d12050307091505120921070809041e110702181b04060f030f09020303030601050d141e 71
    0x5801c01c0d03280307330040c1c8030790300140114070070755100d402a900301c0100b00042c002e190f4600c3d807101c002060f04a105494010250b84a4001625600111a0080c0d0700c1050104103112031440e60b50094900386030107100caa10903000780da5590a540c034082c0b000c2d8825070020b040060009800d0f00004485000d03040d0b8600034004a5210790a004003440c00c100c020301f214447e01e184070041070145006607007201c807915000750040c0e2143c0d1303401d80300005e0700c80c44000200f00080c4048a929035140301d5400031060f402814000700c0d0050042da5440032542e0340d010324000003d2080402200c0d00132111030010190051100380c003100191103892449820180d005401d0145802c0e4041c00101102c03882540101500c0079400000c0b103901c1005002000407050a008031882d25000f481070300a00000c2c2080e903114400c0c01418040101500c030281a42c0c1c1d01c03d0704013031505005070343c00306c1a05c1c0c0c80308007860550741300d52405c402c80c80134201c1c940e900e0300340980040610000003464041203555410015901c145a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 483515737 1250 483514487 483514501
    0x42d0305010c0c230c0d0302030c01050412021b060301150302041e05030d0305060310020c0c0306010e10050301020403081b150a02040306051f09110f0301090e0f0d09030f03090b07030207050306 85
    0x3443c144409541e0400f07002c45c2c115140c01c44000e100c0f0303402403040780e090002c00242e00d402c45000341c034207a611042c4a00c0301041d40d80e0400036051001c81c180101c51002c00003070007245c1d040c003043c010b0005e802203024043c004148281e054a008002145890385d002c54405011a0b03495140e0041c6c901a0180d400c0c04800980640141405500064020103812440c80a000000d42250483d001d6034019804543c0040d50308000c51406489664070720b03c00d0b410288000101c240059004034026401448100007060300782c82990754042c40004005c5805d000b003142c0030700344651110010a54084402801032807078496001d4401d90703204030002c001c03949550402c8804a4006203107005400702140c42072051203000c1c1c00c80303100000d00089032401e0081442c80310565800c01d03040302ca1070503560540b80400c0802008941c40d0a28050050504169804d900802005c00e5010103001d0040000c903000401d40b107240c1c02c41c01810840060b48d161461440d00a48800d83c500c1810700ca4450300b808a845 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 483516987 1250 483515737 483515783
    0xf0f062b140f0403210c180504060803030c07140703290103080d0e030c030703020a120c02031b0303160b1609080327040501060206011505042d0305010c0c 68
    0x1501500b4a030030001c0e601c03982d0881e0000b40b0440b01c0900c883c0c81e02d60080b54202140030311240da080700d440c0c1d440f012140f880c40e40040c07111540014801c40c2440f00400100e4000710849800042c40350f201903541e040780c280440e4000f40484019044d10ac5c8190020030310034105082a061124950380301c25030340e02008a080e65032000e02000c2d04081007004460b034800c0042d84031988111011043da400c0c40340c484c0b200c03411030b00503003002d90258000c10b000c101040003e100c000083c210038241442c440c03d141d00426918405601c101501c0040b22011808030380e400c0003034411064400d80010504503032841e045104160036a4981e52004070000c0c980305040c001d424030829104510700850801000c00c825080411038004000703008088a11100e03495100c602659018000c903400038501549002c480c662070006c540e0003102041401c4c0414000b034100110032003000380015190101020480c040c0c007811840e00d90000749150303e088000810260081d001d150311501410902d002c001264010302d02d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 483518237 1250 483516987 483516991
    0x509180a1401201b010b040f0b090c0a05220f060309031b03050f0f0d0504050715030c3509010b0f040603020d062304050a020f0607020f0f062b14 64
    0x9001101441034040250b2002c03192841c00ea00c480c0042003103e011030105048503081c880608c04280c5400d01c0e481d00c5c1c1050f1401507001460b006d0b40310700d88000c10400400303600070a0141c41d402503808071010003418080300840c0161405101d00500f00b50f517030501500030042a5411008240c9030094541d2142ca500d41c0e0702c0e81141c154958510b8442000c0c113849e0158000d03403144100e48014000740c07441034800e108041c822841030000b01162800c02a60008100340c09881008050610340b01240e03240e80802101c44c07505a00004d9003480101d00d0240c2c0a225071400014040004501008204c510540145030620070944030805440f00c003100740801d40300316000194103c0d9a1581c0d000010f8a681d120070340c500c0541c03400c2c04a4180700601c01e030022000b92025140d981c0451104802d42c504130041c603208000031100b19207003610690204504098469100b0710131040c2d03980c054101d8031003408a81408002520441e103d0325a10500703500d40300d0020300c2d8400c8a20b48100409200b48500c40d82d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 483519487 1250 483518237 483518291
    0x708120a17070801091104080a05070608011e050402030c040b031302011805090f0606090a03050c011416020d1e0b0103150207081210050a0e07081f0509180a1401 71
    0x45201c1c4c5c02c0c00e8a12000d042c101e84203502d200c0301080b0000300c02c01d0920203d003003a0320420180600c46d181c0356000b0022081a08507820030a00d00342c8001c40402240c1264045030019500543c0ba0f680f01c00c3d529a0034042d0f03070b001580b600390020410a03194486103d54a40501c00d80340d050b031206c00610700e080c0d140c03094061140c11002100c00300e4094011a0551a40700c800108291301d403120290210744419803c2d070003140d00e81d0001a184171550380000100301d41d03584a1640d10b02b0b0060f422041000c074024080f000c0d00580020f1916001d10801400c403030144d45c28056080311081681c0b4105850060034441a11403c0c04071540021481c054001c650307001d038001114504085a015940c0c0d0741d0700c001740c2140d0545461010002c2c464507040c02c11b01c010603c50402c1201c500c3c045201504c0000020010030504040c250906000a249042d80c41518001d960700e00e0b550743e40102000302c64612010f882443c1c814040e444080111100084641d05140780003440b011140000600c60341c4043d450715 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 483520737 1250 483519487 483519497
    0x106050f0310081f240e0601020a0c1d09061302091003050a0c1401140d02070609060603081903020901020a02100201091704060e09010312030e0708120a1707 69
    0x4519400c21480107580c00a4000054403849655404144d00d001c1124103440d0049114101071000a040751091050109507414815120300039141c940c2101065802880d60340982030307012468030303442008541d40d4554080b01031503819459042880341541e04078072800103000e040c80011401c0101082550203001e02c1d074100d6402e4034940c2d0800800b22801005010000240440000420030420a40b0f80190055901c1da00d850300384503901080c1440d0100490600914600780ca814481200844544c1c141007080162500800e2030070b1809000c0c00c2c14003520090a1000100601000c0701c010000d0382411001c0034148030380140c0980070381c045c041c039080c00750308a01215805414080004d03c000c0070284000203412100d0358403040d0500c1c14089003c6140e4000c0b4042c0b181c6900424010000c2d0b0b01101c901c030b003940c0b440c3d450030b03103480b5002d005004146e1201e085440704d441c100308041c09025100141d036850400411072078a1500300d18507880000f12125128890a401140303681c0c09003403c3d64407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 483521987 1250 483520737 483520747
    0x2090604020c2109010e06070c060503060303091201141008060720010f06140103110d021e0f1305040603023f0f0f0106050102280209190f05010605 65
    0x1088025045940b50a140d4040c241c10030320030780000722040c82c144028403002512219000c000401e0304413006d802c180100d508000150108000380591800c440c01e500c1c0199480d550400440d0850044004481d00300c010421100710202c41034201b180c403042ca038814010070b940c0f0011480c120040b680704c2c80440b60070001c0801c020310300c144141040807030140104110b404600c2509401c51b01c60110901d00d00d0740c0c0e03040a21039210304030980206d540e002d1034140580000100c1c540c0580c800e480d923102015600042d154a031150090015242e03c000c4000c0b9500c800f150005501c0c543d20840000d140d4000800005c81c1c0d5150030f20400048e640c0107002c00c00108443d0300540c055075144140c1c4140c4502c0389404ad00c194441e400001c6242808402801d00700c40037070100c41c9044120207400c3c04903410010284200c6c5d0b4005180c0400c0354010010380320305844510040d1011048841c040c2d0402c08050030098400229850440c00c101c101a0400081601e070714200202c440a0080c13500080703081003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 483523237 1250 483521987 483521989
    0x1805250f030902090c1309021c09021503100e010503160303030c0e0405011805060315162106170a0804050d020f04061212140f0f2b0e0307020906 64
    0x190031651065080000342c03882a50000b441d510411176845041030000160000592014a8901c0c01440182c0d000d505080854151400f9140110324450b041903560221340107540e21004007500a00000d404242d42e42003a00305d4102d021004e0080d20440d060810000526040c00030300d643c0c0501600135030444050031590101d01900840320300e28200314610104d80c0890340d170382c03140038002c14280141602c10000c4034905400d980300108418842d40040b04410182050110b103103a2000f0745100c0b051b021407809909076111500b00001940d102c200003801d04500d030b4642c0c4170400750b40460300210006440307052407540c2c6078046c940080250388240810886420202852500b07548000c0019124000394004202200c03881c0c0e206844c0030070421301181c00e1002c0c01123143e42c020881c0c40e003407002d1010b1050b07140003807280140706d02d05070740b00041c6400b8110840c0d044d41c041e90542c0d8014040d02408003148a24584140c010b5280145000706000000c40004111030b8080e5000e0300240082c2d81d100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 483524487 1250 483523237 483523247
    0x806100b0a0302280e13020f1b030c0a0605011a07120503100305010509010506040e07060504050f040f0c0903050d11060105040908071b0e0f0f040209060118180525 72
    0xc0f02030030b007400c5003d403643d046011811160161340050340d241c0410310f0b2114204030841c0c0c03201d6640c41080e07104001019050001c9012160302ca0007490058146050500100f4034500c900e141582903800785143c00c10820013203411040c101c80120146100040f8100c841554a2058110007041282d0070460142d056001c0c00155a0004081365400c801c1035903a21042c0c00c1d07035001ca400c2d00d4540d6680d000c00800f458980700e1007a003030001100070044142004030140c1584510b0041521032555081440321540d1940c000409035001400c1c03e000700060400050480001804126000d0041c00e81442200344600400716500402e2002080d260346031000b0702008120141303041e40c0d00102048a000401c9405d14200c81074407010345400e41c0700e860400388a045100141c4068000715038481444400d41c103208050303401c1901110b80ca0308a803100c60040c0d8401c030361140e003103641c061649030001d040c5c4101c0c02e500101400d401c90501255903054460301101d110800c843c80d51071000c0c0c8524604034032407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 483525737 1250 483524487 483524497
    0x10e04090206130f092703121d060f16090b1308030f0703030e03030f070513090e030a170c070b09010b130603050c0307061d0a030609050303010806100b0a0302 70
    0xd400c9500d442c0c1a08142050b2000c9900410b0307214151144c2046030724030310721a6121103075030061044210007110340990107603520090007404004014002c601856500e40c045d1105060303920302c2101040030b5001d4140c0303a044c1104c1012481c041b20740042c40340c4081d1204541c0c0440942d0f41c617030000b810040810b94942180d15008110b0f10024004240200100000c00c2d0340d000c0f5400f040d80311403140c038004082d18132500700c0d094140c1042c01801050030700c25911942041c00380c20700c991141000421008441c005912401d10b00d82008912101614040001c101c0b455081e680e0a80030b51084ca60700c0c20000c4256501c40e0607910820410b07010071228000141c01c1b0040b40000b20300c00e00c48000240d400ca141c1c0c02da091400e680d80c0010002c00204008000701110150080c20300f40e4500302c005000004240b0380000d4690b006030140016a940041d5507002d564818000c0011494904042c2ea80740c1090054144500c900004139890041c800400350072180f4a812952a105105500b2000380d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 483526987 1250 483525737 483525739
    0x604061503020c250e0c07050c04020f09040f02030703061d0f270d030c03050609040206090a030503040909050d2d030b0d03030903030b010f0e06090a030f0807030905040506010e040902 81
    0xa6a1060301c2d019a04580d04101001c200c420b4406080c00d04094105d5201c02074114840000200420340000341d011401802d0038070110790050710f584910321007901c180b20710640c40f50302a207492400703990044a50b0166004d141d503507030304200a9481300031341811300034254040101b0451040000310300300d0110040a5000c803800710400204101e1202c0d004c41460a4120b0700600e4010b20760050791b0b554148101142103c2916060026082c00d81c08600307604400303440640034280010301441151200052000110b602c01c1c100c0e0b0307465540300541d0008000d2254100c91a000300300d1110706485c49014510003920341c42080c00d000030450340c00494005030000c1090203242c0c583e50740161590721189040300c4140203131004102c1069516005003220303a001c07411814460118080c41d220f503072022521410000580c0d805ea41d84154000044c03010750a50f100911103500d00305010100320508020740041c034403944070308120a844034204401c0d00e00848802d400104007016802240c50150490035062340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 483528237 1250 483526987 483526993
    0x70b03060114131d010e2a040f1802030702060a09020d1202101d07121401060303051209070b0d050711030d021b030306180c04150c0b0604061503020c 66
    0x410300741c0180d00b90400c0055540c000148881080350a040100114440213100280807642d07050034000340300b6040240c9503000c4802100261805040603800390a2503100c07502c003060301d982d9100001446588075004015040d000c20420400d40324450096900030501500684070302e0f034402c240d800050003018410b0b80d0180b040f0b00c20704003241b01aa505800b1002c80e0740502690380e250140c1d18103035825650b0303241c8140c59298180d00348800100d0240c0594068031419000c1d410b50781232400b01c0c3c102b620b80964240d440c00f04000304154002c0f000b0701145615031001002513640c2250b80f07450b1848c0d88501003c10604102039421b241c400d42c05264041054149000004071701010b82d03207150003102e00c283e40c1030740c0096800700d43c0940d00d40a03d405030402008515610b0b015000c59100c0000212103100f0f640c000300404c03480c4240009460240140c16601090310b8401c190060540210302030a40345041100c002c1382d0a07013000d000d03407025500340ca145d03d2002038241c18100c0080d4040080c00072640 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 483529487 1250 483528237 483528257
    0xb040207060605090603060603070b07140d0203070b091605041805061005030115031709010c080d050a0c020f2806050f060f0102031303020415090f0e06060406030302070b030601 78
    0x55128409030562a001d468000741850402d401d1060b082c001400c2d551081d4009400c1000c1c07641c00080c0c450640d45c220440a0701d401d0145009403150039100101103241c0030f260151a0500d134000b0107864024011200e003a03c507280d1802944d15203c1040b00816910b04084061085007410b4201d04120300104064001c0d400c41c584a440c142901902d40501840300d288040015180034080e2440c0030035640d110281491071603032100011141070b101c5642c0064007044490b1160b0103aa1681d85103a0000b10759542c54602c2c2c0080780040804440100c0200c3c036009460099034800212207514600d01030003014681c00c0e0300500d0860742004d40700d01404420a001c2c0a0004040b4081c1c640102c90080454a107402d206041102d03460400002904540c02070100304540308126140408903901510300190b0010908803400f41b00f5855001203441c1d40c10f081c07281105680c503034413841ca1508041c2c20341c1c0c0143c4600c4204015a6440d10000c5e00592040005001d10212100115000441414840112 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 483530737 1250 483529487 483529489
    0x507151109032a0604154509020a0516020a0e16030f09020f010c06111b06011a03010e04111804020117010f03060f060f06021b04021e03040f0b1003020a0504050c09130b 74
    0xa40554100d14044484401640c0c0055001c0d16070940032307105980080d81002c4101000070002d00800715070f0030766112050341c95410764840110740d5028101201c529946858542030341050b048048085200183c5400c4903001c0c104000c0c450001c500f0350062046803451440001120b0a030100e0605861895590048150715440200248403c42500c608000000d03c080784039400c062050303120072200031807205107003842101c0204880c192000b0316004040c6842d00d00305558104c040f26221600710340300c0c0314001221403907600f02c50300c610300c00d030303107210300c1c0342d1020030801c04010300384100602c03403010407070620000d0f09940042d01c000c100440c000685580e0740c5036000d04d03451564442000368000001030300d0040340c01a840c2d101e21000351025071034480e00815220070f0801c5007612040c43c0038048003190410002161907080300e07400500e0508903040c45049111102c41e00d1000324840d8503007071130009160030103000701d038424292044600e0030000b0300c1050028003803108408080041d41c460081c0b140b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 483531987 1250 483530737 483530807
    0xd1103191d1018140102060103080a090b03073b0607210513060f090308030a09020a0305060106020f0a12180b031501030c0507151109032a060415 64
    0x200342d61540c900c55044560100c040b610005a0091801200d8040d040b0005980001b072a0307044907440b0344003682e2a84508012a518911500085c1108600000340300360154405c680281e0b080701403480c01041c50340000100706400308682613005840c0c2204a0011920f07092010b408464000d2044c40c0030310400e0490552960160004d50001c6800031445081356072421038400c004d00036505028026084006001e8030030010b603c402031a5110010000d0010003880c1c0000c0d54250303000c0d19860a035600e13441c0c682d4551000740134010052207400d110444400000540d0010359400c000700740c800e600d140104440e400550808040e521920000000300900e404004510038222441115682e0090100040c20341c0c01c0d8034040740400c80103000d0030300031444081805001a502481c00038810507084500c220341d010b0310a006a0600400b10046008100700030300c01031200060810741103501a103c10000140214045e11050344031419100c4146030098034001c080c8100701c1c01c3c0c00720300c0842d4001100c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 483533237 1250 483531987 483532009
    0x30b09150412091a0909070302090405130204050a0618020a03020f030a140f01030b070e0114040602060406060905040c030809060f070f110406150e060c0f0d1103191d 73
    0xd01c84200303446024120f500000c24000303008600003011144510526100c011700844007254829820100400c1c2680c0c0a0b03811a64507020140050002c0e14120781c10401110440c80c090340614240070025074084021311a0006595203860060b80e083c0844408500075000f041d075378000d15900304540e118003003c14010358811030b2200380c00310300e040d1081d80b400d041100c080d24181c0e013616190010700008200d88821075200d0f00d10f203031894950b140407004131941178051844401c04100010003262061340403403000c4c401c0740500024403603240e440c6200750031504126005002d00103401002d0002400c9040117002a8400a05080c140004181c41c42e0056222140403140359128008520410165585000312000121401c0240e540f6007110140441100da02c46010481c020110054640e170710360590f000c0c50041c400f10750039400c0f604007507075440e02022040c0002c14640c01200108a10000c2240c41d0490740c01c01808110301801302c1a6918182c148103a6118000404102c10302d86981030064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 483534487 1250 483533237 483533243
    0xa09110d06030c092f13050604080d021204080c0d0521030609161b05120a05131203020304061d03060709060f02010b090402010f1106070507060b031501030b091504 72
    0x74000504d0b0540400458164214071707403950108a500d05440c0300788400f54a075410b40054135594402100040840c01d10709a00055400b040c04640443e0b40003001580b0303610002c42d5003c5400c00025100c0d83c17000d5001c0e5104012050780046d80702e80c0713203040814800344c400d403040c0d044a00c245140300000b00c1c00f41a050003140460703804802c00c0713258036040b01055006201503560014500c004400207218481800c40c21441784c2e642c5550408002d020007038148014a04405140c80b08100c40b802000b940c0000352402ca0310034181f1020500c01c04882d1012030f4940e2680046150524140d01505c003007203d107120346a001010841c8040b80c1c4c5040c0503a511a00407691065015400c0c01001b030310303e6906c040794500310fa00d040941561915001c007000d81150f0242403c0040c240760031000c445000e03400703c00b800329020780000c2c410308a0300721300a0030b0540d2060000303102c0c1c420021b080c540e898842d088981c444020001c0100042810040b0307554000b050203040e40c420181c00e00f9800c1c90b51009079422 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 483535737 1250 483534487 483534503
    0x9140f011e41091f1814030d1503061508030319180501050f10030c030602180a0608014101090b070b01051806061c1b05090406060e0a09110d0603 64
    0x1c0c404d49030081501c18003048480f0b0030400c02e4190046010010203809005080d005540d9442078124000c005075808072045803000c0c0080f40c00c103040101040d0300380c84201c0710241801c00421506500113081c4050380d00715030044d81143e60b0301204554142e400c0040b450301e240e0381c0c400112a418048280503440d40514004581401d140d05509410503006100f104010388a45051002070781110301c0c4c804803600000056186c03038590300c074030544040b000c0c1c4403580700451000001d07507070b03800c903020394103c0348550342d082e250803241d0001400d803040e01c50400180050346c262907858a0b121059901800c0011315164070856103980409680e64072a92058031061000300040080d403070807140c0015611489030094241d0705209002c2034007406200841c51190107001410700e180940b6502900c0c0f864002004981541040c02c03001d0075643c00310b132441e40124100340011a00a01840040d108284090424030105141c03041c814010b02c1c03203100800c5044400c100e00c4191484030f00540780518000c40070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 483536987 1250 483535737 483535753
    0xf0402091c02041401090207051632060c0d020d080c03060d050c0312120105030309010e13151220011b03030906050711071d01030609140f011e4109 65
    0x801450035072180d045408282b4035020a01c91512018240c03503c02c0c07200f48400024100006040311440c15134401b01da04a4808103114009001c0042e2100c44c1e03010503020b0350000c000892007100e02200454510134050000c002260060030708480d0111440d010340140c44000301c00c40c0c0064104408034601c1e03039402ca0b010500201c030300e2407c401d4500410040700210714261381180040c1c4071244901045200303842504002d584031200e0b0700017080c06068620614402030316030f01d04164415121005850f0042e10b840ca042c00d51a00120030002103205840300b244c204039100803420369414480d011002c240c0c44000034400501c081c01040c2c021078440d00c5062002001c019094684540c9903c20b03030800e403010500a00c01c046003509241500e400000105482c1007504005904030283c0203442c9080c403403003008400000041d0b0090002d0040780000d80b02d480a5150710000f501d07200e030030361219a05604c900f498000c01003601d8900070f921042112207401038a518000051004031581c50301038100b080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 483538237 1250 483536987 483536993
    0x3061311030a06051206220606030f0c0501031a0618120f0d0801030b1b0702090907090b0406060801180b0a0f031505090d0c080f07030306050f0402091c02041401090207 74
    0x1544020301000d840d03002610049161740c50f42d80e13902404c0c94201e01e001c0861010881d00d01d010107400c09400810900000e5640e14009048400c001c0050700c1803c5407034408101988603004e000f1811003921101c2c58217600c00410080117034031028080258a0000301c03485e01c01d071a86029502141004809816001c10700368807141852100e9400c0010441e15100501c0054000900c0940100c00810041075030260240c034140d1511501030003a60080e03c082c00c001400c1000110b480982d00310603404d000c400005818001590801d024001c0403401050051011040c609000b4100080001002c60034541001c040b07071340c69426070010010315505d1070341407050200182c00c61200c5200024108400d00d8065140c1c0e864100d42d02c185400c2010103007004c011b08c003240b03040e40d44050002d04c400d96070350101d1030702400074185ca2182c10301820b40440c0e01665840c10303100751802044003902e246074841103e00d0042300f141d03001d0030483c1d006544480742820b43c1c880b10002e81c083d2250520042c0d961650342 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 483539487 1250 483538237 483538241
    0x2324062a16230102030a1b020613090e0c03010605010903030c020d060207080d05070e0d080a020a06020307030b0307090b090c130b03360309061c020d15091a0603061311030a 76
    0x281c07030707044d5071040100300c2049038070080800d601036035080d56407941003217440002c10b83e200310000210300c1c0d888407401280e109541d0340700350303449941c81d021196000c10398400d050a940c11403103074030b02290255008201081c00b900c4044000d920080604100d0026584c4507030803a0440103040d01c00001c046141d0810380018424035030403442e14140b4083d400078003c009210307003c50500c0100018800320702620582d00800c400140580e00103000d549900d001c0d031006008080142c0414441e1040b00e600160074146e505c1409240b550182c45040b40750388034142680d66501c24a408142001605400100095083c01450160344030040322a803050030148c1061600c0403201919201c103801c0b028624041c100002200d021700030070348400b92160203d540c05980f600c41044203a00031800080c00380000b603082c4c2c0c0b100d0004141070340c90030b0174152548041d02c02c0304c004c511001c00340f11200183d56114503083e40615403104004140b0b04500310780c44001020750303000c1c0e40c0b0300701030400c00f0081c00f09170030140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 483540737 1250 483539487 483539549
    0xf0a02030c0709050f0c0a020c10021b1f0807020a0b0123040212011e050a0b0a02300d060b070f02030c03030a0c062324062a16 56
    0xf405060201e81484107044691040c040c200600c503080019051a03968020b008180310490000c107040910441040c000e0344a41004490705d144000c01c2115841c28503100c07a02848102d030954190a40c0014100c050385d00e160042c22000c03c0d8890344101d5000030300d10341d03d114040e00689076054100c0104c24080850304014090b002d105078014000180360348040042181155012417000724a40000c0040c40709140258200a81090610002145000c44d10303004040310b1003140e08651440d040741c2e204258603e0f0348400c03030203c0d080305401d941180c48064040d20355a007840c4400150b035a13513000c01500d90741c07102d802240e911550011100075450700348442562a10298050340c900003e085001740040d0684000600c01c940c1c8a00400c40d05100320740500c51264110306481c401c1c05c10146003600442a03017000e01c0048201da40300e0145041c96016242c7c1003010341c003039443c2148080454003070407440720b1a0050a128040704441d00300c808204080c01043c0340d2403560a81101940b510f105240c003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 483541987 1250 483540737 483540749
    0x80f030c1c05090d0c0f06080f090a020a18110315040e070b0909130f0302101503030f0503071106011805060904020d080711090a0501080c0d0201020d030c03020f0a02030c07 76
    0x709103074000700030381100443c3c50140084a888441e0070039494499040030302600f204030078410401001c91119040280140590b031441403449040d60b90b060309503603401855000941200c00f1420402045081050110503402030f414013140301c2c410311500c21003d40084030000f041454a01599200d41403d20a03010700840a80c050811117003420302c1c1c11881e200e000d2100e400303020144001561414500c0c0ca0181081e807240c0c84803c0d40c0c0d41414025514280b000707404544c98544010345001c0c55012600204480d4542c94100b800c04098000f900d00e508001c0150050144803e260010200b0038000703140600008950005408200d02225040b038100421a5025140a2041c0009a502c042191840c140c3c00044196202101e181690341e40d0809103205da0480b00880900003c80b41980000c1d0594541000b211a00b0385203104100c40124251000380c0176810240c40000300302d2094000070a42c02043c10058517090120f007000d4042c0e8001c80003d0b0041e000801e8089080100f440040000c2032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 483543237 1250 483541987 483542023
    0xe03180306010e1e07020a2f03011415030708070f0f0b1303030e01051b07081005190b1903030c02151819030f050a140607021009020f0618040506010c03170907080f030c 74
    0x14075500741012a03032002ccd01d080e443c4a07289a41000b5503800300043d03009001c8001c26940404d030f840b00055185030130f502032124001d8420700c01240948489040c0d81226040650192901e413031502d05481c042002c845c91170402c1002c12070401f14aa2002c508070711184c19078010140b09240449690400342c0e4603100000c0c141c2004217209103100440000c0315960b00340607001556440c0c40c00060860300a000105d80c00c080c21010000900d90003020b921203035030081c0c03102216880c0d003d02c0c507006403048503034910202e0300c100041d40c0141002d80304502640714106100310f40646a0b211003408910380e0900321403692005d55000200108107a201d9150b100c400001d1105040c03409010f911451841d44944206a58400c1d2406540d180d007190801d150015107a1980c070783c09000080e0b182c0035040f1007640654100004101e0551081e49045822501603544c001c1c4000741212032150054042d02c41e00e058072030440045800c0c0300620203404004445001560f54440d40d0600f6820825841003a2503114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 483544487 1250 483543237 483543251
    0x2060706060302192615060d12020105040201020c0402030f070c05010612140c01020d08010b0a0e0603040f02010215100b090a05180702060106090b04180e03180306010e1e07020a2f0301 81
    0x100700016008031b020982c050040017691028007248031241c0c195400b6268808440c1400c0d80381d901988040e02841c000c2e42501d1001d041c42050009900c001d03919406c0c40071044002aa004d4403418440041601c60720001c200c3c942c1e244140351140c10160015548600840c102001c094400c0002c0c00b852802030018108035034074200c000d4241201441744042c016030004900a0052044507542c0d00f888005082d20348038145414200c0e072401000b40200e003d8850740400c102140301070109030307110b4004803400f8100c07281000c0c8941c005800415a50750000b84240d808103e540d529030031080c44026040c04407045240c40b010083c60128103900030010b1011701c0c581844013a10b031404560543e0403032600102d5006a0941c840c00074486261303400c07914080400c64010124594101c1c8201e04811001c0300d80e40d0b44ca503110129417680c2aa040344003034821010340c880383c06011f4429684801c0900640d00c03c000d881d01ca0380b5800045408001036580c40c0940040710303143d0b601c404200c030718059000b00210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 483545737 1250 483544487 483544559
    0x6040504080a081e0705040e100b090d031101090602070b1005060304021e0904060606030b332b0c030b01120e120d0605011407080301030206070606030219 68
    0x14450180050100001500084c8500054401c40e41212810510b12180d5191030800105260803600410302c0010329900401c03640008980d0000598000b0781c10f0324a4001c0360b40800003903410500045090050100a080c0408028403a0070035a500641d00581d6520061818000b4003030010f001a2200420303203400c0c001619000d054079800b50b4162410030361400b6000a2202180160400d1940f18004804120400189401240c2281d0043d182401a14801c200700810702038411001e0002c04005a8000c210300d001d107112000d0b51000041c0f56180549114030305480d9007001da50103002c0c600900e0305049a01c0b5502c00c02111450a21f010080340c2c0030303400028a801c0c144a000d00745a41c17a4194202841c0781440100610129001c1d81d540c0ca003282010319000d07208a00c13419010620320088851502c0c550012548250fa02c42c1d0760a1039603086500b00a00380d004101d0030b071105a42d5850110050f11000152407150040d19a00c810311441c01e0448028400b40c010680b8503401c0e02506541ea07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 483546987 1250 483545737 483545753
    0x20c0f030418021809070c200f04020a050903030a090e07030203150f010e2e110607050d0204050a031b06030221060301230708010602011b0804060b04060b04050906040504 75
    0x9420802c0380540c0e9049901c03441d0b80003a12144007158040d40c07500034095040d4001ca080100e192003404000c0703203030251030003030200e00c244490441c0d0054101c5003079860a141640c01401000745a0400500708031880011918542249420101203071903c0420301000585021007903000da00c1d45800d616604d04160302051030790700134000341c2c0039624080d00e04840b80c1c059035039101501000f421814803911060089034040d00c900048081800380c4102e51480c1134401c0b103000000c040000001d140c1030f140c0000840341c5034440200b824041da400c0c030020031155140000035005600601410300f0641501507401641095a8420018184100103e004546241c660b0300810341610102201c0b96503140040388c050004498003c96074102c89541440c650441a0010f000d904c1c0f80c1ea03501d5447c0e0300d801043c0e007240d4030303030783d65175803841d40780c3d4424102c20322445030301750700c9480303840013003220240d10000c2805e0b10525007010000b0038010505100c1030500280c03696124108036401e00080c1080d841d0220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 483548237 1250 483546987 483547019
    0x10806010e091609150b031905090304080303160207150c060c090f05040209040b0909011e05070503040f050a0b2a070c0e07050c0d080708090f120901030e10020c0f0304 74
    0x8000d0700c5c1c0e046105030000c2c0e84c1405000f060031004039696450300d50811400303400c5645003421180c0c94800800c800f4980007040d58180e80340c6000552950f21401c0210000c03159900742d200c2184200c0c5004940d141007241c04030402c003499102c0074007280b802e20f0107400361034101024000b00403014200f00010103910300c01030102c51b0240c40040c1c0d0358001d64003080192002c0601ca60f003020054050101002c3d0540c0182c0501e0a200b40300d11030310010000d005c1c00ea03102a950840010000e00210b03001c14802495a20031030300c01c200310307041158542c0c1c448240310002c440c03609072903111304c036104041481680300b800c519403144c410314605140c83d034804441c003181e4060501150200390015042c030340a04121664410b151007211141000c4000003068000b080311083c000500c1c220220390300010006114020b811418003421030800034201344006508215131540c101610344140079500d1109200642000701915400344c0d0ba5070708455103030320740700d031300101b8a4142c1c0c01000200700714100b14010f04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 483549487 1250 483548237 483548249
    0x70c080d020c10030f06120b060d2a05091f06140403110102160938090c0d020a020c12060106020304210c060c06110306011205060a0e010806010e0916 66
    0x101042c9850b400c9006003410105d60542510306000881e82c85074891555810620481712030086170b40786801e100303d11001c80002440c01c1c090414203180036103890b44e00c141c07403440414003003000e950302d00001300140c2c41a44e14043d07407903070078504004008290030006d000e020181808200170200c89000b00081c4203074800540f0403c0c59101c00c5015030310901000d40319202d60101c1c04143d503100c551071801070101802e2080740c00702102118490b00c8200103403602c400c401c40303111104000b0040610400c12002000d04d4000c00c02009480421051752003e840f96000685c01008081d41000601031055030480c0058059030001004000036030380003084400b030700c0c00390707103400301c420859007120380c1344060070100514000d0200404501c95501c4070301103039010f004c0d0400340031a0000100e0307070410f0b02c81a00d02d41c3c0026540c092040b80c10820743c210300d030055801307814010000c0c1d03100b00028140c102a0407020090b004000100310141c4001c0c42241c100340350030050710552203251400300111034584502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 483550737 1250 483549487 483549499
    0x7020d031508030a0207090e1b300114010b2a0a02030102210a0903020c011d0a03030203090907030203160c06090605010807060f030b13020f0408070902070c080d020c 73
    0xc440e01d001c00708007450040030060100c0fa00c070000c84402075142d17034240c0200c03a549840e040032030711604400180c02c2149601c1a01d80b103c02410f06080c0040000068404003e2210302c00702c000101014440c0c1d0405080360700000140e070310002c550300d456035106912440d44041c0034041d941c501d06030001c00c150f41c500a076100640c84c00e041190fa41c1488080302010b58194404298a280e07000c42003515840d000140c1e400b031545640d5817840c14201e4400d207402a0040c9d01101132030301c203540030780c9800d414150f040f000e810b03d5640f04800604039841ca504101c0050b00041852031260401040c050381052040c03d0950440c6065148448944424242c180c20010302d00340307060502066a0242081d16040380e03040c001981c483e0b1000760744440c944a980001001c4214140b0f917170b0b119104207403c50800510601c1044074249900000c0c0d0040c003411400c208003004006068481007004030001c00d80d80c40003507202c44281c10300c4260707104075034802c40740d40e0880403140b44000c0d400f00d85400c0f044801c6440c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 483551987 1250 483550737 483550751
    0xb0a03150c020a050102121608070206180a05100606140705031603030f0e0606010206061503060d060e100b011205011212020c0a141014030c09010c021003140105060307020d03 77
    0x10491610340c3d805805012544000b84402d039000d400e125141c80307240076000da11006c1251800480d24400f00300c604400503040500801c0300c3c14110703000ca0590b00c8650b4200c0b1295200f540701d49013000c1914040b104402c3c0c0e2080100105500a800c19405c0d1908402481c1841c54540300d072500c070b10440c2c0c141503441c0090b10301d180801d03000364400405170b2000744042080320024448650784138400e5407064054440d440001c0c1e40da182c01000c0c50b00308105a912306080da2030381c00c28810b0310000c4882c1124800e480351806122944204055044050501000304402c00c040c0300251410b203003c0e070f0b221034441c2018014811300710428001104075501c494004803034050000e0490420392410581b0f0b43c40019048009103a20352001c1c40c0500710000c40d81c184201807035410649942e4922442c001241300d081c00094503071002e41c406403041e400103040c0381c0301c15400b0764000390b55840062486000302c0d03500d40504140d600d850080764050b043c207883c518610b041c0303036102a54440710107004c541019200c0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 483553237 1250 483551987 483552011
    0x50406050307050f0403080307080a270804030602131e1202090a0b04050711060f0403140304170a0507050c030708100216020901080f2401091109220b0a0315 69
    0xb203039030139054520351a4450b40c036464000990740c000d4440c54009003c0c0350204283d507110b84212100318441000380c00381e01460804010000e822140c0a0355000740610000010a400e40020507181640102e01950942010320f85900e6111701b0b04550070740d0011032028040301d141d46080000c11601142c40032640d50b04c50b05a507025010302d08a094215041100348050590088044802c0f003110006640b0345030359880040c9484d40040f20b0160005404d1981c4004d0100410029900540162101c41a00100030001d12140e8000100c050001d000010302c0d2090180902c50804400001c0340034118292906407900d0759800d080510303403002e69001038000c3c4480303074a9400301440d0b070380604990301940c0e4a643d656145e000c030b0715444446000f90418079100c2d082408044103400c41038524080700d40d08040401000300b40c2c0c0b801d800c480c24000c1184800680d00c440c5050121404c0341c400740141100c00040c0070544e440300c04045e008d241040001e0000900c40080000c10fa9540342000442c03c2001c0c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 483554487 1250 483553237 483553247
    0xb04081612030b01020d11030901030504031404230d170d0207050106120c1508010306090206160c0501020708070f090b03031204030c020306070905030307020f041d0a0b01090903050406050307 84
    0x42401040c1c08818100c1d550a6a0150401480314800f60282c41080c0d9205c4001c1d2005405100882016002040650300560207a4085900a40a0315007110034843c41401140d1640c8183c0190b5041d45c8507401c0b002c0548004d80288014010a99411040300000ea480d1501d54805600b0141c0b1840e000c91003c40040c42d42d41030790085070f0003030004c0c0b0089a590b090881042e00d01801610f00300d840910102c1d48098007888104040496079450310103a113180c031202d0081c25030740307002ca030b1200c01000a031107030110117003980c03c1c0103008040b9440920310706000a8a004000e5000320701030781260100708106080e180b5a102103510004000c5441c0028100090562040c50802c4814a02080c240070500d54090b0001c080c2c28825021180161560700d002d83e800056807140c181d06501c04c0050100600780020519101e40d4041c0011401c0580d803c0d01d0881014038401c6044e40307901a00c8080d05000d0b4044c406801003100d074904008000054400070303d14480da01444052150000200d10f5541c410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 483555737 1250 483554487 483554527
    0x30b090105011410020d201204050405060f0618010c06060e071e09170109050313140402070b01091d031603030609061a07080c190201030b091009091e030f09080a0b0408 74
    0x1002c11b44052344186840210240c003d4080d00303001c1d51801c5c002030754030300345200c0400100d280208141d08145480200d8031240a010b0110390400221140304400654980142c4028001d1030840310300034609950001c000e01c5810407070620781341e500c0d01d8206416411690483c1699000303034440c50030248940c2c245001d0209110001e14510000414910500300c0e805510b0980e580300d550213841240407007c0105134083d42034040c0200f0340c0c0d940104a510000d03031011117511803001600150703203541000340b81581c12034500080c4003c60300714840200769141c8283c8001d014152002c00400f0f0800c0b2220400390b00c501031841c1070b10000a090824041d03058169034100c4966011a0001c41801c01090a000340c2c030f40040380820f081a8054169280000381d4901c03415612100700c212929182d4004c001c0c108c0540150b5210081c000d140085070030400c64034814a02070748170036410700d81c905c070010084031490348040c520b6004050250005400c144d44a90010380222010f072322280028100941c030005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 483556987 1250 483555737 483555797
    0xe060a030f0b10080106120c020c040209130c08011d040c0b1b07031115090f01030b0411070606051206160e04060b1209160f090f06030b090105011410020d 68
    0x420f4090f107206990100d0b105068429640d5030340c5802c82980b00700e1003030b26030140310600542c01160307295a190802e61701825038007100501c207070481041c000c5028125080c1d222410006000c0358018840b2001c0d44e410181c035000c41d00c902e00440c2c40c00752104560600c040c042d10200950000d9896040e10600d19811a58040c11095500f900d03030b60714002052456943c600d6008000502c45000301c208003006072540c600c40680301101d500c265100441c02000b6603020241d203d5581d80324040400800e00113401d005200c2d500000d88203042000f08624507486a800c004264011010859500d609449002c09898141003c00c84001810009009825540c000841504003c10f018510600285000340a8010581a50b100c5100c2a2101d2034000c564000c03210401d045080402c140d4220360b01040f90280310110000c1d0b03203512a80c44810b0150203031914511a0744420061008094110441b12030010440e40e41c0080e0012070b00207506c4044408089080c048035120f400b05001142e9084a14204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 483558237 1250 483556987 483556999
    0xd080a090311150402010e0612191e05090106080105060120030904050f151e090c0f030429010e04060b0d0501020a0504031a0421020c10050405010305070e060a030f0b 73
    0xc2c3c0500f044500103001c0b81e0907400140d40303202d4480141018005c5038102d0070a0303140101541d8034036802c0509200400e0280f44000e40d00d4030b40340c48101c480010441c01000c0c1c15800b15284c10000c0195003551061340150b50207900d01014844140c0c1c000520181c50700340c01510b101421940406c081c00c40c05a0316580e508242401c0401820328603048103948103041d0301e003000038107818843c00d0040411130700f115601d0740204541c0000a51419119150780300300c07034500c400e00c0e003035800d000891550400d6504a40c58005030340c910705c4202005078110100e5042c424030038115071400503001d070110009000079081e203907509645041074403078070882c070322a941020003556034041300306004180798404d21042c0d640300b0780c0003d12200c014069000d1030082c0c0c0c10684101ca1510303012482d810300c0d11801c4481081d071141020310f03500c41d11900c01600104007140c07902d0b034441e0718200c0054155140242080104956020603e142c0d5441100b40c60401c03a00c0e10b0002848030134440b1040007071a508900d60360000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 483559487 1250 483558237 483558253
    0x180207080301030b04021207030201050d02070f02030d02030a0210050603101a0d0b15014506080106030b0306070c110112020d0605030106080a0b010e0408070b040302010b0a080d080a090311 83
    0x22a00d44c1a0303d018074400e803001e5140103403818000348c44003040d0100034001001001000800a65a0040d0582c140249400101c0d120740d40e00081c03500d006060030901607000410f070303608010340601c50522400110202400750b0300d42540000d84a0344100350590350f440c0e031100b4100c003060907203c0070445104098594140054641820000c0300c4040302d40c0000091443e000c030130319501c60301660305603221000f8002000c5091607020865081b500c09488140c50340c000c8508085070f152440e1100501007a00e17a42050750400034010161141a00018025442035051155080d803040d449001c44c0d03040204c01200181c9040100d5664200798080c1c00300900202c0e9101c03988c0201d610100844600724000c00c4a6070f604d0846549410f039944018200346004401000186d441290040e4418801e6100d0b91a000441d521707041c2c60f09042c1d4007039005079510480c0c01c0440c1015442c140c00b8058080081440e001d400c48001c280820041800400544401c0548100b600031260030b104486041c040c1c0f5851 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 483560737 1250 483559487 483559493
    0x15022103132019120b0a141305070609030302100c0504082b02012c01060e0f04050c0a0f180e03220618050f03280c0e090718020708030103 61
    0x100d1140d0021902c03c4035403401d1210b10380420f99025003110f0f070350034407003003401c1e06511102d0b4000c0300104640c1c0056151112100c0146a000d40d42c0c1c414454141280420500c50a040e4580003807604500c080c0081c2c810240046900040c100103164460100490340384501c510480702030040c1c1d03215200500c00c41c0110038841c0342c000d10400d03090f82a1a503400d51080b078118103c2c01d030b902c1d1129000310b40941e41202d0000000310b5181e50f46c8641440000710301c0955070082c0700707002c0310100c0c0c038100a800408140000c200d000e007e00a1603a400710f40a10829050209004110407140700f01d0030006012003409403000c11300d8001d50b140040c500d003600e4079030798030002540510b0650b184000d1005d41243c4003003030341401981100040c00d003101d0b400c034030582440d0520501c1a000405141c0c984180c580d006040a554890124441389600381d41c02540700e6407034201003525481e0004140c03880044100100440c000642c03404a605c40d80d82070a01c8004043c4103002881100c6001d081400000004018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 483561987 1250 483560737 483560783
    0x50409050c0a17010e070b07030f020109020a06090e0601031e18050a0813060807021e1504050c0a081b0d140609060609130209010b030601050408010e071502210313 72
    0x640201c2c1d0b000307002d142c00d1708a60300c0c4c80c3c02c0c450068002901050101401003031007055081d12440090000003401d85d195000290781c51541c0d4000b078002120403800b4059811803211035904070600f03080510034400c511a15004540d282c2421503241070391000c030740714104000600d0607d81a0000f00791092003e580c1004940f80d440a024180b054090b04000a40c95219410f001e1284106601800390804001520500400328818095080c81141020700e04603002455060050707119000800d4004001401e01c203003401642e218103d150000303160780304642041e20005800220841300f6000b801c0551501075504900c060b50b0340001d218901c1004905030700012241e0048108403080303400c59942d62a58081481c6e800030003504013001030010072502c246400070396000141410420b082c16140d0880c50b084540d4a1005802640580700401c1405d1040c2407520100050744003500300c24100f00800502d60b500c465031070010410001c0019041c0d0b0284c91640300a42c1d1190001000944060084c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 483563237 1250 483561987 483562019
    0x23120309040c0801030f080d0e0d121107032007080f0705010318080a0e010201020418020316050922140702060f0c04061b060e06040807260301050409050c0a 69
    0x8080d42c5000341801d01140158481c9040320741c0304020f0f94491850b503442151a8000013880942c207602e0360418007120805003d40c192400c41651601c103880000350500b801d9984c00c83e0706a0a5070010400c4c400800d91104060705032442c4203404005514041c03096070700e000c1071075010b41d0160240b0002c0842c3c100c070100e0f01c607086880c01d130307800c0c00428000e0055028004480304028081d003002c04c20704988074001c0c055400100f205000060501e0380c0c0e40c455074172591f81d144910072150750000070442d00503400c0104215401061400509144110020a080b040301d155480310311005011242c00c0f02940303800000345da265582d84140c150400c5030000e07603562020358014a02c400800d000550017072000c030568084400d1f03a5213550301c0101640b009000010b1012064580503100c03040c100c03000c2810046240500e1182c05032079940c2c005c0b42041703503c03010b00c100b1900114000d040300c0c0341ca00180c02e0a0300c1c10b4860031180040e59000c030345041860890340b5040d2a802030180c0c940021503414170103c070340c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 483564487 1250 483563237 483563239
    0x2150c2b180b12010806252d0210050a0c0507023d020d170a0b030a06020f0901260402040f0e060f010911090307120201090915090c02031323120309 65
    0x200030380c47d40c2d0304000002034a440340c00440010710305e111101500c240444061001417003c2200f1404503500d070104111101c460010150303000c454980d4264400f840303280d070700c0301540e0b038100320f6003d001100520602c107005000e4810204005052110208108101707815408580302168400c10510b000c0b40030001c0c5c4401c200940950303030300000c0585c01a14031825812100303030f840000d42c0c2c64501303410040c0491076070a41c00d8860340b01c0e4100042c0d550b00c004c2c604001ca03c0340d26a2079502e95800102480b45081c000310410303d5291801c1e0043c0c038244101608680d0454010840326141501d20004188501132a4403510448080c01161241d120301c0c503068a0426000303110050700608002021302c00c48102c26019803100204214290041c40038120951052400190311a0fa82444106840034440c0c0b542c440404a01c04001c9010244101108003401d03002650034071130b18083c660f584011034400c000105d0301140e01c100da0004605110700d0440e00c0142400c0c5c645040c8400c155032500040085 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 483565737 1250 483564487 483564493
    0xd0504060903080c090f15040302060304110405060612040b070c1a060a0902160f2f2d0103090c050a080114010f0305060403110a02150c2b180b120108 66
    0x2c1088002c01e00105c2d8540000540822001a8403034241300c0d1143c90350b03c2680c40c0e02c00501c80400169a820029405a40196034400316164140c0401045601c0a0941841080c040040100d800b8800300800e600076004291380c0607641d1003140680714074205000050020b0680300184065081124066001c2d41080c1c440e070201c0c549901d0700320f0486c481c101c016071407120702600d49400a10a842c1010302e0328400d40d0b504420404100300e41c4656030401e03d031801c0719441c2809480d50750034080e035200201c03400848241400c3d6521241c42405c0d181500001c1d04043c1ca494074401400582c1e401d000c010103000c1c100a0a841d594408a8000c001500700360070501e400709d0002034400a11103500d016a83c0120107440e65031034aa4003030300c14844c54000d80b071980c0111607185015907074a0b4950303110162035243c0c03513942e0443c903020759041800903019807202204c1420488441c480f52588410700c101a03041140542e8581c4401141a08061f1712046011000213403100d208403149910078100c035659412 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 483566987 1250 483565737 483565741
    0x4060c1b1a070e03280c0b0a170f161e020106091107020907050711030d0c0b090703030e0d030917031306050405060a0e060d060924050604090507050d050406090308 72
    0x80300d2a40003034043c40da05034001071003840400043e8401044004136440d017501d5500300340d41c4401c010409540005110000851808100d5400c411100369080c281d82c1a4021840d15204002c1e503450007415603c19401d004a440100d107000c2c544803100e05088960714070302080c580c24024068805406080d4005051800d8160003180030b4085d80d003038550090182000ba5030303103d422640c2e508440030a48202da40100594200e440600c1034108200305583c40070784881c00703402c0c8140451707400f42011007039a000700130400201303a00c03070a8204106c2045800301c404d283e49040880342c18a1642040c0da140014092001c6003c0002004101d41452500c0c84409540c0d540c009517454013170351150381e070000702c1080008240c52240e100d52547c000020501d60804d0046000d41048400d241c021100b0305584007015034036108814251111803030b501100000043c2000089030050040d84101c20030652a407001c2101d06001d002560350403000c0c00010400c034500341c2045c001038200124203602050003500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 483568237 1250 483566987 483567001
    0x51b0d0201150e010e0606040f060201022511090627152706040f090309050109050f03031803071706010e0a0c050304150204050604030b06040c09030b04060c1b1a 71
    0x52090483e4400122001103138078220301603a490b41d0060007181e200004001c003080051910b05100c003d003015500042e03d035400c41c035a038180214420310002c203039070104003001c0004540e003400c200b4655059468130100c0e101c10300494079a03026260100864140806483c1002002c40901032040e1920f0302801c050b00400428802500e1003440810172030540c800c0e809001c00b020b18002a0840d00c0940001003c12548401c0c0084803002007040f000500352741000c119030341c0e00040d0400600b10459110807101d01d480002980c9220310200039030420741802d01d5607155075003400407800911810030440e034403803040420103464020900a00f00751807080c0010074200c085a10030107460180c0758407100e01e1a1256254000c640311010b100c07000d083c1c0c01300408501a103491000e0030080d0710582c100d003128107200007008151010103c100041142d0350408201085001f02100e0f0401c1c1c01c02d00014900c04070081c102e860050121781000040428181c1d03d04000d0980c0383d043c02140310007100100764a400c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 483569487 1250 483568237 483568271
    0x706050f0c04210602071209050411040501120207020306010612141e06120d020a0c050405060102030a210501030f060c021204170c0901060201091202071a0a051b0d0201 74
    0x34581c038500800500090000d00394500d0968154098072049451940443c4d4641c02640d0140c0000c4680240500000582a4111036072001501080340c05100d60b1a40398803040d000d01661050354100a030020395540c3c0182d90b0350469030071301e8000d01580d02030740e110760025150251021020508500e4149034000c0402038584060007003400f444030100c0740820302d040203800d40019002076844072101c0c8510b140c541b0108403017040040c00b038010308220b4403e420311b2403d1b00720991040b405941440100300040c1c0e800300c21292001010f080274050140b190b02110409000f00b48048685840d000010050084da0701d06103030050302c02d017400c2c0411b0403000422619401c000980c6002000248402c2c4603850310081001e0045c1075920803100310807000000140c007a00c2c00e03405100982d5440740100c0a00847c64014500d01c4403600041c54014504050070081c0c00d6005400c120800740400c9030749003544100b04a441100d0b14446014000788000041a12001e540380c41001641c030f04158400d410b0018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 483570737 1250 483569487 483569491
    0xe012309281406030711011407090501021002030c090108101802030f0c090a030611070b040b07031d1002130e0718080a0b0a0b0a0e16080106050903031b03091201020706050f 76
    0x83d140d00d095458041e0161981a002003032100c6030354840c1803c451208400d400280b01c0c46007540c59a640070320300f20001e814020b44441c0009a64010010440103001150889140c0700d42840c140d6410f65840780c4203007000c1c00c540c0000c50130034500c05481102500ea50081d50250005010b400540d40321711449a03080d10031040c809421002031070040000c10079541c40810402d484540241c035000f10f82d61110b80a1804480c01c4412030190020310208507414480d41c0700021a040d403500318206080007131656058150103d02c1a2500000e4103417514403a40d03090801404100c100304414282140701802070307120841051a58011071000080040340090351000345900104c104030151104512071002d008441060b0f40c010208410000745108071000491241a50789184c45407401180c42c020290101070740043c040100c00c0c007440100d550080f0480c1d0b02c03010601e04401c146040080d10713074118010080c40f6a4000050306041080c10019001803080c0c0d481103204100f0383e501c4003c3c00204241c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 483571987 1250 483570737 483570739
    0x10b07050c040b060903070801020c15060a0e0a0914060402040b09070f0e21030a080609040c0e10090e031e120c031b03071e0e0123092814 61
    0x1210324040700e41810381c0600b440200141040303203000e120801080c07030035000340d01003910350b94002440b80601c0350922440d502d8002c12101119507081002c0012545602401090019075810002ca41c0c804602e80c418201140e00021300884000c2603141180c446108942c241d009506282c0080090f02e1310217007040c4107040c1500e9070b8005c040419000c0714801e1100782090307000380c01e07221048818a103080e541e0410000c0d0000550362401d101d02c00070406040500b0042c01041000240400114030803492000e07204845400d910075640c034440140044413660000f02010320702043e0802d10000400180301030103a607004100f05440c00080c9a1b80c9125041200d10030800c3c20b004034001c99071000003580c20440382412603440b00003000d070707441541d803094076480d0204100e0714612000c20b0003160034600300e4110b41407280903010ba013000a01074100040c0350070542c074040c6071134026000105059514505000c3d10101c94401d0911a50660041b00040c4180c108100c150020396201c11400321254600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 483573237 1250 483571987 483571993
    0x11100501060f031e09080f0d020a090b04030804091a1005090103150806070c030207030b011e06170f060a08031c050108060c07020118090510030b06040b0105190e03070b12010b0705 79
    0x21000d80003100400b03c5403030894062a081218402c00721f0640060817244080140059032034103508005485a045907010000701103080c403082002c14203d20544040703800424010850324440c440099400b0480b00c2956408007a50542c030442c1944030001c0c00d18480282c07020400c0140e2034000303400c0c0080340c0c49160200c2d070048002a0072944500d50041186100b4012940410340702d54510f00c0440090304841c0424000c42d990901d003000c4142107000806a42c14000f0b0031180c45c50b0711401c2c45800038104018080c000c00400c0da6502d803c1007400c0201000415241c403425070301c0642d0700351940301c448452041d0500300045000070020540c1400740e0490391086103090b00540c010754040240c0b483e15618045000c1c0c000440d80c1e240d01a0303500c5204000d00308082907056142144840c0c20181c14940078610340000e550f0b503641c00204030750882076a07020210488080702c100700c070389104158085415008207140016040180783c080d20130b14402580c1003d03942e0b2540c005c0c200380d001d80703c0041c05e164 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 483574487 1250 483573237 483573281
    0x306011203030207080c0c0418122a05010e0106080c012c0a03030c0201032009040207081b060723030f0901090813080601090501050906010f11100501060f03 69
    0x805690a0449034510a040150810055465003507003600814035081058101c3c8550502038602440f458010031011038244544c0e45c1e1030b445406c00c10304c5602e181024000140c1d18030481381d0901015030000480401800a03c2d1158507041d8040c280c1c030728160300d642d820f000021500703c41c00b081c45208000306940300c40c1c202403000c42c1c00c801c3e100307201c00b1400002d005076104125511030754543c9001d90f0080c2c451b29032003481c1e0b01c0010201c0b1080d420003080c1040c1c0028100d042000202203d1101004480c00343e140e0025080040c034074860381e036860912146c425180304000d1004148c140c8500116240c110900791030030b1540b183c205014001c1d52401904100290f0000c801a41c0d42d9044100c4100010722266555036400d843d9001c041c17104c50000d690601003040300e50800c2000e000d09402c280a1042c0c2d4540b90125074030a001911060500440304007481c52a48646040c05000950000311070040550302d00d440000c205c00c3c0241400150385803005055680a4007481e9501d01071f40c0050071a01b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 483575737 1250 483574487 483574499
    0x150c0309090c050a0f110a080301051008090c1201180b09070e01120204180512040906090608150c070c0b03070e010e0a060813150203251d0a0b070b16020c030601 71
    0x1070085d0749a00802d202d120340fa14a02440e0810900c4e4501c0c0c03040100c41c2da2941050108441e18120800302800c0003004802c01c00c0c1d10001250001d4144029202041000b2002c5004e0307001d4251070a00203503001e5407000100031701012401e20381c041d5480d80b05035a0b0300c0c0c0c1c075160484480c0b0024043e035884054500c840c2401428a944205102812039002e450340c9200396548600344002d0350070034400d40d00c0101d03040c8900c1016200f0758004108489080002c070b8a4a0b481d203072581c1d868a40906c44858100020302c1070390a4038115107185074017194000f480d58a030031154041d50010364181c00040c0103400c2620b03495000e04824140300d04001e220001a600d0b108e01260155001407248480d01510144c6100003441c0170303070320700304041c0b41c02015849150210040d03c16040b00400103400451525910510580100a0111280e0801c0c01d04030501c40d004080780480f4800e5000a800e6080003411400b4000706090440c050038084a00140818481800300c2c0d4481c014460b803603241e04100010442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483576987 1250 483575737 483575747
    0x2a0806011406092e0f0228060b131505040513020f01030204050301020c0307060c091203140f0406030c0201050601050c1e0a05070e04050601080312010902070309150c0309090c050a 79
    0x851500100900d503000600c4074000b01d610940b03030865104c0c0090354690068203401245001c4034100c54802000800004403006280e0f2400c3c3c0000920103549020031002c1c88050380040c601c0d10809814001100d110740d0b10030f001400a1040c3c0b010a014014011407280351a01445015542d080104125030405800f0041d800b400c256065051650030807000646440c2070000e041240c6520010b0342d1100e00c0c904010042c0c03040b6070303028403c0141d8100300b4021264051042d4146507010f00e819651100f0382c0c019642180f0555500c603151080201c0c001a45e00e43c1600007180230643c95009002c01d8403508015529801f615045403115009103140801e0b005158040b25080c20180c8110f4800c11001c3d248c25041441e42c0c2c01c03016441240714100806d1200401c002401005138000a600c0c0c612594006901c45070180a0704400303030340024450301070510540003800603040c0800002c086401c016009001484001000c4012a50104001540c6012807203a60400a2152280e61814050041c2261 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 483578237 1250 483576987 483576997
    0xc1a0d0e011503140a170c0c10200c09040b150901050a06030b060d050412090e13030e030a05010c110c01020f0307060b060d020a05210405070608070504032a0806011406 74
    0x32491003a031745564040b42c61580074094045000180c0760f9101c107070b62203160408505d82681d0b801007110714840c410942e4880f0148502e0018284035090002c5805071140c00c200340d101e24140e000100ca010303c414801a00b4440d4014041403c40200010081082c012003107000d114603640211928001c006070750003a0009079038a80000c003070510b843d48a803020001c450f0169010744c0c84407100003007500b241d0b4000390200d0107000c5400c8103a0031032416000800500314110f0b030013000c01580380d8411240303850400010450700d038440000c0c40300d6039400310000c00450354100b020f0314038803514a80c1c0c141e0394004601d02000f04042d20141d4030341486500c1c0c00c0054070354004004d801074010000d104680300540302608846800d5a1140d96882c00d984a2801040182c0c0c0c134002034908050034440007640c0012444125011400d11050590b074405081d1101d0103240c0c80a407002d00804014a0014845000b10007500000d4090401e040c1d242c070030580d0380307080034001d10f0504803940b981800342c1c2c544440600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 483579487 1250 483578237 483578273
    0x3d15030b0a060b07080910141e0903010c030f05060d0c0306051b1c110f0d05190c020c0307080f030301091104090905010f050f1b070c1a0d0e011503 65
    0xc9241680c0314020a0a9405180e0643c1e003070b9400300345500030349000780ca1f0403901c601502d40311a520102c0c0c8102880d82c07207084c038000c140d6080344680500c060520f20940f0000706000340200211300d10001d001d8003914060301d03064941803400c00001c03494684050980203480d000200706010906596509000f0040035200c089828240260140e81000f104010007912140f0708100081c03107040d54420f4181e80d40000101000081401070350b480c40e0b101c405507001100d030700401140c291610354202036a45086507110340f149051000540c40b01d03030001044a100d20099040700c40d9255180e1100d030300c800c003201c1d8000083d04200010000b400142d00032040140080b0358052605544030004800c40d240e910046650b40d444401c00c0030f21045500c605a400800c404000c00c003072404080124442e2009684200b40e0f030004900c95052068484032400505101c90210521540000612905801400e143e001981c2008002c920743c40040c080c03072840c0c04007420b082d000030b0700355902c0c0c00464500c4032180d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 483580737 1250 483579487 483579491
    0x306071209051207050a030201050f04121209140705130e0723040c17150603160e15190e0f09060303130605190504120609053d15030b0a 60
    0xb28040d00303040f4005001c094400c400504085106140203400c0d104000c0003031829400c0c0310104404a103426050358068400c91400101660b001c040d444000d01d030106018080081c03660b512100c810002400c0d009681702112010014146038500700c0c00c0d5414402a0295500900010000001a08000504940000b05c001d507069902400300781112050030041d00002e83c01c10781090702025404800c0c0e0000300c175013800d2204140c900081800c501c4003034582940107140f2101e00002c90721030032940e21076680080541e0b030991120381410724240c02504801035505140390780d501015010341d0081003901400741c45007a242140030108800202e005104503018081000640c2c0c1d4000078441c01c401070001c0e92035480c2c4401102c24052440c2c06920380400900000b0001840b0303007031080f1840328000e540418046030344417891034400d007403140d9010b40904003110401d04035103001401c14001480305844100c1004c090341c90300d0380c0080d01c0060441c109905400780c400d1001c502d11113040b541c010090400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 483581987 1250 483580737 483580753
    0x406050a0b0729040c080309011d06040305190506070c0f0f02040e01180b070f1b05031207030204091406061c0b12100c090b0319090209010605030a0b030607120905 72
    0x1c80c1c10110030726503103c03d104042010041081211340c900000740c900d15008500f040d11035000a00060305031030341100c481d800a0b5094003556540f000b120041c1d0341c02000d80b188082d071003000420020701c0b10000c0341c4c0303801004001030601e48149601130169801805009140e10641c4a0508895000c40d00b42d8005444290b032000d64003003401116452400d01c11b4000111520342403100001d94054580020007070048804004554011203c03580011602071034003002c0106d141c0545148980002c2400203c0150200030000d07405601510844051240c240000b0054074108040200704a030f480385c0c40b000900c80c0643c0308484003030840c0c04898074000000d40082040014044c60069840104142d12035184035000001c24060112740701d48c682000e01c11076003040e914025500004203803061210180c51f1880510b0b00b0740e00510803e81d009801d001c840d507113039000101658000c480c001c0115040c070b0030b646640d040015035540b04024071358070305d40d0031b081004a80300070b411840410340b410322860070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 483583237 1250 483581987 483582023
    0x306090501060b0c2b0e12071a03010609080111040303030203100512010b1504030f0321020d0c02010e0c01050f070c18021306170408030702031c020c0c0406050a0b07 73
    0x7040c0d80203003800100b9005800c1070034049840081800c4d05e05108000c0c0c2030110041e00000b1212030a2401c850096554076141011032a00c0d086502c40c440105100c9152441d041c045030040d4143e40d0070750356880c102511038049600780d803c01c0c003c850160604000400100380310b40d000d15004200581603490704c03039a500010718007032504418492265980d105078156481d203040102100c2111101407402c1c1499070725110311500030588041c06109400d20720320340c000b004060302000f000e07030050b04648902c0000e04000085c0541c0d04403001541ca030031100c1001013400903210301c01000580d500c501d070001ca204c40a034940c110079001c4400078a550400719418108002d41c00c9001c8000e00d0050b128108840c0100748011540d100006204201404080701e58580000c16403254000c440281c0da91140e5030120300e14455040303d4a080440c8202100340820303550004c18405201c1d130101c41183ca07059080008030380301807180651000c100031040040c4075240003e444810700400204413a01c110f04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 483584487 1250 483583237 483583259
    0x60906250c05070905010503010b0a08070b0307020a120915020f061807050310090c1d0103110111011518020903060103110f18010f090b0603180f16090606080709030609050106 77
    0x240180b1a80c1d91940700600c03060238244924108040221140c102680c034000440d40c0703e209031300138000103071170000002d00114020051035078200c0d032203855045002c0035203000501c0e04049008000e01958038280b20350380b16100003550704025181c2005031003140c03107841c5003900300d2103a00c0822543d40141c040006843d039040c400c81841c00a40d510110f407266207450528041100398202072482624000380c503d9201007441202c1c10741c1d070704c00111000141c00000503503156202980340f9540e50708024490b41d0b070004d001e045604440b42a03d040c1403444194003140180d000f860841c1e41c041d44031800400c0401c030403050340c40c0d0708000030f09001040b083c40d4006c0380d80f80c11503141c500840c0300403400400100034282498002850710200800801d41c4200010b101444042c00d103103001c0b035490080d040403101c180329030b0740c1283c206e40407107000303030201004400f8040b09031240c9107030145490780c0040c545000d1802d1500c10840c50f41e401c5a00ba09641d1500004c220340d00701542c20303643e50000480e50078129 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 483585737 1250 483584487 483584489
    0x30610090f091d03120c0304080403020603040809031c1d130c0f110a020906060d110d091104140612010609050a0e16030314090d02060f0c060906250c0507 68
    0x6400f141041004444450b000710351002461113900402030040c040c0c090b010001d0304a0b0242034495541c0e240c904000f5036901503504043c1d8400e40000501c070400c1102802400800002e07829102d80b0180e40c6a000456842c1301034440200d506d00961450408001c401d5041c0d0103001450700d40f03000c0c0100d03451001ca8143d41c03182c00118051907000301341c2c03a40290260b0319510f6900e00a24038650507a0124149003009080da03400f40314049801c0d0002016a0041e0441201c0c040c94662904044035070f510246c60b01c8102a516180008030a000e903044c907010702501951a082c02c61082d0700d500e000e00090070400800041295626480803542804a02a0b140164038458002c214a400c65a10034148503581800100d618005002000025003089070040004004103400762107540300e0012480078450704800030342c040780c0094803003804200040640780c0304104004980c2140c3d10520242d6403440262500b1b91203400700d401c441075070300c420340f51803510f0703030300c514181c030f0341e41d02070b540c2e4514041c03503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 483586987 1250 483585737 483585749
    0x1413030201020705030d0b03120c030f090d02032508030705071a120c0304020103050c0309210f160b010605030702060613140910050c07020105160204060f080c0310050c030610090f 79
    0x10740007d80e440d4034080045082c4007001c070801d249003840400c0841c0c1d407846000c2e075042030100e0100b298aa80c0c0d58092140c82c415401400303943c80001c40d05491425a4041c0070038084c2c4884000c0c000c1900380000080d107021380d0f84040140720345802d003107400010007126010400302413000c100810744029240c00941c042c114000da40ca440303003860320001d015968001d0004145e0941813040004007407002070000300070400040c1c10000f80410406800301407003101c0d84001c2000340041d080040341081350302d00b02440c0c00380311403011030f0f40c03180d4007120b180c070056905000681c42007011850500d04042c1168011000d0070000078000c06480d41004100021110060541c10151909610208a01901d036000c4414052140303840c0304c40d80060242c2c040c58458902412138150340104541b075540c000c10150903428002001c0580d90a0865501d0b40201050f138000d00401300080d0150465004a0740035951100c1041d055503210403e1001c2c1e5009005070f002000012180000e804514003d440b015001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 483588237 1250 483586987 483586991
    0x9050c19031a07020c0d02010e0907051e070c0f05060409181205071b05062b02190f091202040b0d08130911030f01031401020f0a031b031413030201020705030d 70
    0xd04120003a00302000315403558062080c01b204000141e0703001101003682a401c0324800490789418000301d945001c1e00c0c8282c200403079101e90110301208202c001c0e090183c421031701804200d80b144110510740000b4800c00b50040b01c00e01042c07029560365040082e40d0365444a42c0b00c1c40040c10f0312138003d048030041041011400c0049e04200344105040c0d4401d0007940250b030040f40034a0700c00420003500c14600f0070502088412411202c1e51910140c1c0b566411000303505644178880d003c504a001d003c41000007010031586040f2010f01030103090442d080b0b4034101402040c4004980034880544400030003944c3c001c01e603201c00c40020fa400030203054109008802910001e0404800c0301c102c8441907048030184005004016007500700800c6a8192039110400b98004825100514060300a11300c202c002000045000e8035109c0d403652110700d21501e03c000c03108400c408608280c003200c034a0700c0210035440001001400b6480003c0c82c06072550312900c0010301c0c24040e0345a49040d5044406541c0c6025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 483589487 1250 483588237 483588241
    0x1e0204060e03060403080a090f05160e0f0106050405120a020a06091802040b030a020a09240807030b0d0605070210020c03030901060501050c0615010c050f0f060a09050c19031a 77
    0x603070002100e65155000d8000f40880d080c180c40c0688081402441001c04039240c1c807010080058110707025030013640c03000841e0041401c0348001250030019000740b648001e50080003070b0f4104041494903048600030707180c4a10b0710782800c05000044407010b0200d4100e02c69070380d030300c40141ca4143c0e0a030020002541c0344030301c490410354145951742459200040740d90040c40b0501c0003404c200201c9810030205000180c1d01c0000c50800c4d030303810311030ba400285aa0b05400c1200428400024483c0ea12b45065440d00c4075503507014010740465501c0d035915600320b2021304940c000950b69a01054208aa82c0101c45925420a1003101640d111108200240d0004802d00882c18402d001d036801920090820a04041142802a51b00d1030000c019036140240b03600c840502e40d01030300b10144844e8025083d0b42d83c480c60000000d582d40e07007018180a062140e40006a00c1820700e00c2441603241d40040039200c00c24152041041301e2050080c0c070040c0a40c3c0500c0000010040795807054a010800c1c0d44482038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 483590737 1250 483589487 483589499
    0x80f0c0a0507050402071707050f0601080d120c050a0c061b02010605120109020d080306130f090506150117060a050a030308040308100f03120c02041d07080d090b0d1e0204 75
    0x741641d2003503001304c0c01806490002000380711421040c00c40c03405034a484032201c1c00c2640c60800300c60361001c2240204000420400d5010515010303000c81c988500b00d070548684510b0045503490000c80001900501608810307a10030580d42c0b900601031a004a41740303400392001d0521081031191040580c0d502c070b808200e142010300c02300b4003018035140208204d80c003940100d0144801c51800400c1000c0010002e620b60340e600360315291200c404002000388001c541c15140040450b080255020703c126000035203000302c0d0721350841c81d1a5040e511202c2446800c000a81048400303801a6440055500c0114403902c54a50720f000440c0607a580110314241801d016040d003201a01d1044c0803a40c00038240460540d04020301c003200d5200c4001c0c0400603d42404030b4003100d050000941c03090a100320800103c083c00c0c1d01c072030900c0d00c45040d68819940d46e22141c0da02c14009a0450200d42c12600402c41802c40102810240485401c017146040c580340c041c41090780484c0203c40500c3e4081818840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 483591987 1250 483590737 483590743
    0xb0d0210080612061e09070b040521070303030506121b0402070309180c12020a1704150509030a03060503010e10090201050c2401060513050f010e060f03090f06130f080f0c0a05 77
    0x1b955400038240c0c00381010000c60040c80745001b0b0740e00852030450100307e42c404009210781c1410241c400d44140035100c0c40d000f8081c01082d10301c40c3c80350800d00c0d00c0e1180a1400b0400840d0308000c80f00e0f000c019151541400088e401020055050290030a000250211008144603e00e44078500009200c820888054045030303a800d520042d8030700c14442c0150854118104026034003088504c40c0c010754030f61614039080018400c2c031586207400d0000340189120b001014103000e0b142030b00c041c84402d48036014175088904404244003e03600680b8504016120340c0e0100100c04d006251103403400d49041d0f0440c0c0761200c0105814019081595001644441440310b2030141c170a6242c114a04000d10703003441c0041585005e4280700e991081100384007a80200003940105070042d001e2901c40c80107020000c0c3c0c0d9041256000b80c00d00400308800c61041001c6005445019034000c2003013032901d0354a400310000c01304030b403c8a00140800414004803105006010300304035090040845509910301241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 483593237 1250 483591987 483591991
    0x181c02150d1410120b010902031005120d030f090c03060b010c141513020108040314090d0f0203010606090f06110a060501080616031505090a020f1c0b0d0210080612061e 74
    0xc13021000030111070000c2d0f40c000009046503205480540c4035194801000071102c1581d10541c2d100050481100f00410042800c072891006901c04010f1021100030718801d443e061f4200a007504280345007400003803c9a885600107600c10b1402c2854601d43d666203950014074480307661119440520b22084615800c0d4200380d10101240d454405001241c0c00684003000203003004081c010038586001c40c2c64a00015100901c0700105020101106824009841d030a101d40a078041c2d4240310001ca003c5014040c02011501c107140407260403441d001048070100141c8500b1541e50241070078140105400c0e000b51406805118050180d03410452481c040801e401791041b02814200031040703180e2a4500d2100301110003c0c4c0c0d903244070340c0c0da65104200031710807520403080180c8041040c01c200e0000b9004d01001c4c4120820800208140c401005040c15a000300203500090f161640a1a00d1003025141d8010b00c1c05400800b80380d40c4082880e080600480f107682e80d0b0100340c5140b24094082042d015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 483594487 1250 483593237 483593249
    0x3010e01120807120e090703090c090603051c050f030a06261c09170c01081f0b1804090303051e01120f26181c02150d1410 54
    0xd41c50360700c56640da900c50094080240188107010090220135020f81c18401c5d581100400c405602d141018000c0c004150381041642c1c1e015030503101003040c0c01c0a00c50b000c181c0b0b401500425645100c1d5610360300505004400808000003805143d07140310b4440d0180d07028080c03905011814900b442d5210480415044d041d40442c0b841382e552541c200d50200b00040c41c10b41015510b0070542c201c010941d8806c40e268403541e07500450740b4225807044004119031981e03100980e1105111703100c0200025140b9600368188021107012282003041c8203000c00100004d07580800c042c00408181000101180d600a1080c0d000c40c1d12034040040300c0c000b003d803c0c2009400540301032220b50500c5040551340c0801c0500400094028209605100c404122225039100000054089001c04040304109400c0010640005003410010131440d1515240c0c94a81440d1078880403010b5000b60200100c0600a491002e02114204000783c03801d00d0a01445501610402c030072040c504203030b41c0e002c000410701e07032041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 483595737 1250 483594487 483594509
    0x5010b040f0b09010506090a1701020c0d081b0912010c020d0801050627010c02060c0f160e0f0c0c0d05030f01090e15040305040f120b15030a0f050106050402040b03010e01 75
    0x24680ea550403e00b5054a8041d1000741e220b600703900100e0042d11030368024803a07110b09148002090b050540007850901c030a101a90304147d00208103650004080e40e240c54021403445076124607885c510302070400c0c00e00040030042d01003a0070107120300b1100b49010b03034401600301040b5182c0c5103803c1405a070040c10141c03100c5182c03e02c90040492340c42480f0703203c14040700500d0702e8960282e200780c09481c0819001481c00b50360780510a59160307201d20001e0400154041d2041840d800a80e50f10b06a080700c82c103581000070b990b140c0a149000d540014100c05405505000c1005214803c0080c01920781140d100c0b02d66908010020a001c400168818152a81402c4c00c007160302c100802c01c0043c0c10410040c0d48096116442d0a8500d030003142c010000b480d03d001303000200040d204440800b101d00400d5608005c0d161880e104148060395951150185d101c80c010034006031851100c00080380c00741000050541e2217030b00260507a070099010403180c0da408401031104d0307100b900c2214010010244a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 483596987 1250 483595737 483595751
    0x10b0c07061103090913060b03191218080312010909030c0308041406131109060a05060904020d0f061502011415121c2a0605101205010b040f 62
    0x49a0340e2800c240c000c00040140310419140d141d0300800650f002100c0080504903980b405903200c401d00341c4802400c2c0c600905040e030b012030030300300491001031840c6e00c0b00d0900c7e40d19040b81c90f40e00d41c0103110b020402c20881d40d806442046400031b800200a868404065661441001e1a00c4400700041c0c0241a030381e8545091a000240c000807041c609542c1410a60116a150304044910700450741040e8824020b21040048044002c0180b0040e60b101e00581d0541088080034000c10610807108980c0100f2010401d2143d848c0600c040c19045100134805440e2411019514043c0c90403076000980058688009200880d644410841c880c1c0040c8000c00000302181c2407202c40d243c0140002482c0e219414401c034a58031808400009000000121201c01311941c800bc519020f40b80040000155a12400c04030b01e0003c215482804c1c1001c030070a000c2c1c001c2521260001e14010f440f050b42d0802d90080014120031412503014054040c100000b48095200c0c1400243c80000104d840600e01d8014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 483598237 1250 483596987 483597007
    0x2130f0503030d0e12040b1309140109110705011406030c0312041e03060203040f15020f0d0b06131404060e070507030c05210d060e070f0f0e120d0206010b 68
    0xc15a210000f001c880415401182d0781e8480c1029074240040c0050540041c0c04241c034210340c0020040c0c5c0c0c065032a824038a6588692520407220301c0c0461880006c29440104641c04040e007100345c54400c00e000312458070315255501821200a5400030002d040007104006e442c2c90b003440116441c2c001903001c0c1111907552050142503201c2c50207400560040c0c0300041d05410a01c11403c0041e43c0c2c49a811550303420542800c2c030750b414071404111910140f246101c01102e0310360003a0b8210000100c01d450610141d4010400540520f003149504500d090005c610303510b485c0620f00d0020040340c16601100b49000c000d200c191500e6800c82031882001c1c0d024080b10aa0000807692119003611f4100703c40b20711481c2c00c50078044140502a5a41414040d41205500c4140203001c05030110004010095582c1e20301b1556100031660040810f4502c41106d68083c081c44000c80750180528000043c00701c0c110015207680d0f40305101d50003a40c0001520810150100000e901415001d4800c0e402c02401030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 483599487 1250 483598237 483598243
    0x18170c0a2408040507270615021002071511040602061509180a171c05010806130c08010908032205030a03021b0105130302121e0f0d0e0102130f0503 65
    0x30800c41040802c80c005030a12400780140d40150401c5d550404c00161034507400702d9000c040c01102c0e905207207480c10010b020030b41c5140d2800300c84c10540151004600c603604060003074002c0141907038040310304030f602610707503289102d12201880c265010075103842c244440240380200007050b03030304410608007081100e0b43c0c602d41c0303144e40002c00322417200500c01d0600402c0d04100728000020071041c1c1859a0402d030f1407120000c2d0807064008460100e032604401c6400c0c0035100284036001c0b0540002000c0782000c00c0795150b6145e070300d006110f4804010707500c03101c4a0840e48124410b440011020040c404210340c804002844948070a010030301b2600242c40d01a12131141c01804018180e00085005401d4804080213003d9159a00200442e00e001006411015074403107089005003c1c4c0c110082d02918800c3c1a212014040340c900542c1482d081da05e201035038064440c407070149200740080c0d03021038410300510003030f03030440c40c000f68440104001c000410312040d000464800b00b8181c0510440c6c0f000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 483600737 1250 483599487 483599549
    0x60902251a0603160603050916210515040606210c051c1e0b0f01060507080f0d09032714040b0a050a0f06020706031107020118170c0a 59
    0x3440900d00755101e20300040d2404092800f40f203412228000d0000310984c0662042d44140d40791403d6503031126600010f8640d00c4854050307032000100c0d15040d8214101880c509803100c5100d00300700c0f07482243c03511200b00034a5017100c0480d40300c1e8407080140008054811814400b022198180c0c0400001d59104020501d19010b07044c0141f200035012241c120030190640c194a41202184c994902050300e0345110014002c0145c2d2050034100200d804080c0c1204a40d049070803694441c2d003808460355408400343d014081051110788140000327000b4104174404d4071207152081d00c404150304494423400c40a07408941380e24a5501c1c0b641c41c10071195110030000480c1c0f0504803400200540841c000a20001640c0c0055800c803404210114903c07680002c03150a6440c00d800b1140032550341c200480a842001e8016400840c0c1400342c1001540100300e901100418201101e41c2192a50788941c89100c0c410320f45c0589070f200032031010381820f00c29000d0f070140ca5005580100f00e0036030f05051020040d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 483601987 1250 483600737 483600773
    0x17033303030d0b0a090f0b0405060d030c11060d0f0504030e0306061008060402040e070c051b060406211107020111072108070206030403080702010507021f0c0c050106090225 76
    0x80302e0b415002942c0c0d45803000d005e4014130310100416130300035140b0001021024400760180d842d04010585a14140d6511008254184e072401c4111303e260351180c1a0740f40b1031362007907084281400b920708403043d41d0060800700a02001c002a1900d400e003001003085003903000a5010360444010301c203e949a20307244e00c000c84400c5c1003446503516400d001c10000d118070790002d1001d50010088c080d41550019036154007502070802c42c0d80c44d100c0d03451200c0a2025100005a02000821080114034080d083d1050800c0001c203401e24a04d00031811081a1804807900030401040011f10004542e00003410031000ca01803401010740b00c0c01c160015914003a016a2040020b640400080030050020100c03082964007818035a181d0a091901809a1406980d00d00165003810000fa6080c1d100080d08001c2d40c14021040c88088040c00c81d000090031407640303400821412071400d00100e203090083c68024840d00b080140c0d0b0b81e07004603a10b000b02075119480d2410035680400c1102198021404540c171f411 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 483603237 1250 483601987 483601991
    0x103260a112a0f0d0c0605030105210a0605071806050c210412020a031a010f12020d26040815070815091e0f0415090b011217033303030d 60
    0x48400d0001e400b0004e0148028410350b820707000031441c9980400914122842510a00007011a4904485d02c414803003c8400c1c1035030150714410081001e0340c01540c0c0000090901041021003034100303481000d6660000fa0205030002110840c804003000b80c1f1044002110b15207940c0b034600300f80f0840910841c481c00340380d00311140e00b01040d9030710204030030002c5074408800c020820700781480fa0b00f204403d12520310500c8480d00005002001c2000281c6415401400ca0a405030b265949450410440c11511551031b00c3c2139450000d07000860040002d030a04900801c00d9900741110f40d0840304005282c4820844001c052003443c1c020205000c25110089813032100603039800800c100070802903c11140401401c50510000101d0343c0d070510b00403806031251442c900074a40c8400305442803403100034005a1340d800100151a2015a1401c140c2e1046404501110300000140768503002641c0c25050f5003c20002982050a40706491045180c00000d002c14101c0c8140040d840f4007038140100d000740c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 483604487 1250 483603237 483603259
    0x50a140d021312021005070807060f0f06030b0a15030201200c04060312020615010507020603040204020918010f0608010e160e10030c03050c03010e0103260a112a 71
    0xd55501991060038803041070aa0752070703895605042c011003075a0240d0050b0104c0c8050074440b446081102c0c08245c004d02170601e8001a0384c1d8a00051a1540c58040140c0d40e500030818a03034401c0c01500000c2d801100618000c1c00c101c03c140003214001c204084848015820800c0181d81018025980c09000e4608542001000182ea030030285500c03182c950240c170f0410080108800d0801e0000543c12540c03c447c036030b54600742a11300004c50060481e000c1082801a0401890b04a00842e44103101403c007504245105010651107420391a10702c0e0a4001007005010000715280e40100900c400d141c41041c0e54074058205c43c82c0003001d00b003d810a54410032040080740940c542da461010f01811300850b0980c412001070081c0006400c40d00000d082c44045a0000c8c0395034140c80c10780d0030b111018441c9074a160350f59804400001c1c8450002460350500b0b00c00d00650f00c0140c09410200d403145070b110003800c0112410f000c03e40800c1d000a80c41d0150814805106001061803d50700b5079402c6040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 483605737 1250 483604487 483604507
    0x121803090b0a0903210f09060203030604020903071208071202060708070e010c051203011701020711010f09030f06050604060e0420062b1b020307060506041b080405060601050a14 78
    0x283d1450341028220000f986403180c01e0882040b98010a6a03042d0740d0440d240d066003004440c0b004161250070010382c01440420341074601035000f0440001c00038101e0320b015a4a419201211000440a82d038400740860201c06108042c542440340c40d801d071001e000c56140c203880180120002a00c20420820002241c0d03a660f40a0340d000112036411000700c0c3c207a860b2801000405600074010541441058242c0c850301400c14026214616407103c05982d182c4c0290004480c82042000d0450801c404080c0c000045503440480d001130390b01813080400c0c2031400354240720030b5072403503441039480a000d40104004201d02840071209080905da059000c03020807800100c842c0240d245010408074140c103140030f900c41d40141c20412401c0c00600317001c400040340341c4560024400803050056002000349000069140d884281e1040c0018000031340c0d03061040c0040520740d5140d400c140417810f140180002e0060802200c0e0b4810700034078200e0714215461900418034070f91305949141c0764001185000c0c00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 483606987 1250 483605737 483605747
    0x71101060810110408061f0e0a0b0a0504060506040e0c040e1303020c0901050d0609020102070503241321051b010e061f060c060902030a0b0f060105071106071110121803090b0a 77
    0xc02d600d80803d00942049c8201714000d02d2500c000d10301c0791002400005040c10240103d4049403001031905060520b048003030034000c5d400070310340c038800c0d030b810000801c1b03588400407194082c12950f940c580e2100f03050f20307001c2c0c0381c050003504080c860001d8000404c402d030b940364001c40308075a000a003c00c08a0580c0300503450031909400865260250204250280c0040e480010303110044040401c1281c07660744542c51f605072400000380001c164500d280050102c502d2041c14022510301c0c065243c070141c102e00e4100c40c041c007880030320b980c1d456502d010401c5500b040019001440600c4181c0914080c4401d8242d0f096144501010b0040422480d800e000041d440f99440a8019080d5408040e039490001c90004003190300c09058511040800d8180d442081510541640210b081d07034060010030411029801c40c080072121401c00d0364405d92a41c41c2c00401884618807902c0340c501c8588298002810380304408820301c3d00c0e02102c051030011a50000380c9008503600640e034680c3e200704001d030480f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 483608237 1250 483606987 483606989
    0x509040608030d1e050906070804050f03070c08010c09080d180b0316090618030f1118070212090609091f060905090901180b071101060810110408061f 66
    0x1a80d0301020400160b03c60654010800100161114400614442513008100c0d201510300c2c004592144c00001d805501510205421a001e54111090101d030084210f01e19408498102c0311314849040804c00f0407024040c0c04504c00d014103040042c5070410320780350354030500661014104103a415807515905443c95141c40070780440d03c62035561b8502000490519030003011200c000070b0038150700145035071140940c100414038100e40f00b0320091454862140550b46031a081c0e4a409904210b0302081e56881c0d0304c10100c51802d042c60b800d03850304842c0a4144104881036100070401002400120f0395000111400c2d01001c440650440e1104241e04051500c4a980c90400b400010b10100341c039904050000c0440e08100c83d050b8040e941d5240a60903120700007100c0f25080c0c0511048030024901c0c00c0110f61100d200e20b020303a41d080c0c2c210b440500b5240b00d5030240b001500f04100f03035141c010f0103002e8141c000b41c0c1c00c43d041e4509460400c21541c0da41004003035a100320709003820454007043d4021200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 483609487 1250 483608237 483608249
    0x60f0a060b0f07030e0118090c0e1804061b2f03120a0c0903050a02040e0102091c12030e060f060301020f0a050a0305010503060c121905042102030f070305090406 71
    0x264642d54440e010b50402d40c49500241e0200c1d41c54044004550b20880410340070680540030305594a140c001542d0280a0b10740e07100d000e01c140030000e084203849108100405010783c10700b05a280c105800c001d07084680c4403000d00700c0c251902000031580f42d003101103000c004201101c0c8103041c07001c10109424101c13200d4448400d138000059904558401c0d072181c0b601480182c0c40c1089207025800c010740c0c59000e144801480c64000340950710151605a02c0250740252480c0007501e032070706c5040041c2045103907664100b0115400480b910600c040c25130713002d032414032034101000000c4414480700c1d07031118000d0010780001d880b100050480d44083d0182da003c208103c030300c1621401840005041d903040000c100e8006464000005501e03d800500c99020f40c5010910515104c1e03080030411030020003d0800c10700e5101200d100d0384140c580d12840d40305900a0f002e00d01c440c82940d080d00c1207010300c0b1007010304650007800b11006021041d02200e50295060030f0079540d03141c0d001d000c41d018001e154006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 483610737 1250 483609487 483609509
    0xb150a0813020316060201050a06050d141e0d02010e0d0e09070504090f0203071206032001030908030103050609120405090610030e01050a0b0a1233020406170117060f0a06 75
    0x41ca060a9200c0d04c18064820540080c0441d40c0d642a090f17041b140786102da281d0104d103440b09840400c0c200c021100003c0f10620035514900305088a400d40d100d01002070030000e42c810020101010750a21030400c400d40c031503000d403102d413111400050406001c1074480d4801c0e0100004a00300038040c41c11a401050321b81414402c0150084c0300d40029002252a0b50115501c2805074000602d07034490300090700e601170000c1c500c180e88000384241e140e01280505061554944d41e02011900d07007000703103000354462002011940741444129040141d40030001006c1441448144426551424038542c004408c4c2d94600100c2c0030745070201d0103002c1c1a43d991b401b95190a051022a00168100404043e002c2d514580c0c1c880d902c4400400011a445014001c5135255203c3c1090541c0c80458036603003480c000410b10b00d00103100b02201240e105a0041e800b04520700d54880100c4045409240141f440e801c0321034002d2841c89034503498540c0200081c412808020010b48604465400b80c0081c192120314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 483611987 1250 483610737 483610753
    0x3070b040303150e100b090103020403081201030309170a08160b040f020109050d050309060a0519050901140903210d0e1f020310090f0b040c0804060b150a08130203 72
    0x350040400d030343e440024003409140803400da000203907418010807907180d0301c00761103181040301c5000c0c4d00044041810140c08000000118149401405414103104021807195141d0328001d4080d1800750b005054611071024002e0000030003254407118035421004003566650755400100250309811002004110140f00740028807a40c080e07141ca0b0f0074800e0f01c0b40b9441c5501d8108200e5042880c0740c000300154030400403000706003002801342c402440d203800c0c032034101192241c94400801d0003101001c00150080380f100700c50340e40030132352507034086521403410303d011101004241c8590384d4004090900d11004090b0f491085240c0c100c54400070307000c100f04003081c23440d81141c0e200c14215080030500380c2c40c05c540040c400d00300e2007142e00504c1b40c08400b402492401144c003000e4220140d400c500203546080420160316513004944103042d06070754003200340c0341130b240081c00c490212201d41d018644a40d010f140d155150b07411200000301d1404c1c07908055491141940701d1110310180203416000c2c0e405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 483613237 1250 483611987 483611993
    0x1030501051512101a060a050a0e040209150a0908030307020d030506041406120304030803010906031b0f17030408100227030a021509030d200c180903070b04 69
    0x711660180d00581071920031a4002c2c81048001c0c00d1809420b01e9542102100b4483d020701d691142c1c448819552000003807403856070025105030884803524011443c00683c6603c1c080c2e01002c490310012013114218244880300e008242100126001c0780c60303140300060200030700c60003400128002c002d001c08580d0380b803a085400945421401720791801003030600010030b01a10b0300e401080391214240e03100b0100790355184104549258102c8078009140010480400411008801103010300540c0c24049545071451500d4402c6814051104140c40c5080c042846030010381701d140800c6600340c11104c801e48840000035802c0d4446e0747c0c8403402601c01c22003400d5818441d90094000d01c82102c05800d59017a40400d9210b0041031b1254007035058101c1e00300e0300d0040c85c1c03102f030b01d1242008880c0b00d5803d180d060310100380303401e04600540c0c0c04039100d8000304d151000b040d0b40070600c6030026405480b10310361000c04980c541e4440c1d420940f84986000c00180101000c109175090190460000c594505080c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 483614487 1250 483613237 483613241
    0x70e250302250c090b06030906060409140a0302150a021c150906080c090c040b0909071119050f0c06071203090b0106030506100309030e0f03011b02071d040f0f061401030501 76
    0x441521003883c1070295000175440c014003940c0c4106d420b0009090a0b43d1254200300013044400790455074200e80d0145949020b408100c9481c0040c4280c00900e01c020b8041121403d54400900c0e04d240703d4010490040c242040d00c42034032003030310602400308003103400300040c44054080c2d8020440d81d51424400280310000029542c10b9040180c40305406c07074035965061000f0b480b440c0110804060100051002414100f00f047d911045500d1b01600d00c0000807541400c04c5010015045940311034400072091007400e2003180b0340c4000140062180100940103e95240980754010345000b00c1055840c0b181e40c060b0300108200d66201140c01c25568403401d003d0001d181c00d8030041d00403440b005c8500b40d140c0c00fa201d41a0099090349604800e0312481c0300300702c400e41920b54000c0c0c26540322441040c030280c80c0d950311120180180c014128403410480c1c494241440c040340351032002090f000340b03c08140010060300010360042c048440c0800740d820a0401b91250200c03d0383c20081e0080004203000c419 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 483615737 1250 483614487 483614489
    0x30c0a081c15030305131205031c0510030807050f070f0f06180b0306040f02040b1809010f0e07050c10090201030513031b170705070e250302250c 64
    0x84041d022918000d07451108071205121a03210442e01070400303001007070041c006841754940001d8820356658a8108840b03400240d101d0444031648042910102002c3d00404280c203500031101c200958640f120640d0641603003071001520760480054034a050040c00d12032070103001d41c0785084414903655030002401d14480b900c90318028601e420404180d09c1d2081d20341403044154804403442c00c50130442080343e01c0e403015242c5540240c1d0b81e90345031001c28160002e0310060200c20b08a60722164410800c54491420b01d044604c02c02c0420018080d18540101c1201520b56856060f112a6180302040d86c0c1742c8030b0001d140d001c0340300740b40a152124485420181070a8800c1c0d0b0301b40115183c40c030344084010140000100401d160038030001814445282e81710301c0c1401440b09030300e14002c2400041040d4449041581c42c0c0c0c011050a00801640c0012607820408105480030b501080340004285060288160001c05070001206d030340440000c0309038591100c3d104072800c4a10202d14040c000c1400d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 483616987 1250 483615737 483615757
    0x30d110709050103050c130f0509031b060609041b03170a09082b02030d051302090609010b0a030c0c02060d0504110a0f0302040b0d080408030d140c090d020102030c0a08 74
    0x2551601041c0416076000d600e0403668008010142c1c0302c4072000308184000201c82c40f0038600da9a401c4503110001340e0207681c1c0211816000380d680e480094944000080321100d125140c0e030711103000c1c081c143d12a45a02c507440b44c1c02004404c42100c0c0c0300d003006000356207640050640710501d90340c4640c0705402401401c108005446608c009070340c8604507500c5980101c9120b88018001c0e1081032404401c92440100003410710586e480c1007081961401241c0b01940c0c01c01000c90000c240c0e10860a00000303da81050040303840f141c2d15890001240038502c10600c01404158407102c500b444d05001d501040c903a180e0050071152501c4115005200906048030b0554884000c0f04c0e1510b41e82c244000c4510030703140d0361020a01c40b20f0641d000d00016101056043d60812261412100440d4110b000342000d403502401441c0e07a66003540004080d910740c68880e00f1803040303080501490000c0701d01141c1e03411a060355100c0c001d5000d800145e0a501070000320f491640506030700c41c410002108024640841 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 483618237 1250 483616987 483616993
    0xf04030501050a151401080a0f2901110303150a0f180c0305100605031e18070506090a091503050f161421120708030f0703050f07030e0c030d11 63
    0xc0720010000b0305808501c10310440a0500c8100d1740d140d48111a6140c0c410b440e040042840340c14100d0010896030840007481600e160112812401105a20740c182d016001f4a0101403404019014544134480901407240b418201103692503039417620096013004121070100015a16034640b49011000128000404050710f410b07080c40741c0e076002e0310403940121513411020501c2400c0030b40540c1e107540041d20b103071600400041d0300f02807005031461480c130652080b220a401300310201c1500d03252022a41280b0310030002400b9801507500c82101d2501156080c40010a00002081041505c619150009171690003542c400b038041c4540011403a4044146000704905548d4804034000700c41e401a41e16548121000328411a40c07074915120b103800c4020304151211445c2c05410380c1c0035907101d080110b600d15404002c100719041100042c9034000080c4c00c0030300040c40c1204d190a01081700502c40c1090540d14501c1c0030742c1c241c04202180c401400034044400c100036051000d003a003d9042c003d110144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 483619487 1250 483618237 483618251
    0x120703020619080f0c0a1b050105040c081e100f0213090b120c031005090708032703010504020a2702040b0904110f0910050c0105100504050105010203090312030c0f04030501050a 78
    0x84c0c13107620102c0c03142c6440c017034040c01c0c00c040740c90448401c01c0184110402007404006040815420711480e8080c80c420b038a00303015a460a0015803c0c0b55070100e04841400103c1d49092818501040840c0c074002c000d500051840b050a5156000340100c400c030702e45001c0c1c2042d010490014903800740106030800c0f0360a02144011400c1e16650740216404150183c1002908807180780707060300100d4101c500b04042d28210303030310741000c140356802904032404550148015902810401007042103125400d5000340710702d107840d4001c9400d604c0b0713510800070104810394440011100d0520400040380b82002c0556035940c0e110840c0d94690881013029106070314003803c007150034030180100c03901a051207088908103c40c642c2002104411240a01c0c280b11f420400d082e441d4200b846000d100c0c00c02d4090080700c0d00d0500c81840b08981050300174606542c0204050b2115541c0080c02c203610f0140801816075964406548041034020440650348607100414080f0400c0010f41100e4800c03c40c0c20020404a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 483620737 1250 483619487 483619501
    0x1806070c03301d191e05010209010305070903110d031101020a030e0105010b0301050a03240e010f0e03040501140310080a030503160c08030604091406150f04020408070512070302061908 81
    0x3c1c3c030315603894899102c0a20407200350100d402c0e0180701d41c041c05150151880409803913107102d01c0720310101c5560b5030015642d0101d42c0c0600c0749507000209482d00342c00311810340e651282184404c0c0725003403180d240070401c9030404d8441c412003001d2202180095445e6241904040c01605241070748514075401c04002241000342842564103d8030001c200250541c80c580f034107032000851402d4540c031508169403c40d5032102c1030069002842180c400080c6c1e41c07001c070b4489811641e003840040902c2d00200420000d076030348641c5000813408e0325005140c1d0f0340c0b1041041008540b0b01d03800403ca600030140d8810505403c003025503c1344d400300100c80300303103086803d0407600f12214100003421080c0a00104a85007440d500c1125010710035113881c111415804205441c1060403610002c50111800c552546801c0100f0344c20014030040c0c40a6040c14100440c0c07903111030f9907000e03080c0181060f01140b40081410001c002c000c54010303000d25550081c1030f40507400c54012018100125071504d01062903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 483621987 1250 483620737 483620771
    0xb0412020f3f0c010c05030c150a050a1103160e15040602060f04080412021c0507050f03033406050717010b0c1011040b0d050f1806070c0330 62
    0x41c03800c00b00a4100402500010348a07507050560944d640c3c401070080c1040800c080103840c50032801803880381030361705e004d000d244140c400080812480500345000b504800510405a940200c0d00e0760040d0b0720342030210000c80e04002c00c040b030f0b107034400103944c0e0003484010180c005205407050f80c3e081d15416540c80d40c00111b004c0060f0380040058002304000c104081c07205070310301c11a902c002c00c8107242400d501c44d441c1c1210b51100090f64030b50806042003240d4074140c4c25400240e642580a1818801d0041c8070b0f209802d00a4411200c036440c41201052440c002c2d540d601c65591f00c504100039508003220018540e0808004c1ca2f49981510320020500d140040d09450a546001c00101180800c0c170784810081c00117551640b01c43c0030240008aa080e8103d0058182e44030043c10000d402d1030702c00403c6000d90387c0a010550100d401070000001030002140c20390348011941000b1180448600d0101c80c004001c41a4400410005400d020718552140b5010b01d00b03118980d080c08080c58440030794078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 483623237 1250 483621987 483622099
    0xf03031b140d0609020c0706080a0c12050603070308071203050c0c1b06040b0c0309030c040605030a081806030f090709051501030f0207050d051c060b0412020f 70
    0x4600400c0e0240041c00340301004211603a034040303011502075618040102070380c004548040c404d411020062080e1355000617081c2c3c1c4040c9560007800a00e0001002801040002294131050341d100d00003c0c90a89041058000039503200050550700e041505240e51040b98003070713408001a043c080495218580e400a9070140140003002c3c04c086060354005145441410900b10780007031003480700054000d01c3c0005018811102400b41d680c0c4c60041d0105810a210b03841428441ca15109040c0290340300060084856a445140c1e2603032003400c2e02d80c12000c05a603288455000200004201d4607801403070417940144410000c0700d151680b1100c08500380d4104850511880c00050386840440d03100e40c100c1c2040040ca2100145004a5a11141d04002c91002c403400801e80c0003481440b1007180300c261055008030305404000290a049403036602d44181e00c42d00700c803007080354400425540c07400180c01c1021402030580240355180e40c0c07417070340c8185e5102000400d080b040c3c0359a00000130800c2d401ca = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 483624487 1250 483623237 483623291
    0x804050c18060105090a08120d1d0304060503070201110424020a0b06012003040e1602070806010b0d0b18060102010b18010e100b030c030a0606030e0d050c120301030f0303 75
    0x141ca10b0340c41c440111059041346400302c0d488818802c00054040701404141e50444100c22255554000001d020302614403013042000c054050612061a0420110581c1c094a4081c5092a0760b9220214100d000d44100c1d98160380040d000180000d502114023785038100400c03035503110170404100810b030303141d40041c4405040d4100140c00240c0940c03041000b200d4640460a81c10005014401201e00d5504a5005408203c0080007170140c80455941501801442c6100509030b0600340640303592205018441c10b40d00c1c80c000328103a04003181640003a0340c140005000554070000710282d020706010141c9407503015510780700b0740701c01ea81480c2018420507000151280e0b01a4070f02240b400d00341d00300401c004d050a0b010035003c1149102840107501030180707004855141d04044104108903616544604241031600e010740c481d61601085442042415040994503003904440c0700d41414580d810390240168000008400c0000160305980d045009580c104032449500941c00d00c04890341401e6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 483625737 1250 483624487 483624529
    0xa0902030411060c01140906100f0f030b22060902040b04020405090f0c09060c01051009060e07080c0c1501031a04080d09020d0c120627060f1401060804050c 69
    0x140c591030411400408207000540000940c0d484040986d0810410540348207405401c503400340022401000e80071030141c0f40120720341106900d40401c040b1003443c01d03c070082069401d03d0010340c44403038000e0702c004401d0a000e000511140b070b901c0c00c680103054444040340720b1440c00302100e40b5410035109a8040d82c81c0030717040c00c500d81ca50350340f000540310b402001207154403070411401c100c60321010060041c0c404481e001051034104000b28406060f402d42010101131724001c8100300e0a40002d42c2c0c0c40c0c0001b241e0038220300303a44680900352540e224010466451740708040e0030700001ca529903803a50480f405820320303240c44c0092032042e00a4103401c2c0c41c003426051050004440004032540000303482480104141042c40b1560790b429600e1100f0b510907401225041000b00034040b0502a148240f0390358403003540d209100301041d942c4504900750280c5200d590f5004140c1008159000c14080780c4001146002036070755201c0105510300803181103c0e10701441030000c06a08106020005040712104a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 483626987 1250 483625737 483625763
    0x10614010e15040323010203040b041209030c060909060f030308280f020d0b031c050d0f15151107060804240e0c0f06030601080702070905070e0a09020304 68
    0x44541e90041026503500c0b009818104800c03100000c010401903201c0e00d0050310400c03c041484054000c04a48000964010030400000985101c58150f03c50341c44101022011000c080858990a454100500c031165203070000c10f04980280d428021039080d04418006e0540766614002d00719283e1000501144030301c1c0119904010703c0362982020030202e122004450051079400040d6111192080581c5a00241a0303448110900a4000d11401600107184202c0642041d9040e440444d0407901000000304903078004c00c03195004050343c0a28001c040c0042007545071003040704203e82c414003002c2001d01c1c104840721030040075503d8590143c0c0001d07000c200d01d004020f0f07440000c005c0007146c040d09008130140d00800135122070f12082003009400280e840200d00e96515190110101d6446591112980308450782c4c0e030000c480e807020b0280380030300351500c3d08442649016400c0d00b20000e500d040004200c0160fa010340d50b224010411100c41c0da04e82c0d80c41c900703503049110540d0043c00f076184040e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 483628237 1250 483626987 483626989
    0x15020d2919030803060105070f0605191401090f1503050106080c0108100603110f07060b130b03120901090e0c090a0e0601050315120a1b0b0f25170a02060108010614 72
    0xc090b40c0d105e04181840383c41c10351a90303600b5030402400181154010f0359001480664084c4450910300c2c09040d940400220400c0c610820541405104241206403144035440101142e9040b6000d40e0081132b28032401c0c42d80301d18007580603140d076000c0c80c1c00d40e100b001003501c015882014001d01402404100541c404e091040c200c0180134403852424450000300034028110301c2c0c8400078070040d4041d41c0300041c2c0050700420001804044444a000e190078039256401035980828002e40c0318402c00c48079982d44000d4001a100c100c0150700c0100c101552108210303d0703030b560f40f0050454420484140115503140c85158a5000c010b80750103001450a0000038081c15034a46689181a001800c080c9085618906d071880c2101c41642104c03c00003100342000c0c2c401c40c007443c00000d03201c0c070b075003250511402d044002a9405909440074089500c0002c40c0b02c14000c0404100700b054011150f115108045215224654010300c4240c0040c4200300001480c0700d010320071941624440740303901c20b489801d14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 483629487 1250 483628237 483628253
    0x30314071b320d1e180506071a0105030304050112090204110406051905041202010f14030106180b030f1f0b0d02180114031f1806290715020d291903 65
    0x21101002145c1080f00421161344500c050550a803041d00c130003080d03107280d00480c0b980550683c41035000354403c1c0310601c4a44c0c7c1240d144443c2040d02c68000810724003e00018000d0700310448100000c07180054085901940000141100010700c030140548401001080310188901d00c640c11400e030242c020a00158840d040180e5400140d20b0b043d0003017035105411107551342c030030f03840f4030042160340b10310000252803998018014104030140906510340349219034081030008140e000344403841c0d80c074014400c004468036405003200c07840c026212918101d000c0001d501003000780883d20010466101d131076102c1c5510701040c0300f40c0c20107a411525400401070348d8045d01154010031104114000c64680d603c80164000120f0043c1e0106205113400085403050080c54241440005038220f00b080c030649140c12110003540c042e1140b04480400100300c0001e004020742090442d082c18107144c41c681c1c01545084900e418240860740028480f0f042060521844181000b0302e010b00e1000c2010980340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 483630737 1250 483629487 483629507
    0x1d010507020a0608400807060c270e0a0902130e0c040b030309220204170d0305070206221113140907030b1807030b090a030314071b320d1e 61
    0x10500c10b4200070f922341c1e031030041c0c0d00301c0c0080b0b8000440d0410703e403210203a03c020100b410712440f41c0c503080c01420b0080c040310500c001841540030548500314001151100c207000300103009240c80c10020203444400ca251109004500c9500c214203100c40000e071845c001c0101c4400d00f900800c400d42104d41c22645419421030000729580c401e82c280400a40305104500b004203030040e032000390514030200100501119009040b00b401c661004d42040008113111ba400e180080000020750fa481c481441c1001c0d4110340032030243c3e008100010340b0340518143da00301010f60000200508129541c4401c51580c40641e44009040e10301c210f008901c5da00b40441c103228007024000306403801340b912502d50841c3c1c6001600d8140c5d281d480f8007450014598980301e559680e18017001016101d0621020043ca14900303400e5003900201d03003040c5902017000305101031240b0010034081c405403044c80029000448507403058211580030f00140c040380d4610482030090521031343e03030000c07000e40d46d040001c845400903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 483631987 1250 483630737 483630743
    0x10e091308041809050d0e0901180603080a0302070309050f03031c0e0307050a0c0e150402210921090d0807110d0809031b011d010507020a060840 64
    0x10401c004203200340d800c482a01d0800403100301282a41451a106140c5074000000740100081010307c42e000780d882c200c1603811a20805c010301b205043c60240b000052043e50701c01072030fa020000341c20001d289c050300601035070b90003920791000312507880342848000301c01d0f00764040d0702da0410003010380d10740d0b1074808c0203c64101c065400140c0c201c018a4151a4ae404442d06851503444602c1074010000d4498000c8003626004a81d516075081c00302c2003400790100780118910541e004501d84107409200c5880043d404490740c2c048819007020b1304510703101e00404400e044481c2800a44240f01c2d44c440d0f0850780c041c3e1000d041d0300c29040c50b40d161180140c11000c42114441c40721100300c84039035904040c0840c16401100c807559111000c03420103103454261340380e1102142480d450b800b016a0003004084801c0740c56410840301e079411000498851041c544001d5204101440c0450565070003021f1034414400300120127032900b400341c80c00a0300c01a805400005030464104030070400551031040c5001b030301c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 483633093 1106 483631987 483632003
    0x2121e13110904060b0a0303050405040c0201061202060901110106091a090f0604020901031d0f0105060a0f180b1e0306060d0309090c171602010b010e0913 68
    0x604407808038030481e0010006030600c9010341082072003030b9009000e240125124507028049810034000c5074080c03407500c0d4180b00014014441d10080da8800a03540314281072030f0342006481d92081c104075040258143c85503400708024020040580002c0d54049818545040c4400d81c0401032140248203081c1711003032000c5480c582c66034a1b040102500d001d40d4030441c000043c2c010f45071040c44110000c16021078808080000b084c5c2c400c001842c00c000744210384a940800c0a883c550340035804c1c141050600400c10140117180304807040c0400000031a00e80383d26000500c4400f1210441302d06a0685554990546014020780e903114108647c02452880b01c0d84005060003024001d07e20712a80d510b8225120502900c8000c40c0300d00300441028907460310f544080002891082035102544c00d1010b50f1155601444101078031040c0548030740e54990705c400f8441e07030014002c90280d40707140c = true := by decide +kernel

theorem cover : BRFrame.Cov 483453237 483633093 := by
  have h0 := BRFrame.cov_init 483453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 483453237 ≤ n) (h2 : n < 483633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
