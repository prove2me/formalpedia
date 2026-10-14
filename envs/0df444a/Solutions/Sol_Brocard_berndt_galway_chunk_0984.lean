-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0984
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:39:03.070421+00:00
-- url     : https://prove2.me/submissions/d1661b90-ecf0-4f10-b187-c0f69aeaab46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 176798561 ≤ n < 176978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 176799811 1250 176798561 176798579
    0xb03040b0f13030f030209010c140105010f05030109020f1002032208070504180f480305030708031009020708071704061407020402041d0403120b010807030203041103030301090b010207 81
    0x49080c0100400c001c480c11303443d0036001c2c0e000b80c506094141800b510607034241c3c8880c0c0c014000800d0107030702c0ba5921b4006006214030030441c1000b600056000b04072201c240c0d408201000c05d6181e08900c940c40100d5a00a941c0c4200221403031200c000ca001c0092502440c510456444240942002030048030404100d50074035200d580d400c8001c0f03556406d0803000a86401000c6e001141054400c0c00200308440d0b590007003081001d000781d81801c6610442c0314845865010701d21702610b2010050b4003280100301040000081d2900550048080c40e076a4441495458aa0b945580a052a18000325900c0e041c01200c1000d4483d25029020000f40c0415407940d0b2181d034401c1c1d028200c04202d049540e48201c140d19005001140d00c09800103191a4849003c41050703a204106c4402d0440340008006c01c1540c4144000c0c58030408813002d00c0889a00400a4104140100351208250b070100014081c4402d5440c02c81014002a0580790b4030358688240740c02034040c5c02d4640e809031107041000141c0e804 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 176801061 1250 176799811 176799841
    0xd0b1c030206061c151b09031b030b04080a02071d0405010b01031407050c0a050303041407090204150c0302010f05070203090114030c03040609080c0114071103121b040b03040b0f 78
    0xc1091611312000113255602c2d609941d11a0080b001550780e0389600004180304504403100150b9501e5400c181451860711030003400070380f10b2140aa1650900400c001105503000b540c0280d80030582e6520358010440c01c0f0310b03244440c3d00c04040b042030038035191102d50f144d8a00a004034010300090003404082c400650a40307083d4120510703100c0001c00090079041c480c0015040c1641c2507016124601526100c5510350741050300e0960300d00f41064240d16110390108407110060092040940c00e0518101c03517408020ba600000f10207010702c41d6003000401d4801e61040400c0c0351a0b0a0401c01c0d400d008000239030b80c2d0000c0c0b00741070100752510341c08418454504280c1340306503000e080413442c642d1199183c401800020908498220301800141140c0d0000e0007030002d4a04018061203462402600040c000300001c6601c4003190000c00c0040421140707881c1181d4090425050380c02154010421110343e4407550b130250760016804000c5c0801c10645118441c0030b400240450185a1615a95488110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 176802311 1250 176801061 176801089
    0x10209030a02150729060108041505040305040b03040521090a090c030b0604181a0120031b010501050301060603060806010311031608061603060605070303020d0b1c03020606 76
    0xa48080d08072801071a0000700d5210b040d081080d464189111690b88444260a01c0e001c100c40c0301502c110500d80b0320319508072607803041007440c000845062944842c040411409209403416403a4000102414050821038009045104110355203145ca42401074031601c68801b05d40d41b0301d0200c02c480112a400c01e0580d8110103000300a40c4042e0b1800c91102c00505158a4600900da01c039010800319079903100182008100a41c00b280f0b00e0ba05072401d000c00c07512100340c00c0c000300104210158140e41d0040520b102c11220411083d120b01100201c180b55000300c1c09030b6060509054001e40e600312040d00303d02c1c100c3d0350590082c0001030315003006500f1381d64640034581c11940f0403001000801c08400d840c15030f003000541070710000d08051001d40710404480e0007124869100b00c01303000c80c410020b40480d05998a6190420940c0d04048005009110301c0c0e401a04168000c96074511111543d80411424880204640703140c2265070f008400f80c9e00c1c407210079805401441f00046d03880c140540380c2c010030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 176803561 1250 176802311 176802313
    0x30411060901050d0f0605060403050f01060501030207110904060e01020c1e0a080a140705012c071401030c050c15040512030f07050f070b04081804021c18050d09060801050301020903 80
    0xc09413428540c4003d12041303103100f400589800e40003505884840041c4060b500a00141000c100c0d0761b010702d130a4403d1980310504040c410007001001c140c4c200d18010062104441192043c0c803541880300107418668a07000725544000303002d10320301c0030000340802c00c0c0c07444072090708500144000302c0340c9542a100c4007802c404c404000404400340705010030100350b0034026000d0304141080e1944d90856500d51001f50303000c82d0111101e42d682039141361540d101c0d60508010702499041038101998860803948250506842d08900b12440d8028800d4410091100c01240d00c1c070b54401000c0e0808a60982e400c1d1241c1c040d0403840301291102d0003c50b44110705030b400c6451241c44008003200c00d40d20030003004065060500c8441d00160039610418000c3c0e0050325240c1d00c1e28480804280786ca102d669105101d40d02c1045140c82e90b204034030842141803551031000944200d06240e200d50442301200c024454014070600f0701001743c005181070107a85203030303484c04803c0e0b0301c0720185802c038498024132a600d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 176804811 1250 176803561 176803567
    0xf0507030b18131e0606170c010c060b01090b0304080403030810120b041403030907080714030712050109020a060f0201050a050618151c1b0509160915030203041106090105 75
    0x3d860038a4200e00d0b01c3d14032518a0755121480400c1d410554040407004403401e58440c4002c101c16400660b40710090810240542510848a000a4000403404900422980c3c07100540036040c1e01414800008020282d9056543e107010b01e0a0403c0b680203006c1180480c1055010840701110560401c0941740002d01028044003a40c590347c64a0a0081c005c0f20142c0b098024404041c13028009140104001c0b4002c00c030840c1401007071030070310f102070700034248802d00780032200d003940c1e00000c800c012075a4190b8201e490343c6880c18494090020540081e4000c02034080c0020800e40c4a1049524980d042c2c0c000c1000c0c0d01c841450005440003501d105a020404c031500409111682e00450b800100d500107004000043d0404101c0e0204160b080b0700103011800180018001c62441e2480080694001d0242950401d0001500d144c0b0180c900d80b503643c0005800720b8450302580f0044080c0400300100b10072020b0041c0000c001c3d6204441c100d402c1c1c841c0d42a00711850824000740c5106410584070241 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 176806061 1250 176804811 176804821
    0x60801091b270207290109020316030506040f0c050a12061d1023010230341a1501030e070f030507150206070e010804150f0507030b18 59
    0x8201c40034400c2c50301c0c4075400c1054034005042c90303001e01d4803100c0c1044d00381490070f024517030340744078040503484103103001d0040041001d03417580e901c20182200f14600b00000c094443d000402d005082501c000380102d0701c0c0003038010380c00b0303007002c0902054983c1d5500d1000d020020711005042d03a42a20a940492076514550308408615807902d99210400716a9100b42d1541d92041c1540d0080f0718002c104240c0500008090039641407100c2c2d588901c003e507000481903814150380031114903003241c2c4c1514020218900c042d50150086401502c61680580c180e00a00c101a0144031350750741408407425800d00d080c3d90352200800d100a803090030340402d0344094040420064029140442c8511040e004278103020508002904d454000b450213100181456400d00256404e22022000ba60066500c40c0e4100240c040c0c0c008005140c041d000e290520442c0c0351031508504401c90f002410035024203240c120f00c008a841e074402d900c603412940d014080e42c61994280a001c44802400364041502a00020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 176807311 1250 176806061 176806109
    0x70902130b0a0e03010504030509031605030c010c03120e28031403060303040819020f0a0e060d170d0e06011a04090e030412030908070e010b030403030b011101060801091b 75
    0x460b09840c5801d240301e004002400082c215a021101200424404107000132241020440692107a0020405222050400001035a07030340925140e0f42c1040181ca42c1401094403034404544003c595080500404003060407417030b140c1c1c00c02c0802009400200901603035107204d254414051030341503194500f417250548900041036200510b030b241c0602c801c2000150a2008000c41000c1405036070303c41001d011544100300c2c400820491442c481e4101d400d00f800803140501060307403c540100d5071484119581c1c034100d4103202005070040d580c00c43c0420204044038013034101c0001412400c2c00d51380d071a030305c402c20071045801d0314549403260725043c40180314905403a03001c404885400c000300c0307040580e10b1405a5088891000c11800104658401c205500c02085101c0103040401d00880c61581055514906808020005400c2583f2550300b5480ca90045003560319609450000348005a11400030383d0285c24880c0341245d022807288000212030600c2130800f010f480312070800340f0351040c2a81000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 176808561 1250 176807311 176807317
    0x507080718051203210c0f070c0e010e0a1b02030403140f1608070f05100c060b090c0c120403020102150907181409060f18100c03020c070902130b 64
    0x348071141a201400700d01c0b0b540310106a000c9030b00c2034005694400a925040c540b1245182c80811a25000802e0000c0c910301c01055400d0760306440b0160341c9510310360401d80c1403030246600009058491070300105051607614030704c612960315400305205031003000c40110420b490481c00382d401030f0802d0205100080881c0305c06140c4a101c041100c0034000b0020b03c0c20b00b0031a007000312803140226600104081841484180000d106030450f1019091401e000301d009900b090740c42c0d404010030103980504000e00b560042045080192010708146401c4041c8200d42c3c4c000059040c1074802c0608c0c2d47c0402041c8c0c1d0480b01078036810f902800820100c0c102824030141d010f0b00400c21801172500c0800c48411007a00d2041c1c00254940c00b044c0034085680a1036100c60280c04e001103908040100f1109a280d5000f56030011403e071403107288000c1c4a03101500b8583c5549007a5030382c9007041d80001d03890740d042d0003900c1c11007045010707102083e582c5c00c5918120301c1200310045031681505802c000700c007031100103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 176809811 1250 176808561 176808587
    0x1060c02030a081824030f06041503050606030106170d0f0908010203100e010510090b0c03120901060e0606070510110903030a0f091a030112050307020a230405070807 73
    0x450b984588190b90303d030a690416440b80d0b4451601021501c42443c050b405059000520021000e48085800b0010102d2000404042440c440800071558076102d5610019040782d14a444032005900e0307140503510740d0000d84210740b1a609040010a41d80341703070003803440315843c510300808113100e43c200309960000c40b091240040c06440b2a001543c41c00a00043d13204000240701c40b0445400c05014195100c0188c004500604280c050b459003681c10000c95025142a1844903844160000c0c0c00ca1841c031401c140e4074030b00240c5205000201d501500207000342c03511040c03503a00703540d104004d01c040c030f00135411b0151056104180e500481001940034010301d03910004200c0c43c112915000ca85503a0000c1004000038080300d82d02d0850b1540a00d8441c041c1c03009900c243c220b11300c2e0308210000350106004400c0040d002042c40b00810000300b048404c51030740605400583c594442c03030254100c0d114400902c1d101d020151499403441e06100c0c40d03205030940c1e15511065280c89804940380c841910fa = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 176811061 1250 176809811 176809813
    0x1030b060a0e01080c1009050603060d060b0d0b040203010c020a02150a0c02150a0207060e01020309041e05010f06080a051324050c1b120403030807050f1b0c010c02030601060c0203 79
    0xe4042800300c10000043d000e041608018401052000248a00c0d40004100042040b03010701d400e0040c0d40d20102100d0f0007034400c0741c0c10302941c6401c1c10160020021402140d03170008c8403411900400c012000600c1c403c40c001c6008102c00c100000d01079880e1140c950009602c18925440081e0043c8070304080c11500c641480c054030f4014465000c039141280702010450042d4011468003429541080b0410240c85a864950030040050002030b54900a1026003446192079080e40b449449030405502c1c0c022103001c0c030600c21035a403003000703d40d202c0240c0980800240c00c50005440e90aa034007480d03004001090400c0201080e0b074540300010310302a0000c00b0f8440d03403150380c1c0c0c052501c0e5001c0c1c54000c9401a581550710317800503001450103100c41014040b960080035542c256440c0200c00d41d011642c00d400c2041907599150000ca0303081c810755070400000c800202e20f210740001d00301e14442031811070008881041c503880005640381001200004d41c51750203500144825442841001183c80c4050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 176812311 1250 176811061 176811079
    0x4030201230a0c020301050604060308030a091412091504030f02090406021207050d0605030c100f12020a020a02090a09050601060e04110c0c0306010e091903050408010e010b09010801060e01030b06 86
    0x4181d65648402c0c15500003c003a800c201055160a100e1650014000ca504000440ca07654440b00039006c01042e1075843e0790f94812070024001d1501d843c0444c401c1580c192403c0e614448178141c09a0005c8030818010308044030303845c1c00704a10100301c4e800c1c5c0b60055044029905550b00f000700e4024020811103495400340119000070010f4505d032030140c002c2e84c070350540340c202d40311051040350015880180729a00c80d0320a0500b54461110304c00c101440d91414403059000100c0070303506031981245040b985440000c0490141d9404514811158030881d20400c0c1d544690b003100c400d440d40a0030250441c0c1100c8010400540902003007412485c0282021441462404101009d03400112180c0e0a54200780206081c03894140310240c00342201641c499903505260480d03a03600c061260140300021011155081414018070a8038010300070480240702e82419421894060201030801502400306140003082400040c00342d601a1a4200fa091029a18580368034075500740180a0580100c414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 176813561 1250 176812311 176812367
    0x61b0c060c1209030c1101050f1204061e020403050d0f020d120b1e09090d081501020c100f090512100203041e03020703050f0303010e0106052b0609140c04030201 71
    0x1030b0103448070f194001d444800050419040c602090b2162100d070b1410000d080110501e8803550105558078884583c5451070545c0d11850703e40014480310b016042c4c0e41c810741d0110104100240c0041080e00e202d0b000740e032205907803050150754010000f007051016070004004040030610030000d141842c0b20b1103c01162540d02240030904444500c616a2000c00700246149074604050740c10a030024042402050314540c1050000c102c40400380989845014108000e002c581c0700f00303c00048814001c0a280e21032407080000340075010544508000301d0283c007c00942490a03e0745c110358444103070007034035502000e02c403800006d5100400407120a2596003075038542920040400080170720a40051506509504045103003840c0e40e40e81e0303040780d442040180401344982c40b4242c1112580c0c20410f80703950315090761100c01e012102c4040d143e0354170301c500441c58844907080082210344a02c0c0410034205016225000303030001b01c030340d00440281000308100652080000780090212204490880707284 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 176814811 1250 176813561 176813597
    0x90c180708071e030c1416140715050a021509030d0b0a0f08010c02100603020a05100c0203010c0f09050105120c03100e040813090b0d020111030421061b0c060c 70
    0xd0181c3c3d510019079103908013844190410f00c01110b56440445260070401c410325003014000e0309000051400b8515a2100c134080000c10544014000c6490f1904001040b01c8000b005030301308002e4100140314071441261070b407010300d1000e4081d6040c3c0025518106030000410007030011040000c3d000030103c000001c044103410b0400018013441800400c40c044028002842d2a51038044100c40074a407000810060399031460041c11103100380d64031b01110f04040e00a80300d45d401420041d426501300341d00002e1542c1c0c000400050f0400c562a00d1f2001502c550044880b0b001c0d00c013010802503c3c0c0d030080745901d8208406154048205500c001d091510350002d215801c0f01500e00711031003000131131144001d0fa0007110748000390442c0741081025141c2c0e400000d00c0740741c20304001f0f4184465092070a00841d81401254054600400301c02041038241c2910440c01160f4041911102d140107d1201c103100715a208024808450355596041201503c4079001090703180e9400701131010003c0c0140d1364543d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 176816061 1250 176814811 176814857
    0xb13020d1202190804080c030d0f03050406090206190906020a05060a0e03070c03080301050102012306220606020705090a090201091413050c030712051b0d0212040b090c18070807 78
    0x11244d4151900c44d0b00d80000e403807170942120916032190f004270329018260b65100c0f030030426a69040c40d002c900c9071600e082c004003c1c56080c0c006900814002490240c5810142107004844040d03601c0400050b0380e600200e80310161100010305032781003240030440c1b102c00e40e000b01c0480405034003524a000c078071f035860329083e00b03442e03000b11910314002c0b004003c03a68080c0300340c18104003980100d02e0341c05801c56214a180900400ca01e21400508411301500e2861498510808038142c100b045900d40301e84001c1d5881990348a4188079110718000507000e032400340160000c40740c0c103031100700c091401c02d08200e01100b074061300345421645074400811010014021a4010301e200c4146590f207080081009200c02444020f080c0070034144020f0004c3d8062800401018004402d2080d45400d142e91421001c1d2040c03404891001d0104000e002c14401c429844c01d0081300e40100321402c10501c0018060003201d0480608054492a800600118000c90f50258004138900d804003170401c03400d502110620b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 176817311 1250 176816061 176816063
    0x1605070e0f01140d0206040e1504020a0e0405060a0506070305030a09151b0f02030301140a050d06051e07020a083901110301230a0909030c0b13020d120219 68
    0x110301c2400401001e044040c0c1c4940c1c001050310643e0700450550040b4000b031043e03200d02007002c44002c000410800904042070030b01c00c4001d20039591511310703080c0107000f2211055a14855031500300865603c1c0340038507642046910250803541084045d850a42d840d4100030030000f03016858240c0f010005003813804210303069180c40c2c0002000340f4046891445034100d90162824031034480c0341002c403240c001081d2411600d6808202030510103a2001c00d131161416448107800c00c040355a000d00304290381d00564401c0ea810102e03070700060200d48070240c4e400c0c0160b5190000d43c0041442c1c1000c1085180284110240d07201f1604200c2640e0b05003c0001c49a54807025401400380540c0c8107048080c01501100031843c1c8445040d9414840c2c0026090b030b101507141000036183c0000c1c1911b848000003070b03006050100d01044104a2420040d20b9000c1c82c1004035009080200003d4051244035400c508150b000303044c000c6180816a1011640c1002082c51810741c8a50b5168032030300d0b03024120601c401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 176818561 1250 176817311 176817331
    0xe040501090b0105010503062808030403140124030308071419030e03070203070b070303060e090a021003020f03070c0831050a05010f08070e0a030f261605070e 70
    0x5100d00c1d06102c0c0300544103800050402c5401c005104140d6200d00f40035007092648519582d00d10f03072940ca00301034041c803948000c805020204000003405603918080741c601c40e400c0002d02000348401d0080070301105209034181189405801032011901c142c8a403a841134250516800c8000c20b480f585030543c0003490360148110701c0200380c0c0fa255900d40510100d11441c40021418140190b0000e40c5900d85801854a08400402c003001854170a0b040350008040c0b00368484514208244c0054903030030301d0041680289005948140442c1c03007031003101d10880298045070700f0368988903002c40380501905401c1da41c2180c10320101c100320728080442402480c650071a00c2249130040b03510301c040200341d0320481c0b0500e1402410880b07643c210303944644108072817401d400969104001a1003000c42c804035640c0080c91828048200100c11a00488a03401041100107003c0c140d8a4100d40c14140c24203a108005c050280300d250100481c1006160344c81401a00c3e0507070303101c80e4100030458003184e24241c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 176819811 1250 176818561 176818571
    0x3090d180906150e09160804020303130806040b090303010b03070e0f04020a05042108121e010b0d050a06141311030a0204030b0108030406020c010807020f0a030f02250b0f040e040501 80
    0x80f03d8124406407400c100681d0508041d1034424940303404a21034150400500059800040442d0303414012110042c00c2034030420255503c411405070344180490b000c841c1918000301144981d100002680e0403108040041031444d51002d0040f944080203204160308400781a28070805540c0d2800505503184140d80c41035100c40c40d100b46c0b1200700e90300c0c1a410460114410342100411200c00855180d0714001d4905143d0f900c54001c45007000c1103260f0b81c00529642d840011070010344001c000c202c0002c020354244404d40311040c01800310340b82881003514400c814541c0d0342443c00d0001e8580c403100103d12001031151081400d400a50f442201d0511040b5400a401c2c400c00501480310381c09484640c00840c02d203820b0141c060341c0c0b070301c0d11844c15050184002c00981203a200b080f4200e00c0c07030613003000d40e070b000c1065103005440a80000c3c01c001c0540103c9120402c24242070240c20700540d08211410501072401c0a547d40310b6001005134010101c00f0000071801c1011001024015071044c000015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 176821061 1250 176819811 176819849
    0x100b0d02040624090e01050418081204060b10170601030609051303020f0f103c1b050706090812150a0509130209090c1509041103090d180906 62
    0x5140002c0449181c14004034030010300170074211441c61419640240c0b00011000b4621314040520942098010040c8500140c050760052070700c24185e020714400c038000e1102d05108010403d410040580103000211010780b0341455006201c2a9500060b041c1000694a9103452030307072040d20002ca03807215400c030440c80c0c00010143e0400500d00e44005c0d0101a00c0c060540500141d00c9400b10100703420312a4076602c00c07513400d14070010032421801d291014015024040084404245040080c086401d80f502c082203800348180040c404031179800707a458600e01003095961000030807645205907002d0380140300e02412003c40419290080e00d480090030454003a0904004564030f440d00000d0040e110f0105001c1c20309400c034808203000341d040b29a6031940e510221001c1c5825500542140d01031045051054514000d100402407000280d1f400d21007610030190728603941c4415940101a40e1081006802c607510541c07400c09000d0180e034800c001c00d9a500071020030745001e500041000040644010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 176822311 1250 176821061 176821109
    0x3160209090a030909090203030f0408100f0b150304110306010609090e030f0a110109020603010b12010e0601050f0a03060b03010303030204090f05040819090302060f0702030f0a0203100b0d020406 86
    0x2030344018410002c040c00141d03541c0c0242184014421106650b441c0c404c040c0456506006a4881000303110449880355034070350031941e5441960b4002102036150500200340c500713107801420600c04000e0003c004030b001810300400c9a80c0020810760f220103441203101140e40d010701c8031038020282aa03541d9030507420601c061080325008100000c03551300030880360105444500030f403040aa49424188038015a140500380902000321b0001e6201d603001001084bc010144050701e80b5600305510441e0f90307a00c81a8488400c40d090707401c3d9010070818001266001c112100406404145180100b98281e82d000c010b00755800a070400c47c0030036000b042c00d1005411500c210440721035050b10610141c1000c1e199a94a44030f400c0c50b480744421000c2d0704c882e0150290656034025940681641d80d01c80f50030001506581018000b00c0c4680a030704c1403959600b4000601011840e002070140c44445190052480100071544581c3e0f080007107001c1d407030056034a51003054014800c0c01d203211106c4100064203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 176823561 1250 176822311 176822329
    0x1a1905091203070f080c010f05010f080f0f10020f0705010603030c060e0c0a03080307030b030a060b030c1e0402130504090620071502090619090602060a02040b09130e031602 76
    0xa03007240d40b052058201103000c51140c11482500454560307030b20248003121a000d02041050b80b80c14904003000018040300c80340e504802c447e03000f000c1d00e145542401e12991602e0f901c00b8144091740c0203000034110ba950540c002c001d09412180c1c0c040c64090103a5a207401d603103443d40298086a0b8440081060004034041e50100c1d000c0403018128510042d40001d02c0103c00b4000030302a103201100003614140641e10021948100074112030004120740703080d002510720031200b58020700030081c180c0824189849082c402208001010003c102c00c0d13014400250001043c011140000000000355900e880c0306001d8041c0c02a1004078104528149580c8100b50110030504500c10030050b02c4c0c042280204c0d010704c3c540c0380c01c00169540c05564005105406004000000022400701140050381c001e100e00ac1103980603025030f40e05130b69547d010130490240744a0034203103d200f002103410354648226031528928003401d001500900600400c1c0c40d6400030168000e44007042c001802c2036240003d03030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 176824811 1250 176823561 176823589
    0x60a05251b05030d030f060504061e08030906030c18180405160602100b030a0b250306030c050f01092706080105060a1a0702190501030b0301090c1a190509 68
    0x90701d4429807600c4046135880000501d2101050390724211811001c149411036001400d000300140070951f1200c087e54214100c0c000e195540030401c41001404c103c01200f40c6102540044c8403a0440e500e40141e48000d50000300078400807080c1ca5020b0074244d58100c1c15003412480e19002165030325241c40d00b140f400b40701d40c058810f00c0300030440420a00c0d500040c504903d1001c40d4021a00300384080100f40f90402d1148014400000c0000b0000280e41544940d1800603403460300349003a41c4010300c1036080300d909000c0500000d40c00781e001d22440c10580010190307500c0c10700d00f0b104542e0740e650400e4211001c015500710025411805452450b82d5809440003405901008208500300036002076501030640c8642d001044025800d0021700484c88103940c685900601016a0000038100c64066800640201c41c0881c0c5011420f140c3d9080521072508a03c5d0700142c03200019080000030541c104600740c0d201800c160400948200007a13001810700102c806403159a11244008200070070a030034003907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 176826061 1250 176824811 176824853
    0x50a0b04150503060712020f0307030203090601140d06053d0501170a0902031c032313081b1b030d0507080405060306060f030f0402010e060a0e060a0525 67
    0x210501056a02250958100e9a42c0c14000d5903a82c8000d0a2806401000303041035508d0008810041c190340c25400071417040d10200280d40c000ea0b00c030401d90030541d000c20541900040e05111400014219a00054101c0c400a040154030386581c02005000303c0340a10204101c05440e400b01d4071040803100080261000f401c25411406c0d00340f00340e01014000900e500401a03d131510f1100303545091080603085010201c034501c85800421028003e00a002460318403000c0c0c1904401c0200c0307c8180307040c0180740c0c82d03040301401001900c0e260320b00e4100401c030501502d203a8010f0b40000e801000405d0180801038280e100c1c0c180c258003010305000301039000c8820710500300505d10000f400c1034126002e039942180c00300e4030380c0c40300c1c004222039008255071015010800014001c11020300f041ca144961b03c00d0f81c0701c1101003250024802c3e18095502d00c200071901003500d4500515094001d03000b50501480c14908058211616a8051240203280b00c100c15800404c4001d001c2c4228820b621441005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 176827311 1250 176826061 176826101
    0x30f0f06090316230d0801030b0109050603030a030b010e13050a1104031203020307051b030304050f0d0c0204050414030f03150406030b13020a0f06050405031612030809030d050a0b04 80
    0x80030740b424040d44820000e100301c01242028502800141540030361040100c00c9a100440c01d0a02070106d650a0000366922110b403c00082e80d00c940380221441444041e0185051110060b820340c09841c140c001075041c0884620103404544444034500d10022041c00c0115440c01d2042c5910f0440303c0060240c110003804100600c00b00e40001021202c005013440c005075240d036941001c54403809880440d142510010460404841001002e140614024401d0b10301401480c900c050b17460303000b0310a05021640300310300e00001d458140d00550303109e4000d600602407150300c108035034256404590801d10039140031080c014203070441514000c1c90312013500c040040d1070031034491031500c0da00101880011031642c141340045440b03040c00e0200602c984010311100c00d0300d41c417010744250828001c890103071069100301d0100800e1200500b041f19800110010034280340e0710200d8aa24000705041902d100405c206400012036200e400d2007940d001d50000748103941c070300800042d40e1807402242c00e03c01c40f007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 176828561 1250 176827311 176827327
    0xa02010c031b020705010f030608060c0a020613150c02070306020f041508010f09182f01090524120403031a06070507060315030203010504061a06030907060e0f030f0f060903 76
    0x5400003980c2c402d00f481c9005540a03c0b040300682780e2034000d401640242414005031110050240141a40d00d07001c1d500c4c10354902d10301003a4000c400d0380240c4140b580f9181e4502400280e80950a171510700d1043d280030b541c0700e48807002a03a000441e08900440006001c01c28500303550385004040f007071450310307a009500d0003041d00002060380c0940108a59503e1250400c00750140b66442404c0e8010002800221080c403807005004088080082d03180800d5200b241940c45052250180c90300149124200c00e03401c403081e42d41000c001c880c4183c1079003c0101c07490803c01c1c02150f510803480395a010070491950400711095800250149018500500c000c90004802080000640d07d06c1d1400107451505d003080b208100201c1d40c4081c0d0194a010140400e00040380c104000308680704e401111184c1803101808042d1108580040c000d4009010a000480c03185041c000311200040c200d00004110400080c03c00480382030140403580410a41d03a0f550805101003607101c251030015606000740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 176829811 1250 176828561 176828563
    0x19050f060f2212080a0506030c13020d06030803010801050105011e081605090402040b030a0c0c1212020d0e010b01021501081207050a0618050f06010f050f0d05030a02010c031b02 78
    0xc0600985401841e00c0140b40000c0350108000004641000c0b802c0048900c02c01d001e088010309079407594500e410080002e440341400250b0380f28009d4041e02000700d000010302d420f00250045007200d00c0c0389440d60070000100310a00055400b0748500c8000107082c0d49414005800e005000c0724510002c07491200002c1c80d02d0300898442e92000b1030b0300c485420306038501c608440c10320412100c19071045c40441c0c0400c540d800d0710082e501c0f07220242810041c1c1d102d02d070b81c10f84a041481c08014600c04128410012581c80b5820549200c4c0c0174040150070840124103440503100c0d1154820700c03980d5508880c004c3d641c3d040241c1e904e041520b00001e6585c1d41001e8699440d009880d000300c0c9113001c0061404100b00080190043c0c550f00f000082210400010303c850140e83c10420a540034414161110000303072021814504844d981c40741803408514107000d0105c0900c2203003a1560180c600c00c0b40c0e001203817042c001071200d0300d070650002400120044003d41181c081d00c00008140c00f450000c2d05007150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 176831061 1250 176829811 176829841
    0x1e0801030b04060902061803011107020603010b0a090305070303110d080103110d0809030102030106020601030b09063c0403020d0314010b040303141b060601140315040213030519050f06 81
    0x2400c150400620b0741d0300e080c00e101404032060000d42005000a502c03046c0007403030200315168102103000380301c09251108844024002c01c2400b0354400820401080035402c0340d001001070150710300b00300c9411030350380d1180c03800c0c8085a40242d000c64503130b440e02c0184880034010840c0e03412241c2404c800550564036440d800382413800f542030046a040d0140000d014030302c0d00b560340c1040014005d650f00d68450344c0082d2158020f100071650340201c000841d00010020400e1403145820040360945103400303520034841c6007100344100b0409482030212100c40381415130041e100300d00a0b0020400364603040c0d00241296070480341841c86813841300040c00721188220440702220307018a40703040505a0740440702c1b124130900502d015080e809940030380840744003003005403151000341c854040d0f0054004080d007440c03100b1035013440e50180c80043c0c201c040c070f4990301030302e41d85442d04c0701007007515241c1d070701c1c00d2901c5261140603021410400c0c1440401c841041600312040a40c0080d10980c200b482c100c060580c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 176832311 1250 176831061 176831063
    0xe181504061a041503110a090e0a0c1d0a0c0e1207060206060105070201021005060a050316260d0c170a02010e070b13120203120a0507020307080613061104050603090d1e080103 77
    0x212540c050007a0587d11091030b00050507140104000410908880c1030380c030107150b8030803071300f401444c200001c01110120200e2074101c04894039000302d0f40c07501d01d02c00c0244446046541402400030740d140f009d44480030300c0d901070b250b10401040054100303071000e407805000814103070402100f0054400140d0380400c010015980a00002c00c10b51980350010390201c4c026042903406215035844ca462001d00740c0780110071511000c0f854684501034143d84207032480194003100241e4490413000004074807440407007018501407160084101d05a40800f4003da220603400c100503911914030300714450050194a0080058400544c074113516147d00d01040d078441c2c4100945045056020300641d00c051240b181995000d640c0e185d0380d1008494040c20715000440182d000744030b41c0a02103550140000d5840c0101320b010340102e1101020b0752400c0103030041e4651024824070500c0006103680720540a58004e8000d10050b1000c9000814000c040f04842c00381c4c0c0b00c50b4090100017182107030700701c7c14a03030540e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 176833561 1250 176832311 176832323
    0xa03050903030910020703030f030213030308040f020603010807180c02070e1306050103030c140604030203091c0c030b0f10060507030e010302090904030504050a0e010e181504061a041503 82
    0x8035400d4000a00354011400300d69003141082d084549415400704425003540e2080d00d5400051a1019044041b4006d280700c400c00d0700c80b000ca05001180c069a12030303500911810001c5182c0380540d02013010b5400a9000b02581da000380000e0100f2500b65044601c0321149107010440340f45507090007560f4111074400c0c0b00b07002300018085004001c29007101407050344c01250038011541c0d00e01d0003c6c0b0740924440c1c01d54511002094100c4410350100300da60240303415030b00443c10079900c00200321040c2c02c0c40c01c03441542640c0355035010010303a840308200c000f14003618061615150030300e29080c1c2640000d24032003070070312100c2c1c0034002c40e0f03000300030b541c0c003180c05160080501c041500103800a114445a166210348040c0400c410594003000030003d40d002929118203240d50f80e024600c1012082c014042e4420981c0000b45c4111002340342c1070000311210b0201c5440150403102c20742e203010305640c260707841d903190030280104d000d03900501d0022990540b020840c0c0507000c40c1034425400f03140401404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 176834811 1250 176833561 176833567
    0x3070209130201090f0617010b130b0a03060305060f1501051303080f0715061502070b0405151207020606010f1b14030c1002090307050f090c0f040b0d0b0307170a0305 73
    0x82da4803c01805000c3e01c6984007005940740c0740c2c0009000c001242803003e49001b8202c001090106410080d280031509083c01002d8003810720703003c00300a40081941c2010550b541e4800000306900b040b01600a45070900b9010b01ca007040c000704c143c81410004010305100e002c22080d1b018082213240e4004807034018041e180c03101c3c8000001c1905100e20103002d800b500c01c19250b181c200e40e65910120881d03444d101490060309416200fa030302c0315242d20030000110340921042065082c0091036100c105841da09440c03400c0d84021170703030800e110141c1e03c040041e804041000420b50300b2400d030000255080c2000c13440c460381a161801d1000c030540000309841c140d40040c1012541c204140d50b9111085c80c06c2e41d000e009640c0046001f5045280c0080c031900c207056001843e41030811181d00c1101d80500180340c6680c4c3c00c8a240120351000591828003501000002000c07141ca42c042c10086454040102d006442001050f1138980c2d01c5c1c0110b41c90764201500c81e04400b0001600780d080e02d51500b0100d032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 176836061 1250 176834811 176834813
    0x8060103080a021606030b0307090c17040f0816110f2107030605010611070f0806040305070503120c090f010e011d0d0203100e07060906020a060b030a02150415020307020913 76
    0x300700f13480303180c011020104440000c00c01d6601608000700c1d00100343e0803202215983c103451801daa020440c04e4000c120b4070442c07001d9000e00e04030354650150040c2e051300041106030b41d0741c800d65400f0090107001d1003031104c010020440d10b96010350140d0001c4800d40950294400082c40243c0e2401e0b047c512078031014045808141d040c004c200040d44c001008010b03c2d0307940e02c805410302074840034031011402003802c04900d01084003039030b0094076407110060085a403139943c2543e4640c001502034640307200034800781e800ca0441003400d0b8415121368581c0c603202d03002801444104003050b9041414404980f42454140e40d211a071b100d1440c0864100e0400280000041001102d610710042e406001e41e60342c041040301d540e0000210485400304880c81142c1d00c000c22545500f29010340300050b000789524030040340c46904007031407030800281501c00a200960000704014541401c1f0900700d2404141001074110b00001640f02800600240d80740c006268002441081300a0202e201c11040c000004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 176837311 1250 176836061 176836063
    0x618240403180b03150a1202012d0c02040b0d020906010806180a02071202160902030c0d02070302010603050f01060b0318010e030f03100f0303050d0506030f15011e08060103080a02 79
    0x1d5110b01820031031068581d1030720115002e50344201c0d078a1031560f2201080b0841d03810101c0c03840c0d04039545500b00e01840013442c0c0c011980001901c1c1c0c142d800729038030f1a021466024501c5520080304d0b07107850303100034004d06d4030600094138010020750f0701c5108024145000751300c07051620766000d00c0034a0007618980c1c0d4540014540c940010182c00b00300920b00412106541c203a008141c540d000d0300744243c1c4659900001c03039845800c001c90094448004604212030141a0080c5801c26032025226052401c075141c000300300c0e00000c505900503916580100240a4140010760713490138260000c0c090076007040182d8003140303c042d1202c6024401840101c2c2c02990a61246c4d01061148050720b43d6110102000d00c3d05410640314080b200342c5020f0001030f2480456030040c2100d52544910307081c40d0205c280c00c4007c20005108075054080c120301c821034000c1c14424010311400c480b18840f04c55040c010f9a4000c001840002c0b00010b100110911000780001102070444c2e42c420106a91040e001c42c0c12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 176838561 1250 176837311 176837327
    0xd2109090906050f010b070f0627050d08010602030412110f19030b0a36020a060c0501050a022803060b1303031b02090a0b031903020618240403 63
    0x901040e52030100d0650810250703801072801809807004102099898143c554914881c100008002880301621400010015044403443e5a8a8180c615140c03070150001280c0d2950741074110358a4000f80d0000c100c041c1c0006e44d08ac090090b5100031070825003008841100c0700207000c00034010089800c444407943c6d0302c6800e480c42440c0041e00541038022062010703802615580400c45400842200080e082041d510a9010303a69a440304484c604121080106424030b807101546480807241c0e0300507002da201c43c08007400902127540c508024050505000703084880280500c0682c034010440c886400c000c10964601c1c1a20a880d07841120120342001d500400c0264007051408001003403024103e41441e41070004ca80c065120070004450344500c0440070702e241203000f54894089404a41d140394035034024100514060101c2d00520404200036008410001d0b080300107a01c808104200300c451522200e038039402080c0207201c022034010400c0e10b2922600140540740b4070b1940080c0c1418802d07255 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 176839811 1250 176838561 176838569
    0xe0303040816060f0804021005210106080702010f0905120f0c0a12120c0909050a09170d200a030b04090204020c0d081506090409030c0c090c020c0d2109 67
    0x101c80b01040b203250b0b20441803041c0d00c82c01011885240c2490801402035084611483d40101a40a04807402600303440540007022810310311941c80c5030f40c1c1d1010381c50b11110360103001c0399183d0141924120760020b00351134803490300850460504525500040c0001244280c0c03640b04d8102c1c80c0c40d2140c4190f00716007401034800e855014070a541954041c0a41c21a4400a421043e582e1103000500c03168100c05841c1201a000c0018614072001c00880c44240c2c8801d0b0886445240440c02c2800c1e07858a555401c0c08407140c9070313a20b500181238460a0002e2041e03c801000c081610b002070122008810b21500600020909158035200c0b10306d010703581c984c80180e12a60007002103484001c4564120780c0c0d0844400c00038007040740d110104149000071510359051420080049183c22500010721000e0301f05881c0c100c003030020308042c4400080da003285410203007101c0c80c400112010341c048024544003644421901808090b01a8030120b20b00a04040b0202442c1c4503916542401035000c86240c002640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 176841061 1250 176839811 176839813
    0x51e0907080a0f050105130e0f03040b190f05030a0207050a0f030302032403030703050d061a070b010501030902010e100908071d10080312100b1803010c0f0e010e03030408 75
    0x4200c540e035003041415000341103000307003081500100007a42040701d8007030060b00d601c80040220814201c00c95001030481d82244415103800381c4403284c1c01482c64009410142c524040440da464184621500811f1840098540400c0c00ba1035a0000f9001d84405801e1040680e00040c8400900000b0001600c4065001d0300882d405e13402e0f8240140250410795842c01d210144d45038855984a11804415405000030061071070b000300c5680c140e0301a0300003520724103030035296600000c56512020f4402c540f03000401d0350717603599242460250003581c01600301030b041c1460803585a0250341e2028481142030002c1e5154003220740444025550407030300703074031900c0e10b841034000100300e418103044144150880025141190b842e05403070000c01c02154011440254014003100c802420806403254005801d83ca0700711080c0e071a08603006041e8051014104002d0407505d410300700381424480c254080d21180b526070a54459030a004001c0e0f00b900308014100624030004540550b41402183d0040120314 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 176842311 1250 176841061 176841079
    0x60103020607170717071b03020f130f020703020c0a0609120f050a020d061505010212031b070c0e0708060d050a0b09012a14070804061d12010603020a0519051e 70
    0x2000c5c00182c1c08a0811113900084240e0140c5184d003403d01d50302502d80c000c4c858034441c0901c2c030500160760540c0007d074076400c2d11070b424002001c106200408404e4000d0b03006d05040c801450038003946041c294024000c01951000c2000a82448003444c2132503a031010400051000e9814814940b07541920302950001180c0c070b0780000c000807940b01100d0301164507004c04405950700016a210181c51000c3c810011017000010070304c031820039201c45d4290301c01100508081ca0b5417661210f881d19038001680000c821030511600e190404169948220100e581481c0d00c0f18507640d8944600084400a01c01c08842d4081515003102b900010000000500c4415583c022081c81c9903480010a40307100111f1501403e444070b1200d501c00f03c0e400390360401003041c54149080c60444240390038000722503800540500600040e95101c03140c000c4c1042c8440081a4241036004001d04e180ba42d600c03988c41400c020141000d240c0180c1071310340844000715040c074442c1415030213000a03c1000c0b000c665120b9805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 176843561 1250 176842311 176842343
    0x611070203160305070b270102010608030a05030106021b06070b04032307060609020936090606030d022e02040e0106020615040605010c0803040309181d0601030206071707 75
    0x60700c1c14012203004500701c42170a40d82e020001014440c100d015500e1040080144050a4000c0003103140a141031000246031503645000d9030940e0000550f03040025070000040000c41c2d2b04210168084807416600e0a0304405440054028816240e0040c00010424001401d046c0594000e1440018070401d5610a0720704a400445a9010070300c100d40041c034120020600980c20700c240c3d060701e480a401e8098000300041001d01070303030b80c7c007903202060074100d481008090200c80d1309078011070307014000b802c00c4e0400800301410482a080136504642c0f14040004404032510030060a0300040115802014040090768029200b80d0b08800300301d8010100000f042a400140d1170721801031038040035401c0d0210020881601c2c1d1500c211400140e02c14a40000b04000c4001960005e200707003880c007409652500014080c0403050300444030701d1394480d0234402040c00b6070515800c01c0820710190525604541c00902c050150000107880e24890400d4101d18000319401c40e8602500072030100344050038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 176844811 1250 176843561 176843593
    0x5250210060b030103030804171c0b0f09062b0516030203060a05040b0403030e030c0a030e010f03140c0c03070c0b0406030f02130306020a022112070212070611070203 73
    0x4040054600c0c052002865906510540f81038a1b0701d031780c901c43c06444e00d4072160034200e03101320905600f500400a00c0d064010324083c074481e9a1410801043d030840903401c01040424007500b81c0d0240c1c40941c100f0111799541c0201028854034100e0000114003030302c5010141c09400c0400400c2403044200c200e00d940d002d1610581160300c04c40481d54959141c00302c04c0d003525000c1e203000b88100101c80110300020300903008010015250380889040441c1107082c41d103000c070240010343c089050001301c01080d580c081003c22440c040f0782400d101d83d005507207125285034002003101c2074076440807e000814200c11f1085a071002d40141442c060075841d5000c0d080194054407070100070914105a4240000d89802552070030051081655421442d503241e1201a51180304184114020000b4040b0149000b21400c1544444980d02580704c000c15420620048000340441003550301000b1074000003041c0c0b1040307881c8260322502c0440c45d14200c0d0080f40e09409404e000a40c0b50180f81c00c5001034141c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 176846061 1250 176844811 176844823
    0x20a023616020f0c0105071a0a05040b07020f19050a021002010c0e0406030506040201080402010905040204030305090f01080112080c01060e0a0f0c08060a090b0f090403110105070e0112052502 84
    0x80c441c600d4610044480181d0740d40a802840303950341d411000344541558003031800303803100724028411445910300035010400e03144d1084440341d850ba5510300901081c0040011400d5102c1150b000409205074481c00d19a80e85108481c0d030500742d0707032580150081000c180030810a065016181c99007901078600041c0c043c00d45480c0500004071200e0040308a0314040c090a0b0481b9040700103016561501d0300111000f08009109a05000441900040503162880140002c40c020364a95844075807000c1048414010340441c82c0c10440307a00e005200031050304a01000e8117178809045590b40001c2c0d0702841c00340c001130344281441c0c520324003040b442641641003800340305200c1000f041140c0000000780d03104441a15101e4221288078401e0080c2e515561180140d004010590010b13490940005000310784110b80440c00640c11201c1240511000d000d9181c1054040c18103050a02211000800ca6160240c2020f041a2200d0208581c01803454030340e803004e108110341c8a20000005ca029550304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 176847311 1250 176846061 176846071
    0xb1903080c071d16170a0c090302033f03060637020d1112070204090b0903071a060d0b0a020702030a0b1006032c07150905041407020a0236 61
    0x90208013105034110f00c40d500c0d259601610b01555002034031071141140c01880c400242c84280b00380c04070080050b0764100039182e90090603c1058004002c0c010540820100c01c0d00504221541060341c1508038200e0000c2e0b030342c0b01c030003030341d0207522052f0081c1c0d41c07000701000040b80301012002c04100d81c0008245075804ac0381c08440c1d021900740300c0c1782160482c1e529403e803e013400d294002410445489c10040010b210b4a400107001060000c6584c407514640041541c03000200c3d40005a25400c012000920b03aa0f801003030b100d0384541c0e181040200380b0f945500c84004113800c600100103036120581d03905035989190060116821641c2600d018000e03a1000d503000416120b2403400003d00707521a01500032044001c41d00340d6061b121608103501804502411100180990070b404550102c1d02070000304a507540350386803150140707094284022076001d000c0c03403030b02072030b01400700803090341c00141c00f407445541a5116000e1800e6522410645042414910a071422584400300030380706699000d4028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 176848561 1250 176847311 176847331
    0xb07080306041a0a090e1e0102030604150303021c111b030115032105041d01060909270c0504060b09040b031501060c08090603090a060b1903080c071d 66
    0x414420080f2048100e49400c005a010340002c00905c0090b0454020f00e80c06041101140c0040f08580c076074002e505451101d84909a5002c0100001441d01d80600c004d42c8401500c2d4101c1c031400c40d18029242d03000024504041ca071510125040f640c03054000d400703281d039a0820340d1441103010810341d9500b049040c003184a503080110055504103282004002c032a40150118128a507169803286803031025880e101c1401814440004d5001e074002004041d24000b100311441c40d0304007038002d025004079801031035000d4501a40b90b4105410748100b040e415030842d4602c003000400d172510070f400c2603807a0031581d00b050911000065038011040600541001103800b8003012525105141d0380310500d1446c2c0340040200070041003900d02504401c60500e000d40181441d214900e0003203441c590054032601c3d1654021141d13002444984d12508404002c11503100c490080708035541c4440400c14040a00801e000180900043c0000c200c400003c101c1040d042c4060000c40e1a50000c0c180100c075000e0308 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 176849811 1250 176848561 176848571
    0xa0510171b0a080a0b06030a02090f010e07300906020a0203040608130305030f0a0e0604080405090708060a140f0409030e032107030c030c140607030b061c0b01090b0708030604 77
    0x10740d242058110068801e0700005100d14035964a03403154940c1c01800254240c05240f0042000d82ca0f0b80048a108000f008060301055261480e20400c0d010000c2c02ca40403c99040b5100c403003658994400060850071003a091441450718034800e0042c52001e000928403440018401c0c0415004005402201c0050301d460a09a94141a410714654503000003000148104000f54602410420182d08a982000005000030001000520b4108240c800303880b0007801240030006441c0c042d5440b540b201007490b03e0f80280c01d00c400030600c003c105005e211700c1d994828400b94600c2d21180e000b80020b0348010410b0080c1c50702c500307010380071585e4000b5941c060302070352040c04960200c0e0654480324902c028002d91404c07200351000caa401e01c0e00b5100714200848405500041085c09807441c0c7c0c500700010240034641840b0001030101c81e030380300506006420500c03030940a46168041400410814200440d101217900d0040310800c1c03c5802176010b19001080314010720000c4005180f00d14026542002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 176851061 1250 176849811 176849863
    0x4140d0507020303030403050a0507060e150618010e060103020d180c0506030c030a050a0617060601020601090b090c071403030106030b0301060614090f060c0109081e090102060a051017 81
    0x9103600c00d007800650942d20402c00725000070712910081200420301d02d4070f2810054140c0d035020a68800b81c50101a940c012007441c2e00112000c0d0880340c1200c411150754620103240010540d41e018140f08204c0300388944000180564000d804445201544050400c101600300700c088034129448101901c4c860840c1101144c1ba040085c11240030b1100790540a00799a04c158414000c3c01c80100340170005d54680c88009400c1840c2c031517078205145400064140e61900c0e85c002481c0540513070112030300c03e00b4032000d007100c3c0e110801200c0c3c0000c1c0e8094101da80b00c0342c03820900760680a0100c40e82d00352000000000b141c80d807592000850980803402030081e66070b01e000440c1d507103980f42200702c100c2c80100b103402518a01010500c006180141200e801d0501c2c59440508540181109558094000401c40f0f25074605034044c038049413100340254144515000000e42c0ca070300041c000100c8950f10700c04103902c20346018440c002000fa500000c1f8102218805598641c065180e00c000071680c6000008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 176852311 1250 176851061 176851067
    0xd0903150e0325080a12050c03011404050a02090a060206010f060e0108010b0c0c030102040603020417031216021c0504031a2211040f06030b0c0c0a0b060f040504140d 73
    0x201402031204010b500b4201000340303141c4003804900c0000070000302a000d42c3c0000d81300d1006010814081d441c2e0309220721400507a0026284002c050300c02440c030400062204100031800e42045d007209480000e1160703213021040000b072140c0850300b80d0102d00178200150b4164006103e50588105c8880711440d1607464030203541441090b0703005404107600c0350040c0030180c0d4400c081c040c000419800c98120100f004040303800c81c2e110ba0405000603800242c180810020406100c400c80103c0c1c00a6242140d16002586880380c007520202c40307409184106155a031003000020394102440700c3d0702410101c00e100260040d841031000719664403103c5e80d01000c0040c4400154440c083c00a1300010100c545541d480c011034603400c0c12030712000307941081a495240c40c81010480a6400c00c001880c1c2d041d4100306070500760060440900540c200608290080042048101154020040345650b1038241c00101c5294540c0403044d0020310303103001c01c03083c84001c3c0303100201c4010550a40e040001145411 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 176853561 1250 176852311 176852321
    0x120102090111010e12030c07060623090c03060d0503040f0b0306040501050f011e03020c030409140c03070903020d0804120b0a0510031a06011125050406080607030506030c030d090315 80
    0x20501c035411605c0d00341da09407000c200a6034007c0141d80c05515055407681c800c403c0b5482c3c0c0d04819046d20504900c400745083d004800e940c807180840c2c440104d8a050300c0e0202c030511004040901642284002c0d008001c8100191000741c01c0060810340010340711a0604010b41080716050310450810300001070a080c4886017104105040c0e6a2000182d120003802410224140030141055401c01c0401c84860b8248054001b03011825404154066008480029601c018100c103002c20401c01c01c0c0041c00360008504c104481d810303901c1200c00152410807130031500817980822800b00030325000404200315441024400c5d8203d42c810401074a50500031498002e16000050210044603070401c201050203544c40e6000c181407400425082c3c0d130001e070508100e21440901c07011618020004000c464411907180601000e941c2044541e16010402d5602c1101400003018941c4e5000490f505480501c40c2e0b00c81540301404071640804002030080c500c1600d40300940e00c00400803d50f490462840c00f403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 176854811 1250 176853561 176853581
    0x309081203070806040b2103190e03010e0106051e010221190306081203150a03030210060605190c0302010902190e090105060d0b09242706130201090512010209011101 73
    0x120070443c418a07090109800701410a00140b0061265091f055016100f04030300d54002c0cac3c2d490726480d20701000c5c142541d6164017503640c10b0341480d2090000d030b1242016070840305488468a09982002070041c0d040c840102d080d004094210401e24404540c800010420458240c11001c070300c42176010120102c4003140520011a00601e20717880c0e940c41008051508003611032100f151007244100040c01036110ba60086000d03802004a024014019101d0800207200030705282d841e01d120700c21000043c1c004080040140003051450400f454402d501c0300100740c0d40542292030a1541260142c9407e071140318010082e0710003000105d6001d03040c000c0341c1c081d0b00e0103011201020f4071507907564007150008103110014170070b00185640485d0164611286145030f1034025099040a00302d0300440720301461101c4000213406542820540d0008240703071b10445a03c8595083c1301d0a01c01262110600ea201907440480480300211820065000f003c50110903201d06030045018040c540c00ea490310f0b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 176856061 1250 176854811 176854819
    0x906020d020f1213051201050f011e0902030705090301050a02040510020a1a06061210030b0c03160f0203160809010e1f030504020f130b09010b0418090309081203070806040b 76
    0x28403044140f9186028083c003001c200f401c0c903e00342d10740300815802c0c0d10456010030305079183c00c18042000c111300c005901400d2844100204081c00c25016071a100300d6220311200554004005440244500306031a0740d00c800400038001070a182034000041c1d003150007100c0c07080700c0750100c51012600001e03035600015400089510701e0013440b5403100b03000d08010401500130404209590071154404132441c418105e0304508555541503050412000000810000c00c448080040c411b0034204449414050881d902e000440922141d808a0441c0541e1803074510b01aa0750683d9000c008036140903205980d800c0e80e880e8a020010001c000e0040c00003510740c4400300840308078a60081c4030b50041503002d07001405042c2c501d200354000c50070010007030120388041555a8007250f01880c1580c4590300625026809a08081c1059a07405a070310082c00c42d2001c0907540c2036024109801070f00c0300350080c0140410340d410a664850f071083d00f60f00880d08600001d55410024001d8a081d10402d42d00c014060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 176857311 1250 176856061 176856073
    0x91909030c120906020c10030603020a03060608010605090402180a1803080f0609161107181506021f1a060c0d030e15010302040c0e0303031014040902100807030e0d0906020d020f 78
    0x6c1482001c0a0300c41142c4200b640b505408005a100c10720b0f03030002148107038000a42185084003890850350250091071041c2801c105100259480d10f00c01c04005007407420105caa038031a00001c1b40285410025203007502e202043c01c00034560406041880b03141c00e01e0003001d00340e13035401c10000c2c5000201c03211032458241c104a02c111b076204001c0801a40d08031740842c0e0301036480e6075043e440d4081c40c20b201100942c40d950380003515250515900c0c018801400101001c2200012540015681d6040001219510074603070694803850340c40b061000c00068282c40d42c0300c4100d0700e0b1603199880c1ca0004404a4101922060140700010f54070040044c021030021141e400c603402c1102401f9444400410040d8000024034181da00b4401140145940d0284140052420404918040c171103180c0ca071049240c88203403030268440c0ca165055400fa249002d484683d5036000540041c10b105030744071300e0f510450100c002d00b1074000604a05035816030b0211801e00d0900b89080340d5812200c18940b906400034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 176858561 1250 176857311 176857333
    0x705040c0519021501090b120c06030c07150905070620030a030c030f0c05090a05010c0c03020402070819090e01091e0203060402040b0f04062a02091909030c12090602 73
    0x4500004041c942c0c501c15190303c5024400c49410140085c0c001044055440d001c3c030200f0318004400303042e03458080015050803000100020b4090000410702d52094400054010401001003204000340c4010401017080745643d0801990f5540701d801150007280c030b64407403c1c1c0e09800641c50048c0f040c407070400075807030005c52001c100c0190101d021007809141d01c80522603200c8006000d00700340d240c09581c1c2e0903100c2d60b0780700410084e082c1e00d030b100c075040c86108942c400100e0700260170001640e0301540c0250390f0380380c070303107000310161003401e08460903502140050144564442c0700301c000c9541d0a0a0011541d880b1036001048034100880d00d1020560a00b8582503421990050341e80007500400040c14a0703030f24103002010750b00c6450392118001c400241805095040a000d040d211207120000888004a82e030020303070060030703840c068410b4040b4070005955032004007043e030707082d55540b00a1042c1113080c40e01400c4402050001c07201440301d0030f810300500780708241c4036040751800d03070040c0040522 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 176859811 1250 176858561 176858587
    0xf050108030705060610090806070c1b0f030803070212030906040213180212070f0f050901060c020a1a130305010203070f0e010e010c150e030309011a060f0d06091d0705040c05 77
    0x5401b14541408025600040d603194140003071032180c043d41d01c403070b0141d04031441c2001c40000721034240c1d1380103013501c8400d019603288071f1070700410390b688901256600d031942c0c8002c1e890411507141310200c0800c00030402c0100030004c41c201e4022442561460540c0740288166826506c0d10030050175001c40190301d1801510304a44290044000041a00d05143e2540e0001c04016401d420400000c000c1c1e800800c1b05082000c3c415004092354a40390050203031982c0019900c00d1540b0403c6403045001c2481301d8150707460741c1121412482144a0f8500c150742e454070394043e4004036080b03800310b603080340985401c81c0112040c01501d039059481b580c41090100c01500c44141d00c40c02941c3c6605ca043c0c000c0c0c1c440c1042c0c071036200340d801440b0080d602c9280000009017920b48400c20984190303030710740450a69464040a645010051000d100c0d00d0b100444040030003003d0302d61000c840c40d41047c9104100040340c00d00309813400f00003000c0d50109900c940030700c0141c4108240c0f5000080003084940007401d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 176861061 1250 176859811 176859829
    0x70e0c270d050607020d080c0c030f03100902070c1e0503030406032c0a0c08071d0702013e090904171b0706030f150302100c0f060f0501080307050606 66
    0x800400091800407075450b600e1418100b1142030f005a4401040c1d0030110b500401314503488488410b001d80f500d65282c81c519100d0049000148000c2008004501d15a4aa80c401c04c06030800b0b201c215182c594a0400442070340c01d03841184c465211510080c0c0b4204042d40c8000d040c0c0d04050004c511f49841e200044004001211400113200104402080324520502c600e10419850000420a00e03640341040c10b00c5944d958043e00c40303980541c03003c0040080340806a03500a6840e8000d0300d9030340c0c80b08816400340050841450100c5600c3d01e01c620342000303044500d850034100211091a9124024401c1454441c00c0c1c00030707500c4950800000c00040c1c880e4400f00302804000d038110700340300d2101001400d000b140403c40140703030407078041849221340c0340c440c28088541c024021300c9907004020102c00c10003500c0c00040d011b05100c90740a5942030080e03020000d0701e07034800f01c60909c1c604142014001891a40a200480b80c10301e0000158a0070010a4401207070708100503040d15100d2230300300b0041c14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 176862311 1250 176861061 176861137
    0x906042a1a0405120f07090518060702010609051305060105090417040b030609100e06010f09180e0705010804120c06110301090f0f1503080f090a0602070e0c 69
    0x20500040070074140003198410841c88104505903880b80d0500081160403c4404d00c0041154003100e810840d2201c0010558120b44030340300700040c5d80c3c07120744020612000d41c0140085c0380c0b051406003c0155030550054007250f05c8801c00300901d49034100742c15449a42e001c7c001d4850b80c4950b00500580c034010107880d420a1240101c0307007105a140e1152441600668400008600c3c04820040c0e281440110b055014808500300800f150610300605103420010f06068100b02510946446090050358000d010302848030781000e0610110301008007408015210480a00036040001a13650091100ba4092540440902c02014401200707c940c0140d00d201074440c13584034454080720f000044021070103000381c0003011911218148048056541c0c103280c40300110300d0450000500701d801091102901e92001b2402d81d211801c030384c5040b103405866000d5a02000c010400518a90005080812110300d51035080d52543d03003c41d902410b0150900c400c024407000c800c81044240901032216005d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 176863561 1250 176862311 176862383
    0x90e0903070212030307030b15040b1e04120c08010e030f07030504031208061e0a12020103232a0a050c01020c0a152a0e01020f0303070c0308090604 65
    0xe040b5000684602e007500e03058200d0760000024043c8056040c0141704c55070750151107100003010494080d0009119620600c22140400700b1003d01e22100341009915103840e98160a031502d0b1103050a4540050b4260f044543d80c0c0521400030364240e06002d0201207450300740141d410001247d01d507441e0b035800000210208002040040001000b0f0007824848034516652498245810350610461446207032031103c0840f86c0402303540311940c400081d030307040d1030003c101110903a8040c401a0f0140035412112020100f24040120b140094115403510500034144225078034510070402589016103011080c1940d0810002e48211500401c000c0a0304000c03440010710300000f40724070604050400d40b00b10350002042c00d0184031013020f406841c90001066044107118940200c07009070012100000c070003808a500039a045981c002e110410700d40031006c00740c3e643c900d08004010494120600110f0205c1c10780808107628020000320140b16990003a0403260909410080101111074024400f2003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 176864811 1250 176863561 176863567
    0x804030f0c090204180c18140a0305030c0307030f0516110a08030313060b010f02070509040f080a020f0d0f05033d05040b100c0f02040f02031602060c0a090e0903 71
    0x3090240c2c0c40100000c15441d031101c007144100071700c030209896111424104028885078288807a00080307040c4000c5170640c000c0d40f00800fa0f0a03010500304444c07944080c015003c04030340c1c6604854003000a01c607441c840e03139984400590640099981b40903000990711800c041101060002e4964aa004804000140f040074010350703c0407035614503402100c0c2000d041f603802601d441041001d005007204c07204242003032140982c0c81480203544802c06d01ca00741c42006014003003000c2c0070302d01044040c03180c2c1151115980f201da011000e59030b1001310914145500c07440c40f644401c144140c01c1134000d40d60a80c0e6613441d58590b2030042403a6903104209461107031074804101080e600141e40c41600e0b00301e902d401c000e41d5180c00100021989003a4003103008034003caa04035900f5500905111031994006103205102e804c03800802c0003410706140c4072062620000500c01c15031410000003034884c2c280ea080b500242d4810034104924062800d01c1c90209094903014410000c1c01d200c4654422004405c60342 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 176866061 1250 176864811 176864819
    0xc0f030c030c080a0c0b06060301063908030f090109080409020c0c031905011406010c02060f130b03040521190c0516080610060f030b040f060e0105030c010c0804030f0c 74
    0x10950b80502e1504c001310b003840d41e844003040480e0710210f81c03080040341c0e054111b40c5060703c080c09034460844548081c0510f40c040980d1455610b0704580400e41c18a8185443e403442d24101e0215882980c41201903031a41c8002002000140650780f001030380819510700f01454411280040d4004130030098840c05012441c80b0745850800683c8001c0c900e41c031500c1c0340307201c1d581801c50840c0da01851540c0c40b49110010404540d8110401401d450b9065072042d81d12060707403100c500c0a015582d100748800420180025000b06d42c400614040c0d4010341c10744400b244806042c07201911896440c0c410721100b40031510124030083d106d00e04172142410904140000c070380d1003034100040660519460740c0d90b007206020f01001004002d80c0280741d818440c0959041c0768000c1d02514001141c01d0800d52100c0402c040c43c1c45540280c511180c3c410402e2001e1034580b01d0b0130120301c60034000d05010b4800c0818a4081c0d6101d00040300304a5040094145414210389408032601200344007a20001c0b5402c000003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 176867311 1250 176866061 176866073
    0x90c0f030f0212090105152e0908010f23040b010603020306030c0405010b0a0201050610140a0302040e1524040b0309030f031f0f06020d2f0a0203060105010c0f030c030c 74
    0x78400d1a01c8000000c0130b00c0c00924441c3c08442d100c2007d4066204024441c41d551385002c001c001c0045e0010945000301a000e80840300c021954000070b00c69428030107a98a44059a000070000861005220b5101d00095210b032200c03510072070703010f0100c4100000400005009500443e003102000c2c0c1658101d00c6500081415a80700f80d001000d04100015100303403007542845400c2d000310044a0000c18400c1c1010b0081c84155003216605172200d000408140090003a03040350000d211580640a031850720510300c8190444100600d8021a400701481100c0540600c3c02074440c44600c0304a1b042904208105c00b4541000b42032050300c0c4010414002d01e074003140040d621600a800801c96062012846448020356590000707a90394046101400519008200c160622a02d031900050104055100713215008240d0b01c85a4140e02030592030020f07010106007829128000c0d0105c03000c0380d07600e0300119814995490040e1000b82c07070004907000284510b680581d058060b01d00003180c5400c0d52550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 176868561 1250 176867311 176867347
    0x4060609060305250b03040303020c011803050a1d0a06050915040b03150108040b040f0606031421070c0e0403020705150d051305062805090c0a090c0f030f02 69
    0x3075803650700040300300091440801c0f41081c00c0c446100c80c020305900e804210003242c00003401c001d02741074001c00d1802c1001c90940c000008862800e28a0310000c00707904014047d64406041c03440007030b003041c822851542008100b101c4046d806413083c0e0445160940071182c1790444c0290551000380b03000240200880100a440030f402e81541d0385d51740b41400344105007210100c40c405418003e42808000102e1500c1c0a4142e1064001c071103010b4904191400000508491300018500cad4140000030140c144001040490902044ac0c07038040740d0710400411026000d200401084004202030a001c4411039001050b0031a1003801200d0800c0e80f030b000014214040c0741c0040c0003034800801c0c0708600030000d006680d040740c41840132181c141115124962240030091504c00e40b085210040380421796004034103c0b809010003800c002508002e400b0b1512444071480071449000400b801280c8070145d48a000c1c2d152040c1c1d243c600d075041e40d540c1d090b8050a5092400e44070b1580c20f000515100184c04a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 176869811 1250 176868561 176868563
    0x120f0d02160608090607030504060e1f1524050d0c02010902090105062d0d09050a02030c03030a121109040e010c1214010509130c080706090e04050c0405040606090603 73
    0x260505126030010200491107540c400000c00c1070140a0019076640843e810342c0120700384c98081060ba03158180280a05043c480360b9a10380700300d180681984010b8009200c180d210304000f402142c1803040811142c80b528054010888840958882c205185010203601d00c07807941002414205034407860300031540960390440240c1d454540000851070003c0c869405420122400381c182006e0307000b40d4648903015886034210750081c03029071058213076060644601d290106c00038044445a443c00311345424031050120300910600d500002076150102c181c60481445540300380003124951030b010090025000c200b42e070501c0402c4143d210741c940e40241c0703580c1c091030b10010a0a90118400420210412030b40e00e20f4076150000504143c6010501141104d0302254000490b480700f89006c0d0600106e0003000303210841c1d01c1d0380000d40400101d5000e040741c50644980c40803a9940e44e22840f0301c07000300c500600a41040e0403032840362a00c0c0d809640c1082c090303e0002042c98403880f80c6070440e082d42e08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 176871061 1250 176869811 176869813
    0x120a1a15070b180a030e0f21010e010603050d0c0218040b040308010e01050d080306030325030806090c0301060305040c0b1321051c030e0a110405090a0c05120f0d02 72
    0x14046090061604160b90403443c00f0408402d0081d010060a49074204110014104840784042500c0e40d40c03001409110000300505041c40b02850801c920a0000e80c01451074055080c00807113015042c040c4148800c07a030704100030b48880100d014003102e09034080d940c201d0b4030803048441c070440c800d100100b25100d188103001502150515050103410322300141d005907454a0010014000b50701c6880303400b01d0403540901c90325103030345541d000030b4154040c25000240080010040240e501084411645100d01a0306c41a800351241c41c1030000441007210301001c1c082c820001002414400c0e800598001c0c050035101d001d840c3c95502155041c0d20081c95201d10030300f40706c2c0620003446660071299041c03101c5410f0500441460782c1e61500c2d0403440490006400300040d9603203c00d4044d07000102c0c01d0b401c10050314112541d5251108a201c0b034002e107503018524000000d40400c1c000960b040c000d541000c480f0200034030b42020040c90b0256000440100d008100c16000c0c070030300c200070f52020300380c03590 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 176872311 1250 176871061 176871067
    0xb16080c070905070e09060f030c13142a090904080a02030702040c0e040e03040806010b0a0c15020a030b0f2b020a0f03020117010f0521030a0804020a0b120a1a15 71
    0x142001301c0c1046c0504503603c51000c4105c1c1505a503070000d90308980240c15a40200c00320f849a10ba400103014100f8400703d407030010010031500c41196107000d011800840c2c01c40030351116024440909000700c030038454000c031412000c2400f1841d16005841e2100035441202e150203040c4d40418150340c0c042c0c20000205400081003850f03843c00c2c0c0180042800920011801c0c20725042e001991114103200c0e101c61220001600620b10348030f041030115282e00011070b80040c1144183d41e800a501500403440082e10f000e81400403850b0642515040304c400506030342c52403a100c103440304448018481403c2d1380580100070401a242c1040840081a00400d881c02d198035500015000d00070410703c207140c02c0c00f4800140991109860088107807442603640717074607401422711580c0ca822030312261420340f48000720780c060045a20015140c8210b100761580303006295541b4500c1680d00421556890382860b0b00c000445001c5203030f10055a040126a90901a94409010400032401c1d5200c4030042c170400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 176873561 1250 176872311 176872337
    0x4020d090b13050c13060e0705040e0c04080c09070323010e0c0906041a1b100b01031104050d150e100e030306090c0319061206060b16080c07090507 65
    0x1500302198060084038680391090040e60b01c0d01d03143c00c51a184d50b8403850200c0403d0706801150f610010142c19100c0005003141401180070708660010700c10948101d0409001484240d6a40c041e1411507468000401c880c4028004000009800524030810140d990302103241e83c207040002982803204100c8200d07080c0d4144003420002c0a0020f0108100c49404c01040c80251211412101151205000c00c0000920700c3c510550358826246080007516840c04070361000900881c1a80146040d0f100400c010400507005400b0358980d01042c1140410600c801c1161b4104034402c549660311031703c5e019100d1004400440d08032060320041c8525540415203c030f4001140e4170800301080106001035080d4908800081c00b1823500500700c3e14603950110118550300691080c80900440c500c1d400d00207070b034903a0703078010300d0481c10603094070307440c3c10a100043c003003e0b081c1c02c4031947c42e00b1042030801a0942c0c0c8030795213294401c00c490007803849031400c00a071102051140d1b070701032003c0b6a0b581443d0344003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 176874811 1250 176873561 176873573
    0x1e0301110c0120030f0a1404060b010e09010501091a0c070b070b07030203090703060b040902090403020f0c010903050d0c03022e0f020c060106030c020102040509010806101a09130b04020d09 83
    0x5861000d05040d000400c0080c0380b94103100650782e010007905c402c0302040e650645164090600d09059400301c03101c0d2024002002016000800c0051003a80c4070803500118004014000e0070a06c107043c080703084114240308110307088140d0903c1100c3d0741c81051030122141041860018281d0042d15a043c1c0480d00c0c03403c005032180e00b580c02181c50b03d0250706500f4140b410700e46075003a5100007030480fa504c6440078050740340d541040c114150002c088421515003400d010392140a01c1840546a02805103903504946c05011140103aa030003000511000080f410155966001d0036000c0e41984503181c4c14492807a60307503981920101604010030b04400f0305100c140c0035a181d40452003941b60061001d0400c1c200700203103482c1111414607020a4805d40640281c0c0207208a800554002c0004800881c05502c009185400f0354405808100b06175581c1a0485aa0100c041c0f03125925208000856862800d0040030081040c14407000900c00000c10000c0c0490313000f4400c4c80b18a03900c5407004410700c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 176876061 1250 176874811 176874821
    0x121103010e04050c030a4e2a0b07020a15060f0501050a0519050c03070302060603060a0e1b04060f080a03090501140702130e03041710060308091e0301110c01 69
    0x10244c0c01840340000e42c0e42c0d501c019640941da245010047c4640c801411141039010381c140c01e0305e00e4030040a0440320510150184d2803a481c542c049103000c412010715a91500b402d110207002c02d11500c900e0015941c3c1c4c01080000a051502180704080c20440810140d1b041d03c0017000500c1300c00111355281244272aa10350b40740d84441d0601c40144003101116420070201e65802c0098145003400941050081c2c03a58054031041d2107691001060100426400103070a81c0030b1641202110b03c156606a030940c1903503811071120000380c11511700407001c2d88140050002d10312000b00040384083d1145004000680d8990000c01341d44e001d10b000005258002140320080c00c070070b1800041c0340400100d00d054512620b40d000380070702c04155074001050b01940c0074040e00403003442500d64441d526400b1a030407000788180160789001e0001d003103c00c008680f09490480c0d0f070100101d4103100d000400c0251f80503001030590381c004103441b46004666001c1c440c0c0c0007019030600c0f005860390031401145007124 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 176877311 1250 176876061 176876083
    0x6070b06310c050f0a11070906060309110a080c01110118060b010f020a0507170a1b0e090a020d03030506130903080106020706020303091c021f090b070509090601121103010e0405 78
    0x142000b138030704070341c80043c1101c02c024918141201043c0121094034900b4840381d200c040060724184011441d507506800800c0d145004140007652841400d080021100040c0b040c1301c0580c1c4003541d901d9255000b0000d1075000d172020000020305010f0601e1002d01100c3e109001c503416581c82441078865030f001038251800c0c410300e20090805100c9555140d980355014000d40807414941020003074200e0042000d10603040e800140005003006000142c80c00503054000c071014100040001030400d440046c060018a40003440902c0085041d24144c000303181c003130516070304a45000081203000b092030084075040781c8282c1e0f4000c07056241940003030401d81b960308844c2c01c54108200340040c030040020012084403555050310520344026000742d1a03e1460046141a10300c02602030401c0410f0342d000d203920034000c0c1c00e802e042c1d680d050402c0300c0d20302c140c050f550b41c071601c0400842c0c02540f1520b20800c004c090301d00001800201c154040300729410983c00361540d1100d18040000f00305060180540079 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 176878561 1250 176877311 176877317
    0x201030f0207440301050907021f020f0c0303090d0e0301020403031d0d1202161d07031512080306030705030f03040306020703020709020307030b0301050f010506070b06310c 76
    0x2010660360b030440140541001d07141d00d01c4020210000760700c50710f4064050074000c2d04956024203104a800c001940092044507ca501e4280000349158000b02c1c1c414020410344060907055141c01c0d0249009401a03031a0138006074040c410540d0b007880400c0110b020b00f414100418104c6003554009261940f20140c20b406030f40107010400c0003940060180d0321810b4440c111002554040000c184582c0c039114015100c03c00340d140c00c0b140f0580104080355040350b400c4901b50065100c601c80d4030241c4007219900345c8111103070002913545100b0b600082480d100202148206980c03000c01d400d031a0014281543c4d40b000010910185217800c2143d01e00800042d0007a007070750342c44002e0a94907030249100280000390006902c108052080c4400300c06051445000c5469061030000200104444400c01d40603601e0040403c0c40020b007807143c6030482c1e000910203490a015559490036210303000d481c040c1c00c040b0110a50000d40c44901c80391035850050240207800f0501031046c0000d6881e240d541c2c0042c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 176879811 1250 176878561 176878567
    0x101a131a0a1206050628030507050102011b110a050607021605041b0f051201120b1e0109020d0605030703030305090d14250f0501021305031209040b0d06090b040201030f02 75
    0x450300b4094642c44002d0f030404800500d0744e60b0000420048880ca284110f0540305805106880350101c1c0c050740141c90180b01100c0b1610b4a520040e400c03030300c140c3d0904514600340400b0050491061b02585071504020040c0c400190050361842c0c41c101c826a007041c0035800c25000c0c809201d500f4030701c500003004102d6050102c901c42c62001812004014400d00400008418010001e4046c0c1d04503240090200a00c0c000c943c1e40e0300080d070321f803007003003804640b0406003802003039a00d2481c281c00141c140805500034030b541d203002c0c805d030001e40c00b0400810f4030a44862002500f0340d07062124000a5010f40c4020401c0c0c036000818a04002c00c1c41986828449031155815080c403002c01512064001415406042c00d1501101502c3c0c05203a200102420401c20003041081019006440511070000750008000e03162810181c807440412983c08030404c0034401c03105075241c0360300004c58026029049107040d0901c2e86500068803c0140f0540b0960f0861041c0801c41d6072501c2040000f00c440f40003142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 176881061 1250 176879811 176879819
    0xf0d031104030303020a090b07111c0201090506030604060e01120c060207032f04020a030b03161406211806010b070209130302010225050106050102070305101a131a0a 73
    0xc2600403400702404050307010806600460084000e03001a29031645195158012403805008480805014600031032030130f0300418480411181d09403009905071900100c1c07070700341014082c607604000e01a070752054403a20005038250341108200e0107045620f00c0c01c85142d200d4100244000e1060340071700115444050f04101048842c0108112014415510300500b042c00d405481c030f4402c9040a2940311740300003082c291150b003680c422100c280f0190283e030711361100e03040c070484070152a201d000203080004403141c400b841c00074000d09200304803620700c0d020011046880301900034100e0b0f0700840302d200103140c041400d0302045602c3c0140100100185005056804200c443d540503001c0a0f001b41d850015008149c000c0d010385902d60503024110101c00c46401588005844000040da825441d010012a1551000c100c1c9001c1d41d070000c0081800e1003101c010701008048004800b0f1285152603051022542d070106c04001070000384034003160809608440d44250085490450710404039064204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 176882311 1250 176881061 176881091
    0x70b0402031c090b07020d2f0316170f0607090612021c0e011e020d050105040902090408130b04060f021c2316060c0807170123030f0f0d03 61
    0x300503507050001c2162030b00041d2012600164060800508e11540c2c0ca0209502044160200c09410041c0e000e441d03200b1651002e264071352542d101940b84a41080750705102060851042e1382083d02400708451000150002540c2050300507540c40c800036421070302c2000000d030311060000001101c03100440c94000d03440112480d606c400030f1101e00c02c0e40c4426030b81014002c01e6110000302030040001e510a060f409003104000d602055100900c545040004100b0342000c0c880d5041c580e070b020780718110342d8a0326143d082c05508a640482c1d9840c1c404c5201151000302d0b003020703100030a00d45c0c641155030007032014045d04201000c800758000d183d8040c030721205140d0114070803011700462480c8405150420b841e1048520510822030f192040310031448040160960103144d0502c1c40350349042081d22050720483e1031a480984002c40882c01074014410a4002c1100754880000001c1d00000c0c0c80044020030b04282141582d04482e41101c50110110a030511007400e5681240c40d0402107854126204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 176883561 1250 176882311 176882327
    0x1912052401020a0605010b0a030e030306060403020420070302010902091305120a050d02070f0209070206071409060c060f01030209011202090c09270718050f24070b0402031c 76
    0x28208805103000d606490740d00901004465541100c02400b480d0b85881d0303d0f1440b07900c15180d0000003840c02c10100030580000c81038030f000d0303030004000510f454515000c1101414400440d80500101020500c072100500300091948510a800119100350a40100040407100822180e9540d80072071a1400256001c505400607820700c5142e80c0d00d4104081c42105e03540a450386460f807841c400180380091107500c42602d0110741c8200c844545036580c01c01c1c203d03100e40003501c112000c0340f424200c644440c01120050550030802034001b50a080b41a04c0861400c0c46c10b5400b03c07002c90307000c0014015418500c8803d0301401240740f007026803490644c04030303820302c0e80102038540c908008203160313555580d00714000182144501c000c801144400c8901c0a59507819122080450701c4440f202c0c048203841640340f021520b00402072442003210009206002d48074620078600d2401c0448951154402d00d0054180300c1d025030041300c124a040d00c140b41c80c10036403551248076408850350031040c1076840b05807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 176884811 1250 176883561 176883601
    0xd030f0e09012103030b0a2d05060708070201020a0f0609050c09090a0b0a090b0c04060201060e100303030e010f0509101d0c1e0a0605030f0a090c050411040506191205 73
    0xd81006800e0908045001b08011003400d036100e0182c00c400210309482101804030384c10703400301c008070254114041c4441001288507441d000141440200301040390880a00203490040c01a2011070f030031075913210400303100f50701d003207580c00e5582003084103000c010003441044840c01d6545411500b03000441558861400c0c2c0001c14008543d000035403507485da60850707060070303910024a0030349040208400860b41c1060043d0401580b03800800507034a401e4507900f80c094420341c00c002e9402420764900714044c00105038241c45a64a440e031001c5010384c14404c1c148201c902202401d040164100020305440300c501840c0060640b0a51650b442400030030018112a0b08540683c111103a031041217080b8191030390a5984007034200000591540c01c54000c2d031203003440740c1c40010b0315130710b00703500d40200c41c4a9800900071452440d02030281d41400e0b07000c2035010407018840c0d81000d903100d00158441d40005100c3d005000040403400810b40c00c1818059100c16034101448a85001050b0400c0c41e0202c0714 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 176886061 1250 176884811 176884859
    0xd1508100c09140d0b090c0913080313081b010606030e030708030a090507091b090501080f070819110409051b030705070f0501020c060907050409051507020102090d030f0e0901 77
    0x2440c14440d600c281241c0d02d105e0b400b00c03500c1d210f803401000054071001d40d101c80300c0c0201000c0e000a8100207054106481e49035000c4106804c545811800b00002d2504800407036010030204000d48a00407592114180100080008905a0305080d001801d40f61141d80740e14645e401403043e64002a00e510a03654000309411000903025503505185180604c1035100d6117241d4600b000544080648414102034010981c5944001c0b45e41c40004503070b074a00c11550640c0040c810310200d00e1051149044a40010003c0d1103803c0b00076510b4050400c944640044000c0700c00006410051499a801100d5020200d0441c00000c0f50000401c4203031803000078000420054002009400c01a0100e150400103070003d008640360075905800a5807000c0940e031315111480382c100000b0752890540a85240968040094483d10600d0b40b01c0c0c0111982c0a080002595000e010702c651580f1008804140b4074002e5503110b4000090300000b0341144a442d203d00d0140b041c4000500084e400150200800e5082c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 176887311 1250 176886061 176886089
    0xe010504090303111204050d05401206110427060b0309030c0c04020c030a030e070812030f060301060308030408030403030605030105151804021c05030d1508100c09 72
    0x450b0480007010000c42101d580e000100d10881d00d00310f518022481944038204942030700c840c0800540d034a000d5213802d8a00c0d803a442c4441c42010740c201709070b5012104008100d42c841b02c0242291503007601c460f0802e001c4e44000e11342580600c990b03806041c88000c40802c2240c40d0074142505134481c0b40008403c0481c000c1e00400340c20364018180d00080003410002d0324907441c1e0510b00d0704552130b07510440a9994a203d0b003901442549130501c00c68101a40f401c009501e4050140782c11340c090140480415502e00554000140c2d48000f4425001200c0c0040d070f9960f664681200b07a140503c0c0040c120a00a0789407003030900c0000d0040b02101c1c2c0141d0882046912035031a480c089021308006d03003003d42c041d420501401082c90750700c1802540d2020407110b840b4210411103103d84918001c4402a50108204501d1050300103900e04c0c42944902844c1904e00d4030000008190944100060340d0304c03003009810301002140343c20f0011000c2641c03285130502140002c6400108600dc46015280d1105110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 176888561 1250 176887311 176887313
    0x1e06051509010e151c120e1e03070503060703090b0f060907030b040e07030c05010e0108060f0603070c0c061706030303040c0e0601030b031507030b030d08070503040317090c0103060b040e01050409 86
    0x102100c3c0341e41000003400e480407440c0c48280c03812052501101182c1e074802c04481b80600070300542e045030703070381c10060051069178040c15201c4100c2d903075010110f80c00d4045e10070042440e440c00e111140c418022b90720301042c64079a6150100e41400c1c020017064151683c82c0a200701544c1d401001c46d0820b40e5071a022078040f5200703001030f00500c2e60124010051050b944004100a0a003280714102c40c0b09881da04a9400c180c0015940d0100840702d86a000e10030300245142c03450200091600500320745420f80c419107450742c0340d06844841e60090408150840740c600e20110440180d584e10036000d60156045040c01c2c1c3c0d1705a078040075409010540e80802d800914230743d1080d881090401001801c80f44170915010808140074001d5640c480080d061088009103420002118580701323030556550080c59071407810481d2546c10141c012404c02c07a1010701e0f07080c20b000d0010600e000f81480d002a240c84000c04001408441d075a600a000c1081c050104020040400b00590304441082d103010454000d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 176889811 1250 176888561 176888581
    0x10e01080a0308040c05102c0d12090b0c01051005010f0c0f1e030e040c03020c0d050a1202030f0f06030105062101020403050f210301050f010e0301091e06051509010e 73
    0x458000a8006d071610b01090311f440e80c03002c0080f0855030104140081d00e00701d00c207110030042d00c840708250008a10300b0307408001404100ca00d81030a80390702d014450780f80c450701a500385500c0380705110103da44810900514404005080000b04000d0903c248511860b04003e0496425010003401024400d0300b4a020320295215448038001c080d41c00c40030b60002c5140c09440034200d03c0400380521b207842d5498184074024801c59100a40500080c035040d6050007040ba440c0c1d010000c98003c0120440d011054244a03001441c010540f0b2042c400151401607540b4104000092055100e0ba042c80148a440d444030340654220848060030001e80c0f07818030a03201e01912031640002c2c0603108560414000c800f011a003c4081001d0340c03104101c2c400801651070b414042802400d510043c0385e5001d4003e5800f6044a0111100160020505090340d44403200300c20008211100000781110500b0108109071042542c070a0383d00b03454001604016002c540c0040d014000c6038050000c0700d0106550b024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 176891061 1250 176889811 176889833
    0x16030602090103110f0a02070b0a090b0a090b041701150e01300609020907021f05040510090303060f05041107021c0501060305030702010801231e06041d010e01080a030804 75
    0x10030b00c00d1141e40c9641054031740c00568040d001e080b0040c09540b0000c9105203e81048880381229030f074800e80da2500301402d0f040c3d16400a0004818400c0440b00080c0d2011307041d000d08010514201c00c0254070f2881c0c4003480c01d43e032501c0401c2544a50048080c406040c0b003030f65850548000c0f41010780a00e980c944000b02e918058600c2000300d0100e481880c0800c112742e0402d4040501c20788207001c054580441c141c2c1c0d56400710b0100c1c5003c02504202c00ca0f082031750b42c010380e40180120216492420500d2811048903000384095001a031200d80c14000c4881c88210708c1c0c010b05c81610304100145c880c01ca0000c00f4003030b91800a1094031444000700510032180c000d00b02050300b00000308005a036038034045640750302c28007089020586090000600080394480e08041c040200002100c00044a040188808400e40c94402428078003a07030358000d0725010b001e0f10142243c0100b004103103001518245409805074803c64014020308018010b0510110701850007a038541000c480030f444524003140854 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 176892311 1250 176891061 176891081
    0x70b0d0b060d02030a14040305030f1003061b02010506010e0d06093012050609070e01021c120b030a0302030a031512120305090f210919080f16030602090103 69
    0x5100403480c03a402e006140c1c0110300441c1c80d4003081003003031045510b010701d0315000c480c0034001c01e00c20f000144250800c0a0200e920071414a800a1300c03a44075550700c401c540301c515203705c40c0c00d070b0503001c1002c180d02441280e07004482400c200003080d200300300103a08140076620041006485d88001c00c104286010602e080000c600382030351080403d04103108001c4050502400020480320803004480018415140120320290402a082e40c420805544403030110050504503c1132085545031a10562110b4481c40059500d240000401c442c00d641a00c0405441d540700717401c2aa01c1000007500001207170310404c00b40c2004680c4c41c00000c0343c008103001e0351b4010038241c458004070404101d90001c0c00d030700540b01d82d28200003a80350030b115a69294401c0c4e05c11000c1d540725590342c03500079142040c25017030600151010703454082d842000c0f402140900d8a0b81d00f0f8a02007001c18881e50301d0910401513002d13814002494034a05229501d0201038003840f0140c0210340c001885007840e4401d400035401c0c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 176893561 1250 176892311 176892319
    0xa03110309030d021006140d02040c0e1e03120f0a0c0303140103061d0604020f061c09140d050a02030f1803070620030403080307080601020a210e030f070b0d0b 70
    0x20b0015040041d403a400e05585c06550b1501e000320115070b1080709189038003448406807001990421a078240300051030804049000d108108410441590755014044216410b40b9140e00e281c81d40d817014189403829644664440110034441c0d00019020502070b01c290854038940b80e24140030504040e00200300d0b4034200b000e8100d641c00084288005500300c1001d00c82003e05901248071a060501c1d00c40300140e4000f5071194580e109241c007441e03c04007a244845540c0240817489406a50240440f1594442100c040c2200c50401d1000c00080c80b0089016425040a528103200c00e00c00944030711400798400002500491030726a0300c507070441020148480501115030751500c0b600c0c0030b40003030781d101051140350142c0a400e000908003c82502d04403036100c1032550460f111500c05840c481001080113046104494064000c02d2082d20503490011029944014200070031600070100c4421041890080c3d209541390300e041000094040d048030b601c14212919400c0a0f0300f10700151401a01d51688 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 176894811 1250 176893561 176893573
    0x17040b03150a240e0103180605040506090a1106070c090c02061b04080c040b030c03120c0d1d04110f070c090c09030b0a0c020a0b0a02090a06020606030a0311030903 72
    0x1400991400e100020981140d141c054550f80710640804000b00c0d00c4120061144003031540105400350012103035606050401141d06080e1802407842c592014a058074020707282c1040c0400c2c054240041d5810041d24000b401154480344c03a942201d13141010303428040c15000400d001409102840b01c009000903020600402003c450000d545180551300e0a072191011a1084402c0d02483d0403102103421000250204c91400ca0400c4010100d0006540e01070254900b10001540c00340596075441c031580541d01e0b15a82141300c11880c0401c0322401c0c07014030600703015107054800310b203100381c07100b0748103c8002c506083e032021000c01c81d0040e01c5000d0018200424a6410087c0090400054034516a8100002d24524008417010340703072480050640c858a001107a25626030350402203050f05180112400e0a9240d40c0d0324691120132540d040040f5808a411040c80c0303060102000240070910081040e0b00305040081d45400d81483c00409000080500e134048201c10300554100010080549170 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 176896061 1250 176894811 176894821
    0x2070f0f031e020c0d0c080102040b1809060a090f090b070e01020f01060f031704030c0b1209010c0f050a02010b03070306091e080f0d0212040c050a06021917040b03 72
    0x9180c61800c004038089880070104910064441d50715501c1010554020050403001030107106032055140340588a810b00240c0103c0c103140240010f100170004010419070b81c411001e203c1000c01c02e4104402c3c4983ea4031401e1006981c0c920544800b620182c0400103a4844005007800041002d00001820100c02900308505c81b178000080c0c080441c000c0e0240c1d011080c4004205c2e080311060700441c5401960f012061006c40c10300720900001d01000c110b01c07450561640c843ca17040c4070340c60b800b0301940308002400180129403042440e400110540c000d0040c5000100003a19803642c0d0144ac45c02c100010a0302c0203441c0c0b003500103040e9203d0140c1a074002e6a1a410150081d24844a003600d812040200e007510498140303010742c1c0700d2074021103080d00f019a0641c1030703a21a44030405035002c1c00d030244120341c4241c184038130241c0244c2c411a440300300340e45007109020144406900c40c0c001c3d904424082000650059200c3c280300760b02c182c00703222201d02c0881c00c0322540129005201045c0d40801000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 176897311 1250 176896061 176896073
    0x130b070503071101060e130203070b0f180d030909050a021c1d060c03010e041727010c1e031e020303010302150301050102030d150515090a12051e0102070f 68
    0x140565100d90320340110f901040560b40c265074051140c000a100c0e20000143c80784200c0081e18285440103007651403181c0d07240d0046215030404040b48080c0e05000070100b052100c048650880d51400780e0314014000e8942c0c8001d000900c4a100d0380d40060b8840b0002107032410b050341101d001c030b00780c0074a02d16a50107010040c07004000a03200207807900514203554204110001e0740611800d49c60803020b1641c0c0c01e086c255030400c080908100c0783c520444410044078668903014294201c002c4101809060041c880403416448803000c1a05000d00312204d00c001c129440f0314110081280070715080016403500d801c032201d414a480c01200506c2c0c0c280a503190782d50200040d4101c0e8001c03510a00c0c0d50314107000d1800503100a12a10340941e00420403812b4044450700310f60ae100c090801c1c1c0f030240c590340740e01181502c54524604100aa0700117a4060989003400e44030003e001882c03030401402c00541d81d12030341d0b00740c0440004030090350840e00d22000d5109404881c0c00e140d000c0120342a814080c43e041d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 176898561 1250 176897311 176897317
    0xb03190303090c0e040f0321091109220f02060c1f06080c0906040b0d080a12060b0301060c021504030c0909060f0e06150d020a080309030601090606020d08130b0705 72
    0x1c6803e01d01c0c010300002e40100700300b6032600558001802030f800e0031003541c00b03941001d003400c40c4010011521900c0008c50b00c01d07100700c94400f8026502809503004560810620a800070940c41d1034241c000c22101c0d50740b140101d42c0180c2e0350b000d0340d403052411642c0001040da00808202e5030b407030700ca04240c066408400210310220500401024480301d61216841e41d11030305020340c21904204400c002441500d003a800112445001074500c1e1780c4030f02c0716260901e55a01100050003c80c00701415030200a0003882108024061030700132030b0a6505003c4011700f000707003c90010384100000107016048490340307002c85005562019501c18016520000300001e400341c00000c2d10b90900c4d041c60102005a580518522060100302504403583d4201400041c01e40d508509508a081c4420f4140143c5914042c8400303800100011030311890f03c01c081514100c0140c2240b54010300f891400c004643d000a540a8408120f09081219039103418400070703198960140506012007602c00c1c40961a001002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 176899811 1250 176898561 176898563
    0x8070807080d03050702120304060209091f060305160f0212040603060303140702091602101404060507050c12180d030c17090307090203060102010e03040e010806010611060a0b0319030309 82
    0x7600d2404810200030f03801c4450071640701015030020311705d11400c03507141c2005650042c1b0881005007821074032000300c0c03160602210010340e0611601000e41020083c0c003260760040010f403406004918040c166680c80e190000036143c24848170005000300c0c203000b07018220314045150700719030b100ca94030000100640520311080e00411010400b003015500c07004122540b040c1c000d01080800d86070444590302c2071200000c14421401091a0170580090070300407008080032004aa0206061600f0100304a07400500030703a06106040088020460002c203140c01404d1071803906d44d0700c8a4a5070790702141e242e282c800203503116500d10b11142c10140c1042c21400840d000344460410a41400c840c9921441001c040c0c2c7d42c103038840c081c10024545590000e40d8404410310020075540441c0b006c0d540b66030860f42090400500c6c0200502800d4020410140109694603103080c2c45a1064030039519603030003409901900346c80b180c0380d0f005518200800c0c2402038007d6902c2c1c1cbc0d00d2145080080090103000c41c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 176901061 1250 176899811 176899813
    0x11a0d0c0b132310030606020a150f0f05180a0b0c0a09030221010506010e0112201b0f0d090e040309151d0f01090506070f0503070b07020c032d070807080708 69
    0x80144c01c040d102c0d1090300143c0307415800905007103189071100b09091006a10041d8650340718400742c0d07130703091044c01481030105044c02c001c12541052002001e4522402217405140c0c2d100d183c131080030808a108507900311803001704c0b1b142d0325080108100d520401a4102a400001d03031821001d19411060302443c01c0c1461000070081901c400700110342c0c0d50300800580f400541a040c06052482c01540400b8841841c140f00d403010080d0009004d021b5008001140d00f08003500301010758100060000061681441d8050007022420090140000d0340c98000c4070032001c00040054209800740001c00050081404140004601400000c08604403000d01c010f21415840a80c190b6061028400103400c03c161205100d4038140401d01034290042803003034512050780030030800820801d0000344216802284020320f40d00d0071117006481c08400030b0580e0b000e540f20030880a404001d00d812118014107860480c0c00c0520142c82c401d1400400707800c000d02034024010b001455460003e40d01d4101e4549030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 176902311 1250 176901061 176901079
    0x50430030c0203060612030a180807030c08060a060b040e1e1015091a0307020316050106091109090a020a0507050709060303110601030302120304030c1202011a0d0c0b1323 75
    0x2014040010306c0010781e904154000c0c880700c504a405a5100c0003081604404e8014850703a8000041c9001c4040e84240d880f0344114100703000f1120140009540043c800000f03000e032619203003d07464244140d1245040e0210000041249000f440b120407402c01e441c89a00c030b07000d003000c8111400324000c034815050340014000d500d150305e5000d40d44082c103d0f07480c0014900b444a512800b0301007580b00800030340440c0810450b03030101e51040c1c3e1001d04024021800050b003981000e80f00e40481d4020621100550340c18001034480307544001c101135000011201c096110f000010050306e01d03010b008801480703405410800300b041d030550b80c001c5045901950724940315501d000d0845440784420b0002030f0040e0001d108400d402540003004582080c0f181c075021032655a9912800610500300c0003400041c0d444088400500c0324078801107181101c1240e914a5180b810354585403500c0c554402d800f607150000c144d00c8081141d80340b41e500186000c0d109405034102140c18042007071010102036120302440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 176903561 1250 176902311 176902321
    0x414040b010323091b010203030a02030414030403051b040501080a03030f110d020304150507050304110a0e010914010902090f090c04091805010c051306110a06180c090c050430030c020306 82
    0x11900d005c0c110107801840c82e5844d62038810002c1d500041084d0341c2141e00105240050400f00020300046005001829031400100c3d01c154543c14040842440f07282071400610010401040c03a52207298542800200400302000b0310029012032041482c42520200315100f03c41c03c10340045110380e01c20030101d0b141540085021041704c5041d611080054028000200001d424000a5011000043c50000c0d03d5586480004803003009820a82000391071340c030100546141c0040490150040f66000d6013440450307004500e1440d001d042c110312500c403580104041d036030100119009044490001e11500d0b20207a0304500f801c03c5040201e0340e542ca4031850b08601031240c8180c1740c0d240b070041408501d0525241b004c48031100700f4403005510740146025800041c480b440781030710703140015200001124003030400c0011803ca03948207040c010b003030499880605501004542c29540030400d50660422100c00300052202920084a0076034410b203526010305410003840602140308130101d4400703542d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 176904811 1250 176903561 176903593
    0x230306040305031909060906020a031506050a050a0302040b07350406030f1415030c0a080d0305041a0108070f091503080a0e1509090702030414040b01032309 69
    0x208450281c00aa001d002103000050745008400c910744100030013203081c0d216038403403c0031122420400c480d02da41c00100c0070b2080340c050203a000b550070303c2007a09541d01c1c60401c000c1d2582c030403240c0d150100300d00020168201070080d070565015251a41280d0b0b1941d600b81b5210b0001110b13a08010b402d002581140560b10031104228500038000b40d2042e428070740b9003042036014204007030b41442d00300e44038542d00440324078080c0c1c1c15216440b403424151901c00c6040500d0b080c040c0450031a8014494110180075003000002c11020406040c580001c1980d62400c12100c812081007214101300f48400000400321382c0000c0c00c005482007041503a41c11641ca0840c8400c4407900d0f03032114240b004481041010905020181c42e00d0328a0b800c0601c00c0110010000d401504c6601c4c00c4000244049980c0d40e060800402d055030100315800114940f908015118050050404806105a84841c14803405921035005407400c40900301100340340324060344d4184441e5004994201c002c0c0710b0282c504004800d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 176906061 1250 176904811 176904823
    0x204140a080a1e080d0506100c08030414190606050418020d0209070e030f060f070804030c0b0c0706060806061f0903140f0d18121a18072303 62
    0xa4484010700341c90a40c0d0762501480740c040341c41e45441e0b400002c01c0343c000c40c64150007081c03c102d20712000100c0b80340040800c50310202d011030b51000c002d1030700c5031540002d10920861f9001500b10000d4034400f29000e0f841c03490b1400da040d4417229041c410242d1010840244c0000013a15000c49040c40000c0e001e0107010582039000070044c0d40945000d10030401350401120b0726412403041e01d40300c0710300a902c0d80400e18000304c074403c0780c1456000d2020000c8101000b0340c0b40b0b400426628080c07036036040030386008201152a5001600801b024008900b180f080c64040390701e966400b80301488065a9001200c1c2c866104441c1e040c000e0301d12091010108048058a1003c0e011035101c03d0324880c00d42d1039180b480c04040c81544420300c1855161100c1010820046c0328640c4140d0310011300b9084101d040c3d5080015a00034900e608480d020000010017254000d1440b01e1040021766040d9146165460b40c200c500f1400349a60189071004a2511864441340200032050042445241d2100c81459940c0d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 176907311 1250 176906061 176906069
    0x306060d081e04060f1205090601060503130204140115030c0516030908030403080306010908030702150901021c110106080304050d030e060409020a050403020f0f090604051305100204140a 82
    0x10040c1280a00081c081001415888040e20500c020703001c01e182158115a01c25040000450104852400d1550348500d02d8004503062200a10083c1002408182c0e0b0710300c180680d205020300400001d034422020400340c3c0316144c000300b081c40312001a0305420400c402c280114084404041ca0f603010090082c082c425148859555807860119044241042030144079000c500f000100c0500003401001080580041d501070160113640c0e0078a07400162060040d94132140c400d410900400015950300807907040d1142c01400c0a07542c6403e00c0c00100d04003105003c2c40031046007035940303821401790700040d0040f818408000812100d505d41004035035902940c4103455000240c081d000000034801c940300c20602ca0050a103606168944034080103030f805c04202400011400708041080d4a08680328080c141030503034981c41022010703c040b800b599401030003140507a882d02c0202e1900e243c40107940f6402d035041400c0e6401e0822010b80c010203540039200b1b1700c480160300c0601d0b001d1440e20400c650215 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 176908561 1250 176907311 176907319
    0x60e030705070608090c1f1e02070501031e050f010e06040204052103190804020310050606090d0203030d0c0201020315040e0604030807090905151e011d0a050301020a0c03020606030606 81
    0x525000b03080f5400c11006280440c58000d0400441c2c0c6c43d1942051807258144000180744c50f03001144000b0300e0b61841d03203419569921007500d041555900410850140c48003840e000c07031500301a044c013600e5606011b135490801c82c42d010030402c2e110f400c0d1001c036044c0c854540100c0c642d81c880d07501700001d0340120b004003940000030003250b4030210b9414548800c03003c020f1068900b4500409840950061100310b40b002060509080100710f180c10307c180340d000380b1505402c10450134a5008078806000718101d050080c171034480010195a802c2007074618801d101e15050140a06502c0024081c1d0001c1c0c0b00c0d41d081c80c2c000b210044061820b4000d1001c0c03030301400d000b403500b542c0b00c3d02d0031070710b460024000001340300d900540411820107601a0f284a00882000500368000d148144003081402c01c4910a29400b09140c5030b440786e80c441c80050103055940030210b40d030005100000c480040d294404c661541c070004200a506402c5021050194040e4095600300d5880d6004e054031000c1c201c46090340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 176909811 1250 176908561 176908573
    0x3200a1211030403020d020c1f0c05010b030616170402010f05030c0909040807050d0f0e060711030d1806050a0e060a031e0531020d080708070b0103060e030705 70
    0x58440d00460a40604484020a60464155580a90742c1c01610103400503004a05c51481e01d0f60104901c51078008151880060b401d0300904924115080c02c200340100503071208140b040c444d007500131440c0d0305002401d403205030600821641c070101600c43e00342c002c0303402c2c451000d101d17450018005200341d4041e111001003c5150f402140c2d603600c020801c0c0d0b0440390620001c0810740381c00700c1e003d100b2403113810b0302513130746000d4100903291401040c0f0010030011b01c01c12004c0816070011100609400c180c0d041502c580c50780c54075049900180d4134090705031140c640c0c2114100e0380550040e81e01102d00c010360300b903549c40d003500b150b1b60302ca1140742d41c02149402041407094141080145600030440c503002411010a0481500d100c4507004000002600ea000380550700b035280324014004940a00301034008016064480c015500e40b04001e445900d1000701e0400344080c51040f50121548065465035a880f50700d42118142c000b07020a84105260001d4201120300c00030440c4c00d603503004802000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 176911061 1250 176909811 176909827
    0x102070506070e0a080703060923120d0f050f01050406050a030507050904060207021809190b06090406150f0e060d02060d0b12190b070203040303050304060b03010b130203070320 78
    0x84510a12581c0f980001c070f1036000003005c1350207110b0f0b800a584140e0000c00c0c14100d50034201a228003100754101000b0f01343c0c0045101da01d0000e100e030b44640744e04c00701644840c020750380000100305188007900501c1c04c02c2c04109000460020a82c1039030b070102c804005068480040c17000440b15804010703d81d41c0a004180305500c0c0000301030394064890b0502601e00309651307020601a52402c100d20603c00c12100602102030001c2c071504080d85d00c02c0c80c400012303d205454001c140300000c1c01182c024084400070405101c441d800c28080c1c040b41007042c50380b031550381c403410045403032511a8840ea8488280031400e40d1a091000202ca5a0020159070812001526200c0104060301b14a07a002c0c681d039038415004a001c0c050010250441d00b4000e140c043e0604001e040c01034014440c1007107420070441440000e40080a0300c5d001171f009400001c82c9480000440d0041c101a40040c2c4d0000142c203c4401540c5d50b60011441380405580034840f0402c5d2482c105060008100d118040301c03410301c5054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 176912311 1250 176911061 176911067
    0x160308060a0b040f170c10081e070504061103070f030807021002041a0d060302131406060910081b03040b04120804030f05070201020312010f0302031506030c041122080f010207050607 80
    0x810b1104600c0a4a051000d09400507c910400300e413007101090002003004815070700c4000c444501d11000540304240d10b030000b00141548254028402030206281d070b6100110020029524204c0d807001c44801e10800c4c070305018140200c210f460344014425544120840001d038002e45d42183c5070107404001e00131503074880a42d41d402c030219008450360b5607040003025994856001c070340f00c484032400103952245007855808990b8001d0046025007810000030300306e5210950704a640350010314280c00340340c952030380c04008400d900101c0c505100c0040140424085021a090f005500c58802c090340c4d0309800400351044c600441e0098049410440d40d000740030300074001400c0003841481924581014aa4400350000007a0480527103020720300c82c144118241005281581e40e480b200d103001d285413840c00690b65228101e5002d00654580721401d0100302d000d0b081e43c1c1202065050114121000205d00000c84002d124440f800c0c8141491400074070010b00c201c540c00c54200e001741c036183d0b0340c04a041e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 176913561 1250 176912311 176912339
    0x3090613020f09090109150e010c0915030203060607080304061401050111060705030c041e140102031315050c011e050601050705030f0c070518040c0501051204030c08160308060a0b040f 81
    0x100c859500c8801580020300008540c66000e07d5515001130304d00f0781108820308480110104205205035010144801e01003c3e07281d280810140c6030160f5030f5650340c07010480d54084c00070010514100442030004120352600701c810566541d005410b200c0c1c0c0e0b10170046426070301808030740d003840d0001d00104421a104030001c543c00600c910000d46003da883c1c030441d8200c50354080c4070f0410f442c510401c1c815000f01c03801c7c0064150092000714184046526900310b103400a00c201c81145010f9203054a045000b41c0544840c040200020000c150b0700d04000303c00f40b0000000d05004902c0c00000850a40c052003e0b500700c103820100450414000102340c20b03484c0d002d40c0500c9070b03030300ca4080e0004841d901d400c0070040e600d900f0b40d005d89641c01c09240440300c01100703401503418010140314000155500780700c556400f98040c036041101c0c500c00d0414a0407441184c00c803082074840c114640d0249500151107500401c000c1c0c9400c10311325a58540c00c0201d00030b500448e2000110318100300040c400003038617 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 176914811 1250 176913561 176913571
    0x604051308070b1f1e080c0306160210060909060e12070b1003050304080d0f030209010e010804170316080109140426040e070f020106060210020703050c0d0503090613020f09 76
    0x1204a40d105034403200d031070513a41d690180900110b00d82800c00340d030101456203001000c60400a0542e11051000680c86040c01481822201c00d1042502070291082182c038070706800141d01003203281e40b140d8140f4040e046a1400342e45007808e11219001c01440010100c44418081002c58203040642d91a68000c441c00f400c100c6014034010303c08130101d0003e000400040590304020304201c01440c0000c1c04107001c4000c0141414414031a400459030402d4090310464402d2801401350f54891400490035449804100007a075000300410800c00a1810b0003c1506400c0d181c00415030790780d076017a400351820040c81007007000344803000c180005c46100340540c20a0368210100c0a907003103030800382c803990065031207000610a050180094150000c040039030341c2042d48020b02c4501d040040c040d41d108980030b06a84916070015440062611600c01d58211f0b10451096658481c950b14000f03200e604296103615440c01010701250300700290038010660160701800c06440c501900040058403200106 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 176916061 1250 176914811 176914831
    0x100915030c120f060507050c100504020130110a1724120a1104110c060403140f0c01021819030303021b1504050601050411041802090d0b0604051308070b 67
    0x300d4000001c0d2207000e17980c40ba090380c4d40c410f501d960322541c00a1070b00080c00d58100641b45001700340409030b6807200401d00c1941d8146000c169a90407121042008501b00340d0b030b844030519140c1001984880b900c000d111512080c2e851a04440101c0c0c11b522800005031030352850301104054000700aa801c164200c821403008000d14162401c0d046085d042c11084002103914100e0392191b072041c0d20f404d1191700613101500e200e40d42000e01041c0d119965000160000e800d10201c000f031024003d04400803107090340d000c0e03500f042c2c4508440c00514080d41110007001a008100c0d06141f409041201c152200002710110924810349180c8080d0001d501508001518901d041c9070711002c0d85040000d40c510b0015003506103124034060a00c1802d040b07040c3c0200f07102d10304129801c00012140400c1d80e0540380c2d007040d2489584a11540e080c024031030403694940080c1d003044101c05120354a115180b184209440901c2603035140c0d0f680d1b1480f1480c021004202007010b00000000c59003600c402c56010310124 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 176917311 1250 176916061 176916083
    0xd0c021e09010603020c01050a06030f02010e03071503021b06090d110c1c02030c01020d0f0e0607051e0c0d0b04030f090810020a02010b0402040f0303051c05100915030c12 75
    0x400481c0681a0903088800800e40000b50a10036070024800d20f17a0003218002e04120003411690303041c1c0340d5400c2120103410400c410f000040599414428840205841ca0100000c0a51001c000c3e005e074221682d403a642d852615100101003802060070380c072480246000d84250307e089030040e80c0b29403089000c82007902c9400e00c030300702030385030280b41d6001c5805013150310194403c0d600c1018038106929100c2d0781190011018800955000824192403000c2403d1440040c510355011604e18007807954050691700c12104046440c02c4000310303150740c0900050644096020280c04d105650b801c1800c000c104041031000500030078415020030b44011a2841e0002d00950b450780d85601c1d040403421101c0100d030f4005400b8601d280c09101b91015800e0a40e4190300701481d206003901c8002c070b203110103014440d002035106c0396800000421000440c1c04203040040b03042428004420038458060768840d2450103120186001e040306030300089951040d500f294060610241e021000c40103007040320151000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 176918561 1250 176917311 176917369
    0xc0105071a0106050903010506010306030206040515220e10080a030e1908030c0c1e040b0114030109090201260601110f0304030b07090515190509040e15090d0c02 71
    0x75001103008104982d1004d440c1c02d2031100705400c5410160803281414036140b0100010f03203030403041d24100c400403240800030002801c20a4014400c0c142946d1031160581c040110780701c281040c1c901594000440341619aa8403903203d40071200c00d002c1d80a0302d5000300405c2000074466200068182c00140034080103a80b40d00c6242c039605000d4120000d15080490031009034082040400154181210540354041100182c20681c240240d81c2074000c54542d0040e840300e90103031003010011284910030710340e2983e407500c0c000c1c014071202600b00c1c00103031076582182082008040100340c03180b01141c000481d44400c1c005480c01c00400403025a00e00030b40540014009081c800742000314000c2d048041315150201004101110a4000340d100b40c1030301c2c01ca0b4481822103030545800600d620106260b0380342c110010b446600980340c505a00900b800b000591559022624000c0001c0701da0780c6c9040c075110002d10300e40f82d0076a03080350000200c00204801c050310304242e1320f180081500c000d6911132804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 176919811 1250 176918561 176918603
    0x403031d010c03050705070201140702010201020919050f10080a0b1c050105010e0c070305041e090c03090308090102212520030702090a0f0e0f010e0606120c010507 72
    0xc1200c0c0032040c0d550b802c000c9402030b01405070b19401034440c07500d1450000e059002800f100030000101020f10340214540c002c40e4005d50480e504994000e0150500420300c2c102850000068020240950350b00d6100d022142403140801918407541e80702c0d45030950303c201101000700300f0122143c1d44010f03031020b5400300c488185091515140107100200781c943c105682c440e01d84001070f1648120342c07410030095002c60f500405640548010b08023070201c1c50310780312210342e25840c16040410b440e490595004074040c0c0551080d14020300c40d49550f51950741e6080507500301d001c1c08080004c400100c140c40e16492540c0c900b0160b008145c101034032401017800c401103020b070003000c620700041151400c0c1c02e02028001d103441422420700d41c0003146031101c650302060504502401490b045074850310700425084060300544110b0044a007100e5800e07101e548010301a100404003101c59000307210208a0505250025217904482c4000406d180903504c0011a01c50b800000141da81404d810403070040042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 176921061 1250 176919811 176919851
    0x110a0306020d02040504060f03170a02010209030304061e0809071a070b07020d110f0d050306040207022d0909120702011106070f030606050c100e071d09072c040303 72
    0xb044040041c0c0b0b0390f051905120403200d65400c4034801001c0e1504c2000091240c101d0789076441e458207a4140c5542c0d220350309074003a0050800d0380e41d0601000c01d0104445511840b00c40126486906800d204844100c080c0d505180546540e19150069401804010300e030303078541e00450005640582c50184540ca038980010415070345400180c0082c24aa20203a90003100c0c03030500e5400c03402074440707802c11045480e40c0700d0044215006001011000445669a0f913040e10011600500050388a04440150080a030203000b030084c80142880c41d54099030800c1420070303100d2101500201f1140484070700c0c2c640c081d00040c80407410050340302d02c0d5901021781481081d0107410300313481c0d000c0104141034002c1c00b602c0c20303030b0061070410206006090164100140380c0c00400a10540022178100c0c04076100c0c01c1141c1a00041d45402c5140e821400a00030320752446d1141000c2025108042d40703c219400382c3c0d0801400388584030030003400765280070749128007032a0420322a04000680c02861001c0f40503480c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 176922311 1250 176921061 176921077
    0xc070804030503070c1707091a0d140706050a050d200d0621020102251508090c0d051513021005070303060501081603020d020909090a0c050a060c110a030602 69
    0x3d00081800c50400880c1e44484026007040b6407074040209a410405a03035082508c83c82c0416922901c0448143c02c01c4020f410200c0000f0302084640d03015800d009042c0b0b03800c143d541302244985038000034420702c1a000e880d024030040c1e80c0c140c40c01074544641c1d00074200e030300b80281c81d0140d80020b642d25100510300501c4481120070000c140e0901d48180c1841c1001c4005112034051a40c1c0803520060303901041d80200940340305c2e05c200d05680200e0700c0d59100c90483d0001140c49802c607440514817900030080a01c2008450304640b100f15480c2c0a01c070000140f080300508540c07051841c10350100900c0c0e0880e91003d041003103540c106140350002008140c45c0c4c0000c1001c80c00001e0f440c42451fa0600449002e05000e09001c40c440c242100104100c030000400790080642c08160092100c031107804031380e600d00000303245c801107092614226403211154142121034850040000401e410110751200c1140c40d5610fa002d12040350f81c071207070f00031a41d1440c5c2527800130744860040006801d52001d40701c42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 176923561 1250 176922311 176922313
    0x16140c040204030f17040f121104020d0e0f0a0506060607030201020f0a0c020108060409150c0306050a0e0601080f0903041703070501050a0501051009140d020a030c061205150d06050c0708040305 85
    0xd81503824001d21703030901d101051400d184100410311041c200f13051410b0031a400042032040c480c5d840d00f00200503102541246074080e0000500d4004182e9940003e0310701d5001e0350070744031006084160259504406640280507800c2200012101e14000000d40040ba02a000145c5485140c0c61031700f446520007540d400c04a08400b10280079564051003040e0302c000103940811202c80341340c40b03e9840740d060340c03044c1000300c1d16950b0030080141f0076000100100000342403e4401e82d1611803c4103600c00c1100c03918001038014001550035034040310f025020714042c4000e54506420401e00d1003000090003025034140c4000c00a040004509200e164800c5ca46d0080006041d410681000040c480c0039010301c080008407481030100301507142082c49003030030031601c92001245078404909140302590015004440c0d410000070001c0d080541078007401d50b126002c105c2c0f5603d03400e60903401c00e44d280341650820340d03440c4803900042099000c10342181d004084507041020a50b00e118845c1d11541040f82d107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 176924811 1250 176923561 176923583
    0x80304150f020a02030a08030a0f05040506040b0705030f040f0c0806090d020c100818070314010507020d081302090703181a060f13050406020f0c010b011416140c04020403 75
    0x11664040901c400000c0603201400c0150f000f0740009580c0c00c0a0a00600740060000c00b00710b80008075440000d1103048094180400e203824180035440d0360044a055603116403010000b00381900c203404480c460f403145030704114561541c7d01c43c1c032594503a072501100c1140703030208040344960082007841e201d20804001003070b120300020340003400c0030000d844180c01110543c0f80104400d4020b50702550000c044508561551580c2c82000c0c60312a0729400504201003240c141c44030311038190031442c412203681d001c89481200520044a040400301c40c2c00c0020303100c40a036500140b401ca061960403502501d80491030b004c0c05038880035100d81030310040f501001401c4020f468054440030aa5205408641d01c51000d440c02000c0b40d110b0411062442c101551000003404000d06035040c0c0b0b8242090910381a06e500b0b03441e42881c004c012081c1010301196041000c000c0000c0c4038411508035607d000e1075001c0d149419611282004400c014000303a901038080e003001c085e100e500c0640019802031251440d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 176926061 1250 176924811 176924849
    0x4090807051605030708070e0603010212040503071a010501051603030e060108030d051005030a08070503120a0203011d04030f110a0b0a1e05073603051b01020c032104080304 76
    0x2d81c00c455620440c0a50400482041460307000b00305d800403102008503d41a0f03a8500d00003900920401c500a580b9070200030902090103800005811002c1c0300710201d460007000d60100340303080b420034818940022000c02108c0c800d801440748a20003e482414080f400d030244410103030401c00240c1141c83d10b94008500c0d1501100940a0030350402804240d09545c43d0928001c6501c13140303200e1300648440c0001403d2800c0210800840304882d0300000c4048140c103149429002030b620a00c41c1040311610080ca00408105413a0b0840c0034a0385625491448800e441041e5090200408103410310701400c15103c005c2070800300114416480304000154541000b0704d02241b00e9100000e803800c02e480d11040142c03881e04601500e0040c0b00840501071400d40e1039024801907441040402c3c1d80b419000f10000400000050440d1452540106148900108001242d0b034002c1040b6803035140e48a03010710b42d10581030240d01c01a0b03000c015800ca10300f50f11142c0c1149141d20660107406684804140300c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 176927311 1250 176926061 176926093
    0x2090d0f0302011a040e060c1e0a1206050603060a0504050c04080a110102060f040c03080315311104050907020f1e0106050904080720030d0e03060a02040806010e060409080705 77
    0x482241c00701c800308406c000410071199181c1000700a0550118000795010b0264040100c0312180184540700558646d441b0100400c4501244000c5001074106107021a983c0f030401e050724484d00b009440094414940320800003d014003504440440d030701044080b80c0700d80c06012080c0214000c0030b001100c404050002032608074002e022883d000782c001c040c440012a2009984200c07508041c0968a944405e0410f11a82c00b00040c84c6d58842b0700340320b450a0401c10140400e0030140390300441503a2031049500e100c1980c00d001c00701880c41b98204401e204d01d10b07104411907000130451046451000b9540559494242c2002c0c0c0b5541e5203004410320380024a00740144d902401e420359000c0b0300c03400d099a6000701e5025442c0d0080481e26004164002481c1e024101c00c0e10b020300a0444440213003440024006512a4000a000e4098180000c0c0401140d008a03401c543c505c50050010340c0c03a0900081002134050200c80d80a074070740700f661012414006c00307480c44600a02c090811500075920038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 176928561 1250 176927311 176927351
    0x25060204080f06011a030412030f0f18060f0203060d0305180d0b1005010905010f03090f1223030105030703170706020708040503060603011b0f0203040e04030906020d0302090a030602090d0f030201 86
    0x1008172500c101300300800070341610114089900b19040c003080948504440c840a042c03800520f13030314180307000d180b11056142451584480b5009203c10444810090f1302c0c0d03010380c40100c41c040c0c0c1011000d9641400a071148000380310203140d001ca0200365031070003000180ca151110800351020444081407250742c1415104c803400921003420700841d00740c503050010f8208048811081e00740766941041c002405590303a00700781c007613078070100400b1a9840c058020740a80301000e044008542e50810705001d0700710a10860741038503001030092030102e01d1030703079004218902291020f010040500001f0000b840500107401c005114100740c030b4030f941c141414503140150040150380b2a0381446050f05191011407440000b81465180000104e4542c0105918620960b8864000d0510380c004110505604c05140c909960b0746600781d030442c42003040e0131000d80c003400d01c100f80d0200142c0030400014415a005150560003d4460118520b840c1c80300300c114034001d01c0980150351251b081030b150311064044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 176929811 1250 176928561 176928599
    0x1c0b01060503190207020108010302010c050102070f05010f18020a0902130801050702010204031127090703020d08041d011a0d110a02161a090f0409080a0c0209060625060204080f0601 80
    0x811405c1c041d031500004c120744e0042c803001e070610903040d14640c1404029012101305a8001c5a6141c0540d030510f0400e000746010100c44031801e01d881d906440d030301518245500b5481d0000c1440d8021400c0524080007503000c2075440b503603019010f400141640300be018862084a96800040e2928a5410400b541a80ea00e071543d1040010b050311124030305440d90001d0a0308040601003947d0350f00d100e001441c001c42500003951003040382c8403090400071200014029501c11110803900022800c03a031260744402805102a001c505c0d5042803c1381503181d028141c424028080030900d03601902c100c440b40e030700020352400180c00810000109100d4150180001c18101041300c481824402585000d030081030002407144940c005000004d5603a500888240c1d5000595956610b860312806444c4104d4803008034003c40d25400090014079000054030410359600c4c11000741c3c045001e20507404011400011920158240030106018100b000075000144507a00146903950600030311000e01c1000c419 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 176931061 1250 176929811 176929861
    0x60e0112110d1a030a060e0f0c031203040204060e1f06110d0c05070e090607020f0316060518100b0109050303040b090d06090807120e030703030e1c0b01060503 70
    0x504060941d40020448800e20002140010b400260390040d1014400300d62000d585485103042010621000b50300c411140b000341400c0b80d0b11f1a042c1d405a50300d9400561800341e161300180042d2641a212500540d0302c144020400034015440d200d2050780c021055458032518041c800e0030062030040d070031100c4003901040c18800e01c48801b40b18401d560b601c1d441c5569080241c0807108404000c130410074440074100c000b0f003c0f80300f8900b0030741da241d440f102203401e08010320078801c131071501d408080300b00d0310182c0c401c05803008940746039125080504005050f00643c64409080d24281d4081803101000318801500041455507100700014140340340d5420031440b9400030442004203000c2d03030f02156554401a50f1003030030342a0a040c224014086e04901802c0048000740c181c0800c440d6640400005242c2d894800d100455a800d1580e03d00715404014081444241850320a00d000302203400304854211096490700356955608101e600280e00c4417000c21000b2080c45043c03848150604c6100756504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 176932311 1250 176931061 176931071
    0xc150411040e011103060d03030f0e0d090f0b03010e0712091101030e07050612070903140102030109050f090a031215120c080a0b010e15060a0e040b0406030c09020d06050307060e0112 80
    0x500c0139001403002400003881560744a00039001c05000c3d401c00f81900d0422041003050700054140c080e2103045001c209400150050004681d44100100a0303003503c004003581d5043d6070a10614001412001c0c110505010310f42a0040c27001905018000e040c5200b18020036020304040e0015017a00c40408080c40143c01c81c00c420700890312031000365501004080345411140d261450291034645071908003500d5080c80c0a170301003c02005400950403148903040400240d81c513850a0744070319400340d031018200d400c95480c0707001103441070600800b0700340c208034001092854207056500c4040507500c00c0000900e1100c1c504180000c11003030100620001000d820155510740d01d40c0c00b1072105020303444000c0f076140b02207104c2c44800741e5801e44d900b80242409654050440b000b40c101600b1b81003e900c29402d2919441d4181030502400b82103940c003d03010081c10382800100400380d000345140a1106a0f2803000040641c1c082101720014201612180b41d801c15603400101540b0040c0b00c0c58031024108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 176933561 1250 176932311 176932331
    0x30608101406062209061e03020102150402030102041805060406060212040611070f0b18010905010c0204201b0c0d0b040807030207030804091d07030b0c0c150411040e01 74
    0x301001d075a00c000b044a00796038a00b415040789a03454499204024600c80d024008205c44003d075006400780c55120003101304215107410b590b601c215840c0402030040c2c1107152074990558210307030301d503400c00e20090004d410507844802070b400031a07406a405e010103407101300f8403086007080c3c46210040c1641740301030709600322001c8440103644521f20a60003041001080a410710100b4481000544070340c4e808010056615442201030f43c01840b242d50401d0f14408148103c3c1d80680c0c1c60804440040c4c59010341c516081d02000003e1007811000341801100914420001c04158010f0240445140f2000950b0081c441901d1420f0500d014060050240411100110321442c0c1600c1c0e006512801c40790fa50141441c0880c02c040650340020600c8002040115052846421807070350103042440b41100c5c0148c48507420341d10b07072081c0303c013801e403180410100f040840904014500740f1100c004403586c0f4005040b0764540d00d4000c5400351001c09100000c509240f91038090780b102001c1c0b4600a100002c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 176934811 1250 176933561 176933591
    0x10803070b0c0a11030f0405010815240c0712030207060e18060f130501060215012d0f06030207020901080303190b0d020301060b040e100e040210030e0d03060810 71
    0x2410814900b4404545031924501c1002a009210740c0541640c2d2503803865584c10a00d50440c0c0a1f0030f01044840c2c000a03000301c1c3d0254202402d44006026110200d5849254607203005008884080038100700700c0f1028a0030308001401c018080c50351031b0020316025042c02410800c90740c005808124280035108841da54440041e9002c940d0580641c0407502c40a0000d003c00901d804010380100304241500c40856581c1d1149040340c01035001e4038400f890040744c29204034400d00540d0503800d0441d0790425089024003080c1c00c000f20003031b00704c1c3e48261500c0c81869100300e594810000241c00280301802c600b4083c0b511401082e00100442c00c500342440c988031030000d01540d07551101c1c2d40360b01d42502e0740ea071003910325121500034000b0002c01e0b850321418016680140145800e18842c1000319120650020341041150007459151340140c589501300303c2401e4480e4981c80406407589000c030a000c0088c40145000200c94900184e09850070010a0800140075649038600d850590103c1c0d050003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 176936061 1250 176934811 176934833
    0xa0801120c0e060a12050c011103070c031b0302120c03070b040e062407030804020906120d0509010c170702130513080c01060f0605030411030604021f030e010c02100501080307 77
    0x1258101c0c0c6a01e0394501d40462040c1350b10b984a0640319034040d209505201c0701040c000c000c58001e98641d400762881e0041c082c1c0e00c1c030622000500701c0315100310400120312001a0400303145c250030301103d55140c4d82d40005161258040250f81e4603045040404d20a02e000c0014a00070914000920304240c43d004114100103002070806000c1c00c02c560100c0c0d48001c841d12483c2c002402c01d103d45841d541c050034014903006048030700700d0140007500003007491854800b00c500c2c14815950020840c0c4030b5010404c42d02c6801910541d8117100c04105078500141e0f036428041000700340c08150702d4440510f8010000342c080c80300300740038100b4504420b000a5604d00c500c424402d0b03070802450b41c0d0311135085202c1d42c010a015403011110210350000030848940c4040118040da0040e101d50242503144800c25403141801d58009500040d80b94441c0c140c03240e101d21064401c00c40e070030000346110301c7d02e01075403e4401e80783c004401600582100c104041c07451080d1130260082d07600860502e4039641d11154190 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 176937311 1250 176936061 176936069
    0x9010501050d24060309171204020105180a031406070f09090e030d0501060e01080a111c14010b030106021e03030103030302130b041202100503161805150a0801120c 72
    0x240c1c44180f01500390030f1040d0035400c2e540b6892190009141d80320070003001800482d4040707441d010190500d071501c0c5820015116060707042d103500c55454856600540e600c1d44a030103211256009021040c14596404515400450041c03070494080c4c01c240f2240707400c0140c003c16410a22100d205140607580d84952000162601e00c0000100382510700030030740c998050444030802c2282070000105c0e4950340440b00495141c4281c8420000b03803601e20341a02501c0035182401c1041e4002e02482d562106d03402c1002c1e40c40482d012000441e1402c00e842c10504201c26048030310700010000040003640e6041001c0c0041803603076641e0145d0f518a400142e5100c3c44188000703020143c01140620880d0102c0318040001c01c800130610740c8c1c1c3d964a80c8658064901c900c800d078419042010300c480002c2c0140220b034031a07085980c407603141210860088d40c1c460900d500e60394000f0031101011a554a50100c8003070721900d291000d0713483e03112000004100f020305821410b501542c204505000035101040d4605403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 176938561 1250 176937311 176937337
    0x5030318010e01050702032536091202010614062703010e0303070c021e0d0f050c030706030510090b01020a14031315090816050402030402031c0f0e0901050105 70
    0x2e403190b100121860700485101941c54002e03982c80d00e100d064000c0103501041c1e9120400d0701926912000e0307546e00104620704000340c01c046801085101500103140040d03025601d00059071840d1529141c00400503401b040f000740cbc0d910b210a2001020181c0303503004016003140c0c002d15282d050951086042034040092034217004182c504d0b0f10594003904101c0b01040480110f0b5140e20b41100002c05008044406070300032045070030929524240d03865440308485000d4211140110107580315140109002410b607090f0182c002103462070b0b0b5060029800030850740d50046860304120142a00706030182d4042141d41c0d00e40b07091000142d8000c9048103400d500402808118881c401c078940c00c5215511900010011040011031a005c100c1341c455404859582e800d90384641351180c42da50b40d9a040422182d038070b030b142c500b0400c520b45031b0021948548060240d43c01080c40e8480301f0300c000b041e544018080394411144101c200c0d4801c0f0b0300c03031002408840340020b1303514040010f8a05d1061101d640300e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 176939811 1250 176938561 176938577
    0x150f030304210f1b0905010f0512120316180617040f0f0b071101050f010b0f0f0708040305060a0911040506010c150c03150b09121005090d090503031801 67
    0x2005048512002040390440f0743e00c600c1c0000380c50001c906615551803501c0c8400110008183c2d12402d01c41e55050381c0c50108103500300b504140800c11781c0804040d40002d6449142d007103c41e4509450051802007083c3c0480700e4001c07886110103480341e4810b04e4840001e40c1c00000c10007050b60710080101c6035844040f0940c00381d48840c241070b1024560301c600a84585070703001062081114024040c0d21031000c5a4031400ca4084001c0807909844040d02c1212221141000501c04090090000d01c0b200002c1103a41e813900700c2c48011408290007015081c0d9031051302260030000e11005200069024120360000c101c10756141c0c6c0c030000f10006120301d65000b1079403500009e000e41d001e1841445000d8000308280341846605248501a000040d40140024107041c0380304030312400c1c01c060605451000c4111800c1458190902094102292001c42c20b44602e5900b1041b103070781841030078001c40f000006003100f00034201000c0d1200c200c0d64000e50090b4020004a005444114400f0601e0502442c169107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 176941061 1250 176939811 176939849
    0x70c080712050d0b032e09060e060108010b010908060406020f12040f060c020a020102060f0a020909070f0f2618030c07030c050f06030103060c030908070803150f030304 74
    0x9040c0611000201103110040540400c1c64101d0050a00004203c3d018086642070005050f110110341000f03004244040040341000131a104145244068001c00050f1020a80d1143c00c00e95030705000c0701c070385604014010b004614085c040c0e000302c14000e081c120074007407a00e0091070380d0720b0b4010800381c4010381c081188080e184901c0b003211400d130544000400d0714141400c0c002c1400007005c0046608514045150301e0990001c5811054650141c010340400d50350310f1441d9031004002403600048650030484108c40c1c4c0d84c2c0400c1d80d402000d140d5504216501000006010703c0f0b00901160103000c80c5d60100b0348400114400759a413150180c00914164a900821034100b01d003031401141c0500021501000d580b00000d60081180d000708018001f0799561000c0c0640d00482c0540d441c0c0001080005001044180e001100c0520b002c3c5000504070b145a141d90005801078107088640c01800070a05c10038950101516581107011039051000300440f10000780e076442548940a129651480c80348 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 176942311 1250 176941061 176941073
    0xa0b030309060a051c050105060901110102041e061101020906070f050111041d0a0b06030f22060501090c030b0307050f012c03060106080603031615110c0106060203070b070c 76
    0x55219001034051600c9607a2140702034003a4216108451a10b0740420005c8604200780c01014100c4034041d1145160015203001140c2c0780700325400707400c0e00b59000c101c0040e15070000702600541c10807410101d40c1240c100705000742968090700141c10030360300510010a0540d1100126038449034000501203002107903242c6113000d800c04c4145002c0c1c20001240c00241202d00d00c10f01d64408086402c0c00e20a6a03c42ca00b20003194440440e80d07410103c1400064240d0b034a81915903001040c0d8101e1207440c0900000307100380c201d01040c08807150382d01c4000400c00c2d03500314052200020141c0c00d0622450b036900e40400d0703644d5214441d66100f804180c07034850090340a101c03207204d248030b008962003440c801005c101201c4481172120078080d10690000007461845070280074011280200070303600d082210030f00a010440c1c3c05c5015a921000401148403100a074407a6203130b9008d092007495120800400d00900311840c583c855802d541082100200140040500715400700d0b041c02d0400680041c2c1c1051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 176943561 1250 176942311 176942317
    0x1106060d021906050306210d0309050f030a05120108060702060606130e0108010c08010506070c0506070303061d0402011b0b01091107020d0b091b0f0f030c040614090a050f0a0b0303 79
    0x2012070380b440988007048490340000258882c21060381c801e90301d016818005201450b41180a840070303046140d4141c8414070a41040341558001c908581d1a14031801c1c8490442d07100c6012280810310001d40c120b8400d003c08229801450500c010707041500d031046000e07440f0a002088a441040c00145481a00c918090202c026120b138103098a507a42c0c5a1200301d00800d4101c4203480454864000020585801000c4555843e80610a481114031303007818000f60742c005401c21002c4c180c481030041096085010040c1054004906c642c2c1c2d241414000582865011640310465004007440440071588840c940f90455101810004e101102d40d0031100060046260083d031081e20307a1421001d214440009500481082003a00c0b110040c009010b01d80703d01e407800041d00202c0a1483c4403061400341c0000e220b40c8006003c1c2d031120340905000074204d84083d0010600340c155111078020905040784082e0f40406c1c0c2c0d102c10480380c180003c0266018000526000d0361a494600c0031045440c24416 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 176944811 1250 176943561 176943589
    0x50d030e01081f0e01030218070c03030b03120715060b091c020307031a041101081905060102151e06100e1c0b070e01030509070e0604020a2c010f1106060d02 69
    0x180c203070f08030745408503454220428402a4440c03070280348120441d2201240e0280124112703240c45804003031702e903020303009020280c84072a030502480501d0708218581c0002004d086114049000e025401d00072000221101500141c5080b001440748a001e92540e6480050042c008105206460043e10019203007403680d030402008682e5400e108514441c4528009000d2407185d008560b4450f807140044509400444807a00111289044043c8030b038040d5101c04d40001043c8144c0ea01c0d010201002007c0407000d0b01d5900400c0481007201d90b40003020518a40c00c07090881d84200c0180000c040180001443d420082c4105806910002c0200e0400c0001d1803c55200d45024824506007901420b140c42d1240c4040c0030a00b0400000c8a250000c500b201c1540c520130034401070341d02d507001800020340080b0300382003d01070b00a90032040b844945610744080c2840d1401040041e00000c001043c10141e074103101d040c000101c1a5140380e00000c210740b5841101540c001504100d18000501000c0498030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 176946061 1250 176944811 176944861
    0x1406011d220e010e150108121e090907180602072907050a06060311030c030601030803060d061503020315010b0d0203070c020d030c0b0106021b0f04090b0109090c050d030e0108 77
    0x1042d02001c4c000c10042d4594102d10412200c0c0c0e81da0b680b50b2600d03000300001c100c8141c001000b4114100c9108010401020b030740d8403806017041c00d00c1010591800381503804d0404a018414224a004040300290028001c50300c05001c42d1490400201c00c10704603a61b0b13482804c02a500e40c030399007008050545032000d41140c1218104129420103200030a0705010555512400781706c81c903550300700050426a81c0303201038000d002c00e80c44c544501c1c6003508007030842c60703000c010742180802240d0326000d0464074000000c0c52081652540c41007514103400303003d2441c0c414407480b0042207040380070410341c3c1510884c1c44d400b69495644840c100c85514248000a60000b9410040c50030705502c1200c100141c1d22452100e0031070f9072103410070780e0380d0315142c0304003030025100411b01000d5040c283e80c2c1903404000507001184007000e40e561030060480076007014500607074480041c800d00c000d02c4c101c0c07401020240c1c0c0329072400800d80c40007001040072081c183d040c003036510041007090008280890311419410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 176947311 1250 176946061 176946071
    0x60c021606030204080c0d03021c0e12010e210403060209010504030b0c1902010513141e0f01051308030a05250e01030b03010507230d1406011d220e01 66
    0x1d500600250000d00030140c080c840c5050203406818098448592150036800a140c20840509560314204165419004211b41c900e02c0c80550340302d102080c1e039040d80840020075098802000305107458181c02aa0800f03007110308c4030410601d103190403101543d420050140c4d54000d0400140c405100c0c03a44000c114000344820000075030002006861402c41c403035201c50031302c2c282c0003040707090319400c0c0c60400c030034450400f0b00030000c0c51303403105d4210b0306410806503015560301840140007810056405642e81d00411180c54043c0030a01c10706070b002c060310100c03001e9012907841c0c00803580801881e070f1216540c1c43e800304062030360300801d5480214250000106001465000610105443c030003140840d0400d1003100b81441c040c003410740700711082e0759155070030030301041c0c504444590744880c002c4c040f0381006002c60104a500a040c403e05003c0c00145441c2003100004008032000d284502190b0101300c030155103942c070340075002c0380d0341151084074903644180a1410010080fa032409201903280c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 176948561 1250 176947311 176947319
    0x3080c03180a030f030507080601120b01031e3306030506010c050a050f07090204031106030429061206040b01090b012006061c030905010c060f09030806100509010c060c0216 76
    0xd000013640d100e5940c0a110503199860143d0b24104152107440c041042c0415426503007105c0e41c07080059400514001c01c02c00002c7e240c8020041c1c1c0e10140b070407180d84079020401400819000440148a504480c01140c101c9041400d64070503e0b018400030103444a010a82c20f03846100f08405403904402030311043e84003440c0880d601c81a81078038100d0b60062050000744000c01d8400d40342260781207250000350004103030802600740d20080007111002c0d02450020440110604c00e4011810308600c454540d0900c20b080010105820b4030138080ca03801041000700040c030481f401070455070a14030200390321351800d0040e00d84400d1030100f03a905603440d03080400c0c240000200365000b804107880750a401c0e0b01982c4040400e11400c0405800320f006108100029441480040382c800d0143d4800070700311514404640a998180e503041e80041d0400c002e10a003443d100c2000c6006040505020f440c248810002800d25039414002030701d003607680c9010300829402803210058000032840c494a640ba11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 176949811 1250 176948561 176948567
    0x30c050f060f0a09050a02150f04031101120209060a0309140f030d050a110313020406031502030402040c030203010f0b07051011071104020f070b0a0e030c01140a050403080c03180a03 80
    0x882d20200c04035040d80c04204003203681c0c03080508140e082009881c54035120340a10410343e6080c4240da0f040c2c03400300240f881c59100b00007d03001031445036142190010305080010105ca0030f802d01200c00920421100f00f0035502d03030007268003441060070085541101401c0404a481d080e400300e00f400d024085040361100d00100c000d12521a0320b081c1044507407500b00600703040344e5031090f009980355010808031750300750148200304014900c01407011950645a9455036002160403501d0f1520344e401100f4402145014004d008020385e1901d0110300f0740d0b1401c030448040175424400c41c018540c000404a0a010b4240040258400c0070b08c1e00380302c60107614140c1c8d19903500c020825521340d01c0c80d0428100034501802162414150744001c1030500c00c07a81c07034030380c5001c0018148010540c0da0321100d040009040c400341401900d044000620b11301d110380e191146003030085c88400000c0c5800308001c0041d8224401c16042008148580e8903907840307015507102c0341005060340d0b496203c0c00280c54200342e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 176951061 1250 176949811 176949823
    0xc1315090e01020c0609030a020d18080312010602060a200a05070c1e1a04090b030a0b090d11070b0403120215010b0714061302040b0402090604030f02040b090c0a0c030c050f 76
    0x10000c0c0440f240303030769207204c1b15441c3c3c010480e54000580003440e000805c035105500b50350b00800c404141019840d81c0d200f45624652180d50940c0c081900c0d2001007124580502001d07500080003441844203203c07401c28078202313011244802d04419000b0424842c45441942a5020903610038801e43c803039601c4082c0280c44018006404a00e01d0103a240030405140c540c0e1210203804121b140c80b404c1a082c81c0c034260181a00355122a0184620000e13032020420000704c081c0111701c501c02900c0c2c0313140a4030000300078540307080c2c6000032988410020440d40c40042e08a404994000d07000c000260007020040381064401000400d04040006c004100c2132040e90080c071500d40b1800e9030781c00c8602000181c5840f124101c509004070302c101ca01036400b60606400003a4919401040145850000d400060070354026800c103a42610100f0848421400c0c58803807030040481c00c40704800b462403c46616005813152034501c2c0200403a0709080420980a82d000030040c80e804800e99042000d03030500e05a0303c1e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 176952311 1250 176951061 176951077
    0xf03172d0702130e0c10120506010e04020d0501080601050604030314070314131e35010e011d0106030209071805060f07020907090f03031805030604150506030c1315090e0102 76
    0x10155181c1310b1864540086140c221000721f80314510f14010700c1082100401c4010b000b5414841d41c00c000000e00d071b94a00c01407051a00740c501c005515414110200d1a1440582100307004240c10441440400d40081d03080c42c0710046102c0d01e83d501d0300940ba080f10001020400c0488643c80440d01d04c0c1344501c00c94404056030449080300b448c448035848030b0b407071030b5519205a41c20258510003c00401d920840080d128500c0c07074030b0718620f40311f0014140782111600740340c440d0581d540b51070340401030036000c040604005801000b40303c06802d580014402190140552042c00003902904994130b0341c4a515400400c8000c0c12680c84071528551164590700c080010cd02c2000034000058215003c0c092260541d0007100c0020700103810341da81550300000300c020760400c601c6c824000041c035540400c25a40705612400000f50f410450300e5041040c0c850140c4200e1190300201c01c0c0c2003858807401054034101c4904500458503055840001e4556036054221445050910388511b0191070705400401c010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 176953561 1250 176952311 176952313
    0x20415020319080103020f0d0609140a02180108030f18040203010306060302042a0509060403050115260d030c030209030615030c04050405031917010f03172d0702130e 73
    0x10b92944504950000342400001e500c11604003011102d42020318010b1201c521a6000091420864403100110402c011002040f50301c45039500c01141403c0e0804285050003c803280f455506040559449001c0c42e010109604d401141441e1000c643e1031400460319400762045640e540c40c0e0130003002514a50001b07901840c10400c01c12070b05c0001c41c40f0f003441e034940c030b04000d03c0304020a4001c0740c4036401944140d0f400442800040003080081c41b074001c00c4440355001114061030030300b50a018404100780c42018003500a59420f032544046008007222005203000102e00d43c0e0420250000e0169604d00c540500c1044200845092907031115241c1034012404c031004514000d04102c251902110010320540051200040409029510020002c45400e22184000d014000b40060b6a401d074011000410184010000e002d14410120507400d00701c200d4070f02d815944845101c41d56000340c041c0300000c2c0c0c40c1a9040d030a40090081d11116a4010031101d1a40560b6802e00d01802ca080050301403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 176954811 1250 176953561 176953597
    0x30606080702030903070905060d0204020c0d0206100e0c030a061502010b120a03440f0105010309080915090d111009121202100203090312010602030c0a150204150203 73
    0x522400001640c1d42d44c04001d0040400d5414510f81c3c3d00500700c0134180c00d80100e0060400001070b601c0380040c015581c0e0000041400d01c411200091070950090004031145400d9041444040700c042c00c00c83d4400101d0400b0381c0e482e116002d81c80020842030740145140c0300c040601083d0310798190050400381d102201e9509080503c0c80380c59840b2802140003e010072011802e0001d2012030f02c801d1145d1080451401d00411240030f04804000000b003401c0d401c08255008101512050401d140d01421003840d04010500680d60b4110f128481d0121344da10800c000340c403c000d0250184110b45103050080c06810000c40740d0b11f0030b140100c40028009108c3c400702003850300003910443c031150071030320090341c0e180051950f921204028034070f42000c801180244008403848420500007140a4034000008598804242814000e44c0d41c0c180c00100c110b41007008288620800084d4004216410008520310354001c0000e5038000d20175a4000d540c001d0003c0342419901d0740200140030103e19040103096 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 176956061 1250 176954811 176954821
    0xa2417100f0b13152105070e07031a0d1104060302031605010801150e12030408010504150b030f06180c090f1e04020a0b0703230c010609020f2b0c03060608 68
    0x549002d0014190143c6503000204015a203005c41c1950780071184040164101e0140c948500341182034000250600c020402d00070481d501d889080d4011741c5c00b140c550349080c1200001480309512182c003800c0311001e40076003e010b50707980e8459001140d0007130031121984a02540341050050a00c1404d0100d40384000008034203502e1104925816001c0d0744119100301c0da43d0402000d04442600e540e2984414440450003180c24480c0c1c6000e41d000c2c4140c401c0d1940e6801c550019a0f0641d0b03503007402134010101500d28244005001c07500004940350100261105071001c0c0d180c0101e00a030360740d02600c0d14040c4205c1d03003400c03401c44e801800802c5100100b0307a040b0005402001c0240e600a4100c070041c01e003001582c041c2e202510255109180905030740e405040d0b409401c901c4041c40707544850000454011181092041030005c0c4031022080d8104a1070032400c5880c0d010317260740c2850a003403241c1032035040c1f05000300e00c2c94081400c0c80100181c07698400d0050041c01c881c0564004181401c011034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 176957311 1250 176956061 176956099
    0x20a0f0e030a120339030506090c0a090312020307020f041505061b0106030809030118050307060c0905130b01110703030c0204090c03050f0a0506010609270204090e0102030a2417100f0b 81
    0x142c40b8217805400182541c9070442b0300051036119a01c000d04100c0c11020210028034007440946d082000c550046031070b0030081c01007180703d1820b02201c83c410392a1500c2600c9003076544003004200d034001c44455440d210400c03062072914a25007250000c5529119003c02000b804001501d00c00c6c0c1305a000b0464a10804816030082c960900040c0141c3d00c10f104d00b50000300581c2041c01250030a20b440c0c400f6650b98000f2984400102040400c1103403618400e0301c541d648151a6014650010020078007180303940c6001e0299118414082d0050b40c0f9465644244051092220001c562040c00c944030940c1c0354113800e803501c1c110301c000c443c1d6008450001604500c81d02c0c0b541c042c1c402c90701d48000034051810405460000254005000070b8080c00b0004404002e841944030b03107000c4100140c1d9130704d00cd144944c100c908030fa221043e0b560b01d00b07170b4100c1e219150a04401c1030b5a414009043d2500155021926008401c9d002c46070300c504101600f151460240c10549038810181e403804504c102035242c42e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 176958561 1250 176957311 176957321
    0x11041406040305070b070c03020d030509041119050903120f040e0c0702060901050903010908130602070e09031c1401091e0e030313030c020607030201020a0f0e030a12033903 76
    0x1c0c02661041505002c40c400c0c05e402032000c0380c1b0800c05410b00503580e030f02003154800030080660201c0c0001c1501c1000d400c180c001c0b0160301c2c00e126007007132a01c0c0e80c4a00d118603108074111058201302d408107420b0090b407810491360f40b01070030101003161550f403880716100e120ba2050041522500103000490812894001560030b003581c001c0200d81812502c5004481d55080840026070642d2548180d4000ca41081e00030550b03c10150421000d1500b4104017071700e002c00540c8030700c00705002d0900700080014040283c0d120b1501c0c2c0111000c000c0000c1c4c80b00c501900d0740d404080a00c1520304000200b006032a80700c5513a60640b5411450000240d82400048a0304401031240320307001000024141c1d01080d0f0b4502810748a820032581800c0141c0100c4c1c9190800041100583c4d400030324600d0140c0c118010302c1c03081c02e0510b40001c10104400120351140070401e0003c0102d407900e440308000794000d4105508005403800b103015032900004031203411400403030402d02e181003e240740400780381c0f01e4011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 176959811 1250 176958561 176958563
    0x1e051804020901140d0606060e010e010e03060129160b070807120b0105070605040c140604060c060f02090616060501120f02060306190906030c0b0715050603010f110414060403 77
    0x42081c984ca40240c0040d03904004640c260301c03071001007054002691611400025180035540e044085043c0d50000d0041020105850b052041d044148180d40ea030015a544c1540d16080600344410600412043c3c40c02c00e10f811805e0b03108004c10101c0000c4e0154540300d110341d0050300300c507969031241c0308280d6012109951107070000300055040c04030340c0199004000380c1101807605924140440e1038075008c460050f0b0f011502285003440c20030004808106e0344203c003000b00c03603646c5014079118000d0440040c6402c000d207051b880380041812403080c1d6041c0e036000000901215139a20b061307007003207000b1100110100c03030552801c000410482708203980400c0e01a0f00a1b07040340e20441c01e808104507504018849640b00201caa810600c035003000121708018070100402040d900d09516000c8941c40d01c1e50840760000340d0900c11b0034041802c041048140742c1c100740d00082c0c1ca440303620110340076200600e5550003060400b8110150f00144c200104101e400031010780302100545000c0002d54816440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 176961061 1250 176959811 176959819
    0xe0603010f05010b16050f10020c010f0203091c09030c030f0302100501051012060f080a030201050601020a02010c02010e0d021504050a0b09090105062b0f0f1518061e05180402 77
    0x11052818801e05c1440c401d49026008485810810004662801030500c0681c8112500411400d034408024000c00740014110003042d81140380411140e5580c101c80301070051600304130243c0600c0b00e40201d81000185030040d4268010546030304103c1c8645510f10400c50051045007040c8615004901c41c9505135203004003107003001d041c03004048035840c00c016180307100c10390f071000005280441500d50900425605014102180759801e01a003110001002581990031000c80e000041c0e0388405081c1120381c0c2400c18403400410303040415180040c0e404007c1d00f1a0002e10900c0e00385c1001c1d07001d04101d80e0200d0b000c03611070742c40c1c07a8000c206d0300401c08030300d801000c0940140300714540758015001080c04500c0c0007101c0014220f69000c640c401780f000c4000030350b44c0c40e80c000c520341c010302852814071800d4409022824201040c3d1200501503c904246031420110486810056410040040940c00c0300c00344030105c0740a1400c03600e081441000d107d11041d40941004040500301d552045130024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 176962311 1250 176961061 176961067
    0x60301050c090105180607050a05070e01060804020603150d0309050f01020a05030a14070c03060603030e01180e090a050601080717120409020711060c10050a09050c13060f0e0603010f05010b 83
    0xb00549158100b58083c541070004401440d0840d20758101624089005000900c120900381c1840d9041ca005030304852098221440140305035500002c0d281d4200d541554025078940e40c403642c0c14410b1050a01f000d0b03015150350310140034198441c1c504000d45000712040144c9000100059aa415071960300070040c1d0000d2000110183c094041002c2c50404800080c2c5045141d40c0e03000319811540d0411208140d035038009006141c0d200c20642031415017800d00000102021000f20302082c030301c0c810040740d1071210300040c44004041c0144100710303078403100b15a0350756100c3c82c00a446542c240144c605402013803941300c459603000207210704804c0110816074581410040c100700070b544450810b5a80c201d0750700c1000141d4071841c005105c45003c0c44090803070340c1540b035411020b813040600300081c100c0c1019070140100300041150004074004840c1020308001e8101648098801640b24400e0000303250b0000803995a030441203446482c0480007044034401c100f5003441220428094100f10708418 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 176963561 1250 176962311 176962327
    0x905060621040f080d0608010501050406081e030d060314010f0b090a090503041508060f030d021b120102120703111608030702160b0403111f1b06140f060301050c 71
    0x8450240c11500031103403000ca08005071038008417580708450724070701c04d03075103c0c01007024010a1060502500044400380300d941c0c03400700d5142c0c0c0c0e2944203035614524549900401c109000800c21500c15044581c41400115a0380c201840e41e84211101d80c0101d508114401c4140030051144070b08240c0000d09070402901e40101c50002010741c540304a580744020080070a601504035418442210340380d4610480d403910400784080000c8405880e4000c0e07200c00101c503410358002c900d14910100c10f1101035107034520240041d81c5081c00d0403001c00c240d403000894946040c20085054803500e265207060105501042d03144100c0e00c9044041c4c403680030120090b00005040c0700045800140c184111034101d0259240d00600780800e5000480504000600b0010404e81105a001071700f022600b070625000c543c1d004014090b08036010104002e10041c0e05840840000e01c01e5100c1074200104001c132894114041a0055080d50341c034070a144080002085407505026107413080044411482c180102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 176964811 1250 176963561 176963617
    0x30402150a0306030204051006021b030325060f02030f0c1303061a040501080609102a090b070b100902030403020a060c05040806090c100f020a1506031203050109050606 74
    0xc164020020140c40c3c5000001696860240034055680003906201b030340d14004010785084044541c104a0707601000084001c0d82d004030640e0341c0082118100c403ca559003801c02151031640d854000c1140d49000500d440c44c0d9501c0e40514451200503001c2c000e00e03125450405514003400d81e02c5201010121400c4c8005400b41d003100000700c01540041d1900400c1d400006c00342c40d026040005a5071061b003c025100808010040701c0d54081c402c100300e01c9501d039100301d0a140b101c0703c0c03803044481c1e0b001d003a081c076520030010038000380381690b8081d0715240b9070b10f030440282005841c100b03290f8003005030114400e031462080700e0045d90325400a0800303150340d64842010b00701d00396a2209109081c400001c1807a03040c0f06840c81440b0540103003140c4044071040200f9004498020340030041c6900420b1039640d00016408643c90304061005406103801d65004040d114030307080107021034508201c00300c5281e00350304038038145c415074002440103545650503c0507034014640103044006c00000c0400034101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 176966061 1250 176964811 176964817
    0x140412081c0216031b0804050409020d05030a08060108071403070c032f010c2f03040315090c0503011b12020d14040b090106150f11010f02070204060b03040215 70
    0x1509225031600101c100da542040380c1080040e0b4030702007005030b50401056400030b2203195011419a2407252204680c480d2840c9020340e007e528001d81e520040301e8103542d20300e24200040e5602800f02c0b42e44880c1e440008001300004e95503030340801e8904000c03800250054101220403511011582d0031b603074441508580044a00341c0039000d0000580c00c0f4101c0001c0e018403070031052003102d03001d21400c0e410303154a400c4600c40d070441130070442040201300000301003158425034484101294a0505078440035107045200b154070051098081a1354140b00031390381e400c1169103034056040b40070003d9480050500b61008002101c101b44038100c007543d45c45010b100d000c03408c07000e22140141480c403403600c10400c0b0783c6540300000d00760f00000c04110410203014141940410214000d100603494030101d01c1d2203407a003c0300c4005008070b00030f90481c050311401c2c40c0c42c50a1040002400703044c000d80c01d0a0000d600801c4240d000764201f180206a0809503001c4a008960107858000301c504c100c05030404d150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 176967311 1250 176966061 176966077
    0x703080319060e07121e0e03070510060f030f060e010c1d0d0507091a0306040f150e031804090b041506090e0709090510050a0b0a050301051303050307030b0a0f0614041208 75
    0x506c03039041210f490b0381503c140003201003488015a9511803604045241c00391480302c0314109030a19006001100c00e252408080325446404007003003412a180002c0640b81100040c0041d6280403814400c060307101c1c40140b0400e1030050640c196281c07503414000d903842808000380a9603c10700b000c1100c0c81c401d60140142030110401103402e604484006802d201050300c2c01d1328103000b0706001c40c0c180141210130300c2d00780c25461420003401c58568410390b200d000c1c002d141ca185403000800340d01182c440c0d4006030421907110320290211304d80b0f8039000903c0e000038a07107040054903008020400e15018480d00c034051508400404009240c080b8240241102100480d200e000305001001c12444a004070340c0520910340c0c010a0050f49101406018a060b50010780f281e0b0616041c8031104201105c440c040a406141c40b540c2c0340d5507054140c014040100207580c200b042003000013031103100c211a1130b0544900f95100c00c49c82000c1401344c5d20714011402130714066114140004001010310700100f80b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 176968561 1250 176967311 176967341
    0x3110f060610110115090506010c0c03080f090301020a080115030c0c0f051c020d0f05161112030c10060501020607050d02030910020a050d0b01020d120b030703080319060e0712 77
    0x120742c0e082c0c1000d00392000d5204c3c0c0c0e10442c10340305090280803047e004023588802c0030310380005481a44e03101d6000b0745189100162035041d0000f60403928a0b516000c031140d070107024000f50742d103c0640320700a10070b0500348035000040c0001c1c056880414480d018144040016944003018046240c4410b40c018900f92021146489003d0305010300446070809074240d940640c011344111441034101820a0003490011020000308010558060801141c0849019001111002d41000d1680418644400c042010f503036880040307030b00d440000001030b56601481c110542403003030580d5040166525a010b50358400840c0c0144031100210001e036016560100e4042c084840280e443c900c400100da000040c948009003000a41010300c05c540d00402210302020310044c000f04421300f4000380b4904640c00191002e58450400c2220f6a5040003900c0203560060112562410000d580d145901800c2d02032203500c9062580c0014858141c0004500c10152034039601c000c1c40342380c035000000703100c181d0043c406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 176969811 1250 176968561 176968577
    0x20103050a0614010e0619180b040315050912031006030b0418080d09021e01031b120c0e042a03050705070807021c0b10091e020c19060903110f060610 66
    0x207c40b40d0509a015088058071041070015200d20314145691a0740c0150b022034800704000c0001810317a00321040d180011010000740c5442d1189900c0c1020b21000e64034000500200601c1081d6440720501011221103440c00c02c038440c286024001070720981580d05c00035001a4601c00041b8110a00408440550300000629515694000352076214103a2001003000340d000d60000b11542c05218115002c0c9403200551585801502d0041101802002120743e8030344559541080078002e1896000070f0100900030b009031200c5c0c2400015a49480381084428607500c040300780c3c054001c2c4210741c019089541c9107031410503d5105c0340300c258070460007242c01403d5800d808000d00000303190988480c1c4a44101c20603403e01c104007050a1215030800b120251900d0b003160200b1031040d031b41c06450b0003003001c0540c035540b5040700d42d400c0469800707002444011140f042c600300b0040e94001000741c3d11a0303e681d0b400040180489588a40304502c0c0310b850b43c042c40214005251002200a00c1c011901d400d400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 176971061 1250 176969811 176969827
    0x60408070318030f0209091519020c0114040303060608070206040609020a05030a05010b0109140a0e070905031b03060a11030f04060204050607030c110102060402010f030b03070b16020103050a0614010e06 89
    0x100d00000e034015641456203050200840c50203082e1550400340c194020900485010840800040080c110f204200b00c03411140380749d400302d07405440742120b148000b00700c0058028802c90304402c0803141140000c2c6400c1002c02c0b544c0c0103004240c003e000c640d0090500c0c1e0307503d5841c00b004288000041c0d90207102da1074000f400703075000c00110301d0481c860000844c0d1522580000340c00b40308103401400f4038050001c1044a00e03240d40c400d0008035580100101d110340c03a104004d99510300c032504031795018000c50f86148441c1070f0036854000101c1007542121302d1a41d803000154101c444201084191003820000708182a1807841c54541003402045d00519080d80c2d0300005040b903004500460224503d0a11082404020070840043c05400e0005c4c100e2441c0507400203050302c1c11400c0316400e051352001200000d8900700b02c09400b4090003682a0f544807044a5903080700310748210100e00203404c0a0005212034494091002110402d1607039400c0f15012030010760304042c4400000d50410340900c0504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 176972311 1250 176971061 176971097
    0x3060504080901110c0d0201051c0e0a05100203010605041502011506090911030103031b030915050309010c0f02071401031104090501031707030906110a02100906021009050604080703 80
    0x2502a51082000a540700607542c005007883c1c42c002d0a1000d29003054000441c1512045001c510b50344e8240307841a521400741c025000c03121030703861241842c1846d200100000000001300051083c2c003410031a20130b0741c043d0898400b6480309010b000d0001c1c03010300c0100201c9613185081d5000200038000402d00400181c20040c2d03005041d440000026007500040212107141c4c407d40d80900c00600b019407440d0f0441c0c4000d841418035000d21107880840a01ca10141440b985588000d086036031050600040548801040c607001030b2500b01040d4a0800d0310040c3d2802010154140381c1590080c1c44240d180c000c80066115240c0000780c141600e400e0360034580c0c2c0340c1d04000c00c0508039407000065030354114240041240d10341d0100440050007005a42e01107600301076a14221402850318055140c91660308a00b00305017541e00035000984260003140480d0440340f40c3d070903102994202c40d24950306009100590789281d0000d030040e0403a00200700461b01380300080211034000c1c01c01903074000d8040b081d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 176973561 1250 176972311 176972321
    0x40f020120100204050f04200309030d1a091806040201031a04090501020409050c120613020f0a0207030b07020a031409060c100912050301030203031204210309110d03080a050c040306 80
    0x42c40b9030b41e4005400d00007440c1580010661034020b850410420000d175030000b4040c0c4a10b112080000c0003c00019a40c1d0810030848020807400c40c014003040100c848060000c10740f52502e00d11072180000003e150702070001d19801d44640980c010071170354890b23400650080122101c50183c080400ea810701031500c2d0b40c0241011240315000044e580d03454002554201c94014110b110030000c00c000c446107000c51119255003144045580b0301e2803188843c000c000921400a540e0740100011402d52000c03a000724041c0f04590140041c051260b903035500880c0c5400c456100200400c510064012804901c1070103080321410180c041c1d80f800b000240198640555480d2918160f6225000385003080b0304605c4240c8018100c2c2421400d650540d40081c0d10fa000d07426074082d102c14501e0003e0280580408154603d001e6250071000b282c0f040380001307000d0010300e44241c503100c80b01c0440c00300b0350070070810021041c0c0d019516215940c6a4101c2940505000f07040184030344024000400400c5881c030030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176974811 1250 176973561 176973583
    0x15040606120308060307090b030303150a0f0308030f06030d14091237120e01140c0106301e0b0a0b0909010c02030d09020d0f0f1406040f020120 63
    0x1d1003c4070b02e0610201482c00640d6001080e01d182084101b8841d07840000c240c0ea04040030312400f40740e160b503400200d444400a90300c052206000740d000002808001c100550003003040119070300055544030709055803020500d050400085607001080502210b9001a1600100003087c0e000f84458070a102e40c58224408801c0f4070814000007200f518003004003d0b2203d001010149082d0358189031190340035041424200301c140420004c8080d5160310503c00e01825000c1c12280741d48400035030066500900b6540140070312208540c111498184d98026401100b441f103413040111390441b6039a011a4000d40e0f101c4101c486000409140010703c010246131052901540004504041c1d8007040b403d007901038140360b0389074076011052109075404021662079504190003ca8420001d1002c12080046040d020f8404079606844c101081091041e6081103030162030301c81810b810304131107503855400990300103211041c4a40341d440194001c2e224584003c42c02800b0f8545042001800b60910b10384c960 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 176976061 1250 176974811 176974817
    0xb040b210a08070605100f0b0306092203181d011514070305120c09010c060b0102100603060b01140f070f030c02030109030e03060c040b27100f12020a02150406061203 73
    0x700a181c0390100d0311b9500a00040c1e507440080b9181110002c3c4511018103214000e18a000024030401d40b01c900748407191294200142111245050092100740c0141c165003c01420b5240043c040d2401142c1da006a440500400c045034a40400c1c42100c0303104e10380d810140108001c3c00c00421200f0805000401d000f91035803652a4860080641189001000c2c01e420460600c290780c016640240d040e20065800b410000d400d5500d0341c01070380303400e41e800b403601c41d09030606102004000c61034200d0030703c0d00302c2a20f607202c880d9268152000c60340a0054030400c110710600a01010035110008022042c1c06410038000400e81c9030007182c2511034506003a40400c9210005000318142003008aa000b064201e1041c14a030410080b015288920b10402c0810628242d45030071542c075201038401c40000c01440e00401c000c0e030349400303400240d8468016012400c241407043c110201c0740200c0d03941c042c0380da01801c4d0b090704d09620b94000381800740c0151400707640c401c00403400450b0030181d10000b034084c3d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 176977311 1250 176976061 176976071
    0x1a0c1c080f01090e0c0f01020118030c0501060503010216080a050d06140f0108060d030e12010617010b030102090112051302040c03142208030903120a02030402040b040b210a080706 79
    0x520802410601a0f100c800b4080c50454500d100c44c101096114020701c0442e0402100100c0200413800340c02082e030180e00030100c07040000201b541010b0ba4070040d034801d400030701507039640e242017500300e00880f0110801d1a076a2004080014400001000040c800741002400e0000c90302d01e100443c1c09581004100b50712004001e691031600700c0e26040e01c50f40910304000c107880d0140120386002004803000302845050911240159160b558600070452400000c0140c41c0d41e41c48511001070391100e0030f401e1940b80500f01c0e01141018000c40d00c0c0c06d034040e16000e05000354404014003c08008107500c241050021034080140e03107500a40006222555000c58182a4518102c002000c041d00d0200e00185d164400c6144880300d5030190203c035000030600d5120b1350340c0c01c0c880741540301c2d803011680c90411000403c22807501650203580a0341c000d40c4d00708105581c09040c0000c840003800740c240d1050041d841d9420503403d00b48511804500e0505480700b2800c81c1e5259050343d08100402c440141c0c0303074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 176978417 1106 176977311 176977321
    0x10b03060903030708010b030106080c0a030b03070816140a0b07050a14010615020105040309050f03010f0f0906050f330316050907091a0c1c08 63
    0xa41580e4107803030101c610329103960044407600046807001001080c0182c4501c1a01e0590340140c0f1170031a65245e9a0307140c42142c002c222038100305034075401e102902d514140090f80007805140010044c10702c50602d81c0b510240d05401001c88920705005185560b6200c4540b1000c807002112443c0e40c441c0e107402d0440c106822500c0207001c681c003101c1c0305101004158002022562010014842003080b51012421b0310410341d030140020344a0a018066031801001d003000110008000103549c0c4000440f2038103a50030f031090f400c50706940c1e040400a101482c040e496000985160080042c03500e0300304580c000751861100343c0d0f07854601c3c0c16000783c65038a10032201040402400c481070900c104428008400c0307640101ca0050561a02048450b401030400c3d40542d01e0030411001c59920039810071a440c1c000d04510301882c415007265440303411100c0182d40017901160340b044054540 = true := by decide +kernel

theorem cover : BRFrame.Cov 176798561 176978417 := by
  have h0 := BRFrame.cov_init 176798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 176798561 ≤ n) (h2 : n < 176978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
