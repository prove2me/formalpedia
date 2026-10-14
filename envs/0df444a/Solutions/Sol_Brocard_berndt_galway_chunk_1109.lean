-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:16:59.784929+00:00
-- url     : https://prove2.me/submissions/410fbc61-bda4-412f-b3a8-b33bf9f8db77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 199280575 ≤ n < 199460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 199281825 1250 199280575 199280597
    0x9091816140904030c0b220b010341010207020411031006020d020615010201140708010f08060405070501050901021005043207030b09030c01020325020a0c030809040f0c 74
    0x910310303184034011a28403a042c80d1080000103580240240f00080d80720710140000c3d1249a81948550864030f900a185100d0740001c00c140000c00310503504803401021245124015800c2c0760305840d0b2015130301640c6400541030020040c60b81409072401898a100060400056900090640340050301c0c810001c00c004c001c0c040000b65200b008002440e5070b000030181d503400900065241d910081900c1c04014104c6035100c51a4003c4d0064070008145140c605610300c0c2c62100582110000e015140040051b0000800c0303030040019a68080c5070890000c040651070030004590300da0040b0052811070107000c156090318110b41c054140507074883d0308004038160700001540840c03400e6002d028200c035070000310aa910940498218140ca40215000b682c41d624042c1441ca94483d03104a80d903103620010812103040004809903c0e040e41c190503030402c00d001c40d50200d81e900c0c0c084601a00703800e40900208002106071000305503034a03016002080001c011303d000002c840105c1c0700c450200f0841109 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 199283075 1250 199281825 199281839
    0x4020109061107030b06060c010216050601080106050105030a0c090e0a0c08070c020f0d0203012c07050a0f180f090302010c080c04080c060702040e0703241109091816 73
    0x36031000d01058544000b000c45050102a03440b0101d1001800201c2d102c0d0116245844200c21038994122040c02950b80d4904c40035480184072042038207a03254041d040022901079410b0060343d04465050750b485c0d00b581c070780010f454002d05010300500d0174041c440741c0c0007841001121101f44074420412001811022070701001d0800b800c02806e9004002c5803040e05070050761246100c081882041d01c8440c0f40d080c1620120780144a0a46000d41ca041a484009010103a504d00c120b0f0b012140400e5030000d6527a03c0a10005c52003a00a1446045008405010b100040c0c2c501300b4840c6865200811403402d2548141e0840d504841d00350700503519150f02282c07a540115100e0b0b00558a041d95920702464100200d4640780c0c4005010f228000010703201c015540c030383d0032002010245005a1b214161349107410b40e80b404490030014008800c0c86141e011000d1144900d1b1070104d2040d1803d40740caa10402000300340f000040100d440180225110b6942c0c400401c80c1e14102e80701804103001d003a081c461 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 199284325 1250 199283075 199283087
    0x1120609050c0c011401060c080c010906111e120c031b0a050c011503030203040b0f071b18020304020306070c02010c1b050a0902090604061b140a0614060f12120d05040201 75
    0x41c0c41445090414010007d503980203040c005801d4002400035113607030b5010489405000c0e0b200c0054a005c0c04e0818040b203088001c8014100322041c2e202d205441041c22071100c0540c0140407205401945000004503042032400c021603100f41c0c2405090200c11140d0410882c82d0000c40d0204005100883c9181c140c0301e00344100761809943e031480c4164245103540080d0340307204500031394040b10404034044091b015440c042d2000c0580c0a003c1c0441e03000b00c9203079101c07005518401d60311758510010400c07661a01d113208480c065a00500130f0021651038800039501d02d0a05a02241049042010503010800c03031320405100800510345219680c0ca80010042d1690050304081100c40c81004040c0c0c0729a2458100c4040b140d5606140a445500c182c501005e000038440c0130340b104d085084100c410b0000840c2c2084c1161040004102c440302040b000d03601c4020842c0c10340e0300030700340000e410000d14107100000000c0306080101c0b405510381c054900304617000181c18500081c2c984051104560700f07c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 199285575 1250 199284325 199284341
    0x91b0e040b0609041101210617060609070c020409020f1305090c060f03041506032010050c101e0c020106080616020303070e06120405060a060f06020a0201120609050c0c01 75
    0x240c09200505185e11480011030080c040c66051040c01015488a00c01c2d0b9008481380d50000d4504102d260307510b054540e2090070f00d044076070050040c00005001d5180000001d4010a82c0b69108030245803568240802000c2540c17007640d00031540b13040c400700d640c0c0300303c4000c1d2400680580030071346042220f00c41740350184401401e4400e1710140809560004264140e95015401c9100c600700c0101c1c0c0710520700100700a800141500c88281c40d500a008682c081c42c91191070181c42c440400414801c08071224043e0212a401542021384010018441604112100002000001007401104050000301da682044420161b51280c0303007003000d41c400b07204d9070b036001009401408010300b040c2d030300039240d1000030030300c3e414006600c0a10307402c0e031100403e4617180200d43d00b0800c100d080c00d050059a603c0c00312400030185007011404216101108800c000f101c92a03001880d10b03201a900554001b00300c1c08807030741c41503583d03440019401100e028540c00ba14bc7c0383c412590311010351085500750f07a41c20f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 199286825 1250 199285575 199285579
    0xf0213021b06070e0108180f030a0206130210030207110a09090201030b06030601050301120804030f060e0613030518150f0415020703120f02010213060206061009080c0103091b0e040b06 81
    0x100100070f80a600044070000d81d2009107440901aa81c0199040c000c620b4428080d007a84128407981410380c00010080000c00030030340071581c43d41e45190100c0b00c0540c1c1d064009400400d10389030000040d000e82c001d0721a080c400c0d11111068203160022a0015485601c18000c864403030b00c50030155600351003103d41c03400055070761520710316004001030024401849000b0a45c6045040c800c24040f180e015540a5581300003c070f56000614106500549064440c204183c050040410840a00001075000e0907070700d51545400c00380d00c000140ba200120042068104d40610b001c40441c10f207080040101210142e1002d40303442c100354004031790f83d5070070030041c065520040b0103001003520038044a07c50030062030b0006014000d41c004902901a1548680088880c408045040d68011884c540b01e50400d95410111a85015040701c4040051091913010b812601c40384006500c241c10644429002e01c44036501004a800415421000c46c0d000b00340c1c864440c1e05105c204030406042640103602 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 199288075 1250 199286825 199286833
    0x71a0702100f0506180c041d06010305070509030a1e020a03080a09050a030b150d1b03050c190b0a0c08030717010b09091801061e031703090a0305070f0213021b 70
    0x1c001066080301101c5174440003e43e0703080096000140d02c1c00b118090242c80c00c01401a1444a500c0140d000d402e40e2581e022070b041c6030026103e103201d14140c40b01000c0013001842096000c1e241d402c0c02c0b2480703a0346907030318889401060001da00d9116801c2c00951092036503d0741c40c00b51400040c4080718941005100d04a450b00400c0464024a1005d07009a84803a91540060400300000c1f0103c504207030040088920b81c2e9000d0311044800c4c0d24604a03400f40090398a0740000a04011100400c20b10841c0d030400780380d20500642c41c2ca8000b4000319250349c28000420f83c2e5548800d07446800c200e40721000901c0c41903a14210180c3c00351041d00404403c0d40050030400c05000240460324000c00038034210603071400c003040c9403409400800040c00311844442441c20a20520007000c610b80c001aa5a10085460003c14103440f10490f442246480054800e404d1149e40440380741d400701109503503152240c044040582da61040c0307078245030f080c04001030381c81107071900c1903100b192034001161481e04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 199289325 1250 199288075 199288081
    0x215010f05150a0c020904050a0606080d0507031b0507032003030708270a060c0311070e04020d06140a020a030c0f08010501210204030501020c0f01060f060302071a0702100f05 77
    0x155400d0340002c44207919142030b124039002c1d00449541c101e08502a62001403003040c00148240440c07068039882c01582c0910020b0748840443d40d41fa21203045507000a0010082040860b04c1030fa00d450001d940b41c0124280311481f1348903070303103001c9803074000741c0341c15007201400140c20a510700c482c50403003000e9000d141000071585032400c8500030b03881c1c0402c40c0d81405c0704080c2000300010007980305c400c0084c01b100c16540c82d194002d0040008120440200344012a441c1d5190340007d600c90485010308008051940c4503400c1c004c0c01604800300722a41502c41101e413203000c504091082c40f800208100503251426404001c1c1580c0c1740000300c000340908160b100c0710f0540d0280e00c00c0d065500c282080150100a13006118074031000300ca0340021f00c3e1022801004201042d001414400c2d00700048690058810b8070b01803c0740d20340e02c40d1005844020030104003440c000d4000d0b0110a02810728403920002420304070301088000c440390001038212210072030800085210740070384c02d00326075820804c0b0710b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 199290575 1250 199289325 199289329
    0x220e16020601150c0203120a1710060e01120c080f0a0504050d03020f1e09210304090b0409050a050a0b01060201020c031b011506030510140607022e0215010f05 70
    0x7403040c0141c009006206007182c10340c2d4000c4014401c840d602030201d54a4680446c2c0c03880301c0e9003020f1031800008040c0d140b00c200102e00308101c0c45c021030307400a507000b07000d24000d815600c68003081c0380681401f000c401380420b0301c1c0c0c041c4541001138889407904945032600800300d58441c14001e146003031191130300082c40085a00010720701c14514840c140140e640b580041141903c2c0910b07201e11180307600c00c003147d102400c60b050150603200c00c00e80d00800062a007a40a21800c5011604170545900c1448100b0400400d9040070b120590054400035030041c403901e03800d080482006054900b5806803c07940c0400c14080d032446d0050629200031410110b400030800c0d00c9126048181c11a00001031a10441100a52040780c10240c00e64101071140d56030316001c1d020300000c40d01d40f40030042c2c4580006050f01610300301c0300700c80ca0041c40903190038180d601700103018512050250b902a0343c3c41b00d5503040c0d0348170a500301400000343c00418020401015007142c032034050700080241c0c46d83c10b204000030707 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 199291825 1250 199290575 199290583
    0x90903050d1508010608101505011409010c0b0a2c0703030c14153306071103010e0a0203010b0d03021c05090901140907030b06031803220e1602 63
    0x114100300c0124101c502e00e20034600c00500394000140304e510b010f00c0059200390000710b007038a500c10300310144400c1c841d4060303200509041e84102c0303000c580d00700d12070b814004941009040c502814103002190507501d441e00b89100808840c0740144179501d00f0b0361420f8070b00039208980e002600b0140440007540700000a5290002488002c050140380c0780ca900400017607080d50b500403041d090448601034804030300c00f0138040c0c080d144c2e926089204c1c06507410401d80e600b110704c0c050822031452241d40144200740156a4003100080ea905940c11461000580d801c0c0205c028410040004201c18051401054212110f080f426031103092001c0048000903000318141ca07032420f20161011880381018400d881902c510ba41c05e5034482c105200120700e03c20052604c2c9513a141c182c910f021556aa410150100e8001c040c096520075010f00010b080903403d03800f10150503001d082540e003400e00d89d800d8a000084803009598040580c0c020a218840c05501d00c10781c4410f42c00204d1134881ca040c40e02a40fa = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 199293075 1250 199291825 199291837
    0x6021509030f0702060d0507090f0e01150e01020a120305060f1c06050c040f06050d1b020a060e030d0906051602060f0a1a1305011e0f0b090103140103080306010909090305 75
    0x41d0b44000b082480a5580700403e442c84410b15100510540c0390110000345003011502a81d400107080c2c060100e1949840941c02e07059a10a40d40c0000724410000295114126040e400c0d04603c184488000064005040500d01a840b03840c041040d0400e20100100415007400c1240034681010403041c070351280d265004a210b800c500e0002c1d46440302c2c103030310005100d250842c80026000c03010014403542d00c40002c003a08040c050080240403c00540042c40c058441080d0b0010391120b00d403680455a15031046c024841200d0450b0300e0298151400c0040d1184e4a8090352001d64400c1084074031000c03111003044012040c800f420903450b104407803807440100540103290b81382d46c0e100380c0e55100404001e490320b80e0000500d980c0c603000510341e5500281030240a046203e04030400010382510040c3c3c1b1602c00e498031000950215420846000801d412085e0003504051721a0084c1e40c50308a0140c0c1e1030301075400f403007030503070741e45002c000240c9609603030303030040d03425a15117080000465401016601 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 199294325 1250 199293075 199293097
    0x91b040906020405091303080604050601080601110106170106090f02030903040e091219030b120c0402130e070c0b0105010203120c0d0b060a0f02010e0c010c1b031a010602150903 78
    0x9505900e420510001c1c003458000ca508000303800284082e1540c01010b10701c5082c820740e40e240380c170366507801440207a5209a808a02141564000c9022507000f140300e01808007400000240f0b0f039960b4215506030700b50a00c1d85001300d03559240107214503005070042c6d280040418100754074609026910a42d20b11440c07041200344403015000c2407003005c00f480110801140042010f80780c59015203445042400c101ea6500443d00c1c20050f1512801d00300a9502416540800fa068441051040c00060760005a80c40c00211030010082a055011800075010304c0c416560071072200b180d0b18241284040603000b4905544c810700150140010140e4820741c0030f01c82411040e2644c1d10011514060840c465400d42d0124012072884000fa030300850021150754594001d0141ca1600d202031038442c00b01c20b10040c0042d00140d00c000110300070440e440000000f40b003214200c281d0301c0c1c41c1c0813501303032100c40461105d80b44100100522503041140c50030348400e17482d000e030050030104401d90f034a200e0303000170302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 199295575 1250 199294325 199294331
    0x4020d2f1207170106090207031706030d020601120203030412050c0925111504080310060305150105071b090213081b04050c130305010506040c1706010305220317091b04 74
    0x9107074880030340100c5d0090802000564880d001440c01908094444440d40a0300761642d000641914001854a04100064014202a07400c24503210300034000301d03c0a03601484200400501004a151400e0816003d100584a00c8031110700f000103d55003c1d01c04800d4405c9040d4000a21011007490580741d81c3d18208183e5160700402141e0510001c1208030030744200d030074100010b100c0340340300131403142d80380844101001e034682748103600326002a101c1844039507404090900950140c4014500c07079000d1005030342c1150105010700d0010003660885d00340e0540100d03100800c010240440c4004c0d00b80c90010700b8000d401c201d1243d88000d00c15980b644159128404250301c07501d21000c458081548804203000d584e140d0400c41d0103480107444041c001d43c900302c0c1d60407402c0e108c0d403241468510700443c1c40300c2d00d40302c290044000d014043c043c000c040020b90040c400c500b4000c2100030310b19120ba01c2c0c0c4409134961100e504e545000042c00c810700c64016030240c0d104030b440041d44141500d4112800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 199296825 1250 199295575 199295609
    0x9110306040c14012a0210020a050a0609060e0703140705090402100815030106080f07050406180209030c040f0c140c030d0e070f0e0a0c050403110904020d2f1207 71
    0x4981c24054005c0c1700410303211982d2400c03295a29440c0541009000380c80c249a260400030381240e03200e040703110280c4607030464030143c00043c2c0d641d0022600c0e14014003020580001541c4a6400c2130501e42c0b0403644101e04502c40b00d0529414040d00000708030131190450f0618154011075130152003042c1040802044030009084200c012050000c10f0001400802c00261a403c019985903910700d02001103104803100060180350500443c03094030143c0740c03c0203407442180c000380003a4112610741540360281c1d6003110011b4403140704a0f40c44103c0c03028082000381818801400e02010030f6075041484004121b14510b03040c00204035211408030200014080c190040d003d4100718540d0801142e0004560340010032030440c1d015140a1030800e5002c11407400c404030161030501c11440000d14a01340200d00030341c2450411a03440d8880e00151071248026a95501d000311086046000c50081080c60303100c0c441c50101c40c03060300c035541054850740c04406045c0041d5544071130f18070910030f01c0300c8840a2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 199298075 1250 199296825 199296827
    0x4030c1806081c0207080d0203070213020f07080304120305010b0318150906220c14060d050f01080d02120d05070c2001080a150612110304050109110306040c1401 71
    0x124010681c80d03060700e1030340021085403640c0c0f407881c0c0c40070b00041c07054030408100301d500400c610024503501d03001140303084055802d009002500005940c2400d60074001c0003001955070f0002c01841c2d1140c88903035941e142c00e00e4845407911036001c0503010985002e0041c4000c0c1c01e102d04030394100764a20740d0140d9454030701030b065151440300003800914000c0141445040c403000a1042c0c0034000c44000d8000141d9201a4034003990000368025102c20090b00c1c0401c042500f1027202c80114a024115500e00307042000c203030081e107400303540781b04698040c90300400c0603a005010310759504001e40702602c20703c00c0448007054079026000000f450b00c0d40e40c6010802e454011106542e44961101008820b80203100036000b0b4032030b04242141c0882c7d000703400110086417a200b144c0c151f11500c0302482d030340ca0500608558080412810003001c07940d610311481e9801c1034a018600c128032540000c5010121460303c1038605c011002d040d4000ea10002c00e105c0080d003500321100641d904800204241300134040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 199299325 1250 199298075 199298081
    0x30c0201050601120b0d060905030702010201050619052b14240a0218090702070504050c03012304022205030709020408190f0c060c050d020607051204020d02040509031b0304030c18 79
    0x240940d1230450321408103c8084007902c880c9000340c000300001c2e0303541801d21280c00300000800d901d4040d03500d8140a649000c031041c80b0360703d000d0b03292100100d45000c14280516501310090b5641c82c42e074104225607840802921030166019100ea21070b5001e441184c0c4910140504802c41d0a60007250340003064640171540e004090340204540c41504012401035100c000324004c02d40a1800d00c0001451a000e03034044a040b69219402d6510071841c00700044000c0002c0310705540d01907001c104001038507090090000e841000380c4803041c042850311007094545002544142c41542c0144410444a0b0001c90362200c4111072005012180c54240351a803081b010b4404001c2c460a83e4080101c1c449900214102c2c1140c4140200c0762880c010b82020b981e6010101d0b45034000030300801c034041c182201c3d0540b25070410310141c003400700c84007a9400101501c804a58000003503001095600200c403000e0354940341c041c41d42c0042c40c41c00d815038481303555151513400365100390399441000c07040349a0319034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 199300575 1250 199299325 199299349
    0x3120a06092a0201200f090d030801031406130204090302160f140a050d1424010608070804052d060103050c0a0b090a0510050c010f0203010602012a1b0b07050901030c0201050601120b 80
    0x20048c5168140398900034100c40820702040d1075000c1301280441c440b0a0004010b40914000401c0b01d01404e400e81c204806040f806800714110700401880340005802c024800c005408200511400d40381031056049007141201c000768450181507900f0440707503c580640d61004c0360488546a521101003610515189003110800b42070301900400840c94006000007a0580e02d2075642e4240700d0b01c441303100f1a12404161006400754209200a0652819609a20014206844007800c070301ca1803c40c4141403490076401900d568100954400b0280f500b1f001402c0540140300c3c2280c2082c60a00c0070480088641c0140d500400660450b60b94003030052080d110883e4958000303002e0001000e215401070b4000384100c0016600700000b41203030411100030604007a1019440c19485e18210030101d621030f02c0d809030580c0208103170030400d01007000d0000ea503106050f41c0e01e50300e55841c80c10740010308450707016849800b16407420090010716a8042d24040c5910303102d22010408410420004030308800340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 199301825 1250 199300575 199300579
    0xf03050f040b041403010b0a1503060302090f0603010b01080405030d020a03062d0f050904060b3d050c061311040c0c0204060902040803120a06092a0201200f09 70
    0x1c03400045100c041c4000300182c40c4c034982c440400c28000d10138142602c00c40d0308140c0c0d10501d0810309000c40d92940d49260000c80d942c3ca0003150641d07590700860708000301540c46200c2c26200c00d00f000207071305003401000f8120f202840c20080d14036091700c0385c94580c0510603041e2000c41e0002040d12406100341c000401801d035004010418030b000030b910303040b0034950440800c000070b54801c0016049005e4424507040b0f602c040d01c1003821b5501c554441d0003c0100c0f4400a9001414441103002c200d080c09412290065595911200341c1104000600d15841d81360818104030041091103103c10011620541000030700f1141200d21025160140c80d441c0c2c2c03070700c4440c3c01c240741032081c1d201d00340d0003141d001140c1d001340c60400c6001d403109151420f03440303180600c6420b50f1040040343e400b00c6468483c245d01c03c0100000042440e198a5154141c0e07040c0540701042c120705117414241c0c40c0b07140018807042c5106000800003034040844100c1c49041c0610003445280d804030704500c011440500710b865038840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 199303075 1250 199301825 199301827
    0xb13050a08372003070303050402040609180606140a03020f12060c0a0815012c0904063305060702060408030c03030115020307080304140a0f240b06070f03050f 70
    0x41d80d551220340c0180d90081000191015500c0f8040c081e50780d0840007102112005940751821503203095003c0c0c18064012a0050381d550000212102ca501c2907034000f186402c2e945a00c140345050400549603150481045002c00c2c2e608000b8503550600200110395060b103141151100c001c1c0021800102816544800c0c01000c08201e003410a10000300f00c1e2000c10349520129485002c2c51201c0542d54010450210300441c0f1040368071084101c2038072100341c020302c0c031020413420100481c844001c20350b42160700360717210340384004030000501c40060139000400c4540c60840326407070f0500d072840f101c0c80740c031340035040001c0c045055403500c404940c003400c011002c41b1b60341c494151420741c1d240c2c000d1040c64400c40c1c0303107650744035400d1000c02103c040c02d0700100b1075400d54541c0e17207440c410a50700c2460207095110b07560001e40080c800440d1012001d01405100a021800b14507059007030000144055038117181c510404c0d955541c2c9029294090b40180300c51440c82c00c10300c1d0031b5a2503c29055110000c82d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 199304325 1250 199303075 199303147
    0x30c070b070509030a0521040f03260c0d03050a05041220011a011b1a0a0609090507140f0a0e09030918010321080a110f0a08040b13050a08 61
    0x440f494106019003100c402004c240350240380600860140c4e20407840311209c1000801c40d05011980c855038bc41260007071803040350700504004d5128001561960700a0146940071a404d4800c1e10740c0645205020b03ca01c1c43d066984500040c50b6400b06010303c000900e8031624034103030b5044101c8441414000300403000d100740b00c074105162060305840c0000d40014a00000f420112001c1d44403541c400303a641950040c00030100c8403c00000c003910300c03a40d030300c0400203030700000c0c0d0040c500164060382c00340074241e0500d5200c4040c603540d05441c50080181118000c5a921400381020031030f0481d0303406401c1038460301809030942c0f0958500039031140c058080260501a550b1449040b24030561a440f075000c8051941a4140c0b01c801c01c51010810400000f40b103103400c0d4102c1c05205029a0301c141c9414000900c20100707820200d000d4000400074003c01c81000183e91080390010241c58156000540a80c0c0c0c0740c1d90b03009c071120020002d000100344000180c650a600c0e10400000080d444444030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 199305575 1250 199304325 199304333
    0x3030b06070b090d05091305070e061b07150e090408070b04031106100e0f0603073c140112060e01061e0e01020d0309110301050a0e060c030c070b070509030a 69
    0xc14151000081c40c0129224044414014011106d801a0142800400344c0081c807143c07004010091200050081e504007441066441c03000410b00040d48850801d0300d800c10101052500c2c1494105c041c001c80340032804900f03180c000c1048480c000702191f020219503110f20b0191603d0180d908010300641040e42400100341e00002840e00030a4030604880c40d6645034545011101000d1003141d803003920f1071001c510301030680b520032030f0322a8016003116001555446c2c042031681c030b0600700e5602014205900090a00c0110b000595274403200b9117070310b005080480c00308482900c02001c0741407040c03c41840400e0002d58005400422400141110b903680d15a006408052011240d2910003a4000004102401603211b0701d18100d045c0d00425490110b0300b0203070004c0c00c41440541304500d00120103549a5004d025051048668006c003182a02d5035170040b40c500000501880e00802080c4100000040588181d41c0c0700d0342c21006200064031446015200c61050b800240e806000d81c000110600c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 199306825 1250 199305575 199305593
    0x901151e0c12050f0405090702030c0a0b0106020d02070b09060c10090803040c050301090b04170c06090d080f01060f0c0204020c0618070506040506031512070e01090501150e0d03030b0607 82
    0x1401010003040c0002c0c2c0c42c0003201c4910810b040140743c1d203c01c1c4030903c101c1c1440544650300581600450b46080b0070740b40820300e0003025640c200e8184182d1001031000301c4e0305214042107054640001c2c100c00342401e031a000c0a000e582d028601a10300400d800c020328000300291503e640010303034100250f4005040c001c289500898017600c11218a950004150905107c1c075041c468001000324041c0d1615602d40f8091564103250598183c4140b042d07010034107040c443c01d80100b40907002480f4050092034050850000100b0354101c060b4280010040c0c950010102107100c0620b180008568590f03200040090140b40d41c1081c0a1280c10100801e00b00c410318903007941c03041e5004950b07080b0b40d90400c2041d10b1186010b1190860343c1800070606c010744c0b8142200d23950000605501038900340c0425980b030300700aa80309001e12a0408010404070f1800d100702405000d40d0303054080426101000504500c0817100168000c07100c0503042020b00d8400e92011440002c0104515680c034480e0a000b00d607 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 199308075 1250 199306825 199306847
    0x2031c08060913020d02090406020d150312020c0d0f03031b08070e09150d02040e0a0f12020a02010519090504020a0504140d02151e0706050103110306060901151e 71
    0x1210342c1d50106081c1c2d203800e10401c1040e58001c052083c1d0351707150350a0019801028208035600b940030701c80800070800364011110243d00240c500340760680303141080c1d07045403201c80c0c0050640d048980003056a440c0c0c0342450900701d40050017404168820301d022001403842d00d05191041c0111100c04008030b500c0854940928496640c843c0518030003000c01400700416a0302c10112a481140c034202828108182c00a560004000040780f031880000781d8100b070302c00f80e4111641c4100404103402c0140342412a00886018801005011030940c0060b10610491540f13a0991032143d0170480139510030308042c004ec0801400c29522a5640703040500140c0080c0101d543c0070503280f00c01c1c078150030154001c03500340c4c2e0010030603000b060b0500d8031502980d10141c03402c01c80003504410307144100350707040007001410f1142e81d00140079827540c01d00c104000300058800c2d101e9044201803100c260f41d17000060341550410035081180005994080d036404191180b8402d4003120f0b02c520341e007401d4020300d480030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 199309325 1250 199308075 199308079
    0x1e03050105130501060e010e040b060703020c090109020307080103150906060303020c040e010519020a050708070308060f0916030c031e050a0606020304030804060f050f1201032001091202031c0806 86
    0x1c1100c0b480c62000240c03042405000001100700011038000d42c443d5410741c08015000d40005205541c03803001c552154031120007540560f0020003505443c2c200781d1041030041103002421815414041401010744030f0620010b0602800a6014010121103a0150400326840442000560350705d1902035100c82c04500c40c0c238400c61400c0250342805c4010302810380f045600d500e191030080c0040c2000750007900b0890700c2c0750400c070091101e200010f84150050500038001d03201c0140300d14211080040d03e01e084005240121821814046d40c0120506002c80c0b81d00d282c2000b050940f104a8110010b041400b80501c21841070042041d1000300c079803005005000c60f840c03d0090b5a01c80c1c0090b40d69100e42c3c84020442001040100080c80c0b1445090b003500249160191400340050003811250704154041c1c0400e5420301c1c01001080b0401040c1c200800880a00d0030f282e2164030006490740c5c40d1071055204429207003014204640e400d00007110140c00840c682004c200600d40c0c018400041281c4040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 199310575 1250 199309325 199309339
    0x109020f0607030e0603041b09090501270b0c090d08070209061818101e0e0c130b0d08070c0e07020604020a032a06020c03060c04150c031e03050105 65
    0x180035091080032200e096416499641041c02240240040c03948010815140ca4002282c550f003c3d14042160078001c0001c0c8402060f040840d003071050845404541c064003200c881d00450764440b860440301013400360400700492047d82c3d5440c4c0706003039200b40c0043d0b9030312180080716031041100c2039014092160080d44e1404031a034400003840020b244480d0388944080100300003c955003803012a1408050800054407082000416100305032880244520100d400d0403c070320703003042124428010005001001000c42a0403400400c5540b0b03110003481d42520b8403140c414020f6200c0c00345182c0304503440f84140d5510065030820b00c0719581c088c05010303c52500203001c40d0b0502e100054050003540c0051440e0284c51440d961682c030040385030034031a13a440000c1c200c0840c14801e26412002040b440c2c01504803000450700700343c148440181403401c049001d000502c007d15065101c40050300050801511810081c00d0236100302c607030303000a002081d5510415280965040d00024100d0b0300c00d480d0300c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 199311825 1250 199310575 199310599
    0x403031e090512070302030d0e130510090b01090b04030c051f050f180a0602010509150c180102070e040f020906041a041e0905030301060f020f0a0609081b010902 71
    0x201803440c000d1158240040d1090800344110700d0003a650400c00110142158200c594a6010070b040500e104441004030f0403803018a4404c0c00d00d0440c1c5128030280110822480c90070030f04003240c0500d680030307043c84656101c0c031481181e4080d041e5400034005003c0e5840d1959544e00e80600c84990303600960740144152903c1413010150303542c0c281c020104a844150503d04403410380d4070170323030400203a80da28a00030f48000341c159240e80f03902c2000762503554008116450240d1b031441c901345c021031030800c4404402d0304006446040b1010341d166403d90000150648240f240102d20780240340e00460525420360080c0b02c00c1004098220304840c1c82928102d0b02944c4a501300012582401040d00344030702140d0f121042481c044d8801102c4419124002d94884114150f030421200c00d450100e406a10010052003015045503503001c114403140300802d0440c0d1050012910381c0c04a0350020007036515299550100540c00060b035000e0501c2e42c20344654090303400329640c044d002102c0140e001da0542410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 199313075 1250 199311825 199311857
    0x405010b0105040317030a09120e040c0f0207030219080d021c091211011202070503030405071a0d0e0715050304021e1e030111070507060905011e1206090c0203040303 73
    0xb070f18100e84c1c02500740c9251252000e18114690700040c40c5201c0300e56904215800505040d40320342c006165035555044030700390007042c001110814010380042c00011803540c803009900040c60002e5039030681d0100d00c40700642e5a80b5240c040d654200e00342c0d9014544080641a90000b1003151061008591501c0443d584400f40c502c1d07446801000c030010b16100b40807010070104088442c0895061401c251480c6102d01e08008a0308404001c032002d810000a120911108101d044060000c840241010359404641c1401c1c1d0311800300840701150b21900444003100090007164010803250b10803030202000c280c0300030050350045034222b22440340303220384909040c600c854400b8002d001034090903264040b04185030301e0400c0400340c00e60564a0300e052800807010b0748042d0a0091103480100400e40c10f010015100300300c203030407450401c0903070160324032281c200c1320f81e03c00d101002e0300f00001030328003205103180944615080007082c1d03420000c0500560303500200520403070303000c0e0751032503c0c00001e005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 199314325 1250 199313075 199313077
    0x3090f05010921020306010603060f080c090f04060b0d0f05060901090507050d0f0c0801020403170304020f0904211206050303040506040e18011a1804030c11060409050f0405010b0105 80
    0x5824000b4541200c03d00808450344480032503006002c0e160b030b1480c0a10780c0001e1400800f6000384001a8607544100000002d441d080c1d8050030381d900142c01001c0741200800ca04031001414000494007030340100302804059405040b12a00c09068281915142d04140ca0030703807003000e401c442a12498000680a11040c85100724880d400b001411a9600c1d2008020721864010b0064030404001c4c100b5400240a1040c1107000b48507000000d42c0361403071410211030b481002c480303100b0400001c0040100581c1d844041891419089442808507156400c05c03288440341c2040804075502c0303d46040000c03d4100d1190100400b00c4e41d001c1c0000b903118401d0680340c0c001c920926800107018401840f5550070a00700a50013a04030044d0700c10545000d04080c2074480201201c0e01408502c00003140c0d5003408003401c515080746c0300380403616050554004000324068503010700f020f140c00d410b003505a0b0700c041c115070080c088031406200501303001c6003100d100d050039501102c2661a0400200c0c20754040c80c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 199315575 1250 199314325 199314329
    0x1c02010c02060c0a05090306010f03060c0c0c0320090a060e010b091e01020102090a03030c0c050414040605151e0909060708010b03040c0902030a0f06050613060c150e0a03090f 77
    0x79024200940f100007960b00c080e04078540400500c8014005507000d61400c0020900804144901d04841481d50400c0300840740c1d204049020840340e40c0c84503010400340c024240442e6031005c01c2844005230301d0000200c0e41c2010310403541c81402003090028401c0380740c00210554801d0344080d8096640c5142c05401417040040f241c3d000703c2c40380c6000310f801001c10190101508180005440d290220002801907000782d0001c50124074070254460600c142138464201a01c42a1400c10007024181c0b0314200d143c0c001000203155585400000d0455a030124504415040c050500000105200260002188844841c3e401112030303400203000e10a00240a5005142c19101d0b00b4081c0d080108080041c1e10052080d1142c3c90403040000d5051543c0c402944906903111002428214188031041034a0f600c0c2d0086201d08014045d9020b1010b120349690304468590800090324649440c0c04100b09100740000e41c48503241141005100d1400320744050b10506c2943c3c0e0102d040e49807170b03803088106214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 199316825 1250 199315575 199315577
    0x106210c1401020a150b0607291e060406031b0603050f0f06012a080327120702040e0f06040201140301061b0609060e03040510050405030a06050402060d0e1c02010c 72
    0x240d140703100400c608040307107501079003402da010500e418211b02007017440d0301005045807072504800d81da0302e8010510014035080480c0c000041d0b100e0400c005c8415445243d01294061028202c01280d0746a40e40d5010000442e0b00541d0381d01071726000c042100030503410b8030505001c83c0c200400100620115030210b1300c40e290107140310070300303880300ea004541d48a0000d1f5403414503200000d0085103a2880300b4a001002d100c0c40300c041e56441c198058500134a420074640507003100954611040b10004600d5804050310469441d8a8082500018000e084034249401c0344d0300035441e10200e07190010030400e104074000c0c0c07515004440040000b5013a0321003446000005810440f0758210800b00402d05e840301c0340a03503000b1510b8401500d5010456405440400043d4400102003042c2c1c02c0514441950076220300704141460319060119845040b00c5c8402010f459481000404568801c8151041d0310b024000030000c810a01c0d42140da140d5100c030ac4a5521401005403203001441401601c2610840e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 199318075 1250 199316825 199316833
    0x90504090c0b0304021507080711010c050a1101030f020c010f0501050a0f09110919060f030207080d050c040806070503040b10030503070b0603071a0430140106210c140102 75
    0x10b48407a903607680d000a442241e00400b80f00100b03c0c124140c5014084075402100a995a041640341c6200c04200c1c5a042c2814042070707000b4030022a402155402e070581e0010150b0f501001ca040c0124010300001c07010401080c40070408001c0100154011500103d28080822450b600d42c400c11803910180d110701c0b1480b0515020070301030354541c0e42001502d401e132440384130701b0081241c001480390142050340100c036981c8402c00300240da90100301581201a1400c045103050702c81d0710b401c103880c45580c036001a4251210b0110f0300c034901c244101c4008040e100c0548185003060940280a0351050320140c0d2612040d0022418540315071a11030110381c0d109009600d080310a40d104900894000c0c1a00d80c107015000002035021a03088465030303a100710b06051a40c1c1c03410000ea544040e100d000000c0c02c2000c56818908241c52527042c045a010f80009800c0004e401602c14103000d095142c1210151400d00313480259024040e80d80704080c02c1c441d03000e610f80907031204035580860142c00503107801070740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 199319325 1250 199318075 199318079
    0x906060603010305190203160b0306210a0f02061306050d20030103020103090c0305010e010608060a060503070b070c241e0f0507050304030b01080c09070f090314031e0901090504090c 80
    0x81117049662a18809400e841002501c0d146044029016500c000e05491000003000b4043c98400c1c0c5040503d0592011926103001d034214560399000785103c005d100c412082c0f050015503407442c003901d2542c3d6102c0e640204468032900d00501d1608250400c030003941c01d00b4010000c2c4441030400c0c980030000b004480d82143e2940e001100038054910003512550304000740400400e030f0a000f1000000b4a020000c12100d29145140d403410400a040b1500145061f000380080c0d900814020100d44c0c10300b002c2c41d200c0201c1d0601c00c1d2404016404407809041d80e5080d00052046000c10944203c52a1100c1074044a50b410002e1356503001141c280c00580c010102100281c080c03809840500e00500440b401c05440303995588186500b80c00c803042980c851803c686842c5440481030340d1240d20782c0341c6a82d141c1d81000010388000d4690000803c0504480071954641130200207440c0104c204418041d00301c140d03a081c1d6400c5500420802e40098040040400c181c201402220100c07507110301d10341507041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 199320575 1250 199319325 199319353
    0x3e040e0a0b1f02072102030705150f0703020625080c0c1f15120b010303200604030c020103150513090201090f090e0d0e030d0305100503150906060603010305 69
    0x86041d00c500c95020000300020100600c0b114540c0700c62002640040844900701a0780210f02409281c005a203d50010b141c1001030b100030400508441c07041d103044941c500a000716002d6805036080f0003440f041c012941c04145540080c01d140184c0407204289000310b145e4050b0400782500c582040301041c0d00c0d5010441c0895000e00801c0040400d4003512644038504800720804100798580c2c0700450740340c00240340b000b40828000d00c0100150120244818120751790740210040501c806014811280101b02d07400002d060b29004414415040d01c40600e000e107805410700504d01c4080e400640740c02d40700700b202d086c1e0715406020384400800807029544500000c0020300140e480480c100312451a00050315015030701200094243c01d01c0c046110000c0031600c52900c00b500002c003041007926002d590303050700c0c04907040c0445e213001c0c9004580ea43d501c9076811a285240e500054140c400c25030104902c1e2400f81145018101d500c00f61034958541c3c0c0d0400c40700d40020700010702140c1081c4c01c0c149402d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 199321825 1250 199320575 199320581
    0x3040c1a03092e0603030801050f0303070c090c03020405060c06090c0102061b0f0f0406090602010b0a0608040b060a0f0801020c010501080105040c12110d08040305010b040507050f0d3e040e0a 84
    0xb90070f01c2d180301e031214207041c040b04054404540c002c901041385507006125070308e4007020340d03090020164000e50600016407602d01e44850b0501c150442c07655148001002544a40c040b0741c090507000d40140d5403071180190203940c0d5007007121009114014801248020f62000c10b0132805081c0b40c080c010180041c01e40b0710000342e840000401c40c07004003000300100025800e4041c000038451a15036280da181307464800f900359002020024450b42d00070409200a41d00040dd00d40c2060300540c03c012075580d0030011840d1801a9084040100340c4141c1c00180500150024546020000000e0100766a280402d500741e400c103490040210040310010301806443c0c12250400c1da01400346140d281d0187c00118143c0000d0700f00640703060320001014403d0007024003600d1011030041e0350800480c50146002801400352000b80385034103800145100c0450400d170810a0034280e0004002034000c08c1c100c205000040d03009008910030f0b807010b6003411510850f0141d50032134010f5846804969920380e089001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 199323075 1250 199321825 199321873
    0x9040510020a051b060103021002010912080711060c03180c06030705090a031a0a05180c010f05040e0c030610080412050d0905100c08090c130e0109020603040c1a0309 73
    0x1c2040c14012140100598641280d1211413040030f800554154010700000400300b14101d410f580c1051402000250800d01c051281d82852801c0314054076516030440c0d810208000b4891540700c1c060038458030010b00300056003e840c050601111003803c50000340d03243d038621200c466108000f40005045980118001c01808800501c2180641d0f100c1d0745413005040204120209001180e0800944200500c6180e0b000030500c8840a13140d002c514186a0b540003501c801d0341002181080410b6403400340003550301409903407190740250700d080c3d441011903410488480d1312688034090003070689400707200f00350b0049400182010300011740d403100ba01c031544501a02c1302071903619100480842c0d014040c0d020700745004e647c085202c0a11a034003d080440c00303042403507641c00110808683c0d54461a543c40e21802242c00842c0d064001d01d010f41c01450b000d07002a401420000400040200660068055407070396041a5010070040305200c03080d0104944103001584149100031044a8292a20031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 199324325 1250 199323075 199323077
    0x62c0c0304110604080a020f1e1023210f0106030908040905070e030d0908100e0709020a0f120917030405010b03240105030c03061f08010908041409040510020a 70
    0x4110351828011842660040d800705c506500084441011841c10f15080482e01508440e0348100d0a018246158914030303600555105403005c14030002c4440c01100039484844400800e43d5404241c50024442c40d40110420b05060500e10307040d02d00c0d01344ca04261406242c48403c3d00380281c0c00c08109034018460403000b940c0001003030000085000c11801414441d40d07080d81c520f2003a8410b0028140390118032403100e018404000c2c0f080c48007110006486400401c0200c1c00700e20000410030031820301c81190001c0c140c1c03030700000f42d440c10310303410003403900c4c0d1802c182d52440c1d24104015100d1701244d0120300b00514101c0d4129003100b0700030f03400002e1a0080d01500001a809004100003031038003030319412030403462201d40428665003c10440c21401404250090081d03640d4480002c1e0304c0c1c09005049440c03401b8000d5403a0803251007110408044d05081c0020010804d042c241031000e50031600c1680480d18a2102c081c40c130b4104085c00c140611b9220b001001c40030001401d4030043d4105400003c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 199325575 1250 199324325 199324343
    0x4060504170f0d03060302180f0a09020105091504080d0905030a0f060f05010306060515120c0c1c03020409050c090d0206030c0d06091d0d0801050405060609100201062c0c0304 77
    0x2142e1004240061040c07a00f058030b0005041d4614418070505400510080c4c6002c040318007044040303518881c0403a0b105440c03101c0041c00940302d10058617140602c107146900b11182040e10385000401000900907103500c94101c801c1c01c1c0080c4403c843c9200d00c7e0003640c0e0140c00c00940140064005503449480c284260b0000c5411030200200000700d4000f40c0c42680c85644489040089080951708112210000b815071031401c00d8042c0c8110710039a01800c1060504070006030401d164006020700d129480001c180070300e000400e00c2d0010081e4015000b50f5010f9440c00300424401d181e1841220742a10000d410364151044507020480b407500002c4c258405044100420140b02403144215400350191010000d0010454444205226034490742c02440340d00601d8620308558001110504480045401040c0c81d40c540020030414011400403907040a203e5550881c060740640040056460344c1c020381881c00c80440c24425551a55449845070702c20000101e850000c1400007543c1c068004c070021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 199326825 1250 199325575 199325593
    0x9091101081812280801090c03090206160f0203150709050a051c050f0a0f0b0903030103081621080403080603070f1a0c030a02030c100615030c020a020a060e01080c0406050417 77
    0xc0360783d031312101d110070002d07214000500130f01010744980000c1c548541fa04002020442e0b001c41d80360701c104040800100803d1024408200f243d50003031165984c00f4080e20100b40030215044480c070000c0d516640843c4130580c000c2143e080144441017207640c02841808040310300103580315121f885001c10740701c82c081c135042c00301420820003c03580414811000c1242c80e640728106000e410002801030b0780d4640040004101058040c000c6e200300c01c83c00601c00324600d5207440c1003903405140070301560544400c50180d030326858100c0b1140384030324025103c0da50725075178140c10141c54000d180107a00050124079010300081454038581e075540d040c02d015003844c00f0400542e841ca50342000c60b0510042e07100266001c91283c0a001c408140120000c1c28000503081c90f58070180482c082d0044001c0581e9404ca00030791034800c108485038a03030090301c014071158503040c0c000e10b015500f13a4618045240072010501c242c01d44011182103030059a2010304241c10045051107a44900e11b0383c1545103d40620 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 199328075 1250 199326825 199326877
    0x9081c0309141b0306100b0304021c12050301090506010f120c090b040b0c0d08010302031906140c0c0106050f03030a08060307030c06080711010b0a0b1309091101081812 74
    0x40c5500540c60001071102a44141050700e41703000105080702a03442c100c030821004140c0d85c01c1da500281c0c1214400614006040128200c048004001e8040182c810302c807071002e2b4101008505840c1c4400090009558002c0152540004010180000f0f00420032990722b001c0d466200303141c0141c0724940444000d940381001303800350700150002880d0940000f2a80401d070010000c0c00e19800d4941807084040d031440e00040d407119164403020301c80f03004c030400a0f401c00100f039111201c00328014902001d00d041100d980e8006822104180c180c0d036191202c0802c80c2e2070f00d02c4581c1c00d0288014011031803c000b01c007040303503401c070061701251309445035040c08800161031103d4034014007003659442c20246010304000702414103816500c0e8103a4075200d1101502d03203d9007000380a60b01d10f2601d460ba9103005011118550161750711070410707a403500410320300700000d200080c1c03a503000036a116120b039164612280c1410401d002d00c0314260340000b80c3c608003420100050002d003a89100761081c20001707504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 199329325 1250 199328075 199328083
    0x1803060e03091f0210050406290306010603110702240307030203040c060503070c030f020c044101171c0f0206100b12060d0606030c030309081c030914 66
    0x6411060380001c1940e520a0902c1c0c409103c1c1c03c50100c51499201c042c88002135215102c060540c1c8109131035000060602200c0d030400b20400000e1a8501ca100d0a06040105441e001c0b89805e81703c0e0161100000d88103200307000b4038008134000400e05103071851581c20003501050040b2044001c03078054014045598a0301c01452050706c05440c09681d0380381074581a590502c481c0c00420a1003001d101703209070954401510500d4643c5414555114156080241c0ca4210a903170308652250a041c44100c040d5a085211658413200812441c0c104600395450403241e110303040207401e10070120004002820340802c0c505140c03480762040d18104036103c120408141c00c00a441c5000c22603611140c15a81da040000c01d034010094486203400f60708020b598611881590b07200c0074000d00c004c000c00c05507a42c0040303800020354801230400106650b450440c4234455944001da000c01d03401c45c00003440f480081440f05d00349410710b414000c000c4401030154000e01080e181503030100b18007d981c80000000708 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 199330575 1250 199329325 199329341
    0x12010b06030c130503121c0b10120f0c1403100509010f03020f012c1903050114070f09030f14060106021c180e0405120a030504030909051501180306 65
    0x1080080da03410580c45020118101544014080e51200b80758051b14400c50060345c00e10304444010342e400c07803291000400607100c10311070941d125020200418205802410740d2940702c444130424403401d001500340d88101c4086480080202e02d02d10000c5400b40c8151005513488020b07030826010300d81e102c002040d4100c40c240c200d5200f0841c002d0042c015403034074041c4080f40d1340d02403810901c2c1250108510328180701d0100d48070b0440c1d12612103504c865460340400340807000700d80300342c1002e80e9807400c001d80030708180362050350f0005458000c52031451044500395262465070303c410550717600c3c40da180d40c1c03030030b01040e008c2c0c500103600c030b032a030404c0c00080c042980204402e0740140241d1542070b18140d10040e106203904140800c0c00080c01200900d808088102d40050340c605480da0350302d041103070400406581c00c0e41d9500000592945242d01a4400790085000382c1c1d4081250392200540c00840d08181c1340c0d031040e083c0c0b091080100f988241d654087e0503c100802c80b290560300d554401c10b0b0703040782c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 199331825 1250 199330575 199330591
    0x708030705100b190918141e030c060708100b1207090f0e0114060f0309300d0906020d110711040227040b0d05030d05010e010b040512010b0603 63
    0xa01c0b01c416040c010350107070a002e5072089600e903d10200760a484034041071a4030960036926200c500c8039441e40304406ca4a8151900440c0c1e8000351103617110b2207504c3c0c000004101603101511100b44440000020544031003140c280004d001a4407480025a40100000c0800d800c06a8044006c5076480219001c0c26152425442ca41803c0c1404840900394400075006421052802d41040004440c6951050b0443d8000d600c0c044210803142d0205100348a40d03022001442800402e00482c85070024008010304030020103585110b20f00a618145078403601400910007606100d8003425501e541c0c40700b00c201e84110b03001840d003000c0c3c00c1164180c03020649024804900400c0368410b1082213401c1040b01142224210b19140d81e05000840440e402c656944503216048030074003d5031115030280d40c018200a09041180001c1e250003035582c0c0c0182d03541b40c240c3d4205000007a0050311030324614180c8c1c0f80001d00e14241414841406411031500108144035901c0300741c606480d8417107100450040c048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 199333075 1250 199331825 199331833
    0x30911060d050f0c0c0a080304080702090c0414010f0c030815190801110a02030a0f030e030301090504050c0a0501020d0f12050702060105011107081f09060e0d0905040504080307030207050708030705 87
    0x3c200194901c0501c020100c004080c800c2103105e074403400100702448540d900500301ca80f42d40744d900740b8107594000e0f81c000941248050040c0b058098080000e441107800c183e10b04000134490100440700c2403e42a44040070810121081000be40910202640302003000c2c3d82c0941d81c4201c0c0c00241e0183c0ba402514804806100380c01d03c5026020301aa01c07000030032181e41883e04a41e140000e50380c2c07144132074010802050946c1410103d1194001f0440418000d086030b450756100c07002c80c0000c0c00240c034100c640780304000c2590524181080c43e00112030050700585000000342d441603407014000124042049640003000700d046000d0301c1203502442490340109044d60406001400c03400042541715500d5100d244100045100010554103500c2041c1581c80c030b81e06c0c400b0400001d0101001d00510080c01d0034401c52030f044001640a4503142c032991140035465030360307061100302d440940f0003800c0c0d04010000100124040d800034003c2c140b04800310b8007a2980c600106e403d60304003680c21201c60700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 199334325 1250 199333075 199333081
    0x40c0809121314030f0106090506010e270c0d020d1506050309301602010315050d0605070c02150a08070311030a0e01020903010c030504120908030a030911060d05 71
    0xa0100030188100540181251410a0792500000070b000c00d0710940074903442910401189450911018240c5a4502c00078018a912003901401808080300c44c01d0010750fa00381c4a041c00d2900f00891075580b6080c0c01081c036906005200c1c20509140144840d00100c01005580f1864110b88001c1601e500400310010b080038400032040600140c0b0340c8030404120041c4140490114042200b490700c882e602450544200320b00b02c2c0794041c41c1104034106103514042504078031041c141c410302103541d2003640c00f0080880d0101030b0010070340c4c0500616800800707100340000028000d50200743c02c64494200850600c0c596800102100c13810541060700000114070482110f42005071a0b070428076904041c0221101c0c4242000c007800010001c0141c2601c0c2c50700c00300641c030294101c40500402a00030f2080c00105680500a400295811150310104010122007d407040031200140c445100146242008400048018041021094510590b480781e42c1856548413802040c0d40c0890010100d950f00e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 199335575 1250 199334325 199334341
    0x61b010b04090309140a050a2303030f0711060c0601081e0a030c1b0e1303020f120906030a0e070905041b030203032208012316080604020702060702040c08 68
    0x1481003000240940d0505950303900180d00300c40e0f0401607505060009440c0ba10300b00c0000d00320341d0580c2c0441d4100c166003a0205100303881c0c80c030300c11010401c032131003015036072114050503038078400c51006015105d0305010010000320b40741e0000c0401a0001c102c5400d000c55242500d0615101b84d010310f005600c82040061003283d142402e504072420b13900548509901c5460213060003444c1da600910307a0001074400f401801840310040d006e006c0300c1001c0b034000e00c0d00714544801005801c4d03042d805441039040c20460b50340c0006031450305904c4000704608101c1c200701480030310340000c3c000ca00041d03203906895041400401c921401001091408030345d50400707040a14003644101c0815114003803030344c014000b40c1c60010485401623034030b86004080d110801d555422202c6550040c102550920507540300a800250003c01c5503011a050b160413a212811011041100200a000490b0090001030070318501075014200036400036012518200381903000a046448240e621000f01e00103d003408028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 199336825 1250 199335575 199335581
    0x50408010c0c1209081522060b010e040603050705061303080c010609060b0309060f07020703050a050d020708031602100306031e0c0b090f0402030402150403050a0501050601080103151109061b01 85
    0x544039003810315030701d81000344954a4101030811391003002ea07003101041d04040e581d0007e101d0245001031200d41064289481005480b40c240d013280087d03920001c4200d545054402d101c21654014020490680f404040c070003146c201c004189403000b03510301c001020401d110000d00200c0fa40b4000003a100e420440f40f6000c8903000c0e0800707411860103104021101d800041c8968000101c1d0b82c0c1410b4a65594400320700e0b01d56036400c001c0c55800744105010422000058a142c415115025200c1090b10741003415524000c0c60080300c10351044034840c1000d41051150b001c0500303003610380801c405850b5107038200043e01601415408040391200482804040c2130724202418040ca00c00d40741a41d4400061320280200100511642c0e00001080c115903c040c0c40035030460303802207110344a6070717281011503d440c80b05d5001d541c02c0d400e00d00010050362040c2c91490580c1d522815840b4111101103896000300400341070a43d0b4610104100c0c80e280e1b4480010349100c06070b10003000c001900804000e425 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 199338075 1250 199336825 199336853
    0x60302030910060305030306150c03040305030903060a140711120414010e060301081221010303081f05060d0903020f071401180b071410110306010e0a03031e050408010c0c 75
    0x440b40c40c180052000034004800c80360031200c01c0b00c100b52049003029407140242300b0b440c0e0300c4040d44000100001000804400780655020071000e6990994481d40400e00750382a81c19103082c02c01c140d00010794410b020322085100c40926408491482c0d41c80071002c40d50b5030003038201c841c1007103030080c0c903510640e400101c1c81d0110900340d0b0700c1c4d404c65250001450b940c9905488607070003120b0100301848108801d15880b0705e034400c0c04512281550f501d08001cac250080035aa80001d10101d5881c2c01031900020248104841016003d286024460880301d001003102090480440c00303007003001c049062003040080064807481071440148444003001416180712080c148074a188000780c10445400000d09a80c603094118a07215003940100a00c50309158070a80040301c40d130b2404441007103005200001d58443c1400381c80706902c54001c1000c1220072245840000e00181100c21100d0710803c0c585001ca15030310342c500b4081c0c14180c40f212441c3c290754241204800181c41008104140b00100b8450300c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 199339325 1250 199338075 199338103
    0x911010207081b060c010903090501080c0a050a211a01030c021207030507030903060525030216080c0111041d100f051c140c0a081b0418020a0603020309 67
    0x803920301d818080c585480f050380940c0d400e25400800039085071280c030100e46000701082d0080201c0419464041e000d16a2400f0740760004000e4000141e44280c0a4200c448030181074640310309000c9003001c2113034060b4094056043c081c0c40002c1030506080389020700041840360300c0b6000e0f407071030350000010101c80035000c1c603204562003011842160801030088481d0180c152510703996075052410169080c0322254130060440e8541010041c002c80e5907607010204540e135402c08000321001c10300440590007280c5c080000c01544c8541032000425000c024006c5456010010805803068481d40b00300c0c0d081903000859580005401c00c1e40c02c5c030301c2900554020b1001e1030350f103174480c1400541000e070241c0b4003800b070041e4100040741d5071516075440c0240f00e20b0f81c4811000203103228006017613100d007a24100c46024208220011a0219000c52a034116040d4803c800752020003940800c009814402c0c900c40980901400305400742e142d0326424005803825480140e52070400c150302c14178000000e81c40507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 199340575 1250 199339325 199339333
    0x3060405010c1b0f35030106020d0507020105030a050603070b0f0c07061e0309060b0d1a0601051c0506120d08040506151807030b1306081203090c010f0315060309110102 74
    0x1a002803845542101c50580140f110880310480ba03200c00745c40d02001d1001d90300281422405e501c160903900095040e510103500742c3c0c54056041105132001c0c055500000e006c503400340300040307106044d580318550024006045038400341d515100002c26038400f060ba01a00d58000801209200d8100025801071038140b604c10b0f02005113501d0a404000d0203030103401010713154507402c0c05200c419001110810801004804290800d181c0400307190300344441c0301070500d6644000b45441d8003440c191000f0062001d24400f492407400c094100500c4014410780e03000345800d0580c811944100101030040c04079485452860a29091081c5048002401c16491905c00a201320181c1c031222107140c42e0380000c2c107044419441c1c100040e4050310310b41c0c001d55000300b4409400b41100c901900031108640b160b0068071b00d002d40c290078120051004030382d0556154840740c28424a940725003c2c1003c0c0001c207140000341d90004030640c02e840d500d5540400b0000340c0700e0340b55030705200c9032024200511600740002c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 199341825 1250 199340575 199340627
    0x117060126130209060904030e0d03030e24070e090115091805010509010801061d0901090b07050a031802030316080f0c07060909020a08010611071e1a04061e0302040503060405010c 79
    0x10711034000c42c0e9a2754013500c080780e98101010302a0300000c20069402080e03404c10101d030b44620003013184400744052040c80342408100c5540c02103d070030742c400b0409410038a0b00da09200c00c40500c80c500312401c0e001c012024000040b80300b490301c40c1d220f0107441c5134000b02c0c49524110802409a42c103812420850b45890000c000d0b070725502c10700900e6809010841000d651307680d00d603580180392903000509500114810814100d6009000340b83d200002e40b010400c10107a046042e41c0030266400003900f59000700030b000c20381d90b06042d0991800d4800c907001807030500c44003150b4010741c001a00140441c0d000744802c3c07120a41024940c0e01070211014114100320501a000b056204103108080a018401c1c540e02001c440c103000001c040c06410000300b2800500d00da42111883e098433603104000914440010310800840443c0c08594160343c5c0e55100200843c101c1810448040000c02410780c00c000000d283d403818131040e44114080c0c0000201441c5c2c4007000b81041c0081c13001c0110440000e007039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 199343075 1250 199341825 199341827
    0x26010510080c19032006070302060a2405061803030c01020406090b030c090f040e0312041103030f0f03060a0f061101050a1503110f1c0c05011706012613020906090403 73
    0x5101101d070000d98002215450360100c9281706100900e6540101d000110f400501d178000a80601030107031440c0400003604000380c047c8144021039503103038411004080c03c00c40c030b2806e00e01811045280644807141c212a03203002070b18550021f5048032181e500800c040008075049001030f0014030080b01d085146291602ca0302986202c0c2520203440f8400c00c990707400325a21307113502081c151030805007141e585145108082c0000c4108450448501c40041119421401c002c410380d07410507040d0f0f0341d46003491801080c400c42c03500700604150b00702091000004101d089150420020a0135480c0d0240c9070a41d0301070107007503400c000c01d28000c0701c2c10000c150980010240c0c10400322038104048800250003580003c034081808400c1541c02140401c8a500d61040f421403041014450301040101c960344600540c1e440e68008141c01c421102440004c1141d40140070041c416800c544035070700c020390200c80b000c00c180e000f60341106403400d1008180f811401d0841c44942c00c03100440300c4810074682950 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 199344325 1250 199343075 199343119
    0x801050906060a111920010206040f0f0b07050a020c01030e0d121409030a02060a0510140f0d0305090102010c021603080f0f0304060f0b060307080126010510080c 71
    0x2108030b01601d400140e81091a10800d80441c10000300420b0301d4080c40f800b000544d00d400010016501d1221710701c001d10b0345101c0e00703c1d4460300c1030301a00904169a0780e44c50307000b4072044ca000d050300e8469050043d0000905c00d111000e10a030290384440d91180d00c60100207240c10950341103681410310700b8541058a4030005a400f007248243c1c44c0559000c1c449000810250014038034200c0101c11040034008040c802201906c1e030003c00e40c1c00c550b0b01d40e40700c011040645505070742d03070001c142c3c10507028890003541801c50504071002a0041d80c480501e2004a480094054801e8000078400b2815898544e03080c000ea042250051000301070094042c1c400f01d000d20801d100c000c1ca91b960004680c4640841c503000c0d038000c0380080035026101d15003410100080d00c03118000d0b01259107408002032145c070700001078a004666507600c00480382e00300604610701c240d400c1c038a0301948100f0841032650b000c0c02d0103954400c03e99011801d403400d180c103040700c2c03410b203400084911074800da0f000710301000d401007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 199345575 1250 199344325 199344331
    0x2032502090105040c11060a0b0f01081b07030e030d0903110a0308120a060b0c030301060906050f0909060328140106031a060409140a1104020901272c010608010509 72
    0xc42c0003d8041460308246d4224170a0060b4140d40d000d40c1d42006070070b84050f070107410081c07001d9540303102c000024001140d44900840b01100c0007800044020114006080901807051090034110280948140001e10f0800d0303ca5032100012800d81d418070401c0024807040030214406d0f10340c4c1088509540d6404020f000b80d030100b4500c10964000a07800c4101608140000c04950081c99a0340c6040c100c00f5407030b50f000740140f401044101c040000c04500c43d00031103940d5881d24420301e0a0400362410401041c0c0040c1000780c4c10310800440c00112054950300140c2451040c8100300d408a480c40d01420741c0703076180031a9000d0b9140c14020804201c29000401150f2410700c0c004245580713080010b00102001c1c81e001d041c000c50348410001d03c3c2d20014100301c1040c0601b8506140c02e481c60104402e92040802c1d403400500c545400030812400494400c1380c19000310001a1080d495244000c0a0305170440c00c40e01000500303010301c02c000c038003006440c050082440c01941941c1490081206d1000203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 199346825 1250 199345575 199345579
    0xd020309030d0804112701080c1005030405010b0a08070f05030a02092e030303050612070b09040f06030210030501030b09190b1312090915140d1b0602032502090105 72
    0x20001005c000100140350100d540080205000700c9070107002c030f20b444001042d2400e81c4400c880010804100000d08400c6100c0c0040c070b885204a2620012201504044d004860075900e44020000300d60361809a40003420b0000c00900a051800000c1080720160380d100c18082e1300044440c0015890304406c50740d10800c11285800d03141d6a407510310007030941850304c150702078001150100c10950305800041c0103d2040300c2d03d4140c144080501070302d850316441281504603040102401d24141030b000154048408240007602c0c036641d401040391192840d5034000002c0c1c0c1c0c2c3e00140108207044003150b8120306040c000300b01d41d410b05654482c2000308294040c0c00640400e000502c041904100820525849500c884030640620401f60a15800d0f01502d1001c904044000c03113240199003042c0300300d034140ca15501103126001e05101d903524900314241c3e10444132594800c0d035030000c17100080060404d43d00555540041c1e05c43c004200e2411005000c0c0c045410071600c016951b50860309040d1034003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 199348075 1250 199346825 199346837
    0x80a171b210403020307030914011e020a0f05100c09080303010504020f0d0e07080c040207150b03010605060a050405010318050a110105090a03030908150105090705130f170d020309030d 81
    0x88548500900d060007004005500384401c100000c00d50f000c0060031506103e41c40d490342082d01d55110f803076110004944540080c440c0c014140c07407800c1c4021405d02d8180c460040d01d81c2e0b49240d4885e60100014440250360070b40c04610980002c2d40f1521402925044030f2402d0f0f003003207040c03402c03640d100e00c010711401e44600d40105000090b0120710b01201c2000d0302c445420008001d402408544907686441a20914003c05100c4104c1d07007801e001302c42042d580500001d041c0d1940d01c120320001d08040204940542da1100080b846886000c02003803414095281c1c0794485107004001410399092900c3d14000a60070f540c008005900010448101e983c0414001106480400101e600b405a1004654001100d900010a145d00710800006031601c0300140e42460441e18054213200c0020311409802810316400144205d11500150200034070305028070b004941c1d0344e03003403000b181c10a8111040341a04c82d8145400998104940c126500c0c00b40051820100c410000075282e2007408040818800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 199349325 1250 199348075 199348087
    0x10501050d0602090310020c01091101030b03031209071a031510050306060702010c0b101404050112080f0d1406010f030905061906030507090203041a060a12060f050103080a171b 78
    0x15050003031211541c003081c42151100b00494600327029200c082e100f0745014109142540c1154403c1c0180101c2c2c031000f600035460102e4a42007200c0d0aa4000d180c90154007800c50085011074143c0c0e071903008100d2240c400c503100d081660342c00007642409010144078814141a64401c04e420a00752a072120044404580301c0720f05000507a1190342807007004001c5050b00080211884d0715100300002c1d111141849044c44101030b044c0000c6030428024080b40d0407080c1c06070400034001c20010302c500455013640300d003450b04c2e600c90791045c2c400007040350301c42660001c1000125684005200f18054103840c040c402c0c078682d40c030b0b200d40701e074800741110707109508056a0003203c000c2c50b00102d000355070110494400a03543c1c000400250010785c1c00b1580510100c41c0e2000384000c07416083d02070704009101404852030b04802110482d0141001c59107191101d41c0c441110743c0d5031042034021801540b40301d580302030401d40101200441c40e01c01c0007071302c00c040034002480c0c0c500491181540e01140007680e145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 199350575 1250 199349325 199349329
    0x90609051e1507020c0d060608120c060604020304140d030504020108090307030e13020c03070506040b1003120c020f03061e100605030103022404030c0f0b0406170403091a041502010501050d060209 86
    0xa03845c0e0340c01c04034004000081000951203601100c0d104402d94840c40306036400151175104680307800c2d00c190720071000326802e45065801140c005115005030894005004001070900d031102c2c004201080d170b90020481036503000221a54007284400c041c2d480c207903090340c001d041c040404801c9170090410550300e1800d0082a81224a02910b020459454a4092074050341c2d8910480f03003200c1b074030180c04c04584480a030b46804070540f9840b00d407050300c3d285007040c01c031603c8580c0502a40d20488c62009401262030078807e05028040f9040280e40000d92460342c00703140c01020300041980881c802c420403020b40d100060300c1c19254111010650750b850701c0c43d0001e80d20b11409080168040015001040140c560b07841001c540107074000b60903203691509142010301441c0f080a000c60f50580c802c0d0704d4050503407a0b03198441d1080c00d0070307440952180c034003408c091a5142d4110003604001001d00c0f010b21078000007031105800e80300034803d960500e0f000c64424401c0c0d240c02081140c0201d03103000d01c0e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 199351825 1250 199350575 199350583
    0xb0a02030d0914120903010b1002030d09110d08030901050903180603041a0c03071b0305040306020c0f060a0f061a0a0f03020c060703020910020c060f070309030204090609051e150702 80
    0x31003082d0f044490380300300140041080ea200101c580c1c0300e5840c100b400c06003820709810036486443d1030340246041c0f01c80422500c011741034200b070848121392a03204680b40c541e02c049107205907600800709952030740f9060310305508545000c0d060700815801030040c0c000413201036400d4140c22006881f49078898035946441c07070b041030b0405648a8490307015010030840d8050240a0b6100e02c2d4582d40f420b5402200c3d1503d4010184041313006400108100001e001160780d94004016074502d003002c4030000410100803a04141d07040d2000c02d032660700d031524201c81442d03600030100031b803072845410201120404c0d09007049204d0310754100c00307011f80c2c89804002107001e50f042d101c40c6944281503505910b400316000340254449aa041c1c8291244110f001202c0d1002551038180b004c0504040d140106000c00041a904014401c50402c0050400800107841343d0007101141845184041000e0000703207041420210601d600944c1d4030207860f881a2a2400014070000381600c00302401e55a4441020807414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 199353075 1250 199351825 199351853
    0x7020d02040516020607050a020d0c0203030d0e100b0a0b090111030c0d020a030f18030303020c120f0304060507140306010516141c02011503020613030222060b0a02030d09 75
    0x1c0035181c8810806211183c21544801421950aaa00a0340e0350030054805d80a01100b000c0180e0102d0342c05c0c2049806a10b15240550004003180e0420145554100c20355640342c00710082508182c41d034009007416802017140a034022611b02807200c1c2001706d075007894000c590080d810002440000f11200e5820b100321444110720742c0c190340e4014404840a50703540e82e0b030a0118002015425842c04841c42507071010740e00101095070180e00303440c64404030040d40044421030a907020b1303003a4203001003001c0c43c028003a0900c4918420b45900c0c0a040000484800801d070206000941c2d144c84465070850046036030111003420502c2c0c4480f50041e040d41c040710b4082d030081040d03142c007488030314030340000440206e03000101c01d038044640c5028008a003610902150540005070900c42400107140007000f80c002448404030303520310709540e42c0001d803845240d004041940f02c29101100031081c1c0328080c010240120000452521503948002903a0b840340000c41d4000340c3c0d42c1c1340000c04110007000d00f845 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 199354325 1250 199353075 199353079
    0x702060d02093c0108060916110f060402131103040602030a11040603141609030b0a0e06010609060e030303040b040f051e070e0619031e0c06030203010501020c011e0507020d02 77
    0x101c0c082c1e15005024900c4030f00b03c428480700c3d600740c011559031081120520900016147c0c1889442d1001c0c86d0b0100c0f0002c9001006001aa24201c60b500104120f002d28079407210004145c2d500740f0380117008000310507044240813241060141d055190710b8408680d003095103d0303c01039070303984c426001740018016105090820000007800044143e1705800078006040103440d0741030f0940311480e0f284280b140185030000407a200700c004002189050004503801001c4810100704024009141418210240c02900c0850038041060043e198851204175000c00300b5002145541005d480300790b43c01070001c2000b410203405082c030390304100040c0204484c100e00f9041e00e40302c912051104c261180365601030090341d142100c001546c60724207c04028a480d00d41c3c0043c04180c1c0c1140c5401c0c84200c820f4140e07402464441842d0700001e0581c41c01800248029600141c4950605000a040800ca02412410030181c000340354024681a81d0030f414110b068100340707654224034400f03c0e443c0038000401035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 199355575 1250 199354325 199354369
    0x1a0406060b040b090103050f0615160c0329010b370905040b0904080a0c1403030f070305060118090f091e05070b0c0c1009050d05010b0a08030702060d0209 68
    0xa0103005800150000040989050145503038819504030b010900b200c9c0c00358004181c440c0d00041c00500c100802e880c502c01400d4440761852030700c03808031034541c950040b5102c01d4211081c0d80c03040058120782e40406c5021850304659454034036040d0150140c8080d00700d1707050b0b585405650a03041d13204d500c486180d000b415440b0703c40344050302904889140c40380a0286042c40000c0c0c00515020034402d106a500c1b00302d2a052401c2c048003150858100d210032984422480003c908512040001d58810303090301c0b42205181c50600c40050507142e01824250501c422060420310b9020035800d600f0503180103800010340d0715680074446024180c01d00c0041c04c10b40383e4209040c81e051950032040b249070b00950807a01c00b182da880c40c1e45550320902e04030760401d0b00403001621040ca002d100041740444286011401d06444400140c01e80048040486003a9510702480f00e0074102a604a001048048055420190380e60040b0320b80d0300c00d0070f0200003010b0b070008040030165244544014100039118040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 199356825 1250 199355575 199355579
    0x10e0a180b0301060602120f0f0421020301140405031c0b130906050106050f0f0309010603082205010905060a08090a0f0803090105012903190c180902071a0406060b04 73
    0x1540205220010769000c0d509080e00450000d000040360f8248844028400d0300d000010341210880d0341021030300100243c002c01c07000030b0400741e002c6e03015050040501016118030940c8101401c4a48050444100300101c2c030811000c12404030a944c078003840d04401481000d441440400140f080741c16550b030064101186501e0020607501918010b4030075038081149980354072040d14140078214820110724002c0212001d0401c074640615003240e520400440c0b07094480d07071a44203640140c01c0c034074020035196000b005003100181c43c5500625003801d00400c0e0608101c00b051161055030f0201043c031185d40e020035006101040410119504444008402013803890f100d64a50b00c15160480c25600f024000324529070721880d80304c40702201205943c10320008001540e0349820050114200e00343c2d22075003642e600303041d00a2103120511940d0b00748240b0384680c04264110740079003000d4181803062001d5400181c8550990301c0c5200c41c0c144945d41ca071b5031403074050080e01464010520f060008240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 199358075 1250 199356825 199356869
    0x1030b0405130b010f151b02030601030f11090c0313021c21110c010c110901030b0105031011040303110f0706050406260a0b240a17070e010e0a 63
    0x2a2000b0b59100d8000708000e030b6a9200f035000704094501420b8105240c41d00c460141e2400340c0300710022075007946c207200b008840c1a00040c0c1840c100340d1043e2a144080e060320f40400440358a5a0704070b180440d00d1507900d007022003410055020040c1032010781c000a176144c105640c0ca07280c070780744101003206880515440c6442c02d6142c0018900c00030740c00c144194544070403607004814900300c424030b080081282215501c01110010500002600c5402a070003261005480707507030009002e035014040c0c10100d540341205040c64040c0740520210780b186000406800c402941c1e00311001c481d014541380303112502000ea49030800c2c0400c030011030307944502c15001843c22381050242003102c081d5100c501090300e81140d0b0119012828040081480741d110004140c174040f0b5000220800000c2d066200031968800101c1e40400241c00003141d2840c08114109542d030305c1544159000314101d03003038410b1701700010042c0a104600344407906011402e240c0c402652150b008000c01020781e02c01d410200400119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 199359325 1250 199358075 199358101
    0x132c19060e011508130b0f072015100506041a0c03130602120c1011040906080c03060106050405030607030b030a02040212040309170c041d0d02160504060312030b01030b0405 76
    0xc070343e00104400c007001910320f42ca050003501e40550022180300f00c44e035603608000030300003001308104180300c48070903240200283c0780c100d951820840c44c002c200344a500d8050401e400b50041c40540d07404ca0a0030140441e0b181c075801d03a001c50b1001c044258142e0b0904120028170b01503000c40348124480456410241e42112154038101c84464007a2181c950000c0b4244c4807900c1141c040301d01a0b8411200480d840103a44e00907030040d050500102e0405484503a0b1009854465006c4000340d80069154115881e09000050041480d07090043c605031034000480e44524009003440c003410380e40c030038062494500b401440115680144210340d81d50520341082e400d64010748041e40003860b5040081290325404000101c902800d00c0107002c142100000c100c0034105100d40180540e20720030a0f5090700d8000c005c981c058a005801400f120301040e0348450382c0308666403059106504081080010840b802c0c04485121181d1502240c10310308840180d0180021181c0d0039002480e0800708500003000305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 199360575 1250 199359325 199359359
    0xf090f1413060b03010506100c03030902100504031a010f0303260f07031a0604050d150e010e190201050901080703020c0d0816030902030c0603070212132c19060e01 72
    0x1020040740f4040001e240c201d0f041100e5054108181d106080c0c3d920b030140c03000c8818244649008600d55071a035000c10000f10b40b00719240b000c1440401d080c01000f00e0601315200210040100d01110b40c03520020444032291884040d042c0310039500c0280300c500d001d2600001c000d095041081407400c4c241c440d180044002c07680780300005c0c90a0140c60319580500b001004030300300101401d080c1410b0000f04504890908801c60b40040000074030314128105000b0b102045c1e07401c80001a61030b451013001c6080441c51186045039100c6940101b0041c0c0e080741c02e40340490030a02c1d2812080d039824400360700901c036580300c28001d031051080314003031140d101e81111710422040600320441d0100401c180e058541349000251b042e04020314040c801c0c01c0c000e014562101440c0304484c1c02d51140c001c4030000354010300310b540603444075541c01d0001499015210101e1092809010402c400c81f0590480c1c0c40e801509034860060b490316400d40c00a007680180d8085c0181500803891541c0d108400c3c90180c4644d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 199361825 1250 199360575 199360583
    0xc10060605070605010b0315090a09050a0503030a0b01021c120603021c021011030f070201020a0b13020102071a180301020f0a030b040e01050108030403140304090c02030d0e0303010f090f1413 84
    0x460001b0039500b40000559020325159070350100e4880114007003104154000740021286581e84e518200415010080d10741e43c43d0050014540e6030070020850350560b060107411605640c0500c200d1100f4014025030b403020403090345007200401c280c01344048060191a0b10207075000c0355203080f00c1041e090380c2d08605001c6108550024462288030000c2d03400c40808110010545c100f8030003000701c3d0314000c004105040c4140305594248140f50b49180c0c003010141c54020000c210604010215601000140701500301c080f0b6640305921500700c000f1b464428014030105909213144001810385094059036004441c1102e0140c0324003d4950050090107040313a40d62003141800c181800720481071141030305a46844021318078050558079050031010f465040104148000c010018900b016880351300d10419403035000e0769480f400403c844099881851080c40682c000300010020307101c060490704111030440001003200c6404c0e10040d00205100310501410035a0a010090076040035948103691600c0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 199363075 1250 199361825 199361831
    0x1315051305040b06040506070203010f0504051005130f0f110402041d0c040503070509100e1005010e010f2a0506010b1c0216020103020702060d091b0801090b0c0c100606050706 77
    0xa50700820040e1200d1004031a040502040180140e08155005158082c00030380040303800210100b42c1822a10112000d4849401800c44080d0304012401500d0300240309080001400f030013515801040c03034080400034100b1094014040030040b505680b403c404000800440d06c5507690241801070701e040040850840b41c0250002c1c0b4440202c030300b55001e849000d401001d24030f041c003090211040d805490984035000d941c80029520617020303940383c070444648410045103450701c0005065030b1415031390541070000003030420740c10030740c0b0007003010209001da58243c021440c00f11400c608060581000342c01782c01120004078103021100e00628542010300009a807150010503200d04078021203101740f00d0b01d1401d2040d000950300c40d40180c40403d000034002840c01440c62484403c0302d01c5c0780b00445509100843d80181c03074180c0ea0340f0300e005180c411f00070f0114680603034459518200040c483c00000340c01041c00b01f2900000c0214015101041204001c1c00c1c2d22400007030441d40200d801118181c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 199364325 1250 199363075 199363079
    0x30f060406270b04030318140d030b0906090a02030a0f0f0e070f06090504020307110a0308010501110106031505130f14100204050918160308030906090a0b070513150513 74
    0x15010312100d4195422410419084e102c03560218007401a070941e1402d11410000b009011501c440e96918422203130170018050288814005410340d54203141092094903200d00304843c1d074560318641e81e84040d83c09001640c81c1c3e202c15601c4002d00400581c00b0000b0b18041072001056041da1018010f81510300849443c50740d507502016520890340906000502044820071450a02e034000d1070f0415090708040e00c0981c0b60910a6161110180069000032103000041002c0e5800c050202d03020b0b00f0381030080c0200c41c2142c441c202e20b488060600e11005c0d40e00d40015000075a509505108039500101811034110282802d4024003184066001c0500844400340300422103882154201c2c0d0014058074807641c0c807001c0170b5441850111a0019030301482c84800d80c503c104004800c040c40c46840b005889003001200a450030074020700b8102c0300d90240003404049400210b806a2240551900c1613950003032004a001a40d015070007000c003142021410001203411001070310310005940300340c100b640c4d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 199365575 1250 199364325 199364381
    0x5010504020f041e0308190801141815150a030509060f070503060117010605070302070f06080103140f0d030f05150604061d190602060705040f090209030f060406 71
    0x11140003a2882980000c000130000352505001520307040c981c10504100c41e50382e83c0c89030003041c1d0000c51001c00c848142c40c00000907039000241180036020340c8900003030741800100481c041d00c0c0e100000f40c01c07100c48180001e50b42c2c849020440b05410016100305001801031510409039044a410607011070300b824002060203400242840c412084191072091a80b00d503941900c00368000780106041000301020303006510f14100d031660080483d41e4a0540d15074440c00c000f41042c00c1074004050001c0c00040801c0000d40c0200310a041d245c200350040c403c00e5040d032090380751021062800490707015996414501c0303a01507206032002402010240000d03a40e004000300f1203030f0342c501d6082d444078044c0400c3c020940718040c4140d5044c600184894020007007400502610458142d06403540105502404425414170031190410342d503080403401c081c20721a0800c80c600d01400703902c0c0110703400318050000c0c0e0380401224204d9030392103041d10f10600385418018090b10019030f2080800c0780d80c21a40c8849 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 199366825 1250 199365575 199365577
    0x10c050903190b24091005030709110d020a050403050a0c050103110702031e0c030f06040303110412020f0109090504060501080f0d051c0608160303080f070f0804020118030b0a0501050402 82
    0x110b80d00006480c1113580d90124407510b807110040800c02448840040d07070032500e40c039807042e004000300e0403103100d0a03151504152501d1180e030000b04440b804d01c4801c0d6080341c801300644441d14003211001d030315510900703411502802141e02c0070300b4500c1402e600c5424000c0018210b000e85400780e0341031009071080100503010b440790140094140c3e100580c030b000302e8460030b005083d03000c0c0d003a81542c0101e500000000c0c5080a00c0e4141810380e000389081c0020940c140c402c0783d071100d03602c0a4003420589000c1030309152000c0c8901c0680101030507450711840d81c0c410031401025003a641405c002d44d051504044008013800d004066041c03246030103100504000103804070b004491503903034515245070b01c104020101d90440c0813105c040d85032000440d85000520003035080b4200407040380646413031400c004103160005071031442c001032101d050041003130303204048841214150500160903100c910040f6460f503082511f103001d007098100c01004102183c41c01030300030300c032089051109980b10703030400040b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 199368075 1250 199366825 199366873
    0x405030307110a09090b090d09050a0b0a0309060203010e060102010f02040b0f0d020915281403190c03060e06040501061704050312070806091e27010c050903 69
    0x8958030a028050018841001c8400d01c0100038124038a03850b030700c003400fa0544080410842d145c804030b10401c05451401c200381e0030b2002e5940760000a07989494089060a0032a0150003940b038400985801040d0080d00700202c0154070400441d40c0b90782d580450348601c60140c508034015400c000c02403803c1d0605009131400d0781c001c404c2d118a401000e44440000c3d03031100211002e0a0780903c0040c06555403c91500c4019641c5819180d644070f0071504030304542c0c007800600b4501000b42e0364801050390f000c1c110305032050201d40015541c0d11000c038182d01c0d5403020000190510704004010550a505800c00002c0b43c803202d214480d1740d110b040030042961024010000041c0e1906522009801500303952908070f802042602d00d0882c0c400040c5a2045045803c0350100754040c0602c00c07c1e0402c1440c55034800034202144080f21000c260b00e00315080d020340032804040c800a4010b0001d410707124a0703101405c0c000c00030042d101c00046e007d00f03150004580540b1034040c44450201c485101112401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 199369325 1250 199368075 199368079
    0xf0112050c0a0f1418150f0306161808030a050711100f02070e0c0702010e01120207031e02010b100302030a06050604091d070f0e040602043f0309050d0201050c12040801110405 77
    0x1171561500722101c9841d03012905582c0c0f004145003201000d44080c80301e44d010703210074522080722480d8040301030840820000804400300d4a49010401c40301d0110580d0129045407034081d50750301003800d1011001c060710500c150b004203d407090490b41030304501c1881602403a5002d4450702540c448490380350540498482050007010030621005611441c1405503041050515007210210f1285503001ca030020b903400c0340400c80170b02d02503890203e002e06d02c0e05080414402031060a5a0101192413007207400401d000303154010006c9031007090075820400182001628190300c640e980e4003034030041c0c032051400200c134468a82801c0c001800c0824050140ca821000750340a0919081c44203180107402802510600e50038400400c10340c0800504480c00035020035040c09000800d040e0101d92140d01043c1344070505901d81c03a10009811541000031a001158940c0c400729050005a0759842103002c1100107011703924050104101800242090b40c603094001c020400ba5103001c4001ca204074003030f881d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 199370575 1250 199369325 199369369
    0x1e0d0e1c140307030e0613022e0e030106081212010e0103030807050a02120d0b090a0b0d1b15022401030b0411010320070314030f0112050c0a0f14 64
    0x640c0070014401581c10883c146000504c0419040c03540342003410994801c200450820030040661500220849051112143e00c0c2071103003960004100d0020031410000903c0507446c001c0e401581d0070351140c00200304030820703980c40403c2080c403907610b035011002d50101558100000300301d07111001e414034184c1c0e52588406e4402d8442120a40d12600801d40700d40c214031496041d104142e203543c0207004081c45001000c68100950801c01c00040c40040c12000854a480d128039000d540306498048011342051001084404440d503540c4081400d400041440301d0307000340f2000c1542c0c0090b0005200c1c60380400001050401001040c01800030b12000c1c01d80108070010802180d00404c1d41032441c40c050600080140394280d0768045045424280b20401c04003240240905070007502c081860700d07201c0c03080d500d980740c0003601102c0440103006a00f03840c0130300140101002800c119244003004010f0020142d503540c0c03010224455154007070b0320f45086000b821141c440c00e00c8640c0c0014910140242 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 199371825 1250 199370575 199370597
    0x40614090c070f0c1205010f0510050d0302101103060312030f0601030b01031e020301080709020f0703030b130f02071103030a09050415090905060106030b12030a03021e0d0e1c 77
    0x80040707a040100c2c02d540010242c4250b07400250245450001010484115a40d90345030b41002c600f16280308074044404d5040c003041004940004c102d20040d00d408541c40b4010a00c03030304040349003e8082114440107440d00710b59880300c1284002452090004404480c0d5100302c040706081c00d40020703070f4101201d0395943d0114016600a4210001032031044c5000121811203005000c54014940059490542c1c00001403010030014040400900700004081d850010152681908da11407070360080d00b0180c1d241ca00260540d07520212719601000b804040c40704204040600000703610001084900501c011540440780c2000300c1a42d0320b0030131070344845110514210600024000e0f28155618801c01d03103401041f0078521344511101d1034040c4009103500c8d0f05282000d012580c00150003442043c107500b100c1c40307000001088600c043d05038540580c894001c405042c43c40c1070940c502a5120030041004102243c20b82e10030300107003540074200c802100182c081000c0354075010400038001002080c0c3c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 199373075 1250 199371825 199371841
    0x30f0606060d020d02180906010c050619060803030a0204090f0911040f06050612010e06030c030706030b0103180f03080c03060609040506060d0203040c030c0f0e0a0e2a04061409 78
    0x182c040401074801c054509008849000c040343e01c032111050408a00040051903810300780f1a099011600782082c00005695841d800da8501004001d0b00714840c0345518500e20192680006005095820450352a41000380241002e5001400761002080c80c00007203070703100c0e1414021407484580100c0c002d8609180d00781800b0152240c1d01480d0205925078200046948880005182514030341c100680f03e941454002c2c0203101001c1c204610981c41040d1074403041d03902065080440e0b009090009000400c3c50060300544000c40700c0001542520003e101030084030884c030180350307200b80c1c1c4200b40365448101c80c442d1030109861880d000101400343c8030b400d040c1f907440160000c0c0000c0c901424201c030400820300342d031310499040341c002c118124100704210010030008007800d00c0a011500300343c10704501c01e0602034010900054240c4030b40c1c100f84000c0060242108004900314031003104840750324100301011405041d14007a500e081c5000414074000410300a0800c0c4c0240b07001401d17140c1d00a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 199374325 1250 199373075 199373077
    0xa12020705010b0a06050c010b0301091205031305030301030803010608090d050f0d0f0e03070b0106050f0a0f0e09010303030b011107080304060f11070306050f0a1a21070806060f030f060606 83
    0x141100c41c0c1d03580d00c518044603951120180000c00c0c0d5035450640d51104600716609580409510134081d038149140040011007407100015180700c0c81ca031150301c13640d0325140650641407e4201030700e2400000300100030f10215400440c140d030740700d44a80c0f24a850364140550388600c44c0152000041e82440305103000003050b030003003500317903090030300400d40700801e85220040318185d034400110b540c00003a0200410031000043c80c014402814654107004580180800358410300a1030020001d180307114600f80760282c00814407502c03000d4110240c2c0e40c0c607480c0140007404062009070101d10b07040c3c507180c840203000500380705440000f0081c41c00c09240c1001a01c0766100712410005004424501c0c0340491001c0240c40e0007540154404078050901c00460198007001a1000500f541090007085006814400094000c003064511075802900b5202880003400704240c8140d40b030145503000640b207000018114001c0500f00d0b841007100c5004404c060380d8070302204880425800c031a00082483c50104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 199375575 1250 199374325 199374337
    0xc080f03070e18130b34090e040308010b0f0708031014060f0403060e0316030306140603160c020424171c0507030504030204180b181b0d0506040b041401020a1202 71
    0x40411403d20000120003a00b01c4081b582c801d0b0881c030344c5039414039602e5101040a000340300d840c004080605154500401c1d403c5d050040500645000a544000e001e03000211100c0303580100e0340b10740b40d050036100402030b95924400c042320441000354410840c03a260045803102c07500181c0c0381d8a000d140d40d0350348028044d1a00f81040320b000a00ca0310504400090480e0101c038030a581c00a611030071302c0402448a2001a8a00d0086106000f00040c203507011601c07410b030190506058070401320074400240980940c4016455070400d88841c180d42c46002e0001200381c461908204101d44c420a04e12035641c0d001d81c080c01d01030311420016400341d40c0160021300c081802850006e140a4490300072805035103500206003629000032660106100d0000f00302900401d6000b00000d28490050240e5902c08440030003003030200100742c181440e030385c490140c0880300e80d2000a03281d9070728190030130f5441c1101c12201a110034044030b04003240d0310410310843c1d403001c3c420745075403403090041e1ba03014000350130007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 199376825 1250 199375575 199375591
    0x9060504020315010b12061c1514040c05061602190503100207050d08130501110a110706021f021233010903150f1a0a09020315010c080f03070e18130b 66
    0x403007140c016803240c5100c0c2c007481d41c046c0d01d0051329540750b402d400c0c082b20000640302400b28101e0b000d010004240640d51021a2022103000703482d0307950703803070100040c40503850300a601081c1c54090003a010652100282142c00446c29640b001714042c0b10707c02a4401c1034002003150304901c442c0558030703009183e0590414484200c048000b0044d03683c0d039084075144e041407001180c000c20502801d60b4002c011500d0008401e001d40b049a203001f07800781d510003503040c051100c4e2030060340701003a0310309a9042d00c4401201c0015615182040c40b0005104018011074641002100481c0500c03141c90038802d0303800c01010713958035440340c0c95031311112100740300c84811814540d102c1100b42c0c804146800b540c80d12602038021168181924030400000440301c0c0d200d0340f03020b40107004111400c0c0c44a580c0900e261805c2c281020f2001c4540b520f0709551013905512071156501100340660b143e8801e0300c4c140c085c40265002e4071550054980380000c51011181d01d8504000301900c040062602c840c0c01d9004510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 199378075 1250 199376825 199376839
    0xd141909080d03050610050901080403050c0c0a120605131a0c0705010f0c0e0301110904050c0903070b130e0103020d0212010e120c1b09070f0e0409060504020315010b1206 75
    0x129101e850400b2040030a40740000d88071002e102c480e15015212000001150901600d0130211500190640400502c041c0510030081071466940805002c14841ea000060400c8031041d12000a01521070001006994480c50031000a54a00d10fa40da554100d030341203000f904506029020029400e68010321202600000340320500000f070090103201c1001c0b101101c04510942018401445166542001440381c1e0400c43d58005e82c000329022070b610203106503000b20707050303803020102ca00714428030124503014480e4500014641480c0001f404000495607101740480c0d035a503010301d20a22080c0006944840c00300b103010700503d8007104205049541c03600209144213000142420111241038001c3c450b100000c0500ca400740c00d210948d034640a2000303010322000c8075004a400d0910080800c7c00b403001e0401c41154041c0600e0085034441402030082c0a071103a5490114090003003030b00c04038003d02c500c3e10240380c003000040e517103810b9840c003844060400000c490b0380d0b031a421010b4211600604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 199379325 1250 199378075 199378079
    0x90315020901210c0e0306060d03080603031201060216090b09070e04060504050a0c11030703091a0409020d0204090e061605090d021807080114060415020f0109050f0d141909 76
    0xd00d83e48481058440034a00107160341d90420b011784000320121001740311b0b030448801c20203940e417030f00031420803150107240c09440e90350b514000c01d10b5803003910007110a210010000203042070303000800301c480381403290010301c12a40d241c45800a80e1100404160721852000003e62418820058460130a20003880882d2980d035500125048030000d0300c504076040d0b1581c80d11030304550443c100c000c00c0380540340110325200d1542c400038180003c90060000c1844c60b40544c0c904a030607402954080d10405108642e145070801020000350f009101d0038009504203100400c0200d00442e0003481000140e68050408110360012038041e072001c448035a1040038021010096101c003c140300411004414600f158205850043c02202c0b050784444410021725200030603a0b102ca4040c3c3e40bc86440c9854035441448561003a030805800d0407014486601c0c0502007401e1010004441140d080c4840c00d4480d0f48d515007200b203407400710b0f0071a079541c40e140400c140a600e811018400700443c1103840c1490f6815 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 199380575 1250 199379325 199379357
    0xa0b0702010b10020d0f0509090406050403110102030f0714070b0c030c04031b03060b0a06021903110a111e0d020d0c0b0f03090d0305042103060503030d1a01090315020901 75
    0x10f070401c1d4400006030b008021511344650407000ca04551100c40c24000d003040102000902030010061009102075102d40224041500400c1e41481264a800003903440b843c0008090000395401ca0741000080d5040301c42220045491045843b00c941002a80c1580e80d5240c5c01030096510241c00c0841e48041040f0020201307806c2074802240005810308038809610710b06001040d201846095886000b02400c2000307400d8001680041c00d000d1003110442c40015803d09071540850b080715032540d80980d8051000300040c1c910003006802c02105c90150003071520600b00c420504000c0410b4008020040c81d00240ca0f0030070a86a00a01c030324035050b00c01da160150b4001c0343c2c1201081401129011007800400d035005c0c00b02e6010405c0310300d4200440c0c9459120340c50071416000c1c00300840b064802010303860314460b8000c4006400041c003180e80d0b440c0d454602c0740081260380c2c480310020318591b102080b07d40c80303410141c040b41d41160340100407a1181000200039482500e41c181840300c4101040000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 199381825 1250 199380575 199380589
    0xb0615040b040806010b0c06070305130b01080309040c0f021f0603080a02031308030f030f060409060612031209020603160203091504051c080417030c010203090f0706110a0b0702010b 80
    0x40d119481c41c0310b845030b1924080500c2c244040e0010100f4a10034020660601030020306130303a00050a18012815807641521034a17120000d1002406c3c102d500030001c506e41100200818591100392010401111810811240c02510300c4640340103810032510700110400c1b1241540c0d610700e05407800540780741c1e03070740c1c50a071983c4c0015000405604081081c111925000440798020406080550b03d050080000c098035448003c20f018ac0084544020600540b81c9621005c022a44500200007140c1c590b0612994076801c41c108800040e1041000c08060540d4011400e07160760140165086455802c141c2c49204110392410085101c1409400f4070303a61a01e03070b103040b55a0070481155440b0700b4401401140703164070103070f0302da0920940700103400199414112400c41d0010240c000341441c04168450a40c4139402d6840700c158004000d01c6000d86000c40c001625000340002ca421007079840c0350607103c1014072443d44010390041515070700414181c4032241d910155a100005485028030005800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 199383075 1250 199381825 199381829
    0xc02210708060a06080706030f0e06070201021305060c0714010c0b0f060a09051611010f050a02030f100b09130b0904060905070b090d020d060212131118040b061504 72
    0x5500105080207207075401d10a190b04108580c0c014400076003401940c2c0c0d500d2003548241010142d50718800c400328642c1d40d0004440d03040010503541141030500b0000d010390000034840c88141840d043c000741a1030b24504a811209114025141480c50840050300c3d003c00a800103040c0400360307410b900091090b00e80e151140d130229100a1990070501c0034441060040d40003800c07450701c0c04040c09001e00c2d819040d1041020b03145006a100d480c0086014003500c4081140340e421420b01c0c091104602d842d070069445413102e0401d5041968440030030521a81241c450600010810441c042d9a42040d00340102c102d081980c000c0343c064a2540070076010a07044030f00343c4440381d5600000301005800d100b080014451007003124100f0340c8520018400c0c688403d0028412172511500380100412901611202c05014002014a2a210030601030300c0e1013903d0116441c400942c0c0c400c100f031403e886510080d150241e100404c3d40c1e00c603554112120400341013654071401d05000d15403401a10002080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 199384325 1250 199383075 199383139
    0x30b181005070314040f23030c0a02040c0f08150f1e01030c03051513060902130303020c0a030f110f15130806010e19060801320402060a0c02 62
    0x78280c640010000c044914445070720155070b4040d001d000108216400ca082855045200c0e10002e5110140c194840d10307030360141c98800e0001042e01c9148000100c0d0b01610b0034000d890174400000d651a00b2a103640303014402d4004a11068085000d000c2c0140500e0303580000588084401100c02002030040d000414080b510700ca0b09284130501035a06018a4004a005003002d01071401e060000c42c500e03481c802045405102c01c226082003046142c3c200c203005010440c1c046540b03c0d42d0744048909900b280c0401d40161241380314000d103a00b0201c40c94000c40f40c101c03141c1d20000f00c0a070342d0702c1c1e0301d080c42034021075101010105080503035954203151403200c1007900da42540d07407a0f020210030100c05194403c0c1d40a806c400c004000501d454802141c0c0042019110000007190902d0f000040280360803408542d803070b001003102404025406900d031f03d240d0345c0007001c8941c0f007007220402c0e00c0e01c100e40085d0022400d0003d018807600941a074902641f00030000c41980340360080f280e00300e130480d414000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 199385575 1250 199384325 199384331
    0x60303030e01060302010e010513030c0e07140c10020906070203011d0d08040b0f130b07030204030c050d050a0201110106170601030b240f01050d05040308090105100f030b1810 77
    0x1041503018454100581064402400b000d881c40e00003a0800c03003a0101c0c5d50610100244071a401e150740c031484005107a1005101c410151a4403007006042001c480b10000304019001d010510580101541d1401c60b00d10300030074501150b403100c40069048000c490303800c00418030804005039028041c0480d40b0001c4000d10883c0200d0301c0500345081030810340c020034410424180000710b80141500c0b544000741c2c07480e000c040c1d22800120940400c980901810b404004014400166031607002801200d0258800680b441c0d190b00401c0207080c10500010180d902c4005004c005500544156208407200c2d0000964a95682da0641d0503c0314101840090b401c2080180f0402141c2d100094005290005c60410f800d4071591400540824041080c42510014150881a03100d40c0c111018102185c0c3c0c180b00c181068075020704088c4c410342d000760040d42088009140c00c1444000741080318044485418918650f4441d1541c03210060041451000c9204030903080f4902013110485802e8141000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 199386825 1250 199385575 199385579
    0x103080a030618150603090506061c1e03080a0605030a03030c1202040b04030212072904120b06100806010c080c0102040801060f080633031608010911060403031e0203070b0a06 77
    0x100c104c1401500300c40b0601d0700e04001d0380046107000401c50b0340b014081e100c40f04054500c081500d40e10320120700c000c2c41428040c032084001e18031a11880240c9102c0e071100e80da10780714107051034180c45881c0100d03900741c1e211000c000e010138465003000e04990050305010782d150503d000350000366070154016580a2a0004040046003000a240403100b10850301501505080c1400303590803540103c1800302c483d8100043c0b0191140200464006020012451910200510700100c071480c0c1115454800d9451951460b141c2d0f024191492007420305035601035008900340d50b00c0245400c580919840d541d420711010a00d148244074502c0034103840c1c050002d046251001aa15044004091004003080d1520307843e451000003a565180440091001d000e0164800c0030074a01810b0b002c5104041c002c60380001007220041d4804da0f06c107170090100b500c1007466207082c448140b05034440200000d116030301c80b101c1410140b80c40c500420807841901d141030400e4551084115080d582d642010780e0f20907003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 199388075 1250 199386825 199386851
    0xd060f080f1509030f28080108011b1b0c0305030a05030f010605361e010306060302030405100504030c0b07080612010e0d0e01230a1103030f0103080a030618 69
    0x51044a040c0400481100e0b140004040340c4a01800c80e282d103805c48041a06104881100451500c0070341c1c0c5a81d101103405800002007442c1420700c5907403015480c00002c0d0395261507122100994140c140c03110b000401000c042c00c1c0c0e01822088041e0303a04642030001000081060001308000308050f580c0d9600c0342007140f1544819941030340f10304180242000034240030001341c2041e680c80350030317594241030150440045142138500500342d594020701128040101b10f8200c00452059482070381d0422145407264420340480c481610301600c0c030f60114001e02c0e8000c08640006034400d21a11308200c20100a6554404a41050350703e500420078800c2080820305000102140f542c450400911001000c40c4800e600c41c03014003885020000c0c0203003803070416405081041c20441c4100303081c04420341a1401c0820a8005095100c002000010910b020440c000250f031700a00c111041c2e0851646141d6541ca665880040c015051684540e00000c819a010b10001034429018401040d156001c6072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 199389325 1250 199388075 199388083
    0x3060307050102070807051003020903030a0201140a0b0616060b060a05040302150a0c03080c090a030506010503060c0403240f0218011101110a0509040e030c070617040b0c0d060f080f 80
    0x4181190b004013410800c0100000c0d20300200c501c00d5400012400341250110301a108410980e80c042c03000042c2003c24550560148000143d41c000242c050f4840c0c1c509a416201080311581d8861800c1c028110200080d0b6910001d8601c518070000700e120b80103010400c00d400144814001c1100440c082042d4148294500c4441441141c032525121001d1805000c265590310040c041000172400100804051800c0300c43e60003004020621300d42c1e60745481a590517090044900a000b00e9010034444070303108090703e0650b50700400e0400c030300d00e00203031406903120024119150740d900e4414148800c02507100612006100d580c040040f82d0b1610005081c8240000710700c11140c4c0340c0140f001d42a400c180940380c44586500c1c06981d82c80400c400207016124900509005020010f03903514201000103c140848107180c8600d080103102c10058400400100e0300507202440c07400c00030385010820b1f402008030300340b9000300048007a01c58080350f00001254010100e1944080307258004800208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 199390575 1250 199389325 199389329
    0x50a0b100b0708160212160f05040e1c0302360f0603130f02030607030209030607030b090a0506120601080d1209020f090702120f03010f060809070302061b030f03060307 74
    0x40a11480d00c6141d43c0d401445108110080074a580700c00c0c500d1045544620300c207822800018111120028440984080380486205420a041410000046a041078014135500e6101000a40a40d15008c18028a0079076008a0902055800c03c08003103d0702c0c903040f05039a400022192101154504c20850200020398040c403846841441701d01880303923844d917045030783c8a4140c0c03603140c29048151030001403c03861404008c1d814028203003004083c55169001e0500d17000d00b182100c0d02c98450741c1044d0100c606401920f60000c1035000040c1c1a1600c540040360845405011907902c281d071310f01447e003446001c0c1c2050b001c50b0804006580d502e40d00100b4040340c200004402c10080c021a400074500780f40e0301c080705026109039000100c1081c0280506003000907101070282e076a690900f0b0442a035882400341917045040c030000800c0e40f51192009030b00c00c5140d1001001c4540c29502005003507003010015005014405050942a4030107201070828a05101141030300c83c101401054140f40c195 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 199391825 1250 199390575 199390589
    0x7080a23040e1f170a060207051518210415080604061e031e050a12020706030204060503280e0102030a0e0604050d030c030b0a060512090609100f09050a0b10 69
    0x3c0b281a2105a141180300000c9070300d01d580300300403130382003030f00380341c200501c0da80050700032440440c28400380f100100310103083d0f054101c00d080287d61400b24030030320340d120003201c10f007994801c407403140d1641036400d400c1040040035441c0a040c20f03520114283e0142901510b60b00060040042c0151401e0034081d490203860590124041d1566002c0c05c054a80c0d00d5100240461280103900c0c2014000c04420284140c0c0242c140c40080d012800c060580126aa074240010300c107481c00000c40e1032082c820389080d144a40e0781d051035600c84a5414060054030003401b84110300440d1a5050782104d4400c2011a02946001507140e2506007c0f5100316184a1051000d58010504102c0012004585851a050716040008205034500c5048005000c2d4245460300090f8080e0003240c541e4102005d0211516240c040805581c0c40b510480d8450304107441c880c00ca540015940b0b07500300c071a500710900010420343c00141c840656280d813440c212841800703881c1413840e6014003030180851032106024102e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 199393075 1250 199391825 199391851
    0x1104060b030a2322060b06070b010608090a0f02010804110901140901090b010c080a050403020a030f05011503030206130203030c060708041e03090b090315010905070f020f0307080a23040e 82
    0x1c0f01d1540904860300b01851180c13000c2051016080007110740c4021a81d00c0c0c05003e568448806e441c0002582d1028014000403403003040c00540d841c1d070b00240030390007254004905c0d000350081fa401901c6200003e0002c8a80080302450b50280f512040041c1c0c0c02000b0712062642000304200c144410040182c02130b0104504185070300200b6600920010540c55010f2150b80e9205105e0904940030b0040b50402544101d0360781c0c0010500c1040031000410500400080000500701000352190444901c0010050f80201c4002360304828400c00d510421400030b000c0c0c83c940415035180604020003149d901004c02e00c008140001e0011040446a209248441e82d802d044980e0b00d000e0305204c5180b01d540401e003800122008a07480a11001ea181c03100c048075100c0a507180e404038006000e040343c0c0a0002404954048a15440080d02040007418000039600c1c00ea529119201140e00c100d854105000c20344142804040c072483c8091440c01e042c3da4400e4a46c0d080c8040300034450f0001c1c0207608030f060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 199394325 1250 199393075 199393081
    0x1504050304050415080d0503130501091a0f04020d020f040906020c01150f1d0a02070f1112010b090103140a0210020c010f11250b12010f211104060b030a23 68
    0x50000706e2145070465803c00e90707140d81e540c242090341401341220080c200d500b00a01c00d130810003801d80451070b00c1403442c9400450380d07610804a05000e0202c80180d4000c0c5800244005424101441030401c2c1e0050408240b0403010f441700d00507a1310140030380750241e41d1000044900804040b290029115042210342c140b032820004510313020740301e01000d0214001a002c502e960f102c070b6040380c0d003440d48030303011100c2411541415003034182d00141c1280074036040785010090180600c1400310100300281aa1801d03400e60302e40d01144074071b01174a540c85119020940d400341e9900c04030301c2c0d000d0203294018000d03981b40100041800b0700f1440c1c68000d005900070441c642000c04640003907103442c03580c144a110040f5000c4020321094070b500000c8220b000060b03d0482c8500c001455041e180c0554000100035540e1418145000c4840300c440b040310108000c902c005128403c10284c0741100510204c3c0b0720b901c1c2c180c08090b69206403108043c55655550f0b201c4c02080c421580e100c0c00c0c2c40e0005040d020b107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 199395575 1250 199394325 199394339
    0xf010b06030f07120c0807020c040c02070303050f13030f050c04060317130b0f090427030507060f020a031b0201050408041203050c1c0908011e05091504050304050415 73
    0x8040a00810b01c1c6010910005108038481c01d042610303503640207410301c40891070400c040c20505c02524210014014000c80ca0070307908150040074240341e41c9500900b40d0130b1854070111034540210285040f60171081040c04004402640c0002c0a1b6000d96840010500c00f403074060300d000c00140c80d031401035041030020804500105e1031028046880d005c0e10b56910f07000b0b01800118105500a0540e296011403030603440b400300e20141c540d902040d1020804d4101042c0840c01503400901666140c83d24102014002442072000c0d000b42c61083e00c0105014040109001c10703a00806601c1001980d03484442c010f6030306140700602458040d000801490605441c0d10351244520b01994034120040841141014494811030b840000140c00340c5884554202c00030740688200706540001403040080402c590b0303818800c0f80841880010704404015010028170301901e0010303c400d4081c09009510070a00e001d100c16144038600c40c0001c1c0d070f5224101800c00c412116904041001c15003400402c1c0282 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 199396825 1250 199395575 199395577
    0x30b0105030d0c111203070f03110d1d061308030406080a11130302010e03030c01090f05060115080a0b0616030305090d11060402120c1002032722020f12010302030f010b06 75
    0x16138054800001d0040843c48040c6544a0404000c103144204640e8405050340f000001c90603902c00019101440e240003002c0712540f00d50301040300304000940000c103252502c80020b241010110311000d4140741d40d4480035040d5001503210074042500c41c41001a00c40e0584501030390088004c01090031305c5000209041e10780c0a03804020305005a80a41500c6658100141c1f01d100103618024044180c1d80c0c03525a00c90011a4021282c43c802c0c0750000c9207903100514405404222907444e40c186a07a4030510b0b5015240740c142d03880d0000020880100002c1070740905541700c0d4040d840c0170560b401d11032262072602c55141060f0007004590b0003861503806004c00d845400607011900e01a499009000d41e45c1080045042d050b48410000182000c481e008405042407000000011510003442044807624902400400340d00600200b54060340101e00145100c803079402080060921a040001d00a241d00c400b60030000180300d400100214a400c218803024148000f001303020b02001c1501040702 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 199398075 1250 199396825 199396853
    0x6030f0609021207080c090301060f0e0f13030e04093003050606180f0907020a0606050307030c090504170c2107020a12030e1302070204050601080c030c09010216030b0105030d0c 78
    0x70461103201080c1c81b408042c00340c44911074010001c006140e43c83e00c0100380c207106442103090302c64040002848403c02c1d03404403407003030f02d040e45504802191a075045034400c404030b00c800c2c0c0c400e940300301e0440455440d010a049000d1402101c06e441908544800c0c0aa40701000443c1018200b108015140c0c40d20015100078986038010824140c1407040000c40016400d90b00c03a400c907610301c0c20400300c503a001554000b81c6010b52030800103a51100709054481080740005041080e03091010010300034940d0001713600034080c1d005104080f07402d50100b2000c0e401444585101d9001c1240d035402c4424003004101070700c040e0045c6034500f000650200704580c1c4244140e0940f03514416100742498010000c0600c142c1c0d0080411a044034140b00c1000250412542a80104c0c070303050000f161540581070041c00782900d41e2000c1d0655603071a40901041c2d00c0fa21505046019400c2c044c00c02d100d42d14401d40c00707584200743c110402d41c1000189442c01000211420812104002d0301002c07420030b80d00e0102c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 199399325 1250 199398075 199398077
    0x9180e07061805060307090501080a11040e090f010929090705040209060c0706050d05011508150a2c090307080a0c031b060504020114070206090409030c050706030f0609021207 77
    0x204580b10580c14000c0d0300c0d50344102d40141d00041005801c980c803600c11710a13a00700740c80d656866225503840000701c600003059886400d00410007031098017402009194045001c0044072840c180301c0a24609450a015080f641442c003076400441020001036403460302fa900f801c13800d05603d0644e12080c0e80d85114800c01d03009a500180003c400e448030320444540d1142071088590300c41e51540020000e41c4541c135030110581c40c0000206a0b044100781c04d0303d50381c600f80d44002e900c4d211406030b51106000780074619070100c84000001038040ca00c81540c11440707021f0f0103900d14114040441e06420304018900d07022a041045400002140b010590705c0556052800c40e01c08945441c0555070340c82e0340c028003071021280c05180c0c820042c2917080700d88074520030380e074100301142e459030000c00c24002d03081c1c001c2d4002c0f0300380003031051400c140d8481e10354640079140844829110761200d5041a9294200a000a4403005824080c008502800b00140091b2400b145441d50003490942511000f405c040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 199400575 1250 199399325 199399337
    0x12030213030b0a020c031902100504052d010c1710030305070803150406090207050708030406090e0a0b0d1a0c0403080a1b0615050109050402130b0a021c09180e0706 72
    0x2444070150ba13810380d10300a09600440b55a03180714030304010200860310000c4011710841a80380f0350754406008460284da4004000d1022001104085161038625050701ca60021380c0c0004545140090080600f074030080d48544d00314241e0070709041c1061900070480120b1404079007003000000da002c4221000b10b074018001c1c684035151007a5034400d40f00107000c1d4a81c402c1c2000004106140d041d030003008514880c400716224159100d43c0c0329180d01036442610040b54102e01c040010314020802c0e1a07000103a540300141c61501c001c0004c441400f2440103991b0401c1880c0380080c111310b507880e03a507000010041d5060501e46140d441252900c280110344040000034154850503840d840f01c0405401d500220500424001409809801c6800c5c45001e00203a11101c0001d09814a4400c54666602c43e4450303519550400405c5142540700c6210f050851040221444003d091040512000c194598480300e8661078034000200b0701c440c2d120b210903018507095840311851030000e0b50700c00b15207940c1810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 199401825 1250 199400575 199400581
    0x20708040515130b04081006060504171203011e08060105030d0c030e0d0501020d0b04110a0c051608030a030501051008071107033014030c070c0b130312030213030b 72
    0x82036060255440d0791041c04003040d0080b0303221070200c0c0070704242c620042c2101c11007d00c1081c00001e407441446410007181c000c120a00c00c0415000c10070035051184804c40700010490605007070554002d81c85070b151110070aa1128449a520b03828200901103040100603550419001903200c42c40d034000c80c402c1c090640c6da44000c00d400b0700b04103000c020004080c011242100d04040303001c0d41c082101c8000c10340ca440e000da0114603280c42045000801e4042d0581007603c94101a250b0448240d01540c5030b104d244a40301c504920070a28001a05c81c400c0515120207500c43c0c0503050390b6040e0403051041450141d906920b55204400c19030245e80d038034081c0c9415010044840c01c0262a4002400340c1150040d1204030070781642600c029014078840c2c8170150031a00c40100c8821110302e50610004108001054a0240302400b41c001d00380210107030303001d0740c0e61201500040c2d032001c90000358034041d080041040c8200305c8001061900d440c00e040d807038400c06074006041919240402071080d0340c0b4a000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 199403075 1250 199401825 199401859
    0x30d02130905040501050f180703020d06060b0a0c0203100c080a050601031b18120302070608071404090b0a0501030e03090d05030910082208040510030f11090a08010207080405 77
    0x840d400920300140c00300214109414000d0203040202c1d03180150000000101e07803043d45202e100780d0380381c05c07103c0034121480c199420881080503880058542a44940c80130900300c071900c006150880c25030f02c0301d001003072061040c9401c1440c0c08000a043c0c1d490a03580c841a190404031540d4806032070340c400681d41d0b840e80010382c01404071022890680124060741a04a0b810003101e140190405404040040d0b45d00743c6207068615050000340140c20880080044034054000306402c0300503401c004500b403204401488040e0443c2c1c2c0480c0905465454114613410000c0240700505400e107400d11031180c1c9085801c0c0d4900c030f520f8989025514039605070341071100501c03c0c0c40310303c44001d20706125001008801012460280d402420030804910303a10000030103900801d00980d4000810ba05161505007048950219449444117154031040c0640b1680c210b03210302050740e200d40c40429103415a800a101862a50ba00103c066030704c1008202c010a42e20b00c20b0301c04462044407a22048210005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 199404325 1250 199403075 199403107
    0x2040902040906050117010506030712080304060b0904030f0e090c0a0509031212060a0905040f0308040212061009061202090a0b1c060b010314060f060901020f030f030106110a0302030d02 82
    0x40080c040b0f6103401c0c004181c45194400558a88042500070711403034441030105600c8481500c1120340100c100c1c0350700c030006031109010790f034454029040041e03200d41110115020217021201100040e10410107182d031a5044600d401c6c0a240c01d40c0c0c00700c0380d4a04480a40d80c28810200c0810610101062020b6540e5003003062400b5042e00c0384c1c0d01c58031800c40540020303180c08140e45492190548100100312032001d48116446107422002007800101a0346060310710f003002410682c3c01980310014080c01c000100079440c010904000d07040d100070b01c2d1905400c101c0700301c0d80003082e910b03200c0580380001d40e031100c4a040d000048410005160710b1250006510004948150894034645071841d0042c032015902c07103002d000007030302c0c24840c0000c1c40c91003c3d683d41044840c550b1040984590a200e03060100c00f52003080da040c01122180c0c601945200d166402800900700c2e851000070041c80340652201d04000c1e043e1520300200b920007081d0750040c2d03c82c05456511141075502041501c100000c0f50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 199405575 1250 199404325 199404341
    0x901051e0d15060501020607050403021009030b270a15020309070819030813150903030b0a030f1b0e010b070804090509011a030304050307140307091401030302010c080c070204090204 80
    0x41c0004405401841c02e070040e41c001c8090003074980d1030110700003165400458041d204581580d07945150034150343c00c1016803003450241c0301c200b00071000c1c084002564500c103c0d001f52000034407200726115000d003a030318004913060144003541103c0552030014010700d150204a10802e640940c40f640c0c0c5079459481c0070b640340e2045495128210046120b04445440110790360b00980d6554042e0f52800c1c1014143d1a1000700104030300500b43d90012000001e50001002c80c1c820316022400e0b00d503240004448c498182c009136250004600810f08014030455080c2c454070240c5001c0c103c103440d00b41510804c0340c0511589085600016010040103039960407a005001090001c01590600030f88140c000d0440070a0f400d400c284000b913104103803500100340e40440c0c0f001001041902d04002045107410510306003240c140c40345c201e0214002906005030080340c510642011425859428024250ba220380901400d2001d1001400101400d110403174601c9a01a00c1c041040b5580e0700c040307030042904c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 199406825 1250 199405575 199405579
    0x9010e0f031204030501050f151e1f1b05060f10030b01090b0907020106030b0106050a0302210415060f030b07110d0e130506030601090509030708030405010219020c0901051e 76
    0x240040402d07140c800180041d80d029500801655584000060644d04181e9101c1d201d0f01080c40c1c450001d1810700c032000c40a600000440740441c0004020130706d20300407203074030f0402c801c614443c1c01d90166002c041180f030500c60700420f070044c0760543c0312140c54140c050301035145940c41c20001406442500000401140d10102480e000e603901c4074690000c000c81c070805c41c49161a01c010401c614814002c030420f80341c1290104100d6481c1400c203a034954888003210342856024011107a9225070b251811101c0d02c5407000c40f03401883c1a00e030a20410b0395409032030303a06070701d070880a101003030204050405481d0300544030707002078442c2601591040c00740c400c401014807400c20a15a01548040040300f4518181e844a200e801c40805a0003600c00031100180c0540c400c1e030041010400c00d40013180c1000b119010faa00e40b888030348070807800c0da10840f015280e03603400240c600e40000010002d1545081300744042c103840096040051002d0806104080c404c0718102140300b5018080340c00c0021366080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 199408075 1250 199406825 199406833
    0x30b160504080d180602060f07030209010c0807060603030f1e08040303020f16020906040207110415081501140906102d0c0b010602060709090c180e040506010906060509010e0f03 78
    0x12043c402000002c0800545000c2c0114500010394140005540b5000f124012610040780da50080c04400a400c00d006060400204c03441c807138003052503540240011809103201003411400c41c00c010388400140e01c43d0b0010419240c0480c143e030708180c20501d80c041614030300300d4581d45881c10120060b0103001c0300c0158500e40024a51010354261417840c84084c0300755140d500031ba0302e48003000102e00031684060b211070120311403120b080c5000d5100a08104291b04400007150329400c1c51841d000710a544007140c14130b42c0b0014081e4146400810a8508046510080e5468140c001c12620780512040005010460580b400f60701146040700794520854801a43d070f980341502c00500c0799603000802d03140d840030f5000101d1118404a801d84c032400d001d031074603000142703001c900c40000e0485003400710400400300c0e00714003604440e821840c014558003050403084d09081c100f00c0d06040301070b800032418030b00d088000c129264100066030800d00c0c0c00d0808a5980030b403400071441503041042103e605000e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 199409325 1250 199408075 199408093
    0xd050a030212090c031b0d140a061118040902010c0204020d1d2104030b270d05030108162d05030106030b07120606080406091a0108100b010801030b16050408 69
    0x100040608240c10101c00b1609071102074034044c20070713140751040c0c0c5801c10280c65407400401c010fa103e48200d804235804644091509031039100866550031520042d619001900c100700049070300e0040501c0c40c0460741003040102d242d00103019450348010080c007864010481e81034545143d4803203c6582041d103002c000b1000640000c84e2585131100c54804d101c0f4446030043c2d0079544060580d0156039002d804c41d100c9850703100d01c040801d44102010b40c1e44130034240c00d68503408410f002041e040d181944030540c0329410018424142110450992641096500104880c0000744c424000c1111406440004694198040081490030703811a076059800c20301300008110800b008188550026071f1341c0e01c002180740700c000090352039510800d40040d5454000c2000314129074843c4c100c81341300310f00300450110305141c0c02c06408826401000a50820141001c658040f03001e60f10490100346840d6110390304554462604040181c01c1c90394032000d41c0501100c0c54002c4040754040c20b080401c452201d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 199410575 1250 199409325 199409341
    0x6030a030825032004030b2215060512010c02060109020310030b041a0c03010b04060315030209090d1805010206010902090307120804140a03030c03121b08011e080d050a030212 77
    0x1000c1080d0500d040040c2c4645503411001803802d4400703413a8030507080081030315501c0c56402c81d07039400c0443c205a903608d100e4500000d01a0070380305010310a44840410800c4c035000812107440c0804942c5103250341448031311a101303540494030300d041da2030690b03005031070b5145e4008101c400760b007a8200620844000007400f00f4809141c110300c030107404104d07245409954250461425000030700c643d5030340107010701c13013440f2407802500500c80d0080d40d044001d9605640b500066900d820540300010076400044500b81403507031003441850720580c41009405480d140c4030000f0758078801440b8800c1e00d81d6004c5414289682d051040710f00402401840c01002d03201424170310f40550040c8541c0c00081c8611601511030305003250303148100e98040e1103900440303103151029070f404004001801e01e0385558216150380c01000d0410342c0ea010781199038030302840d814015007a500e0040f10784281507108800108001c20702000507100c002c111301d45031003a100e8508000550207400381c02d450041103003094007007201314 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 199411825 1250 199410575 199410581
    0x6010c2307080c010f090e0606120f0402030105060406141210110406260703050907080627010b060f0705030405100c060b0f01050f210405010c0908030306030a03082503 74
    0x180380181c1c243c44080260500642c1c0e40040d4a48140205500d00c500304282254031020355480003001c0d00e803618068041c5c1c2083c44004080316200701c200b86240034030065003400d01c50558400700c190760810019081246002c100c40f004024107204036600c580ca1040c1c05020320204400c0407803000144800d19240800d001190041c0c0950000540302e061407030500c00103103040000c1c0f095184c040524640300c028045000e0030f4001c041207031130b2140f0031001540040400015228000144034112a0b201e8500c4564410721601c8249241c0e80c1008114031640daa26811107000010551505036030740d0072450101c0c00e500441c3e000f40d07445480d2220390070969400200161070148105000c101c1a9100700400c60300c2c40a15046070300050301400603166600c0d00c0c100420200c81d111030440f00c0d144100407044c4102c0c208990444a903511103442030b12007a0001c800402034240c0d200038505500d0140c01185d40e61802010140411000001162a104030500b03480402c81ea030304074040042001078006005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 199413075 1250 199411825 199411829
    0xa0e010c02030c06090402093114060f040902100207061101050f0105060306011803031205010608091c09180e010b01020a030f0507060b03030304050d0e0a0303270e09010f1b020606010c2307 83
    0x40f0110703002c9c3d0400c40000b184039001045a01111308130080d110901480705098002d61750f44d412a0755501000090b94494484c4068001940d0080103110700f4414001c3c48058000c2e0004910381c1010306000324695482c03056815520140d8940ea02c1e641c95070012200e104007010019a40e4201141c04024151b010000180c9000091000d1005982e902021207800301c0c103c034a50303802d4008503042581703601c0310501501c10f0203241c544021515101c400d5213184c071400101c10071140355203440048024100380220508030300c09001500180155417805800c1d00e408200d0361040103400910a01013008aa00c0010401c0e40901243e40302c4c40d29281469607a064289078101282d52b8111104691138182003040607a03905a403018025828810300300440b50fa0300b01482c1140d2499a40401c12840005c002c0703100d4606000042401f44042000104484a40c030301c59200000e1a030b0407250f61b03900060080d800101c01c0c1703050f07198100c0500f801c10040c02c0c10385d10004458000a08a8901c0c1030000710001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 199414325 1250 199413075 199413139
    0x6180102012a0e010201020c010e0c0a080c01120b0a03060207050f0601080d0f0302180409051c0306050904021c1403040509010b0a0f051b030f0a0e010c02030c0609040209 75
    0x621030001e201c5040001029031030300ba1076031280c1c45148640d200b0030f11004410418000075040111841c1002d0a40d110040660151b5004032071030003e600c0c00c440040006c0005101420003103445800080410307485003600c2014076200e541e441019107801c84224003d41d0801421510b5000600d44991a00026001003c2600c80c00d0700110341e00d000030400d880b04c1800d0b51a0301a80700456031064003c0e4001c43e66071003d1a81140103207203140c48601640302140c2c8602c0141a0f1148217415502d01e1420003109002011300e40030090246031550004590882d40440e005072050507140d810045041400d032000781030040c40c1c075605c0e841c40303000400342040e09c4e4119803242850380c070390681c5403d41c0161036840000500f80340358643d1540c040d0000708124082e90010f40c10b4080b0500d0f0f0985154000c003040c0c1c080c1381c4001500c102d2242e2000e684141c12500f407804030200c1081c0d40000b0f649140c40d4143e644a11800104441d25586c1e5504840b103486021301084c20400315041d4200c603051210703040c60 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 199415575 1250 199414325 199414331
    0x70b0f0a0815011d03010e01060f06080a0c120e0316110406090203090d0c0318030503070c0b160312140108070306110f0a080606090d110411040602030d0f06050618010201 75
    0x31210b10726031050031010881a074407a119a4855401202e290384504240c1d40c16550b50b03862070060b80401e02881c80030b070641c070180441d484d01d0410011b1081c940100b400e4269480c3c20a1006100c0d40a030802040348150780c07012072000100d04501c1e00b503119154000440c101804584001c100f1020014100c1d04821101008042ea80d4542c400582c0302c100c034200c00c80e0708229078184800b0302840130120b050340a854103801118040d00d0f0394581c41d4541e002a1281c1e400400c160003005819a42100a00030322078442c0e0500c21002081842105002c5000301800103103034480303c03140c8807544812041e024820160744270b0350b904c580c2180c03101c80600040d1344441c188440742d45064424002c580d43c0b5034003450690b01d400c0f00f2070b008890310000501003a43c010420404182140d91300e005280c074050140003660f02c010001000c01c011503542d200800150309051104100b842d8000c0152510b03002140720105801c107100702840020308203034000743e80c01840415029a94110109008445002a0020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 199416825 1250 199415575 199415581
    0x15021b010e0c18042303040b070605160e040507021204030c08011a0916020a0605070519080112060213031b03050c0a0f090f090503031303080f0c0318070b0f0a08 71
    0x200401c1c0c083d41d194031102008000208000920a44a0110b00d459542401c1c01c01212001c603142194000e0740045654000811060203000705481001e03000303541c0c1500f0002e18001108050319108040c884070f449030741d9070400500154002e10081c800c0156096109503103603100e15004c20000b4150283c0d0002c1c0d803815a071110010180000751001000c0181103c045a54009186a903402121302120440c0108114580094480c0c001d082c010590307a110191215403d0301d100a11100087c4a0030810001400400101072400d20b0448600e0700400c0160f59286200000d101c40680340d840101006005544170350340114094511064901c140144d0307200c4101c0300704100c0101c41d140502c400c0c01c06000030070403406050350301040c0f0400350440041849145601c40fa81186c008803040b044507040c03803410a00f0103a00600103030780913984020355076040c24030000c607030070350f020042800e0190700c942e5441c48408042000003100500b11070305004d50303c003a042c1c50005141c001c07000f030001207103000000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 199418075 1250 199416825 199416829
    0x902092802041223030307050301080d0807080c07051609140f01050609090916090204050f0303030f0412170a0f0b060702030c0402030c040302042a091215021b010e0c 73
    0x200d8040340e4055040030f844080c81d03200d2140c80b103c13011405000d2003283c90041000c070000c0c07020754484e540303a4407020f0b2a0742c5440d001e2401d1195a6241c0d0307080000d248100481c050300304c1445034000020b0302840e926a1020702c3d28038680f501082e01c048403201c2075800050102c1150300300001030300340d031140c0c611603450380c1240b00360041c000c3c000c26a0024080c040100c0905042c0b04142d40508200b00301d03824000715051184814286411840c00036800280510081c2003e100b10481c2c0d045c00d80046141d850b100143c0184004c020708010b0400d0081d040c0d41500a2144041000000110701000c540c2c2c01d0401ea0b04008107083c035100d0800304d00300306510100c0e00e0a03505a9075202d07009000340803c4201c60007080700a41c0010030000041c03409002c00b00158407148100d241c200402102840081582c220061801800c5d41d0000d0030032010110510441c41c0b5240d0648489500036030b07043c9001c2071104150080d005101d40009817511803210400070100c1501b0207001300c1203240c00d80d1603036194141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 199419325 1250 199418075 199418077
    0x190b1806041b0807030207030909051003060b030706120c0908120c06100308031503030c0102070602040f120203070b0a03020d0906090308010e1e1302090103050d09050d020a0611010902092802 84
    0x168035011403d02800141d2241c043e400a00b070051080c0707001d10b413070354648004504998040c0d940c0e0941142c03014052040144510491440407000c800805540c0d00d00280104000e134104070000001d0348030402218140d020780c0222000d45030755801e032a1000d08007001d2950300e40204262202031300c101d0000c910314071030646410f015660000980d6143d41d0300d20100300d811140a08407940c161004004c0a1180e250078806442405d20803403015075030b41e24000f545c1200b1107181d040351040500ca4980880140d80c00203280c003c4402400c0f50948071500480154000d0042c0300c15000b42d1428240c540042003e90390244102500c80e0b02d8501071641c840c409150044400c070380c0e15400220480b55011000049000103902040c0010340a8143c046907000c501d0100d8280d1003194503034000070540c000c0c0f0b90042c4000029000036140f40c41c21200b83d800250b10060b40c0d114420521900000401c4030940a41200400030b0b005004400d484c202001d12940070b040e680c41551400820952000d001c1c04140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 199420575 1250 199419325 199419371
    0x403050d05011a0f0903120c071403010606020316080405060f0705212a0709060501020706030b0102070b0d200d18020f061308120706060617190b180604 67
    0x1409150030100712010742c81017907020700c0c1881d07070500c00d14120758002000e03500104403103501a0081c0c10103600e02030128422103e1300c810144030340d041030018010240e0000582e014045103581403040c6010360304200d01c891165070080c1c2d800450000f645030394100414010040e0b184a44210b5070303a903e04040480003044046502051030b8400c01c0100103240310029805074048111203005101c0d00104e00c22440c01540c1e5110481c1c5079118141008290380501c1a40010071031410180995000400001d4a8051900801644500120307801e41d034000c0960050110a00c15001c116041000110041c1036400c007990702c5415904100c009030722403008011944190354040c11006400c07501d00300704a0386400981c1c0a2640305118500080c051030100040e049440d07010506540c2d80c0440d05002d010b54889412180601c202e05164190704401102c0c3c15a0141040100d12075559075028444087c1400e81d403500c1c1d00c0701c0d01e1403009041200b07261a041c003d032411101042042918410f141e2501401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 199421825 1250 199420575 199420619
    0x120d080103060b150304121103030c190e030109030806040501051903020d080f031305150f0f060105090303040b0d0f0c080406020304020a090509031207020f0309060c070306050403050d0501 83
    0x10200400c00a040b079000b107040f810700203084034221840d03a0010b540d690412207003915030900710003540c545160800e52042c810000040175500e54503000c40c044081c2d204520f1144410b0840b81004081c0300d1080000d40d05007800100244400302e5a0708004000360300039100a07101d2442c0000004041c030b0200c2084401940760030b2426000c601e0b41e001c0143d95001c1c3d0200b07941d803000421180e0320000c8124011403140c40000d107080c44241e1f040c1450b518102400704c00c124250074003800d1104c3c1c220035442481e8000402d10001c045c070b035901c0e0b0040f540ca0040c2a10346402d40310108010070582c9800024108030b0100410810840814440040980b00c0110380c0e20003151043d004140440e00e1500210350050005d4141c00140750f841c1c0200d01260004c1310003803050b820214414842e03141e111816504840700740b000305840c000701d0b151340b0b44034030034a140203101c0d01c0c00084031301007010184524001190084410004c515042c1800382003584021038a4524910340702c004140e030900000120070207409 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 199423075 1250 199421825 199421837
    0x207030e1f03050c070605010305060403020c040b06030a1e060b0a03110702010804120c0803010b0316020c0a120f0512030103150207050309042705030c10060b0706021323120d 77
    0x41c1500030340041030050312004610038204210000b003403043c001e0304c1c002c5205000600180c80c090038024244210031003903a03c114144041c0d0070803507442d0705c1581d80004181e03000182000c15880c8102241c01c44640e045090f50420b20006800c00140d0081d2100048c070782c50034031040f0b2303c038510355200340f00c0c43c50020301040e11900403c0125510008403001c100c45400c00c1060861142c641980b1a00240d101c40d021072400007c0107441c1501130402460214140010040c51403100d00084000106003e0340c5210040203e540d0140606803803a82c15080e04001980c103206c409050303820751a4800d010548480c1e6a482c0d40a2010340284211900c5036004400b45003041d02e84020400900010002c0060300840b61700094840b5001a90908005106400840d07460401820190030300100384507103030724903140c03c4042140c0001c078412910f646034407201c01a95203c40c040c00b4000c80340c15402030307070281d0059941c4e644850380070388a90b0b00c8240d04031003081c5022400b00310301d651000c26000385400580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 199424325 1250 199423075 199423129
    0xb09120a03020705180402100e0a09020408010c030b0613051026010305070614030c0714060a05100f06090302060901090e04081c05090a141f050a0501050303041d0604090f060207030e 80
    0x5c4240109c0c00c03681e80003000c0500503665902c0d543d00344d0700076030400440303a5500c1e0039449005e03402d0320441c140443c2c141c88180c00c10501c030141182c6900d030791084070f00415001404003500347c4510f480003c40d4400d40240c0e28030340c6e01d2800302600700f00c1c2404129141d120f0a000850418002c104001e00c03150b80340e03441441c40c2c1da04511441c440d040b5160841d15920f0050120031045400d00c01c00c3d2142c60b00a9002a580c40c049440c200030300c503190310030048804070403014042e0f82e80c058901d40c26241c041d9030241c1d4450300800100c0c3c100b0703204d90040c0c00100d000020b100170482e688000707181008565400d01c551440b49020081252015200c14055030300c44800d5400140c0240c440e25240030351070054030310f2082011020b81c407000400851002c0c09580b40200b100490b028403406001d00401c0d0010340c181814204e84120780420040700d030060b0140c03030300051038a54564024411499200c02c0e820362070001850000003070b4020a01c01c5000c031b60906540c480904101e600700d0300c08480101c440203015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 199425575 1250 199424325 199424327
    0x50103110a110a14061b0c0a230a140c0603151003060806090109020a150804080c0307021c0203060a05100b0d06080d050408060702010908040b09120a0302070518040210 74
    0x62074600c041043c000c952010001c10507060090450080d12005065149012a100707071840d1080302c00071950030424004c0303800908000504034030295000380000b80b2001000111120541019003003001c900c0717042c4014003000034010280f00010300843c1145c40c4403480030708000c56070000b282d84040c08120051000404c2c548141d0028000c4030500340000c0b0300d0307200d800440c00c025040b104100b0303e0f03440c3e686180440c140810400010000a5220125030042401c020107120300544040c28643e03010032102041e007004d002710303442c035907004180b8604002070340040c00c50602002810303407290040741c00185107002907008140c41840c41d00f0b4000106428603485200356001324880008007907035030b600802d1041d0104002c265100c01510386945882c9009030f03080c5000350042c90302e0216410b242d9628001901401610152504483c0140e110301a4802181d6041094000110248a105001c00615401069081c00c0c0d917419154001500e50900351501c614206442c02900a1442500c0b080f00c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 199426825 1250 199425575 199425587
    0x303022109151b0601030b01080d110d03090309150e0418020f100c020415050a0f060909020a030207020423090109020105180102120a02010501060806010903080d150b180307050103110a 81
    0x19681e43d607080c00d5444000b061946007030002d030000c40c2e86001000060044620801066040c00c0321807405240c101000f031078072602c480400310420305164a80c24488205130140156074098801400641141302250100400c0c1c4484a1941e81c047c51611150f008010360000301602c0c5c844d000340502d5500301d020340a000c032002d45544540b040000314400c1200681c0c0f20300880007082d50303102e06004040c0c280800c12905c82d040e5071040900d102505000c01140e6080b00c0c205040f0f60560000607110380920700250040e02c41c45000030342c01842c0c82d02c0d00410340c0c042c81703101d02e03414450010040303507541e110301e5242203e89401d8080d0115030284618141e4054110280d0035520042c130558088407a04109011341ea0465203400c80540d450b40c6c0140070803527114201c240c0c800c00908e0200303882c0b443c0da141c42555106a0703052014031900d4000c80ca84000e0000006401010024880c40e41c41c0030007030f40b0031208a60040107038400d0142d030900040c9507209001c1c62070101596400f091400784180000e84030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 199428075 1250 199426825 199426837
    0x150f080d0e0120010912020303012102040908030901020d110c03040e0c0705030a0815010c0209013302070806060607030e1201060e04030905090f01060207060e0a0f030302210915 78
    0x100f00b0102c4206000c03042042a25804420420021070141c0c52032410110b05001c280d01642103500074001041420303141880c0311030005000d10100603c038040d0000c60702400d65008081c21007c400014080403010542c014021070b507010804101141c0b0b1000c0100180c42605100c03840b544c014003090290f00c60144070b290b04a40583c0c40d892801d0110340da842d0a60f0051640c58010450311340405c204030800b1184220800c1c0309107042c5010205542c002004640d06005000c034565880d100101c484584000c45810b039406900c8110258240d00d00080d03480032203018078070b2240181c40210b4220304140c030a0b215802d07030540b518440c4020f00c50030701100b280e8031080d1507410740d240c17030780080d030504000c0f03406002d107019a948a40290501e410b02001c444040c1c196039044428032f0040280c0c0c0e0340489c000c400d85d5031501e84081c044031590b0000e5408031060700400340d0080f6000001040580001e8403080c0c040c502420b1214904900040d4100b500410804a4020386201c5080003000005001454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 199429325 1250 199428075 199428077
    0x40c03030e011409120c0d0609140f1002072307090c080c0904270303090b0906091b0411220605160201030f110d090302010509010b0a03120e0d06150f080d0e01 70
    0x1d6020000e000107800303911982c40c15a0203da2700c4140c1c0051100390001c925210b98410001c0807442c0d10310b4480340d038481c8484a0310070101c1e4003142ca88100081103224070703407000900e05824070b41038401e11a83e0300c60301c5500c1108071062070042e0031800c80d03003d007051622552501d001181005451814000580219401000418004111424490107040c205100c0742d00a540008054a00d0320b0410301030807000d042c2c3e08256000d01c0800403078039800611020305410010144148440d0540402c01a024084c020800d000c03020981c0e601c00c100e000d840c41a030118240300a0074080d070710101915039128110102c0160508481c07080d015501a03080b5a420001c076050004000b0080341c40510a90401a502e20000343c899417420203241d4240179260f00245104020000c00b1203080000700882e610f44030080c255040d05000b40070040c0280c08507119004041d11104141d00c0e00d103404001005080d8008401280110b40070072011071400404094540760001081305102c0c1d410240da00c0803151140034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 199430575 1250 199429325 199429333
    0x1d1b01091503050601023729060406090b0a15200f0f06060f0405180f1c0c020a060e03070b0406020109050c0409020a03021017040c03030e01140912 65
    0x644a1040461070020301d507541e070000700303030400500081c1841000e11407100e00c030910348105400c14150285e40101310010050603000b904280c03030714000c01070521000c10700c490135400000240780124010b040c82400b00310340411519456120303c20856110011a9401034540c46080c801d920f407504195600303030725a0070215a141d80d40380481d00c402008405405407500035041010300c40c84104010650101400c2c050b04042c9020404695403944070140944103a480300085030381010207000310f43c6150020401c4d1b852561518201c0761703403000440b84118402551008001805110b6007070300f000ea030f83c001c2032003114628091003120722a04090302d41d0b505008484002400d10401c000038401058150000b180f0400302781007250a04100740049030086017404503800050303841c2c1079088103807541202c545c3c1e80d20910100441e01c40110118600c00c0d81c9003034081c00140300000206500301ca201c2d5031000c1110712a0340046800d540512032038a4010014028890301c0e107801c60391009c1081e0450119 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 199431825 1250 199430575 199430579
    0x100e090109120e19060e012106030c0302090f06030a060e0c1908010c0504140907170a0204150c020d030806030a1b1e06050a0302070303060e1602011d1b0109 69
    0x4035a5480421041c0070204141080c3d5030994209040c400503200c5000d540865198949100079000240c12104d490400090101d1041a68240c0e10180c004c440c600e07000b045007903124600003555181602013070b441000d03100c002460701f1158050113441840c1c05000b925685441b5650301c006424186000582030283d050b0340c3e03c82c0d4541c50780003d52104c0c0407100b442c43d103240c200352070708450000001c1c0040003400c20003800550900300c2000004131081c1c0b040300c0c0503540d03004120380c0c0c180e00c0070014010300040014001000d005e6000b510541d43c0c008004500244245400c2c0c8080c5c250313030b1009400c00310718201d90001c00c0c0240480e56121001a050380d0710001d20743d4030704100b8040880105415001884144101ca00d40e52a02400c011070700604102c0508001e0040c00a0058641e00c10815400040010400d48a40c00c500b0007803240c03d0058849045c40c1c6400001c0c0c0c0320b55407002e0015840c18942c4180da4024002b29003010110b0805002010305188172100c4030200d181c0f201d07061090032500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 199433075 1250 199431825 199431833
    0x90204020a08070306080f0a081e0a0504051302120f1b0705010509010e120403110a03060911090a0b0a061d0307033e060702040e010e0703140105100e090109 69
    0x1c01a01c0510382d00d003010741c544100007404440b0950452280c1d940320010442082070b0010356045105c1e00440c3c05602c2c3c0081400508244601c0d0003170050701d41000c034480c148907400c40c01034800c0d00c60403503a6046154225488004a02a01170000f407540c00340008a0541d00781082e00d6a00304180d0740c7c41840a8079207900c0d0541715400148100d40d01d84d510f104001e5130200030701c103e03407803408031002500c0c1c680820211142580103d00020b401e511400d0031707100701035035004851130045500981c07d20640d00c45007400c8101070080d02901d8003581c0c0b500b000843d66a42e0380b2070080e8241c0000c003c83c44941c2009411544c9980d01c800c410405640b03200e805030950790800240009500c5079440c000342c20301c4a512504040d030580020b044080d440f0b0300502c104000c1030402c50490f01c0076130310651540c140d400041d02030b040041014072694a0680d070480010400709141d020f69000704207410b650054640520301300e8070211041d0b04a049051400e20080f10906070b40c9801c00346290010036444c1d12521 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 199434325 1250 199433075 199433077
    0x121f0504021804150e0a0b0f060a02010608060c030412080403121104030804030c0501021b090a051306050411030106060509030a020d02010c06050c04030209060102010231030c080a052e050a09020402 87
    0x1035018400c61407a400b00411052060000c0d8001c41b026414407030400e05c400407031080b142130b488840c481c101c0032401200b4903200750310103402000203d04858150034281090704082d8426241a50084401c40751200802e0003401d01901440d419a142110b0640c900c820b0f0009041840d101440c8031020000003011403010300280016600070950484140d207002c002901e000401c0c910b540521581c0003660000b583c0c1c0304c8007954001a145d03008220750340c500c048600b3742c855071400241007514250900052118100781010360070750980007040324903102c540550b03080c0210320340107902d0350142195a0040c07c0c40288002e1013441030610503641081c0b9501c2a0548008031140d19401401080c100306600e1705002d86500928207000841c940b0001c02c550000d0002ca03112011424000404200c41c400240c0c0c00402c003c58100041002c441d85445900d521440300c03400903a0148075218001c4190036a80806130740315104200c2210303078490409005001380034010000648a5070300c680f084007580345c0d40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 199435575 1250 199434325 199434341
    0x102160503090102060105100c020405040305071401051503030403051b0f1806030d0306030f110f061201030507090204180b060f070b0420010c0320070b121f0504021804 74
    0x1440c0c80b1901007000900e03281c01640314610401d03400c800c04000c00d802200c81c044542d0181d80115882e5250704041d252131180940081007425482c0c1d000304180c0041d806070b4050720b074108042c088008032904050f0340e40258040a460f40d0000c011003601c40800ca40012041d81d03014001c150202d40440c001100c003d1342107503210448652204004061406002444a10186003020041c040c01d640b9000ca20700031886005184291003541e094060340c0c0e0360080290350720000d160701d0365034032140c0c1322a911060038441105c1c0b0703110b00340010800c0042802039800b03a62a904014000d1840c51125502525955a07038981100c4200300b03244034a50410014020280100c200154034206450100c1002c81c00710200e510740071803001c2480e01c45c0c0c0c0c00106512080d402d45001d02c1402660510f2001302c56094100103400d00c100c0d103002520010904c05005000a0103c65010980d950100481c2d10520070ba45c5260003a0011020310840c40c00e940078007000c50350a000280c0c51120b10b40801c040715043c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 199436825 1250 199435575 199435583
    0xc01090b0106080a0606180509070c0b0a020c010b030a02030a030f09030203101d0723040b030604050106031703100b07030519110d02162c0f06100c050d11010216 71
    0x2031040015070130507405030303e008242c030b89031208075120208062800c1200303a006551040311440c011410741d0707105000d08503c07030780c00c110f00101c076003000e403c810002e502220090055509040b0031a44924000c90f00800150f00076016102c40902d0343e40448505950421040c10300110740d0011016031001c0240301c055032070b20003000804025046c001100d0803031181601d41c0c40c1c1c4c401c800500c03c10349000007600460068043c600600007a64002a01400d20b1119858161051008120911a0541043c402c8a00501c03405000010345040328070240701c01c40b85030100c0034202070104003400080004008040c003a150840c1403802d034044d038080c0d100082070f001c0c0c0000c032107015141300300304180000d20b403012140c0001c0000c8041e4207542c8051045d144101c2c1030304400c203090030a2000c0007c5030356004400d600340e050100c0c81d25000c0c1740c0c030f80001610013901440c4141c038007800090148000c0e10306190000010000c002c02d0700c0b411508140c6007400ca111a5400b4803810a030707c0c40403032025010b90300c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 199438075 1250 199436825 199436837
    0x23030c0f031809060109031b050d05060601090e04170721021b0604030515070309020a0306090c090507020c0d0503040812041d1303050702041e0209040c0801051003020c01090b0106 79
    0x10000b500c030345030348030214020300c41c54403a0706101e5a42c0e0003140b100d0131a5131003044140040c1d1064000d24014140d54003240d000281d8030440800c1040c08510544641c20980ba17060649440b60400c3c172011130b00326001840d00321451a032800d80c0006502a1041c0b900c200884425801d40c409410626101d24040c0c40140c0d001d002c9003801c11040402401c0c800d2070603640107081c1132564542541d180c4440e44c00d02074072080c03800030500c900d00c650005241150050003095a00f50340303190240060110250581c0d46000b2a000810180705500429008110903802003d4070b540344010040a0244c8120441d85071004000c0000c040c4024010100c107000140300b41900c891804540216200030104d03401030002850303041000421106c41600203450b01458209d0311070106101040081c06030260041d11040305a40c1c0080728030180c3c0040801d100151014003520f5545001658104800e000d0b00f82c0c09a00110341c01d602504c21703401780900340404000464180000d807204003080000fa000300c000106 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 199439325 1250 199438075 199438087
    0xb07110d0b070f08090a0204110706050f0a0e0a0b27010e010f050a02031b0705100f050712090503090d02060906040b12070207120b27010e070801060323030c0f03 71
    0x1e0060050451043c16090070749051618402d22a03d8009003900203101c0d56445041140c0a1100e0302941c80895208404014a040c080609041c85000300c0b941003096082601c030203140c0e80d01003040b12003a544a00b104201da2036130f0060000422074101c0c0041514100030784400354500900880084071810340000885c60300c10180403080d204010052280d20303004109109a4844091b03060344000496081e1680b150500d2402c24180001403240d01d48840c10150b00c0000580f10f41d00181c01480b840d100c5500040b0880301074000e4400d0044042c01c10307001803210781000d003420240400380c03e03c01892907142507a824002000340e0050b030050500d50002245840e1a20413008242d600700c1d40d01d00085c182c0901c2c10400a440c0c01038031030001d01540b24600461018080701e29070300b83d80800f241c51044e400400d202c0c55030091600882c0f8002c40e21600c60006000d2a041c0301d8242901e03040301515226003e141207043d2802d0f078070092010a84400c201c8007404400907c1508001c48034440a156141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 199440575 1250 199439325 199439327
    0x203031605071a0613050103080702010e01050c061e18060a0509150405030301060806030313090207140d020c0a090c08130309050303130513050c1909080d0507120903020a0b07110d0b07 81
    0xc42e07103805d002803680c9820300600108d40c4141c140c869030340d8240780c403064000000c00100e0b298021014000e000b4030030301d4140100c1d0b0201044c80c03441010040c0201d6690750394101d0000480c00c0401541410350000c4009c6045441c65400aa500ca0640740032902c5009018150740c00c000030499003603c0303c0e0008401030041e40c0c1d000349550b400210480040d801e000503142d42800d08000c1c0d21540c0c402c103070700286034001c2228452001411240b05001e42d5907040103c14040d494101d4004050703c24203a854000c02c904c940f0b07100300c42003035041faaa640b441760344482e490b01d11280340e014240e06110b030102d00018940d400f00010701340c440300c00603251817042c03903c41803110050600d0112801e4a051200700701c210703a5a40191604c070b4880c4100e8103880d40c1840d6095402e40702c290001d00c0280600107039400c5090b004401003408070302c0b8041507143e403d9118000c0341c815990340002548021502c9040041c041d80700080e091803402601050b040900500001c0c02e0001c0c0c0b180122000a00a000c20085d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 199441825 1250 199440575 199440589
    0x1050906060301060302060d0f0b0a0605180103051003150e0102031611120f07060912030c0e0a05030c150f031303020f011116171206150a0203031605071a06 69
    0x96042e0000d014440c110b40c0024010302400ca13081a4195450781d89884903e610313013003055031340d03006072030305240f951507440003000c0c0d41c0301c213410b220078100c151703460351255110b80324142c0704155003602111040d0960707482d1800201040c2031152029154600c40309151000e100841c0904d5858078001082166518090300b0301d80303010548403041d0000c0b01411050100d290845421340c04103241c0d0340c0d9445080c90000010b024a10002c0d00c2403102103058440141c0685c00100c400341b03282c503418820600b800400802041600549070140c01c8130200592908008000d022503085604115042084000c02c1030440e0304200c6416001f2007000c860007003031607014010380c0c8a000d01c0320028002c60f84d030424403500d6441900d2100f2828040b010046081c03007205205000842d40c00002c45580702440c120501030310b8000e450b00c2d40f190040300d00f035107804640b1000326a907040712034003c0d41c1140d0307032500304011a030189022070051120030003450740091082c18254009182040d108841070410000380541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 199443075 1250 199441825 199441831
    0x90b0a091506030518070e10080601120809011709060403090902091f09050a0314070e070210050402010c050a0f030e01030204060210020702030102120906162d02190501050906 77
    0xc41d1a0001e40707100090014012402e40d120b0b8100800e036a1550856050313101d004034071284050241c007401080c074003810322001d80588a0094841c41140d10b4114842c0c17118802e10580e10f01820031024400003c042c0e43c09400c00c1101414000c1e2854031a820000c000c01048483ca0b005402c0082040308064002104101601b0f586004605180c07400d13001c03c484502e030b40fa110140691030242200c426200b04074400c0942405000080038941e04d10b014900e09050403c000310b18002d00c1c0012482c00045107000f846005e0982c0100901c0d0040082080100000b13402a0f042003041209540800c80411001d131145d44a240801c52004090500520314040181c3c0c0034100742c010007041003195030008541e900c40001410060380c0e01c92501c0080c0c0203215178100301d1074850300070040101403c1f021540ba1b21030b070014400c248910b030314840202c40741e00302d80c2400740c1501c10341d40c42a28004100f52804600180e0345c012540d0000c54801c0b000d02141c52400102d034540e448a0400003902d1040c410150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 199444325 1250 199443075 199443089
    0x31c0c030c0813060f020f0d060b0f0d1e0c021c1103220503060403020a12090506030f04030c05030f040504110309060c28030c0e090f16020c0901090b0a 67
    0x3042a04800e03000b0042080a01901083c0541110030400d0007020f40c401e00142104810440d80e9850889541140781c0114910b4600f461500100003003000b041e10460700f29802ca280320510b00703000c1280e00c0c0700a001c074559811544c185101052140a5588211400303100340340c00600c040b640c199107841904160310805d404000b90b415003000d020078000309690300e141880c2081c43d501c00640940340e0054145502a584c14803401b4180024143c010860440a60183c4112050860028002c0c0c03040f4040d403152170741000d001c10000302404619900f041d04140309142c0030401d5040358480f41d03d1074021000e58000c0c4030340090308101520b00b80c4134140c80075010007203190840c07400390805901c07898003c0c00210452000142c00300b000c548980c000c0740005198042021401d00c0e08001001404242c18202c045010100140020324006201070301c1411000030505159481384220200d0648080c41c100035480358685070207490b40c54241c3c082c00381140d09400505603403601c1c02c01c14072160310341c0180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 199445575 1250 199444325 199444331
    0x21100315060e011503021611100305010b0a0c03020312011e0906080c10020a05030a093002011101090605041b05010503070219030504030614011703040b0405090703020c031c0c03 78
    0x21220050b244070741100e0301d0f000030161180710610290003a00c5046605c0f507403550710140010800991826080c407260003583c001100040b450380c1602102d80c01c1c0600d14000c1d205120008949102f02e6440408134031070300c1503a0400e00c0d81042040300c014203801c00000030000c41c0c1485900300b20b00318010003c002c441e60500183c1d14100b0820345074070001c03149501803a1040c0da0740d00030034002c0002c29102903000c01180d1307883d400d154008001400c46e00410102c0c0042c0d07000046070351120080e500100d08181610b120f210815030040d84c043e02c1503441d4240380c2d503c1d00305a40104500f803040920940c01502c03044c058000680605484045a41103507051003014414003015650009554103081c030801c046405ea01c000c0d0500307841c2406244c2c07000307080382e06000811a2044a1040641c122450b0342c4404008421f46a0929200d02035400b943c426103009210801240c64090999a04581c15003401850200c01c2d024286c190390048214078107200280b075646881003910701c40c071060307682c040c6010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 199446825 1250 199445575 199445579
    0x51201020909011a0c060109020d14070e01030504060e0a08040e090604031b020f370b120606040305070602060405061b040905041a0109090209180303010501052110031506 75
    0x5042140c041c02002c4403038002c182e1052100707016100b141d8810a200e8100c5503d50303912340d262000b031b50002110116032400c0c001420700c6015000055801380720742e0f84403600041c103042c00440051400610030b070f40880d01d070000703007840e410140104034080e80940344c45541c444c00d00c4842c071507040000c1d0109400703501840800c40860751010100606c0703d0f00c030400a58911503400090710040390404450f44c4050480c02d8240103042e200e4106510702544040c00ca0341d600302c0385401001c2c401601c07034296003100403c80400380f40000b5144562088005080a052036240d84407680380404a412400241e070200c001e00003800010084941d026408020814081200314603010b091b01442c421120941d031240c001c5010041c0f41155a1040442d0000301e040642e502e91a00015045241d02a400780e56a44041a500300529070402c01001141004610b035918181c01141c0a92141c01003010103244128998500044441101e0080b00c0c0c42d00382c91455421800c1c902c0c92130318000c5890115520704401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 199448075 1250 199446825 199446829
    0x705030303010501050c0c04020a0815040b060a18030f080307090e040302120904020d110a090504110412020303041703120c0909041106090d0609140613080922060512010209 76
    0x40781c0c1034680070f01c0c0090315003490010107490003001c490503e034460b0012440660056104003001d1040750031089070405400c134201031104a4407500c44030340d00018100000301e6a50300801141001700c02c000f441141c0560f0702d490303900c101050500201c0c1c145000000780190a54810620300240029542d40381c02d6083c5680c01030340d1060011922441420040b03818a10f41d55681d054520442ca111002e000142d000300782040503510105200002c2264007030b0116180c1403d10490751342c440600b100514203402c10254021003404110101d80c503101c104000f099500090112000340c118141c000d40e00c4844140001c0512000141000138140c4140001541956001e0700a03030087d070040d50340d80da924100380c0801c3c0c40b84680500d0907080700603560050100841e69200101c8503020b0b65680b140e0051840c141615448195400301d0442182c88000010039406001071201e024014103060142c91801ea5107200d03403d03800da514461640d01d44080100b802c05810725030350811041c00071454401e10b800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 199449325 1250 199448075 199448077
    0x218070503071214040c061101020f04033206040308060d0201020a030815060403030809010f05091c021009060509060108010507091e210303110307050405060304020f0a080a1407050303 81
    0x50780030001d4070400001034100f6640421301c0d40355807081d461114501410300d4802c000d010320a0b400000c90404242c08456010b00c2980d40c201c070080d508030b10302440c5880d856001036109401d10b4825155807000d4105150080300e4074050507503400a402189030506000e0a60100149614080d410303000c41e180050b0381c045510741603aa0f05040281d030766101c10501296170400b0044e600d403c414006004814140c100442620845c6428000e108008028007601c0503500192084c50882d4003000d0311070140d1001c4a0351010720081881110a1407541440b90801d450035039001b655466910403d00003066414404035014140101c001d1006041c050030090207034016104061180380c402aa80e800258491268802080c2c1c22403200f11251040c4000c60400958880c100c02080c41c05c8540030800010f80d041d030348141550348600d070402d45000e083c081c8a510040c0101da003c01a0311042c6203a41c1c03600045005402c071040240302041c5103151600c1740048114180c442c40d4045c480400499030000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 199450575 1250 199449325 199449331
    0xc19170133180e06011401092705040b010e060f0f0f0f0d1209060c0b0105040c0309050f0706110304050f010c050307050106080c0a0b1303140307140a0218070503 71
    0x1151030030990241ca007011601e412260890300500321400010540d4541503040401d001c0325000039500b0990303890800c0203508510304c8980b4040f4110b1031003000009001214070600002d5444c0304d018040007048501c1c110741e402c41d070440303501080400500682c829000801c1d0701003003e448070f070412030880b030009002503444a0301c144602c1c21001e5800b42c0e520b600c4614880400054920340081d0388910702002c69101c1203000f43c00050000c4030000c1e0709480382c50f51484150b00a445280c19908140078007000e402c001e0b021805058444112000051081002d004c0e40d800c0030011b03200c480e0a028000b042d0030f41c8405052411b070b005100c140140d9841c4405842c03200c50901384541501c41501c1d1050543c010290080d1040d480d1500c00a40c400e400714591500c11411100c03030520b03a0b110f036104140da004403240c0820400c420b8905000240030511a083e40407126000c0303c0c00d050559441d041105050805c0228076086245108118204010030711a06c1d82c403c040c1888520300101d000346070380001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 199451825 1250 199450575 199450631
    0x30406021e1608090120010c0e0108070f0503220507050f0103060b030f06030f0a050607090501030c0e0111010204050a0f1d0c160c031e02030f0712060e0c191701 71
    0x50400c4d451703020302005160600ca074088801381190414107503000f48448001079000c41c071504404a2158800e45046100d20b0981d210350340c152903482030841b040c2d0001840300440c07146070100b4111a0501d12891004503110b01d004001c528100300c14020b001d8101c0140e941490f0a00c20180407002d0058107899000300d0800781c07400281d40300c0002a1501f25610b00d0300340c203800b41003003100034018003245081c4611315035214600c00079660300c011000c441141061200003040901c9038443c543c030490060b44200c0b6450005130510b605d942c0081c2940e4400e504c030022079043c07920100403c0102c14440007046240c401c80c1a480e02c0d01c07001c4040c0074880c2e01d0038142c041e92001d810504000703040c101031000e107420402c0003d02401501d040000d42c42e80500c260306c241704981002d0326034140007031000d0a407035100060640500043e640c4101030310240004901902400d03101c0350703007902c8001c40140e2000c1400c11a030030b42440d292a0031180c40110440000c0799042501040c8680c0a50b441c0d0394a580344 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 199453075 1250 199451825 199451827
    0x3170118111209030706050601081519090e0304060206090a0c181e090510050601090510021e0a1a070206010512030702150307030c0c0b0609040c0803030406021e1608 73
    0x4a100c10550601c200d00d0031003810300780c107003d00080d890000050904039100e804200601c4e1281001910410310032100c160503007a1a9024010b1030408000d111800d20ba0000e5514030035441d40306905c299541d00151150070360001c5003c20403183d0420a16400c010314030013030702456150f522410350a4100303010306030345041e41190000c003807145540a032006e1440c4c0e8415103d01810310114030054001400241d4283c400c001c0394404008007441410b00a50058503260403107071400e0103004c02600701d003010a043d80a081881400c1629501c4550450f400800140c00364003030782d18102e41c1c04202d480106600040318003c10050035000070745641900c604a48420115001e02d40b158503521901314000d4102810f40404110178600d01c020f50b0080413162030030b000c0c01c80701180444a64200c09406468a401040800c1090801c2085103401c00e005144591a1306d8980400c24550380c400d0300c0840b00f040e40000c1000648684405003a44c1000341ca14503890403400600b21900f030f01c201d800c00341000078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 199454325 1250 199453075 199453091
    0x250e04060b0d080705010c080105060903070608070302120109090309060203070b0a0504060e010c08010509010504091a04020a2301030c0504050306150f041107110603060d0803100308120403170118 86
    0x611500d00c102e4160b40b01450664429142c60018040c048461207074001c19480c40006c1242c1c98400280c41c2c81140103401000454903040b01201d5442c8081c0c4403400345542080341544004110500c10b020300f156900124082007640360007040742c0c0203035016000b150014040500042c80b4480007a402c0188403102099030340f05da042040c010445000c85001a40c40d0035109001a90003581c0c5074101c8008495401e041c0c0c7e80c80303060106036205a10f00412011550302c3c0d01c0b140c1c0c084400043c1d0814009030100491070780701e501d6201c0100b83c28802090004d8030400840c010340c1d040c0035a8083c43d505150150629280001080d51010003a224002842e41605400702d50b071518141c081215500400a04c2103919a10269400e540b0400056402051001d4004501d08000044a0141c0005401c01c2c022840070745400f012074001038400840760041a00c000f02090603000900481000c180d0320311602d050a20380500758031404001c8811811030000100102130740071204d02040d00c012600815101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 199455575 1250 199454325 199454329
    0xd030504030c0b10230907030e120f0702030307260a1b032307050f010501050105031f05030601030b150a060906030e0c04020307050a09090b09061c05060702250e04060b 74
    0x4c031260022209108110444440d0403070140c6160381ca018144c0301c0303007038581b51010110159a003c0b00504540d82c0b0a80107628250601c500a04124201c5080c450604107154000fa0440d480b400c0140c80300000308030900716042c210066403690b002c4034008186401860480905121400000c0e111104010126841814040d4102e8050341022002da40e003001c010403d500305c127400201c000d540710312558500c2b00700328405100f5207050b2031050f11402d055961300202c03103080f04903180d002d151043d10080002215103003089940d02031886041e1400d0145804003a0010320041d0303465003840b508100c1000c02510783c0003c0c0d1141501c01c149070204444400d034605904d0b05488600c8107400c144004200b02d45580d00001800c2c80c0240ba030340e01694581d4032106031040c1c400382a200c5078803203591070100b401498008030300580e01c07140f1480c0c00c0743d0740c50f01d4540500300340c0c044a6190260300328840351080325011903030781240b90160409080c002c1c1d0034461344035201d800c0140014112592265a00745035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 199456825 1250 199455575 199455601
    0x10c08062d01030902030c1305010807050108040b06090405030706050c040e0c0a3e0c030f070f090c090902070b091c0203090f15160c0f05061909051504080d030504030c0b 75
    0x440015000e45e0480d50141c49230001008240b043c900e543c020104080340304d40c8030f00081806150403030050340e82600c41c081040900038010780200c41601c0100a80400150140981849800b00904a548480c640500041544801030482d8002c0504101c44000990880340e4040c8010302c44d03990700d1030700f0542d4042450002a4203444800b000c00702400900401000481030720428040c0e081d22402d01c0d1454500d5914283c07802401c0c0041c10b124401e1000141d2640600c5a03115249803080480f42d440c0c10500881e03104e44002d8407040c0c0d10004000c1940b00800c149044130040380c0300c4105230041c0d658029100c1c05480c2801d03208130dd00303d00e541d80b01d5482000c5c1e004664060000107071f640125082040300c02500c41821643c1d4070b5100ea00185101d1100c00340c0c8100c4d10003400d428545640d032109400010b010949003414070200180c08540da0b1107204015007080084480c80f540c41e4203000c480303880d010404201008140c2410100b20000b42c0c440940d64115500400501e1151106031010f07040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 199458075 1250 199456825 199456843
    0x110a03020a17061005100806120f06090111130b0d0623030d020304151407050f0d0e010f0c030f171303030501290a0302090312040e360f010c08062d0103090203 70
    0x18510031032b02202d4605001180940c0100164002080704014030b01d02251140200d00949a54101401e820020004032200a28805c00140000a040c2d0345441c0d0f08210b260225441d8a08101502c41246545c00c0800c844041d203c803a000031409d281ca0702e01ca4030449928450030320301700214212001045030643c0c00b075446850b4800180e170201d15040420079510f8900d841e40000041032070b102c003038695019a0105101030016690308299441580742502c40d08641500001000b07904140c80003c100f401c1030080c022655000d011140ca49030b8140102540c2c8180c01c96520b1902c2d440c2140034031610a1658111100703c5480c0e60b4030b54410340300560090003180d44103038040c0201540885000b0844004000355501720040d030f0850b40b5030140500d00c4083d040b080d1402844444030042200c91014075400f01d1300e00c40e80c200c2c0c030441c05890383d89003515144071003080850020028044249491014040d180404081e404000300a0a04070704081c0280841a418103980d00d03103000a5440922889207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 199459325 1250 199458075 199458109
    0x8060c130f0303170f070e09070216061206080102040807260105072d120f06050a0e0103060501060f1202031302060c07030b07031404110a03020a17061005100806 71
    0x40c100360b0700d09014010014650070406049655400112151384000c2014021980c81d5160703c003003038800b0140000c1850141034041544902450000c2d203408020018015068903510380c00b0f03098174004030f00107807012604054030300c0c0d006120034801e2944c001041012515545042251108017541440348651544107c1046500380010480d486410681c5419440e40140340c9064102c0c00b02d255010500c4103441400000ba02e2648240c216517564120040c0303820340440008815a44000203429484192f129140f10194880100240075051080a00500e41ca0811500e130034a50813009043d007003581e8a8041d010307404000314510f086040c8038040303115400340c241540d600d0740c540c01c15907030113040c4012a51500b09000180400740319000300914040b0038098100c42d0340301e40c0c6d901064916804245600584403203c00405030344d03031460090003004c00000c820085581d908425050803001841c0c200c068014a03030400207625046204210740703255152100281c0c903408002020b64100130f244078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 199460431 1106 199459325 199459349
    0x105130207080706052203030e060f07081b1308010e120f1c09020418061a010f080601020a080a0509030c0d0f02060c010e030301230a08060c13 63
    0x150004503001d2080080c0130f513a001b0303042280c06c00341e0690029403a0b01e854501d000303060140302d40013100080b2a46c91468488005803100c0030182c240040c01104800c050300725030865080d12200c1c0c0040300c904003166030f51040319001c1c1100e440e0803070311030040c203191aa04958840449603a44110140350742842d00c0d40410200720356040140240c2c0945603001e45005986500c41c80d82051810103a03030034008140d042420440d00004510503a85560911425490ba009449404424a01d02d4a002d003903039080e0040b414a990450003c0c940e03c00801c0782d00362550030202814080e0f60641c200c0700103000384010810203c0c8440d401502ca02c6104500b034001d03080420080c07041802c22000801e804c0e44149186242d0b84c000d1780685040100d199034000c60820740c1741d081c20b0800c0d0442d02e8508850030040c5082e143c3e000a0144803c8110005082c00d07021000e1820700c5c003d20041e00c4903 = true := by decide +kernel

theorem cover : BRFrame.Cov 199280575 199460431 := by
  have h0 := BRFrame.cov_init 199280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 199280575 ≤ n) (h2 : n < 199460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
