-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:52.446084+00:00
-- url     : https://prove2.me/submissions/28c28b0a-3593-4adf-bd8c-0d1783d61288

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 372841726 ≤ n < 373021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 372842976 1250 372841726 372841747
    0x7091403061608072618010e060a050a0603020901181503050d0521100806060301060b19051611040536030d0221061504180b09090109021005 62
    0x7000308401500f4889003002042c0d5050203054044a40011856050b010700802c00e21485c040c14143c0d002e51040d02160200c3c07120100600410703100c4110703100205500e44072204080000c1000400d1a824159681000300050f55900040d034028402e80032410316040522905200b00c9014180d61a07072a0515902000011000b2403290283c85007410483d07101d245115032681c0c40340d50009140b03550000c12041040c001113160020003510f221004540c41559180149070899809002d05000c2c88010f100014161121401c110b22913611403a003a4104003032405148900922100d048410851940204030b440c20207202d015401280d00540e00041c00380003078a100e07290710f4600b0512110381c1c1c0c5902c01542c0c0804000715409000862030465035148100028211001a9007c402200700b20b80e0200d83c0e00c3c50442d6680700a0008148003600d4a89040901d102c0c9100024031584021340700c010521440e5180d10069220740300040012450060031700c1044548081d00c4031110520a0522032030441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 372844226 1250 372842976 372843001
    0x519050102060c0c07092f3c0406080103051c0c0201051b0f070e010b0f0405010507061404060c0f17070c02010c05100b01023d020702090709140306 65
    0x94005403001d0b03070311113000c054142000d9003900304144103170608907058040800c845d00b03c0c020090404c102e01d98124a0300a500c19032141580c011000c0c0a8100c00c50b604005000c0445042d000e03d400000864030400f11046413500280d1003d00880c07245001001807100a1100080914411101c00210710000b00c01502c0c030005002d01904211b4040340e440d002c040c492007658003694035502120f408a014402040e076441050094001408010000051040507801a2141903010b4901103080c142040011111a0001c5400766085901e40d600c41c1070146061030224000c0d8000e810100311450340b5100504401e1040b01d4140411881060544801e40c100f03200e079400950b289010340d104540f90004a508041c0301b2000741c424003c5c80100d000f00b184c2c0c1d5000300d4510b0001e8081c0c0d0301c9441480800d0a00615031084161510140c005240152002c20680b2403900101c1500504021080d008105101000c990600101c3c00100c8180134a12607110300f412811411801400d8916010504012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 372845476 1250 372844226 372844231
    0x20f0604080d0e0a121205090601030605190207030504060906050703120c02100e0f0111041206050a1d060604060f1d150303070b15010504031208040507050d0804051905010206 77
    0x4600128507401600e000350064054007036220304481d484d5030503044c48015075150715100300128a0307903184250b49480e54050355124044142c0038003d56031030b607220359014110007801c00184c90300d00d1020044c102c460344041d08020f4041c4d503955071240c1c14880040d052000c03c4d040141840018040b10000070b034814032200542c0f01c15240401c1c0c0e4144000e0503460004200c0e08003118a04104010103a09800540c60080e804c52000902c02c030030961440502e98800c40c080c4001c4035410541201c08a2056000250010444d602c005031086d880083c1e92039010140c40080101e0300010140922481c050148202405030700c6550700380030b880c040210500b825540e00c0782c0d9104102c3e20000e41141400003036425428805402d49a641e1041e19001e22201400c40324402c1c6940760018580440d44650700313035000d0781ea00030301c48821441011030640e101840100103c1e0f491060100102d11038552001d58102e070b030300c504211074a0704e090034100650404c1441e4054480305481d0300800003030b81d0000382c458 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 372846726 1250 372845476 372845483
    0x14152e050927030703050c010b010306052805090c070501050105010e030a030c0203160b070c0605270a031704240504030213020f0a1d010306081b0111060106031b020f0604 75
    0x4810088440e07442c245a9142001101d2070b020208032a0180b40c2c005d402800d084c2d80250081045805190054048440e64091190000001f88100c0a200300d4502115809602d070700c0c83c0c280315992440007901e40c5400311a100744040b00030030b0f5041044400d010362400f41c030090910490720300036080800e41d1070814080c0603003080200340c0c2e210190340303003805150418021002410041c6172994141d80455100840c11504010320303c80000d03001e841481640e04c4013005154035550001840c00703000254110501007580101244400000a034041e0f8031001d039045000241a00e441c40c142c030310101c55402002d190500544503814010407603002d0200c07801d80f130741212081c240c580380b400c01307100034000c1da0900850024006807452025400c1000c3d9681140d03801132801049404800440076500f841c450010103601401d4500500c010f0120403040012061411454010740402818500f1000b0391010700403907a00c00d1824499400301000d0301014515000801800800c181b00940c1d6100092015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 372847976 1250 372846726 372846751
    0x806060c03190309030206063c1203040e0903070b0c07050c190f0b040b041716060c2f04020f090405010914060108100504051b070501270201090314152e0509 69
    0x10f0444c0d500c5a1030340c144d250809801100880b152280064be280e01c80c0c0610110301b00e4940005000203c00011125855406003030344549480300d061041154000103011251030203004401c0c1441e0f220b11020340030010122138a087d40034030306100581d8208082e004003da4100400c024040b054032441103c00302c804460300a403400300b02c0040d060600c250341860400c1000300607400100154000c4030004200d020300c03078061090014248200541c400d1109258580380c02d41d155400034034255024003c501c004040e03151402c0b101d9000070f0700301d5000f40c00182034155138101c068103680001d001d144d8020310a00301401c0038204201850003502d00740c46030f01c0c400c64031071000440f4850110700651321111689403650700e40041b4580180600a02c2c40f40001409901040c01c400d19981400c040e002a0181c481d00f065500310f480342c03d00700030642443c14036442140ca40d00c1280d141c401009100349903400c0b460600103004540482105007a800d00164074000342c01c1480240e0310f9601d119000b030048540b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 372849226 1250 372847976 372848059
    0xc0304020414100927030332040501230a0905030708070b07020c03010b0d1104060509070807180e01120318061808010603030806060c0319030903020606 67
    0x1006020407074440b542c6400b140382403045400749800d0550994400f0341d8140034004138950f00c61031a2108000600f84280840c01c80b0700480c1c0a54480484c0e006050041002180340c0d007008107158511b80c415a5001820381c00700000d01c1400e101c0c109100c11111508414182c000810810310400540b01c0000c15544a440c4c0e001c001c0f040080725009548686080e446001504000d8a00101124204054080c40c40301038a2444d040c803c21403071102c0144220750610550300d5480143c0740320000150002d1f81ea520228195940c07011aa11602003a0340305c103094034041900400300c0d010b03403c104010b40c0a0718414015030352032683c01d5054403c011080c06201801d4103080701c0c07446022a624001ca2484503003c00c0055000c603400035141c1021500301d0a00d95541e00c1c0d282280d01500c0301900003400303031003c00c5151401070b000b002a4144030b000c03030342030069002c1601a0700003144000008a030b59105c01108054061011035404982204c850900000d100700005035400009041160b07441040c3e00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 372850476 1250 372849226 372849229
    0x80f0f1516030e1f0c020a0206030a020904021303050319030509061902071a10080615040e0a05030c0106050114070b07030e150108060702070e0118090c1809020f180c030402 76
    0x3040e0308090383c0d421115010724041c020b540c0f1800c1207a59050070340c00d113080e0b000020f000049060450b03501406035442c5543e0801c05c08003d40055803071030f40c1b194080141015000c61150805c020318000c1005c1c640e01c0e07101c1c0c50003500c601c0a100d42c03101414107000c10800c0240700072684c80c1d446188800d4600d41031070031005c3c55000f4400e004005048030f5418031840004803c2d4500740e44035411101c86100f0756901c0d600c000e0317035884007142c1078668904010604012800d0503080f441d0320f000042e003101c0314071040d59100d60554004141964841e951500104100d40e804401c4881806018200300d242c4207054031110f499010042030600cd040d240c0403074211100b0f00300400950301604845076070081d40c50b0f980c0c058440d2001e880c40320041c80341c2c0d003000c00c3e00190800118125000701d030f1007810109402440001514030041c0c182c2d142940b40c080000d14005950243d05001d080c03600c00608002e070340c81004507401c2d0364030708240580b00c105184c1c150529548045500103400901d459141e644034030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 372851726 1250 372850476 372850481
    0x303050a09020d050601080c030f0c04090f0213020d0515010f0309170c010902090702010209100e030304360b0123090d030c0b060405070e10020f0304080f0f151603 72
    0xa0009410450f6600118144030020580a059400f032030160b030b000c0302c0c03402e081680e66480d14606080c6a008091048040e00e0150312005220348038458411050402d034000607480b220107441c00c41060b4000500035598840b5208050f4090485511041a00045000201402c0c0390a0580052686c0c561050081c0200d078050010803138156890302c3e9452405040c0b042c040c0c9040601240108100804140c44d41d0040c0255000442c016065655500d4558000c03603c01d12050010794042c00100404600c0c4140c0440ca2004048030034810f080354000c0c00042141700114201d12100c140c070340010405540ea0261040e13958600c0700858004019042e10341c41e5103849541e071030755480701820008004054107d208555182e00452013040303155101c071705100c01e0707800480340640094100524001c070f9280400c039402c01d20050f803040740c00c0345401c0d580c0e140c40c43c0e120740c110034215400880003100d18203003040300e15540342d00e01c005005c03e80e500440f0303488051070251120030016560318002e40400c1c400e5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 372852976 1250 372851726 372851741
    0x1501060915031b050a18050627030304090c12050906010611010b030712020a080604170a020a050a0309180b030a020123030708010302150a020637020d0e0601120303050a 74
    0x40b8003c0308040079894003412a0707101c80100c00c01701d180c01100e01e082c00c1c0c2d5024024103c3d08080c214a1038020500300c0054101c1c60513a4050030351084084a64068804202410181c141941c3c0000c20110080000d040007c0c41c04000524500b00010400f4403400821150304503840c5003400142d21010381e0f0810301501c0d010520319018414120f002075071195050203c85258000c1d509990902c0d142c018070341c0c80d04011500a45165a1011021200c0090340002c2070000c0080c41510b00784070a680e681420150840000d03000070b15641014840e0200480200ca200589458204100170040d00425110300d80e10704060306002d0003c013a00c1070f80f0b41c45007140c90480b6004c42010758a01e00504040d000720402c3c0420f138010385001030160951440356089580514141c0c00400755a511501035244140b15908070060f0042507440715000b00e04401c03d0072040c8201200301503124500c5a5080341242c51a400a2005a0280340100003c0310201c0b40460826003628011072595030f014203410191164 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 372854226 1250 372852976 372853001
    0x5130b061c050c0a0b2110030f061407030b0a14121624121d030f071a0610120212090a02181519030b0705070302150106091503 56
    0x105042041001000f284007a00d05034100c800c2e8040689821008100d8001c801140c8528030560a02c0000d10151224166001c00d01c40e000c1203510781c403940c0d40d00090008840860302c841c1c459420036004007003084129844003d0b03141c1084094903241c0010950107440c828440c02030b6144000d80c91b1900c1d28440600d000d94140b0891f00d885092000341c2900a04900c03629481980741d400403000c1c2002c1c02900106101980d0351400d148200381201401040c007a445000050f0701141e150ba13642e903003030002e0300f810170301d4519164403810507051a0056002c02c49072a00101d54140400400e0385d140084408465014a083d4040007a1a1499402442448000b266021146041114101000901c080c00300e10035a18100240540030503d2050002507418806110154080c05032601780503240d02400714000d140b4001341652a1034000f40f01c942070700c0c100005180002c0c003900380741e010002205940f101501c400070561520a0040c403030203072400b501c001c00c1c001745040c0038281d100382c1161029428 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 372855476 1250 372854226 372854269
    0x2040b0907021501080d0f031d160e010506031608090322061101060e0105011d1c0b0705040803070201050c0109150e0d0206010308040605131701020304060b0405130b06 74
    0x78500d01c007030b40d110f84851418035207070518400480c070000081350703c01440c2c099031509100e815101005070050441902a0b500101114401c066600002c01c81d80407021160135030005100e05089404042c200141c010303d0141e1020402e00035588100d01c07210281c00901d10303246680741c0b5480a001c0c19442003551410b6060b4603100f8401d1a6400c00082c1f4080760483d840b0949400081d40216083c0c030910301c914001e150450340104019401880e00e0010301c0f51009082c2d10300454240003543c00600c0d8a803410401e50030300401010004c0c240003298104565041c480d082c145400d078803555910400c04001d042000100e40025103804c250020213089510000b020550160b440c3e580000b0720480422400d144034080d586030040d070011440c503040c1c1e42c0084440d8a440c0c18000c00799143d5200303822680d0b600000c0600025240b04120980e90000d003224000740e1b50b420641000f6050f190780b281c10f94801c903d01018030580482e640c20a0750043d41c0004803062550341d0000081003080e20092175240c00a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 372856726 1250 372855476 372855481
    0x6031b0c0706020d1101140402120a0506131a0405030708090a03060c020109110a0b0f0f09060a020709050f0f060d080d09080c07060f051b032109010627050402040b09 73
    0x603000304207040820394071780d94480100b0510035000d00b691800c240405da15007598000c1005030500000302100c50748640c0c00c0361104030b80d5943d11460082c00300d50440d000103848900200300f102c054040c15003510a40d016540038202034032911703168410600c006101e480000f5a009403603c0c1d0910400085030001c1c400c018171f001d0104040e011300745101044403140c420700c40101603860700916040070303105190304090915441d282040c00b21f85c031009103030103881000d2002a0703582d9145002461941216030141100500d03080c1410117403100541840340c4003a1000c1080060101212900da0020080303c1d0341d8040c141e1418801d0b400d1080503002495581005d0740c40060110000c01003488078043c0c0104ca580c02d541e5541210280c103a90b00c11400104104040d28030400a10b450308078031040314060f6407501d40000301c3e2050a09001a5040480d001541040424142840381600401b0105c07425400d403043e024401c80d150194100c02d0250307545e1400450295103859205400d800d0024001500300e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 372857976 1250 372856726 372856739
    0x6161b150509011e0e070515390106140d0212190c050a03110907030e03030406061403210a170f010e0109180314120c0306011d06031b0c07 61
    0xc25040d0104101c0d07400b442c4101c141c4600350b100d030034a105d9031036000d0420507041c802000603003c0001d80e40f40c0030103c02e10030b10704000000a103c040070264295204903140184500b0303a240105588404602d9240c1401008090014100d000301103508582e410801d040e1480000c1f1140500c075500a9540302c0c1080c603145040b2908041c41c0d266004100341480c10b9696070800c548621180001841c0c41c0407010038070442d040c0710002c0c50b0031940e1070401080c2100c45002851a5400880d003e035640c9031240c00810640c240140c101c1c811510940c042c2c012841c001c00329542007076a2151240501500286020080e0f05c25002c1d40603071160040c4401440c2821b109400d00341c8406e008841c0381d000120700009180c1003501c1030010024201507815142c2c0d41d40e0302d050b210400300d036641c00c180e00d208110140000300d60f02e083c24071802c00801030340c0e1a81850030004110203901d90800a00c41c024a0302e80105a44403c00ea0754400340e4200c030100d901c5007120030440c01d401407016624561060750000b03e40c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 372859226 1250 372857976 372857981
    0xf010c0305060102150103050705040b21011e380402040b0415050a1704030e10020604030f020a08071704050a060903050c040605130506061b06010806161b15050901 72
    0xb032109a0856900a0f0200c0244602031400e1100401c240c3c0f00075000c10043c105600410b82c4110010f1030b010403240d1081070009040741042d0700e8920380e551381d06460651030320420b4044c24403c140c081044082d0b0100c0c15401007205801380e82c040d0411a0008500c08140c0006114840c0c034050010746d2641da41d131a4550310758202e801950000d48041800381c00051042c02540c040403c1903aa520100c00520096903008201070800e50070800c4081c001121070301c2e0240c20f0b91481d64268010a541d1500d030074020806040500c034174007150000001e100100b00b44030147c42c03944e600118403d046e64803e90343c100d842d1085a11003a003003c1e00c2c42c400101c1c150000d01c8281200c1c02070003911207004c0b0050820045072024003550350f002c44440300e0303010340303400c11b0303000b40d611007006440945005501c00c01c10301940c8000c0319051455101500510240c0010322405810982e203010502403003c244a0240c81c07103034a110010a040b17915840701d0184074402001e581e1907070f5014810411400c081d2125800f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 372860476 1250 372859226 372859231
    0x120c11030a0b01050916051603231c020c0a020126160207050d0f0303090201120f0207020a0905091507090308070b010501030b1207050d02010908121e0721020f010c0305 74
    0x100300802000a0003101d0f0454081c9044c6e4031594071a4607095034900c428500c84041001035080202e403071400920140d501e5405500080804115a01d40302045050342e02070810603d0040c502d401440f0343c2c4003405001070001009942403e080b0241548041c03506400200d101c1d0000e40d5015140034030441d100e180a82d64000c8615601342d54225448a080c4509044003413001001c0d2150404502e01003803084e440150014030515068107c1c07070038a030340303101980e40c2080003804540c2d0004e0380004610704160504010b1520075024000c070701d860003da940712a07404111407080b03005000090030541c41080e03500b001e194000b040303135111006401c11085c0c2d60824000c1602084c41c2c0f0301848000d2410a40e158007200c002c2c0c00600165052100b4441ca100a2100403414410807010100d0908000c0c0041080380d0006600217442d55040c5164141c15498070101c09803404041103802d003c9850007402d0004001040b0403038154036450350049260080c0141c0b51080d5519000340020001d0b80360b00400e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 372861726 1250 372860476 372860479
    0x5041a0a06050108010b1c0630080301140109030506090601052b030f02100207060b0f01090b03062103070f0c08030c1f02090d1203060e04120c11030a0b0105 69
    0x28a80d480c462604100c8001e405580e000c140900010010903c0b010010700000035400411040d600ca100000d4003074030340c242c01c80140c4110a005001c98480c1d1340004086446292541500c41181c070b80b104011880180107000100c525004800d00c1070f402802800011a4801c00b1141d01d450540110340e1980001c2c004c2c148030743c00d240c1028818010000c10407556042c4030f15450000103043d0340a9801d10381e01c03036004080d401400c070507200a8100384003511901c1d02402000c10b101d0721440420440c3c040000865062001c04034041c4010660340c400d81c0c2d0700030000d8400e5142c140000900d0003446055100000c1288400039040c0c042100940c4c03580c0400788101703e40c00700d081d00d43c440c0a490703029400380d08420b503001000700f440380c0300c1e1a00f07510407030280c5603001860304401401080d1150701000054455422481c0d802031081d0741841a0740081c60b00c200d2810507418184d40707084000300200a9a42044954500c42084c03040da0a10340d10f491400404480d00c085083c98201580c040901c07070700d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 372862976 1250 372861726 372861773
    0xa03020c0105070c031b05010b03030a090e09071a0d1107050d0207081f0b060705070f0f05101209020118080f0c0d0b0f04050109080406030b04150b040b0c0f010504 72
    0x604507900a40402c0f00417541a192801d80c00b900b42c8111a0481442000346c9241d03480788202803050701d0034001010159400c2e0350303070100642032401030071003540050280c104a5101e40000c0184003201e407a85410241c0e24044075070342c0c1490480003800303003581c114002250580042c0750b0041000004040300342103881e03000d5401542c0e80d907603407603202e0100781c00da12820000f41a0b1080a02034991048045220080c540f41c100407a90302c0c3ca40c0b4082179900440044803491105119030380740820454014501111000750000c41d22900601b546200103004d03000c03548a201c4a004c682c090540b40c820007881c520407240f017650b680015035442082510a4070070703004104000501d0304040440f06580c80d0015485c803002d031940e034003a0564420040056038607550300d1040800040307001006000034009940c020800303c104030100821980551420f01e402104007104002035044442601c023124000c0040d44d44800c00320b500641480301124040200c1e500c1c0c030b03042104009203200072001a10701a03550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 372864226 1250 372862976 372862981
    0x3120a0e0604120b16140706060e0f10080c060409020d02091005041d01030515181c0e180a111227030a14030604090203060907060f0e0604050d060b060a03020c0105 72
    0x1800080030798140e9000149502400403043d001c0304010487c051180700f000491955414041e500c0741e03030642d0780800d48103115042c404482411381c8107401414a110182c08a084001c00040007481036200b400303002ca80100d4440403020040d4152040508003814002e54011125001041a0320030701440b064031103800800e031821900c403c420360580e9800740060003520701e050b0098120f1302004000c0c0341c0d0820400c450110036101400752080100207042c00c18412030103520007031307c402c58401c0c0d054060f420f1154809001100c84a0050700103900c07200001d149002070b2070759220b6108188503d041d0500c220180282d4038011045c80c50203243c1c80080041e511141c01100340c69201d840b0403d000540e0341505403520742c43d000000c42d00140001c0c0001000741c400e901003811b00c1400c80d02c05000350014002001040c0d0407000b161040d08803450114001c00d5a580000c4090065000d514000c0c00b81079902e804100c090b9001c0401c00c0001000e4607241e03841c0210007406948011200b00c415401d2501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 372865476 1250 372864226 372864241
    0x4060f11072006041a070c0509130b06121b1504060921060903020c03061005010926010e06100519051c0206030a09030e0a030203120a0e0604120b 64
    0x15604526404456a508a8610610402e410ba00d0141140d80032004020000d8561405800350f01401c40503800f0079141c40b400d0130088070b0075425030305c807a0003034022004219284400c04403100200f50310031400c0410344c4484001c1060f07405600c4de00000b0348940c400c1ca00008480f0300355903030246c00499218860084a9961400318087c912400c40031076040c0000344110074403032081e088020807880200c0b0100182c3c0d228a0190b032100da03002e60150b00f06071956496414184003130707503100c09c441000f041c50030316100000f00054094450800c55142009210481d04401c6081d6038002c2a408020300808003045e41c403070345070303501650215504038840c140042e07203040c8000000755449072a40c0c000104c0b8504030a0052314291000304040245d400c0340e01500590314140518040d001c2c8280001d0f00905514018001040c1c0d018030900c55004803208000507600090b03100001c40b0004100f03074407070310380e1401a6202c4d080d042031141d01c020301040125044282d5200a000280600881c5441c0e444541 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 372866726 1250 372865476 372865511
    0x209060f06070314070203030403030e0102010f09050d03020903010e07060e0a1205060705030601030b09090705010311120105100207091103190c140a0c1a0603010c080f070e040902060304060f 84
    0x10352054120800703016000c0840d00400b00a44441068041e0503e40320750740c4e000030300b541c2c420b40088001c500002d01c11113055909101e03002070031041074020041259141c40d110b99408101010004241e00061801e0142d202074020501204004003121038803600c07641e0140c2013900280d0080d000702440b04001683c2d40c600b10a4019940c0c12001410301034850680489041d071000781b0380e505040d2140c01e103401075115900c90718810b04040f800340c441e540c10507000406070b03141e4040070b4400748000c1c040c0040741800c103105181107a00880e0000c00c07030a0f1030f81c4140d0402400354490039000b0314104000c0b4102901c1001540f1496101c08820030050401038560100c0300508042c01c005900122074071140b034000c40c000c0c0756048640c02c01c001d85940301c4d600e405600d425510261503040186052290a040034000d420490000381009111480c11510005185600270410002c00c1000c0c82032426035140e07a40400c100c907030054031196403864542081c0020f8115074404102e124174181000c0184c14129 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 372867976 1250 372866726 372866749
    0x150310022d070212031222021002060105011d010e04020a090e090601050139081306031a0105040e04061802040e03030619050a0513020d02210a0203010e0414150a09020906 75
    0x101603a07040747c4402c031118811500501c1d010024910160302640940e50b050002e1200d10040d5006040540c1050001029058042c01c05021695400c060440a0b0b800000c443c041e89000d0303c0050721010901400c541c02d211607405800340c05103090603c62080d001040302c034143d84e400e89804c1c071869401008003c40880700c3c1600401c0888950350540352604622030f40c48914000c000c0c26040c11464a811030420b4210340c8080046613551a4111814030441c0700c07600c0840c001d08020b030416191144068040c0c20050000b08810368031004400001c40305503510540540241c801c101c24803001101c2030356540140e51991068800c001d100d205068175404041c162400034040f054018907003420b108230700030f940020013180e5409000c120b100100900c00740260076092824202a00b15808440950700c0000d000500400c1c0104010b000c015010100c5030741140d4014110744142917a440400d080c00306507025512541181020b00080d06a1500122900350086900d00301036102c60040050405c0b10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 372869226 1250 372867976 372867997
    0x803070614012610050a1401091407050f0c01320c0f0703020a0215032706060d030318030801170609060411011809050a05150310022d07021203 63
    0x15034900e883c0c01040c0c03400d00307260fa0203060032160380b104c0c081c0d1038600b40c6000300c41c400800d40e40c6600c41c2ca515224049410f0041c581c025082104401041350710b001940c0080c4280b0501100144143c0003643d02c4088440081000380204060030701c18806101002c4982d0078107078001102c3c180481e020f43c02c00180d60040603103d5032289010340030594905540c111410940650241c49213400150b00c0d005070560700c241c10900003035075920b0200301c0031401c41c0295140414520417210400c2024038000703800c5030001c00c1151401030060b030a1408501130314045180405171118220000d0806030881c5c005816103540d00420300740f481c210304041d42d94103011a001909640240040707408190201d80b4074001c00300c1803502c0341081904c0201c00312030b410554090b0548a5a82d8100b140e00c03050380c41416000821401403d6400c04d02d100003a50303400000c0f40c2c503480300c0e500183c1403800c1242e14400c484448030301002022030780510305410840340c1000c01e082c1d004486030341951031807000200455025081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 372870476 1250 372869226 372869249
    0x801090209091603110c0d0813031b3306082e0e0a03120606090302101d03010e011a06030c0711011209060203040512040617060a0f080307061401 64
    0x103507500e242c03580c4003203c0060000d15a544e0516112011030400801800c40040001e21140522a10040402c4002000c0082d010702400d28000001da06c9960440011441000f00f501900e5904000080c881007009140c1d460403525405070148100c0302c000c0c0051040108100071031390366000e1070307500d03402100042d4090700c1c044c036608540d0350351070f980440d4032805420000851040d004002031402150b405c0c03e030007241441e1081c5045448074051311029040078a0705c1c101d1907246501140c00400251386c99001c1c08032a803811f0440c070750035000309080d03140c1c018020b0250804160105000b080800d0614030381d07006907441c51103070f810540c3c102c2c0e000351204d070310841c603103100380e122500030841c00c25140d41080380e6041c40442c8248180180c00c015170295100680e6410b041c90424902140b1750301040f90384909000c1000380b00c4e089640c000382101036100c0c00115642e000700081d08094030b904400c940002100010851040000180c60861703c521007c200302d0483d0044090b4940c002d210f014403122 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 372871726 1250 372870476 372870481
    0x1092a05060d06090203010e1816050409031107062d0813080418021207020a02010e190506040b04060f05090609010c1a04200402071211030708030a0b01080109020909 73
    0x620400601a900601100080650300d60310444c01303a0348280c0c440301c2004440000e1014210b4120344129014615900510310300c08a48104030907010944181d80c4600d070344e108440207050141c0406440c001d084000d842c03410b600c419014084c510341e81e084100c8454564540e40d50311510f07a128100302259500e40c00010359902b003610f45100d111800484d945c0034148400100c141d04803000039041c4815600240c1c8820100c50545140310b402072138030007150b1120503080d0250740c024681e580594025541404a40b0600d400241c01090b0b03584070721f400a50004001490b8103400c0050016608203580303001410409140031200c80c0208805107501c090b04010403280c40d805840c242006505c51600b82d0380c0504d04848812071003008980542d001440d01c1c401411855030080c100403c0700d0300326030071030900d011600c6940c1214401501d074414442c4110f400d17040054100191002503034040c0318a6507a2414018000241002c056a01d012807041d900104400d0183d00980d003c040e4090306080359076 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 372872976 1250 372871726 372871729
    0xb0414010e04050a1e020f0303031504240308030f06010f08070807090909030c0309050103060b0414150a0908011503030f0315120803060310021e1e03040501092a05 72
    0x81c1000303082100c86110740740c80b0300001150a12081480140c0103109400d225050040c003108031165104148a41c100700100316250f45412074213281200305031000103002d10303d0b006500e055201d2510008076034958403000020042d014005500c60000c0c1d04002d10161282001510240018003101022840480000b107a40d8071071a070b9650310400d140750490403141e9a605810072154000001d41c0010380302c0414605064004460030002c01081c60100300c1e039490504420028021030080351180001c0101d902400e556030b04401c2640112808515a0740308501070280ca00307241481251195401c3c0f80f805440c0070104001141240e8040c8c5800d1008a14400218010078103114070241103c03503441c0204203503018024501450740300380301d40342c0d403420818201807504906a8640c0b464500400c0000b500701c010807102d054411690f1280303611080c1207844200f540e081044c2e0300380d0451011041100b80901500001c4030640641c408428000c244034003e40469000e4001c20115807130040d0070000e0313 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 372874226 1250 372872976 372872999
    0x1060b0a030209010c1403130b040b18040209030706180801051e100b031305120306030717030d23071d010e010507020402070c08101b030914010e0d030b041401 70
    0x1400f0514194120380746a589052034040041e100144544c400306d090450b0f50002040107020300f0302d1810a9080034a800e01c1032000d03110317816000a0415000e0741800c03081e142d580668031002d10003801c1c4c803005500c0d440001e05022400c0080304104c030590303000052488043c4951800784000814074982050264100a0b50b408060402c8040d02803c81e400128007031700901541c0200b10380030510000c044c1500380780d887c00380002e005000052003002840312550380083e001d0300b00c03500940440d60b200702c60031342c04e800e50040502c45042e041c101504006d2102030704040ca8414084100307201c90546032043c0c103ca16240703041c42e84002e00e00024000704107601400c550350610105240292a004055022800b641c10030401281c10142c8680c0034000e00605010002601c0c1d0144010400e944050581001845040040d0001d1503591064007091140401c031040d0700070300300c9000b4000e00c907030f10402c076907540ca8000c9520000b81c6060300d12101850540079080c1c00e41500241d44c0080c8e401d090300c8642c7c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 372875476 1250 372874226 372874237
    0x10501081302090a150806060916140a020a021002030703170c090d0c090e0f100506010c02041b090b07020a0302120307120801141818120f0310050301060b0a0302 71
    0x18000d080800500060b074441401e1440351042d0031000c01c040d01c1c0c1100303440348690706800c142031b16000701d0300300011030f01c0c0e00d12203035801030701d100440ca0340320482c8505440103202c030b146201c0d9a080000d6030881c0550002040d001143c403c3e0341285c51b0b0420200708a131030b030241c0380d001000204240c8082030103540103e01c05420041030940e05152403140b40014440000304035080b02d800d050301c1403c01c48204140700740484422014064088070340ca40c03070500e454800d0102c002100e551b50302c01042891f446000d400d4900c60303018004100c003c280c210030340340c40540c0405480000e00100c601045180003407040c0e41d02c2950240480c6101d81c1194200007507046e12280722452403000b40110408a619103c0c60000000b854039240080c1d4140100182c0030f806001d070300e600a41740c11200c0c000c0d10b002c003c92241d100d16003051030000035901e0b02081e405c01c01e5218100980e0040410091652400344c0000d600403046156501c0402d039441040c182651f480e03204158221105101280909001e03400400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 372876726 1250 372875476 372875491
    0x1002010f060e090c04051303030504110a12050d0504051305060f090f0907140a090c14041706011205032205130506041a0916030609020c012405060301050108 69
    0x215040500010422280c1c140d2007082c111256900707002114078148031a008225040d18248128030b07200d0802e60700210418801010103030742d40001000d00123502504108100010f011143e8603545001c030b1013004040b0102551075020740006084581c0c0100203c40442d0800f800300c809050940001c20014040140f4081c1c105c49055192042030360f50004042c4a001c9445165190742003c1190b075207881029084a002c3e10303446a0600256074802c0c0030101192110714000c511081d40070b800312030b0071601d00c00300c042c412400704000c910b6072a94000c0300d02c0004030364110385507aaa0380058146a210301c14004c4c1c444d410420041410a10b01e8611000d00d800684000d4250b41d0b64601190208110841601d01c0790f94910900901745070501591000f4140703141328640d00c5048030000381d990340018020740c2545080386a004006400317074100380e0050940000464540020250503806400380c61864200036541c1c80e101487c80126400d5181601e0000d03041c0e0741180c0c00c003070054503640720240000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 372877976 1250 372876726 372876731
    0x215040c12051c170702071d0a0905060a0c110610060503180321060906030d050c010b06030f0601090f0f0501030f06050904030c0b01050d11090604020c0a0f020108010b0a0e100201 79
    0x100f0249003e0314400c10354075540e60b0741ca407480c08050100310042018110310215081000100203802a02ca100c03412284d5217040c545003912740e9030180b8010000604002d00e1030091004120480f49254442c24420074151140d40c501070603154803d0300e942c1e08544564030101c0b09423050141520620140d81d0104220111540503106a2134440c0355070484501c6c1c84c000004510226504402105415040b02094400f0780c100c0c00c2280000ea15940c001c045082003010120784403500403825040700c84030650181c8400d60343e090010841030700d42d608031001400702c1c903490000990703400e020308243d0450340c0040c1000130b064144030046025203860454003190a4440304042080c0d40c81984040c011031194a60146240580c5048440440705034441403180e803000b10b080c1c002c140c5020492000301822138152406654080000d4001d02800c44008850f02c02c3c40d20140401520048016500c4d000742c84180c2c01e40c3c2c1e501444c5002c0c0c03040910030400180300405110660070186020110345c501030001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 372879226 1250 372877976 372877993
    0x7060e030301030506070212041d090705130e01050c090d061107020a080d18050a0b2d03090f0102071109040204060b0c010605120109080a140405060a0305070215040c1205 75
    0x180c03441e002038006071002e8101a007441000d640402007071340d000050a4200d801c02d80b8000401c0c1305000026100003954050100042d0104000e210a90207031400800100007200f59102040041c483c1e0300c0344294661801c404145407458103019200b82070380040c00049003225030390b5010040e00c0001c520007881c410a010f03203001a0b4900008002401c1224010702346d21254aa0042693707142e0031880070940f80c0e40e48284500c0e2030310305040041d641c0d81011035541d00002c507200c140c1e11515046d55044001496044045401c461004500820b501c500b114103042080d1661400c0340b040407001801d000003082202900c3c10328099903548140000c0c0300042c09641c07845d1007066644442e641d1912a5034444050200340b4000c688440141d038050000c00426801d650303515040d04c10f25180350144080b0801d90040039035030310115405008040c024a444d06542603020f406420140e44001c0035010300102e00c183d0703060b034401c428841c58000070200c0d41e1a2802e140b401c0a100394440030760301402401035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 372880476 1250 372879226 372879251
    0x16030c050d260706140106050307030b0d0609030f2601151107060801080d030e030406030b060403061107021c020d06050703062606160905060f041d0405120702060304080706 76
    0x2102a085004400320b20b81da1012490000101c81c000072082050454010051110b10f5100d403d4031703070041ca182800074061144400003102c1c1100320100900305402c21154208040c1d01041b8003001d42125141c0ea0008072690b228200e110f940e05090014804c0c0078401089448000c0d8014804100203003090b9000300761040341d040c249805034001c8004264071100400000104000310340150030300d49030800200c803540d0f40d026180d221314072641081588482e000100d0380e075003204450086500803000c00c03003001d180b4051090f80e0400c1c071081c0c0c8901c07052800711201084001e00700c58840d07401011011006a10b544030381c01404054000000c051740d0300f0317000c20007103214200409400003820074400c1409094030050f2404500500d4000e0000041080f0007209400c00c1c050415150200d4289880300c511900c0068280180d0740001400c0c070711101c09041d001c1d5052822405540103400356110700e00000c1104c101481914002500540b00b040043c011520000280070301354840d04001c07503440c2c507440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 372881726 1250 372880476 372880523
    0xf0307021e090f0106020f0325140a0b010609140607021306050d050c1314010b030603013305090601050a05031e07050a0905010906210b030f0c0316030c050d 69
    0x3c8428003002a030300018010990108440f05003820284015403509211180c00d00c20f0002c0c820007040d125802814540c104038a42010000700f060711022200e080740d181c04d21248000003031203080e01041d003011010440c00c0705082c215419503c0541440c5c5855140d0b42031221003403820910050b10f540e100383c0030945a035240060b001d40703801440180080441c000030080b89601d18503610f10603515090605004c1c1d00501c034000d044a403000b10b0340e91680d4802c0d010a014082080c034984504000114808a20b91014824600700c4090300241c0c1e030841e00ea00602688107000d503481782c08950184000c084840c460002180d01619400c2ea5440e00c45608820048080007540c90101295012a080e5401940f000c03298000f000e0920b040004a490020003400c010400042d90040303004102c841c0e03820250b5a000680c0006020341100d404091034546a03449041510720244240070706c081015440210002801c15260081503084032113103400104035a1017528002291001100075031215074a0004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 372882976 1250 372881726 372881731
    0x3080a0e040f11180d0506040f0f060606200a051c030902030f0a02090c18040203061801061214091e0a0c06050301030606060206070804031b0b090318030f0307021e09 73
    0x10f003412912405260300141c0c071650151100e9024241040303245012904c002042c81d00107070802050482c102c11414141d47c8009060005400750303061000000304258404500004010b030b501c0000c503103100440409450300991040034000380d00c441350b1028800440309815400803810300740000c2048d4241e0110b802d0400490f013403011500000b440f0820360030301d030072010b034858001071026280208080b0782c0c000007105025414000c82d400700008115481b0381071a44914040c1321900e14085d070703413a800100f080101e40d417100131490400c86a01e115540c1c0044950088408030042c01071100c0c2508400ca090840c000c20036424440c92502c1804200c2d5248401c0142c007165582964075070445c10b1590540310340d80e1194045500075820040e80c60f9014000070780003541885c01c00d0b4080b00003a4000303c00b010703800000c0c003505c0c2c19009014481c5800001400c42c1200030881c0709420f0001c2c810582c5030f003d58090170140e608204403031001441d14030313003c0e40c10402401068242c0041c240200390f400a04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 372884226 1250 372882976 372883001
    0x70e1302030a110a09120327080f010209010801140a0b0415020d0804030c02120f070b0715140118060e0a0b0103050c09010509090c1603020303070e0a03080a0e040f 72
    0x4144500d01c4600d01a450b4a075203c0c1240518004107014010310050152080c1355011307128034044020180705081848030301c14188008005209002141d15041203103203c0d00f81135110321200c24071062410f009807a90800141c40c0e02c10580e2800000b6460f210449065642c049480c140115844043c070000e4000350640241e0148584c2303104202a01e8124028802c50a01c05203404002c0060362141100141c1359040d80c0c11241049280380240c40c040188000344814000c40c1c1011580d4032040c03020781081406001c4101d0b100c0c8035200d48000f154400c580d00b2240c8103030b580c01071210303100c060f03a00119001041c5001078170983e036040d03180500106031004085030352a9081c6011a43c1e150040315001098203000710b2034040da010001c2d28034860314041d607010b010700c14005015511000305440718130005024140003454140303402502ca40c411130b10b45003c80e29019203400c05081c505c6c1c80030250f95018146a181502010b800c4d580300f0748001a043d840b54903000101d00209103170091041d040c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 372885476 1250 372884226 372884231
    0x30f03070b011401020303040c2105061f0906080601330504060f030b03070515041a04180608060a0207050f07080115090e0c060901050f0403080301030215070201020a0308070e13 78
    0x18008520510030f10280300e541198000e00912000c0740c8681e00100c1200c880c02c0000e0300301003c41c030881408000140340500325020300000c103c0c00c4414130400252905110384400300c2c164941e1040d004941150149a9a07540100010721152950200759150036841c0c8003a400c0c60f1388140e0801c05040c08280c81e074000a0000301c9c04005003600041c604040d00030504003401000c00900100380e40f81803601c5054440c4001c0e0322000055040c07101210003904040c45107020602742a11000034560140c4a00210007800c03521003c42c6038624401c01059492480181005450300502c0030017941190340f040d2918003803892100c0800e00700704841e10051085200110300700410403210b4401c21125401a14401d003000d61032204000c0110340700242d09001c440c155100c85045004841d540104c0b0036400207604001004014840440c01450490740b08480401c81d108090045040500a50074000d0140e0300250743c500009004200f2160f00900030314104034040c008100190504c00c104c44e40c50303491039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 372886726 1250 372885476 372885479
    0x10201113a0c091d13020910080303010902030103020a050105040b0301030303020f09040c0f02010f09030804080a090e04140c1507111203121005150a0305100909030f080f0123030f03070b01 83
    0xf81048034494130300c08182d1680c180d03d4242a6105103550000000b44035910000014004545840416018018010807641c40e5a111103000009600038041688100d0805d8000545507210b0b00844054074511022a415079181d55015006500a920703c2000d99006100d942e04c1c50300c3d50f1080c091800440c0d50703542c032090200d040203421948aa02411740503810800c51038042500310000d140c10591142d0030aa448192036001c40f02d050306e607040800d00000c800148401c3c8680502d4140320a07030864203590030080304004000100050390509940c5c4c040c140121008190413000d004150f500c060b000e54204500302031024195441201d014030215054824004c8100b40b800e640009002d09490380c00518482000a0380503000e050680b42c02c06848600049590070000800c0b4010f000418003400750382c0c41c0e850094003402180d501360000a03070308400200615090350748603049500d0004080e540b1139001d2680240e10204000407505849080181240d40070100010050300d03008001055155 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 372887976 1250 372886726 372886739
    0x81b0c0d0b040b010905070c021302130e0403080c341707050613030e09220b0405010f05070905040e0703020d080405090a110909190606020309010201113a0c09 70
    0xc0f10681010421900d030004010140343c201000e00000303501142e0f4000035444611940b00a0b2148d104110164042d03948001850002d190f1858003551181c0c68450796603a808122500d5401603503101c1e0340390854ac001401c0b01c208404901101000942141c46c16091981c55a080c203203010b1001c1c0a84020024245060000c10300049800000c09806071080c0b94840d10003c003c662042040d40c4280c85440100d0141d40580041c1c5100b43d600d210004c8801c0801c0c2000011014100c4060350035508001d80360603500e09500c500c1307100350700c9500c0340303403256040c070b006d01c0024079682103140342c40d2149110100c017680da160046500d4600c036090070f994403400c10302030080c81d80018007416511410100001c1c03130024000240c0741900802e0340c55564960f140309200aa60007aa00c106850a26000000c100180e0100050098038402e070000e11000c61380b910004040d2007000540c2c4290003000c1030724404006130300c070b00c0080000e100050700c0f905083c42e00a4400c032140400c00e0008215011410040b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 372889226 1250 372887976 372887993
    0x6150f0609080309060306061b060a021201090b01080a0c030e0f03070501230a05041e1a0c04260c03030409020c010f0b0310050c0c100e0c060304081b0c0d0b04 70
    0x9080b0900255050000d424081a2103000180601c1e110307000103da0a9102c84c01d8142c1c5400e40075410045a6035410000070000080d8000002c0b042c0d504203020001c140724a841c012500c203d00180d544200310350710700341c02c0303030041031460072010805484101c081c158080800c0640c2820440e0005190f42e02024a001d07401c488450401d0940107040e400612078041c6070008040d4042074000d004155642d80b0b180144d46602034051107101c40d1039030b00701c00c0b00f0300c100410740740b024184242d049811921900c65a003054020361140113009c9541038540c9660400032000e840f141844a02180c0400d0800b0f230009086030440e8000c07111041c0e010844e66041c007401d00440c00d1021024008103c140c4960002c00d848003513280402c102c040d01c610200d00407462100c200c3d1601e448142c02d0720210242b9a1080000d4808032542c0344a502c281425161949840e6084a002c0c41c0d11000c51071400c00c4412140b4030405142c100105503004908009080380c40b803200b0060020b210f0008441c0030b00d000d00e400d003013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 372890476 1250 372889226 372889229
    0x100531110d0c0c080a050705070503060105030c060c070e0403021f0c090b1c1e0e060717091c03270809060f090310091202060405070b0706150f0609 65
    0x80450501005900248040d02101e548044110021070081e07040181a40c00c1003512034000c2140c0c4000810080503a07100c0c002d411118490002d54041695410401d560303028280501076040d00000603a03102450884002c01c0c04c5c00301c420a4840e910368035002d006d82c81c50211780941c05600320401e010303d90841c205c603026030900e60400c100714140c03070100000d01864440c0625a9490400134401012801d0140a008594081c10003440701e1030001c4070040c0506a000b01003803460382000e640c40244c010220344a84103d1680d0ba40a6031000700c00e60141000901501c2d06549004441916028500144200c000700303805442c04209450340114008270141c802c10310b941180c1c195146c1030300103500d0808440500404489454807080e80004991040c0f243c980603d41c944105100300a15500d950407034002c20740a280c0d011a1f940c940f0b80c0030703070311080304603402443e80c1c003c1c0d038003803060383c142c2e0001d400d0250241d8030008402c10a1504d0104006054000065008900c3c5081280301c0e440f455040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 372891726 1250 372890476 372890569
    0x10e100c0207091109130b01020708121909121110081e061c060e070f030b01030314070807030207030209070504030c050904030c0210080609060402071a1005 69
    0x112044044800030b48a514600a9045050312a03101c840003002d07100039078443c0080208540050703080403800030018811b001c4d11a000d400384c2e600c005500d920200d5038280f590b0002e04100d00d40481035001c580700540d68030902c0e06016081001182000d80018141501171286501c104040100020000083d1001034014200f010345410007681c5548500381c03455205012800f038800d42c560f40006015080b035504420303a00014610300030180130081c0c018103c805407220035074004907242c8403044508503d078040941466255001000024859496012014610383c10cca00b804410355440445500032003080d001a803001300c040c02940303800d4040c0d40d04417400e07081041c0741a283d82c0c0c881d49101d41c144100fa02c110005000202450701a15501c0203c542c01030400742e900a1000d03016040e50010785200b4001c6000c5400505541080d01c02c0302e42d059044951b07078071704014400b80c12101d0300d40207050070720000300d5010006040d21091900c0404014030282200390804c5400340940f0030740d02c1d04081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 372892976 1250 372891726 372891731
    0xc0a090305030a03021317030d0c021915050106140f0711060c010c0801090e0705270117240a1d1606120203040c060f0302040b0f0423060a03020d09050a0302010e10 72
    0x2001003010020882783c6510116001040340e4603507100c01c4c0d003400f42000a405005940c00312910130000240040c101c994980041080640d07252181110940b41c024800c901e224004c1144558080040002d40f54103840761460b5104005040c010500c07a41203014202101c0e07441c1d4000c09035854000c1c3c1221b000d02000c5c00e041041c1d4507403401180d920001c80c07203440d020b40c6171554503088044002103142043c00400c42150740b6540d6420702d1110350440c003401e91b095805800b00002d16060651800a803040502c8504100d0b0317290700c0c9441b0020111111004000760030320f942100c04030000e200300000348a4880008072114503ba4010f84596100305050505a10400800000a8070001800c00b680c001e8a00800341559000e1306800038417560300000e0034800040350880034000014010001d8807900c401002002c9141020682608106043c15030312450030700003508024441e5015002c0c0c11211500450014044d454003828007150741750660050351200104007000d842006035545074045603104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 372894226 1250 372892976 372893009
    0x120609060f04020c01060308070308010503250312020a120e2404032910150305070e0f0112020f03010e09070e0f100302030d1101110f030c0a090305030a030213 70
    0xa0450045180440c2c45982c1c0802c801c03000080940c003000c0655800703940c6507501c2c04c580c10003401c200801d2046600c00e100303c000c074041048040c0e011401504030020b03d14401400e6948000b5042d034070112000c1103100c1c04031110003003847d000400e0104101d40d15660004003207041402100c0b00200c5040860426000c0c5040e0000c0803081140c0c00c594001c20304801646c2541140c1c0b01c460107072049455a03048000a01c280491061035a004aa100082d5014296500300c2c0503016254100d81500c0810950083c2010741c1c00d0426002c15400d505141034100344d443e80c40200126080304c4482d01c01141d0200042c0404c40029402ca9004501c40b00204075203407800300713843c20183c3c008110100b82181807010800c140e500840380c2c0040d640c020242c81c603600090340024802c14180d1122700b000d40c2010307201ca040c0740c1120304071a02c032001800720602d0355540c040c40c81055170200088004201000a0002c0812400d102600405c04a6900983ea409044a500440705c5868108600980c00c0340203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 372895476 1250 372894226 372894229
    0x314190e07081b0301060e09100605010305220201050409230108030702060403110a0504020315030616020a02012006012c060607020108090a05120705283512060906 72
    0x200860700c0c0c3c4034410200c2c09601e080002c240949001c0d0b0101c03c4a4401d10103104400c90003045000826244e01d40070001aa43c0da4011010b9400c1925000205803003008034400710749401520610060045c1030540c07419641d004004202d4070b41000040403100c04080c400c1040e8480f0145a00418544009609140712900018410b00c25880020001c142c00c0417000034a0315401000c0700101001041151240342036154400c00303107000c401c5107101380110340000d40c4021103900101c140c60020360061031903101550040d0f03440c2409900d5038540342c4001100308802030f4104001c82c040c1c150201a0713070a0f240304980310840c49400f42000780c01c82c0c0c585403c000305a200e0034266440f0640900c1c0415160b2500c060341030030b0030b0120344042c0c114003c00e400030800110402c0184035030713403140007201c0030500c2989a40108107921940c610400b240350342c16402040e0040e401c0d071480c90f8406001520380100c10b8184210740c41c0c5107241030170181c001c42d0850511a00c942c81d01e50000c003e4410740382c04c0ca000300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 372896726 1250 372895476 372895483
    0x20d0206010503160b03130804030803070201150f270501141314150d0b240306090a0303150e07121406031f0f09060203010f081c0309030314190e0708 66
    0x11740101410007000184000400c040701910103900a400a81c0d26902d90410414a50040301d00c000550308001c4110080074503011020304407880e442445020fa4200203442e00340c005000b103440000000d56650302860640703031044074000c0c20700d8450742500048400a1048590b9201c0c0b5040710545013039003003880314508602d241d034042410507036140110300311300c0054104201c44002601085000b02000203010050310040b03802201000d4034052085054201569000225220070307183d04880406000640203030031020010b400c0e1000c200656485082940c071200003154100c001030903c0304d01050b004154070580400540c1c8007050740152a040c80400e07694050104990410601d41111040240441d4005090504081014004001c00342082c6010350030a01560300c64007000300c1b00051803000025400c0320141c0b03005581800202c4200244d0080428280c26410b02d07480d5103e00508103c0300c140d1521404688003a10581d03604100084100c46a0351401000c40d402400c00740428030000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 372897976 1250 372896726 372896729
    0x60612050312060612070306091109030a060f0207020909061b07020108041106040b131410021e0304090c02010f0b09010b160501060503010e1f05010b030619080d020d020601050316 79
    0x80090740003d444102c0840d07820b00c00c40c0c0e036070781d801c00410701802952903054200c401200c0380d2250a00500d0414003811100d41314044d40702c3d034198007642c0310200089094112803020400b03540014146402c1da000b00b4922102195070351540d402001c10092101360203400c0341c19440c280d403840c1c0d090000e2940060000c0d600500040c00000b0040d0b00700c880c40d5140c03011100a441d003286410307261052809980b25520880c010501c210442e03181241c6c00d41000c0307000130501c020950043c60300350400f2588407030b02150784611420078002080040745103241402024186541caa0000400131155406002100c80004410f44100d0704c10004002c00c11401040d02c40b52050800c40e540c8001482c6821030041100354801500b41d428078403020486400811055084040100c047c00e000006824000c2190024003402c5120340017800400c10038103100080e0309a0038072400c0d0590441d500d0750f10703441c03034903079401c544400603840101e0030400303203605010741401000c080c3d005101130403e803410103607000140d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 372899226 1250 372897976 372897997
    0xe0d17070519110607060b0a060f090506031608090114011d13120e060702030d0503060a0602030901020d0c1113020d0b010804120507020d2405090a030e010e040b0a120606120503 78
    0x310b0b486003400403d500600c500c4100524048a030b070750752a40504003130482d1032b0300d102180480400260303c1c10800c0c112403040d001040c1a2413503c0b07032800c2c1a2440b103c0949000030541d40c0e884040f0700e9101c81c1c150381d03020380414150000c0711025074495000103000108806081800c1100c400001100382c040314081e8403090230020350450b04034011400c1406003240103580741c8178603444003c100c0c0d0400c00540c081d00e41551600f140e180c0303407441640e507403241008150050b03100c607140c640d08a102c1d41c1c2c00006c1504c941078034480300300e4800c0000d1003000b1694401c40c040741d00040f0b022040805108646014900703090401e0586059225018034904d151451000e1000c000b841d0300c110350701d02c24001c1d01103500002c0c1d8051030341d1a6001c400b042c40e018554006a501d44004a5121000080c0c5001e60300c1d031640c0d03204080d240d4140111145018101400d0b00705488000c074100960b61104581c001d032881e50740340844e220460030010242c17245948141c05507903a450050010130404000c8a508450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 372900476 1250 372899226 372899239
    0x26030c070b090f04091103060f071b0822050a141309060e030f0903060609220c050d1b06080c1b030d0f090303060602030c07060e0d1707051911 63
    0x6a01c2c08200c1c090540382c8419403007817400809004129500c000c0107000981035084030115511040101030819040d510b05002ca003070704d901c2609040318104078800035840781030b40c581840100d020b0b242c40540c0901505212004410052200782807034503469000b05207822100300d040321403202040d0a04039850b4070344801c44d1548015010301669800801440c113003181225590400b009400c0d4094203d650300c0380c82070190102007201f81c600041540c3c018210601d604001408410f8000303c01380600000f1204080d07910000110765985150300e85105000e148220f088889207842040c20f802e141e00031405003d140c1060001024051050b80c40c4515002c0c442c1301d00910b1803000701d25500036030444505040c103140c0800d20003400364205001461103038030280301a42d181e60081c2d07124043c0c2c07101080e071540550010010a4440ca8035070b440010040c01444902169482c0c0c002429070b01d414081c00c1100014080040100800c04505402102400f08214903055a1810b050111055032a4032030b05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 372901726 1250 372900476 372900487
    0x91606050d02040f0f031e1106030907030506090d0314010e24060706020403060c020f061f030b040302070303020d180302060a05120f010503070b03130f0c0b0426030c070b 75
    0x12100c2d8125005001e9040c07400f00c1250b950841d17490803480c1808104c82d0140d80c42008541d60f201400400400d03680000342d818030308032a80511000760002003845140e80f00fa54400004100c041c4500c900981041d005001d06080b0782c14080c068980c611004c00320040d01ca07004100b010122858190800d07080350280d00018ad0356001c0d03458010b403021760240c3c40a400200d403000c00001c0d50040085034441d850a012802d070703610050b80c5a60000ea200740250300304c0c0b40004d01c80c0788000c5c81a4280b880d4151040c003a1070300d0b600c0f012001075086030200e01582c01070030148140340d010840890405407602d0709040a204038401c592041217030307100090290740085808402140108141c03007520076030300040c840900d003c21a03802184170a200c2d441c0607000c1d00030080780a400741400c13248280b010314201405500182d58110900c882000d00352038500c40c2c41d0021550000e03d0004000400165006160082140203a08c002c1e031a5558226810740c0704000181b0b01142c045824000c41e81040012038540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 372902976 1250 372901726 372901747
    0x301140a12021c0503030a02191805041e0203010b120105090108030403080307050c030a0315061704151416080601080105031e01061502061b0403050a08070203030702180f09160605 79
    0x7070f40c84840003440380c00040104940c80070654080d11305203c920001c48140aa104001d44141c0080c107443c0c0c80640c031008052000c0e04054006501003040d100a0326244491120680308a030020f8000041441e000921f030b0f00020107a2070814003400048485528552504600650b24030982c4001440c4040c04400103408070b00840a4910841120080d28bd96414102004001701001c491404482864040124540f071080c0c5540503205900c50109010780c03039640307510000c614489100c16041d6101d07410361040e0800780d43c5041c02500080000031005600d603038054207001c001000a0b04202c1c0c1e100c010080c0b40e500050102c0d004010080716072240c40410910340c0948040d800041d880320b42d2681424000d6030028040c3d1007806503591000351070f6600074002406108a00c00540325500c003908a4000c80d207620000c3c2800d074030040462b842d194403075001c80c2c501c080309114903001205890812030b070499010b52855000200d0b0b0082c0407401611040901807050714015901040004210f00104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 372904226 1250 372902976 372903019
    0x3051005090103050606120102040b0714010e01110c0105090307020d080a0309080c2b0f081905100302030105090a080a0f0e130203100f030f060f0b04060b0301140a1202 74
    0x15010107440c0404070340e1070341462582e4110a0f10158001c0c0d2400f825400d01c484180700799005d0321880c03090b8616024098035440c12105c3c80584c0c0342ca00d9544c554001d00340d20800d00c5503c5042803a10405512540c0c813080650841e90000c0211125400810032032005988441407400025408000380b40c0b0b511241104400800c81c14000400c100b13400504541a9000010008260301040d40420901d04c05643c940000c00350412511005c551751a43c88002c66000e043c00d16886848401c8541101da038241d156800c0d40c41c00d542409010740070400920641c2800c1c05407079407082d02c1200a00076a049680c0e16252407003a11010810002c0c80840704041510503032402c15088002041829081034260904009610944810504000343d61000552003004c00780d140843c2e81000700104130310213644030000900f0484030003005850b910780506405903518810700c40a408061920b549070360401d10a540341440e0345522610a0740d01802c20000d140c031410610154590503100c1d80789008410300180715 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 372905476 1250 372904226 372904229
    0x30a06020706021b010e01180c05010309170a0903111c02040506010e030604060b0f010f141c0e061909150c181d281116031809020c030a030510 63
    0x4400e40f00044d21000a0541103001ca82075810000c01001c11312003003503d44c10810100003094119416001c2080f90700036030240c640d190003529a48980b5100c08407010003544440110700c0451590b08081c0140405030082500010041e81e0096220700c12404211800d41c050300005e2003142c4410002e200c69104214181010001504941c2c05040c280b5002c8040c008090703c00f809401d4001c2c21818641c8030300c280a441c42c0c0191104840d0746005260003840e0b43c000181000701c0301c12860781e1901d0321044c0c4284c40403241d0b008c01804071818109200c51001d40c0624505400c00e04007910040410140101e40c44071003030085000070080e003c1c000035500c4198040c1d01502e400282800010a402c6281180340d02001540a000145d0303130311104021900400d40c000b4407042c00b0101000800d118960040308074003200c00b000303414000d10071150304010140e0f007021000204945811052401140e001d00040e01c60a0015400d20800d404003a030f0700e02800c9042030070580c8400c04101f008070011849170 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 372906726 1250 372905476 372905497
    0x120d06170619240e090706050a032307020a230309060c28050d0305070807110c0a06020c010206091504021e0301020301030602071a0907060f020102040f06030504050d080105030a0602070602 83
    0x646980c03c100300c14aa03904180b082d960386003036600001c0c198503008506801641d0f501d0700e81908015102c88220f00600d0100a4000102c0b0301e0503600004c072409821a5109030007550091511182d6807505190300c44c40100c3e2502100119080d4041c401401304c2915481c0d80d00780c03085a212001410f540e480c2c001c2c580d0001d118a0264002d81024640d2184003282183c001c1c0100c50030b0100411046044030f1080350034000103406800800c0900f0b01c03800b60710110625100403100f20350700f20400502502c4040e4444005a44010f9805c411941c0603c40654031550700c00260113a01c03081c032141800100e000300003e02c40c050300850700c64400440c8842566007800500210348a60312031402600035884800103441d0345144a81280180001c6400d081c420345080c800f03000001e140a84c01c0d1018484409140195502400080340760600c9202c0d01d80244060fa0b80880c00d818070b801d0003801e0400c01c81c04c5808005552005011540700010074851803a48030500691b661740509100d4006e000394210314 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 372907976 1250 372906726 372906761
    0x4150909020304080705071203090b0904020c0f10060609080a110d05070803030703050606181003020702030109050615032b030908220b0702090604020d0b03120d06170619 75
    0x40c000b05070f01405c0c0142c4918201c42e09a40c0b15105803400b11005a00100050082d48060002e0720000c0003a0a9907003000d4409410040940d00e03250900c0c0e0744014001039540615828021042c03540103076001000d2604010f0703165403c045102d500c40c1100000035040b10b0114006210390340323071440c2c1500000c0d040000d550002c1d4071100155143c0d8401e403103460000341030401040e9a880c1c08021586079035040f080c206407100d00c1d2420301c41100380302601141455030900507507015840a005d0701c6111880381d40900002d00d803e180c0e00a03072045c101c100902076400610901e0401c04003402c880c00402c10104401030315014040100c010b0803d221300100420400319a152120350001d955000200c0d82244600f0400d0301c80c0c0080340307031b4020a01e0196001d80e162011640c507090a50091100c0c800070f10003c521000200f020a1425042400f15040104009403404c14219a441050003404035400841c507241004058240d481b0310140c8120642c80146e00d0100d548580c60380070b40041c0e41c504250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 372909226 1250 372907976 372907981
    0x9070509010f080c010923270f1302060307080619060e0a090c1b020a03050a081207030c0804020613030611070302010e15010303051606090602071407030305041509090203 75
    0x80e8003008099102d881814800c0f480002e50a42c0196014029540c0c00c01840007000711404200542c421f010044540041c0308000d08400d14608071000c4442222000306403440c1e0520943d50204500d0040c804a011a0707003070140001655003d00b180d4010322249850740427920394500084030341120746000e4034503880c9240d00180450f0001d41c404019801200e110360080d54600380d09098030364000b00341700043c215001d002903000c950365003048030340c0c009050169040d8407a40c5041c5001506441515040c0300440c521a20a1104203807552001c8140380620201c0c44200020b02030720310181c8000d01c2043c0102e14900300c0136450202c00f0040d60010070501001d00101d0303100680ba40000b20960040d42072110b9540300910014249a180002049012a036840c43d10212001c2d0400e0741d50380b0022410f142c80c6408614a400307650345060040c400142d4a4901d4074003000f084407064480305240d0403103102000800d4206099608440402d10600b0b02d117004010200c443c050305401800740148007205 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 372910476 1250 372909226 372909239
    0x2040816030b090c06030c0a030e03040617010f0e071101020720030c030321061824091b0a091e05040e030f0405011412071211070203150907050901 65
    0x2004a82c000c41910b441034680c41685038990303200d00c500f15003000d02000450785c82e5015100400381d8440c5441e0024000e44c0c0003001a0650b80310b94045400211440a01508050050321075401408a540518201d620700031415007811401400d11007407104022072400e08840c00c1d011281e020340c0c0003401402c40148564000000f443d114410b070701030300c99500f00e0842810000f08980302c9100d00d44500355110329022018445500041220390401a10744600181c0105010118019034182045890305015802c01e9034183c1e00480e00c641c451307a4100e06004e003c03091101000b50f5a1740300281581e1b1307007070501810f88029085510030280c80040b0400351224100341101601a0740045405014000c0b009480f1075490040c0043c0480d005000c0208001540c054a000302070040540c4685061851034500301903040412600c01c0042a100d1202407620030a910964190004541c04a400c141d0290007007a40c070101001c9044022220a01080d80b8400c00c00c500402040014402e0751650307151407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 372911726 1250 372910476 372910513
    0x30c1204120909090f0209070c020a080f1204150305040303180303020306192402070b03010902031e011206020913020f0d060801060311010309170c0d110c150706020408 74
    0x103050748002070140a01003840a0140594014541c00c004052400b4440d0f03020441c400c0c2d000741084080c080915810401038940e691020001c0c01c00d60041c0010300e210310b600c203041a000365a54454084100020b10803001c0b5068040e848020318170b8005601e0780c1d98074098000300001c00d10884284020b41170301c0c0c1056030640003180b00c1d007425070b0000e990b42d610384a820302210301400b80103603103007504c0703030b466045080c3c65a808000c10151045a00b415681c1c28802c03005d51003a00411181600001008140610300341e10b01500d400000c40004c1c5980341c0064000710656034580201000e8000802100f203544d11040d441401040c0d481c02c41d41c590803040c8200d4654499131049403002c1c10103400242030b8406105000840790403102e402d44100345440110001c00c811351040b110103060784404c01c20441c14901810200c802100100210039201201415080907288140b0b19944280480e0580d80c940e1a070003001c012603010915140d480303030314200c0082e000310740001d030031841607121864001c03e082 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 372912976 1250 372911726 372911753
    0x504110a03270201050d15121a0106080612030702031204050117070804030f03151401030e1c0e120a06060e0a0c08060f191d01080a0f0206030c1204 65
    0x140c80802010881c00c0640da401405410b500100b480301010340400342d4014002000d03001d00304040010380d2008401c000101a500340c01c00b02c00700c803401c803120b01004a0342410382212089003c0c0b01400e585403a000905005004010074001c1007003000c00c040c801c03820000d8440c02c40d4000d003075800c03c61139600a82c040360014807440340010303001e1001281c0180d0000d0500d0207440f02d5580d0001c66500d80e141540c520340b400c003041d001c041da902d1101c0460070b0a28200409401506200c042c2e000c940c200050540343c0c4071082d032140e9001804487c200004c0071100d48800b00c07c500f00031111100100015640b40b08440301400c0c1401184081d40030000594019015038040d400817908a072180280325040724080008640403400010100c0d43c180742000e0040e10048000300301c042c03441561416400740043c640e001c0c08860f918004c91405030b10b503150302c150242140400500b000d81c0281c03115154504500750180c014a4008003050b1450350130800c032403200601c504c420711141054589480c000102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 372914226 1250 372912976 372912997
    0xf030c0606030c220c0e060d0506100215010326040e1f1401030e010b040905010509190203060c0c010f09050a0302010e0d091406071a0106020705030c100f0306050411 73
    0x2808411030041c502800752039616207440380303139420803140b10248100405280d1940e03000c3c005103d1500420365180d0008101c0288020000703e401d0030b02405012140000d43c0d000b0741550400070800000c02e2404070110f044a81200c01c4070700c40143d032050722041782072405207811071502c000b601007200d20302400302500646050b52100a4050030811210105c1c00c6c40c00b80008001c3c542c5484142e43d0f00ca03800041e00720625200008020a48400140c11102c01140440705a5112070401c159190140003c0b90200010926140e001c0040d038000781e11148010842c012040300071419001c680c0b000d502403200b520380c0d1142000721030b6050403c156101c440010031001582840101e007a6140e0210340c500c038070009921a5020941040c1800160380303400c0c00c240340c003c001808603201248100c055001c003200c000e68824a15414860000e0400e0200e8100034002da00440442695844a49908900152a107031036025500180e80c02c502038509644201d905c00e0900b5110309200c0d03114001000341c0c6a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 372915476 1250 372914226 372914233
    0x40b06122a0301050103023609060f10080a1b0c200102030904020c03090402040b0c07140607140c032a010e0a0e130c080102090f0f0916020f030c060603 67
    0xc40d2001d001c1960540c59814849801d1004000650181d0050500c81444498090150942d4966008014040c400c41812917004025050490620400311500840207030380724807100b44410041442c102c4c00454000410940b040000d00401240c0e11018400c200d00c81111340e4024100c07401407411440c1d05c802c3d9485860305241c00312040888007980d0790140d041e0051814035000780c0030000250880f00c445021408100079466803655144010f00182c03038018180c540303030324120034201e2600e030180e0005010310f50940318100080e900c1c401650f107030720b501c0044003039080747d640c0c207090500000c110865010b2281862070003a410a0b050111006004030340340d4076050b05004011034510b02c41600340b58026894880900200c50340c036039103544c0045040380351440c001c0d00e6074444400c1c03c050b60007084030b42d501140e003d41b10b103002190079845031000c0f20480d90700b104143c005800800043c0c981418204000001c45040b070090107100d0174650560300780d0340c441052a84d1562101f008484041c031a01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 372916726 1250 372915476 372915511
    0xe07141825051206060f040f0905010f051e1306120b0405010b240c030c0a05030c01050c07030e040b0a050607060f060617011509030609060906051015080402040b0612 73
    0x1031107030090f14207520110700f244145845083c2805000d5025143c9908a484104004030b58580d512041030000d01c02c403007000805603d4482a0b4a081800d078101502c81c0d0100d2440700503411034480181c6041004070b45c0345d04641c07407071100c0d50000c0c90140d12440580c04001e110400323100701100714901c030f180908001d21203a16440e0070401101c140045085964110807404100c04803400041c141c0140c0c048100c0f89069000c48025280c030301d03008012103583e4000951200000428040d0760340101909030520304140d915a0050031001200341072502403a91108690450b41e10301c1e000000a00010303180d20344c0c0708200c3c244800980503102a5214041c10014002100d92081038509154420262004510390802c0208200745541104000410840d50404030110303c451003180183c9109100000c1c124005280c2031050700c10085c21050360fa4000c0c4020801409080003030241d44030301d490448019030342c520000f00100008003980d500504042440607040445400141c040c1c107801c3d02441050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 372917976 1250 372916726 372916801
    0x10f06080f06210102092e050c0c0909061b0901050702060a090f1d09070503031b073308040201090504090303060b03090109050708060c07020405070c171c0e071418 72
    0x603c440e81d10b20180507c064402e8072114450750192100020710810b4910640c401e1002032547d444c1510402687d411440a22400074007a4011114500b58190284d080080100005e4094003400e4000b038061403002516200701c0748580303580c801808030301d10125101601e0b007001c800080d0710455062440f400c41008100000070008403041194801002145001c01030310501070341c1080c040300804103104019010a500c03940c0804842e8072401e000c03461001c541a40c12000350001c0902c500010300042c074050001503613000700041c0c1643c0c41910042405010351808500500f103075401000c6981c0080144404c418041d00002c4001c6c2c00b4004892103661500c21242e11442c081d96524015a42045110b006050541200313500030b24604000d03044100503191540c00c082101c0c9510700e9480300145c1140e90385000401101000c40031441005a040520b00c0c0a0390341d90b207401580300709100840701403030070380d66040000510440e00301911000d0514542c2c0c1d01c042d40140182e218100380a54400482 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 372919226 1250 372917976 372918019
    0x12021f050d11121506072a06031a091008010e07060e03120403021c02040e070504150308031b07080a030212180d0804020423040506010f06080f0621010209 68
    0x24501c003802c0304542034543c810512a145240300002d41c12010912060b004a82d80702d15005540087d0f41c0482a1648880031001540e0100d40062084c58a0030f06604c00c424060850361200100a50f003444050712503241d4002c011303003039910900003982020a40206000089135102c00c07140240c03109130782c9411200405441e076040c0350400c1100d1000b48020409031500c0c0c6030000c0780a65407162000e40d121150003260540e0b245448044440d488000200030754202881020005592540d901c074103e401d60380c1e8144c00b0302c40984440e8400020318a205400c0441c00c049440b1558841e01032691003500e42030103130194100c0b0070800f9401c1c841d2000a0301d4102c811000e42c0c05251480064040c0000d8044151100c0c24041c1c0181d8105a4621003410909095040000d10301006040c2002c2c1d03162078507105107031440c160040350b200707103190740e04205080e04080550341207030005a9a81c140e90700c80b03002c2003060803041d40b01505402c480000782c440300019030042109032010754451482a1a0a525096 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 372920476 1250 372919226 372919237
    0x80702151b1014060310020a0c0f0f05120c15040515070801060810030f03030f290a0b071e08091905090a1a0409080f0d060501020d030c020712021f050d11 68
    0x4142d0003c1d05c06c410002a41c1d401003a070220746041c4030840f0701858a41554280000c0c1044904505140b158002d1010402101e00c428402d9156a890182e90520712615040c04003204014400e01d100814100901030140c03485513114080c24541c18940310100510f41c44003817051001182c90507000c941020395880300c00059a40101b03030308a0402160b034003100140035580343c200c2003aa41c0c60100110202c071120700e88464080261040300e4540c44403c000d40b48072075910088552800704200c000065001d407611201000300c0303008001d4007415040001151041416465010210b00030116540e41c001604105940054890810b59518084000100c0d501910320903c40107403055001c003185026045804e02503c9040c42c903003031503140003140c4201d40000e0707040b00c0c805454141c14005941d040200c1c107021403d600e41070240794540304019450700114000d03054410741249c510010b545400c1e035118500ea019031030b580c1303644140d90720003400364020808114050341403007212010071400409898 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 372921726 1250 372920476 372920479
    0x912021507080403020c101b03020c040b04141303110105160806180c1305060d0902040c05130308070f0515040308062d010215040f030912080702151b101406 69
    0x1015031112001c00642d1140d001f1a0fa007000614150b4004104070514106c0109110b50000c00e000b0210f8010030040d0341c90301029038092481c002d2030041120034004515046521f60492030100100703414100e404003e01c0490050b41d60808081c450b002012250084407240f040d650241680c9031401008035030310103000003040c0c083c00940803994140240340281300b0f030440200c46150556544011a5554000006801005580c0d0710b40c0300c10341c1414019081840c0651402d140b0342040740340d9060b27030301e0b0f030310700001c2c03d04d00002c294a020880070042c011100c0703810508540303100044801041d80000212030480009078180c0c040383c402c0c1419184a44000c00c0c69000c400c50b0016900710618038016030404604501c507200310802c245007004031060240380500132500b44844070b41009000040564002a00244280c20304030104503c0000c2d070b0307030340c1d51b0464049214a07000c42e00a002030044400c848440040b6210309085080000381d5a40e0b04a1584414402c201582e003400780103000441d0504e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 372922976 1250 372921726 372921733
    0x3070b0408120408030933040305060702010501081009060b0a080a0c1401020307061119020304061b020907030207030306090c020f1e1e0a06020a0f1107032301091202150708040302 79
    0x1094646040183e101100c24201f040c142e5032030f84140e10420f1607148064001e051200010180203004050140c113510209900003440654505120150f6880c002010000030960380e01c01101008481c3d00200b4031848014001e03000c1c2ca0b03e52840d95100c44098a0841c1d2219030800e001070040e8041104010b20b40b8160042c6042840715220b403000f5101c18049003d11060030010702d001510861814441d41c48140c1c000e40d2a142002000390101d001c0180c1d0100c2581003004002c0140d440000740c41c0d0000c4186009616000c152405601501c03180d00090109403d01c190401d0781980020381d899184858812203403460050b00240548425201c3c106560707030040e0046003103e18a04441e07001070200c0300112078620900351101c2040780c001c507610800003400414041e10059102090114502c4c40b2070203000d0305450f66076500000c42e08104042c020401602080410f4002980105190340d04405013a0740c6040710718000751034081d42ea07110321a903c0c8410218448610404005210300e46c10b4004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 372924226 1250 372922976 372922987
    0xc020607020a0b1522020901091a030109020c0c0a030b06040b010e03070608060d1a0115050a0e010f09050a08060619060e041d0d080603120a120903050903070b040812040803 76
    0x10154010950380381c1a04200c0900d084240307140d030f0206030145d0303000201c0016258581c5400047c0305070391a502806056100c0031400240304803400450741115650b90005a80c1d1070300c48003017405e01c012860865840080b100000090100c060045841140111010031500000d04015540300c2c00c418240c64166000d0781301440128001c091064004600400000d0321718120780c3c2d030110440d110103103140c00a031041d00420008252181c16080100c003420a90300b01540036100401201d10210759034100801820640c0e01a4000d03088440070b008042d02030b00080361aa815180e843c0c0040d10300500a207440d01801801e00072101d9500280e46003507032101c00042c1d0150410019108421150f1404140e15070507240791241040b04c54115401900d51a180e49402c104050500410310150070b41d45400b007142c4030342280e1140e0b604002e03000029000491105509040700c0f00c1c001d0501c01501807180c0703000071070404a29409442240c200301c2c2101e105101c00c059200c003d004a200754155944107009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 372925476 1250 372924226 372924241
    0x71e09030813170a03020601120203100506060f0f090a0524030703060909150c0305091213031403040f05060403081804110406050c06091c0c05100903030c020607020a0b 74
    0x1c04184100300b6aa072207190325211450f50740322140c160000340b54001c0002c4001c00d40c061000c82c0c01401c250145101407820341c0c010035140d030b41d0f80303241000d459a240c1c005142c80e50348900f640c4001612414040d26600c07403580b01c2000c1c3d800024900d00c81c40d10803100245502d013000306004804115080b0308650201c0302d80d12805500b0103031104090503160070011504002c1441001807075401104081e0f0454005410801102d2200118104060502c03003007000c0d04030000341c0100210146101142d480314042129060003c03070343c20051408034042280fa400d420000046d03c2a90021a8451842a61501042154825032100920074002070220b034110100d5072080042110000c0d10104a000056180c602a58010381080303020032400f00c0d0010960800b0800590300111510052a80d501c1c0b0703406802082c60180d0b805401c200300d091400d401c22400744103407000c6549000d400c0c4400380080c070380039010705800090715005106036400140c0f054030000718135040c6134003d95281d095844828 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 372926726 1250 372925476 372925493
    0x50303070807260a050403031808030a0f020f07030f1a01150c02040f050a020a090801290316060e09160c08160807060209031218010503060103090b040506071e0903 72
    0x150f0b1002c2140d9001c0c0043c40d40045001440040340b40c0d035501d69200c0c158034019100d906590300641c04d00980c200188800d4000100320752001440d420500034028510038200e1030608021401042c80c001c0d140d0010801042c8040b440400b442903205411405140c070315080440303002d110301c41d140b03541e8090078aa00f90051601800060001d040894080c0c0e076010040c060350402c1c0c0b074039200355500041c007400f205e42c403c8280e409403100300028490b0b004a84900001190640c0200681003034a100d0301e69281e40422090005044030501902a43d0795a50054903228a40440c28015580200002d0340d981d0707160f207481070901e010f44400c175004d0340d2621450203d400100300703030103007031a080c5146010542203000792142c58807e02c80941d8804400c07041c1810143e03541e034440b090450034040c068a00f0035054141a482501303107003c0e0b84035611100101d024054008000d02a00c20803801e200a111000c540380348600303180d80759081207403410080a031383c68203000d20507000070305e084400b0b00006585d030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 372927976 1250 372926726 372926753
    0xc03060d03170f090705010c0b01030b070c14010204030203061e1f0f1707060c0308010e04060212010e07030b01020706121a040c090e0601180902070f120f09050303070807 75
    0x914107000000040d00b8024200201a90781450001900e03041001c0607000308503020140500f0300c1d00b5107496000390345e00c611400703041c08010054442c07500024241032042031100800f0f034100c0c000528121003031034070034000d500131b000c107900a00030800044c807455900030850300e00a02e1100781015a503111403401341685060a200700c08a13000c2c01000490111015054010b00102e000340c8626000f18440030f49040d0341c5511820074004140b0980c004170f6000300c8400d0450b04041039070002550341d441c1820080c400c0785003280c1d080c03401900102d0061031150055118184640302080180600001640d03500f01e0b6204100c005400320b008580381c50101d801c040104403000c010860308841640004054800000003d070014480000c200415800100031030f400c184282085030740241d001402041204080c0501d164803030700020b05004102140e01000f1000d50060040c0400d509145802400da031002d0180c0381c00034101c6840480c0a240c040111038000758031140d0280f420000da074902c4203c903042e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 372929226 1250 372927976 372927983
    0x60605190308030a11040f1806060219031e0f170108062805090303040c0b0301140d0f0c03030e1206091504030c0b042303070309090e0307022101140c03060d 69
    0x1300c6010805c0982c020014001400003696200e00c61801e241940d2490119800010120782c2002d504000701900881c030f5a0001d0010804285580742c28101921440070303c3c00d0740b80500c003090110004143d8000003e0140600b595100c180a0f410842c40ea110a00300f8041c0c610680c100d4008541e903014021030000c002d001c110201d17181422000d25100881d0800c4403001c0d419040001040f041010011211000d04514061a030955052103805129080d040f00d000d4040c0125100344030502c10810040a04030350f002d60103484268032464001c04203103541540350301070410036915030705c80007000c00c0071071007600e05400918070343c1a0030b1101381c03044102400c141c06200c0403926103000320310920b010922450040180c620000901a04201e00a041d08441501030704140030485c002039211a039003040342c4014074041018100f41c400c45086219a41000f58440fa0f05500040e20801c0e2804c400e1881c0600c40c000c211341c0c41400715814071a082111644250001040007582900d000001e004440f0700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 372930476 1250 372929226 372929231
    0x21f0f0b03060a020714030316050d0920041d060408070c0510031b08010311300f0c010903031205091905061f0501092102100c060605190308030a 64
    0x803080401e0429500b40c0342403080a030006450814030046504030030f01c0b200210300551661501720f0b905404511000180010060001095400d080e00d80d08950b007596080300c690315030503000c40300300d0940d0103600b00700e81d0190b414805a50010890324000945c1291410084c1181d81d4031503403880d20540c8554012102082c10002c0419280c549221004100b00b560701c00040088425040310390342e04a595008041020401c01400028984070007107602000968400360141c40a1610750b045180c0d400c1e202c0b078007103180d4004d270142c01e030005001d4103030015800641d01c9440c0200011200d06407280009401b20b011100d984800070072a5000e15400000c00041d0f50140880c10303c0a1940d9402003019034055000005001c00740e8101903c2d04440d0601c0c92280614074500000a40341c3c001901c0348608048003040c440c5119100c240c0703565880740c3d0081c10140740c40d0303225001070b0400038500030651f0038914014010401e418981c0090008942401d050300c212859a6a08035075030303200070004100280c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 372931726 1250 372930476 372930491
    0x40501030b13060b13090b0a03060b0a1a071b27180f060b040b0108161e020d020706030203041502090319080406020114040f06050c0c03190906021f0f 66
    0x64814070010f803150140322540d44c4549405c00c00143d405401c21503045250038440700d806d54544891b2011280c1c005004204041311800040342051300fa8400d9660b502a09001500c0d11a104001d0805c103200d607851400d203481d031103150142c0365298051302c01c1599034040501c0041c2e40526588000046d11440404d218070030185c10a10030203800000c41e85e00b03005250342c204000f62400f40001000b0217543c20403002c10004002085070002908000e14842500300c60034400c1d104003207585203c42c1a4140350f80c0204802e9000b0340c0c805007110000700500495201245051280c000c44c0c2c0629040b185850030908584c602000030b6120a220b0780d458458540402400400d01049580185c06030301010b0b180c0d40b9100303020342941c491403080b0500020803800c01c00090081100304210070f0300088000340d01d0395601c0324208503109100d010f005500c00810122902840c282050794400c205540701009659560006d036580d03900010f600c45c2202c80b0100d030304103d0010b0703071040e4807100a02c2c401007402d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 372932976 1250 372931726 372931759
    0xe0307091104050f040b031b0406031709180c030402060d1d011d01150b0702040e0610030c060c05031b1e0a060b0904080f090609040f1b0311040501030b 67
    0x4900e40400c4600740c44020808002501e0804201d1140602c01c1c3c406214618100000a0722154032401c03400c190701030ba04041d03615840c2c90348014091a40603070051a4129070500c5e01205c1d40148010910a5265180040d40810703004003103406818442070300381c2551034079403c0000b50340043c030070344903482d6544100c000003244101c5440400d280503c0000745c0c402d200d00464071107460300c403003052b2a6030401000c1c900700c01c0071050342c0003101e00c1c0d95107a80d1a0025407001401400c80c0450200e03040c4988004d2215070084010781c3d100b104d126031500c0c2000d80d503c01094a0340008004068031a4206200034000518240308240045004009642606071100c0c03076224034044620f14952582d205003248000c001d007500c140202d15000312110402032415544c1d062240c4213500c8000b41701900850103103031940301d01e400d50f080d58400810501c0628003510702070004001e041c802240ca4580c5403031100040d03004e8411030082c1318400c8951441c1c1802c11006502408010201c00c3e0000b18841503038280 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 372934226 1250 372932976 372932981
    0xa030c05091c050106230105180603011e0503340b0c0a140304260321060f041e1a04061706090f071517040503300402010e030709 57
    0xc049aa0b026001e95003181015402c45400e90440c0b845843c60a420303020942000621080000302482d01c41c0c0d4840030300c4e4142e07200d1b076034011089400220200000ca44400031000b4400c08040e07500d20792020590324000c040d40d52481442160208400b40c41044440440d5a02200f6194208112214082d030b502d15807800d030f43c000c103248203c030b0308030039464400c0000316020300110342c0044000f9810b082c2003a000794515a20302626824148081c0f8001d440002c040c41911640c0d4040c403641c00b02c07840800041c20312180100c1c1c43d18420300140da484070491170b0900c42c5800c41d68541174070701300088681c4c0e280c200600d80403000125002c076606000f51650b03614007450025110400f41c0c502c010001a00355840c190000e4150800c513000843d240004000c0050039004544c6202c24021240c81c1800d82503440c41145a00603d246c5000400c00c018058000000c0100c8581035840c982e00c0d48803104c44c2d440030303001c0701001b009145144c8013090140d031091418038000d400090594800380c1c2d64001c000704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 372935476 1250 372934226 372934249
    0x22806052d06040c03060b0a0f09090501060201090303060602010203040f140109060510030b09190b0a020c0d02010b10170123090115080f0c030a09081903060f0801060b0a030c0509 79
    0x1d41156030303420031074241014021041096103a0405006490911980400c24003891148a04208421815603019480740074240b00920500700c041195584800d0001d0213456110410340c0800d003811800502e40e40b0510840c1c2c400c03074111841440c0c0964560b0b6425003004001500c0c000b941d02c614007000420704511800d405818031004c02043c96143d45011185c001c0d00800800c05504114042c98002ea104042082c006500c4030960107250381e10510745000b40126103103500c0611606e00101c20103901548030845064045800c0c40d41c01004070310407180300102c1070343c803854022410010000c10300280d0440e000e480454504500550800d0042400c002c400da000d010b800300015401003145402500081e0401104c28101c0e01e2803804020000043c80301401491003255504825400d000318001521082c1c0c4900d001c1003591b8541507001800340c1841e0151079400081c2240004040105214940803100c0c0c03a40c84505014802c1d500381c00030a5010542002c0c0402000702d50020781d5005180342 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 372936726 1250 372935476 372935551
    0x40201030c020f071d0a0b01051204020a1503050f060f100c050c06131703090d1202100e010209041506080103020607210504080f010b0f10090b03010b03060102280605 73
    0x80f81701184101800800000307480c0b030fa44a45440004a484d036030100890341881d01c0c0c43c84603000e40e1950b101096003410998028004080c10ba0400316215a054000c2401030090042c0700405441380c07010003000b4140240c5103540054020740500d03a66003e200c2443c60340d80107070306031200c0b0b240724008100c2c140d01602102100b04e0fa8001d003407200a0081902044145400001f1401e01d009080412801414072402a260741400c0d142c441d0000e1003003004428515602d0300030320100e0000d0142502039000025858400c500f060000300752050820030040c00c40b801e6580b2468030740d29503006d22103c1d501000c001e603000e541100c0c07080f40141c0c030010044001011036030351560707892512500300d0400217500c80000d03459060500e00c40d41c5a85a5402254041c0d0032648441c0c0341401107c19112003803150300000407240080300008070594108041c500c08c2c0d9003a000e5410005d200362915040c0400300e2900c02c60110328243c00c5000c119540d01907035014504411481b014120440d12690040000714400d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 372937976 1250 372936726 372936749
    0x3010c300f060f0905010f1412120301050a060813110102120c0d0e060711040209030c0a0312080c0304030f080c0403051504060e01060602100506030106031205040603050106050c06040201030c020f07 87
    0x400120f014021910028400001d040255505260103004034800ca44501d911107501d081c0014035513501d082000481254034001c4640ba00780b5504a942c06410034841c0c00e03c035118a0000080b11030184609520414050000c44460301260341d4044007542003070821411882941038090120180e50010404058131100800391901b6414006040200001d69640101014407198001a8514900c0030360310b0b00442d005610f481c0780c60042450715002c0740d0000d13802910488000305100d0103882e8010703940f04030361381e0800b103949050212425100964000700000d00c05059103404030300c102185900301c070807800c465151a550351180e524100d1119444151100080280030401550388202d050f214003039030081c80b206d45840e0010751916503414017003041380d851b600001c449a4080d070141d03002d950b100007969181c0c21820f000070219085400345201003484d010010070f0f190700800641e01c034428000b000300441e0740e41e81d004501038140e907100841540b04030300340703a60300240a00c1100050007110020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 372939226 1250 372937976 372937979
    0xc130902030a1b051c0b04020f0616020a0602061909080d060801020d0c180302011209020d030903171806130308030c0918060d0f0f1a0a0b03010c300f06 67
    0x4003c500f003102e41c009842451040786881e0340da5021300806810540214040d107240d510350012a40080000c040540c0c084400191107070400320382e03081d01d40d14600035030340c100070345480d090140d0341c6031402da0700601e03207540c40400d110301442542c001e010440d103d840002c6c14060450020000c0d034582c1c0c1c2001c040e0741d40100714898003c132941308450302c032082458400414100c4146c440b8602d4202e00001e0304110900d500e03104080026001412180e9001d00411143e10341800d0040c100c08850208440e440300901038901140c840314140c4000ea20060031003c12042c00e401000440d520000600c07452581c4020300102098009029602c21010200300300e6440b6203913410410705003c84003800024031101e02c140603c1d0307200c040c50101500e80c000c0003004240756078200200903407005c41d002000c01c7c0d2243d2075a86c0c080e00c6440c402e4025007031b02c8000d0100343d9240003054240d4891410050008452681010711000d0003029889026000342036012201100324000c41507a0020407070041c00c80d1200b10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 372940476 1250 372939226 372939263
    0x1005070f11041d0d0c0b150103110714070e010503060a18050604060e12030114060702061201090c0314061813021206090706050313150608060f04020312040302030c130902030a 77
    0x131420050561901c180c3d441415515001e440c000a042d0608034070307001004c01f0150b40694000c0e88104100c400c543d864404c0c49c81d2200725485010000c1946d0300403904006160340003410814180c0d00018041d0109503914030041c0c005026070f4140b5580213003003c0121010400c00d0101c90b0280d07000e0b82c4042030214a00005500e8454845566030b11414100010807480d2402803044035a92000c50f041030740caa405000140c914001c0000e025260b003001c4d400001d410203554401d0a107a480c0b07440a1203090038004845c20400b01c01c0b21199080350640045500c0c503160080401c0c2e01014110240102c101244c000c12024500d822a0450990000007032144862007000709100611103071504601d5031400000520034a20b4441006051800d111940c0404510301d401603006000c146003100c400f840d190351400c2405c001034409900034002c01d51002e42c80400041242c0a50380c01a00511500300c0b0b0764144640d10001088060b00345607101c400c140140d400b4801c1e203111501803542082140340c03011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 372941726 1250 372940476 372940483
    0x313060501060507080d1503021008090105060a060e010c1b06120e0a0c06080604020d0c020102090f060405010c020607060603021224040b0f1e01060f08061005070f11041d 75
    0x81098090003014820f84c0c0010f40d20701c0496a0f26502d588000c40c0842c0e406d407614054078040c0d00029030182d12181c590321403552002e02c0510401c0c40c3c42c003d21154940320103014201001c1d00444c80002c81d1402c1582465019039250b1607213038462a007200c21500c018104502042880c0c0181002458101e1803140184160050f4200401550058080c2c91220fa40d0315885036100e12a1505200c919000222299100e0341910612200c80201340400c0c008010000d0007940240c240c6445480c03075201301185818008141c80a40c8e4061710f5880800d5255000c025094000c00742c1200c1030350b100e00021006841d0384810b25804000c01008001c8070b040c186c0b05020500c4a6018090240081400c00010600c14901c1d150814000381c1400c04513100e00c0310b00144107442004801a00c1c603c50000101290b01503041c5089520303d947d01d0078a80c840d0340800901092404402c00011802d200c02004540200780b10959284215409000e41000002041c01d40e06071008040c0540700700c40d0400d034280342c01d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 372942976 1250 372941726 372941729
    0x30711010f022710080406020c0106030c0501020d0206010305030a030e01090203030d020a110319120e070e010618080706030c11161809051c020c19031208012304110313060501 77
    0xc0400f41d204501800c04030311891078001d0400708204c003510108042c41090f40c121804040d10b08001e026240d2281030500c1c030b100b0244201070051190069080c0072503c0403507000d0603654042c01452070104d0956049001d407000035038042c000e5580e08003010040e60708000505503138032188005601c1d110a00302c0580440c030340d0209a242600704020001c800040717002c1c10714011190781030486e28654038402e900300038400344085894034801c181c1d0100e981c0750b412070a54101c501943d00c084034000120602884075a151280d10000e51000c201846803600a4110000daa40186032014020040e240e9aa1500403003d24410359424404410b2160940b00d8244040900c0c2d04841440100421f541e129516400400c46071508401460200d48140c0309100d807070a480d1005000c06541d001a003049411881c00b031008448908045484c02400746c0501030240c1210340c00d26101e201880d459203000c6640000782c2201e030380310365200f8101c40124550009540030725641214a030b1156142e14114080382c4c0c06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 372944226 1250 372942976 372943027
    0xb19030c0603150609120f0218040209060f010e10030e060f04020109120206071b080a050f010c080609010909031407050d0f2c0a030f050a05010606050703050f030711010f02 76
    0x1041c40a10266401085c0c000480385565801c1042c411503044c80c9400b41d466820080d8000d25070500c4407041540504441d0040b40215941c0c1c00d01d84440f010814462848281c003404100c103080032245901e4840c04a250701001030402280c00b0f0341d0b40d21842d04200e0308451110012407110280000d6503401101e0700302034528040b18400280e510340000d041030013601c00c0103200641c950604030700030b0004400030000303000a10855054650f10320b840c03500d03030449a92400e01903107001900c4132000d202c0c814440c0184000361a10710540d0030030000101404800ca01a000d00404840540309480004010079041c0e000e003014100e96600d412001701a02e0110080c20100b1040c29601c4100011101040b80310f46c1e81c0b01800c081d00403100d4046085000716500140c52100780070000d00912034041350796484a4860070081001d240c445006850b540511603010740010414800100c2c5c5540c00c200550708091107041060714030302512100ca0942e40b4078038800324082c3c1c0200b41c0c18a1903c020b5894814442c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 372945476 1250 372944226 372944261
    0x12020c01050f03011205120a0c0b0f0f0402060307020a0b161206080705040905100207030e0a2403020c0f1f1505280f031b05090702100b19030c0603 65
    0x528041c0800307010601410304c0d170008210070b640070042c04100306401c84c10f040070300301d444417000d06024054003050501a00c114071400009079800364240380f0b0900c0380d0f0800d00c040c070194455809101c01508010054419886480710800c0810440c410980c850700301c4606c030110414610780d00603d04513820140380d00317144c10540c0604c0500c9010034000150b039001c0d640003a1102072410218034000c000d1400e9510548006459805d2541c00507440300080f0040e582c20f00982d9803811300380d08401c1c009050048000e810203d0009403481382c0c004005020440d0100c8100c0e034803803010a820300341d00c0110250883c0190f044201c00d0342c61806007100f50944036421324501031806011541160004007250081c3c01d844510200b0803c440c10320b08043c00200c545072041a0300d91402140e0100380c440d043c40780702c42140c1d0001e0702e4030748550000d11540c40d0342c2c0580140010a21000090030b002204203a208800b0700300b915441a030b00303243d040150b01403440b42c0391040c40d007000642101c400240103041e100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 372946726 1250 372945476 372945487
    0xb01030e0102070330020c0d091502030906030406020712020c010e03010e031902070b16023f120f07061401080d140715090209070e0d060b120a12020c0105 68
    0x1c2e0490130402d1410115003265096001c2c18140c44620903404402a05c564400304a074140360700c0004500c20501c2242e12000c01480c0c46080714901c16515811a000507072041103e02d980d0300b045000342d600030344a40d01c00750a00f4410b9941c0d1407c807064202040051f4000344080000f9a0710805000b05c080050b0000c0101421781504661244039404281481c0011a078071492214420400c2d0300090000d005c10b5a2260f02800d400203007000041416031040c0c03440c81c1c04900b0203c8000341d01c00031145d05c3c070700c4400e855603400240c0c5184031520300c105101e001b8050f18100c89100d88004011660303001c034440d540c80c4981d1801904481c075800d0300c410600c4d1141c00510203400c00150010050b80302d42410b02210500d249560074501c1040402000c52800e040500c0d40400603406c540c036414801c035100300d51982c80e0101121880440c212955010300700c0c3d261240480c0341039016000001c00079152856041c5040441454004010b20032503c02051500300704e00d1560502079070500b400c00f403a14900c1e11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 372947976 1250 372946726 372946733
    0xc03020703031103011a071104050103080304030816092102040c0e09010f12140a0804090507080604091203110912030c060a1503020120070608090d0908070608100b0c010b01030e010207 81
    0x46d1080c811550150034005000c1c0e051045810001c107150030018014001c540e103d28041d440c41d00256011000301d030702440440d0b010395513120002c82044182e42c50300c0900e0700d0403007113252984c411f0380c112042e00c171001c5d43ca0b40540c549000d20640303000d154071480b80d0003401c01d003800540f0905a00194041c50320900500181d0098204c4503c02500500c1001c06041c3c02c41c50a401c0032101e15006118a00000e0001002c0c0743c075030040ca118070b04580340c0e10039598070001844250780080100a018160030705644800b20300035881024520500204d80b403d2000800215000142800703c20300c0a0b84045050f8042e403508208266010355254018001d13a49603404000c0c6035169800300034180008000100c0c184000403070800e58400c921411201c02a80d40c01e809409c40d641034562510314059484020501d070b000b05d03280320480c2d03151002004030614200f000c96003444c010380101d000d146c41c0d10000448007820005803401000050001a0220030600054200c035010030710f10300c09900610182011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 372949226 1250 372947976 372947999
    0x204210b06040510090608010b01030f0507021e070503100e0d1706040b01120c0e01020705032a01110312010602240a09020102100207031107050a0317070201120c0302070303110301 79
    0x86400e450203d940d0b200c40401812544190304403003e064a0500c0001b00240150481c40445100303032404c02035100c1c0c1d08040c8007560011144c0c0c0c00581c3c80400229003041c800d00d444da007242580d50585103000d84400010741401d500d1411303c1003164852003505601ca10902515880082c01d00f0000902071203e4031250144c4002440c051141350b135801c1021460740110740450354006144800c00005901902c054410341c42503007242c3c014482c0c200085a45e00380000c082d00b03d000e6560004031000c0b10f000c190755146e581c080d040d80c104030308014401107002c0200090311964403035419213066581031907402441c0006035003030140003100c0400888212110078413015003000000300301040754005400140d140c480d10706c4c200840d261000030f80205040d0311419171804061584c0503034070072641d01c00401030058a07a000161103555000c0004c507941c0188001055105e20605059800c139014583c1c80044418540845001c03d070005900c10806034544100c1600b04940c01070a070465042c038588411 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 372950476 1250 372949226 372949231
    0x51201090b1f031503080316020c15090d02060301060203030702010f0908120a090206190e060f0324040218040b030a1101030b0a0305032d0a0e090604091202010204210b 74
    0x1581225100b4405070940b0a4200805001c0b0825440309095640d140401040e8170494580c107021100d030407095940c80c07000c00d05446500e0000c0505581402c9568500750302d40c00245501c1e400041c070400c3c080181c40b20000b0f140200131b02d130095504c80c079100e00c0103402c0d00d00403581441e01c146400e12090002c1c3c0801d003650480980c47e010b0b20000e0f075a0100401c000c00300101c01030351000000c0707511501c0103490034130911a81900d5407401107103442c00040c8041303030088005820340700701c00780f0000324101100c0102c6166032510a14400c0980b0030100860304070380c00802040401c0060b0040801c19003050b001d2448410300a5000713122000d42a01c525441200d03004205041603140c40014030380c1c0d503e408402005e1500182620b0380c1d640e00262081c122403d0211201010901d038501040610661040d40c078044e0058031480c00445045c003c0281100c07006201c0c984c02592101a040440c4000c55400c4121005030001a0742c0d9052820040c0184070601c640b01e5019043e078a41b00005c0e191926054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 372951726 1250 372950476 372950509
    0x3060a1d07120209030708030a0f020312061c1b0e130309090b03070323010c1d0402030a02120709050f040e0705040914030a0c020f0d08070b0604020d0903051201090b 73
    0xd0b4a69030116000003921910340f9540e4180710b1503201250101c03020000b0168503034281c40307980b0174481d036050981c1c41e0f0085001e03501c501d401041c00515036003043c0003900c020184204c0099540303040c07644e9050a8034005222603100c407031300d0441800b1765140041490780100d090304090180094680c0c3c014610105400b40c51501c60300c481082185480030080a4059944001c05001c00c1c610048020101c6401c1c1700c41c40029070a20000c40d4040303000b80302203034050524400d02103d80004405000203940042c003032a003180d5003042200340000c040506240030301030030341d80d05806624020030040321404101c1064492031400c84184840c000000d81c0200700d81c0e040c0c401081d44c0c80a42000c0300c4000c034400340ca10150000084000240364000f0404182030320849e811046540c500c01482144503507090014441d050821032000030484c040c070391641c0020005c0001d80b4140f0b040e005602541d618600490200c2c102041d0080c564040209090241c08460810031803441a1800241281d91011603034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 372952976 1250 372951726 372951737
    0x6080c04090201091505070b0c04030203030703050715061409090c0112090215120a06080a0b06060702040b03160305010e030a090e091c050a020c09040b0127050c03060a1d07 76
    0x30700c21039004640c8031008101200e40d280c5030715600900601581e110040485180341007400080504010b8070980d0260382d0040d0046090400d5558141c82c940d10031102540e010308214000c2d80031980ba40281c802803c403050412514001035014020003010241c211100da0300310900c40c1600e03991100f040c21444242241c0419101103500110700e03000d032046104003100314001030304004403034102c0310940141d508140820103540c1d1030a0003902d420590100420005621000c41d0191400c04081c000d0280020f00000303100300c401000a14100c1205010f6225424100c0b040080c0242807003440c02075040c0002035841c0680c5001d00070b0403100b9500410040c4045800451042c0342c0802a0000501100003445c10b1060044c0016020f5080010303130000612071030000c10b03800e040030080c050250394003c00441e03da9080c810380017150103134cd64140074910130000f01200c4012071801114000c0300a40c14035945c07400d005040c4481e020542d0040300c000c40154281c0324081026400e001c1e88845d04d840c05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 372954226 1250 372952976 372952991
    0x5060f060f1e1207090806010303050f0d0b040e0c03070b03040b010b0a120524041a271311030708060703050604090b040507060f090e040f030921050d0306080c04 71
    0xc01c2c6440c00503030350348107000d000310f4125101c00c0c000312030901600c1d59848980960380d4510149039504803d0000500040c01402104451003c0030098091070180f00c070041200418040840c088a082000a08640c0c2c0040351000c03407424107001110180c02e039100e00d1403661070b1984420740341c07800c10b115020303103440005081d14803180f084203040f40d5000c0f030210030f0045007000d60524041e01d030701529070003040040c500c45108a1034035103d500088000b0254070320104a200e001c120000d0b00c030f00061030803a803044655480040880800c0b038071501080c9694003c0c0c0fa040e0502d10707200300c07100000c940282e00c04e031024002c40360005021030317026550340740202e21959000045030141610070340c010a00d42100e0203020801002042d048255122959131151211400400b02e45a4100c0c0c0b180b80e0311540e8a001240c0814070b0b00c042c10000500a0501c11201580e520a0341004070f0320401c0385030041d49045a00c0c2c02c100080c000e500c60240e813890180000c0d401c04040c140c817480400c8000307225503a00d000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 372955476 1250 372954226 372954247
    0x62c0f060f0309030d060b09013c211e020a09180209030d030b0a170102120c042108030609060301090b0c07230a0219080a031205060f060f 61
    0x845144072005100300da1a4203114620941c0ca03080007800524040c10546c000c00d0080c44401a038251070030503954224504008820054101000c1e04150855645855810f01d03c034500c045019030701d0f9280c2d0381c1b600107181108801e05500001c8645081e0705040034092402c003000c160898117440300324040165112001801070f51000e1595000b6429502d1114900310403070120f0b405080d02c04000c0d01507d407844881e040440c12500c008000da03178820b208a10500502d0808400b0f00d0003000100300061900071542e45101140c1030441c0d83c01404540044c082c40b00f81a022640c00850a8104850344050384540e034070780305400004d00c1d040c008c6d00c84030000391040d0f90940000580036000500b03140300e414507020041c42c0784c1c4204c0b801d8403000700111203419491500b80c0b0b20708441c035a000c0500f03014003240d13003040b692070364101c840740b5140000b220204505d04107000c9410000d110b515480082000f00300c460065540c001c010f24805e100550f12a0b0307507500c5d01811a800002a039030110b03910001c540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 372956726 1250 372955476 372955489
    0x1401060c121101110309010c0305040b1303050c1b1207181a0409060b04061406040605070201051b070513050907090b01050c03030406021305030d14030a0e1501062c0f 73
    0x640602d050341c203012004e40c141d18444021402200c403440207005180b00140240c060321010703100246030301007030b00026491802c0e42c0c010100c520b100f45049443c100000040c50300e410000c4401d021069610503191980e45880608215217503800e4010f400341c0352505160000100c800d0b00000072682c1c540043c0345408001115031203004800410401191403681401002003090030b0013540598a0316102280c513044104007140c550000034402c0b841c003410030f60116595004004202d06000c2c05000c03150b078080070000740f0b039101940540245940c0d4030b05010008148210310061381c02a1401050298a41010a020055500c0c1c01c4000c100c140600c0012034040c030410595140600011060204100c0b01e80c000307080d080c010140d181c5541d5110810161110981c042980106847e100c00300301c3d103e413800245600c4092284001003081e18075110504044040840340c41030465000140101070300f0200720304100b001410203881d01c603a100c82e00301c015130787c1c6078100b07103d8020340004101c1c40e91640c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 372957976 1250 372956726 372956747
    0x17070f0c0b0901061415070221030c100507030204030f030f020f030a1d040212040f0804030f030507031701060905041d0313090c05030c0d0209150c101401060c12 71
    0x4419180e142c42c040310024002d0407035014540c0318401d003444481c110f1070310005818010803031a41031494211a5402c00015405014003c8810030180303010041602092000d045903410380000b80145902c8120308804440c0c0040240342071500c140300902c0030460500c0d01002d00c3d60701d070510461009030300c8020f07031518180d1030040c1541d10001a00007141c0d41d11191030b4a152004521110224059100b000240d000b851401c10084050f0030001e404180b1041844d0340c03040c010b0020f03030320300794494803040301c1c2609040080d0040b46000480d241016802a448840d01140075015501e07541002c1d4010003001c82445001c0c86203499203000500010b00c01800e00e8010701c1d01c0c04070b03a90740404101194401c44140709031b883e0305240c400d00c00e211601444c1181d20074111030324650300d4135115000c000f0003904803215013a001034400303021301c00583d0721000404540c40c10000038007a03907900303120000030b032101c0001c60290340c91003000400a940c0c00c004101c0600d07901580032000b0102501049410301a81d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 372959226 1250 372957976 372957983
    0x1c03181106031e09010b0102120403170a0c0206040b0a08061f05090307080a0c0503070605030108100c0e030d0503060f01091511160e01030b0105120c090601020a080d020307090617070f0c 82
    0x10004e00c140280158400e5041040030b8080d50755010013419009007034003651102034120484650f49107010b080c8000100300113400c5041040d510b0f98203401042c20ba03009a0807814070207030000350007210340340c12408150344408112501c13000411010101b94001c00b03850390402c184800807071840b005640070b0090102038100001103640181d0207050200256910b84100c034001d02540e80c0100c3c04510403c1103a040e101070400810003006201281d00c01098069040820801128440001581d0504c0700359040d90f065030307030282c503410448200500e0408084040d414441c40d0311040082c0300000c2c45c6042d1080813418144482d0142e041c00a050255030b10b801440c80c0d1401c00082400c00481441a040c1d0f4001d03605240c15a80303440a001c5400140041c03044c4c40d03809086403c460b468000415580a44184156810803615541c0c0b80c0f9103800c00101c118525030084100b0040b56403206103200240310700c0c035250300401c00620300d100100c1c0c00648038000300150300505080c9140a030380c0d0408541e03030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 372960476 1250 372959226 372959281
    0x30604021c0b0f0604030c0b0a14120108011104030308150d120201050403090e09100e010608030403051e0331051008062e030b121c0318110603 63
    0x2034214070030051250000207403040e0300003080780e45281440011341d0b007074030f83c0002820f00460600d00c14030f0280d048500458200000c488000482000e0400503140d804283c0b00403030101d5060004071402e40d03081c0b000801c4145000d10080021070703030113206590400c085448000303120b14180041039954058150150214a100c00c540f204c0f294150320813407050340030380e41c2d12484070785400c0b03041090b400558400c3c4499000080b450b800304055840442c0c03006045d0000201c1e07035640e4002c642540c029030b20560360340e003200341358102d40c9410800303a540340140c1802443c0360188038150745030b80d0708800808078040210510680840e030f800706805405404000c1c100481d4045501009014010031166580030b0400090500300c0100104214481e100d414180c1030030180a004040740248000c2c0b04459000c114905820200701040c4503c01320300440150b01c8520301d214913805000d0b42e06100340a01001081c00381030010805150381031b4684141118180d56940341e291b00c8590464040c64805650724 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 372961726 1250 372960476 372960517
    0x3200705060322032a020604051306050a120b0a060f061b02030601030c0801150803090625080c0d081005040b13050a0506180c041205070b03010806071202091503060402 74
    0x40c0c00c170301d400d4110001000401c0f40d205901c141511001e503c600001e4004c034060106000c0c52034444940300c4a28024030703000880564800c0001c1c00c2e104107901c40c1c1241d030b03940b400402c140810403101039842110004e040c00410328007070441d1810030091040808011a07020034120b401a031310042e6400940041c00c41e0104c1d40c41e41061048140b0394410f209003907103401c50f41c070b40030140791501008a4802c4001340d03007010b41450501800b98001c0d01100c81d880026901c08000814000d10090500d00940c9116212440701c1c043c0342c641500c10803842d0034400180b0420002c421072090900540d68161000300c0e188036201c008c00d100100c3d4404501c99682000100142c60583d94030a5206210490322410081327a01d141080d02c01d0400d4440c0e17840084200000d2142101c8140ca900034a4420022240318581d20b442c007442c01e4000303030400091034001c01c00b402101940311181038200304094a0440c988281040020104000da10784041d0404001c400100c403643d03641e06480001800e0a0300d0076005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 372962976 1250 372961726 372961733
    0xa0302030105010f180308130e0412020d1b230a051f09030909110f1c111207030c020304050411091e031908070804030302010903200705060322 63
    0x9410902030030f40000d0090f10102203080c400c0c00c01c08280e6080c00542c0031200c0c1103444055103503104458520760071170042c400048404586c0319030f9120314058000e5a0700395002c0a0001c1c05e10303421a1040c0100309000301c6d1100d00b1705800603034074941d941c80081110a540a80352103400071a0600030351070340d8001c1040d80341c01c0c420701290f0001c03682250204004007034102c0c00980101d82c1c0d03a07040680014030600e018094048954130101e0341d0390b04000c5084c200311510703455039500d6004620011340100203000ca001c00a6440c0921250b18845168650520102506041303180030028001c03410140c64650720760826000f8030444000e001d0190050066a0f04c0718200c15407980646e0501d8042d4001c03d4030b900342c5c0080c010b0344009110008000c0c094032060001070000e0340401d44810b0b504030008200540018061400400096100ba0004500203480e428040c5c001402c042034041208d13070081c424841c000011a0503420740b241150b0190b100c6d224955802455460820808800c903040040d00c02407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 372964226 1250 372962976 372962981
    0xf170102030f13030306030605011503142205030408010207080d0b0301020306010e010e010905120a0c05030a080a0807030b0607143c0a0501020711090a020901050d0c050c15060315130f030c080a03 86
    0x920070bc680781400280c440000b003912000301100c80904003040b00c1042a00d580d41c82043c80308840c02001246c0c01e00e9290040b407422607000890460380d01d000014545510f045030b001c0c5100e060340440c000c50440c64600c0010307004403610681c050401402002c2004168000e03a0000081c00c070140c0160a0401c01c0d00d00d5595803001f525050320003003030181c00010b41e850009000605960300c03c480c03d0901c95a210b0580e0540d2000d04500b040c903407a03441411141c3c582c00007030030ba00303409240406465940030701100d0419603810103503c419175104480c40703400c11784600004c44003004107842100703520103030850904101c400007000b44554000101441403107000940d022004108483c0002503445144605040b4420401580d02003881403000c4d80d00d482084c0d1202504884c0c2e8107150b403030140100192800c0291f40d40030f0181140e102c209100d06030604004401c076102c50103007158658241f13882110b012002d0040b0080045840604020400d480307000c0c5c0e040100c1e800509151a003087d000701401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 372965476 1250 372964226 372964259
    0x6190602010e0c0406031104021c0908040e0619050f040b06120a060e010e010e1510080a050705070c05060a02012304171804110903070f170102030f1303030603060501 73
    0x24248900440c90700e4030300c4c00340b250f10200c80d40a0030700c4001700316200621000c0c1d00029402c2e8600308605003403000e0b0a0490003041d00c914031501000355120b04050540c6150340001d45400e00941b0b0300e801c0d01034800182140d450540313900300d4000c54002d2402c4001805801603041c8260001804140c1c1141041804611405800428005c0c0049501c501518038282424440d015866210700e00410071901107888042d003149600340c005c0206680200071030199461030300b8420010b50034004100c01600c407417240d43c0d000807032490024038181d03180d110340c1d0780c208890240512a800000fa580c58040c000d42c40f01e0368617094110744481802e00010540000300c8100e42c1500c03900b5040e00b6418090b0048401c41d5240d0810b4541c001194070540d052000910b6041203246410030100859011607408212520041400b018540c3c207243c103180948140c03901e641058092a8014024055919001030382290f00c030400514140c036585040c181100500100e43c4058025407400740045040700c0405038044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 372966726 1250 372965476 372965501
    0x30304030f0c08010902090f06030c09010e0406060e060a03080c07050a1205010b0315040f0f0615050a1a070803040804091505030c03062e030611030115110a0303050619060201 77
    0x324150780d900705a13090f204080402540b1010a20000307101c5e580c2d41500c1c2d90041c0020302140c2c040300442e00820000d01d020381102100084590402c001c00245000d41009040b460030030104504040300414071012480c040200208000300701c800d2404c1c420464040209001803002d000d907952040112840041540c040e1869420800400d401742000160644280c81140c0c00001a0741e440d1541039a456803540229002101448048085940c40c05501d483d41084a180d13074800f85800d04000c261605035021501068058800800780040340701a01c1301180c001044503a02d40e00c42c50120007a00c5617401800100345421300000605078181d4902c42910425811200f10466403002c1550f208000c0740c0c00142c07511010000d10341e170003031200e2008000c2084444030035038a480e65142070a90f41c80400d0540c4068000c0010030a00f00b100b1482019460f080c10442240304480c0303407283e1600304610024042c903480d171003c44c116880e4a1a01300c44680d40c011840300c000e8850000a010b04045540c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 372967976 1250 372966726 372966743
    0x112110a0b070218071b060b03060709081506060d0c051e120c03040b010b0d0f0e060f0606070b13020a08010e01050714040509060f12060c0408060709050d060911030304030f 76
    0x5101d11a80d401c00b2801124192204424a06d04440360041d4171860710040b951207856031103400c0961810090140129410380703540300d2090820300d44624010004203c82103a080340d900740000c030f480e02c4084880d0f44040710808900e1080082e0190b0b0640300c0d0f5103490000400701070a0401c26815200900f42d00c5000d0301d40c0440c25120010040442e01056501602a4034034a004210f0200703a10014a03900680c501c0200301c14210000310011160401c0340c1070b10a401c294100000e0010360031503564040000c50300319003403c8840c1c80312190074100600752580d4904002e100c409643c0c1c0e25007001d004186c440c1c001d00c0601140e45a982c041e10041e030308000490200d66144450701012020ba81c10740344007a008036119a83c2c0c1301000009490450900e400480310482400b81d90001c0c000d0520070aa886e048075500e5184c1130b0040c4c40c0410040187c000c20400440601841d80c80315005105550000b00c041816641d60034125414030180c03080070b50610000600100f0000c281030f09083c018083c113241c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 372969226 1250 372967976 372967999
    0x302150a0504031815030f060b040801060311040e0703030305060a09020711010e01030b10052a07030b07050304030905061317100f0504051504050c03030f12130305030112110a0b0702 80
    0x505011001ca0107800700c45e461005400044a1107507001c00d9048040b2500802d01c0ca0303a907440001940d0154110001e107035141c0b081402802128154404088070541e01040110300040a40303458807a03900000b0105922080031a00715600c0740d828401801401d54115501c903030034a0120320100844112501041801022a801c0d40c041c1c803d04212220142c03000c0004000c8020448081c2c5c4025880d124100e104000901281c0c0601050407800c0c00c0c440052007013a0840c00c01c420480d10080c40340c0e04005041041200103644032454504541044c1d4245488044030b1030b441581c0003640d04100103620b403410702d0304074100001840291034040d50700708008012030b104410b82074070801c4602400960014541c0c03c841c0a03016180d43d030003401034050b902100001c00000341160b029600101000c0c8002c1044401c85c0303503602420703402c401c00f0200312000c4000c070750340913106000521500ca80c2c043d5294120050140d2581c05a190716001844c0c801d0301921071140d02445d4001640c281d0203054034010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 372970476 1250 372969226 372969257
    0xa05030a2c0a1a070804030b09060109180201080405030715050601120614220513020f06120117030c1501170610051e130501031b0605160302150a050403 67
    0x204441e01d2400589108105824001c50041003890503400010b04441005503002080c4910081d00145100f80351040c0b043c00c110004a00e000340681010502c1e5141952113450303841803181075107842d5820f0a01c106266524104503007075000d0001c0c050050b800c29100500c14607107a91209116030004d0300c514174aa00c0c000c0c441412500750340283c15483d045000010300a01d0f081c00410f090b10070082100300d4203400340800d50705690054402014458000b81140d00714501071945924904040e1005c81c00c18004006130110702c10184540380450701d03050103004d4000814021039030440407440c00c40e01d890b0008640500704241c00d126810140c0510301c0e00010820f0003040080c020106050103480460138035042007010b0482d440420f4202002c4002c81089445044c0c030740301010700344440016658074500b40a1041203a610800c039480038211014060645c001040d188142c0726840303d0000c14115180a0b0710b091016001106803020341401c01c8058043c980043d0301c113038440e0343c1e4112400d85001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 372971726 1250 372970476 372970547
    0x2010507031103270a03050405010210110306012a080301080606060406080c030703020715020304030e091b070c05060309030a0e01020a02060a181802091804020d020907020a05030a 79
    0x2d00061440401c00102c0c400743d45101c0180c810000700350000d00300c816120b680602e011110744044010520118041060390f03018801300c0e400640350041481384510000c5400200d110040c12241400f06d4076800c44a0481001c0031040c0c01c0c0e05c042e03c22002c5003101d08220840b608244540d000b9482158001200303414500142c0d8101d030314544840006840307841c005000740e0801840d250415500b80403200104200149026108101e0000183c2d6070500e41402040000c1c1840d45502401c41081409101c00c5420f50358201c1d1149a54aa82c03284481c1c40e08070b008051950100d54840c001105014655501100506400d42a0b44816240920210041e40c4030100d5180181d444103050010f20009405410f82e21910204001929800d0381c80f0b00c180c9071202c601c807185490032603020641a03034604100005c62407441c03010b02400c45501d8103600003100c50702d44160003402610048046070005008010514100b544081501d444484440d0010605120f0f00703502001c001e905400030350750501d5103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 372972976 1250 372971726 372971741
    0x12020a270e04121101090f02012d030b130c020606090a0b01020303010b0f0c12040501120e0601050d030c0b0a150b0a1215030506010906080f0607210b0402030a0c0201050703 76
    0x140d19020340d940d5075100c6601d00d101d0100000c0500070b19900540011200307220f5181041e21030319a00f1514101800010040e01c07003c0c0c058002001905030358160381914079070308400d902b11842c0c0072903070224410114003e130801102e54101c203401c1203e0001c035a90045440d030310501007aa140b40340c590315117968100b554891f00006001d0b0300100014071142401600500650038400900c80c50041180d216910340006179080494000c00424248120b60307128070740c4552000c440074140200154105400c0d100e4034103105541c815030040549100301409501d1709448680c00c5032004940e131504c030400c00f0140000b085003201220301e160022440003e002c00380c3d01c1c24000c0b552070a008451185001c0f0040a100e56005132441c0b5448000000800400c00301c1d01a2801d02d070081900b501c5c0240c0302c1c0ca4080d100c454030310a60000410040c50030b5102501c40710503407441d5030904008100081e00001000385405082d08280004100311400255030844400c10303089900030004e584e5480411000c4440e00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 372974226 1250 372972976 372972989
    0xa1112010303030b0a18060608162015010e0103060c0302030c12062209050709050103030f050a030b040501080a050c03032712150f01081606030c12020a27 68
    0x9400051011a100e580154103042026020030031080c4c581a01c62508039030002080681070315404140011684040007981251401d02040700030169000b01030b00a42540c1c000d90307221a001e40104403607420030400010010300400d4500d000d961107540c40780014609020135201c0e00d06140358081440e120b40f00b2248101e150542807810401d0111103072170100c3d00544403e50000208003108a0b000c0c1181403840111506100000c600043d45016030030403207603900035084286040300400c046038000d004140404814900780c0d69680c24010300340d00a00505880c0c81e0440c0c42e00d030000c9202c1038001002c0c0d40a6028104441c00d071020407080554034456401a42c600c00c00e8801c44850105498102c039a030760341c005003d0100e0f807200c4460710745810900c1212041c41c00c80c1d54140450102d40885140c0500349000140c039005111001c000c924202c075204d000101581c400c2d80c080084e205a00c00c000740d0116500644d03a54829100c010103040c0c00b0340003903c02415074100d07000c1e0340c904480f038081241c3c02d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 372975476 1250 372974226 372974257
    0x2d0608010e060d0b010b0a08010b040f050603070507050601030821010b0a0f02010207020603040308220f111903080d0614030a171312030806010e0a090515030f03030a11 74
    0x200768615818200141203039030410300800d108400140d50201c0107020b400e0100003141c651641e207074010203440c4182e0024080c5002000f040c08021042041d640c246c2d80300b62081581d0703480321981290a440313884d0000d00741d405103070004020403490f20020120401c602c900d0103850101e02100c00354014080c40b80d141c50060810202000600580c01001d0001140c000142007460030b402180c6a983f080700d04400261204082040030125140b0f450a4030416a075611501d62181d50b504522030f41d000030191000c03c141c080c031001650342c01d04103403c034201f6031421848070341d41c3d10349110359400c400c41d80a0902d080003c00314020401e2414914116401030052401590b07e440328004c201c500100b408404104001e0188080e020503076441c020f2425a5000a5840540c100140ba0100250480d41003000e0754407100f0181e07a8640c0741d04240c030445c140c0012a0b0701c400c0249020101c80a80d004d07013600601085007088900440518461501d2440510030041c5414102016110382c1411118400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 372976726 1250 372975476 372975479
    0x70c02100201091b06020d02030406230d090605060111010e06040b0a060506030414010c0509060723010c020309120708060705090102030d0905160e130609020d06062d060801 76
    0xe4900c001254410650000260500080c0c503040609440510712040840c00044c0c04c22031360b40d04000c00c1448050341c0c4059070506052a0700205140b1050845502c1580c07001500b4640411041c11100b040001503000c021205092811a018000407641c02d8041100c0ac00007880460040c00b6049518002c00c0c09040c1a540c0c03030f81c42a0504c0030240050f010140e4400d00070440b500d4800007107004601440b0700348a2a00160352560039200d0861007581048410b000029480c4c40c5d20003590780309907201c1262518011440c0c020003081000c560350782a69800d1540702ea40458002c001002d0f900c10540b03890581c507081c122842d40e200c6040c03084c4890790703001e03600291005203e1310203001c4003e01441130f6850400c0303080d02401940c0382807509a40320b40040300c440f01c0d21005030310058000c0580300003003002407810801c0307070760b86800c2108094172075501d9120003021541d88912140105622035001c01040c2e03140e0001c80d1514644907500d0810300310806207901d10b01d0010360004d04890309a0303a4119035a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 372977976 1250 372976726 372976729
    0x30f0c101b0e0d2105040f0f150f110706120f05010503120d0608100e010b040902010f0c06061a070311060c0a110f0f030c070f12121209080a17070c02 66
    0x10302c401d000c15240d00c00000f00803045141440c00356001341065644071600c0d00e0806558980c01c2200b45c0c000e01c941d1415803420410b450581c00084001c80311401c00400c1046105400d8400411034810215a4001d2610100d80643c1180b04190150071f0b507070707042121003d42e4190030219402030242e1a4990b1080701c02c2c0801e8960350000340714039603207000d001c0366440c3c1d21544c40e8a40520380582e02846a11080613006404092049041c400700496003440000d0b082d40000e4100c00d81d202101003049503071204c04040c00b4480e0007140c001d0441c10058041c3d600240c9065070a50060141100040d0b466001c1003d401c1d00000c2450240d03c10031841c51414544007000e039403654104840022a00800c081e40c80701010a1214204900d03440001c1c540c1d0300c00b2490035034103006007a00240141310407600c09204600d001c040803600340d0380c8004408a80005008162200303842c119001900b9414518001e00b08008040905000c98880d1141d4017000c20308103000e000301303601301c074040002400e11a044003d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 372979226 1250 372977976 372977989
    0xc081b041a090c190807081e0609070e0d111f05030f04020a051e120d0203032406070c05040c080108100c20160b04030b0117030f0c101b0e 61
    0x3241c02112007a00d000b030007001c01344074800389480318000308036450204040e45800001daa03500060840d0046084505c0281440c551003010340094007031840c841c001030200c0d0140782520358012004101d403071070480e2440d22900f401720a1a48034040d9600d9003060101e00e004108420f81c20b48252601c6055548038000702e0341d1004010401c2c2d9112111000c00115611152520101800501442c4440c0c84004e0240601403000c180f0f0346d03403594481c01071441020b5020080d02c0d00030980d99108002800c0144800320142080846198080c00004200b01089010b0725000d04940d02503c040c040803244060940d00e800092103034401a400900e1486031802e1242c2c402044d035403190410480006044040341446d290310300203a42c0c030750300c0401411040c0904060400080000d050150320785400c3da610012100e9041c89512400d4491b86078103c80d080b0140182c0c0c000c8070b10360b113040f903d5042c10610382d5581c10110f0750015a0b94a000703840c11056181042100b01250b80c0d880303810242c8000c07801e1121 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 372980476 1250 372979226 372979231
    0x601090905010219030509010e06060d0f05010603170a0f02030415030504030207091d01110702011b051009120e031606050f0706050f070f030c0813030c0c081b041a09 73
    0x2140e542c02c000d406103013455002c898040c0002a41c00240a2400701c1c5141e0071200503240c04d14a1380c1c020303410803020303684c1c13081c1d050303066a489960b84510341e81d5071800a000d0020364100800385a807003411140388c00c4c1c00038040e250901d010303a41c24503000c41c4090140d8503803089015110401c1e0b54825120703500c5001b5005150040d1081c81100c020075525812103040341c404014550309900c0c0c2c040c0c0310220340c2c024041e41d074035080840100b5140410581c0041c09210341e10b00d070180070721500042d11047c40818800d03010f2144100e10184000350903460101d0600c040f05012402050301c0304075005081c06c0028040003e503c0f06006200390508100d0161042d070803030300100d07040540070040b0400051080c01450b0041400040e4100c040c181440094400602e0540f21402c15240201d104299035019031002e030040c603c550714940920090604581c2e62001090252444d01481c000141d0b100c07002519811807440f4150304c074070450701b2004100a80d0010352402e00c0c0390b80001440a0146401402e064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 372981726 1250 372980476 372980483
    0x80a090c03020d1103010f020418020f04050f06040b0c01060302040c020c030a110d0602070c060305250e0d0203150105030d020d020601050f0103060302090415050f090307030c14011a120c0306010909 87
    0x9200301c4e0302400007429991400394449409801007030411603221481485285035100400039410258603100c2403601d800f80f0f2050a2060307807124147c2d206602d582040350040e00100f0400d030740c0c90410b02003403030107400d007440203d0045141844140c0d1851000c00c10004440009001e0f052101d0301d43c850442e0002c00c81d40744c9038813510340e000142c0061581d1008150f614450041000f405242010103411240004d1501d048402c41d018218107500140e0b4041c1950b0350207080c0380480b11074401c04a11000404d200c000d40501ca0740c1d842c0c00d22001c03d0384d40c141c120782c821022244501010758041742c81d03020048802c805a8055070050cc41c81c0703081400581000c80601d000181382d43d803a00040c00100c4203407001c0d0340d25040c480c51260b03508840c0c0030f00390b4010041800f00da441d04210003041c4e41c9108851016040001148108040001a654520000c030a41c0024000740c804204e48030030203c2c0952843d4850042000340090240c0d0200d2030800351300d001000380a2503844d00740600060450b00e10100c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 372982976 1250 372981726 372981743
    0x10c0f02010e0d05070312050309342612040e1906031505150603010504090606080303070e030c19061107031205070201030c0306051c02030307060615080a090c03020d 73
    0x8482d07458910041d54014021401010410b00d981007409407540312502c1d400c00c00404004010740c1540000c1d824800741c007003002c1511a007132100f1442c0d0104000c0c1004c60302044540400140c0d000c5034043c00768000001620a481a140c50884240e48507515050300b6145407040c0400c020700403024440c580d00200e0174245140094410458130111011500301300e8607401c103070144c10008511403280c80d9100103502002e4481802000009440c0c0c001482203d204e42c0d201c00720001084200c2c0c20001c0106211003c498403410609806400440c49030500d50017849061071005803880d1a411305c0e2002400d8100300d10205051000440303408030107049001113886001d03400070016204048a0344005401d50724140c1341e1110b88001400d032100b8820010130981048403d01483e541d940d480c0d03504102d102d00e2030072204070610100b4214054818094034140c507241c070015907010210b14624412400340c0d6044c0c415626000d004c41224900b080c0506900c0d904c51050006080100f40001c1260040040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 372984226 1250 372982976 372982997
    0x118032601030c05150d0903030501031b0806010905060d0c08072c0106030222030507060905030105040b0a05270a061b0c030c15090c170c06180604030f03030b0f0906010c0f0201 78
    0x10038207403101e040c1e0840010390344100410378443c0f5213a0002c901c1e02171005805425251041d103d039543c0041c010310391a41d0340c44020503c5c03503556080c2914401c5d401000242103980d18507240351a0840c0707110b145090015801c44400c20031740d414a04c00711041200301c0f010180d0030120120020b40101d6116001c2110084103010488170707620f440b0300190b200b44010503400381840030081400344540c0c0803d0081e810720081c480040c4c20b000721141c1c442212000001e41c0c0d590001803c803c00d00c0b007800e24440707400341c0c00c08030703841d0310701280d0105194010501800780c061300b141c80036002d14017070b010040003c040348802000a440f032007400c0009409200c04c0b03103007508130440010489841e130408030355a480401e82004500001b00e0114801c240c00009000c900c944103021405521590f81c120007030030389803150f204c41d641c1e50000382d40c003560300182411460300711860080c000340b10042c0900e124002c08a001c0c41e0600e03000210f94071400c0180c0d90781d04203419513603402000c0208214120b050003561000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 372985476 1250 372984226 372984247
    0x1020705060d0605040b060903030d090203030f0f0301080705010507080304060c2a12021902210f0307050111030601050d0e0f1b04060801050411120118032601030c0515 74
    0x50300c00720100c100b002414074646000c000898414800c1140166400c2c00b034591a81d40103c26100060950708001c215543e40b88006801c52007403006111001d24003290030301d6500344100285041e55401e074111784890751103600545580c001c2442c020954101040040c1c0000c50716004400320034503d00b006164405982d0300031090b14100c240764154440904441c400703020300d8084198651543d8006040b02108070319034600c111040c0e840c003a0080c1c1803007420054403400d081c070030160703601c40c203003901e01c90307182e00b1543ca03265444183c0c00d451030360034154110300f4130050344100c0307004080586132503203083c52103400c5c0e901400c2d85c0b4500c03030340e5070051040c00c1c08461010310041d800e1500c241c1444001c4d90b080e508000440d15250410b1001d60b16101c2080b0002e200d040000c0d62081d411200341ca8143c030041189405042e2601582021400e80040241050382000500ca2842d10381c1d400010000d9403a000ba40100400340700c00b81400c51101802c111741d0034582daa102d81142074001c5c2900d0b0a42815 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 372986726 1250 372985476 372985489
    0xb0d020d2901090e07030902060d0221070305101802120103050304090f0506090103020d0c08070602030d0501090c0c0602180d15111e250302150702010e1b01020705 72
    0x495115101903010201d9030000d1034464811240c0c0d02420030754440c0f82410489900d003440203182d20245a594484030040d552203500381c91082d101018103543d0b4020000308681525240c0e030315810386c02113800105030042c1c02030058a00c140180c20650111900e08102451840c404070707403860b21a42c1c2040040701c44070005005a0181d80034038011030b90380703103401254402c560180c1201c840c200c0c07518081c020749640b103020f42811a5011950040b4480d420701b40340c80c1d042c1050f40b2100e920720074001e0000b211500800584500690f80b44c1c10800c1b682d9032008041503846104850340018881081d940000d082c0f40e01078021580d007001c00601c040b40620209001c200d94030340541fa446084094a84500c02e076014006814403c02001f5060198840350300002c0d5028038048081601c000ca4661500c0c40c0200c52041498800440c03003140400301d081c040c0d22481c0100c1e4841060350010300062800303005019809000d11004010250000342c1c0c082c0c40210342045058504500803144000791a58554 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 372987976 1250 372986726 372986741
    0x7060c11060a0510080d0e040b0f09070306140d05210c1009020a0b0901080f0a02070611030405010c0311040501030e0c04051602010b0102070302060d1a1306031e0503040b0d020d 78
    0x800001000c2c28882c40c0c213280c2203100d500ca0246a8045600104007682c40882004440c03015580800c0c071061070f9002680800320452007c2c2c0100380d030070801c992a0b505810030821034181a0000002401284c103000100702c5454019159030312040c460000c1201e007039451001548886662400d0400c40a07070a402d1000c284a00507025840b000c1e1380003945000e101110050081d40003240c03030400c3d0342c00040c1c01400700602c0c0399001e4a0303130301c0003c00c140000d8040380c012950210042146203699805038540d904141c2e01a62603618106440e104c590003032180740b144200d4001241d0a142c940070045014100c40340070214540214000114140c559004250060507ca0350111008051190013030840b250402c0803411544617000410160721104221400040c00040104064115008603d82c6001c2408e0846e0040d02c81c9a503542c502c6000c1c0d0100c801c2d00d00c500100c28440c001c03107103d2100643d00b03032070152590300300700400c00c241c1c003c1c1401001c5191a002d40542070136040c082110440303804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 372989226 1250 372987976 372987991
    0xd080a0f3602041b1707170406060909060507030f05010605041214010c0c03080c03070c0f0620031501020a0510020a11030712030509030a020706050c01140a090b13050307060c1106 79
    0x103c0340c800350b00d070350031025500540000500300d00b0740386800d503401003059131200721610300d1f51950350105081c000d094010720090011810248400541841e0180c01800110b030017400181c40d00d441141b90b8546800b4040c100c07261a42d82c81d04143c2401d10f00a11302440310b90450fa613003000a810081d0750001e0143d40a14003c548503c12180030506020b0054034004180c4011110700700200045950014013031940d0341d4200704003401c14425464074100801158400c60101c010401b00d10030b2142d403001c0250300c104003070700500000b01861401680c4d9500351040050280e007144070086244405580030b01494141e911b48401c0382034100c6c04060556000c0c00c0c05441c00d03800754600380d10290b0035000c1c164000c1080c0c4000d618150003150000e40b00d80c00c50040c141003140000d6200c0071043d09400c0b98a000d10a910400598184081c0711001004000c40c11105004408005001040403914a001c0349800c1009103182c000d55565030710080a0000310807061080340d80c40d100400c0c3c1c04001c80d502c120390303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 372990476 1250 372989226 372989261
    0x3020607030b0d1707060c1b150e030d0603141203010509090a0b151906051215060a0203121f1202010c0b0406021b071a0d0e0d080a0f360204 62
    0x341c02c0c25815520b00c02c18a0048c4146141c41188400c601e03000705030403540000111960707910100340b0501415480103000b0f600c3c40081400341c24071a5070351081c0100c0c3e1056900000b134010b000000c030380710352075180f06603100e060074401003216041181ea02c1d540800c5400c20b03903c1e86000b40d035410306907580903030717045030815040345503c0b4480c10080503075000440791410b51943c4510304075004205202d5645081d9421095502281d4040d81c51255007140c0c0a004002949801403a48029a01c0c0c11100c0002140742c04040490502c2021410070f83c4103000e07011101e101541091000040c0026a580c12410010401481ca02140d01e880015000b18482c000140c1e80e40c10398030300444820f502c501081c02da0b4010400030000d21900c2500e002c144013581140d580c456115a03541c070010003803034400c3c001c140540044003203081d170f12400861142040040800042c50f002c4000c0301159038811106520300c01c07034000000798007a0315083c15004080d0b50504564841c2950205054560007000d080a82c40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 372991726 1250 372990476 372990487
    0x201812061509060609041a03070b09010201051b0412080c0a0b0412020705010e01111608061b040f051e15090312070b040f0516081b040903020607030b0d17 68
    0x3a03080c080511002040798102102d0803c100010110b00c80d00714070510643e51000c2d03c06249140b155000e42991000301900c00180d502c11650b00d0390b074440b40c50306006500e00320001e10040c58481542e5031003070b1010800e0b81040c0c00d00c00888445100c172241175800707a406000d0300900f5441001240c00991154500c0412401e06241c48520001e41301d402c00190340140b41d007408036980c031040345800400e003443c09a08220908210360305094800b6000d50500384d00400c04503a2160003e5031500070428259081c24142004030040c10b94080c5000c0c4840c2c0d912401c01c10042494440d26000162001a900003000c001510006207a4207079150070710304180c0d000c0b0301401140b8003401546002500040018680000d03680c50b5500c0341d1000300300078040d050089018003032081c104002c0640300d02008420b81d01c29202e20b2740d65610241e02075245040c0c202002c00e401c603818540141c480302949a0010841a03d510f6410740142164044180d0003500d01060040868202c8000c01c0700c0094040a05d41e690 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 372992976 1250 372991726 372991741
    0x4020105070507181b320c0604020a380c0a0c0f0602010b0a03020607050c100302030a0c0e0117070e040c08090c15030106030b0f06070614010920181206 67
    0x5030001e050045c1c07a42c0e202c03441d01c0001500510201d648280b583c4640000360804101c0c210445641e540f0000c0c5a68007040c624041d9070b00103507941c012802202c40702c1d45182d48a221a80052540d0800d05d1400f00c3d1017840040b500525000d104a44003c21816081040041c0748502d4a080214151038102e8106000c11030442240b1140c400b40c46540300074080c02c03c602002c12506112440300a004420000c1c80d00c040c08402c0c0000301c007200008044141d0300c2d2040343e004003e50800d40310454100c0c40c0c411170080b014001c0d40c8841a4480685810203020940c0185e05d050800003003404091100c2c02016040540e914460b100d24010103895205050503d0311281e45840d03600e40b041d50040080c20303d04d4402c00c4586050300d044403054580403d1460040000c104501044800b00c0d810030b401080030070400c649600410789013207107211401000d07a81e9803030a90a503442040700c1c9600310304860300da6221240050041000302400a031803041d00000d100441c9601a5010040000303030060014080785 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 372994226 1250 372992976 372992981
    0x2130e070e040c020f033001060c050d0306031703070926370c0306021201240e040c0e0a0306060501020d0c020a05061804050408030702010b0102070812030402010507050718 76
    0x4107641c500c000c0a4145410810586d00d100d4040d0b100c0020b50040e007540c210001c04c010000e911001f000307a0f20140e50b55040c0181628842400c111410300505981d003c03114030030f00c142c1c401c41342c00891005046000420361612580058442010003103060f0f404030782900b040303031801503824004a09014490300300480354140504020400d41140d00c1000ca032544207401c98a074500080030304100300c1025031f1450694603a00c0103501c024000e034004107140190240504640f8101e0f01c0605150802c5141400031001c8a844074901c4004184c07040e90311461418180d00c040b1400f0840d00301080311010380c100088003800d03294000c480c41516404248215641401031108144c81c0b0f0904403040903030303a80015007120b45c038004d80c1d000b0500800c90042070680c101d0b5a084480703006c0c0c0104110b04050900a44030781c82100c070800950f0030814444c00c40e520004030b0704101c0380501c001e0402d0310a80314071041d8a42c00507005074100502801080080382e170520040d401044c3e00b0500d41000c01034180e803c0309 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 372995476 1250 372994226 372994241
    0x103050d03061a07030302130e01030c051002030a1e091a0306010e060f07030503060a05060a020d0f1803020d060902091305240610020313120204060902040f0902130e070e04 76
    0x7041c00020700076103682c07001c03c152400070364941005610341b01c0030104207012400c183d005001c42c0784040d0000050001d10b0502e2400e13154180e683c0049101c800c50140d07030720301c80c1003e00c10000300c2259524521500d05400c01c3c00c9081e85c1e1a04d080d4041d0380b4000c522104030242c0b1410300340d034000801d0100540c1c01500000c1c0d01001902c03281d04180000c0c045440902a041000d0148170000001602c00d0307546810007000703007038010081038641c4440d10000350744210704680c1034081400c1c000507496690040000c0403003100184c3c1340c08921130a560900a80c40c005d11801c40b201500c2d01750241c0140d8440b4456403213284000150641c40107642011031400e05c101c2c00003140b50780440c0302a0300243c4910441c5a12000c1913404404008200e401240396115030107051481e40072001e00480d81202d0750540d14170f914002c9509020043d20786180030100d104038840ca049040f21448100039011054019001c00d10001d1900700c01156075041640e13100604950880010364031aa05510a00e064441e059 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 372996726 1250 372995476 372995489
    0x203010b1302091f080f070903080301181401050a050409080f0c0f0123071b0602030a1d0127081306030204091406220e0f01060513020c06010504090204140103050d0306 74
    0x80100610700702c00317050301001901c0010000340f014005906140500b04e10401554400d402035a00c1d0780d11601880241c5031009180086070905031840d150300b00c0c4c000b0883c142c1e480200100da200d4504810031005154520044070812000d100e01e1003030180300c0014282030808440906421480b0700c02540c2100c240d0000b4414540307800c44454a02c007200d905090340f15800d8100903001107003030f800c8130382011a032020050410340000100500d90701a5045054101a034030721070001c014186820300c0c20303285190301001c03030b8000f50405081843d00301441a000d842c010342000e417900e40c09507414043c1c00341d82c1d0800400320f81c0014040021501910500c0015010042c0300340c1e0720704103940000c0b00401c1869002c640880c2e40c0300c9000741182c5540c0281641d1503060101e4000d4190b28030018003a00c2c85104003485480c080321503484540442c021503c01d50907017000390090b0b071b0800b410000204043d00f0243d0b081690f45417411021200350709507034041c600031002011582c83c61b4500505540240e013001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 372997976 1250 372996726 372996769
    0x1817061b0f0a02030d090606050414241504060815060c1e030d0204080106030506160519030905060a050a1a0a0b0306040e0a1101121103130203010b130209 68
    0x24240d188032600740e03184604140d08090340c0d502e001c00100e1a502500c1c2c40d55250a103001d01c1c0c0070400c004d0354414011610700303450030b0120746214181090f0303032041141e619510507002c1c011021042d20380c561020b0b08007002024001c8240c01290700c01a15003203508040e0200d40c043c410300001488104290310100303001c039040c6292201d80805540c440070f500840080003800300d0150b07400e990007441030b62094564018110740396030341d0317900f000e01806481c03000383c84a000740c1001c22000c4074111840a601007898039113030720742400c01c000041005c034081c480b0390806a4429440c1e00040f018400c00e802681c80501c0480c05040141003e012a40c003030307501d420103078041c0242d022036895500c0c1200885010502d80340d201d070342c1c800c085009000700d40442d20f418007030343c05040200403080d0b00400f82e188080c0d90341181c0000450300c2c44116180d4402601c2c0d800f00510004000110005620491034405170011809100c0000407451019003c1c13000300c5515004104120681450290001015941401d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 372999226 1250 372997976 372998011
    0x30f011202100e0a170a1a061c050703080d0b030c040c0f180e01180b03010203060f0d1a010602030403061505010804141c05070203250b0a181706 64
    0x6a05190b90315608410300c02e401040ca0919604d1001580051407041c0785040003200e000c00241d11010b291004a5024842214080b201c80e10b80c107800c1d03c1000f010345400d0071012400041d4a4111031480e04603083e1043e09008000281020003400711400000c2001c50180300a80425041511210026008524104110900c00c0d802a0f40c16202c2c5094140103959400400e410050900c40d034004412851070b4900014840025000302c84e644c1003e808100066080030007010300381d200035151107038082241401d4103843c2c5400c080d603118003403203000072803882d0155280003a0340041c244e11080c00341e00082000c000780200ba000b004d220256402503040301d5070134600068013244016002601402002c40100d04000342000400040100c04c0c8540c1c2054600a40060403030b480007130101d00901494010b4160481610903c1a040b42150300c1258190b00700503d2900c9074000340c1c110400c01c0000e2021103060201070745031034050404001c10000c6400301c0c041c0c0c10715121003d054580000000d480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 373000476 1250 372999226 372999229
    0x3e09070f05031f0503120a081e2e0306050106020d0503251b1212020306010c061e06082d0c060f04180905010c02010b031005040f080f030f011202 64
    0x450f548040448503059090080c032450005111060304030503014071a039400c000c2c1c1540d00d20050500d1034055035401040d940d0b440d00c501480000c1b0812581e1405402c80032030038a283c03540451107042008100e019226020894244107682d40341d01c1600c41c65540d000502807554180540500b640190a00c286141820b0000360f685170382c00741d00d81c5190341403801303113074003883c0320b030782d0074003940248040d00016903a103410a8550244031030358680c0845c030f012240c091920841e00a40340b0170f000503140c50b821120030341c56210150041c0000100c50f419040c045000f914010310888000d01001402840c1c214981900c130340034500502900314404110703c0c80d6441081001501034110714007652070035160461456031a4840c06150040c080700f1001c81580a502c0c0d400f94801030681d40141c0080c803442e04008070aa080340d400c54541038058010200070142000341750080c503002441402503005242540d114000f40d038001200d0402c40c03060000502a189001040c040d001d04005602070440010a60 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 373001726 1250 373000476 373000487
    0x601030f1a09060609031006081e030a08100503010618050a150b0c1e0109061d070b090307150804030f030606090e0a0618090203060c040308073e09070f 67
    0x81d281c0d210300c500d0000122603844660544040b040e014080b9100d040e00d480802c0c000c2c2056002d402150310601280107042038022000104a030301913009145411010a0229031811005006607100076a0000024140c2c8003403185000402d4100c040c4441411700110240584501410b030541417401d00900440c0d47c244c44005e83e045400f5800f080b96030b1205100c0140c11300a20200c60b10b40080302c43d115002014064000740b0155115035420416000584085030f10b0716503081c0041071650160b402441109594001400445802400c07180c0850340e40e50312a60080310741c1c0d00c0c2070000742e409017800101034010019018200d220f04061045c14101603000340284c0c158441e01500d031584402092006080394090800741c21072000903050b41a0300c00c3c880002c0e19060404030b00900c1144c0001e011114280292000c1c0c9904c4401c0c41d01c1c2c52a03548501b6a07035000b0701d06040f140940c01c5085108925036aa0840c6d04004175190300220010007000c120130b1000080409060001070b1003580f800c2603109 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 373002976 1250 373001726 373001771
    0x8010f060e0f06101209030e09090105040506190905030f04030b01170d120e0a050619050c0d0c020f060106080103020a061d1e0303030124020a120c060b09040b0601030f 74
    0x20340e00d680d07040304e0b50401101c0d0000841d130503040f1945092503000926038003482440c503414003502c0045003516011951800c9682c00c07030f4098000d41003034000c00d07100c440200d414046051b441001044080c05900c0e65030465000a0340c1440034580060200104650f40205500410021001d002a842d01e0b070795090310354601d20503610070400c6203104620948407940c440c09007596800100c034400003803407422582ea08010780300b01c800c40d000c205000282024a000c0ca81c0706441c014480c50804041d07103400006420000f40e904254081c180004841c1ca900704205402480c02d5500c16005502d980144005484030f40c21800801042680010200e1044020300700780c02810b0703039140d26160701c0c020401400c4100d50513044c0d040c04008000a8144100c115003101c00040c00280d00c1d00b2501c8020036a80c0301c441d484002d1070395164401c400c0d1158014103140001c5400f81c1d10119404401200042890034201e50840c0c605040300280405540e040c8103c1c0d55441c0f00d42c00070000d0740f645540d21003141e00c90 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 373004226 1250 373002976 373002979
    0x403050a02011202040b03041401180302120327060411090906042d140d020a0302151b0301120c0e06060f0714011401030b151e041508010f060e0f06 65
    0x2c102800d412210f140d4116401440c41e030303000c07544a06092034140c100c8480f0b4030a0450b958241701080c03242c29217070150498100d506070020079828000d180162140e400c010280046000c842c88040182404098070085d2940008060700d158035141c40c00c110340300c90190401d406503124500700100c080c000180c1c03036041500411032030498104c208007882641180002000040307840825202040704804807846029496010394440e000350300e00c12030765054200c50180c01603100c0c1c20200030031940c00481c04d0b00034060305c0112064211000d901900360744203a0044940810300c003554000d0146409030b401c00380501b9030f040c204a0400c0700003d075036806840380602d0180d070000350423010418006160b8002445000c000c0c40481e04582a1504026003480152940d5091100103a10700d044000c06c58030440c0003d0039a001e40041d890240c00d1110b0703140e601900980e0704c0f1500814901040e4202005100313140011a4403407055a10a0a580c0340ea802051003800f03460600005c00600c1080a0740f0540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 373005476 1250 373004226 373004237
    0x17092a040e03040f09180f0201050f04030218040b0916140d0605151f12020711090f010f05010e13020a090902030f0610020a0f020f0a0816090c050403050a0201 70
    0x1458000200284202004061244400a00040d84208003107008003243c20304141040a503413400b1807000316031500a0300400c1c02446550010041d0b01038000741030003e0b04505502d091581341d6011550031a0740c59070700301c141d1200d10100410040440800c03a0302000341005045024102d048007800404140581030300c20300607240c021400d4a812403680c80e003d0b0003410510107820700440403096203a0160540b0702803403805604c4801e0b0a50321901c4002c2a0b9156500301040c20380c000080d0003508103540803a40c00003415071180c1e1541d2400038140c00b4005615424255514203c0120099882035010138148410019406401d03a1418401e40c2d168505660160360b03804032000032191050030382c100294161001c020301c01d146803c0c4403c603205803030a8461540342084c255050703958612107840203000802c40b840c10001410311062040c6980380c0a828080700c1502c0d44030190520b0b01929110304400000401000940d032035002e03100341c1010b00d04009107464116100c0645031038854001905128 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 373006726 1250 373005476 373005553
    0x60402150708031906060207060e010806120f0d26010302061321060606030203060d11060f1b070e04020303191206030f03020d1b14100603031709 64
    0x30040340c12207200c00c0d4450940750b030324509424107104403a030380320918140620301140860414000103401d819502e1070384822501078445001100c806400404050700080c0140c40d1146601c403c0080b00e414003952000b034501002c4c00000103082c480c8004461200708044490103402c3c00e856001907042d0303034042e01c0340c0b42e0317030900d101d003500c6d40b0302d0f80307034040000120003201711b07541d9074614030300f400040d841907801707005096594004500b6400180d0b14a60310200b1202c10000061240540440008d4080c02c11070600d00200506901600081e190301c80d119814843d482081e84280001000342c04002c0c2c01400310b00301b0741c0200e0b9490081800500d240d00810360142c240c07601502d03000865102415003804001d850346084c19041c07908050490140c40b403a02c0408071280140ba030391101c918010743c50055a0120345a004011142000340c40f0240217007071160303010301c40501980002d5402380d220901d1404940e5170105500b407000742104d10710f8024000306c642c0300301d1291004802c004ca1081002184 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 373007976 1250 373006726 373006759
    0x270503040305070612060e01150507060b06030118060e16080403170a0c080a06051c0f06021201061202070201050406030e240a0f0b0f06070c09090602070b060111060402 74
    0x5100301d030409002e52064850000d65207a00c0380c00b1522446601e02c1c24446d96648500f0000810303028010400c80c2e0b040c0d1148515468864000740c010300c2e000b004007046140e21140415525882070300891020304806c00000900d280d80e0240c10000c0c100c11108a03c1454442c0c8110185650504807408100c00300003c90203141c441c9960110f24203070f0000c04090760130510000030007070448a001c080030800080c0001d540850520420049a101030310030342d40390704021710440010790300c034400300c41364202284800b011400a201170804050009002c12055040401c0508a40003c1a0812019004210100040c0d030300a098804442150501041908518440900b420f0040008184c403007207186a41c1c40301c0081c20300260150101c2e180c200300103d18404a04142c030320072442540c100ba001d90860501d424484018141c080c01841c40051440d101c000b00070a45d450820241d8003160041791038414408000212768000c2000d00381081d0400c041007c0c10748030407000340068441c407454400503410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 373009226 1250 373007976 373007983
    0xc0903020604062007080a0c05010206070f081f0f140306070915030b030a050109020103060605070314220b0d0b0402030114040504060b13140709061d03010f060306021c2705 76
    0x3910301805036005c0e20b44400076966104803424090700c3c0c06450a000060703d5001062960103032595603214100101010310507100703100007902603c44044203581180d40d01c54043d03c000c024140300401d441a280ca88179210f1440c40c01f001483e840fa810040c140a0782e5500300c40b0340d1044420100046514000d030741000d030000e24451014a8050103900c2011041050642c407003118107100740ca04210598850000302d0300fa004114005002c15103600c442c0d45d003050001c01408810104140f5061039948024022120400583c00403121300004240d004020507980626023507640251011802d641c50b10817402d44400d4038035061070040355120041028008282c1041e03440d8030018001e00098008580254010b10b4000704501442480340e01241c0315600c600425400c503007507940c0d040032520541354070700150360202d91031540c0340d90f85010710741002e9140d009580c025405044010707161441010700c814030304003100e4078428103854014440305c800ca0191148014400c441c2d00340400381600d2411034035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 373010476 1250 373009226 373009277
    0x90d1d0603010b190926010603020303040b0a03050c09060a030e0a14030901030506030c0f090702150115030e15011418090f0d050a0c0b0c0d0614040c090302060406 72
    0x304400008000b26203644588010040300d000034900701d072a800004401c90b0402c009009a086103840c17445c0c521000703010000c0c480746c40441b104c00020034036035a60020b4607551141d40031f000460f2000c81d40e003003450b405100d560781c0039020074039180c604424040002d00500c80d400d100e5083c141d54010403100d03601c2c00c010340c10030a42c0c00850040f0600b00c403c4e94543da900810700319800139042800041c0746043c040f904204265014103103440f84400d103020807021110040045045114101c00800d01c0301c5501002030081070301040c0d118a40c2c1d50007000500303a0b5980d6003294850391040d4555000740c0341c410002411503140400c4030a0a4000200107461000d02112400800c440c1000340a141903022518084117001c0750104e80110900500660703ca0248102c082e02084010071500080b49014550643c08245415100d01e8954202c084004950031604480500b00c004411344243e030904e40700e8000b146506080c000d4003a4510360000c0d0382c502c00c500900081284d001002070030010081c4030140b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 373011726 1250 373010476 373010479
    0xa09061e0f181d0d0518040b0d060b010c0609060204050901120f12050403291e01140f09041a0606280509060a0e1509011209081e090907020105090d1d 66
    0x1c031383c01e8165400514640204d6811020740c046005030185500c1c0501c1181100c400251001e980190079849207030082107103180031414449943e40200002c2c20038400c50781d845106072030060b15a810202032040301d0405810040f0203d0340b150001003ca01085c81090301241d00a60141d80c6000740f1408503030380e0146034801000c16005000f143e000c1c280c042896000c00c1420003041b0300c941c1d941c0800c1c0e03156003206142e800004584030010f00205c0c8140104941201d03020f032140d4000f0744280041a21800111401c1c0d411004c8203a4940e485502100141c2d00120221000350404800d01842065003030350b02d00081450202c2e01c01c04802c14018030a903603e5100c002d180c6901c4502d040c80141511110400040c8900030a1001d00c41f83c0900e0000c1c1d5540c0314041c0d4803001101c3d40003c01000034401400f00351002c11307061042001641c9003c1e40c5118590404141039150306068050041c115009032001c0d00303590403c0c08001004400041c401507070310702c074075140268042540c0c500015001c030180c1103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 373012976 1250 373011726 373011733
    0xb0601021c120f0501120f03020c1203030a0c112e23100b030a020901030906060801020a02190b040314040806010902091906021b0a09061e0f181d 64
    0x8072440c03904405070000b5031809800c03d00815452101d024103c1c1d1090107414100c00d00800702401085190444814203842801200c2c12214060005083c0c2c4030680300842c040e5000100300580b9641602030002d03000a9030504e10500345080305071a4645002c050140b4800140c503020010315503409681c940c0000ca4104100301144516a6541c400b03500103003201071011407140895144c0c0070200d160800c81d40580c0079142035803560400c60019501241c000c0c0d0400d5220b68100020503a5481040001e0096100041e03030384e2280354020b0b040103883e04a000c140741c2c4d040f00c5070011a40e10001264000c1c0e00d0b28003007540041910020a0703c2c012508040760701c0c0300e81c000101e92140b8980c0107111034082100d9500e04200300340d295901022040c0106001031300072400e031400d040c40c1d5081c52041035000070030921280762030f01c03009070845482da4491074501001640391140c818080624030302400480146185140c1000c0e40b10034580815521a660140d8401c3c00c06500c03d1302ca5180c4c0c100c1c801400a5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 373014226 1250 373012976 373013023
    0x80c1903021b0a050d0c051209010201021c0c09050a080c0121050106091701020a02070e06040906021309051b0406050d0b030607020d0f021615020304030c030c030b01050108130b060102 81
    0x82a643d031840c00d400c03101c038400d00c0420344401e4091000300b240d441d4050003d150001500c07105003c0c0c0d800c880c0101d07042d50b40034084403060301c0e03170444810300211001c2c0c1c000810b40052a801400c008203075106600910f0580340a0001344408100d04805110038246624100300070250200819010042901e84030324000020800c0350b8005140f4044803002d84003d41c0200070748543e503081f449400c550501590141c00c0c10807036034290307e0748507511101c01000007604040907100d00c4140e07805503560000007010341806104c1d4420500c90190440d10355034005c1074540c4200515021480f56000358418030001180e0303403c0d140401d0304400d50043d00a8280e075000c0c184a500a0364894003145440f01165405031841e424910014018107242c03403120850308070070b00e41a82044141c40d4000301c6821404100004000300d114025400f0046109814084189146062003410281c042c1c00c1541044420000d0000506410415030f404981085c50002a9203a010050f498544003001e0503506070003c041c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 373015476 1250 373014226 373014277
    0x9091512010b090a0c020309040b03070906080115080718050406090606031a060603150f0301060305010213170601030803010b03180d02010b030610030c0e04082710080c190302 77
    0x2c0050031041c0c405a110781c4981159034240d0790115020f4005a0050001c800ba915058020442403440078050310592074030340100b10300780c401c107800982e040e030345a440f801d00010100d61224014141500641403080c00c209040700c0c42100188d0101c003182c0c031040131409003c000d500c043c4815030321020401401d5600d28011014000d51a0240780290913100040c0302e41c14643d0840f8491009080d0080346020030004100f05215400d0b92250550b68400c4041300260091005000881c80d5040d00c010413480c0107a40c1791901119100b040d11a04008010000a1441801c0c0c905441494980c0c85d03e950f642c031008041d00119007a83d890030b1240d01c0600e2507490301944981514003082e0180c60841c0c0c1d07000c80204003e00036210040445540450030030688000c191540e0300140f05240c441d150040c450b014040c0d1001000c2c2c4864116240740e810809860141551000484641411116450300114041c141d0089c0c4000f40341500c009100c800c0e0491003681120301c4d41004800701d0004405800303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 373016726 1250 373015476 373015481
    0xa0306180515041b0507140a0c051003090c1502010e120a030e0a0b0106080c070f0b063d09030204060b091203030408090d140f01090b060609060909151201 68
    0x101c1295140c0824018200c1c1414a400b80f03a03a610350303004032010045006030f802c0702d0f42d906c11281a83c0300d038500d110b4202030300b2060003001c500a015680d60199203050004201205a00d143c0c0320051502d03003d00680060a610360702e000b01c0700d1402000802c190200003da01410210600344030700e000d5504603001e0418140080c10300e400301d650b010001c002e0182840c555074000e50030041d10110780040100840b0784144111075204418034202070074508170b40d8682c544141c070b00c80103c2d00301100d030041002034208659018141e40003c8104601c0c030300001c0001100c807001c030007000d81482080f001c9801007402404014001d584c050030400000e940e480a143c4150000c00c0d000c1d10914507081a44d250303400000c2500d02494110582a1500c031510041003c1d50700406411601a040004243d04a000034000307450780c00e05400010404581030700d0050b000c0e500080c0340920503c0103010160fa01c1d00c0c0c06064844080c0d05546041d5292038403881d80c0012034082d459141d00c24140e0131158407030078064 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 373017976 1250 373016726 373016731
    0x8011d011b0203030a0f02070209070503040209070306060f0e041113150e0a18060b0a0f0806010306060504051e03010c0c0b0601230d060302060d0b0f190303050a03061805 75
    0x8025004074a000490340c00d1a04482500603072050010a01c04aa1030f4451400d00c440c0030001450034240d5404244500360466401c00803038404400c20003541000d00d000e0703610000074603040050b941804405403409807424009800c107c2c44851592083c2c4603039120301020b0400528035500c40c00c80c0c3d150758a51078018010481621110070301301240500034a1064804280103146d5010345007050140010703002600b900b07065807034650074000b40d0511694000e00c02098070341d455441010800c040681000b202612036410140340240c10440f035907110003654191401100e08084542c03400300c620314008030b1081155455480d0040c1c10b42142e0304000c48068a43c40b4590121340760f682c1c5801500d03403002c004503003041e005084c0c3d00b00081c8889000240b02100703204600107031640d03ca0300400c02540050540f40102c0da5580000000b0307103482e20b80194589000c40b81214402240d0f5152100c00032103100003070920901007001003e80d4080d802c041c000d0044590000141039401002c5000b80c84c06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 373019226 1250 373017976 373018031
    0xf010e01090203100207170319060608071107030b0c0a02012c060a050105010503060f030a0b04200a050d0b04050f060c0a030e03070203250e0a0207020f06031003060b06040801 77
    0x20f203e403241144119001340c0c0c03d41600850b418915559850506805038001440c00c27600080981d001c6902070818490400504400c1e41d6400c40c0d458103100161500001c1960b5a4a55110000410015a80781981588800340310601c9858a0300e591042e4050f245030760088e40c0032644c4c4814003000350404104400280350280c22100d00c1e4543d01a408100c80b02802528005103080002400b50f040c1607101c05401c007001340482c1c05500440d2100c0c0400d00060301e007103070b00b00024105041c000c604203040040da107408507203403000c1c14506800614403801140005150700000300009041c40402c1c00b024000307245c2602a031762540340c00074161085501210f00305005c40e1805084104d007941c0007040d40c070f03101c0d4081c009121920040e031100c00d400c4101c40d190300b40400103000102e0049803e0340d42b40e000340d041d448050785440300307803041140b030800b01d1032803c0c01042c0c140104607950b052040d9040031250060700c0051208114004038100c0c1c81f80780c03c4001d1641c03c000c42c080c194000c06801c0f4004502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 373020476 1250 373019226 373019233
    0x10902340201020c0909120f07150c0f02010b0904060509030403020d060209030105070c02180c040b0a0c050606030c0d121b03050d0e16030b0a020c0a03050c100213030f050f010e01090203 82
    0x62201c00c0150046064500742001d51155000c0c47d00c16403841d00405400e8840701600d0b0801000340d0321042240c0c1812103000140b41c6802140718040d03007140d040403600010340001d000c681d2140000c103c1c8814000c10241a4036103800100d1123320091080303c028507009001665161440e04000000e0341c0801c0c000b40c001e41c0780c10001624a88181c4050703e100360b00800104480e0802c05221045035030103815000f0b260410031002800000e0700b0000c03c450b000ca521440d0390724000d81882802d0410092010f4020342240c640701c8416036601d4622030006a014005040588a41e0b108a880d4140306d1030140122200c2d691075400d064000001e02010940b0002c00d003d0950b050460641701c181c10030184a03011030300c0720240001909201c1301c41d44036805080050410f044810b480b450400c00900c240e010502c001001001c0190a00440071708400790101546800c054005621600c00785110240c0007880c035014440800c04184503140d0b920110000038012900308144490003000520380c102e00c64403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 373021582 1106 373020476 373020493
    0xf01090906080c0a08030408120a090503070f03050d02010c050a05220b03010608070804050318030c090a0e0f12220b030c03061005070b01090234020102 67
    0x6030020010150034005102250130190403100c19600b04000c00e1108401c0001c00740c02100d0903814103650b411030450100c0308190303942c001030b9043c003a01e640066061444660074044e68050300c107940d8180f405510603800ca50300300200501043c4d041c40224100d038007a9001d4036050350402001010040c0c0c5503a02e17006041c154105401c0501c0200052115603440424076038400b2550820080c0e80c20581c075041e6032409010310701540400d0040c00075286850610691104000142c88180c86080c50b41040004d00310940b240b00b041c0c82212480c180070030000860030000e800c1c05079400d184c140000c0c1c0302c032130b0b540401e25190180c103044a80062480440b030005c51094800c20440c41c0c0707034100741c0200310b610160302e0b03050030410805005190104001586190440b00d8988005955603031850041554000300e078100102c038010703d0034076541c0c001d10b0500c05401034800da00b540c0140f0b = true := by decide +kernel

theorem cover : BRFrame.Cov 372841726 373021582 := by
  have h0 := BRFrame.cov_init 372841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 372841726 ≤ n) (h2 : n < 373021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
