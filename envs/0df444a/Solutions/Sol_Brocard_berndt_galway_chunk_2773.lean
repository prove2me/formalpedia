-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2773
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:25.30997+00:00
-- url     : https://prove2.me/submissions/d21695c1-8fd5-4d36-8ff4-4593eea3e177

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 498561151 ≤ n < 498741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 498562401 1250 498561151 498561181
    0x705060c0705010c081905030601030f0506010804021201090602130f06211d010504050d031b1403090309060a09060801090c0e0906030123010f080609100506150f0903070b03 76
    0x160b810418002d0710a010002034901b9290781c4c202194021641d098000030140c0103800840700780303001034030302981c0d00d401e07070b04501465004007810307109c0040c0e50b107598080c080c00324140c4512081540d22400305d01d0004203988010300d40003587c01018614641045d00c004840c9400b80d10801c104100c85200b4080134540e884007890322001c1810008250507104c801c08031010043d211208903500c0c0808110a0100102c0c043e000c8c0800780d80d0802403d91103c0400d141e490b490064200002c484002d403028004a2078000c50700306040d40c0c100c90403c000140020042e40c0300d01d126000292401d1030030041c980d08503601c00d016000b011414003108606101c01010708000d031031403038404d030300e580c02003a401d84003984084044e644010a164003400a0080351160000a21551000c080342e6540022800b80c0440d00341c2c010203030354009d06259003c400c0e184015050203081503a014860320b034610080d84a18004001703100d0441c2c01583c40384e070791200b01400c108043e402010700034010410040c00d220000d0030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 498563651 1250 498562401 498562409
    0x1140a0f020a0803010b0307081803070615080f0304170114040807060f051e0f090a0f2d120c020f060f160c0e090f030403022803030906020705060c07 66
    0xc440c900c030394159030807441c0001d4040c0182c203020000001013101c00071400158401d15054844200c9515405080c098a229950b1890780035001400a0000200c43c0d4004451165030789a170441d9503600c0d12041400e003c0d01c43c3c1a041198000101000ac40c41d61420503010318011700000c002040c40c1440c21840303030380e0060009148071400107507801003142d254085c03441c40b003c404003000140350070b00061361000c081e107402c001c0e01c5240300005002c0410314100c0034800c035811030142c00c104d01c0784d030765030b0410710b580c3c240444850391205c0c0e8009290000b680a070103550690890702f1100000ba00b460101010903c0c1c2d88000c10488480d00e20168881c40b02445c0490011b4a4072565450000a4403840e8040e000d8030340321180da034070301c814107010041c03032040142d0780f20f400b01c0350035512100354207685c5041a61015000e07070020b10081003d450f01426881010a080e0701c0302c011a10f92030b401190b44060364200b03d000c107801d01000e212240e41001034002070002aa89180b8015040d00c0040d5076400e44c0c81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 498564901 1250 498563651 498563657
    0xc05060f070309060c08092811060c03120a0501080a111e04050c090405010518040f0c05040203091606050406051e0c0307030c0506070903110d02040e16031101140a 72
    0x40421142482a4080b040a0342c01104c1005030390780768030008101d0038084d113802c0450300c601450402e81882c41d410402400034041c8914003021040d503a407580c22040040c11540c064820f101000131094144000d08080028a140c0f541c0341ca0558009011544103802c007102551002a00c1000140340c1034580120080c2284d41e04da00e5425208074075411b400d0000c40302e411504240a0100b91400c02c0041c02a500040f28280b042e60b803180c09001254441c1140081280040404030303000c80d10090041d19103074002d400d0a07040907264804102aa40196241c425940c030082d200e1803005200c00e003c0000d0512490300394a0b091034103000074000c2c000c0c0d02c0906104880111012403100611b0100c0b090350200009581d1542c81034203003d841d035490500c0a42c0c0300d00500e000182c100c0d100307911a4090b131340c1c405252002040c1c4031090100305c084400e01260400d43c0d0b10b20296919604002c0340b140e1803a810750705107645003189040519584284030403414040030180014600012105a82c0d8800041c0b0f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 498566151 1250 498564901 498564931
    0x1060921150e0118051510030f020d0c0b0702040e07051e03160609081225110411040512060402062502130f050907230621070f0c0506 59
    0x200004001e01402d40c2d03401d22507103060a0800c000c44101070109119003c0d1080d201c80d0819816180400701049403080c07210340c50b0440600c001000585c0c842d1b9075500207004000348000703a079a407848100d002d8100210f103010104c0c10703508519150050407202c420800280030000d141c14007046d8079071262044c424941c00e04560006850310104400380700d88542c8410815925074070a03000d00416000d000302c4446d0300850a009032032040d620200d544510002c1154038000f15006442110303103481c1f00003120740a8015545552541da50302030a17a03245021a68207641d10300e0001000010243d109294806800450400026985031400c2d03618180c000022868840c01c1204402115004014020f6011080c56501994046154094640042000c00c10451920f41c0d074611555200180305140d81c9a007491030700303a5a0b011401c42e52005401c00b4040504001840c55281464010180c48034402e040e0102008022903004901c507908444034100358000035400e40340e80751544e50041c442c00c6000301c42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 498567401 1250 498566151 498566183
    0x18020d020705060c0307170103050a020112200a0224011202011101020c03030f010e091c0201180f12140301060302090d0f031e1103040e090a0b0c0301060921 69
    0x3901140c07115075100096940f28500241004020b80003640c058001881c2c0e0049150380c02c281030440c2c0d050329001001403810100603401110140d008400540030541c5450001204031400ca212017094103030f080005403100d09565001f464400d00710301c0ca60f01c0725140708211603500c40c040903d50554414481c20401c5029038001a00c201a050120468642c40040c0c0000c0c1800c0c0880650301407400b004041000380d1f071314091480c8003001a1102d011130b80003070345c0031071507107061250618442006000201d000c41c400318000380d607400c80520a44a0780c140c030700940104950070085603203e103a1800d12041c4000e001c204104a8041401040309143e400108414940e079540300c000c40f156400b14209001902611b4000c2c840a5000315000d80034a042c203d0031082c030b020320001801c40031518011400c00c1c0c80c0102c40e0400903009031102003140101d42d60307400450180f4000e907102d2081301402e280d0342d52402100520a80380ca51041c5505012107001250104903c0c00200d0450380003071001c0c80031900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 498568651 1250 498567401 498567427
    0x2315040204030f08070b060109030308060415181b03051605090303121e070509180402120105010b1207050405091303030e0601080a03140304020a0501080c040e0705030412091802 78
    0x901c1d0000391100c50a50103000130800610b004000081c401c900c41d000c252a0f00c40191038a82c040c1c000200404c5075100040e10504290780094004a0301e13911900714503503030b000c010000300e440405100714a40c481c52100041c50030b01e0320300c0245c5e00407454100070520f401d0424002c021380425511040100001c7c0341689a9010001d913400c2340800303062140b185c1004441e4007088a09540600b008842d0f010004408034082c03415951482805841500e0f007401c010082d82002c907009000303c4c0d00c070700354500c400024042482001d020340503c13503415986101a855692440d440104100300f004802c020034400d2751106070206800c00300560200303200403a140b40c03e0700a80724401e111500e511030040000341080340000d0503d07946000b511800000c04000703400c00094802118080d401103865802000203522a000545d48152548241d5007407540344e0040c40407515042d140000000c0011082c00148900b494050304036240e98140900c4d09440d00d0a803800d00c88e82820742c81c100a60120b44051f40002d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 498569901 1250 498568651 498568657
    0x80f040503041e0503100507230d02070303140108061e131b05010909061a090d0602180f0d0309090c020304050301090c1d0709030f060204050904051023150402 70
    0x1100703d00070f803401c685050f401500085849054424807920340500b005070368505c2120702400e81c69448403188040d074564914181040946084407140c1080705249c168040c0c4041c15115109039800b02d0082c410000000380040185c010081507001034082c003898143e0070480f403001d22000300d80383c031035981c1d944858410387c3d1241c140500f506146400484038565000494010f07140240c0311060344030b89411002c021546180540da50505910350003031074541482d00546414030000b8002c1a65803040e5490070309a0300800409120030103401c0b0350000318a010012500340300000d41e11b00a02d186503441c0107011010307078851841641d540d241c4482c61184244101d402400015000f8445c00c1982c8c580442914100e111320741e4203c000c1d21014089022100c40c0341c0c00b0701274a54901b43c1c05030a64898001131000000300300d400d95030801001909803034031028540f20314003a0019060380c0003820148400d03604201d00021605094900d82c541c00908030f040300350003644c80c4000307100400c65000810000c1c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 498571151 1250 498569901 498569909
    0x3050613211205132108010b0a0c0b1003080c010209040605062d0405040c02150606070f110d0209070807020609070503071809141b040b01050304080c0109081603021c080f04050304 79
    0x155071700c01e259001c640d19156101154049079658051a85d984100180c2805056000c0b0b0000d01c0840c011700203c1d0400c4030b019000030b287e9a078145403503900d030b807460700d580d2108180704502d035008a48215285003d20680005160a8a8051400f0110412002480201111308040101451840d096501c42c40140c40c080d10010704104035126000c24082c0d92060700c5107103c0c1c600a07802002a20314204a011340d00c100e58001d45414a5802c1030b45c440504111075400150030002c1e9481400240c1c0d500b0403c0d81c015009a01d8400060600e00ca000782803020040c592155a401802d040001c0d4400098280407103c2c680e420301d042c03001d9035201002a005002d8003a2200c0400d0818000814010071190f1340703485041d82c0c00090044000c140800d41d620301e041795010950601c00078000c908040700610440103510300004001d450755030f413070903150450f00c0c061040400720900503003010f4040200c008408600e00502419440c4240700a010480062183c05040b06007004902002000c1042e90098 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 498572401 1250 498571151 498571163
    0xb0f09010909061b020c0a08030406080103030503090f01110327060604020f09120c182403010216081309020403050604022b03050a0801170c190305061321120513 71
    0x244400030081d0f0f10024421024464807c1b120b0003c1c00e6003000084401720355445c1c0f20842540e1030f5481c01e40d07007500024010922801410b0340c95403404001c1c4100e0061070002d141c00c0351642413480030750042031014044490807401c1e14a0b000e0a6400010b921b070b511000489000d61b41e0588001d0b00303243d0703015900b40e4941009442c1d00d8259a0344011410724228807040d100010340080200984120103015140440c5404600030203604028201d8102540700001900161401e2400005003181d98003d41c13050302c40d100003103900514440e42c054902c000f0403041209504050550302d419468400c0500003c3c0314036801e098840d40b40c10020410005181c0d544422146402c82e401c024103140e000d40c601b20006450322002040c085c0c19400449002e49200d4010f083d0180c003001030240203000162070410f000800708000000541c104040303881504a47c080c158a6041842d00c08221110840b5807044158050300700c444450b0300048900c1100180000800d2039154100da0b400200c03c090000b0b03244c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 498573651 1250 498572401 498572441
    0x2030a091824090507050711100e09040b010f0506070203030d0c0e03070e010e0609011401120f0e0a050f060f0408070c150305070f030c0e09101205100b0f0901090906 73
    0x10400200182c00840780d10300c50a000654a03080e00301d0307640c42280001015080c81040c400d0713090800940300001041281000d000c1c0302903040002c0c807207540c11a411603400a4187c014040150409141c500401d0145d80c03c50400d5055800203071a80550051200d840e0360b50002d044019104050702c140c00031000d810349081c10b07121701400b41c7c3c00000340a0704254031117138000704640d403c096901c2030403103c07862001c41c200700c106001101c4c1b4000242c1407401c00c640b104104030b41c40c00c01e441408180010030006000407019031408508101601000600079002942003000000961540c140c0c09503005408a5a40743c1030b03c0c01d808035054a03041101e0100d00c04040201b450b8169124500420681d2a5001801c40081088050356402c5a080c80041c419014550b0507082082d8469001228071314403401081e2107100b03144c0314903079508044c1d8165001d0f4a14410840310340c428128001c8040da8450084990400444c46c0d2410601c82c4540c016650f09144082c8042c0768030100407203110401c4811 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 498574901 1250 498573651 498573701
    0x8090a1e14031e1804052509080f1506010819020301230f010e04022a0703120207080604030c05150c0309010b01050705120306010c0b1006030c02030a0918 68
    0x10b81c0790841404481c3c03100a98042e808100c402609803078102e9024101d0300c091030300d80004e00025020140a80e0540e4000c0340400c5541c4104440e2481c0d0380c0d155540d200f120a10302581140f074010b01a540c4450f980019204584802e01c10622030b90050080c01e00c80103940350303202000420348512001c281020700c040000308441c0c87c240fa01c060424807404001c001e100030081040358003003420700400d000c1043c4254801140c102034000d030250350402c3c80c80c6040203240302c49403101d150341c0304c11b41c24507a001198184100000c04c1007001200d207030751004002d00c0d0308055540c0d0b500c40f0054400ba081c0000b4526010030000308001d14020000603100306d0000d82045130001c0c0240e0826030b0180c86a508014941c40075510400a5076015034005005090903881c1c0080814940d001804907810405107016207000301da11003110714020400d403140f80c804c00346455401000c449014500e1403c40d0010003254400980c03041d503e40698884840140003000055544801003044a1101c481c6e44485103c0710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 498576151 1250 498574901 498574903
    0x1410090503030f070e31020f0403060c0203191422050a0501020a020303030c0c010e060c0d0c0314040308152707030c0c0f0302101a1008090a1e14 64
    0x9801402d18100c1e240c91621201400d481428078000180c0e04401b002285e2545140d148242c01c100c100034600310070004140711003502c141d900078042c407803c0b410000b13010010040c040c03041558905080c40594100220902401c0e0f180201c0700c4400100709030081c60031482220350046481c08c202c00c4510716600743c41c20f200520303104ca403403082078454610030500050300c1d400880c24006c0320b82e008000d98550354512223200001e0700110003440d159981c540800350041da007040120300034804203a0b070f15110550b84064800303541426540c44101400c110040403003100f2130030043e0b0496410704100110760f4601c04a0100d103448040020703405007800d20403044413503029015206c45d8042d16151501c03603507214019415914890130707080001c2d402c03101d11404160185141192035110788140c03a840b120030281a003d0321201420130100b40342038420940306203008072205c0854040e40c100305c400c1e49440102d0b103849400100024048066205250124460319401071241944c07250204d00c0305000c0100c0c003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 498577401 1250 498576151 498576157
    0x506090c041d0703020906030106030c180f0911040b04081b10050313030e041b11010b03032a15011706010302100c050a1506030506100f0501030e03090d08180402070f1410090503 78
    0xcd44040382001c0588403140760340020000a403544010710203285858001c1c038200506036440591001c160521000c15500031020040004081a100030440042000b00c0c0d600703c82c40b601c0d0010710804002d032450840d81e40004c150303a4080305e2070340021b0114546080c00c0e140358161010940c1e0081c684100d0080c0150101034002072044240d66080c030004242d00341c00d089440054040e80e065000b44400c00302054079642001c02c92002d0620800840d03840d0a4491a029103c10b41c180c911103240014006200a8103520b808010b48a0050030554519004200c00c6c49081c0404020048000e501c4400d101e010411540610351011074011a0340300704a9103c014070990004494074040c110204081801428600302a0740582d2181c5003043d107080c1c0150001c00c0c4140506c60140010302c844240c2d5520301403240940c0c0c0c014990203075254064000e611801003580c041750300c00d0303105111980100d01502c00030701010750310203410801e02100750042ca00c0c080d10b201d460300300c503809c102d00e5104000c004005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 498578651 1250 498577401 498577421
    0xf04090311010b0409022b0507060903030f0f0e060d0b0a0305030d2a031d1c080c070b06040e01020c0d020a0302010c050306011707091502010506090c041d070302090603010603 77
    0x8002e030f003046008100681e407070204081d40c4250300d0f0701c806580c1c00301c42c00700b0180055803004040c40352001e40e448904100e00c5512210206441c20400c1080c160400309001c05075501c0d00d060030034803405441c041d040490002d111070051002240c0e004040c10344d98042274440030002e00242e0190b5603841d0440e40ca80c403820700c110015081c04500c2c40c05140341c40c140328250340d2403c0c84c003440500030481200105600003016035940700c40100001e50710014011201d05c4071404c4100c0030641d003401c401414105c0043c090310500c500c00c101c0c0e400031640d120f0410743c000008071004201c0da04440002d9005e03004818090401e4042e1403c002d110703640005450000300e10a8000f0b001c00700c180f030001d4403580012103034a030100356008a62500ea50600180c10f50044060074607070b0f5010f0f1592800a8140a130034040c4c2e0150395610b052007007a103403400c0f140d030707008802a483e40d241c10309141c03a031501a041c01c58080c4510070414003040041c0d0081e0161080814040d000640381c1d070b541c1e403000f005041c503814 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 498579901 1250 498578651 498578653
    0x307060605040203040b0403080603030d05340210020705030403080a08040519021e031e07060206250c03120f09020405161b14030d0204150e0d08090f04090311 70
    0x4030024407070906000780c80c071882d00b00a420000c2d903282c3d103007a030f4000c10041c0b00b80d900d80002c005011005425206144c054440c044203004010a5400b10341b0802400010700640d1005001c43c034260035500003121a081c12101c80301589891292400c0303807840c012038000034402080441d0f54541c003507100300b1880c811400780044810b02c8000141000fa0070884000184d0840800000d01400c0358403040c422091301c0b001340854104200e0013860611702001038103152801c0d0441c18007000703803a9040015a070044c0040f900c01c080800818400c066800840809100703000c201c040820031716014880c82d0342200c8000c0414800c030346240c50214000c105686080384541d240101240d40322504c20110320528100352a88651090546400740740e11040000840380080041504140c208052001d0208440780301c2c40580c5590a080d100c440022504508404102c80c0052481076640c1d080e8840200c1900240410743e2014204040350480245c0c801d10b94002c3e04244000080503881008040c2a188881c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 498581151 1250 498579901 498579911
    0x6070c15050606030a2d02210606041a16050a0b070503042a0902122a04090209040e0f0a060605012102030606070b0405150a0507170402060405040608030706 69
    0x50300c200211036055501c19048003050002824400032030b80100c1045031140c81c08208007280d41078003400220b034909068001500421403060f0b810703010a132422002101800e116a0f482d0400104175a40141c0c803804620305040c440f80d103161203c400841d002100700003020350f420300715800c1107503031026009811070302d8241500000d062035214800b9640150781c003503001000036494030078490102c4502e1003401c990030511316000559054a01c001c100d184083c44403a00d807880c2000d0f9400740d8461100d203100005103842605c0401c3c1d401c00003150103444000d000147c80b0402500450b00804406542084a11840107440071246d000107244034124463348050066584801c01125180784282d00b08000d42c0c054070b80311603020441e0300510b41c819000f4003828104a602e03201c8440078142900c0070b032113641050803103a004242110b80705602c141d60407414002d07402c0a5070000c0c054020f9010a215060030340c0d0118045595100445005100080040c0030071500d8070541922544400000c440840c41c1c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 498582401 1250 498581151 498581183
    0x70e0a0e090615030a02010c0627060b010302040501020a0f03091d0a29040e0a08040e15092e0b1c06080c0306040f03140406030c030b030610060c02060c06070c 70
    0x1000d060f80150020300600300403012540103403075041207403104030b9145480311083c165600381d034120403492003001e145e410215401820024121036810345801d0403d0b004020900040c0d80000d11000a10303400344d140c0c104900103040840c0c0303d110a81080b441c181164180400c080c203040c0c05203015000e2540b0401c000c0d840f41c0c6001500035170380044420304c0ca46031252140d03d454958008a041c8400b80d0a40e80160b145e603036115503591254102450001c061018402e001c019510f814801c14001d80f50310056003481e441011104103041801c02d002201c1031080b81c800c1d400039803c50000c11814203095144c0048907026440175468943e400380d182d00d46600054080c50025180c001c01102801500c0d150f200c54440040d0001b05000030b46c01c0c001b403032018076909401e520007000140f001e59000180d0700016040102038a822280003882a40004140030980224010303c2d021252981801400e004091020410600410069118900551007044002034111800d0008980300350000000c3c4104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 498583651 1250 498582401 498582421
    0xf030806030d090b070c0803040303051201120807060207050c0306070203030105041404080a03050c1c050601030c170708090a05010203010f1e080714010e060706090b1005030a02040203070e0a0e0906 87
    0x781180e2000003603c0041c100a4100808010320104c0e000303070508070040d5298406603195602591049001450000d019600102c8095100f405000110700d0300c0903001254135a805503020341700300038252a90000d03003031080202c20840c050b0400340140c02d0b41d465141905000e91a60424451540900e04007a01c4280000b88000324500c21a8007460f01c034240010321070b003180203120041c40944c00e56010801c21505480c0b6041451580d0b1a6000208042c60804001001d90366008005000c1c0301d11620599a41200100480c1e40101360740381454260355014007031490f01c4854100074100754800000071940c10b80d84403030305d0251081e0445110308945400003426411150b03218082241e04045010301c41e501c4100d408680f81541450840d01c1c6d2945540001c0b01603004800843c2c00d00d548060210800144044840d8481c0248540e0044986460042a202d181c420383c001d00c160b40c004002049039015250000c4e0301d020107000a020251030320542012038000751210031051150f000060f400d0f400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 498584901 1250 498583651 498583663
    0x617062d0f0a0b03030c060a0506010905030f06010f09020304020607060b01091a0c011d070608060a030b0711060a0c1d0a08031b060903070f02060c1c0c1a070c0f0f0b040f03080603 79
    0x1b0300100a0903240e903104900c034010300303015051504000081d03d00040b550340420401e0010309014002d401c81c0d5151020345402c45c0c5107580710885050050041201690399001551201034011401180c1001c5a1004030f45e03a80c0981c018007803c1070b01602c0c24040e62041c1c0b02501d428801d610080002c440c4620240044007042c2e10003510b140c0c80b03001c003840110300c10070429402c010007500d01d001c001d440390f039201c5444204a42420014000010740380704140c0420919130000c0303078103030104840200001c3c000c120200c000180c4060810100619985469540811004048010580c0d88a08050791040b01091010b90413080d203101c0c510205100c50004801c50f03000c1940450f0090300b90420381d081c00110b03041840c512440d401484402070050b015803141146c1860950f0310b03000b03140e105240c40002c3c407110b0003841300d03070780ca02c0401c22180c540c016106640303094000c005101803420705e10f00702c02000c8402d080140816040e02c00d00040044103040e40e60f4041c481d417960001a95180185a601c1c030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 498586151 1250 498584901 498584917
    0x1005040203012d0b04050d0606030f12021501050a14030a08180109091109040504060b04090c05030706020a050d11030403082a031e0c101503060617062d0f0a0b0303 72
    0x90081100300001d21f0400310000046115500200d052a030301c1e2554403400075515810350f401300c4480011105540c0c10701c2101d80e84209000c1e18010b41d4185404a221000315000d42040200e0480c0c043e400380c5d074108481c400d01c03503000442d07e54900201c0c1c0c490101d0243c00388100c0c08161454800b02d41d41d1054041d4410400e01e03900701c07a080c0030701901080090400a003059503e10390350b46142c040c6803103602030284041c0c000d10111a070585850140352400f1501c1d44804215008802c0300c0000038008034121101082610b4124a4940798800d8107045114a41c030040010b50002007101018440b080ca0100d0322501001490515120309071481d22440740c819900182803040c183e0480719441c050241c81c9900c0481c01700c4090580c9544100112a9680c110680d041c281c00300420030040b0b103002c1c810161141040f00c4403901c0954584960b50345018007000c080b075a051145011909402c00040c501d1200322611032098141843ca64000300c1c0c0c00d5420104150a005030b0750014100041168084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 498587401 1250 498586151 498586169
    0x60a1406011b020904030e09150310091a06031e06010e0601090b09011d03010609020c0609070f1a133206040b0c0f030c160e041205031005040203012d 66
    0x50b801c164204031803078600800403014440100a46145515095a1144a5421201014007104088040500c0c0025030104202120b00303000303a071000621141005150054804628015611303181d0009003004070849590340150108641d2407019800054035904844040520881e60740f140001152015640e0140041540c810071880806504c581c0d402d4128601064071348424444803c0003a09450a66118244041d0040b5100c01c0354141400501c3d04010024000c282503440c1c201e42c2c04441c0954400e03009a42846400909900480350844044440c2c2c280b440c900f90384c459a40075200046052042244040b1441d65001d168240e00d07500c1e1319180040109062918120110000340d22021001d552401102003013501306100f00003820000d12070401405611810404131a0300700c4107a130111000044000521002c103000000030384e075004aa26005507a03588450184900c0825507021a801c01c1c4004000a640b849101c0c2030f07001c03160608003010300020295002542a20980507401c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 498588651 1250 498587401 498587447
    0xc03060e070e0c0a030e1204030c09020c061801090203190308130b0619080607030917040b070303050903070210110f012a110706030b1003021809090f060a140601 71
    0x441c02c010300281034540103174500442c02c1ca0400d0002410229021204585002c0100313040c802c000b0410380f6030000e803454450031420882c10040030f82e0b66110141004c042e071003901c06c04100720325080d040400c2613134001d401c5175040010010b0300c40034040d400381c2c03d070001981d050119440442c80f220809606401a000368480d031524000c02c05070554028221104402c10b0100241071003003031043c04d200d1911528002601c10140c18142107001281c481b0700500c44c010001480700380c00d4041900c00907901460000344942c2c948004611358492408003079444001c03002606951940b05c0e1002c100d05601c05c00742d4414010f0f46404a080c3e6a02c1ca414042c0e18043c0c4021000001d0603502c0c0754000607180c500307858010041c4100c10b0030004150055800a5121500006c541c18040d80c0c6446080d210300e02145004c0003440321b00c01301c10540c1000ca01c51844803010568005040060703000013074140b01501c0c0c0f035003480981c4d900140f04a1a80028211203500041c02d25801425101d4030143e1607140e042d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 498589901 1250 498588651 498588661
    0x1030510090e0f070311100c031b02012d02010e070608011202010306031a070207151b08040510030207020f0301050405030f0715020c0a051005060114070804120c03060e070e 76
    0x54040b08003424164424480e07040101d0000700301d2540118001e100e0a41d442c0720102c2070102ca5481d008011040c4850250094006030b0701030300f00d0145011003036014100781b00c64030040780c00c7c0180140c07600e40c00810000d088403c0c070720202d051280903490b40003082000701c0aa00142c40f140715104102c007080da08401048644584000800d03824130500d40024015242e60b10350482100e60072142c000d8180c82010000c0083e0100030842c040c155564800b080000741c5100141074445899078102c2800c044807070042003140070010384000c0d1400416091018941c107000034000d4015000507403180c0b43c402c42b1850352741010311038503010381c0e0000051403415080b28180d02c0d07280d0041c0701c200c0e1081454079040302c469400e840908507010104028008a42c02420600d140079200d20b668803d180c0b40205012090784c007d40208445183c603040c05842e90301500740241240600d62140e00f0300c100030a4500100700f44a41608140ca03c691030800906800000aa95404050240803c81244900814 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 498591151 1250 498589901 498589919
    0x702010c210b041103010609030b0c030f06010c050a14010f0501050409030c03081f14030609060121020111072907050d0c11181603150302060c150c04030201080601030510 75
    0x2e803107104050710100341d261046900c5911540242d0002d400920b1128040c0b0403c03c0201045030041411b61a0038250b0604140901000340080d0480f0f0603c00c01c4491801003000a1000c0120240c020341040400418459058043e2a41a85031000603207060b00110b4149030510900c01031a0701a40c41a01d001c3d00d658080d12403103005095007190664a410741500402c01039250000341170f40708000319030640c1c01000d061030208040c202ca020740d040a0010b014a001c01c100040368040c4908a07403d01a0b050700040e5000305160f00c90401030b008441012441c50000200608244800d03550401030409061041c04d03503008008008000750001801076101c00d1145080003169400340d06d101115414500000b00d08518850000c0140700300c88041000c06458400c1c044485480d0381814071a800c180d4031659220303e8140030003442120082006200301800304001c219111803050295040e007810012105160050b1004034001039056001440c5944240509070088800710000c041072402c0c40010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 498592401 1250 498591151 498591161
    0x51908060c0a1b080d0c080f0c0a09080f1e1603030810080d0e040501230d03020309030708011406040204050d0b09120a08010e1f15090b120702010c21 66
    0x1c000c2043c031a40644541a1103841e2280461050030510790360040110b600003615901140607090080110410890020509015501198480882e561013004240544000c006c80e0804200c6100d11110340358100f40010704120560303a591511607058a02e004c0c00c2d50354100d4403000144804540c0c508000090042c1207440d00100000350b00c01009480c0c103211460080b807500d0002c00202c007150303050010f083c6842001d000d4a821000c0e030f00d102c0560080988450055500c840c05441101b4608080c14420b000b03850000c0341c020b06403810b1550324003a660284c5107180004000034680702c04071ba1a403415108070b03400ca90340034202826048064840c0701200e00000c01140486c05284d00f4103070a030441ca80100710007071894a8501803075040024010300044001c0401d402001c014050402c08080c1981e00c01c2260220140a51031060000b4103e54105695100b00e41c022400304a9444101c0010780b020704c00d002d07d900030411681501d2048030003402543c0c1640400009040b003500400c04d907006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 498593651 1250 498592401 498592417
    0xc02030d0c090b07030201020a08060906010905090a0e1219091208180901091d0106050d02060d060509041a09060601090b090406030f121202070506073501051908060c 73
    0xc4080d565540e001d001e40c031a1300006007140103075400189203407416004036101c0d40060081d10342c040035180410001c3d0a601d41409003501c540303c80000900c492400b41c01c901ca9021445056a401400182d1007001507044808a4a1501c00c1c41d040c0840d9544a5103580c0c003120744c0540168800d200641710780111b580301e0144000380100200c0042c2403512080c000c00d00a1600500004282841c0c0700d1045210b82c1d550089180e0780d05140d410049560707940078072661503804a07650b5030b8551a100014004013013680c42250424100001c200502c424a0403202c24680d00d00c1c140026941e03030710006910b4180407074280c1d000c47c006210a211000c00c06000e0903100710041c0000603002c2d182e07103034980c1c4500c42c0e040480d43c2440684034802280d900c110703404041031440314191701300341c415034409071683d4006000c07404101591030031180c20000d103a83d03204da1444005007040e2103174508541200540c002d018050080000c0c03440c0c11583d1800040300030498440401400c0c40e41c981400f109110343c030003da = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 498594901 1250 498593651 498593657
    0x302010509032505190803041a12040f0311060610030f0f05040615120305161707060b030c010908030f030622020711010806060306040f1d0705030606040c02030d0c 72
    0xc000c11440d0358a01c003590a941282240f0a501e45440704020300130140c5080e21800104184d02005401e00000c1a50143d5184500758404145921813001c6d107800742e41011260548048140030520100d02e0558810034029510810b0404041d0440f03070b900d080c1680c0d0690401d80004140c0a414445d500107200b401f080f040c04540f840700c100311803007a203030166800d0707800c180d69205003008034022040302001807541c503040b40c41c0303070240d42c0700a0864000c0c10042d0142034072008030041000b0603003d4588000d031400708211788611060a20000401c1c3e8900194024422088410b20540c0101c800790201d502c494001e51414285881c01d104541025000540012000c140003180c0084403c4122032040c0c036400050710b07030045041180c40c412b9000942410b01081d00107201007038840d034007100d030701c41020b0314041203800125255000030b0102c50800f480c00e840051600700c0074800850207104a070021800c6036080c0e00c400c0104802c54080f4109d010140e44208003600383c94025800005442440d42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 498596151 1250 498594901 498594913
    0x503060d060e0f030408060f06090721050c0d0609060b370c0b0109020f04060c050c12010204050109090209030a120908030d020d0e070501140f16050604141501030201050903 76
    0x35100519180d103c9484403507541000c201803003002c4082241941c0498450341040050420380042410050042c1408042003603900014040d00c900b0f11441c245018400303801c0000340303440345400c143c6412104910584904249001480d0402d900441050b100143d104903d030141c5000504400c40340c1902d801484c41d5180d820380040c1c000e4080d80468080b00741c940c0c400072025440c295000c00b90580200303801510500880c40c091a10308103803003d50b20781c0d05101c0440b810605200e890183c8502070243c0c0302080044a50b00b204041d0040c20440d0420789910314a00e85920111007a400744c40900b94042e40001c1e0300e000440c00d00c004405030650203007003c464403130b201c9981c182194020041103644079000074007510512894459142040b1203080a849400c0c20720340001d0214120111005c1c03d0712002c030365040c80f20454011116141d209101c08035082c0c2091420a44030f0030102c409071001000060300c4078a104020580b46e00c021004802804035a09580c015038454100c42d43c036a070580700341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 498597401 1250 498596151 498596171
    0x14010e100e0f0d0834060e100903110c090624040b180a1403060109020a11070e0703060e0f0c070f0f050f0601080f0303011a1306050310050d030503060d06 68
    0x1e80902c0411340503c0d80300c1d03620811361942c101d06581c03100a028114000401000100d80d410070420403050788484c01207001c01c542010300d4a060070080c104141c0c0c0f49811129410590050104441d1800d1102515062a440c008001450808480c041e400401d0524040702a10340e191181c030840b0b0100c0c4a0608007911407040c24000d4028007240c000d0802c004503452028036000c001c0c94020007121600869800340700001c070b5143c2e50f040c490548000d40200d0600381450003041584e1460840104550030581d84040040c4603940075a0240082880e215005c00c401010300d13450b034407544810700344620030345460400e0200d0342d00000b003d442c18042c05c440f2078000340780f80102e06416030190009200b802c1c001c1020500f0004180d10481055100d81c44100e040c00c000b0013920f044584074400011070342c40e0841180060310940648071040040d000c00410000c0c4c108004e180211004690140da10340c8490512060300322780071010f000302d40103000041d00c2d49001d43c040000c00744608000b003014188 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 498598651 1250 498597401 498597409
    0x1209150109020a4a1806031c020f030a09090605010503010302010c03080709120f11010203130501030b1305040b0108060a0b0609041503050d1112032224020414010e100e0f 75
    0xc1c1e0140349213011604e400c00308a0704d41811441804040c81c41d0071025810402e0010303990f9036510315001120001c0310280d28020b0f00a111142041e5601d500350703540c5099042004013004440c0c02614040e520300759005c603c1c0c0d44503400341c07410303a075041c7c40d0b290f68180681c0301642c86600080c24103041106040d00840c2e0004541407410601c1d109040f4020001245d141103a011064203402c0b81c11980140401c180c0744a000c03000400702c44003824001603407125400070901010a52000654041c1440c0520040204c4490800d0403520079100340c1e040741d200e5032441c20985801035400f0703074884d0082c8035a014601c0e041c3d015800218605425851190f5030742d4400d8140325100d1003010220700120007441003082d00f405080d603a80c80704514145146402903891803160310103008a00d0045402e00070402300b28580f108218080c07540710300107496150a862840c06035215001c0d0011002c0b0700c0380003a40e554042d40340321051000040c030b12150240015821250300309070402107613000840300800945611 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 498599901 1250 498598651 498598757
    0xf0206030a02271003050c0d0c0e03030f21060102120a05070c09020409060504090804090209030f1015080604111e040906061d0c040612021209150109020a 68
    0x9201030312103d041080d03040009103640380c6501c9082c94200800c20045c00300d220304554403400d11020015080061400844109610008064062000240e12415480201d000d0504c0350004401d5801c0141041d0049040410a480860240e401410704891483d2644050108084145801c030b041034159190001590304680c4006d03072080e4006014049440c1c64090000904006d403420320500b841643e40c440d0611036403207130303600a0b0390206e50812155400d10580b1b5074040740e10120f0351004095400c041c002d00400c00c0158100d0300000001410000200e08644101d41025030910340200300c4082c00b40032180030070080c4020100109002072640c1d00d02c510580c480c007940000441038100701c0c110b00303244088441c0340c1481407080c0410503008001d000300c0301507800d5803038415201c6060100380c10290250285075140d066001080201c2d0500c000340d904a0a84900340d02d84190740d0383c10703825080740f02d4845a8800108102c15a400b002403806140d0000c540d0303a6250f00403014880300140b0601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 498601151 1250 498599901 498599947
    0x60d150504150603050a11040222090506180412260603060907030f030302090105040918060f0204150e0d1202030a020d0302030105010e0f18130302190f0206030a02 72
    0x40d034510030322050255580d46050010301c5100200300d114190740320280d942c80020001468241c01000c000303025211501aa0010007000144000e101c0003d001c808110030f042c01500152850400002c621745400b804103980c800032880c041d90345442d00e444014900001c080341c001030001c600d42151f80d4000c107060f1020200c1200341001200c1c107000041500b4400d014080340059031000704184041003c1c001280b040552604006a40b040000d005071114081e90707124941507071612102007143d4441c500386151051007110b08106204d0201600022402940180021b030781180c0300c2c03400c0b054002c4c0d2100309040c0c4000c00740e020640556170f03486441ca400c0c810b00c1005070000b058502e22150100810012401c107401c040d4103541c1860002040c440411160320300c2185c4249031443c0c5501c503003484811525001b401440c1a1510501d000d50040b03039080c049005114000404c04460048e61501c82c5465102d071081904009503001c001054002400c0d03003444580c20030960301c0c600c420000c00d481e20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 498602401 1250 498601151 498601193
    0x14060f01031101021e01150e0c03010e0718061d2e02010e0109110307060503071b03051b061503030c0a061e0903120e0d230705010216020a121703060d 66
    0x41d22205081f01211040b5031090148040c2172081c00000001c44007034078151008001c802c50984e55860741212110440702e1a121030094000c004035880d90302207a03400c00130460f4044130305107402200038042c4001d500c2c92000c080d01100d0050b60743c2d402480800c94160f04803440089004201c004081d400c54500c1c031422581303c1e203c182c0d1005c0c80e013814042ca01c01024a42491070541c41d01020241148002ca00c45c0130045031207280080405007da825035480c40d0000441104214800510541c0da034026070314503a40d0380b150102d0b070800d407400004480c40c0c4891100039110081440ea14400a44261511401080742040324203120101c14414220341030301a40d03c1c004001941c4c0ac0340c0046403d60304d112109034202d0201281e5168011651603643c543d0345400c1000d01c10f54064940c480d01852500800c50b5000141c2c4030200350030103c0e00f4a500e8001c0710b2040310666a0450b40c10720f0103040304003c10400c603090105a1082040015691040015052081c010f020382c0e141e41d031500c0000e90150807 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 498603651 1250 498602401 498602411
    0xb060c010902150711310f0e240711060f011d0114010f05040906080a060e0105090703141203090a05071a090420070302070314060f01031101021e01 65
    0x66241101002d14450703401c240c00b51401c500703615000744910985e114180a4103107004071498071441e0481e2801071615601c000d0701202800b52509014154030100f442000e800d151a1085003c3e0200d01034078004d01d805c460600701543d4100c0d44202500082402c41803003850f45c14154640c0c400d009083c0b0600c019940d21140e9814040000000d8002040d0701030801e2943c0014003035983e9000d8004c1c81c008003400c0a001006c40090102d8541c81150040310b6100e081071400540490006204082e0511500c030510484000702c58482c220fa40498400c916680400300c00c0010a1140c80c001d428204982d00340c403106801072110480700c0c0d005803600c03162a40124000002d010f070a11118019005011002095010000c684112800359908161290365034400b202401d150010400340502c148600107521840d050502a40301c2740240b10541c1e0006d19045060340d4420042071091180d540e40310b400c041642140c640601c8003075440d01c803074103600c9000400d05150301e80540585007201480c0021071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 498604901 1250 498603651 498603653
    0xb0a0909050a09121b020307090c11030c070e040618081c2c010608010608030a02250911070b0a0b1806030c0105251217160809010b060c0109 62
    0xc1215070040c81061801e2a107082000000d071040c2e5001800d24051a240d030215440010380c000e0300c034504500035810f00c070303120380080d0082c0c07541c0014000c907045844001d59866954155078031b0340700d560303101c540310340254009110300022841c0d0300d40c105014250006246e001e03243c80745c03040e1261040607540361002242e00c0b151480001e44504280c1d01008040c0600804907124550756001c8107082d1016440141c41c45840c84401d504c5a4001c204c11340090040f03654560286480744d1021a01130018000c1c00c00c002c031400d0002c20312511700f2001800e0b10710120320f402900d4000700010300300314020b001c00b0090f840100c0c00e40740c20680520000e600000d100703290801040f820000d140000482c00c1c84c2c500403c8429035010842c64422102803d02c1540c403034440d8a8000420248422220f64000c4014440103018201c080e140e9090259260601c0e440904414088075000854000d4000c2905556001080344121183c940102d10400046a030700c0c98100083c440360400150044280c1d55802180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 498606151 1250 498604901 498604919
    0x312100b182b080d090512071109010608070807300b030a0201050f031f031202160302100c03030e240c0a120504081216020f03040620070b0a09 63
    0x10200c0010810152010720448040c610001000036003e403031928040384681e44002e01d03801c810307205a8860242c8070441c513520800c08140e0895102070300d5801d4107020000140c24100a00c170306a46d515101e0782e41c2541e6902c02104d8480780142100100704420505a02c13015401e400b10340f104800040c002c480f0041440e41101b200d500200151099015141a4000d031341c0207070885000240c810a143d50320f80d1881812580c01000045016030840e8030003001040c0231030010300c824044815801c1c1e5100141c0002d00c51a842140e0001940c000c803c40180201c060140d0310181a081c801d003400704a0f40d1200b02c0850034800b0300c11b0401141030070079541d103030040f8010000719071003082d00c0802d80c100414100010281d40125048401d8103035980c001c20180807084059412460081d01481024508040030b00500700603912210702502c10030f080210501d1003c000d0318107852041e40e07420181e01441141c3c541d02070340c42c001114940202d850100b18031542d0002050790568075115140c01c0d07481c0031100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 498607401 1250 498606151 498606169
    0x714121e041101110616050304021f0c150603021503070c0b0924010b09011d1e040b0306040203030d0c140d1b0201021c0903031401080f0c01020c030312100b18 70
    0x104d89a40c128008101e6401c1041aa00b02c80c0c5046103040354680c0d1341c070310220f0955800790b40d400c54800d00321032403540344035444040c59144074811002d40320845110041d0300306403456400000d50202200641c403282e0388040024540c007040328602528000120703150400c9800c020f136020003080d08001d29440745004010704c207801e400a201981d000030340c527094400c2514062220003a04019402060550240418050803c081801002a041c5000c600510b510080203101603501890a1400304081c920f400b046081c440c0b038020b80590300d048001100c040052066030000c1c1c1c240203e4039400c550a44008000e450f11514030000015075003220360b9141c030000c00d20030350001168010000421680102034003c461080145070110b081d03452880c041c1c016142000d1064903184c00200009680701002804024100c01101614050807a0000498450980e4007520341c15600400000c55100881950680d01000c4d1124003844c5a4491503c10203541c8078044036080c504040b20503070301c01d1a1091035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 498608651 1250 498607401 498607427
    0xf0615170613031809060b031b130501050c03070b04060b010305061005091509040f06060f02210904110d0b03071203080708090c03010204030302150714121e041101 72
    0x20501440d008030681028800380070b005040280900304040803021003d910b4000c5d1400041c1400b00b50349414141c4855041211001030faa244030300084540c03c05c981c01c4803010304100f40c18900c80c0b404d00d0010b581c550711003003620303c0ca48020032120012400c5880c115021f988100004550580c68000043c1aa1005404584200d50400c42681c40c250440e013121400380e02034840056540714101043c0c420300410341c4c020381090819002d5101402198004800e41da00c6450307446110944603803c90365903220039004088800c4d040f0540d005500b03401c0103048015001400402c0f2000c0c082d110345042d400041417249019102c0059012a00c0c09101d5107001e000004d4103d0080c420030b80b030091000c0707800761154003481390030404103031310310790500141a807510098002e56a4660301c1c900295035801950000c40c610400c0008100124843e9000000d1b90501100c5a400d005101c40d02106001c80605000700c1c0d006d0100c002d00282c09c2028609104600510040144001d001e001401103d2440c40c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 498609901 1250 498608651 498608653
    0xa03061a0f03010603090303060317090108100f030f0507080a0c0f0e13110f06131404051605160204150305010506040e07060309110a080304080712020a060503040f061517 75
    0x1c6a01180c040419241154250724000c6980740d514107090f8001d02d0306403c00340540d007008805500c0103980a0003483d916000303a0350a64140c1e00d209105660314031034000c518450703500036801c00100d40c03000902490307103018406030340e04207503176004542c41c2c00c041c41030445a050199404010b0b1405404a45008002c5003581203154600100034001260a00380000c20300c1d00f080d41c1c403241303070780300d40e402581030b01c00141000d9030701c08000e88081d80b00d070704c00e00c1094800071940038031955509040c003809005894407880060103c4040406a403603800c0030384801003000301c0141b5580541d40b10b0040b80d040b004042245040d1906500301030b030a54200800e07050040c0d0420352030150007a0000341354022a015460f00040c003000c02d141110140c1c082da24501da00031983e101c0460001004001002107800c1c0d00100d4030060340c0c40454010a204c40d81d03001e5031180120300200406802500107680c810320541000e0305154080e650b900865030707003400c1c5014075101c5504c2400071170102401c104c1d010105034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 498611151 1250 498609901 498609907
    0x2031e0a150606021e0307060504050f301e030a09200d08031e040c060f080708071d0d0b150f03032502090f040c0b030124140a03061a 59
    0x200c3c040c0d6a118051108001c00c03810070200307001d00e0402d01c1503446041c1d02150901c1281040c2c10060b546000340301d101c1d8624000e64008400c6070309040c221456a08030100d20015507110203008140e50b4110507002e5210019020318a0b201204880003103204a860140015409096040401038400c00301c102071285010240d502c2001d41e10002c10341c1030680d00c080c4c01540e030741d1000c0340040e50b41194504280104c01a400380000c00030301010010584030075640e07019180342c078050f0803145040d0603a0008042130804002c240010720850440300e060b01d121614140040350000070078013424400d0300540340344007a90144800c8080e98480b000034804100d40030500045c101c00000d40328810b0b0350a10444120007111016140c00c6085484415900105564554038080c2ca48011501c8103c904603098500c11101140262104056074140c5215144000c0d0b140307007407844002346943e030b03465070410f00410b4007072020b01c01d0082c0300030702100340e990760042401440c0c0b52104094025200384044514018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 498612401 1250 498611151 498611159
    0x30f0b070e0f0f0111070e0a05060402091806010c0c08011d0102030108030a0804020d0209040c090b0402180d0f020a08070f14030a080a03020408121c0e070b0702031e0a1506 76
    0x20076140b040c0c1e40e003102e60014100c0000016900480046500e680d180542e0740000742101980c40200c1c070600e20004184101d5075410100812440b5840703400340d1005034052048202c40180403004d502070b10605001000c4000c3d5140c02e000000150302603403490b0745540520300120107405121008013800c1c40294110350504e000241c4030700481030140204884034001506650f2254a6401100d07005003080b842070505007000c0f40c02c841213001e1307080c0150a0100c40c0d415802c0500c00c81e11500c03410118490303981c0807141081401565050152003111880c110300001da5034800880c80200420030080051516014804500b100903511501c82c101400720a0692a140403413800d10035503025610b240d40d05035241c13042c1c000380150f8000c00858803c7c03001e0102a01c5540e001001c4240031100003020070008184040c2c1500c1101014003003913045640204012041c0d203000e0b18038a031004080c1d40c40c5420025100c0700c408612005c0300c2140d84407070090300902840d00b1400c0110002c0c01c1050020b9414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 498613651 1250 498612401 498612409
    0x3010905061b0f0d0e0d0206040309050f04020c060f06040b0607080304121803150f021c020f0c030d06030308060607050d08060f130903120b0f040209031501030f0b070e 74
    0x81862281d101d00c2c071030569580080c00121414106074403855600d8008840311040140054044482c01c0d1140380c01c2040d0980c00001c80911640d455070f00c10000904007020b10000c0c092502040e034005400717101c0001c080c9018040b080c41041e0001504906103070103020003060300c04106c3c04a01900c010420b00011800300c00441e90b00982011140031382d24901c0e40101d030140d0310207150b00c2a4206125020003009501031004c80251580d0304180268a02c00c0b180350101c2c8a20700c003031900e40444c404190380b491590f4010342240d098001005d802e280c0c0628411b41541d01144d5051a80d594942e000d0080581001040340c010105417009801d101143ea81c0c03958aa42e8a52010144145180029859900d2110784c17803103500702900740101115444241e81c083d10204904801241d0042440d400d110039511804601c09802000802c0750000002800000c2d030080214681500072140b00d18060b04078030500714000d42c402d081104102c2801d0501c5074071103801404042c02c01502d05d8050f04141c0c0c2d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 498614901 1250 498613651 498613663
    0xe0a0506030d17161106090604060506090112110a090f0506030d0503070503040b0411040c02011401170c19080607020d020111041508130501050705040906050d05060f1906140f03010905 81
    0xd440c011313549203100e5140c040e038500c824040392080e20f101c0c0004000f15840f0101d4110b0049103d9081482942c07504800c01c21803240c24095a00214250303028a17010a000002002c005034018000c030b98000d0300c9520007000e4440c0c10002c0d0034070b1034a400601070941010005424200709070b182607419030a04e070000401c6840b0241010303041800301d5000c1070502c406138a41c100103800041c0108442441140081d0103407025005621a45440c0800008c101c01c40f0340f8207003003602450001d09a1041510308000000d40781c6003010818a032002404900c15504000342401542aa002451602c03002e040003420f60341da80044c9252004107200401800301d0b0204600c4a02241c0c2c00c040d001390340c6100c0e01c510344aa0544000d0819820901400300803034000c001482541c28140040c003210742c4032000c1c8003128109180040c200d03408034000901c04440ca4900c0d6070040000508049079590441c07181064500f1508038104e82001d40010001514000390f118514400545c001d1007070410035158292504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 498616151 1250 498614901 498614911
    0x60b07030215061521040b01150801060f030f02190c1b03150504020105160b072007120302070e01300c06110c041107030206091b06130e0a0506030d17 66
    0x82c0045007046110301440e07400d1402c0e24030380c1c541701c60501d45800d2044180c4020311800d5030f100c8200484130340452040c111a410390300aa00d41046007941400124003c0c031110042184066007444291980b102d03c011084803100d00d0769403840c40178002d0408800410031004c03050082c0c0117455080000451222085031502c41d00c050001310743d030b95400145c940e8440c416500888141040321441040100300c00c075805260306940d84c032010f82541c2c0362021800880700d10001c003035205001c20054070098060040085110344165a009a540c204900b2695020f800c1030440e80500101c0c4040e404910355034007441440302d1604001499a5140c08500d4107071400740400300402d00d01141d400c4e68007000044204400508104420b0f0322880034000a508200c5080300180a0034000c40c150310400680c280713502c1d2420301d4000302c2c84030302810848175a1144001c01101da002941c002800a501040c19100340c400300004103461500da010181000c0c051604281880a01c5405c0c620b61001050784503801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 498617401 1250 498616151 498616189
    0x20c09040606032a0b0708031503070e0c0301090b150307030b040e0a0b0603100b09071b0b1602010f060b070f020301111c0b1014130504060b0703021506 67
    0x6a155820074002404458101a10301a10b0309018400c2c1243d0a041c040c850010f01010607070a41c4640c2510541c0c810980d001e803103030f2010710100f42d408880580c004010318000302210b464036501d0b401e07842d00640407244080c01000100c01041f60711103600456620100440300350900c10700d14400d4113003900002d01400c0416940c1c003000085074a4640c09032032080500d208444003802c952608511101c4100ca0550203406001800101404140102210424010329a03000c0d541d036010112030401c40b812941880886a08205002c504031000040c01401a070b4000d0149058200001e4256802c005001e4661445e056040050303040802c1600c0c007242c0c0c070800e4804030340107600000703015008251b003c40b0140000143c440380443d0030b03070110182171701e642c909205e02c6408208001c3d5541c5039070b0082021540c11200004030303900c40303001044009446c210b101092512207010504503011034000030140f0b100019a18149501001141c00c10f0036010220151440d010000c00c03030ed0706605112880c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 498618651 1250 498617401 498617419
    0x70503031e0306120316031b0f02060304111323010e060607030c05010e071d13033e120405030c101403150a090c02120d0603050a1a0f0106020c 63
    0x19a60b51303400000401c2100c1000c907a1550128040c0b028003044d1403170110003060b00421107a0145e02c4280c42c103030300d85070420a080001060768080c000b069000500844209103140c1d020030403940c40d46560382105001050000b2000d8802c90031100c00008051149443c1407004010022800c0c2c5420142c0d01c0b01d41651041c0d00e40315146001c1e1558103042e04020f1441d400d12a640747c100100041d04000c550079030281c102586000060407407500400e030340c41d00c1c40701103590b08000424081e41c01409803011898080d418030b1038130106160b504224000d86072940800c9407030201d20302020080000c5038620124203e00d464902000240e4800402c400742d80114a14006085a070307005540007003105000e000d0241c1d0724a00031207640c4c12415540d401d00c0c8205003044000c11403031218425100107040c1e94000308800800ea0382d44820a030004030000c8025520750401200091050256480f1288035881940c0ca802c1a81500390040500400c000c0030340030390302c004220b0540e00244d5000650015509920 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 498619901 1250 498618651 498618661
    0x3040c140604050409080a0e060c030d0c050909090604110a061e02030c100c03380a0504060806090f19081c0626031e130504051305070503031e03 64
    0x41d50040307602042d0302c64034082045090001d03400007824000e805640301e100d006040810050780b4080d0303011198590340240f0007990599541c0c0e2007000c404da003905105040c403c00d140014003000085444201e260000002d1000308030301c0e5603240c144200c0032500440d02030304002c0001c004113000c401c05040c80700c8494006816a0090044500c6114908140d40ca4440c02100c40f002030b0030710702c6143e4002490058407280311010441e0b449034808250307800031302c040d40162081c0c0c0c1d0b409803920301d2640704502200c001116500e9118000080003420041c04907460b103444035905080c41034807010000c0d0042d4441103060615081440c1030250322101c0e880d1a030350080c3c05002140c004160546005250050204245041440c5144001c550351078030400000e8100b41d6030307120301031601c90700c1c0c04541d000b81e041c45c607481c040003500581c4030f09034420340001ea407100010152a015591030184440c0f03108114140101030000c0030207003c0030340055240031042c030080d10f940780442e100060856400b0011038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 498621151 1250 498619901 498619909
    0x7061514100507140303040506041e03051c0b0a18050105040c0507020d0311060705030a0c1817010f05040804080f1f05061206010602031c1e0902011404030b100503010203040c14 78
    0x20350413000700032a51079251030300d400c0e651200c090718140c40c084c04400d800c1071340030b481001214600d9070550f502828150b220a4003140c240700c0704c900c00111500c608a10415440d04040c6c00010640c0c1051240c80b150238041aa0883c0c5060b00001d0050303040103012184039410004480040c0e40c1520324070060082d070304044960503071a00702640310780980401d2182850703011020714000c80c1001c0c1e00700040000f0a0050300c1207042c4400940c0078402d41e202c204081c031030180302400c2d956060070012503c8188803080401302d40b02190101d079042408101480049002c000c03070600005100e00800c01c0d4803145450210304494034804041017030f140c100191860b02d46c24408010701c065102103a0301541c4800000e5240d4106c21f4002c20605a0802c070f86d01e00d100240104e1303596200c8a10107c0e52000e00c020443c0c0070b8402c0342c0042c0d0501c881e42003100d42494106c3c008000541c000c00f4003003014240141c6003c1c50100e05e50115120340c0c014024040031030803110b000c0d0201c407010078041011030400c0000c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 498622401 1250 498621151 498621173
    0x31c08060a03080c061501020d020604080d020d02030f01060216060507260a08090c0f09060402130b0c07050102060a0209010e0f040b030d022103090a0818040207061514100507 77
    0x3864500c01041c00e411350b0000182c00350152910b84000341c1c0c0c56111100480e5550110700060700140d000d1400f180119100754001c0c075050310030185c054075060b03030700c01031364182d03031041e0782c61050405040700400096a05001481880c450604191007084c0750030320090050040c50303406440c0e0304040c88803120980462642c051000345025071141c942c06a507401500c2c8500c101c516440c24091402c800406160941403c4038600e401000303124191911824840203400041205041719990400418080b0b00300005e0034019030103000900d00241054002801c1c00c41c003400f40c84d400c600500c5510600da2708048014070380c01060b0303035000c9082648400a009008041e11403a09400b90a0381f9151255000c500b0350519040a83d0000a0155072603000318144070440e8915120740040084000181045000303080f0720120400320007038841e0560004049034400081121030a6950301d00805070b0b22002c12280081c001500b41020025040d00803903004542003044104201000850034100f195a00340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 498623651 1250 498622401 498622403
    0xa0b032d04061a030c0109030b040c030c0b030702070b18060901031407030207060501080d0f0f020a0b24033007081605250302010305130506090d0e031c08060a03 71
    0x81500c1e003042e0400c0002001582c084a40340700d0b010f082d40c000c80c14002600340c0c1107441a591200480d203035841c0c0d8000000040c2085031700500500000001c160711004800c003400d412443c0341d40c1c0b4149420085e2130160158131100148400703014600c0c3d0700c021012144016017040e40d00a95400d40140124001c11030214a25201d004c0c4d103040c00841a41741d8045c1c10340500c2440204a66600d8103000d41d42c07614041d600e400052002d65030010518450480025502000d004480c85c8a03081c0c0d443c00c11441c1c04659010301e00e46042400c0b130b5500100754581c01c0c0c16030258003410440c0005013441881ca01400511212580840820020403810380b00f11101140c02c208102d4840e2100e210003407002c20240b0055a0740e104020600b10303c0306c40c100c003410311003a40200b9203004902d07646c015400b0b008010942c240c42080381860201007842408024411805c20015003200104d18070041e01c1100c002e403165000f40d200c2910192142000581000703048146e09080341c0e5607407243c0020b110310040d600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 498624901 1250 498623651 498623731
    0x20915040213060201020904290103021c0e16232403040c03030f051206130603050d0f0206090c0d110a17010504021507150b040b030109050703110a0b03 67
    0x2d0024420380c0c10b42c00341c044900125428403450040406001c001d02d0f201010001030301419182c405c1941c025801414603000000746211118890313042e03e806c0b11441078ad80c1c0080d07080305c80c0304d50716004041c81083c0900240f07422141084c05402d00181c2500646c503070079009280d00d0340d0407140c103003010401d40500107414031055643e10305890a00000c9034144000c0b40460500a04850110702900a890300d0071820003441410790364550400c040e210006860181c0e40b681c4d040c001c00480c8080c080000810819210360203268003120009203040320040440340e07990401d04c0480b0b010740d10000780780c141d075801050710541034240c0000190340c0c91555125691202c2c603040040c250303080640240744551b008070f0310b000101042040c403541911a82c4d00045c61040500300d080ba210b1503560180110090143c40040c0c12030030080483c1c01c440d000b0310107840a900018040040010080c1601c145e65010344505259628060f03d401c9140009056000d01c0c07602d0030106400290b051548000d1030755018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 498626151 1250 498624901 498624937
    0x230c0d0804150504031401020a0507060b150d0203060a05040b0d0615080303040b012904050402070302330105060c06060915040c0f18030b16090504020a170a090209150402 75
    0x10b14068120740c45484100ca8501d0250704c84100300f41c040c800e0b2105c20040b502c2c0e180c60903801d0380c2c03400000d10008681d150311003004441d02040704401009880003102c64440142e0f01c0c1489001c03c50001417681c44144200e04064541e075044c2c441d28028214151f1208010a000308a0700b4803601000e420380044516120204c100000d06c00c50002c054100c40c486011020300381031951040800c090039051030401030304108000c00c454182580100541da02030b00c15070b000740c00c940307900c1c2000c0845070a4000080c0c14942050809910746404140100421207070a807130034484203020354542500504141c40342c58400001034050f800308a0b541c214801c000c10400c2040c6400380c015200d000300d003001500181d00b006c0d041038220301080403041641e0b0081c14032081940c40c4060804803a401c0944401084105400003404d9110f80c000360503001301e243c45804d800c10420038480b481400c02018890441c0c28000c0d00d00140c1c41d204901d0390000104c603c264160001a800304019202d0707507886145000c898 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 498627401 1250 498626151 498626189
    0x180c0406050d1107121206260c0a0611010b010e0f040905120a0504030605090f121c0f02030f071d0f0d150e0c06070c230d0302030403230c0d0804 64
    0x1000803910341000e98075410014640d00502c00704a841f00e0080c40e885141e1000c10742c20b20b228949a0100814510303045035621a00e00021900541650f03000001003910050444040038080c001d5825040080c03030041291182d910000d41c48490800755071f80510b594411181c14800d0521841c000040000001a0384d076100040007050350784944001e40f0f8a0f1714183c0031640d02d00c40826081514800c09005013840c00341c41c1000c1b00907500c84414211044218803148086030051f00030f9021076009581c0041c0c0300d01d80034140c50200040180f801080040d07001d0001c000044030402000030b080e080d41d1240b1407641d090b010070400c107150800a48030303a40415084d4aa401c9075040b184015030b2a9055484404d441400e02c03c0a001d0b0040050112500e078006001c07203030600b000c407031030546901c042846022103000070400044024030280c00503040090103009100d01765910042400c107a0310000150043c0c00020794540c06010b15940c0702c0c05d20314401206000010702030710081c0521016a00204400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 498628651 1250 498627401 498627413
    0x60f07020f0307180609050112020f12070902030a18120302030c120f06130b01120911151206061204020d060902120d0212120613020d05100302180c0406050d1107 71
    0xa144c92260325941030104c00700b114480c6006030b0b4129285034041e04c421982d140c1c2000110320144801d180c001c2c2018401d02c0d0b101008000481c02403080c05801039890030144001416281024404480c030340500001400003070f1f90300c0c0301104040d140c0c540182c41c1d40719481840042c0c8517660140036110024000d200241103610581c2d4014030007100c08261283c000c004440503904128141808038440544400c40e04020340c100c041c405204108181494651400041c5504a00c4041281494020540138203400c0042c4815410101c01c41e4000d0a0005801030031100907030043c0000d00401300c0b03101c01030812445801c6030564550003060f5480005c0c005813107a55a038039038500d543c014482c5061003501001200d08503001c5150094070201155100c03814448180c4c0000c0c1c06001d8a5070803c10030000ca0906c0c40f400c0c0c0115042d003030140c141d0745580108010715007414050003941c84084280040a0040b400b114119052400d045403103803c4180c094000b400d40881c603816074a0000717528010404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 498629901 1250 498628651 498628679
    0x6080a030f03050a091509050304031a071d06040311190605031518010e250c150c0807030b0303040803120f100e01030305070c15020607021b060f07020f0307 69
    0x46a9020007013651903441c04003d450a070740001d0501c881c205100100700d5520b401056030280214200c0349841c2c2d680d5101c010b40c00710100504080340e011010320000135407080301d16529070312000e02034010044003400a8114400d07440001d01c7c00c410030101c2034441d115000b443c646550350500030030440303603a264003404503402184d00080050a1f0101c1c101d0707502d06214090301c0d990750314071141e000d0b0b82030140088000b04c000d458240500340408000d07070024400c0105800700c00303003035480108002c241d1070300401040c8600c8486601e541400d55520b0320580c042d40590744030040e480c02042031042c2c2000309042d481207820081c0769003c00030b030103d0300505400440d40a808450b240c0c00781503580304400400e0248500038400503111180c010404603118078060503e1900414824015030b5540600c0141c6550002112001d88c0100b401c0203111901444510f5441d032841484074200700f41c60b00000c405105000445100c3c0f0008a41c2109640b50580c01e0040400301030200c8020303a0315003035001e940300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 498631151 1250 498629901 498629927
    0x4090309170a031209080d050c0702060315130c08042307030302010605030607030b0303190e04050403113c21030103060b061305041805010c0302090f0306010f030b040606080a03 78
    0x4281e20750440c220710051060701700b0f507504941c0d071a050450503c5808042c00c8041d1203030310207440601405000da0b0781c01c1300445c01203d0b030f05000741009095800b8412241032001c0c000c5046464203c21000c4140c010490301d40c4542d00c0b0340058004a00b4803101507010501c500300d0003051151160105c09c0507015803081081c3c0344114200d8900355201002202a1007843c200ba5404d03800501201c5a990500c600070301a60f500c03401c15403c1a2200c102090844e5011681603001501c0b10b5210350160f40203118030f42c035011004040c003501c1e06c015403c00440c501000d105841c0c00c800404c07204010b420038040d048400303005215a04903a6840c02c04510b45030006e010645866241071016201f82c80c10b10221820525040c0c032011781c032450841004018a820105070f4800c200150a4000003032080c41104203c00680e100141c54000d003106100c0801070312074041d4040d900110062000046011101c0c003141e50084440c1d0a50381c0d24a0008040c0c02a60f0101c080c0b4402c2071802c008164000245403004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 498632401 1250 498631151 498631157
    0x90509181c080115140a0c02040f0203041a060603130314030103030306240905220c09060908070b12040f05011503030809010c08041707021908070509090c04090309170a03 75
    0x59889900c9841d10813950520800400c008800d00304144040002400741408a0304080107098103c0d000704080c1d0314560a52100d0750b40c0001000b0030400101640455106100440301c51443c05001003896840058014140007500764800820140b29001444006003850126a00d0396524038000c1c0142c80240117910340000b500501d621001030743d684a03500c01c01e2541e5803070b43d0903150100740200441c070554000400b00b400303450803030f0003d03050003406050070b0203659280700c02e072610100825400858118242503049441c04000c04080d41040c2e0301c100302200d424080300c0c0ca85241800a221103a000101194200004c000c1c076030001c02c9031001164081e0311307081e02036130b60401003d003243c0d9080104000b103040c02e40424045502c00380c036084100800360000389031504980000b00840e01021006074884030440d02804402000c0c0726440082c401a101104a42442e42c40c179a1500c1c40940040d000365502c402090625201c3c0080e0340c018000c0404229800d07141100807a00c60600e00001c4d008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 498633651 1250 498632401 498632417
    0x1e03040506010815130f061a010f02030a12051305070b030f1e0708060316140f0d03320313050708241f170d03020901090509181c 57
    0x41c61001c40c01c00c19010b91401d011681740c0e41c01091095040707034140d05503480c601c07038003810000070018070400d00a49000003035000c118694100041c044140c1000040440d003060140000b4a87c002c8031204102e210541e000c02d4a03a9030102c100d0304410070b948040c10601c500d080002e00c0029405c006d40c000c01c501010408240c1d5440d0307490381b0907049003d901e43d0846480c000034203d075202e8420b998001c1401000c0c1c8125180c0c0c40802c80700c109031504884082c1208105c0f044275440d205038100b8620005440310b81441011782c501a000024a4214803660300007620810a28895940c8074409210b01460068407800c180403544540d003140e2504451505c01e2402c0800c5207000010315440500038030481d1000841e2003c80018280b501038603180041c5121050049070302c4401340c00c040500f0780c00c80445040742d4010303040d9140001403a043c1c4280b42c41004460280c1c1d80c499042c00c1038420036a440000b548441c240d942000c00780328180d0455000d9024040301c4e524060003054490700d0345941c0c02e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 498634901 1250 498633651 498633659
    0x61e07030206010f030c15031b1812050d050319090c051305090d1407051c02070e06030d0f1101050406020c0d1e111212040303110703090501050904021e0304050601 72
    0x180100c900e01001d0420400f40307400300840000c1202d080c7d601815854085070480320100b60f9611084e03c0600500801d0700c0b800803c8182e0180c0c84000014240e5050000e4450f001d40c552035229003034940c400041080c00000101000d00080034061048440c82c410003d1040904049007801418040c4511600070120100c016159a02560340107200c010068403d002d40c1d40d00c2a5080440c109101c1c1c040c034828851900807a6092005c210320646c603204003041036038030040080c20700002e0740047c0b5850700746030306000403510002065403002780d01d400d142007100c407258416120480c00115080d032660804041104005481d009080039079891000c480d00442803e100380c1d0100398511844256030b005001e00495244640c075051007030040300c400e4880c03002040b4001c480350b0313201807940d204a4001d08184400c041d4144941d54102c2400c0011a040812035540144985190310070641001804200d155807940c07164100e406400c120034180c082441d2403404c031050354000b114292071030700a1000005d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 498636151 1250 498634901 498634919
    0xf030203030a0c0e10051e0d02040608071b0f0f080c0c0a090b0609040b0f060c030a0e0906061606020408160f08010902130911061c0515031b061e0703020601 69
    0x104e0b0000070b00000140c1d103102e204640e81d4001180e035004081034001500c1e50001880010700b00c0d082040c00160b995401e168019020b218060092010030184103c40060000400e44c00c902095101c04540c1c00d20055007006001380d094a840034243c140c000030107084805002681c5840ea290036114600f40980c1c8000b4807040364058000c198205508000013206031905600200312035500405464042010700049070240d0020350f404040d560000501144007900617110b01071919044418004518003c008203180d400b40205001094440403828002c000e42c0c1e40580300600307015000c0707a240300e603800c42024042e5014442c1c1a00c1005102020424140600810074215000703440c40e0003506000c081d0100826003400c06459003a884990500c143c0d032b0354030003410503400302c2c0d85841d80540c021790100225a8003400d10b020304c15840c14100d2058802041c1c41002480035907044480301c5040c3c01140301407245202d0b603402d9807a81c14501c04507001d04e1010b0098940241e0031995260f0b00e40d4040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 498637401 1250 498636151 498636167
    0x30a11010e101e1d0405040512071b080109030c0618050d050703110d020c01050a020c0a0314061e0606092b03080c1e09061605010204060e03160519030f030203030a0c 73
    0x2c07040070340900d00201c80506183e0006c68210f4031035412200c0b01401340212044030380200703008072080e84083c4222410740310a44952000703003000100820200080350f40241126124160040420f07444000c1d03825464502c04580c01a43d40080c26a00c480c002d4480040c81d40e8043c803000c40200e030941241c903a0f0800e00141074000a010b5030010304034600b0020054440d6040a15510214031a01820800d00d86030300d10b4050085100740c0384004103400b01f040603410f01c0402003211900740400e07103013040c405660008158001d201a507030706a449403d00c002c141403e441d4100160f00c030300458a40221844484032255074180203aa0311181c41d00c0d81b150300c400754450b42c10b802d0107000c414155107404d044248000d200900000700f01c00d10342404882008184100f4400a40c1e499502103020030050f80c1101c980c640d181c108a02400c0d541e07a00307500c2403001c5034441c0565401404c1d846a002940c403801c10440020f9504004259214001851b00941d20b5008072919401035051452010405014100c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 498638651 1250 498637401 498637427
    0xd0c0206060d02060c030c07080a03030c030e1b1819060f0308030103081b0d091503060f09200304050c041a01080a050a06092f09030a11010e101e 64
    0x204a4202c0c1c0d4003003052030780001c18448040c0c017081203185a040020049a0000c02920001d024070817228140902115400346000c2c0c00e06050449c2511070540100300000041341400005144080701c00104081c0c098a0401c080c0351108513050120412078a001307104c1c81d82d01500d0a102841d180c0d202a490700380140702c020040041400107200041504002e400701364807020100749811581039520703142824001c14000130540ca0340c4184140c148403945481900a68241032110918001d1218484c800e14032802410580e0303404d11045550700400d203910400240c84400351a0304190501e07507203590544940034837a80c031308945c01d0043c106081c034903010f88005850700a641d41d141401e02d00540002060503001c143d80d0035010580d106d00f8404d010854582040c90b0f8510303242042c4202800340d00150041c0701c4942070050844a03980014081c5c9a6544110007c0c0301c010311100503100004900b80190340011028a00205107a002c10000141138604007514014800620141c0342005c00ca2a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 498639901 1250 498638651 498638659
    0x1f0906180e120d0b0a180c030c020309040b0301091b0905010801060b160c05062208060405280209010e09010b010807120e0a020603010806090d050a170604020903010906020d0c020606 80
    0x880c03100b02020001401000600f248045200155134000441c90500c60b0440c9803240e150780c0244071001005c3c406c40d4518030705403c080142200408003e503a9018940c0c4883c4603a46618401807140c400b900040100e981c031015103d40007214210071013412401d80100600b4616100c000a0720120500a000446506518170b520b44014a9403041d191106044240d580a040f90800129a15035a00603c84a061014285900000c801142030351208a034040300c2c0a500000a1001141000c982060103070302000043c1c011209403401e0025080c0d0040010b0f5110003198000600112240001032046241c14000c2203801030f014015920400141d4480c03000400d14000b04001e0901a40103400d0342d0004011203209001d29070004a2175031090300001401d130440001d0101e1043c082041d03100f00b5045040040c01c0101c0c610001b441c401c641100b01c0c040d10030520114500e81c8840e81221170154010700240503003013081c10600040c1d4080c42503401c000780ba002d28944000d10100360107010b420014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 498641151 1250 498639901 498639913
    0x1061403130f050f12180901150507150c1d06070b0a020904060504090507060206090d0c0b061c0609051642020d020c10050904051f0906180e 62
    0x1480b502c001c000e070320a0840d200e02c43c1280080f0006000c111034044c00307507499181a0f0354401e158001d0340305400c035801140036100b05001484044403240c0411020380c03452a1050300c403041402d01c0c0b418542810402030200f81703450282411b40350307c02d40041940e40d00ca0540340700c10340b1580074010144560706000c2c014a4440000c55420b81c0c5e560001e00aa84005101240d0983c1700c50000f0304075000380d202141d45600a8800304002e940600185a210035080083c040b4104000e00c0500007828881d001885031204100058095840da4082a24602d451250102c80c4d080c91038000300600c214581641d4610941460140284800f01c0c00300540741c0e805a2601c80d40601c49022000c250301900c502500c0107a90b85c0c42d540032000d1100e1415040f501d40c01024403002219003e81080c001100d44c1b4083c000950002052070b4100080f261654400c2da070026107651807000050200300d0350001038140701c40b568030000308003032903801140690351040403054044e20038081120480c0d50f11919a66035411030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 498642401 1250 498641151 498641153
    0x1b03070c020f1302070b07091a161a2418040528120305060904020f0a0f0b0a030608030a08190612030f030513030e06090a0e0c030106140313 62
    0x24110030440300d101406104904034110000b5101e4010388240c2040140d0200c3d4980c1032103420078003203800401034280048240d0402e280d4a0402044000304082014005005008080b8144500f140950041014410701d18007070f0000044c1c0da030079621030700c0700400c503106442035061209212203008030080082051003100c01004059000003003040e9068001c1c01c03a4114000803020035040e10550407040d034618021f06240149250f00310030a03650400d881c060810501e5190b204ea000e40140e0112271039a08018000005030010f846904a105080c0452000003445402c0201801000c4501d4406001c00713074840c140181c2c0e078010161442c00158040010804155181003034408100c007465010842c2a15540300c0014100c0e031400840010b501c00d40d07400301d2564940701e03040d085201054481c13008411914002d00c2c060007903200391b1150f0000105003a09a442948031301c02000368070702014403451300300d40c0c40c04290003d2041c040468903880e81c03c00030750f03511001c0f01c0c425072066010f4413180d126 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 498643651 1250 498642401 498642407
    0x6150102031c020d050403032304080f03091f0f0605010c0c031e08040e1012111c060515030c0306040812040f02030114150d03021c02070e100503061b0307 68
    0x4031541d002242d00b007095a4240000c1c1c01901d06c10b82c080c4d100071594403050303003c04040300c0480c1c07010146402904180710015044101315801e03d107503d04516200e40300d25102d03030708181d82d04860b10b0000071024100c040711000c607048054805a2144100496550344c4015135a00182001c001c082031840e04080c000203d44203808402d07200003a00520040d40b01e83d488603000c1e0701540220207121021000c20650b80103509440c07019003103228007440c9605031551690203000c0380c1919a441101141c9007540c3e04003030102e02e90207072600080c0502090500c0300300424180000e1050314040d02030242c0310000380c1000aa140e0240340e0088070a840d189001c0840b01c00072102500440b21001c229a4400c0540c0d401d001c0c054000c440c40c10b41254600b402c0c94060600300110040900a00c00c2d503105002203500894202e2980340c03030000700c540303034110314400300d08101c1c040d00043c0310841401d00b8080f070726440d034103601d00341c1d0001d0701100c1c4c5580f1303280d0800f40c46485411208000c40d00800014840c148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 498644901 1250 498643651 498643687
    0x206030a0207060b09010303030e010605120c040902040b0a030b061809150712060b03180d1710090e1e0102071721131b12140c04091101020615010203 66
    0x1c041d5500080c0c0c0c141c1d6000003088100203030701c1600022b07141c03944505829000c1c4900b41c0104401c5030380d0f14040610300425503c400140c94072920403a900c1010b0819904d5a0704840c203908401404600707100d85030b10703241e224040c042d60b04a000f54410480d80980d6084111020701a85401c00100807000c4001010211060000c103c8030800071000c0d10080030601d03502894010780f50314490b0980f41c0ca045001d0b202111158011a0610781c0f021000c603d8403500401c0e901d4140d0418030100600c0c1e41d41c40340600041d142a4048440703a498030683e02506180450043d07055800c504030003601d107201051440c00d07405040406441003054107241007800356a80010210440400c040c079250020340700802042c400100e95003a588022540c00e08200480b005003100b00015524405410900700087c40d002d0420b40d402c01001030100301d6140d944054104066885100010024071090000d460828134908400c4120341c054440c1302c0100b20018401c09002031800701c180d00a5041c445280c0380056a5a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 498646151 1250 498644901 498644903
    0x80115020708030f1b070501050d0b010e19180203060307090903020a05150712060815090a08070804060e09060d02040507091a071202030c12090a05030327030a0206030a0207 76
    0x101c1440390009045000344040c1c140e0301041e580315502c1d070542c960390213020005030a03184816000341c40d0a114586e0007200307031040c07004022400150030325144010f86200f0741c0560303140c0d401143c211021054184001d070003425540000030904c41070300001e610074140c0c003054411a0341904092011301000765141d1240075464083d1046030031101c240e403691400c240074582c0c160b007410000800c0024180e0400c07840c0b100c51000b6503042180d00e2802c207005858408900c1d18031400182940030510241040104e80840c80c1c110000030396980d001d1400c80f4480d405441507801082c1500601d0f034031490840c0086100d00707005004074041641c82d50801c001404000c144200303116060340081103202c103d401c00d41580001e40246542c85000c0d080100c2c4402c03619101760215481000050820b003404244070042031103407541c0e5030f01e075034a81001500c1190f403034000c99018480480d800040d01c07641403c10243c01c01c40c0b01d520503520410001d01d5114421900040c0d0055130030408240307a030030641c0c010301c146 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 498647401 1250 498646151 498646153
    0x152309250506070b07020105070e0901031103120a1701050409080702190b0f0705100501030f110102030f1206040c0906050702090a090602030403110105060d030801031b0504020c010204080c0f0108011502 89
    0x80d40d00c800005806030050761050343d5a0303164204000350795809104507078208460f4180501d04114003800580c012605001c010218070942d214481291800c001c0080100c001c1d441c46a00d80c9840314006200300000e02255008001410001909040c01d1040b07401aa1700030520600c1d2925603000d00c040303801c00801c4925580e40034200003542d442014003030103d00742900e00107543e9484604181e45000218102414114584001000050100c20201d0415913101c006450b1000955005030b0640c000d0408411040800042c4c040c0851458550b4503c509001c03923080024078682c0c0b10071680d109080c01080e001c00c5040060001500d4442142503000b41c02d054003184441c4c043c0c3d10380090341c005840484c003081481c01685801c13403080c0202c40d0b0062054a4403c0c0260054400038400da50611010380207030039218034803a405802a01c4e04014040140c4295901c100f001e8065000754024400e160450085013681c109500d07040e9080d5006641c141e68015469003821204071202000305502025 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 498648651 1250 498647401 498647473
    0x15080a020a0c080c01060e0f060303040501110a0c0e0103031b11040f29091e010e0601030207050d0206060a0b0f0403140a0f03030209102f0a152309 65
    0x140b43c9002002216444c5001045040c030b003261443d03203070b10040c25001c0e8041110b401c0101c203071000820340381214001d20704001c4120403d08a5400c0146c03291002d0310002c49003901241c2011421940e9048920960b1398044819100011013120003044000510f9083c00c0d10a4210074a082d401c602d030080b030841d400050004218a40c440000310002c031080350f01c00040366030241d80c43c102c0c0b0410f40c081d4640c1d88403400041052200c00d0b00c0e070014003c0340380c0140003101003841c44e446076041e02c01855200f81101d1200c46d0320b00c00650340300c44c21180790744656030405001c2040d41100f400d0301c61041c0b5102445040171b0543e03880a10300011580c100d030b12442440e421401107285400e2829403503000e034034016541d41c4000103000d80085407120881c2400201048200070901010060003c034420301281c1200c41001e03800300f410100e24100140c09040312021240348240198850b500e00818075281600b1210264910409207030203c4030480b941d00080a01c4400c0803802400f80498013284d004040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 498649901 1250 498648651 498648653
    0x1091a2e05040212010602070512061303120504140d05040515070302030c070b1c05010302091311040212090c0406061e090e090a0201090801060b070f150518060115080a020a0c 77
    0x2c1243c010440c4480c100403d000100407403501030240d039000d45001e0311400c05020218100e9507032940090101100e000028845a060500c101c15000301c401000300240168105030a06a4407004071543c9200325004542400d55214000c6003143c0031904054426856492907900100042d00105003d9040d4002000a004c0b1b500c030070701501e0060a0021280fa8803001f280840c2c10054031004040180349151100600240e541e502e029603010402d116080101032841c98011900c140e4018040e401500108850030882d805109aa04c44c221000c120361050100700304100c25038038907200b5980031545440c0e0321740358007090845806000f011401d004484036170b202103c00c1100411940e01c1329980010315071b41c04560340100801e0040c880c240080c0021400c0c4084880d00740704403580104201e0b582c0c080d0404005114229042c184040481009280351004030035200d0343c00d10b08202143d0007040004a48180b80c141103840344e90039541c0e145040ea59842c2e0035402940080082c0d028803500802c658 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 498651151 1250 498649901 498649909
    0x30c011404050d02010c0509060705010f0f1d03071a10080601030c17070602030901051e03040f05060f01080a08070516080706030e210915070501091a2e05 68
    0xd114080d480c0d03000c0c0034501d8581003882c105001407042c0021a41081c10305001c456004043c0c4120345000c0340c46603541c001c1d520f8124010720065042d50700660030080e1480089800760b002d142841940203080b480c080c00410003a8032482042402010702c0003a49610035524882c500c0d4581c4443c030a007801c0310182e10341c690b80d03107017000c26401292040030b514428095000300e40d042c0304046080c00003d20003e400c1032030207034803402890040c9040010121f1a80351104500398503686066010045955134181410702c044107880d400020303a403d114941c08558142441c0c5400d43c1211500c00141000e10242da440c900c09030302240050702c0d5442030004801e040c68181112100420074180241201840c04070098141c400030000800d40d0b4001d4058041400c084a60701d0500703810361507035196150386810005202004590240c1c055103404100300c000c0040c15440104040c4c05a07400341c42201702115120140d4004030380c08281d0403c1b01d140104d1903513903040c0484003d03503242030355a00591120089 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 498652401 1250 498651151 498651161
    0x1a07050604051b01020123130c0801050a18030504030204020702220902100f020a1506080a0501020403061b1d0f030a0305031012080f160f051605010504150c05030c01 73
    0x2d890325000342a070b250300320440350b03454a007100702800240045206c01240100d10f6010500208400302005c00244900c8025130542490503444070121607400d4030f030803440c3e00030481124220086450110542c07546006624403000441c2c3c1a03440341e140c0740c00d580c2804003035000440c1c00c0782c0018903505007041d0660921030300b0803c0030f0f903240005981121401000954485072504005010040c5a443e1285901050080c02d09800407802e0040c3380c05210740303a00a03c80307540300c0d0800f80210100c05040250640041c0200d90240c1002e02c0002040b810b150540b20a400b6000041128200544003200d011601188414002040c3c101081482400302e4180101c0c50400c900180000080100054490000b1700c0a0850042559880000c7d940e820381c16120301c4269520400703011030b00354007000c008010403c046234450300030100b15466240c0103664103d05140e07041c0c21800c03441c0c04510740d403003807041d28100d5180d41d25210110121140aa502c1c010943d000e070b4090208110b9502c20b444c090080b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 498653651 1250 498652401 498652403
    0x115060c170a1e170c1c1e240609050a210206040f03061404030203030403110f12070b06030f1b01030212010e010e0708190b12060702030310080a0c1a07050604 70
    0x1105001c6000030540510301c0402803a511701d100c070601c18200000350b13142503044030000032000014103685442900c10800480003000200c9414105545014920701c039291085003403480103054001d885100540b001b101c00e00071160040200f00040190b8407800060f5070714007154408407600d0b40142d4021030005c0e441a0010040b01140d0380b0f040041203600e2260b03940c002c7d0b50840c03407111414103980094682c4800740025040081c8920703800b0449805021610103414000125202103000004969081d0002901900c0420054000031602c0c20b02055451102200344060156072114502c88481c0c500c1840c0002c0c10550300740150380d0310500d140e0a1a018103400c0c5600d02c1c607585000c10041b61198002e141a040040100078050b1200e01160b480c0d0503480701c10000b180d17541015000c102c41043c8944158070310b1080c603060110303d41e0007000950245000d208444031003a00c9032085a034412140c80c004101d403001c05001c2080345065074043d6100340824102519001c490344070540b5082e4103840c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 498654901 1250 498653651 498653657
    0x9070521060109060203030c120c0c070909060c02010e150a060504050103230304031703190c0f0f020a0f150603140601091d031b19050115060c170a1e 66
    0x4180301003581c0022000f00204400e1004518629000d009000ea6000e0801c4209009500e80013280740805c2d01c5090300c040050b14800c84038000d55070745002025203c0c40c0300c1030710304034a0a00901c1d10184180034032540d10140400419180346001580d040c40b580c0100466805643c60300045440d6441d03004881c0218003609001c0c0d2600354410310a20b149040b0305601c000d5510400c000c00c00690200c2d00d0034124100d00341c0341c907201e1f601c0d0541000d400f401c4d6a010781c001391406608541c03880d04079003442e00c10381140da02c1071440c241e504400c1c3c1c0e640005041c0600270304003400402000801c0807241e50001400c0d0040810082d0741c0c0c1d90352850303e240c1d00412081d55041900144211600e03031040183c60384100d00404e1185080300c103c01d0712071003a40041400c44007141c40c1240e84200800004d4042e0a40c006082d0085e092400c0c214024180c036510b40d0b41402d40204006441442042c000c1c40381a000603444010101e90915070445034088500b200c00d2104040540c0690f0600c90301e1054640f0850b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 498656151 1250 498654901 498654967
    0x8180a080a0305130b030118020f09131a040501051e0406030f050d020609060c0913090804120b01140a151e030c0e01091a0a05090402161a0f06090705 66
    0x1d1340b50609014075400c083ca07191010710040200e20620740245001c03080d1500c00503618011014003404500ca12006281c0189135031514014004d0b05038014080f81c441e4602c101c80740700c01c138010042611020310450380d00c07022142d03040b611520703040000c0345100740050001469665940c1e590203c00e00390b0b1015207068100614400300990180006075001001c1c1018081520b068000c1350107600800e10070b01c0c0114230180318010700d0607003a4040460309400c9040c89844983d610142890340100300400c42d5080f10107800080c416200780c043e00007030880107000c003d001d410300c04040b006100224842040190045007154048201000e2107411000f03170741d01155218000e40c021309209510a45a410400c04103070421001960f0f90fa030064900303580e15403a945d40d9004208954034081c0680f0240e00510000750701d203002e51228003070092584920341080f182c00c107140000302001c40c201d030095070804030380340050280c2c640340e040d445c0d0003a45401e00a081241216a40c007030822103981c0552a62100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 498657401 1250 498656151 498656167
    0x14061c1113060216030818130209030f010b0a03060203070c212006180c0307150306050111030702060706020c0307110108010f0320042409110708180a080a0305 70
    0x81c6070600103008140010401c0001c004507500c5000700038071001c0d00341280407600a240c8009540a0350b4541c20042102c00d40901e001c80030802548140e40e03103031003817245007190707902003c06004038a500d090040600c010246035440b40320281d44001d001c1001c00050583c0d480016220081a581102104564280e10f4400820180c40c0c84d11030b0000c881014640c0c00002c1202c0e00020303d442c4c0c0324118405480c500110903552a00e000c0b01412001e526000302d0501007915281c4220703001d40310010b5581403061550702d00c0155000c50311040226503d800421100e005030400000a102c090302c1810014541010646020700f15040102d0460300c007840c092840c0001e41e07122032414090043c0c8a0355040b510b285036a203d4a180030460600056884026903441668881c0e00201018041203150390700740300b42e20360000c1003d420b8050840010f1070644039000801c84401078950701584203a00c10f05d02013408070000390f4601306880c016400070383d282001c00d2100b400c1c4603100c01d0500c01d49540d40c880c02c01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 498658651 1250 498657401 498657427
    0x20c100e0405011212030b030c0a121a010b0f03060d0609060207030201051803070f020f0402070c17010c050403260a090e130c030813080312040204140114061c11 71
    0x40c2d0040c51201303070806030f00001c60b804009254501c041d50400040300b03e0b406000c40e0400c818518050b520080280300014141000c1c417240d07424510900c0c1100f80006441c0280190700002e02a1002c2c0003011b00120311034014030b80065030402c2008051403000c2c4030581d240740603240e641100300c0c0d4254010510303804060302406044d07007002d0035442c040b070880310390b9106035602c0c003610760040d0070618104001002c2d9100d0080301300d0a584094010365031038501c2c0c144407a10190510a055111035941040010700e00188184040001039940700d52401d481e43e1500c0001e00419051841080c0306980808080058032005219113103540d02c1c2c400440f8030300055130510000c002d1400704106440740171040098014030b901025a684403000c0c40c0c40d13005203030110b903800e40c6940240000d84000644c0c400c01d1001c240c0d08510030f5100325014406d5075401c070704440c0390440a00c165080d20303240c03c0f1040c006140c01c0028059541100c0d15410703074004103025200a8940002110b20040400540f00c8001d41e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 498659901 1250 498658651 498658661
    0x403050c011b051804090b060d020f030d05070209010b0c031b16081b0108190203130c031a0112050607050309100f060e0609191e09030207060216120f03020c100e04 72
    0x1040f2010086c1e00096241c1c85120040100454031820850522004664500a00700803021000d4111381c8100c107440c00c050040d134000c2900f68419521040002007036010407080305c0050016a019604000301c808407801c80451070a107007201c43c00b507001d050b192144664a07200007006680001c00c2c20807210485200251b024000650400840a0400211040354207413043c040c220171200613600d036650f8603401f41000501e24020840300c80000c000080c8407503080d90006522004049001e16641d859141c103244080d41002041070300440c0000c0c10040c000c01c0590790003040141580c601609045094088885c01080968110381c2c4450038000c281ca0741400a6006005680024041c103280440100040032901d00e06403141c0c59105201003d00c0c141c8900f02d54050f01101480804030030304d0003170b442c0c000f107004400c01031080c11100341c0014054460841210950400703082c0602440c1c59100244540060075801c1d0310030300c00c0c040070035110f940b480403040d503d55807003031940c600340c3c010082955 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 498661151 1250 498659901 498659947
    0xc120c0f1506090c1d0604030c0b030f0f06030c0d05071502160b090105030a0b040612050c011106061c08040b0c030a120c0f030b041e0f0609140403050c011b05 70
    0x24030703100b0540c00c01500203012100c00314032100c1560417050b5200006141e841250070040c142c2070652800221845c102c0b012394060140503407018170070750380c17921029500002203440651560012800c18201c0c28249400c034500c034019002d07120380540300d17240c4a4881166400180050b0301900ca4050b008141c6040f000180603401106883e20000200003012800301078041c1c002555205140e036803a940301c0d07200030014695900200c01070281030400f162581d8002000c035000ca100b2004a048007040401c0b11440340e940100100034460b0100e030b040901003011007080303400e24010000812140060b401805846851400031541c0e0b048100c4010305d100c007900f281258031410004008606500008244d190f02e459150006d540c00e1000c0000f00609104c5050300c0313252120740340580c542e2103140c21002011000f0740051080559450b1050200c03481d070043d201c0c00322007210205001034860002030bc0712210280000c1807070341e2a10b0444000c003003c40200d00110f000041c04507011401d02020401030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 498662401 1250 498661151 498661169
    0xd140702010206040b371a090705160c151101050c040e060d06050403020c190e01050603041a100f080c01080a020f0c0304030624060c120c0f1506 64
    0x1120890340040d607581c0f000f403c020030740650600040d1313614080c90415950044134244000901e012900121960303c40e07042c0e0240300c2810402c01507010b803041c0704006080c503805001e040050f41c59550440d182c0d000011810811400d00050703e01090507841c01401034825248400009510300360003a02018444081800d00c1c1d041000304041a4028000e8070300f111050301c40275005039213a10005101c554110b0004100514100910080c10340c0081c565444150665030301040c600031400e00c0b0700c2407042e4400d030b400d04c500140041c02181011009550441c0c41410300040c03d05640d502a50032003422a000003502a40c1d201c2003010401c415000e8000b411640040c150a82c40c510000740004001031031800040e40004064a50584a20072140b0040c68041a2500d41e078491501030060840051260605410001d04225000365281d100e01110f083d500ca01b050350b8841d40c4d4020103010841d01c104144000c24036102c002c11088948410b07460b114107000d18000c520500f4000c1190080d400581032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 498663651 1250 498662401 498662407
    0x1206030604050c040b010e191e12020d0c0305100b0306060d0209040b1b160204060503010506010807081003141507031b0503100b040b071a040201051909050306090d14 73
    0x818000300f1980107125050300d011464844000041c1e44142150b1304090300950500003034030548441c84108002d03100c0030a01c0c94030010046201d815185c01038051900200310301048440145800140c144030341c5c1c46a04a2003069071340c0c0e00e0700350510211b007400c03c1416803a003648102a103410b00130503610241c1210110a03800d05074011400600c00100001c15003202e0a02142901d8181c0103070359110842c0d180d40d02d64031040c0030040c0c0800010004101c0c050f41c1807000100b082d1406005980c4114410303910b505c80e5680342c19040700c0c01100034045415400c2e0801d004004030b030400303040c141204001c500410745000e02c0007100140b00c80c0108103a0800d4913007607003048994016284e04602e03141c1c600d4416180e80382c404c6662882d0013540d20001501d030b0005000182444040c014055a41c01100c0c800050311101096188440d411507000b40000c03030400c0340303080309035540310b207444445200d28280d40e103107498501281c07400c1820b40c3e0306071340e5510110361000030590040108165500078492541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 498664901 1250 498663651 498663653
    0x4030b010f1a030a0b1521010b030403051e07050106090b0108090a080901110f060f040308010f06020316060b130e0f0309061204140d1706030109021003020d0609111206030604 77
    0x2003800041c0c0000c0c48107455418009090303940340711011000c6c1c14003405aa0350032032100701003260f020746a0011500c000707030f42c00040c07508104030503a0701c191342544603546800b101030f00404c485a10b691052900d50014400480812002d1040310090500700000181c8a41d803c0c00142182c00000c10010041c1e0200d4081400104080700b0364072900400c2c28540c221a0040805506004041c1ca0f0845540300d01801c0008480f40340c200640528065191404941d0702c1c0c0d4816602c08041c0d0242801592082203401d18050b0010408030790b003401084002402d1241c280000c01072101c2c003d4044100d506c80300c4e40c900c0a2014050f11000d42400001545001028004591070340100307000707800040e5100f00000c05024044a0380c030080d03081d0005580034201141e6000d850407212441717001702ea0134808006511401d0510840d00b96070b8000f4807544c01c00e203003e0801c030043e41c00b0069068009844010000705d541e01406400c1c20340d4201408151603590404180c4820000104201e11071780c00001400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 498666151 1250 498664901 498664949
    0x5040e130f0318050312090414100b1b010213090f151a040f03050f16061b11120714010f080a110909132303040b09030a0804030b010f 59
    0x2004940c0c5810700d0383d5801d40801612410300e903598041078141c0150980f040301c0c41007510041c070290008950400083d0704106401e1540c0c2030480c2d0501c5d11544040043c007042c4080c0b40503121584104062210301d100e41c4141e1803d80e0090046400400321042c001c0c840180d40d8010006800f280b500c04100241e4017a41070040e814543c0725001e12095141c82506001440704101c40c0035144a000501045a5900e42650b499401c4c1380d01080501505002c4560800c808401c0c0040300c0143c1d440d04000055076008400003030084800300c81950b40281c2e00c1070651110b006a071b071585420400703040c0c0c0303602d407051400c1004a071540c9103040041e5030090b0928030741c100ca8010f8104000580c00a000d68210f40c0c0d2402d1172042101441d485543c0904002c0c980d0181c48000d01c034184940300c04000d0200d0406080040303100300d161445190000d00c018403188072014068118400300400b180c0c89100d070754541e03480300d0780710f50000e4480006100042c008811000c0681c402009095036006136520307507107258 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 498667401 1250 498666151 498666173
    0x180102090d0b19020a200118050703110f130c090e01060f09150206220807241103061306050a0308071a0115080603031b0c0f12061b12010605040e13 65
    0x610501b2003007221140c2c0414254040071448071090106d4980300035030704126603280541c2c807048078542185a070342d074100d0070002e24450180d00701400030040410a0b850003000703045590310090410200d03036000201480d80030800c500030211500c030b1821070f00c54008010210b05e0b5680002003503491620450800c1d03540000e685500841ca41c00601c8150040000080c028401c1c6801416a030804243c0109106003007a8081600d100d0010030115031191300740c1b180c00d80301c800703100380c2e00b0351010700008000d810b06c40b0f5442c0045808250000740c00b03458000240011046400030348031110b0214024042003000d8031803807401c02d03a1204405042d8501901404204000803034a03080003141c20103d0050b4604000381c0320051040410300590b90f50740143c2c655550300325440944660020544025603060400782d0b4203541012001500003070307803501502da1900300c200311084c4080301c00300803500050240c0d00826019162941c1c0d62551640362010000681e0301c0904024920401e0903a05030000b46c0c24002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 498668651 1250 498667401 498667427
    0x20307030b0c07080a020303060a060e100503180f06040507050a0f15050d0509010f0c180510020a02090411030c010504180f0e0304060233180102090d0b19020a 70
    0x1003a0364682d19001807203403034020701e10020711050000c1071000d8159004400703980715000982c0ca40c20080c1d41c80300c0495070524200f00c0140c010302000b044190b064440d200540d84504041013040b004038501041515000c4c407401541016000036040c002040030a01c0107030001c5c44102e50080e000c9045c00031054480703000d0301c01d007008006c101481d4448107026009075011194416010481340c549801c01d9806003038048200e1003458507000c009104d2901076000e03c0740303c15a038004d9202c514144000d00c5000c0403144042c0040d4840d04403804016640d4510984c4118810102550341d0001c00c0141481d09041d00760050600c40c01344414807400301107841a0084003002e8001140075510160b0390340060468107004d04848c0000203001c19100c4c0c0015030700070480c0961040c12a02e07500701d0070706c01441000d1680b02c010030311903070007084884a03510900441019100300041c540340c80500001c00306c6180480441e83d02d00c0103401c100310800720b0390a401c1c0300004e2610940c40c0402a00c5c00814101c03c000d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 498669901 1250 498668651 498668663
    0x10b1203090a0b0a1b080a08161d13110c30092e0206090105370216030f140a14160602030108061e0a020d151503110702030703 56
    0x56111400c1c2c42a05805c445580304044404495800d0510402030741c080e5402c1800b181c10361000c20400403030400c0c0301c00700e4841607030f4400c550f518907400c03803c2c911812280951701001000d811042d210301c5100e034040a421800c1259591584c8040090a2440884043c1c00c089203456240b4284005661507014103100461002e96a45424001034100c1da1150750240700b418a40c0440c2e004041d0000e203c06444600382c084814540d2954040d5082c1d031401c03602c002401b654204030613221010b15040c20020300241d0b4036180c0c0f02000d09004422070300940750307030000340327000035581814103400440c115240ca070249088aa020079005440b40b040c854030002c28200210400c41c8140307030140800b6101d8101010b070b02102c0120060030075001a40083c05815654010710011400c00c1c0704002c0e010035007214000410f8500c0d501d80609a009402c824034003c5a9900d6252804580000300700d10700203483c4600c245c050380400c82c0c200408131140c0f204402d136410010000d440c0035a03000a8100200c1b64460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 498671151 1250 498669901 498669907
    0x1091b080c04050a0e1b040e010b0d0b070504091802010f080f04120903060e0a110102061306110403080d0606180e0402091b03040f030e0a180504080912010b1203090a0b 74
    0x140350b220003440002100c0b80103001b510b007580c0841811099440e8848401c8a092003600800700d41282258000c2500580c0900b440140c1f40019000d00b55259001c0e40e00d0424500705980c455455043c1c5901140080d61180704d00c103242d0442da04a0148100c800c51031500c08424502240b60919985024001030030700301c103581d41560b4031441401c428003c2d40e0b0100c0d050110440c48404143c0d11807210360201c0311231004c1e203007003004c9501c0064554801c0d0040b044e0050340300201d0700d0707070002441c900700c0c04410680c04100100100e604075004100000c0c1c4941c0000e003040c030300403004040c00150100e000044c0600a410042e45441c04400c0e600300303070101c6d00c54482e40c6034800301c1c0101c002907044440300b41c0404402c01080c049046440c00e075080c080d4450280002000007040034600e054040c500c0c01d80f80714517207441e424030b01d540305075807082c0b0038410035140c580c000d00002d1020200c0c0d5440441a91100c115602c01c0c01c00c45036031461061000011410001c1450010352804101c2c0a401c1e2001004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 498672401 1250 498671151 498671161
    0x21c0509010c02040b27060f1809070f03080c0c0108010f050613090509070f0504091509051204080c0a08010c020a030804031211070b06090403090b0d0603080a0201091b080c0405 78
    0x56100c010605c0e8014210030700200c0882e940f8408041d40410024000804400134800341044155001081802403402d0302500c8140020f1452170340181c6406590b00c6816008142c4014200d5a24081c50041424644614146001c01d28125441d00b80c9030400940384010032000354944e50351001e60740c04071869a280c2002c03500c0e501410036503071700040324241801c00b84010f804002c0b80200581d4501523071007200c0c0c1d407170b0f006100c16540c0180c001044848410b0b08005040c0c40341d44000c040c1d5108200759901c002518230000d0554206400c114601d0b0400d902803e0145001241200100f00180082c05515503501010b0340f01d41c018074003d41441202400101054031402c80d0500305070800d8000c0003840042c074022041504039440441c1e08488110200702c00e0328203001c441c1c1c8615415070301d588a0394200700720010b0542180030b5038824140c80760800700018109101529120000303034000986d119182c104030142c1c400311082c60321010340b001000c0c404014081380c2c05801d040b059401050680354 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 498673651 1250 498672401 498672409
    0x213110d09031418101404170a0609140c121002090a09110a030c05120411030f07090b01080c0a09050d080405100f080912090f010c021e01021c0509010c02 68
    0x4030424601030620000d202402c9070300c0d40600d92285103041e17805080b06000d086056826540c084019103502070b0500041040d20b02c100382e1150440d041909561215565070b95000c199551141c08a600710500d0180d01880320b0104416000d80c14101c40012008a00b030700724544441001e0014082240c002036000503e8a40e101104002c00025100b04140304a40844208541004601d900040d040c42010f0f010b1a10403002d036402003505103540c10868a42e5540e6100c4070045c0707114160035005441400c4c10809040c04080000d04402201013281d05001000401200c401060a4a005014891044181d5000108c042910002e8078030007104070041c206030724140a181d1040e540401c40f02d8580c64142e60040c0700d10000300072074542800e0b03030311180756150316481d0840504800c0013003440001c00c0b510300340100440180c011706080320814001d40100303101940040380d0380948035642d00d5100780340d681040301001454140c411016150380c1502d0040a0703200c1d000410381001640c2c4020790075903803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 498674901 1250 498673651 498673667
    0xa03050d0203101e06030f0203040305120405071208040e0649200a05060d020d0609151a040f05010c151815060b03060105030a0b1c0213110d0903 64
    0x4c000c2042080c03c036420f8880900d1a491401172a0020b410b01030a5110300c110b60003a24002d55041d100d042c1080c2c000380c80c000c5001e000400c165058820200002403583c2030740c07c5400034138000d194490f620b90405801d040f0300e0780e01030304040c0a1001c4c103c0c001070410070340003401c418460725814a0f0b21880d602010990404802e402101e904400d250008100401042180105024144950b00205045041200160307141c490590001c904001e9100c00c0e500ca5401006580e40e413101c005801900c032444142200c05100348081c05400d240d5003172240144006002c3e41d20100118851300d000d05141c109103500e0120301c83d80341800034000c052002c20a41100c00d0307958040583c020071024200b202c0410030381c0e6052009980340301042c900c07144055814040c0c081510704d492219440c40e1a803100440c2d080c0d000501e000250740c3d98109009083d52080181083c0348a8100c09203200c44850041002144011400305c3d0324030702e84000100c00c480154140c4201c52402c08001a03c0714540c1405e80e0070754 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 498676151 1250 498674901 498674909
    0x405060c0a1e0506150a180f02040905270304090b1309060b0a060809030405010e0117011404050a0b0a0302060d140117060714031f03150f0b01020a03050d020310 71
    0xb840110400030003511480c05003080d60b00031000ca40141d1126804050031070112080e154218025140600030604103804160080600c80390024a03c04081c840000300c1e08a50010b401c415240c50900000c0455640c4888031030400e90343c48640081e0903100c02c3d0b500d124610031901c0403601c2d8003c081036542d90700d00e030f91101c48211100703001100751460000c2c014013450032164403605013010049101b0748101441c0b48075244a034010b603d0903040c140150303410396003186480c0c10445042c14800040309441d81a50003400d00401c521074800703803403040105491317008040700f074a5407030030010f8680c0b030b13441246000489405596255845d240091070501a060405182c41143c00890002680351076440401c2031195030302d000d8134850f84603100c0840c5e0190a021880261981c01c2c408103450040740300c0040312940440c40caa030001656035036040d003075541680d0b00d441c1003030b941d44a0015a100c0c42c003c040e451902407025040300c503003680c2c010b0034501920b1581d610b141d5011000411000340155004003038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 498677401 1250 498676151 498676163
    0x803041101090b25020d0c0e09030a2a0f03110105060103091509080910111c0917010f0e0109050d0e0a090b0609030604050d020f06041203050718080c030613080405060c0a 75
    0x1b000301e080c03a2102145904c20001183c03040000100160008000da5440d1105656002e02c089000c2d00f07061100d54504503071104a00030b00048500198079047c1100381548251980b00c245014a005242142d000031701c15414076040243c000001203440342c0c0012245200640051901c100d802c02070366a00031024825000941e405003244916040308035042c0d03020b9a541210b050110804139450041d52001800d4086540040305019800700020841e0b103216260000007141c0e2601e00e120801c2d200d070140042d826954a8005105000d010f0000102c0c411190400080c04184440443c506c494280b0412900395030f2110741000542c0e441c0101ca030301c128003c04540c01410311f400c0c0291036080404900001d44504199140000c10201c0c0840c030440d00410a14110301e0902e00603005400d0003060f0108104103032314000c01d4880b00480b0030020308030400042082641c802c0a042c03a0075805000003402482c0d00c05020b001400c10804c41f01079031029105281c944c943c0355010f501d44030010380b0081c26 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 498678651 1250 498677401 498677419
    0x11010e010c030b0f0f1f0c1a0610080f0112080d110a090e010515030403030e0a0c0f09140a1805030a050d050c0c100c0c0f0803041101090b2502 63
    0x55034543c103c03a403030f0082115402c40f103008000c10856042c1d030b03100c20144c110310020078460303401c440c000848101d5161414803081641caa075950400c3d041038500c010686205110a000d040d041400d81c0071881000c60500c4c3c0e2140c00e048101c1d40608505100e8801c414002e444080d04000000d001c0e10150102a2800d0009110510304107540d40c02083c58440011a172140005152292007551030407a0390107000c0707c2d28031045c82c4521344154001030040d014551110380072551070f002000398620f810300654802856604092180388028580e6100c0d00c40c2d9070512034940ba81100283c49213030080c0740d420b00090401c680c545483c0b030580e1201401f900c03030701002c02c44540c0d00350007500400004901a6040111b5601e121801c0c0c503c0c0075029503183c030ac0e4410b00c4210040d2081d41e018008250250401400610465458820781e0110034001c954600f000700074030003005844c8400d1403007820700342450000d040c28800200403034003440c1503030041c0c88020601e00000080c3e400c010250302d42c015100307180c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 498679901 1250 498678651 498678671
    0x4030f05030c1606080408071a160807030207051504051222060906080403110313060302180411220918020f04050c07110a0e18060906041211010e01 65
    0x103120703000346181422034003c246110320a042004001d5058440c1511449084d40711a2110880c5401ca820100c541442020100c40308184201d4010303c2111100342d07100c2000c844d4038004007a014003070008028140184689000610302085410500d10300c010180c0155403103040481c5000c1144036a00a20000054030400890707146015100311003900d40b207403417010354840d41121008118445c0d400041e8094000c01d0029100391040946007050008990400d000e04481200100c015407010003c00c3c0d0015803a18003078208514030700541000c440400541c071810031803044600c94071500007038004200c2c0c96000244845068900a40007012040028140440c815001440d4440c003c3c2e00c1504102048115450680a020707c1080307801505070811519607101d0a02203454154540e008040034004240803800313148180c49511150390308440381e2102c3c490581884009000003801c0d0700840100808070700204140b030f88072882d0b858580d4030006100300041c014020701d000413040d0350070103c07018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 498681151 1250 498679901 498679903
    0x91003050c070210090f0602070e0703021b0105010609051201020c0a03120e07031113110d090201030902060708041d0405030702093d0609050a0501050a2105040b060603042604030f05 80
    0x207400e0386c0c80820700d03101d260b45804003645d40d0502c42c4130b40f64441850000003010700b8031a40160520840003a07203a103513181400e40c8542910002d800610003e960150100810325250042062240740e0b0740c02107181034602ea100584980105401a09011414844a58200c46030b8000104011580252880d0a48a180c00040c44655104040c422182c1502600440e006485008004a000c5450030300e0700c0c3d0290040c101501d0a00c00030390515a8034030120000d601c0c0c403030003864007d00c0740020300e0751142070a81d0031000c036105d204d5011a1490380030410000520000c01c031000503404603181801540c50510b030100c0d084144158008042a0450190030036844072084100380403000a03441281c1e0702c071082150084000e11401d030740304c1c18441301080340303501400003060606558031340180100841c1c6e007500740c80100d042c45604015900c0d0100000d20084003160754100400300d03403a40c61030410341c90748045807280000107120381c1c0c1c1c14031745202030f0511802207400645d40518040c00e0b8040b42d041c45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 498682401 1250 498681151 498681167
    0x40303061a0903060103033504050d0f08010b03040f02030a1104060503150109020a02010b0d08120c030c0304140f0f10110a050304060c140408030c12091003050c070210 74
    0x4010382418010096940701c0010156841204050f00a004603841c1d0740b011983c0780781d2241900107030305151000b00c1020580d81c6208484403000303840b12510b41821b141c413034507121050150004018090391300c1146998082c2c0701c0c50440f00c0c044401c2d030310b0307803214100309101e8005258000c0d45403140c007071180c0c10008a159051007655084408001e1140d881c0300381610b42a05040a00400c000d04005012a050300c1d4040c128985543c030001945e5259540480c43c1068025410b4600400110301078841c03150000849501c14012504542581825545841c05000c050401044644080320b48514420208070900001d810740301107070303c5e480c02242c4164888001003140c1102905150680f07007501c804204032000c20006580d1940b1750b58454a50030001e0076040c0190040240901000f282184600042c00103811008003035682c03040d01c008198908400003911031040c6ca0706200062851390f030902d11111003401810003042c0c5d80d452a86000103403161140003980301403010701828510f5401900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 498683651 1250 498682401 498682409
    0x40e0a061b0905010815100504091b1e020a0507170f06010510051318020d0b030a050d0e042a0207062a0311010515100c12080c1204030306 61
    0x30801000c026550320088405203680400042256208108841d5109171030701ca0303000000011102020740e203a00043c4010111700c54080001c0c2c004035051000fa50326124007800c8a03c0700600300c002082c0d80b0400f40001e6030207960a80512035800928403240c1c028046034640c50340c480d040d41c800c01e885801030003036420103c00e0800e00348204940c000142c00001102ca050f2503000740801ca0b940c58040045446500404900e6120300c4040d100003804642c165400c90b00400c2c00e4000341c6c54901010800d4222909100014413a9000303c00182c0400c0002c00c003182171156601d40135105441650204001d0200007040c040c2e021026440d00e48041c1070045030f1300c0140c02d40d07801d642c00c00d9504c1c8011103020042d000d8004460034072801920036040407105210466100c0e0a002269090003400182100c0c00ac03500180c2c00749402c030707a01c00300c1c2c07500e01b19080410040c0d09000c40d01203070540b940c042136030750504040709200071400420051543c880966094039612005100320389030a00c2d0040150032103110b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 498684901 1250 498683651 498683663
    0x70c150212040f05121002030408070b0f04020f060a030b03032208061b0315060c0715020a03051e092218121d0301020703020c030c0303040f14040209040e0a 69
    0x48540e0700120401280c04030f0b0004040604041d0801c020403c1118001c00b0b0351455100b04c0c410704d40040d005001452085024070141034444126041c100c1081c100140502d098005800800005a8814a024815417070655101d40c554003203050a50081c01e1301d01026a143c031001c1003400f0b1110103280001482001d1307005c10346400790341d40d1001351f07070309800d42e1308000d504190514100c450154002841e84542d4100507143d4514205010890a5004130f03500409500252800d00800d4041c00122403950900c0c401880c27071810940f0300809901600c00300c02041010107c42c1603005900c102070314000a4000d10040899400f542c03014010b030011440c680a51741401804905003072005052490b95400c2088403244e035510b150100c0d84c410010315850309a6118172410100341d1000d01c0a448494801e4000300440c5412070101898101c608142c18441d5204100a0000810000c0303a5421543c0c0d001115804102c0790340040c001c0d02480030013640040c58800e000f8143c600000d20301072141d003c0d003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 498686151 1250 498684901 498684913
    0x13031401230c0c07030b0c09150906070f050c0303030705071511070602070309350a080909100305010207080301150201060302010806060a09031a18062208070c1502 72
    0x18807030410058040e1a009a101c1c001000038007114203110003411400301c0001907440980c0c8030b56403038001c4c1b00240d41e10700403814045000e01c11403c211201c50001e641032015a0700b04011000041c4580c443c80400801f10722040030325104102d410000720620b980000c041d039449190035a0010115080b1010680c2d16400a43c0030b07039a0f0080e548561f051a41030860310914041094550002039803003110103e0400c014a00300162803018030480c40342035451420350b280001f0751b070320704500441a607031035040440c3c10802150b0002214036003180c0694805440906440d42e451398109481c407034a50010b0b04039400007402108019040c0000c506950020280800400700280704900300c4d1a2400024040b0b2500030205d107803444c2031406040c4112840c5800315440d03441ea43c800f01800c40003d01451300c01c9005d804d020295000031b4110b8032031021030f00104854505441140b400c01c1c7e041111440003c0c600481c00240508a0110f0f1081508000c031001d41c00d9a94a01c0c40380218199400b80041c0166 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 498687401 1250 498686151 498686171
    0x2030d120e010e33040209090c030601090c12051003060b130e0106030614070c1103030d06080f061807030f0215070b150618130608060405010501140a050616030513031401 75
    0x15600002c040c0603200c075003031450f81d9146c0c280f1601c80000307086030600e032107074101110b030756074040221501038500310b41d000c0b6000042c640c1c05801a80030641c0c21091b00c1c1004100203484003400507000403641c02000c08034a0b10095008220b0340782061a968060318100b00d203041032400150440c0382228801e000811403400d80fa5042c112011080c0c41c1140010f05540728040800d1001210710b02810004090342c3c03412514a244804445803648000390390740bc007400300b480c40c0809006065118101118100f480c0007000e240903158605ea0000a03c04984040d61000b0740d02d404004500b81090001c00301e0707448007141031a00040800b120340e0f12000302d02c0103116101d82441e0b000c3c0c1e214407070701e400c0c489100c01c80d46041100c5d4510000900041d00e90711000096641401c01003980030f81e00900000441e0750410f03086000800000d040d00f0f00400d2541d40400003911054112030a60304c030710041461020251030210380074030601e1040001000301d13500c04018040d02c10304140c1302001500c020803842c101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 498688651 1250 498687401 498687463
    0xf04090219050702130c091502070807060509010203070b130206070602030603074505160201150509040f02040603290916030209090f06070e120a02030d120e010e 71
    0xf1003900a40103550000342a50b601c0c00b0f50001d1440b0902c604004104e6511070050f0507503a2804188600142d1082c3c004120303004040c0b0481c0b0203807500d03140c090310f401700c40c0c40042e540b4070072028020284101c030700008002400310307a001e1103013941c010850ba603200d981d818140040e400c00d492a038400d016018002580110404490300b022810303202e4a2040da400c0c445040c2c2d0300000b036103a008034504e41202c114809001340b140c540f00311400601405004a4080020f08444441c0c045464401e59208144001d98400c01140d40c8154000705040d819082c0d44085405815954002000092076000402d81140c00e42084001e404010102e00413039503030414250342d03454200c10005801c6820840601c09805c00d80d900b43c2e846100b03102210741440713150340c50510b0910708940070000100c0d105120790081c80c00d98005504030100500500c5090b030300d03400007a2141c2036603d41300c040c8019194120105c0c03107242c00c40b503060034070503000b041348040c0c4280e440d881c0c0e10f094100d07000c540d5104220001c0609 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 498689901 1250 498688651 498688657
    0x15020106050120070801090b01081606050301090b06070f050709151421030d14011d0a1805010f0b04060503030406050d110c010516092111060f0409021905 68
    0x200580d00e486481d940e9031143c06409524651581c52402000e1012a40c0a000d002d00c9081c02e108a1007082150325200c038003401c060803440060b440e000c1180f001c000440d40b1101f501e05450840400255104a50780017940b54465001e00401454541d09c402080c0500030513848201e581c03100d01480070900b0509120014500c1c2d0081c68640c1c9002c518440e141d0030404569000c40b9580d80c01c0c5202010049500d07407464000d201c40201050301c404140c8410400e6a0301180142209040340a002880200e203a50024000b032520082d503035130f10f0458050202003a140242160800000c00824000110a0000e0012810744a02590403d18000b400d414004105c03400c0382c6441d5100360800c420350200c00701400d503600f0740403800d031014448005001c00a11810b801074004140040b00361020400141c041006540304042e42c007507a80d880009003841818107080340ea44000b8202d101076003000040c0180c000c248078925820000316020408010507801415240200d95034410550841c0508586500c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 498691151 1250 498689901 498689909
    0x8221217090313090509011103010806090c09090a030f1e0503090106120c0e040c03020a080102090906060a090506030907031e05010b040219050d0603140d1d03070528030c15020106 79
    0x901101c04014005071548006d4004080b0800070504800d404800210f03500280c1000a4a421090070701000f03a8041040b04419072040d16203583c5450040b844035251000e20348043d00340700da43c03007200c9086482074818030b08201100e00b94000700f42004600910325001100e5200240d0b1800c5400b00300c0101c601d8030069201d80c03240745040428245030f00310940f02e801170400c80c7d85210f8084040016070300d80503c0d6000d003000000050311340620303104102c5a21005028140941000c200e00d8407065403214810f800c0c0d40c41500c45607501d403241c1000500e045c42036070010b04003a40780714a0070030755a264500c80500c00c0c020b000078403024403034000b08002c9100380302e1516100009100c50f0320360f96000d400035103000640e0100010b1016680d8440d04a5044824403000041e007100740702c80e15031900002c80c0250f1005030148040a40e1130200070903540c00003800340e9031141c40702c440d2100c40c1d00d0341c0c54429040f01c1000c80c0242c05213903483c5030803011496640140440020f40d080642c01e40b0f44148036510483d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 498692401 1250 498691151 498691177
    0x50918030a1101060302130209010e0a08060a021812010c0206012301030903030219020105061203040e06010503090f0106080703060501090b0108070f0507020d110906030a03082212170903 82
    0x503a6180d00751240b4405500d90a240d5484080000c090b90307600c1c56503a01d008025102590f02c208120005000f65074110b400c52043c1004441400b103001c00280560b840003031410016601d00708440c14004181043c12055031121600c0c2440511000c1174028018014058084424903600c5d000c2c04850701841c0042c0c1131551020300c4440c0560342c03003a0400403d050107400c0051404029520000400303194080c0440981c0d107650a1044500b064209405609050b43c06503041505000f03194007402405025581001404000b25a003580140034411121006030002c025041c0d6540c54540c03a0b10052009590140c54540005207849550144900c00803050b03490a10f00d99400205468014011002004215080c0080320050b1074090300482a2805400c0014500f00c900003001403034240103101c2c90080d00a01e643c84c0000b500200d0454112600b1031240c400c9221605440e46041c2d0002c201805805079101c0000c2c0c5603420506000c4140006050700c142e55864100803a0f403817044020080d01c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 498693651 1250 498692401 498692407
    0x1030b060f091005461b0201031d060115090e0403081801020d2c030708091c12030b0301060f122303040f05012303150301051005091803 60
    0x103d1800a9102e1030200381c5003045400e10b00e008901a0510f40354049200011407514100380c0d50204068601c0710a40b44024102203a1950900c0107102c0301e0300c50b42070420013019405440440e806500034001e1381c1000303c0326040c0c441110f100f507503840c4020b01c5032400c03443c42c2c15111501e1a20600400c001e4410182500c00c880d11181c3d021102c000000b454550700c2c11804009907001d41c001c0c0002d050542d66240302140e8001600c4040c543c07031041181214002520010404480401001303440e210b03504000c92584400014010960050a44d5601c0044400ba8851141007041e400c0550382d2860300b0743d4040102e2101101410300300c03076403402010760b522001402040003407040340c040300308a8442e252041d98454010900a03001c014003100760b00c150000315042c40b4106258007400018102480c210710803804409626000c0080c102032020960800000a010b05c2d6103032002d610304070f0014008110780d1500c0e1881241800d46070240c644500e905902003200341f4030201c02c2d0f940002d00c200245107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 498694901 1250 498693651 498693667
    0x504091109130c14010212030417030702010f1521020112020c010209031b0118050109050d02010c05101d120d0b1c0b04060c262707030201030b060f 65
    0x15010a00601d042460048690001c0c0011a983c80342c00080c2030074408032040d1581c040019043c54840d011141e06140140100004608801c2c03a46800c1013035a00c3c4c0658a44410350100e0240000c104054001400c1c2003501c2801e580303000c060001c07101c02c14040e0441560840b015161080c15000c0a80040e08004a081076150254000c100300c6c000d82c1c0006207803445c241c000c40c1c1022006040281c032214008205a4196007140e800180c020081401480427410301001804000c1280030b0540030340c4040345480116402400810881a044002c56a4542d04082d082c0007800388118110b100140310f084900340c9400001e142e4081050028545041c20104107a030401080020503055000c840074a5010310310000d040382c1c420250041d6044100c0d0700d003070f0402505031580101c01c1d108106804c2c3c900600b04201500001f4048411181a101c5844150012859041044460350031681c10000204186000150901240e2007038070280403180c0c90608005040c041c415140144807020842d580c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 498696151 1250 498694901 498694909
    0x2060c0a05070c030f0302010c0f0c0807140615010e0f0603010302040209060f0d0f0606080421030e01110409060509010b1902070b0304061d0f28050f150105040911 72
    0xc0410000d240850400081d82c965007407034665603109454859608003c80113069081c0940c0c0d5a6543d44e040c00115000045002010208801c6014041d91000306400e0100b092074a03501d488100200308a91980c200241000782d1013440e6a400c41c0441c5001c038000801e41020500390f800750038014603050941c1c0c69074082c403000c4c0d84008402940188104207540300c0b150210054205907402900026081c1001c268034411141c0a40200e4241b192990400000410150840e100014520040f042c9000c1280c4164064041c1300582d030115400c0140c2842c1c80301d1204080d00403510191003e00c021a43e81c814010160003e005100c0c183c281000b0400042c0c6030200b884a4000480c0304480004d0b55401550f48560000e41c0c084030841d860310811004002e0481072160300380446030192080c010001d80c543c0d83d41801c2c8000031084000002088640061280d100984c03d4002d81514288200c412142d5100c143c1103140d07140444559001098904013407117002411036001c219040510700f118208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 498697401 1250 498696151 498696157
    0x4020c07031b0906140a17100513020108100b0a0c141b09180d030e01060b0d02040e1303020714040b040908030601022401120c0905010e0a0c0c020102060c 68
    0x24103445400c0d40040022201d00c80da1200b108400d091080507401d240b0300105070354265004000d081d440b45a003891613a24600f0000480701e45101d1100d6074203031202c03101c0c02c00c5000c1480307580017860031040201103070540250035000e0b8402d9032030300318554482506101d00c010a000d84001c40c00e0600c580c0900d64050501e0001e01030240c6c1c804c00b1a0889084158540b8003082036a0041030b9128985000306d0600c104d5664104070000303520b02c1504420304010b995080600740903c101500c070040d05c040e2103020742c84000a030140349110350342d8512900321200654000e208071000800508000342c10164140408030f41260b0541c00303043c1d070b02e01e0700d00701d401204019100a54400d40e0f60240100c0c0b81e80b240b003102d070800c2c440d41d03503da01e03880c00070001f80c2000385149240c4503500f880b000b807218800c038800c0802e054404034845052122003074140340c07294428540007003c074980703808000b090078a164035000340304802444050002e408544022101c2c10b5088100901581c4864081101c2003280409 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 498698651 1250 498697401 498697417
    0x90308161e0c1a16030e0d14010b0a0605070f08030a06030206040e160912080a030f0203040c210222020c0303040f020a14180a1e050103060b01090b0f09010215180f060709050402 78
    0x111902c1c00015899050014810708c40c000090303992414400720900b4801d101c0c100508117810100d0403c441921285520f400d640001444120000000303a250f440540c0083d002d95005880300d6143e41d29148106414981560440d0b02d818001244c0c4c41649e00c42c00b01c00f001e032150344a040ca0740c610703d43d840410b20380055a00390185602e034a54443c01007480e1010358460380c02502c09446c1c082c40d01e80005900e85800c1d110001d08079603a0041c00150300c03800480c4818096010b0300802080d24145101d0090084c3c040d000d9141c0000000e00c01071100100070500c02500031a048030b030680d55a1499080c0c00595440742c1d401c59006107542049080458040368096001500804c4403904210751400c15080e50040700c00880e134800060050210600c591401d0035001c1c01c01c18078841c203001031545c1c54094543c6c002002c1100049070700150b4400e01810108440b64500220f41d41006003c0381548084840d20500e00c6c452403400c0c62800300000b41c007902400050716008074907410f200c1800040d6014942c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 498699901 1250 498698651 498698659
    0x50d0b03160b132d060201060b0412060b0a06090f0504050106080411010c0b090a06061527210b0a110307140405060f1207090308161e0c1a16030e 64
    0x3c40012081c501da05030502d280009580d411100380b00b42c0d080b82ca00e060310380004085a02d000c00512041d4441001c0344c06a5441000d41e03a0007103110720381704014046070386004c5c0d00030301c55000009a0315000410b003001c0d110502c4400200540310000d000445000744a81400500c0b8200450040707030148949400c0804180f40070f031464440c548404c01680320640300d1058907884035120030140109842800c0180c030f1085130354100644816001003aa1245c1c41c00c0d950762203540e00152403100c0c2d54902000040c030781030120300303142d5180c3d0742c81c200c17046603a08050340c1301d2001c940003505c000c0380340c407030707110000c00c680742c11030075519003003400c48180320310090040316004200400b107000c1d030b12030000e004044a4600d0b01c590f240042d14074000c400e5406840081071007800e0200f0710010720103209441c594804003d074103000d6440d6040400585003040e0340588040c5002c0002424046003402e42001e0358503010307031008104407821004c1101c2c4903290864407003a180380341d0a40000c0c42502140101e0744020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 498701151 1250 498699901 498699937
    0x15050d150606110f070e0703110427050a090b0a0209012d0e010f0c11060d0c08040c0b0f030a0b0d020a150f052104060e070303050d0b03160b 62
    0x102000302100c11640140010402c054518266a0020404c0402c0000d80030081c010b45441c00840c0d213012040070f0640010315840b202c110b801c05102c401070f20000c1ca0383c0784141c5c5080340e100c000318610b1209001c08907080380c00e0100050f0684103034010003580e640d0210310030107256a041800c000a4200f8900c2504000c86c0c1104204103000030070318001c4180b80d4000d8140340300c031810710140242c2c3d1480401da06010300d0740141d41005030031440c034a0b41c407604005400d85030841c0d00001840c500c80c00c059010045e00e066162543d02c1e030300914561007207110f40b070401146625030000210502400d400d00490340c4041001419000d0960000f81c03c0c0c0c03401400b92007014501d0ba000a9810203d070f00700d080780300b072504020343e504d0b07502140c458403c0c0c0c403504103989002035440c907030000e03085000c4159490100030004201000100d0b84000e50f071801141c19035011584034a4002c1450f0300c0011b19041e024103000007428103240105096401400205101c4245441c0001880c66a08045554031015607070b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 498702401 1250 498701151 498701183
    0x1030c050d1a042a031a0d03020f010c08090c06090307051c030f0503060d0b1b1308160f03020112150b040303110c0f060d0204080f010c110115050d 65
    0x1a000d5460001c0d50310702c108a1503000c010910080300d84041c1c5000064114200c00030b200c1c1080280000c56240a1501040202072401c8440340c5060a0700c001d0381005480104c0c40526901194a0003082c503610001c1c0f201c094803400407900c8880c25200d1004540101c0d080d2442840e1800040821010280545034981d50b1507000444903a100004110018000e150385020075a00c42c040c0014603002e070520b10300f1410b10b50041080f01c012250000e04a88854000c24104200a5140c0c14481c03100c44105a075145120303170159161059200d031103024801c1e0075101c00d020310005100340603248141180c40042c2c0c9190011a06420300c0c520300540c0c0e0381c0d109181100d49140300c0086010b48a007026180c1d8562461a0080514968004101c0d0070f82102c01400b200341c4d1218601c0320038240803a202070301c40310741c1d0980c50001e101d203901c074210364480d020615810360410341200281d00318944444480c00b1861036201d00b41c0341d1704096448101c1e5154814000c43c540012041611401813110001c6241a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 498703651 1250 498702401 498702427
    0x13050c03120a1119020f0d0b0907090c0918020a0c1b030b0f04051002030601030b03030309011d0f031905041d19020c030909130f0c030213021801030c05 67
    0x381e00d0412030714000004095102c540c1090740101844144002082084192084016429541c1c0c800038460076034001d4400150351740c9140503c01907042401d081072420710b2415a5500c0d840e510403104900d050042100c141030150080f113040f20106502f0111200c010100c2600070750092a07840e0902c10224a400301150491500110061180c0034454038a415400d1014981400030003600340743c41c0030410400080c3c4007040700d030b92840180002507143c1d280c0303e005070043c120700501680c06102c00b0080107010201500000c07111544180c0401e640708080b0640c035114040c14010003030135842004010801407a5200100101c80140340c16402c00782c8846607000405550a030742ea54031613240050002c5021540450710501c04403c000310b192000c0f074a0100d440e0b00405085c01d200c1d002000002c0c00c00c10441c18100c0c4081e42c003c01d07100303a040b1103140c01c1c05c400850380000e9006c1c1002540d00e8440c86d10724801c884c510364840c0a072030b4400800030011805050b186c2900340030400f040c8000f0b002449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 498704901 1250 498703651 498703663
    0x703020703080703020304080118050a022b060902091510080c0d0903080708071b17071e0302060703091e0615080c030c19030201230414091302030613050c03 69
    0x101c0303175000d90396407850036640a00351154400c3c55420804903800d4500003440014071034541e594141c80c160f2050800440403800250301050340482681c580c18600c3c20007101e94801c04445208441140042e00c2d500360703407401e0602051300c454020780c00400c03240320140030b501d285510000c03250741c451a080d08080c41c101138510031501240400c1000e4248101c99401c01130305980104540351042e000754010303d000282c0300350303a000030745a01b0180e0004011802440200d45269400c030420313001d0421082c0e10005144070600b0103a0041c01020041251a88203000c0e09001541205882d0f0001401c2c102100703810243c035a0440360740e42d8502c0403040d041e80311043c48004110742e10141103909041c00915060007042d084491080102021020745a000030700303a8002d07240c0a10b0200c10403d00010401d110909800e07004113480f20101d00050203411007261100384800a075422190f03a1107650441c408a43e80c000e000b581a0000c000040b01480c02001d00b40100c5d0103601115508042c0c0404681024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 498706151 1250 498704901 498704903
    0xb1008010908031503120a05091516050d05090901090506030c1306080c0103020c0d080c04030b010b130519050f0402130308040f1d0a0b060f0a090e0105030a0b0c07030207030807 78
    0x85404010040c6441c00c2603803c0584013000e5000c2e00f4804c10b2040760540c1d912502c10400180040481c0c40800d03521049140c0880552401d480c0303558034060103040c00c80d1480100e086401d8814118044281e030310034026680400320190401c8503a0742007076640405010001d00300303a014070502c080c100199480c00c0802e060200c4c800c40003d5124248441300f414044c401d1071031418180100003032121580001540c040800882c5041d041d603845010040650740303d19400504103030141c40010412a0200004005940c071400381580c61550b40e0080c01841c10610805000e00580141c0401190030040101842c1e880000c0c00140b6000c881c4820ba801008181c0060b80c1105020400313004400c0b47c202044041c000c5a0020b01088003002c12201d02d810b0000d207900078503900c8505044440c0c507804290b40c0110000d155240e01ea0320390a000030300028441c8140343e0041c0c6254000545030401061021200c2d400401540341c80d03a0f00441020103512024040302188509040003000c06c0c1d0701c0000c0e180311 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 498707401 1250 498706151 498706163
    0x70204051006030f02181017070e0a09060308071101090b0f1b07150f0504150e21030901110f010908070606080106050d02131b0f08220b10080109 64
    0x2031800c0c41001002c40307622800100341e1a1040214010b03281c0c0002c0303c43c6c0d4584040707401c400742c90b4550380d04850508035490407039040c50000707040c00030003600980503e40d104025281c400c18941e642a5070402d6400520014202074401c000c1400420704403185c5048224040c1003404d045030755a4506142c03540100e6000740e41d0307900803420865608001d0003190741440288001c0a14908058030400e030310300103038014400e1281e82480802c1c10b0b0300407801c0d80e005010707245400c21212132001c0c002e0648010308609038819130394003070040700f010a03002502d441030b00340c074004600703004031100192941c604003500fa0300d403441801d003130848002017401820f400a1168103a02c0d110700b400d180420075550560090000e80e41880414031103030701e510400c6481a074044070b0408040c000c521500340144440401994940c000d50f5030001042d4101c2c42141c41c070f2002c1d6442c07541d5a0b07912500c03541c0014250070400340c01c0e8444c40c14500890341044416810685800c04c076240d0381d5440d84480e0840f000c5000850354 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 498708651 1250 498707401 498707431
    0x30b0114150406050405011d06040501051e0a0809150411010e01020a1509021f080a0203040807021503070f031506030e0f01090308040c060206090d18051203040f06141e07020405 78
    0xa1960b212807613282d0588608e5040904002100000f0703040e0065000c1e1030304022021440a03076290500c6546c160006007031045030349c0e6162102005068090403504409c1c02e10690809000c80b0807859200c501c91600141d9502005482c0f0004607031200110f8989411841140b1a00010903405010440c448078a034500081601d40d910600c0380074084901035020081a42d0b050030701c0742d030704004007a0f4400d1122600581e00c0d0396034600800a4022030b40023039004205070400000300000a001117011302c1807507ca841c0e00c0c20010720114265001d0040000340031511103820081766010b504009880c204030020b075241c1d980b080d0031036400c407004280141d0005a40d4030a102c1840200e9854002070700082c0b0107000380e464201d0000d640c0b07040800300101040b074000705c00340b1901740e550404006000010081c090318826034044560301d800c580501074240b603d003080052581d00401854184101805071282031891003540a00d5000280c2504c40640d00100080001a1317128481d681c400c005c942c2c52890 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 498709901 1250 498708651 498708659
    0x516090503030a05220312080403080a06080a08071406090d090506040503060f04080c2a010813080a0219061a0102010c091a040e04080d0e07030b01141504060504 71
    0x1221542590026010350401c018141c0340d03a9109080302c60304110101c070f2404016492594142c0c0000d50307400681883d000103070044049038080e1055008074003075501e0001e00d4644504510440303c0034891200c8a40c040142e8070300041c2c0c0d01024280f180d000701c0d9204c500340b91490340d041c100700080361103160320741001c10854969a04008003074050142610454101400d0101107aa10400500008070381e90505001400b04450801240c4076030750904117841d82010040280c41101403401a41d04c048078030100c481c0b1441d40720728038051103420170038881d141c0c10b001c90b214030503180c0c071903565001103002d00d24260301d845407141d42e030075141c506c503000c0000d00903c24401801d2400c5001c03013407030444e410200406103540d031080710101504c5450501000341c540d20030b19103407103115a80c01303120500180010801406001c201820980410b86030600c0041240d001c4540c80300194003004010540d040010320003aa44490358030350b4017a001d045180700004d08030101d07070389401c0350340420002280018184 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 498711151 1250 498709901 498709907
    0x601080f0607031104121103031305010314040f02120c04050103140d02010c230d060b070c0905040203120a03090c080f010c030b06070803041b30050d0e030a05010516 73
    0x2d030701c1280ca1808226800f010a0340542500c41c034400e00940700d42c0c642450052200a55001034140c03002800c03290742d503110004000f1b01d0f00d6103108180c0400e20340402126814a0340d500a407003990700c138805c0c01038540d141d8200400304541c0c0180c0c42c840c0c03040c450324060781c0c2c03a2031084a0185d40901c0d00d03041d80404a9000e01d2078096025800b60441e4189107240513035681003001d103496411003a840308412035805044501901039030000030700850901200051142e0140020030802d402611840c900d9a2038030218400c1d1182600e009401d6844481401d503240d6061010303100311101c500e030100307540000c1c0c1c80b4030702c010342c098102180b1a0890001e180f55020244280c2c540c00b0420f090902c0541010000103101d80902503000e4003086c000400507040010380364105d44010004a10b00400541f5035880d0349540c0703055804101001c0003111181c3c40c0c500403e204041181d802001064138074081042201e540310200192505840303128038000c0051020b00800748580c000030180102204c50080007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 498712401 1250 498711151 498711163
    0xb030a0605091501140f0c15010807121e02040219030c090f030b010b030916120b060603150f1c0302012a0f0e01140c01140604110403230601080f 64
    0x1424a200c51840610340c5980017091040071941c44a0b40707507114075400440194510540751800c000d400742180032540044075a07c154180c0d42001c040b0707600543c035502e589542c007007030310805004414079200c3c07081c200c1889005100c2c560f1004c1d0025050922090a407580304112100c0074002c45c3d1900c0003103003499801407030719000b007003050940c0500500e16250b400e101c40c4113002c3c004101c800003000030601c1c00104000340540004600303155505580c0c00e01c03980b00c2c20008404940440c1580d020440e00d150400903207002d4600c0303610f50140543d070710f81049040c4800401c0700ba04061104003280340440c0c06802000400e01903000131032440800b00c51340081d15101441000d504c41e8200000110903881402241c0c0401241040b0781400340c0365005076000c118100c0045003400f4001488019150103400c2410b00c3c03000205800101d0300c5050410094a80352250b00d200540e06000400120711458001246900943c4201104010900c402414a40c0c01d0304040c4880d8807a044500c0485810800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 498713651 1250 498712401 498712411
    0x20913050c09060c010207050607050d060605040e060d0203070801150e0603011b080702011e020a0336080906070f05070e0906042003100b0a05010c050703030c0c0b030a060509 77
    0x1084189004a4032051500030a01003c0c000d20740402c1181c3c0303a0200358111441503800604541c2d80c1d2810712001403440e07121000c0385000034140703400040d10900503000d40e02501c2d1444803001c4250f4808041c0310809080d407400b0b07030345031060440000d60120b00380301e044c00d03500051944411071420010161007450002d4981030190385003580c12040d240701c0080d60824510b0f5490204600d0b101c0541c100e000d8071a60403140d00014298a4003a00f00700c03290300038021401d240d00c00b440000741607101061034404552100300c074400030040e069034000a00c1107145015200d013001c030b4181a05400801c02c0798010b03100440e8254800c001c00383c01d2281c00c204c0351000341030f01e803020101803610788000d03510b1300c1002d880103011044850050000140d800382c400c5000310041e0455a80e0040c00340c07940c1c0607000c000300c20ba0003004c0c0d880300410107500c1786c404000c0542d0842c0081903001e145550441c0c04224058054500d0310310b035500840c140a03103a0007103004e2140030502054550420302000306400010700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 498714901 1250 498713651 498713689
    0x60e0108090c0442060807090e0c040905090f0f030f04030809010c050307061b050403030206010b0306040b0a06111203160804060b0402040e16210c02070302130209 72
    0xc000c03040d01c00042401801c10140d501085202801c400031900707809040d0100c02c040e040e8001800b4011101c038400c094040c207021000f244a40d203010a90300030109480547c00905040f4050010341e800c45003043d00003410051300e0f1300e815a40e00280040340d2041c0e40e140000d420008424030355141c10802c021400300345c60080c2d4504007122441c0f90b258032a82c40018400c541c0460064110381c05400030100c1c03960000d09481d5910800e282210007003041a0b800010308040b0101440300c0c61044040d1410b4a900d5002000c1607400c080240100d60801817803070740d010303031644004a55511409940c074028004d41d05d40301c410204060302d803801c2c00100f0104002e9100705000304283c945100c403040b000e0324014100886c60381c480307083c000c0250800810141c4c20900003e400514402102c15007031003060b50040c01122503889110445001e958802c04408007081d1020601e040d01c0e46da03200c80010322039801214035081d52a07000c64000080704800386c401550103e1a01140e0411682d0b51001d0200c0381 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 498716151 1250 498714901 498714917
    0x170d320306130b010203270d03121109010c0209041403370e0d0501060b04080703020f060a080f090307020301060e0105040506120d0320030c03271203060303071b060e01 74
    0x1c0000b903807801410b250441d01f8026080c1c0b0300303030b1281d2031008034000d58001e002e8001c0d004040c01c020301080c0e2651540708803640782c0b48907804c049507400e00fa5606120140d481039403400349038081090703c15010b807055a40e0681c4456a00f06200200f008110814803044220310610417903001e00307085200030380400f406d03080880c02da02c00b40368003034006010650126000301d803e840c0382c10702c00c1c014205078024140b240e50006021810b01c2c0005020b034201c1e442110040f0290000000f408807134010007020038007040c4210007007804a000e014003194404d010000300c1e82052880d400003401c0d81c00350f5206169003c08400184002d0500c0d000380d80e03101c0400c3c2e44060700c03070000c003440c1940d481d007000c10141059a1003070140600045c29070b48508440301002c205499082036042c1c034105a000780c07100d035080080c0c5030881154024103d181c1c483c801d1907102402010210700c4040d00c00c3d500061050fa85170000b0806040041d849068104e903164902d64010442c42c14804c001d850750b0341000c011418445a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 498717401 1250 498716151 498716171
    0x5090a0212010b090a0c180f051e0a0b0a020f16090c050307020a0605070203070f060c170903030402060901140c3412140a0303050709170d32030613 65
    0x20005400c605d031900001415500d5034000c5400d51251003085400c150740440000c2d030103010b07009400a542003183c009a0034241c3e074800c00020f000d00c40580d500000d000e10304200c60000c04000e01170b5a98140103480701c0160489481e0306164044510210140c4140c02c00e200c8030040b0300c98401c03c140e140c209140b45003007551000e59181c50903800203003035940302c40000c0e2030300d4401d01c01c1e520b000b80d0107036100b1100c000760310300709015000106545002590022429402030041c04c0d10500401a02005c0c0d495500c9503000d2010550207000c0ca581884940140c20201c0084200102a03240f410701c094041c0c4c220070800e420101134003605803002d50310340100c0138130700c054440415001c5410400741070607034092a00d4a0110741c034181c507400507180124003150b418140c141e002a4421030440e0340f203084c0c071921035018001484114940d1602680840440b98071203004a000807400f5000c106020b00c580c000e00c0308551414000018030030320f0f680200610500b0704003008404d806481c0e420b13081c0201168 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 498718651 1250 498717401 498717409
    0xd110a08221109090f1002040e060a0b040303050a030207080d05040b1f0608060d060204150f020a0305030103030e040905120a030e01050f0c030414012a080103080f0d020d05090a0212010b 82
    0x1410308190320070099000424104e1400f0081d03d84064000b1050380c90380300c00c51880034021f401510915209007440e100040703070707442e003070150500391150a0b801c6401c6c03d0642d01c0440b00c41c0c0040050340c040c9542000b0102c081616400a44070015130b100000c2100e107090b240141a0050103440104a1a000030b20704607003556400d150020359055141c004040c0c1d440c10300050009401500c00342c4a240b0010700410840c140140031918000c00740c540d03a486007144d440890b03036001d01c908040c000170014030040c00000d10a502ca003140800040001c0740e414859100d035400d01c0c0d44000e02c103640e070000042d08281c1581500501004044000082000e85400b004824a148000341000d15111000000504100784501302c901e400c01b851000700140c0b04540724618044080510040200d4221200380604500c03c0e07084906a80d1300c010703151b0403c2031640c0c0d5140369820405c894484142c007407041c3c442c104114861a4458010f02c4000d050410080c01880000c9241d2014040c059041c50110401915 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 498719901 1250 498718651 498718673
    0x1091a150f13030206030703050103022e050d020c01060b04080114010302030a020411130e01060e0402031005040e0a08070602120f090304060507032007080105090f0c060d110a0822 79
    0x70320300710381c1d0341c48040b1580420320782c01d50f400080d030043c804414048626815400310b41624400e039011301480308000c0c070300343d01904035100d4041c141c00c0c811805102e243c403d0005e81a0a211040094200125040b2107420340d0119004890350000110741040400700c24083d03403103800e14200b100c6040e541990042501d54011a4020b805591924800440424070008440000f4404500d52030311548a12580b04074110a114a4002400da60021401494030b03100700e9005420090b2003281c414900000d200c0541182911158a8003038103a084000c2280c9500902420b840780b280180d40303c11401c4428848500079040c4020f200c248000c01401c03003c00003c5500b0745020b401c01d55243c011614003110b17044060940228403280d0503c0c680214200011303000c0903140071200903c4659610310b04540d442d09800e40c00c0105500c040a4807155040c550001c00042c0f15204002c11208040d0000002036800700d20300000080f0303502c0410810031690800c0140f40078922001481c0e00c0c0703003503c3d0100044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 498721151 1250 498719901 498719917
    0xc090609050a0e09030931020a23040b04030803060a0b04030c06050f130602030d0f02090a12020a090c050403120c0b060f0d0605010b07020306060415060c0507050901091a15 76
    0x2599a07004505013003001c100f03803001810001d2890701e0010000b10f269010007400402c804d1842e0b5003401e407031900c040074003e81e510b00319607070380f07104001450f0383c098003c4007903000307034907a4881c420040411803660b80c200900180d4050040c1c5981c83c1048001d1140442071680b102242040c14402400001e56228598080340d03000d20b0182c1d103c4174080490754991080d41c08030b0500b1f0b00701410010744250080b01509070422a8141080300050926a22099120311850341d50f202c140c400c001d110b42110000900f000c580040c150800454968044d8011a80c80607032640100d40c01107000c00c00c000c4800310101000400d840d20070035030071140c0c3c1c2d02400780802419142c80703000504081c03441503c0320241518141e8226100380450350f540c12840c00c1c0343d8481c6c40264068040d14002a129041602550042c03032500303c08a0105850013408a6000005030f000b15124011184005040e41d04ca00c08039011749141c2d180023034061892210389545800c01c480d40c500446401b4031503003103500c1c0030b015141c0760 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 498722401 1250 498721151 498721169
    0x209150f060408030a1409130e010518030415050f040609030507080a031407020d12030609150e01090e0a06050412080f0609010513060e040f110306090a0807020f0d060c090609050a 79
    0x784014206c000a030040391a180d4005000404d290011a0035400007805012504002c1150707840340c83c0424000e01640c0030459a540c4108010408134450384618040f8410600d02181805030304250954240c0c060b500c21000a000c4450900c14010103110440041150034010728501681c0c2c0d40240040c50743c071034122610b090104000301035454110310441d049900c400d481a2b5140c20b0100940100000c1c080d80c590b03940340c440d4841101e008000b402d820f4602003003014010fa1f1801d2420f03000340c00003031419201806a0f901c2003000802c1802242d000e284a41c11074912420000c200911a030b400412003461200c0280030f0182a448100720241540c50a81d000890b0400120200024184030b9100e01e01d50f0700004204001c0c409041030414282d81305286824991081d0810075030ba8800a850842c00c0d0303041500c61a0000d8080c20003000084d10141a10344087c0490002408813110018192081625280300625107540310035118068452402e10704021070501c40460b4510360540958055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 498723651 1250 498722401 498722417
    0xa0b130e04110d06060e06030c01020307231605040c08040f0f03021c030f06050105040e01120f0812070305010504060b0a080a020405040204080a03140301031a04030c0209150f060408030a 82
    0xa1111549202c000100040c0251040101d0761030450014030051140711518500c0b103020039500e14010440300c01c5d80c00142d000b5410280e1030b0701c51415250250680500d1001e009003a10054001404403810350407103803d99290729890315060005445240c2550801c104070381d01040001004000c20055098020041a03407100d034902d81a4648240e64074800880307440c04035000541640364110000d04400c10388148030640c1d807a401940c0501860190401e84510b8400505c24140d80045020032540506041c050801c15a03c81149030751044071040a101446010003141c00d415002d102e0041c002982c080040701d2078910010b800d80602500c000403c00b030f6402090341c103a15901a034010703005c020401c65a40c2d9540319210b40e206040da0045020660b180d501040d0380780ca500943c0e0403250041401c030401c03207010061041c0c40c100100100c052110828518001d0780702e40c00d0880c850040400e14940c482290000c201c0000c52008961744a408100401e010140e000b0064030185100c0d8100090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 498724901 1250 498723651 498723653
    0x10513150c140c120319050c0c06041203030b090601050d0b19080606090c0307020304050609040e01050f090723211f111305010e030c090a06050a0b130e04 68
    0x400c110382040c050909400c502c129140b0303041c0070544014800044441c81e0f902c2140c0050b940e00c0c0e014081e401400c4c440c0780001c045900b40036030010070991115070141d604010348800003d03044e4000b5000840044040f11042c2d04160300f501c03a00c452248101c451042c07038076183c1d0000f442c62050b01c0e00c2138403031500c41018000b951180b926600c9501d040b119181036007512184c50700e64610080355500d200e025100081104804100f086030b001d810f042e8051490281042e080c4815a03000b8508503410541e41c41c68200c05403028844d20f4010003c0e9941005241003c00c00b941c58000140c20095042214120352001d980c01c44c3c50300000000156800118000715882c61907884000e41d40400340c50041160fa03802030b002e01950502d001c240c0c2d403001c0001c043c1540c001e010600840d0185490360442c0c0c00180515802050f0f04040c90038001c04880303441607400c010503008072060b80d800c48820b444110a001c545004075014014014102c400e509000034005030707807010505d512580700e898401201180c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 498726151 1250 498724901 498724907
    0x2212030c05160818130c2d1b06140403020d02010e0a140a0519291b040b1b07090504081602040f0912090b191107150804030206010501051315 62
    0x4c4212000141032402d481000c1e041d0b0707030140c51140000c000240c003901000980d41e000c52168980c00c1c1250503032010b02240706e101030322007003070090704005001400f100c8007000803500e0040c0c0000c40e20580038021a802c0a1802038074081c42508405e06690602904018103540080c2303a00285810401100d100d28101ca68070741031108000700903045024849041c0c0d904004105d800120710300c212891404034000d81ca00c001198000d031074454001d01000c001c54081100d02120040b01d040c0d000c6241e2806603034042c4007200d03900c04001444d040180407500012100107008030710041a5030780c4207201c4d501d09075803500401d10805000c0c1c800000100810010364603182c0c041c4029090101c0708004c030b411181042e042080c038a02101c00012303150080130548081ca00d05075203202d81303044155407559100c1314061b5800e03282508448890b02c511180004c119644803c081c0c40524240c44003d11410035003002802d0002c142c121a040c44420040700c80107401c0c41081d00700308c4521403401540410840822 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 498727401 1250 498726151 498726187
    0x4150305040812090d09080601050a2c010f0501030501090506030303070c0f08030f010302030c010c1509020f090a0c09230105072a180b0f04052212030c051608 70
    0x2a1642203290810050341210014600401c00c2a03a120f040c46d4607a0386150564a070400d00030035030072100384082003100b0441030342ca50000035040003905581000d22040d20701c404109a2180b181c20741000170411465825100301800350400c0d18060125152950200ba580e1202429201c10081426500300520411500b451401503001c02c0b0907541e82444044210580c6080c08107a03c030f03000311101c0b080a98010000d20300415440400000c4144450468000410b13039158161f03086001d1609404c1541c1d1036940b4079100700803684000802e030a5100c0b004045003a103410a20159400c1c502040c041840d04505146241c4240303891542d48010b03160081358003049044000c082c401440101008107240c40c214000d813413031006080400d0301002c9001013958150b27008103412841d01805807206007003540026070720600780403900359443e928006030802d00c00000410303280340b120704644c188480c0d032500481142c0034007490001d040c654485040c00240540c25002442c0072800070307807143c11348505140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 498728651 1250 498727401 498727417
    0x4140d0317010e0a0c0e0108061c080c250e130303110313050c06040303050d0903050c060a0203040c0f030b190f020d060e1008070303081905040302010c0212041503050408 75
    0x6408550f5034007420100c10310252451500c40381440000403060303100720003003803c05005a40d6240b049d1a5441481001d503407020118000071003984266002ca008a0000c080b80142c6400501c001c00c09040c2401180920a00340312407041c404c501085010288001603030051103006204444241616082d0000d0080191801c0341c0390000c400c0060440c2e405204810441c01107041d15441c0c13620808208203845070b030100a000c55001d0002525a034642d60041e030800c0d00c2404d04600d4040c038038003c07901e071400c01c80d02da000440c0c00104000c02c2110255090000b400d0355000706c0d4000f800c5968000b9150402094500c3e00514000740c0c09100740c0e00d07046440c0d1f405440404554610b50078000d07078003410b91070103049501940c0038045003007130549090500c225503078030001d44031050039503070304a4040c0c0000c4c020786074541c0310710310000c000002c901c41c2c14080c0c2c0c800c0d000010150b00700c02002c1d040000403000354001e04414001000380c4d85000700d1900d1060480e02e800505555207107020080d40c022112 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 498729901 1250 498728651 498728687
    0x20c0715020c0102010e01060b040b090d05060c030a0b0906150721020f060c0702010509090907091b0e0f010f0c02030f030307030e060c04030c151205040503030a1104140d03 76
    0x11034500c00c59008900d081e980202a07000b0b00c8419107042d5840d081c0d8815200750005024100810800380f44020007a01c62030030010290140d07100107460b05480c00c501518a4040c8081c004180480c0c108030b485142e540c02d40a40700035110b0300d00300c4001203480180d41940b804450b00001c0480401400c1000c41d603440c094aa08240c201701d0446000f940c40143c0c80d4062042c0c4100710102c1c418049030420b450710258142d440b40e192661440074403103000d201400d549a075102d09003004c90300c1e9015006206088000c0308a0400000c003000d00100340610010800c1d02413841601c546529036408413030703202150000d041c411101c1e0080e10100345010f4041c801d55405000c007000380001e00c1d9064104110a181c1c820480701541c83c0d03a104040c1c0e902c00d502c001080c078011030604100c20110121490b090103901d040c500c680b6240d02c4450740c06d07514100c40842d9650400010041142074501c51049201d00040005003454280701c6800c1c0f1110b500c4070018800c0841ca0002c6042510a000ea1000c1c148455 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 498731151 1250 498729901 498729929
    0x123090d05031801020a0b160909020f0a08060108060d110a0b031f0503160e0c090303070c21321504030e01111504050309040c02072c010306020c07 65
    0x800c0c040d880703400503660f0b4003034034071003c0c0c50088940c0f00003141140c0640080c1c190020780c81360081e1007260260f5088440c20f0082459000401c5103491002c1d001482c140d81071150303290031341c02c401085c1000c0107000e05e05000009043c00616200c424142641d17540c0070310140004240359000545500c0e45600c0925010f6000003004440805000303044065a030302c3c1d10001c2500d441324105516040da940d80d02079200810841000302c0c01c482d09030182c00030402801380b454259180042400d60780240003d844000d00d00c04104507141000252403060310101ca50002e22502d6503480c92802031b119250198220b1400a450907101100100700101a624004940c005403050080114844040360b081d00403c034480034028095001d1101200454020809098007042a0700d9442071a1005041600c0758801031241c010203071a42d02c210a40103801e80c0007826041c2c42e005128100c0c000c4203420040b00011500009030030741141c0596419a548a9000f60b02d41241c00c10007841c141c2d040d800b4400d0b008281c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 498732401 1250 498731151 498731153
    0x204060f0b09030d0503061804030c0821010f050604092c0604030f08160807020c040e031209030a050304020904150501030602041401082202220510060305060123090d 73
    0x100c4001c0c0a69001602134401c4184986010f44860000b103818580150201840d56205a45950b45550007440b030b0800c01c0140c552902c84007156008039601c0b02c0410403024100c5061188021030070300500c4080b010116040c10304001c14028040c40c400c850844d03031a208040c3d100201d110400d17200c0b001c0c401380c41c42c00110b04440c4030354900042d5015030102e140402c0c100b0b11035100d085480d100340c10303542e00038602d40c515100032240044000c009070114050451207080580d01c40c02000b810b120301000a5896600e01040081d502c6c50142031015540e2040005413030658012007074035032154040300c145105644e182810744ac850b00c0154803010752403410303002008228055001c0c1040c2e800c880424547c0d181000019260a4415540043c03541044000040700b4082448110305c51031024240d091a0140760034080c1d1070082982405105680b20410480c40003c203240080c014003182c86e00b8401c5082c8200080d0140e04080d808240021525681d0111116800c0c00c56510307820251a41e90003c4003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 498733651 1250 498732401 498732419
    0x507051203100515041a03070201090f03020706090e010f1725060f08280902130902030d0f080a1503120804020108150f04020c150106051c02030f04020d0204060f 71
    0xc5002e141e10903c1c03003504d070950f0b0161410640b41030703d80b004510b9004507041081300d02c480d00028080c1045641b03541c402070000b0020200313104018800d400828445003804406804c0b2030058002c0b85540d00c140380104101d150101800085440c0e0340207100b01544420019820302001c1958000064541464009070234650140503089070110303910b8400d0504903110440341000c0035102c414403070b42d00010181000781000d4124800312040b000c00a41d070b40700740d808240e1101400020540c0990366104400a40c03c003813090807100b204601d0204021404104064a80400a80400c202690b5234407030a2030140c103110407102560300010b8542d9030803080030005042c0c4900f00c804078001468000450602c002c100468104800300411700000f401c05041804002d4000000900300d501c201d10f0f17150041c0700501070650203040150307581c0396100307204100464941e12204401640a01c1082080062550301a0035a0440d44c12a0b401c4540106030000802400035504141803a1801010000322014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 498734901 1250 498733651 498733681
    0x30a080c21030a050a11390102040302090601031104211401020c010b0a05030d030f09020a0608011505032401020a0b010f1d01031a0c25020f10020d0507051203 70
    0x40c5040c042550382c04017480980f1110b0141d4036900d0824000320700f084400c0121244800301510800300061000180fa0b5501140c81c60b1000301317a54002018070075402e02c0704000b540440c0a003400d1104800c00d190410040c0f1403072103082035a1000307682d03155000441c4440104007640242c403034a0084900c0a0183c002e40c02071a10030ac89600e080031500442c20a20021000c0302d00c020701030141c24141440542c00ba0901c0690320245560b116402d40050340c07081c4000700640f8003540c611603198100b110b001e40d500f900c00b9034001407103030603c03c20480c40c203040041c00d10050090b030b003e04080c141c3c10045c0d1511401c060001c1400032800b001084074084480800200c991a0035540403440200380e20700c0e5407035400e004c007a00140e0800110881070010102054000403048600703840e0006034000d50001c00c6035090041204409100044194a04010300000013001240c103140d100b800c000000c0c1d900c8150340c0f81a0709000c0080707124001d105040c003a0b901345c4401d012226940c1d1601e0021440184 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 498736151 1250 498734901 498734911
    0x130f02070c1e0501020d0f0908010903030b010f080103020901060c020415300b0c07080403080c0102040609080303100911070b161806020c01050d2d050114030a080c2103 74
    0x1d20441889034107682001050b900315841070300a08500b6081300703021914020854007803002e0000e440000606141e0910981d10318501031b40d000100d1450b0310000400410550300b1000c200310529006002580e1180c1005045442c170b8141894030075103038400300b40034204a8034500c1c401194020005504140162110300c0c01c820382200c07003006445e41018005552114102801500e400e0b0b00285507010a07400900105015004d80360401e030341ea503900202ea034400940f111150b500801c08212854006090401425000300079509500d450300f08102c4100c014415040c1c201c1d11150040c0490001e6030864104903000030f00400304c0e282600d100a05000c5035020080015032003096591050424105c4500307030340540c1e0290039240804401114240c021489200358036a0b10710103801041003400b800003a40c0b07070820301d0b0110400000c012404aa00585c07140304c800e05190001c500650300403c0b6418803540c80b41c00c480c0c48585408455252140040c03104030109115042c91900f0040c5d080514410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 498737401 1250 498736151 498736169
    0x1504060c060f15030308090a030816051c0e07050607030e10030e16030b0a0c081303090905090f0f07050d031d060406050304060c0f080a0203071e0903020306100311130f02070c 77
    0x280ca40a00a42c0d4505008238040d001450751004144880900c55039100c9240b0b1070310384103003402c0d41d0201040e03800340c1000c000b40510355248901d06e0811410310400004080440f110781c100140c0741c40152401000291980c4900c4000d0304c0d04201c54042c0e402200b501080008803040075144403406880791a450005507249a41000020644400c501071324181c0900d6541d09ca1a5489449a02c8214501c50307070201c05004080c90301142940f00351244510030003080000f420782d81d94a04009003007429820300d81c5039a0308a11824069a1582a40d003246140c4c90f01c0d10f46021002c3c0c02003035586401540c28954070171000680010005d5210010711300490062004001403031004209503039410204000e20081000100020881030440e40950391040301d50038000880a02c0c2d046071207803210002598004209890030500c2542401c0000300e600ca0030012010a82504548459200301c42000c0c15a208a01460724400500400d410004c001d0310611800d41d22510140740a40688005000b03a084c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 498738651 1250 498737401 498737417
    0x210021804050f010f03030c060e03030f16030507021c021002032a0c060601050f070c031514060d11060403080301030b04021323060315241504060c060f150303 70
    0x7010f0680d801ca4100c0f00401c510003c3c4a213590307003e40d46640b942074141e8100360350381110120f950b014801544101b000b9021003600d0b01e0100c0c2008441c0014048410070989008200a9140d0700021080320141a0802c8040041d40d280703406c03450a0043c0040386a00d40c00403080c02440140400c2c3c040340346580522115480400401e8034260b80543c407901c1c002540080c0214200d940511300601085400148183ca494460b0301c035a42c2c0215164400c0b241102524000e410030b240c188541c2d03591482e801c040710080d060100009089114401010703290b4100c6079080b2841d41d0300c1d0303070880d801160700142c410344942e5241401c0541710000c0710168002c95000d075210049200510079030b0034006428140c038500c2c510511107402682e20003856250907124031500018816420b82406100d4500f6802d0b8607d401600b0401c0a80184000c0700107000304411044000c0c80d105401c01c2e00d0580c0c1040c5044200074240c1c3c00e2510180100400240b541d034a002801c01852074070040300030a0707900039119400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 498739901 1250 498738651 498738661
    0x1009050102091017040206070f141507030606090b1614030a03150503060708090c030a050c0f0312042903070c0302070b0906120c0409050c0a0906080412050a021002180405 75
    0x34941349800c0040611488000010700628040010b02280350080d0143c00c0b001200b96603039103a10318000c441c0c00302940a12003000c1d6960b4601102d50307100456207400d11071246005406080401c81d8010f03c01c000201140c0e0101039070301c42034008181604501600041280a03401c41d459503c00403031400060704100701c20540304410008001114009402004a566a80000c440c004405001040785000303131094080c40341d4040000ea03103814014009400804050410001e1145800740780038080c1d0000c1c11025103156041d01603d040382c0e038066100b004080c1050f0382c8444c0714500d80203e019810b0100038020920350000005203418400d03000c036020b8548400082044d8080c0c042d1843d40100104254160172001600c80750b0412896010301e82020748681400742030b41e000310381d07259001002251200f00d0303076808a41702c0c2c01000181401603d5007401c1c5c4680d4040c03e11083c45c0c034188040000c586058604c00c001c01403490500000071910741000c09107500c001d29059015902c280d04050100b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 498741007 1106 498739901 498739907
    0x702252c0a0c09080712030c0503070f030e011106150d060f14040209011205030a1d12031c1a04090c0b030c04050a0b09031005060310090501020910 65
    0x118104200a400074840945503100c084c1c20341c030002040002c40e402e107030031003000307a01840d0134943c200391802c08130302e5417082110042483c10a9030048082c560300141d403901e10f100c01da13200c0b400c80c000c60403c2e0340d40340b805039034040c050407290040284a00e130802950408a100d404041108080403101600311890035200480000d007540c100000c45c41c048200e02d001d4000700860000001041c1c48103a40da024085404090201190005a02400400c03550741e80b0507004008410701a5211003c0b9240d4100301646031441d452905403060580341c50098111a580140c0081c0d0110f01c10400c20000d020511401c2d20f4221300c00401080541c01c0300015440baa01015600b0343d5a4076042c00c1c0580000d655101c0000114140701c456520394001c541c61001581c09800030440703485107400681400498010740d03100070b03e401500d5080240c107402900c031500d0f0403500e20b11520300402c815 = true := by decide +kernel

theorem cover : BRFrame.Cov 498561151 498741007 := by
  have h0 := BRFrame.cov_init 498561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 498561151 ≤ n) (h2 : n < 498741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
