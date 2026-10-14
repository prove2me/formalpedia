-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1605
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:49:18.053514+00:00
-- url     : https://prove2.me/submissions/9a4d49d4-cbae-4536-8292-a9fb8fae2c67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 288489208 ≤ n < 288669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 288490458 1250 288489208 288489233
    0x20619020106090b03060f07020f0a0605061305040b06041a1c1703060a0614070b0f04060c020c0607080d0f060b120105010c1a0612070803070c08030c071514030103 72
    0x2a8009129064440425400b81c61034089100e4040d4480000644504081244290415043e0042d04e07604c5610344021410f00b49044000d803429500c40c0300340506170030407543c140070075409414104028101a0365004100c1c0c4013400780c80c815500c40c01e10b4214140605030700640340340010000401d40c00801300b40d2918000601040d5104400d01156142d815070034400c5a100b428003c040f040150b0034040c054030001c5000d041420001d005101c030400050715800018000c9540d0f00b4240714528003454603005541942296508640014000210341d455403001c0d240e0035580400301903241c40548103030500600802d0603100c00c007414580001203542c403510003000c02034407010300c10071607070f881f100191981c418101c4010714113480e068602070480d6203101c002ea00020010a107054101856004c54944411038006916940001401d141000280c0c20048001c010160243d810aa07241c00403544541c400e108404840008141d0030f03903007510402d1205269003070403400c2c41e22035840f401c00c1c0865950 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 288491708 1250 288490458 288490507
    0xc0908010b0a050a030f06060e0403080108010e0f0d120f0f0b0a08060702100203190e030d0b01090308030c1c1a0108010b030411040f0e010e01150509040f031b0206 72
    0x28158211840741024441035042c0c400c0540280001850340e6038005044024100a4840d2623481501140d04200440380e2400b89020380d8415129504203003001d400c403206091210400d0b4071900581c1c0c8020404103001c602402c4504200800a1440a4000c054900b80055090082c9811000701c501c0d1420ba208040d800b809603501c0d0741c00ca4540d0491995020259080ea0260340406d4031a00507031110707002550702100200903504440d5030400003000740c0e8145142c4d502aa080411001101c500074841c1d500502d60928109003240e1558403012440d1201601c00b009902000840075680c1c48410564140700010000030000c1c0c61184549107800820501510f000031022000018102004810750380902c0d0008480700942c070240d41000020406040851165030f290480c7d120302003028400d54106002090001c59081907801d42d40303606607801d400091042c0300e55024440030030260341c100700c3c0181e807508020798005110010416002d00c55800294001d00004182100312410200a01d400a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 288492958 1250 288491708 288491711
    0x1e011d0c03041a250329060306040504050106080a030203070c060504060f20070e06040c080106021b0f060c0f0c04020406020c0f060f0f0a0801081507080403120c090801 74
    0xc44180d940200380c481520041c00c54040403034440b418031003d075400c54000d0803c903040350703200c01215150f040701c5211601180200343d80b20000d80303078071440002010080600305440c900090f00c039400154103000141444c0d00035651a000942000800d41c0720b10054142039003124050015454000d44c8c070340c012607080f200c1c43c580c0306000420070301032410707901516086c1d11307103100c00700310700000312a001c29182180c8d900c16901480503840120070702c481c4000d000c0720402307440b00381b0702501884182c4d840c8603000c0e0200b0a10000401a841d03012035140d520740c403114004d02c00c041072900002c6c07000c501c031540c0301d07440340c000a0445507000c00000d046148a1150b02034411890b41c1308104012130184e03125600250304031019180301c1e454001001c0704040e90040c0303405c3c00d0030900091800e0315080b81c13422041d90000000c001c1c44080e0443c000500400c2c00f1801021b400c0428520b5a210110150544003800302500101d0101802007007603a000c80450340c3e00b009070300e040038001442c4050b5407281460710f5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 288494208 1250 288492958 288492961
    0x31b12030c071401020a02010f052a01020c010e0601050303091909050a0b0909062502010216030c03020f1614030109240b09091203060303071b03030e0111070b031e011d 74
    0x213500210308003683c250141c55503c40c0005144040d20281e0058003d00c00020544074080c00d07500001100c0c581d550140400140c884894061090845910380c40d589100ea12802c010400c0d5580001200d103980ea00f51011076004601c0300d0b9140c1d00410940054506034140010805c41c030007280c0c0700c0342426400315828480c0b6203550190a88861058400d04507014411400002c04c030111800041e0141c01c0d07200040c40c003481048000011030500d901100080c01c480003041c01c4c0750b4104840405100c9160141c407500300c644a07440a41c501c144a52104505034880c0700406590070750106500da034104240340b030403015980000040032003c1c810706800f41d103808409041820100280c03440341c500c580051005220900e84801c1c550030040055078144403c00100001400100324440c15819030801d80d075015007946005480040d80b9101c2c2410071082800701c7c1005000050514101da09040c1c68503604e4076840e80700c2d8400202c10850390340100400300001030100d07204040304d041e4018401d05e41c009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 288495458 1250 288494208 288494249
    0x1e0c020c0a050409030801060e130e0a170f070215040504050a0605091006051606090507090c0306300c0b180f0402191107090e0c130605031b12030c07 66
    0x2c40304d0820b000717070014406030300500c4181e002e941c85001c0c00200402c54281c0d003006290810603038141d40721440301904030300c2803003081086488071143c54800c000130141c01c20341068900c030824004d50601a114056410101580c1145041120090200584144814a484941100500300c5d601c5110300a000c18070001d1207040704c15141e007017034510940d01c10385002d0245032080e01201c00c02c00146c40b4103540301c81e260006841000f0800040c01c151340d0208501c42ca00c580070302221202d5201042581c003086115103400c60508680072420404403c0c030401c0c40e403c2c200b0504030381e500d42180c0c69403040020758940c2c10080c078800031040e140480d450b12000482c0b10500081c0e0048541410b07405190440118038103000705400c08600060000300d450300da0f0340310a810159100c00d891111a13402100261406080c005110002d90040e0001448850b1038100460343d6610460100d012141e25103a0034070b000d5072040a00349114070041e08894880f01d103405000d0310380ba56841020210b0444a401ea80e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 288496708 1250 288495458 288495461
    0x31b02060d1a030c0f01020703031d060304030807080106091d040302011b1808010c0e091902071202160e0c0f0403061419051b030c0d1a0f0406030c05041e0c020c0a0504 74
    0x2d05e03d8040c1c0c050400145942d80956211881d192841050031101d01103070039507290031001c0c5100e103001340e81c2c400031410244400382c841d00040e00030701c01b00200c2c04d030103001c1c0900c0103520421104580c1034203500c03542d80341400c90040c005454581088648102580101d41d4000b51041e0011b20400b0351003400c941d561800e9007242c0803041500d010030000100340c240c506e460036000d503109282d02d4600700c00c0301040921000300da10829045440b80a4400030016055042017440021255070350074207a41414800504100c00c40100010700090000885002007a4204159001180d0041d410710407000b00d0b08040e422141c00f19040038640055050907600328405001d506c0c0a500c1030101d88140002030800d0000f554001131461400f8441004806054013a0748242c030b03200d00c615080307070131103003c18020030040c40a0603440d64441c509040c01400420100020782044605c2210f0001d80031000c110540300210b810034801807500e150510301c0e1907587c0c010603031030041c82086a460340e02c2a1140304000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 288497958 1250 288496708 288496729
    0x51e010b0d020d050f03030a0204090606020a050c04230108060f060a03120c081c0912050903151e010303030e0105180d0806041b021b0d031b02060d1a030c 68
    0xd51000e141c000d910050700307001e641e10007224002c506844058070284425451a0320680d46040000c0d070020b03040190130420722580000c0c01503403001d0424460540c807880c0d900c0c176040c825a48916a40c9140500300010340c1802c210150480031048119a580d000700c2d07031070b0780003141c070060042c006800060f032600e070041c0a54140c039030010307490000d0100c00300c0450708400d100e0402c440141c0b08108224204c0200628086009521403000c6140d208514000c99a0301103a402c074018010203100d000080e80d0042483d8500a03501c046003512692004171118071210354007011044101000004424168150010181404144000d024548403030030000f03400c0411070101001c81d0084a400c076002c1e071051105c0394201030020700228142400c08070000000d18401d40240241e4090518059402e11205c0b290044860441e00010428003030740300601117042101e14244d000000d2071000c01156510002d40b110720075840350404c8040e0740e2200d1890a084507847d014420f105200102c60103180454200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 288499208 1250 288497958 288497981
    0x20102100e1218030f0d0e040e031603021c1e030e0a05030406031e0504020f240d0b120a05071215020d05040309090204050a0b0a020a050a051e01 64
    0x24003501061100980042000d00d40d0011103000700040c8001541d6200301400c00b244040401d0742103410104101450076404007056003890300041a14000c4c981c200d004000300c614140d4000c5007040c850b28100d41184184003540035603404820354030080c5940014100462450b2070401c0008020300a01030300c4074210103840709040c00d040300201c803210303100350000416403450b00121030740c401e40e940d5102c0c2540c015800840000740d44103420658071813440c0301501c07512800d00e0200041d04007600452005d180c44c110640c0500144004c10101d003000341d008141d0708580c2c0a0244d11110350750a0500608840940c00f0312441c1410942d02e02c80c1d90210b80c000740c1560001c0280249440d011300c3d200201110301082e00c0c1e51780d0080507882804400e00041c03c00d034004a1001885203400d02c0e01a1400e68260040b00c0c0350380c03040c4801c1c0078a888102c0034038280c2d1001c0300095292483e0003012443d0981001006065000f11ba84a000700300001686114803803c02e4186c08580810002d02401c8403e0729000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 288500458 1250 288499208 288499213
    0x706090c170615041503032a02060f0c240105010f0e0a06200616080c070b0a150504021303020111010c20390603040807061e061719020102 61
    0x71943d4980300140c01003284070094000302e82503c001800002c441c0e25540305074041200320041c18141c000d00fa400c2c9411000d04002c417040548150080750b101d024041d1403891800001850ba428074404100991216104403881c0381024014121000700c1d90007842030b04e010400145d03241e8201da0180d0000030101070080c01210074540350090440c0e185d10b55044640355244009000850514107000c20782c8100310510400b0350400c04100010602e070002083c408242e00c09000c0003000545803070209400070f11504021903164924011101c200c82c59503c802e074040c7c40014031a2102c4920001201240d000340c035050304038492195160300b665a201024800183e0300c8260400c03074420a101000c0b52a90001125011490044c902c00c6149007110814103403903802150020410860300281d180400030740c1d1032400e5040a5982c000c003809491030040c24203441c0c40d400c10039000540d81c104507440c054a0b040c01191340ea031103012800940084900454043e80100e03443d645041021100e01d164186e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 288501708 1250 288500458 288500461
    0x1506060d09080d09080c0705030a050a030f0905130f0c080c07031d030328031e0b01030e03030703020a08010506120606030c04030210120e210703020109080706090c1706 74
    0x3040002419005411140c0724414040305041d40003600c9000003942c41866a55560100c20080703c1c035010165103c14400d0340845600300000d40041030102c012685410554542001004117681c0003900e03070045c0e50800b10303900d03100741043c60940004201d00041801001019038500041f1406030040b501410034a004101d4240003034801d001c1a0020b0610001c0f800d1030700b2036400000d0460b40440001c103070b403031241c80303c0072644003c51010076010486802c0c1000785080c4594116500000030961102c604d030765151312100740c0d012b0380100800c141c140e010f41c0c0e030f83e2400400142c001c0d0000342d8941c000503940400411142080000c032640f5603900e00c500c101d9540c807a0304100c640c0d840180250041e0701c00303010000051322540a4001d05c0152a00c0e510740f41b02d18251940e0884640491a41056008180701c1d000200305a501c04d00718128407404580c1c600702400c1c00e9000d031484640080c0507c0c8001030500521246920034041244103002d001125943ca075800304086840d40d1102e00175411220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 288502958 1250 288501708 288501727
    0x3111005090f06160f020306010837051204060207090e0a08090d050102070303201612051c0f1107080a180b03090c09010501030e070306050705041802040602150606 72
    0x15440318440500038a01d80c9042d6800320f18010b03540e0b030150300321011702080f030303800c0d00318030303040c8811405401d0900003014100781c488070001c4415021100402c9240701c02c1002d034001d90308140c0c40c0c606203400408442d5135682003c5080203035802403003904018000caa41c003081c00d200c035000d000040501030b0001d0116107082d4480c080d03540d0108400079801701c0000360440004500303001a02d03403640031780c400180d0b6501d150200c6040d4030340c291049003144000c2180440d94010050100c06450700140005601c0c3c125050581e654881c102c12840201140d140e462010000c42e001a040c00303181c5141401070b6102e001c3d107a81d56000ea41001002c10800344003191605210301e01150480315400a0701c00b070b4036520000080b90360710503601081e1030703003040d45041054201090401c1c010b040030b280802c503100090340101d0301d40c0110700004101d02d80740c401042c0080e103d40d0a9602602c4c1176112160460ba48181c4040298064840c0300058022800001c5400300800e613024030030b4002824861403c0d400702c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 288504208 1250 288502958 288502969
    0x3081602060118060f060305060109052e1215080705010804050d0305100e010603092a050d05011407020607080901050f0703020702240c061003080a0f09050d0c0311100509 75
    0x4140c18903284d94200016108075032102100051400d40c40005540c18200001801c101150b00010700580d020455500c800340690f10071820039503d24603910304d500c950101116900500f0124903e00346c1000800b0090014082c00300040f540b05400f1038000954031f03801583e01480455001d89950051036224140d40d011380c210070b5000c260814401c03019510b600101d400068280c0209000941e81d890701410030241180c080e034003000f411400301e45525035190419910040b8018903000b18402040c00c8100b22003500560b8480380d142ea29011203107842c043c000e584200444522000a0b060300c00702d03c0216043c85030500035141c1200c400c0c0142e48007881980070b0340c485a01241c008035203411803c9500642c116460594154000f9142d80341c2100701d1035881c01d07001070849040102503034001c0000409070411601d4810761810060345c1b00500c52020340d0018541c1c0e200d10b03085051001d0303490170081c603005900c042d64424410844083c0c102018041c40e9460220b605001c101d0801c40305559140c107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 288505458 1250 288504208 288504239
    0x705090d0f0f0b19060803040b0f0c1507080c19050702010c0c0801021b030306030604060b0a150c0c090b0f130b03100605010206010b1204020f040e030c0a030816020601 74
    0xda40071807800760603982d8050314110406003e5a01c10300b9003041c80507000100661001c0c0703400c0303860213212450401031104d449214031b00c00d207005d0071000160703104504036620a0302e803081c00c00d43c103a404001c040a012642800100d070a44c0024070070500064807850fa034400d540034428884200b00d09040da01c103040d500b40d80504021ba042c0110000800006116900c00d2005004128000b689800c150744110188055440f003480b5203400034820002191000100d0f20303485608200d02242030744081010421b203410940020210050780710b034a07071103542c01820035001148a035941d49a044c0da10000310084400d0710200c136601903d00362212070319103401c0c0041c00101c43e0826002401c0c003403400c000b0345842c0d1006442c2c01c040f81c03248800c014940e0140f040300d005010110807070b071401d01400b800c200c1000c00200024031512a80c03806000c60b8071140d111100b5040da050840303a0300c00b4800c05560f69180f00700b408500254050700041d00300101c01b4001510b2003215001451280d082c00310365042c8600c1d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 288506708 1250 288505458 288505463
    0x5010c1409150702040e071410021207020d0b0403050a140415030f020c011505090a0e0d050d151805070302090d0303090f020907090e0106090302010c120e0402030c18090705090d 78
    0xd21664016176694030442680711041e1006003001483d044610541c01041010548550801e50340354003a40c0d000304800f40c40c00181c80c070145d95003003144002103540ca0842005494500140108003c242c0c1040091429044a450b0901e800b42600c4244405200314002d41c01d0b100c00c002c901c0100300d07000780c003d20006036000c0c80250402c91414080c908503a80400240808480e000c01000f20f401c0404200ba08080c0c440414415900034640b159982c003114620041004400600d20800e51a598002c0c1050010885440e036400c0e5502844001201d0100c0d01c075055900d804c0100f03112501038401c6604a400c040d0500c6440d080c1518103500401c0c81113016500400d100300400c0c01039071007802c028400c082e0350300c905841a0801d6901e10700420140c111700d00b8030100781802e00150fa048030311516000c4c0e10981002580d18000c0088a1201000b6070864000d4004410f1102c0703013a00300094000c58880b1008014508094020082c003d603064840d500030640400107200907040082c0e41c40301060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 288507958 1250 288506708 288506749
    0x1c0216080a030908030a0c0e040606090303080c0403150b011209030e010e120304030318080d020a02040504030e040f020a1701050a14030a15090303050915070302090f0307090905010c1409 82
    0x1203c0c0c2c0740e541c165841240c1001c1c000b0341d5018108640c90b00954811200d48060710100415803c2800140a01c1410f000203000e10800c000080d0b41d060b0410b0844010316400780d03a03041c000ca40c0d006c04501508221002902140290004031038601d5944508824240c143e550100c807003401d5001075900d25107010849401608040180080b640d0810090000314440d59a00c816007031402800c1c0045c030310580100620341c200314504400750382d001805c140e24a07012280003821341c41c3c6103429204600c543e50a207810504180441d0424030095001d081d2840e0603442c1c0310110102e80e030032a00091070034010164090300300d030003e00900f40d8540c0964101503010301240c40f18501c1b6205c0f805640d802c139003030003009a114404031041507818041d4030f40000324a0010240050071007204500d556008008504040e4089600301c500d99608100c0900c012001e001d440d4502e03203411082024046981c0b040d151582401080300403144500f008103851b000c120050740c203111110082000c5030180504500310f60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 288509208 1250 288507958 288507971
    0x23060a1205090a06050c04030b010b030a09050f0d020f0f1f0e07030b060a0608010506030a092904060b0603091902040204032102061f0e09031e1c0216080a03 69
    0x50181d1044500500340b400c000d00070308415280c030070190784000708200314410090004000041505800d2170641c1d481d80309444d00c90b959810800003c151507400940f49100b040724005000402240d015070303c0d04642e0a031071000b994218a503699083c01e060300316507a888030702c66407410750542c4000302c1c51011806012030b56441c9a0703551071500255800c1039030460400d400b40051850000a00c2c001003909082100c4250f140c1000204540001050384910741e89030030f00b600400c6011445c6152100d4040700903801c03101300303074a44005a4000c40381104c01a1514804194501d031600641e41f081c18444000d05201c58803544000300703442c55445c03c0b44c026400384000b02c0050581c4460070100c150a00d440d0300040748945e40203107414070243c201008040d01500094503031684085841c142c40c4001110340c0d054036140d140514610078601021482d03810028200f503100b00c504020038148000c4ca0800250701c5d1800700c200103d00c40c0b0f0045100c8100242500340029003054054500d01d061814000b400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 288510458 1250 288509208 288509237
    0xe060706060801021b0c030a030509120f07091a0f0a0506071109040f05060709030b0a11120a0603050610080a060c050702041a030d0503010311280801140123060a 71
    0xe980107004c036030031700c4800c841540480003010840785694030001c800038002c945054070f000d4194800c012400740180100100405641000c10070404141c841c4801c0382d2815a644400e0303001401601d081d00300502200c0c0c458076141c81c0c04089044990001051201c180b4942010069140e00040c4120b6684903100c2e00c01071a42c1c0d0321003003076100fa4090341e500e1400303140c185030a41c203100d001406481400034141080c4080b8a03a60700300380d071000f450800042c6040000c1605005400f0300501c44403003544c44e5040000d010503d80080b0102ca203e041198542c2e19004a14136004185000742083e070b5100503603010128440703030054030003024039080a0b450b204090300800e0030707110380740e82c002c04010300100a29040c0c10100b0503880c68041c98034115007154190303510311642500380301445118141034125000300d40c421510218403250004500500300742c1d01c44000d03000c0e000c000082e0034114400e000014a4444030880c45101c0c0fa9118201039407030000f0f50811000c1d401581424082140d244418502c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 288511708 1250 288510458 288510461
    0x7080f03040303030f020c0601090e070504020304060608060108030c0a0b15030a0c030b0106020c01020c06180d0c0e070c0320070f09021818010306110d020301030f03021204060e060706060801 84
    0x4004500203160344a041d400c0103001e071143e4100040703801c1e10401101c064100080b40540c15108002c0700882d0441500c00c0c4030345000c07042d4000301c0c0d019100005000c00c02040e83e000b80201d5541c84d007600c1407a03a075004c203181caa00540302d0354003958003c030a042d00002c09803290242d005000d102540e815464040103e071806101c2101140c0824031040184203001140240c107006180e1440200155003028000030b480d81158855980201c10221700d040703040121032280207204401800c25040d6140900708990401014400d100c5040000004940340c3e0b8815904604641e4250711404007038000c40803c01c05520a40380080d02034040c82001103207030754044c2e404000402100d41c02684442d041480400001c000341e5006100d042540180000002400c103400e044030303040a80083e404144a000c0c1d20544166555100380d00d10000c004020403901c08a60300419009508039a403110034040e0401240c81107000d400003140800f00310455600d0008001c240c01031107100c1c0031507a03a6407100700c0390 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 288512958 1250 288511708 288511723
    0xd0204030b010602031b06010f050618220609060f030b06010c140a030905060a090b03220b0114010c02310f0605100206070f0e011806082d07080403020708 68
    0x3c00507040000c8504103040da20300841c040c0c1d940c01010700000d5140860842442e9031a109042c0101c2e0040b6100d05030107480c054550024801a000396465004102581d90408000c2d0010040034034000020800d0203041c80b075103058484d1040c811a0b170700e00b0750711001c56a8400401c030904002c010820b01340000c2e0026400d08036039a03000b000300900446440c0c0903060600d02d81095014090520841c5070140e80311a803041240d400740c46140e500d8071007980402603080c95007410720310b141d0002ca10310200304072004440c0c100d803446480c2c090a04d10071001110f0158103003070081d500040324005000d402d012045068030910150740c5c9140b01c1d0412921083c207445130582d000a0239650744004203c5418141100c100c03528443c40501071518103008050102d40320f0300112400c00681101444099005015800096403c010561056039803890010180c803402c43c2c00420154908541c8549820060920f0500c071401c0300404100b65140b420848111030018002c7d01140b00351a400a14400700780b0214 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 288514208 1250 288512958 288512969
    0x11403160303030218091605071704030803041101050c0705120c0a09021209150f0408040504050f070f020f03180105041d04210215090708070e0103290106050d0204030b01 75
    0x3503200c02000c9000076040202000c001d0081007010200070341d030080840d24458031800b90802315114049410501030714095150401402a0002000b00c10b02c020000034500c034610a6401c405200024001140d4901551019007900d80c0401001d00043c584010710702803901108040302c20240c02c03540000c1d200078142c0c0c01407500c00d82c002812a4128203c4205a038400d0081d00241142c200040079400000740c01041c00b81190130a0000c68104041c12080f1801400000c20a01590402e16070084000301c00791007010100394a030f01080b00c07943c0081540000b0500c21800346007000108200403110000d0140c1305410031100b0003001c200304403040781e8208012145a2642214a028070b4414621140c0c00101c00341403512045c515200c1d68002407540d1162110102c131f41050701d0340740d5458903000b6540c00260b01c83c0100b24002c03c8820003450098101c0703001e000650250300c0c80f1641d0446541311040d059005104000041c0071540c001d80c02031a01004c00300300140b505549441e0304130028801c0e04034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 288515458 1250 288514208 288514211
    0x9110a0f050c0118050105010819060507030f09110a080f151008010204031203060f0e13061d0d121a0d0c0b0a0305011404050105060a110f01050112120509030601140316030303 77
    0x40ca01800305c24800e0501403e10304004040c00c401d03c004843c912004d0764001010a521000050400c601c40e800a000040381a00180016005032601050f00308088810030701910303401d44002404440018009402091000a000c0e10040381d4400c1d20100402890001d800905040000f10000c0c24802880158000c0c030360b0845c00342c0000c00c02016a0720a074802e1550f60143c0405000d0810420502a0031034280c04103140c0c1c21105152900141c400e91410590494003d03018420607080030815980d5500543c1d10306000d105205144411100c00034190038070151090349100c0e03030b81000c2002c161410b010701c00d285155952200603032b48c1039101c18140400691140b004220b0100f441c030310402041c4080760240499812310000c642c15000c2c3d00c000070100104e50f8091250040140318509240c0039980017440b0940c0c442c50543e038401c2c411401260007104480c0c10240e101d101e00d00395400c2902c01001341610b41d06e40303090044070f61207181c45140c0c0341c0a0644600b0321821071846110007140f00e41c60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 288516708 1250 288515458 288515501
    0xe1617010b1314100509010219060213120803070e01091a09040c020102090117100f030c080c060c07050d03032408070b0a021005040512030118050109110a0f050c01 72
    0x1c1e00c000c0481d0307660140c00c44030342d0300340d0800040d55401c0c030b5040d0401031442c0c03d07a00c4080a40040f03103071034040c2c40520021403451274002d01b44482da0700141071403401c260b56100e00c5561901c603840b014070b18010103031801d501400852031032031250028400025051521220007510b80f0080514280da1000c4505000c41c0010742d59038a0a15005884041c5510b00003141882030040c00602405031207041c024203c8095000540050b424113210400707008140b400d40c4016480380307090480000240502d101500c640d5026000318a0100c04403500540f40d100600655482d00c3c081c8502d0b41c001800480c285521000d0015181d91076120480e010b0701c82080c0880d0755490800560f0a10700c05411200040c1020408004910b800003454804100c1042000881c2d80d203900303080d0f040540307620100e0b4041d9400400022500802c0420000f510380c0b000040100c0d13603030340040904584086004d4a4170180034408410310601820b00242814282d040203894820205950b41c2142c2007640b030121483c6a000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 288517958 1250 288516708 288516727
    0x708040509090c030c0609132c03042918030a080d05071101052431050a05010311040b0406091b031a030c1504030f03051207090e1617010b 61
    0x281040ca84401d5132114500f040120100c1c2c0300448c00c04c65600456111404400b07001c107042c840711a002e0240c000d120300a041c000070291641c2c0188520904940e00d0528030551307c0500c4907086181e14403d030800e10349000703062284030382c1c0d64040445905008141030030300801c4092000781510042503a0001e164545004054852041815820980c1e8940020003003490b222002000c03d4040d1386440c6100910300000040f9141c02d034200c1c0c100d01c10100904056100428010b45407a200300c1d15081c07000741e41c1c10342e0a1049a00910002d0b203020f41d880403655043c20640d014101058015001060441e190290700003a00c00800206036801c030710b0b003070f07a11196078184119840c00c011066024091403942000955a580c514800c078840e5a10750503c002048124049900031035000b5a044183e403158140580315411019889400e840001c00007940c15229024440568040740082d05450315051002d882d60302c080c039020f40c1401141d11104052118003040c06000b0300d0344081c0c103070307690801d0f4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 288519208 1250 288517958 288517963
    0x20d0203010e01180b01050a0c02060c03040b0a020607050a09050f011709030307030b04090b0f10031401020a09060305060915181302010f0f08062209030c0201080c16080708040509090c03 82
    0xf069004d49891800e42d0b01059607034000c0454184112520b46845421501c2c000078904d440703403c2e0006c01602c000036000404040c0079000d00b05c20b030442d800340d40f070030ba85420090b0740a100d04461280010b81c680820300c120318210090021103c03041c074140c0700d206c43d0700e0b00544160b0825503007030340c15500c08070400080079030500a0805000040d43d003440000210f5454400031400a4100d05c12a2441d400044149022003085401036800c500e120301500d8007449214000d43c00b0310b00042c002407108070b003c1034083c028001d140c05201d010f46a41840d035101d2211066082c134240500342c0c86101103640000030307002d10020310b01580f40508080102c85162002500b603400c0c215028080c8607901b000341d6851038000c0d40340c507404501580d1140d40c0c200c159441c03460304541001503a8916290402c02d10034140e0119050780c0e404d1003a21246021f40f1012405009030207464060f2404110720205400060303101005061018401c006807802c1030307103039000a600004100c030521196800008100302c03a1608 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 288520458 1250 288519208 288519239
    0xa0905030c0c03160b04050f0301090804060c15020711091504060e10090504020307060c020f1f030c0203090607110a03060c05031b18010c03020f072309091c03020d0203010e01 77
    0x21090380305072040c949201002c00380074031f20809203e08041001b103c0c141e1402e4004c40501640444a240d645031134910240001c402d200c42a04d0103011088400581c2110344210399406030400e40710046e4410800822107007940050a150700645c49580d08040c980b12809408007070801086484160f160501464500c0315842d84490306a40c1401b0501c8003503100401d84600303031485498944120001400440c00316850b030341859410845076001100c00c1d034080840b014040d003a0f03540501130f401e01044101c1e030382d000700b90720280d1160081000c100052909088a400c16101901e1550039554a4407140102c0c5d21101400c000329000000300302c102d0070b14811020020890b03a00480c10700c042c607807041e0340040704114030303c2c180070b12400032800303040c002c020843c100c45031007040761700481e00c0c1e030b09801070046007201c0c81c4e8000c29141c20344091841c10b20b968a1240c0c00d42c0008181b905501c940d1441c240b80c940d028101815400c0042c881d48084500081d806003802d81505c82c025450b0951400014a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 288521708 1250 288520458 288520483
    0x10e0a0f05090604091a1b031602010e060f070c02030109050114180105040c0e0a1515030b0901031e03200706080609040c09020d1e0f1b0906080a0905030c0c03 70
    0x341400c00d90002c5c1b0b503035070032800d03001103006140459501c0e400300f00640881d2001c0b003a02d1030804803c0003107003030102400d50249620390b402881102035103003503959501d0301601d400c880304481c1c40028034010b01c182c84001050f80000d0010a4805090b119182103e01040c00303030b4842d64030342c1c0410076a102401c0e5509004071141b03000700401e1074545c8030040303144145d000c1c403070403018100c01150180d45035412014021140700303a0f0102d415a1048142e022f090f8442030303100400d0801d000001c991500c01d8415040303030b420a40d8440346042c00310095046903000c04040b01480108849181081559441d682d01c03071103041700400003d0306004002d80702400082c5841e2117000100104070010304d0380f447c10b0003118020000961255680f800c0000a403050440031010b2201e1a1419005c026058211003003010000b0302c00c10540409900781c80c40760803281c0500020465000d01080f01174070a200c2650322009103100007070390300d01e582d9540e4110750203151404980e910480b0104c409187c03d2103110030322003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 288522958 1250 288521708 288521711
    0x18010e01020a030e010503061210150803041809020111150103170a050d1e02070609020906030c1012090209010902120f0106020d031808070f120c0b060906010e0a0f05090604 76
    0xb40d036035401091105401041810820080041984c94a070b01d50103001212441050741c0000f0f00c0ea940e04001000d190086084903402d408000501c0e00f0040121415140c00520100d41640341501c00d1000e8045080c08030b0400102403510480381205101e40d0b040031803010403003040d075407460030100300000e82030006181d04801080600d0151313800c1400c0b00d20310a40c020010560b100c01d070206284040d100103010710101d0000880b54104455079100c000010310032981402503403104001d0650b540e0405600c0398001924058180006014071091100c590b0f000c00045809206503000c2145410203034441071113690041080381d100e40c03440309180d600c09603105101d8025807400100941d01c01e0400a010145580d0b000d00d0a52214000d4000c00b4554004454542d504024544801c41105418064410308803440c41d904c0401d207e06902803445810103840e003070940301d60041050480380504064144894090708081c0c0303403203201307522000340303210403124245520301824010010030040c071081c4541d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 288524208 1250 288522958 288522973
    0x20c011b1104091205090112060305070506030c040801091a1602030406110705033301050a05060a110a030807020d0813060b011808010207020a0603140f090109020618010e0102 77
    0x11500c16081881460300094001820a224408900203044024001d0700c0b0440680706660516008402000d0095003070f6901441d80d45405001c400311150b41c00010801c1d0010442001030f85401c00145030056814aa03003443d141d5240d4419003106c0f201d00c1c0803219490f0861032080d0307580c602c032000c5a201545a180d91541c0c68905c0c8001d440c3d1050740640e40500045404141c550f404c1000740c2d0b005040050300b00d4200f950341c2d810816210501c51140d0760329401c022000320103103c040607403034101c40e8040e100301111402c0008015542d041601c00108002c4070b00da003800803400c100100b0703491074000e444600705420b0485009080c4562101d41909114440091000c540744d80ea50000040d908484002540244900100c0c1c4c28074102003140e001c18210040421031001c194001e0102d03034400c40d1945801962002c080d0140c5000403801035074643c90070005901030141190040d8008a14800041c4504203540068200c2e001154030390301e1120903103100032841d40c0260030041da4034003d00003040d04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 288525458 1250 288524208 288524237
    0x20406080d0905060a05040806010f090e0d050702040c030f0c03060302040b060702300a060e012a0c0302030f1201140301020316031e0504060b0907030b0f04090219060203040303020c01 81
    0xe00c02d60f8032503540642800914080c075a0f2198003507130040c5ca8040161030701540c0d22022089080170340d000b0401807500d4414150705109000894140403d0f040e26414149010f98003000014001d4206042c28035031070b4411128000700d9071040b0101d0380c68a460000c1d102d070070740c0140400c45a84180050107004104042000b60b03075200111040312010f000303004406440c50b408041c02c1000b00400c60040e1250104080800c50b0341e0300003240c6842040002c012000140004420982150300f1000f41c001b55202c844e86405d10412081001c45c1c041e0040380d180540a10f5103981960103480030b100094060780050061803403000d40ca1865080880007903013075040c0407500b6860f9105440450702031550321440300f0510060b04039460585003051008100901d01403d050010b40b00e05070b940c1e1b118905403000668958000d120718111074001801c2c1554450440c0140001008031030170682c1d001711030820303801011252011260140409502843c0c0b581e10310f04d8064a4000f00200c62070502ca140b2508850 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 288526708 1250 288525458 288525467
    0xd03050106140310050603040308090c01090b0307050c010b060d0209010305132f0315010923011e051005070201080a02040b0706020a0c05060a0b0a05040509100b0a1d0103020406080d 80
    0x1e1072510355003aa90304c2c3c5480c603040480c811203034409500014044204028160404042880785550340e058981400c2c3d43c00044440390790034041d050600905101040b10f161290000d041140d0711a000025800c0350b51300005c040c1e41101c0c120155a80e0009115001940d00d030103846d80002140414510b600d09aa03103240902c0c4801000600e18144030f089105003000c45030320407582032009020381d82200d00c0050b036240010000d0050305101d60a002100301c2609440402da80300c402049603d008036400c10216801400c28003501076594030f0860070208440c0d80b64103800558404d951201039031102071740b0001d001ca5400401c07030030180f0310500c42000900307403c40440e0306040d40983c0050b07071042406000d894180361840060300f244079140c104066008150300041c0c2984040b6012100c103030762503040101b5944203c54140300c80e0040c1455841103803554102d072420000040c0291030083d103459100c150030150a4000c3c41984441c0c00400650400340315040c080c1c054100a0040307540c40501c041c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 288527958 1250 288526708 288526727
    0x40c11070303110a0c0612050c0a0c12020f03190809060405030922050f010e01090b01020a060c11030703050d05010b07050a0308060f151e04030b130f0b07050a020d03050106 76
    0x9081c043d41008602d090001403144407511030740034264401c4580c54010040000072030b25101140b05280001203070101c5072020a98148840e151f03030b14160b541c6d060b600d007000d01c840c00000da0113620034a04610103204050028080c3d8082c1880415102100544010324804000e803a0120303540185080c0030100301e010040340c0c0d9403442921524050b82f40380c510361022000c00b015410303903c1d1034481806505206028400e04850940e0142c412690b00c0e803803008125030a82d082c07580075a0090400000290054002c10340010540c1000c03a140d4840441180c150b51124204500107000015070191500151048601400f05030400c14101103083d5181035841e0700002001d81400201030014203180c0d94119502903201d0050705241344104402d10982840d0044401162134101c002508048034107401c081d2000c8a40014181005032604440c1d096000060380064030100d1a80b101da0020407840c010075801906265141071340c0e000b503103000904043d0100c55050405041c80700402c9001ea00000c450b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 288529208 1250 288527958 288527963
    0xc09030b15100c0b0702010506010e120309150304050601150c03050903250303020c060c0d0813120806130c12150801091b1d01090902011b0c05040c110703 68
    0x80800d5264203031a006a0004000c40c01e07070101004807090b0b6030340da016000c500c44900c42c9142d0b8600f030b120440164240e48044075154000342c0200c05c0c0140324a8007500d410036070601001900c2c074080e060310100c0d8841d8100c1c0c00c2c03154020310020901c010003004000140c01800035608501c0016201d54000700800c001803009001c214000ca100c1d821a503090201c0712583c50030800304082961034001d40070404100b88001d40c094018140c445030f55050036002c82d8082400e10024081c0200b071080c043e00d0054025201c2c2990121180c0b0303110010f000144040590081034603000f100d4640b10301040030251808403040c50050502c0880e8240d9030300840d0b60380c0480350041c03000c9400600a20110021100d170741c840c030410740c248070002013400240100150110400c5101e103000070348484080c660180d5600c00410f0006040f4010801da04065209044607441403400d038842050010031607001031003040342592148041c0008010a181030712803529641d00c141005181d0a180301100780c2c90b09503e2002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 288530458 1250 288529208 288529223
    0x50c0c0607020f030718060e150121020c030d0513030816020a05060f070e060408060106030b13150e070201140f0a021b010902010905060c031b0102130311130c0903 72
    0x1c0900719980c40700c2ca0012a00c02500b12940695140c210381000c4920020700e0700c40e18503191000c20304403c11000c1c00e00c0ba0380011074880c0703001381c0140115110020442c40e01046502406100c000b09807900050030112a054001c50b10342407a803c500302220000b80841c030301040d00b48100750010380c10258041d48450b41c1800030981940942e0168204094180000d003030340100c00030008078000e0310442c1c034043c8503150f0311208401045c02c2449a14440d601401e00140d010b0001000310621a410000c00c11102500080c07181841005110540782c00402e4400321403c1c5085c1800304e11140602c0c15444aa244001d01880c001e032b030400000603101030300b03641c18100e02c04005101055550119184002c00034124088100e095000d64020030001b5002c074005448500000f0b113034a449da0070b0310f090b0003203c3c000d5480d0141805c010340c103c541000342c00b2040e5400340028810900070091610040d0300a80300c031340394812580208a02e0600d04c01a8000b1030b490654031b2180d041d4004d01d48000d60307600411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 288531708 1250 288530458 288530467
    0xb0403110103090b0f1918140601050310021312030806040b04020906090f18010e011d07140304020d0605010f140a03080406080405010902150a030507030c0e0d06090501020f19050c0c06 81
    0x180740c58110410481840c0c51b50802c1d90100240090903802420740740501908800c000454060a4461310288aa1641640052000d0008825690081406044d40e18023064419500c1c0f20850124018030317400d602090b02001004802d0405010303040401303004460861030a51040006400da0041418a038014000000c07c000d06403240608079040341d05807050030842d580d50f007680d4002c0040c2400f403280d911111041904051940f580168080c0407981c40b5003100358032918120019801c003d0050b030b4840341c0d80300c0d4800464290720803540030303016195884005a0800100c0034001c01c0070700c0918000c03034003000d041010807280000d46080d21070515007200151101d05000780500210240030b0f60101400c045d0b4803062203014020481c1c0e82d00d40c1c80601c0300780d1740d111003a411200205001c0010900c0109524020318058130410310051140340005100303000303625001d089800c030180181d60a50300085034040c99216440b020300c0c0741c000d0300c0c0803031400318000801c9880d40c00f00c1c2543c84c012000440d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 288532958 1250 288531708 288531721
    0x4090b031009230c1e010e120106140315060d03090b0d0506131814120c0303010f0b0c1002070609060c031505030c0a1208130b0403110103090b0f 64
    0x1103078195100d80d20406210308055400c0070740050040d2025811040400d8201510011000c42c210805441c02400c0702a000704c280c5140e01d904054807142c03410091501c01c0094682d5690031101c0e0901d0211000041d85801d0502c926640c04170042d903d403003503001c1079a402e8110541c2d920fa40d4000c1c4c0c180c60410203900d00b807406540310b504640103202821004140d01111082c03550061740300c3c4c0811644071481006040080d0300300c49080301c60032145a42d442604000c119035540d84286d1120090807698000c42905400e4110340100c0344580140e0400070040041e10074030410f50019040041c1400d00c1c041c07800b52002e90b1114145001c0100c5500860880203004040d400030b000ca642001c0c1c248810519104024020030707100070480400d084428010405090000704414440c1000e080c40c00c0550070800c448003004150b85040301e003c3c0302044a030101d481d150a81c140284510b0340116225070446c5040b900b005c88003e0540e04161030030b800100411200e2030030507004518007407001c40315112107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 288534208 1250 288532958 288532963
    0x60501200a260d051005180402040504080c1006050307050a08032d040605130801200c030d09050303070809012013080d11010f020405100f021504120806010305090304090b03 76
    0x1004000311070b0224401c00c020036030b038112a2161303883d8094000c0341a11703a4104492410031621300700741d0110b8000040c0050803e54070840d0054096040d49081c0a01e4501481ca410030000c3e01c4044c003629480300300f14508007005008081c10003110b86681c01402c1120307540e034a000c2c0c0038943e000c50300c0c000700003440784404034200c0d00c00744170031803a0341da4442d140c480c050241d900c40a10825491402d0100040c00d100610504c408810700c10062081100301c0707012022207411103030b00004103000400c90450105154420301c80350034454001b89d0b4072490300280103801008003c0c000032031030b41001c200b84800c007203001198030b035005055956620b841c09050402c2107240c03985c01c1000940305407054070380c030729030410302c403000c414015002400803100300001d40013030340a14821240c0100408010b540c1050140240b030705428054130407100c240f03e041c102c6120100064070300b60703440e1600b00c403c00c0c60554004160f07640b2100078201884541800300080d40c0ea449188100d403495540c4441a0203156001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 288535458 1250 288534208 288534263
    0xe04021020030a03050f07020d020c040b011704060606020d0318080d021b070510020c060405120f0604030f09092003070509040f0e0607090b0306090a0906020706060501200a 76
    0x78401c40e51035a14504001d40140015500101c510804500142180b480001ea1440d98441036020300000ea6460040c400a000c0522420307060280041901805441040040e44100d00414021908601d02400a410591006c81000c10141046030b14841c040014500d086220391000c2196618100500614002e01441c0440b02240c2d02e00e100d400181c890000380305040c2d40d4101c40035044d0505d110030a9a50f4001c6000e4030f6080031060104200d40d141c004000d480050010040e81c0c01d01080c461224102201110202e0129280c00e089005280c1e0250713049000c0d040c0400c040188030100c1d0208800e6941030301c0752420050b000400100683e100d1011b60380c43c0c52000d802400407102504034031015003882c0b41c10002c6e03889042d0000c0d541511071404003040301c0b10515550b15603107401c02489022000203080c1c0c25025101e01c00f45c8001120751001f040c41c24020311000418078104000142142200c801408502c10811800203e4401c0440c0584005074020070040c4503080000380d10024010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 288536708 1250 288535458 288535517
    0x414010c15021201060210140f070c0210050406030b09092137050306011b0302160605030a050106030203011a0705070806070816050301060c03050319180204060e040210 74
    0x420092008030f10705901506980d01c0f0340948140400e41d500400444081042030301070f0008020100d1902c48920024039005012494002019001600800c0300090342200e224002140002e040042c10b5141c070542d034804000301c50040300c60500900e51503550302d00c0c00c1d9401c401000b1710801d081c0800e592040fa80c01480203d100300700080030303480203107030237001d4451000c2d58414034100d40c16051040084a12440c8141c44548101c05120012400d419116070304030150b01c65907090190401c1103480d8000280242c1c0da50a42d00c4c40d0441415083d00c0040e48071105060041c0010b000d004e07000084a20720b91240c8042c80d44410030340c14042c2c40d01c0f9103540010610f000740800d00030140d40c4820000e00c10442c03150f850b20b03038284440080720140300c00d03c51318000a1990800d040080d01c00d40045410a0005922403040000c0c00c0b81101180c8927002d0204a40340c07010600c0046003018003481d00201403d601d042494500354000c6407444038000401c03010051601000300c2c460715086403000003901c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 288537958 1250 288536708 288536711
    0xa080f1314030918060a0e1306060e040317060303090d020a09091103070f06050405010c14070b190905061801050f0316031407091505040b1207140414010c15 69
    0x110703103403180e8680d40542c440300c1c000c40750403e1201da01201074821600030382000d0040040b0300d10300b1911035003090000d410315880780032900c1c00304085210741c041d4201408da41c0b200206581400c0c5000f0f04054510349a5030060f80302481001030a64010043e105540000d64100d15418913520010f8908243c3d80c0020f074160b032a00c480b41c400c0c002958070b070402e00041a0200e900b01511582c0e007034104e8880b031103103c000171003c00003401154420900c555882e84691000070b1885801d00d602c5041c0112504101386004001c0b801d420410040600a005d101c47c508007485c01f5800c24011910501c1010102a41d981c080450040c16900c9041100c080c100140403003030300d908005403d05254040c0140c8203001031704000119828001c602e40560043ca03490b02c401c00054070781803400440ad20441410010f010003440f00165a07d02c500c000c0001d1000d618680d21285481800542303440c40341000001c60302010f0000b4054105000005400d085003420701010103625072a118040601000715050901d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 288539208 1250 288537958 288537983
    0xe030114060414010b0d1802120f0115061413030519060c05040501170603071802030f0c1606110721020c121b0f03060106020319050a080f13 62
    0xc00011400030300800d01207900344150f6803040c1008401c2802801a0307801004104440c403002c24042c4e004007000c05103480640d42c03030403907030b000170700440c840c1402224660402e602d000e4246400b8880c030201c551301c5000d80c030704035030400070001c181840c46034002005840004070040b00850b142e0741c0300011580103044402500500c020f40040c5070985d80f00b29804c80c148500700200901900503242a00e1040e95400b05000d12100c010710348100c054100b64250055800204070907031803201c1c07250b01802110f005a5203040040c101c16000400403c0c03c03200304010f01200c2520076240350301d80c10303142c0c1081010032800b54018514410f4401c4190050160110071341007040100d90f0024914042138030303002e036100102107034240b054a10365408454459000485c400a03040ba5071418018070900203007081d49411380010201c1c4c030300311081e0042c0025074008207503014120800e40811110307070403a2401504108482402500e4030781c01034261586505070f1320000304900001c4c40c00547da2030300203e08040785e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 288540458 1250 288539208 288539231
    0x61a0c1222060f0c030c1a180c120604080a02011104150f03060501080a020f0f070606080d02030c0d030203070c0c0b0406020c0604050a093801090e071403070e0301 72
    0x185038005080e08410100540c00042d458010381003094000250b40340e9000f4040650740448214100e030008513010419800c02c1001c041000e0042845a007035607042100c2549041206131900c040d5070211031182d140c16094115242000c10728640141e80a0411900c41040c110140e02420f95072001a042440201c0e00040c544065500f00300c2c1c4c201d064a900c04030150900084055503201d01420740415060300c0452080000c0d54010f000e840480410365041190010940340254080c401c1030310306503220a824401070304284445a60320071130340001c510b0001200b01068655010076244802d2641c0800001d20281c061610580d8a0b0340c0151010012601c40000c45115082401000014880c4010402c0103043c404c00b11800d50780d0040030110311074540380280004d0062280305450b007039070800201003401010740e13000740c00303a83c040408600440170b40001480030350280e000303805580915003070098480c0c0006030740711a403030907407001503a035900c3d0401a07954240848009030190301e002000b510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 288541708 1250 288540458 288540487
    0xd20060f0a0c030e0a11040b0402030a06050307120f02100e060c01051503160902090423061509060a0305180f030301080609030403021518060c1c03061a0c12 69
    0x706150001e81000100c1d2048000c074100d984600a44201d6480b0b0007424001c901490900303821814028808100c40208074040750580e002516510022602da16003031080d4034003803240001911002007454202c27182919008454460080080e000d46207845001080702d02c5107007464500314028007055683c3d01c14801040c028041222070820a0301c11140e00540d900e40841e070b5200081c900444008005c1c00c14420500a6000d0103c15510070390392101141101c82600c0346800745034501c582c400c4189020028840c845001d82c080003c07800007004500004c2c0d4507041560210340d40c5140015041c0e8401c8506181c80100f408204054812185290045440000250306032031241d001d460554541e03000e05652400355000080d40300600400a65483c41c01401130003000012031601d80000c0f080f8404908254000c00c048015608080703844c184c001d03205074a0300d42c49101840d042200700e01e05001c0714840c0179210910f08a240e00005c03582c104101c20040100b04142505502c0d40d82c09100030b4400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 288542958 1250 288541708 288541711
    0x62703030c020d09180f090f03020f060606030f040203120d0c11160317041a041d06031009060b040203010608010510030204060f081807080615090402030d20060f 71
    0xa000034140031074140200d20108107072050001c60340b242400182000c0c4505d00001502c48400c0c1c4440c2d403900c8054003599140070324a0303998058840c240304c0310341301d04000f42000c4030030803c20fa0a90102090004985403c01140d500403a05040800d16850718030003e0f06080d0b440c0d03115a020000840d00221807905603000e104418800c0d150052210900307140151a594003601c000c480d02e80a030b43c20808503510b6104250700d102c140005c2c525003520b07120050070303240d0510016000c030703100481c0520100c20391302541c4210030b411084000c486e02c1c0c80400603907030300c1460154000084c1c41d5420310040020716007181d580d1440040055480e5a15940c00620f00142441180d118003500c000703540c3d180e40280300311410348100b40c0c0c0755804400d0103e8141d8281078050400041e820039903c10002070903090060102501c900c10250040b81400500002a071482404191050190301c6c180070060b5400035a00e061007490341022051500d1100e01a216074a02c03405158150188908000c00c1181a80009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 288544208 1250 288542958 288542963
    0xc0b030a0605040605030a08131a1201050f030d18090f02030604060608040b0a0903050d020a030b1203121504060510020c040c0309031718010c030605100c0f0b040627 73
    0x1045480e95410400058a130300c1e21420342c054200070003840c0072542d100020811b892030f07aa00b210750075540300049071a10100030003004070741d0004140708603484817075808540105003c0310300018070040d250000b601c480700c0351549410f1050a075150040224054003200043c90600c5c0108441603a50b041c002c040d500442d03000e4491032900702d010072101d008400b5580070b65048503444506540b01201600113004100c0e084e0140f241c10f202a502c00e0702940000c0204001607500401ca0303454a00a1083c0200103070180e68681d0010b000300d9403003042d66044190301891001c2400c44400c8600d01007001088980c00c40c5400045c102e500d000441e0b00060000d6404000780c6d0300304020510b200c001c400300c0c0d04c0106e0040000b074040c80c10342d000746070082d5180d03000450f40344500383d40f8960840c010708454020850031301003034941d00108000e2a001921001c62103180c14034102c07082d100d03910301a071241000b43c000c10b2480c4100103e401e0205c0c0360710440c1c1d04111101c80002141c01d4461545402c170001340308 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 288545458 1250 288544208 288544211
    0x6030e060906010f03170409020a02010b0306060604180f020705010212011a03060a050d03140c0124060203121b030c030103061d0309100c0b0c1c06060c02010e0402070c0b030a 77
    0x104070684000100ea078101c4101e0211810300604544c0c46c100303440d90210080318190001d12010503100800d100500218076a60000180d120001090500700b440044c603a92013500e0910080044900011203a510700c041c915000030140d2950792003800070b000d0b900f800340040d0704c003041c3d103040c1891014426050701c0000c043c285143c406202506c0140c40b00b00c411542003003540c1e40401c05414070046010740303144a4148405000c0e42c1490160050b0490b801142c0d151707446180480c014004200d200d0500d20303654410014003424002c01a47d01d214080400310744520980006201300d010100390b00c0e450100c80341c00c960342c2c00e2114801e41d1540007800241c0d003951030704490710307007801c80c8510702e922401c00f8001031030034002c0e00c100300260540000800010b22100d00c00e1600081c082c040c0d464841c482d04107071a80c0350b401c586034400d4010700c9040510b184502d841003c0c005190801c18070840e00381d0928140040d1907050300400c02900505500a2418812003400f160200704600035600c0f032000b1510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 288546708 1250 288545458 288545461
    0x12180b09221404050102090f120606270a0b0a05041a040b06070203070803030a11130b0708070b07093809041401062706080a05190606030e06 62
    0x910044500c60006466444607440c920054101800601080014211000090111088444103185590407201210390381d60020301080e4601c2e00104031038007008207445d998440c602c2146525079541019020720b02c5003110507480482624124403007103402810006107220790420441c3c18016080702e404003071140d101e56402240d00d040520032080184040119078680c00c1d00007040c4001007a00424580d0402c1d000c20520003d03031020403044000341101c2004583d41e14018103210111984103040104080080004060b0380c543d02005038251404081701a43c2e98a4901e400d408901c6030101c004c041078404410000110340150f1910203c8100c05c6070244281ea80d540b0102005900c8540000501d01800e40c502a103000240a0220800060000a0040d00c9400190741d045000da102c00001800d443e00b64070f00100c940c1e60301400100d0300c4094078207203080c0440901b03640002001d040f10203a50380c001a5070030620080c08280c10300c00d880c042166545410008016011821040365244500b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 288547958 1250 288546708 288546719
    0x20105041e12030f0813150c030b0406030c09050c0412060b0f120d090e07091701110708070317040c09181403130b120103030f021218030d020d02030f070303091218 72
    0x1c3c01b480e05950b000c0d038043c10011800c0e194400502803041501c0802d0b80e0b51082981c2a101d5105100c05035024010400700180b5084120013038800041c01601c400e0340c184070410034400b0f5001c2c0500c90aa00c9000401d44000d00d40104c0d43d84a0a080705c1d5501c08110744c8118103000380804c051805140c0f60740d03950082515400c8030401c146040e910080087e02c4000c0c100401a6840d10f03200c40040818001b2408480f00040394202360400c1c607095030001c2001505108041d080750380c00a10304664550720140703213084d48170140c554499100d0010159200c47c100101c0080002921003040e9105450400c5240307001c0e041b5550f41c01c0550020150000450081004003848099404210420012078042d80c215902213800b0f1107902c07c0b48082d8456034815250303282030325020300a10580000f050880340c103e1800c2520344419410110159040001c00105480e408021280215401c80403182e03920700c00c1c81e088005041c2441c020302000d00c0d02405502007a40003030341020103100c003842180a551120b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 288549208 1250 288547958 288547981
    0x11100c0302030d0b0102121207080a0c0914060c0a030206160504030c060507140f03030a0c0807020a110a1212030605090709030609080c06040507180603020105041e12030f08 76
    0x240014000d40c0c01880303500c0340300441ea0804501010184141d403801c280c04d200c000402e4100c1005150858288002c120406920245c2c59510140011050088180c1848086c000400700d008410042045c9403043c0c2560b1128011901e480c0341000c11500c0c444142c7c00c000f9104d69050f04e0f00840700003584200c0076014420070503501682c1d0808aa01c1c001c6150030000d0320668411b14045a14680d440044240900203010226101801c1d4000c2c0d0f13500d1a00b600c4038011580400d02c0d41003401102d0050007601035000400040c031a80c44041c02c1c414094101c0003421900c0070794803c2ca5069180d4030000c0c01c20003580ea5070624042203071003e00105407948104484020101c89030340c0080c0610004001180040c3c005600d03685c0280391107031030500e0f020303482d40c00c00904480c1515554800e0740c04002d106070b0124043ca99400c0740c8800c008007401c641c00208648aa8404c10b440300c038032201541d03244841502202d00500d2000c400f403a071403003d4500904900807082c80c4001140c149800601000010f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 288550458 1250 288549208 288549227
    0x207030c060327050a08030106030e060c18041a060a05040314030304050d0503041b060f02070f0f03080702040f1409010c0801060c0308070207320303041a0d0f0501031110 75
    0xf03203048001c43c0b000416040c86041d1440ca0242d072180b00d050710480c00300e00d841c5c0045000e04400c3da4041b5415a640303810500d414005030441c80b081708204458880e0640c00c034001c2c1d00030602120041813410400b10441410440c800c4c1055020900141c2c22100c150000014822a403081c510482509030030707001c0355100d000c00c44010b8104d4000d41c0c402058103110708010f49d0300610810801042c0c2d8984500201032040d550883d0020907100c221009140b038042008000912665110810f00303030820021060b81081c81c84000d0404401080050866440342c1100101e0b425454007000074203c13151030b0381c103407000079a844290381d4030b800206041c103881b59030fa20f8103a0b03045450b151611360f5170342c2e41140c840000409101c00c40c010710b600442c001c4007869000c1a91014030081292014150300d03a0301044412800c405e100ea0b204000c00c0001100c441810b10a00843d0910b10361102c804d15051400762450344039140f0618a817100100c00c100c94080c58602400d41a82c8803090070f05003081c1503030010305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 288551708 1250 288550458 288550481
    0x40b06070b0c0a090f0308090405060925110f070f060804020102060714090405090d03181211030c010e010903030608150f15041d010b031915060b07030207030c0603 72
    0x84100014070300c680740400070700406683e803400a0300290742d5603c480c50060700360402c648083d0000b4503d842480d040c083c00e6082041110b2244940c01c10324220107510100e0038002d00000c626200c500900d074090105401100c05a10030b80d884003015a01c01502c49899000742c01c01500d6201001c42ca051245401e030f442194184c00030401500c41711400e54a24900b001921190f49040284481940b04d50041a0080b0807180c024524506c00c40c0380a029252480701c081c42644906c440707000807940360041410500801c0c1407500c4125000c5000078214412032040c0c0d14030350700300b10706100c101034154464141c003402a5420001c003521121000e4464120380701580d4110814404035041401c080f8070720346c201041d5011000d03610300c4c600104055036030105084150070320305005000745003002e010b82000340304100c02400c030b0030707401808442c3c60f60003114025044c0d2010341540054554190b00c50340240003000444c1e9162102c0c7d00c0c000395541501d000468410607000c1340024114000c0c02003040404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 288552958 1250 288551708 288551723
    0x31a13030503010b0f09061207030b0d030e040209010908070308070516150f030f0f060e01052d010306035a060f0e0f0601050316031e02100509040b0607 67
    0x7444d103d007880031034100f01c03101d02e02d0300401c105651181e5503003002401c0328413448039064814980b903440501214070404043e40124940800040000d500062075281c04200704c50058550094400480c3c20f400709030445106489860408824041c2041c0600a020720600843d00010350182030500000c0d546c6c8a00380d000c12100c040b03020b04500800d181201124203140005a4402805042c000e0703e403040340c041040c1742e03038150910840c2c410b030702c0e081c2c0580707030590f076001c007405003215401c0d24103841a182081c421100940741e031041c0e00c641c2007031000310b0300100075090200074105580302c00201e408074264808807005400100c0840020030716940032141c0c40d010b508142c400400c180c107000401044950a03039866610642d6001031043c90101d960210082c1a00c024198401d480e048060f003090b0b109501c029040c865203032118240d0826039901ca445030501da00204040b0904550914009612603ca1410001020780c0540900101c40d4200c0d02841b03403c1380801403051510410b0400b0b441c1c2d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 288554208 1250 288552958 288552961
    0x10801031511040f090f020306010c1401200d0e0c0616080c031b070f0509061e090a0203071b0b010b090303070c080c090a0e1005091501031a13030503 66
    0x20605811240340c010401d00200350608042414107503030f8003a0b08035985507148100180301051191050042d0300c503007020110b195003040400646400700417000284003503e5942210382100080d0440800c28240e0b000c40d9500c80016801060641c1000c01c02c40720152608800307540302600000c0c0034110303030740240c80686420031003c08000084000441500c0c2804100841030000c1c404000410000c2541100d04088840c0365081504041c0c0c15400103007030b400540700501095890756801508003c04460404450a00000120a09151200040d03002d020203081000c4211280c000310f1141c4142c2d500c0d9000007410b180680007101c1e1807200039101c4001c00c0c00511581c0c3c0040c00502d03481034010116410700e0516588c00d03405001540241e40250814040e890950402c2c4009542200340d1800c184000c1a100e01c0d095a1280031002034140b054a036804140d003440144059488002d0040d907613441503869081c65205000114080c107000c0001e400000c844002d4011070840c1d16038165106840c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 288555458 1250 288554208 288554213
    0x3070c02040222030803011d07080a150b030421020f1005060d02150403031e0509010c060209040612050f010506010c03030b1503040b0609100f09200309150c0901080103 74
    0xd4009001c142c0d01000103c86101045100b03002d0000118410000c01e0b0303a0b5030604410007502980459084070f00310210702801003050304840e031942c0c840401407002030b029106071410b2000a465500c072001000000080c0002e10003030340c241a109285100421014022403a0304980e10440d007401d20180d5000705030707208402c020700e03040b20750404001088500c003041c01d600010841082111000340244e8001010005c1640001d41016003499030120180d0f4a16840005030240c41030200031030400018071000d000700580e540c10380d00c01d41c0c070103081080515102c1f010311603249184072080d03440780b00341141d11401d20700500600d03105000603555060b250346c50340c1d0158060408865034550044040c0c840c006442c2221010b1403150b4010244c4001500f000024001041c0001e0800302290b440c0341d00520140390344198201c111015030030b000600040150140000001c41d407106170700e9800c00401d002e00400c00285070328103a04491046411500d500d4a00c2e01d0038402d0000182c042012030004202 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 288556708 1250 288555458 288555461
    0x3020f07120311151602100b0609040f110d020a030b0616022116140d05030f16020a1e090203040209040b0901021c0c0207060809070e04020d06050103050312060603070c0204 76
    0x3e1500d002c000b258000d8043c120b44400754641203072034001140903c9502e020181d4100721490a012501c2000c1048091410215186101d00b04100f4000c80e12440305c403060701d50541c0301551250b01280e2650b00e60960704a18406940180344510019040a01d26206860144100c903281050f05403c0520b184142c2c2c02d110b0071241c2c010b085800d8441200740e118600c001402208490034007011314030491420940b01511402010b02a1800b0340b03488910800090000021180002110b6450503224039204c0d115014003003d01d02c000b500000b044000059910360642c2c8182e001000c01000300b02d0756250b0900604a000c1150f010790b110300311101140101d1701c00e04c03071190000e4541c0c001510b0f000b04d890b030301020341a0594075021100e0707072498034000e42e56050001c40c0107003440b4502241c003801c00958540d40ca48041c0244461510180e010804650796428101e59495100d201400250f80d24100940c603a0000d408802002149a00082c3c8074680f810849202c0c4509454910140e400b90f001e100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 288557958 1250 288556708 288556727
    0x270e0a09080408100902040e212a0604030e0306040807150f1410061107050f0307081b150703020a0308060f0607110f040c090b090d080408030703020f071203 69
    0x101c0380001000080f5004005000d0700d102e1000f18403020410b154188180030403204510361420440d00a85061401e409120700000d45441c11512507d4581c0346030010708086803000044412802106a4522a100004204c8034452070007500c48103003482941c0c09150f10b4403000c4a004003443c0b010090400041c06001002840d403d10f0880080c0c00b078603189040040f950301d00c00345202d0303442243c1088080404815094090400d501e01a03201c0104800c1d001c0d92000240209407040401500410752600c0404c078500044c800b54080341e010408504090400c0c3c4002c40143d80103000040b0110b105a01d0581120140340c0e06600501c1103002070b4078101c950500260407258010308030150b60207541d54240c00307804424043e18280f080b28101c4001c10420800034030f2110300550410030007a0b071640d04050382d50204c546018400c3d680300102c071f0006100080c01c80005003242030104011494500010182011600c29002c80b403004801c003d25541d280000d12500b0302c040490202880042d103c2e45402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 288559208 1250 288557958 288557963
    0x8120f0304031b03230f04030b0402040b04141b1207031805010e150609040209040b070203131202131509090602044103060a0509031603270e0a09 64
    0x2d0f011012480b0840800183c07004107070005071540c14800b104c61612144030017561980c0181628050203298076102900461101401c000340c01c4000031b0654071283c0020715602001270007046030f2030b04200c010b04844019220900300d40250101c0d24402075180c3c1c101c503000c0204000d0309106940300f01c011809000b1400225003240288801e84001810034003a0405140b404800341c1500710c10480c001000041c01030605105464220500c80940c54444001d40c00ca80c110b0410500b50399500c0081e840e5204650700c0244510b981a40003c003d011444040317201882101d4111442d1621001d81c016141d4a29070710202c07103c4402c0c2084140c681d035026102407031260300c1c09804c2076500c181258180414412000c640b002d0604c4441c80c60070794841c0055002c910700e00c10304507101d80d08040707690b030f45000b1f01d41545980d03500c6c040f0710712150403c259100e07811001017141000750145001020a02007068070800414005000403000d000440c103002540e00326103908003e81d68084648001d402c142105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 288560458 1250 288559208 288559217
    0xf02010309050a05072d06030207020102031e041505070c170703021306090b010903030e040f0e1b130902030a0f0212030c011a0a050f04090602040801020408010f0608120f030403 78
    0x6500c00140d05202803071400c0d003c4c1010f0000545401440207042c1c000309000c00003548281c81c0d20340381089502c1d1550035506241340042e01d806070307403005034038500c22201e2503044207069011070040c101a40c40208241d072400c900481551b48840c40c00d4446014030000206500c08120341400080c12441d039000d2401141000c5944156494001c112005100c0c0c40c0d8803a8141c8a504c00d00c0b0f040c0d140c0c00754040580080c40c08041c081d18548009065090001c0524401d07601c46080410100e025000030200d880030005984032011109480c011045840d85d00c00d005808038044505c029103544210144140c0140c003030000703d0b8482c0d075242680c1c894030718204d03403009c10170320041c00360f034010401b030414802013000024901280d10a013548034020040c14920444e511081031140b0f840e0014494501607041e5404200c0c49618503110010340583d0b003124031250300c003203400601c1040c15000030380189e2280c0fa0030003900b81c40e409042e8840c40344095440707220a00f040200c01e90241080115403140c000e190 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 288561708 1250 288560458 288560471
    0x6040b09151e0c0c0901080319020c040f090303050f1b0c010e07031b080a17030a0b090709060305090307031b11030d17090606090105040c05070c0e042d0f020103 71
    0x4003000d01c0c000c902990b041000c0040303810f404104003004a284426002c65103003540d580341444483da40c0c41080304108040849103600c2047c00d000300002210400c0080092007150713828020f010081a14a0b07059001070704180c0468100c1d80f00d1040107010751070782c404140b200070108203410003581c892245044659600c0c00d2140140c8001d02900c0059803044880040c1d01076aa0400e840308001508000c5440c0c001e03030040360000d00c411901503903070501041450340b640d0314040d940d402442203ca296422040134020004240d50182030032054458903101005070303446030080381da500c1c00761080083c04104401c614041d0000c1700c00092085c588105412180306010320082800e00ba480c40fa10004204110000f000b201c020301c3c0c01e07030f40c03110b810001041d1a151900c0020f804e42c006100d194000c540d074410442d1070b02c1c4a401112441c3d40c004800821041e0380e000d07a6a4103046c106c0f0b054641c10400386100d0000c0026040c91195180d00c9618203c1c06d10050b220001c900b00c0002040b070626580d0302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 288562958 1250 288561708 288561727
    0x3040509040503030117030f0a110f0d050d180b01030b04021207060302190203070b010512010906060f05010306050306070e0405130f0b060406050409020102070b0c15101406040b0915 80
    0xd11480c0708500c148040c58695260042c031500c00c1c0905024102c168100344070300c188040085003503d020800903c0d00f000200b1403090000c1c180080005c0c2c500190042c051040001c2d500000180b00d100e0003075804114108010608000c05440007000400844484d40104040350056884541050005111141031038010741141e04e40080c039803207131021a40200311a00042c2404d000a240b04061b400036500d090659a1405404001402111300c101c00692010000c0e0000354840e0034220780c0b040003004256140c000401d205045481076900203810101c0100e40345c140403c0342c074000d12a0380c440b580d40342e02d0313541040301414008040d5009600643c00c0900030840d100c54090702e05010b170b01e002c40c1c1402d0a105000541e926070304010701a031300b00503c910046c0d9001810380300703e4420502c40380d25140381c08580750a2142d0002604000070145003400303c3c041d9564400300c00c651f14030f5880d0002922003010b2002034000c9229180c84450144407003c002c0c1051000d144095845154040c40c000086 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 288564208 1250 288562958 288562969
    0x1031401020f07030f180b070b040602190818010e120702010c06050a0504060b0f0d08070c03020415081b0a090b011e0306050a090504240605061b211803030405 70
    0x11401d5000039512240c0c5e01c1c4103500203140d5245800980404811a41841072251161094141c01010055544002403c0c88141e505490146c4c0380c2c17840094a8084000004004640c19940358400d0807100002d440c2c4090144a502801040d0102808c40800001d6140c1d0003030300164400d034140090300c3c8130b078000a0000d10445201364100440001e403800c040c1002c90440d1900300f502c600501c400425802a642c07845041440c55a22881455903007101c0e02d4030303444046003948003d400c54241601140000040c5500e08142c0345030008a403d80c0c400340502151080350815655041103522034144003410160300b001300b0902041c1041201c070307100107004800c2c1c030ba8804000b00c000381d0344503400c1c401031505003600c0008140b550f0b0144528186902d41640c402c0c010400f10040c0e404a100c40c61700b0f0701454002c0c100508006000c42d8031184a0701c141800050142c81e003180038000c0c6c501490181c1c103c115103e078156210583c441c00c000701e4850300e480307070b2500700a0b075035152009010000e4070342e460 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 288565458 1250 288564208 288564217
    0x1021b012708281b031d060c0607022a0d0209060d050d02010f0c030b060a05090a031217090a050a12020106051c02030106082a0112050708061905030601031401020f 72
    0x1001c0d0740740f000403010007009050007443c114102c1c501a030315003120040303580500807032a00d2000002d649509844d801c0080e9161140c02801034050003540d003003141c40d41d0081a01c842c0007081c40c42c501ca07119090915203106c031100070021580460280d0000f4090708001d502194881d40180c01640711007116211103140003c40c90421006039103800c011126031101c2d0180b160300401d41d0500348982ca6038000014110b008402e5440c00300305000c605514196203511607040215000702c0442000036030b6010042c5051041c03201d42c64035146002c0400c010550005550044175000009003e000200381d80d00c1c0e0500d1000f0780034400315901da01c000300301580c034026610049000000200c01c0000b140c8117060075249241d2001146800003d0004503001030340382103607004110081d860103004490300041c0e5074410b08231100b0b00068600780030408c400c2e07000084980940d000302c41c600040d01c0c0c8100001c1110307000d409816015080003004000107140100040c0400058074005420414142511900740d0030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 288566708 1250 288565458 288565507
    0xc02030105042006040608160207030c0b04060813050c12070515210907090b040f0603030c1b05060904050a060b032503050103020618031e01021b012708 67
    0x3e0300900400c0e12030108081c0207145094844d182401d00d0300b01e018007184030080c0a0888010208400c2c5910f504c01e10000c40515801342c8410740d26500c490107040907030828002c0c0400f2a468801250141c881c41990080b001e82c030000520f50701480303000740000c25401020700d42d40703071180b2003020850382d0310310542c0d20340e4550b2200d40f2030311101b0030015044e1104040e0200900d6650700800c1c0f280b00740c00480c110301605c0340200f0109071400c50201080041a0300c121100007036185c084040200342c0e019003145080d80c004e40d012254150b6500c05c040390100c41c0d100d039540c0880e0800c02c3d002e8500b06178020950118210034001358032030703458850b0300740d540c0211220252007c4580c507640c289036940299059000040c0b408101075811030380400d446100309a00e0201c1000d140400a120707641c1004180382000c06a41c180c41410701910100d4040d400418039200304200394030a0300e031042e81c14426003410070f0038800700c000c100403800d401078070034100c05105a07040b0400300301540901c082e0760101100303480c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 288567958 1250 288566708 288566723
    0x1218100b13090219140301050c030105010c0209180106120201030f0b0a090b0a0803040b0a021608371520070209060d060509060109050106050a0206070302130f0b09091312030c0c0203010504 83
    0x590035806c15003180e000504658907514140014015640d04c840c0c0d01041c66410380c0c8070381540e01c5102030680c44140c01c01b030300c80c800d41c203180c00401c0c031131074614a18101c01d2003070328140840000c03100c02c0000d43e038110850503000b00d644401000071505681240440070300150031500040d45540c8d21500b180c1c09604900405100004c0000105038100700781c44120000a222446090074031184544845100302160002808a030060034401c0c40c00710694846c200d12143c064000d40c043c07401c041d2420310890a444041d14015011114004000340c2c905540072415510385400d8240d402c00c25004c2010701004d40100030780540d140014502e100741360003107100d40000c1603198501f860320415108141c000d0b20410000748600306100b40c00084440c0c00c601d0508015841b07414180000d05407a0b05c9901c10f044059105100256020744400104104601580c00030361b2581c17890010500744e62a510014000c40d016504180d0252007984038102c20714051420700b403400b0319900061300b5500180c0c1c02b501c813030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 288569208 1250 288567958 288567989
    0x60902040305151f1404140f0708076201050d0b04021e03030a0309050c040b150306040914061608150904081218100b13090219 56
    0xc4050300394640c4200003119080f0440503034001d29000720183e00c111700d404040102c0700d581a9aa43d0404035980700407050b09605807074500340c55000c5c0174080d20701c01c01041b02070012036001441407410760950504440b8685031b00d102c410044c4402402e00e18201c0e502c006a980300c1070000a11080d80c0845038000400b014480f8800c410701085440c182c3c02684940318425032540022501c4280380d51250301112220ba04030411180034405810700316586602d03000004500d0442501544451340e602c0c0079000701c03030711894142c0a11046902d13140240742c0c0000c069140d03a4005140400550b030003a000b40001c641e00c081035540060001d19103030f850800340c11080400501c3c8060007000c040700b41c3c0078540115282420201c510401d00102c03c8140501c0b00500000c062041e018110707203400d11209406069031130304100074203240c508102c00003650b00a0842c00351540d000d80c01280c1d40404010040d0b41803403a807281e44130041100a1b4102d82001d1400103031642c1700c25007c441e000828403586c3c45442c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 288570458 1250 288569208 288569233
    0xe0f040e0708030301180b090c0c0f07060c050c15030f0c0904050114090a0c08010510140304121403250c061a0109060804120c0317090c0a0b0315090604060902040305 73
    0xd0b103506c0c60201d281ea500d040d00da80030982d109850203070840419241a0b6440030b4508440d41483c1e800200c100a0384250000090281c1e402042d60301424050383c15034499072040f8081007107800e800100106080005d20100c0c100042c500b5216400c5a401b406c1d42c0d04d07180960300401c094030800d0740680540e102d68900c1403010b043c21610954041c0200004001501c00e07070f00d0150003010180200c3e4025a01164101c4c1003a00079254001c2e15803003502b030355441c0d10301480c0c00d918109180700c1c54800201d40c00d03a900304004036042500e002d0304282c42d690781040411490004a01d44c80c00c600c3c8104030001141d540819414400d6a032054050743c20001c4800403100058861340300340c0d00c40030030801c0e000c04003c00304929004600b0b19580e20728008001e2069814110b41888500542c00c0210003040140700700703280001105400c43c0380980e20404031aa0314050b5100d5808200c0d00710060940384e8079002c4491a01c400200d0f80301d00700400020b80d098035010a1012038005401c2142c4580c000e0303046104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 288571708 1250 288570458 288570479
    0x604111c0b06120c0d030302090105090303031306140405120a1403090106081209011e090506041d0c07030f031e0905060f10181109040c1d040c0e0f040e0708030301 72
    0x80500703d80c40200700807400d040120b0301d000e90340340f0007604150f4003003841d1002d03038800c500701e5503030250040499489060022600c03408035215003044034034a25100b5080d5461080c011400c0c40f540d00900038008940a001c0084050350040446030100142c200207940402040f9010b5409100d50340300000322181441001e501c1d080c20b104480710812001e00c014801ca0ba4000943ca00440041c00300d003580043c3c404054035920b4181c1c001641c030640100340410f2038400780700c20031081c2e00741c0b48081c038003621014502d84c071501c6504000740000e0006d0000654240c002d811030400c850200c0c103100b400080d00d0581e001114407074981140e0703a800642c180003600d5800380300d55030442c0b004400341400918124442001085075521084c40540340c240d8178104100e20380a13105000350207417040c020300800300c000802d42021700b00748145180c0010202d0101d4109442107000c8440340780c464040e45a172120400003030075160000142d2141c1c44a007007108000007440780300c3c010300c40b10f4001c6480313504201c078400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 288572958 1250 288571708 288571729
    0x1e060405060a050c0d091a09030d060b161112030c0d0306050a080304150e0402190201050f04020310020c0f030406020a05100e03030a09060207020a03030906031a030604111c0b06 78
    0x10a00c0741000d05011300c0b002e81508581004003220400194101545803114440150811004804408a04200d2100c4001c0014040340000030010030800391941c0c0605100d000d04880c18020290f0311030032a0004003540000c801d131580051114007441c44a440c2940395500261018044d9007025040c5600d95406000e41000350070122292100700b428801031503540d0203644a0b00c0c51910a601d0301ba04011f00070100c00d5022a03014006554400b01e41c000000100b104896050042d8030301400900d01001020351140a41e0b40100a40a092501215803010b50010400051180100b0a8046000900f00002c2c00206038a40151801a50504240d403c00008203012104a801e0003030b4052210303404000c4a0b0700109400c800a03802c140760400200031700445100a4020308500004024140c001140074201c1e501d596050054800b5003c0c110074243c03404140c030b80c243d070001010400003292a100c0a950210181080c80d80752107141e0032114200d9868000d071080c41e099001d100342e81c1804400312 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 288574208 1250 288572958 288572971
    0x501030c08070f050618120307030504031505060a030b070509060c010603060b010804260723010c020703030813030e0a1410080103260415021006080601050102120c1e06040506 77
    0xd6000c4c80c0201040c0103101b0308041d181e4170010004c24146550300d040e42624000400e07012251940841e20700a441d682c000d00099072901500021003d84010750f006140c81100060040c1c0d003558a16910039800a0018042d01d041c020240030801c0e543d103405024200300b1038958000b0411a180d07060040458150508031030420100308100008039804016214000c5070501500032580c0c954403450142c1d014040c0020840d101a8041007145210b89542010310b48800c1c000f0030841ca000320301030381d0b206076501c00140410000300000d42c0250035000380054807400b90621482800703120b40050001800e0343c10400806801d16916a59410840c8800420602c9411f01e84c001d1f505640b10842607070386000e9242c0c43c00d991764041034a00c1c0807500c180c0d4000c010860400807443c80314207010791904503419020004e01d24140d000108181d000585604840060b0090800c898000c0d140280e82e501440350f00e00d5074440d4405200800418030006c4080032031b660701801a600309450610b08050025140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 288575458 1250 288574208 288574229
    0x7050a08060606180612070e010e06210a0209060a08040501060605070f06090303090b01090b030f03070b19021908071101060f06030b030c0406030f0311030c030a0c150501030c0807 79
    0x1000702c280c4070714080b120096085040c2d1406006002c00042491081440c2c802289501500f4890300941100c001040c030709090f21a44099001c0c402444110b00668054908000720100411440180d034440380d9004506080050300d480808000700d21181c1c0304690120018042504100502c81d0a11422000d402c40e40f0b0410316046a507154004000c0800c0c50107481651385005900406001e075000540113580100c040b8800d42c0e645014100418042e4440750080c0030b21010000c2c1d00c2008012124100c1d07100c03001c81c03225221103240240d86038001d5803ca19855080010b124013803400c01c0c42005503043c82e40c070010305103003485000f07040f0141c9036005100d9a041c200103012440c210140813080e1440391400040300804500000c0c50f041d802c0d545260014584800882400450160503003024000d840d03501150f01c3c0c0c001d00c0c60b600d2107800950b130340c0794000307000f42c114007440f44509502260181c6044001202228510340c125242a0300485000760658010000400300307000c40c9000304100c604 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 288576708 1250 288575458 288575461
    0x110d09170708030406030c0e0901150e030c1c140109210c020901050f04320f0702071503021c050603071706040809030a211805031e120c07050a0806 65
    0x2da0356030301d0040e030043c001490303241c10716a0f0040348a0743d0f01088002c00100090a40e50b543c2094500a0b03d090300e074400014002090405641000641c0004100c0050702d22030814003400540d8018800300c403003c88040382206060702045000740201c0309464061b07022407101d03d0100340d088007005e2540d04010140880c0e400e00001580d2005030710341c1103880a444009030900c1c2400007400030280041d0710720200e15441c22052103010503654000c031300040300100d4551a01c0300305548045c000e089840d00010303401200d00f8841d40b60070409411082416080141c2400303c1c0e0311200e40540d0042e40b04c201000da59004010b024501084400000d088080780b4030a900300c850642510b4600041016140a400103002101e03034504222541a840c3c05c0001c514000c5441000c4c64000c0300340f0038140c000580311034000c144040c241110041101c0c0c000307000344205011548000e810505400303003180240a004248002c03891010001d0505001c084081c0c1900ba01302810040074004581121500340d21040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 288577958 1250 288576708 288576719
    0xb0906150d0f32010501050a0911031503012a0801090c050a080c0f04120b06040501060c0308071e0207081b150d060807090b100206060f0f01110d091707 67
    0x50340c4400a68112010b01d4520b1800000314110210030b0f40c00107030a8040c1c4a03040b10340e0790b042d0b02c10ba040e50030490b21503160f29504e03200c08041d2802401c0c00180010100045034076044042c001e29101140038002140c04440d40c41c0724042110881071f116003213446070344a86030b40c6511424460240c08030350010003121850440003011070042403020710900c1000f00c0410404200d0b50b095030f85000c1d00c00c0105580d130707854a510b84060b2040c03070011151050910007280c3c0302c0c5440d02490341030f1140c640c0c854889040c16201190005000f0340050180045140d16100206c07501041a0111240d60020319505182076901071078410058031000030095082600b980d1983c4e0b941c0b03484002100f445030503460701d40c06040c6800401d443d43c042903c84c41291000101d9072040e400a8241d0042119014082050780d04280d0715903a00300c0707140e0f602010901001d011490140c6909216500c185010f0b24481540c0c00034070f14140c2e0584040011031040b800030059840c020300007e40c809001c03800740000c54a040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 288579208 1250 288577958 288577973
    0x70e0a0f0b011701091107020d0627020609011b02151b01090c0b0703050d0c020a0c210b09030d02041d090a030801060302030a0b0415060206130b040f08070b0906150d 73
    0x107014140f00c0321b45940007906c071810300406030b5011035002048040541007d1404400400c81c0070f81814800403400c441c450b15408440c01d074200c15401920700703441c0c03080c01401165680c0030f483c0720f80107001c41c07a585000540c5a0250002680317500c1a843c607a02c00900c648408450140a20890303568144005400050b11020301075003110300718282079403500e070f040c40e040e10079014104007000f165103400d4000981c83d030b001400d00c46c25405451102041a200c5c4040a042070010700c45040d0204802540d0000030009084103a110601c1c0741640e0802c01001c40d1007059034400d5008500180307002c1000e02181e1f01080b451504581c4a5000700305016082e9070251000105101d140181a0301200140109409400c0100d061100500400482501d040c003055500154010080140310780320000301c0b08480440c05141c040e8102000c140c5540d51681d42c0c00d032030f150f1001c08660820080c022107000900c4a00614040c082401c064401e900e00600581d418061800c0c0c1c0c031707110303108900c400e40116084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 288580458 1250 288579208 288579211
    0x40203120c15040212100603020f0604061709071502160801020a140d0b18071206060e04020c011b0504090e062e0b2b0203010f050d05070e0a0f0b0117 66
    0x10080714803280e0fa86000154042e0703000220b411141c044d030401c103804070300103510100c162407003141c1d20f155104405051007030600550040c440410b11511446102c0901c0d0031280d0340c040400e20131200d481e81c941d084110780e070b9060a10440941d008000214000901450860190041000841c14951422801880c1602401c110300ca40000050040316040780358200941121010703105d04610b00c00008090b0303020001b01c460381c00292000140d00010085070040c20203c0309655640703500650000100802948100980c8805659903108240c04542d04000c40008000d15140e071a200e03450080300600744c130034a0049201c903400c201c3c01c0021030480800c100780b100050000c003140014848804020307828580c0c00100c100f440206001180c0041d8004031340190318941c8001066400000c0400243c4c0070a008200040200000500c22800c00c9a004101940540d0440e014255241541d040c142c0056036a142c0c0d007a01e492101390300305901d01441031468400c2c41e000c048190701c21940700c02900e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 288581708 1250 288580458 288580483
    0x1031b0f060509011b0b280c0e01020f0c10050f070605010f030c09020c0601030305030c13170d03110912100501060903060b0607030903080307030f050c0d060b04081506011e0305040203120c 83
    0xa4606a200074056a070050487c00910001c040141009254019040d1a039072645240140703c3c03070b411136081e04400718003041c00020103041490a00034101066030f143e00042130306055070343c0074426040400c44a0141038000c001000c04054201d0035400d0100c208000c1e034120074081070041110840c0c02d14001200307811280c00d8078103241c40351079074400d102c0d443c81a1860440e400509140c0455071a800c40c0280c00d0b03204404040312411195640190142c4503008000d400d48501803000000e6800d0105150700c0300d810480540c1c1340c440c5070344240c908691085c0c1020700015112102802000303042d104c1c601004200b00e842c9418608907560062820300d103400000d000101c007202240b00b46000b0b4208012504d2001818401460080644240740d0040c060004c05281000b0002600300303c04812103007030310050342c040c24014006162600c0e50701e030058812410015120302c40341d81d03543c03101d0700315a048906980114940c2028010180707485000721313242542e00402c00120071650340002d41d6440404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 288582958 1250 288581708 288581731
    0x5010f02030f1603030603020d060b0a09140c0c0c030f0a15020f03130302030c2a01030507050f091819050726040206070605010b04090e060f01031b0f060509011b0b 72
    0xe03c0c2e2800314060141c0f940b00a41007442c424503e01004002e4200e2100c1a0051313445130b00d2641d0304c540c0303841900d82d07461100580342f20042c0452150b00407400140402c440890440d580e0420250100c0d1900890038102c40040d0403d840c402c08020115a80f602c80c220361980950a01c8203460036a01e081c03201138000649501109004404c040c000d0080d118003070864815111901c0d00340641c145e07170100315118281d000c0410058691158003074802c240c0503441c11345c2d0301404c0040094050300c8540c001c00c4100d9102c07002da0501040c407840301044502c2407074229140741441c1c52a42c0c060064a102074550b0b018441e284840c80100d80c0e51021800a038241e290030741c6541d440d980081800c901c20035002034801400e1100100f2001c021000500448100180800451840c000066250071040e80c0501d03400307030302c00c004002007035441120590300030100c0604003d0680c2c0b40032000e10710f03a141d8084400314401280194196811520380110307207100c000c9840318442c3d26641c0c0c100810004017524002c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 288584208 1250 288582958 288582997
    0x1002030309100615200105091e0105040c121b171501033203130305070801050402150702061215012006270304080a0b0a0e0601030210171005010f02030f 67
    0x10041300034400b486174103007802007000d0700b000c6c0c00303c548039507000103821600c050f43c141040c0e0b100d405201e0540f05e00d80026645155608003541d0980c0402100001c0c0e644000c4200070542150890031007d004200c0712001c0e20707042c0110f41485090403d40384600c40c0f01c1044a0041010030b4010581c6e42611200c10303000e0060362240105501e01200046034000755210100c0d1580440803030380c59040603031303004c3c1c0102d80b030b2141d4030040e103426148111002500b1400340302c0d00e102d2000410000c2c00071540300030314103400c00c00c140c0d0301a4500d00089507400f5042c01034015145007540c0000324943c220750030400304540641f03210581b07580c8040190070416403d00d4110f8181140c060400b0040d0781400980c01ea0b699107580c0e400e0103540321891a01610b420120f130340800c01c1c001440c401c080d078540030240545150307840c54080100f0f034520005c00201744503000500d040d0f080c1008041511642c126420000d0b000d04180004001c881c01c8039114043d07600400450700f0f000030300d409454140042c0d60048010303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 288585458 1250 288584208 288584237
    0x315010e0301200c0a0c0b030708010e0c09010c030c060504061a060f1c0908030a09060c0905030c1203130e100e0c040909152901030b180a0b1002030309100615 70
    0xe0100881707000e8030b0050560001f0450185407001103005091555a0030943e0762900d8462020000a544188940f1410400ba00c03065024441d904105030003810402503006164481c1000c1e928200c9040320780960f03840c80041d032a000d43e149400c1e100c00943e40c0034101324070101c05411521802d003049081300f8844c0f92100d101c81c800d4004698155000c4d4082d40c5904100e04414080c1460800c201d880c3c90800754030199036803040c1d50350b2007100c0c3c0040040c0048880001071102a10000301c6907007039400200844c041c800f98900e03284000b014548980002498040d0820601345410741140c00344040c40e4092100c803640c00000d0b00c0540300501e1002a1500d160302d880600d0001010480070b0303075402c0000442000e0411616080030f02d001640001d80c440740b0a0046044600e83c6001c00e0340101c14030348a900083d841814550b0080c2009000103c082d001c0d030000d03000c40300340c603168030069000100b08214480700b4803002c120034480030400d100d110706010883c164400f0701c02c1c03100204981480a9420f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 288586708 1250 288585458 288585463
    0x30614030706180909120906020a020901030210020c0604060f080603060f040b0c19030608010e0f0303160201021e031f03020a06050a030209100905010908060f010603110c030315010e0301200c 84
    0x18502c600c001c120f80a1740d440e00411040c8155000008107404810004501c0e0001c0740d1084000d030700400d02040c583c215800c10060400c4000340008510440d40340d5030260b2034110040000c0c1c900c80e00c0b0307210070a00840006141400003001640250802418003045e440ea0707001183d0450f9016491441ea9922101042030f03900070107446550214942c4c04044c080d5425a01038015650118000d12040340c94481166595207890030039801e6520400001e5005648200e0700c072100101f40c03002600e0b10782c0345c0b1002403101e049003020b11180180001130000d180d103503001104c2c0c00300c03115071100700d940e1858001a904071540d04c604400e00200042c1c1d10704039031099048626030f02006203285410004200020709040c410b02803240421580b01010800d14800641180308940c0301c941c4c566107a00740b08044000e08520405400c1c0c030f079070600c20455146020304c007035840743da984422000d6814046000409010714440309a009900d0041d50b40042c814500c81b003082c1c08004072000ea6030f243c000f03401d01d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 288587958 1250 288586708 288586757
    0xf020d06020a0801050a060206071d040e0a140705010207030317060a0302121605120712050c060c030a0201050c09030a020415181b05032509180c030614030706 70
    0x30689480018400d858035080051281644c50580d0100901b0340c66440a981d0382c0c4042d29403002040f0001031261008a1103444080380f82c0c00900040b500c154218846c500d01660340744200c0b000924040144801241003080c20024102440103001891840d00d000d02658240203420884154190000b1001d807540c007429030007558041d0000305802070b0808025229000035050380d10b50b6135480c0e0005000e2401400c2440712102907000740180e41e1900c074480c0b24490702c1d41012203050044004000c0d407036449401405c210780c41d440180d41e98842c4040d0081c210380c002000240c0c001010312014080d51000a5204d1613203a042e940003038203140d0205001c0303031003005500a40c02903158050f0f507003005626400c010341140d48031040d0044207104503015107041c00112148541c403030800040c084000b445040c1e01001081c3c40c186034881e95100d108a450008803100d040e64100d4032549070082e41503141c86107200500080d80007a502c082c2400001e61501d0117441020b0400921001d10025140341a4004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 288589208 1250 288587958 288587963
    0x1150c06110d020c01060503030906090402030a0605030f0615010804081206030a12052101031e060b040c0c1b14210105070327020105120c070606141512040f020d 71
    0x81d0b0b201e0346000c100d100079504c8860f039100b8550808a000800d414008181e0b80080c80040c45981062000300910000750001800400c12680306d090014440c0c03400d00c1080503d0742e9040c040c106501d8400c00e140c1c101d8070707480402c0381007005003420040480c282c4810b4480250789100c00302401d0715000f00007446c20741846c2d0050891000d81c103c80d011107030010014000c900000715a0004040c0d80034840c903100c0006d00c4040d050584011505800400d0f50707421300c0f60740f4424100050408401030204049564026000c804251845010800d001400761303010061201c08085880103401c0141c40c0a0500b0981c240602402502c0311181e036810a41548491b003181e0f80c0001c02240c0b80c41400180586403c10503100c45451040c0c98811040118010030021a0107840b0603140054121101c24500c0c00105001c400e5030080c4186800680c1500806000f8507540080c24020342041d401c200e5440c10300390540c0d069030400c020b508021000d18000690040e0072902e20031081c111070021585648a00100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 288590458 1250 288589208 288589241
    0x509030a140717060c070b1902030901020403020f030105191a03060c0a23070308131a0403111b06070303020f0313050c1c02040b04060f06030e0d020601150c06 70
    0x6075445203000040b94021606a04543c0d0f00314034049000a8543c0f009583c41000c0304401c00010700400e00320a83d4a030082c81e010210340446030080004412604256443c0d1031a0f50001010019480c01203602100000c1c2200200058248040c003803103044681100c50140640718001e1000f1225584d40d00302600070003030300750341c9140380c5030054440c0d80d0300010700a004145c0494022641d50401c100704407031110350702e070814545030071030710b050710b01307820040041c407192407907500d0000081d25080259030140b06094030781d20281807030715000d441c0508807042170811740e00c4082549044e14101440c8154150150380503607546146050480c060f110b00d04401c05007090020620100c040941e800ca860240284140d60041d481c801c100a108501103041380c0340d10032502c28130809468030f0361120300880340003030000841a40c2c0c0d080159103201198800c0000c66680c0602480700300c0300b8001011202042e1001d0451507050030120000440c2e012110380400281080c00c004100d542e502444103d00c0300e000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 288591708 1250 288590458 288590483
    0x15040b060a0305011505070c0b0309160b0a03050114030304060c061401121202010213211e061d060708040303090c0e0603010f0b090a02070206072909060105010503070509030a 77
    0x40142c0640420700c10f800340501200c02c801562031081003503480c2c6507480196540d0340381c81c00c5040c050075080030300404100d000f01002e004d0340703281c2e6400001c000d1103502d10032511220846006030840714140e000d80c0302d00e040d03821441000d41d400300071581510700c10305045035140703828140f0100030018198202c0203041d003000041120000c008103807402c288a80242034500301910000c03402c1c0d00512100c003140383d010401c103002901c12005403112520121040b00401402c540701c2c2e04d15105850f440c1d1303200c126040c403e07c043c4100f502800c2001e01070161181c00030002000c041c0c0d80c504008241000b00154000410201440380d0000d0160681140c032000080e502d9426107081d040c1e0603a0514865803030000280c1152125004171810124020f0100c40355945a80b4603402030b602c03458013241d100c4400c008041c0028107401d56100120107070011121881d0400b288845d02c020082c28506856100c00c004200a82c0c0c40802c41e81d0002107071601c6900d4a01c480c000c00d01e002010b13800184407000700329 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 288592958 1250 288591708 288591727
    0xa030609060e270a020f1c030809011802060904110f0f030105040e06091c2102041e12060209040207061a011b02030a06150f0f0602070501030b010815040b06 69
    0xd03200b4020845030307204016140d0039001c000322907100f09007104142d40100103a000940340130341d545460048081c0ca02d0a405000c06900c2a82c061130150460100e0740000512550540074454403031501c54964000741d079403e09400041740f034025614418440c1e5201d0528102000c0c01e4020b48020b40d0071284625118030154401e005990002d01401c3d0189140c08440d40c2100b0001074258003078030540c03000e422800b886000c0f14102941004404050144c03000e44000242e07211080d8041d0041c01c4400161a6800d281c01c44401404280c841650100400e00034000c002501c094000d00b40d91000c0010382d18644600420b010740180c40000e8440c3d8508480000060390000c110150700000741c3c1c8000e0b0640506003c1749401c10a05006500f6030f201001d06000150305520242c0d14402900758203460b01c0d542c1404031510401d42d00f10401c03503000c10004101c5140c041004601402c001d00f800c3c060b041c0709000003440014004c100c0034202e2205030841c0c0342900c0316848034100301d501a21181e0350710301c8032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 288594208 1250 288592958 288592979
    0x160503040803120c03010312030b030c060a03060e0a061503180f03030504030905150403020405090307060e0709060e010501081302040603120903020909061e090c06030709080c010e06040b0a03060906 87
    0x4031041506083c1840004920340a1102100e0690354040c0301d200c0b0042e110744040300145800c40c0580e400d0700c161030560202e81d5500d4013800b10120a86d41c04074055061440700c0700ca03200003904400c669400c000003400b65410000a03810190464540081c00c001c581c1c681102d50070640c1d20103888003100703080b15800d040c0e00d900040c0c0700d01d010781c0b0f90340034990f55036041c0700c0718030102808441000c200303100c04d100515258000f42d40084008040ba401e00c410340c0c548104072040d01090150755840201d003000b004c3c03240c0c0034601c014200072008480c81e61402001808048009061100e84c2d01202c460b9811580c581e4041c901550f04030000c1180c7c00329908004d4005162400164400c00e07080000403a030810000e44a0310542a4403450860329240002e00500c14801400006490052800c4183d950b01c0c2e6101540c4242455a60350802900c1c0c203001c6400c081e840150a41040f8492655807110b496070030442e005c66001ca4200340c0d0780e03810914103c00804058114405160070030100081c40c00c1103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 288595458 1250 288594208 288594217
    0xc1a1608280813020a1809052401051012050c1b011506110a1403090918060c0a030b0d05240708010b07060e01140f060307030f08160503040803 63
    0x1e0090380000d855040100d454958001046440042c030380310001920071054040d00c0e02c10610103004e400340e0380d8654070720981006e0b0102000e50525038505d14502480020800090300380344110000c1d15400c1302c64000320710f4000500406000b5110140c43c1403200d4451103800d070460100600401c041d08081420710496442800f81a0103107101d1751071115500018452818115400300030f801c4154070307010707003520359444000c44e161503800343d41900070101d0400c1e0140c6070410f5400c00607564800380501088443c060141044442c4010701072203604035103000444a800814a07400e56131602440c0104402501e22041c0031600900c21041e0a001c100000909021000030000e00b03055034182446c2c6030800d05000c503500741c0005c802c4c8004019a60503100201500c6015140c086403e0140b0101142503412803110118003640300307010060310001c1190980d40011084015042480c90741d240d4003984040c040c000b030900c01000440700c00110b000d00a00c0841c96100055130788a65481d040c0c181ca9812 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 288596708 1250 288595458 288595477
    0xc0c01050709031b0b19050906040906061e0206060d021c0f0506010b09090103060e03040306061e0501090b0909220b010e07030606120207150f0209030c06070c1a1608 73
    0x10301005100322101480b0104c0181d5510315a03d5090881d10208010052034183e81d445c14020f0401401c2c00d00d4540030024005407004d0f031800310f0721a10b840002019401d1407400d040c1e85040010540d8074140d80410550381001003129014124401c90000072000e110360210718010101c400900c400700284c20075599503240c0502c1c10303502c1e141e0340c452000c030280c1300d00c038000c540c4142000018400900150300030441c50300603030100e908140c1c581d0346000855070300c2d40000745101c1081d0741c6110b0307614840810700041c2400b840c00038562407810b03440004134050695050703c5a104a80040d0300d88007030045c1e02400040058101482c2c0d41541000501c00000b030185590080341c11000802e901c0c068058135080350301d07681e129183e01c8210350403203000b90000c40d000c0b11946070031036201140d6140c2340a19408001403143c0103a4520234603041510f03102d84c1080389801110244040c402044022400008131041079442002d2082c2031030911003144141e184003e400c1c0c14901f00744003409289800350040e0345 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288597958 1250 288596708 288596723
    0xa0f1806120b09010806071b0c0b0301050f0f06090112020c0111131211122b110a08030408070807050a08090a0501022b020a0c030b04111203040504050c0c0105070903 73
    0x12020080c8943c0b80b01c02d002d0701030f50fa84107401203a04140f19a100e200801c000b640300c180880446da032190000140390f400616021004001400145000c052100c10904101ca11018040984010580758001d401600d81840158803104500082c1c0e90111815030000900030400304c040903c28103480d0b0010010280e01024801021403c00054030003510540e800c100b010b202c82d0051310800c04240400c0c091441c2e5801803440c44008208045542c050b503500714a040d2003004412540109913507000006a031517503018541c0e0401041407602101c0d00107030800d60312030752800d090601c2200c40c45070800080162256510380014496920045e00401004031004c005c40d07076840e0012079444149601c0c01141c0c49085d40c0400344011820710340c82800302240141e5024601a403038400310204e131640b044d142c51403200200030402c5042c14401101070300840c0c00700a82c0708032001041d620b000714059140100d56550105003070060b0b100548800e00c1078a00280310900d40740340000c0100900d48422550780 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 288599208 1250 288597958 288597971
    0x11103074206361e0e0d0f09050904060b03032104021c020f040c0e030d050d050916150c0c0306020912010b0117180303071d0d080a0f180612 62
    0x601542d0700c005410304002106240d803081e4210301c3c1c0010304051036008940040768180120b007800901946404c03114810103040d1510401201515100c13480c94036804101c01c00d00f050010350340780d03d1500c0d0000d41142c0c00040c00490b03400030174514400c2803040703503080f41003825080031107070360b41042482640300341c403040c01c5440607040c25800300d144220001c1d8400003400340c0c440981010307845a4502125403810303510018000003c82d080401c01803a40d8009040000e42281e5114280105904030200c0001441803100c0482440c0c40a00180207428844039850804500d091103000c3c02d901d01d54109540d01900c40d6a4a0120001d600c0240b04600030f0880030504480172406200c0c5440034801a1134a240108101c00b000d0384828000388018145030180c1018a188581000075520411031911041d110340d0707011402c44840b1501c503d540d403003060101c22820014007440d0584400290307500705250a01000c00f01601c0c080e103850000f101d50950f05c1c40010340b030f6070305c2549424684041034081021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 288600458 1250 288599208 288599249
    0x806011704030f0e01091d270f07090203060109052718070e010b04030305130f0b0d05090601060e040c030207061a121c080601050d1b090509160509061b010b011103074206 75
    0x73303804100da1180c045028001d00700140d051140030401c03132420040502d8101100c040c401070018500340d940c0340540034501e1180310101810040740c0043c4c414103140c41d9487d0301d45480304103244035a0100034101301002c40c0d000514124950041c1c00350004081d542c1041d501d94507031503041c0c0c1040340c403020f205081c140446c01c0620f011070054184c5103180c0d51001c00540c02c90501024040303111040303040541c03c00584022500c07901c110000c040004840501130381c8582c00b0064001c0403244442c500d41c00c0580c4940d541c0c0982c41505460305468205031084e07940d10401078525003e020108040b241c2807246403821202c4810034009400150703240d40e85025162400d01140640458a103640c442004211b07800850050010f0802ca0900501d900d1511032040321054100550b5200c101060303444800c03041c159a04005e02110b0b4030403030001107041024503216050010346a001d040030110004990110340c074a0646d0b8150781d552800c040d188621a10142103004082c07900c0b030000258070003492100f1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 288601708 1250 288600458 288600461
    0x2203030807030c0e03120a0c051e070503120d09020a030209040c151d060d2d050601050307050d0507022d010c03060f03030806011704030f0e01091d270f0709 69
    0x204c03080040c0c001c03c204210003441c019181d00030b62000c002d01502c200c10f400082e004100d21305c034a043c020742540c001a5807892052410340250031442c866084006544080301d0140b056407c00604007401250504072800482c0016080d604003a41154400b001c0000f8004100540720403682400c000c50340116880d582202c00c2291705142c40000005000ca941643c5802d401804075221125400100c080a00f04010346801c130503c100448a490b200340c140c00000f05100d200c1d4000020308215107149001c80000700941b0806103034550301c0381e031a00822111072003003020710007141d038016030207c441030301d2004c04408480e48401c420184d03082074103a050340c40c864000c1e10200d03a11218020562070950b41c1c2500c0c4504c00905c03107030400014502e0300f2070031a030841840c0c0c001c500a1701d5171004244a407800901041c00101464180885888204080612403441151a90100d0284806601d40c10302c1141e0682c121005030350f10154a42c0120114600420102502c00782c40088804180e80c9810307000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 288602958 1250 288601708 288601727
    0x1e0e06040302010503091207200a050a0902130314010902030c240a020f010603030e0f040e06070c230c010206010812030708090f01110901110307050a082203030807030c 74
    0x98000005000800040d4020000b450700000b002e400d503080700f07445071070032005a042100191984200080461200c500a009401b0040310560305001001c1c01c20380820340502c2d0354403078010110390006a016101e0324842c5d030007014543c4060702c41c000c4a0b40741040d50182a14840c1030303220340a440d8540d8032501d8102c007855801d1414005c120852038803082c440301150080300f141425401009540c4207240c90078448c19000c0c6100c3d072944100704592906100b41105041c0409014910f00f43c14040700c0c080024509500a519141c0f5614010080c903011a034074442800800c6a003c403030800543c15103002c2101205142d083e8200d5101e81e98410304c0030390340d6002d048040745aa400308042020355115010b0b080d40600c4800448080c08440341c80c003401c41d02d0a030740d008940c60021407441160345c1d20114150f85242160003c40c241722141d15030b1500d45824590080403150009800c1582d482002e0070001c400c140c2c840111042c50b901c1c00c02400d640f004a0350607001a15000610300752601552024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 288604208 1250 288602958 288602987
    0xf0501080a030c020a0f0303021b0904021f02031309020a11160909020a0806070e03070b0a080f071e0206061f08150123041502060405060c090a03121e 66
    0x101029030260714161420f080540050340c0007010304038041100e41c000d007600001103100e54000e00000360380b55807540e500201e4503400b0748180902000d010250b074903524001c8462441c3c0d10301408501401000f64518850040f0340c007010200e400c00000c0d005000e0340680680c403015181c1007403581c1401074194031105056003031424504924010300c90104190312610745c8a101408001c0c0a6458608403031410104450280005402060308603603402c00303001080043c901224020704280071900041c0459100400006000e0750031800207120f1840344001522520100c04070002c3c1a100c4030000351250f1040f550341e401007000940c0c0c0941c1c41c0d0403140c206280403260fa100101c5440700c0b400d1458881c10061401d040141c6e03421070300d0340c4c1441d074404008043d90138214640c0c0e8a2401d90305002d00641d0030940c0b030554120344100000705801003101d0b640305407880c0701d190b0754000140016403d4001c681000e1f00742452103440d202030642022421f0031000300e0b98040d050081c00703908111440c0d041e00b40c24 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 288605458 1250 288604208 288604213
    0x606030a0504110904050d030c050a021203090c0411131a0d0b0102010e16050112090809010c050f060c041412030d090f0501090308041205041a0a0e0904080d0f050108 73
    0x4100c804698070090308a0b21448007071000c0001040003601a41d41504c041d21541c0101c0a0401c000d40c0500c00c0300c84030300d0302d420102d00342543c030000a074460f070030a10743c0040c041c0e0010020300f1004007400b00304120200180100947d160000101c451508481000421249550008904403848483c1c00d0100007059040500c1d10512a100c000a03080310368030681075640b2009604e408410600c408280315001507403126250303151000042c100890703441d6160b00d83d460001080080380c4c0000807034943c50800e003021294448a442c000c2e14080501505202e24024401441b50340600c8a0042007112260502075032013541510422603209488510104158410020324040c0c110365000a050540a4844840250395903150b99081d5417a03114114001550202007204028040144a42e01c442c1c1c0d2401900703150619195049a08403172004c2c0030903040c0820068001d070302c074070346a0343d0001d405481596141000d181c0650107070000010100c0480c20200c07a42051a11446158121504c9500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 288606708 1250 288605458 288605461
    0x8010e030a1b140c1032070c0305150a020c0601030b0604020c010e0c0306090601030b01050904080c1b130908160f080c0d020d0e060702010f030b220b010305060603 72
    0x1c00b42d8034401200401803065400034403400210f46804a000502100c400c003801001c2c28a82c20458050709014040081c024504240005099180710500045c0601402240c2d02d20f5a00c00e658000d00031148000d2010b0030300480132042140219602101c1141001040c03080d0700c0d61200c11091740654079074051607600003401000400d40003044241c002c00090001440d00d04000c591b64252418080c28030030130b031f0080f4021176690034100403207940034000402421880d4107554503c40f02090611445100c1d007120b001113002e106100040720403003a8408102e1350390b0a80c40840640b9a075200c550315105614420781d5100025440c0520034999600060395880c0c030710307041c148074100800a102960881686001400002c180303000600c148210217000344569a100103001385484206e454102c20040c100200381c0d103c0d2144410b850040d03509091000c40480351000450003007800c10796003640008031000c10106019032000b800b00392141c2c04003d2001070004030054069803425035030140c000f0b00c100b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 288607958 1250 288606708 288606727
    0x603180b0415150b2106180601051606090b0603060c220305010606050301030615150509120712020405010b0a0912210503090f060103020112020d1808040f08010e03 72
    0x1d1150700d200c515000050b4240340c3c041c1c400c5034160103400a6424480018030301103042e2a4005980001e03281c55108000f0b80b5050b400306821202c034028002c000b01400d00495a1a030080040d6001140c07a017180100780034190814902400000300c050391001d00820229465090104501e8450f990b84607007240781c2810000607901040c6036000c5503060035082d43c00800006d400307015100050190b56500364aa50450520000301c030b10f44e00c1c14985003410030004004401201c60100a01d80c8141085929210660301050f4000d008140f58a0b090040c80c070b0110f02013032207030100b05560340241c0c1d0411160380c95400c0320903503204000f601004909401000c1045001200d001c0b00c0d10391041d0300750018070b015192400c04040c82900c00b10042075000c0f04001900004200c080c0304030040300b004210b154995000600307203550300042211700302d80005804800040301d82023070640a0b810707248d0419500e25824040000d8010b406070803c072140f410f0700041e00000500a103244548090040c1d8a02900f02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 288609208 1250 288607958 288607973
    0x5090607020d0f0c1a060915030705060d0b0307090501090b03032a070b0c07031208070c0b090313120c08070b0a0c06060b0a020106030c0b040308030103110d0b100603180b04 76
    0x450783c0404110822240c0000241c00406100070300304c081c0151103490030310004005044400405840a603048010701440c0c0341e40006403603044820964065668101a040701c00142c12080b50141c0c25109078500001d142d0156404a4121003401000304522208501056101c0c8150384500e0001120044c222940c030a41115910bc507440c1101215101076840d0140803003900320707000301c1e28560020103041040c480c4481580c196030003079140c40742482c03410120140010b110244003070700710b0711010300261011000300304681d442c00d1841424140e4035a2601602100c3d07810381021140950521800504680700240d0142650100c0601e076082030b100c004200c030130f00f0040710103590b09525000006052118200201038842d0b482d1b0001c2a01070842c10b141201042c50381c4810610305041000b00003041c3d0103415a03042d80e40c0300b4161000701c4450f0340081c9080404000c0074102a194038180304103030400d14091402c5070a207803824040705a010b0704202c1c4100d40000042c02c0e20424000240c00a00340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 288610458 1250 288609208 288609227
    0x207051e040f3e0a0f08150307090b1c03080112020d17030f071b02060d110a110d1d01080901150603020c010f050c071202100f0203070305090607020d 66
    0x40c0716000a84a140300b0912840700300c500d515a0100f80665161802c6a4503e840c998180000650091420001c024002c2c403103c0b00304001d030104009a008103000d02c2002001d20340c2c0b0b1900808443c040c0f52100d140b0b01c001c01c141d51100340319162142810382107900404000100c550035456003950790b032904100070018409090100c0c3c1c8050380020410025400941403111401040038130b603160310304107041c44002c0303001400e540c0a004116000d400b5030703c2005082c2d445190b05a0b09991209039840600018010110322035101c0b010201d0600c0001ea40090000c0300740040d00d007100d004800c0c2000980324640600f00750b2152900140c0303a01d00d40e500031004250002d03660000000c10081e45080d00300c2030241034201d440000d800081d130b030342401d20901955001d1546000d0400180c14101e203101500c0c0700703075103005040e044003c640c000c6840c0240b002c00a6401d0408082c0b21a00ca26561000250300460b89400404d141070003007061800d0014201e0305c1410160001c05000d1034440094402c4840d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 288611708 1250 288610458 288610481
    0xf0302070204110405090a090b0c13180b150307050a0509030c0909010f0605041406012106090c03060b0315040e031e03070201050106020307051c0c050a0f02010207051e04 75
    0x1000c2062500507291403241450072100409059180ea0812040044608028001c04200c1e81842d015101285841d50304a4012040603161680c0e4201d80c9194490411664000c24007941e003940d0007489041950000c080d00a030880c0d0003a00060303080301c0718116010988400e0700080062040e40b400d640500c00400ca40c0e40c0042c221030f100124034000503460603085401c60002c1e51280c20040c010040e030300500380500400c40d01070000010020010600400040000c1c0c100032006034007004a9680000400f02c054254000380540380e1210550800340c032223002c5800000b80360400000f141803030740c8190390003400040030340907100e85441c1c100006007002500c0031400f4002088060004c10724101d4020f618101d281010341c892401d0140613003140c00c164000070039500100640c4002540104400c09000c2501d040301c0c0cc0312500500840c1d908025100c02030540c80350085e20401d018044014800783da100740d0888000a80314414488035882441d008040f0801c1c00e000d0100500d4150003480f003020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 288612958 1250 288611708 288611711
    0x100e010b0418021602100e0108180a08090a121208010b0f16021c0b04050f060f0a02030403090b210604020c0c060f120f010f06020c0d1209050a06030c180501020601060f03 75
    0x2000d074000030350401d1b024402c2c5010a225034401134455800c013a0b040e034450008600303001e6403403204588503114515594002c6c0f1074000055040c0032641c03902811030140c1241d2030701c151030700228905143d5039100041440007040c1d400c400080c03014180411507030790303d4000000c00d0800c001c81c1c06071141c1c0e0940f80300c120391100301c0805168051565a890028160250045009a0400b03080040c1841c6107000001390540080080001400c1e500c61074580150b411500181d41e59074904044510701a2a041a50140781c0005c1d46480b280c050f1070150b905110200130b50601d500c0f4082007008a00c9a20740911054009560710b401c03614019020b44164900303d02100d2404146000c5000c100d4400c5559010340d621100040c41000d01642c0340c40e0213000540018200d14281200040ca25094180c008245030511244040703100e00c500c2098004140150400400f9926040d010b809040409110030028103007c800c0d84a0341103480c0800100d44060300a0036503a42003041c01c031102c1100309c82c4a070a06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 288614208 1250 288612958 288612997
    0xc1d09240d170703030e0106050d0f1403070b0f071106060103021305030a0305070b0703060f03110d140106060e012c030a120201150504091106030603011103100e010b041802 76
    0x150661200d09542d00d0810a50343d580d21031860003408680f910090a03417142c2c501501401581c0301c100c104840700344c1044034410001d20302c0c60104403840d0191400001ca00002c191041001008141035020302d03070000c030010b010b98984c5412036585a0b40302015821340d0040000c00c451b940254003d1019045017603c1844158440000c00d00d060b081d040d0031000210009170110501002d00a4a40c0051651a0a005c502c0c58a07020920910080c04043c0241d4502080c00c1310326a02c0b0072000b4055030741704c08245048030340d03251001e0007040c00c4d20907200441c807109000705d820340c0710700c41010074513101188c1c4006404040c07034840040c24a05001030703098850204c04601082c0c400e035600300340384626030001c10081406c40c4c4401c2160701a50110780100d0070003103c01c0004103001440d400980c0e06403600ca84aa41d4003001a002d0a003224108401002c00010701c004095072101000c01e4a030f8104030074880e40da8505c0c0048444c455445090000b1120011401612010381c00a09a40c000c042008105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 288615458 1250 288614208 288614213
    0x6190b090d05061305120a020726060415051308030a0c23041503020301080a030809030412050109022106070f1e03020a11120a0c020406090c1d09240d 66
    0x2c03c081a95103446101000700c15008005003044600e03e4025141c13240c90400380031001c06582c680ba940206c0324105c0c0c0c10680b642c5030801002c4440300c26010310301111168240380c03c00c40c1c0007114009441040390b0034080080c0014540200c0610a0340e03204c02060b01c1c2d0303a12150060001e1240000c41401c1000348d40818103082c0404800400c1c0c012425001d60750b503072070814001600c1c02c000200e201818010300042040d03160106844100035018203200c107480c0c1c1d525801c0390940c03055800901c124024801c4031424841d056002c1e0000520130b4490382c41d20b1101400354034502080380c00c11000c40e803208001440c524815215592884442d003041c0413035003441d81a0903400e01e0148a02c40010744c0c00b240d13805043e13a104854044543c030301e10141190a0040c0c0d4040c1c1280720b139210440903c440d6582200c00c42d112540b094008280c4148104a0ba90344400d0042489880414900000d001c1500c0b406031440c100602d42e0080010180384c1c0d41140e140b030054080b291607501074640c44020810240b01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 288616708 1250 288615458 288615463
    0xd06020a110105010e010b03060d050708010608030406020f0c0a0308160f11040b15030c0a11030408060712020405031f020702040903110709060e06010309020a0b04090506010806190b090d05 83
    0x2505805445100300444410070007400c44070140e00c6401001940ba0040001c036200303c4c100c82e0821000d07503508400c150b107400d100b858101540e001c81c030f0302d61030b03d00000f8001501002030705c260f170500e030700740c03030207891584a51543c40e80450011580848025070400014100070300510b591081658400c04a02943c2c40300c9c9080f00800c1c05c180d403082096850a1b84070b16092148080b1044c0895841102c022017003080000d40c04001c0021088200c00910082418066a082c8081d14170100860740c0e580d0310b550345951540d5040e00e40c140400c01002d001a0b20540358001c0e10f0a540c0013400400d9a1265107428004902901406980182e82000b8010241e100c0b40038494226000b0b0319000250090101c80f649044900c5c0c0c440d00040346484020300c1088208c0c00440e0308600c003403a0100d40c09400d40005040030445511203503121000050000c1d030394005030811482441e0980701c40c0c5541c1c2e640d0080c0f01c00c2085400c0f001003a02d00109044c045103540001814800101034542041c1d00700a82e112032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 288617958 1250 288616708 288616717
    0x80c0a051216061d060304030806090a330503072108040513050402120a03020303040b041a1e0604090f021504121a0a090c0e06031006090506010f0206010f03060207020d0602 76
    0x6080c4040707031090181ca8501303038a40d01009031a90307891807078551001861110b000c1d00d020300c2001e0000200307011010a4210404041041d0001d903020000d006960047c40120b20034044a01d0070408006001c3c900840c85804883c034142c803505000c1c1c01000f02151400e0002412241c50341c0601002c540d98803503100d0543c40844010001801d030401f40108480c0d205a41e041700c01c0760744042407030400031303502100b601c0e00301e6400840b07a540c3d62514a05410080c6520070701842c03103c0c6040c00c1080c1040302c2c20404001446080101d01d854490070103010a8521504019010700121080d9000500746042c0d0300e035850824101050038140c5601c2a084c824561190030340d0b8503000c200d00075042030986103059030046c000000410491440f42c0c3c90900c81281403141c1d0182e40303032140001e0220344080c0880d0034003c02d001c0e010809140c84503643d400070602034035003c4c001810100c980c00790a0002580b207041e82c9840414601035407659686201035804030b00102d030048402605c880c0042c10b20700150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 288619208 1250 288617958 288617969
    0x6090602120a15050603130213090204020a0203070b07020303070903030f0201060512031206061207080c0c240610080a020d0905060a051e0403080c0708070f110307080c0a051216 78
    0x220f51802a41d0034140344403502c2c0c022920501c1c00308180100b00d035801840d084d90f585e055174500c0c445078902c48894020400030102940040c000244da0850725400320081038000d216500107040da48440398101c8e40da01040300c00001142e24a481172010a01401002c01009081c0c0700106615445074045040b24081544052680c1d10200f0194210f95250748915032240065a4035410440240802030a800c4090410024001614013081c4105031500403a500181024220341c240b40d510000e41e24011240488401603002d04008a43c580c500340002c40103440e40c1e40e03540c903441d031a84003e130002544001c85208880390f030342c40c0d031030300081060000c90700c0760f4080d040002e060b142c400d000380414100e440203003000c4040d5034100800283c00c000c2c2c04c0c1e0060f84100034583c445801e17180c1110710b0310924801404194400032894104201e070b00601c0c3e1040d03819002d481420b6501c2000c940d07150701e907001c06c0346d100c80e03210b4043c41a4284580c8060092100008584803910700142000c00f003030710398021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 288620458 1250 288619208 288619211
    0xe04150305010617060c040618170a2009011a040806100905010f030507270e010f0e030403020d0209070309080d0f0c21050c19020606040e011806090602120a 69
    0x104200a82045040b451310428001303800c551034940012406442a4040d80c418010160305800440c92001101c2c400b51203c0d003140c0d54041203003900103507954900d88040319501c111000a544c0d00080010705501c008001e02401d240b642010005074540138140110b49070001d0030300c800a08004108a203038002c02010a100480c0b80c18602d800c005e4990507000b00c800b0700c40c071840400000d0800281c030004c8034840000c1c0d056001410440365203030082c030072801c0051814070312200c600104c10b500000811107449020409a110a1346c0c00e520b0340618440a54014480807002c40542072110b81141d00801c10700c0c0004180381d00e6640d070546a0841c1c80e581c540036070758001a140483c032901c0f030050300503d00c0c10143c8036803288006034a144d0740411466140d96440e1008681c0c1d0740c0100e025070b03844921040d94011a1120740c0030080d41d8a0040326824815403d05d810032090b42c6043c82001d8030780c1c5c01c41903600b40703404554884ac0007401d440e03201215443c0d400c104500d02c0d4402002818041c42c59a40d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 288621708 1250 288620458 288620471
    0x307030c0209060108040510020a02011e0b1009080a06050604090b0f07020c150f0a020106030203011e1d0a200a0f030201020f0607020c0d060207020405180712120e0415030501 77
    0x14802d0764040180300d507042c00030960520003c1400011010310600000001503070760419844100d01400304003003012048200c01e8540d07005800d16401c039000700324042e0f5a00d003080c07920f2242201e200c0e00764410200c030f98000446940100b25903800290f17002c2005403000c141001c481c0d85440e007080d4200c805182549581081c400c6481e41800004400311003200d241370b80030403c49418a540c480c03c0d010358010100021a11030185c000c0d040742c0b0040d50010700801052012000701c00744070783c41d076150481e813900d080c0c64240e040c1e80e100c603030f02000c0804900516140c00f06944070002c551030704041101204250000010355030364080207002a0104c600311045181c0b8500c006440c0648800462000740c12813403c00c00b03040e9000880f40307103200d0100ca030306d0340029582c14000000e119490019402c00d0070003040003005402c149082525803c0a8112031110b50744031010109941d20304402015040b0b00c2134807410541c801c010b6076594038002440001c40e04003e030a001502c00e1107600440e0f141c0d44400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 288622958 1250 288621708 288621713
    0x1e0310030b0109050403051801020f0109050318010908101d0111070303050f071e0507051501030201020705030f031204020f060a03090311010605210c09190506040b010e0d140307030c 80
    0x49440c0c2c0103002d03c1c1420b00c158202954054414042c107207100385c3c034424207842100c541c0c1c400c0180b100010b407114000c201003252401c085480794840341d01c0c1c0240d10a000c1074002c003548034204d05000c4541d04000350200c403e0000c0d48001901c4050311071170f4540d06480342824050b60030300c0341d00c1030203480c0ca01880e6550f20514014058400c02082142c0050850302040410713a0007100000c0b015921480c070480e00031003d141a6050f003c2d511014043e403142c0d110421a01565110030340c1668001d800b100c080c00d0b030701e004140e030350862039812002d550030a0221031030700701165101d070340c225100801c170044441001012840c0c41e0414580741300083c1c0c49880715800d058201100d070b0180348404000780200c5003440d000c60200e0522544603090025400d8120a441c1c0003400020a299001041850319007003d402d031107821558010150541454840406d1852400b031142c0089141d040e1a09402c50b1100010480e848103140030a65012418602d0002c03000818801042e003248240c44e140360b41016030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 288624208 1250 288622958 288622973
    0x207090b010e090402120f010216020a05090c120421120b0604051810050301091a070504050108070c0203120409270203030327192f01051e031003 64
    0x2001141480041d1015804a8483c5a01076a00a030180c1b08050100368041800d80341403500e0b01201010b51002c039142c041d0b0001c44501e80d414038002c0721400c55440e283c604000b01c1d01c81c10354100c6c3d2003440410111080c01003d00c0150351082c020b070301c2c400d04946d52031a01078840e80704198141c00142054061f94000140d071158108200090710701c203050a041030041121500943c0c00c4040b6010410001440b01020388510009054090020b0012265a2808090b40504038400094601c2e142c3c0016400710b02c280c0c2078608a136016900c10245031a01c1d0425640445410b100b80d0b00360040c0d800440c0c0c000302c000010402003511032070004044440c981c7d40011805481600e400b140178114200740541d50020903250040794079040e011481c0d42031540c1c440031148034640c25406000300c550101d420a501d83e40800a14000c04949c1c141c1c0c0c005002000007100316008441c01000700c1186001d0551045000d42202203194140c04c1d40720110003074684031504101d40401200d1110b00b001d00800008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 288625458 1250 288624208 288624221
    0x30a0809071d06030f1506060904061509081207123e011a030a080306030a0f05011d1603080d060503010e01060609050604031a04020619020c040e0304180b03010902060a020709 77
    0x25005d0300740321b1400194007460400c081c147c14400c00380441e00100542d5079a00203c01050f010600c00541809079001a1000905204840c17080c090408401000c0010030300301c820280e072022040324411a081030a032140c40b010344c800e080c485d9a850103441c0510341c0c481d2100d540c41c500c808610b02902d0705075409007903841c202e18400d081c190300b140322505601e0020380d4003810b5134085c40490f10b81c0c1d101c6011918050348000301500740440c01f007070b02e0706100065010101c0c0d0344483c800400607201140021360790b24502c50180318030180d546410404a03d020010b0042c07800940004109159101e000a003954002d00040342d09954800c0c0070000d1a400c0b501c9000140001e40da1541800e2454850101100300000f5036800d4200c407600107002c41d03940c03008980d0441c680c0b181c0030410b1150b1100007582c402c8030303450481c010351910359624540c4200206403404c4502c4401c1100b03034105d5000842014010009a06030507648034001c0780d005076591070250132280a550b00811106150032440e000303480301e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 288626708 1250 288625458 288625483
    0xb031b1009030c09090305091806010909050c1b161e0602070f06030b03070b030c07050f0316110301111204060606030603020607080304050703080301080f060108030c030a0809071d0603 81
    0x4810780704000203295140382d581102c1c1c1d1074400244401c41c0f81010b45444c810380401c0b940c0500c8001e80d682da0042641c45a0b4040c61003a65210840b980b101107540c2151f005581860091038144200c80608415000340340d00e11695005444440c190f00142c41c030600403603004641d02000d0754102080c1d040340c1070b218100070320041c80204603603442d06144400c040f21070301510301010b4a034942a8a103880c10021718001b00504040103680740342c59129543c1e02d07000b801c000c485500584094030300440c000410380748613184072086011040c48581d184040a070340445803d41554840442100035019000940721509001e59003203040d16151504408840064000c44241460440b090000d0381340c0f4001e44010395403203c54103a4949850405510388191640010503c950001c00890115004142c1c00180000304d411a10181d0301c4d1030740e950712070041c1031258038541e00512000a02d00d10a003c455081076892041d1a2001e07150311006060010150010300354400140c24000941400c01c40d101c500d80e03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 288627958 1250 288626708 288626717
    0x10c02071d1005060d0908040603020a0f2c030f010507170f2715151311030a1509020708040f080a020d080913020d0f050c0708070204050a0b031b10 65
    0x41c028540b807000300b01c9802024015000802c1e03c0b40020072640c008034019401c5a20035444036a0b5401c003c01a40c060201c6030005400301c050010384c6070044c9100032408070f002481e24401c8803285048074004008002160307251080070010220201c00b80300311402124699204510010010ba18002d10980a007002c40e246140d0700422900c190320050407440303880c041035207070000e02c070410403240303440fa0158161503009000700502000c4166440a030b00025003e640040221001d602000110b41380021040c5a0010400004030001a90b92007021041801036000081c42c2c0c440c02e200b002c0780c125100441b901a4005418052307a640c001141e40104002c1e002008514055804a0b640d09514440281200004201c0403c1542c0c0c10645107414a010f94085403203a242c192400c01030710781000d04015062511000c915000a070f982100c0300c0580001402d89881030a03820711004040061180000c580c1c0c0c2c44103201d084d90113001c605001d80341d034002c10985030800c01c100001443c0d4040d0304410310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 288629208 1250 288627958 288627961
    0x20a0f091104061707050c160504050903090a0915081009020f1210050a0b06070302031b03090a030f0f0204020301030b0901060e070f110703050f03181e04020912010c02071d 76
    0x46034080403420804c030404075040f416840b52602516240111044c00c04580100b40b031440c0c10503c4084c5e0f010458030704a80c10300107170300c448034029124070480388210381101142e04107000510181c0c00c0710f24000c0b11865441d510558801125091078811080341c40342649464445056240004099101800840d5107100c0140031503611555015035000c0f4040c0b440e2148001081d04400794060004000d01030a25907230303070050385402512a07100380141e060b1184003406001c0d05110010540381e00c85005407103042007604586896201510100c1c084440c4500300200400507210390002e98021849401e640c02182000c0c00da460a4402c44d80003c6410f10400041043d0203500034050882d0041c9820580c0e650700ca031074821801c0600301d40015105208545288803072103800001402c0514030b007081d260210380f41c10100110290642107052000940c50f60459031403074145d0041685c1c51004000311070038070700a4141400d6960300c03400400035810049081260091100416482c0000f60780b40042e10f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 288630458 1250 288629208 288629219
    0x20601050a14040605090a0905070905010e010b03040606050303180f01030b1e01020a02120313080703080a030c0302070515160503060a0603110d1b0f031a1903020a0f091104 76
    0x800746901c42c9152030415008540c0361602c9039848480070b0722014000759800d2030000b03034280181ca00c51100311840d01ca021000038404000c0d2103000c0c18ac903a001c1002060364030b0403551200c140c002a00c15201d481e5200c0b80055030307950400c01007218422201400b040141468108130f078a56209a4803418941032240c403011035070354000040050340c030b090010100d0004c3e45004030300d42100e19500035000300d40380202c4440d10b03a0020107044006c80603408415800d49441c10903403140300a12000f04429400c1c041110f845000390003140c0a11180d240050400301a07484540c0390110801256154190071028414100ea0702d1900c800f400c4090304107a8550b003000c50116101d07460500c03800040558650505c50403110103406c8801c2c10454540500001904501c40c000c01141040000042078124950351b0641d0302a0095290b08800c0382150380906100d10b080c440701800042c1c03425071701402d1031001b000580c1c41040c2e110190042040200b15a410030703001004a5100e140c1c2c2c228540b07401e2004110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 288631708 1250 288630458 288630469
    0x17070c03140c0105040c08010b18220209070c031d0d02040f2406020601140105071101120e0102091306030506011406040504050108010c02100b15160c06050309010b0102060105 77
    0x1541850020080ea1801c80c1800142c0aa5000e650455007020240024005400c4000b003e40d812580200424040401006000c0c035881c20742c10030101c00e800c00510540e200245020070000ba070720710385480c0d00d1305034001503030302d5422600c3c40041140401000285580f0062501209074900c8003200b55080700700003d0210010a0b5000744070b00d44400000d005454150422816035034134221500d045041418150890140d0340103c100510915000040d4910407002c0107200c00010f850f00c0d4a05501512002d0000c1c080d1220755040c440f4000e03866042503c5d92090442c0c1c071540310300060700d43d412a403c00c21801d4002e807808003140d0138443d0034408210701085c0e00d411100072001d48404e000112000c207d03240200e510859000e45081c00000300101c06400c4081e200000703609482d81c51500344c106000319040c185405030800000385801240f41c40000003021034070010100c03410715154a039a8280c00e0de2035604068005503001c028401200310034010f0349180313442400602074541c1400003061 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 288632958 1250 288631708 288631727
    0x9031c05011404050912030106020a060c03050f1807150207030308010b0f190201060302030709230108030d0b030f01021603080c03010608061302070f03020d1202041406131d071707 79
    0x62186130341d1008502c10780380400a50101100c601c403080d0726581c1d550f401035140c401004040e1000c43c14002228802da1180c4a440e01c5005101841c5840b902d5440741040d2213805513100301e0032480b4050000c42c140c1c826a0421124070402c0c2d004240050862800030480581030303102d941201018030071007460710f80c64025a0350810a401050180c4100440c003240502155803000e50907000707202021849804681100051002794201446a0704106805903d8a9002d01c50340585400038080e804a103e001e0300160284e210050403540d00c101000d90352070032030b446030754948032400d40f1564900406070080e003441c1d48007101500c01811507142c0100580900b8000b003272030f4401d961100e1107031403203441507042c0c40d484da804c0a07180e251403010307250195849041e041c20a0100791a034038001c803950018000c03102038403e01e040d003c083c1002c2c3c0051041c1604441d01013100312035a0100843c21009040400640ad0b03c0e9902010b49428010000313080b640c4020075100e07400e44c5110070000006d41155000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 288634208 1250 288632958 288632999
    0x20918130f0512030a021206010806010210050703110f04090c1d04110403051f0b120a0204020d0e0f101506020d0e040f020f0414040507021f02070204020309031c0501 73
    0xd00d041d2981d032604500b8402540b80140c40c0840c00f10038000f41c0e130426409000b187c10440f0040545488090041d566000b0480e400c50040e405904140d200702e01c250003080d045050b50501090083c544846101190000032071864007003404102008008107034040c502c0c50144606003503010f4181c980c841c8801a1190380d015009035102c0010111180c0d120f0708440040d504141076810107442c401110492019112845046504002d800112850603640c646240700b075406c01400b44040903800d00001c0c1d00407800724648070ba42c940004e644600c091002649080c940340103003415001d2400e001341100c05400414440c160090b005004441e00043c0c50b000458407030130291090010000010090207540c01255452400032075000320111140000e082034803100b0f448d50f6255080d80080c4400c980c1c6c1102d0a60060384402c44220030002d0000041145082030700c005032511049401150030b80e40203980c512025407001501403002289141415a074070000c0c0024410b5500d0010305a49081c60000d24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 288635458 1250 288634208 288634223
    0x121e1e0304030c0204020a02010906060512072319060212030c030408070f06020a090602120f0a180b180f0301060f051201021204050f060f010f0303030b0315010902091813 75
    0x1040a0502800d6032007410344e402002590b8407500544000c0c064540031400300d42c56428a41c02280070b10300140095100f2143d0300c010210b0a10b4002080100000407900088844502121080350f4032840d400100c2210144680c031200c6142400c003e2410705100c0c0c003141c40b14400e0060110b010440c100b20b03504160440246601e60b0440d0070442501103811074011b21091000030042d0392036030031280b050308885298082e03404a90380048000c1c0035104000d6a40d034075400411407084a98060074a085044500000e0190156107034585003440d5840113074000004c50f2402c024111600d0802e850405c0000190024090b4a242c0507605190551302d02405200d200b00f0200c08104650035030541303402c4245030005a209042500300640c840c618020f00c094240904d40000303288040c1c4800050403940c100c01d40320340c070614540b8220014400c101c401c65240c0500f1088400a5410b0015113029140b1003138010b9640c140e550802401c00701d190b000710200540e100400c540c4078100800c41d61003a400451 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 288636708 1250 288635458 288635461
    0x1404030305120405150406051501050306030705100c080d1b0f0206070509042301060e06070f03050313060c1101200d020d0b03100f0b0f1c030e03121e1e03 68
    0x81007810701203030071845d4615074055001c020a1050541005020b00c0c0410019040c4a40071070044410307200480d191038050344810780420090500404615258450303242291040302544c0d588000c43e4082015030b4441500ea4202c00003818000440101d003141c581012400e06850f22006500c981008101130203200c0041440740064030f07190001100303201410803541100310444050103911700c00380622000180074240b001100d0600f07004451a40360819104421201c10799412a180c0d400100200049503000007800c0020307440c1c4c05150614134260316614081d070207405105003116205804181c5021502080702203a103000340468503405000e041c056601c10342c5604900c00f900e019039100b03402d841a2200c0c100c44408035841050b484026900500881c0d070031208208910619000d400e43c41810f0302400c2d44440f280c144030840c218801d061000084031f107500002e0030f12400101141d2440000940c94028003505400e69500e5641e4910b21030a02c460721441c00c1409140009900c91842d0020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 288637958 1250 288636708 288636713
    0x10617040b070e060f03011508010323011103010608040b070914040504020f0907091706041703040f0b0c0a02011103090c0d0305160606030b0f062b0c060305010614040303051204 78
    0x40703c004160000380210f5514071080c03040605e030398424441c205010002c0a1920446841011860f0482e0b4000c10b041000c56000d88007103403154034400030645590750300c02c0110346c0e00c160b15002c0c41c0280302a4071205498034050801c1ca0742490b0061024040000320b080170f2250701d03010300f02c014900b402501d0004050b900d920200d4003510f008008030f60700880900c02c001e181039000c00010280c9481c520701101107a0342e1156550303039500903180240081c002910052600c0c405c5005540e100d401188040b405c0c0070607803100f5440e43c3c010f9a02d4403800030700085580c000d540902455108114280482e441c602c0c0c0200d03d180c40300041300e4058401c080144901c0305261040d81560700f21003054803076903010302140c98514000d009074030007259080d034440700007403c0846440d0041e102d00300140218200c901018403400d1107045588403070080300d0352642041d0116010030740390300c050002520009069410701c4800b80c86002c980e2004081f16a081106000180c1c0c0002614100c09641e241c010180d241c92 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 288639208 1250 288637958 288637967
    0xa11060f280f0c022e05070e0a0b22030b01030209060102100509011e020a09090213030f060506030f0d0e131d0c010908010603170309190614010617040b07 68
    0x11101481c1c503402c1003002480120203070300c001001c2050340c0031510004c6245000b2003240003014000b5629801d46000b001180b0131030307001036505c02018034140052078000700c00141e072100103070801c1c485510041182412404140c50070540f48410030390302e044107031031991008a407100c140030007405103005001160090340204480ca0542400f507006002a16040081c1c82c0204001000f0406018505c1202c51991105108480261030542d541088890406510a01035880074114018441e241d43c0000013240c0071041c0c1303400b802e02c16003020030241000c904262400c4401030b04584660440c07280301031455080031210700d1011003504c3c05181c045480e041c1400506000d034042c640070112403c040d1454001103035032104140c09888007070b03680b6160080f1500725001404028070307062903640c1107560020f03290003a651041003802152113588003130320a030165682d4064100c81d8641c40d035602503100e04007101c2c40c501400781c034a0101100407280b40500072042d00948080d00015503c3c000c9030450b44038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 288640458 1250 288639208 288639271
    0x207030507080a030903090e0903090d0c080115050406050405060618060d09050c040f05060109090908040f0303080a0e15060d0201030b1504030c05090103020d0b0712110a11060f 78
    0x3010529483e407441000c00f0b00a440c0b4140d045000034041c0402150202c800d03003105001d50070210003541403000e090107000802c08042c0c000e40d5404011781000440b82c509002c0c1610340c0421500c00600c2a103004c041c0310071703901d558002c0740c071650034403007000007a07141d6a098501c2000d425004218041c1d290020540310711814100140542c24000980d0034040c00041c86620000705850400c07034166490406d4040700d405032140380c0000e01c0703a24100120780550b00403c042e5805100024501030341d990314041c0400300f543c811000310b00d51504100c0d43c680540301d82e0819140036405052050b480c1c07034400d114400014817103441851610100e806691003a8400340304118007824028000002c1c81408101b90013030300c0202c40c045044a800300d840c0c1000e10003c1c2c101e9a025140d502c00e0402ca50726102c50100c004c0030b8004000c9220740480d60382420f4020034130104a400f52556944860388002451582d10000d417034074651045060025210600803880d5101402030740061100504450740c6941104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 288641708 1250 288640458 288640463
    0xa02010c0f02210d03060f170f1506100f05030c07050a171305121c111b0a08010c0905300c09060a081f0609091208150d060207030507 59
    0x120840018001c00da100400a010b6224102c4121420481c1c0c12811b80f4914026100044003010003041000499404494001115401d41e004081c612070540e240c45554020018803903011010b0001c50300309074022920744106032030407070401c1616400142040c132018109003031a00000400e402448030521908084070352000c2605000449000784074560f40042c8203a8131421400c40000505207040c04885854001c00c1001e04580c452000c01244080703100e4902009014080c031008040f10345c1404071800d1080302030107035004002c85605000c2040059000314100307030716244110141700e4010200000722041110072030800c00c2c0050100342811032509201c045650041c51240c8407840101e0301d446450300c00c0d0340c2e400b02662048200208007030288101245a0015084007480805421402072455000e42020032465640e2425004840300c5900c2550301c09a89008000d046910081a0382c2000160a800500e141503000190040e00070a20040c1920780c0000d05800b0103000b00c0c142c450032074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 288642958 1250 288641708 288641719
    0x90c010c060b030d0f14070b0f0606090909030a030f0c081302060c010c120b0a030b07030504110904060e0c0604081b031204030c0314030f0405010305070215070315170a02010c0f02 79
    0x10134003030025107078220b10350080000c25030801904c41c403107803178100755400306400260f0a07400f9101d080406410b40009001a034002504005000c0c05403181000d075800b500c1244011503950704800710080841d040c2642c900011810100c042d0312141c3c0c000907a46e00420403040c1100c40003000e200240c01482044038452855082500e940486500301c003000c49051a00d5005200d2000c407007080020030710701404005c2a01008501141916120382e0065078054410403901070500301f044009485440c0c22181100d030aa01c590380080c81c0c03441440300510042e1300f0346034141450b0a00300403540340c8800c1a801002041842c84036a881d0707500304103100b44100000d410942e40ca40700e00b8640052019070005603a860251220711001c03a500004440c01a04000709207410a403c000c0114090f0102402c010114400c024900440050b00d83c8010300640c0241c90006a0808400000c9042e21032544002c100b42c11881130604100c10200b5800c0000d0750920f440303d100b80e00c2d071611070404d28400c0004dd4106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 288644208 1250 288642958 288642973
    0xf0a0905011e060b040503060403050705010f1119020a11150d0e01060e07020601030b0a020c0309030d090801140105030709020a021c09050a0e10050618040f0b0117090c010c060b03 79
    0x30b981049030b00d60b0000080405001198075007529918a100718410903425900840000d404203105402030b00d00c8501ca54004110802c0740300e400000c2d10010741554584110004180e0081c0c030400c001110040c48e2070018010100c095155035011118a400790350048103514403180c250324101c1c04503020a03462842c01c05c0040c040041040c002c5c5210b0140ca032a000400001c82c0001d070001074000d040303c1c0d02c02d00044c00c076030380c5400c2c020103034100e0002001184018040c0c04002e503002d208000f40c0d01126960284420b180981c0d50342900d00d10142c9a159010280040c0700c1c0b5100803a90030b06640c40324502590b1004d20712000c918103060080c403c05844a0140c4132001c159126001e80300b00d4400b00ca80446d001c0d11414031142c640d0003503480050860110100f0401410000c01601040c1002000c00c0d00e08640304005c00c096a81d080c04555549541d00e01c2c00c122982c00c50200d5001c0c12400086500c07501e031154042e40c0c1c6441c10f00f070490501c65002e4117030041128035080b41c1840740010741581d161 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 288645458 1250 288644208 288644231
    0x120908060c030f0907080a02010302130b1c06090212270d080a1a010509100e04090506190c0c17040902040801020c0f0d051c0204051507110301060e0f0a090501 70
    0xd640060b10321180035480e1001041c03c040001600d1170640340d030140502408140f0b45c2c01940298004d01803c001c2e44088000010701443c040c0c00707880c15085080c403040c1c84280e0406520304940141c0c018813003da2041c404040340c0c070b050741358142c1c0c040e00c14044000400c07440c0b4080380c46800c128640eaa80b61064010388804640e0252001d8014040f80400b4802c558402140e18203d00b1402052070000303105100390a85858070340b08042e04050141800e8841c07009407408502600d4204900f900d05038081024008240340240402d880100303202010000321004502c024a02540d011015101850f442450188030781c40b8402c640003481b000000710b42c1c850740c07a00c915010303402c00640c146c2d403401081000d40000c80007003411149048180d4815281404451409810103984034010000c00e509001c0403509480d00340e00ca2115103420654079403200b0040c40c041c900d01d81e065030140d001c0e0341040c50401041130000440382c0c0002d1011202209582c0e402d1040d8000d101c1c5408c090015801c01241964 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 288646708 1250 288645458 288645481
    0x90603080a080106020a030e0603100806090109110604050d08070809031903081501080106031d010e0106030c0618170a0f03030b1002011b03051e04080a120e0a12090806 74
    0x28a0344581d1502d020a80c3d81d0305060780c980d0800d001c003038080f0f100e030300c100c003005e11742040110342c480e20103540142e90980b50ba010b245040c40440d5501c02c6070390345143c000140040e0303045400800408a03490ba203890b0800010460382c051314600200b11100100d020010071a660080d909850740281c22500034058054038224800b8440105130045000d03030003c0b98484a85000c0d0203030186040c3c40f00c4540f03903c2c0000860080c803000c0340301d418550002d0200b8512140038025021a0014080086652421400d049051071f007554010024031542d013600001d00032513450910101c444001500088080da00301a03030505414103002018522500907200416416500c24403080318140c85069107030006623826030032100c011800d860398a925200074041c2510035000b05602840c06410303441e03442ca4500c10080b107550b0981d0103d800013008505034207405d034010414241d404420100b40001e509024840707445419105000e458100c14000700c10b2414010020310009060250480d01c0c82d14103c411a403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 288647958 1250 288646708 288646717
    0x709272f0405060f03060c130302030f01051510020a0204150e0a050f0711060f040c0b070b1f050d1101050c030a020a0501240b090a030b011511011506030905030409060308 75
    0x1d12480c9848042061410250302d80d00c3c04840280c001c0843c2d4a07002c5204001e5009a45a1050820081c102000603103090200810310f10785080089500d08050440480401048440502174009050480401e07a800580030580c20303019500040c40d00047e42100b401042960400d907901003c15041c080148201e5100500c038030b0407010207140c143c44001046030403242140e00b102e410307400000401c0007034104129442e001441403840e28801c03680c400f44944681c00c84d180c151790380c002100402891000c5002c4010700c103c1c80e04502e864007810000050701d918040310025002045075850004503034050b4048910b0900c1d41c00c06c4940320036189100079503a0180f02003c03a80c41d402d2954050704644401c0f0686904000306094101c10390410205803660381160320120303401f455000e000804685a115020f0180561066014000c0807508020705903119040e0030203020303031412000851090100100d41d081d00c2042c42c0108408406c2e013001451409140c2107405081c1c0f81c83c10002c00c01210304002e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 288649208 1250 288647958 288648053
    0x10050408070605060105040b040e0c1210030506010e0103120809070305030c010b030c06030412050705012307230315010e040e1e03030105060f07032c0102070927 71
    0x40c0320f6940d446004590743d00a500c41d0034441e0009200500070011074101041d40100c01c130b660303107040041030304404400320800d8895101012958000340309103c1d00340000d9024281407903000c99194599900c10031421903031600c503c10807640d50081000007009100302001581c1040c101d03a1204950490b01e03001b00084002c2e07512078800d501481c6918100783c1c050f2440382d9041a07642e981a80e6812003668240c1c03100705c08840656a90320361401c503120288182c140b251040340c440016241440000d050100c044a840086000411001c0e20f0750040744116603001d580000100205048840180c0341c42c8540c4200c42e902070f081c07100a520307100b000151b10904010408694151656030805a51244000e0242c540c20503810481241c0d07091010300107040c0280300307150950962401501c0000c602017003858a000681600380303240207a60b81003115001038801000c2c01c00280380c1020400c1c1502c810f440d400c0c1e811240540c641c1e0284031207034145121403e028000034804410000c1104055215071252 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 288650458 1250 288649208 288649211
    0x50f010c0c120302030c0f12070f0216061812060c0906180510120f140916050d0c030804060302030a11031e04080c010c0e030d0206061011100504080706 67
    0x814480d8400c65100c070240341c0185550308400c1021000310043d600041810842c49030400281c90b22104200040142d501d0080003001c881c01d080c0d400405406908118100319031102000018801d801d4905e80f084034400d0400c01c80855074401f512046007400d0348204134910416580900b1300c11190080840d8104994405041ca51580c0c000c0d00c038803000e54007503021905095414450340c2003443c060310441c4400d013802c0e1043c0c45103042c508141c40c1000700309001a13880c0c41c441801d0300869485075030012680c00c003034104610300c9685890380c40329038440d0521414804a48809104203503038000061a0002c410741d90741e81d10303400042d001c1c0d4412b444000c02c5c02d18042481300d803441c6090a072805124101162482d40d80c0c40100340a002c04054400e803084401007203140f40300e050074414801c4082a07525407404611030356080500f0103910407034100c1990061402c101c4145d030744642c501c800d900300d828940b6145d038094400502d0a110f881c004907140b841c00c0b0a2209000e03424001d0118a031081c2c0c2d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 288651708 1250 288650458 288650471
    0xc0c0501050703080f060f360f0f070903080f18010306050d230105011d1308161103060108100b0d0201051903061203270f1401050906030103060204030b0c0f030f1e04050f01 76
    0x123292041e0750049404170141c0340308402003451245041c0c02903802002034540003044a45a0b120340e8441e901c00b170045c8040d0140010154031110000075820340341102400d0030804a441c1c080811110480580300401928091103800954281d519040c411280601d00030861582c403400c0f032790040c1440c0540d1540c0c1528800004030b407030051070001209a6408034100d41000c1803802c204407048100c134002c581c000c140102d40c0f00b41d80c4080010324000c03d9040d0052960388005820001190000ca80050094000e9041a00503076081000c440031913180445d5580044420541200289030301c0d00a54410500c0100d01000c0c0366221142c0348001440b80c400c004141d01400d41c0c0d814181c418403405040e80082e05e8100020414028550004281030508524100c0740e4000a12294402d800c111030880e4085400e0090001081c0143d078819a103400161800b0300c01d80c1800c00e03e0100900380f000000c100400a08802590110040c80081c0c9030b1000d41c0d2820300e490041d4071821009204840c5610300348 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 288652958 1250 288651708 288651799
    0x3050613050703061e090b0612070302092d01030309031e0c031104090b011e050907020606040518060a0c1e090302130e07060c0c0501050703080f060f 66
    0x100d0041895001000304001803641c0d95480103004074a005002070120402c500c20a208107024807910780d44110000c1149141c11400c0142c56122410802c80d9503001c5082403005894284650fa003010220074240c0c002c032480c0c0d802c640a030108042400311010700900000402d174000c80b035003080e00d228140980d681034014000c600740d07180070100604040a02c01003080800e944a05400b141c2501820105440d5003546689003510821391025680e00b4001110107119003103100684040e14045901308001d04055000940e40c100292040d4400e9079140c0202d5501d040041078940c25014001c2655205c0c41c14400080c02090101415008252078200c0120b2070111250400c0c10307000c250712020080e90458080c0540142c00d400040e84040c0e0703071810340b000788000300020001003190740c0e1900002c4074145004811203c15611003410b0001c10722902001940101443e584109804000c018640c1c07410005001d9004005015401c4044078910420354080c9c0846040c00001483c032035401e44600c003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 288654208 1250 288652958 288652981
    0x90312090303070b0417041409010909080a03180c0b0304020a090c02070605070c0e0103141213060309021302040b0903060609060906100201110a03050f090d0e01050a2304030506 78
    0xc221566054200700801000640c140405a820900400500c101009003040800c60750b4802d400c10009960301101c50b42e1a0318120f9131250141028078410b000b0082150358044030f5000b8034150405040c0ca4950401e148101c5c0d800450f9640d8000074503110455540118040e164000e0f80c6c00c0c2d001b401342c0c81c80424180700780d009450914442d5401030800303074030b03160003144c0603003041004495451030000001590198030b62454040e5000b00d0829041c40e2041c04454580130320070410700043c150030b01c00c4501e101900584030301182e1003400e02040406040c0300240c2c0084882c40c0c40300c80c0c10b101080100f03407401c07441c1c0540100d54007a022201070391251170402c498040c0072241140d00602c5000060b101e03040180c81c9801280d002e00001c00c504109801e10b0b03201c3e41100300c110002951707480800c10030b0f210318001c407504401824040e10b030023120104d0051021041d01c0109060201c0052207015080c0b041c0c1495142c0c8544504104080c2c00d42c250400c1c86174080c1c070050700d0354800d0340c01003145010003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 288655458 1250 288654208 288654217
    0xc150c0e120f030f07030e0d0809010215061507060f060f061d1e060c0102030114041805070504020c0709110a020706141c0902030f0f0706090b040b090301180503090312 74
    0x5540043d030401c1040d03000148a0743c840102181000910b8a1641e86d41e01e492030071040311841100d000d1340340d03e00b03040024501000d91140a65062421040c4a07403a1203462000710058043c0a03500d5a40310141001d1000d0003132000e88603d80307072400303c0c0010002c115184200565a81c0d5484c1007150b4444000f007031040302c07000c80c01c940c840c100400089220300e280d0f110f46440c61000e06018100401809441d00f2a0800d070300c8420303448400d080c0ca4409180c07900c41c014082d5010024000c009040e901c6080c0da40025024580c0103560000e91404140010007142c40100b54140301440005c0d004e100003192038000214101c01343c49445004103081d8000c0040c003a00c040600d14840c204007000e454699058071141e40c0381c400c2940e4001280160f2000d0111600500c800402801446441e00e50b0910300007082d400314042044001081c4469510907044a040310381ca032140380d03103d9107250000781c010141c5455010960140c1400d1808202001c000380c0295030045046c1c1d0401d072205410080f2600c103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 288656708 1250 288655458 288655483
    0x5012004180b0a08060106030c0e09010305060402041e06060903140304051f0c0b15101e05033d050a0609030b090a080d060e010801020a0f0c150c0e12 66
    0x180e400300071003881c030340741d00114841100810015002d980c61100700c0c00d041c001e0300000d00203500d40000b4210142c00022000b683d903029035040c1e089600d507884041c3c0700c041c00741009200c0c688070f100b60b1003106418501400724000e06001000400d9940034040c008942c144011207100100d812070a03080840031042d5000c036075015007218000e804103403941a1a00b4001414410b000010440c140828000310721a07114548078433880341c5c185035110800242100f04842001000308103140c49030014a081c40c11a65020309040580d10303510707103032400c014045140c0a891844490107103466a1003103020081d400100a0341019060f50361100c040c0052110f0707a001d0b04001c40c2b10540b0800004130802c071050741c0504400709851080c1641d540c0c4007181e5106002120250792280c80512a66149000388dd0040ca00140210b2030700041d0003011344081c568965007030500840c01d9160043c0040d030320501c4050115060100700902c9101d10280444040b2030b0301e940200e045401c841c880c1c1d880011944004003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 288657958 1250 288656708 288656729
    0x7122a180e0601080c0d0204060509010e1906030e010b12150f09060f070e100f030b01081509060102030d090308011502161503090204021206030c0613050103050c07050a05012004 78
    0x166a40019591600d000e805ca480800080000207459480e0707201900103000185c0d01d8a540320020030004242d04007521207144215448902d0450454140800404982c040e0a022418014881c07941e801070001481850b0000c1906514054078900803c40d81c940c3d0048100042407601c030907d024211342d1080303074403886542c4000042654907025050440d0b000300d0904d0108440c06403140811110041c2c1c0d440e500c00b0503c4054441d00054040c011408200002c2ca002481441c001d400000c3c11744c1d031a11801d009074241c5002c204141d100340116990350740706440a0101c40060f1500410f460824440e521070741c6080c0800b410031901c081640301d80c852034800c004400d5420101c018804903515a2000141655040c1900040e121030024104c050011081c0501c20301c0c100040c90f0818841c043c4403032003544100030700003444078441040010744400b032030000f50540c0c580140392814401c01c40007070142d10078103007032130304100c01504646241c5001100100710144190b01d00c4c481e90060340034440801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 288659208 1250 288657958 288657961
    0x10b16020f041b02100e0d0c0602070303090816020a0e091e010b0a0b0706050c0903120d06050a0b0702010306051009060c150606020601060e01020c010807122a180e 72
    0x14a070121680c8007040d801800001c02d0702d08002d2a03103050308458403050158014004900340b9400d03910910000b410303210081c0450000c403240080030240741c2d4000402655000c2510340a051095010440d0307070307600100040e82c500c08034419520854036503004031700c07078550b400010504000d8bc4100501070a020340040c000700c11a0191018408040302c0744403140e41da40da811948550740d905080c0001c103107554905945401604000013640d50007052140a40b404104510958a00040b101305481c1d0200d850b0f9201d4903d400c0c54030141181d136001d150300241c02c04022031203030780c4003000384241e9100341c9040040c603a1b034105100444040b041140082507801104100e81d500546450751181d01c182454502c88030404141b8045032a190802c00c0103074000e0005006968000034559030300c01e0240000e0007028003d1000801003a8010160010400184010000882503800c004452120b00d011408039403264417041c10201003101d1720b000042d815010024118010740412030a440b40c6911100c400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 288660458 1250 288659208 288659213
    0x30d0c0b0901110f090a09050c03011e08010c0504150c020a180906051602070b0c03040b1b0a060b0328030807050d0903030605090606030f0f100305060c12010b16 71
    0x403800000c1c00e6090654032501c0c0440e107415110024002040e4a94200b42c03504000360a10595510301d0300003e40d55843e2001340250003001c01c059070704442d0310841d01c0c59824512a40005400e141f07520141d80c0750300380a041455142c10001400c140e401c017501c10341041c031a18004490a071642d4001039008084601c080c011402d5154140790155122200480c0c0c102986d80c901d02250703070490b001792030100b46c500364502007a810300c0b403d4000e00000078a1410f01c40340340b55403a105d2180c0e00c1410208076002440610f210220b0041d2074111000c10305480d540182c03401c11030080c02c0741905040c441c1c0074030b9014103a21284c40c17007103411081031241c407600c150400c1d9030240e4440802074000c00511900744041c103003c00a9008030440c062090b0340205441d072400d402e00c02c1c0c1010142c0000c1c82102c0a0042000002d16064403552003403500c2401d01842d2240c5040d054105c0d807076000a0454080c0e1810021616440d400900100344102c0c404115a03980b4000c03c0d54502aa00301840703444030f160320b100301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 288661708 1250 288660458 288660473
    0x303030c031e0c0e060706060914090c0d0f15090605011a07120309080301080c01020c12150403091505090306070f1d060d021603170630030406120b030d0c 68
    0x1203c4103078108100105005400200710b40c0000c4400c880b000d0304d94400b4040c0c04d0740707402000c50048a08218a0603801e28180880d114800b441849014159200b1507005002e03d00c2da000c1e6141e034010411002220540f4007c1c1e0140c20092800c1d01e0040c00c00d000002c4035411405154112610085402e087c0003036503540d00c2c000e032581105402003617201c3d22207902045041d401940200447c4c030040c0700482d000400a0308000500da190391042e8440c50950000103404200020303220842c2d00403010390341d214078064405095a03002510244041c00710300900343d800c80d00400b08400110101c9010b030b074401034110b8640c00307003d41c4803000488004e450444c90031380c030100c0d25080c00c0003001d40b420243c2502c41042203800c840c10101d01d40354a105100141034105c8005103142600c10040e10852621002080343d84851031682040302120240d4081c0000c0b00c1c0c99001003180008040c2d030340d215511040203204074140502106c90b10700e08002c80300d080c540000c2c2d044c0c1244458a071100e280446498041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 288662958 1250 288661708 288661721
    0x60f1b030c0904050108070e010f030201081f17030c011b02030f0a11010c050901030c080105090c0c0a1b08150103031d030f01111803011103011401050c010509070303030c031e 77
    0x188400d0703003404400715590b158002e160280c0140c10080400b01d10303268010074040c2044c1d22241034980603000500140c0d074450311300c41e031203682d001c000406002c00f0441c120011545a001c035040410301410002050408030051080ba4078110081c0b1080162080a1019032842034001015a00030445111801004400784c00e06480038240000488005003840d429101100c0b0024002100095095699030b050300c11040000d040e40b070515000d606000108144840242c5841c050000120f00045901e000300306e40d4451946c06144c58030400041d80211408500c1c5005880b420700801424442d601a0a14075074101e030703016500c084041e1501001040b0a4501500d80340c0c05008004c11451040404d000e010044400844155540c42c032111401c81095070400c0c0b014404d90426041c060030301115429641918010740319112500440760050b281c2e8810301c440c1030740d15420842042a0490007054900c1142c0c001e40f0240144c1c020400c0807401c44080035103101c08003190317040340e4114104650015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 288664208 1250 288662958 288662971
    0x60e0a05031b04270501050f01090216020909031b0a0506160e0f01050405030a0302060901051005010c0206091c030507020f04060501021b011412011d0c030411040212010e09060f1b03 80
    0x20351304e0741e503845000001e4038462500740c92503034440040c85116140115241e0048c020b008086090070419200d14540c2401c0b10300280c8a18414004915400c2040c01114210b02004519689041c40d84038001c8e2200400711003940c040c0125800070b100f40c00000c6468036640000e65454050742c3c421020407090b9103ea584a90421000380404105038800308501c20049000750020815858004205403e5460081030b040d155030101c80c2c2003285980150b46004203070303411034101d070320b40416001051383c0d055851071308144200304241c07860600d030b040030003040c0c0240241c51a0154416000a00007030f900781d4407406005901144a00c261108070803943c1e4411001450300c1940084000b403c0d003078030b42000d1a031703c0c4140412001008010b03281100c82020101519001c112803400d12b8000716580001007004e4003000c460402d11890356103e41c101c0e00c02a100e21800301155031200721a030461002169103100314421003000c55241ca00d050062480b40f1b8498188d00030719217408810030050380014124 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 288665458 1250 288664208 288664241
    0x2131502010230011715060f100c050d1b020603070e04020a03061403011119020c0d0f060b041506030f09060c05030915090d0c1506060e0a05031b04 65
    0x2008031000d035200140382402d000c0d8001030500c200491480a9045040c3e0104c80c070300d14800c1d6600c08214000c6424031b0030b41500e02012100b1303901c03100810f0030440f1100b40140d00980348400460a40d0f005100c44145c10300407011103051030b08051090320702800030049c1c800c010401e1840d00006103420001958020168546070380c1c0300050b44003040c01d0b82c1108802c2070118be1540d406002c5118418114081d4079401c400030720145108440300715140c4213090550744020464050410114000c118034401c802c3c0181c000080c50b50b940c10090480e0004080445d110b41c104881c4061f10b00c2e2070300a05510b90150140040c0940c54070f0402e80c014021182d0100036144c55000d080080b804c5807140e01d66511440e100c1a9980c5070100b601420002100c8407174003110901014014003c13400a488207040409090500d4900700f9818200c015410042d0301c03082d20350503c40c1c0410403aa0003515a0b0501e41c0a580100b140c030b480d2004c08d6203418a81d5041c0d51140710644c0c1980207403800e6044443c07190300e802d10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 288666708 1250 288665458 288665467
    0x1903090203120a0203160c1a0f120408070b0106120c030b0906060d0608060124180e04080408031615020901050909040614010b030f0f01060203030403030905070506070614060103021315020102 84
    0x11405492003140c0c2641d580c6001c034404c008d0746400f400c109054000b41801035140205412512800740181e040a0400c02190000181008a400308450b061600700b024440b403580d5410004000002c12521118054241201040c200380a4040d04224000040c4107101d56603070b8100b48244d40c0c026070b82c00c0680b107454800001e0030800620146001e0180400d0f80e40c00405900c802e0b26880c038041e03200004210307000350407a5070300b818280e03040300b6101203080428560300c50f401c00c104140500c1d044945180000150490b8140125441100d15846451401d1401807181103140890250041d080c0c0440c20030030811090307207003683c1d803180d100d80300b0f1074001501e6040c882556420082600000e00c410000000d1140c0c0e88201040103621217007401c00d00c41990f060006c020346070301000e8070003020315480d0413281d02005001d201c42c04c040c2c0702c082d158030b071203110300e0802038083d20490384181700c06410540400d0883d4464000c90b046042c1040700340b450a0301d4806045110780094201c141195400d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 288667958 1250 288666708 288666727
    0x5190f02100221010b0913020703020c0a060e0901080601060f0c05160b040303030e071a0901111f050c03060d030c08271309050c01030b040608121903090203120a0203 73
    0xc082c080f42d2100000706045200d200d07840102d1440103070412075216005014241041d9120304c0612240c0042c1e1401503100e00c2c091400781e140101080c0b06036841042ca82e800300f04194888864a8414412a55500141d070f80c4d89015480355000c0c045c490001d00c000600f40b180f54010100c1c1888507128904441403000190104240c8103104d401600c00d9420004041061640c5030080f00380720905000608070f524602030303203620a10070300e0f80c5400c410b40f001328030880c00707070300541d0640c4002c0c0c04601555419502400e0340b81010320b07003901d2059000d1620020480b40d020f0401500e100d0313900584007a18083e0103450542d203c00045034210348a00d02048202060035461100f8602ca00d01e0400900f40d58148204012000904914014000b0301d04007258011070000540046002000e0070006000a413140210b809444150864142d91250184454000030200c000300602072040030800c159026801c0c080301030300c0d84a60041e606512000c000503500301800001c0802c03900c2c4c2e0046030f145c90400f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 288669064 1106 288667958 288667961
    0xd06032105121603020705161a030103050703030806060409181202030316110a0606032001080708070305181b0109051005030a090f0f0602070c050105190f0210 70
    0x1031840800304e010f541284d80044c0c0000650b2600c03000701840c0a54980c4500c40e41140c0b080d9052179500055114050380c2c107890340500030340032441c90343d28100c0d41920094031155000c101000005480801407260b0300c500d880460f180740f0744480c14284840030808041c00f100554004208001c1914110b10294900180c81c0c144104d010151981242c03074103e10850080c2510f240c18001f0041c4502104c2e00402c104407800c0300e03016884103030011221104195010300118140318045800303240070307411032584000301e0070b4407085090317001502601c6e0802520402503035401072000008296401805c01c400340100340d444007a5605151801042844018180c05016a69005c503c0030005080c1c0c64551041c0c00c001d01c03d80c00e00c00b50525a0095021100844414842520004031940038900307071100424002c2d080c5e070700190400d209035200c1256200c500c046001d41c0300c445020b80401e = true := by decide +kernel

theorem cover : BRFrame.Cov 288489208 288669064 := by
  have h0 := BRFrame.cov_init 288489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 288489208 ≤ n) (h2 : n < 288669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
