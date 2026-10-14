-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3529
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:55:18.340761+00:00
-- url     : https://prove2.me/submissions/1a5ee87c-eea7-44fc-a1fa-f26d6325540d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 634532374 ≤ n < 634712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 634533624 1250 634532374 634532389
    0x304060f081b0c0a12090311270a06033c0c050105090402042d0501170f150a030b31020108041103010f0209090906220201051c05060111030306 63
    0xc240060b0041d80c2d948210001420002c1c0000c0142c00c010341d5022841d01c880c5e110340b020049078040d040e07841ca1110103000b080080c4008001c41e0424404041403281c100c020250340a4200201c4000090700c1c81d646c3d074805407106444404c5816003403615622020b1403d140e1072042c01170095003120313034003100b42307a45101ea500c255010705410801c022a203114035445950407180034110014404500d401d03819803064981d4100c40100c000c540401d400094a035000d0080603000461550034dd81050744c030201e2083c58120001c007076040c9468510880c81c46601c4010030704001d5402000c40c160035140104840440b0060290b050064002d20000c00542e40c0c030241810880660910784060680ca0f5800d05004c01c035000310040354154032300300c1000e54221140d401018512401e072580312140e0355910000d034650340100c41c0ad01d8403d42c91710145e2407400010014100e03c80c414140b4501705580101ca000c41c58500c9004d40c043d2966032010301c60b4079a0441554214580f0b0040154514540310002c00c0d842c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 634534874 1250 634533624 634533661
    0x40b330901060903081617032401080c04050603040c0905160e01020601030f0809010c14010902011b120507080712080f10060207170f0109050606090901020306030303010b0d021603020304060f08 85
    0x2041500310310007040101e5002c40e51226414800681704d040c0100f040d1901195103809ca2204041901d09a5595004035016071199561042d0305d400d280c138040038080360343e0009008485586400d6400309c1c0d092110f1090a00030000c0c105011190341c1c201c140034241494140c40c003415503102c4001040065888040710080903405050161140c4048006940782d203403200005000d0350081c80f250107040b0f4151300c4415214000d03600c558980f0180305610101e0890003001030400d5440c403401c03d9841d80543c004118040c0f24800903450036120751140c2001550504110780026050b101b231154825004001c250086216006050a00d181950180d45d803078940c850011030076100c440303040004c1804d03c01e001a02c03100f4002801141c52a2a016032902011100240315640d240089807006c101482070360b1282001800442c40d590800510808540050000c442a9502004082c56030604102d81c524a41d109400842e126803c00c00d015040a00035820502048451010070550208420b400e020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 634536124 1250 634534874 634534897
    0x31a041707030c0c08010f141003030503060303131202090901150501030507051e090324011202040905030d05190b010207050d0203010e06070f020709020a08040b33090106090308 78
    0x6503480301e4a0b05446034070b0b070f811000c0c0509040c0b035000684d5450642003403034002529141044885d00040c1c0140e02c1400984900c110060903240c01e000180c0a03c00075604020010f003128103142c01d8043c3d41c1165181030704400c1c09080c1002c040e0045051200a10341c11000702c50090003401200382ea030b0045040c1c0c0d4820340e41016220004600b020b4020b40031034192000203040d00803180003100540308964403160a490080c4240d00c014045107040603908000761404148400080e4640700c10722106209624040cac4e4020365450101000401c20001092007205552011840e40741014000400d002d0303885111000d242492113406841c1c2e80443c2d00e00980b1000c8a5960190b005400800c0c010080d201101c1c0140c072903502403080d215045122003208180e50b6085584040c1c88000d40d10507405600b8100000c140c040010400242c00034800590044900079640c03441007800600d1080c41082c0c540040b0fa407041000070558a0400180301070141103e0708203426594a15640d0381ea25218001d01c058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 634537374 1250 634536124 634536127
    0xa0504030909020a02010204140a06020601090c031107050a06050106030e030702040f02132403200306120d0309020108010b07050d0f0203120708070215011413180804031a0417 77
    0x40030540911503040140050342c01c00c5445841020019000354007500900d0b40c2014030355400491441d1214002c1c040e203416501030241c6034a0701c41c024018015040015050503103036040010307204200e902030311180d401000101900741d20360810900b161010380207502014109010240c2c8500d00108484040d581a50b0001360b11076449030100080c0141003440003000518100081c040224502d4242010703228081d01d120503607810810f904a400340d40c0f00c6071800424006502500c60035202a55100002500007103804c5018061a401c01800c00302680100e5540c43e07003d000e6581c48118030740541800032045d4a85000d03904d03030030b9503914281c80c0c0c3d40030000c113050042e4010b4030900588503000d6a4503258440b174200070801500d80c94044500d000144903443d512080d86c8011050070303040f5000c40444101c010b52107424482c1300207070b0b1401c442a694443e400b400c00088480c00c80da401500450105444504524004413494000c08011038040001010301000c60300c1641d18072100e003402c2140a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 634538624 1250 634537374 634537381
    0x705031b01021e0c010813021c080702040501030804080f0a0b062202070803011703180f040e030c0c21030423040c0f03180c050d080f0a020f10050f0a05 67
    0x40340340400400c03d8010842c2003004070720349014001424000d40c00b003600ca003500c5980b2031003c0982e0041007440650300805020b02c000568016441c00e400a0703000d08007882c6820450380109096440c00c1c0d1085802c44000142041844070a001c0d03d41018141000b03070041c0c1c1c1982d02c0e58003c401000c0e141d41d101d1028007100304100c40d4905440c01048808180564a031030306420038200982003441a58900d0030b01c2c0109503025140032080340c1c0441d64620074200004070000501c400b41c1180d2001d903130020303a52503404208400420242203018242d000a01810450034144810f10910600d40c1d1300000e110059144500e60210940e010380300485a6100e0300024070035a8215031004000703c5811915000b59800d07e1903004d00e00d151888210b480501140c03000034050300142000400140600d1000d4505201c0f074507142f400f1501490041e1002800c014040c000103900e580030745121800b5900013541c10404500900100011500f049800c10191400d9030a92024030360041a00000a681c0c5c80013 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 634539874 1250 634538624 634538627
    0xa0209030c0a0b03060f150a030b0f04090b090f010204031a0a020405090106050307140c0a02090907081608070602010b0108060f12030a0e1905101808120a030e0705031b01 75
    0x164034062401000c1089030383d926440d0640a03070050380c0c0d50b030050381e100114910608122415907907116160090320701c1c100c14907004500601e40107210690080520000080c0c43d500c5000f46030010703000f003809a6060038221002890901510340d09580d990040c007003040851480d0300030240504401e0590007055541590460081c4610342065521240500001c51075039801000340d4801c81300340d01d801d80000844140342070507010b920882441940100848001820800341080d00701500b43b084820864482c032295080048200529a5030002074a0810800d1000c1242e540208174a000800005190b50002440150001c042500445000b14802e00780e071180182c00e80008240401d0b00d44030300e030b40340300208088500c9451a101d440d88102600340d20404807411310890b04010015100f02441c05810703107443d80008460070306658403680000300000d00b480040a0100464055540d0f00b2512001400300e5031030348004081a030001205000e141c40c00500045440401c410805a80100000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 634541124 1250 634539874 634539883
    0xe010f0c05010c0f0206070309020a0b070212101b090509010317130906090b010509060a082a030601110c01120e1603060b0103051e280507090326030a020903 69
    0x40040596191445441da49a80013060702010505503099035210340701c0d003601700c043d00c0b41e01d1000796014000c02002c110a0b00e945005041c0c1c544041e10344a01d080c0d48000312400c0007800c000e2081e2190701c0750500b10640303c81e2224880f2504031410110300d038600b414086000742d1814003004020220311007505650417808010746042c8440c1113000911141c41d20201c002411303541c03060b500c5150600c04550125070007001540c0310100c010f0308070750521701c650400b03c0e411603000d032a081400032680c2441c80c0000302141d40c8413240610000b401c1e501d080c404001000e0b502e17258142d4080303030040f01403194281ea210488007814903c0100215004440e000e0b62411b10940080300c0c452030309040400420010940c12201c0d0440c800d80302004180d64031070002000141c1c03c10300741c074035803950000180400c90910100c2c00224110000401880601ca0032600312503040d80c3d40303004202400c03070800c1008103110310710314845405130403110034602c1340b40105207a00000d40302c0c4401e40e40210303041c0c0d1592401c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 634542374 1250 634541124 634541147
    0x270b06010c0204021239031f050306070c0b0610050910090f180c0206011503020c01020f040e041407320d2103020901090909050c040f060e0f04030e010f 67
    0x1a0489046c00040e82c07440c49101e1245003c0251007015161105c0141c0c903144280015100715076146030b41e4504200101d022805400446000c0203a001c075143c1c40030405071303202d05026101e06001c8501810840e40562004184602c60041900d50402540d401000d4846081090759460040c880d482c4060b00d03e04182d0b000005040340c2c00400290b5040500c41400c00c907000b8103420003440d021048120b032120024003822080d000d00700b0040d05a903110746d005000480c0324800060500702c85076421442d540c425800104405502030a010901c00b0340741c100b0001d541c2800003440c0e40c9142202e41340120040000990403a00032900504801b4403110070346c480c100c4010040c2c02007031458030307042d201d00305e5002c007181c3c5c000808503450040b41d009108441a400c0142c640340c030944e29140502002e0050030318112039500400004c9466a2120b00400042c113100a102041844c202a409001948010030000d0141d6140040c0000f00e6008100c48445401c01c2c031740b15010b0f802000c0305490010410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 634543624 1250 634542374 634542397
    0x612020d1413150504030c020d05120a1d03060103150e0f0d050c10060b07022205090318060f12070c051204051224070201060f09270b06010c020402 65
    0x1000300046800380980000d0514818003c2c081e00804030001181112000c840007008901360550007400f40c03074005030085445200380102c0d040404190900f0311a90800f143c410007050200903541c194100d14420000d005005a00402c0c2961541d00c0b1482c21043d010590710541c3d56600c0c51100b44a0b082c0301001d510141c000171100401c04041c002406e50303010b001c1c1c2c008240240660392107400070030300882d01240d0303040005605002c503903001c000e181c0c03410211800c2140402c4600d41340d021454083e00e4411a51382c406503450f4a1004107604038130100307c603140c0c894003007080143c3c0200b42035000d68425a030b507540070204ca0350700c460045d5040484640041c100f403054034000b02d02408020024000c1e80d4050300c1440035906000d02c00c43d51241058141041c1c000e2a02464023403030f50035601e41d9404800d910021900d10781d1480c1c95810798516801420709191124440030f003000115009400c080751140d40e031000648551503002600d0406800681000761000402c810341d521074043d1100103d82 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 634544874 1250 634543624 634543661
    0x30619150302060415031b09050f06070f0c03020102300f07050703061514010c0f0201032d18020d0f02010c17090915030c0904050f0307140105100612020d 68
    0x4c3d01178a8495031494442c18000a0828200c0d03005040911400902e140c025207850311858148010030540b01d8400040e903810002c248500000309251841244201d4090341408101505500009050000201508210441d01c10840b0702c0c03801982d01e440c4c82d1255164610b41c4985001e04c0e0f802552180641c007170150300c2000c07008410300405038403194840d40264041c0c0041a9102880f1901c09081d1175030501299003039980c00e0100d907100000140d0144145030000e109000540c95010b0f4151800064440140b08540c1d80488246407280201c13103000c0341c2c00110405d070680d000a003100c1449000601c94032a04100d8021a40200ac561150641c0415240a00802c0d0740b074052884d0000342c4001d00c0341240c0004162102c2189895041020340a00508041c0c084030713042c03011180010700119602d00c104100c000440a0500140030124800d900901d842140465410b095030005070151003403103002d410420480d43c1000e01c03105503a8184e10003607210588848400028510000c0709010312340c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 634546124 1250 634544874 634544879
    0xf040b040f150903080d180c060f171003080c01150902070b150a09090206190c050d0f020d1121030118050f0c0c0a050a110f0306191503020604 63
    0x40342807003206488101c000100300ea00030000440d04411288006094000b0401c003200b910324082d005a00181920000d11595031120b944030807144505600910018101a8540081d250300900002c10101d1b400c500c0360352414000c2003043d0740099072000418000000a861f0300c02c0c0001c3d0051551091402d801d0382035240d039a81201c0185d4000002122507401d040009038043d46031a207510340c054009001c0c0c4000354104140349006040c043c0040e640030300c1c14030003880d92980800c0607821511071a91488080341091070280c0c5080764008810382484040308120080d15400501020b0703980461420308160980034401c242428501c1080b450412211040f8891018055000f18101d03131000c04614044e20442a03490100c0307000741c500c82005e842d100702086640b032540000d442850001d2043d1030708000a55605031600c100000308548450100b848559180380c801602d001c500b01c1503020300b0f100c1c6041e01c91440c000406a007480c0304240d40e00d400342c6031917103501c0709030000d981c0c0076000a41d0b554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 634547374 1250 634546124 634546139
    0x50304140d0906080f10050f030c150417071206050403030e0307061505010302041202060a020c0d0507050f010305060d0201031a060c0609070f0503030a030c030216060209011e140f040b04 82
    0x2c0c00ca0141e54081400030b000324602d0a40c507855a8410112076144c00203041c01c00d020800032007005802240d062140401110640c2d8600441ea41010340041c1704580e150f18052a04100e001c06000c09035441d04405010042c0d020104942041181c0c0b260340000d40e6652480c05500a0543c0f02100b2311078400440c6a50420143d640100d20380c49000704111034607640c0c0c500440a920540c0100442340509055079001820510040c080b6032140740142c1c1c4074500070340b011a01390040a80d00b5156a486054104483c5c06c00354a120991802032805115030303d003810100b2402050004000d040540d0361070092003c41c0315201100c01c2000051445a40b00103082402e076680038180c1e01c1c5c0758140291080058044c41000c43e49085800140c069401d2102c03011080d40101000340180ac281174080222003400c5c000310030035100e100d114040060b1183c2c0800001000142566558040c0c24041c0603030310343c440d8001981d0301582c91115216a582d01544044007841e015980c0607841340c11010a0128411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 634548624 1250 634547374 634547387
    0x14040902071208061f1103040509090304060912080403020d110603100306050c0306090f0a020403060603060e0607111903110304030b01030b13080313060920040b0609060901050304140d 81
    0xc108954a0780c9090b103e0800700403802e01c1180c8075141002e6060b101c14040b41c000d4201500358807109040d42d041c03541c0c070004030f44280400c680bd0101c64000280a001160b006100400501500c81c01d000e038500b1141c3d03546090b44540d02001e849202d00152000400c00f2038030841c2403c41000e040c4940f40d00b4103110004582c0b001f80011115203092400040f0025030840544e403080000400c620b00c1912070350b1503041250030192200510703a401700008004503086022b460029445150000749080719504014100080a0916000c0201780510310401da54000b0310300340346450701071480703488070754134a0144e4a8120710146200d03075000206000080c0300703a283c0907038120390051150781119603903420b4210318881c0318000180319401c1440480c080a12000182401520030203000811310101e4540d804902085405c004ea1a28030280080d00c5080c24010810414001d440090600c58060300007002402071400f9141000300110000d003d2250410301030b00385201c82c0098403007100c0d4014004108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 634549874 1250 634548624 634548653
    0xe1c0b06121b01030917030c03040b06060a0c030f05070b102603030f150904062018060304021c0c030302010b010908250801060b04080111030708071404090207 70
    0x100d1610184a400d280301044203542c0440c18201110542c15210041d13000301411030b0f080ea40d22441a0000300348a5003c0c000714060551104219104d241516183c201c2080080045024103404e2088801480e0041d0703d4002d40ba034035080050860304500340881e0715000b500806050f140e5007906020306407041d401f01800b0750300c40c0c1084015510350b0649105e003030241c00859a100b0f50003000091b000e05000a40c554104074000601c1c0000c2e1622400204c90032004c4e141598110f035101040402015115000307400110300c03007000c0d1304100f4140403490354801824002409104000000750840d600e150a451030070f80c0440402c1e145419506000c10380200c680004c0f0095882d10a440b10258080c1d229041104d1210005180c26000924803010790510300020b45122260b090303000c20780d00720a001c0c2d44051310b81c150506c1c0c0c480703203000d03071032429202941d4940006080420070311840e0741d4402da12590240300d90030002c00a002600013100c403841154007106285202103040400c015240c00031042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 634551124 1250 634549874 634549879
    0x10e030624100909140438040b06090106020f072d0602071404050105060307050702040f06121a070e012d0305041b0b180406090c0806121c0e1c0b06 65
    0xc0d030174080c2d9035134800c800309440c050628801900ea201140c0ca0020403100c1e00381c9000328602c48041e1040c0075a90001d400e1b1801c5a543d55180300308032150419002c5a80100301c24402407a80083c0d8074202602d40003a4002c1c20034001c01c6011813010f0002080d411025995580c03141309800b541c1300d20094984816025200c0c0e401996100602d080c03400d4007696040e01d030001d01c0030b4516220250261103070b91000340300b00c1e0080d484c1d174448100e050036442401d000700300002001c00c60303074a280f13418560881e400da0340c0d1030340074944024003020f1988281101c1c2041c00c01c1c00c1a1741d005c06840c1150140c549203111908003403511a0080313480c6030f8981c001e58081c034442c4083c1c042450300e402521a044240740100750200f202407200380100ca0707050010b19404040600005002a150020740e01510181887e600210b00d1500900141d410301d901031b01c689902032000340c460f0b140006107071a540b80001140400304526141a40d10680d1024903011903d9241d00c00421164094905918006c004456161 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 634552374 1250 634551124 634551131
    0x1305090c13080c13020918010b1e07151107060c020d1d01021b180f09060c073305090f0c10080a0e030f03011d0105010e030624100909 59
    0x1c2c10308001800849400b8003d203100300b40440c4041c054000c0d04a03110702030f80f0078016a400c2c1c808980060440780a485d40203080741d55180300501d5a00503044681014018807810410302c004101002d00340c4014180c0c0580c04503695400b0b824040c0240100240649030b03d2a10045558031900000d00c46060300080e00d070340b6000c0d00701d05030000040a0840b0094007503005407280c1b08150640b445a4000300703600402c40003004000c20700d0000b481304200c600c1d0810030342010520107103007030070008030740e10100a0718a246868115601e594000c03071421001c400812000d07a151004030030507400c015519240820411503407805140c00da03030f51580951408040d00501d2001001e0303090940301500d020142d03490348600c50300c817105810000e1000c0b5151400e41d000a0104503020030403840210700030f00d5800d2000499145000c2d55900144041c1c0c41141400440c0d03100141c2c6031004140c60360700298020440c0d0340b1100c8200d00100d2406541c4403207070301004c4040319081326a0001002003e4405105042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 634553624 1250 634552374 634552379
    0x51201050d08030415061a040305070905010b041202010e09070c0b07180b07150e07300b27030c161a071b0e0a0c090b0f1305090c13 58
    0x9144007403000007810002003080014080f0f8507200d48800f5102c1c1e02040000d01d199a8135142c4481e04955129100c4050002010010700408000c090040c095044041200b545042c03500340b003034400e5201701b0107120b405181210035a8090009003002ea4806440c0d41070b14501900003c01000c66100e007103440da10524040ba114070f1084c042040201103004c90034035842c0c10080700c031429800040701162141003040d090301002c2d4440c00740580c050f811000030301425013403178203030000c1c3d90b40d0540b0b03064a00b4a0015250594542c259202c0d07141d40c008088000903120200c035446003004c130803080c0540d94048030758640d481d10b00200034580088010250703014694400304050366100944100c94200c0c0300070640c3c03880c2c00206001444118420281070382030590384428029818076951207101a44081e0082100c1200c3c00d00840050049618103031f84030f54100143c11640340103800d0040c0c1d802902003aaa000030b420100705501900004200d45001d02c0c2100100b941580502c048507056030229400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 634554874 1250 634553624 634553629
    0x15040f020612011d040c1a1c0c08010602030705070b0325080a14042d06140406140426160605040606060c0c030209151e03010c050901050702040b030c060a05120105 72
    0x1c140261b501241c0381c000303140352001c2c410b5802c51401c684010814108481d084404d20f4400700034001540c02800304610f008000041c028041c1640702c0425900204400310004401041ea00140c8044c1d07a0565201e458031040c8006005000011815a0048020040344950080c10061117003543c00303402c1c03203400d080c3c1c5161a010402075074001e1400d03c3c41a010340c81201450018810146100310803011100191619403e03101c001200b4134481c0040c42c140400e011641c0601e0b018620205144035150500f0754840508446003070f18140d2083d00c0a202d0408108404e017150040103015000300700103203141c14840d009020940e4101e809901c3d00c03e000910760b006601c2000d661744c22800c440c4c81d207032854090040c14880100800c10341548950140f0640d5107104c100c00350620101c00e44d0341c07001c1120082c1400c40e90031070601400d1000030701c01e0402c0b41e80d0060443d8042507041e507010a1003902080400c0c030780015440d1559110101245011000354058050004400180480b0406980c3c8009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 634556124 1250 634554874 634554929
    0x501030b0319110603070c0201020601062d0302041205010b040509010e120d06051c060606031e0f020705030f0c101a1e030f0d09050a0815040f02061201 67
    0x80e40c040e0020540da4101003280005020000c2c02012950704100e045000540303140d10031646003002c102560103030802e5580c10069079024003485e092010389840400d0500d007c0b198200440080592001210800f540c460307016900140003080d0540d50340c43c118500103019100c485d0b400c40c0514a0440000c0d0354030014014120310801c3e0b00301030b1202926102c885206a23000c1d2101040031903c820780000d25403038482c0c02c000e10200540e00b0110301800c0c1e00c0c3c5174043d5035850b40a00105800d04800d00024109040300070300300c88100000103107050841a03000041d00034914080d0140c040880c1d4401081140d5005001c242d56400a640305e1030380d180940c808a80759070b40c1c00e016822410b281100c2600f4868004100d01e40c20940c504151603400c40020301e4280075550301030540d08104242752240740c00043c5c02001c2c040c1106d580c070085042030741d504d0360340f8190076410030440e104030b0200b02801049042c5104040d0003400780361752400f10a00c80b00c00201c080c030803044403044040074100500716595 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 634557374 1250 634556124 634556141
    0x20c0c10080105061e12040318080d0e0307030b010f030309060804030e0f0d0210020c2e0c1a0a0605010f0c02090411220906050f010b030c180d0609050106050103 71
    0x2201c1452503401c0c04240030441c1c1002125507104201d0160710b42c898000381c03010b020b08403a61805512245403034540246250b012a03800d071424801c0030303804e101c018070110b86615000000c0c0b41c5912001d24002c0068540a826030000d041003803008008140340307004a5460061300e001e52500d00309940d49040803240c941d01164003074001140d2401a002c0b9103041030001c0b100034402044d07129802050b400145a04500200250241c0d0003d0449130050408840034080c0003006400104100c0c005c0c0524810b00e100f0345031030410000203940d03c1c010043c802090300000c2508140e404d52034036203141c80c0c000905040c0500b501186034800348802d581c1c442c0031103695035a80a82204859262983c81c00c40d43c002c1000d50a600c4012481c005000601580010101c5580d0135000701e800945030501e502101d10103000700300702100800c01030000c02201c0040780e411028114030740759100d0501459860004a000d9901d51003402030b0740401c240b01707440e002050400d01400081000390b031b03504015800c03140601c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 634558624 1250 634557374 634557377
    0x1201030606260d030b04020f1c0f0c020a060207052b08010f0b18040e030d020322030c081e040627060e01030b0402090406080604050c15030a0506030a0c09020c0c10 72
    0xc0d44649604c80e03003181c01102d801810260504d000300c408003c194001c020007044643e00121070b0103e184160050415103810301d0010407500b600d4079030003511140c0c40b40c0050001074000400b03004000d010000404414002e102064070303100d40c1c0b0580301203011034170795203000074024074004030b0885800280f20080394550a58180340c003900205116030031107100c0c806a032040d42e50543c90790411007400207040003440282d00607a03030b2138030201c01d8a10450502402e114407200303200c0e10703000a420580e030750700d1243c0000405071074510720446000900c59568000407035900209000070600e401140e00740503030350400e6901d5004180d403040e0440e0b04041d07201e0300d03002601c0301e01500c0540d40a43e002c40b40354800544094508030004000c941070310303081c0c2c0c02070900760321540800043c03100074040d01d41c100104540000003510b0080c103c1e0351601000d001118034503510310125803035035820003004040780e07405508183c0c001d0782c0b01140c5000790019800b030035150140400e200c10529110b0074886005005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 634559874 1250 634558624 634558633
    0x90d0b100306050c0a031b1d22021c020705060c03090705180403022406100905030102041d010801050606040b0d020d0f020d06143010060603180c03030f05120103060626 74
    0x1510702200d0140184000326005149c1c07131800007040010b02c0c0b1012060800d5a400740e076641d580c080f0801b681d01e160030320422052050101c18001034011410603082681d1401840d01c80d100c2600702802c09203d98043e43c0e015409070b162034800c03605007010030f102d80e009809481380f030540c0071741100744d20319046031621000c82d240b40050003030324003950389210303200486c9840d050980c0c64a001c40d08980c001c4e04524405041802407200c19004201454094800d900003448141042c401040d800d000e0703401811205c1034003107102d4500000d941d050342c102080d0301e0414403070548210109402540304a8200d02003d0900c0e001169080003023813104800035000e05142c40819076544588030f000c01c241c005002500400820118050b42044681e9100d20304010000751705143c400040c08644001100270480000303a00000701007280108802c0880390181044450b140304650208c44520561203424000c0c03000000100078080d141d8065810f641071940d10b185ea0141140c0c004a032403d82c1d40000c00c40707501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 634561124 1250 634559874 634559897
    0x309050105160f230d050304110f18010906050303180405090708060403080106090609320a0f2303030a0f14040303020607080705090d0b100306050c0a031b 68
    0x81000140081052401d010b00e04040658410030211503104003a038004010400c0710000758050060003400d40c1108008114844440314090554040144050314000041d10105140d032644002075901050060800714040d0700c00c01505186c02d800e01440f2a424a05000807996080000132144a080c05c0003100054150400030000684030003030140040b809050300010300c020003040003d01583c40b07a1142d045540c1054002441b1181ca588410104089620100042001540303010450852001c580d41d40101e12050890b425903c0c441094020340019800140361410030002001d907080450514618440051060310890150040d2989600200140708509025041000380480da0b810940112010f422000e031083e000b81d0710075009030308032000304010b450340070301c2503a440421810014113080d0000c0105a440b101280000c0c0020005030128820011a00501c001075600400c2070041c2d2074940070b001140d4010a400901081c20802000580442d00410761001405075136001c1002a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 634562374 1250 634561124 634561127
    0x50c070204020708300603060c04060809120309160e07051c0e0313090507091a1c020c07060924030513060903020d0e03240603420403090501 62
    0x602c9a070f0200c030010300030010b045c001000c482e0204820381441c140e039254861069400c10090744014a698440d8000108000318040308070140c2c0c0c166441c0d86880200340e43e0300c90f400c0c1e190240c0500301400c0c031080481001b044d0794002a03100c41411005401d00308141c0da8840d40360b508001521500d0100c3c409002c0b4650485051962184031006107102280103001c4e0035040c0c1c00c5030701c00885418109000301081c0000c00302405140d0300020b080c68030401c41807a15514108210494034410b00b2748400090790b000d818032201c01b00c440301c20380306021540ca140e042e802a0361a50940300e01000310300b419100040500302070756110b00080c0307092207904589007000c4d030480040c000241802e0010b080b080340c10001c41c1480c440e2844042c80b940060020f0780c4070100182600d2080009a8401ea02c20102105460304540408a60500750307451849903807a000002410003201d50200401d64201c0076aa100316501d0402e034841b44915074801031038400b0300c4480c01d0b490380310844028000c02c141c1d40b0100a9035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 634563624 1250 634562374 634562377
    0xb0a05060702030a0b010605130b161101170108031908090d03110706020c0d09080c01020a0b09030c0313050a06030908070f14031b06180d0806030709051306060504050c07020402 78
    0x42c402020360301c0b40c404036682c201d1031799803c0e00200c0019101107410080b0311728070230b4007a02802c00700000b10f00f042c0c00c4000c2e685203183e505600604c42401089901c0d6564040c00403400c004411a130100499a114010b80396070740c0046044004066580d124203006a000e04d243307901803402d250141c0300e01058640305401400700396042c1040f08a003040651b0102c0c4091018001c410762a8014284e2900e03103c40c0180000710710307000081c1c1504003801c0e40586a0b000200b00100f06c0d0310030368017243ea5464104841c154000d6445084c5940000588512141212040c910566004580450b00561604c008a046803815003008000032000c10160010445254404101d00c3c803c1d1000c01c511481e0702d0314182103420003409205c4280e00d152521400e2042807100a6105090640c4031a000d0f0314000303000c2c0c6d1166800c01c0c190510402c0408180103403400d000c03c0e0050050b880c1e050205040c40c20001100c69140c8406652070f5150200c0455540381902030f0b2406510a845164108081760302044003d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 634564874 1250 634563624 634563637
    0x3061303120e03090a090c02010e190b090a0b130b070c0c031b03170a031a0f10050c0a140f12030615040909030207030b10050d0b151503190b0a0506 65
    0xb44818018200c4c143d440c000300c4006001e248402007a03060f00b601c0040d00396207120b01508441d0f008285140380d4070701c0040104504a402ca20024860b48500704c0c0d59042c06800b183c041c0500310200c040000c0021042020741c04544520b0050600c6e40d56464100e03448454041c00528103100c2c500b041012038000c41d681441c001440c03040c4550076580e50f40d401d40c030120304500c1005100004c02c5220f0304c242c040c07161030860f0103502100041c81801303000180901c87d1209041b4031a0026000300610a0b01c54801d840c107541080007100d1841980f4180030390031200d0f8140c4940b06d442040001c0c0700302da41c04200b01041012002c4102d0031519075004000b107030381c2034210264005009020001c1c886500703000b40c20f406070094014207252421030802c42082140108001505580c0050400c210740341e000034032000030b13001080605681c41e11290300c160400030010060740030601c0104015955446001103024038491291000c24152642240742aa421030003001d50003c0401c0f0300b08058109080200300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 634566124 1250 634564874 634564901
    0xf0902070533041b08120a140d180210051222022e051303020103150506071119080c0d02011112040306110c1905010e07030308060306130312 62
    0x610521a19050380d02c04070844094030300d169580c03070311141500a0680007003d00603400140c2050813a08480740b070584541c0001404110601d10002c1c0803403088020380f0300407070300050148103020f0005d03194207100c001b015040e44209068500d00f942d0f00d000b41c00307c407920b402c44580c00180340d4a012000d815040300941811040011a0034400143e85c0d00307880001ea410403800c0c2001e03411200407650b40c039a940203413200901200704081016242405680001c40b030342460041000d8456064013060321070250720098002e05d020800004001c82d60202030740c040000d4074401c85240c02010100e40162040c07243c20000d03040400454107905007a204401401d0040c10071150b104000324139589407600c0ca50f11014400740100c2c1c1803040001c0c5004400c0748500f139405141c08c20003900060341e01e44c42e145d035101e41080440d800c0380041110039000b03804080008000e6449045c1d9070300b03006d04208421644203109004010000d00007035818405080d41a4150b81c0303c504448400c58118014170720300f40c0125 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 634567374 1250 634566124 634566193
    0x270c06030c08062e180b0304020d26041404240905061504080d0e01020a0c0603092f010905030102160308040f0b1915050105090f040912090f09020705 66
    0x284c16900f98041c1c11082e10302c030b0f9100d03965040d01682d4400440c2c0306401007201c0318420814400580e413216420a1540d41021060b2840a6010b00004140c1a4062444e00400000c5000100c4800c520005400c000065805104011494581d072500004d10b48035071440455038201400742a216500c602e41c0301c00040c050800320350a84080810740e03081607007d184e6641c01500d100c440c00c0d9000d003170b01c4141c000a00003080048160f5440003071400703a40c001c94003010346e5000710b4800e105650602040c895585080c00c2080f010742c0d0203241501c004610480e000c039034048400900ca0505108407580303184040c226626690888e42d007103410a0021b03205441366002159840086034503000310501a41170300016480d0080329071340e8074058818000c4001d01d001c8000c4030402469821800322071055508565810311040021700250007825400000f51901f0111100740130300c140c0200315401681d12039078a460a9035030702e1300c511007607200e1500e008110b5000840c1054404041a40060101c0801305211 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 634568624 1250 634567374 634567429
    0x6030c03020d2c1501151e0206061c050601030602090a0e0907170c010c03141b0106050a0b0a020c240c01050f0603070501050f030a270c06030c0806 65
    0x4000340d07640001001c003030b99141214480180058000c1041550742007001e4580c8040c2803880c0d40d0131800500c00c0307501040041a00d0007419220f0003025007080c0c241290882c90421000b0025902c8004440ca03d0041065070010701070b03503900310030501455074494000c0c101c50b825035450754080d40101012941104000101042000040c03141c0e51081c03052900401ca61403500da0368654000c02c918030200c4580000c80412603a90307215012282a6405007011150943c1c19059070f1481c1c82000c210a00d000a11320383c01c0e902034019008041102c1040b600d20f0342503515042000300b60300c554140e49000da071021002c0000c60400b40c012041c440140d0300400c0802000000c0c0002941c064400d112190b5500c0e010807a406421070380881d0007410540042c411141882e0004c1c000740304040b540000c001c00400000e105113290b070484a9000b010f1005003051600c400e002410480725003a046404c0c1805c4400803490600c2131280b4542d00e10306540c0c2144580b00d00c01800344400500d1003400742c420620608 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 634569874 1250 634568624 634568647
    0xa0519170f1507080c03010b1b0c0d050a050c06030108060106031509020304030201020d060f06120e01180302060703060902030f01060e01091a04080606040605060f030921191806030c0302 82
    0x620020b0a0b0303070114540c581094000c10301000100880c074030305028001480b46001060540720441100950400c2600c0b06480c0c41c0d16209042c5609a03014885407486000c105c008035808400c03d1040d011945d12503a0707403081101c0c5000900030302c3c0ba55480000108a90351285d0071084e500c91005c2c0046020f1611619480142da0040b281030340540c0d0002440020701c2c03150310400c8018858007540540d81c0e41084c41c000c1000711a0301c00b0720920740e2a050725812403042903101405484240c4c0b08070b541c1000510f070107900c031182110a203007c01d1400c00e00003003001d038034001c0b6842383d000e90308030356402da003030200a580300c4000640f00d6042003e0104045110b0000d071072000907401c00c995181e9105d42c134001209207845d00007044903018071f0614500300803d8403202d007943e6000b40c03142c0599407640d03580b4000c02e240100c0103802804a84482c40b0011010419100421a84480c021352070001c2c0c00386c90701600e48040c4d48048e0003c001c1c0c502c40400003148280c0c0480b1202010340340261070b020780c2030003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 634571124 1250 634569874 634569883
    0x13060501030305180f0f010f050c0d211803050706090c081c0302120402061b01020d0902040606030b0f060f0d0510290f0a1403090109020a0519170f 65
    0x2c03000304070009218100c228503040100c0f071181e800c0341c0d8002e01824400c045550440280142414401c2103501030814902941c265180323581c0800403213100380c110790001041840c0300c000120344101140140000180c140c003640001c5e03007140130100848841941c040352160702c102c40c26114a983c81e000a00000c07020b0340d400f1f0050603000700608002d04052403101c400000b00e1018001c5c144100b00320f201e0b04941c00e42d2941d000350103c400c0c5482d00080540346c0500700140c80a980154400941003170345140e60741c0141c16590003a1030401505884240940031940005089030b4059280b00a070140c0f80b034108004c0000c0300b8070125244c2007115445d500000c0d1032056400c03c089005050301440102d407442c403070700d0f003a42a036080aa040d201c0f2208120403480344be00501708006001501807201da01411003031049442000c031307003966490002e10035802414280c0d0300303e02c15000c100000495140050040815482d001404540704e071901351906c0c580500c501050109018960001c4d100d43c0d030900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 634572374 1250 634571124 634571129
    0x40b22030f0e061201030b100e06040f020f070b101d06040914011a0405070203120103060e0a0c0306020c010b2202130302150307020d0f09050f13020d09030815100813060501 76
    0x40c1c84d04d2072941945000354003070900401c2d080c1c01d00101403080111828820010350400000d60f4001003440856032900b019101d04042a68074100005841c42000b440680b01442964144699080161a42411510072000400186400d2070b00404220b00303250640c05202141c2c030502c13600009908849201c0e0030740782c4074254111b80b0440080100c4160a190180740d0b400b81d07803840614a00088030354160440030042c0006845147d4418000c001c0c18030400c001c3e503505401410012506603280350a030081d50090000940550038040310000e40d0409200c600c2200c5070750500b0700e181d906410146402900a03038060b6010300c045080c00805619400190480aa00c15503001c1e03481c0352111020f440e0080d0b02002008008a00c00d0344481e03140d00400001c1503950803984090f1115a440004042241c1300c80442d450310b10000f100c00070700318140d000d01e400c00c0c4240ca41c070000d6900e14960020201c3c8a240c0e09401c449080d4136050b11500c070f5020254440c0c8990b5880110070815110b1000300e9200b42c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 634573624 1250 634572374 634572397
    0x601031d0703060506030604030207061404030c15030f2d09020409050102030f1005090a090515010b0927040b0603071805061c030c030f03091a040b22030f0e06 70
    0x503042c02404258002d542e80000194020300b01030070181d500075038a602034891141003010520907060707c000d210781150300854208078007020440c0c07245a00e0075480c6101143c500440d1a00098034544509030103002c24094005100c0005074440c0003c0c5150304a0400300e0344c001c0c80d0380e1408500140d0f11032140200042c095000141c480c54041da00c0103d40c60054000007450741d9198042203142e4501500e158092010300001ca40c060041c50400c0c13a0035001500307409011155800410800440f4010b800c5620084443c0c1d524180c1d482411a40001c0040c1c141042c00d99140000703020460304901c00c0d80102c0054100d8080503640e24040300c0844403550303448882500e85040c462107151000d40c07441d4641c0d101c60710f94188202d595000e040360862400c001c0610402c0c52114604d203000743d0100000395000700f00c0d800f0b102d0450b40041506082114111000701e210380201d0b4084044180c806d046100c00c014171026040191801d035500140303c0a41400c000001c952400030f03845510213084221402c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 634574874 1250 634573624 634573633
    0x403021e0d0f080c0d360503040b0a0302040510181406070611040f170601063011040b030a0509030c032205040603050f0f010e15131209090e0319080601031d 69
    0x80d40d05000c65100910b520400074406c4108981c003007400801100d04581b062401c05070340310309a010540207409585c2c80107500240038211105042c2e000100b0889416030001540e9220391242840110807103074088481d000b0506005410000e4143d0b4400203101e0884c010081c10300e41e43d819101224181c0d5004078035031003501500b18454a008010315070140c1454209000e02600d06a106482c3d4035103500c02103114450503c00562207103150344180300702018984619034990302c860020340346038020780c1c8040d681840d20000446290010095444061032a0302540c50300d00289081c0509207600c4900d039161040ca40000129a07945200d01001188503c0181c1410700105078518103000407160142450703410301988229420010070340f510481184030600080b62034482c1132044080b06000020000301c2c1080c409441c0c1500012100202c41c0d56a01c1403080c2110007250f00c7d120300402d02c10b107000041901b914200240510310403940302c0010315001850542004e9051020909a9042402c5411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 634576124 1250 634574874 634574921
    0x312070908070e040f08090f04021605160e040f0614010f060206060415180207060c0305061c080d05090313031101021504080d1808030403021e0d0f080c0d 68
    0x101841080000d024001034081c3d1490262200320240752004070042048800181000e01e030350f9000b030724080000001d0011521401042d04107070040c0791030401031300e4901c20f81d00d103100103940312044401a40d80001d07036002581c880390355104403d207180c04225046612024032803013a400c450031203802803100c0c50601d01a1840e20002034208a800792000b40510304014a0000e5620800b00103800c680c0c50031154040050032401c902d0081c05881d0000340b4035401c04141c800c1150b8580c11040c010b0400700d0364009512580e001004403024400c800800001c814018070321140721660116621940038000c0e40e1402c41c600c000348140d5103881d0400c4440071003084a0000c02e5904201941c500141d040f00c45080d41000e8607410124003038410645000c6403070b586020101e02a000640040319804082036441e402c180c90042e442e15a08411841205080944440040d0000500c0d00045041d0b455004881d01d0303001040399031810051524051030010403041d01d1100003840344503107160666880307211411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 634577374 1250 634576124 634576139
    0x914220317040b16030b0f010f020708031c0c050c0d0f090e091501080c01021515130b0913110108041110050909181b0a0f09090201021509190503120709 67
    0xc03c0841c44d040520b0240024081e0b04c86400d000d19003c02403c2095100751030f850100c0c50020190491040340c000031405004035056404012200c040325241482041aa038008440602402c001c80d010780d44003005a40c4901c1c010f8105000694951500303001480e2100c1000300090f005036450a4182c2c0000b200c2e80c0c0503010f03148060b000d400e0a0010785020400d00b80001d644812154101d00c010b02010301155802c4444001c1000c08030000d0000c92510190759554001444c4904029000d02200070010b0341c11442640034008036580310031554001500030004680000d8014011648625220b04c600e00c03943e510214030b400140d5a641d42540c54485030184501000c01901e611500a07030040c40000c0c0910214595000e400003e03850101c075410000010032600b0964041d04030913825840105200c0d620b50842c15100c0d0003038085071084500700329590314000d400c60b09100181c102c140c030000407a480d1384030080a54054802c680c1801d1500014150703100003501d0550104101c80c2c410080300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 634578624 1250 634577374 634577401
    0x10b130302060a081503010b03031b16061707140706050702010915200406020601060503070203091324050f01050901020a080c0f060f0c0d020306011b06060914220317040b 75
    0x3004190000c2c0701c00c10614010994a008110600000038018110302f1149182080981808180c0304c1c80d03180c48540d22600500703099009000b04911009282c0090f1200e401469000c0320b442d0310b03058071860100a0780b107410040902400c002c00319501c91009002040180c8506055480f14180001d0340c000709d0ba0f03000490200004c599140c141042c00100200760b00400c90504541c0182020350340c030f0303035a000200c3c114880d41c40f0444e07024010100f48010036405903c40c001d03903c2c0c0c5c080100c03100c07020051610502481441030540c0211645102c3c51154441d4000d040d23864818011540c09070386941d01c00815070408844403d1030362022241b105140410000503030480a0b011026490707003001800c002ca0382c810540c80213101a000004129140d208250100400c83d840c3d4807002c1100361890310704042c0c820392103160701c03650500020a404810325542c0c60f00842c10210710141e0604880f4070602034040111041d004e02040407000240c0115070600b6500c92881403015114a26080c0306030541c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 634579874 1250 634578624 634578661
    0x2100806120606030604020123030103080406030b041b14040e0a020703022509180b04060c02060109022506020708040b190302070b060f06190201020301031118010b130302060a08 78
    0x4a82c0300700e00340036441d24041900b81d003140d020320f4080801a16400c00d04030044186001174071a150000c00002440805da02500503a9415901131141c009240200025145e4014481d15002c0c04400c010b03050b03d0140e0081c104922400c1c0409080580c2c0300303401502040103c0e1182c02c4503800051000c1007643c14801c4044448441c000b04070440640b0009048941107400b82001e80c507640d805030b0110400040190808940c8035095620030301e0030f03250407005412a40010f0303000d44a180c0004c9020a014006d4910b5651100c1682a81c1240e82e00c210351141d1184000355051a401c00446001c107103000024000f07040c911808a55485590132994031141115424008051061041c140007520168982da003000003103d0b03503551903c004001925504c54480c040e100349007106283c081240e010b40180d07040300d010f907080030fa030501c5000c103100440348525041101c1e150300d20011b01c2444c0c55403020380790120864102d0008142c8039804104150b00c42111580414200d2080281d070604100d0801103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 634581124 1250 634579874 634579909
    0xc09010b031603060b03090d0f08090a0602090f3102161103161d09030c1510090504030302121803030c07150606090e0714070f060902100806 62
    0x515858a040d51905000140c0000306218800081d81e0180d4400e4000401600c141071416540382040f0300c08070b5541302440004800304000b000744540780e601688400348651240c0f0702030002500300b56906002588144006a84582d440110003100e0f1600c030b82174141e281c9840401580400e401c0c800c401c040084e5204c054409004001402504a044e05868201c0b648403503401d2081001800207801c160f400d400804940794030740c400040070a4000480300c0902d035180c0602e03103d03441ea00f500c0341d243d02c1409100011940400004414669111811070340a080f1044d181911a00d8000503410707150140d40075800607801240ea00c00300d0ba80004501c1e0030800e08058801641c0c02040c010303031071b804014606081094046008001e02003400189040c3d46c1d40701204000003a25960060100d091900500c20003140e1a00045d48080c01142d20054002c40311500c03508105981e03590401350f90700c8580807122030751a400448010384402604403400d038815151034075940391403010301542100c07889030b584 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 634582374 1250 634581124 634581139
    0x2160e2203020a02010302160f05010515062a0f03040e060f040902032503050703050703110d1a071e0822020d15060305030a0c02030706030b01050316110307140c 71
    0x82c1c000442c0c10034282c0c203090150310b41040d100c0ca62281707241d02d407001c0c042c1405102064208441948000d100703201c03041e001481120100103000d2135000300329405104440141c50744060202a00c10101440340d41011a0040c1c0714000e0100c3c11600194031003069800c020b4140820740c84d0107070b0702c903000202c152410000c055440d00009c0d543c41004442e085142004000303520000241e40300c1d03601960708441210380940c0d8a1034940c0d80d840c41440156182c0304c03c16001e00840c40c0810141030503d81000d0000c2000100c8640407a03c0c5a01400d0b03041400054482d50011100d2a807017440300400c1900c54040306d24000d20b004980400e8480039250305000035041e000140e8450300c02c014255040050f80082c0c0500c401e08100800d06500050820321010036071103545175010626a17010362080d41952407542da1660282c0640306510039460103c0c00610028002c44e200ca19007084e60419841e00318030311500d00200d142903921141c0c00f13440881790b9080c0c16203801810030640e1042001500c600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 634583624 1250 634582374 634582441
    0x8100923060a0e010e0a0b1605160602160204180b060a290f07081803070f030b04050109020a080d09150e193308190c02160e 55
    0x1a22150000e0800350602d030345071143c0d00151802d600004519030810101c41c8040d195003440070409000311050032000c003448812a200900c40d0050b81c00c8040c4d031041219400040c2e58655010707400180c1070340854202c0b0003000700503995601904c0049417824034481901c004600742070ba203101009001c2c600440003500100911890a050b40d0720303002c4003210341c0c40d0021031040801500d10035107020360a0410b01050220501c40d541c40100b20701c60f20030684800d103044c04410702d80c89000720b104da80c200940d860302c00c0012039402e600c01c5a201c0c0c03149000060520b03040e800181481c04175001030741e880d4860110800a40e070810f020030080c103903807800720701040c0107070304000d008140c064040d6008102d400c4441d010344102d0250f03603000d0b00c52040c2d0324445403400001d00c8000c038917600004140406214000900c00d0156541a010720110751908440080d0309162801902c0e0328040c80c41103220341c42c7d0205000d217200d508800035101401207580c583c105101e200d803446088289406911007090703042c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 634584874 1250 634583624 634583693
    0x304151a0a09090c051201060513060509010b030a0213061d030f0a03141e0306040b1c03030b121009050c10080718090203040501090201090909081204020a081009 71
    0x3980704880360341c80c0c0403c0070f1045241c2650345021603030040340c02a540c0b002240c1c1e1100103400100c03e0f40e85c04e8480c440c035030302c0310f1100c40240e52851007440e80010070f11006100707000d01440110b5121440f400c0c054a80407103080460001c1d44160301410000c0d2005194102c80c00000e01c02c0b5065031800c80c01050701d00003038602c0c50f40b56881c042c0020140010b58031130407021000001520384a07010641d06075003108842080800703075441103403414842c910780a00d024441c5040e60480310b001c24100c0ca10780c1000800e0350207030024030032414015403104800f100d501c0c0c0d8100400c405120100111404580c0d403860303140403842d00c0002d044480c40307592a041014a050382c0014500c1d445940380c5840c0c58400a030741d91018071002117401c0300307404500000400c41440015003180b90482e200faa2540c3c80ca0340c0c0d4903d8981201d5030300a00604e00d0600f001410500c008440d256904280014175004003265149045440c081c18a00c0780035a0648a007218014041400905024105502e041c8203005202048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 634586124 1250 634584874 634584889
    0xa0b04120f020901080703020f04020a02150a1506020c0f0d02030a060b040219050705060129070204060b0304140c06041a0d0905160e2406070501110304151a 69
    0x604208254019614000d000340000010070340c6401038281c0c00c071540c4680720140c0301c02c040c0c001a4040c2e075107800e200c2c010303040030710072603691900940c007411440d07005140700c80a031103010f4884200a0307254a50f040043d10300003043c0c0018142c58000b04243c00c0e21005004070030781403440b190302c20700761010b101d0090f0324045240c0c40c0b0039510a1000862415849c0054000d01aa00d603154656090850000510341c10100910400c3d0064007198011b0b0390310324251440d1031017642d03200384038035038559013201d004e2416001c1c140740762004002181d0070381c0750120000c441c1c0044400781c1d40c03440880d005013a01c2500f0320524030040b43c29111649800e042c00c94448442451400381020300000282030340c05000381d94403c4d8980d941c4002565604040c1020b84581c108060140e40e03c0c5202c031501055400c03202800c06504031070840000340e540d00350320f02007180b607402c0011f0981d03030b40d502c400c0c1ea0f811145900d4000c5205070700c12a210404100e01c080d2480480300d200c81309038032060001280450b01c3d079038000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 634587374 1250 634586124 634586129
    0x1d01090c151106040305040602062a0c3d09020a0509061215071101061409040c0b0a0903120503040c09050712021222030f1d0607031d0a0b04 62
    0x5542080d10034651002ca640040602c600e03a550700905007440b04059016009000b203960036400c891003500c0302e250001c8600740d000b0314801c40c080c040d259203c1c000c0b8500050002e44010760705454100703410341000b510708161b80800a03500b0502c22810075000f160313000181020034480c08108003c0c00c0035400b103906807040d4015284180500b80009103550380e0741c2c0c40406030384040740a69020030712410720320380c103c20140d41007400326500418a03003081c1c00503c80e80d0121105100020a10a4060107102c030a07400940151000071280c1c4001c10803421510050440f04141d60351110075501e9414140a4110801f00050800c0420810b0101084094402d4010754030014400242c5407244031059641e140d800c006140c0740d0b400407412681e1201124015486092500d1070459484100d880e807100c185082c840041c0071a0303134038007000784841c4940080f0942d4000d0b101140000c20700000003541301e4011500c2100010100e40b800e0240360aa001034810040c0309803019a41c0700d0810245102301c0c011130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 634588624 1250 634587374 634587389
    0x2612100f06141803031c0f090f110117090718021c0e2103040606051c0602090103090b04080d060609061d04090219090506060f0a0305060111010e011d01090c 69
    0x41414140f60000680151090b48000c003181c1c0d50780103ca011501010300300491079109842c00e034000301c903400380d03005443e400c40d8480b910801d0f40d459555581810420130792041d0400031000990440081412080c1c4c0c019008200280602443d164481c0c4009000c002c0010590340188400131200d0003c54004654941410010440407031400c5480d141001c1c8403207180c101c2a0810744180004001d100441c019030040c4004d2010544a2003403101e0051402001040324200040c00c0d4045101c1c0e40c0500800380052401040e041455282e4010b030301d000780c1d41510901c40c000740051001405104400040809092032080145083c40c0074108043c50a09000c80c08a42241c02038160b541d0b07440304003da84d00401d9032003070300300322a6070050b582601c0c01800d807050700e00808902c05180c402d040e0780c171458030040c4040c580ba00d4240c044000c1d04002c6d100d98180300d0b00c0390014140000a001b0318003c168504000103444105610424101e00d42201c030318211792508140d0303404070b44010140b0b004d48904 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 634589874 1250 634588624 634588627
    0x20a17060112060f081204060e09091009080a020f060105060d020c0c060d06062a140f010c020d0e1f030b01180e0103060501212612100f0614 62
    0x4910050b00e44145003240b214403540f61040210302819144039007016035203210121030b0518a4901d5445492185000f22030208020302c564040300d26010094035881441c4409450082d5a00c460300d00580300e50b014100e507400c102142040310741b6410402c405400749454000d02c00c6502d484081030081c464461701882003078000400111403d401c0110100c1400041c0c400e59075000d041260b03034001e10090040c3c000041c206c06200c0690310344c0c0c0d42400310600e65a10382d01c01c6219a940c43d012031149818582003680600a001959980c080c8a42e44010040781c0162068085841c40100702c0c40d0411030081c03291071505030780901800d8059030351049441d2404e00041d10a413072801a220b44800a0501c01d828140074000b08200b0b0011162a0480b031044c0b01c10b0100f030340c9401c0320003281444904070000c60700480d00e400021810a07050000a221494803c0c08080da4018100c0142e900820206144904030b01c01c0c0300e401000e1400d04d4000303003c40c45004030440d091640041410030103c200c02040f440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 634591124 1250 634589874 634589881
    0xe030a080609042307120510061703090d030c1b03060605030706140313081306030f1109043305091518060303040b0403030f031104120803041e0503180301020a17 71
    0x60070000398010304402080d00706d1121283c6401d03650340031007650001e05203080c03903000144e82c1000741041440c0d91054001d182000c218900f40b010b8030605034010740410462001090110320088000f696001c5140411140a821814120156000b5a010f14042e41c4907000410503035070300c20480c1148103000d0a105640fa1141c0d620308048041030703c4c3c090018240003412010b2410690401c0d0103c5400303407014801c4031510f050200c102c4041949549504104100c02800ca00d040d90191001040e1102c1051035056412485c041c00340c449440d1100c005900d420500161501060855120748080c440c0e604481c100404100f205901441d02c0301000d81c01e40201e1250b40c0c040c000e0f40d01500b40305080d1902d4682d2411f00a040c0c1c9210501440402c2c43c14040c0d0b540d01d007030b0404503026609401241c0c1e074440811b40c0d880c100c60307000900a49400c02840d20410b05402800d05c603100079402180111340b200c1c1348004804021070041001403280e0300c104000202c05030018180c0791290000403481c800c655 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 634592374 1250 634591124 634591193
    0x60b130e151008102108070501060e0a0903080c07030525020301020f04051809121303021906020d09030b0c071401090b150303120a0e030d0e030a08060904 68
    0x4411003800d98040a1040c101c0b18641c0e010342214400e0b43c0141c1d42c68031050380c4034071441a103004055451030703c1d441e10202801103002d540c002c1071458410070001031215541d0116498190080d50964117241d212401c50003407550100389582c010400c0054a4a80102c503540900035110310304d142070b920504c101d0403000c070740085071664007141d8000d002950baa0f40300e4044240ca6a1040c0a038500c50584198200d0610104201c0a0b100341c980000801e200100e0a44103a915040304c40703a404d0047c00d100003c00181c85120040000700d605001d8004801d0416502908000d420038610b01004034000003000403c4c088000e40380c01c2a102c03070380113655181c035080c2940f032a0718a04880010350f017000b10034010440c22064070341c42210340d00d10151408006900301500e82c49000b9003c0348103421030b0080762044050f40d0200303640c0b048081c01c80c1e15141c0ca045080c003e032820401000215000802c056108503008613081e40d106204580740c0900d4581030703230f030200f85681040a541385a111124110702a4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 634593624 1250 634592374 634592401
    0x1906030e1b100512070804060e0a0b06040510180c09050108070507060c090504050f040302011d100b06130b0a02120a0c060c11030c0309030d11061305120d0e01060b130e 74
    0x4c0083c46241405141118001d8604203050301c04417115481c3c0255461a450b002c14180c000c241c7c01002480c0c1a261241000b0140202500c1d00400840f030313220016000b00d010080c0c1100090a100111347e80808281c040c014542a52156051002c15800c000d1929802400c903030b400c0e44e000e400003c21003419001140c050055400c411781080c5020140309030720b502c07070705050b1080d4881d500a11071000080014008507054000d450307084d41c00190400001c03040ca07001203c401c0d002401007030a00e400d5a0013184403804d01d600805900100007034040406a0600000c880c0208211407585014583d50004088009202e00540403940c0c4041d4001000e21030502700600c914040c0032642c0392191441c61036100d9000201c0340d482882401000c2600902a41603c00d080510380007070200c03a034070440800c501c0500d100048030340f0300520240040a00c12000a0510268a4640040c030101d2118000d4216000758021807410718003880599070b000c0d0f1b00c4030207609440201008815a4a80e0744403000c41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 634594874 1250 634593624 634593637
    0x150f06030a150b0402031e0601020309180406090206071b05090c031f03080d020d05060a0510080408121e1308030112110301020a1713050a0303020c0c1906030e1b1005 73
    0x4580008181f0400400020070700c02c204904070b101c011070b030b100c50340160b0b9a44a4a01a03c0d0025414000d02c030300c011490103510392241c00344c8400b140000d2940c3c0050011381c010301d801ca80003542000c140160700303070742454100070349030aa0b03640d0300070301f8414001620f90000401e100403094107449a40d4558070461180c10003580d102c1605500c1d07642ea001d00c41c0294114904040c2402e20703020000b04e0340d1800415410484501810022001840710f10031103407407500070410b0b100b1501c2002090583e07428404814070030700c81c0c21103402c24281d2242e00804d200202070a4110420b1103a5480c00100d424942201d04441c8480c450b40c0c401078a601d403002003158202202641940f001c20215405a040058540b00020441c0302d110190748014150100d0525180040e02d1340c3d2040030f0500c0041c0c001d40c01008801c0080c0110b808a002c010001072600c4044050342202d0301240c0f00402806406004000c2c4140e000b1002d407400ea41c0000c5015402421020010b01c176182d03090680701070b00d01400c100c400e0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 634596124 1250 634594874 634594879
    0x809040b041409030301150c08040603050403170a0203070f0f020616090305060415050105030d09090f02190e03122d070b151804120e12030c150f06030a150b 69
    0x121894503c0c2c015469400034030070f031170360001c4d072022004d22188212030303102c6216404048030b4205810806c00314010200100308406212050051149290220320b600f441007042043c0560f40c0d16140340001c100003007a03900031050040101c111001240c0101d2041c4c2e2143d00f071840840d868181d00c108485200b003642c40504107009801c284800e01601c0040c0b4200440854001d00075039a03610103056440ca605055540081c501e100140504030750703900000c00c00180300d8000f5003407030704900c0da1840c0800301d00142d10205a954444910508050050020b44003000c0010381c1004107480c060b0061101040b0800c02c0c1d2200c0706640044080d031031043da010303290030810b64655071401c1488881a0a01108014800d80c12840160501c407180b281ea113108075840088030380404445c1805803030310584400040d80c0024000c140100d1003408201511000303ca210042001c6030b002c064120f0400c03800341180180716020820442c0648000a40d00c80300c036804103585c0420003142c2114801429904641a07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 634597374 1250 634596124 634596161
    0x12030518040b150301050a060e090106120b100302030603250e0603101b1e0e060703090510050d0e03030105100507110d030e01120b010801140d0501050a0213080106030809040b04 78
    0x20299040f0601031416500d068aa0343e50007034440c3c0003521803660f1700c001c131684003086100502c4881d1043e403032600311403440880892450961000119224005172290000a40c08001c0249620b020017007041e907441044140311040b0b83c54034240982031a0b5004009041c680c1c8000700340c1d25202081140404a00307900b0410001c031000c8070b014501a25085804000303000103000020581005000f40710001071901d40000600507001404040d8002d03172002c1e024402d03584000102911903604030703060794595584075a541c1a291112000b00e540601207066030380e0081c0014400d03034550082540c0901c9550408584403c52840c10180c1c10b03540c5d40074140c10142c0130340040c08046c4c0140c0322007412003003629208011040305400c0d40455038200e205900083c0ca0000401038101080003062000c0c0c00640194a41080c5488890a444c2c0c1581c6800019500041ca41071100a000e02d00002e08030f03210003484060304d9130300c03000303524091010710034440c680d00c0d02d1184440e41d80754400703121082004e1940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 634598624 1250 634597374 634597399
    0xe0703080c0604170906041401050c060a1d1f0506150d0c080601020f0a030e01020f060112060605030303070c0803061c0b0402030d02010b090a0504030e0a15020712030518040b 77
    0x450321520b0585088404810f1030745540342c0c442080c030944020340005406181414a062100c98590310840f0210341407107000c00410088034400d10096106842590000c9802d400300058161009001a0461541e40115500500e070b01d44403030312111844418000800c00340c950900144080c0010900091226000141133141f41a25000086410819110740186544001c01a602c500c180003c00b10705030400440400002d015041c50105c3e0101031044482200c0444091481c080080c1c12a200706501c4203049010006180035000141c541a0051410341c10182c6014010b225030510003000a240440000c0c0991030701d1542502d82c00c92581d181d81112110301302008004801c0c1c1c0d0030383c0207004030300318241d03e5401409400c249020240080340766a5035180704000404d07003d84101c0c00c2050f0944105001e0f5034040c1e1110280c1103501000008018003c0040d261100d15801900b520280b83c1035500841e801005840413660401d589258001e08400064018004829400d1b070148005149 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 634599874 1250 634598624 634598647
    0xb04111201030201120b060a0f0e0406080c03060105061c0506013f0b0a0e0402190e090715090b0d2702040b0a15110109300c11040e070308 61
    0x10394101c2e8000e0b01c45450740211248160161604840151740003641007201890302e03407080e07410301082000d42c64100302c0c5488403800034054404650141025912280c01941140b9051000b43d006000031a02d56140080c01990303003242c901018a282c071401c0ea610005101c0c0d074091700325008118031110085122a079442c40c18400410b00c26280d54118200413242c100d00c90f120300c11140c50312001806250150f140c101d000b0840040284200c0e04070380c180c41801c00d0780e07003c058810301914141d0f007185000e2030200301c014500000d03a400302c41195894103821b9030007504004a2415100c85990140e0340b003403640c1c00340d0041d0107510140050700345c0c41100d50103583c810203602c080140c0308a5040c03001c400000204036824106010b003001e01303603442101e00003007400380041a0402004000209400101e40c40341e07084000b101921000098094614031004110076016100300e2201c0d0420182d078106a84030800703480700b91420603024507070b9001d403041000310800424004550040010b41c0d103c107030740070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 634601124 1250 634599874 634599907
    0x60f030a0f1109060f040801020307020604170a14072303090a12230a0c06030b0f0405091005090c030a080909060915040b0604050d0c0303141c0b0411 66
    0x1940454207151039500c000d8000c0358098141c100000d2440c16007040703043c10412607164098401c58075032450402c0001402c007020b002541c441c0f0010f0b000b400143c90103040000840001412801040000f0054466080d8110002d1540920b0704002680c03540c43c940b51605211041910381501c0c1e00ae5021207600508000000380840a8162090381103107070b941d5802035041101010007028210014500c2a40003061400d440d00343c0740b100c08030744040417542c50f0342d00120317016000f03400000e44411141e00a810401c444400d440ca05490801c203d15101c443d5507103c04030b10f0240340600d42c8640100e20b0780c5200300030b1a4421310340242a240c49414610b04185540d00406441e4003411151b030006140b0f1600011340d41c0302d0340d188600c54443c04178001c200b000401c00a4030f419803081041c807010920b40c8410300316001ca0307445110425071050450a01818080c6201c0181441880800c29041001090300105130101c17607408000c07514150610008000d04800c2808120580d4082741d12407a961001c0c1d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 634602374 1250 634601124 634601131
    0xc170709050a1d06070f090e1506040b070809010e0a080c21070f0305070b1303060e01140a050603010f0e0312040c03020303071514070c030c050c0a090b01020c0315040f0c05060f03 79
    0x885451b1011800a01a0344840c442c0c4284002c034081580003904509400c5072000480070000d100b03a01e41610b03440f000380c2d00d41004006aa0140e00400d1341c1d4280d580128655605035402c98440300201d140110150340e070b01c0349050072809001044c00b0f08141032250360300c1e40102d00e4a0000e0312080ca8941c040c8a20b4103015100640b12403140c1e1000288044807001105c5044142040c1094001e04640302c0c01d000d02140b030400007056589511201d16052041d01c1d180c010200c030200400d1608240d0205401c5d0f0f01095010001d191034040a416074040010440320f41d441c2420078102652f540c0c0c100002001e1941e8000394140c0030008400d01081085038a22107601c0d02d0342020060048ac01c00000341c2100122141000f0811a0900a0209001d44021603038103200300202d8245800c1c0c407020031910710241d4803401138a61101114142c80d0303010700480006031400c0d8001c2120741ca0075201c507060800080d0001c1e1020400c640c0c0842804030b60070115024100261009596502c1b06509000e658401c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 634603624 1250 634602374 634602377
    0x513180902040f0912081905070806030f1204061b05030703030203060a060f12020c01021b0d03061a0301030f21020a0605130c09020315120a0c170709050a1d0607 71
    0x200e102c4600500fa12442d550315030448690329600e1242001640d083c200a44000e000318050029400101d1060140d28480e01d80d80e80d81b12200c2c2004000e05280c40c081d03824440c01d035004076032105114204007042c2c0f401c03624646813518111031a01d40b24401c103400c1d07440191035404000340200c03d040e007580095020f90b1041d030356036480541e925403c80d45c0c803040c000b405c00005d10000e000551040c0c2d42d0081c01a0706050f500051a00c02284042c00c19000b01c545203403401c1e08200442d41c1100e0f0148100310007005021141c1100e0310700100601c19522050100501c04403c0d0721b0520300344001d20040b400200b6004446040c807409400d00139656090380c0308119011810701e0002501340c0c07860140c0604643d0301c00130001480d1f08000c0d90a019410050080100c061803c403101050b0342c40da205450342c401c411010f4000390301c03075080c081040b8034990800301e01c4016070b03d517081ca4500c00240c40e10843c1c1c0324050009054482140d0303000a0401d0502000c07043d940c45494609068002c9440c40c01042c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 634604874 1250 634603624 634603631
    0x51005160905120d1b1a1503060c162a0e070203090a05041122031b030b0a0b120d11060a06050607110102030f0418050901110426150f070903020d03051318090204 71
    0x14041540d83c0008507a00b8400013814049814100030b402500800709204030803041300449440081c012444038415440c8824480c40010083707e001d4200e1240c201903103101551511802c040468000c4569109481c026a076035098140220020030903244c89100c2e10b17220660b8481c404120407041001030005031485465071411800982ca041070b042d08032503101045039103a0b40c40e0f11014004016004106d5007203c4c12481c8802c0340c0c5010310030004810100c1d1142c4c0a040d03000d2414620700072000b480310381000d1420f90b0030701c40e5545580c29920740a502c21251018080030400403810f40c0500420f801d14100041000b02e060810700744000482c20030507904104503540c62503c5400c1c1d8480b11180e180607242000207210705031100a0182c105455040780d41c4030090f80e034541501e08840c1c405000000401b032020311010300030180201d5007050302c030314082e002c0a0554001800e001d0704000d000b802c1c00030029103071081c0001d2a8601d00140040e1f424500d68a82e8401030350003a020a5800324812840e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 634606124 1250 634604874 634604911
    0x60c030c0822051905150105010203090603070201021c14070f0e040c090512030318070b0a0e2107051009081009051005160905120d1b1a 60
    0x400c0c400d180255400e40d071519141c0d1030740805082c80e540072484040d041d10150590401140d010042061000e8458400032440c210781c1c00c0130307401d10700740c094400d1410603408010005aa4000243e0358006800c55038203917240c1318070609a009220700220040020303809081f504448816a1100140d101c801e48054a150380741c202c202d0700d60185051690225410070307c220f00d0f030304199022400c14211030514550303450f19038000480c0c0404410751003080394400010400c86c5400c840c280824485d018006100903410804a0035150117250090310411078141400c020550b5056400d82407401602c114214240028210546450b42409200c1c06950380c4115140300c0c40c81800201c08448541010305202d401841100c0040d0080f101c0c1a1120300c90103e00111441c083e21030540245900c1c0ca500001094151000d005c0f11010f6204a1084241c951102d10750301e00418058040c941514001106400c1e010303d40108950107000035100315040d50003102e07003070107003070303070726004280c880020000c49030b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 634607374 1250 634606124 634606127
    0xc120318010c121a090c0318030a0804020103050a090b0403020a0b06030c061b0a1a190c0807030c0513030602040915030f1214281d0f06120f04060c 65
    0x800c16980c02c0300150002c03c00e0150250140d000951088103000071424030182000042d0000e90256040b030010380000051003024405120305212940055000d1400c1100d8500003174881c40780284082d06040d120000104550395645c00a110117500904100b142e080508000f591382c04d075148111002c4027200045001840c000902070a40c0b18000c01c140c0c5040ea40c41c034514900b0381120011195481204081400580445082040e2048401c5240042c1c5440b15407818900ca04502d00c20407903180c6a0100d69542e40081d1f03a940c8003009050206140144000840311481004580d844d003a2000e0000b20400207960000c0c811648140c10600450501c12484240500107100c024401800111071600188a108054040803000d00f002040c4410a440d030030b103e98007610310540014503401c12030102d0503008030301450089181c43c00000c1e2404124180c2401c9010104c0103118220000b01900030f40e0780d8000700c4801c850401000d076001d0800c01f161483c1d01406444c1207501c54201300590301140d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 634608624 1250 634607374 634607381
    0x20c0f041803031a1c0309090216081b100209180c0403140c030109030e04140f13021f0c02131505013606030e01020c0d05090102030c12031801 63
    0x1041030048141c034031500d603901600100b000301d01503070300c1040c01d10402145955000a54583c0c102c0c0d144540780c5d00c000c82c42c00034614113181c0c014000c1640705100310106120700100a03034030241d1100641390b036129091103107440c140a03040c4006842c49051036a214032003030340c5c0280001a005981d0b440500340c403104a0b0340c11410846641d009420306101c20404a07502402e01d04081c0019000c0e2542c044020300071034299400d1001c01d43c042407807110360344000d0410b40301c2c5115004031001910711a04000302c440c0f1381c0100140504401c1c8002c8007125003550340e4001005415540d0400d0158081a040340c00707000503529a000360310400f02c144106048200600031180d1101c4003400503561241010019a0915100300c00394403d00090340f400c0e080444042d184660f20203000400b0102c01c1e15100000f4240c403039110008030b07543d006003c07844818000003016028030700c40d420803640b03e40d50500100d2641c001c81010080d1407007045440d02c100300d03010000318001d02c0c642080c0b442c5882c4080e5443d00380e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 634609874 1250 634608624 634608641
    0x9081909050312090a1d0403140a0f03020f040b041508061c02040c0504180605040b03030a0c121e0903030e04020301030506040f020406150203090414010323120a020c0f04 75
    0x26410004842004040c1e55000700040320000740725031401501d074100400e99280c1038000303400c91b0503410b06100c28075411501828025601090040c940650420000d11540d02050b0120074103070007060041c028071030030041c5c0740500740390022103441d00ea480c2080c030b8100b10002250b5000c6145080401c40710b0030b012502c01500d20f0b015482c1d01103044950709002c01040c0d0b00302160b0400c01d00303000c0814040d01e100028034510384400d5001c01c20604010803c4100d60300b1242041c46940b0401c248620160400c001a050365005150690451009001aa5554004440c59071042e0b08401080ca4058002c40c124040e68040e81d80d21520300c0b40344003440100e200a02014142b40e10074800030300020051800b650b20f1501c05000403500320380e5001011446100c024242c0056000800c1d40022420903205402c01d14030500c0902c0c907554915101d04c41c5803240f98854100c1c07841c00c0048440350040c20081800104241600650740e90b003400300c000c2d00d40442000180c400d811403029840d081ca400e0141040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 634611124 1250 634609874 634609879
    0xa0201140601140f030c07021f1106060112050603010b04150608010b0403020a0302060a0239040911060c03090907030204031e0203120d0902042408011401030f150908190905 76
    0x40c184e01600d892515801c02028440512070030040c1c600140c48116210940010311107080340d000204c80c4001c0c007410034400755021075170f00007820000581e03841242d130000c031030452a0005140d250380011a01500c04000b21640040c03c02c01c10385c041d102040c8041044800f95600e800ba03903600d495018070a48150310010790700800303400041c0090724001d0028091818540100d40c0244481d21200c0d81401c1c1c2c0174550a4110f0401c076062948024084c0b048400603002c841c2000b0300381540c1da0302000c2000742d0714210701411000c90814a0484100304444440600404034051413501840007006903000d030100b151082d2118240e5015091a12000c0b00c00e20303802000f40443c03649914000800c0d8000314044480750b07840da00c0103005603c56200384d0340d201c214442501b58040c0440101d002091280c0c2c060540760385815075081d41381c15450420b9040d2980300d045001c81c00303e44e00300300d4888900410740c000c03a1071505030928200070040008ac40408a1444c17405a0100610400d0b41d003020903108113134 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 634612374 1250 634611124 634611127
    0x5060f190513030b07020a0b010f06030e011509110c1b01091d07051602180412020303010602070e040303020d0e010509121e030a090c090506040501091b0807020c04020a020114060114 80
    0xc0013840c103003da40c3d030007515441250103000d5662250781000e40283e1112005015451040c030880307a150091681e041c1c0d08000038060710001203401c0e0b13152031b03584c880c1c1514079955941d05542c03681078100300c80eaa00c6c080700480d00e21401c80c044049017003d0095803a0b010a40101c40068111492078003852442442e640c2d14000d542c42030801c0e04d903a40240c0e061000e4500c00c04801e00107980e01c400d5050540420390402c0e00c0ea00d0645000301c1503603146000d007000d542c010310040003440d500240314000d6801c9021031a407543c0341d5203000c4d80680111503d50a07020f042c18141c0c04a1203056010900c03401490044075882d1980180740503541c891300c130100c1c072020300300c1c49041c244175024401141c0010048100091040c41520781c100412610340001200c9900c40040c440e060cd010700526000d00095402000002602603907840413802642100091040da48009540107000b070041d00d516420142055541d5a201c0d1710003030003000030410500c5407000c098080f41c4d155106030030002e1029000c14410707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 634613624 1250 634612374 634612379
    0x41803020d08070905030a06091a010503070320090403020a02010f08070906080912030702030301030c271e05100e09010b0622030501021326060a0b0a05060f190513 72
    0xc50780d82c0b5000305150240b154001c4001004d0300c0400000413400d0283d40005140e07641d6160601d8008499103000500591034070042c0440e50b0042804d40859500c0400b030087c89013a07000030701c03a02600450a65001100c2020401410703004a10f4a903114802d81c0d659001d042186419035103c3c0f4103403043e40000c1c410000500c4014040c1509680100110b812034070941544900f1404036401101e040c00103030408001041000300d40303103020020300000030b40c0b011650f403146a05881c0c0394030384640b800e12640721400214100d5081070810b01c80002a00d05100342d1800c0c0102c070229103264460244850790000002d17900d404180b180001c540c0b00100702502d0030504103d0050500d459101d2134200301d4104d5800000103030300340300800c100040100e075844050f10307082410008861186060304480b906040ca0b80d40c9034004503010707a000a1202c1c00007442e04e0203502040076441c3c1074100e15000b6000080c0d005200c0d41c80c030040c0c0032650251204e071602e00d00040084480740102401840c180014642c103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 634614874 1250 634613624 634613627
    0x60c030b09040809011b050a051507030e151509070509150705151b03010603090c05010e03120c0a08030a021815040b0d0f09030e24070809040603050f0c041803020d 72
    0x490071441d2454134502000c3e00c01c1c7c55040c10890000b00444041d0300c840040c210300c00c0742c558883d0b802803c80c00d080046020004c0b04035100e44d412841102d04000441c000342d152159403130300031100c0c03002401041c042d04d030015000e02298000c0144a1182c601000710039280e12002080381c18a40d03003c0701074018a05000300040320041d01403d00840c644409101d002e803041900d020798020311207583c003c1074080e81030070862206506a004103041165a005a507200c3e2400070b0410041c000c9109016075400060500905210780a50000c20710f14000080c04480506900a000101c1d4074000d2000c40e400503c042181204c201c80350550791480c20b0204111041c0c40b07002801420382519004601001000ba043c021a102c4031801c6010400a0503084d9160600800703807050040281960f0000120790841611a0301822400401500740040c06000c1911290081c0d00113503806000c071050740b00d40d140160348441103c52007d004615100d080140201814070b0700c1030194064011b00107650300c0d01f50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 634616124 1250 634614874 634614887
    0x40305031b010b10030506180c1602010908030a02030913051b030a0207020d05061b0a09050d020a030b0f090f0601060e010c0501060503030c0a0b10030201090e150d060c030b0904080901 81
    0xc401c0a035560f20301e4580340c60348440c0103540503844503030380000350707440c18208200c000c1c0c000e041c58021031022802003000d8102004112500010098183c070203508061004803003207001da4100f0322142c00701180100415400001609001004807030200203072802c4007414044440494403200b890040001003070a001d151002150080410a00585403100e5a008103490086004048580c0c2d440f07042000600024044140c08800050020324680080d4072402400480e450203440e00c03410100d0303040341c11581c031a0302e0b80d0001d55000724200402c1c504203003000c0c240401180e0039651400f07001c094400c0b240300810420b06960003a10ba8100c52007682c001110340c603001c0c40c400c80b269941c2d1580444c46580400c0a010070050900042410076400c1c680340500c400d01500c0c0c094100c62214080c4010313a041410081920640c01c0d00e5400c550b101000700010304401c0c2c8a454100d80c401c5e50600900070300d60002d400d900070903201800b550200d801480480c2c002102c028003002824081501191320992 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 634617374 1250 634616124 634616167
    0x80105011205060f19050c0901031d060c0d09060f02130e040b04231524062215090905090d080a020307090504020f040314120307030216060219020c0604030503 70
    0x9490603903110361039505c3c00c1101d401b80c9001c45039440c007207401e92056070306d070041c5100d02100e000904012150b0403491596810041c0140c0210603000c540c07081c01e40c40c2a0b000850f02038024000b88101400820800001c1d0300007482c1028a51210740089012018850801d00842c0d002c640fa1005559585942d283c008140c858002ca00c9413849204070342d500c00f00240544898247d602485508080e000301210128291401c0d45803416120a00d55595407101a19038450905412034407409076405458980f5650ba08200f1f0710b00032841da110041903005101301c0960721011010003803511001080c96544801003a10b20015010500148919145030081c41e00412141031507090503454400250070ba81101c0800001e20034040760420a00400e8821501c1d01d07207140010380120717510b00314441901d100044c813042c241600001c1e42c104028040c1c01c090744032508003800b15224160401c0c8000b515541c6005080140700d80c00341c0200e07600d403d8040f501107175072010043d46007420300010180c41d0081c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 634618624 1250 634617374 634617391
    0x12d091508060907030b0303070c0e100e040f020d1209080d091203032a030f0b040603051b031608060a0605030309180615070507030b0f04120309020a1e080105011205060f 75
    0x40b030000c6d0039500c0402c09041c1080c4118508810360341850608851290001e2000725000307101c41040205060303580c102600150042d41c4c04042e031401e40081610f1100c105001401c800801003440385c1607501010081c29079820500780d038412955000f04950340c8150f402254200c0841351200c00009010780d00c02401c6425111039113404100307038000c1c1c000c1e04510706070400110b916080d40300390040c00c0c0d106140342c0d403004035010003400c1d041d40c60740c035980d21150b2036103e40d5105500d4040480d40d002c12040007500d450840890300192284038007034407150244c6144404074180100858207103070100940e44440300140010340780c4080341c9044080400041c00c01074114283d108100c0c0d14844000040c1201e602520082c40042c0c550300d442d05041800800002801c2211024000040d0410b051100e24140c14a40881c0d40b022600010f01d035141294800c05640b01422001749050300103134142411200c6c124000c00041e0382c1e07800031000780003051000034026003111000030790007920020140e4110b10390 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 634619874 1250 634618624 634618631
    0xb0a0507140702041401181410030b0a020915090306100b0f0d150312090801050c0304060b060c06041217060a0b0c0f0102040b192c012d09150806090703 67
    0x245005005460700a8007d40440c1c40607481c803e95590140c003403005c000100c3e60042d84076280c880d405042c845628000103004405041c0071806004290b01540e90018008022040404002e0344111250703100208107030080c0035850000d041c10700042102d40885541c213451030b1904040c4056041c83e507006d48070700001e160780c504009506a10055841c0c3c041c42c400c2d01007807140300c12408060410b070907a40c0b00070311aa041204028142d4800c00c180c0e500154029800309050144800207185030080a84440c028400c0504000901010024064407544585c4a1003107030950422607413140282200c0e040c0e002400e0403000c1064120380401032654000b02c4081d2003d031044582000e003a6031103544414990140407950451038151040c290300d050f940d50400058916206240c5004800600101000e11014018107203159008081c90800400648003c8100d800e0041c2880859144010844006801c000c004941c180314101850024000c0340c03918881903039040100900ba0b8401020343c0c3c00c1546 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 634621124 1250 634619874 634619891
    0xf2301050c1509030403020a0e1b0706090503070c151407080a03150303081b0403031e030f0204030807060608010507080a090c03290a0b0105090d0c0e010807030b0a050714070204 78
    0x19044000d078000c2e441c00d0f020356900c0f80380d401000352100b069082183ca211f0130300306002c11a800c0b1029011100c1c000500c03141c545045003400d2000707200002d005025400006445005c01050403010320030703101042d00e2203950041c400400c899200203020121420701c810026000441c2c00c407400760107003285508c1c002c50109030958001d102d12810b03600c00c901051090044c0a0130790581c03d9101d250801500b00c19003881d249d510f00600ba03d0400e0203104864502481541410b440307500108092410f8a00a5644668034a0034030301c281e010786c0007681d00600e890710214050741c042c052503000309401c5d42c0354211521881103060007414040001c0380d96001102d0004006986e00c0040d940d200e1404a600e00c10070181c4550042d020001040c00403218580721307002059130303004401d903441c041d025240101c40801703d00e00340f60301c03012031b81200200042040000400120008164068074401d240f8080240c0750790005405481c81078032a140441d01a540088071049078201518a42d80000d202083d0300c078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 634622374 1250 634621124 634621153
    0xe0c030706110705030a0210050304051c020c0a080a08030c0318010c0c1103071a16051b0102100b09011202131506020c03071d0907080102030f010f2301050c 69
    0x1503030050011400384070b1000c6000005000010043c80107902509202003c0d60024550300761000304541130100100c0820140301c07082101b000c0c000391040a031108195100c001a41c0c840b10a00004e200f4109000040341350180802d140368116030280f051400c680b108090303800b09402c010044200761808144814100c6130034041d20714018034a88550111080d00d0034100d8a881d503900c2041d00a902141c01008000d9207000300c9042010504007040d144d604404880715201d91440c0042e20911403441c02d003e4400111a011051100907000c540b80d003482c459020040e40c1100d6107181d88036110300d00401005081d4034041e600c092000f00049031b010198000f00c03084514500d440040c0c04044901441034a40410070f0028040b4110b00a041c42860230030072a174104c081d2401d110700c40102c00041540c0d5030040010002800c0240000c0d52249010181040c030700303000340310740c078040e85508000184401c00c80748240065011300090f00050f1900b40015074860b80701c2c00410b40a8410004441c1514 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 634623624 1250 634622374 634622383
    0x13020702010c060614040501170d0513080f0607170106050a0807032307080705090d02040902030c1201020c1b03060f06060906070c1d13031b0803070807030e0106080a03030e0c03 78
    0x4110303040c041e10005d1540d0090200322403058016a0a0040041d0801c007890f20000f05000001e80178a0303c03a5075418910000380350a4850751108403d44140fa80b0342d110301c100481c182d80700c6c0300140e80d102c0e104544402c918401d0705081c820300d008190304003c0c1040051041040d154003e0b694100414152018900e1102c0c22150b076118100d4140340009010690780d0101003683c00c0100f5141c80c82c245032104000a081d41d0001100a1050b0303907448408046440030301480341180401030845412908501a440c045e500c0090741e80a0b41c040c618010740e1035403000038020040b100282c01401c0039924031000134642c030340c081c12031a4800302c10f0092825558601c00206a004c2c881c07881410700703038a404400340c89400c0ca2420701185c4141c40d0100700030142d5034111f50351016058a00070308601c80c000300361a101c18244c4005005a0310010402c9107094201c5c0240b4080c20107070f60108500e4481c404098201c0d240d40c05405290b82010001c030000c80c1c400c1d088403a072110ba032005d903941281101c0010340b82 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 634624874 1250 634623624 634623629
    0xc061b030a0f02190e0a1e090902040b0315012c070e360f0c030f071403070f0e03011e091103011401050109150509010305070c0203071e08030913020702010c0606 71
    0x2030803c0c0f10011031420149030a100410160814801d00400400c0ca1f010b80d500d540105c0800c142e4541c85030342076554541042c0406440039091300c58140d420512441c10344000d016542d1080c9501c50009100b1040d94072007040810041d42503c42c54807510300480300c1c407a83c1c5c070030a030f88a600c2540d986410100241020034002c8009091201c1082849900c4401c04004040c1141c01c501401000b0324000054101d951150042c0b030428120741c1c0f200020b1b1404c04510302482034241c008020000555004101c0a4000d01c0d583c84803035201d00018109402d0320a210041d10648441480e0100649203030341000307074150711a8591188081c1070002090864a5120802c000005440010009940c01080030000341070061501e09020001103400740c8144209502641010b9035034001464051041c040c490b0700340c1d130040030b41e82000c1d0b480d0482c14229031500140c2c010340308500000115000c00008581c4620400307044c08409440c281554030003500001e000b0782c14083c01d980c0b0440050301c1445460302 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 634626124 1250 634624874 634624877
    0x29010906080f1b28080601050414040302100b0f03030d06060305060d080702010503060a12050a0b062407050f10021c020f0d1e020f0c061b030a0f0219 66
    0x405a28000095141860340079000c0d915801203c0c1c9001040d0900d501c00e000c611066449001e4070940000001051003455008001482c03080300120310141d0114180b8102c1f00300700c6003070005001400500025000c2614001c0160b842030726031381e8400710300e504016240e00c002440443c55650140c082411648070003484e1815942d190018070810350148609500010181ca200f0054001992072440c42d114404004c0e052101c003000041181c3d80700ea00b1070700138101031020b01c440610b030b42c604a562184400801c07110030320031138000751080c00c003c64024802048107911111500d203501d00314203580e01608043d40e4a00810178203406000040001703400312000c4490041c1d86003503400070a40114200c074002d00501d401040070400091000c002e4034243e0009000005110510200000d92445240403080c0c2c400d001007001c1c0030001e00680030b840d0101040e8241c510729a18410340c03449103514611001036420080c00072070040341c15640681c5d08c0b0703010650b0052600d10b8003403120301046040c009210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634627374 1250 634626124 634626131
    0xd0309210204050c0901080c0f160506040c09020903120d14091e03132601051515040e270a0809041a030d0f0212280804050a290109 58
    0x8003141424842d26500c20480341e013541c01c1030646000201080c10103482000356103000305101e03a204042c2000c90301403440007406a40e070b00c0b1085c0707001c9885002c11a4290340c210542d060000b90b14546001302c0d40701c40310003000b403e612110111125165003100039901201e50f40c0700c00c2200d0311100070144500407803400008100c5082d02e0444041070010003c002c2c0029002800300480c1c0002040095095400a21f101c1500010b2801604c9450780d41e9000901c42d5820101400314003041e03280315900314072090b502c02410303094001011000c3e03c074030312400e8803284070140061644081d072a191052001c0b0041c3c0c0903203c103481c030038140c5442003c4109464000000600540318501485021016495690210303100010303078002948591a00310310000748000104101c042e18400c1c401403048030110380f07185072a420018243c0580c060030030309081e200c210321520176850300c0c000c1000912480d40800184116071180e640d040b00d012680c030040549400c4070b54520b002004400c0f0103800b03800fa148000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 634628624 1250 634627374 634627439
    0x4021c020c210c07030b07021c0302041e0f030f150c090e0a0510050f060d0203010807050307080a0c03081b0a0b0601030501090605010203040b0f040506030405030d0c17060d0309 78
    0x40d95007103154001c00469002c100d40f44001d080404c01c58210380e04140030241e01d650b10a402da0a00b40b86800f29505400c05294109285070141d02070410f41d070210303103206890450054170a0656140340180414010070350003c000080c201c220b021800351042030082c0c1d682d0621130f5000155655107036440d012644010045c40030b0b01b004041070b40d20160b1403200f0700480c20106020b000700c0f8654040d003400756800c6074120016484120440c1d00e08501100110759941c0d40d810002d03224485802080d106e4020ba4400044e11300000076486020b40e002001000b103645169115502c82c0c1c0864403180704030010064503150148280f040c82c0215000301c0c171000c0140780c44030005040703800c16000507154904d0200140a1642c1c004282c40a44100445540d990001c80700c51b000f0303a0090fa404564401c03c0042008104040840030301044d106260301400744a00303d22040e92003040d144014100c09400400007917151400303000040402c2d000e03080c0b500140b51201040200b2500d12640034035885800d0040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 634629874 1250 634628624 634628653
    0xa20030903071d06091320060d05011e0303090b03040c0b0a0201020a1e0215041103120706140705030403030b010c1704030b16020a0803090708070f0305060603070b0904021c020c 78
    0x1690740304500302c900c00c201d03160445030140444001b540140528100300b81589141812a989150020b4002c29954981d1034007003507100541024043d2181c0030140821503a107070328104903034800780c940c540c40700c1c0103a074140030440189420040c07041e50000030500001590041c0c020090060385000d500150340c0b004d050002909120946400740300d490b407440320556100d6170100308120082e40c00034542d44903482e1420700c0d40c89083ca042035194140502c00c2400c4010414200800c0c0c454402c00062102941301008505210012524240814800c05c0080c001901c030b580f21030380c2da60050420b92100101600c440c0c00e030b1034a020b0020300f5620700140610601038144152a48110020303080248034080301d000a40700c0181c0c00c8004e19004011010400300c1e6070911001020301a84411964241d903202c40c50260300742e4030300c0156524080d601c04100d0605011a003013041d10007d059481c503107042402408020f40c03020502c00207481c4039010b012050555030004001c03508202004000001c280b045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 634631124 1250 634629874 634629929
    0x60509150d0312050a02090f0f060901180e1015020c090609040f0c080303011a09030d0311071208070314060901050909030c0f070303030605031906110909040501140108030a2003090307 81
    0x2c03140c4519261070156240d652010103d950380be600386400c2501e900030b840700400148150700801c007031030f40e4481005041e68188400000719005141800304900803490166199032401b0380302c940151328040000c6a070704201010304d400610615220300e00c5003143e1503041c903036001034000d031495070000401003140b1101c43c401c1e41e00e540149511b0038500f0404400099594511000c82018035880b203503411a02c0750803006880c1491b03042100240054a0098001c10f040030403100340c030220f490850780d042181d000500d018480c0780003500c0c4c0302403039080208008101b84020446c040c9032008111046000c107007800a2070a03403003440c4c01415103509515000c1e040e0360031a08100d01960145a0081460058012002000350080c9000442100c0083c201c40c05e48565500950413844900a000c00c02c07405504c181c003000300217125202143d80b03c2d42c51544900c60340494100003403102a0020051803468208100c6e6881c00080b20318184030500801d05101c1e403580102e504999100392084c0c0d0459440c2d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 634632374 1250 634631124 634631149
    0x60a140901020c06011a070804090605010320091224040b070305090a06110423030106060801082802030a080a080106020102090a060e0f0a150201060509150d0312050a0209 75
    0x20002c0d070511180504141e5030ba841403050300c4551888802c0c01c00702d84020003c5600c1c403a000060150707156103c9086d200603141620805001902d056800703c07401d03a4414200440d010340c070951920305a035000410940c20705100b000b90940c02032101c0c1540047c0001d208945c2000c00c204c2803219464203051071000710100805e00010315042808200d03c3d00300104075000d9031503020200041c00202510b2180180c020364111b0312402040d407034014104a503941c0d40f080302400850003840ac4685034030044032100003e21900c2615440319a1050300400e4400c0d036504100502032180c0d00c0307405540c000919040c04907801355400e040006054041c0b0354030690103409803071140001c3d85059603241c08110490f03424400d4404004031981040080da4412603134103810100102007580039a251158a101d48851001c407038090340c0f8201c8006001d0a2048440d441071a0807011000e03071051601c14812828416181101000303c0600c503c28030f1900c038401c1d1406168603400060315900c0480a011031a400c58 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 634633624 1250 634632374 634632391
    0x903050c061312060e1603050f0a08091e06030f1e0c090d05010f0e010b03010b010e0d06020c100912300b0303070203070e060103150e01030f02060c060a14 68
    0x100902440511120615030031100c4804503404640f510342050001000401e403014464090902e032040c14040004040040d84e00400581c0d501c0c69110400541d00c0c2042c8000a10f0280b051052030032500d0041003018480310819000c060b411618400901903500c00c4803a01c00d19292181840034002180160300d0b005d60000291185a0421505000c828020300280c1445401e0220250f810408203410114003900d24950900c458882d2151103406400c40942580c000e600c2c00604114071340c404c2c00e440c040c6110181c07200050300d160340c4490001e913001c0c1110710110b2081c00c0c1125280c0415100311600c0703e0190f002c041c0710078840c1c00b004000b05032130200303502440308042c090303555544c1000d12584404da680a00041621003807001c6400d41c052030002035494003030348000164400030840039900c1030909a9041080c000b9101002c400c881d954090100f8030a04000184000348000340e11941c4540010442da0030300140d03118152510740c04884002d41e190702c810300d00c0002001ea44a458110011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 634634874 1250 634633624 634633627
    0x6010305032802100f0207020907020a03180e010512030f031e010f0305150406060807090519200a030204030b130311010e0a0f020a03121e02030f09010e0a05060a0903050c06 76
    0x4032400075130f5500b070f94190074038959030b40840c481d01e584140c1c1200d600e641e0190000e802890301190103074480105103810b0303001c203041d0458100c400020042c0003054034120540803026909100900c0301028610100401c60721041100f0f098a004100c0903600c117500303000ca00d144130030719010384516505043e80138980403a12044240000703076011580c03c0400c03181c1036001c2d007540c0c3c460804d1400390001d94495901402590800308a04440781c114502c1074090358031060888421051071000c95151004640b0358126145a602c4c0c400b07001001030103808254507000d8181600ca0300c540359544416501c031401c1076581610f0701304140d00200302042f47da4201000f040800792030240c668541c07412600003801a00b020010000b19600e424400001c1c40d00415405901d000780e11019040284540318030303040b480e40e00004e9004a02c0002201e0000044056803070500c081800151035203240d0798151a0b01600041010605888410160207411a1955200a183d08e1400d08604008440e00303114040c140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 634636124 1250 634634874 634634947
    0x8220609120804120c05090115020f153d0501020d030b09190f0e1e0c060a0e01110f0c040f0203060d02060c16030501060f06050a08070509040603050601030503 70
    0x3550b81036404807901d00c10142404085494036840c980b18a4202c04c1e403010002c0d0021404141d1461001e210a04c203400301e4907101042c0c41d81e0b59403100d007501d02c880490f0b200000180074104109101c40c14268404514001b502c10390b211289030300c0054000c100145a0001c2000301d0341c0d04000841e1320891a0804010000c0d002c0e01140e5640303c010f0000c5030300d6a418034907020800d00750703210f050401c240e5041000030500441e80710ba00c1d4012200d85154041046080560ba40c0e4081303007000310b14030000c220130310b0441d06c88000d8440c40f101807003c506000340545140d01c802014040360010080d07900140920620401c00c20003101c0c41d444400320414410701c02c110490f1a5125201c04241e012100e4544400c0c0c0610a603140c04d142090180019a1002d400001c01c030301504810203a4a0012400280715100ca0044070b05005440f50000051482c10101c0c01d018041d10040c9140c400140c0301280e0942c4a0f04c9451400c602a40122080c1d80005a0300d507003040c0a08681ca6925481c8a00c0100c424 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 634637374 1250 634636124 634636133
    0x2b110c061501020703061503120503190902220c02010507110a02090901150f03020901050907020a060903200f01051510050306040b040c0c0302060a05011a03040822060912 75
    0x4100410085600310080044142070f0700800412000350343c003403c03d02880c040c400910a9402a92004541d03508003000100d07403440c01007090324450b00b5200c20350403107103c00340144009064031040603604041540c0e1400c0d0119031021a075102c10100359030102e40c15104850090071604000d08840400c580c03d43c1c08180445c010074900c034820303012640155640c460043c1c1d640100624503260006210001d00001c5034002c130041c10044a00860386030322142e07a24400d000b80704100f2581e0000580002441c0030001d0015440b03000a02d0007843c180c0f91258050051500c0e01c00c201c00d8080f43c507802080c1070f00b01410309004156100c08070804814a606912010a1900d1554252030040c0140440003a1039a04d49500100da0b20b103004109108402514202820044141038242c0060140c80d000400e02446c0b806207034100c1d840312192811025640407610b0315500090811a080b410402460041034501135403100400080039281441c24030b01203002c0c0c59001558022104520b4200355540481c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 634638624 1250 634637374 634637383
    0x60e012a050a11280302010506040911040f0608010203070203090f0f030d050f070602042d0b0a0c020103140a05011d1005060c03070b01081b0307030b0a0905032b110c 73
    0x11516401c00311031031100f1204150820040314015080c0302c40044139058070b4410a00300718000c9029400070407480e1500810f1005640d00c041029048100c94044225107090550058403d081c2048002481c283c6079001182603900071f48805005a0000c50307407450a1070281a51045c2050444404690700d41d40d201082d1a1285139042c1000d0001c04126040c44405071421030340e11580c008d6085680c0c079100d548189480c01241c8105a0b5102980d00e61501d2081d04024141a101c1d8002d802e400d00a41c000d048a60362a4403400301c1c1016210106284454814400d641c0107401100c0045140d605000c1d4000b8501c80c1400c0c40802a504c00f400c0c41452018042d440c81a42d4041d00c6c4140e8484030315240d50b28512600d40300500c2c643d20b02d000002c0329240030409640c240e0400006c0f81030800c902c0109139030b030704890201600c441c400c000440c121403001d81c0280c51441c41101942e05000c071440e00c00b1070020780030342e40c5404991044441c040f05140c40c4036000b1301010380c1031414100b500c45010680e81c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 634639874 1250 634638624 634638637
    0x60909070c0f1208041502070507170703020913170703171312030b030d0c1109180303071e0305010e180304170a0c05010f05030a05060d060e012a05 65
    0xe00092840400c02d1081c1c050403208101e030440c3e811119000120030040800404a8041d200460b040300164071480041c02144d41541e0024000c1c100c25041042c071400b111210400340d4a184200440040181c440c4030b46d40e4811101c64000e0b0b0740406550074080841840110154294401040128002a0080325402170000c0e21000c16407140c0c0c944056400200903c10041d03c48081d000e445040380758142c1094212031010350a80e158080645010766542c215610020065140c1c14245111800c040c00020b40c401d0202001d080700700c1c0c0d8000341e58110b41c01500e0308030014020035500c10340f440c0c03d440f90440daa80075190800034ad40c94549101201c0501420113032040e04080020924003a04005a0300503007030b541c4100f003400040e0040e60382e95042c1c0c20030496035841000d00c00902c660044414034640b50b841d403126481e644c1d0710303079441006140040c44140d0100300720b9242c00100704548100c038240486480004bc03d07000303104c0042c1c84080c0040d030a0103407088414081802c641c1c00001c1e9500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 634641124 1250 634639874 634639877
    0x608040f061103090604050d090f0b030907261b0a030b180f010c11010203040c0509090a050a0f1a060307090b0604150f090e01060207060507021c08090f06090907 71
    0x2204828a081000b60012602014142c8804410300031a00c1c404103101d80501d00c100101c2c0c0000707039180015240310340c20b8487d0b040340201c600310030050003904600450348903800000391490180c40e90504140011039841248035000941c001c96400c07502007004601c10304070352220302138030200180050b0ad05141400b0050040c074020001c55003800700003442000c1030f0444400d554200c01c0c4a51141e00811400c41c0304000119041c11190703c0d0b49042c42200d001c2c5030045103109980d81040c051098510014044944070300c03d0780d044c080800d04c14003205424520804075406080d02c2403c1c2070903d0846090341c841002c1040040c0141c40e07400046403c1125020031003c1040e64940c00010b40b0760190340d0140e00c0d4040c04034180d00c0c41545c015082c0b4000205a11584181915071680840c04a000d00a04016a00c00703507007840020300403001b51070300a1005000d00403800d40070700710304165205a401155585c20110303041d00c00f1318040b0340582540a09888031410808a000001c008000c080d040310f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 634642374 1250 634641124 634641143
    0x100501050609040c0c240c0c0b060108060a030f121103120402130b0303040b04031703090d08101e061d010c0b040c12050a030e0a0e18010f0f02180901060804 69
    0x3c01140c00ba07600740f0b000320f40003940b070000c4078510300f088203800c2c6d00308050345101850601100569070107608445080d0ba04102040c2d1180d032170300010740e503e03d0050f02c1d49601c00c841d00300000014054821035103225124141a20303030154010700c090300250b10904148460b82052003800a807a400340c0190394041c1e0100e8500c1c20704207004840070700601810744440d0301030000103008103e031041035000340f00b2248110103021246c2024519000d041c0400d031460000d80d00071003100400c036807040090075001512942c1580ca2281d949620741e4400305514014803926044110400a5940010312603000d81403481c96030741c0c0d216980780020180c2007020303030080403024584085402d200c00d11f00e260024161354808841c4000c03240c20007584d03844848104400203100805520300500b42a401d01084820900b20f002103501c51000c4001c104691180c0c88206650f13519440750b00c42801d002d400c0600341e582600507903d500543e01c0d80c3e0b021111074103640c01a4100801084010360007007907180e0150b004090f02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 634643624 1250 634642374 634642391
    0x30507111b0609040f0207020f0d080d0e012c060a0c091211030114040b0a021602011b020a060e041104050918120a030501140102010911040c0e03070308070510050105060904 76
    0xa07032034040c810200d9000317480d1424403180c001056004101305402100d60243c1d0704104010012804013032200104180d10a001c0c22a29190713942001100303011080022aa5002080610b60711200076120a111000e005600c401d0406060000726085419400c0a0183d00b44404000d04182c40c01d110310507038514401980030034407400360022111044000c000740070800710b2511001003100140c0302075600c0001003000c14a40b001c18407c0380c100d85c1d1080d0514038207503940d40054070350000c2c0100c3e460803100e48213203045c0140c0c2c3d042000c1025103190388540044c0e42400741030204070b0f1806130908000b01c0d000c00c028003080c1d0360040ca00b40d004880403110310041e403050781c1e043c2c1480c600d07900c13207802643d01040442c0c95941640009050790349003020080520b051000480c240c0b25510700c0a84a10012001c9000509103500402501c40da03d00b402200700f0003400101c1d01c0c1000c1540305484a000c00f01c0c541c02080300c14410104101c004c984181b1865060400040e43c0380310b43c0c201688120781e00e4900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 634644874 1250 634643624 634643629
    0x4060c02060d060b0a09060c0507051e0d08180402250f051605010f02010b0a030b060303090913060b031606180b07120816051c0b0907030c030507111b 66
    0x202c0e20181c5045809214282d59000038501507006680450046401d03540c020a00511500c0780868250b0003000a0005514143c1400512841103500c64051f000d90070300407041e0386428640c0034006108408682d03440c0d40d041c00102c059169480f80c2c030702c06d43c0100a0010002c00c003040c18403e01c1005042481b0b21003152a00a05015030628020030070f0003002c1c062030b15011031500100c1110000c0c0c0328034690803c41c0d40100d080720b44034001c1d283e1001c18000188003040c000e031000c4d50b010101074200c03483d10102c0c0002900c2c84004444100082003825120000c10109000c0c034030f15910305034010300e56010303442d4244407900c83c2400f85500f00f090f54044407560608501500e002050a04c000a03038915107405c04004000b1101c4003000491032400104000d284580d5200c07030408003d80d074032414021401c40f8031165000c0640031640c62030700c40810110781d95401903454080e0106440010f6446484103001e416130320020404018051034001d482c00d071101c081141c0ea40401c41c5144608241240d100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 634646124 1250 634644874 634644877
    0x6050601020c1e0a060309051506040216050105011d01120b091c080708090c03120d0f060f1406091c0614130c0f0b0f07050106180c1e020304060c0206 66
    0x34141c0e0100f120261540e40b64011225101c15040644a01c5091501d640c0103409454005100510f6507100c804842044890016000d4109d80010400342c601243c541c01102010301d50402552141d548000401440010030030503214904084880c0c01a5031410301c5100c11402071003406803c10585000140d03107110284980407690101c0304030750030f400d440c111000b07248039804c841d030f100421281008140c0b0000009503d100d00b810040c010403640c22001c000c22070301c0c1c200d140814026512000800801151801418060283c0000c0b80800078030f00380501010000d940003041c0901800c1024041d162240c40c00c90128507050000043e48071154903240004040307502164068a0a620900c4500b64850f010450442e009080e0500034546405091029003490f100c0d003403036040208441201d12600c400038014460040000155440d0382d08400004200c8407032004400d40c0d035444504500070b800c4176500154a1001004168900300084080d50b68400c1d400382005104601c6400b00455641c5030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 634647374 1250 634646124 634646143
    0xb0918032208060412030b090103020f01050a02030d0507080405160b1218010609020901030e1518030d0c0309021503041a2e0302040b030a0b04030806060f0c1b04060308070605060102 80
    0x104440f144c1c40c0c142000b2050340394150b81e400000f0700f040c3d500c0d4003502e0110070043c1600e0300201840d01c454461001134651f27902c503200e0b050a500050000d0121054a449801d05c502902d403144000d624142c68807a091260142982040703d00f41071051100080310800c1d203544058000d042042c0d6165070510039625110300b10340403443e40c00c00e000071070070450540150a22a00c282c8040c801d0814130420075071507a62011550724080c41c80c000140d0003508400382100c000301d25400380d901d4643e06084003401d035070303002c020701e800b20340c98081500460034040104207252080440003401c40c2001e5441010303650002d914030a9075501c210204510840380ca1102c140c0104144000c40805101040041c2000d85448240d2107180f0700b01c6c500b0a10b0030f001c03404409845c0c0c03216072224140e036503075001d0f03940d064064950782c1c10150500a904140058000418155110500900f283c4040c07161002d8171502d8280c0319400303181012410000100d885099652190307020070b011895549050040f4038122010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 634648624 1250 634647374 634647389
    0x7031d060417010c09090b0d020f0a1a07290403032d050f010b03010321090e0408073507060b1c03030e0a02010c02010f0e130b09180322 60
    0x742d06407050141c056100c4452a00c0c3d44c0c5400ea0265035941041c0c0032508401c1d88981c00c5140792551600514150300c9120314060002e16080066440f56520200c1c20b08105000313441140014010040c01050088040b0750f4204400c40440350096620089141401800040903d034075490340004001e0700015520450b955018005201c0015440e46d41c05090142c0d2211881c50b414000400d1190358074003160305807a04030b101d507407150100c1061070b03080d10109503c1100b04400248003181c41440076060501547c0158a07040c0c850125040c1440c5c42e07020b00d07140c5910000c2c41c2164802e050740800c0d02044540304003c500d929610307281405c80250002d050516130040840c05000490082e2120000301103001e075030100720b03c1030b4225040e50b41e014a51070203404a254490110015072154002e03000d10102c500d0100740401085003c00c51a803440d405050189071215602c41075030520200341e40d440024042c941c05641c0c0c5c940b61058603880b0303450100d00c10200242c00c0305400c0ca640c400e4840100480e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 634649874 1250 634648624 634648649
    0xe06190519150e120c030a170903010612060c03090c3303022d0f0c0a0203060403030f0b0105091305060114220501172a03180c0607031d0604 62
    0x90b4010041c50b440340c101440303680071a06a0544840019421003000c202400818440f030503521400b910000d140c81d00300101c00204281c00700341c1c4081c064140103044440301024a82d00074070f41003042d02c40c10404c0004041c500042c840108a4100fa41c03001c507480780d01d200e451808031740401049080000c48060449041c52035206241790716a00402445401602c020161020f10501d649149030100c25180c11400511500c10704c8c044660007040c50581000c11200c0c0003c2950210381801c2003100c007640400e079543e400e41d03410700f554040c000c1239107801d2030181d01c2e054500c0005000e41ea01c00c8040c4102981d41c0c4006419640503a0004035440325403031196886481c56015400105900710440c0c0e0071103040800041e0307550103284140070800e10740c6903141469440e0103600e07240c6076030004c40550a260005052015404a01c025402030398041d200071000c901100485240044446070f0900807002041810042940904180d0001042d144800100c1044c0b50000d216401b0b1a0020105c0112 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 634651124 1250 634649874 634649909
    0xc020301060e060316082104181406010504030b130f0f0b100b0412022b08071205120708070507020405011502010b010201060b07080906040f030308010e06190519 71
    0x1088903000340305400813802c4031240900803c000c41c82d8040352080300284e5001c0c8400303115000440c0d01c0c1190585000b0195801e0980d2a0440b81c0301c14048860003827899696086150042420501e10364030070428240a07160038516950740caa0498001c0202c070800c0740e510707500c000304141211031102c07031900000d04890307a13110342c10701c0040c1d080c042e60f8450307020030850000224000700d1002e840840703500d101c8001000a0b140c09101001540c8071001020000740c040f6040541500706803100b40324000c00406485000505d40903000000e001c1c000002d215043c032108410045200c180341d40b003440c030318108519440d03100090300d49009010f0002d505c00e003040b00124004001c4620160514035660003404060055001a400c84034280908040c80d0000c05ca07090206103d40020441c60001814040c03500369204965812440e05401c1100028000070040180c05981c0c1c4102c1e400c6003043380c503280c40c00041040039400848601c1601d00902280000f071492100f005c502c50020700c005021102c6841 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 634652374 1250 634651124 634651139
    0x90e190f0b181503070605030a0203100905010b040504050a02030c0702120102120a1a1009090b0105040b0a09050a0f0b04060f1206151107080d08090f0d210504020a030201030203070c02030106 84
    0x800c222543d01c00202000b0082c0755502c0c00107210300444032aa1aa00c0c95a103c0c0500000030f54801009450006403811001420f481c580c8922402405000ca0352034940d4100010881515005892404824010300030f00c0034004542c02200c00499045544141d07414110300ca07140a40101c0d01509182086d540c10407512800c183c00c0040c0804081c1010308036844400b041020805001c0d5400000840044003400130b84901e90015501c1041410114103266840c0851540c66012420504c00038125443c1003102d4204410740a004d082d0b0140728031409800c0c00c1801c60b29010f240710380303020087d6406d00d4403070b02d0b40a00880a09003207201c100788440e64840d0040801a03941030b034501c0005000703040d18038000802198030300a231000c10002c2e150124001008441c00d40b2b010700382c02e880d1b000c0d418800c040c0d05002c02440c1118a2103403112490140c2e22210451204046041000c5c110f04005c104401030b0340e02094a4141ca5090030016120307140e10b03400300e07440f82c0c038510005e41562a01e40c0204182 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 634653624 1250 634652374 634652419
    0x1c080703120b040e1002091504080f0c1e0d06020d05090a020a09020a05070b0702150906090d03020702030312250c051b0306041e060c0f090e190f0b 65
    0xc10340d0203081c40b407440034030140400c8400e8034190b90001c2e0000c00442650301c8440d0000c01d8080e0300100000505400070000d001d46138440c0e803290b44603900601200321074000a2062000300d500898003007288445c64030000c4001c0b40000c201c40c1c4540d14180645003040001d9050311074600c12414100700500c0c082000c5662603450107410713071140080c40d50004a060150003140d499a03031a5454605003000340e9205958000050b140c40154010031414008071140c8500b014032a03d0300c88018089030400003016814000e02490080816004002c2d000150f1800011115001403003114141543d0382c003483c40d14100c402d0350b00079070a403600310000d81e486039100038042e1415024405680c41643c215141ca8540301d000f444141c1c1581244001402051210003219000c40d0310b141140303081e8003151f0303071a011510100f80400114000082100f140c0e0b500400c031802030300c51544100748504001e03801d005041c1744411400c40301c54440d0101c0401130000d81003200880d402500e410321801000040740e214 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 634654874 1250 634653624 634653647
    0x80112210c03080108011e1e0c18082d01060503030c0c0307050a080604021002150f1f0308092803240c080f04081909050315010506091c080703 63
    0x404410003c1170460042c8030b4041c16222662504a000c4200c4c0701d9080038042c00c194a2008410006800e0240b4040717004200e5002c85950300e420030318081e044001f8001d040e6800000703007a4840c896412030780303240508420034614045401301c4450b12042e080c502416480e001103800d4000071400441501d00051b64880e03a0320101c0c1600c200310386401c103000c0901400c0c03091032030a9010401040250a100702e0003020400c0d9403059503a45a01c0c5040524070b5401a00c101c0d0450004204110000719484001c50b4600710006a01903007031720b507489081003800703404845841815008410b52440c9421801000c8040b014100410181e03aa03050158004403601c00c030000d60603040200341500c6140f44500c001c10329098031130302540d8440d0b026920100070020002c890841c810022031154811003a115242d0360307269540d0283d524108824181422a554000c1380c64440c1440188090759074501500c02c00c003810b80384d10460040c4107030081c5101e8402003014011040008100c1d082c0359114100440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 634656124 1250 634654874 634654877
    0x2a01020d0f0e030f0c070e01080c010305010602012f090d0803010f081f15180501150314130606030b0c03090114040f030315050301020f071203060501080112210c03 72
    0x111140e080c1e851001e03100710003a008110780040000306030010212014000e00206103040b10426903c03007101588a650a0f0007481442d8050b07140b00d01d0035a4540986d50141c41c1c0d5100a01044620040c64241010b000d00708001d503032041d01c0070400401990040e16800c4000a00d0b1905080807030600d00c160394000e0241444030300c40c6010104080c14005040c841402003000320152403031a214510004040d21400c07100c0c2805c14070303000105010f41c14200080c1402000000500c1d5141c00141c440c0c2c40301d0103584605042c00c0881207041c1d18a01e10a540c4d205a904415260501d441d151480c020001508020810390f42001031041810709e042c0a14400c1c050f81000f04100c490754034041c6038000341120010407070f0078651540b074002131103900701e1500c94001c02450402d05440d00300180c00d82c5c11a1000b0f03020702d6000b013040c000784505a0303001450250381d030900b00506410180001c0502005019203107240e41c00e0080310302000a850405404020101703082c0992103894280103003039000040c0c0560 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 634657374 1250 634656124 634656131
    0x9041410020c01180b01030b150a0e0907090e030f090301090f05060f010509190207050a1e110402070f080a1806110607080609070c030c060f1b090305030f2a01020d 72
    0x20380d4045400c008249a00002650040d030b18541d5023501c2c4a0004281041010f0f5503081d031404e0713841d03802c0c082006e482c003070b0142c109602d048075105142904a0b0b2295220500744441e40011902c080308a0384c44980d4810703070b26518102c140c04640540103c00008014144404203401800310200b4018010341d11f420102c80280d990390b003002030311f80068510390b2500b41d95044ea0742d443d050b15801081028890800e44014203d01d4031401030314943c0c019981c5048040d4940300e003c00020074080c0030303e50f00c200c0b011410100303e5142c4209148400340000c0c0b0465001840608a5009046015280d00300c9000d5405180c0c4942c070088c51400e001f50007034000d00c0b40310040780509004c0d0184510542000d028546940d542c00000c581d1020702020035020711982200324000300c1d400b03000301c04204100000108a0310740c2040d024060070381c051303180401c0110742001800000c1c0c0101c122a250011024000d481706031720b200410303003000c800c0a078115203021503503540c84241040d0040c259560300c602040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 634658624 1250 634657374 634657391
    0x1200c01120b1813050d0905040b120a0605070c06052401020f0c0f04020d150302100215070e062b050105030a08040302060a05040f030f060b15030609041410020c01 72
    0x4081d1010188003550100c4902c500d052002480c3c03030341c0d5510000c40c101c1d51141144c0d507140c0508003c8604900350000d09119014003190038030f401a544d4145065401c28560b02d4013000b555180c2002d0400101081d0b201c6002c01c07030385485026030701c0c0c120b50064420090760038070f0003c00203000c081c01d01c80180c0b040a641c18a440f980080f42c2d0720801c1c2c54507405018074059640820144a000c00708107680701c4c1c1d00340090801034005205048402e0f4011075003102a500318010414002b010356540421907001c1090040680b03443c6481c1a003101d440d00f00400c1c4007440100041190040300c00d4030b0710300e5482c6482071807800d041200080b8540c038246010411380e40c99500349902d802140d4405880003800300310810050a180004002c440c0240c036156007069160b50014055191320750068a220803808926400d0225900c218080010100d55604184a01c01e2210700c840c040142114443c0c04600006814010201407682c910554007007550710a403101010040207422603a0b220481d98a0400d98 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 634659874 1250 634658624 634658657
    0x2060105040506330c0c03100915020304030c080705060a1506050a0c02040b0306010e0f0108031206010c03020f060a02071703040f0b250c03020c0a050a060e01200c01 73
    0x3514000c503030150a103082480c81c608509200010310b01c995030100903813071081240d9000c0f0740107407150009040140012030494810903141c001094801d920311854402c0c0c52001507420b41d042c0040c0a401100561695150b00f0142d03001424100042c4c5480b0303000810004002c0e0204059124034100e072003c004081000c0742c20203807a03c007401041d000c26000c00800241c1c0d401042800400d40c40204003180110145001c40e040c44800c0c2e116115207074a00f4240400741c00d00003105405400c50800640c180781c1306c100f001c0d12069025041e641400440b078800014148280b02c0351f0185141c12007240c1160501b000c11400941c0110400e44141114081c407281d4403103200202c80c090f0f500080d030300c894851036440e0744020346806085020402c0140002c1201e000c144503684001c40d00c02e84540100b5440750902078200f050002039184109080c0d2020b1110b56104541c4030706440c2c0f02c1c980038066210000043e0b0b04684c4071070702e42c1342288044401c40159800081c00107810f003800c1c0c1c2e0300b040d1113081c01c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 634661124 1250 634659874 634659881
    0x10081f0b070309081c02030901031802150304150506030a02060c010f0516030e0304030807060506060c01060803210403080a0e012705160e0408160614070221030c0c0f030c0a030206010504 82
    0xca0011f0300304200101080d031281d080112160310f0010343d6003160095500161614224010801c00641e000c403c220034021510118168120100c005010a06d0074000080d02c8907482c40b03000b8420306000c1140000030809501c100c001030240c0400304a641041380b1500f061046010700c400000c0d0074081ca0b450340e9103010044d074040b80c0c0d1000e4180e080220b15650b086c0035260040900d41c0006060120410f4850240900b4006000003c0655501e03015110710000713074031004114080d000303184000d0000083c0c1c481c0440354001c09042002406400c40060b19000d00062030503507440c85074940c1c0c560f004078818075840e000240720354100ea020400303402c3d008002e030806202d4484081001d80004000c2009503000f0180c090308520341e403801441560b00e280031140011004030f0304644840420002d02d4041108107203005070190140c000340804099082540f00003021001d9021010408180d03100c020040c40e00300e0300c401011b498031703004010705803690341020181c2a4010b110b103100000b101d050520 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 634662374 1250 634661124 634661173
    0x314070306170a050709020c0f2a1815060417072903011202040239030906090f030c0603070c050d1b0f0510020415080610081f0b07030908 61
    0x40103085c6076494401140003d42002c2460015801140b40c00e0007545820300004070091181d02d0301c0c0090340f60f524000c80d001c0e4031200c4001c5c001c810403941c0307515071008400c2855120580daa0240340c41c2d610000840c1880c002c13684005840d04061f0501807a6500101d100016030340003410408081c0e04035900c0c400c40340602c0402442d40358040005101110b00c0d611501d42240c0094400741c83d080b074070f02a04101c0c043d0f100d016402640c03d403034041030061960503c4e484550402008500309a100e5000410300e2064042e06031189c3d003d14000921607c3c1804007103500080182100d440345041e0310041c00c85851000101c560307008402e01031590b50f00860529442c43c422200018100300d043d594500d51f0804420103a807548581d10094442c20720320f00041000d065845589070641c40ca071240075090010251210340306003e07600411000d183d121402680c4480f0329008103103a20401206d0051055007a0400c2d40c0308903002a8080074990000b0007401110803c03011211011440f60312009100c1030710 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 634663624 1250 634662374 634662383
    0x3061d0f0102120414010e0304140111010608030412020d020a06020a1202070323010e0115080c03032515150e010510080423150a11030121030314070306170a 69
    0x40c3c0200300801c44440c550403180c82c25000010310341c0b00660328540746800540c03040040b841050100900d9507846181c03155208800b0340207205081c103001d0030b10b842c0d004c0e0740240d04501c41a00e040400359550142c00c802032a40260950314202e4841800075240d14901505841800c248007a4003601413000890508a98028540d00c1101c00c140004038503142821110b4000f035922000301002e8500d0a10800388a01241d052000840349410701d21801d2a408294041c4a1f800903c0303074421000e0804110003100d01055020038000055142c58a110707601410260341c2d02d4580304104070528a43c10056064a288034030385140f9a80c0d800412164500c2c100d1194001800390000c1000103070041c04000c1025100c3e442004148240040d251030145a41e03004c0b04807038040c9041c80f0020303403036100e10b2812003c0007056901d558100441c02240440d48110811005202d00803001418801d40c002c03070748252410b03e240d803582040c0b500240230304010300840c2c10000070b010085116100000e0b100b05100e070312 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 634664874 1250 634663624 634663657
    0x1211130b16060c05071b0801150b030a1104180b090c030103021c06060506071a0a020906040605030709031401090212010b0a1a040f242a030903061d0f0102 68
    0x120390b22680a03108a070721060600c8002c3c4400300005851144005001e00d0301e01d00400b03150314180459003980c03e004411a01c030244d0150501c900e04c448070440707500c0301c100b901c08600e0a6064800119034401c9070307c007000d441d8881900c03a04058044c1c0006251003002c0715003a5407603c031070f1001040c41c402840000d5100044088002c8050190500a10714600910001501030340d40d5010848540c840d0320110b464030288044041500c540f41d4409401405440046050080140c0482c000b0b10850042d042800340100000d10070622400c8882c1c050740d44418000a8007051341806400780655010481c070034403908244503403ca005100d415070000c802424101c410b0301d0700b41e164540240380f5905001d010070402001c00c0748805525420001c00d11800450200800b82c040040d207420749101d003104001e10403806d4503108042e10100550001081203216041c01c5518003624010030652008201500b0011700101100e0060030440c400411402515142201080100e080340300300f075180c0310072452 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 634666124 1250 634664874 634664917
    0xd0c0f050304020d020307090c11070806040b0708041b030f0b0a050c1b0703050312040201021e10050c0c0a080d0b09090307030819060906030c082109011211130b 71
    0x14840c8005004c240090b0954180ca52215492001d41d10201901004601c030000c466010750410030030741009100c00301c007138042800c040e51906e4a10002400302c0c401c01c41e142020809001002d441080c2c40d09000d0700c407000c42d941d02e103400b002c02d40ca0004165900c0c1211000079003801194050309105480d0348066600d82410b0f05445007444429440180750351041150100005070104001d2401c00d100c0422400f1500c2c0901c002450015412036001030001e140320360101c00000001d50f140c0281c0e200202050582c0e61003e0b901890040d25505405031143d1040d030b0041c06450001071030f4228180c4d030309100713042540302841003d201c1560700c01c88a60041091202191186800d1504188002200303450750a609421030140d1792583c006040c07465441c1010800c20881d80030401c000c080140280c40f580c0d071803030380010a11041c0c5442c040e00303880000703031400e0981c401c0d80b81070440e0380550020015400c050300340b04510381002e03019141220b103214000c5400c4c0c2240c41a46d0081c401045560340401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 634667374 1250 634666124 634666129
    0x24090b0105040c0f20100518060c070305030708040303110304030c0b01060302040f0e06061e0903100c0219050c030d2111220f030f1101082e08120d0c0f05030402 71
    0x3945d00798505d024600d80c2004d00422801050b00030540030a03061284661044010b050100c09070889a00ca03800308404000a500b0000303880e4032420341d0030011400e60b1141400d401829460102c98560307400001003104243d0030290003c1114011080c069880c0e0b00c1d00d03c2502244500e01840001040e02d0000300140d0b10130041a0b40d0004002d48641e0030101550303007400c1800070f0600704983e4440003060f41c0042d410200425180c01c540320344103105203030020798003030f4a45003010071005440780c4000d51002400010842c3d100c201101404440c0321040756840240b0000c02986000d0f03440b00002c0440d108885c05004040e00c01500f80c2e410b03407070300d200d030b5420315000b00a003482040301011105000a02c14801c644000c000c5001e03181c0b403154003d261401085a20a051203039040c00210014421a4121005103000d0080c07c60801c004400912a64840603e443c0d481482d4504c074040d10380e121017100b400035000518078400103101c04080c46206aa000803503003c03c13000181c00340001805803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 634668624 1250 634667374 634667417
    0x605030a0b032404080d060609060e030c0a090207171306020106120b07110a0210080a140c030a0e031c14010b181c2a1e0324090b0105040c0f 62
    0x313441030178030300d00e8030009203038143c19507199900031000b2441140003000102d4102d00503c0341e11030f04402030007164101000060000b107450182c4c641ea164041041001c00081102e4a280c0c0e5003c40625070300d5645455034404400518041c25005508042c800558001b815600881c00383c2e0004000b561607803840f4040b10030b0500c00c80300a0041c402c0c100b65a0241e129a6000d44c000003030b1380c0c0c0307074503962510284050680380d001d000c82c1408800c64041000035105c0c11b003642d4001c5000800402c2050f00404500e1441c0207001221441c1600c0c481e103840d8411740c55108514542e0745410204607684d032407000d04218003030780c080c40804182000d8a807072149003030f20626130721040d400d0302403640007803a40ba5441d0034180070700c20191618102c500704403181e1040c0d030110010300b1504809011200d000810001d82c10061000404900d02510800c840c04250030f8441040d00d494030f0200714440240c1002000650300388501c0f8004d91502070320849a0b40b0030102d07443c9024480c1ca540741150205916410074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 634669874 1250 634668624 634668631
    0x5221e0312051608160b0c090f0121180201170f0f10030b07120b060405060409020904020909090109231902030f01021b0c0d030212070204060e010605030a0b0324 71
    0x50200c0c3c03e800c001841420251003400d0b48900211001055460b010b1503004024104c5031010205004958444c0e40e000801c40068500f860500c245c0c680c0e440510b02590f00540515082a082183c0001010705207080200100d0007640c4c5d90600c4820a0741c9000d6000c800e0341d4440950040800086054a6a8848507049030b8042e03400a00c00f0307a40d403100300742903000703a90b1400060f408591140e0300c1c3c4e205000380c00346c100c000c44026150a2038040051000d01c52071190741c00c038036008038040000703540e194181c40c174803000030700411190718210124030300805031040c0480e02e002120300c14555080d00b50070180c003840600303070003402502c139003042d03c01075080a44400c907818400d1040b04011100280040c0640035580c611120228000506e000d052110790211a400303541d4070341482d40400c0d4002410348034121001800342c1c0c1c40309240085800303807000f9001110451400000001da80754400c00a40c030541e040700c0708002028140080684402c01c8071407214179a0507507409180314080b0509460342 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 634671124 1250 634669874 634669897
    0x301090c021c17150d2409051014010308030112150f1d031321020303033607230910050310060b03041205221e031205 52
    0x29202040320102e003001d00006001d80003800c462202400011248241600841c00b40000c1c4840d440b04008100000910400a00032401401240950300c9100000c0c50b10300c88038410070b0021100d10f00b0080d9980700b40c5c042840107640b501e010036910340840c040480c140c99004500c1d41c607691819038a0300541801000945405440d0204000524020700c21007003002c261013404280081200e0901c20114004e8810540b213420800003a8500390420b291179064034030b001841801d03044c8a41a000400041d400c00030b415201c0002401004520b41d01d6080c0c0044000940102c15480a00400c40c5002e4441c0d291045070700c03c1c0d0060010781c280c001c40c6055500c003240341102c500740a0000500583c0151150200d8040e110424410750174140041940d0412012041c001c4919103d00d0180701c0c800104068461550304500c0030115209000301c9501d000c1411000e242a58210900d60540d0960b00c550384840b078a04082000c81c4c500c14480808581d040101501002d5507194291000d91104c1100b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 634672374 1250 634671124 634671133
    0xf01061505030a2316050721110a0503130902070c0302061c021309050705070b0f10080d0210150e0114030307140102071b0321030608070602010e0c090105060301090c02 74
    0xb140360006032581c8107681e6082c140114600740703241780114001c4d54036151010040104144c40100348030501099494162910031811010060320886550300700c00c0392000180a0020b09205004000002c1c2a4a041a01401d44241cbc3c1e0354481c0d078124842caaa00030460946400100050b1600c100034000b01070040710a103007500104444072080343e04c80000300b200d5101c82c000903c1203c01d0380c403401d0342c8040c140c01c2851602c2d07400c0d02e507507889640c02880d00d10050b00d07010003c0c08817965544040c00811046044402140404102075100c50842d440b41041c14a04000c0c840c014072070410716000c54a51080c1c5a44c81d03400e01c1c42071503182a003e862a90944000c100c1000024964a86400c03560681c000050300d0b216281742000072400c01c111301e80381c0030404000c10710118000464003207070f86d28103a040407078014240c00300394080c0a0707a60201803140100b84000409640642141c1004d4040906941c04000c81070f0800950540a02030aa0450801e20051005480a80c800d00e9055450700448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 634673624 1250 634672374 634672391
    0x90402130f06090f1406040608060c090f0612041a01060f0c0503090612070e062118060c04090f0203090d05160c0609080609010506091906080307140f01061505030a 72
    0x44142e4001303181d030741c81443e5502d0003c07030404182d1482980001d001c0b10103001c01c038948100c00c1c1c0d440704064506103018200090307140040e510020a020f5958003d410703140c464038070350b80040c0442c60440302a01c050000c0d01d2421100d0908810040c140c90654079103815020914208460040c90309400311401d1104002078810f0b9036508015290510000b2602c0c1164909000001c0c919005400301ea4005c1006008003c9480c400020400589501c03a15103182d070340e00c4045240009041000e40d0080c0c0c01064180700c00c4410240040c000d540c1d10902c14400366556441e20822440200c8a8103015044000111811403081e4014144644012406601c8401c0354031044030a0566034003407404200351402c1003000c1c02050192070fa108050000810141c070f4080d000c25001c1000814a0344040c1007032038a14140380d002e60202001d03114050880361582078901d003a4004010340c1c3c088600520408003800c0b641c03039050040e003050303501c00c2d40102a2203080203c01d484070b4001403d0849100e4507030840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 634674874 1250 634673624 634673639
    0x101e0b030313030c050102100606020307060504060209040501090b100509100f05040803040605030106030608010b031b0d0c0b0901090f030807062a02071410050313080403240506090402130f06 84
    0xb080281d4000d100c0c2d02c035800d1500300007a140c001d0181e45960300e6410031100304109a000300c01e495903280c1008000c129a511458503000900c1005a4254018540000480c10820541c001c2c500d4035800e8070501c1c0004030700e00080d24140900f517022640800503110440c0000d10513008850110880c0c1441d906150b1552100c0d070460300700381c00003c001034000c401004a01c5d4140124030060030810020030401840c400866110803055801c2c901194800e05107500700c1d2100100c2d00c3c0324a420031b1014034120740707138110800c07030f907100c061a2400601200408940064614441c404481c0e20004040c90701d102c03aa2200e002d440400c0c00ca408840140020916400c80c500c2090031319501030b03000d000042e09000e084801d00d0f140745203c138080d100f1080c903c804150042c040b070382c03c242110542e0b40c0c01b00c600c2c41c0005040c0b040350070080c8102c401d514912013072058810740a41014400000b030003141e0312101841007145c070840780a940102243c2000340b03840c1c081ea009035201344040c02d01080e016201c080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 634676124 1250 634674874 634674907
    0xf3e030403081e04200321041d10061202090405010608100e06011d13230108030f18030c030f0d03050f13080c1908030702101e0b0303 59
    0x1800c1d40428405410020034050705085299110014501c080d580d0030310340c40e60080510008960340e0701e0028200440a1035608100b108000200242c1160a080c40d4002400f1035800601ca0032030642c1003190310013002c201d4242000c0c8100800020524030515000c800c5407083c00614048452990030090301c1020b807a5401418060b119a40360b042d01401d00626043d00f014444e8040e08241e4803030418000d03182c9c0e00c051000c502c2104000c505071342d0341c81c0200280b088c14444220290385441e045608026001e1b400e0f40c07111083c1160b641100d01d0f82c1ea6008140c40341b1840c10480c00b0300104001183e03081ca9250610320302c980300a01110915614500071a181010080007125250300480094100316418040d80341d00204a01e0040c19030705201c1d611104200045800800349040443c204800f481e082000403c4c201c64100185007032522820406144d600544284006000f01c040907032005119020b1003103920400007021020a0800c0b503924020400500100d5140c081000b040c8a41c005075207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 634677374 1250 634676124 634676131
    0x302041e060e0f03120c01020d02030a0623101209120810061d09180a08130803090a09020c0c0301090c09061715071b0b0a0f3e03 57
    0x440e1030802508054020b0104160250310b03e00c0342c41c21840c00011900c02054901c608140480c0294450544400a40c00381c0901441480610310100400c6074504d03582d00074400320f4101c00e04c0c206040c40c000181c2c03414a15440301054102c20112900030341c0c00e21038030801400301c00440e400a0350003429039079285100444100c1c2000241c862080c0002c1f042c2e41c0303180000415030740c1002520030304101643c43d01c05c80000c0c0100c1c8920010000a04048415480f852030780b1307401e405032041d0085510304210103070001324052200541000c40425041400000c943c8410002003481500c0361401840d0400780d4404884100c031405284044041d0307440902521070054452045c80d0015030030204840122038a5510000010406034600f410304207010071035000e550076502c24441c0669680009403801d0381030700e403203072039070090307541000103001c03840720346074002c454989080c4800c94440d1031b038105650034500c501e841d46901d90310100940c2d45040c0c3d402003000c95400c1c200d40c41c802c00c4503000741640088 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 634678624 1250 634677374 634677419
    0x1c0209060102030a1704061b0305010509010f05370b030403080f0f160909060f030506400c08030d05010e0903040b1c050f04120507210c0804080f010e01020c061303030204 75
    0x24ad006015920f00a82e5040c050205c650109025902d0500003c2c01e0741c6030750058207284008200007a402d00385910320040b40c9000e886841040070b030764400a04244d80220f5083d0300040d01c007008251b00b0b0325240e407264020829400c15588585891b201001d15101281c0c03501c00f84002c41e01c0006410707215004200081c81e0042c80c601e205c070702d18103000d400c008004024042106056680c075640c0040240480c010030090400700d003d070b030001452070b100018968006032103003a4405c0d000800071400402090704560f000418070580c1d80c1c503514060741c4003050354000e00c5030300300344014040c16400c503014101c424004030b4090885c80c401003600c02114410703031700500c0c448c8003030003008184512119483c1001030680340c00d034503040c103030313143e0306a000490400d0340d55118660303a41000b018841d007242074130150003405171035503181d46607003481c3e5036411000c0c5c5244650801d1101d0050940c10b03c01e40c0c0c002040d00000c0c150075550091140440d606407503040341456030a10000c038080840c400b42e4411030446 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 634679874 1250 634678624 634678631
    0x403080c1c2114070c060b190b1303020402121906031221020304051c0c0b0606090301020904050702010c03060e0115050903190b04020f09040f020913021c0209060102030a1704061b03 80
    0x2d05141d8150381d84c5140c40d5000c1e48c240c454001c1c8602c41c07580000d0481d01c0710290703103888400e100c801440f0030115610180d030041c000319241c54807580b00200c8a0140150ba800d00c4644180748036580107443d1107100c00b42081112080c80320b02c050007404505000b02c41981a60854010b142c0c03e2001c82e0000d403410fa410741d20600060180110760b01c450640003c0342c0c20311200300c0c1c98644d101c2d940d014000304420300950b004500c44500345c41c2501610f00e02c4100800074015894581c1e4024000c007049240c0030002070411380000b814800c01204581a03405a810441b1840c5e82d0100644080d400661881e8151145c5140089110001c08209040c00d11031804c00c08142013500410402401c030019842c03043c0c0703400060000152000c1102c4001c945d05a0382445250780764003649000c0350341c040c00650042656056100e0900034104150b009c14821201001f0603244c1301c00490b568050400410040b414240d00142320000c1007032941d6003e840340c080030907107070100e114a003040b50107070703104001003500c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 634681124 1250 634679874 634679897
    0x5070b010f05180f0a091406070e030601050414040f020d080705070e06010e0f04090c09020d06090c02010c090306090203070b1c0c14041e09020403080c1c211407 71
    0x1410f508410101000440c2400e09003010650015100009004603d0640e42e0380c9540003000703480034091030907109600944040e840e0840d0054403012061003018400d009400010404d0300e043d01c5041d51150080f14126126035913692004013901800d84141e070b11070131001d0341c031000801000046c0465403103603018060b00c03841c00380788009120014114505100030040d000c102903c505d00803003403210044030041800320460502c0790054600b500800309060000903c1041d4085a80045c0304544c41c000041200701c00304c080480c02c0300c083c04041000240754200c02c1011444540046960f0741c0000c1c191075000d039940c104202d681d801303000c6040d618000729034001103c0006205080b40e10125081940c0d5203100101030700031034071540c012100441c0b070070b030004224071032080034040143c520610115510760312800d0030b0b15540c010094622291103251500581401d41c180c655410240d642c07960a100f100124148141c505030340705e0350b03084a030340700d10003004002c01c14000d5014900315120a101030030b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 634682374 1250 634681124 634681129
    0x201903030b03060402090601030519022704141b2817010f060f0c060903031b031803080916031410060806070c020d141b031504060b0105070b010f05 65
    0x209001c81c40c500c290400400c00001d611030b5241aa0300242c00d103800299030346c0d02021107000300004104242014400700308e903202108024001104070202c903209841405028003000240c41840c80600d0021400101045014014150303064200c240803001c58206000514840081c02c0380000d1a05003180c400350701ca00840e042541e0000024800008021a40c10300705800e107030070307103611a00d0204800e41000884c03083c1f2910401d112243d04c8a010301880d010340c10003c001d00745040c104d03880c1c1182407e0760186540603210b504410010a803480c541422a52006e0b2034030744d0001d08007551070259800019041d0485000c11b400746200e01e0355210b0100c0012a020700e407000403001290640e191410512500000045103a0700410f503203005d8410704c4061004c181400c10b0440000c0140700d40d02c0703125085c2c030008070f40103c800e031100e417413007000311030384020591f030b6003984942c12900c0005070000c0b034042a1150001254800c4c103040051400a15580b84459003009a0240004019110f414806407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 634683624 1250 634682374 634682381
    0x20a0903050a21020f0607080702010e0609010c020705010c1a04080904091a090102281110020a18060e011409030a030207090f020909010e09010f1416080108030a20190303 75
    0x59558130041800740300f07007020b140d030320080640700c882403029000008010500c00d41000c407a0f500c8000c140e034200e08044440f00d010302045401200035000d83d0304041040c0d442140481c001c1034010000d801d00003030000d101c02456002400564000808210a0f4503d0302c50f400b416210303a200740c100241a0841c510550010301c0301902e1159123900400c100d91222403851100b101c0300340da92503a00c81c003010b200b505440c01243c100559006000b42d401780301d48194282e01070035151502d51281104080c01518296a50469000b5007020600d07540c10410f035940305051200c0100001c030766452401041c0e1000a280200e980e5080b00140c1c8110000d0002c0442070241c0301c0c026900120a50400580d100020301d000814013401a208242c0d2000500e400c00940201e0800f6140c05010011850f00e6900301280702001c42c1d410f040213500e140032408451158503914102c8440c540510f00b0400076013000c45102c0400b00900358108040030300010b1840c02170040d00e1160006040d81501c0e50061328001e400d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 634684874 1250 634683624 634683683
    0x151b020d0822020f04140f0907060e010503010b0a02010f1109040f02030412120b0402040306050601081602120a0c0204020406050403260403110102011b022a0a030303020a0903050a 79
    0x1905040301111940c01d00c80d40801a21540c104d0b070030500d00e60740c60080b40003484003c1c10f2507031083c07400702840640050395411034001c01140040e6001292984004c2d141110030036201070002e601000100400d003811006040e00101030710020505c04103d149030029200501344030514100001110111498240305840002008020541c01c6107010f0301c0b104190007a40740c00006200300b07646005050b5030240e015080b000e10003001103485649a08180c0000c19003124031a02182148002c03403400703040c0405900100b00c59500070140e01c2c12140d18448981c024104010a1100070042c040040c0e0340c038009400541a142d40d01030f1554a181050b08101089142020704480d03401d229401012030b020884d01580d4012a17605001e504603c0100d0041280e80701444546103032907800c0151a9000ca6081d1038505050101c105544c04140085000d41400d4401c2e68041a004402c10001c0c1c000d0b0003801044115040801070303240c1e01d031101e5080041120040311150490480d4000c2c0f0708814050380c45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 634686124 1250 634684874 634684891
    0x531090b030a150203040302030d09060c08090f0a110a03020d050622030207050f01090905090f0616022812111b01120b04021b03091f0c151b020d08 65
    0x1d41c0c06a4443c42c42c01c503a907801200c0801d80000c00a000c0c50300800071a041780860302010070004c0e000e814018000c15003502c000c00000d0040d000310f0400d42d40042d4803905840703200d01418148805a43d007a0780c88620140381600054020000809070341d03005019030119000e035000d044c2600c0d2041c034010030ba0030907801009179049280d40f95000b0907800100441594000c0da0b1036414114804016503441045078000c190351414001003013074000c2c0200f12181c840400c502124030b00e80710004c400d003000742895940740059101c00540801c50b40300da08000c1c0d10440796814103c03004940c3d03c540d032100a107107101c04045141a000324088480400c190050301203980704200d800258000000e226640310040c0c0d0a4840c2c0350000b421b01903a4543c110f0360000c0740c0060103640359001849403611303500b100d00b0b25031145010078409000f107d040c42c403c00c00300080780d8840310120083d5851240e01c501c500303407100d041c43d540d64000c1c2c00203100c0d44143c2e070101e03450b80040400b15405003000300320290041400c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 634687374 1250 634686124 634686133
    0x3040b010b0c030307080c04050a12110a1d180303040b10050103020a12020d0b091003020108090304030c0612020c061005100906200c0303070803010509100b07030531090b03 76
    0xa54142e000300a9039000040c516000e006620b92044042c5140240d0b040203500c84190100010b184030001d400308a00ca110f0300741c6c041620080d804101d415041441408030307031302800c1d42074000e68002c03440043d030290000d038943d00b07418808a107032131071600111421038a0101140600080d03e800e44003090042909103019482c0502480c402071044080d044030011190300821000b03030651303150b00b29405540025204484500d0240c410b1b410080d080c1c40283c0c0411001c9006c182c2d103c20104c203c1d000e40b90040c0303060607039510f850350480e0f00381c41019035032030600d074240400903810074240406030042181d9025070070554203010803c084a0030380304c041c8041c440c20200401000b900704e41188016013400040501c4032000c500e800b1300304010700000c0d681c50301002800340108000f0034081c6069079002d0314620841c0e40c408909003035842250207900c0303d1180a100c800002440780c40100030385400c4c1800d807800e0101d07990120b07005496040ca0b20001c108d0441d4280511201c134456150210302c02c90061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 634688624 1250 634687374 634687387
    0xd080f031806130f0f0203100c11030909010b09190f03060b04150b0f070605091b03060408161104020d0b011e050304021e090a0e01050109060b180418060203040b010b 73
    0x10007400702c400d43c000b480e24100740003030002e1010010011000680140c00c4c0c944502c808000503008040610b1000f0106c1c90121014803c280c3c00070aa880d141030103814500c0503403c100003160b4075080400c0f50b0b50302c080301d5890a0880a01d1000603c01409440c0c0203031100d505510705030b01501c0000d0401e50059182c01582d5403104c0c509414101201c042072002c66841002011145107841601000f0f00715134101420f002c103100c00042c913030300c1c034880700e03621a842082c01e4400c1540390001900d016202c0e2070140b0001d1407145441d1010251503218041d47c1c4a4801505e02140690b0401010400c1050740e84220300900d5801080d8512504150300090302d2039055000d01815601000e000031340901c9406011031030082408003c0849100000c0403105180341070f0440102400681c907440345603508040000074244410f0081d20141d90442c196203040040925102c940200f0507100541e225456000c0c00620703162440032203182c40d0180303901690342e240c0343c00c2242c1c1030b0300306910403d24010b0801c0740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 634689874 1250 634688624 634688641
    0x8011401021203151005070308010506160b07120903020a1401150e0601120c080411030d120b241b030909150d0c0b040302191505160b0c04030b06090105060a0e0d080f031806 76
    0x1e1101d00c0760310090a01c0ec5880c0d4100071504880a141a850310a03d00400c9100b810340000d020580140b044400d03014907507843c0e8502e42030b41c2805402c0c01010010b03020510260312130072030450340a041803600030000c0084011140c02d039a0074107100c0020810b002c007407005011540d00f224040040a60080c400d9040e2904014200c041d00300500c0132460b40c40c800e081d119504d001498008504108451024804c3d00b00d5144850344484548242400380c8407030000c001c000401665000d4900801c03c00140e900c50711483d0041030000e1007254050254080c440010b2114405200a00511450a521076065105009800000045150b1003a104610800100c511a004e064a8401519085407140485081499004080036008201e05100410040da549260024100f1280517034002d4640c0d80b41c840c240a58200280541030700004100001900140501c44001791040d002e886128089140c0d1501521504801491040ad07035000081c000004040c40d189903041c0e0f1904080c00c4142001c001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 634691124 1250 634689874 634689907
    0x190513150f020723010504030b0a05061912150905061f090612030c02030a081606052511070f0b040603060501091404110903030d09020108011401021203151005070308010506 76
    0x44c1d0302c0141000b0f4200901c50340b041003510f00030342d070108640f4a241004602c12006c2c1c8400c031801406003000c6d070002949910b07419030030707030071210340c1c00004031003141c2510380301d00e16038600451090081c0c503020540c00080c0304101c0a441884e2036290389401070310740410580b401c034a07507021104081c2030440c1071041d81159210644c3d0386515040400d000c0301140b001c641000380c2404080c3c185240440c2040007503190312024050684203201c10170140da07032120001480703040b60310000d007400d0072401201311090250310051080c8d840c5c40c0450f04c070300355201048000484035030000c41000b680800c1c108000340c0c0500030360700031346400d00708a001c040c20141003940740e079216003180713114030740700c200700014084001c04071850010b01505695946008240440250100103422030000d01c40400002e42c40c2400420301e101d90388141d01624a003608143c58441c2c80d007000d40141c129202a541404113070795002124070301411141c603460b40310082418003404103035050740300f903000350b131704101d0486554400c54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 634692374 1250 634691124 634691159
    0xf0c070f1e0512070f060305221a04050f0f0a0614240a050405071d032404110603010609060807140d091104050c04030c05040b0303190513150f0207 65
    0x71102c044807000040700c0f61034403100d42d2080f400320301c1c43c0300007254060345504424810710104400d40e84450845e003144240f42c02580001d080d4600f54912a006070368020652600680110102d4002406081c0804d040c41101d8488581035031014864000b00441030245031100d4a0003800f0340104e2420203408a1407aa0321130400c980b1590416403500c06580704050354000e481e01030401c10042c500310764003030a0138400e12484181c1c10608a001c5400e4980003070b2100e9800e40314292170211041030b0410703250414015100300d50b800d054071249001d03910b529010b03600800e41c42d035804200e18603000024064040142991042200d00d9018049a08941040725080224107400140c0101c071410030024903000490348581c05401d080902101d80c20001c05401680d00803c0320358003050f0380b9810881100c54020300c2980542050019141c207024499502c980da611030708146141003000da150090080481d0083e0448000d0030518803980c682c03081c116036095240340001e0000d242400c10442c4254190f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 634693624 1250 634692374 634692379
    0x3030903290f0106030e011e020f0906340309030f1b030c081002030112061815090b150d0b0907030c0f030203160e06060d020f0c070f1e05 61
    0x90704491041d0600c0c03045035445210003079200c581c01c1c110402041d00d8000c0c07013201c000070b06103c241740f250081882082d0722040454052a02d00e200d5a00340c4001c1d4000c80590a0a24800e100008054584000511000340b000031000b40082d626034075180c140380000c1076500b0048444100c2c400003604162218143d030b80004025910310818a0603c8002c44140401c2c8880c0300080000000c10988999070703010344030b00d10159040789a400301c00000302e000900c40c07191160b11098203840460311540c490381408085031501c030710804407920b404a891045440901020b50b070391607002d040c00a0700c014560071440540300d00000d6142c03200002d031a0750328a40081e040303030440c80105005220421140c0011944a074180440710350303900b0880f011904911003640a40174504461000202a500c402d0a0760042d0960540903141c0800b807241e00d4001840d013098072079080001d40c00803405007018124136aa250020f050701800d040030000b1844565100c8641429450190720302002440c10707007400c0d04c105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 634694874 1250 634693624 634693643
    0x318030b040602070c0302040e1005010602011515050c031606140105030d180f03051011090607030c1a090105040c0608150409051009080a091a04060c11060a020109050f0703030903 79
    0x80c2d01700002c1c0c103221a40002d5001d443c1042c0c00315418401b080ca48440140c62900700000da0342e92074203a0903a03502013278444d0100340300d460030f01900350804910f00b00c50019103080c5007486c2e04814581d1a550192640d4030307c3c00c3c46101601c041100764041c20b2000070402e502540c05500d040003107642c0700d040c0b8030228103007ca00850641ca40207008040350040040403000e155144e62414601d07141e450300041d908d2601d0401c42098120b02c01041104c902c540060f003003074500640c94404860001d560002151034109104022092001c48540703140508401e06c00043c0d107060520302078116001a07030200c014030420404020f01e03818005801c2d150202e00350303008507a160584c43c100f41040070000090050900d0110240207120101010f00004042615103180d095251022280b030280c020b050f82c1c160760b0040000313204051194980c445e482d0301c42d8900c201c8464407080001c00c00e4020f14002e40060703544030401028048100206c030028031030200545102070440d00c0060182c1c1d460300014164070b40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 634696124 1250 634694874 634694887
    0x1e0c03070f090b120d1716050406140c01020301060504150215061309060c030b090108030c120f16050c010f0518040e031603211a0906060702031501030318030b040602 73
    0x40d204d154600c1ca0302c0c0344003501c0d0004107540e03002d0909140909405a0592001c0004d0440c224002c00c911414070203854140c145440c1000072030b0510391a80314000400380a000504400340240040c47c042c00715600c4090700e860400d41420140214045610300310750001a1003110800600b035031b5904810309440e000c114542072003885024140501d0028005440c000d075540c05079074941d10111491001300c81a46450f42d0b00c4c00c50a50346d00810a001c88140c12009a0b0316800302c142005104c81848110406e04201d10f840f800f055800309414240d505030450390034100c0d1503901075524001c2e09c00500b03110f828a400d0310114a440d07180482d800d070055590f41e040c1139803107000300145d48004c04c020042c0940c8a88030b04c0c00804e00d01c1c3c4c200316041c05580c00004007035064018018080440312141035282420038040401c0340142025000c01d411110802200001d0b071400e00407581c4c000c990401082c910b500d1031500910907040c5000001402ca010780d000c1c0009152200c446400c1030304891701588808 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 634697374 1250 634696124 634696129
    0x203161104020f040905150105030108150406112b062106090f060b0f0402030712110c1b0319050a0809061c0b040b10020d0809030c1e0c03070f090b 65
    0x31a024295030f0740301010038000781102d8035400031841101360111064444c41d100005440340d000038021005a90010701e484070f00f800110015940c07240c0a0344000c02d0924601d50080007691181d0001072040b00b12400d106a0000d40055810034264021800c001d0a481c1c003200e51030652100c070140c0d1040c00315030400c5003131000c47d07001648480d400c02101d100082c22480c0410041c40304568042c003c04150310704032400d24103482a0ba1007007409850308502214010140c6005062000c18201c05180a00c260114a80208144074020441c400d0200c1a50000400c041c501484c18001c0d58805404088542c006032011450001c40c0d40c0c40000c1c5d07600d42d680703000054200c2c010280c41c0d5079551500c113150b18400f90303030385c0180c030303503680180c0e0b0421076a5810300034468400040009140540e000c2c4100c20314003031240c140164440002c000341c03818400380d90249428110441009c100380101c2c2140168005014083d03104031823000c40c0200000c030b00c0e1000c081e4044c0c2d00c0e4810f5200c500e645a41e9110f058 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 634698624 1250 634697374 634697377
    0x60117040516121e08091309080307050a0809060c1c020408010c0c030e0411160f0b0a060e100e0c030601030209030607080a1a0609040203061924020316110402 70
    0x107040190907841d4483c2c009008500d005141034440c12032100e8042e0608510001d40c0c45121340040c025441c2c0703106401442040d100d0103915131442da50b5491004081650900910f00030704e41556100d58503118400010305e1180050044145504428184081c203044031045079061800d0003040e10340b5103000032810780207001b2544400050750801c1402217100d82d000310030b898440e12070348400b0076042e2481c0910040f1610091101068001040307101940099800446016803259050401e003a0350799440002d500000d4030340c100442c0e03e44c402448820410280a40d2095195010680301440e2011540b540c0f07001a044081881e00040801c200e6442034048030401032010302158400e081100c00105100740c100c545020359490010040b8801540d000341c0c6c129400d0007031019051035030a100708070096001130011603108400343c2800c10741c22107001508004044c49641c8200c441100c40d1075003841c6460030f02c1101150402c2010106018141003079904460b0080e500e0441203401101080c003d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 634699874 1250 634698624 634698643
    0xa050f190e0405010c110109050d232d0307050301140a0e150901090608070b030a09050f03030601030f0b01082a0d0209130e07060c050c090c09090f0601170405 70
    0x40d001c0344070400c024404150031019040c207542c2c4c0e0b01a92204041301071400ca80c0d041c10000c2075a08444071089843d8481d0280c01e500d140740c078004e1650182e241e01490b00c0d640c0156000c4102540000e04400e40010305000020340d40480d4400c1440d518060000600d5403005003c2c03d00d0903510124055031a44444e00c0c01005400001c128014a04080044041c80c4043d41045445048041c00118552001b030180c44103c134030110040ca10541001000d4aa03030300024010382c400ca07074486440010410170880740f030170004500080c5680341002d80006081e2119002c11034142c5003400070000c00799030f010100c654401e444500015800d0050400080c2e04c01030998613908012001c901d00403480015802001403d000303d50014200102d407004100703944d41200106c2c1ca58000400c20001a8001c40100800c54864000d035400c84410000042d0142002da50b0101c2c2c0843c0404c50341d886040c8034050f96001661003000100c0c1d41340150000f020b5490400050494091540100741003050400840e2076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 634701124 1250 634699874 634699889
    0x1605031f021c0507081005030706020d0509130c08150f10080403020f010c0f090f1a0309010e0a15050a05150d0201120617060a051b071e0b0907050a050f19 68
    0x518204140000c0200f501943c415098401006d000111440c0001346107003212101d80141603161000b440c02d4400b50030403594aa04040081e514151600207841250602022034480ba002c82c2400488010000e47d064100c5010303407a204550b000e0740e80c500009000101c598a0048030a589a2070101d051441e43e041000142d803c0101d101080e5400c00300356180d40c6603950b2500009540e070200c060150000f0710810840c22030380e60840c000540544015a4844080e00001c10048192481c080c940074400e501621042c0140703600c0064240709014194005001c3d01c400d00c981d0401e4500d40c184842084000d51164107007604004c02c40e40114101c8480400100c3c0411030325070b0f03840d40c0c0d903040420403224010900441000544111080c413402e030050350701c0c4051090114030140c11a42542c4001025200750010095802240d102140e0881000d44110b190384114145000c20903d001d1507a00203a10402011800f481103480e14010541030910880d0310081d8000800700302c104100b859044040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 634702374 1250 634701124 634701131
    0x905010213030803071403131407030813150e010206160306030204050a021b070303080106180e090c040b030f0a170909150f0f030d0f0216081605031f021c 68
    0xf40480d0a0146203e02041d48508072024464a800342c0700d44012101e1807080c2400520354004070700345000b8510300b01d03184412560095269140c901940d00041c200d9054444840414401c040702c4011600c0388140d00d0502c0c01503145e0000c0040d403504c10051030106640c1c8811507900d440c3d8840e030429802180c014004110a0034040001d40280d030054003525090605079076400e60f0300c840000c0c504200c4e0313015038807142ea590038600100e0381449007510200d940d205101001c5502d40ca9051072030f00a04030b1000815601a010342480150f440003019984030750851650060340000c042803609403e07a10104143d51500f000301d901c884c41c0104600306070440303c2801081903c088070681c0386508842203a030000803108500400c00fa251a1007242d83c0c00d5001844020300c0319025000e80702c0760318401d0056404200820710a005025081d521480b03503a0300240510781840041001d0001405042e8054044c40e103901c80404110940c2030b0801801c01d9000440c12a0701000030840d01c9004018241403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 634703624 1250 634702374 634702379
    0x30403081b0412380702011d06090c120c06070f0f050a1a012102010e0907181d04021905030109060912030603031b06110d021b1b040905010213 63
    0x500f11190f69020444002403d161400c003004001079031119000800a029a112090000034034000100500400299900c0d0b004d80d40506880c401e070303040604400001003210b0b2070100795403032414004100b624052178141115001c4660040b40240c4181016902c45644450034941801c408001c40e1015221201c0c2d03010140402402060720000030f0b0113070342c034500c06802d00c680b03504d07680380280304001c050110303140d02c503c00b900e4070b03010034500d2030050500c1c43c000c11161000c030750040e030308403009000030b01072544007050f05094903d145e02030304145e540e40300703225400c40b000445880042d101038415091840c106282c00c15100096010742030141c001e200c00005031600b080640310704d081c02c0b54242e000030354240d1214840d105040c212605035a645584c1303e507a81001b4120780e114039056907219210b400414010300000c0060012450b0f100c00160303140d4640101c0b41c1da03040840b008803020313040300245a1501c80c0180c421901d00d0022034000074680800d1800500922035000c00718034889181100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 634704874 1250 634703624 634703639
    0x5160f1115190b0105070201030507050c072411150405030f0c0c040b06030412030b040209030318030114040b04201207050108010803040e010b0903070806090a1e0305030403081b04 79
    0x200c2d01403450440c126404008a0141c481038941030401c3c503002440034010ba90256100f5040907802103001c1c28050318104070112031500b0314045400c421002c904001c41038003038100c5000604000070a030700d040c0204908000019844085404000107500e2560000c10240881441155000c3c1d03007141c02c0541e1003074041642c0780c0301c072094035003244580c1c9480c031034400d030b0304000301120f1107644d110051796030078a500302041e0020f0a9048080d0317041a402c1c0720b0710915440410082ca00e01090440c1159600400010142580c107042214840da00c812000d010006401c1030045030842d52000d0308114500740510050003680d208104d04da8400ca60a5200702c1100010612401f40c0f2007c2e601c1c030f00542c2e2a003514940e00c0c4210311404401c0c1c0c078180010889004c00401070600740200030b09949103181e5074000c6074500300090720000f000d9004114000200702c0a4901940c0711a1a0075850000e4196901c0107851400010000b909204040c000244001b800d0203114030b0500c081301e1a076840383d0700c8184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 634706124 1250 634704874 634704913
    0x702010905071a0307230f030a1107080a1215180e0d090317040f061101050a0b130504031733030705010c05010f0203180d0305160f11 59
    0x10140d03100d002e203050120312041c24983d806034810007948158655140d800c421034100b00e04074015560541e5843c040e048040340400103000406400311066240d041403030f00b00080700d442c07055544900100700b103240c0018286070192400c3c00424103101940b00016503110019241c0301b210540350002c00351020030504403150340b02040380000d101c2045800400950980c2e509050800b03200460342100342080001c030042d000c0c00c84e540444008508080d0b440208140004258102d180860b8000c2510300005a092088540c00110050b0038480f4001e84000302e40c0c260101100c00100f0b580300c90001c0d0906000d0708500308402a00f410144203403603e12108a000c50141c00d11006003503507407003409510b908410114440e02c5d002009018001e01c0c1000656480441020450701e554946443c47c031501c2007440594403a11000c03125840c0200659005800c04001c4021070091515007424030821803800c000804c007414180c1482c03c42c5120038101560b81e030704174410340310240c420101194a450f20040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 634707374 1250 634706124 634706141
    0xc1407150e040b0913020a210224030c0f120406020c0c03060c0307030e07090f0219031404062007110109060801120312091509020109060504080a0204020d0e06070201 73
    0x1510100442081010041a601200d0f00b0341d6000004001003068001055406002c0c10310003050300781400d54642140c0f20071180302103d82200604421090107504107a418030000c40f89200c55036010110568040b1107500019005950454000c24803013a0300c07800e0011035580b0050441800030f00d21701864440003130b40c07120b2400007140c080c0500128160600254950181400d403a115081d60b860b00c0086000301140c02c1a58000d00c00c10700300050007081171081c001c0f640e0f0034030005642c900444001c00160365103d0b2420007010f00d400d80000442411045075a005a0300801c0401c0c00714810303a464903940d2092a428402e01c0300000d40d0410402040907400814100ba246d0008003590347c441605c0c60a024414200c20315500d002131400070f4030424054101a5003107000282420894480c520411100030000f2115607460017a9400e568000c050300000f01441c1c9401490541000100c4d600c490780102c00034010354010941c5001594103400c07840d0003103050b4048440d03500c1d0034000240686a01c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 634708624 1250 634707374 634707377
    0x25080318131e0b0a0b040909020418121e1b0203070b0a031a06030c07030f30050f0702101e0203091b04090b060906010c05030f0d15150c140715 63
    0xf021030089401c14180800855107060066400c10303162900c0310340984030502c4d0482e4056a585d100034003075101d40e42a04000e5001c0e4040d6a00984020800744c07100c501d030382c0c1c070b000d035231030140300100185522100030008896000d41da0340d000c103201d2011038500407141d004688200c001280b003041190b4160b110a12104001c100215041400001d0295a210980d00c0f813900301c50810400340424020102410300c140305113002c0094105440c4103403d0310f440600f105908000d82e401c0f0000301aa54007506400540c1c00841200358102003001039951a0025000c000c01615145044022008000562212200c0050655692a10504164907013008039501805c291402407250b644d82030600c18814000c1d84860703071100603183c2100700441303100000c01c0303941004090701c550000a541030024101640042040d95100c0000300200400d440d03a440500950b064055800c02c01c040f00300b0070740c400e02c014a081103c440620384c2841483c0154003401c28074640308441000581c1032003503a151070001c1f04d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 634709874 1250 634708624 634708631
    0xa0504020705151005040203190b0102011b030c0203090306011d0901020702010c020d0807060e0d0f17014217160807030e01050925080318131e 63
    0x444040204900030168080e019600001a01101101c90542903411101044d010260f06a07a407000600740d900c201e604200c1a12100c200c0303a058906405000f50001007400248880a45003000b580b030002c000c40c200c01019200c1000c1081c040c020b2084508280340941170b10310715a10391000c41c0007601e184002040001001000990a41061082e42c2e03405a0584d54025051910340030003920711310b085000d40e0b040c5400c0100c0c000181c514407504586d01151005030107120b0744000c020302841e6041c440242032069a140d0500c0d410000c170141415a8204100340442d60750420110108a490000b0085042c070841611083ca61000340c0705030800c00ca543ea5140035540c003c21703800c0704030710503100c410001c00307031500c2c8010450084a00c19807051b0280b400043c00043d000456081d9041920300901d2504103245039202c2607000d0000d94400c0d480306500072062031420024075640d2184071011190615071014082455413030380d60b440c1910500d14014401c60391029407101900c00404400d0381010314 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 634711124 1250 634709874 634709879
    0x2030d02030301140628030603020906180408160b0a061a09060d1e1103040b090604150504170c0c040b19060c020402040519180b09070c0309170c0a 65
    0x3000080324143c4400410040a200c010300030300000380c124a040303d10000e41c07546025428031109a040035140700c01c0d03070b0208030289103006001080c0ca010f00000d006148908010514418000d00503800c203034004070031a83c4814000b0203081024030b8004c02005541c1b154280003217800160000000c0e180000009c1d504200a030000320300c8c41c440c07120707a030f60416000d021554a07001c607503000f48014846400b07048030000b2011030300b03001c40c0caa00c03201c0c0b40342c1c0a020060209104e018180a58132400c0c410080c00903051988444c282d01180e000c0640e026030f1600300090030405001c0e03c912252b40c03101c880303507181c1c09004c41640c0c548854030701103400380d0320703080c81c200c20ba18081c202001d12007540d44c00381107814103041089038100e0b409035042e60000d401b0040050503440d280b80004d050303000d000806c558281006a003108060b070340200840540d0510016010542d50515100c2c0c0000e1075045c418030540403850159000000c56105400d044000841005c6038100882d8080030f00400b15416108141c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 634712230 1106 634711124 634711127
    0xc0308071106210c0430050d0e09090d0801090f021603030209010f0507080405010804140d03150b0304050705090402011407050703060609020a081501030b0409080702030d 75
    0x104a52005801c0f105000c0040b5000070852601a00d00351030040703014120f40e58902c1880d400b031541c0c000450192401004151042c0e44241a510f0710b046400001e40744074031034408640075a203081c0001d4451700c00440e0800c201c00c0903071600483c50b401c25141100804103d552510480d40c2008281c070129a61000059064401d680151740da00204000400840c46036034250144030041c865035000030303006e10030b80341500c00a291403082d0350f072182441c48404805007100681801140d0036001c6040e49038001c0284500c0311558812026526060640790344421100074156407c20b00741030005243c0140407a8001e40145003c00340c0c0411440303c000035a00044040b1600e50003503100b00200302c03ca002d080000c0440c05403c5060010511018080c402e00070314104c0144000c0d12510003d83c040d90025480f420060700401811a4a25000e070b51980300c584240e1003407040c00084080075 = true := by decide +kernel

theorem cover : BRFrame.Cov 634532374 634712230 := by
  have h0 := BRFrame.cov_init 634532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 634532374 ≤ n) (h2 : n < 634712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
