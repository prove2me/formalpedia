-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:55:57.212589+00:00
-- url     : https://prove2.me/submissions/e57aee5d-3aaa-4e70-85e4-1c2083ded050

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 634712230 ≤ n < 634892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 634713480 1250 634712230 634712257
    0x5130527070806010e04060e1912141303030e0625141f060504020424110a080715020306030a1101020114130c060201020f1e090d030f030b0d0c0308071106 68
    0x142450b28004080302c1481607010b1042c0c200440303420103034007440b60b220109c0780c10001c80305200030a0a000c6901c405541000b8040c5000416101c5562121010103002d0f01e219840f02c14030101307508100410350041300417002500e032111509845141e13043d0a89200d0b1072141d02d055132507540032a8901d00344084110000200401c0a1798807522904500a5000400c02903404518183c100340307406107822400c0b0311541522a010015a20f41c41c4a002c0b120410050901a074001010720b20707240c0d21591145070151a2410580b031503c000f10998802c4a010700c20060003884c12150f0b6568600150170b03000030180c150355031101002d00000e80074446612641101e114044858607034640600240d01ca5040340342160f1060003c401c948208504031071150340242c0700d054640100c58011490384c4204a50b054000c452402240d0406810a60b101c521440301c1d04d00b400400003400030300c24007403550303d40903003c001d220100b0404070703100380010315055003d008040d4107030041c0c901003030046e8024031104415 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 634714730 1250 634713480 634713509
    0x609011815181401060e04030527040c2c030d080405150f070807090b030601051606020406090f0e04120c2a1517070f12050c040513052707080601 64
    0x10f20310038801c002c00391901440d00c2e00c090906131001004d90003500c1c000c2d0215078506e44001c40062020401b1422600d00070310600006118a0008108920300c8150241070050b5500845000c404181003095407a8081c00402d107034801c0781d5080340d41c0e080140080d14240a06290508550700c4000310611450582e61049614200b03144014401c81c001000b030410044d8509041c00314200d175a0440780c021400746401c4d501c1e080c10820031441c420304014010005440040c0000c2c0d0586c0050f40f58048541500304c0151042c0e540411407145a03003240d0043c125906a6115401540105020662140903183c2d1b00c8051000b106081d80d005040f00c64620a031000c2501005000c1c400f06003020b100942e41303004521850440030030022964041c01850078010501041801280f040c0c0600340e1000d00988144458282401010025031040c0103241c0610f020120f000b134441160302500d4050350320f036101c503d090441200c1015580745040fa400095000e8104000385000003049018040d14214812014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 634715980 1250 634714730 634714763
    0xa2909030703080a1e0b130207140d050f030109020318030a030516260703020c070b032403030a0c05160e09070807030312050a021b0c03060901181518 66
    0x412203008001c500703001d04000741c50303045c09401c0c0b8403048941000030340801e0080200c000115081407601d0042c0c081c910100300ca006001e02031040d08641a11001502e407030410440b4102d40324070032080c081040c1681040104101c0030107038000c5a1280503071103040d40ca40d102c0c0c000e40d030455000000050000340c441c000d00002400c800c0001c0407110341810000b020700481c005130101045800c2c18501c1c5041c0c85000514105d01907011590480010400e41c1c4d8120348402c04c00d98540c1040e41d0007081240c2c1001048107200140c0400d100c03440008000f0f50501c401403004668500320003004965030f005a695018840143d4018000a0044074450060380d240140c01c0504e0314140fa03000f04016480f2250401c04280c00c03000090b0f6a030340c2040e0201d07295071346031890b031302030711807000910500e2041d0403187d1000c107070102c0d4002150804800303032100c546520900a003070702d2a10010f484652039242898002400107005541e4662a03c40042000800720003085100d8680810070358181c4800c0c0011403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 634717230 1250 634715980 634715987
    0xc0c1706070905030c061c020301150e0103060b25050d120f02090f15190e090a0c0203030c0a0c0f0602120703050f060105070609170c1006080a2909030703 68
    0x3070303114a0514000240300d152000283d0750710100c144050003041c00295074900101000008003032510070003019552941c2d18480c01042810441104000545150380b004641d8400d000d000100d5203a4a01c5a0821080403000e270b17402c0104460070341084001ca04214000b40050098000c640f40710303158460000e01d40b90042c810340700380d0460031048500c1044100569904c405070303151030f44010b5911031070704107001e040030900d4480c004100d0032441c9002074038521181c1c04110300c450000c0a484075103094450712400816070300c60000100251b00180001100a9941e20242040612074641a0440b00c183c0c1c8030130701c1d02c2e140401c0039905c41e500012200070390360ba444071054010700c491400300010702d000d0031003404400d0040d041904004001500d00d00b4030100d90019180c01d030b000703d040b00741462001000e000903405001e5040c0c141c003d2501c000032100c070360703ca01c0084400c0030b405002c0180c0c00e41d480c45580c001041444134407065a03100f9007140307400030200c91300c1007503108010b5542c0d02d244c0c100038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 634718480 1250 634717230 634717243
    0x901020a0e18040f0c080703050102072a0302010503060105040e090a051c0c030c080d02030708060a0603090803160504211e031205060102030d0c020105150609030703120c0c17 77
    0x20360040710b940d103400d50000d600301c00c07070360348603400000c4a500d9409074907107400a0040c40d406002e031803040d0480403007400019070080102500c10044401d01a00403e00c801c8440d1040150018004100c5020000b550082004650104051501038030b0640c8480c141d4115401c26225466940e0040020208105040023000310144500d10318807452902e24800404010710742e400201007040d00030042d000c00c00500c0c00d9850300c2d91814011354032442c100310010710003041160102c0c85100090b0001807018040c0c8120703620b0340d4216008900d19900c440424028440081500d000c004080000148a186010805161440b03104040c00c288245041c210b100d8030110501403000031081c1640e40010b5049126950b110440c04804203056480b000181d08500500140d100043e0901c02034106542d41940401e120314285240b210f00c100110301804001c0c0201001d05070540d10031501440841c00150859030b00211a2504910740034203980c41400e07030300341d075030086140d0801905c040398804000d00c81c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 634719730 1250 634718480 634718507
    0x62e0e1009081504080a0e04061205030913050c1e1605031209030a050a030e010e0714030105010b0703080c13030206070303020304031215050d0204060e10030c1d180309090901020a 79
    0xa803583c82c18640c0b05d0a04a100e45202c500610040860914a80d1182d8008400501284950a40040740c0342069500c980c0f10b02201c0e8420382d440d003812203401c01244185805150503240719800c09040f03080c621801d1544a4400134008401e0298266105407080c5a5002920500c050741c2c94100b54419214042e00161600302950418010040d040790702900b80c56501710145008910b02104803030180c018540c01041c00d0702e60081f65004640407400d8010703023081160a0380200003503030b40c1d440200e01a0041c0c60009000450450218603490052005002c401000b5141e43d01011359035800500e0942c0703c00000c8000c2034010041009040c3c01c600c03006d04200103000244070321020382c4915012801280902c0c3d101d41711903400c5d54290349590340300700e0141005030068417032400c1840542d13070341350460320040b54140390003007001c40e000c800980008500c1e9114490040030b520b8001c07590900e05002003240110b884140b003221003a40d621030009004031610b0000690310b800d21240103000b8000c1015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 634720980 1250 634719730 634719763
    0xe070503100e0a080a1101050a0506030d050304080f130b0a0806040b01020a05070504020307140c0705040b030a0312020f0c01051015020d050d0203151f08062e0e100908 74
    0x5541da214000403c00e11589a8070500f0726548448040741a04c100c2d0101a540c0c0b00c1e58070308010002995851340c0322900568044044524884120004507494841107034010402c0a00348004104460340c42d000e8103c0000c0d2042109119455a45144182d0840156240010505020f11a07d42400d1194242111007840900020500b644070f140d0f480102e4404c0d02e001300c3c1c0c0080060762140c030480310241202e02542c01c0a40e541c0100000c0d81e0740381b016010b010300c5945400f400000a150015950070001d0b4140c55421504000700341c0b401c001d402510b003225403484200300c10b0700300c0c02080c49180d201c0d10f050800c203940c0c2414003d0b03020045400e414407a09542c451303000000340f26040410b494030302005074009a070741d9456074120b8440301e00225055801500c0030240c8074406081d9240300d420644665030b8942680c1c0c0d00800c0001800d0320001e17503002c00081c0801081c048100320301c80c508140180c285403111014150116004a8424a00701700140000030300b4008090f09100103d9100302290 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 634722230 1250 634720980 634720991
    0x70311040e1308090301150e0a050115050c0c0409060905070b0c030f03060f101e0219060510210201020606060703020322030b070305150a03030801090c0e040e07050310 74
    0x1c16100003070700301400300c4058209403005201042a51000c841191a02400034054158959030401124026005900b22000302e400028101880f41c801c5c20b040303440b01d0b42d011390803542c2c80d0010f896550004010200f140100d90a00300c0e00e0b100d6028500180c2e109100c0010f008555082040c24001240c0001895910400640032105400410341c0d10360114404110354a89072400000c06c1075240c150a01d42003d00024284109174000041c1100d003400e01061030511032507a8812a2580000321850500c6000c1f01d50907401305441380c0c000741e0f20040d00290340c140580c907440501c0b17840f10342c41801081c1c50072160741e200440d40c0c1030080c550001d0781617801c9810080310369000707510b900840a45034902d00a03440001800c030150744040c402941c1114003480541040c48006001d042c040b1010381088034180242000390601c002854200c03505a500c214080c0d080407001805002414080070800143e6058a0078a55503449052401c070b000d800285603c1d860002407504120f0340a4850362042c0c500b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 634723480 1250 634722230 634722239
    0x370e06120705090a0209030309120604120e03070e09030d1b23091c0f0302010c110d08011a09060d06030c0b0c06060f044a10021b100507031104 63
    0x281d051038110344c0348280541c0301d80304030001c80e1075402800109903104d0442c0c0c840400c1c00c503020505a000754056030445015503d02c0009490300800b8010340c40d0103030320503c01001414004207405411081c0c24080d03034901980c482e0340800b40c401814040181d415202c20740511150000004810f00141c0d800c480d50485001050494500400391011300401c5171000c001020005110500045a030080d1030704060420750030700900921030501102c0101d012a007580404100016600586c45106d59030a9a10303828480c0041c80f10300740c072106000480d410300c4070001e5642d40d100545101916694000b4815240d030070540d04a20603a80b0094011004115006810030f01003021540820155051403100c0703e2800403400500008040107007a101c42196a101e03180c1000c804240850f040504015001c142e00326001c02803072406400c44164020307000a01c9148094002d49810341e42d058246480c4520020010304241c11348007440307240c540da0340c1017099050b018032500d0b44a18030004254101802c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 634724730 1250 634723480 634723489
    0x3030537021c0c0f0609080403030503100b0304020f330c15060117090a080301090203090c01050a1b0f06020f03010f080318041e060f06020f0309370e06120705 70
    0x90002a148050843c0203006010b55a00a03014191f4418a01c0b565540e9a0800400d80d40044e01e8031581c05020a0740002d0f10b01195056078060341d0000c100c03140c0082d403401005140000340d902c200084810204078883c01040076900448124031030403855964003481503031810800710741e05040ba41d08031203051050a99020a4040f80c80c0440c040b00815034030781101e81447c08490364001480320400200108140c81f06802640c000c0000710100c5000c420890019905806417081800c0041c1d021041e00c2c00740e5501c1c10b6881003480c0900d10120705030083d611040107070b030300c50982c0038100000000100000000b41d03180400038030001000e1420f0003020180303508103140303813500f5610890301c03900c0e4005908547d02081068118049007080b4040e0390300c142ca240c180c0705208078030140c09405e4039440c000d131010080301c50590008180811a0402580e20348004181d5000980480b00d441807051016007640342203405820201d940e01c80b01d190070400c01c68000400b8030384220f6500a80740c20070840e200c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 634725980 1250 634724730 634724747
    0x100608030a0f0509091306050f1b0702060c0f070503072c0c13030302010e010f0603050303041721010e060d0309090b040b04050406090303230103030537021c 69
    0x4192400810b031401841040710b00e4021070111540c440041c006100e4402028108440101c1c4200801e000c0e90341c400381c041c0101e410803208403142c00c049e142003640542e6072000500c4080e10081640b8202403105585034030b8403140029140c0d00d940910410b12262800700080300040ca00490f00010401c5480888030800100502000400d410304011401900b0017000340c8155501000700c140c03940340ea0341002406068a9480c40410354a05480b100b50b1034128002c0d03405a0b50000d00070f62850725513946240c0c00c148132586248190f5802e10101003e0000800c0755804994404900f8a441d41440c140c8000c1450250200348249842c05d103510010350020514400c03522280710010b10342d0403034800304002d03000c1c2c0e4034810740c000e14000400c000c016840e400f2281c558003aa42c10821046040c890a1102c41c110072401c688034400e00040000920403001892003140665000d0700f00e030220841c030844080c01c55101c8003086200b80c8440e402c030785c1c100421200f80c0c0915000b114503002041d8050f00020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 634727230 1250 634725980 634725997
    0x721140c072c0414070f14060a2607030e010902061903140109020c0d0305040209060103050603070b070606080c030c03151e07020309013e070b030f04110d0b0109020304060b04050c0c10060803 84
    0xc0b000715000069600032b4810440301d40c1485090050151841e60b4280902d90441d80c0c0d80102e45000100e410346a8140b08448645a015150614012060080b281c0b600140840681007540b5800000b0301000c0d01501140200008407002d81c8406080a48505240b800c900007000c040c542020000940c0d51401041d403c41001c1c02d001a081d143c00c00860305200301c9410000c1c800b007001500c1030030001c41e640400c2c1100d901109644405042004054a9503101501241c1c964480c480170580d0015154410f40c01140016050005505192000c08002012102500035800c04160182c1c40d58000100749140840095403041c00703881d1058003103030030420f03030f0540324502000340d02100d0110302002040c0203440c00007401a00c0c1e1034201e02c00c00007000201c41c215440f0441860f07403516802c2100c9030710303800c5500140d0303160310f682061030320002500028815109152680d8803031240c0d48a900c545400f17150300100881da20500c1000f1075103008403c1e0000c581c0309240150800110030040203560584 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 634728480 1250 634727230 634727239
    0x1210204230d0b150d17130f030f14010608160e0f270a020315010618060e01050a120606030506041107080706110721140c072c0414070f14 61
    0x6080820100d2004030703e10b503004200071481c114032900c1e200c101c4041d002450680c005400c0662304c401c000c810341c06080c8401401620600c000c2c400098070003040d036040c00e0342c000c00029116900d011540ca8403100040101a802c52503405011001e5071801c0d50358422002c00003069141803012070881822601c000300104a1180c418074041c400060141019282e0000d044511009420041c060350120038845c1001140702d04407031400940c044a0311100315101515402e00031480c2c2c030015204d6074810024102000300705004034641d104a0310844000c0c12007541d00080d20300d022010f0000b01c3e1240400006071000500c26200000e50190881e50341682c0844082400c180300d00c2003500a00416200600d0141c0300c507191010000d002002141247d1242d035029012500d401c0500c42a20858010040c6074001c01c00034840442d1480840008584211032803480e00352040829000c6001074900300c4c2c403018038130614000403004000303440c050310742ca041404c0060301e8032441c41090024010f4541c00f4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 634729730 1250 634728480 634728511
    0xc090c09030b220809031e0c010f09050603040c080d0c020d060c031401030b0a05060d111915020330040f1a040302060402100f050901210204230d0b 65
    0x81c80090f4800d102c0010b044004500c4150340f0300d861030854000b5164039002c2c1c030403d11007074409550385010b070300401c00d5440503040460a6800444050941c0c462440034025448000141512110001d51080307001c1c2e40007900090a080a0324200008061601d0400c03084203010002f40c1d1f20000c6035101140e2006001500310740092007034000d45160680302c10031b0000c103800001804040c44c180351290542410400003595003000b00440c03000a64006801b114200d0f1a050b518141741d500001e04071941d0a4403450a60f944044080000002e00220016000400c84280030200300d10070741c1c0c845903000601c214280141405a54000d0020001b600399141c8181c000305010001140343d04070400000c3d4000c0a10b01420065915032090b541240594100c4010207440c500c84c08c10350400703c05656075103150420180046588280d034100214407031510171260f5800300310f0b0b440140300030048034107031450207811240840b100c10010503c1900071a9501988000100f4428809921580700b00040c00e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 634730980 1250 634729730 634729741
    0xf0a06180503030a0c0c0902120411030a0212010c0e121c0c0507121b030203100f0e0d08090f010e0a060c110d03060f06030e15131a040c090c09030b 65
    0x4903000394002505800b00003122000568044e041c4d51000d4022080144a00c0d074a40350780049215246410304800c071803c020030001100d240c414110040020225100b02e2a290001a841144800300481980d50340b00140d402c039810440340e01210104a610700e000c8295105050b4841e202552540c10242c40c02003090760440c0540c204014054000c4103c801143d11821150b548556007036068801e4043d9800940700e07090509010402e503a80a80a40340080c440808000a0407441c2e4000c0750090b1145510f40c0c19110400803c0070101c0c50b0760750210b060906036562410260320182d419016410b14002d1122440700080d900003655210800042103880c0b0700b002c8442d0885224013001c0c0d030150340d81c04554160b240d000203081d80c0000300c4081c1c0c00b41e0740b2101941240d44030304415035103800c2481450300c00d02404c40c07165841500c0b202250505c40c0c0380c0e640d0b034182d440e10000002011100c10148004e003d030007042c0704080d140510b01004580070707904010342200e07400d10000f04440e922400064 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 634732230 1250 634730980 634731017
    0x909050709060e0f0105040e070e1b03151c03020a0206092d0301060506070213091707050f010f09022809092406060503010905040303140f04060b0f0a06 67
    0x304610002003000e5503c03803d024101000c1540c1c2850388426540020800d458184103603039000c4c441900414510f80f820010360180da00c0106861480004034400d507101c0180d040041d8841c50600703410114010105041204181000441c0003440d119801d40302d0000c1d400190003403405030110340581d214510040020308141403400301d41d40313101608541080d400b002030344040302060110002c0c41495120f00520205010b141d00c0030707610941a00701000415600e41c09400d0141c0a0718042425080040a0b030405500c80707002260981d2003034580c0b0424850a2080078504810100180204000c5400080c264980190400440d85250740b5800342000c1d00b105070401044088005d1001061504042014814000411228251a10100004040c00c1c4118015901640c46007803c40c0d003042c00c0e440003054010021810315688642d0488409485e00d00c5034404c0f104c1e8001c45000d454035103007020a903084150414000d40301110045c42d699a0310f840002524064a0b0003401c90039040300c00d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 634733480 1250 634732230 634732243
    0xf1006030e1e0d0210020f090d0203071a0d1505100302030603071a0c0f0606010c03051c0216150b2101060308071b120309050f130f050603010c020a0507090905 70
    0x300042c00c0c0e00144844550030100d0151142c81564090380d181a0103907082006038820103855030400740c420852600c41d46081c00c0141c1c2100d00141c00c80702800d803512a81000200300404012211502144186c10b400d2a400343c202d407468030000c2c009401d4900b0005c903211408004d421020300d40c01000241c62034408000700700c018020000e0a0481c0340c00841e070b0042642c131039001e001807401200c8030a1550000041d0703240c042c0e20103039600032000320b19440848503a0016498808a50802c8001000a0005002500d22031407075180002018400d490900311140140b124010300904040c40900345075038124034030056480401c3c80d603901301c5581101c14018903080d04000d014003404104003091180c0d0b00c2c5c006030b022800907801c1104c1a11811a140b0080700c081c4000d0000b021000140480d0a007500081034203c80600400c4202101c68400e105407104607281c076000e2076a44ec00c0264a00d0240144220f205182c0003610301d008858031340a071502400d00507060001c3c0c90700c098404022042218 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 634734730 1250 634733480 634733503
    0x2070614040c0510050702030d11030c061504140603210403170307030b010c050d051809071205010603090308151c060507030b06190e0a1505070b0f1006030e 69
    0x600035500c1d091800c105140395500440b806240e0080c0304200c120f010f04c04a030781458004000b8601c000101c0011a00b44803007424452550005005144200f0781c20444140104607010300c208c104141d5000780412146440b032001160307800601400902d4501141841111540c1009218282d081041400c1d8032301c01c6500003011003803541320070500d000d8a0350240d4091421980c003404508500700044a100340041c10140503500004924000c182c09a4020714040856039049034260254000054183d4021641c400101d1905403526218144921039140500b03030504081040313201684004000e01002008446505041ba13440304480d50340300541d40300001103030703200e25240d1a2490004003801041c0c4550010034104510717805285070210558030609000300e007200300400d0f0342030210360040f0f42004894104142e110081444405400240302c01032040e1211940c0d0015850010400480101400705606132070007804246420920324000311401840c3c081042c20150501504204d5207551 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 634735980 1250 634734730 634734761
    0xa030903020f0a0b0a0506040e030d023f011e0302041503172203110f010c05070b0c100b06120702010b1e091b270a2603070506010504020706 62
    0x100c01308083c1d03d00303284c464600c00e0720a01c19511690b0034041a00e5802c04c021307105030824080080b490f003059020b00751100c09d1000141c0900809051a1044158080407000002c0ca001d0302d1949403005001703442c0102104070803180c071130054200212210451b400003d02c41c40d119007084000a0313241003800099071304440004074220350f80d850070b00706a01054025841e42500524640c00a00806403070302107030f030011100301100c00594108881d0700380c00400c01e814003141c0100c0801095007003095901130000380d86500d82d11181407030428504503d640100f210681000c1e44005581c4420003a560406c1506132000307541c0d100c080c01a070142c510028601e03004400c0745000e030b280c0d41c2010b07068802444262141e07269a191000100380005c04001c440c132091030300301b0284a900d4070580000c000c02072040e42d007043c443e81050020f802c91115030301980610f001e08854810b4410200100e20014600e03d009600d410902e5480c5900d1343c0d81482194413031580880c4060034040142c0000700528108003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 634737230 1250 634735980 634735993
    0x20f030c01020703090f0b1c022106040b04051e1905130c06081017010e030f310e07050c030d0e07050a1a090409020a060e090c040b0a030903020f 64
    0x2800c86000750081d40d0281c0002c2d03c2490002401c10101c000d1205580c0142c800c80c0c13030310000b224065106071703d0401c07401e80140d0030004a16441070105010f01003800220000107035091035400c000035942c810302c0e50341c03207685000180004102044052551001c440003000e0300c039a142c000244d5011810810078940904110401c00b820405903404071240e881410306c01c0c4110b86032803084440c01c00817039115010b400c400b2014445040c20305510109118840c0c0046807024404d2251410364000c00d02c80800c11001003000450300148401496604000440d018804004480c10780100e1701c0728490b98401841e003d001c00d490314402c1044494500e04d0100b2641c1e60340710b08080100030710100651160a00600401003094548102010111207801b0391900c0b41c48080d88010b9111f03030100b26079035400740d038030440b5400503122046400018451519060416a62030742800307010368000742442ea14101c01c00c010311100007600142c80003000f80e4500094109441d1800741d10b4015500040310ba03521414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 634738480 1250 634737230 634737247
    0x30a03020606040f05010803030415060503030d06090c0809030f03070c120f020106080606010c0206090d0609050601060f0f08070c020a030b090102130807030201050423041d0d0c0c060c03020f03 85
    0x344840c00b400050b14208002e030f5000c01e060044030000c0c01030a045800400215010a91072040c007000400c1b000e600007070380c59954000034a5640180d14192699456038420002009075110349a240c503481c1c2401881e900d00058000e840384610205400700c0c540c04404642614454000150030f990300104003442814a204003400c507030070a0758a48019800c009000c5842080442d040703001d0315040c1c586441805807903081082c2904003107061500503100030036070400f086141c09950b01050040f00034115075410004010821101c0d104060140100080046142c50303224001d203510203803610f406500c030159840090840c1130641d1010384845281028401c80d52810750060088275220540c0c032032102d40e640c80d080d0f200d611a1001a01181046c00100400320109000c800003200740007501610600031000181140c40e42500142c036811041c42906046004000705003210006051810190b440c40d0f403082d04160041c0100d500f0002014503041c00c040c020441e0301c50900420b415a601e42558 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 634739730 1250 634738480 634738483
    0xc10140604050610050a0c11030a080702150a08040602030a0b040509010510060c080a200a030206041208061509030a021c020a170d0c0c050402031006201905010b030a0302 75
    0x2500e90314030640ca0000858182c1c58800400c1c0110b080d1a25511700f0040d0f45442a5000e0248210941c1c0c00f8200c100e04103640e55050010f641d071144211080c41d1206014010300a00c4001507256000c1d08804200403112a50000401a4441d500200140c1e581d900d0581910140840c83d0f0340d2a04207040c40d0600c580c182c0190003092180411010358100141d968800315071510303148101409100080050440c068030a050300030307140107090002a00d441d846010180380c0a2209026001070304400d05100800c41c001e40c140886c901a40f401d0a080d04001000859114100c0849242204005040aa00d4405004540103190001d0040d44210355426100d009031015402c204c0c82070128081c04a4120709020f4190481d4050b117004008a2103030741010f6404c5440b00a0603200e084082c0000200c80d0ba9900046224000b20202c006100340f61139005407445203d0540014a200c0c0001c2c087c940060018900140040d0401500228400c4d810658010905400055054000c0b9150300003810340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 634740980 1250 634739730 634739771
    0xf0615040b090708240f06030a0905030307050c060c09011b23060114060c1005130804031202011505181801021b060906010609060e01122408070b0f0c10 67
    0x40c0200d649240309601000c00f85c580c01d08055694003080c80807072180f442c14480c2c09981e002d0303110000020021440d44880d469034008940180002c1c000140341d040196052103d00d070026034028001d8102010760001034055084d0810b0700041d40040301d1036074280004400484140c442d50384585850360140807220351151824001c80f4001c100f03002c144c0d48141000d1701180d405030075280141001341d481d0400e45003c3c0030060584045280e000200e280441c5000004000440c4108601020b082e16030724060b080d25408841a2a0840100d90411450300d80700704407110000420740d002116620280c10b98005107855610981a43c404240f4040706110408202e2108402034100d5507107503501901c00390b03503f100340030320000191011410410302e401002c0009901005040c40080b60162425050454024800803030300f440c4c10070101d020810401200b03101406505028104180c06c1412a03c00c500c103d00d21711900001c00508203010f50310070f000c046817110b03115000740241a0b040074407201c03001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 634742230 1250 634740980 634740991
    0x40e011e0f06141c0507030215030a0c0c03123303030909112505061515030912030903160f14150103021215010e0f090f0615040b090708 60
    0x1840c00b280419400c10f003c0601e02c2e001c100805800b14400b2852001480d00500390080303802c0c0c40390310b40210040c0e03a9207580c10414860258107680700d14042490341c080c1c032543c08454050000ca0190900800d5000340342c90000c0e4090400400c0545d40242c4985c2158454600a09240303008200c2e9880d540810b05074a0480e1300a40d200d0464640342c04072030045480c1760b00c5203a81034000b00802c210200c8103444614051095482e90100c030051902c1d210b013031400030ae50486040028038803c84403441d06905a040304221494018214640400c0301d07a075034810300d40b420b8440203000c00041d82d191010400c41d0300404109884460200035450030864011030050115490051441c8011052400060700e074401d500700740100c0c0b841e074610740030703c6081e80f424683c111040c0540c040c00c0c45000c280d407090900900c02b1450b101c0403403130145001a0f000d01e001d040d02d1641d822407081480200c00025031242c010700d0700f4540c11200112040004e00400000c81c603980c121030848104440d50340c2000a1320700c42ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 634743480 1250 634742230 634742261
    0x1806030a1e0f051e060717060f0409060f0606141602030c1327020907080a180309080d0207031211160605071b050604031e0b04150b040606050405040e011e 68
    0x440010100c140c03105c8040f261440007032003070101e01c0074000d4200401c940218014007054441d0b1030b0a030114066554181080c2ca42c00e2f00c4105040c0034026030321902c40284002c0c43c1c03412103410f07800e603c10001e12641d0600410064011008000c0d0b44d42406000380070400100600e05820302d00b20300501600344954400304191160718035265290720842070581166000f00b01300c0c21a558060151956600a4844180d2640c2d41e903505003200042e802c98202035000b6112130b8081d510b0180c42c10701c5c11b00e03029040340854200e01ca041002566041c0b6842e500e9090781840c0012940b07404040d07141c90071a1100103003824000c00c0020350b00c0d0b04031008090f054051001020b40703003943c0205150080305032103510740102c030812040010940002c0200c1e014900070b1101d001044058032015403000b0305070703410340300c5945d030941114002106114052000c0001c0e64117012581c0360410240050007a071148900689e00c0c1d40b008022403000f94042c0e0300410803c028043e1000300d1080583c002d0008145030703581c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 634744730 1250 634743480 634743523
    0xf09130e0609121219200702091b1c09121d010807120209010302160629010503010303081801050c041d060a05040b011e0305061806030a1e0f05 63
    0x81d20030b1403040310002566010880d015803941c42d01c0c0c1603070403840d5503031110580d502c01b14040900c40540300500c403400c01280c455202d4840c0c0c010040c0d1403030040c00012145c0d8000d080300071044030b210300b030b600d01204010000c09044203801e9900050030514400502e00d20108a0207440142c02c4a1400038400507441d400009062040c01929500400d50f540d00214103110903051081050f90010440b4000614015092500000b44508810450482115401d40b107881d07030039034040205400f0f4550341080c04101141c8204030000303021b510060101608002c003c070000341c0512103107848480b44410400082049140414019207243c109005034803200c803d8020081106141d61207260003400b0080c501d00340745207080c0400000b4141c1d40000e5043c044582006510b2001039522480810a01d4a010813946405410890021054540c0794107850a41060020a40300040c1030784640b54000152a140100c0d4040c185005120450040050240070103200070803202181c200b001c50b0700031204200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 634745980 1250 634744730 634744753
    0x12050f030f1e040b16090e01090507180f36050615130b2b050405011103010608060d051204030318270f060b0c01020a0e040506060f09130e0609 63
    0x100300c40b0603140645a12440c201260442841094001c4050300030b0070308014050f81d401024200910990004001c107980e0404c0202054111383c0a01c0d41d40036003409841c0d69820000181803003020390060107469100546072106203003004201d010705a10741a920a00015006e0000e0f011308411980d41c1d019160041000003447c030b01e07005640c980709004600d29005401c20b02d1040054000714041242207603c400300c132090101b1045074107460349108502217060702d8242800c0d82511401840e444070140100300400c0190390028034550400c104513000012403a003824420314140c0c5200480300070f241c00003000001c2540000030035030080c8070a8007824506e552825440ca4403180c2c00b240480d4000c81440f201d260f22503642c40280300e100200303000075a10f915100e6014080d040041065a180e5001842c200c24a17080084c174500c0c407404580c107002e01c0c0380c00c80c0410481d010b03040c01840211740124400c1c03c02d5503000c60210b0000c602203c100001040c002e0025608c5101340c2e00c0c1d0303d45004180c00c858 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 634747230 1250 634745980 634746031
    0x103350f27191401050c150106171308040e090106081009020922030c08070606030c03060f0501060905011b020d08030103170403050a03050d14010f080706110a12050f030f 75
    0x1124101d10a4a0b01c1d42c11000055405c0e502c060181d46550180b5503245070080d0810900e14042d000c1c50351000d0360010700d4030701060a0b5074080e00d131010b0610040b41d204009015401142c4c180d03852001c480c0a15140c40300e0844c0549401d4008e448039004150031107007a19a03a80c89000d5181c000c5885004d10317200d2010701840c40c40d9029062150010032589000403d0150b0043d0b60498411409549840e01c107851742c1080700c07103d410842c1d00030900e040400a1203900c0c0640010201c001d88204482c1d4500f0802070900303100c6125880c1808030000460300303825444907a8030b254a401521660b203586051130480d90950090004481086c0304000740d41c81d8a02031029038082c1c030351020080c40384442c0c3da101901e958009a211554958071030700300064400c030018906000f0000d10320002001414031403218185503040d005402080744005401c00c24510018445132103c1d04580ca104c80b000191504072114803407250480c01640b000000c0c06900e03403000074420b2158070503084c5101c00640c481c4903031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 634748480 1250 634747230 634747279
    0xf0b160309050a060903200106090e150601080903040902191403090303010e04020d0501020d0c090503010b060415141b060610050d111e030103350f27 66
    0x20b0001c2d03011000807000a4002e502008480e8040d00701010905e041c100d8021f0760b140f605540e06c15694442d102004045054012002040d003c0700c05407003140e00c04040084840c000920650410200a0100380c0700c48044c001c4034007030300d1480c400b99a80c05210b00d50940251382c00c01c0c0500040d21504010182038181001d59000300032010145103181d00c0c1c541c607014038107000b90083e68400c0c0500780714000903209100400310b00d0900b04c8041510a0b9804000e0240421a44007038003990612001c5015903803403a0484080d078000703038000d10303104a200b202220300350460002050139210020702d04c10452403140f007403654210600100c075019502c410901419000071003041c2c0101d0018008251098070710b401c523000740d014200e60b003402c00c00703c6621000504220724140200031000401071061254802c00c140c078001c088003004030995103000266001588050080354030f0070340407aa040c0760150301400c4403024007603000801000c1c4c00030000f1401540c0d0581e0403610410040740c1c9480300d0402e801c0e08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 634749730 1250 634748480 634748483
    0x9060305070b0915030a050a060f050a0302090a0b031f110f0a050702010c021012050903040302090402091509010303080702010c020705031c0201061a040315020c0d1b0f0b160309 78
    0x250110034503010450344160402900550310240c908261135110480302c0195204901140c0045101c0c1400311902088071040e4000d8000d45041803401d01164803801c001c48216503040c0c960305000d9886085110090203080b1303400d54940100c8811a0000c011600b4149411103000c82c208510707105455000101e00c509503c0c0e1081c510140300003000240140301801d2100c0c010306010030007c855a0002d000c086030b4080300b201207800481e00c400100818410160f11a103644020f501e05400d5070005404080b00030700c000c1c130403c50500010940408214205041c5c40003800b954071958403883d02402c25179088075800b0041d032800d200d82588620020380c140480c0c8024019003560180030440c2604400d80c44040310030340d03481c3c2000046804541c403000700c00440d06009162030300d055180840d000e119402400c240305006000d10718210101141162103029a41850b200c0740050300001c1c801d0342e07014400900101c0750194503105000c42211150b00c2083c10a0b10307180100d080e05001d41c103ca200000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 634750980 1250 634749730 634749733
    0x201110616050d0e100c0f020c090a0203090a08030c091804120f0e1c03110a032a0210030c030b01020307080d2a090303120b030a02131503060509060109060305 70
    0x14251000750040300202030605442c5408645510b95400e81454401e00041c0c1940782513841890900b4070341e100069601c48040381c400b80c40c50713074880c3c80040d41400c4050a00002030760700002040d042c1038100035400310a5404005103449280c1141420020381002c2c00d01ca004503080c81018840c4603000100c03d10869000013417015880030b4030012651410f01d0a4100140103103c1c490201c4c071768405110076140f100c0c5881c2150383c1030302480c0040083c0c00c2c02c01c0580c03181d0700c543d800c42c0019401c0115100d52462070780c036415440c00c03d140d809011100000e800b80d04042c60a40e01a20103906410080342c460306510240700e041503081c0120303502d00c070f200e1010305855000d020359400f4030001d800c180300703e01d41c9a90b21139400d603407240c03d03000c0a20031034090000300303140340d03010030030960400c090540c01420910100108140100802e4651040d518003c0c0300b02d1304407541141500d8141d2100541c0601484009481500c0c0c1c600100103001c1034a511550b441480000282c80781180036010a607980b220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 634752230 1250 634750980 634751011
    0x30402030d0e040b031203040c0602010e1009020d08030f09010b0f010e12070e1f0501031b270f030c1a04150504050d150c140301180204030203120702011106 69
    0x7202203503100d40e80d9000780e500a4950344202c000e90f4080200000b58076040f2401d80d034905003480d114800c84201e520600a59041651120704000302180780d85c007407000d01c0c402041710310b020710004820583d41d0b00010103c00020080c0000750a00f00300d803d229900900081142c0c1d5075030030070002e0210654518030300088910140382640e0600c5400d01341800d620f042183d004c161645100f410a01080f034144070f038030304410710342c1d58420160740d040001050203080800c12500c1030241c4181d803160301c85c5240c09015240c650001c0940d8903028141c1205540c458bc1c500140c0c41d503140e0102070055100a40700b11090000220702e035080c1200904116002540d02403a01d03180071620116500401401c0081c01428040040c594490182c0c003504c4a02c50194407544550890340c510031205010a0301040200717140340d245c0150702080440e815a6511407082f1078411030084a14017a20840d0402505809503031040600411244041c0c103009201340ca03440480710b00c0d03c0c02666542d604441203d21003004c036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 634753480 1250 634752230 634752253
    0xb0a030c0b0c0109080301090c080a090c1a0903060403031b1403010905040206070b0c03010609320409060207080c1e0a0b0402011119050c060406020304150224070e0603040203 77
    0x1001001c2200b008000407450f004261078900058109a0081041907200c41140e00c130700342e04c4034070030358803041240b0104900b82080e221980818058044c41c1240e954400400c0c291b501c03918147c460002e001811103580345071500c2c00401030031090301440030090f80e08141020550141c1840503074403000096441c00c6a281c1107401001d4000580141d03080f402c10000c1e1004104080469441000071165455695260000080c983d4617540d000650070440000d45842c0f00c1d0b888410b800304c000c1b2142a40b8070b411a84c200207001480024070040065100181141c2000358006c09007550801e85ca0a0720b4040700ca4030354014802420201c1c10405070000c5524400040030710550640060061400d48000315074901a6071070400c4040d108010000800d240e042003000030000061070240076110f041c04c0034500706020b13589019a000c1c200c0c1403203d941034401c04520070001e82030802140c5814101c0c00d00c003142c040035a81006e8441e10700280c4041c2d440550f03410a00200e0b0700680e8068024460342d50310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 634754730 1250 634753480 634753499
    0x1b03060d080c25060302180103051b040905010e090303090d0c080906070b0a05061c0f1b0e0115030c05030a05150a061106130c0611120d0207060b0a030c 67
    0x103010049036814400d004102484004000302c140d07540c0d110b4050280ca00203103100108414440c2e2110040500400071251241d01403420403020300420700300410313181c86032440140400c59a170b010600725040490005010415504010b0490b40c01c1d0300304108a40307501000e5520b174070084551501550003103520030f042a208081030717558603003e410000c0c2410782c084001001540490004d0390002d04001c1806071140b080c9c4606500413200300c40c1005004490303404a4040f5034040d9010f49840340c491078034414051005030801415584d100c41e100f070742e52a0000c0d1205410203008034071029041a480c3d18605009102f20308900e0010340320281141c0c3c0f024410f03005010300a01c0404009251402d5840c1c44d10b428840d00c028141c2a1034085600c172001d800c17249030610050044480188510b40c10010440c0c49121006507280380c0b41c00a40610008480c5191404658003900e021030005802503d80c0c40f0ba601a00c2c03058802c840034404148090200720851129000107844401041c108000380c2c2032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 634755980 1250 634754730 634754749
    0x1050c03070f0e1e01020c2d010e0d0629061905281701030c030609080f161103150105060315120a1a100902031305160305061b0306 58
    0x2181c82c242e05110a0f41001c00c40c4904008a070f11401070048642141a42c4c0500170040e41040a8400c0c0307680c80b00c445034a665401104074020345400200400c80c076184d03c1565400003415014002c64500d8000b460600010030710b808101c40e01c8050030a10682540d007000d5681124600101071a050040344070000341c20b0822001c440003845020450410178030341c01da500d10104645010b05400e15440d0302009441c40d02004a2014501a40401032000403028080300081d01e400c01d00c0051111003034030b0050007a100391105800242ca01007400104150f2a02c00095590f104140510200545809041e60b680080c158922100701c0500184200d0411a000c0e642c031000400b111400030701c6000c0840c0990388440c04441031900700d500100c050012981d40b41014611200f6150410b18080c0d4021000a245008070400b494001000c2441c40c1c005034803002803150014240c0c0c220309484c6440308842030441c4001c44103401407600080c00c00c003011030b205400c40203c4005600d141d07100c40c00c000c0a0708 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 634757230 1250 634755980 634756007
    0x11120d020309012a060504120507030909050601090e0f060a06111903090909050705030c011e080402042306010206070516020f0409050d050a1101020a0903061e050a1d01050c0307 78
    0x42c14002c0044d81c0c1c52100016072014056680000c46003441e041440030310307015070300c4402440410407a000c0001d0380b2060540485034500000280c0303071140001280c05041641c007112410340c02905200d41100ea404440d40218000c40704e0484880c1c0c0d81d042170700c820801404a00082d042031080007540020340b1041c403001c910924000e840c0545a078100c02c11a480703c201550360303511102c2d040c05503090030449061140c1d000d00300030502501040031012402e07052000310041041c41404901151515001109601e0311001070100c14020f146000d03000c450204c482031f00510850380495241800b5800729164208003c3c0325070303c40390f10340c0c0078084040750329a00240c006544210080100e0420711107004400c034075a59041d0346131042d00000b0024854103d4032003083e441088042411a0464403483c200d80d4801c1020460103198a1200303008101c02c5078501c81d041c1002c0c10403890140660004105201003450401100200c5040c94200c44040b100142440800c0001c10490740c00785980a03480d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 634758480 1250 634757230 634757267
    0x21060d1e0503031e0c030c0304080c160306050702010b041b05071424070f02060f09010914010b1201060f030b0606071e0b1f1e08060411120d02030901 66
    0x40e01a6901c032481c1d64400c07952260207001c04200084001c40c06840c0340d800400e1813540905500300074200c070a00e07120242004200e9407000038547c005070401d01c2807950304035a40606000d11940c1c0e04001024003800c42b00c200043d441e141e01d1681501d00380c880c0d442500c0c483c07080c060109100420a685990007020103543c000d50a60f8405100401040a59000300c86510141001d004c00b824409141c00302408110500020005081a02d6400a01c041d482116072000320002c1d122a80f4040c01046412000740008040015800100005401c81d04071340b1016683c0c0808005162500c0e400c8078054040c3c02104403080c8810804920700c2c209050300090f00400c2d003480e22041d90b0351105007990211101041515040c4844203001030010307076541c064440c03944038480f481181940800c1600b14052043c3c0041020300c8484040007012038040034005440c1118610f080500381406802c4014090301d20601c2c501440703140c407490200313610071115401d400171410702031203400540300c0141070884040103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 634759730 1250 634758480 634758533
    0x42a0302190906030602090f030604030206071b050604210207030f06020d110301030c0e1005010e1203040807060201201303060e010923070f1809150203010b21060d 72
    0x149219100c3c440c01940308800041c0d4407440507051001c41000909054400e800a004000209401041c260b1740a242854103418160f44181e48100c41c01240710040c0080c441c0d00200010030030146140200e45005480111807054030304022aa580c0031030100401c030300d803442e401c0c1c0001034044d0003800d0030102103100441d03040003214602ca900c0d00309070b00a407451040850100030310607010030707280d0300440d035070180180e05810310700003038a600080c0252078011420701180640d22074003842a580540700c0e410903101c07400c0da138840080c06440d11001c164110190100c07405822500c5004540070b5190101000300c0342e0b4070b0750b200d64000f03050042c4075083c3d65480300b40520019180c50800301c61404c0102c111701d035100d1420346580c40c081d0395400c1424056200c08051000d840a00307200c58584151082c00706602d192481c0000301c05a0003200e9038800e500201c00801c10a541c400907112050640c100c2000240700401c03114222031054400d140c00c03071810340e40d190100700c0007080c2544540345200c52400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 634760980 1250 634759730 634759739
    0x30c12090a0f05101a06040b0918150a170705090a02070506071718060a0c0c17030912040f150512070801051509060a08180304030308042a030219 64
    0x140c1e02c60041c4100d643e42c105844803800c1080070f2003030004041c4500910315494420001060180c40b42d40191108a00e002c94074560f15a01c1c80340c070303072540711400500300020b04101c8100c2441842d55644203119040d15400810314606025134161683c4014005115403403400b000d10600d85400b601a03907a10750200305440110704d0401105000700b00a5451000840d11020001d41c0d481000d41102c0d02018003400c54089400f0014907250469001c1c000003464800211007a21b424a01c50760080c8008201c400348010381980ca03024501c0303060080d042d1520110541c03164640b03403007180115029581908801c2c00f402810b90054001e0f2851030804501d440e10f142c1d01d629078500c04564200010321800d0042c08503003010404802078401d5105014148080d03a00066400d00501c2070102c2041914000104480b078009401000480c20304152aa0b40d5100e0500506240c0d041f07400340e414a4540348861145280c0038400003c401c440712040407100e040d507080140e6603800d81e100f245100e032801170220f03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 634762230 1250 634760980 634760993
    0x604050409050a170a030e3405090906070305130f0f080f13050112020408150a06150c1a151e060a0e090a060b040b0c0703060c020d020c0303030c12090a 67
    0xd40c914004e0034020344510300008000e040e00c2101880c40e44c1c07604070b04100c0c580c40321032012089070160100d010031524011000040b43c0e250071980003507403225054042c8804020b0100b406d03801080c0075941813040e540d9070f0304101054405280c00800c128507009240703002c16041d16501c0300c1e9602c41d072060b528011940b4195020794001c0c42c9052862070f41448208110345e04468803080300d102c50041542441e2610007015119607003072098040a40768400042c0300e1515a034401d00c040c01107000c522400210b4204020080000801c040f01d03641005064521480c500701c0b0b1081c4200c2d00520044104140304040c00071a6190324440110316101c5020009650341d0b0354050802c0b1b01e05d075566082d095108504200d000800601800c892924000c01070003d454814111400cbd6614002d1040c1d9801c00504501d103001c1042d400589241d240c240501d040503808200704510800650850f9040e480c090100764a0b48803c1d80c144025040c2000340c0c2c0d01000030000300f5644040440c0c00d48a000c0c8190707e482 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 634763480 1250 634762230 634762253
    0x60a06261509011d0901151e050604030507060e030c131e1122051014070f0c0e0a050c030a0e011d1e010203040305090d1e050c040c0302090604050409050a 68
    0x204d042c14003e8491400d024041c00c80543c401c03203c20007401090502c0c011102d03000340c24000c991010142030303115200018220190001401c0c06083c0541c0ca940e242071a58407400580240400100a95004103051070001803230940e00030000c01c0c00f03805241151040b401001d003401400785a002c0003034070744001c1038280b041c6a003030b40100c030b040c40d034480040c0942100b4a6034403074101640310512909000c5a00c0d58403000920617a2400c2c0900c030702d154440008009d0194120040203208000700002c100080c00d41a80100e070403005840980d030710340d1101c44058401c101e07800911103000340005608030089403c03c4406020b4a00002550320704490311107e00c1518494006c0036070700085e045840c020070000081c0303480152170000c41c2142003030f6600038103a104a0010a104e402403000310818842a002d6101c0c00c2d0143d07410100c0c5d803044c1490680c0d1240c18242e001c40c0314a02d84441c50762042d00a00803100e00400c020405403a21b42030100700002001003900541c0d2911600189100095124211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 634764730 1250 634763480 634763489
    0x60b040c020309040b180c03100905070242060a3201021c0f09081911100c1b12110a1d0703110f070803060a0626150901 53
    0x207035543c2d40d0914103100c25100086911402028401403d00104202c050600e801105c4003a41e81d56989034091003100c03400c10b541100c03001c05e1800c014041ea07950000b03241403911200160005040402e03141440c111401440e040741c15003549002180180d803000c846941c000e8000340b04480c40364440b084a00c01c0c00c403491908114601c869007943e2140c01031450082003080920061500d103a8600342340c1c80d1081d038100410f090003ea8031220000310301484491004e45407050480303003c0c205240c4400d2a0341100c0c0829500e5081c090410000340c240300c00e0800164140d81c546556014507686d901d0001c10440c14011180340c0f88500100740300e00349e40c041d1a40107004240f5614401c40c00010050b98040702c0e40300d8143c0400e8242496003181c401010154072543c20704000402e014100e0f840b402510031b8684404046e20300141c0c1c00d0030042290301031801408183c0b00c0c10f55403501c64905032020200008803440e00030300d07203030a94110f01c503030030780c07141d11488a00c540f104210141000ca1b20150080c1c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 634765980 1250 634764730 634764733
    0x4080d080a0f060305120702040b09090c090702120417150f01090b0301090f02010509030c0604060c03020c0402040503030912010b130e010e0a02010f0c0819020606010237060b040c02 80
    0x9000100341d25000c0e482c4440140742042018528681c0e40340d9541100c41070071003034054085007400c155503483e808481c0312100589012401d00d05410b01c10303111a0000200c900c1b0710102c0011401d800d10020345140c6101071030801f5450036080040d185200c04034581400c1d590b1040d25030b400a410380a91281c0d00a4240d40f141029075410242032800362494504214040e1780341000660210354020001d286103038081c00d00341c4d602e44401001c2824003074140152604405c0c00200000c14582c070a0203603031180d010b5800e945100009078104801e81c03065110b0250305500a000c10740300341c68041c00404a501d042d01c000241c88100c41c0200710040480c081011205981742d041060901d02030080d108004000c5018102c042c516900103000110404940010441e401c02043c9c2004038420032034900e0f2030700340c4440455612040c4000c1d07680bc0c0458840d40140174070001142e82214801803600a640c9000fa40f05418203440c0b00d24134201e0191106a980036164405061103072503601c266005100590b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 634767230 1250 634765980 634765997
    0xd110705010c02270105100507050712050a38060603161112070201091401140d020f0f070204060b0f07170904020d0b0a060c02090402060c030c030406021b01080f06090c04080d 77
    0x608118220b07071f403000e0440602c6001c005e8480010400b00340e4406075100418a40b2680c003040c10107500c4c1200b40b00d4018001e03282248200b2400c020756002500054451a100c1d107a68032242c0003600801040d225283c0000080c40419080340600c848a60400e4907854a4100f51083c580c94600c3c244000c0c01c160003840000400d04159680800607a0241c0f101104c0240ca11180d400024803a040e104102c013000355021039282c01100480e01114410400b4102850700c2d814406030310080c0f5030080c04200d1080c1c2c03800a000500401000540f500520002d8450307040c140c0986400c030000306110085186034100700580203017544d442c4090204911420000103a4589040030301183da025500400c0602440403400d03c0140d4920014581c01a81510200d441e482422041840e500030f0760480141c034000413802040f80d03680003401001c00001a031070b110b84c0d8010800150360358002510110b401e1041880050f0360303400c0401c0401e41000c17004007030501e056500e105207030500d00140e019200203107011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 634768480 1250 634767230 634767239
    0x6190e0a0b0313020d08090a0f090b10080a0c1716030510050a1205150108060703050619060e120f07230f09040819030e0d110705010c022701 62
    0x51036540501001d4a10341d00c1d5040c110a0032a03201048500240300d1405500e0040c10802d51005540b6080d03030241689030b02c0341e160700002400c194680038846185180c083c405001d0314105010b001401459140c4007810b46903502c00300d000c0c06840788201e0501c41518415450b400560b510315203d941811a1404c58045002004040d00d8001e041001803001c102c00511856468a2143d011a918038107998009803443c606507080004c0c41190481c0741c1e048100000304482c01040c698881c140d85d40c1c00b089250f44060812500102480042900740c00c8240188410384c0140621141e04c0030040a120603c4c0d0003038a1503140802406142c41150480704013008000c680fa0300f9904486160380821140e520131b10b011800920161105610030b145500219081c045008115400381d603c0240c19040c070070302d0f040c000c1c0140c40a003224105a01c501006941602e00c15084c08040681350350207031a00e64500001199455a100c006036801108174101c0c1484900407043c400c400b40d801401c81c20590300d072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 634769730 1250 634768480 634768489
    0xc0304140a0830040305162103090c0603060b0720041a1801050d2a0e070e09041205090117100302030d090f0e1009020c010504060510061d06190e 64
    0x201010322043d40000c030107000009030001c00307940010b0000004030b600365099080c02011000050000d240d412a4072050741c020903030581103290190700400314810001e9540c28102c007182c0c3c46101c1c207820b40d9802c0c4640741c000740c050740d4050a4041c1410400004031940c1c0c00003011180310340500003c451a6104001c01810282200250b080c100003852040350715120209556940c4001c005100080400e50907100b50703070f1b40d190507110303e04050700c0c1001c2d5504c543d02100321400544402010a59800d1031800c3e0786003e56600e4816980030003204410b01e040b0105945c55000003209038107004855100050540c498900584114100b009407214585140141414922020702030410410720700001d02002580b01100011180081c0044110343d544007100701b1443c50542040500500000700d2100068054201c42d0013180140c104001545440146070b510819074030952010941303c20300c02c58942c950300c06a100e10340014007206d14003080113141680350700c0c5407081180407034445614440325050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 634770980 1250 634769730 634769797
    0xc01142106030d05040518040201030617060f0c180906040b040e0114130507030b06010c0602040305010f0b120d050d1b02060115020106120b0a09051902180c0304140a08 74
    0x83c9080880c546805d21000c42c41a1500c0310481c04803030486808142164402e030301c40401485290242548007015185035a11000281c2e1401d4940c00c00601042c2c1d1400c044040f200030745c60320000c1c080039034071040c2441204c0c03000801c250350040c5c0d2600e0380d5103d41c42e1401845005020742000184610310100c404065450107005031100d1006410010001240012550103586e080720005210380e40300c0d00122944104048010020360000c035001007040015000300049400c0b01000b8802140088244000050040480c4100e44e01840384400040e001d6801403403607207400799010400010011000c1000c0000d05914001a0b000303900401000300301100038003004255200a1001d54500154245c0445140c075010f03000d80c80c0040480d0741d409036507001c0002d156000c2e094131030b686410840d602c04070300e907044182d00541040f001c880c80050000010b80c420300c0b41d291024159107a68031420404000400c070703050b4500ca6400c003403012500740405845507403041d81f8081503d80030700e100c4d14050307038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 634772230 1250 634770980 634771003
    0x1050c030f19090f080d200409020c0a0210050301030326070302090f0307090506100513120f06140a06080c09182407021c020c0114210603 61
    0x44050040c400c145111046207600b0000c65200c0389803400c2c100c440b6900401030040e00070203840e4501192400c10240d04068051000800b10030001011071090008252008000010100008000500020320385601400c02c030074803d0100d030059080f5a02007407880030b4620000c40480d00110041040551040c00380c0c2c08081542c0c009800d21030a403581d00703020040900b0000030b044d0082090100707511307401405248510001c086554480e51121210014034007a96102d0052201035840312009008c0c20071148510018400340302150314000340b600c451200d0300303021038188502003000380100b4142d000e00c00988101c14440c55141c102464a13500701c402950040f042900b242900d100300c0d980e000e0115a120040f80400b07603030515150071150401d0814104140d03a00801070200708844841c1513698820440794017114440000300038110320065030402c20b1001230703000503011304136035200700340088540b0f240202e203e00707220640c1f0080ca1401c040040b000c0c1c030341e00c50208124051400304203605001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 634773480 1250 634772230 634772251
    0x30b060607030906050d0902090a0509010f0e03042114060f01050a030b13020a0503191502130314070b0c1b040c09030305090604090504080307020f072103020708120c0105 75
    0x14075a6401525202c050310410b4144007020414a18207001900480191507000b001300a0030701c0c040c1c035400000e0100f40c40c0c0e0500b0b580303000c0007140a602c1d43c0c41030341d4038000890015070406290840900007106039500040d0105c042014900009103040150503d00d40035001a0a40d8901690300300c1039050140e00561007141d59072020408a0001410541c1180c0c201540080d0003d5a00110310f40c0980c03a484960140706000350740703101c0440031400c40300291049051501d04495158400268014802018482120307684200009105000c4040480d04c582042e00c403265a01c108141954109600070f220681025010201014074590004540c06080b1400c010416161030f008060501c42d0100509100c00050b6400c99a070b914030a8038000c108000040c0304528192603c0c03d040e4100f514058094801d210380482c20910100f00b1801340da401e920b0340c40e000c84289800340d5403095140000c0c0c081d4045d14001141b0901c0600030680b0a044204400b40d40e0295041c1103821140010030b0001e18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 634774730 1250 634773480 634773487
    0x290603060f010608091e070306050c030105210c130506010f09030b0601051e0a0e0915060d0b120106081608011e0c1710140d12110a020a0807030b0606 66
    0x76000011900c1c1980e0162421503c0e80e40d6050700103146c50003002c0c1d40e480f400c81c0e400c40701070050ba0010b00030050743c0c40b40000344542e80354a041c0a155000038020294000514882440c04400300d001140700201c10381c0c111281405410f0208501ca4440915044107944038410002a541c02803008210280c0d02d15054480c5c0345551202d840c0044060021390400c440047e92100a80c3d1440640c40314184c2104600d42da085010000351000c1400007a1074056081d01000511250441c0700310702c041c120140c03000c1c0ca00505541041c00819551b0042079104064003c2c0c203040d90403d1040030080c0c0717a220014281c2512402c2103200500c00c0303034031021660381000005400351100050011100650b2040890789a00c00e800517540410140079140310f40300c400042104c19204000d00e1011100f01200600541d0546030a01c402c1c40481c07000505000000d400210206c1d2150220540222402c804d40716140040c2d800504c0d10310186d40f16413400e5106010a00a110002c503010742c11a404490301880c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 634775980 1250 634774730 634774741
    0x307020a060806060d050a060501023702012601052805150712121b0f21140a1a09241002150108030f0906030901020729060306 56
    0x19554031a015120800002c40301107406602c5140c10b0320480b52103148140070910381040c0c0a0000e00f203620607207005201c1c1240458440e034204c8041c3e00c0d03c4200c1c0c9640324040ca00407020b42442c42400701f04074100030255140481b80003010304198885a901c41d030002442d49000100f0102e000341c58100804194294910302d00c0c0021003240d48222801900ca40e01a040f2900085459024460026011054134400d102e0f1031603008071002541d444294041104031280005802042d90113500302020030108030004c0c001c1c5008500408040d0030b903c2d01040202c04500b00d041c2a280c0f04a11801032180c410240140200b040c0217920ba00300003c030b15203111424000000760528400391882034400405082440c100d01806003180c499800076012071117504d40d01c01d0081d03507018140241d10302c0051000011903255004030890f442a403105180c84c0c00e1240900420600750b20240122410390b40c200100400602416084194140d9100042880c0d841e0032445c40c41d1072600402461090f003000c070800ca03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 634777230 1250 634775980 634775989
    0x90308040e041a061e040f020c07150507110607050708030c0d031409070512010e0109291006140705070b0c0d0504121101020c220e0f070306050403050d02030f0103021002030702 78
    0x10284400131502505c440d00a43c040b80080c640050207407211400020b11804a00c1b0024028040341d225082c0b00810466581c401c99042c060300b28010803090308202002000e24000e8081e124040c051010b4031103603540e400003145140d00c10140e841043d005014440070b0b10f81c01d440781401c0d14001103c401d0007441e02c800101d44468a40c01150311510750309803000c5003038200f540000f8120424500802060b041801c00000c80c184258116001000c02d040401c0200c044c045014050458030342c540b402d640c1054001e0310808200009842112002e0000002240003041201c00905282040303a641d1070440ac04682058040c444040c280709042108100481ca001c240180498005200d0403182c10b007000101e051400d4020309551004540718a60402002842c00440000a00340308021007091004901d80310035075813040f003015410041c001c001152007504a26480380c440c1c03601500e1325507010103605c1207810641c1c0380720000e281c1c2c600510450514640c142d01c12206800214104283d590004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 634778480 1250 634777230 634777249
    0x1140103020405220308180c0a15030e16050f01081b090a050603070206090706020714060d0b060301030503070201030b090c092101090b10050105030c0a0807090308040e041a06 77
    0xb400b0300c1d6075100048a501c0c1c0d40e40c02c0c44822a410204001d10b0700c150500a1091000399188015103007003540e0113181d418001445804000042c001031240c1c0d1805000f0180c00620b6000007007496100c8400007203002d001d0229900410b41c00c010b005129080c4418080c001040c4415141070210b11014400d01c040481e000e41207204030a14070958440d4144041144181c03241d00203034100b2404428807600356000318a0380e03ca40307040303421103c88541c1d40000b02d030368281034483e5001d1805030f041c0750034032810034200401400100183c0881c042c0c0c030440c041019030b07200740e000b44c440d0381000c101d450844da40f6010368000c24408031024200c0341404916203000703102e1a0203552051265079001750706a010200507003c402c04400003002500b070507003842000303000111155500395000d6440440c0c4c542c046d13000d4070300455407208000d040403d1054162150100a40900180017440c0320000004e0200300042000d4550b2a050b00703580d013040d00e41400c1580c0002c1360900c00286140400042d5118a0001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 634779730 1250 634778480 634778483
    0xc060c0901030b1c02040e012d06050a0807030507060810060c050c03061e090106060f080a180602180307060e0118030b010b09091b1222121101140103 66
    0x22180d4800d9032900581c01000381c40e004035003204140b00c103444c9214444148044007070082c0c5082c820381942c00f00560880b1208401d03004688603028160380c40030b81c40900010710715109407001402544640014511000641c0114400d602000701402040001d02c9a540100018203140b02e9509094043d0441400309000ea0010400c10b482c407242440b40401035141c8010002d8240c58682c2840183d000100001c005500310040d240c1c0c000c10095001403142c002141c3c1c0540e1410794405100800f00d84041c006407002c016241c581ca12150280c0001440081c0d0603c03607a001607441d203441c0301d248031540c248004144683c220450403c0344940095000d5031001c0c0074a000719140c0e0811445401c020131075000030f0a88100b80002251042c2000700400e410f4408656031100f0340c0c0c4040b203841040721032665080a1603810700c0f442081034590403040360000c003000c41ca600020345208118115020850003622450300281c41e0300c00041e08002a49520f521100003440030001d400c038196001e21040c0b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 634780980 1250 634779730 634779751
    0x2312071e140d05013806040806150d14031201050f0112020f040f08150105151603030906020706060e011403060f090102040816180615030b03030f0703020f0f030c06 72
    0x1d20000c101080d8000001c1001d003c85400b80003121209045414508880d1840c04030311465403001c4c80e241ca80251011236028000615290f0f9540074a4400901003141c042e400a42203115070001600100307203030f5009082c1c24001c540b210b00d444032245060750103a028a01030a01c41c5030242c107999200204690004034a9005a80c440710100341040c0d81c072899016468030702030940f022450000100d142c69412005240e803c4080c1d0b201c03001c00008000c0d410325101812410800040c1070399052050408180c02030a0010380d001c0c0381c1d03c0301020384e4040c18049444c3c030f03074448090092900d40c5820740c1c05400404401c0e04000750762004241d94000c00b410107443c40600d14005030b42031200350122070140c141c03201a1f80111015241c06000c000f0390f8012000614004001004220000e106140480d60140c3c980c000801c1d0840065009003005c0a880c2d82500003001299401c00d62100280521482640100100785c0d0390040079041601e00e440103d040c7e0010020f2300a5040005202074002c058982e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 634782230 1250 634780980 634780999
    0x3060f040507050a081c0513090c0c060204090905060a050c070f11100507051911190302040e0f060c070f1b030f060c020105070f08012312071e14 64
    0x18000e00c2c0540c940d10056002c2c40c0254041041e19010400041c2020100c00d5a07400102602c0103a400707004031448004e1071441103c080100d040b440c0c100a000054030305049440340c41648444083c0d81c0260440400d0544820311141000400c000f0710360f106c500204e040103181022100d01e0240d10403103001401041002110030f0070300c0500d180d100442200200001024030402c8806403640d0042070041d41c46001c3c000038420150300801700c403c200f5511203000703c5014101000c201007401c29540f800b040101102c0c001c00161510b105186034511000d0041402107800e80116141c40d0000304003c038841d0f014001702c0c00040000c0000e42c0c0207a440140800380d995400880b03c61040e4036070028007038180c0300d4810000c0c80a29409401c410303070164002c3c0031540ea115015076800711401070a03c002074052004001d9140744105001941407170109007a20f0701c0d40800000d0030301040c2c0b07003000f109802c000010804400001c80c0020040b51807003014888502d42000740401c014000ca50901820115 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 634783480 1250 634782230 634782233
    0xf06130804050a06030504030f080609010b0d29040b040204140f06120415060b0a0f0e03030d06030605011e031106031b0a0201060f0603110d111b0102030403080a020903060f04 77
    0x11401d840c0a00300c082c180c40c44096640324020050702003a2810341c0400c850b803403422031442c0309030112881243c019007818000e91901805484560011440107c80d0755a200c040c0a00441d503070385200ac10a110619441c0000c0210821040740c0740c40504510840c0704110403c980c5d65089148148007404845404a0740c42a00108055114805115100070a40c10400c010890000030000255148503410041c03141c8800d50b021003417054210030030105e500b02030501d141c0c030310a480c030341c100f440042c05803810b00c800c40d1200b070250f8070b0f190000c4440c207865100500c1440c14a51a501e024001d00a144c3c600c00d1868903143c070b120f01e1010003c0c0c02083c1c0000000c0e8600d0100300240300f903244480200360381d8009000000d0003444640100181036201c0302000a10324032078010b045515080354000d030b00d000020342446004205010000c0c2c0c03c1c017014064a1030750b003c080040c150325500e82001503074078a001e2800801c8640020300d02005a44140030b40391403a01c0010345181c0c40f00c40946410b1858555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 634784730 1250 634783480 634783493
    0xb18040510021312020a0b07060906060608011404200a0503090c06040b0f071e060221150111100501060503251706010e100207050f0315270625020f0613 67
    0x1030f50447c05420800064942c01c01200741d1010030300c20f006402c1007000300d480300700071590030302e0038440c02091108154031080180303881c0d44019115000c20420078918500c0c2da04481403500641c58800100e0300100400580039002c0c010600042403c5070820700c1c150070070b0140003245c010120780426108000c580081000030100c1c440460078036480d684525802e01c0e103000350103035010159002c500b800b44845a054601d83c0c42585020b51030390941d00303420b80c01d0700004642041d031041c10002184296403111500000701e00c1141c0c0602203076030b0313125540c1c80c002269209002d00c440c207080c01032103c51b001c0c00c1801d41c400744041e0000321001511050b5142c2c0da00480c0c031004403a070001d902c4580924414036054000903104111030042d1460b40304c084d076400c1090f41341e40200f4113260b150300b032900001c0c24118a62454606c3c03003072100300480b40440d500e1125403410400700c55034280f030045030608207000f030b580529070440c0700708900c001e0402c6078031a18441d8990383d028000700c000145944c1100c041006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 634785980 1250 634784730 634784749
    0x7091b0807050409050a0b040b01020c09060607020607060222061404170a0615151d060307110a0302061e1905070203070503030f100b0c070b09040b1804051002131202 73
    0x1092040c4070a041c1045046c2c000c0002c54074840c41a8078250a0404c254008034010003142c2c40180010041e036140400e01030a13a0019104a82c024000c105c803200140031813010b080b400c204a0b0b035507078858811030315102e04580c080e08003000303100030b1a04c1f42d450f890410003160700341c0310111440110b208100400780d1030a0b08002004002c03a08090309800407040c0006003030102c2d1240010800124082c6d141580c0000315129200d000c0d0620358082100c2e4107001000303603042400c5103403507000c54582c0410103040c00c2e40d246007200184c1222061002c0114008886415142010804505804e1150310754006040c8035092000c5103442c0c0000401650003403042d01c00654205044da9902d24140040c4000d8240c119040c1c4515481c6a8020a56001300d0050b88c00440e03556008001c4182004080c821907002844042d603c1503c8403000409038840302104100303003c0d1110000c0a6041a1401c80e0424006240c1000d2182c030621000900c000660700e5035080b80c0480304455140d0a1500120300800c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 634787230 1250 634785980 634785989
    0xd09020d0b041a01060926030403210e221d011a0306070903020105070f08130303030c0f110a0f02040906140a0b030105010323010603020a080309010207091b08070504 73
    0x440d100c04100c1840b400c1c0000032500c0342d909200360040da8179284141c840c0b81140c00303200540e2100300c940c0340c4600602e16114000740d4240c8116810280d4980c2c544803a6070301600c040302d01030143d40c4100d0b8010703081040314150103800c40da0b040420131510059070b004051070380358100c0c0307035114040d01030041d904003501c80d100c8940d80020700031a100c1d04d0b84104c2041d03540101c1800780c85068002404684036058020680347c0c16580e0501d402c4ea00d880e803442800850000b910058401c008a9112032040842d98000754403949000c0b80d0f201c0130940c080c200b00160300c240402e01502083c82483c075040030900010069001c24403c401c0c42040c00030500078107808000402c204e150480c1409070300e80c0c182c05184140c4844400344400241e142c1403500740c072000c1c400285507000d090703c045404a80042000c0201042d40000074510b66250001817050b54903901c078500e9a04002101030207540d060010a01502400700c0030b100111001c0490580304990201210130010150301103132155201d2002c0701c0090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 634788480 1250 634787230 634787243
    0x3150f13180b010510091e080304271401061422050a0801020a1e17010b0405011b0804060c080c070e2401120f060801090b0108071a0d09020d 62
    0x207003000140d6000d000c92a2000782c80c050205000050540361000203000300392500d035030b440401440c021000790f19519919011407101100d030400300b45a40c04002820003007140300302e54011045004a4010050120080c4244941c10318844d0010350680700c02070307811030313600346001031003020001000c09443c0103501e4801039039003100f6540103020696880c1e607825500c044600492450751480010300701c2c8035040010000c184112280100391400100811180c840e60601c0c885807a00c008030700907500c100344c214100340c8101180600c51540d00500041d91a60070400c03619014400b915120031502451290340308004035000c02c0c0c4104020801030707500000c07950080b80c4800d80c0b205802d1a010f80101c40c2c20314042c0c400320007002d40f08400140401c0960301a1242940104100740b0003014242824948401c41c0e01d038040010080024400e84a00c1400303610741e10f03000e50418080f01d0800141da4030581041c01e0b0540229500740d429801c40341880040840010211118808034038020340158020f41007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 634789730 1250 634788480 634788491
    0x6030c0e04021005070b01140a05100914010507080405040b0f0d060903030b060a0c1202030c030f190f12022203050a0c06090605092103070309150503150f13 69
    0x142000020681c0960302c01c9489003c0c0300c444000488281c001c1810150000741e41600400c1100310790b20204103600300150110214036203c10108a511154801010015000d4001001400d614507041c0704158030910f0941c0c80c01c03d075a11285210700a90082c64030459540782c8200c0180e580f041002e0740700344054072040c5290014101080101120700c001d0b804642020210b42403441d028086503003007450ba03203855a241c002074403964160a41c4642d00c00940c0700801846190407001c1000c0c11903003012000d80e85d0f0310a510032241d03001c5061030400006104561205050040c0c2011201030074401c507070b10041e2210b401014140103100b488a0140c50100c4010002c02882030210701480064007880740444000d69428044541564a104920009070180321628661606210200c0941b0307040442c1c00c1d880304200c1883e81560310816046021171078000c030400148031a040401c100c00c0c1d0750308245c2d04618000741203000b04400c1d4a03001340720360640e108540c541c0e0b5a80c03030002e142c80c0609404104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 634790980 1250 634789730 634789739
    0xe0303092404121a01050402130306020a12180c0510091e0b04060903060b10020c0f0d1e0212030a120c180303030209030705031b06030601021c0f110a1a0a06030c 71
    0xa4140c28221140d4401d09213400100c3d5a042c1402180c3c080c0d0003c100641c107051943e16440d0094001c42e41c1c4200f0020742006007040c0045501544800614281c2c40440c1024546071100c0303d4040c59100b40d001d42c00d00455031070b9050b0070003091012940310b6090b500c071010b030b205440c0342900315a030000790740001e005c9004162070798450744040c1980c0c42210b0806c281c0c2c46803010014224038031210800182d000c017035240524180070150780010300d006008080f1264051b501d8441c6c2d07000d0b00b100700b844400500a103c095240240500c44120085c0300030703510301081080c00404902e00380d40c03041c4d816030b2a41c1c01080c5152103030403113115a80c50506105a001d85a10340100603521200d8031910034070841d03902040358500816440800040d104409699030340380010301c170355900010519411740c042c9801040c1d080d2a01080400e4011080d0343e900b03c0c201e02c015019000041501d40140d0359446140c000c0b0000c2c06250a02c08415109002881c16503200c07041d5030054141c503000182400704807240003d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 634792230 1250 634790980 634790993
    0x602120105040f090c031e0218060f0603040b0c16051e100b062205060408030a020127030804080d0204140a060503060108040f170f03070e030309240412 67
    0x24181c400c01c440c00e1010425250003e4161a0b00d203101034070b454400721040001451813400c0040d1003844884220603e803c1e6000034881c4441c804402040d800140100a09407400c104201c00125044503294118103103a210f08850750300051401a1182001500b0344030080300c40307490805254094100d410074001c8100b045484190703414071880c18428100c1604201c040d42c000c80b000c040002d0442401e2000c0b00a4180c0d203282202c05a44041038071013402710b1103454030401400904440d400841e44e940d9100002030840701c000013100d08522902648901c000506c03410400d0240e003514141c0b1145d143c0d800d240c0c1a62082008001c4070500c00100050031514100020701c0c6000700700c0d0184249643d401065942d0f00c01191340d50f0001d5a00c40c006000180031000911030a40506000d00801c00b206030301e4030300d44e031000710030f000b14000100420019030341c0300024812130f1009034051400c200c405000700d84a90b5444400380c0300200c51282c40c521440301c86003500c1c0141451280c0c40d407554800d08001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 634793480 1250 634792230 634792267
    0x71106030403170124050906160b0f0c030f0109020304031101050112230a1401091e02120714040c02010e06070c030801090509070308070206071403030a1a0a03120c0602 74
    0x581c60355030f6001c000690303003e80250302020a8040c00d0501c072101c00f0500c00311806c0e40070b10805580000140421501c2e14551031704044400d00c202c0f0f08110b20b08000031020f0580c080104401d02070001041000a56100b41610034110b501901015880e500c0303929083c0e8042e018403000200c9503180200009840e40c080d01421000380c042c2a414040c0001c100000201182400c0c00181c42e50105480c2400104500d0020014100340c01c00024040c00c2d9585180754403103000940c04d02502035402400641ca0840303d4400040d81c072000038404a403601d60110fa850204904051283c0c0e580d11142d06003500030740260f1440710581b01624107924012002802925520800b9000558107a001040205403407250030b008001e40300040014034a161380d040c61030713800444100d80007841800800000b98400c80030b100c60703882da0409142c991500200600c02c6070004588200020002c940b079a11940350183d0140541e13420225030704194481c10400c1d609003d050400506040c03000030307207480245961042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 634794730 1250 634793480 634793507
    0xa0509150414060c0a0308090f01020309100b031c11030702030109051e070609030813120606090e0109020a030204020d020f310303120b01030f060609050301050c0301080d05071106030403 82
    0x140c1070102d1084080c00014000d22803802c1d01e991002e80c0c8100800c0c00313410a1917220740d502084840c44950310b0003a5003641c205403140312140c1c0c4154140d1030980300d01e000c0c40b455a402940180b01980c05c8000810340d840e10700316400c09000542d40c0c40c20744038409000325010341c0d030040c00174050088a8a400760340e4203201c240304094418010354100070940042010390440c3e9460780e034405917034116114030005a1000d00c4c00103911030a0713607000030001200c1c1c803021440f1b07018140000f800c0c0d240c08500002c0d240c0300c05070b51a45074944100040160703600c034000c1040e41d4040c2d4005072a0300c2005c203440000d219290306100d01d148046508501d451100c0706080389130720620700003040f8840c4c040c00070081455034040100400ca009072040d0314540d050b8041c5c09041014500400c3c0c90640c00c8221080362403035000400001d48030f1000f070200381424014290040d01d00b40d4841e24542c9405a180c1d2a600000d01c03c01c10050b0000f00e002c1405805d01c151010843c000704207030f03135078101894082e018051a860 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 634795980 1250 634794730 634794749
    0xf060c06050a0c081b04050405040506060301110310060e13050c0d0e19060b0a030c0b040f0e09070e04080d1a130912030c0203120a050f0903070807080a05091504 71
    0x240710b42c071103020300b85086100340c5580c8800c0c2c54640d143c0142c02812583d8008a4074207002c0007940e690745000f5540182c1c040c001070030280c1845018507081d42c0300d1940c02001c440342001408030421030001c0340703c100e40d56884d003d200b0480c42c0d400107041c0c03c01800c4460540d400d00c0144007044000c44000d010100351040c0400c103400552450070348411400d0403603101c3e070030107400c00741c04510355821036480c6200c018007640c0c20684a69803101c400d91b45070405586030001003014406802d9000144002d82100d004600071341c03410000b055a202c1d002c0c0100b098840580000c9400c02c240842070300c0d40c41401d140c05000d4444000401c012054100400a200f4140f00319008000780d0103118106c280d41d0004108224031850340c2d01600541491032a0300214403080003c0e1000a6404496500541d401c800c0843d581c142420640c4440601174a49103103078204204460004244138111070f0055407000c5030300e031200411401540c0320301402210716000005d88050b001300c003541000038070a41c0c00d42031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 634797230 1250 634795980 634795991
    0x30e0f0708121b0616091d010302060c1207081905130509060d0f0c0608061503070e1512070f1103091203070c0f050f041a040908040f060c06 62
    0x1205955880951162450907000b1100c00d80012225000425045400b125000c1250101480d0749203801030031601d46128114000013150202da016100c00f00418444c00f16011103c400303a0208550300061000a128003400280c1d0510006c00b0700c4804114200055010b072510187c1c102811940e221410300c100c480c00311f090004040340214191121402050340041e040350a01007845200710020300030300c0d486200b00003808005042080c1107a0441d2283c0d03091264149040009882b549010740580d00c51040191045115042c200560343e11a134545014800f03614007a011620340d120f030304e02c070030400d80c000140e4242c10400c103000e5600540d034a6480059050803102c046490b020101c0b15040103400030003462949180c0300c1d240241d4018840e082c1c03490410941d1b01c45a19502c3c3d030f03105414089810f402046a4600380240d08400903080d5801d0140014840951144404003002e0910a07903542c0000c40510540c0c3d070544014010000302008165150031000d40350b51160075007207914a0524 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 634798480 1250 634797230 634797253
    0x3080a090f06020d030c020f070f090b01020f10050a090b090f0f031c020306040f1506080f060603041b0e01080c0301110f0403030c0f0506040b01030b070806030c0609060f0a030e 78
    0x541e0078121140d0b94003400c3d0260025104601030241c4040b26404c40c488c0c40c524000d002418400031008100412134240e00900c0d003492039041e50800c0302001c3c19500220341340d10a00320085140110b103941d4500010320b5540b802c01e040002c000380b0401500301d0040004002400070001100500f40c0e040c3c0017102e0310005100074090741c9208601400c09280080451302000040c60b80203140c00130b00007480401e002006130303005001c5801601004401d914292803c012030341c1c2021030603030810b003420a05081442e040d00400d038035200c0038000070888109200403070004964007204030b002e4988540780014551750b440e04260350f070b498546080d209518295010300c40f414050200e9502d140210001400d140c50b5490039101900005016035070b22000070350400028100744682442244a02c0202e4030a504600b481e90201000400c920b02703220782401801407941d00011594030035a0216211943c403401100428820b0145d2000d400c184200403401d1584940c240d04a0388440c0d10017011218442c24070b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 634799730 1250 634798480 634798499
    0x2010215041110020c031204030b0c18100e092505031003240e100606030902131802030f0f0c0102070b0a0f0e09090607091217130e0103080a09 63
    0x1e550080c0001ea2940280b84a400c01056224102c1c03000e005403441c02412101190405520628040481400040034400c01296502c030300e0f00040c150110601704142c101408203094080f240d0b25201c2e03280350480c0814107200310000c51180001500e0019103041a814540d0381401d5001c040006040000019030220310500c00e0368440c00800540080b054034546840c00b075406910f260000656039100300c23814950b010300a5940b02c0a80d800240401ca42102c021402c55034560407800406003003001d00c03400b50f9140107816000912820300010022240d054015403501308100003034050041c4a44034105910101c0c05a0107244000269050515031100491301c0e80c03024060101d41b02e406000195815100b100b00c0c021010309410b0a0344403544000020308000000ca801000030750201081004103980320b4007020050804204580d60001265500d51520001000b100e05100e401b04400b1343c0c8880078990103000306061308911010b541c580c10581c4850780200007030b0b0080349603200d001801298 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 634800980 1250 634799730 634799773
    0xe1e010c020a080f0c160807090c08130b071b060b030c22050907032114040f05061614060106080702071d0604060b030703060807050607020603010e0c040f060507020102 74
    0xa000074a81c2c0360407130700250403401d07030000c802518903440303208100c1d2003045005182c04054000340d0005c2c14013900d03008610040d40e0440068108105501c0c003070122207001c0c200f60300e0605074801020440c940d21036008640040c0343c240c0002481440141324400d005c070030340c00481101d0341035040c1c5980c0b00c1c0140601c80c070034654171041c007040c3c001c8000c2c400700107443d94461a00001d0410995110300d0b626100c4c0064040e240b9048003e42650150940481d0780219107090910031550070709081c81d03e07007021842d42c200548101d5004000c0007594007038010000c00207041140c2e1251403020050b41d01c1060580c1c0e800e09000700e00c04246c461002c148400d0002540c1010ec03006c4003017203005281c40e103030b814245440c0038205e140c00648985000c43e0806142020f9413244d0703001d03640003514610b0440070b2490000c0a6012601410b070400041c00962540412a419581c032680000e090782c8503d40780141ca48030303540c0720705041d00e0307404004580c00350b0100081c118903000740c0c00c59098141068910000c40c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 634802230 1250 634800980 634800983
    0x90605030a080f0304080c0303103314040308040905010e0f0405100b011e03051506030c0f070201140a0306090605060c150702010207020a122a0501120e1e010c020a 72
    0xd014480f00011903010f00003998014481d1000a080c295050040c524541081d5100c0013803180e220360a11400016001d0a1407480b64092000500b0107600562103c50825012080c10031080e1410388040c0e400080c1210010742d800200291741e03590303a10044004040a014203407000c0d240310b02050352071003080241e40c015a005030241c03002003046500074004000701d0790f145060014560303275000040c0c40b80075201030340c50454401081c42d14211200ca12a603012103600d9215403000c0c818802c042c00d0200c00e13036090811414030782340d0780e040307600059038400300c1c540043d0f1100380005107000c140f43e4141c02507021190807074000e00c54181c407442040840d000300120701c107442e480708082404c2e90781e5070301e0340503004030480c00018541b04840e0081461141c1540107548600401c0004008200540140d050001d203045801ca100e000f81c4a08018081e416108150411824001c602610301c50303540070345140c0701e0000c12a800400c0940c1b40340c0040e500541c261019501e01419560312500101ea0400d406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 634803480 1250 634802230 634802243
    0x302011107120e18040615120f0609020a050a0801140c0f030601083c0c040302010c11031f2f0d0203180a030507060c030603030909050a1113090605030a 67
    0xc1d20b0100c403c441c0c620640010942c000400c158030801c00201000b1240143d00480e80030628106130201d5121486060f40002c881a80080006001c1840035810400080d8810030210750b800160000a04660594001c0380d4041c3e034010000800550550200c1d800381040800c5818560b2000c0d10500240601540c02485204c1007001079100c0d845281d15943c41122804044ac2c04041c280704940c5030840c0840806a010228a000100d00400710348960721241105005141034103690000b0704080402070010540081d0f461102c1003540d00340240303040c4d42e05031030903562341d203100b660300e90064440b0b0a0b543c0702c504040d03400503107040305242041e6100440d00c01c4082c9060102c41124000798130043caa00d60b03203464259031030503412051004081c8140203903505900c488060400f0012a5150003e000505103803d40810010342c0000c400c808480b85098001126983c0f01081000b0300219a254074180100042c0ca00c144000600c41200352003030140104140c0d40c6680900d070b85c4d0207180d400074121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 634804730 1250 634803480 634803503
    0x30607050a0810180608060c04051f050d050f16090e15030c060a0302031f030c03060e01020c010c0809100e070b07080d050c030618040b19140f040302011107 69
    0x14240100c2c1c006401c03508009600c404290b4813881c0c05600149040c13207000031071711600b00704090300c000c200170342e004170091325200e00e03080c0380c0300011b2040b065103010f054044003001c1808421074022410789064580c404800d0159140c201805140080111114041d0f40070300501c01002a1040f028081620388040c1d94003104c1d120700700ba0740f0010380751030780050341885805c9104203e52070b040e0183c4900445034802584038102540e000000080ca41d00f05030380c00c0c003512401c00c08661984800c0d411039410460000e0003408512405029100e20301d500c0340b0641c2818643d0000c03950001045210b905030a0680346041166034001095030b080e0003140d949988248803d11501c400b08000340801841884050b1620103180d0401050b24001c0b19828941c06001c8100041414010784800030020803001503503007480d26035907100d45a41d0142a22800d41e0704403510f0302d40b496495000742000020000c0c01046450981002c000d0345a00b281c0c01c60042d4207280700e1208c80810a01540c2040d648545071000c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 634805980 1250 634804730 634804747
    0x1c0c0504050912040803121e0403120902091015110604080a0c0b010f080106060c030f0e03031c0509100b060d02071104050c07060c020c0d150902030f06090c03060705 73
    0x6031030041d01c00c5542d80645101c007101c0c9440100104000e0030604003031605c4004c0f0f00341c0840c540340010003101404400f050000e50004038061030651040e410b05100d5050005103840d000204142140250801d052205001a0048500d202411260000140500e2012002044920380c00c1a286070340e45511800100d40001c48140140119114a10b08802940031a4440030083c803000c0c1d1114801c24000c041c10300c818403082c000c1030b01070880303400c0103c5031094903600202102d000c003c1040c2002100c100d800c20a540600880b2080c021104800d40d1900f2031214810040406443c242003a21079155a0b8601c00d03040c1c01554a00c000044c165401c10711550551000703580082e0084071000c0701d4a030310b50020b81d95486000d0260030b0301e400d10394a8100d00d1801204a40b40c001c6070310190b40c801440019182d5403400700952242e840a81c01c1d40000c07000d44110b006c1c0c1941100250306000c2c2e9940c1140000000a80901c1221b0380003c89200e4119075083c10340715101030720b105001850411540c103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634807230 1250 634805980 634805989
    0xd14061009050a2d030f03020705010c1208060a030b070302181027080d0c1203050c0306040e0c042d050606090d020d0f0b071103090307033c021c0c05 66
    0x40da1840650030700150700050130004803000d6081d042198400c0041d1883c0051550421854014010078281000030040c15100d14104c40d440c403110008000511000030300356118a80f0300802585d0000c52041241046803000c1c004e03400c001c0e030f40700400700c3c10b240c44e80707041c60304030003503100c031080c0d6107030010600701850303904402021200000c0c13507040c2e81c103800040b0107100304018418102c0a6a4202031030006d860240307644036100355400c04160602090003a030320241012a80c01402c11140040c1c2410040c1215060040392041c0541c0585011600c1580c80041052411114480942c408070102c14603440702c00c0707480540e801c1e900040309000c044a2070500c1c56001c0320640c0020029042c190f0b05590f8401c50341e10b00d00007140c54468030024401c0d5980c10242e0b804010085002450600003841c01003541c40865200c003504111410380706140141410700001c100c10346502d040292221410059a40ba400404040340103000305141c441001c0b41300c0002c490317901e43c00f13030507410090701d040c0402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 634808480 1250 634807230 634807259
    0x30618020a110706090627211505070306080d090e0c04080316020f01090e16050c030a0c0209060603070e0f060409090b010509060d03081b0d14061009050a 68
    0x410034001c2e61a5800030780d960800076100140810740d11002043d081c0310b4000d00c94151b0003e082007021000c131a10610182c0700b5002820703905040394008004007612130514012013013074805051100c184880210740300705508000c1c032644850700c1c280000340ea12940541e9468410715183e0001e943c000c410302c420300108102c140c00c109660103040c00c058861192900b15407100c400d40b03500d072405160010442c02c000000c541418001d007882c6000c13900d05180181080c2008081c0b00130341905580b0410300e41d028000762202441c1d480100e0f070b00c5410214000d0242c810000090f80300c0c40300500090410b250081c11071f48104982c1d0303602d840d81300c12007091014142c03400712900c0d401442440017040700c040381e100361075072640580046545545044180040141e001d0071150144021b4500800400c1d00090500d0300072142d80860700d6545141403243c0410700404d4282000c49051403c00c034012039508241d5800740703100701d500e0380c40c1100e909829a115040c0b846001d41002030314408000390006d5201c203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 634809730 1250 634808480 634808497
    0x1902030408070209010902070213021e0d0f11070506160c0210020109050102031003140303010608130c050a12061a0f0f010203070618030f02010b0d0f11030a030e01030c03061802 78
    0x4030390805482d42d0000d20800802d800800c0061ba02203140300079850912624121800c1e016021850078280024040201042c0320990341014000110100741c44030a5101c12400d4008400802c5041341c03d40b0200c015601c18030007541c5511035040459194220102c609140c800585c0303030784600f4415542401018080c2507458800e5550391100b60004c030b402030000350710589210f421f0041250a61a2404444007505207607040d40c0d00900060064075041130749541c00c03c0d5005800041c000607450000704ac0001c9401864010091005c001002d070900c078441110b5034801c3d1424441303460803115002c4030390030241420758841c4030141c415055003031400d15407003150410b205913460b00c1460345038001580c0011542e2014201440482c3c0141980b0101c41c1e5030a42c07aa10003440030681ea0340000d0f1840c1c0135094068a183c0c1005209002c22541984000100101905640c4503002c103003406804400e04842035800307c0d007804601e07502c0f03510a01c6000260380030051001060410001c9002c000e400050301c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 634810980 1250 634809730 634809743
    0x5090408070b09031e130308030402130e0606090a0b0d15140c04060e0a0b0702040507050d0906050402190612020d0e16050312030103120e031e0f0705030619020304 72
    0x8440041a0b0540407903115103032501c021a030380d6103022803503001c21180801c0810550000e1140d5502c003203089010004581c0c01618250312070b250340c0001401c03516801c03c3c01304001e207050400c910320710000c03902e503100b140c00311980b408940da0b10b6958000d8400a0034003980c0001540030f103a0008a544010342c0041076602c030000b0303c007d044d01101240d518181c0d15009165400f140402119074804501d5107610000e44405240c00c1c54942850440c0c003071044001e2280d0b40b43e00001c0c1200344540262442c202c02c507a0140300902080c20000d005003030590b4182e001da5034640e04021b100b00c144500d1800c65240d0790720b4003403c0654110690081d082040b04a0f4410388500c912000d4850030005900205502c120a040303480c607140c00c042c0381800c0d403a08040088000d1004001252948100c00701e4100c25040c8400301c12000e00000e810300202540c2202d042c24250b1181084660000304811071002d50800c40d5541074a0b402003641d11641100e03510b6400b404000d140b0600017440c0c01454100b4401c12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 634812230 1250 634810980 634810987
    0xe150a06170312011508010b0901020102091e040c140a030504020a08030406080907050a0b07200a140f09040b06011d03120d1a0a0605090f12030c10060e0105090408 72
    0x50031400041d2205588440c81d50003c200c82c1c8041c09001c00c8140181480010312480841008000d081240705102c1c46100d10408615020140d00030740440d000340b24000c14000500392120800c0b000c48200c40703002405149481c0101d10b915000b1040c0f410306a540350681800c150010004501501000700f00300d0300300b00381090004140c1c10820142014201d2078031001e9803807400715400351170000103034007061003001c0b010420042e00040c1400c9130401a0000e04540c1a11048422410441c8003203048070707000389070311000042c0148035a050f0880c2d210100e605100c841c00c041c08006a48405680244c1404c0b03820000c0f0b80998001c00d001e04c00c0c100e014164030140c684d2400024248041285401b905080c0016000801040c610441c026440032614134481c1c0032145c8042480b044540c0600018888001b0304407880e6529041c502d5012040148120039880805119030b4403600b080340380d82031074401c1e108880c1d4a0080c0d0300500040c0e03500688001742582ca004108880036a0161055841080c00c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 634813480 1250 634812230 634812239
    0x708250801050103050307051c0e0402180904050708160b090415080105040803010f0512060c03070c060f020a0f0801080309010e011e02150604020a0503010509070207081507080a0e150a06 82
    0x1c0c051580218043c0c8081c47d11451a4140607080070a0600c0340c02c021204040500c5003076400440d0040d0820090703030010b84516020b0301e4a4041c07520360707001076400000c10f4100b00401800168a030280c814240c140e401200492004d01c5041c2c19601802c0c03081c1c001400000f0450605500c0782100b02d0215100e600c105d5030f10140d0500f1508107840640b002007002006009042c513148640004040c20756002205640c000c543c00e0315032001a000440881002000c203405610808000c0c00007608400100064810100c500000b948940300322030206895540b0081c100d0300400d107040c100c81c0c507034014510b4900c00304011103004180c0f004444c144102008041e1940528903c1140c1a800e10380040404a00322050b0034400b40008002070700c5240104400140158004152411210b0a4078060b07555154818268108072554001c4403d40c8900800c1303411007544c140d40d241c0a100b0301c2d1221205034441c00e0787d00003034030601014410720380d10074004684d60101e00c1030350560000f01082c0001e241c076200c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 634814730 1250 634813480 634813483
    0x1020109120903111e09270106090b090405030a0c0f0804030f032a0303110c030c0313062a060b1c0204050f070e1003021c050106020d0207082508 64
    0x810303000100060b103020041c01003009240c1d4581d48104c00300d9040e098044684a5181c000c90450b0005001d450184041014040c4042c0941340006094604007510140800100c2c000e281c64807484496608003800346000c3d040c4a04021b02554000001d10702c0c00c0c20180c41038884950803281124081c5c5c0200c0318a001c11a508041d1015502c1481095803a50741820b0040140800030020481410100d00e00782039405a503c1003144903516060100700319020b9001403013075010352031160f502400300251034029a4008001440c4107a449082100150b48402c0100c80450510054450941400c0e61a00c9210361043c202008a44140004141c1054200c0458401c501c040441da024101d84414902140707410f001e0300742d002071240e40380800d91130441c0f0014812581e900c0b20030b00400701c403081e00742054402d4044401540a054518403000070701992240148003d102c0d500060044407588007400c1c0c030100f40b860443d4420b000610b0250410500c4102c403403180c00d4900e6103a0320244000036031140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 634815980 1250 634814730 634814753
    0x17010b09220c0e0a0b24031803040e040302010b0901080613030509040b0a060e0f011e0c1713060906021f1109030a0f020103050c071505060103090609050607092108070201020109 78
    0x3c00d0b08045a030005034020b10400034444100c907125110090401c40c042805c45040ea41d11a40c40104070008c800d500c0d4002d41103100381e030401b044441d20740040006143d01500034a00d004015108610a0780e0396004498848809440342c99005c2440c80c10840442c1c45500a4100000300400001d1409018000200b8100490784000003051011003000d816140c1011032100c480021f003000c00400c0c031201000040492100921002d01c50648102d038144820381d0801e84291040d00b0f00e10355242602390444181d0b40d05407182c00c1c00100140340120301944045074820b1104042c5a038181501030b081c0354280a0a1200d5100150250500c510720319a40d04014540c000e6001c1e02c06100c1d103040c940001000d0300c2d401450020034940400c290000a454041141c2414074108000a03040d150240102d000c0c00310b16030050a29402c1280804c2402804107029005901c40d40b00e03030701d00d00d507250065000200c1481e00240c800c40000700303c86c003050301c60004200c1244144000203c0800c142d68040701400e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 634817230 1250 634815980 634815991
    0x306070f0c080d1d0d080907060c12030621061107021e060d1406041d03040e1003140c09060922170c0601060f02010501050627040617010b09220c0e 65
    0x6105c0350480514a0b00090807680200c0d0540187c0f0f44242001400303800180c001200410481402d442d80c1102803080d0b010307002030301d10000040c091a5882d02e540d803040824031000e480040c68404400404040e490407901680da02070f110b82d0b00d6500214003c00340610214640e41c01c20360810840f61031090030310401c48080c0c481040040a410428244001c03500b100821207004078030a80d00c0a10400000141c80c00c03a000884104400da841c1c00070050449a40d03072009090150b00c031040e08000c003020074003100d400c00a960410f100d5a80d6070030810b5640082d00c0c81e0202046441007000110100c40005da0380a0181c00390140489040c002000e40b41c0c8074203940300d2582c20000061140a40c4a140c5190180c81803000b4803055042030001500b42c4240050b2070104038081c2c9000540c40c0c02c0c044150036107200100100a49555003005003e14040981c00e400c080d4a8504818080c4ca81226600e004110300043c5541c2d51156100c0861030900d80746003610303100b130381ca03030b00180004ac2051020b1140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 634818480 1250 634817230 634817233
    0x509040b060f0910031b030803012d240914060f130e161106070c061506090609080f1507021c0203070b0a1422020a0905060306070f0c080d1d 62
    0x19403450a05011590405081e1a485031044104001162385001568192811a20031038100c3c056000d20703240b12400c3d42c002000d441503203000010042103144541c000000342200741034994030810011506440b10b4051080c0e000c80d51418201d05040200c040d2003840d000440503440c0020704032402c1908040c6500840b240c01c12242001b43c130080e20251100c201410303041c4188003a2507802400e4841c20020807071001c000a0b145060140903943c0c004c4a0845482c0303c50b010359a4940b800200030075606d001e19008104900720004002e01d00144050006805d8005050702e10310024aa10b41c00101910800c11841a04140010b98410041c1090a02101e030010340d070b035202c64902030030b50342001021204107034a07040f040388500018100d01580315821030f503241200d0300880d985044070043c650001c0e400800300c100100d02c000542c1d10460062100b10100c42159039024011a2a200044034a800207083c00c64920300041101025240e070744045007012a802d0744103210084060030119409015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 634819730 1250 634818480 634818511
    0x3040e10080106050904030206131106031008010606050f07020d1b0b0c15070206070e01110712050c030a051203060a12060b0f030601060504060c05030c03190215010509040b060f09 79
    0xc1c20709201e520000c0005a850741c01a18180c0c43c003a49a000091118020700b14001c05101040240990f0304080040141419240e042ca05054a80c454039400346519542c030700b41c00842c000740a1002c0d035003001200119180317445125400d1010502c8200001c550408080d00b1f0304107289c3d03007810800080e140e80d0038001d80f620005400705140528001d0300b001010011018407103010750110700341e94840c410b8180080d0384030140b00101c0701440700d800c81124034002c6840c041203009064140d840c1180c020307001c46021207296010140c80c0c00d00114010940e910074241d61540740c0100c8081c55200400601c9a51002d658080c00403401c4540d5000f10740c4103540310f0841c81c46190605628800350400d0700240183c0d0304250010300188158041c4500340581c44403000c003000000c1085420300b9000301c083c1d0740c5501c4401110101442e40010400240c001e94041c40001e424400d0b80e18102d5600400d05080c0341c449464502c00b9a8001c1c1a1a40018107005140b03000d884091125005da6490550101c0c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 634820980 1250 634819730 634819739
    0x409050106060809060c041505034615120c03080315040f0501050901120609050a351b010e070e090708010e1b0a0806040c0906050105070f03050a0203040e10 69
    0x34050000e06ca902804001d1005000c1400c3d8503041d5a01101207052203070303480d115416000c04000700f441e41c0d480d4900516000108004440c800d041144003400c0f00301c2464551100340c03c0c00e4803110508405a200110010002216078521400340c49000e1004039220985a403100c00c0c6039801210101800007481d40d544041d41030511513078074a9160040100105c1d4100ce00164481c1d00c180320f10080c03950307407171a00b0051041652203c0a0941e100c011140c0f075094910340100f404240c00199121144001d0b00540a100714020000d02c52041801d03080c13800b03104180420034280c180380409103d40d038503414032900d1031007013100070701411070042e01029a142c80e070006441c05010f50059001c50f41091140150001c1c001601014030f0000010001c8010444021400d4441580d00c1307000944a6034044c031080c44070396082c85081c0c8450704024060302c0e89810056071207100e4600024084050540f1700303404240b00e0006440c60325150300c1500c2c6010395481c86400d0411065624010f6404c0c984c50070003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 634822230 1250 634820980 634820983
    0x5061e13140f070507020a03020108071403010f05010206060a0e04170d02180301150810320402090a06060503062b21020a0812280516090b180409050106060809 70
    0x42c1c0c0f20990703103044c84c5000301341d5003c1009614140f0000307050289503004036042c0c03406068544001c091107440281c503983e60788542001d021043c0700e028094080e407400725105051000001d8162900c0c55904016500c1e1742c0d651021104020200094409091109400480450004044030f4410000c2002489c0740300c0704242c2100c2140c0d6084682402c4180e081111410110b4a026261000a07001603c0b84945580803c0460000354200380c0012000140311503100404400340030b54000c0ea1042c0580d41c88010441c1215407902030580481c00c00d0000404601e000c04c13045500701d0412031b02250b508000c01c1c040380342c40d0a1020440d00000b500714940030369450039003000c00d50102ea01c0100528003098031509181d11403003034000e40310a444400180c0d094107620582185103000d10705404040068049000100001d480341d01c6042d22204100a010748514440800c1d1441c8140945c035100262244c0c030566000274841c560403a40380c88141020075020300c00d540041c51640c580c44014640000650b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 634823480 1250 634822230 634822261
    0xf2f0109080d0e0f12060c0a0809011103060415051504060201110f0a1d091504051b0f0a020109050a121b120e220606030c0305061e1314 60
    0x1081c07160301c915040340348264801c2c0ca040304480181c0d00e5540410400002c210b9a040e900d2944a69104c0c10307060107602c40000008084244c075558030004980c0766215114269090102e0000c1c04d0401030000c00c1b81c0e4a0140d218410303601079180102002c56840000c5294084c081c8202c0030a10008603080000c40d4082c09800342d100440d116807490803194032a900c11038064008100c041040000f4210f12241d4061105c0013040b800400001c07440c58441e120a130146500d84126028030300b040c0c0400c1c08100f80600b0742c003001410340760142c240800c250040c00c09030440e200321401c5640391001c200100f0760621421810034010441611180420107000c1d0260400d4006075204c8141020701101040d215850700c0404000d900d4000e04520184000408010503040700d04c420042000210894000ca40e215030200c0e00d03113442c148040c00c2c62042c142c013250022a031540c3c1001c940071102054000e500d07181da0503440c0042900a50000c2c104d803950880e0102090003031060000c0e000d11a006601c510031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 634824730 1250 634823480 634823489
    0x602010204150219030806010c1e0c09050702060a02091c051c0f09120c090c0e04060506090108040f03260103031806201c05091512040f2f0109 63
    0x82c00d070000922650b8a4540b10024050204581e0746d000c50103d0384107004810003e0b40181c4049140c03100b450300030708601280502260002030742d220000360503416014681c481c0b90aa0040d00d06540c81c84043e20103503200100440e8404000d0070030601c0103014038244401940100020311013000310b1075910807000d40b012082d20130711111307002d10307098240c2c000c508a09072610080c180c0081c1c50f4619014a81200681000160504200c0d402d080036600c403003600711100d4104d0b01803090303d40c0c92042c801c1c580300d1a6412800101060002808107030590504003a4510a1038204000f40404400948ca080202031102010180702300400600d0381c0203142120b03c09034081034019852900b81c010b0040200800d581224083e01c1001344800c020501c18907e0500c0b4103140c0c2c0c04d98a007810b100910b10b40c0210541c07072141d078400741021900c0c400701040e5082d100124204a0751a04e8544801e440c89131000e004032940c0c1d008070880c00c02419039036045c4401c0401019004c0510540100250038210076402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 634825980 1250 634824730 634824733
    0xd05100b090a030609110a1806140d08280503010f0b03070f0c02040b030f0f15010303020d14040306060f0501020c150d0b1306170715050a08180706020102041502 71
    0x1daa150307941e9400c03840040300e600442c0060004001d01d0122414890307071a0655110900e00c00005540455195009080e12056402c100306034803548000c081c0200040702a070460801450340000900f1302000340070031407a8110307043c44405c00031225020000c46410003000110080010800d14103103410300c00140494442d12401c500d02038800600282c860402081003025890902c025515075901c1501c0004010302651941e803c50b68202d940e03103122030312500c01c52181e0001000316a41d00d4892034103980c0c2c0740e4043d11000c3c0011a0460b0740a100003080169424208000000111503124400c0108900710245d07481034901000a4200325540031100d00800c408401c40c00c0249281088400c51b104540000030b041441102051464100801c40c0050a03d003c01c0400c15a03801110740c40076588860445d00d4080e02e03040d419a54800e02e0b60f0700c0700854000d000c0c50486902076940c142d0b22488030030051051f0b41c5280601413502601e5803144000d0707540090188842c00e0010038000001c1e80600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 634827230 1250 634825980 634825987
    0x7120519020d110d0c09023610050d0e0a0605070f0e10090b07050102030402030601050a1505031308130312140d091113051017030a11070b0d05100b 65
    0x100400c5101c10500b00c0102814015182c1c80701c60b40e50240c40d030388501d403c0707500c52030140e40390345984000b58003800c21101e00300b110715403000102d4415000c074855450f00c3e0310321004542c0580180900d0003940c2540714288581480001190419441a0001c145250005194a03445410650115000500f44004009130981b118900c0da800c40d0031022442001e07511044020982442214011032942004160740d2002905c0d01c18030805401031802107000f00c0a8a1031a40d03030b90f041041e801520b2050b054000d4000e201021000e000380081c0d58050042c0028030b40550705e643d210200384e03000c04409501004507403c14801c0c4030810205c03100c040c1c000e050504403100c0030314090006018110b2035410403501c80e140342c410040504100c2c200400040c04002c007910201c00e1300d80140c0b004449139a4440c510050001d0440940315440b00066068000b4500d4038603403500440c2c0d2182c504101090314406e022000918101c0080100410007040c0000143c90174100310050340c900b2168403100b00c0307540c10f1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 634828480 1250 634827230 634827233
    0x4080a230306130609240527070201091442090a0206040314010509060c19110f030d0b06040e1f080303100305151b130807120519 57
    0x1002182d40055044030074910080c940615480608842d4012425190070841600c442c2d95403414136030041a0070390040c3c0609503c41c07041c002c903000c90201310242c00b50305501180b80030054008840c0c1040b07491001003a07c1003691a014081010090081001e42c018240084101e031031401100721001030050074000c001540c5c1151400320312045c2c8041004400b070010501c00306040102c0d1100e1a400303058580c90b030f596400c2c41184009064004642ca508240001d64a0100418031074418800d9010700c50030440c0c03400c0711b00150b195215a01c6d040c41420303000d10134002c000b08450103030409502d005507035070480440c0c01c41c240e40f0040c3c4054000c850900041c040381c045065400da00840740d04800e445079050010480041c0101d52180350103000c00004c0c01009440b010051060b603008804460303c3e41c5240b40c048110340320803141a00c4188030046d100031104600c1004103030072440c00c620720385041e03140c0201340d041c407665a003d01c10404211107a4420803400381311800300700c07058501d00000c102d4036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 634829730 1250 634828480 634828547
    0x6070e03190305090415050a0b070c29030405030d0e0115060c051c121a090609040b01051012060e01170304030816140109031d06090105070206071a04080a 68
    0x2c01303c0941c8940d0f213031942c16903008035942030500201001015404c2440e034030000d02943c0da102000645030709c220010045030300b00380021385402c000000700c41d001407140800e1448031242c01c081c02c11240340c0000c100f59201c541d00b6008500030503618000003e01844400c901c900d00b80c9041c2d01110602c6061065080400d4021501120088040c142d078801e4000c1140d00b11010884c041620407140d16000121201981900342c841792014141e41005454540d01c2c1009440300d4100d40042c89410300740c00620880c109001030803103c139924185900408548080305050f2061900710014102d04c0c0e4004104400c025500d151010002401545c94541507443c0c002c0c26100341114010050040c107031290401903040d0840e425046940000c101c51509031030001c0901861981c485411035140c1003680705031405408441140b00d050316401c0c41c00046600b84100d1303400040b41070303500c15140800750451101131440030b80b182c1d104482d02540c420340000040c05076801c180304605410107a001010700c0144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 634830980 1250 634829730 634829737
    0xc08190201080a180209010b0c060c0306130e010f061d0c0901020714063001060201060b04030b060f0301150603050702010203040f03180305031b01113906070e03190305 74
    0x502050200e0180c425010b0030300210004c00f0000d4101c151180002840a1910f026240441601c02503c00b00d454180b05034849002c261078036070380b041d83c90301b90700007000050348101c0c03024084000110300035052440b0b400071140d4540c011800c0703d1020300c04424001480201550001d01a00050300304411000001d640303070541c0c002c1c003819100e240360741140c958a007410741303291014041c09100703055078014041c406840b4080d04114024403000c00864007c1c01801060b055031441254035041910355240c01071140da020303240da0340205281c01c50900585080c0506a80c40c00804a00000e0907c3d11a0007801c590005018a0859206005000004003000440030055405107402e410000486449180c1034815901c01001d5101c00a800407001d8031500c1103030303c42d101650080003081014a555100351244d1000006000320620100c0e0991040c2c1005811003d4060074600014608540c00f915142041e25000e012940d24524800585030400c0070440740260043d070000400f0440ea07014207a0300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 634832230 1250 634830980 634830991
    0x31403071403090a1712091c030c0315030303150f080d05070503090301151d040b0a2d0213090212060603070c021804120908030708090a03020603040c0819020108 71
    0x1607000021894054041042002d0035030070400180c4206400b0314810a2a40113545030f036880002d07900010320700b0101080c5103140d48880d44402c2070b0458030610880c005c042201e00c031001c0c190744060541c446143c428020001d10700c0790b1000584030319040c5401a0510b4594840e40000c0440e0f04240011480407412003c04015130a00c60346802291801d5800d50040d800c0e100d4043d03181080410804140c0420101290f90070441c480c03800000450040520401300d40142000280c007000c03800514070b6520482103601c07050b04541c0301541c4541002401500350050800198010444181d14034200c20201c1c01012103540461070030001c5080c203c4401c400402152040d80c01100156000780200a030380010396000f4200044032711820803060030a40b00b0b60703054500c000250000004503000e0001d65042c1d0301c101e40254101492980c0790b00841d4030a00365690001c140b0200000141c0707904015502680c4280d48115060382400115403800a50b8100c2c40001031a1402c1680540d80112085d500032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 634833480 1250 634832230 634832267
    0xa0c2312150d1b050402093d08011401030204080d1211041d070903030c0803040302160b03060f09070e0603090a050a0f0c052209050f160303140307 65
    0x2aa2016540708889882221403500865600051010480d0544207803410002e101e0f807a1808503107a009100480c0100d00001e80c20420080d42d03806030189004c401038904404203400038404000a03059200e104a0500e810f0104401030018400ca005a103000707a000c807000c1ca405c6081914000c91542d40d0a524040301c4203100d111280502084402c1e00002240f20071610038650762a52965080000362081e01c00980320203010020034035072481803600204032a00b590780d501d889032040e1107908465002501c11015441140c4c0458590011503620500078011180c072241c03240ba0582c2400412120016294440e100203000c00c01e000340c000c085102c450009a0305542c0340d80d12080c140b0b00e04001d415000d44584500b4420208000100c007880c484944607500c441d801c2940e0b58148080000700080d400001c40c071102007174482d021541e0180341480c1c040e0301281d03521001f5a20035804c001262812042440113100d040c8281a080b0184022030045a50024510b141c4564000c00243d2102c804100c02e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 634834730 1250 634833480 634833517
    0x5101410150c0204110a090504140c0d1b09180626031209060105120307050304030212011d0d0201200406140c030f341202150a0c23 58
    0x3540e02c40c0d400d1041c40d6502400400848036100c980c04484e40050403090f0000f07005c0d4102045500f4540110040310702c41804074001900c90881207a2a030304100d060b0107503103a449126030035034210002412680d00d883d861746041c0f02d080c40e035501c1d41c2d4090340700400b0909080030002c01c1440c03000200d58034894408011003c26074140c560f9281540b04000303031030007030362104014070110400109045040700d40440c0c4601c1c0514030415055142d000f48180a04190018003040000d400c00c150302c01c0303207807182600004e013a0b00079213100e50540e00d00d50042580c5904c145100070f01e1940910909125186c05440c02440c2d00104c0407600e9944a035008640c10440350b2040c1d021240460016503140c045101c055941b100d0149040885a4012a038000481c3c0984080d4811080b0000e100100740c1c0f0745080c4000700d100a40d1608806a0a081050003c40c03103025203015050002d806810700400c0d41810226a0f030b22080c0008084100d105010840304401c40c1085801c040f0791001c46ea00d03001c1080c0100d50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 634835980 1250 634834730 634834769
    0x40b0702070305120c060612070905280b03120915090103110a030207030f03090206070f080c010c030f061706070309060b06040b09030f07050a0e0405010e0a05101410 73
    0x41c2041c9a00081251150103000c4042070128405445600c50860031580a9640c540030004503500c40554001240c01415082c01100d03140d40089601c00c00c208509c01c508450500b08480e06016420005130556490800006601e424040300200d087c0b1080c0590812120600190801c00d5819000103500c2c0005403100c1140d000b074208031503d01078500c9460301c61071240005800b0794884407040f80055006020b505105000c3e10507004000c0d0050a0303070b400c0050315580c061452001c00c005030b0306e9080c144111002e100d000d0041d900c0c0c0d0903031a540071488034007980400e4191102500040b01e20b119a5030086070003040007602d10303880601344c42d0201301b140340e07824514003d00030305003030940020b03000030007050290001c0000c040321501a012640e140f80c1c50305000c2d413070320194003d2603809186210b0030080c00c1c3e0440d450640060140000143c41c004d1094080c1c81d046050004071030940104400545060241c4192030101200101180583c54450307440c82118101e40102034155204458452 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 634837230 1250 634835980 634835983
    0x50a1e0b030a050303091e12032a16110319121101060b09100807020d0e0315070806090c030906060907270810110d09051207060f051e040b0702 63
    0x40310980103010791740d0700d044c5041032585400c1050b103010509a000c6182e944c09410004500005201501d02c09013035845558440c5e10f6aa80c0d4081c42d000101100f41c0924010201d6008140440078500b83d101800d04524140700444c44c0c08849510a070018010982540da041c0c0400300e4955019207036400c0c00a203c182944c242c00b4600c0d404042e50701c2c0c07000c04aa058010700c001c0600c0c2d5000c0320040d41e070006615007100d001800b266038100681203074241040c49800f8201c0000c2c0828024103071840720024280000c110a0f04032a030400060303a100501501d402c1c075190003074115031200702c12451894002c903841c2c1e80720001b8142038021007949000a84480c0b240d400c414103804d180c1c00060800ca200c24042034100054080c0b215140209000301c0092010340c0704440141ca00c441d1490308091640a041c8010444201c0603511406041550380c61070315210020541c13548a0840060902c51082c0300a00f02e61004000410052a03140b0784100d4200ac404c18035070166100b00c443c049a80c4018049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 634838480 1250 634837230 634837243
    0x1704180b1005160b01030f02040b0409021e0105070503030f06010f020604030212070f210807021f0e1219180b07110109051504150206042006040314030c01050a1e0b03 73
    0x6130100b01d1481c004420003604d110703005d66490084070144441c15480b020001200d07100c5000a501074544844290000d201c1d401107071060405061090611180780c51782c5007140d0007107400d0943e8100d4001004001d43e0082281c03180180c051000345600d1402d65400b9607214000014080c03660760215400d02084400720010758034590084100850b0712400c0c0c400c8600c1515001410045401c0030000303004503200080c4525900141848800183e0f6a019018000c290700d0030641035a004031100c2108010001008140d1500d41251200c2440d405400003440300c44180003060030341c80c11050810080c41c400d0140c0e8401c0303070490b413444104686000103071107003805540816084085c0e17030008a0390644040181c01200c4982c05540b1641c41d13230789001c0740c0300c1e40b0481d8000c240140c280196a412640d43e42e0000f004180030b0813030303841c1640381c0c1c8881492281084a0354041c0e8400a001c00c0b02d03001c280a05900b24100050511494600c0c115800c44040c8501c02d5060003030780c84502d1585c1d40e0b01080603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 634839730 1250 634838480 634838483
    0x1e060315111303030807110303370501030f060c0e060405131410030204050a1b08100803040e15120c060c010f0f050f010e040c060c020d1704180b100516 67
    0x180c0030510f90700d2a000d0104801250001c0105100900c604d00b5034a01104403489003000e01e82c4030281c05610590300f00390b0b0624804003802d0302121074021031b400105100f014041c40c06412201c05048032450000251681701c400e0703c0400c0002070700030489449420584096840c03c46465903041c96460a550050600503a5000e5640c1318009001d0b1701d01201728440c094038000d48082c070155540740148800c0e01d0041d0034800d910440e07100002c2c2954803400c4104c0e04040c0b44030120541c40d584004813440c1d131708650400c10f0070030010f0b418451010b1903a02d05214410781601c203012404032988220fa140d080b580d0003640034200010700750f901c007031084d0720041c0300d4802401d0030450450445403e000410b800c40c0c0b02000756903454004611042d080034014400c55120f1449080300303007007110813620086180e504a0708030322040d05c450009030f90b82d4418680b140302c2c501615280d900d0982c548031411090202049001e20307042c1035003c80d448074441040c0301c074580d040003951801c009003034144400140d00d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 634840980 1250 634839730 634839757
    0x30412141c050c0f070b0301050415030f05010f0b090628080319091e0b09062a160302030a08131203030b0102071d04060e16091e06031511 61
    0x10031081e1150000c2c00390646890b00d404540411404035525079031001303c0e0154080090040c001041989803c0c2c0042c46220464580901c805980341d035019140c0d80d4014040703805075114110355049030602d02c56500b8500045500e14190305085011a20480004c80c19200b502d180c0031034130340d42003101d41e5042c004000103004c0720340c2e80680503244203480f144005c07848001400d0800005185021502044d100010950011002850501017541e1a440091501d8108034248400c1c40308021840940308511043c400b4604203491454000d410842d110f51808040706030541c0070705c09070b10300281c2094496400544140e48100310323041c960400403c1d5018540405007000300c0420194540c00003c59000280c00712132607507880c3c0204104840041403c10f00030000000010042400b581100c0000d0201106862036440001a000320030001030704150085a11f804814680040c2c1414130b11007023010000400c02107003103a903010a20300b180c40c034403043c17661030b88107260000e03807910211003500240e00c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 634842230 1250 634840980 634841023
    0x20301061d1f0e12030307020303010b0706060b0313021002060c160204090b131101030618021804020f0c0f01020309030316020c04050109060504050603010902220e0303010e0f0903041214 82
    0x103000305080c0d18000d40c5809079900c150038050044c0d0000550f8000c3e40c080d00a142107031308041140503a508408030a4405079228000000c030640110000e44c0074032640f249516081140d030041c000d81243c01d104040440d4031400c100980e04114406440002d82c401184009a41c0c035400054003030004c0c0d9030058031004141040c403880c1c011035032030346843d1440f509640d002e03186180015401c4807001c0c8214203100c01024500046d0b0259170703004211404120194501000320f2002040c00c90f004074800101c400c0d800100206411801c011004002074118002e503c1c6141101c0015141d00014204040760301c0c00305e4480107081d0003400101d0b15814041d108000542e9680b008402074038803031055a000303916002c0401c2c4c9038213060003410fa8481c0c02410801b010014901852100754910085500c601d075119012030035020f090004500070403050614111a06204400f41000d02002c0c012804640c000c00040150b0841240411021034200e02c100c090010a480900c3c1040117101c800364001083d030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 634843480 1250 634842230 634842289
    0x2720030709121a07030f09050c0a0801091e08160b061c021008270c1009140906150d06030c090c080117010e100902090604020301061d 59
    0x4502852280c121541c036420490381c2c4050644800711000005420300b040020118454506005000e030054903500d00010380700c40595102e03084540c0c01d502100c2642155030100c50300c0c540b01c0b4903180902604002000100c0c80d40d6502c46c03c501c8030841000103899000068014402c901c410303074144046603a10124100050b20b04681d411008544043c444c3c0190110703c000c0400c7c0b03039020400168013030194044000e2240c001d0300c0f4940c0017044c582400044030000000640c0f1303c03001010400d501c0f0001c1c20904482c2d41005041e5071034008040800460390010848403288140c0b00c4001e2400340d541400648415010900c10307428a0341c0348a13007010000b41c2450340c02042d40180d0449000e45c1c0040ba040345c84200c11026078040021017000a0510350051003204e0700d200c109100c0c052801c000040713120010068904280e50049120090359440d0041e100b0360078101d00b00e550040e41214110714540c101803025280701c52440d024181d110712041c0303c28080c0c940c82281d6901c141c540c4041c54229881 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 634844730 1250 634843480 634843541
    0x317040308032508060d030e031c030f0506090412081b07050d02010b191403160609080c04020703170402152b02040503070b0f041a2227 60
    0x80102001603410303a160741400d43d0311642c070040c01000020203210312007140d03403400c86104040d86c50165050140741451640101104a1a249040d181c1c90105641111980c20012101d0040409014010a804100c006140c03c9415542104a4100036840d5224032900278104009108000f514540000b400c80611100140a5400743c410b6070091054000b10310a108400d03200b00c2c0329417005442c03210300f40000415540781c0c0342e0002018080b13600403840480c103120011500e80c45080400c243ca0030501c00510203000d4850b54400036903040d40340c01c80c0d46c1c3d002000d64070780c9000c1f8418540200003080441d502c403141c40c0006000c801110f070301d801280c1070030b103111120800720010b583c4094488006100c0c840c0207450854000501078014189001c0c107802041e4450741c523a41c1441c108105c00700e0f811101c0900d6180b0030103800d501c6a290325070301c0760742c40c803441c0b400218211800da0403408000c103c021204280641002c54081440c515090b16030300c000e0b10b01d90502e0f02100c40d0701202c00201c0c400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 634845980 1250 634844730 634844761
    0x20c10090b16021e0a0902090f13020a09080c010f1b0213050703151208030c0d02072001050c070b0d02040302030a2a080a02010804080c0a0525080304031704030803 72
    0xc5032070621340b003190380841d02c90407a0003003460b80084081e201000520b400364040c0c6200040030f03015040384105000052090600c2e03810307402440d940420300b510784540c07080d10708000e0015034000740f041c41c4507400060710380301c1d000d4074480c10445441c80b0f800741c00c19010402e2510942c060b0202c40d0800c03821107500d01a00c001c07174003d0000303403030042c61203580e00701b540241c130480e4811100d070201d114461325404001d600041100c000c0400420003008070800ea48001c1c030001e801000515056071400038a107000c00740700444141001707008d11089444000c0410a10101d40600d80500e9407441000040006030103954006036050040d9500d5100744000009220310038420038440040300700100e41100401a454040c41c00240c0c00b04640354011350065080d507801c02c0c060f1044e40d00786070070480828039180c14007400300c4840c0c00c40c01d6001c40c040c042c030707040f582c100d4442e002112505082000a9a03203001d24800600032030b803500c0c0c002200094140454000d5034002d450f8555070719159402d43d28414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 634847230 1250 634845980 634845983
    0xc0415050303071203390203070f060b0102061e06091008010f020d0b0117070e01120608010b0f03280c030803090703050f010b090613152c0106020c10090b16 69
    0x80c1442e030f15246c42e55210b42c45099000380400010907100c0740c0d4452408000100b012001544010440140481d00c0e40b080c1c031070b01900c516004155000c0c4040020308004001d000c03500e14800700c404034021303001c040d0307056175014074146c52a480341e41d01c081e00090700020561020720070f9403034038528291324106600100464564840140000b503204401101d071030f01040142007403d00550b000c2a0071030320801001440450525008020040c0d0701c00440494070981c0c80346059030b44d108024190350610a800c900064411009003045803c0c0030442850f510300e5181e01c7c003401a0845803c4204120035a0382c1c406103030002d01942d16460600c3e81140d4072f0a160105581a1007141030404a81c81c05005003107424402402061054031101c2c14880b128600c0c42c102180d003030301e462031104070369034900200c401000780c4007104090500b07412a15000810122014408051802c010f0000c0398001501c00ea0324401501c850801e886884801c48010b880360304407526814000501c010149811032030000e41f05d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 634848480 1250 634847230 634847237
    0x6031506051c0203030f0a091a0d05130b221202060612030315010804050c040f061409010b040605090105120103050a060e0309010c020f0105091507061803020c04150503030712 77
    0xc80aa40c8000320302c1c2c026480298554070400c500c003020002c45010b07082d40e00043c1006e800f0309469030511114104c501c0d440051824003c100040549154010140c00060304940d80c910b058031034641c03284000009001000d24a9510004c240c440e03104440c6c100b001d13801c11480f440030012030b107000b9201c48007a6155031040b600107440d81d100e904040b0413a40038144c040c400030040c070302c000010745030746800405c1038403c0c0c001d40c050a2030380d8417140034540c0c04a0300d1482c001032a9090005110b00d000b4401103440c0a5841e03c001070201840e80003c0b6003d440e00380c01c2950300c0f00ca44034012034051003009810791581810100000c04c2200019000a91620480741400750b2804226081ea41340121a0303003500140e0010081c4c4c015080c107000040c10804185002840e0140920100701c00c503443d014040d01030600001c80030700b40a43c0e841080910485420901107141c9152402075a0b43c0c02d0002580c03285980f11011046c903240003500031300514010303054a07100c12140c103001c01c0e0704541208a4020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 634849730 1250 634848480 634848499
    0x603131e031e0509040c09030812010812070503090607060605030a050715031a091017060402031002070b220212011b021606110f030313050c041a0d05010603150605 72
    0x100c403070001e070030884001d0b00d680c0c05007454031050801016050440d0303000240180c0301c00102c0498094402840c080c40c1d0b5010f0304000d94500b42d04a850001d070901f010300641d10600c8400300145010040301d0745c81c40c04031101c0341c9031074450601070001c00c1154481a45482070080a50410030f02080306401c0351400030b02190003100d070020980c1524078a06c0384948891074000c0b4200c00d0310303044101507040307007980d111078280f070f40c8070030002240300c2813840c24035410b03813114041108510f0200209031b2612034580b0158140101a40d4a503a05c1d10042d12105001c44190403084412a880059100040d00100950740d110341c0041c0244c02000941d01000248280208000096000144044c803110128000451241c40d10030100d8a05006550703400d50703405404042111b0940400245010380082e01e0440500181c0f0b00d0154274012036903403610b01460600310210032481100c400385001040076148207035130034040d107402401024590002030407200030a00d0211545500c0d4412416100b094805c03416 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 634850980 1250 634849730 634849757
    0x1180309060903021005180319020a05180615070c06030603140a02010f11210c06010e070903110f041514061213051509060f07030207020a050603131e03 67
    0x206200b0500001c0c1d0005056811102d280d4401c400415164041040034090740089800103410405003c0c0f6038580720020500c0c00040d440c0c081071810052800b1140e49040070700700501034409810081403a84500386002c690740030300c500d650489035100e44c0038050a080c03a0301c031070014006010780e00080c0c0d80c0300b05003034106807410ba0001d2f03c46182038051b100d2a940445111084803429810400e8140034050103030098407600100d042c00080780c04145810351a10350301c00c1d81d6842c0640503070003e22048264010b0104040e009400281075a4111000105070341c18a4042850420341c00d05141e001031a195000c070b2110f070188015810788285058003500200b04804001d901d019420004a540c030f40c2c075010a030101c00b0001c8940183d4811015210569003c6003400384039441101d00b480290000c000300404840c4024003a030b400369a40c20114245030070341e000308620840312301809025000010118005201e00865101440d41c8600d14002c1e0040400a045030202610780c11000716048902001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 634852230 1250 634850980 634850987
    0xf031205010501020d081603020c120a0e010c241103070306060201060503030a02190c030227060d0807060e12070302100b030c090c0f040b030a05071403070203120a06080118030906 79
    0xb02e91507080e680b01b10443d207070f4010400e103901022a000080c994204008000200c061011146490648807460385940900501074400c880d010381c0107042200301544240065010448c3d10b07812428001102c24400f08503484000416400d1064540c007a408810040340f0307945038001c2c0043d202980c2c0240034241d0f441c01416900d01426011401581051040d541d40000103400c00340300c103010b0000044100ea6903004181c0b801543c203680040c0c8107130300b4514940e2484072481550018801e07a8001d200c6103160b20783c03403030500600d0300051800d41c4415600c01c58003001c01000c46418080103155035128124580607503146000c0b0038640c2c0050401c15440d01c249408180d198101e000900b10a08a664001c10310000354401c20f806568400d05200200391090640090362007000034602c0000c050604040241c0355140385821840600400c00400c4641d542c0401903031100100303070b000fa0400c6c0c0c07502c1a14002030412600264015844e14030207038007441e42e041c60100602c0c020340300c1070022520313800e003203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 634853480 1250 634852230 634852243
    0x603020c030406080c13061715281e05090a020c0a12452301020c120a15060501090b030415050f090106120b061c0f03120501050102 58
    0x145060707002800200040c41c0075180b0941e1004404801914100030030101550303801d103d0304280001500c80503140d2000c0302103030100e60171400c111050020740d86240001404484900540c40403558003503411f070100c0f50302c808001e001e010580d00040403660311000001c41012180b0910f0700c02d0350004041741c0240182d03c2260303990265140901540c8286450345601c821a404560b000c006200d6506114555100024841c217030300c205801f402c80720341c1c0c44001d0550241c80348500701000341080c100036081550070b00d5070010810801e040a001c0e45040140d08004c086080c07250400d4007440744151480b0045070310304030030b03114050b503074003130b00d148400319040b80c40e0342c002c1c2c0f8003050404409003c0d9182c4074016507030084c46004513121b130306c0c1120b5410040e02d00030740310207106402d120140301c4442004c0c0036440141c000c10b021303100c00c24100d440d100c00407034010300854068142810f0310039000c00f0320340147d400780750000018242a000340c03074010300c64a09041c620b00c004d440d0500100c1c0381c0d071020410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 634854730 1250 634853480 634853497
    0x140a0620030609070f11070b0406090608060a030308061306080c0415080d1d030118020f03011401030204020a0519080603010606080c0d0c0509040c0909140402031216020d0b070207060302 82
    0x10b4140035507a03060f09440d4001032500040500801c2c0c0442c6c40e81c0f0504100b2103020f40b5003c0807090b104d501d400d0024180d44401d0308510306001c56542007205644909904608680c4c0629103020031741c030780102003808043e1000c0c45400150038007001083d924000502d05181480569003000300480120110100321001c0c0101c455075000107000d6078005224100c881ea030320040c0a1600f010407240c500080c211681030301100ca0002905044006500d440e80b07030a55141420f030001c0c480f031605d02c2401360b090704050000a104942c045001c0740d900d881501901c03006441080440001d20f10381034040c10481d4110f407824400c0d802c0480c0402c0b058816010180956a50305c200703410103800000d840302601c48a80c008081203818442e1a0f0310f5500d0340144100d051007901c955094500300b8111505a0790681d41032003144280b1001e110050b10700044a400340500a02e085433a20a0f541c0e000414000403240654021540c0034010140440120218050403d540807203d041d65546029410b90056000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 634855980 1250 634854730 634854739
    0x50604060206180c04050f09010606020d0f030222120b100e1503010b06030a020706060803030411010f0c060525031413020a030206030103140706030608030412140a06200306 76
    0x1c14042c900c151820104503000b80c095a0141300100042070846004898801d400030304a0300f800402c05d4288511805004544054150407500d22405080e00c0c280c0c3c00341408140d400644a90503c8480325040c44411040351851034891307071150009041380580c00140c50320400000841c5081482c01440411203001c011080301325074078109406403042c00c901d02290035548400c60641295603d40c003c0d031107101030300001600c400003810040c08403401c0341c001000b242d1041060101060308440c087c8074112092a00c034050040103c000ca44400300818020940d034200410b010002c04003c2001640c040403010341942000149812029101342d05000b092046d01440030840329114040b00300246800507102c165090b50303907404160103a01c03d030f1042d9103200c0c4603142c104400e1014010302008014903d0309000c2e4504001c0d0b0541c5902c02ea1055400700359441c07001c4000c00800907054040340e40c00105650700c000407070070540060030601c214413001746035007207403ca004020b00080c0d0303004000140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 634857230 1250 634855980 634855993
    0x703210e0f0d0c1502010f0b241c06060e030c09040813050d06050a110301082a04020c011e0228020a080304030c0203060601031a0d03050c010905160506040602 70
    0x81442016880201c600380c021609484820200340881101c400038941c9422441c012040140024211000060241c8803141048081402507030b403002801c494581c15080b40034441c1c44102d0b200440d201e86501c0490103444035100d03110039121a0f0080c0100c50700ba0311102814201c800416445030001841180c0c0300c1142d101260104071814090020001829000ca8205031100e0024140e180e1003102105d05503100e40c20082c1c580080c0c0203000c9900303c4141464152350405001030f8440c18050440d482900d06603010444041145034004800080908115682c101032a85a8080c10006000c031095054410300b58151800c0d40c800c407140f2300404011402c80d00027103914800e02803680c0f440c1c03104511404058001250a9500450040384241c458100c040c9240c414903040210080c007442c14589440c17002620703011406907510070030108498030300540c0c400f4501515035000d40d51144060b036203022042c10403c500080d8080c0d11520215001c07044507601c0b03040000620850082d8801604140d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 634858480 1250 634857230 634857257
    0x31b020f070911160c0503070f03020f03241509010306090c060203040605120c0f03011814040209011511060c04050f030c0114030c1903090b07020d09060e031e070321 73
    0x180404400a1050f40d51440c2e041d60b4500080c0750a410b42c109d14411508010100704600e82000d81010842056000d00104449040103088503112461001a01100100000c900d40143e41d01401490801483d8040a50310390500b8402041b41c0041254000e4403454040744c00b86c000000d039000c86e00260348c1c00e0300d8003000c800020341100d40a0241d190f01042401610b0030f0a80350805940a081d03051613018412000e4805181a503688600e4009614084800e01016840e1850300340c4c1914013104884100c66042c501c119444500003c0089083c02440c06000041103044014000c5520480d03248030040c407048205038562151441c6a80801c01c020415004c5116050146510918074041175040c02034034044051500080740c0d00d000040d960340560030410130100e45031038006045200405009103508405060608540038090600c000038070700d2900da640c01c100d14444003450140e03810345140c004080c1680c91600780400c1303804e0020042c040e0100ca80c3c15001030803541e03081e9143c40545007036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 634859730 1250 634858480 634858507
    0x91002060c04091104080703141903230c0604050705030c0315070f090803070614010902090d06020f07020315071b0b060405060103020d0c0f0801050a0515030601031b020f070911 78
    0x41031130712040360f41404000b5001c44d00707000d02d6000310300450269040b141000d00d05d508060000c14003540000d140141c1b14082640186012000000327600c2c551a54081c0300c01c0111640102c405241842c4109010001000700105e090030444000341c2c104e5640760841801c25271102c0d01091441d600080d141e00041e01603120390304d03d005810060a02808864580c100780d800c603400030f20140c40e195100e00b070360421030078440d02c500d004215140c011130804400030000f490310300040d90084e01090b0082180303100300c48041c040700d150701d42c005c2c11280c001100d9081651407420841c2d0410100c2e0800f254040340b8241c0389031411500303501c40d01c1000c035640c4100030040105005040c0707034100760342840f0950ba03216541c0710b10710441d02c090b1542c20348031380c28002c002e0400b801600500d000b58890341080210751103c40648200c10102c91400e1307220380da0b100c012801045203c01c0302441a0b0b0001c484501e031500401e51030017000e07503c07041d900003d8441403c2001d403018081e003200941d108000010740c4040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 634860980 1250 634859730 634859741
    0x1051003030c1b08070f030302120304080703120b1305040524010608100306090605060901170709050c1621030c0e0d020102010f0c200c090105010507050c0301020f091002060c0409 79
    0x61560704441c40d84542544d403070708165800034038544c00c0303020043c170a141d0104201a0403020b05240c01d480d40c40c0c940d803428814000c40302c0040501031211050907140841d50400000c541e4090701206956640c01a400c014150035a41502c4a004002419103084402008521002c041d684070301000d07440d2030b030203d48065004100c51268680d1407004800110207020701404580920784c082000e0a20008100c0000b1042e80901c01e41d00080c00c4481a111000c141c100c111043ca46000805550307089a0440e244a0440c45d4850400e0b452910300c100018084103a0481d1001340710686400000007050302100c400341000e502003018180722810600e095001030007000d2041c800480c11071340400d1680c007901c0490340001d010a420700f0b107030b08491140d8002d48030341210203002401c07038600903404510024010302810741003100020700201808010040c0c1d1644c0c0038060002c540d261000811203031350350018800148a0350984c2c0103030101510015802c2d005c1d1240c003052a00c0c20385095000001000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 634862230 1250 634860980 634861013
    0x30c060e07080f250e011a090d030e09060a1a1e0409091709060d020901020a0c06091d0c0a03050912070804050a12121110060b070b100b092413030501051003030c 71
    0xc4101301002c0d25442703880b4809c1c403091080c0c079031031038803c04003003080b1034540014801c40c0a10303402c800402c42140c1721040c4c80d605111890b2401e5031122051540c07400c4e8080a50240354034407000800080c00540ca511802c10383d03014421805504240c0c0c00303003210a2155026880c2e0000d000d01c8000c500c60f040768000c3c00071280500440742c040e1110350380e04040846c55813103c5d021595000e4204030b550410040460740c0520038131a0480e9150291504886000e069080b808040d81e403c0003c42c2d0705003c0081c91160310866000c2030322800d082c603210a040e03101e03008060150000840009400d0031100c074041c0c920307620851000074520300c6101143c0714600b00084070658410040303440c40003d020300c1250040d101c0810103955031806c40c00c0c4800c1e082c0300940b118889947c081d100700700c0e4a8181d020344d4011642103c0c2207010171190040c000041c21032110307000794554001040e80c0034101103d5880d080380d201c0c500902c116641e43c1e40350303480d0384107512000e80460312480c0c03000009020b13008203e0503034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 634863480 1250 634862230 634862279
    0x717120f13091a0f040c0c0f02061204080c1011120c0918011509150c05010f05090d0f030c0e151b1513030c060e07080f250e01 56
    0x441c1c0d02c00110060b503e030f400101c0341c0b199120b01182c1850900100f814440a402c0d02c0c203010000c40214000c2c070b02100c0c00c0018140c1c00c0410410400c5581b42d50440c0c205036403080c40600302d42001e0801074030701d6102144071042882803900c00c403000d40b100d0282d5403800440e0f003219410306030701c030910003100c1d0300042c81d202140c41d00f00f114011507a00d41c040c0d500488101c052400b419810074071007010f45544040c200e01480309082c0b08112403540107424000003002d134602980030340b080b031821278007508000e83c0e0742e81401d0801080280320180050711804440c46a9a48034080700040410307012901441c80b0500090b041c2d41d15a0b21a0409615105007021700c402d00031b1a28240c0c2410038141400300028036403a403c00c03241b0030341202107141c246070001080c2d400d038203040c0490b80d07000e000002880c500400c040d803600b1054540c56000e00001004204c0780c0700340c0b550903000e40041500d801c50440b9088811a50b41c5a011390f4014940300001a01c0383c0802a038002d900706499482da60b240300a034403488 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 634864730 1250 634863480 634863517
    0xc150201090210110721030c11130509060f0c160c0911070c0b040503031206300f070515070215070f06140403080c09030708030c0717120f 61
    0x5888011454441d03010135695208201040342c801c82c00c4c0103030b5a004080303540c2a01c4044400ca02c0c15094010f440d90315080c0142c61107542d162400c0c0c080005112954000308011100c00d82c038403142c004500c204c0c07440096500d2682c816111030f0041e030040d0358a0041d140c0c05e000303000820643d0a200e441c081e0003100b01d203000c0d50740c1b403003071100f640c140d409180039a00700403400b1010007441588807400f800e03a424801d0305003424880800d80d40d018800b0143c003554010710100e1696222250414205a0301410b000914003030b41680b400049100303000624284602084e007a2080d01c0031034000c090b901d0040500c8100b41040850540c0c1d80c100c82400e9901030310b8212542c0d009031200c0001e1098920a42031942c1c1c0801e0360600404603100900c000c20104225010000004c0d0703c40720700ca6001c84591100c0c0c3c0c4894074200440d15184482d040208184000100d034220407a0008181e41142e1030002c01181e40c5480d00092500c1e000c441d000304641210611000150740c440d1000340c13107018001c1b56402031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 634865980 1250 634864730 634864733
    0x21c050a080a0f050c0d181e030209090c01140d06180911040c051b010e0a200307031a0a0b0405180111040f120203010f021b0f07030c15020109 63
    0x108424084112204940051100000c40c0c0102162100b045181012170902e119540c2258940c07043c0e030b00100802c007c0d1142c060740d0034203952000c3c0c0a802107540702d1500c210708048241400544d030005031300c503410307410001f000e1410026285440c5072040e551a100c0c111501d02e661440d03004944c020702403076250800416100c44492002c040c003500803102040084442c00d10040b01400e252000d0700503428020380c2240560004102c1c0d41c031f80060200e50444445460246005004051807202240140030180c0184a26443e64000d050841da84004440b070084040503582d40f03040c031004058080f1a0310b0300c122010501c002c0c9600c07180704e076004502d40c81480001340032602c080f250100c064400e80442104c3c3c031824401d2806264420304000e280c1400e014188a9001c154850210302141025000c02152406c3d0080705520913429403d40d166070020302d007415070b036010054808061054014441c1e00000c001840c0086a80203003950712440c0c2440300c800300400b4902d0030007040d99242c00c040300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 634867230 1250 634865980 634865983
    0x12903040f05030c0d0f0201050f061212031e091513030504050301090305030403110601140d050106030b071e0804020108180a0203071811043c08010213061b021c05 72
    0x4e14250414040c00c401c030400710001d8620480c103000a070446e032401003009400032900340c8098006a00f04d820005003c058443c452810320165104c0c400490301105101000a842402c150070710141d603071034409070340d0703001009039500c491026810095440c1400b103281c48152a8902e040c2c10f01030b2400a1400351101d010909460545500b207001074000000c202c00e0560200c2101d8002c6a01c01c05042c05500d0001d0100c540c0b45000300c5148103d0b0001307080c1302080802d60103c4021603022900300280c0ca0103403000750002c0440005c94a4270700686c403074882007511903444144281ea058541c4145503c4408014281c560401d01c45a4503100e132080090140c2e40402081e0024000d0707082041d10500042c0045056980840700f044010300140810301007040c04088600300651000c0c021403058289188170465019180c41ca1044d408030664045070040b0190010b11070803120748690785031240e90342d004031040c050160341c481015801c6200c00c401841c01559884104908401201d0a41000e4585d136 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 634868480 1250 634867230 634867237
    0x303260c0d18020d02060306030102041a07290a0b062109011a010c080d15060306030615060c060c11010c02301b030409060902070506012903040f0503 66
    0xc00d50800003040c0c544410610340100c80a180c680e200c000010950356001c01c00220415400922504c004000101e0f0758600354103440040125032000917403004459203440c0300d94021602540c1100c42c0b9129403d552503c1840c10f407200360b4001031481503a843c861400010b18401c05c0c890761111081104200191014030302007200e08039010148041d0422407815802c4601ea9032500310b400d40c44103a20740890fa0010010704281e50401c541c150f03a01e00e80342c1503c0082c04490300c90950044141404182e060341540800207891007000104501002c000011004400a100d058002060004484002149500214100c8425081c42940055103000c1c480c29a4180002040103030306c00c1c5003030324184803903420b030038401c10800e04440a0066681c3c1c4844440c80380c004200720f419441d022141c0d00210070401c450050010000c00c004542d1030341c004401951001c0c8094483e403240d0301c0089290001025601e420241080b080e0100708071141d4075030b406800051003500e5086811110ba408980148001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 634869730 1250 634868480 634868491
    0x40b0f0a020a08120a0b09010b0a0e1f0f022527021b010605040b0d080a021203160e012a08090414040c15020d210905030306041a0a030326 61
    0x401c0d104e464400c4100c0201d44108040c00c0c401c0c0c0040e801085009a0001100c1c8259483d01e04252000180000324640210169402c085c1401c0c0711100e54985038000d540e8202c0100c950f081e54800c1c0f401c0c080120286140c2101c811442c0c9803101c04204504070743c0c03d003505a100c2c1c031103414281900041c1040480e080507a01207400d00030070304c812454001c02c0c824403028250840382002110001000309843d80b0304200c0041c4dc1000019081c406140204241058540446002030b0760745458008400c00100c41140741000c038003880c038036010307a40c05948903028044205880e54140107400144200f1b4101142d02612202c104010302c0c3d079240c03104c1c00f440310b4001089144408034105450156080f64169001880302d20f842e2041462096002c19010020a0245041e0704c0d607100c6102c42100004542444044a52809004804001000c07010310300c500001c0b58100400d0040980b801c0b5480303a800203c07903002c4a080d1041c4006409840e8170b01e2400040c03145503600d101e0111804d41500c100366031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 634870980 1250 634869730 634869757
    0x60e0615040f02070503040b0309030403060515040c030912120e0f011d0312010311062503031803090e180d020a1211060f070e2d0105040b0f0a020a08 66
    0x30340354281040d0107118041207040740118a001c03c02e480f85034503800750340940002c0c00000800300d641410704005503800365420210404c802d0070400c4040903010440031520b40502c1c2000e20304c0840d5030080c842d41c082c480d00301c0007000c40c0c0b48400b0b401301c641d0380d00d00586040312a0790f4040d0041c0c0220402c00c1c40002d0302100000110304950540d039400d00d0b43c40343c1c0084074a0f03204100c8040c800101c2100ea9044a510244507003840039440001000d5000d04801e0b2040742c0d03e0404800440401d0504819020f8000c4c5c03400c0160b0f200000fa007003003100740000c0160220303041e140300708031540400105680c4041c040125541c6008524107080c246003052100d9801a800f203802c5400f809444102040f030440141488803581014003105926040000c000031000740b05140060401030040e0400d00704080001c05c144a80a0241403040c030a20101000c00c0c822140c40d80190344650080f801c41e01503908420506040c455001a40e00719580150028011801081480c10001d070411000c4c05e0030444642 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 634872230 1250 634870980 634871011
    0x204080d0f09080d090f0e011a0c191119050d020d020406030c0e010303020d03051b0a0c0c080d08130f1704150503060405090a0305030c0f04031505061002210304060e06 74
    0x6502c4c120460681103207e041c44050010800700180b101d0145041e000b907102740b40c54600460f80141001805a6158050f030b0b61402d00000304450030342141c5481100721407810103480100714840345294107016282e0441407c1c1000070252610000c13030100c1c00d200420109509440342c2e20b982e2007000703e41c02454811031078401841010b03010b1114001014060ae000c110500d0010403980d00340211030101c1c103190b600029054282407040a41c0e001c0f280d04856140360143d918156141d0f174200c0302c05e02000161040d4046050510400081070130150441012000b41090341c6400d0004241414045200402000001005146482c44001c00c2d01c140d100d41d80c0304e113000310034081600c03001480b10925401441000d03001075000703819a078001802c8060542c0340c2074556070301040fa1085820103080441240d03101c24107030f0f08582105204036010f48582c09200e00007101681d48290b4080403c5d1120074820000741560400009103500c18000c417400300304940c0d0202801e08009080e20204007031081c08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 634873480 1250 634872230 634872239
    0x10e0406140136020c3f0a0210061806270b0102070e0901050103030f02060402090c0a02070315020c12040b04032915010f051c02030703140c0304150204080d0f09080d09 74
    0x40d10b04d4030f0310b0701ca401c08504590000c0788100046c03603032001e000340c0a12004205640c7c124804c015180c2a00101901080742903102c0044840108489032a0785a00c0d08010010403041590f00d00e00ca6400c01c0305200510400450746200d014004903c080b41c1103118051000030314240300c00400b0702458110000040035410343c01d0007040d04c0d03060100201554822800e020041e15000300195004149a0300e680d00e86003c0c0b4000ca0a01100d0391014205840104104403101c510341d0040a6458000341100c024907031001240c07119014030305c186651210140010000b00b010324600090032144400c9242604d94658120600030405403805203110b01e00d1042c1800035600211141d000b94980e0400b81d007030401d4800004a0030440d901410138164001c07010a010501070f4101c90742c07156030012407001c1840c1c0b881c403155854008403010349900c3c803000aa159005003d01c00c9070f00b680e8120001e001101d00001007918019a00705550040010b83e600000300c0a02c1400f803550f104c00c071513440000740d0785803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 634874730 1250 634873480 634873513
    0x303090c060c0807110406051302030f0a05040201090605030405150405030d05010605180d15060b03070e0a060c0b271011180d06020f03010e0406140136020c 69
    0xd80c00c5101448151111440854507240c203035498203038081010f1803070154044c0800c01800260b07000c0e5420490003000d101402015401840c41a22481401d09040e90742950810542d442500e019000c902d18440602c0f4242c0318800543d80306000310101c6100b00c4400c10346140141c02190252aa50404185d80d044401395008448c0144954540141456200310b0350065076000424154031450b02d0356000740c1049000c010340201e000451504201e01551000c0352100c40e402103e003000044d002203803000651406012580c00e42d20180e8400e410f40e0107035a501000c10402510310500c40c00e0305400000c11104040c0a2900c0c003030303140041d05088820801c0081681c0c0075030301d10b8164580c240040c4407641a91510310341d5003001281d50b40001c019034240035009104014103400605000000030030078109510000c0e01070f6100e440d08115841c000285504991420b01441000c50580f44600031420400341300c8001001070680c4040c00805080d110104980c031103003036070001d500249800d0940c5440c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 634875980 1250 634874730 634874753
    0x806070201060f14011e030903020f0303010e160c060e0706020c04020f07030e1201020c06070f11070504020f090d0f02150c030703080a140411040606020102131a0c0a030309 76
    0x105030009200740ca040104401d580d600a002d4034016000d8041d510020b0f03840b90034030805182080e200d003070103105e0602008000c0d01c000d90080d4090700c580d66015483c0900002200d0407038403160b032048029101c2c030f40905486050348040d8001c2000121441020844a10880a0f10026440180081850070304040e090002c1030030440d11035071050006041000e0307100200d030003071035040c1303030008140c901000002c0e000103106103600c2240d8408112800c06000001d0241d00034806e42d1075407240c01c4940da40494a0701c003101000c44c0036400c4108200b10504154014018282103580640d08040c04035004c28514050000166013664042001354190b0610703000704610803108100841c40c0042c0204405e60740d11440c0402070801080c040001d60011442e404100c80418404442486041500b040c10b80c0300c00b60f1030b0451060b0f18080000804a00520884a10101044100e0700d9640313010000700300441d4981c420380c0780c51010005064622010b0021807185c510948001902d000142800a03802c00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 634877230 1250 634875980 634875991
    0x20609010c03181205040b07120305060f011d0609040f14090a020616060209040507271a0d0e0d12200304060207020409141b0d2604050d0c0806 63
    0x185072442c0c40070405402c114050040c0d81144513144003140c0c0340c1d1304603010320480c1c1c010f4004500200e03c61080141c83c511125070511590380c1172000c0d48034bc0c1d041000c80c4a006201a000c80c980708001c0c440d200000c20210809100107100c641401c030301a000c10140e640f2650307000c848540e2201c05590880c603503100a5040f00889009100081c0241c2c007050442c42110421412000302e007009600f009074032f4045035101c0302c010708140710b503051801000d041503061217078030800b11003da0034a140040502c1501d40c2100c8514000700500c985102c0020303482d50000420120741501c3d00c81038984070904000c07030000094283d0390a180d01c186094400701310760304450508548160180e4104408082e101982d40040d084080169104814400a402070a802c18000d186042d1405031404010001c91102c20480030340c80e094100010000c2080410700910390010409203078460280000303120501c08181070081d080c2503d16007a101c4c40040c100c1181410215031030510a041408400d02c10f104003034204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 634878480 1250 634877230 634877237
    0x60d060e090f120c0f0d050418050408030610110102160b10180507020a0213022d0307050901120e0a1a090a080a1205010905060411120f0a0b0907020609010c 69
    0x18080511260740b81c3e140b16420000d4604003144103100240180481044501100c045a0444d022664040c005400034131424009a5640000c110004250b018583c455507000600528541c3d07120704000c51807860400b21401c02c16070341161380c00f000c024801844589001086401081010b25120030002c6001b0030310010702c44608400c1100c001c0c221104038940c05404400b03d4540e440b04800c91801c0c920100181d03000d0030880201d86110f407194000d003010703007614110220b00c2240101d60a0243c5039030b005200c140c841040010070080c07040000c2c010145051412403100e42b0400a208140c944080d050f0000b0b0304a010040108100016007400c20300d000514a441e0740317008401a6120300320f0610203003041100103000c00015114006e45e000b400b10301c00f0304002a5856454807001400101c51003070103580343c42c142245012510094a0303041c1001e0700100c00a99a000109040200103480e43c0f440540311360040c0d4440c5d03218041d0314400d014540c0108003500e8070402e25030a56211062032000e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 634879730 1250 634878480 634878493
    0x20a0302030703080601141209060604150311010e03030705030306032a0d0201050c1e0f011e1a04090f0b0130050c09070c0b0708010e01030209090705060d060e09 71
    0xa0300882a24907203505420898402d60300d81c00180c8442020801c0c0c0100740c0000280e101c1707070f4561201d40a0082c01c10304102c414943d1064107100c01c5554141d0022601c000c882c80410004011800c2c10300601d2040c50001e06206c44e59020924540005508803440d40001c0104820303030800f00301000103c20042550641000d0404110b81008068005140194110694142075901900440320315200b800111070403003206021040b00b0440e52145407003140541c0722241d141c101d0500624080f9036008100710301c0d80700c418000b81e000300540c1003500b54031206102041401c2e0303100d10540e4107141c020101c5400e119003601d0508030760f501c1600301c000d4504404446111800800500140d50aa402009076a03e652420b01a1030030a84100300ca41c003642180410942c035a005881c012414442c1c1c00c1480d1545580c0002d0b1943c1009004261038034040000400c09840d003000f15076048500309064800300d03620340011a03c5035100b1410314105a0701c84804220b1007640c200c44541c42004003000d0f151 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 634880980 1250 634879730 634879733
    0x181e120c031b1a0705011b0c050705030303040b19241d0f01050d1a2503060501020c040f0e0d051c05060310021308030a0314090d020a290a0b090106020a 67
    0x520003403083c4584443c0c1d401042640170050254801d802e00c00d0b12141c00c220704800e404004150b03100a0008aa15000c0c2c1000021181400410b60f4001c5501070061041d580c0d03808003e20a8020b0803403056085a215000400025405070708810a40702d10501a44c43c3d40c2406e5403090341c450030750103030700c80d040030f130802c000000000d0804541556400c035032071001602e2504082c503c1ca03c1e401c0040d84840504010b01c0319001c01c01e01400741c2c0c81d480382403c5040d80702c001d0f0241c04483c1944107060258202028848044ca8075602201491840d06400215800e0000680e89010624007081d004280c00240c80c03c3c220507150280700d8540840728060190345080c50219840f40c00034614100c4054000c00c0d461200700c1211000c20140004ca411240c4a104a000c000d02610700455035040c10022040071815210303011031040103a180300e030024041240c10340d4500c0342031343c2e110450705452541c225001c43c403170070300c442c0d514052501d480011070289441c2007009002c1906a00040a56000d01c01010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 634882230 1250 634880980 634880999
    0x5070e0c0a020c011d090a090201030510060801030b0711100b0a270b06090907021f0b010219080405040e0705040c0306060903151103071e181e120c031b 67
    0x119201e02c03c3c641580c2800c0d909852183d102c682800d4280e020100310201f00e00748895074054620305000340c0e018012a00c4d1240000240035003400707204001003e1900501c08504100201034214042e40b80c820380c1c0700c0340c0908681c00c1005501811315a251521450303009490410100707405424000c8480d007850250900300824100107041c03100c0502c0c0c0386e02d02002c00350341e40070617210785603405840001c0514103c48001d45909100d00711400320b04005101e403502150b40c3c401e160740b060301030700180f0408150b25101c050300d00b6064412503002c0d031304010206980d02c0311700400d002e000b02e9000a18000d400d0204200554102c0c85031002050f180040400540f40d04c00981c0040340e40000d10a5144940200b5001c0580848203000841480000600010035800040c603105003401030350314220108a40400c4650003201c00070300911b10902142403041910003591118080040710825003019651600340c04a01254401951361043c00d030000c000340315100b150348248880302c0202d03100307640c00d021101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 634883480 1250 634882230 634882243
    0x50907050406140903151009050708150d061a0102010e060702030f0c03040509010f0302040e0f0622050703030f0801090b0a0312020309130c020c1804030c02030a0f05070e0c0a02 78
    0x110402015203507050b00f1800c01000c44420701d0000d819a07035040ca0240c00d1481c0c014040c4e40350300c071907042c802d03000031081c5051003a24060143c50342e80840c25103444501d9489080e0391003016034071101d20500000001d82c44c0c401d8418920300032a20b200581c0c5000000b9007142c007404044a040c0c0c02880c01c000d61180c2c00b100f02c42d60003001181d203d0310365007035480041c07850107a41c1096411640380b0b000428202648521101228800c4400b031140000c40154992585103241c070748074143d070210010410003200302080d2056041c5452803601c12100503140c1038036041e410b42c0140c002c241140304805107194003801d902c0c054143e0801c20310000d0700700c1010651130752041c0b0016042c0391200c03020152092090080754920302008080841645140325024000c04181150300054403d1206801050801d406458111440d40a401d103195840f42c40a4841980c1118120707418011404500c0c0081c2c1010484182c084c00350004201e010b090002c1d000c002c1c2006407841810f20001e00c0880403542e80003841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 634884730 1250 634883480 634883489
    0x120c06010b160c06020106090b0111060612010905061f0e0c0a2105040c061b031d010320031501090302090a0b01051c0e060604050903070303050910020301031406010509070504 77
    0x80d507910074000d0740310041c940b29508010140303580d840300083e000d50305401c0071041e141906010441c81c01c00d000159a5401c42c610b60316180d40024001500c40e15046001c80c5182780c504002290360180c81d91100c3c24039800300c41e01313108100d80141e1980c0103036034117070b02c640a00103022a41e00365080048806505000306000d0702c04110000f861501144c100d5181101e49004201c030501040c00c06250405c0c11140a0050701c00051a076104800303040414001045010341544400001001400450340380c0c0d004001ca56040c940c80b04001194000da64030014035440100807001d8803170402c001001440d00d4504000e07410021060700030700140e03840d900000c0d0401603c1a0005880c020040140c4072400703100450031512000800040c0e03038415940000301c004030320340d007511066583d8104002c11a001500d0740241980207100d80300000703010758401900488004111031403040000485001daa00c240c0080b20340c51201b0480703210030082000000e015240c00c68000d5040e1500c0d20005107035004078880d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 634885980 1250 634884730 634884749
    0x31e0c020a0b070513060c032c010e06040e011e050a0509060103020307021221010f08031b1204030602120a291c05010c0206092a130f0509120c0601 65
    0x20030310460148085a204408610180d4645d40d42c0e0030b80540410210321058020030420140d94503018100240c06600f013640490740c6050850b820011100d149030040b010b0341040c42000041640001d110f01d10f070081c00701c10b104486140a01c1c40159100d0380b41d6200c54003460f40c0d40070510496075003d04071031340300b80c0078a00142c40380d594140c12442d040b40c0100c00c00c10982c000507056116488400740c007008020141031441302d0303640d510003205120468440e120302500240410207506503800c043c06e9441303640d001240c4410501410030406507215900890b03140741d0000312544114003001da1180d1018141a0030000e034051404600f800701010b00700d1550f070701020141c02c42030f0307501e038003002c0108819004031519020683c98424020900d214064025108020000c3c2e8a510f000400c4540c0d00e104844c1100c00c8148200c28461149140c54843d50141306400381c040ba8186620404000c940160008591403d1140300c0d581407652064500842d540100000c0c006c42800140340d0303044a0f24000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 634887230 1250 634885980 634886003
    0x290c0c1c080703030f0f1b1805090f0705040e10030605090309010e040f0e060412141e030a06050402070b010312090317030408070f03030c0e0406060807080c0910031e0c020a 76
    0x100c000901125506040081c0b0f00b8100451f403e9449020081a50301608e40b020100c1c0c442c0040c161910702c0c0d00c00c0c940c4c01405400000d1a01c19000308503030304151103003402410540c03100000070603140221090ba58042200e03c040003409218004d60750448002c1000e14981160400020f0007280100300c0303d805140c899044140c072004030352107e481082c80909645a50810b40780500d91020800c0c022400140c1503002801449201000c50300308a01c02c0b40740c40d09000107000a800d00d41c00050140c40070640d00c910000700c030740781c50001b010300512501007140d082d03040d40b0f0228416a40071601034100903542c1010b000140d09012807a4002c5440500203842c2e40e942e180c61070040c402c5040040c40d00c480f0080e03100400d034040d0040380100d0245d441d000f000c3c00c0076005010407990107104900004010a020406203070050506982001d000005185044403c001196690040100200c0001d6561038850105002d88000b0000c0d42c4042c2c034107104ae4100300074000d40c0c400071000d01508c81002d46 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 634888480 1250 634887230 634887251
    0x30b15090a06110a26070b0609010509010803070f1b0e0403090e0105030c120a2103050702010203150d1505151e10140702040606030e1b0901290c0c1c08070303 70
    0x282083c04c0804080c0314a0746d6520100d241401c450541503900e640601c91602c00843e0510b0040312260584600000850410342641c5aa0b075405110b008156503415044003140009020055090054036110100700c4a03404d00340350041200d0f1180e4072442042e00035000500403035401107000605400200c7d81e81407441c50442080d41040031110008064000c0880d0340a0031102c4030b041e1120a8107141c4040020742d4501320103a00f42e12040341c041d15040d800b54000b10207071038003c2d00403503200d02030b1000c0c4101040d0a88003008940701510075105405001040c0142c504e0812103107020312404240f5032107003903480008545600010111001848150040440b006c90400c00b82e519403a0018002e2240e15503035138016005004a407840401c0713016041070340540781d120034001c100420b005040c00120360328180e4440c1c0080f0a00144022078200c1841d84008112540c0242040d101780002921200c08400100301109040e1000810905032142c544000305080d2010789a000d40c0500700412002d955 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 634889730 1250 634888480 634888523
    0xb130c080304080708100513060207050c15030a0b060f12060d080d200721051204120e030a0c0909110303160b010b070b0412030b15090a06110a 63
    0x15410564a41c4008500083c0703e5034001218000c032560700b01580d00d40c0c0088000407050710021581541002c034102c03810400203070035a00070403031035001d101078540e203c400a000500d030601c0d612205044510100c14003d00302e81c2d901c2030050000f0212841840c001000e8481c4038107018030b007105220040a4000038015403181200616090f074804011650f0700d18a1841900030182c41c8403171014581440c0a490b442c044030803c03901c02503001100800c0c1c844079182d2a101e00204169501c080000a010714000403001c0c85405000b0792042c40100c00a02410900400c8045001d04c0c40384030398041c1c419040464280b60320442920354912020910344d03024207200c00ea1440034503035150144400901e4921408141c407401012038030445003880c45076601c520040081c022840c029120010740c2000c00c0c00a01d6180700e5502400a90074041840500000010011400c101820102d0f00c0001031024523840c1c9100c103440502501d0034103008200480a825640d203084040041500385c0301030440201429 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 634890980 1250 634889730 634889753
    0xc080d092c181212010305010506060c1504060204090f090b1608160509060307030b0306090c0312031308031303110106120b041b0f0614090f0603041707080702031005040b13 76
    0x40358101c1d900e0400940f440b4104d8030034401914503518180c00300d8480c3c82c14204451200c0c00003c020854807280e100041d0040402410480f0440e608201c0002c10b4030090140c040d01c003c20140001743d40201d42000c82c41c442c0010030100214002c4c2045030303415134001506581243c286892039480c0ca1903407905440522a169519a01800100c20041f050380d1680220900f480160300f9907007540c44045d881030b540c014481442d0741c5038000f007000304110400c91010b1580b1412140113005004681d84420b80d4607481a140c8403245150446100141034000f54a043d003078903042c008014192508600781c1c007182c5003520003855494100e0205080c4002e060b9404101c18000001d5809aa034654001e1003a000074031503d8081054041aa464500d08070705075502c100b8064060408214a00100141c56000400c1160b008402d0000d03992071010050147c040b42d0b2081c0041e55681807070307004143c0f500d0f10b28601c0030340e45400d050400000541030b00c0c1d8250410b141c032171258415080c074640b03a801e02d0b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 634892086 1106 634890980 634891003
    0x2503050f0c071706070206010f050a14041e050907050d0c060c050304030c0305030306040f1b03020a090806040c0501030e03180105070c080d092c18 65
    0x300380d100408803a6851425194207036203540307103000480030841c00c40324660b011030200100c0c1e980401c6201d000d09181000e402c8114940030015104199074014005050100100084240c03102d4100301444041c02c02c0021a104558003d40b00528040720900410f1044040028041c201265044025070308042d032040780c81d05192042d00d01590002040b03503140f00030040080868900b80002c4080d5200d8400b075540c0c0e041c17610420080d102c068400c100010329103064071183c1c04882811009102050902607100e20802c1e1041e20000402e42c8004058003e144c01c210812105100d41029220242c80800c4071b0206a40b009660307018010015a800e044800c1201ca15800b810103001442e00c41c030305107030342c1c2503c3e901c41c1418240f8003100c000206811580522050401c10b24001c10070003000c0102c0001e100c0e818400380010030103081d000b0742584003020f44140c7c036414040d01c050318 = true := by decide +kernel

theorem cover : BRFrame.Cov 634712230 634892086 := by
  have h0 := BRFrame.cov_init 634712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 634712230 ≤ n) (h2 : n < 634892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
