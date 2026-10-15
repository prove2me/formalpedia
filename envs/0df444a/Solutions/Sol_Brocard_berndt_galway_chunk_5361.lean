-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5361
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:36:56.565264+00:00
-- url     : https://prove2.me/submissions/bfbfe0aa-c599-4bf4-bb44-4a3da5595201

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 964028776 ≤ n < 964208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 964030026 1250 964028776 964028837
    0x1e1e050f04020306130c12060e060702030c07080316030503091c030504020a05090402180c040f18180b040b06011707021515090c0f160807050c01170f0601 68
    0x440c000d220650074148001a000b26a00104141900d00b6440c0c20810018911401c851004120002024485160f1000c0031182d40101034031881e00300690002e40c2e9402c000c0f45c144c002d0180d000300080d208000411141ea2000b9502804520705c12500e01381d60030b40004018040c02d000310341010340f0348030721507505000d01460703510001018101801401801a80e2f50442e50082105c001480050f030795150000300c42c1058020502201c1d6150340c0b031a940350050354812411203401250102c4e214466101e8003d640042e03a00c100810841a0801c1c1400c3d480180f002e0046106040803c000c81e0301c0c280c00503444501818115000c0c0900804241c0301c46044402c0c0300142c02141d102260305000143c0550000341300c07103450400140c8913000481000000d04281d011000c000394900300c0407014001d40d51240c402c001e0f4202201d042e41400c81c03da07800000125904e00681318040b8584d0f00803a100401c0d01d01c10218030440d0303901e00d40514203103540a04a0b0f81804941c2c61904030454581c40204ca44000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 964031276 1250 964030026 964030051
    0x3090b0c120a120617030313060b04060f0515040501080118021c0504060507030e1023130c05031f0e120c0a0201030b030c0108070c030c020307090e0d031e1e05 70
    0xaa22011003143e00d0342e040b15203001880040d11100c0c100c004203480d00048c2e0340034401c0b08a81d03d45800340c01020713883e40240e04281094000074402e0002c0d00700000b10358096540315003104503428070030706600c40c41c016a4041510380d13005000100005218104410a030701c4014900010000d01180c2c0195010346042500e4a8500300810000311780201c03500000c0c0350070103100c80705900f88291384450b46010801c0303a041c1d039154480780044d50410f8802003088541d900e4809418400106242160b50f2002500e81303601140e00006d890400090f00000309180c02200c030191683c582c0000064254219299010b100d01017000c400d25400000400c0e0b180c03032101c02420400e41c035100140c2a281041d000c60b100780c020b94411103099800c054038680c461781c18176100342e2450b0b8600d41540c0b40c1c40c000314044c0d0144520000858000c899611404140c4441030480d11484041c1000314217552850135500b094854101d240114400c180e040020881800b05600c80078100c0d0704191021030303c0c11a2980c40400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 964032526 1250 964031276 964031297
    0x70f0b0a2705060d1803050306100837060801060812040e06090705160c170606010c080d06030f0b0610080f0114130f1a040903090b0c120a 61
    0x1d811070030902052512580403441c00040115014204403588505400303103500207a03041da10803041d4003c0403402c1c0b40c9510031040c00d4080c10000c1442d0012140b5501601a41c243e0000d07890080c0c1d0b4041c400d0003500460a90385000c22401c0341306144220584000d80c003000b447d1806074240e4022070001d0441400002242131405407554075010112002c16001c6a08001c14060f0742400031540b42e22040c107550a07140303600c492108076807520070032406d00d80441c4a10301c6c64081268101e100d90888069184100406114080d01e13a2100000c1d550180402c6d82c0c0002c11000802c2c0f10080c08a4071820100022710b01e43d80e48980f0303241c020f41d42003180c0940b040010440b6501d4107a40d10106641c080ca010682460301d4403903145400410b002d1051500c1c20660003075540d98407210801c800280e150001d120009607001564045c000d1115002c04511054980c3e03d0b01e42003a200c4c00507a40d4040c1d031070003c240c0c50f10300551490f0340035202e00001400344540703011110360510001e043c595050b40d00d1000380d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 964033776 1250 964032526 964032547
    0xa181128030515060712020307050601030f020a0504050114040b0f030f070e01080a1e17040306020a1d01052a07030302030c010513110f0109150906030f0501050d0f05070f0b 76
    0x44500400c0a0880b803103440e68080383d5184c010660380e01a80c000c2c1c0c0b40c45024080c00c0242c0c9503020300d180003406031007000000300800c600034850802d40ba201703990500c100358a50041009603402409105500000700010044524240e000381582041c080c00900b0b141500002090411030200a0007007968001c07681000141c1c60400c0150040030708070041c00014040c1d50320200c2d9200e40c100b01803003081300800b660050241312002141e00c0690300f14451350301d0b5131300d01d0503c0c087d410422108004c5240c0000360310001d1550215540d400205940301441c0200030440d00711a120400c5d03044800b286501d01184040c1000c028501c0914001d400070f43e02d6800d901480790950b0001400b9501180c1100031303140000e140700e80f49400042c2c0485982e01240b01c02001202d41800690150007018040416a11000d4114880708203444032aa0140304003000503495405545080c4109a0400e000e80d02c0d1b1740101d40442080540907200710240c0789025507513001c28405985a800c0b1003e0080300040d00100c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 964035026 1250 964033776 964033781
    0xf13060c030c0e0a0807170c041d010b03120f0c071a1218030a0f020f1608010b04020f0313020d05060f010e090f100c030605060706020403110a18112803 67
    0x40440481e5001107130f50411400ca9110100c51240e032410003205001540a070106001320036102c031020700704100030a00400000c0c0307803820031100082e2652800801a41d141008107010034000041c800d41807400c4561901480e4580c0030b213900c15440c3c0101b50021885140c416400b1012626061742c05440c1c0d8906454007030034001c080c1154159a00450311002c40003000300903078803401c849041001c3c16099000080c0c0c03c201c503108906015024421400e8000c00c5600c16910071385444000822208100c081440101d100c1d100e0901d140e800148002032020700c221488005032840a0f22035200b0807169507400d464002e007900c140c03a9402c4948014010325030b54100d51640706001e840101440c3c0200c0c949a80c0314010171203080031494945400c0c004850190300400000c00e03010b4456651030307810781031050080d0407d000450710301308015804440703490804010340559095000391860496027100303c0000300005211144c8400b4148001c00407040c2e00c040b42c80c1440703480d512408450f14442001400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 964036276 1250 964035026 964035047
    0xc090608010e0601080d03230711010e010c021c03150b030f07080403050a0c0305091504090b04140c0307090b2823070f120c030201060e0c030f13060c030c 68
    0x1101d81c0002c004202c01100086d00f41c58080c418200041c1c46204038605002910141000034029020740c401d200c031040e441190000280e8119000708400d03170100e0656420b84500c9420400141e100740c448060402c40d0310303e0280c6d150a80c1c02c0005503620480c1480100c1c4078244d200002e40d10010040001d0b2a80d01400164800718510f417400c03052800784e4010b4000d0003941070309000c11501e06000c40805014008a4118410083c0b41c2030001c000d40711450a5648140036a03240c50b403c0c403401d0728050405001c0c8801485d58481d14a0240d0340e100000309030341c0c00050003001040010500010700207c200b00404110042000d0311550f54500d00c4424880c451845c40c280410589200b0505d0180c50203100302c040b00f00002e003180e036500003400d24071009451240080c011822294020700041d03045811425000d02ca80c0007813102b1983c95083e100c000000301d581444004040001918040070617085941c4001e90b000034483c45040341e180c00040359102d0a03845e01081d5107050321031495810118010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 964037526 1250 964036276 964036301
    0x50d090801021c18051902150c07270f0606181a0a020313060c0203070b03010f05040c030f050901020d060e1902090d1209030c0602030c0a02010e0a030c09060801 71
    0x1440c0255038100c0601ca9101603440300a00740c0d9840c10010303d156501c24900c0302c95004021101c041a84440c0348071800c6d000c510480c418444115a00d00110114081d540d02c460340c0b8000c0e180040c0340c10790307210b10030754440704982c440840d00b910714841d540d1604c12140c119207040f40025080d807c050300030b004254403c40040aa410300c8604011a02184004c0d030100ea80004035030340c4030844980141c0c0703180102e1201c1648100e0518011418580c00500411100d00860484486035614180e011042c4005c1c0115a01610441030500c501d003400d802c50a603000207440e0016800940e80c080c001101e0b000d9403543c0240e500000c0c1c617141443c950240300c02800d8440311580c841c0c01c00440c2e5100700700008a915044640115250307060760b850381c0800e84080c0d0441105c0707200071080d070780041014185001c22580281c940c0e2010401c130b4400000d0702ea2007010742e4004c1ca00342c04203400544a1403107203142d03164005000c1314084001600c1021480040101820104540c0c3c00c124507a030a6411218825 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 964038776 1250 964037526 964037531
    0x1009053607050a0e06130927050a05120c0304051e0301150f060e06250b0f0a050705032a210108240f0c07140609060108070b04060302030c120103050d090801 69
    0x1b80c1815844200c034011074402620005d40a100c04410300299103092403205800814a0058000e000b004900150320790311038016a262847e01e0807900c0c003540200c402c1581c0583c401e010038807090500201c0f400121400345121192000342c4030000742502c1000b0b81c00703907000190316010015103140c980501c000e00440d00384071848066402c0807500a000300041d9104a030405031407461120103400350145504c0d00700111054901e00303408801f1280a00780c07001c11400380f03440001340090f0b200d401924011030320b143c525070807140c42a805d000c22a20080300802d00c403104001201044910400003441800681c613212240d40c5000c2c855820420041c00908160303007080003100c01020808051036001e1148550b501450301c46044841880c0200c2000510000e4110896441d1040c00200c8c42d104149682c02c0702c0403030b038a8a10701d6440b4810340c803540e06040c00c1848184045030094000d1a4841002c006050604500000c2c52020845c00c1c0e20a813042c1d0094803128a4003a84503052401902c0b88000a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 964040026 1250 964038776 964038787
    0x6070908030703050313140a03080f130201030b0f102f060105010513090c08010311040b130c05130e01050a1707140409020a030309051009053607050a0e06 68
    0x203203480744036200c4014104240040010000510700410041e210740244a12156071000c1c0f40203542d8041d8810190007090900000407200d92003c1d2180e03105014112500540c65610b44c01540500080d0000e9030f40171007100041901d41e2242d120030031207100c107507440303041c0000700041c1201c04101c2c50907224241d00080042d42550f06000442c00d0442d1001c5c6041c0c0d03a115441c6a090060b920b49402c1202c1103400e203040b0110056011b40e02c1816203014000c0b0103d203418030302c208411184040c0303555030000410402d404480503694882c4141004034149075140086210b210307280d0103c1900100d0700f2820110050242d800d00030b8800000d0b1284a0b4030f000381a0009501590310b20340d45c4509911800b00546031207950311f0320f811010007582d02a007103031112a143e1174083c1082d8154000e503070042c048488100052407040c4007103011110b010380910070a0821500e111200c5510361a2407440f5910115040023101300e69001c24407488407a41c45549131501840c00a0161300c1e15036403103205060a000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 964041276 1250 964040026 964040039
    0x21061c11010e12030328090302070e0a1506031a09090618030c06010b0703030e0d030c0318230c061c060f140d06110a0c0219060507080c030405040e010b0102060709 72
    0x48079041b0300210503405450190444404024180c90160312040e41881c8941c01003540014203403040c1c03480c100d082c0040780c0c0c0c3d41900004551101000e0444502e0a4604002407402070780500011448902c41c4c0d454298848045190000183d030303020000e074003c004102c840d4810111000100c40030b0b401942c900140f80c89100d99400040c003d0706450f142c0015203904041c02540a52007c02c20107050b1580d84440c40c0e805801000352072000750109081c0500c2e0030302c6d5000420b5500722198002d00040d100d00ca41100800000003805400715540300301034803600d030741c0d984401804003080c41818010b62940c0040d051429185594442e40030140d03e8041804510045003012a0601c81914000300e50842030800d80094011402403407010b100c0002c8100180390b0100c1000940c6000b9034011030050303008482102500524440d007800140180103003c0052100001858a81200d070b040364103085d142c400040440e026620354020a0b99036900240070703941c05000e1141d100b0101d00f05290350754500203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 964042526 1250 964041276 964041283
    0xe21030c03070f02010b0a15090510090e0402040e03070b0403120b01050a0305190509101d061801020c330402090601180e01080604031421061c11010e12 67
    0xb41150305218000041c0044180300358405049000c0003401c407212036944000304541c4644400301c0100058140c90041140c0c100907607940302c522039a94500d15110328000564407000c801400403644140c44030700d10800c030750040010700710441c000c01c40076941382014900904145030418a0169242c20140c803d03c05a07000001e03a80c03000440c2c180429a0b50310f043d8035492920a584800040b9440c080c1071190301d1100140408902c0310000f41000b04c0030106046130b0310b10124031216200b80e40200001000c0c11740014142440d4000800054100f5140c400d4042c2080c03c070501580c601d403000018a1059424080d820007140710810f00f030015410f042c0c0105030011402081d2605010960300f41070741d802030a01c030520080031100300304400ca58568400c02d403600c105a40940009400c081500e480e662400e048a40c0c050003804c440241041c8001014940d69008000c154410302e00ea000c071000d80355000300000c4c01fa10404544288519072000034001101c0d04140d20700030850090341500010002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 964043776 1250 964042526 964042531
    0x1020f060c0408070f1d06040e0f0106080c01020f0618100f0911010e0102060a0221090f0105180a02130612061401080a15181b08150c1b0c040e21030c03 67
    0x407150080d26547d21004500a0001100100e4961041c4503905d4581c400650050003603450311020b5031401541d203001280da0382001301c00d04803540c0000380864414400021411240703d0000142d0b0034052100c0c03c502c0442e403211401c202d0380b81d00c80240d00c007013001c0e01000320b641c1c480900384000c4403480500000d560784d200600280071283e00041d40c00125002403480404000d4411802d180e80c0703000102d0310744a1180c00841c105942c20030340803400c0360f04161500003100c184a0b00402c00e034185902007114020680000d0000b20303a85020100d810740c0c0c039070810307004103000e0803000c0703074194002d6684080e544050303002d110f003034105800700000103040007420050340e18201000306110a221201004440d04100c0040060601600201e80c089902960740c003101c03866000d40c0c40c003441130424003401050403034124070080400c000d021050419500703140401d8460380c0c2207030405491034011a0407201d02046201055005210245d050310704c0c01d1f020b846072008801b045040d030801400091182c0000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 964045026 1250 964043776 964043819
    0xf03230901020408030a02030d05060f0616061b020a0c0608161404050a120b06010c0f020d0501092306160203040e07120f1a180604090201020f060c0408070f 69
    0x400104000341000d4040c1c070050078450040da90303501d07082c0750060341d240c1c08500030940a50030030001440500e052a0000b844001c040c0070149446d01c2c000080280c01e900050441d04c003031351070324058400155050040e54031480307600105215040c03420005070f0700d031407640010100440c07071040182c1030b04080800010580341d820600c60203001501c0d1885640120340220740c0000301030383c0001d42a020214103004a5020b040d419109455040044030b05102d42030b80606032045001c909001414a44604022140a4400004d480c110b6940b00220700d0a02050b00300311070400c0b480d000c402c0c0d070184881600003045828800e4622903281c8065200c1c01584183c1001d4143e40000801203405217a080540c0c02c0350060030415a1840d11412000342100040781e0001c1040600316201e0741060004154241c03145041c0d00707115034540e0200809040e8a04007281107000302c10540034800c6003000907600075981c0c1100a40c50700e00b0706800c3d51500ca007070762000b070b041d049814041100b0288207908512070100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 964046276 1250 964045026 964045091
    0xe0d0507020114340201050a1209060e060a0f061406030c16081902240a0209090f04030206070c03050d020912030c0709060b12150409050d030501060f03 67
    0x189000580748520f0314003c0c22800c0c4000a034001c18400c031a074800002850b0040758101d2002c0e01e0f0302c0c1107101c011214000340072440800c44000c03181d00800d07504070350b403007001130100d444002591a60140d076802c001e6050264050010f02480060a0081c4030b45010145420868103103002094128807055075100c0e4002c4400002088007114402e00b00d942c0f002603421442000035192501c880b69920420b61101c24154031182425120b2000c40c045601c1929083c0c0421003440400002078002c801601d0075200d540c2c00c110200041d1640580030b0700c01c02036210852200d240c41c0c18040c1c11303c04014034a000308289540301030300094002041d2890b82c07180c5080140ca9400203000310319105c0044811014038480440d1020500c0307400201c5070155000365400380403c0d50399040c80c07040c6004407144420404401f0780000c41d8400310150344421014001c04c0400c55641944681741010320341103041000948a0780140021a01304034070400c0991a89810810300350f503407590080032108100401d21070300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 964047526 1250 964046276 964046287
    0x31b0607060b10020d03051e0718081e0f0f0615010918051f12020405090709060b0a09050f010507110d0c14010905040e0715030f150503010f0e0d05 65
    0x401d5072025000d9200a44456260301071800084d55426410820000003030405000400e104210007600c0c002100c0c00700c881c50191240c040558514034004010b03000000c080030005100c8204000c540c0400401c0c2c4198500011000003160400c500e51806001d44da0000c0301c034805911000a000d540900342c480303600d02c003800c01e800480d0740c003c00d81e0018100074803955004031081c400340d004030f0244081c48611040c00e05201040100746295100304c400c0100c44800c214090b0030b082d0805548a65007000f512110740e1202e8000003101d9141d049a040b066010503c0c40a1542080ea0034014140c02c440c40070304104000d00003091342c03103802d01c0105694101140ca2050340c0301c09022010b52a8850792400d050b5450701d440e01c0250180895150001c1c3c01c8a00000c3c403420079210710304d01d04000e08007429805007849003041ca0a0141c46c007040415030b4a000040012080f4400c070f01c0728160321791044490a1034082014251200706400b0301401c0c0c40c16440400c070010014202a10482c181045910380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 964048776 1250 964047526 964047533
    0x801061a0c10061d060a0510030e03040e0403020f061e062e023a0806010c08040603140a051e060102010b0603040b0702250b031b0a020c010905031b0607 67
    0x4441c004010342c59042200c0803076091021008080240c000110790011651020700300014101540700e2140c102c1c8185450141e003903c40d400a4202400c014100e80c5006d0303581001510203802100c00fa00160480c10710b245140c04140045908950702810b00e09051203005910a005140a0706652007000c408842c50003460818010452000c1c50940d05248482d032004080d4031224840a00038010824480d108a10001002d09089440c1090446401c05081c4075003070341c1003440500b115040c05882d44070310001940f00d030028030181c4441c0d503002c21103003100140c1820711540036105203419418403080003d0040405014801c2821450280c21144c8680c4c0060f4010f082500c80d094014900108020600c00301c0d0b501107000320b00300e608070b9000420584070f410303207028021130154001c4031f99103041027000e000101071908a148004065011802c840300c041a81c0e01441c082c0b401368000d040100c0b020343e08508140000e00058001e070a85249030102112803448051805118070808a00007052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 964050026 1250 964048776 964048783
    0x3160f09091403070f0204380418150c1d0d020f04061d0f220218070f020705100207090914060c0d1b080c031803030a06050a0801061a0c 60
    0xa0040c10b00c00e03290350f2143d604105440340b4103001c5c140d0045091510710a05245060241041400c040081082e1340e84c00c4040c0000004072441d84a40c0140ca0380200030a81d209003800e021007911400c00c5103500c0998404000c2900c4107000801d0500a5a0404032080090340910000340c1808903545008030fa024030024201505001e501d42d007103403600002140140d188040111403880c2d00c400100140e03200e90305040e200e1022140c00100300c0c0d402c0101e4a001028040071032000740300070034114070414560600c030355640c011601e0310002071a007070134080e940b40c040c000e42000d86019519404085924000a0364030010391043d400e03a00e5480c041d031024814010707083d8401d18440c000782c03045030616426811180d08184c1c40307464030342e140203210a42014000c005190708071064484402603990300d44d00020341d0700000c14030084c100c800d14400000503014002103104034444075000602c00d0800082c07002210041d0814000d5038508841445810403040300880040f1168400c682d4840f06150b50508 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 964051276 1250 964050026 964050053
    0x1c0303090501060e10030b0603060714160524063001060302030a0602031e01030b01030b0726011406071104020c1507030209091509070806011106011403160f0909 71
    0x45a00074002032146601101e0005421039009840e5464140c603140b0406440300c8060b510304001c9141000d00410000300a00a400c0700e085a48440d0390683c4240c941030300f0f004c08fc5590500b500090502a001c84210f80c1555810260a0341c03280e1070000141c1c145005c0b580e00143e62599034402d10003100001c0b100350000740c0510b601800352001242d1a01c0c0c000083c1d002038030041c0b41c00b800200b060414041d800c400c0c50403a9088100c03520281d01c0c603180d1090100000e080300040016120301d46c041e034080040ca207070103203540041c0b000080d0300d012020480c421100850a100354410895000805da54a4056400c201c08440c01642c406150824501d041c1c19554401d003442c0700c0034104030010750076078003404204c001910418000c4c0d65083c084140c1e407030080c01e86580000c03034901140510b48210a40d80e48030906051005003155014039107458032409901208140741205909411400c05104000c22501031000c0380800324141140103140e10001e00404912603507d01003041030040354a483c58 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 964052526 1250 964051276 964051289
    0x20f0a0f080604060507050f16020a0504021204060c020c06040e090c1206011806030f060506011b0c15020609070330030905010c02060c04051201091e030e1c030309050106 75
    0xc0003a03881020301d0311030070103c40565584d0314040c005902c2600500c21280408500070504c0d140000a14500c1e00050345000306036008003689802290300d40340e13480100b4140624280300185850549442400e4607441c1c003510045402402d5003a08a49608040e50259483d0140c00a0f240d84c4a41d04103143c04011704049074000d0101e16803910080c80410b01c3d60507943c084207a44882846008101d007520302610000308803020140c80c06000c02c0b596441550043c00500d003160110f4032000e10503c106109003c02c0d1034407001e650080148050000c8001d504802c540094009480d103482c009407140c0c454480549822010701e40038074045282c1000f42e40e456595849040c55a0038614010010304018000300c0d40c0798a08018504911300000e0028410b0026002d000c1c9030504200512041e1201c1c04003505089d903e849030400080ca81d050340402200c070341804000703414040c0c1002000700d0710465905024210701802c140001540c8148800c1103905410301240400403450818010322050b4000c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 964053776 1250 964052526 964052549
    0x1051803152e06050711240c150c04050d080909010603060e07030501030519050c0a060507031e360308040501030e03190c1712060907020613020f0a 65
    0x4480541034921402d141400000d0414920348004501c07050300e0203001e00740115406010764000560421400c40424001418100640c10948640c00303407881c0050981030000400301c3c034500b14450411210f078240d8101c031140c9443c1c2c101140d0031452440796015003400356802d11403000510040354200c07015104042d10601103076030768070001002802c21340140c82d40740065070f002c54002886030050310b05882d000700180041c44546060041903d800310310841d114011084010030380d50312001c0e100010221034403165502c1c80245402483c40c010800ca0550708211480d81081c6240d010314103188800241c8040d1005552041034070154811035400c2100e039600d2280003104200d480e801402c00c03507101b83c0b003d0180188100c07100d40c40b8001c0302d8031038190f98044d016604115100e0800d4000c201c0c01001c0401d115103030f02221481c0c1d82d0001d5000c1d011007a20400344855420000d04a5034441a24800342c5618180040000031031074190034042e1141008694644681e80c4c3c4001c040024000400030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 964055026 1250 964053776 964053781
    0x230601051c0c080a0c0f0305090c060d0c0906050c0a03030b01050903061003151a060d0e030406050c0c0d03020316020609040e1c020105130b100e040807120e0105180315 74
    0x2200c00b82104007000b40c0000c000a0108180780b000c0d010300c0700c3c074601d16214a10b1501030698114024800242144290310543c0100c5441c3d840e07000003001c030f059100d440803400e604011405419054107a206000f008000c02862403580ba02080c01030a15600d450081800e44030f100040783c0714083d40c05001e605000780d90070701c0074251000964a0449109a440c40300d1041060b08200407250344080013014201420301120320340c50a84000c00310742d81d81342c50029200c01000840e5140d60030613040900441d100064032164440b0802060301b10380c20492300b4180750703001c66500a4480c01400100b00424035001101c3d411076031400152010031001410400a113003103030800d103607a14003d00310762246014010070452130f540f06028040c416000c07451000c080040b00d554800b8041c40013072018401004410380800d0244142808901841c0110340c03075500c40d150740c200b10182c4e030300500c4100140b2081c08183c03100d59030000107443e050005c0c8074000c0f2100342051702003805d244d003819a41140f84002c0d000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 964056276 1250 964055026 964055077
    0x60708070e180907091e0e0f0601260a030e040c111911030304050a060f0e1c120801050f10020f01230f070212070201031b200123060105 60
    0xc035288583c00380340031139903955903a10307006084810154403241c448a94002c1440710791825002110300000c86800c59a050100002080c1446030a80201000350a12a80c0f1004110490b5014021841d1400901010704141c1e90142921030b031008d00c540200e496410b00200301c0d000340341580e03840300c0e00420b86039018690361061515100c50381040310706004c0002e503102c03242000002e860990304083c1203010540d04000c070980d0015a411403034801c21495089a031803540302e4020300c404084040c00010b0100d10381d81742c07180e05042c1ca040d20204208100c40100704564418009a004541c06e580e0000366500c1003204a04162514004240940c00d0003004d04484003104034103080b071810309160304a15200d1030360743c1c0d400d0760081d20400016800310a0100e01b22515a0090103000d00c14180010901d0801880c904480c62a03a04000411200c2c1c01031a10800c225030b130807040801800080003c01c201c03485501225540c4840c12001c501e05000203480c90740140c2c01c84415850100505000d00d10350507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 964057526 1250 964056276 964056319
    0x60904051909061b02120d020913020a030606110d230c030301081b0a15120e1f0e0f15280903090f030f2d15140702060708070e 56
    0x8100a0100000708071380c02c9100e2003c1000c3c80889082d0607054a00100e0500d124081e420102190754400f6001848104450b11071004060480d01034401007102850100003402101c1164081203040e00310105040480b0703400b142d00c142a12019441c8081e2980d24a507040140c01b40d0041c0ca01c19120002c004554043d0009450b00c548400302031150407898040140049251944590020843d4845115403d40c2c000e018120030100b0000d00090341c3d00414040300d103010070390a1707a01000d0680c4501c1c107071003009a000c0e820f0b100f4010402000c28a00c0c1c42c1c19182e803170000511168021002c02e002c24036007161074050419400803120700209180180448078018001040100c021544101c1c00148801d000e40c004000c6035001400c0503040c13100da481d686032000d80a04c0000c071145100540303040d9000c0105050440b035024841e0b0920b1181d030212888111515100d0007140742d45641c0070440015400100554800071502d0114429266698150381451034240e201d5032108042c5d50143c140034016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 964058776 1250 964057526 964057541
    0x3110307031d0301091518080f0d060504050702030406032307080f150a091a0306010b0405190b0702060a020703020d080712030e07050607020f0a03051e0c06090405190906 75
    0x205091901000150105403c1701c0c0007040051202011030250560004298400c0404034a40c4c01c1400184089a42d142808c0d40b00d80c16002088401103100030000d207151040c0d4010305020f41382000241048500651342c1e00940c480e02c2e0816448440c0c0343e40c2100790186124880c0124000c11903681003081300078008200c2206c00d0406600c1c03010004041c0a08482d0015031010090100f4215a080c8a01c0710043c02c0041c2c0c00400401103401e44a0f003545040101c6130090048845c01a1514141400c000c82001060301003443e981c40302105016961f6400112000320354110b5400340c0d07440c4400c000781d0811259034406944081140142805d01803200010003c440c4640740200d009160078905a0445c0c010401c0c120407076010751814011803c3c190000c1180ea80020b004030414903088002501c40c44150304125580d1308105040c144500c4c40351000845000080040c1c14030712407600102c3c1c514010304600e01c0c17040361560f001c00c000c0860742c07813031141c14240e00c0018850088241040ca01600c8003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 964060026 1250 964058776 964058807
    0x70302010506030f0d09122321030105030d18030609080901030f051005040c09090f0204080105072a020105071e030906020a0c0311031207030e040c080f0703090311030703 75
    0x2c511480e0304240d0082280e450640c00b46e1103000c0c805061005541080510380000c90b0394401c0200140700c0c10301001c0000c1c0c80c40c1e80c480000d08042261103003902c0b02c000703040d00c000000707903003800184619600032a0f103690131790640c07030070080041a0000704100b00031a030780040d052a24040051040c0000c3c11300500b8141c1c000c2e00e0902c1003184000c004411220f0442d4801011080040107100900c1c1039005012108030300c1c80d210404c140c07506030003011295120300c03608100c1d41c0080d00700305811080c028540c0c01142c80c1062440d061400d088a501c01e49815002c010108c0300d00b100608580c00b0b0000d440203190400b5448680011001750200c184038280000d40105030440c0c2c000480700d100241d891610795108a60580e01c0e8515618860b003032041000c202d525011740100480718604c44405801c00350b0103680c8194000000c2002d22040343e0241c03400e0000c0215410400c104800c000c00742541129540c0f0f4000780606e014141101d190087e0701c3d0b0000c1c3e42c000010f009060540c040d800707000031042c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 964061276 1250 964060026 964060033
    0xa0b0c040311100e040906150608010f0801020901021002160c12021e030a080d140f0f22020108040309052205090115030f03111f050601020d122007030201050603 71
    0x1444800c01c1a16006038240c2c030001349100d04040c046040c030340c121002d0b45100700804204108021250500c1c2074254118070f002a102e400100007a91440d071004e03008250340b0000714504820100001c2d21881c1004041d08203540016640c40181d80d400d411513010f40d045099203010b66200c007d1000c0c141e080749030aa10030084401b0f0158110401c9281a8a40e1401001068850919500c1b80090740000c90800c0f841507035007800882c003d50328241944030300f2005180800c640b0f0402404074900a025100c038605588041d6030340b1176074004a0440e001283c090038841d0386035940e841c0c102c0c0c030040e10b03800664125040c0e014410302101c09038500c02071904085000d20096440b29076039800c958103094600c4404503005410004107800006501c103940c083c0c03a20071000f4260a000502d0544101000300c40610001080944c1c548184261500040709101404182c0d00c1d0410080c0060944416150b9990381e422042d0410507088212030700f0f0b0014148101c1d281c5800c1d007000790003450103c510038083d01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 964062526 1250 964061276 964061303
    0x8030d020406020f0c2119050c1e0f040f18080a020118020a030b06060c0102210106050c0616030e07120b0618073005101a04170a0b0c0403 61
    0xe400301d0500903901c409017070029402c0e80c070b0001060808051290400c1b50007103103100003141c5d90070010104c0043c0920010300030011317250144006200700ca040c4a10280b043e00041c60b055a999400b440301100841c4e01003a50480c200c0300364014685404c0d0500c915018141d6542000304000c080c00312444150003c201d07004c90180c20f11065400d40350020352026115405000051354101f1345504001d0180000b82041c0c0001c2101c0c0c226030049071032040b00d642d030007056005a40c0f00301c0d02501410b0035103400760a02040300340c050b0343d0b1200a050050052000c0d4582a80c06119078003522031440c040045444050380c8441001805040341d0094600f80c910b1000580c3e5404c1c6999008052043c0b450303000c507644d8918200f190b80700c004a01c202c401304004005c5002482c01c542146800d009400d50000305828001ca5000080c03440d1b520824040700b541c90362040d208a1002981e088404114108030701094803140c00e402c150189000078080d0318050b040c1701c0d070380b103102c0054400c3c1c1c1e05c00c850200580 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 964063776 1250 964062526 964062553
    0xa1508090d05090f0415050d1b05060a0503070f2601080c040203060310020a032d0515030a020f130606170903072a08010f0e15130b070908030d02040602 67
    0x288501040550007851350b00d5985040d0601d81d03c1b190420100c1444180c42940b07800c0007440e078001400060324510b050300d05e40e0810165603100100181000c4403602c0c0360481d1180017030458000100b2040034426045c1c0b61555050007510316030f040210010700c901801c0c56a00303440601c40005c1c05080c0c0d55210700750400100e414144222406500c0040040c03001100c00e00e11300740a98002210203040540300d410107280c2c902c2c201d5003031134006c140c8001b15146451281c24001102c0c40180340001c0c02c805041850742a8802080d10740000741c05403400a1030f07941400200c0d180860310300421088516221001940a50060061000c0d010050b500c030416114800d00070342d01e0080f0200540603624041c030310701804801d020090b1442c1e03203c401e00806156200c0500742111254035002c0d847d151a0080200400c50611502c2ca048180a030b0985490401910b55a21340804440003002c42d0049008200e403280030705484401481c40c80212a503c2402c0313010f03400070303410620030000940304122882104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 964065026 1250 964063776 964063787
    0x1706030109110d0305120a0b0310152117091e010519031b0905100305090a1217090a110d030e061e0d0501051503090601060503060a1508090d 62
    0x1d0a0300030380c1d98102e5032104000c210841a0224084092002c10001d441c2081020f149a40c070440e5040d000280d00c9510340181030130500c000ba000d1070090303e4108880c101c2200d480c0369001351410700310141030005042c0059240882030328000740840e42800880007001c2e00f660014242c02205580c091241e00c00c900340090400c0c082e00005020a50a1110900c44181e400d41594101042e10b0049400b03050b0684944240002e1a4140001504440240445c0c24900034280c0000d00c98502000145401c41c0a2900c5030b60000f0b000340ba10242c1c00c1c5000d1610f118a1446848140000052055050131070341c8954580c2400400c58140e840c11010785000c0c503080d80510203542d01601c45a8000c1034102c104100c60340180103030040b1244c0a180304000009550241141441e400c2000559505101c200003400301904950b01103042d0070410407014401c041f031100e045800d6410102d4503901c401001a0820601c1c2d0410207110b43d0310710204180a070700201c0075000707800b900103580b2030513080f0320210364 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 964066276 1250 964065026 964065041
    0x2030115080f04020108040614070c06150b0d020702010903080c0f060c09010e0d0201090f0303030b030106050a0f030f0309170c0f010e0d020609040e03030723071104180204020a17060301 82
    0x102000802c0000e40036501540305d80380e01c248210000680041000600415100213032019400180c0d180e00e540100050740c860b203401241a03803a90468a4504018034100384a01510020b109030081044411039010789040405140d06c52802602c4000040d0fa0507034880c00302641c0d1002c0d00c2500f01040589412208035400300070180d60701001c164030402401040c0c6000c902c228104924040c002580d45031800440003d1340c0309a8010450031121000c05d803e440645d0041e074418010300301d04000340b103c2c0301481d10480f64442e1020340d60802d2400c0035918110a03500000a504044c034880301c0012300481c0c81c90860004036200412603406100449205c044109420317045079075941d200000d441c0190142c29803540040021681440039040c15055410940b0310801103000790740268202c0c4490385203540352001d8500598200303946130311a00042d20030011214016039403880000e8806501c41c9a50f102260098419542d452800c0b800a00008101e843c1c60079011407070000c0741061074107020380b04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 964067526 1250 964066276 964066291
    0x11214073204030807051c02160e100335071a010305030f07110325060206040b13020d0501110306130b0d081b120409060e16210f0203011508 62
    0x1e0405080d541d4604081d1712246041d200c07442544d10020740c000d2840036001203400540e018000c5140001103544422400d500a11124400a4100003814003010300e654100e0781c01154003403904040e10980d8031404419074815040c0082007083c44d0700f04507240000c104030382c810b07200c1121403220208100300048082c04020515002000b40076076000c0c2c601c014200050180000c002c44817041d000081c9822002d0b51904560b03100c0c00049200b42800310325000040c5034a0001e030003245041e0f55040300c5948000e040c40952000c112001081d9254113001c003241e140e02000030414030190760f15030f00080d0401c0b9080ca100b02540031000d40011403a0140f224500307000307400c1c441400c03c6d960742c0e84200c5c2c00000303400c9601903080c80b034030312412410400001d41000d6407401d5682d50342401d845409443d403503003240503001c0b407110a105110400400d201003408079881d1101d02c010300c2c00d4101341840d12781c4110381c04103820000b1541c0b0522072640214101da07941c0800510a0307042010a803900c80e82100c000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 964068776 1250 964067526 964067627
    0x702150306040209060d0c0806030a0803040605070504030605150907050f30010b03040203060a0c0c14031b1b01030902011b020a03060606020a050114130201121407 72
    0x581648120001a60308400010005414020b204d000701d40c0c990480158640e0f05511903140d80d034a0340d0850080e50f0461020760242070341c0d847e0380d1070703a64443c807000c4d2000345095a10400240003a02c42d2040d01c0107107900a8040c0010704184044c650110b22406405200d80b1f50240031806080c014011944140d1400751440e00b4904480c0160320808203048400b4160f82640b002440c2e60140c2001e0180a0018560107584a0074140181440d0030401401d00c89000d02e0f1100401e41943c005020190b19076101d0100c6038103029030702c405800d40c0501715103240419400c00c46040c88040100e2260ba880d88407840010204515200450649000c008040d006c070b01808032500321000b451056042c1540054000030307030a50340b555010122200c0368030200041c0c20071400baa0801c2030a009808825680169010560901c080341e00d030507100104000b03041c0500d803a4800802380440c2c10441d00c8004c485200442440c00305005401d814680b404050000203401c1d03140e00f900105072850000001e8002c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 964070026 1250 964068776 964068799
    0x120102271e0a08031216030209090604020315040c0c03142d09060d090b060907020c01050d06030b07050403050706050408030d11160c1d0609041e0c08030406140702 72
    0x25241d0066618140b500720003065004560080100020a00d010602c1c1c0003107401d20340005080064426544140105801040380c1c5003a680c0e400119504184111801a034907110803682c0454a0001649103822604004003030b6005074101948900c61402074aa0f01c512150340b4100c0c003e50b00c1640c40c60b10441c500b06042810b860b803105820614030700d640d042145004420740004105420038100d0303144840e1200c2c03406003000f139503605040d0130550550380e803040c600f40100003a4481d0b400040c001e04100001c22a80d1104c070a98000900442c0c00c0b000080309030401d040b004000c0c3d0301c280820741c2c0b40e01c1003010018440c1d1044c0101c038100c0d000e200141d41818000c1190078040c0840110020324410140448980d02012546030300d0b01c42d01c1920039540807842c0c50785004a59204684640d1000000b03000c208080d140c0c00d005c15481a1302902c1e081d090400b941c94042080b46c0421701801426030480042030222002000380f09441040c0c4845281c0e003610014280c3c980304032480207400441c04c0c3e10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 964071276 1250 964070026 964070059
    0x1020c0c011b0605060105130305030901200a0206030718090b040b09070806090703020c010f0c030b12060a090c081b190b0720042301060f091802040512010227 70
    0x44c54010703805241162400c3d8141d14072020318016074205490941002035009442c0d0303000103036181c1e80ca90741c0c1074159441e04001103040d154001844086c2c024000000040c000620909882c2e21410741c44039812410390310740040f40010a004c0d03044074051032070040040f1003458a44800c5200301703002e80c0d407000160703078441c05e0007000d601c013030178080505800340444641c400081c040c00d481c1400401c0c3c00a4440f0b05d5a9004003581c6a15110900991000c0808a085000450015800240c1040103d1302500342e25002d2030f50540c9500104e01401045928100000446058100103108860318941404003400301c034600302e40307445440381c00041040040000740510300004000c103001a1b0f6008903c2b0600003050a481c00700b6401c0d6405840760205000d16407460440038003400c0d0f14a0080100390468101901703003038182c010486846480102c0c40c40303000d480c1c1c0454001d040080e0a50980740705429845010b504042106610071b17191568030790b080c194505415103070b040000e01a41c80451600b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 964072526 1250 964071276 964071281
    0x106120209070c11060c010e0c0613260102160606050301052502070f181a010507081c091505070c05030901030c09150503010611120706181401020c0c011b06 69
    0x303011228050ba01d0102d03181c0d966040003606c3e401c0022400807403507032180c51820f82801130389034805214807010701c8400d42c5819860840000e6400c0605020f0b00030a4080d18000c00c96015411842d50358000143c942d0403003040c04020140521556051004580350301c02c160036544122690820803841c030304c095070361021000403280711003441e0054481c1d0940b1078504c60715120803604000ca01c1d0b03062941482e882d00d42407084100d070150a03034101c01110346500c00281540701d607803000740c1140750104a10b24020184500d00b400c071402c0c01010410041d0310726141c103c1801e40e40d0b4041d02c035894280081d640038043d200070000b0640c0480034510746514040150002c00c0060071a00130440c800f00049504000350780001141c0005e5280c40d903e079894088020304844440d00b080516801144d00b030114040c1020548a1860b40640c0c0880e4503800060102c0ea000104480641110900303252010303c0315066009110040401d400c2e5040034480b04015240e10042015038251050000c0c0c146c1d012542c2c40d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 964073776 1250 964072526 964072547
    0x303060105160221151302010e210a17030412120207061a1014040909440a05030c1612031a121c050408120705010612020907 55
    0x1a8205901051a4000c00d152100740c3d44403000e03403030004c040c0303081c414000c0010000b00250550121020f01c0c0c80c03640140170600b4400300070b040c04080100d04010390740301445103654030740b14143c2841e00712101410542d80c10700c482c000c4d102e50809100c5007840100300403c482c404c542105143c40840a07591003251100c0d003066030120785990a105031800244d450107000003040c80d80ca03280d0362030b0a000341045041605256840300b4031000c140c0c802210035000040c2c07011181000303000112048030b410500c0c01c4480012940e11244407035141611264014100040d407451070006640040b039880d1b840341c41504c0f58042081c08560103000041c05041d120006003070f045049034600441c0300c1c1a981764425510f81d0040b40000c240c481005d1511000e0120311416502d00403503403401c0001000402c00c5c0c60302c02c0000c40c10341203551480b4004c0340078020402c2b0760080c1001b130102c501d50080b280c06000c0341c1d003215104849550130f05a000440c0f609a802c020320486c0c0050040c40b00e512070b140150742c480c114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 964075026 1250 964073776 964073797
    0x9060102010608070810050a0501210204020d0c0f02011b050412021206041406062b020a050a0f090e0c0f100e0a03080703120c0e011b05160618080303060105 69
    0x81e0b01000c15032103018055200149410030042c8500f1403050f50305410b03648000c000641240c5060010030040186041040e04030018000c200d5120b5068004500030340305503000d160005060041d400301c4140e005035000391442c12b5034002c10061444c0b089081402110b40c3c01880000c1041c0020700103040c2d40f520107032507580f0040c124070a0050009682d030030200c0442e8161072855000b005110b1101c4180a0b15600c22000c40b44412585807070b0594030490070401c0c0f800e50403004c8038610401103444080415026120050a10700029611a6030a60b440705038021b0a03401824862030900710b1741c0c000360030420440001c2c070004c424403001061014820081c500034081080c000d2600916807161100d05c0040c5004c0c03d141940c81d19941000390400c8900c494030f880c040c0c90202c0f070000d80b591206040d10f107600c092070301041c21070692202280101040b90003070614022350081c41c00c150b0304071b032070741f4102c8520b500c031070040f429400111060300c0d80d60b104003d0b468000f0400610036612810003040070028 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 964076276 1250 964075026 964075031
    0x20d050f1b0106230d030806031f05090f0105010302131e020a0513051e04021602031002030610110a0b0a180302060a06050406050d0215162d0308060906010201 70
    0xc100c903040160725408010909030755100c0c01801290012203210903201c2c190440001003240360804645410b80d010005000c000804000ca812690709000304040a01380520f01a64204402d4000004180580f2005c415100711561665040710600a02d412207030020b04c00d8441e555041c2a0320090301007400401c1c051526010010082c51581c4003801414000380c0c0e4241d2a090803c1010851001c2d42d0031180c41414002d11a60500d4072684400000706015900540c403010492910501d0100c6007000950500030340b446090100110790142d40314041c103c0c0c071040080d04e00e070702c19960407500d0b410390121340c0c001a1916020821030070490b03800231000140096841940b0207150004d20500d882200141c011320180858528140281005482c003294100002440e120009a84990990009010700d0140103040040507144060f0345140c1c03a481101441d10116140100c03182101505c0c04132903020b0704643c4240c0d840c20300100b1803016410749405015498800400c14044c0009081c0750443d034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 964077526 1250 964076276 964076287
    0x1f180203070c0b0c13060302090f010e04020d0204170c010c0305030f15150a03050a021606111605030c070b090904141608010b092401080705191e03050106020d050f 72
    0x526400c1d9a510a0000725001030316159121703440d08144d202580700208050041c800e044007a60b98003829070150000b4284018580308403004174000c0d004100583c41c4881c404a070000b50100c1400032502e0880d9000e05880401d000349005580c800021031000d00010700c00d00025044800a076a0780c1d4000030001c06002e03142c414400026640c0204a0200c174459901050b00181c0c41e4150007200d810020710482981810500241070504a550040207442c550f12189141525100241110311302d00014442e01d0888c4401d06040c0d42c1c80e07200240090a51041c00310003e0034404020656150f40401040680340f030b181c1d525000c0740104c6000c442c51a5015100b090580000780303141100c0282113803000800d5840c00b000400080a00081804910a00b0007000195000d07030400b400042c80700900300f05c4815181c01c601107a41d40602260b00580d41c3c501c2d0000c00d0015000348944181e0410000d080351101007911088081e15000c0c0f10f4000564803815656201a000c0c030043d04049200f11042418203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 964078776 1250 964077526 964077533
    0xa0323040303051804060305120703110106080c090a0b010c1524050301061a250c180f1811060f04090606140711150403020907081f180203070c 63
    0x95000d5402200441c50000b81d584940d005440c0c1c61031800c070110b80401200e480c40d218580c58000c0510b0f414520100022010101401807049d4034468540700c000708042600c0e00512543c2e0348468004901c505402c1c00010000f14060040b40504030060391828034602c1d0a40c0c0f0110341c1030b0840c20808015480e00785410705c1614464403400c0e44244201c0410381c1a15000905003100d030203400c0400c80750301040c02c4142e90091001155106820380c20b1600c0091580e02c0f96040c1c4015079400100b1b0113814280008043c0314149100041c0b2940c070104100c100000d02e5050105c40c1d0b4440003000e60302d002107005c004102002d00b00f03030044c440940107038602500340381300040035440b5400203002c0302e6440c1410b10020303901503200035000070211029841c1c520300f078070f680050109580801c1e110700f410340304640002e1000002d9500565011b000c0000e5030038141d034060003c1c8401c4a11054600821400d00f101030740b004211030481d61485100c45030030702d20710581006507000602d541c01f441036600711318000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 964080026 1250 964078776 964078847
    0xf0309020607060f0c09060509100306080a0b040c050d030c020405090c150d0b060a090e060a05060c030a02010506010f0509011b0c030317070309020a0e040c24030b03030c0a03 77
    0x40b41d01c52040007500c481d031407210f2000c42d0b030510503440800c440341a0601c4a541c21908070303440c03600c003110303034a84221030242d003100030b84569005181a400f44800c4141000345c05401640201d120701d0003400034580300c000340038000d40c0d840006030001e10b105600102509181c2d119942050202050b91028002c00300420100124a503e01d600300c00c000840c40103592881c41140616481120180d180c0012100010300c00e40700c5004503031320030f4a42c1010030680c0e940e031190b4170024007014106a03141c09010f5070a07a145d8215400c0301c030255080c0342c00108151300c1990007020310141510303031b5800c100369040110b42c00d01525110b07481d0040007540580c08940760b41140070041d8440c0c4c4c0c035209210740040000304070310b0014003c1e1f000e05041103425401a966007a141c4255480102c0004040da01d90903c4036030f01610f6400307114080e501c000d8414844001802101507000c890f18184600b41c51181410754078880d100b10080c490b00711000c007800103880741403880a0f54080a9150002c074a0b000b04148a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 964081276 1250 964080026 964080037
    0xa1110020a0c030305011406071403090405040b04030e0a030b07050c0a0804082d0604032d02010605030c03060118092301061a0a0215100f0305071d09030a0f03090206 73
    0x1041e100c0300500704040c0d250140c175015104035201c0e5a852540400400c401c1c2c003810800030b080300f001d4070031082d43c1401001520000c200c001d1040c031a6040904003940ca140c0180c41c158002030a00c802401c0c0d41c1400ca40c01c030100c81d40f107589040c0c540d603150400c560396040b01d62841041d0080c00c80d000c000c600c40c4400ba1002d031001102034101d034410310500028404185458420303101c0c2c1140502440e04001c2801944a501030801c107600a605803400d0200c030740a00440e04c02121010304010006505510240c1a140e003a022180e900e8850400c043d40c40c2d03424458460606010724030b03003031880c0356908030000182c8580381ea44684000e649000401c10707800400c00055a6490f402048170300074070403100c018592060780c0350f031804d80c800f9002510743c41c0210148480c03c98010104902c09542074800000380fa00c0d0041007403c2c0d07124900113844240600c103031103070301c0c010304100503101c41048900c0b80100300440095207014007461081c0c8680340f40e030b000c0d0b41c145541c5020080141c3c840a00405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 964082526 1250 964081276 964081297
    0xb0405010c0315060f030b2b150b0915060705060103110a0f05030615210102030a0f021315020a1e021e180a0b0a0608090d080c0a111002 60
    0x308211075207802011642d440401c482e086444010400c0b035540c200b2480d8002d081c4628000c50036000740b401240540d010400c046400300546403120082d504820000c1d40030a1041c0d81441d4256011081d0707105646c00054034661152840d07020603244140c001d41c81e40c0c81400030b0500340c00e20440780c030340c00c2c24444264000d40324200c41094804aa14014400e04090411940700c20001e504000200707544000091100310560341c0c841c0045a0740d40c441050703045190524007210300042e5a07086450103900180c40c111403007800c0c0908414041c04900950354150f0800302c04501d002e20f010f41080c08003240d11444002d50280e44800000308101d02118020740000080301c801280c3e0f82d1051010807024190083c0d01003c910845290399502e00013152004c0524003000041030f1102110700c002481001d045030b6201e00401c4000900903005802140310300011401d0791a001c0c81010700396411113048448502e100310800040301100e026003280000c20b40301c0130444035900e59118201017268042242c41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 964083776 1250 964082526 964082531
    0x1b07210c060c170a030605030d0c061a030312072d0810030b07053f0121080313051b040617060c0703020a0b150909190803090a0b040501 60
    0x1800400c80241004007a1440c01406a68503030302c1c3d40c00b0780d0b082036281861498001404220702440703900400040c2c4401401e8030440441c2100141c5090414481201d03818103000c01040c80c000c40803003030b5a9005001d0044c502d0a01c103585200760f002c2d401010f8009014170003080881c0410305809100000c0402c003003804a130110074201070503025001380f140120700c140030010710000e0034a030300d002c2e00150582031041d02c80f401c0598140403208100250707200708807003003448000c901d80c1800c0e80c5c80844692031110b22301c0e40c0714100000d03c4050310f00b5000d210310356a025500090418401550f001080380001c00044034140e89841c10184d1089a10802d9030550084680324501441001e000b018082e0142120350903900c00c1c0c545801d0000e2607210441e4000c06c0364000e26009102c841c0003d94080742800b8589400400c44d5840e4052400ca14010412440001e1041381c001820701d4001d01d82c000b010240d0746256641c0003043d8802040134405020344014100051000440240a540f08a002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 964085026 1250 964083776 964083839
    0x120206071a2403070e07091a03011a21070c02130518010c0c0f05120c0307050106050406060e0f0301020d0e011b0806061c020f0c301b07 60
    0x3018002e000d006080504400e15081000381030782c000039401c2c122014503800c07030101d64074144266135034103165101010804c862041e9010a403901d400850582c0c80c001040760b14200810000512402030b0300b10594810b10142840c01ca9856001c98075612140d10304d008802c3c03681e264085054000307100c87c001892501e5a007441000c1c418034400c101e5100b4410000c12022406040050004004030300142030318811290443c280403040c0f100140b050ba8004426030748a200e650715540e070342e0040700d0981e01940303424004a2039160600814089590a0751100641d0084a081005007100101019810340d4204014000000030b40030f0080000e200100014131824620041421030000d0302d4840c0800110008101c2241d83d204140c400d04543c00d10303161443e901200c404402440f40d1412054615130105550241000007e810000b9100841c0c281d0b1a001e40c0c0e101034140601011980104c4800c04c1c0200e03811440c0e0801e403610400400e200300c4000c00e581e1900401002100030040280da0020f000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 964086276 1250 964085026 964085041
    0x16020607140910080403200a020f040b060408340506030604090b0a020702010e0a0503210d050411040f05070806010302090102030f03070e10080621150c0a020d0201090507120206071a 80
    0x507001f8080d2003001040c1d06030220030940d00c0e2102c40c1000028464a6448801e202075202c1c2d9100000d8220b028000c56034658950013450340c0d90385201500604101c20031101d0b0b201100c044607040103403603d01d0704000309a00b46410040d040e00020a469045641d426072000404d4000c2e82c800d000d4024070100594483d8103000041aa030b071070901e114001c0703200c03800070001c0d034500140c00c0d1880f21440b58135090341003030000c0f05482486901000c2d48000c1c2005e040c0814090101c107030306449501150b0401401203c050310300d05541c41111007001180c0c060000a2465020b60000c20b041001441030300d140a25207410360440b40c00a50f100c100003900d101b20b442207030030620010140c0c15182d0514240030700c1d1103800076082f0210030a42e003445244024041040388000c1203180622080582070050614044900261542024501000600c184981207407003174018071074181c07816044400307010910b040440031600072049030412a04a0020030a40c404a40100c840c01094810154140e120303041010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 964087526 1250 964086276 964086287
    0x105150a0603060f030305071a0406051e0603060c0c010e03131a1e1c020c010509070f0503102d06050f040b01080a090c051c020916020607140910080403 67
    0x104420705061800c3c00078008215410300305800c41e030b8189042991051a440c01d40d6915801c813105a41240030b14041c442000080c1d0004c900c0340006c450340b0500e01d5a1000c10300604001918942d806400202c0844c2e142c0c59004014801e004038140042414064410705038074590102201044030500010148400c1e00300644030345420084e07080140c00c01400402000422201d02160300940178005080c1c1c620749104400101c40c954006c404540314030160ba01c0c98040c05c0c0c220741960460081c0d50001c00c020300b83c2d4440c401540d901400400325846004a07500040201991800c0da01c0d0282c034102c0e45001401080000c910b02191010945134640403c3c01101c0524000c4503114500300483d003199668040200d583c0070303c0720040401c000105060040f0100d035142c10054000c0000e80d9611500305038400f80200140c403d440c146c1285d554004007030710007200c0b0324810006801c528082140d5500c107030501100c0190341c0c1c809510b402e05810003d954020320002c0b01011581c2013042005164004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 964088776 1250 964087526 964087529
    0x506040b070c05070b03060a0905070509013009110907050d0f180f15050112260a0f0e0306072f030a0c170708070b01120209040f050307050105150a 65
    0x905003048810b400b030365000d8841c4101c0c0a14440141c0100015400b036581c8410400241580b0300100498106044001c1a036030100c10154081001c041905c0610a011203160000000040b18409194103058030413024102011094518581c00561190550b80742d01281d8001d100c03d03255696030340c1042c07600000740c414100300d520780285003ca15060381c0d0030884240c800b450b40148a010404001d00d022100399050018400350315142c4000403552222100b6901080d1f400388d001101c1d0490720b007990b2060201021003580c1c15000910100302400d0103400203600615450404032074107808035010900c1c0c140201c50840000340b40203200051001ea12a6242400c45000f203041e00c0c29030001002e6a50b8070503610040e041014451000060104410f0640048100e400e00c2c59550b5070281030078100e84d004204203451445030324000080c00c11490031000e00c45a03000c0c01989442d92191503039604601c00c03071300541c1c1031b02040104400180080c4504ca116810300701140201d4005042440000d81c8135 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 964090026 1250 964088776 964088791
    0x6020d1413050d272612040e0c040e090d030e0a0c0b0c0f0601030501061502072d05040507110111091e06070c2c060603071112070506040b 61
    0x152080c1400b04802040030b038060049802e01d6015404205180b101c181803112001e0002c404c510004542c0000d85113640c516128014040013402d1075041c40203448400ca5421450a030a0400c030410a0490301c11040da0b124543da0074803420150351313100c0040c020302c04880081c49030300034111640045415108408500c00e0300707401090461115030700c0e00012003880c0500100c42c1c10101e0136600340c03c0b007001403d01e444072220a0381d12079652460014081e02c0f0b0740c05241144007000c1c07419245607200049001c12201c0440d000d4000702039200600c15a038044003070107041c0614200000c01e0988450190501071085580d4580c0607114030000a4215030381804035504000b403c00c486059a03071016034501c0d105428100e03210101c030b0300c28001003003440b4aa000800c40c040860300010f4900c0c481e10003402c0300c1c2149081110710052442685240d8a044070210751000c0c0c20303c0403803000c0c0c0c46503215040d2004940304650030300d10f104080f0ba8858021010407506940000100300c20841004040342e0402d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 964091276 1250 964090026 964090051
    0x30d170c0324040e010e0307060c030e0a12030b0a0e090609010b030a030302210705040806010b0901050706020702010909050c07110d0b130510050708011716060c0c0306020d14 77
    0x1000000c1c42c0b0341c80c240300ba0000d096860b00c0c0b03101901d5076403680449415240c00e0000c00c08031312003a00361601e035045548181d644a107001c1041803d28001c0c061900c0700d0148202406203002190b0b9000030f010a403e2400c01015512178010015031641f8002601411690b4282c20031442c11f401a2860000c0040c02c8070351513410300303500b255540c40015807030340040d03854140540c980b1502a031010360003031002e091411240089007400b6086030001c3c01442924884030a441ca56070301c92514040c0f602c0342d2070001d07000500c10450500811195070150420520514101030680d0b5035401c15002e0396001e6613405400640010700408105e80c031000180d004805685261401086840c0e00b038030003d008140541401c1c03520040401c00501b4003204c046a101010b08105608054800802da02424010360603259401e1210400401c0c000512100f20700110310302845641c14030008a8869094403c11140c9001d00200070000071401d002800d682d14411200254241e1a020f02003614200541116103d50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 964092526 1250 964091276 964091281
    0x90c0c010609050916231f050a09230618030a0305180d080415021e07030303140402030a11030c060c060a050c071223030f04051c05090f0d02030d170c03 67
    0x36950400605009001b03110644c581c003140780071034a1a404950b08122140f01e001460001ca5080b0010b40112005940c2e86103250341c41d5404c0300403200800b0340300e003125609006010814a491001414800103880c51705040f040c0400c0802d203440d2407100e003200824004902c0b200f044a01642c0c00300607803800c0b94807043c1031000382c80f50b80080c4164001c120b052210101080740b254000c10400e21600721803c000c9004103040e0b0421a1102c0c00d6000850001f42032000c0b01204050030785826014980040151161032625659085110312081006030980a25401081039a0718600905a06604070018240d10710700110040c0403102c005058808a403000d000307880c0818a070800c080751980c01030800c1c0c5e0701d0b041d00290f02001c869004a0b015403c4400104000351121000051409a0311990807a2480c00f4061640644501300720459800203d00748501107040c0380c038892050348507801802c0e04480303000c950040b9040044807141d05010506000e113518407460041c03511540074410500650650 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964093776 1250 964092526 964092539
    0xb0d1101110106060e0f010203040f030323030106050a0e0a320616240e010e070801181e05070806400606180902090604090c05090c0c010609050916 65
    0x5030050885c0a0040500c8035030424642d008004035005860082c0115210030360320700e001003c4800a00401050440c49110000074a0122090f64183d400c9500d569040c03220751041160b04049200c2495805111483d00003a55001d041054002080581d05900356000744100c080a100003014010f001d14000c00400b203c0040d00078035100e01c00d600000c03032034411004290302a02c210f101d000700020b5610b4186891800e00c2d05502c00f103e25070049081e500e11603a0381400758200d03000781452440303501c0c5078491a40002d08140407032091079050480c10404440b29241d1f5881d10881780c000c151503600c11406d01801900c04880641180b2802c1c11560461f4070180d107030000280680c125011851140102104102d4103070040350251004603029552960b0040628000c2c100c8580b003a070192030b000021900c1c82c2864012030580030f40060f01c1e410034520780014485601c00c0288070704139096080c4004040400b00303001e01d02c005c0444c038a000c01e6509140084034101188144040302e009030743c10042005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 964095026 1250 964093776 964093787
    0x3070806191e0c12151203030609050406020918061809241b03101202060c01060905040c051909021308120a080f130f060b0d110111010606 61
    0x100515500401030611403261030030140c0360b070501400350b44144064600059060754008080101d007651856890300201c030b0744004031aa41e42c07005040b90f0300700c3d10621034800c02c4550099503d2292a00040440e0780d14000012524107407022901c0b0b5800213910f8803d840d0000d080b582c2c0c84d40c2880c000e60309080100000b0640c0c18000b5016110015100009040400034405e1642c407403e11101a860026110070140900c0740480b48e140785011300c0c141c10b902880d22481900d10504a00c1c4e8003195081c100040d0b40c80b1400c084d80c0c203d910000410040b4500e51080c0504c43c010319900b0b40110300c5040515104480c1e406a810090055800c40300c101c1c070340c102040c10781701151070810005a540c180c180c08421070390460b8002507024032540c1105d08040c03030f2603c001c2c5805041030ba100003e648424828840000c03041d90104114450007042d02d001c0f50046040c00c00240c4501c00c0081c03140300c52400f00b00d0b0550714203000d41c0c81d41c001c1014404a5600400807058202400000700082d40c200300000c3d10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 964096276 1250 964095026 964095031
    0x1802191d0609011505160c0302091e0a060f0b130b0c0d26060d0309150810120b010b160b04030e030d0302040501200a080f0304061103010308030a0917041706010503070806 75
    0x486c0500103455414484950300c080c0103540c010b42084540c0c41d0201c0c96409004911a501003031281583c0000c4031402c1d6840340006440c9418401d002d01c929008004107290040d4403081400a20310030b0015180310640700804541640d00050882080b2040c0c0243c03034486100361101030496040c0102d500c550705004034942c0f120301100e007a802c01c01c0c14203080721b003604645c008507015080721411000d10764008921501c1140a24a041b10003501d50078a003682c0f880c10b40006090321400030060000803940000b40c401c035850303100d08881d030356016156040044015941035011071003203580118641828411850720302101d08007076160915240000303060009004c0900070000424106e038003071050610030a425107400c03290003915055038103105051544140c82c1201d45914048240a03540c4400741501d0490360010b14050a640c0e480e0040005041102c40c100c0e48038142c040380030070b010f240c40302400c0034060141c1d83c0264071445000c2c00d0316102d41078002503c03907401400d0801401c100050500d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 964097526 1250 964096276 964096297
    0x3101a0d08360616140a060e0307051207030f050d020c070308040510093002040903030b0108090f190813032d02090414031e1c1802191d0609011505 65
    0x190170900703003020604103420071400819032820403030014403480b000005000c503503000c1e030251071042406a0b01c1010301d10503114010003041004c8410191070b4044c03070103003010720780d41d407005440c1c400540449400c04905030000c650280b40070030280100d0034244c5d51b800000c03d0500b032030a141403c02108a4580d151706139040780100300320f16100f42e0342c2ca020001c1e800a941c090001e10030151380b031030b01401130111048607500280d03025001a24a400c0083d032074001c2d070101d0024041140824040c5220542807841c02d888454003000702c095401c15507e8000000c0d0300400b20940179100da0002c07403800740c04ca100e0140d40c03409540d1490b0056130702c0180d136507085940072001b8121038071502c0040707065000e851a0303800c004049004454101080c04024002c483c0005211a0f04403255030b521402c48e02d4220064081240c0d00c0e0214006017420034441220319001c01d0300880705a40c4402201d0340038070085c2c001c21852810014054281400110640508a44080303003200742c002910080450140c1550380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 964098776 1250 964097526 964097543
    0xf0f050703200429040b0a18180804060311040e10180e070b09011b080a0201050f07021506042702030706020604050607031109040908070203101a0d08360616 69
    0x4c0400da9100d5202140d4807030041e00c004420355a07118108070002034000c0c2208110309107074054034401c6241104803005903115500700c0c207203401d120044000708080c05002d110002c2c02c2202240300b00c100c800e1f880c0b05002d1528070026003810408410ba142c9112085082c43c181040904810300401161100c103451070404020b0f00c90101d200100c404411408003e80390003041c440000a000880d0300a2100841d1500240100e4545207078084480c0e20803600076005030441030701071490228160600d6048030009001003100d200401814400320b1140b030700900f4214200d101101141070503c82800108914005061a0b00d4551282600c56a0050030041050b51380d031810b180030360000d01540d42501003d8010440881c0b00c5ca090038440d40100c100382e12a105500602c4980300070750140311102c1c070844007194812035098007030180760b03003500d68111400242803124a940001980440082c40c1000303180360744018030340e01d1059040308928001d81c000c00c010080610b03100390103e60b0303000060380400350 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 964100026 1250 964098776 964098851
    0x20d0b1206070504031709062706041a072a1a0309060712140406021b0c0618130e0601030c090e0c01140c0105010e1504090b040f0f0507032004 63
    0x14a1241c82004c20891b4423101c003040f6039000c5407400704040c80780d0b0f1042126030307000d010502c1004224040d42c07003218540c0001035030000003c503402c00500300c0c052013220015605061500c072000400702c456899201d20100c42d40802a500e0070255001c90010500074a500d0b5003071001046880d10001400300040c07003480621003104120550224550f03820004001c2c1181c1803070701c0c10502170b510180080c07440240c080c00ca980c0e000408190301c17182201c02031615152103d901800d0b900d66040c40e000c903500605130101e050410a5600540d01a00980390251095604503c0c106000d00803c0c0c11040700b2030310301140079148200000d00c01c203400341e090800884020f00c91121464cd8461011964119400e00d00006141d05142044074081c1450b400145942c81d82d4206000032141c02e008060550141c10002c40e01080403030b1540d000130390043c0c0003104800901c0d201d4501e029809c3d807080381d003119030b001410b1000902e0340305d000304c88a00310340c20b019000880c500e80000003201c185490401000c03456 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 964101276 1250 964100026 964100063
    0xc021e0a090603051b031903080711010203161722080c1906060603150506130e070e1f0206061201060f030302010b03070504020429040306020d0b120607050403 70
    0x4020010711500c00203000071501c0340342040e02c801e034076800032102d021100000040f40c03a01003900210210130f01e40400341243c5941702101c01200140c041014080b0703d469002c1804802e0000350301c901420b107040450042e04090082018001c1d50300c10582095210070700c1480c00798000b00c0740c10404000c406600c01d990900705140e481c07184484101c01840360300740d0161b0306181403001d611000d000703140810a2a548500c29800d50741e00f180e080d42032000d20f503002d00480c9403480180070030402d803a0719840420340710100a85128001c2d0764a03004601b1103a912074003407801c0310303018001040c04407002200500361040030b5902c80c405081103116030280400100c0c0150300b540b150b0020119120b21500040d41c81c14040d0081100c0610f43c0d02030300455101142c039082900803502128244106d208100365011110342c14030000310005400e480c81084000080750550020b411252206100001d840510704200a1810074444181c013131a000b50003081b14803508117090703e0489402504140ea20845c000c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 964102526 1250 964101276 964101289
    0x408120a021e1b0909190c05120a060506031b1003090203011506091410050d090503030c0c0d030b10030b010c0f0b040506070813080906070c0905070f0c021e 69
    0x61200090b10b108520081600e000081c008840000d00364118001034030700c030144a000c800498002c1d80030381c00301c00c041c0a102060007100101c24000d9402030002a118800030707011002c00e251802c0594000d07c040303c14000184030f242d420003812802817440004810035410b084003000d02c01c41c443d4209807000c0c007026003c0c1e08010341302a0300400030055520300d401d02c4441c3c40501e0060b240040c40290000c81c00c54070501c14959901d0300200025a81ea614140840703e980c800d140c0141d030300f42c070340d0094000500b041000c0c5001c0c80f0601e8050780c0354a184440c451812213441c1d081c00c20541040360704d1060381c0f03c129140b900500b65140201e40203203020010b8540038806040204400d14114010007402082c0d40d95a000f640708109907411074030b52100880706210309035000c1410f40409643d050000b50410005c1440c4074024226504244d405d889800d00c85445600546883d900c6004000310300d0741c070039a08603180c02c032810006e9401c0c05a401140040004a2035400021000c5003002001c1d134601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 964103776 1250 964102526 964102543
    0xe040602030c1e0c0d080402030601050f03120a030603120305060904060218120105220c260118050105220b07090305160f1d070315090207080415050408120a02 70
    0x301d65400018124004440242c4c08024415002c1c000c400c5201d00e850321400700c543c0103c0d0000e000b04016400d140c00c10883c1d001001d516076241c4070701c10400c080820901c0c0a0a001d07412a100002c1180c5141016400b070b4615240280825140801300f10403a41c98008503500f103600f0100050b04c5038451075a10403003400e090b056640c06100c2150500f0102c0c0d05401c803030f07c104240980032030b84d9200f08206e4041c02c284994000d09103d60a0350900581c00810024500105d1660804e11410340c1e010324242100c020000b0940005040c10010007131180c04d003c0d103504407182d003030aa201d00c90f803003070394203094440000d00604038040200441c6500c0c0c4540d070228080d6401a0170740f842d411001c1800b44101c640d911a08003440ca01d00e200140c0710300c402c2180130401152889180c80c0c1d5590302c90807030042100c403c00f448104c2d140a0041906003461002c1c001c414418000b096585040c04002d0070f80e2110000a0010400104424401d01101084403005082071505441d00c0d58401034003030b820030300003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 964105026 1250 964103776 964103797
    0x403031a090915091f150e19090302030412050a0b0c03010f05060c0312100801150509131b180b030127050c2713122d08011e0e040602030c 61
    0x3118a1105c0016558032644466401381c0303018020b2a910f1524148a52085803107604100c10186184005412a000242c40d140300703105030b0b132826480e03908403082d40521000030b0f20154440030741c18040203515a00c040c0c01c507498000482c210f40c540a407124080007240601e038002c5e140440e0060103101e04009403841100080480006072a00250200310702c4520b00c1001d0700c542c00d08050b81c5500f160080340304151107010340100b00c1c80d6030701000102c1d4020b840d0b9040f24810b9a0981c4000808091203409018100c0018140090a00b0714400c1003a030b000c95000e18880d03403414001692004034546070355034910103107407246100b00c230a042240c1001c0701c454481d42c103d0117502001d039024a902c0c07001965200c9007540e00c070440d01c070180d82da940c0400c8120000c0c00d0050240b0301c6910315005000c443c00501d0707503103540ca040e040051190b103450003c0346107400104a1400c01400640c050496440c803080c144009580e6007490881c10819007440540054015503000000c240015501411078184044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 964106276 1250 964105026 964105063
    0x90612030d0615020706030b03060c091207030b060109060e1f0908010510150509180a2705060f130639080703020408062d0403031a09091509 62
    0x43d100300e540b246810f0400d90000601071900c01143c521f000341b054603009000a0000d103110307660456807400c0d44d80300b141859400401811040768081c13003000300a000c1c612818076981c0d01d09005002411801d06600040700744229621141d4103605c4508040c4049091152500c18440d090441030f42c52070003039046001c0f42d5081004000706403c00e80b03000d174120ba80504040c40d45e0358030450704999a0146010240e8411245135080380c46c15000601d581e0000c030f42a01c00129441c2d00310f07035050348a40c2808042d80546a600e0312406200087c02003540c04500d0840c140740070b16124080b203800903070b054801401c1542d54141c00c5101d40d510312403a4ad1031315040841148240802c2900c4050b07158a0389008001110070000a2045101b80241d8003164407101c005c05141e10303503840c03501200e2f02030150303801907140c0c40034001c80d0f4002c500c0d4030500407070103a200040d4100c04404001009100d194005004140001c103000144500280320f58242d400c80001504503118401c00d1428600c100c0840402c090713 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 964107526 1250 964106276 964106279
    0x30c280608160504060203071b0b071a010f0b030a091a0c12061012090501090204110a02010e0c0d020906011110320103080f040b0a05220302090612030d06 68
    0x160403089040c0220203540442c1d11000d03074030b5800ca803d0712072802040c006030014010000060100310031140c042070f00c4141d0070359603074491a05180702d8209820640300c40c83c040c00f85035440c5c0511200c5c20f000d42124850440c5582c00c1c01400c03405840080c102180450f500c4400c80300340310142d2140402000c043d1120000c505000b80050010b03003298603010b94040c03a090200303489152100443e195841c0581341c003409a95100808001403c0300c15050300c1554a50a121006035524450207c154214100007510f407600807200a08541140c03001b900103038007800c150841656880c022172040707a4102e03060000d0342c0c1c8540040343d050004802444c50b074410040743c2d08a4240030382114080c9001d00006d4200555018151069001208614240e00300c0c1d080061000c101d01d20028841c415004e02c42c64a0643c1d0b4151384007040e070080d243e05000402c04100008400a6030f02d507050f00b020032402001c0410700716000501003140c094841e610980359550703001d490007400d009540c10f0941c200010032040303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 964108776 1250 964107526 964107539
    0x102191a0f04110d020f06130915170c15031e0c030108010c08040b070503250306050a0e060a06050919140f01020318090411030d0c0b1005030c28 64
    0x3a842694101d4a040c41850107280a0508a03c10369901d90000d02800b01e4481c46007e000e40d0754070144041c01640181c242c041020510303409207110b0903001d0b4000c2510a480c0200e0903258185031515507406401c5030004ca030707081d605c0c3c1c444d402503501110205540c03616040461b00c807102d610151820000140000c10169010050296040b208154000d004090390b91a0844c1d803910200c9006011285250104181d00d02c98405140d0214030004240c6214401480e2803181000d00201c0b400002d480340700500450070700040070f00c010311b0000c15020007420400005013810640340250010828040303003226940d51420500b0340102018032078202c1141d00c55210b102c14114652800b40260030014401c01030f54800803c0301c46040a90a41600c010303820707010807210401c082d0081e100301034002e030030600030b075024005024a903642d0344a4210865042c0f811880b0035100600c03210425400382010070541e14003240d120060710089a900d41800701809602c02e41d01c4550b01c5c41030a8800d45480441c0700c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 964110026 1250 964108776 964108801
    0x120a0b06120a0501031401110d0906090515220201021509100e010911010512150307240906020318091008160603050f010f170f10020d06140102191a 65
    0x1038034000c8440d03281c0402040031407403c1e2340b024682e00d81c045030100851181d10340700f540f021300304a100d03c0700400e030b0a0460315860714184502c1360090309100b151080c0280314240d80985200003043c0765140042c5526600040e454020300100d4100d41d40840002500044044c0880282440803030402c20000e03c0e00164075000344030104003120358984614691202c0c2d809242a02c40880502c0540c14199440180e101404000301c2a81e6405104004c00450582d684103104800075803080c0c542c0d05111190003005101907034a91081b010b5400411003056805c04071440d14010341415100e2420503191225038901000c3d41d940904980c1c082d44521820079100e81c4018000c5038010b0703a0501031511000d508440441c801e20901114040e41c0c0001c000560b0301c0c417201031264000800340c45003003c012455a08103610701010700c0c406a400110601401c0441c070580e0068591000c0405241c070407000040d45c2c03600c204403503c1140d142650395600700500c40d42d04400c9032044c032103480001d00b80035040071039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 964111276 1250 964110026 964110029
    0x803100e0901060612090c031e0b0408030919021f090801090803070f03060f030213020903060f160c0c170f07030602120108010e0615031501170f03120a0b06120a0501 73
    0x1450703801d500515803113a400345d0f60109030060070342c111f07840c80c40c1d4070b9001030310004c4450150b0b40d00c0041c110022486542e9058402c50050a00990f45c0c81c1100c0030718106010380c00a500c0000303004075004c0268403200c203101f1040014480e01e0140e000f03148420359401103503600c28100e943c01c05070f05508100307002001c2c502030764090301c030790304005001e032410b0b0207a546600950101001003041000545404201c22262145001d0300525002d44800441e00b4518100d8202000240900c188a440c181e01940e0b5501100d0034a4010070041c00c0d641c4440100010b441540034055000546002c901000c0c410001c02c3c1050782c084501070782d40e0f4645500a500000758900d81c44440600008a2107012300440b0040c24840e006000150303100000d032030151000c000c507103405210304a085034191b880020414040c0c0b140213039124070001003040da24500608410810720940003481a022212a201c00030f40c1c010032408800300f40e20102c1400300340c01d401030b501000310070700c562401d0140b908102e51000d070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 964112526 1250 964111276 964111289
    0x180304180b01082a040e0906070801060309050303180708030304060b090c0a3207030206151008040809010309060606050a17060120030c0304080d030609180803100e090106 75
    0xc019070081c00155200d1a08540c040b65086446154051000034500e84d2010030013082021400c0c1501c0d40d0142c40300000c00c0360307480080e9104e803042c0b00703c0540204206004018138070341888546219070f101516400060102140d10107a0f50711007091040a01c40c80000d032a071901125100d20b4103040010180c00540341d95406128005d000c02c01001603801251065846500c40c510300341a0813060f0600c4044d95252030814000c1e00e80d02840c4000b480c0c000f001c3c3c440c003070b500920503070500c221451f128001c00580240708510056940520b2500312100030b502c00d800124160300c91842e040107034040e000c4e0310720040510b494000702007206034000016100e401e5195895001d00c803001d28a4800b180313800e071340241c0450310b48030720b1100c0798a01e8500c0e5401d10094009503402c10564134441440c40d0440d0700906204c0d0403c80724000d2265051048000402035804180041084001510a0b0408050000d03100754000000500e030454481c1108004160707020100380e1500e04203200a000304590f00495 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 964113776 1250 964112526 964112531
    0x6230319050d030c0c0803160c05071716030c15050706061212020111090f0a0902180909010b0607140f06010f0f090b0a1e03120e0a05030f0d0818030418 67
    0x1240c16a205d2603060005070f50210100e443d50315800c01000d02d00c81d040c0c00c41e01c00c01c03298003841400914244551300041c40266044826040003041042c241282c00d0300f08907000d1005201007010801241076030040721700304400e0039080d8043d2401220284100b01024000d9801d240000070401c51402102441c203024003414440c24600e44012400e9540e6008807600e0050248040e2443c4e1600307000718180b84000500321640540da451004060741c10030b6082e28615068030a003d03015040c5035414940c8400000001c0081c4006100041c1c442e00030744001401c0c020304207917822401002081210040009481180c4280d031307490320600700311842806031003107440600d440000d000b0418000c103060a500140450307181c0c2d040041e00c01107580c2010718064802c802280000118000880000d03a60a299030323070b00314681440081c004445100d601c01802540070a00061401401051200c400d943d28a0f050a46848400306010348030000e664072080b5000c000790000e0042480c1c100410158040a0309 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 964115026 1250 964113776 964113791
    0x1091d07030f090c0e06030f0f0102190207080a080306061204260937080c030c0a03020321090303040608060f01110a12120f0b01020105010906230319050d03 69
    0x4200550b0031085004001314016001440f01d1042546a00e030f214401a048905480d000402c0910741043e4240d01da5883c0d500103600808200251401c0c50401c08031300050407035a150040302aa26400d060703010340350510110200d4915034030f10b0100c503964840302040303008070705107428070800c20000403c02040d000c2a540028910040304007c1d0303040b094004040d01100925110315440d5114908141c101481040010154070a860a0030f04060080100100b0b46445007030181880c100706020090311840301a4001c00c01640c00003603000340c16540b104940c0790a0b00c15405820a40101102076506000110303000c6011035101c1c5c40c15120728000c44540080011031070043d21251100342c244102c6400c0f8503110004145c1e030540c10074035487d080c6000803110241584030307411600000e111141503600d4018421540da4240101405803108070010054545828a02e860f60505194010300e0540c200341c81042c259001d05c841d44102d00e41102e40442c1c070030b0625205881d414129405000300380351142 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 964116276 1250 964115026 964115051
    0x40b060c0c013f090f030215091f020a030902030601060f08160503010302013c020615060a0e030129150c0c040902120a0308090709020717070201091d0703 68
    0xc0d80e5400074021200d0f00303203001c41e1440f80031091003901810b048954541c00580009540304090500341406503001c2c0483d00c0c000000189006400781442031250b2000c50740c002850050341d440c030b40613070140b003005a50342c807060001d074041e0950300c00c0079625000700400015000d400a0000a00c0050f2380d4424002e0342e114110f4600180310f402c040800036070300780018001075004145541801268606805a4801c0c400403022a105c220701c454440713035000b1107100030381501000381c0b039000340c45100c41a6100c04600003107011030142c001c6c060200041100c820980751030030742c0100345c84c3d48005a083d024007550680c442048a660f2a014080e41050f1521590508400e054440400b0710031b02500c5842e0a200800025142e8171a00b030780c2c010740035a80c0d0552050100400610305101c0c1e2200030f0f85142000c6101c3c10000d4a5200c100d4980c0100942c000141c100c102c4c1c04021079455030701b80d848010500040f20b04075510b400c8055654024202c0a00030500518840d00c148503c2c0e070107014641c840c4d00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 964117526 1250 964116276 964116317
    0xc070b0403080901050a110f2d0a170c01020301091d0d090608041502180a09060303020606090703110d02120a2703020309060a080a0e070302130506040b060c0c01 71
    0x310141030800b0a0010072000d603c504d00401d00e0032883e1078590b5591181e05001811310501d43c081d82e0b01980500e100902ea020f4404400c0c01640c40941c40d2a6078a0344903404545031440140028950101d6400b40740c85600380b141071790704801020000315103c0da1a0300e1500b0060245c0f00c0d84001d04407000c411250004400650707000001c069584026005140c08800c3e0342e0f42030301410869110b40f079541c04601034545031004d4040c0f000d44040318042d008008050060f460a1034110100039820514140046500010000e070803100540b102d00031070392001404c400508410542c580c42e01c0000924003000d44c900d401030105040114848401034541c1e9a2031012244280410541c2c04044402c0b40000e034071741d01281c10f80a000f401524903082809000074210350002c0b19100110300c3c0c5005004114259100d0321b4200918100140b43c241c1c21038000a801420411120031303003e496100003101034903150402c60080402400050f1115901d0303076480e881301c10180704103002610482e44401c0d883c0880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 964118776 1250 964117526 964117529
    0xc03120f010504020a090909020a05040912111c0c050703020904141005150d02030c04060f08010e0a111903050607170f0c0a05070f14013903050601110d02030c070b04 73
    0x945803a600711f407425040101a10001d08141d0f0700c40802c040000e5147c886000b0580503d121758000d6880b00181e680c05089541352340c3c00055164001c0541911750b15100964036807081060400281d120345501c0d050303152034a00d81000350800400c00500c4108a141602c85010031b5890066500186030111207200301c1c0d80445140004111142d40c40503641402c0307030351099107030020b420707a9040f031444d10124060301c651b54416900e515801c082001546c41c00c0c42803200070108a00a0148401562600501c01038078a40c01841001c0c20701c1c00c0010f00c0306400e84400110344c0441500c4152a220707038050405200c01e074181c0c800141b0000013841c1c18000d0142d562103030141c013020358240000d1042c1111260040501101c40125006081d00440d2080811706600c542e110000302d942c0445070206c00c0c42c070240301c0040303441e03004211650b02012101c0000c3c0484640030314000480f944d1304001242c000780300031402c0e12140590310b140a002c0e64048002d0607441241c1040383d001036540c10040901c0c0c4a070303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 964120026 1250 964118776 964118797
    0x10207030201080a02070b0708160207120204020f0c010618060e1026030309100b03150c03061f090311060403020102100e120406020a05010506010c02030a02040b01050c03120f01050402 81
    0x441000c0c00198001c4403c0c0d03401102a0b0303001410143e9a90300c5003d224401d030303401c0d030101e14080100702c0c0006881381010703424002ca20280c00703800c0c80d01d112000e011104110080c86150040b408152055040090301c02c81680580280b143c0c0d50340e109016401c412080074501c03054100740c0b010441503882e036041c501605505000c0a015403a00320140c3c201c01225004507004400030104955104041001d0b42c041c4540c88064640c250343c68803408121981c4400e060700982080d10f040045400540240c2c0e8492610204981d882c2d440320000b031010b2149005401e032000640510768112503000001b003003500d1003010f40c900300f054a24100f124a0040348802401a44013a400d1120765403d500000301c80076207603040316210780d0641c01941141d0032540000d0016071010300302d141444024041d143c2c00180c2070070a200001c80f640c0100352079030941440640540d440d0f040082890f48580b0859003608000c038242c80d140e105101e00019100c000b41d80c5a80c3d010301c01800840d96140070f2007107511a615 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 964121276 1250 964120026 964120033
    0x902070c14090703150503011109120628180609020a0801020405030a02130b0303030403020d2d0f02070302120d020c040b10081e040b0a05070f0905012d080f150102 72
    0x160b1040890142c10040c0917a9284070002c1c0002a81d43c070309008424031a09800b5001c0d85520840040c00283d03601c1c071f90a0700041e44000180007100f8100c2407290090403031101c0b41c201e50402d4a10b40c1c0d000e0300e0515801040060000341c0341d0244001644150311482c030813943c19006540c1e44286600341e02947c050740c1e070305400241e1a88018901700c0c6182d02c0b404001f42c4081500301041d00040d0858008403026400760300700c0d02c465014130340d10030111074252920b620306900b100d6030b540060800e448100e4000e0140710703e031031071024168020030502c8025507000780342d00140300c4880c0c01141c070b401040710158058450514411011300d8036005006807110044e208058004070200200c44005010f848119a0440b12500e04003031a013480e102031049000301100c00080c00e01c1180d001c21a0f000425010401c402800b800440c103070700040c030380d0450302d00346046541081040700d174442c80c100714008a5013000a055480b07140c0380e0040341702c0f88901d0082c10039621079035440305c540180c00942d0205500603003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 964122526 1250 964121276 964121281
    0x15080622020603010b091810060f030f0608030d1128091e0e07050a0801030b0615070c0608071409090a020706050a090b01050d1e020d0503040902070c1409 68
    0x5803100c680d06068000c004104044040d40c011079580c0c0d10030707040b40000180009072803005051110b062400c0e281c031780803101c909180c40944001c0404c8140510400c000c0d0742c90f0300491f028403e4024030008818070008003c41c8c1e41d204942640e07030b07002c000342c400031500b031001840c4121590170945d002c601c00f0840034010403a419045911940700c80c4146800c0c80582c03e4046560054440c64001310f42100031040d81d92424400e4004c42850002c04510812002300450610540c0c805141811268024640c06117a25100700181282680980807040305101042c40002d00100c1201401240c07090f4544510b107407500d0208880d841441103038080d080c3c0d0f003040754030702c2801d00f0101144c3c000181e0b10018140724032a55008151882980c0c0106001e444006180c08e0084000e0700c14010201202e02a5408080d81c1d50200304030481c540403800d00182c03014640941d22165416941076a10405880c0c1d580d460f2007071170000390030029044d2001000b107400400c6902c2207280d000c0c1009401820400a035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 964123776 1250 964122526 964122541
    0x106080714060c0303011e0e22141005040c0b030618090c0402190f050a0c0b100b13060908010b0a1202041b091a1602090a06150309030201150806 64
    0x21860040d242c001404020b040c1c1c1c000b0090014501a00d0404400e080d0080014800303040410b20b604841480214131044c00780c01519180c0d803070384018541d0852510340360345040c211891301950701086180e004e01c01c01c0829118103580000d01c030b0361052581c40d501544a242d814131b02d000490340c1580010303154241d01c0b100d105c61030304540d001030054102ca41300700e00031012500381d0700138100500e1407048000d003140815800201c2d4808840c550315125050000c01c1300010540980c0240c0544180320000c04140c05040000711207015201030f500c2643d1703403d45c1c4030500404590038420500017400c0ca680120300c03072506000c1e41d202a6001021060b5040c14450b001e14450401d1004a1b0b0059585003101e241d410211000305840340075441e502c04091800d5800c601d02100c00313210304282102042200d41807440c102c0542e031069010384a0012555a4844041c0100f20642117144880c0051100b002c409a254001d500042e01c00c1d8000e007c3c0b603800840800d2849100c2c06406c01a030003901c0000e455 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 964125026 1250 964123776 964123799
    0x6090a1a09030c03040f090c0f05030606130503030705030309070608010503030307050c0f0f0102090f011128060203010f03120203071112030706061404050f13020103020a03020405190905070201060807 88
    0x407507010705a03858502079000300303465075100b58405c650401c178180d8200030301d82142c490041c903042c03a400c00003001014514010006d00c0001e014521036000404c000e50704c01c0e08141c0ca04060f00019003242c2c0d039030a181c1091503413508111451217030ba214584010400c64480e00c035660484001600039401c6403250300040c0ca03141c02880d0b40d0b1ba0188512541c204607000c0030013201134010503076000140d40b081d07450140400d000c14000c403e8103020b0503000a4403000d01c0080d290b8403d500b03034040102d4003091101024040303074072103401910003800800042070395400f541072031080364456800c00c00601c18500c000d0781c890090070f202410003040fa80da40c9030785040030401d50951829071b03419640b40409656603242250b500e174009501040802c0075036440c81c1032500c80c154000202e07007540003080c504411141c040b0301500c90020304058000c0784a0180c14029015200030744001007800762200f01020b003280c1002e86911960010318105408030308858018800c00b01940c0d0000c010303021450819254890 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 964126276 1250 964125026 964125031
    0x25142a0a080a030f1e1a0303180907210e07091112100b1b070506120109092d2a0506070203072103021015031103012702010206090a1a 59
    0x1245441c1d00792005000c1c50640d09501c5c114080600150000c140b8814100d01a440c1e40c20601961040150388080510602c02c00c1108400312041c41455031503000031984200980a40f81c0740201d204610840c403911038004e000b0360a00e650890ba02c496030b440c1d0050641e20703a4850b5440500c4104980b14503007669000c2c41b544400da00ba54a11100c0c0d40702e00304c12050388000c0d40700456180c8100c099459030000e00005000308011216641407003001c03001c1c0441d085062080d1a00a80d441e4450402c0001410025881e600c2240c140710f507843c46086084c1216144c0181190504810783c00e814001c0550703200e80340c031000718004e02c01e0454240420300480341d001100c1030740d06216140002a00c02d882d0103241e40b00700122454145590754a10380a480c01d00317036500c0f1080322805c1502c1c082103c0101c06080301100d40201c9004a424070401c0070900403d9400d03c603401e040503503050080803082c188080c4003c54400c0c2d01f1103001d0307501c03400715503152850840300604515042224000000003001d0094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 964127526 1250 964126276 964126301
    0xf03050c040315090c180b0411030f1909060c030222080601090c141b16032409020307140f09011d2e05090f25142a0a080a03 55
    0x4081d00e4540c4140c440d94081b1080020103070352500420200c505081c040d004014a60039071203415400c0c001070034420103070000e1498034201e00c5900240c070b0303d0b503040c4c000c804905d400507001c00440404e420010302039030100d2079038000ca0340703122982c60200d04a600c06208940c00c58001d40016400c00708038801400d40c004400c1c0400596240c5800382c2e0261074001d040c13840030703034010b9000030041c411003d040140a02030082194042c0404201181c91445113001d01859102c405503d1503071128050000c021070b0748040c0d014401e0b000c012603591502c0e03661001c20b02040b590101c5400100e010040d004000740600700040180e420921500c07081c1207001508658000483e5503544040d44641e03039000c460741e0a885808080d00070420290511341d0300d083d0000134840310301400d40340c86080200e05110303007031180c81032024102c3c825250500c1185031606541008140725a9280e0302e0840f0000d1000d04600d401d604d1410fa4104018280001461400300340d00c03c05681c100301c08800c00707400510400c00100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 964128776 1250 964127526 964127543
    0x2040507020109150b0a081b041508060a0f0b0a080c06030a0b060721031a010c020a0b0a02030d060b030105031216150f14060312030a0e0d0f03050c04031509 69
    0xe10009001e40300d6120841d032521000145e600c3c400007041521692580801e0341c5400940c1403052030803c201456110940a44022880d041068801d8213003858a5118034181e0140105104601c41190000385400a030002306011140e4200d0400c0228031480c403030301d00d607540819903800e101d0410a0196607c031004840000f030484000020864070351046c04101e9161600c02c0c6540301005c1c40400c4043c1034040b51504015801c1c150119088000c2c10310400b50501c4030100784a4215521500d00c04060854452540e03210982024040c0da2a04401041c40384181003040100380b511011041c0d078100e840c0280204074041c0065110581ca41c081c50760a200425840e440c0d0011800c0420103070007013003000c2740000c2e2006480c0040c0080710a000660000032060b00240822590b00080b0070309003404c61100d5640d41c0c3c030346132004401044024050300c0103006020f02c81007155007041d945112072003a82c0b030903c41591076000f00c641f540b24501004222080d000c110b0550320515a0080c402c0901c036030800b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 964130026 1250 964128776 964128791
    0x20d031109011d041b05031902030c09120c040f0605120d170a020c060c070312050103230c0a0602150a050106050412050f0a060608012306010c1b09020d0b010e0d020405070201 77
    0x1a040170030102c40101d0046074000041c8078607810708492010321821000400c42c21400c00c01c1c1c07500254440c08034401d109001702c3c006140e4a10040c40507220132400148100084070030f40f54050040c0c281032003518030076294200078580c480c0022980c1c011030301d0550382c0c2c114441c0b400164560401070207411132085683c2400855590794082081c240641288000b0f03030344415003464000c00c030340d034000246280142000010400148901c1c488010f012620061300c100303000300c0d8420b524143d46044820790064200c2000a90755030081808855540c4158a50710250741d00882802554801c1c800d003000908100010441e0b4000c1307200da2050503105006403a040c00310303240c65914102c1d084d4015250160746220800c0011824031076044520058008441003150b880c10601520314020b0076070703040c0900300c071583c403c006908101040d03401c01d500d00701d0032594443d500d04000b5003114524040c0d051800386a03240540c0545426054924010050006807100e0b90a0202509015240a0966488408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 964131276 1250 964130026 964130051
    0x603061e05060f120f0109300c080d0e07180b032e022803180507090e2409011404080d150510020a1109130f03050f0a020d031109011d04 60
    0x1580300d415004105c0303040403141e1075000201000440c510044039a880703443d00d88c201038010034002840c64001e02d84a07250032030090144080d105500c1e40c900355016651001c15075290301c45501e51030b9290f550381044062680800d01d50340d540da4a662906040400410925400c0001351b07540380c3c000000b40c05414603220342e101c003d00044c050800c19008501d0207115600036418030a4110003500300800d403043c0b001d01e03150765031211000d006100c2c08680340c12400c0052501000400300d1440508022946103000d11500d124038181552407010a50a0003041070288402c0303165140142d400c07100c0386140440e441000c20007000c03210f141c50a80c800c80c0030001800e80d1144500c0940c0c0207690090001c00b11549840411402c0c1c490300e00b4440c480c81c0050002d0310469400004802d6444400c0131081c1c030403414161030318010041c000b10b54440004000300c81503408214100850199207050040b80013a01040301140241c0800b54001034140c0c512500c4880002140b036922000540001401225200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 964132526 1250 964131276 964131281
    0x902031b0301061d150d020d02040b030702032d0a18050a0b0d110a0507021009090911120c030613140601060302070308010e01080309130f0603061e05060f120f01 71
    0x28002d0b00422050701d000c140f140c03111031320322509090803981d002d0710100e08100b004460248026144d0107550100c1c0840c008a100c0d8100e82c064860460b46503103900d0308240003941c0703071b0001c4495164080d4071b08000034152440c0c4603001110480486e25400c00c2041da00c211840c05001210a28041c210030340003030b56842e4001101c01428008074078070399680480d504141558864082180f908030704109055071030368800c0c103441490f64101c0f0740c0000c10726290012035000301540c001817040c506d0300521204100f0f041c20903005c2c402059903c4004001c01800854642d090b030701405030160030103070009103166010680011094070607540c1b1b0101c42ca80100b520700c3c14000745c0020340860b90000d0b006050540101940740182680000181c1030347c107100940c2e4a900481940c1ca004142c0d071040c180704880c107074000d180d40b0030044004001150303890030440054046030340c1903041c1002e9640045d21858460080d00c0c0300d900301601080b000c9008005218484010702281803c43c020445007402c2e0840030b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 964133776 1250 964132526 964132529
    0xc08070f14010b2112090d050106140a090b0d0b1b0f03090c0307060912080f0a120e150412050c0a0308060a0b0301320a0303080405011103010f0902031b0301 69
    0x200c000259644069090281d0804490084c3c68031400c0004640c401d020f000451080e107201d400c40240d00c0340080300c0410b05142c18a40010074a500f41040071039961ba07100b0032100d01c44000c0719008070303403562035500c2e804a50f5a54041034121a42c40f46000c086108008416001003601c0c0b8143d0002083c02d000380b020707821a20345034000901c00420700413119010030251100d00c4040300038022042c81c150016021403854404c454010710003001150a20041c00165550007040c940c540b60794130182140107000665100b070413100d43d454030600b44e013605c0c400200240e1240c61841e50002c0d40e03c40c1d4807031007001889107001c1c00401401308103c071401d08007400380042e4188641c440c000141003810030007101c142c41e60407070030300141301b0300041020000e448484c4142032958044209629490a030980f8001c16290b64240c10002d010400801c069000840b148554001d40003040055102c07495401c907840203205c0c04001c3c034400b01c5c05004584040d40116001400402e07200244807644e590608190401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 964135026 1250 964133776 964133813
    0x608031e04080d0509130e061602031b0c01030c02010b012001060b040e0109060e04020108070e0d0212070306050c161502120a05010302040b0925120908041707060c08070f 75
    0xc543c00d90075040c00c1210401c406e240034000d00180c1d0320003a1040d541c1c9001481c40c607111070941d096034070190092084428000030500000b040074001c4030001d070364950801c0100d00091600054220780d03441071258956421059480307420381c01c100e08070080d5a1082d125010400c1d507031100c0c00a01c05c002c80e8024001090314810030902c540c50014480122032080d44441c034150004010080140c0e0302c143c41e29844002406c0110742c10101d0300c00b040d00c0d4100080b00a41000480802c680700942c0043c1460031a842140180039030b1352041031710605030045001400b40d420360721403403c0c002654035680700f400c09030b00a001410042c02c041c1c4800c1c0300e10260b03011545c1e155240c005209604180c002c91318002e13010303030b503090740c2d414803a4049103804a04480b82c044140d20f2500c00da030300c83c03052a14004105100b6410303c05103240b42008540e640c024401d41551440e0a54400880000803c800b001c41d0040d45417200e01c0b0301c840d144c029082d4808601103540f001d40d042520000b8140c02c50141c501c040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 964136276 1250 964135026 964135037
    0x16170f041e0b010b03090a12020303181605040c110d090527060f010509031002190f0504140a030204090605060307060e0616060b06070b070f030608031e04080d 70
    0x102800c0595104040e0310710707038440c140038148210202e41e1000c0401e04440e482c0680d01c0c0c1d2642c074511040c0c148011010b00a02c0b04110f03c40d150400c41e4000051402140035040c0500a03000b409591a980c074a00082140234004c522000c02ca24500395000020100e014288461341d10aaa84030703a00300010301941e4404a020014144400e0500b03518210ba070049980c141c0441401c0b018810003080c00041205104110162001c20b082c3d205d4815207800c804040c00300d540703012070020403601a400c4804844d040803803c2103900342d12803042c900a0b0001c81e42d919203d00d02410110341d4014030155081e203d0700150440d200100689840c030607290003500840000034942400c4041504010080d40017000b00154103046100d555180701c200c91401280038240307900c01c1c4c502e02d07080300a840c4030034015a00c8031002ca203000c00e0009541c8010720503c0d042e13692100d0440701600c1a02161103d0180640560091028000302d08460303644502003110490501e040513980c1c00090710309416041068000741 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 964137526 1250 964136276 964136281
    0x90a03050f063106062102091b03070503041b0b0d0507050f090d021302030c130e070f08090c03031b060901180f030309060204350616170f 61
    0x4040c4900c0d90401041154107480703003c40031200b00350303801c15000b08a1584a900c1071408200c401d40c86140284610600d011441d5980c0007020442d186a003070580c0104034200020302084041c2218400c80c2c4074a00d003250a64540300002c542c9508000e000301d690306c6048824040410196050780001c2a91881c02560f17003801103d6103040d42d001400d4101400802e10100710000c0d000300c1a543c81c1581035035002c22013081400002c50525802d9810768540780f000041c44079080b015002000c00d400c882002039907036076031407012401d012001c82d0b0305000501000c2c403005403144180201d9410841040031a20000e1030000000c1c00c5903c800044030146104500070f0904103010700c0911303440b505050007004039255180303084428031043c600c014a60105500ca840c109402a408201c005400280031900c558980c40f4031942254070078038981c55000511700600d58541902500d0319603000030b0010784400d0f280c40c180c072046000c00b84040c5040c8005c0410781d90361112402c1c0620b100701d00c074044000b60760 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 964138776 1250 964137526 964137553
    0x16020618010e030c031213180e0714010504090e030702040c02060a0b1c0303110f451e180403090b0a080f0403051c0c0e0f0a1a090a0305 60
    0xc902c00700103000e508500320369802c541c0c010656509202c40c0040896441ca08000d4100145620350016203043c5240c100510b10603100d42c0c05200096041001c5400c0d0315140d52101c04014461441d90780020010407041c0084e001981000001075610b0089a00b000016030002d0300307444a0300d01c0c3c900180d10520800c10b000b403650040000060f01036a00742e45074214054000034102000d40080c050603103500940c50311400720012a4408401e1000c01e688503c041c50440e04800841d040c0503c1400c8002c1e01e0225008a800304442e04a402641360280885100f00f03110701c640c000c0c0070241080f07503100400311454480702036608805101c80c0341d0200070720302468003400005190f040100c5000e414400c0c510115000040d0302d40000411515011a0b643c61400315090b12074080550f441e821a01d112014844042c0c00456001190b500e5120011815000b80301c4040e1040240652182d6612010088007140c05000e1010602c1030188901d8403180c01e02056052034035a0044803d54404030851400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 964140026 1250 964138776 964138787
    0x10c1218090c05070b10030f20060f121012052b0512061302070809010e01020c0303090f040b0418062708030702071e05030f0102040b07081602061801 66
    0x5016400c1e41040b804030302c0c0c44002c040c2e00548400401c0c1d090b440c400b10750108468103110005640c031a07030880040c5d5071443c000080f03920444244001201104d2941038600e8140140d40e5403600110009051102104100064000181c5814905c45400802040d4450b02211800009016000520b00b40c460465000e040382520030144110490101c00c2000040d84078040b40c003601488615528551240390010b019002e4100038040030130f1002840200704100c80707020b4800071000b622409040c0044034010b81c1c803512030726591685038004010060706460000fa0600c400d060207440021a0910400800d04980410003041e4030b01c01c00702030350740c00c01c425406124000c44040201100701d2000c80b01e00c054485d8429801081184040001941203101700586401404c4c0710301c1e40d401c00b0396602c0010780d00000e80c0c0502c500030300980509000d91001402143d04417100faa981500d4501e0988404010390480307589440d8040220300d000700960ba07820040e01040900c0c1048907566050700001400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 964141276 1250 964140026 964140029
    0x90901080115180f02130e090d050d0c031b02071a09030309040c030b03100c090e0c09280f0e01080d120c05071a040308011e1202010c1218 61
    0x80303030781060412a40280c01070040811903030855440041142c40c82c8a4001501c4100c02e081183c1c0d102086913000308004404107000c43d04000c06000d0a6125400425100c440b4041c1a80104004020000800ca1103620030b400c00700343da140000301c16001c2c40825201103008040390f00140c2c0010301c01d002c0c03410441005050f003440c0442c461f1505030b003403010984030300840340c03100d100702da40b2282c0c505007034029003140b02030784401001d64000300424941e4200410302882c035a4005059001d000c0b038041285803945000700317402c054581c00d01c01803204200d40030740036500c401202c0c510301001507481c0b800e04078480040c2444044070080542012010000417070164004003403580000e0b584083c0640006c192200007034800300215025403003803015100e030310455000500c411a016aa40d640c10310100189000d14806c3c0e8a40032240d90320b00500112202e02c000075219610100320402507180300c13101c002d81f140e00c107060008514000e0785500f80124440c3c0300c11000308829102405130002d21010040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 964142526 1250 964141276 964141289
    0xa02030f0108070f06050a14031303091505071b080d0f0221032a181c1e03090b0c010c0e061305010c11030d11070509060d020103090c1a090901 63
    0x640790a104c8441c106882c41240b003480000100c5032403403403141c140144503800030300580d0b40e03e052802621800d000390341d009a00040c108100400c0292000303030304110111169480c24148405030310392013011080f117441a0070000001c60005241304003408912440455500c440c1c160a84c4840060700744182d030664000d008600f24812541c840f01d031000c1c1c036042002d0281e0340c801264041c0242c200030b04200703580e52032510302282003e40c003070040c2d103038600001d419034080021901c10400c080220000810081035091480752850700003022190801e82c1c07501915054514661b180e0000807540c1c85005010307400e9440d4401e101c0748980166166100f031000f5118240341c018003000502c049400c80c05254100841038903000240085060342d000041c50080039076022a109e154042c103402c001c43d161103240d009030303040050280741c40000d003482600d000d00240b80c1c50080d43e0044001300702d0074004031803c507000300c0041460b0380d100c1e011b0310304210708070b400641d0b0b64544000c01c007220f40705a0103603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 964143776 1250 964142526 964142533
    0x50a1706120a0f03032a050903100e011a0a0b0a05070f06050f06033d060314010207030909020403110f06070b0117150c2a0307060605090f0601140d11030a02030f0108 73
    0x15000d048280701c40c108120194035045441f9023240c40028241581104980c0042d810301400c0b407040348041d400301d140d103c140079205075502c044009000845820b441401e6200806002c00c1c02214020001450480d2245001e2014081e80d0790760034003180c01c01e80300015452429410004542020049415503050030b041540c4802001c000002024981c9180a1140020072110001d50f07015600031402450303004032444c00c201c01e0405940e000350018403040e00015032196001802c3c001a00c211015250482c042c031100000c0282132001c107030510728900f600101c04000e00c0001c200034055481c0605130320741105000c1120884858907040740e400d82000060844414400049a407000301c850b41b00c110900700f541a20300200044680c0c101d141da00d040c6003c00a17400c4200521a4080c400380c40b81103d10799102e4482c1d800400d10414106c0350035000c035144840500c3c1c90510b10010384115108a20041010150705e000b002407600f0035160b01c00030640200c1444007030030f075521209000d0555040103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 964145026 1250 964143776 964143821
    0x150813021e010e12031218060a0515060703030608010507050c0a1502040e01090506040c0e030a02010c02030709020a050c010c1e08070203040b0403030c12050a1706120a0f0303 77
    0x14400c07100c422003412020740d1861001070207034001c1d240503d01c00c100809020500041c0c40740503480c0e911030740f511042c054900d4006032012502c503000d800e60303078200c0004100907a04c415520005142c05004c0ca006405102080040e60b40c1d61320062800510a6402050682c0742001c00c44c01c1d25006002c290900105022104c8a00c500080404049800007110f091015000706140e00910503a0021810340c03100b54000316458042d90000c81c0109403e640409c0040c20050003200d44041410792030b9410b0b0095454800550b00c20b03101401064001416640e1711503030303402c0c1c0301c040344d01c410281c1000c600080f40e1210040c1d006c0c4030341e400c00d80c00c0e401c2103c03100c1220745810b150560881c1842092181001c0440e000920070401c0c0c130050001c801e5010b90704c03a220305020749450404641207a070000c808014030900362040043d13494080c499100c4c0810844410381000b010300000300380c59001072607035205007a0082c6c1000b001050900400ca03207070240d0500d08005055420740300c42d4203a008040c150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 964146276 1250 964145026 964145029
    0x7151401050a05240f030108070e0906040b070806011205130c0801050f16030b0904140f0106051c030507020a0303111506060a0309032610120f060e07090615081302 72
    0x2840501240002105843d200e11244c100daa64041c0202e05900c0e14030110010640400008500064440311f294141c01036036a00041a6540422507004144c4c1a0b030f50b000c614100c1c0501c0344907170000707414100120f801000708a55030440343c044440440110451110905011040702400081d100c020003d1104e407030a2400502c1d65440584a104620b03902010000c502d07219a0081d0003a180c004d000300030f241403d0410143e0f5142d4070350300c1c60b40380c02200070b0080c4010051081c0822203030090541c00044810031142c064402c401282901805070030000d00c1d005036138046414000e10f21a840c2d0616150305144941d1600070201344001c46645c0000601603140d03508000d956a0406d14030b0041741c07100d5145004c60f0400265001040f9402e1000028035010b20030f010741500c141e103024014182ca603904c080c91101180c00c05409489100703005c0d0360f14041849500000d401c0d8106034201c0309034a035540820001c96125500000b04408640800061140e00401e604e8000c000383c005400f100500342c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 964147526 1250 964146276 964146289
    0x5031e09091b0c06090a030311031005010f2105041a15040203062e030b01020c01090e1f03140606010c0218071e08160f1403090307151401050a05 64
    0x402d01124500c0394400e807080111004211000515004159100703400c282d41180e80d500c1034000106e000c0f0741040c642d26981558032040c0c0c5c0c0715200c008001c8038140d19020040d6004848050443c041041001c503104440c0d00d545003d81e80ca158051000410780b400d41040d02403203d80c400c020365903440100501c1881c00b43c02c000505900011100182d0b280c403010001030785086458903484c165001d40d0030070807881c00340500700410300080d61000d008000303585004a032624201c3c0040383c04030316902402c1c480e000149020a81c00040c070b005944200245000e20108401e0a03402211070b010011001c0c0204807092004942003403081c03e015403071030781550028004419001c40300301680b12900025200031b1290740705d00002145038200f200c07045c12404008017041001c41d040d011841401110b2400f0314401d007140c5078a240c0940c0c0d0a850035000248a10040e030000d0040483d906c001d00c1080d01242031b16041d9000e903a02c1070030001e10110945007109083e42d05920051181d40544010003442d00da40c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 964148776 1250 964147526 964147531
    0x5070e060d030503010603150312030504110639121c0b0f042d09050105012c1b0a09031101020d0e120312100302120319030504050c04050405031e0909 66
    0x90034040341880d00d44043c0e8100c40c03081c3d42702030329001810550060180d05580440e0065015403421000d0002c0e502c00d10055110750752040070036100301000703132070035480010010400c1d01a0341f51810700c50f02e122000a00d46000110000c2a00340009105540341c920390803035010615070018180305541c00d00d4001112410b4904055010325281e50080803458001d48400300c00541030301d0b062000003045896840200345000c2c0072610784d0310300800440c010044200b10804200102941410441108070b40c0003510b6000d050b500502d1502e11032080e5001142c0b005d031404d29102d41e65005110302d1030901301c0050b201c00c0b0110313042d504003400740c400c0b0950000d04400103100c1541e003200510742c540415441c5100d00402071507003411210900038010104500001268021286110401c0501d40398076100e00c00c8044500203801d1500c0513449281c00f03600981d905c01d02030001d59000d03040781d001160039240c01b15401c41d0355400c006a0101c2c403004c03107480140c2290711800b41c2800d20001e01e02144106802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 964150026 1250 964148776 964148789
    0xf0915261e070c0605090606100509090109180605160f0c020a0b03270c1002150f06010903051b0a1203090e0a1512030e060c03030f06010302130305070e060d03050301 73
    0x1240006401c030343c05036662004503680003004010500e054503445441c1d00d810b1769180d11415124040680c4588a081640d024000040012031164a4045072070018120341c0c03006840e603444000182c01095561149901c500c66082081b1030841072028024000324000c080c242c1409240700f07841c1e0140e15603d4143c0300b41e516041e0001c1d601c1d1070b41c840c01e88032403170507da4151000c200d04100b80a0210040385031503440b00243c81e000b500344400141a61141840a060b8080820340c0780000c28500d0381c002c419822910605004924545a85503141802642d08401c110104070300542141c501300840f42c10001c11402c000300900d42001d540c020012051403080a0030341c0580004541650101d0303010311003d104000211803035980e1500444079107283e9150a6011a90b03500c8912494100381d070490310a00c174400003440c6140c0c0c440030040072010f005001079040690070320503809840390800b0404083e500031402041498907240201d501407000401e0b040c000c00c003030042c040010740c221055a0540342c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 964151276 1250 964150026 964150081
    0xc150c0c11131a09071b24060b090f1c080318030a020609010b0105040f03020402030403021501271b080c09060a08150a030507060f091526 61
    0x1805000a01405044403060b8816031501400310034080d0602c1d40b181c03081005503416242951000002d450030740348400c0ca001e425007113500d11800500c42c00d240081c1d00c9644440002c0028003480c41000700e551541107060a2400062661014903016804410800e01141ca040c403444143c1da540741040d44000c0c0060110f000031001c00c5140d040410184c604104800c112a00d803230103014000c3d981c110644100c0d0845d40380c4280084035500c144215020344064101124280e880d50342804002d503c020005e60071405110720401d40154820304542c000c212088909400108000b1640051128140340001140c5071101c1c1001d1401c11042c4110b484402d400c021301240e0b02d0314140b981608c1003105c901e42c4000d0000d10300b0070341d50b000105140201c5120b240ca0b4244100d41c41802180c050740c1c003000e003090340700700c408101d0544900d0348695100c0591400c00d00b1107549100040103800082c8101c3c012908580b80c05102e20203041c1d080c101d440041e03001d9080d5084c84054140503000c0070661105411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 964152526 1250 964151276 964151303
    0x5120105090d05160602030a051807030209040f031e030e070806130209040201090806040804090501050306040f0602090112060801200415050304140f0d260c1b06070c150c0c 76
    0x4882c1c40c00018145c1c00441c2996603180c100802c40045c88102c80005140c15240310540020900185150036260b01030704145c8513031115205d03400101d030503500480810070810010f118011417a2140070103980310340c5020920a00801101d801c100f0980c205000543c05101004422520f02c5000e0f029190103448048031034075a4001200d0520f415007141900740300c1c03402404100004200288110741083c0c01c100000d90b07c8004250f280e903c01e40b00a0007611140a1600126406900511040c2ca0505009619400e0883da04003580c0859000d80c0090355521004100781d00062200705818516000441c50141055a02b070f41110601008004000021000900b00800c40d03905499a0400fa812910142440701c0101e0359111141110b1f0005020303075985081259641c0d94054146030312070003e5050366540c000c5080c064110360411005500814a404c00129007840304c00e0050205036a503585000407810921488155980721000341440c146200c0c0c0c225038006240d00d0480e5001030b1603c02103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 964153776 1250 964152526 964152547
    0x140103060b01230702030c1005030a05180a05030c060721050c0405040203091606020309030a02011b081b0705010c0c0e041b060c02120c010806152205120105090d05 72
    0x900814680051410403c0c1a01d91540041015003a5a8401c4003100c8950558206000c0324610701810368001c140c00303001080c03095a0f03d40116510000ca012584039604454052501c1e080000400b905c2c1a000003640c060030820030301c241588490382e070904030001c000720444055040c070b81480c01c0241030750341e00c081141c001280d42110020840144150f461381082403405440d01e00301c100070121481481d81c009501c1b07001000f502c0380081d00801074900d845035074005407940f000c1101ca0315581c1440102c0c0c180050320a0018116410a044030703035a400f200345508503e452080e0308040e0501601450190020f8103840c15070080da0084c80d400c17105500c1b50715184406104003441059582004800860743c1513110080085241c02103584090580000c01459110010008520b00007031390400080c4007400c0c02a840000b05400840351450481100c0c401c0d03403201030302c075103900c820074203510204100c2c03904c84140c02154080384020005801c164445580d94000120044180103011510031202c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 964155026 1250 964153776 964153787
    0x604120501110f0a03051b04090e030c030c0303091506210a24060504050f075a09090c1112030103140604080a05070f02041d070801140103060b01 64
    0x101e4415490254030f8048141004000d50444d204107400245080e00042500b14a191580000900c0980c12483e09080690a0b00504611180016903100800c1040d4031040d0810080001b0030f540d0300956101e0070034010312400d180303015600ba86c58941070010b00c07110307036904624024004203060001c031b44031250164403800c00b402988058000d8172080b030440014000c14460342051201ea0b070003004050b8980302000200d407402d60700c80800605e45000190458000d90300e094810501c1d08801191414107041c084519010144000348008540840d8103400c4181080c0488500c03140c0000981c40b1001c44000d0402641b4403e4444564542102041c001c0c05401c0303809014002805441950b00c4103103056182e40e00a11080351404065011900001d00118000d0f00503035000f20094506002080216030355000120140d8080070074800610041c1e0f1944070717071644031890012064240300288071560070450035520001c0142d040410012000d10107505542c103490740040c0010303a021490004850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 964156276 1250 964155026 964155041
    0x4031e09051f0207050307140d020301021c140f06060a2f060f07020a081c06050d051005070e03150a090507180e010213180b06180913020604120501 65
    0x1084040603100c000701e5030444961502e107661607004c41e00d00955490505070303030340b020384a030020b414010100c004191601c07007a04803404e800100090304180d00d070504d1a0401c0030110801e154a41d40741c06440d00b99110071001903114441a4594009142510100d509482084195003c12841d50000104291984070802c5d03001c00e0f95001c078588407024500300385e40f01400d82d8030103a0b00f1310310b00000711401e20014405498640c003c0d003903030a100450769800307030901030f007412100f461b511707154085819202c908510100070301800c000c2c01d8041045000b40101c50300901600d0030410b101451a05a460001e4181c08107071480c4070400c3d80b581c0e140c0589008000c3e4050003012401100000940d102241d0304801100d0a0460100001414100ca00d4200d204449070800318451444c010011221480169510341043d14008203414840710000340c01a80b20191811080d0205100d400003810045005540b100130101103c034a000d2a400180240c0201d1156500c4040010200810000290015003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 964157526 1250 964156276 964156279
    0x10327050106032319080a080c0403051606080a091106070203010b04050403020c09370213060917160b0c0a0f0b0414010b090c09010c080f041d04031e0905 68
    0x9010708001d280c81d5000200704d6829420512520f000030440400c8103600340c1889600000c21854036905000551701d0340320050801305020b60502002010810600a1201c0c2100d8a41c0c00110a814003402415148000d00325a4000d8a01081c400014080c0c0304d803850302d04030071201d0310380310704007440000d001d0010300607065081810034007840304058001a89502910044645100a540364402c114155409903640d0140c080c42803407041e80355a00e4038107011251003030b110240c035003841d0200c510050200341c1d0143c0001221407004010710070340c003440d28140030384d1f2101509401c1c2005203c0380d00700280d03015000300c102d400900241040b40401c0856000d070b5005000440501c0e0500f0480b0310800110350a030f40c94034401c00704080d4454103100e19070603001700420180320b684441080c501c0f150841d010541c103000003061014041000d08005e880c86141941d0304a660b103082850440c501031020001004048620040c0300020b9088551b801c801c80d810564950007040c01c2a04580c821259030046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 964158776 1250 964157526 964157543
    0xb070506010f050613050108130b070801060e030706020a110f0901080a03140406081501031d030301030c05060f03011208040b07110102070f0605040614040504050c04060e01032705010603 82
    0x40400401041080c101c1d584007140703403219079035282440b00078030078400542d52842402d8030034405913010b4440940c002c80c203030007446644127a41da1504100306d400d480e44004603a14070300400005030700c42d400d407007004400d4010340038040c07514601958509541900902c0b02080003110079403502d030b0110003028900024207100c01965100e0b0020340f1a9101c0c4000c2d030004445092084400862004840840c9c005a8a20040307030384120301c03422880c8081d02828101511510602950201c200c00e01440c201100050760b42d03545946406207104005601040c00380000388180050302c82c65205681c1122900b0302e0341d00c6101020f01d8841910310481d000444d0345e0303202140d0201031003800e0601c100d140070301f80c086408168640700c042041008501c00d09001a40402c002d004c0140310301c1d850144e501c2800d584c40d0405031503c00007030070b503003040341c0c2500c1d2003d0100d0204041c1e64410440c5090000078202040b40001c0d0b16542150061a045803403000540718411908105095015100858102428 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 964160026 1250 964158776 964158787
    0x70503030c281a0915041a070e0a2c0f070c05031c02122505071104061e060905100f0e150301080c150a0c020a0b0408241b030c040b 58
    0x3c200c2109020360300500c1c58412406000740745001c0e208118003c9400503a041182c1c6c003490400c18a9034001401d07482008031078209080b0ba41c0328a1404e102074100101d50654039007080c620900380f010000410a17182550206000082080c140c6885d0003651610340000e100b012418034030700c0c510465260140c8010804942e02c0c3c0502c00b94080c1500d560300c2c1100341c0d1240c4401380010784029a03200e5010014013051404c00c026401203004000d458400c1042e00700c0001c0a800140885899500c072002540018860700c00c001900c980e40c074040d1010f03043c030808036402c1002295208298a9102051104081042a60703501a0f554110134000c000c00c004441134280404000c0c07034000f803003182c40d54451080d10085501c0d06508041f250801d1140c00390800201070b00403146400c2041007a82c10464418002c1050800c0c0001803010b4020300c4010120b2002c900d5543c030511031107000012003001034000307000040c0d251801e88242c1d00e139403d15540c1c07217848a0008400324800c0354050360242a00056 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 964161276 1250 964160026 964160063
    0x708251709010807030902130216080403050a030806120c3007050f0102011e091703010608090706030b06090d0c0f06120f050103171602150309070503030c28 69
    0x405204000f80d0710000261035084003902554071801c0001d500041400821284802c0303980980084420b08415401080d050346030f05550780e006401c08c1e540382d0083c0e1546414141c021000c1d9070006019540701e5407001241001540701d12052909510407a03d4007203102c82e90b41080525409082064204100d0140144205684014511070369015100280e10b501c0340f0343c0184282c2c5081e10041d00b0083c82c00e034103d03e400005100c8140c04841c11901440000040d84a0070055400b034216500c4000d218104000003d140c0700c90b80d4003031001c140c01d154115100d43c6455069401240c419950469042c000d494119800505604000d0700da50380c28400241c50344d8000542102154a03031010083c0404420002055031000d002c05000b0a0100c1c130b00400c0400b03000c000781800004401d1740d01240c4040c0d8001080c4180601c1c1000b14510040b00307101030754800f400314100420044008601c0d0403d080025a200c4600d2120040c035a90204003144110700590480160740d9030144032a00510300086 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 964162526 1250 964161276 964161323
    0x150d0c090b0303190f021c0f080903160f06062108091201051302012a081803030406030e1b030d0507030e03071d09120d090221030d0b0303070825 64
    0x4950070b00507c00c0c641200c2000303000d40840c0802141960380c7c00b40e82014913a0640701c2580141c8040c949100c204104108545c4050060075007a2041c072a980020125062010030b4580d60340010b03803c41840c1074603502e40c0d002c011f2000041c40d400441e00303849503490000111b880c162100184515401e0000f04030f42c026100c0c0035148040c1c400d0303da82840032a044101100b45100001c3c0b00c00c010704448101c00465941c4000c0c004035100440c42ca280c000b0088042030450b04264880404070791103021340d600c1e40f0000d0041c0c3e80d0806202103003202c014011800203540303007044a00c6d0380920000040d0031080c184205d041c81081c00022b411103680a07981c600343d101018158007640c071000c8650020030015200403034407d00700080d80788040d0408010364107085c020004000c0890b80b0903144203e040c82e07006908050111403402801464071420391840e088183c60008608611a07042000030800103010441600c20725110054580006510424011400080500b010b46500340ca050308004400300135 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 964163776 1250 964162526 964162547
    0x1e0a030e041401240908150c0c3013060302030c0708030108060a1b17220f06062907080c1507030c0f02060412091d150d0c090b030319 59
    0x3603510206000c0d0004e401c07600219280644000c50700200011450340c140c2e50a4140c000c850110034a280c00ba102c005203142ca80c1d20851080800b000051144208061b10280c4c101850010301a070300d019035500c500310b1030000c0c130700401d014140d0200111b800c0b00012000d0350b21300e81c1e10005060fa84d503100c15400e41d80303140486841500c01e040080450209e1410b00354021b20221a4642d49054412400e889410143c018455540003041240f0902034101c400b204000b903034040c080e15452207200d801d0010035541503812041c0e2a29070040d40703100d503008151205000420982c0c8407070702c400c0c26103422640b41c414040428101c0c441d0185009035418030201050040500b510b04001949240c04c0c181d6141d0000300e41080983c11000c0000c01082c000b002e130303808a11151400c04252a2208180020f6005101d016000c03401400d0400102044040f4020400ea0302210f030302050000c9a61a10b074020320364003843d054280c850f040b00f0b200341c800704103a480b082d602007003111141110800050584003036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 964165026 1250 964163776 964163819
    0x5121909031215030804090c020a06091124040920030f150f100f03240608090705102a0f050c12031e0c120c1e0a030e041401 55
    0x100600040510350407031000741105d501c03190350345c101762400d1310600c002d0203008070400540c02003000c00fa000801a2207840000342c840c0c0083d030040c5480c802449100c04801a0400c0007164070b581041050800d482510212410440042000480e0b4080c0300d500300e03c201e0a406040d540401804595900c2c0d80b4520711888081404422400c021400c014850f0500f004041e08500c407985040030452095032049201c81d100d040105010a200078280c20035284c0c58003414061701c1220041c000d8a5201c2e0303900790040c600d003004040240c01c0c640040e110394801d008075014020072100c510f1003480350610803034107603a810400410549507810060310120300e1070022603c5001e0518101c0d041e28141880d10950860b11008605041489101102480409114012803c3c0600c10302c000c02c071080000c200c0401d0004195501c603405040b1482c60030218200c0300780d0390122154400c02c000000103281441c2034141c17500204a10400020500818600183c5403502c0c10010010403002c46000705804c07075181 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 964166276 1250 964165026 964165031
    0x27030b07081e0f15041e0c0f0201050609070c0c1806050909011404060b030a0f080c0d090324020415020a02012c0d051603050601080601090c051219090312 68
    0x40d00d0716007648840d0100d4041031480d50364000b2400f44040285807420707142e00038000054100380712150350312000c2686c20700140152170b61220a6404c0d4404541640803c1500081c400c3d030030f19100060224100130070010030483c0000300c0304140400002050011301c8500f0504407458264001c000240c15503000b068000c1e0b04610114045000c1403007080d2440c011030040e46490f0b11182c0d200b0703018100d89120b4690604c0798002c824089002e8404c5203040502ca003192590b56198041401d040c155130b44616030601400350003c002044182041d1062344545a826031180c051200d6603d009000d13a8003c28001caa002d2034030103040343c0000c3d54081a5001362210145a007415103001d000707140c0341000c0d051080c101004280c4500b803070494207442d0380c0b2500640d00c06602e03004d419503103a000d60380140c443e58094001088802c4003070006038007501c0550030500c850b03581c082002e800c0303110303141d201c0500320150b20000d10740380d0581c80307203034003040070741c9800d200e00e000340d040040c2500d01c0b9241d0f140b070162 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 964167526 1250 964166276 964166311
    0x209010315140105030c190b1b010e030a050d020a03110a05070606150516060f05091506030a0f0f11060414150406020c15040503120301090f0b0127030b0708 69
    0x9010569090413504002c009001000840d07050000008071243c02009100c00b880c4041040842075014144800e0b03402c0d04055030301d02006405081d10b65842c512259a0810050100b1103580201100d20400c54450013607501d03040e00400300c0c020300703010b85c1c007007110280401d00361111544040148819806540140410703a290468003002c4031404410310b010a0041024026191200341807115a0b0300807880000c0305a205260341080d11400c070350301e10841c1c101e5024090196100c00b501604070f10281c0040041e1000c40d41c0f00c003280165008040c0ad05240390b1b0041040010310244070016220140180d03484669920341c40400da140d0300030301d134031605034071018110404001c401c0e03a088404c1c95000f032107203000f000180142c500e4000500c40d000340c01044041525202000307820013001c02c14486070340e290b1410402034120340300f0605081d82181004186d02c000daa1040486a00d02440d00441c01c0908581500d4200c41c0000d901c01800560f20f14100718150784c024558510584440103080d1410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 964168776 1250 964167526 964167551
    0x60c0b150108060d06020f04140a0b0708030a023006010219080f1c0c080601030c031a01111005011d071404090c090909060603060b0d0201050403080f070209010315 72
    0x540d1411040c9002441d1040080c0d21468041108801c0380e01a1000603e0f15120000d80c10031a480307030300b00740750445031042440c2c09801c0001c882402071950f40881810010f0540e04d824051101500c0e0000e4260041030b00c941542c4120041c0050404030002c09400d000c4030302d07006210341c10489285025028114039040c6443c0100341070b10080381d120b50500d2034030811426100700c07034212080e081910400c030030030380181c2412445502c4203c84244c03205a41d92400000040954880740c0c1104c0425060044004d600840703c500505840030900344401d051204030311461070300f040100b001070703813130304010001502c0185c89029503100c45441c2003103885566910300035900c011003494403000440d41007200700881c03c0640c0c00009000390502d0800501036460328007009980d46110142c900554074941001002a40c0c4250320303500030262150b148038540c940010344140550710000d8215140000d4514403007080e03034220380300940c0c02850741400b07503101e0034418000c0754180300d060100380c9403102c400c952 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 964170026 1250 964168776 964168801
    0x150c0606080111121302190807060504080d03090510020f040906080f1902010c02180703050a0b060406080c09041506110313120512030c180a060c17090a060c0b 70
    0x20382d043d918003103190410000301d0000403c4001c0c50b80f1501c0d2484e50315038005940340440c2d88120700440d40b09200403810901054107240c1d550b44250280310042004000b480000f188800b42c1d01c0441c200000c0a1003941003050900300b528003c900b81e588000350051b010001c00000d01b09503250714004208098030750b04c242d035483d0108142c1980795442070300f02501d03e462450030200803d1041c503042d00404080e41c04100c5141e500f4032644c0f06910418100003a0941c1446500d6100708514070034819509114045400b80c07080e40138200411138100d000408c0901e4410458800c41d00c0a8030411a202d802211a40c0074a00390241d20000f0b24080d802d403050007000000e0b2120444c0100c1854240ca01e0130b0740c21196040e1424049606019071080440400f640b00090752007145102c5500740d075400a1a1460042c200307089100303204042e0301c181401041d41c00300c42d50320b0301c592110ba03090b44034147c6003040030039005e00100158003802d422001315055500001c035101b09071050001726541c0c2c69041c12600e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 964171276 1250 964170026 964170041
    0xf061225031b06090b1602040f0507080f16050c072610090804050f0f0307080d020708060f010e09030706090f060501150f0f05041a03100e010e06040b0a150c06060801 73
    0x211402d509020700d17031802c001401d01041550040001c00c00c0c07075000c07909503610040e507003c40c40e03500d00421846a42110f1100d90110081008001520308402c0280010302540705000c10070602041149a668003080544068800d20764584d0301801c814068101d40c04105084c58071a000304224081680010700540312802d41c8200ca03281054180030921404112809250340d00084940580419403400e128200140c0241809000754203000c20004e4a401601e9100900e070768030550420241044c0c00c060329056960340b9507105c240b921030604d1703145540030300c15001d4901c5203811018001c20074000e00900e081403040800744403a83c3d03180040d0f5400780c10525680c0c0030400c480180710ba0f5030b200d10200f003000780c0d05041550402e40c40d1b41c0681801010551004900b83e000003e111000000c09400c0b070080896815280f4158100b02000003080c3c1c000d04031600880c2c0341d0041e107a1554512051300c0250007500c141d14003885285000610803428003009861881c03400e0300100f204101801100e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 964172526 1250 964171276 964171289
    0x1c060b070507060302090d0803180708120304020f01021e030d0f06031a06060c010906050402120102070f0b06130e0a0213021809060301020c0607021608060f061225031b 74
    0x2c01480c0c900f081d400f940c130000803981c0c0310009691450008002401450152024011009140c051601c041d803904000f40c0000002d6030043c45204203260101c8222940941d05440c418000d03402c19005031b260006405091480032140607800000751000000752540c1e221003030041c02280c000702c07002c008a500e43d000181444003940c00c00078400d0040410560003c0000e0201071404551342085401c6925048040300d001c4c1e200d009000652420303c80030700008280340e008515200141d43c0703d00d07440070919070003014a840c620008540e030769103058150803032004c00b0003800b1704c840c084651500c510398803104a100303101806c1c60540050721482aa196441c080040030008062102041301d01400105030315070541d002c000c00010b828051010500a00b01e1790020400d408030020410010340c15500020740b69802001005480d0640c001890741284042d918980e48248404605003895038040441d0f42d5042c14980001d4440f4000011004890151264410380c3e900103451111024540c030640f0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 964173776 1250 964172526 964172533
    0x30f100e04110a0506040b0d05061203091e1c122c03010603051002040302010816020a2003070311040609141611010603030e1c32031c060b0705 63
    0x14001410510301c02a0790300020043c408180c0c0d03500010f280e41d885034204055030f01c8042280100304c0380e035000740e98102c0001c0f6014121144280503803039807070240c08005841080d000980c003d00010401c0b50b81c0d000c010240c0054020720079090500020741051004945011030b051444a4082c414442030120901d030314030f40242c54040c0a90f00002c601c5182d040790380f555071864004001081044524294180c0d254007507121440d500024042200080c01014200f0302c0d400c1c1c0307e00080c0d02140403013030305901640d1100e0b6414045491013142408046194240c80f607402c001c420f11403040640462840b04460a000c0c00d915094000b095811041c02100a210345c100454141e100c140c201c804007144610780b0081c00e074120004542035030040d0b441500482c41c607480c800b0140c181007210340b0f128034030700e00c23403824949403070b42c03120602e030038400d04c0760b0002821142580041000c11032140c03041300003c0489450748100311030040302d942c001001b0358100d480c0040000b00030b80d5501c02d450f041078100c4042c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 964175026 1250 964173776 964173781
    0x6020403031d100f110a1b0510080a05040f0206070c05040e01060302030a0809010c0804180c08061c1b09290604091a060f070b070201051306180203060903030f100e 72
    0x68501c034804c0f541c08401e0085004071107454801c10071820310b582c1e010321000103102010210ba594590029003105018120040d06540f0307142c3c0010109070000323141d603000240b0b69180e0804c1500c91021070002544400d0002c0c29500780b241c4031280700207861044030100602c100856215017210001c4c80002c0d0107801a009002c042007402c030141220110604005c00700c82c1780c80c0d481207120391260704490041e03501240300f03908540daa8891141c40a0071403c2000017410640d000030b00310403403a1040f440d0400c18401c503608000102502d84d00c04244080c2c4408410b8036400c41c2d038047d04882800c00d54008030f01c14892090105038600038111803014200a181c60b080500343c902074a4440c0083e0080901881c9000031625101d0042a41b0320002c25141d40f45c90703c80c6455182d806000c0c11031411603040105210b50304c00011000d41c03e00d42d10100005810041d2140f0340c5880c919000060740c50f005d407404101110740e010000307611402100016803010750310400511118005400f4a10032000030800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 964176276 1250 964175026 964175059
    0x15050603100b130507092414280203040e09070302060714030405190815161b06060906033011150405030408010606030605030309042706020403031d 65
    0xa40c00a0000781040e410668a1060101503e03c02d17140000013135084c0c42c04100c0220f00300c5124601d07207680c0b103242c00322200001c0018603001c804852600c41060015240b2088000e074100c01030f201c02c10f00016440300c0303002e00c4c0c00f9480e50458400d42c11081071940000f0f4000002160303c00a030b1758001d06460038000c891321400e680300b82250b0002803908c02044040340950b20301c040340b80040000040d10346464101549a8289101407000c948001c03610414811141d0051700400d6040a046c50450b8807442440d8003130280300017020010f0200e0b0714020b0007050443d40354114006a0f4021190b1150206103100c01c80784850000c1a1b100705d09107142d000c07460162240e0100203003084484112280745001c07005c8002e07103801c19213040b1403e82c170004040248100130700903400102214241000014a45000b180c0c992183c990302c00d124950f500800c05294164820f84840c103001000d0410089450b40381c080000c2d401800f00381d0115006840003500d864860181e00c0481c0700c060a03101a4900140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 964177526 1250 964176276 964176281
    0x1715120c1f2001020a030b0105190e0a090608030a020c03061612020d0c03090b010f03080301180e061321050d2d0b0406140d031101021e03041505060310 67
    0x801e00208070309848100e070703009000b4002d492140700c948001a551011404041c08640d80300001070f06000c1c050214401540b00101c0e0403041c3c03082428031114541540f4002110300c4c0b00c0b43c000d00c4a8600d00580030802c0b84002000c0d1404003859000c84140001c8003080613600e07281156400760a1800d00c58103000c0c82d204103203a9810300140640035040c11100305030039042d02c0e141d0403c1d0700042d950b20388072014031140d11822401045040d6003207599a08645400003684030500504210080710390241c0f0105140d60300103d101000d5009442060412040d40a4490a4540e040c3c4060840c07600000118043c03513151481d2403100e07200c07146082480c222100c0a400300c0c2008096508100070711b04500c0300e4800e00c504c091680414005585600d200c01c120480e00180c0001d19005c1c00c060700c82c5001d0b181c1e41c500e00c02464150170080041d404070700745030b0b000e4030076105111014901340885480003150310000d1409035225580345070010811080203070858001701d80c02ca0f030660042ca0010300b60903160307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 964178776 1250 964177526 964177579
    0x604020f0d0213030c06050a09210813030b01030f0c06080c03071809240e15190b0f0a0210050709120309050901080609070602030306130c1715120c 65
    0x1501840f100b0303680e6202c500c0b070550107601c0040031a0000440b203440c10751010032480501000c1c540b4150302c2c007229035000c00c1503200b41c2c00200f1500000510101ca0122400268011035010710101d02d190f860703181030110b4017801c5a0032280d00b01140e00215845015600c11403040e0180026942544d940f14002c0300c0c4181002e184004000c2d0a61001c00c120b110750141c1e840406400301d8441c540c3d038503004000c1c04000103a00410b000da165400b40201c6010038548811200310031100200710395034208411503091081c3d84504103400340012495a03003040c9602406480c042c94081e10401c01303000d603450f81a11802c5414030002415034100b0b1100345144201042c01600034500400b41d141c0390360104140c0182a000801554044420042c81e25020840080034100c035101544c20b604003c0040741c0284101055034910684881c004560580b013500080e890800001d1035014904001c403030411442c3c020304180d400b4204080c0142003e00c40014240b6035528054031000c00c03501c582082c50980d0161 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 964180026 1250 964178776 964178797
    0x8070201200d1b091502120d11160f03081311041e0501080f0105011203140304140a030e030706170a0e070513060e0f04020d1113020408060f0604020f0d02 68
    0x700ea50203c01c0c000c02191110420381d407603d40d0180d00f03003001224078100092284540c21075101c68122020b0201002c15a403410b041c1c0030307000c1f5201012a0944071031307004034041403a0000180c403c3d1028009040c100d502da01c0c1c0a47c8680a00d80c507842031400010141040103080b0188039080500c0f1410a0390000320018200e079000c1d030344c0402c00300d05101958400ea02071221980718401410318445d080c45150b0040103481d5051f60080d8950360050031466807483c41601800f404030000b42400050210345180311481000d850007000d45203805080f2504032144036019210380740d008034495008040b25000030800c101703200c80035558001c260000c0c0041c4000100c2d140078041c0005a0380d103641d4081c4920008119002c50340c58107050240180c0c0794010a416003402c43c800510016803524805032481a40007c0d03800f00e01c00720072002c41c80c2910310b0031107611460701c00900091038080c040745070750056907050400d45042e2511400c20042c1e00034506038150410f010170152019041683c0207041c111034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 964181276 1250 964180026 964180031
    0x91d071101020c1603170405010219020418061b02010b030c041a090c1206010801031e05070b0d02120a1401120f06060603060602010507020d140a09030b01031208070201200d 76
    0x100c190960401c086a000020301300024101401005070400c2050341c0d001d50080000d091524045c0001d58408036100019032a600200c2c28809645880e04420700c0c03c00070260002e038104007803501340d005184001e0540040128082c2c000f0160b84103004820078800d00800034042071155500700801000d40e82c01064110141580210868603030340e20080c49030051340e003c1d03501c940000310311440301d0754000c012504201500d80144001060b15004d0b00004036210300612103c03405181c0b0b18917229407a04007183d041404510300c0342d00348241e0000e14035000c80d8800342e5400e4482c160048103070307088000308014100ca0b03100180809415002d007140410f0142c1e12507a82c41042d078075181d0840e440707070300000002a11000c081c40150b809000c1e068104a1902c02030651107403241c2d000380503003404828034038206800a00400024420200800519040b00c0c80b0031540d60741f07180c420f0030103c00c980c020011503890000030b51800e0040c4184e0000e0811401c4103000510100c141040c681c0c0040200d4030010b9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 964182526 1250 964181276 964181287
    0x60f0402040e01030b06091e070f050d09080c0c09010b040909080f03040b06090606070f0b060a08010e01021e0c0601050f040e0a111c050c0609210d091d07110102 71
    0x4520310303202c3c000e60250051905070b051110034064071031001400c08500d110030780c0b240c40405217401a40c40d0b0001003403170880e80b85001c19000701c50300d00c185075002c13211070b0411541c0401e102c0b0138030040404a4044c421141c40b20451024020041c600348038001d840041480f04201c1c8a40ca0b40020390010f20443c1c4051400c1510040001d4981050b40c0a80b41300c08240200300c40750409241c52600202d08950301400c1840d29034400c48407284640f4001d00340b403001004038146846030700040002d016010001e010b00004d9001c070600075000780c03840003012851040c180881c000800202c4450290b410085d0480c2c1e82420b0502c140d0034665000c46801541e106810380502d14140f0100c0503051194055071072030180e00c070421924119a9036441c21103031380941c203200010300000c0d0100000109072840c0d0781765429280005d400a10401c4a4150140f101c80c44014081000c01c0c00407030742a8076214400066200c2207651070019928902d4076120001b04041808680281800c0d42021110030000d86800c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 964183776 1250 964182526 964182539
    0x6140c0106050a1410080906040201390c0f050a030f05070b0d020c010c0203090d061a1002150a020f1c060306060f0306050609090606120a0c171005040b060f040204 72
    0x8030f007588005814840036400308900d29007085490300400d51441d180416091030b941407500c48502500007414010815421455400781c01018015000c011050b0140d000380c02e40144003084d503031101180c04150000c00814560051150f00341030341c13009042100c0090465642c10804680c00e01d081d10302c0d00c62244001104041d1030014408550515009070f2500c140c25039050030344402100b14030a43d0000e20aa4001c0d8407044884507a05130000000303d5240c0603110341510003140d26038840c1d0031081e1043d00d5200280c000403840c03c40c10310303100401c42c1951307040d01c26070403400342c9400c1d031a60341030420403403080030780a98501c0040e07140c00100103642c0341e4130303a40d2004460295201a1507401c02c0c40341082400075501c22940e100d00107503030304100d44c506480b150b61250b50042215110ba00c4c121400c03648400c0070400e8400155108040714043c51b1101c0007a130000c240c80d10b03100220310a0996030101d0300000c2c0216402070703a10650804890719a24100581030004040c06500300341d0074000003031030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 964185026 1250 964183776 964183789
    0x60c070c0e070c1a010b032403060c040e07090803070b090c0d050601050415050312070317071d010c110405090a02061303020a0f12020f04060e180106060906140c010605 74
    0x5074516143c909001a81d403401031020b07a0a030802020707075604400100030090210301180e07803107102e010714000400c04000360b40460360202d0b11019010710403541004480c410400080041c0e030383c82000e4017050765655400300c906014902030001c4542050003c02c0000d2100d80b444c642202e0300d0300036200c03129040e601294098a08030003d440c154018401005617041034411941c910003005911050241003070082035440b2849503441450000010b2041c0606204407590a190000d41d0411180c90070001c00007808041101b14510310424108000d40032503007d07209600366241c3c8180791902d603c005408120040000520804550007002010f40050751030300001c0c505020300b41036401071b0030b04600511001c080150400f01d00710a0b10b071002d00c14a5158141d03603460030350413183c1d0100341d2460404240074005a9005200e00c866080501200740b1441560305104030405008000031a40c900007101c580c0c005100f6800407a0b4041e8001c0d80c0000da520003405038010381e030700102d0400d9690010401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 964186276 1250 964185026 964185031
    0x31e0306030611161b18050103030815030a02150f041e0801060315020702190902071b050109060c02120706050c0f3c01020a0201022802060c070c0e 65
    0x2580c85405204004052050f1420f40384050f100c2c0b4100542c0e85810901c1072007003080500344074a4842d90302181141c607030b082005050a0030204041b488070a80600c05441c0c00c2c003084007c02d8000300020868112020140407000c3c00134020302c00e0741c0940e001e0000b00440a07009510001c020003400c8040d43c65040100010987c8003041b446d0030600b410b0740c15005106411511407641004070401c0030400785013412010100721040165a072007030344001034424800810600300c50701207c20014151010760f018040c02c40c01081c41c8032031541038082d0b01074110b8542c0a12408940603c405219091141d55540042ea102818103c0c2854447e6921481c12403550310260008a0001c0c214292000600c040d09280700d015000342080c1030070110b6154008560150700304509507203807881907281d10403940301c11021010381c021582c070035a03008001d010f5800305414545d8214100b90716103100e0b41c0c4809030321501700c160b8080c0c0072a44030001c10031102c0d0f00ca140d00380e850300820000403038007084100342c2c0c90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 964187526 1250 964186276 964186337
    0x20a0302060a050a02070806061516050703060506030c0f060f0a020c030307110a06050c12070203010f060f090b030a0c0506030705190512010e07140d0f1103090705060c100903 77
    0x284c682004030402450a9490741040d29150810414000e158507085000c410a0316086040c0d5160307504130b240101c403481410409800c0d44101c00001003448010340c80240907040079010b484080c640c0c1c00034822001090000280c03c2407040180802020015000d0040740c195407040c1d0710324460003c00607107075411600059941c0b801c9881030310303000d1a141c0500e50003801907040140c2080e201072003558451582c450700d204001d0001a4140071594207601c05081d01100d10010404103840b2070b0302e400203040c0342c02400070705489c00448011500c0c00188400c492039200d041d80c1c0e000b40c10081402840d8001400b024140141808804925040143c0702061840706070f8400d61201d0244060404545040e40840c002c0f011080038008410303800a44541c02460400b07035540c1d030b004000c4520f00240141390401a58038a01311a044c0c001e01464015401a00d0481c03c8540242d11002005072510584010580a50002192000854698018000c82070080c00c1004078180c00b420060324412010701c560 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 964188776 1250 964187526 964187537
    0x60306140f0f031207050c10080c0d1a0d060606030e150105190b0a2106030b041b0b0c030d14070203180609060a03050405070602010c21020f0a17060f0a12020a0302060a 74
    0x201f003e414003c2040302300c0c881518110000e410311916601e810320400910704561a2100c04d0407140240c2c0e003a822264402c003910001d0407408500313000c0c0052a00303000c2e0f0000217040c0054481d00060004008100074074010322180a40d182c041040400a0440b11142c6c950840080008603180c10901030140000c0548420b01d983c0751300c50124131001605a8528a1940792060510100e25003c0040b540035500840d04222401c0700c03003280503503210a40c4101d550500c001000c5a91520101c043c101c1c0101011041c444082074880220b0010301c00ca03443e40041c2d2041c0500310344490380c0c0d2110382607444050001403500d0b600c2c40220f8420340c4541d03d090003281d114003d000400004100080c01070069200802948500707603402010011510340406000c4102c0f000400e504107181d0448203521a03140f56140c0e1018503c81c05000d005903008440329110380d441c0010350034184440c85864215004000300302050034800750303000040d035100c0f080e41c200c840510044016105d076401012100801d4031789 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 964190026 1250 964188776 964188793
    0x8060619110f01180c06081e190c0201140a0e12030a0207080f041701090309060f0207080106030b09070e0f0103140102120a061a0403050a02010e190609060306140f0f03120705 77
    0xe00f5117500c15912000130401c00744108511480580100c1590581801c5d0440e41c0341c84011444501002c94543c1c00916443d02e8035002d46560158403085101e0200308620034030742c0c3d44c10034010448000204015494106440a0f10305559902c021940f190100c40b00500305811030302e07404425040526042030407440050305228518120b80404d05511002d4001d00c012012031f60b0007440301415100308070501400244c02018240203002c400017902e110f0008210165403410003c072800010b0340d4154540c060954049006c51030807180c1c500c84c84034410984050b910310740e502011180c00c0540385115543c00d0040c6803201d1030a00149002c1c0c0c4900d400400e00c5421325205141e026180d40000c04015001c12041002441c0410100c4410750242040f40d01c180034103022a00300042440800f8007410642c0001c10140d8018540d00c1c20f13500c003035404000098039441c00e4a032805590301d82991011b840010f880c42c91802007070b02407184402030140c4001090303d0901d05544d0b007008030300f110342d03030801e409 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 964191276 1250 964190026 964190033
    0x10090b0c010218190b0901032a200a03230a092c060f1203120a05010f1811160c08060903090108010e0603120304030206060108060619110f0118 63
    0x3507410b40e0f06040700c084da0a0704c9682c01003d0710b09207074410880e000d003010480c510968001da000720b020f51020b840d511030700380100c4190007446941c1c02011003c02c3d40342d0183d005504000c51070500e000785031740080c080c1071400d48047e12100305910304201d0408031a46e091044040e0310300a00001c9405880d81d05160303042164443c00421410721110201480c420403c0882900104654110100342d80070fa1007456080e01150002c5001c95841c0020b10001851034041d101803524103108011000b8100035598850000c8404d08a061141c821010312650000c680d00c1d8103603021540540040000ca860100307061210000c0210700c0700152450740004800b086000014001198026150f00c0a940f85c0f034102c2c40082c052050600a0340482d41600000071105e4404000341c440c0000070050094403850b0524000b951444100d580c1c5000643d10004103605080403800d4039000d040350005086901081e2104540c07012600c02c1c980001e00c0b9120007481030040c02c7c841d42c20307803040c080391071007407a0140e04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 964192526 1250 964191276 964191307
    0x11b0f09061404060806030c180406150b0706020d0b04050c070218010602060c0a091a07140705330304210c050309040207020402070b0a020d0b0d05030910090b0c0102 73
    0x78448024480080a00b0b420300c03200c1c0080f18151402820001d50700e403034140209180c02a00034010340c0001a12007518519040000e10300d00c550311804003030044000c07004039550810780034800c17446c03418414480000002c0003500505400d07603100c0d000180c90841d240006003030301c0040d0b07002107450038001804801c2d41403024000b008541c003000d000f000e41d450800000c3d5500b41c0103140715041c06010a05040117445038031054001c0401c3c00501c04201113010503460217070321029003143c0003884500074005d219008150401250402414032541012a000c280f038001c0c201080c080000c03908110854406070108084d5003d17a0260844490310003810394140040e82240c0c2c1080c0901001503550030018200108a070711140e8240e90240c1c03940707003a20115001e4015284000c0810303680e00c2c1002460b0103940d000d0100300d58480801d01c41d804030201409590706091070081c1640c1c000300192035007070030308038482d0350380840520f4035032445507507a606c804241d0424420034119940000d0025640306040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 964193776 1250 964192526 964192529
    0x5091809010f060f030803060a230f240309030c0109050a050d0212070818060304120807050f0d020c0a0f032705090403080601020f030a230c0a0b0405011b0f09 70
    0xc1008016050030a1300d000d00c08680c034400144054000000a5810f4541041c458021701c00082444580b800202e80011541000a00c641c05103039410404610b515082d0101a04103140441c20000b001012020850a500041104902d80700401c10b60208003024840c4890117401500a402001150f18106041c0300340103602504540c440400300c81c280342e0130011580c680741d100300a6a0740f40d45041d01a5160a41000c2156000074040304200621982c1c15030310b0541c0c95aa9520302c415982d00d0003c0d62a40589030004a4071030b4103001d522840b0758994010607859032520304440b15002160f40301c0700c0c1c10001c04011000216800e1035401d5041510a0f038441d429020307518a0302c0641404046100710100500250801801c040072481d641d00a00c404250884084107990391402500e0003e4106852201a14001d40d00c01c883c894464a030181a181805642006041c18101d0b580300e002114101a10907100c40d5070741d103501d200509241c0901d80080c00151501464400c1d4440c2c05400c0c00000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 964195026 1250 964193776 964193801
    0x18151002012d0b0405061e040f050403020a140105010807050d0807060c09090c0504062f0726031e07080d06030b22050316150c0203042102010206010e04030509180901 73
    0x5c0c01c0910010399074242c3c05c0b01d41250840c250320f00c060701c00c600080c003404550780c2c03012020f807411084c441815408500c9801d00342c090038007804007441c50320509007260310034802c904654212000034415031420151169416000b268181e0130042e41d61500c41c1210700e02c071081804106181c0c41000451014002d103040d1881d5810117500309803414801030300c0744900c1043c0a89078900d002402ca40070722400400900400c3d90011603500c96280c1011210420a0841c42a0107107188032181d29040400001c807460004140c444a01d0161010044820360304568805c0b03414030000d10500c1500c600754450400118000c141503c918201000030680c009185900c00e0300062100b500103001c00c03000411200104811151032040000750f08001c41070000500e02d00401c10b00748800800150350000150090b1141c0b42241d14070118408e2009502c9021154003c0c09600a0001046100d0816000c168014000e003009803508503918006101c21010074044103c591141c4240308014000344104403003500f2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 964196276 1250 964195026 964195031
    0x60a05010503210a0c0f060501090225050307020904031101020703030209041b170601050f07060b15040305071806090e07091a06090409020d02130501030218151002012d0b04 76
    0x584618003d61482500c0c000428010b070051030a08004106400e11000c1d0f410200070000c0d541c403940207001030341c00041044841801c21041101c1505070441503080f070781d80b050080d890801a0707420300a80f11401841902132000d07602184075125028001000580e210356001030303980c2e80f13440030401203603100c3c05400101c500c1160f14200c3c03560804160600441115010101541c4190049400d8415100b009503240c401240341d40800149801002840c00122443c503080c00007811408114001da11018000d0b5003d00000c00c80460f0500c24130b1001c550286022482c00e0300e4034041001d45c0d1400380f0038032141e0320003002000403600500c1510540c00110f0009540e0000b9038000420074003400401510469890300c50400315924080b405d901e040d80908100405000c0003015030040409100680c0245100d03202c0192050900f02803c2c030078800206804000a003d2050140041c10820494195981c480b40da450070410442100318134040720a1002c00021110a504155102103041c68040e90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 964197526 1250 964196276 964196323
    0x5030304090e011416022e112511220207020109030f0302061006091401030e1504080a0206060d020a06030e160803090103060b07081c23090d1706010f03020c060a05010503 75
    0x1440f01f01d01d000201c1c503460011401042802248446100b0851010381d4100807071540d05444070040c1c4105c5490780154400580140004288281050030300d01d50b0034440b04070300e40311016000036030240041a00600d030403d1086d45a07035031410184001c41040d00543e00c8401003101d610188100500a454540740401c6040e180503840150600300c442c801d81403584801192650b620100101d07085080b495402e0881824182000c14081d030213009118018000e010014903c1c4c1401006006225405064640c050b4030b03100d8200c0007882a41c09015440c0114004626101440c0d0310f840c024004c504044c42ea00c0b905079001500300c40c00c942c03100c0e00f000307414402400400c01e10002d554021907100b05040040440944c000700230036120211003000f10f078811200d0904031000703c0c428811940c5030201c81c010304402038161610301c440f015600030004c5000c0018590351241115000560190174094184585460624100310017190140c0704542d07504010011441c0401070812800d41c040544112070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 964198776 1250 964197526 964197583
    0x90302070b0a11030f04061d1c0609050109030801060e0a1a0901051b07030605011712180d110a0e070e06070804080109030e13020405030304090e01141602 68
    0x1480e09100305160460040b90000c01d05009881c901c0030961080c003600d036a61042c681c607540b01d4000303024030000286841c00b1048035070000e203401c1d9111721008198540355844402041c02100c04000c0840b00262225000710008109004401000380b2036150341c5203a6041501c024400d80900000c10b210b51482103040000250320b40c4101c1240051895840c0d640114500503549889601c40100c0000b180613031030554040d0100d0a642960321403201800710780d0f0f0307030f440c040c2140e99000750070826a08480e41d0703603804003c0340c001410072007200303c1550100c1c4550b00014040b910584410f40f207481c88800c6a088a242c0301500d00c002c1c0c040300031010203e041403d001404451041c00300c80c014100010302070305100103c01518000d00c40c4400070f1007100c4151900400030a5081540c90040f0382180d14a8840f0500d4001e40707003610000380045040a24124004010b8442035085000c15581c8061507000c66100038081c0d0702c62419181c03404140c801c4904000d213000c1c07c2c00d4070001005c2d100d82d05d28001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 964200026 1250 964198776 964198783
    0x3041506120b0414071409060409080304060e0111040b1b0c04060305060a050a090507060c0f0f1401050108031c1509051825171c020d23070b180102161401090302 71
    0x452800e07140512950307075023008140203051202c030141c1f00b40004401c100402c84160480c900055841000340a11250554640380e64000d070700404100323510600040140c007001c240c141900e40060011940e4052104012604a139102c3d001601d081d00201e00f000780c2c000d40b5010340750308000744003000c108241003600c80d961507920302d000300002c00080d0740c1c0e41c43c240121002881d4249800c80c0c0440d40d49a01480d00003240101c170000c41c90705500b00400090300060104c1a1004810103003400c2001c1060501d0810050a000d0102d9407031180543c1c0128031030b01141f25180c8a410310000d5070084440031407a082c0b07003801c01010b0000c82400ca5000d10b61294056009100b12455607169050756000f8400403070420011b00c0080c07032410062134141d007007071340e00043c060290149903d07841007030180d0f0800e214214280503c00e12181404026440004007014415644010b505c588210054000340596003a0307400940089270130650708050074203100047d50b00e4900700d9242c90081206c0302c0c4030b6501a46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 964201276 1250 964200026 964200059
    0x70e040305093105060f090403080a0b040914010c02120304080d050601030b030a05011d0102030108031204030915020303180f10110409110c0105011a03041506120b041407 75
    0x500000803505410110940c3c800030b00e400d440314210902c84862400f02c3c010503003160094450030314000019614104141800c0c010b43d016070380c4251580d01d0b020b40a0160031741d00041d03900300f1794402c009001b00700018982c107030005204001040032110448020310f0700c0078059044004000800510000800880883c0d404d010721000101b2507a49580040e4020000701c864581c150103100703280c004002040d4803013024603155101443c5500c0c0740004243c200d020900410701141d00801603066003403400020300c2d5001e0b00c2031500043c419200e0b1359910766845039104420142c0d0011060108401c42d0841440e1482080001010910082c01d031055803180070040310b640a40d0380720204e43c58511503200302ca0280250315024080d0b5008000d4424003a800784601c040654070f0320300081110107081410025050000d039038942141c68503220444504c0799004804c4000d669450300140e00b0045900e00c503a800e000350440240d5250038240b401c042004017190307e6664000d044203011a0700724040c8002d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 964202526 1250 964201276 964201279
    0x7020d030f06090f060e0108030a0c1b1d2202010c060b010504120804090b030303131b170a0510020c070b03060f060c0a03030c0e0105030c0315090a0e070e04030509 72
    0x342074910800000002c11581d0821000b09090542030814030f040307a0420b000301c640304007403d02c1c141e0344c94035419240d010301e50f0340c000050074100307080001c1240180600e00d01d800c80c8842c036211075a82c00c2d0b081411034110440c1c1e07407410318580801141140301c031143c007040290302c42082e81c0d48a00f0750000300b01d4010007800030072003551018486e4480e4802e0003568058103141e2074211300c0d20380344d00f0000c403641c000d480f0b40c00c0c184c1d0424074107503014100402500e00549141142c0c801403c0c650303440c074503254941d001150210888482c005502c040781c41c4224403200c09030029040f040074900f0241e04105503400704068081c0100400e480d000b800161060844d41da40b05120b0301c030f03240c11000034840400c5203100b0ba404017011854110072000400d00c1d04400d03120f0b480810500b04139460540f11502c0001041340866006d00008000d03204100c000d55001c0ba01464503400e83d00c4045c0040d003401d10545582c940c2c10799615146015501c1003100390007920040300078104a103415a0018101d106036014503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 964203776 1250 964202526 964202531
    0x50f0309011b030e100b060a0f02010e060f0405150103031b061107050c1315030b040203210a0201060f0e0c280804060606030b1503090a02061306020105010b0307020d03 74
    0xd99618082d0310002410b203805011051808054078018040c03c08050500007900804880c0d40259402d8458084910805400e550400c03001d2803003170320100852103900c01555208c424583c0070420a0040b41c1c4180d010b41c040181d40d0507d8100b207131030140c00d030400d0802c83c24030000510200b45c0001e415480402e1105003110342060600e404000f40801d4031003040c1c0e030a030101d0948100840030078406040c500550340ca100c0381100500000c1031700c0202c0b84c0c68107500b040400a00101d001c600307900e5440b500140131144e501c6041d46240031144065800c02c51800c1001c1112032240e40c2c2802914001e004220f480071403a0300b8000905480130740030b011804c0905000400c840c44600144d6101581d1030591744550502a0049000d400008211800c582c41c514180c40841c03410301902c9088403554000c0c00710104880c0c20740142c1202d50014150395a00d01c940c18900005030355800c004c3c9040c04030181d00d004103a280890190942d0700c10780044e01a00d000f4010440c8280d40007600102400c41890007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 964205026 1250 964203776 964203781
    0x40b010501181403030408120a1416110111150114010905090f131202071a070f150e0f0109060b03120a14120901021b060121050c060c070e060f01050f03 67
    0x1a14502c031b10f52061800e4040e0100c010505c5034140c026200c0d010054540c40c01c5501525042502c2e071060588100040c0000b907004c0c03001c80d100e85400040c004060412180c50350038190014035004000000203030b520b00d200b0040c810314120039210107181c0c40a084c80e6160604007000640f4082001b013040c0c5c04918280700080c08800303481706502080342c20200c015403c00b24103000039158441c1d8043c04510b03000013500d202e1404c0c1b000084035406038100707810042488c8266940c1c0d5113030a401d44c070a02801e880705014215000240101c0c54100019000001c400b0340b54501030b02610300000134188a50080b000070041c0c40c644900311001c1929500c0c0142407040481c20500c8103004001c444031419219004010503100c0c15401802103800d03214080c82d04401c64502286e580740709005981c0080b003804000490381503508228400a4812801d40ea2002c3c0380201007140c54001100f0b09003560300c040d0b0704000103582034030035541116064426802e000320f5a40060079038451449011140d0100000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 964206276 1250 964205026 964205029
    0xf0908100e10021b2a040218060c010914010b0604180204090c080f0906090c010c05031c14010b070503090f01170a0213270203060a0b12040b0105011814 67
    0x21850720003007032140854448203c610f9001c2d00d100d4002000c101380c82002c4141c5110582440c005602214980b200700c8144d00c88020b101c040c2d04601c05107030800c420a905540c140d46c03414003410700b000f1035000000d0b00402034200401411900303225503d03039914107416000e10f42c035400102c0e019120740080c0b03428810804510000240326907400844030a29100800c18030640c01030000303014100c00704512400351110840103032a01d4080d11310f101540d01c82e11004015501990315041d0460154082c1c0f8109450706c0d003400c060261503500100c06a642d04520884100e80c441e120780901620f014540c00d00c50240d54460f901c0c1f05144985114800d14690582c2c5603204001d40b8414850b554001449424413800c5540039400c0701940c02640f064101010a003601071803050300ba0346c0f130b0031000071202141e06900e1500130350024050907048141c0704800320345815100010b020f00c0c54408281a01e61515080c0f6000d21300043c0c100c01c1c1080b01000c01c112244d603100c6080821f50311b05c200d034080074003e07450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 964207526 1250 964206276 964206283
    0x5090a03060b130e061815150607060e0102041d09070311040e100b03010b010e0102120708221d01050603310809040b0d0f0605150a150f0908100e 64
    0x202c0f002035060910758105245800030814602460f00c003841d000075103502a8041c0c1d10380d00c3c00c824a0740c4c40104440000c0c80c04200ea074414804020240401340f0300304c03180e2038800581c4c80c1c015485a40b690000340400c0340605494001003090005030000c6a1800d10040e42d54803141540720203403641d085130400c0c8100e40d032150b1258180e06201c5003102d2144400d481110f002c0c1c1031890900c0d1107940303441d14032589540a4011344411190581c06018101c2d10004251801e800c0b0328415181c040062080040074880b4003040744483c004c00d42e48100c46440c05c8110110b07008126030070304001a11400400403526510140ca4100300c0344a00880f81b811007003e03180580346003565205005c4a241803000c28041c07000c1c000c1100702c0d0103a03401d000d50440078040c004560000b00d002481c46000e0300603540405d5581c2d0240c0d40180080320450590b409010018415014a03009000c6040c03e116014681940028a2000803421414840d02c0d1510b08000c0603280c0b50030f80c0f00720405540720000208052400e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 964208633 1107 964207526 964207549
    0x1b01050411040203151903050604080714162306031504060e0105010c0308041a070f0e09070905011404030215120a05090a110f0d060c0f05090a03060b 66
    0x10510201180c51070a41d515241b520300003000103081031003098003c6015002040d2602d034541400f0080030080300c16000e10342d1107610481d80105008811404803000c1d0100141100c890050030b203141c0145921382d5910070000810468615960004107402040c195000c00443c1c1d19001c1d45c81c1034140038080d036408a91907112110000388039070b0a00341c0c80351080541000c0b10b01d5603c2107451030802a038810001c5503018a40c100b2480d4085903201081303108990071a4541440c1001404c0c40b1094003840741084110418800102c240d0001c540095a010340203402000d00310800e10310540209081c1c001144c40000030a03043c03030250181c0c501518001d40a4002c406056035803100c40140d80000a8110b029101c103a0719070350b00c8120708204079000d00c01c04205804c903000020a89110410070405002c0305200008503034848d82840c0c1c0560758040070001d95036100e41e0004040c0e4110 = true := by decide +kernel

theorem cover : BRFrame.Cov 964028776 964208633 := by
  have h0 := BRFrame.cov_init 964028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 964028776 ≤ n) (h2 : n < 964208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
