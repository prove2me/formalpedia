-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:36.023278+00:00
-- url     : https://prove2.me/submissions/9ee1aaa7-5e4d-4576-b6f7-39fbe4691a5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 726079136 ≤ n < 726258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 726080386 1250 726079136 726079139
    0x60103020a170a1b03020310061112070618030e03010e1b0405151903110d030503041211031309050c0a1e0201110703031a040b03070b0904020d02031003020310060807 73
    0x2e080050030010419103801c0d0303036840b18440010b0b410201c00c540381480d0b01d00596a085c440003841c1d4100741e6900c000f0401084401c4e6600da40d0011600000c00e032180002d254a036151440c241001d440c21034400aa004200e10001c01070550080b95904c070403005034000c004044811300c006072070780034540740e0300034104900310043c0700d40c1008d600a5610102648420039000c0580380004c43d1a681000c0340140440c09030014000e10000329082c983c45001213800207400c40b40e80e503000d04107010013480a88a001080c07822040f0b14091544415500505000c0d69540c80d620200d102080940c3d0140303480c0d01c0d151800040d031040f100000c8404400450301d46e44120080b00c9240c40418080c8110365085549900a6503492501e4402400300030f0b1103520041496680a035901083c0c4451300d58842c802c03402c103040342c2101e07100410582c1c10781c0d4103003130303601e54580c82000440c01a214840048404da4170000400013118500211001601d10840a070340107000b00302c0114003619800d004501083c0c120030300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 726081636 1250 726080386 726080417
    0x501030b060d14011104061d010c1401090b190b301c03060303110109112404080a020306010e0906070c03090504021216050408120a2d08060103020a 65
    0x4044000d01e1192007083c050f4458078800b542541e0515410b041840001b282c103024032908400c0a480d0002c0d040f0720880d0740e0700c0450000b8240c584541026000c01586405400c1101003074000d1081540c00484108141c2000f000068080d40154043c041a5281c00c00700102445d00e007a404041c8564454401e0b080742044105041410f901003034681d0b00d1040d504000c0811001c9558030a181c04c6030f46001401920f03500700500340e41030103041c402c17503139152400071400612120340c010240c40c419030b00c0c0818001140790000910f02004044c060306980400c00092035100083d603440701501c25015203410fa681c590308400c5c82e18095451500035000507000450092050304846580c600030300d004140160350b440403904aa000000e410140710b4501d04104004003600598001d00c812071811518107031800b08155245e071110f00e299100307000c0c0003c240070380c94800c04110a111074440c0d400c10551009058100610780724a8410001c1a859400500c96602030700c00e0b140d200b401c0b44c1ba0340c3c5200c03042c003c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 726082886 1250 726081636 726081649
    0x8070311060c03040807030809100e0337050a120203030c0301230913020a06020d0f0e0a1d070e0915010e010c05010c030603110301090c3f02040f0501030b06 69
    0x8a4103000f0320083c003002415070710030042c1d1030045015a084a580700407510501009080c08010401485a181c4d8000800e0f05c001410350b2040011070403492814000600b519070b00301c1084083d8003085440c00710300d400d100000c03901c582030901c508000460205003042c20303078481c0030494001480000500042098802080a0002c0c43c60800d800070000f9000c84005403038800251600084c2c0600c9003400c1c41107003010b241981c0500480c0c001000603068501e4020541a00411b0580030400140003400c210b80300c0d5201213014100807200b458004860141144103080b0071210000000d15068a10115042080e180340c040c1c010380300100031017040d07040151000c040a0745854101710703204845801194080c41108800c2c541c3d80c0e0081107062550400c11201d001046411f84280d14028421001070455181c0000b21070106101032000602d0503640201c8410034188a000f422080030070b6042401c416030004030440c401c40c0c0400034038001c0e1510340200c0e0000d0000a000003100e0020400511300395 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 726084136 1250 726082886 726082897
    0x201050c0a08040909140105190c0903080c030a020d0c1a0403020a0c0806011404020f0712021002040308130801021207120209031606140309061f08010c180807031106 73
    0x300115290100155150806a84035500c01c00b001e42e95014080100007103283c0b038040c3c0703016100c003e10003402d1142643c0524402c0a0101030f007565142d101c19829030164140400964119410039201c285004101c1c7c3c0b02d92007000008014021202d0035041c06009591014009170814401080b0640c0d440c40c6022010b0094020b0341584103030203003440010b0200b02881c02070310700d02010700425454181805a41d050184030984030343e0045c001419140550010b941810f6004138400c680c03030110100a90031304201e0080c203c205070000401000340b110420051500102c0a01a130340341681c0da580140c01c0f8050b120448040940307210111700c0061040800c2d007403071004000d00515241036500003078900000c0e20a1601400390b2550200082d40e0400c0702c2d01d8a0340f00b0881c0769840d501d0900c20264560f00003c0c11010900205031100d50490025941140940003483c020003801d0119040a01049a0031880c105000f4030040007141c814004100b94007241e0b81316a030500c074412500c0411620b50040f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 726085386 1250 726084136 726084157
    0x40603300c02130b0d1103060907030809060906120c04051c03270914010e010906030503041502030d020d05061f020c21190b151f09080715030501140d020105 69
    0xd1351558003c0e030340e500300640080c038441c46040b2441458402898140705005008402c544c00c070800410108010400b00c03500318038221b03616036580d00c41c5800980a40118001032002005240030052002855401002a035608580103640c0760080c1080090700c07071026074010000780c85400211042e00e100201142400c0000181e0704055031160810300450b0b107072022211500140100400481030700390340c0c2502500e84110b0601c0b400d429500c9071580ca119a104214500c090340366492486842402602c1e64140403460a41d0755040100f04c20000c0c04054440b035204581c000400035003034401c40e010000801c0182c015140880240b010025400301d9400541c00c98004489040c40c4008140b0460542a13082d02010710706500c5030405403100a80204034096003162a085d01ca0035070384940320075000301010450755103443e104150031910040315600481d241c1c400d051012540c80e09406443c50700c116940e90405c020380e80c82d5000079824144d43c403075581042e400e035006d1000d54826401403012505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726086636 1250 726085386 726085391
    0xf1b0f070f0f020916030608060c09100207092307030b0a1406040302030703030f09121709011205010603021e13120c080303090309040c2105060d02040603300c0213 72
    0xc140c3c01007000ca0b0350440303c8904100d0340130710b0100f8040c0c251007100c021700b03052401483d5514200820303418a01c96400940e01c11622004888071107172080100b0809044891010300200b001e41d84844104980c507607203c49940e6400340041ea01a1003880b50402151004100d50001841e10220f0b19262a0711031519410117010070000c80540c07420013180700194800e5441c00300c0d0790480000201316000e140c00c020610324404100074081541c140589021407800480503507501c900600503242454804200c21066040c039000041e410342543c09130083c1c600c81a20b480101c01c0c540d605a07028481d01100200c40096400c0c05d110380e00706100202c0100c0d02c07404c000c4640c55100c422081c6181c0084590b00740c01d900022356010b142c10a4003c909040707009050024010f00040c2216002c0c0744640c890f0360b0f08503034420004546a40e00c080e40b108264010384104074183c8c41e414101c141c035160740044681020707880345d04000e60f9546111180b000c2e0807a590f010700c12980f9820440a148000d0304401c5094 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 726087886 1250 726086636 726086663
    0xb0a09050f1206090d02060c040305070b0d090609030c030206010504090206040e15030f0d1403010312182102040b09040201021b0f090915090102160201050708120f1b0f070f 76
    0x1008220303c0b80504900390007489001842240240790180051441c01d4201062004000086d00090341c4400d6400c0c04441d59110348410320103400502c000000980030900300801002455040310301d200000780254207036038450b80c0f00d8040c40305441c40c80d00000d4102800304020407144407100da40503003124070031440205603116400000d16150540205c540d09400110f000000150480c22101c401581070000d14210f41c503580b0b41c0c1102c0c8840e11116000d1158003101106c020845202d9000a05946802d41d80d400c01c24000c590100c00c0501c1c0e0480c001d070311301649101c0b5440c1030300c1c580d331195505900501010343c0013481a00c00ba01c05216054101c03505c064002c04566601c000340784201c4021000b0035080002031090800c00d0800742405015910401003400310038100101101c1c0c0a8080c00c20590320700311450700502c1845a1090450400c1404c0c0500041040310201d075406804086e42c1c030141091101d000078058400c00d0302c1c10054040803c00d510001e862103002d01c2d00e15000758081030210703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 726089136 1250 726087886 726087919
    0xc010c020303090406172e05060333010f0308040320031002030a050739060203070e1002071203080c1209010c020d0206040f030c0503160602090a0b0a09050f 69
    0x5c1d055074000a010968841c0100280e110800902841284c15091001c040100705000d810b1010304144082c0540d07110400035803280c03400c000ca207101600440146140803031a102081c4036115840140000000b07802c00042d1559445020320305a0780c006050030320b41841c2d40c0d40c09000d041e40408000111112080f1010b00c1c0c0d60600001199802040d00943e480c036041400004a84008001c0300502070f001d5180602c00f02c8075800c204400c0d00d80195003000403441d42e04c55000c0d0040c0a0010102da00002c00c000b420703903100f00003250a00c0b0960b00c1039420681b8500507070f260300032805003a5259500c084940c011a00c81e0040c1038220340d80d00c82c114604511550716100341a012142c099151303443e04209050302c2d40c100141c080c0251184090103482c2090380d074001c8145105000a0304200710f0002c80004e2181c1401244e0318002c64a0f40400b50600ca46484006500a6401a4070641c0103003c002882c403500c000700e800c015603990320022003600340743c10040030505181496820000c0000144880c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 726090386 1250 726089136 726089141
    0x61707030c090b0f0703030b06071a07020109230601080a08030a050a112b06060210150503070f0312031406010c030203131e140d14241b04080c010c0203030904 70
    0x105542e40c42900c1c0d45581031b04010742600c0c00101421b0055008110721800300702d010b030a11201d10300170000040b8035107803000128054113002c07a000e0b0085070305507010044004800d08000035075007034209407051aa0f032540c80640701c10001e41f0250401c801080040e4840d6a075501007030f444604030b20000b8044112094a086075000900303d1742c0110b200803038000b82c800a89031005549001c00341c0c240309041c1880402511800502d0405200036129000401c9030210100792001400d40a403c441200b80c1e0785c400c034006a8058032023505c14540c20941040c045209006140180d4040b40850b0840d0f1242401100d40913402e002c00e60850000340840500a01e858454800a243d003800d8810503009204000300240115840f43c400301d4900d1003200010744074403990190807a0410083c6400d902c00c0100360b42000b402c2d008410100b004610382254080c0741d0b00c42c641c040d03041010304225000d10104c46c0350940c8914016501503a101e00103001840d88514165a582c500c0501035905005010303000c10207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 726091636 1250 726090386 726090397
    0x7060507051327020f071104060b07050706110a030903150608060718090608150c09040603060905010f060e1306060806010617070509090a020d020c0a1b061707030c090b 74
    0xe40110072495407440f1003524030007407084003080c00c2145420f11103003030641e03d8415914000d2180705406802d00317a0382c2c0c95601000081404240441d500c00131480d00580708c0c42140034000124a511103050034400340007800910792079241d01c2d20b58800d811500c480c0400a200d506540a2035140c80b80810321510a100c0d141c010714143d1503581107654000803036030b0941155080980b80500c2c00404000c601790000700b0150300252505610308d00d8840d00303013102c00c51040c02000341d001400c0100000410810b5800854090300840081014a00c6c000301142a51280d2103100041d81200740410303418045101110b4089105030000604c00350b403601c1c81c90600304242e00c40000318103c501c62000c40041c650101c0d80c4030324203180691901130004000381c0040c402a080d0004c1c80e0740800e00000010f419411103c0c2944c0c080100c940e40100d915000d0321444241525016200090000086c0d46000c1d2342e01000141e104a130111a1b81d42e625030440040a03a0f00c00d0074200070900c480000c680304035400820 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 726092886 1250 726091636 726091649
    0x803040221010606020d020a11010f02150c0702040e0a0c05040e0f07081e0715031a032b0207060c020409331d03070b0a110c07031203050606070605070513 68
    0x3c0f018903151000e0308103804400c59809640080c18050000784c0165801c1c1da91500908160b98020010103080785010f00400341846101c102c18140141c01c2c1450010700316880c0300300c03024008c029440c80c040d502c0b2a40c0d2031004194000d060020701052801e60042e0985040c40c0040300c1c14242840c030a186000070b941c3c4160300d0303600001412240c00100009213100c212007040288112417400d400307031f0b2028074903410308010950340344d030752040b035051107441000f50000040441da1020120602100502031254620501454101403990b60364008151002110352036241e46000e1821502032002400c09510111040800c010340c104201c1c914512202403102d8a200000683d0840d4070030710704441c1c1030f160310344011071003030400810030b00c0000880e010503500807200e0107940c84020840e00602030b01900c030003c505000c540c81460310800140c0354110f038003404d4080080e8125100981c1110b0090310b480c0e170070940810903400410099017200e60025014900799142410201c0e01c102001010f40082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 726094136 1250 726092886 726092891
    0x306040c122a03061505071506060f120501060210360507120807062316030b0907081b04051009052106070e12010c09050a0e060d080304022101 63
    0x49242d001c6030801241188604080003da0f051110458040c4a40380d481d03410840005002c004110100c1c40c01084110260414000d036a11510080c2c031484c89071402e48001400a0300ca0a00301c0c902e1302402d41200d056401610312542500c40c0100581641d00d440c03c0805203e0300b599a59803100d14074040d044400e858132418038038007450024180708079548900b160201c1c0200c040040741d0f440040302c00c071940c040d200054000b40c0c910000d031140c1401d114600d02c1103501c81002401001e41c019481d2400b001e5404104d808000006c0041400007542c1250010f1868000a48900c428100540c40324502c190312505050b580c10009031201e034035a1001e0700060700040d040000303041c04205e62000c4181c2d101c80c0c007504580c00400c075684d050300500c203804100760101d4048030341d11740c088181c2090601c00001e000d0301f1408c1070702401422080c400d841c000c100c12340b03000840440c02e4004500503040104030022820071611041c900341c0001c0c00607a03001e54181ca600a20000007801c941e0501c0107400003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 726095386 1250 726094136 726094181
    0x31a060316051309170a09080a050714010e030d08060a0b030112080c19080904140f0403051308030304200d051c120f061a1809090304080609030c07090e030306040c12 73
    0x2461722800360b1040c840c0b507010416009c0010070104500c0155020707070b40034000d62041c3d00f00482d00941030b0543c554050294078181030110f40e000c07840038817500c81600c031049500d541d900020400d100911500c1400d022150140000a0300e044c020300b02d1884000813030344c450001040d04090380002c180203c1d4420800107410358a400c2c01d0150100019200342010401d01d80044d41079030814004100804001c0b000603001d60320109010500083c054800403a616443c5c41d18001400c0303028031103116810764420021203282e1400b001c46807030311a0702902810310358088403001c000314108010408284440c0502c0004101c40c1d40c41034500c840004540031904a240416514a40000703034624000c610303040100c40e082c10310108003541d8a01e0180e40241c2c040d9240c0c5001c90a50149421950090064a0501c4007003a03000002d8280420800159100307079a680c0c001c1401c8881800c0c10801d81e800c1440002e4843c80c1a5100f00d00101c3c3d1401c2c01200b50281c4044c03002100c00403030944d0b40f40e140c1c50a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 726096636 1250 726095386 726095407
    0x31915141009060b09010e01080c0d0630150507030f050405030a0e0303130302090606070501090807050106050136090c270b070b0406020d06031a06031605130917 71
    0x1400d0002c04c280280c8510300203620340001c1280310a502c0e6181409030400c00700700071102150442e101c80d218118204500f03502c401001c8414200c0b07151461212400070040002403400410541e28150300000e0690302d0341c070500107800030700401000035040c10394843c251500b40c6510300070140725900c03400141d65101030000c005400000481603c6029178004e002e21844074103400c209106680d0100e68120359503039080005201845413290040071035082116000c10001c401010700b14142c400d20080c003115403070300c00445665140d0100c110010006050403058445100004260751008180321001d65407a407906005950400c420240010000b524840c076501d0016412240602c91784e150754582c504c1c0c500741101c24090150080e01c0c0d1103d0070045020400b255044035402c000303d2805210742e1b5520300300381094040690409072a042020009a03440c030300804e0402c0d000d10040103003241a4106402d00504140e1807800e60041c5546a00e003c0108003000a00d01d0f200101004050781c1c0d294004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 726097886 1250 726096636 726096641
    0x608010608090f060a02090607050726010905031c0914030a1805061e120901060504052203140706020334050f090f0909010504020906031915141009 65
    0x40452030281c001043e08801200c000c01c0194110883e4080543c036001c0000c0048c115200c0c0d104018400e0bc2404800207003103e040e1a00b007580240e0303000741548a201c00702e19900742e460045008100d40c0041002081ea0401003518088264400e0800508602d480e0707030300741c0800f100710040300080d480820140049030b40442c03806043c141c1030781f0342d2940600d4000465010f00511007000411041d04410024204080d403d0300ca545411114075003490a002c0141c81c0249a039024040c000c60a00c00040c40300720001030041080c4000c0e80d04080e022200b910f088138026080092407040300002c101c000c001c52944d0002d10700900c5020500d03400012090614043e900080c0a03640c02039800034180301c0016004420341d600608803c10982d665030b48a00000d4a1b501e03000740703407135000400500340414010b05500c020711581c401e40c1e0f490740f00c0d144d0b0000c0541d500688604078201055445048000828440c45040014441800450700100ca80041005040b00300d0382c11480e4080c0c1001084510041e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 726099136 1250 726097886 726097891
    0xc0b0105040606050304081e0a0507020a050a1202040c03020c011a040b0f0a060320120609100f0b0d0e060906161d061803100b01121a0907020a0c0608010608 69
    0x21101004050b1802202904c3c5001c0140b000d01050310100303402d450810a00b81000500c16903042c280c0e0b580d00703a01d1b00581143c02080b030590140e9030240300810a8141440f0f90b0082d59085042c1e03581484050b0b081002900843c03101d141010b400f446880e119403004d00417001840c1c00200101079030070500c01480116940520070a10030400700441c2040c64541c207400750f05482d16454045500041c00320703205156404446007804606000035500001280b00c4036003401600201d84005045c0c4904240c0141540b00380641016400c080f01c080242024000042c40c80c00c1c0f5444003c10030803d5074030f626003480d9044600480c190800344c1040240254100c00d400b14a080d428200b164021140c0742c1e0003a002801d0360640908000a020700250f401c211481d804000c0007012030b03000306009030720640900307100102e1501003407070600c00c810410203d01440c8600b1800e403000e1803110048100b0400c0080c0050f02d20810b500582b002c0c500810a0465114042c0c102234588600c1075252172001007014100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 726100386 1250 726099136 726099139
    0x7060b0f030618280f03020f1911030f0d0c1b0b0a0906110d0309210509030c0a031208180a03080106080603030304030c0b0c480c0405150d030c0b0105 66
    0x1c1c010041c0448200c8a050100560026100521720070319150503882c004911584050510030700808282400588140c04941c81c481c0a800700010220018075503a030301c182d5102076054020030ba241c180c0078803819050708070300e000c2c814080144896100c00096101c0c2604070800700007000400c00306058010704400000e10306407601482008280345855211003641070344104241e16114003030709202000780310040c560b90403405481d000300c050030041c046a0289000c503010380995602031081d40f42c070040f240d003143c1d000441103030002d103141ca08851120000b498252440541100b180b0016001c01074022058880e13203c0040c5541812006400400010b040d148642e00400421002907403244e00e950310a940001e0400140d155031000c00d01034090030b6204071580042800c400415804c00c0e441200c09048010b1030709205020303082145040c06400c44180e000d9100302c1e68040181081d60001b984006a80926501c03000101e00040c4594030b01d1105400148540c68604180403c084d50306004050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 726101636 1250 726100386 726100423
    0xa032d060c020c0901060816050912070608011401080414010e0a11150708193c081e04031707030903030608061005130207020a0f080d030501060507060b0f030618 71
    0x342c106d0081c02c0c2e00f001002d072243c0c80703110141c0c0d18544d4080c000365840307040001d008103c04d44401b14403580e24085842504002260140000f840c5c854070142004000d406a46480c900d54a0b5210070107120250750150409640c0c0701040f480c290400c2c0001300c9850b2084008441780f046050402078481c01d0280003091204c02004401c0c00958940200e0b5060400310400781c110394281c0d00240c941d041d058004440e402400519000380715441c800049800c1c208441500b180321090070101d44210703003110880c1090111070550100c540401c100503600510a09c1c2260703c410794007844d08602002a80c1c141d0119031160301c000101500b60040201030040c8400a04030391500085005102890307204082c0103801050501402c01c440e1340484191540140c0105980d564400811310600114802c507811b60284418201c0c225100e4014103040350950b50301d0500300300264840301c0081c05040c01060b440300c82101c000406403400d021461180310856900308210390000340c007605194504491490405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 726102886 1250 726101636 726101639
    0x50301170610180b091f140a030219120804080615090a09030302130e04120504030b06060a050c060106050c010606140a051324110c0a032d060c020c0901 67
    0x107090240500032030303194100d1000b071501ca41000c3d03c001c0050b1122190004100030803c203600d00141a456019003420518240044c1e0b201d088500720b50700880001d038040c0d0710307001c100050715008403105040918000c120350655a290780840c880300711450308686001001c00d0401140100344551a0f11140507036034175206100440002d8491b0000415012006a4840c0e1403410325102e5810f9440500d80f0210300d0041c00d0b01c1d13280d6060844021141210b4070342201d401140c2c1244682e043c2d508803503200c084442240c036080200f01e038036003260340d21a08026091144030026070b81003101d01c0c024005900d64507500d541c41c4201e6429144650403117400d0019081c4400c1c640d08070401140d80082039840c020780c40d42c00070100300c403c944040d4070150b0140390002e11250a0b02c420701d02c1c201c0310b91060b00c407141ca18005004103503d5803079402015500c2041d01c1010000b0545100241d000014a5818618903200251480032201e010380c0c1c040c1c0d41141d80f0703503040461580410465001c0c401c101c5880002e503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 726104136 1250 726102886 726102901
    0x501180312090803122a030402100309050a110f01030207080f0307090b0c06270c0f03011805060105090c1204030507050304090f09020a0f0b0a0804050f0d0503011706 73
    0x1121144002461111980c095000e1644660865000b403c0c420f01525034840c80d004004003215015922a001c1101d203d4807011204101280440d0030002c4040c8142181d482c1d4081181d0b050242c80d003141896224454040050010b010108117a1322480d140040140c0c05428016030313403400032005050610411090005c00e40300310542c2e01e0f10002e505815560390302d03090200d809214552044030180e40209241c1614100030407014405c1c940100c08280c80d600c1c00f02d0b888100480038403841c40d20340101520100c5418000c008454865000d400400c0800b1400d40d2824030000a020a440980142c0c0050007649040340c001500504108102c6080c040a03210805280001400c02002d125000540804010741842910000c14401104002042071a040800503005421007288900003e90004c6010020703100007809982441d60414105880054140c40c610ba0140042c0c0d507a10484a240c03040d5a000c104100328202c0903a519600c1c0d5150540d00450060282c03040f0340c0300c0d0012420003004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 726105386 1250 726104136 726104177
    0x71211101508030a020d02010b15090108070903020913021c17030a0908030a0b10030614060c03120a0e07090b130c0e120106050f01050906180105190f090501 69
    0x400d00d40d040000765414200c16504224401d6500400c21400040b440350141a00491011000d108640081c040404840d04003c2d503000510300300f1500030010701c058549035100c0c0f41800ea200c0300c14244002c040c3d45a400099085404071011000520325681c0c450842c01e050213051117a4802100f094007104090341c4079440c80f41d20702d880325880400800000c24a03e15608148400c54100d90611360ba4200034000f40054005140d005000b070b0b03801440404402c0c403c1c46014215408556140c1c0800c54820400c4225804450401d1451006002c20111a80e491103414000d05440700b0015040c10b002c0ea0407802c2100039070003000302c1860f0802900060b254540700300480304240b000054889a004019154412808102c0d0340002d1f10001c40401008150300c40020303284215141034844e04041c004445034450565640d410813070034801d5241e500c00a942c034a1204c00c0504215090041c1d44c102c01c001100c9a5524000050a40348985800751700179664402400003880c0440c52480b4550500d03c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 726106636 1250 726105386 726105403
    0x120f02031017030f280201090b07110606060d090618021513051302041205150a06060e100c080708040515030405060f0a11070303150603020712110a080708071211 71
    0xd4154000341c0042c01e54038800c08090607035085c400e00540c440200380c009000342001201150021400c00216190381d02440c0300d4800070b0150300042010b5a10b92050004580049000242c0c59885640c00070000302d1901404a402e2812152102101414010132100003c0e04e440003841410401c81051103c02c0d2900c11070944000359681a80c0307040300040b400091080c0e0380101c0c0d8501310714030518100200400d14509200420404440035228540010121400e07072051074003045401c01c80210070b04044041c035403080f0741410007003030340c030607036282e8220603400303404211405e00d4005030900c2103151181061404d6400d11030315604514042c1d4402d6519600078000b03040324540000018603405090300280030a04240c210b50351240e000e4034001e8007609070380c0100c0d000080f20035404100ca0340b2910954900725084900740c59104a20303e010707141040d507095a250305015082c0d402c804180f8160080c035419100b01c411a90714036007820159144231151280008000d0880c1c1c806a03010400901880e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 726107886 1250 726106636 726106657
    0x60f2a0307061509090302031c0b0d03120636020307081801063b04020a060807030b060f0703020c0108010e0a0e1e0102030f09070e1501120f0203101703 67
    0x12800e8111424801000c0654080c5441d02e00f885603c17020154088003070450a00081c60100e1410428801c07001601c200f125526045040501c4031400700348958204040100d40060004095444040d6209052200c44040100300402a07550b0b40d500125a5400309030304030000114114249883e00608101000d454842c2c4840c04030440144010300b90701c004e00800c2e45146848810190b195465a110501c43c000031559141a412424905510a0740c522546c0c0c01400d140c1d8060904c40182c0350305a01914010416035546a241b1241d261640148a0700001703081c225211030003894000d152035640a40941000400401044444003100d1900e4201a5044000c02c10709c40c0060000d15090709000302003c48030518000c49181c05041d80114064840180a0000c0e55039848038103a07203510521594460080a0000501500160000c6042020149454060701c2400c0d00350b03100740c0e07550001000c03581c0d50020500c1394900d00520000c00a14452403013010700c0c855401c9103500c900840b010103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 726109136 1250 726107886 726107891
    0x60a2f0d12200d0e1f0e0f060c0f13030309090c051e210c0d050705040612020307110f010522020a0308090a0b121005010c150c0e060f2a030706 63
    0x100841d0400e40104e42035004400468403607410713071515100200c0b0f61082e400c0c0341d28a41002d6119000002c980f000040d80070300700a1446032a1011100c145510404000f19071210500860080a00079910480194001d6491588041c1030119805c200c0314420100402d00c403007004145040301030821031001145c8550107a03512181000046980d01d40f80d1104641038031110000c00c840561414068058024220003c0040c0c1d56104400d4070740f442540555408030780c1d9103000054806207900190351040c41858044015510396101500d00aa031100083c03d0307135101c104004c0703103500754100300d03520311323074030b5000060056590b0003242200341d95001c0542640d80c0090300e800e15407100440c1d41d00401484640d5681c492541c080244a02007d440001180798815000215588140412217203075400598001c840d05072805654000c01d180c072020750600c4042507150000d030303560f134001e042e2040c0b100010300e40d21010201c0d200c0500700e50a02d009520410714901042d520303400000e9a20340b030f500c034600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 726110386 1250 726109136 726109147
    0x10f0b011b081e18031617070306050109050a0e010c091802131212020102090a090f0905030d0b0906030f0d14160f150b060a2f0d1220 59
    0x502c02610070409041c00304040c0640807070050626000410000b80324441650b095074800042541340c11502c1e80090f49517685034400c1c0800d2928803008400c00c410344080f41d00300e40d07683c1d0302e41054460987c040a40c0c00e0b41d03581008413032003590113031141202d1008003c2005081c03110f00642480454014000140011350785503003940e03010760441c1c00c1d0025070300942d1030f46c40e616000c3d64201013001c9811541c0703107107407840825aa8014000e6802100300189010407031818040b5150091084840c1c01030b0998440c9201c002085c07040c00200b402c10030728003000c0340d50107045c8140022545e02031309550003907201c0403550301e4002e030106010940c210541b42150385120405500600c90099014034041c00f41581da0600c100811800c00181030342c0304400038100c003048448000200c0e0300e185000b5802213020440310300000e208400c8201c51030b180545000030340c4500000a012144c224404801640c0600300c0c810340f42c0e400007090f180308c4c2ca4000303092240f101c099600c0c9031288000c058003a00403d01040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 726111636 1250 726110386 726110393
    0xa0f060c0f050f0604020307141c050c0409030e0a060912030806030a0c0906061d18190f0501090b0d1e03050c060f06011e090506030a180303020a02010f0b011b 70
    0x40780d008150090100d0391040c203203200241e160701c800c1d541280300c2d00c01c820300058145400e01d0381200240000f070030013800d80c024100108011101e41c00446686c040ca0141c880966030700e00c6031400403400b81e5030b5103160170005018007482a072507400000910109032001c000c0e00703400703003040300c212a81458001520f8640728007084c0380036603080c0020302445d407040740840c0d40481507010800b211140da03100310004403404070b0420444884c054854014403400382290305c0eaa421289950000c00198102550b4800c01503810308491203080c9800d03c140c0c5540040010162034028400c200740c04442d9a4001c4150341e030740c0042e41c010080011941c200804d40d00e000e050098080e516540088415503689280603140107507844000c0b180c06002c2102c66a82c048251030040c4043e50401c11515101c80d42820001000b6140e0801005075601548440341d800c0550242407283c1542482030b01c0c0503071601c003100c0010342940d40c0b5403103140c42240b814440410580e4030044007820740c60b070600250040c17681410b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 726112886 1250 726111636 726111653
    0x6070c0b030103030201150f03030c030f02100204081608010b130f0b100c050d02030f0d020319090803090106120807020907200a1401050705040b0d0f0510060e0a0f060c 74
    0x51100481030004000042499019008103401d002041c01000c2c1603078440c1d100e0f016812403800040c2c0042c1520010354000380c00b84907034241d1410180116802c2000c404100b109036805900626070030b410414404040f15402078104000d030900e00300034495031741d402000c1154214248070800c0c40b50707101d80f42000e0f2068258065049804c024128086203810100302409800c1d043c03c0844492044540d040310f040d20210a4400b050807410416140403000d000071406174002030505662454540b508010a00c1c1900c20a160b41d48105440ca40303a02e01400e090b4211070860707104042d9807502a0340c40c0e0008111004850440758124b9101520b603d132000201c60314004184600d4114038100003881800b407001403901c2038144544428000342c0d01c00c0d0310780ca0990b00c042e120300b0302046083c0824011500440050101402a02400101c200105100305e040d9501900c43e030000910801080c0a4603a00294811402ca406e540314101e0914002c501546a201880381d4005c004282010108002081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 726114136 1250 726112886 726112889
    0x190516050706050702090f060603160e0307060801031502031509130209180d020a0b0424060b0406200715140f040e060307030f0201050a030e0303070201090219030f0206070c 76
    0x6400c603403800ba210040944a40c4c0202c1e0305920480c8108001021401c030400380300e104000160020f800c40d101c2d1103020703214204d0f0321407a10500c40c202c2c401d09100c1d1020850400102015a10900d0301d51450821910768202c0011800d41180100104030942c408220003125100e400c0d40e801440356106c04411451400c8004000d601064010510500890003000c18107030b0b44941e016107455030000101a0ba4aa00303a00004203440c01807000540810712010114407556581e41c00140c00180210080c000c6400581040b40c0d80e84003c82c05001c0280c0c003502c1c00303a0920f65040d0700f80360141d0440d1040d071389081a1194001003e100060361810604c940e42d4002a0305503035003840e440f10300c9000a00388541040c05090307080e210100005546140008420b412a90410541c2420440603001140c1d698001c00d5a08281a10390407040d4400e14108011841043d2541c0005040d00242c0304200d0010303040c2d8020018920400020b001096045031a4810168100d0741c0c0c3c1d0f41c03200d443ca0100541c10f0f01c3e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 726115386 1250 726114136 726114143
    0xf0c03080408181f02060916050d030e090a0507140906180a0b1305040b19090222060c020a05061e03060a030c03031206150507020906120601080705010311190516 71
    0x3480c404c4030586010b5031100351201403136000d41c1c01940c0c902d010329545805c2d11007240724904007000700300030034184900c4200d01d0f54000d250900c408a030000109215040544a480459584408004801e684401e0066401040c3c640952401000030001550f501480840041e0280900b9007040030f80d030749910a03802070803401b03c015100e441201321840320000900c10103001d14204083e05005143c0324208040d0181030f40307041c0c2d403105d0410258000035000bd010312103003404001c03030b003103447c5800c1802d243c014030450b601e10f100c150507031041c084100003550026004143c1403184100c4111310920041e40d00c815030260b25125581c003400070301079061035480640050803550340403081c1a070044410b80c0010400c0380900c1300a5a4400700fa807110f400d145014002082400700380014906581c030b45070002001480c0e03000d20034039003402078200b0703900ba84101116489400b007041196098000c0e0380c000060040c0103402c1c4800320840c03081100c2407914a1040060000e170305c4007107407901c80c16245810340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 726116636 1250 726115386 726115399
    0x90703090507080307050610050127050d1202010e0f060619030b0915011e05040c170a0518030405100c05103204170d27030f0c0308040818 61
    0x207403458915105e92240301e054074035004110000f1070300c423045074803007080710410307560700040b114502c5c2200c40350080c5491119503810003190020b40346e035410704040d0000d03018111402100e0b03446134011f0f084810001814074581c20049a502440e007001c10083d5200c60259076241c0280310702e126000e50102d4a4000a084c1c504000c20b01038500000074906980c4c4003800c01c010642c1e604c800c06042c5a0364035102805004032040c0060120741000e400800d100e513000d041c03850170f281e107950b001d00a02c40b003150010603055441d0300300080a03a008c2d0020701c102c801480654078007414000843d045000c14988031060140041802c002c105080200004d403c180c03080c100900000d80c0305130355090300000401117006095803001b0110000080c0c200b40581c0d4080c8801b0700307500c40e031010b10f001600104001d04006980c0c0c035641c480707020340d881d140591300e0019001c80b9801195150251007400c0850001c0f04000050504000103504407402e03a410540085a094840c4894040c40b496181c600d45001c2d006807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 726117886 1250 726116636 726116639
    0xb1302030c12060901291612090b070206180609030a030201090c060504060219420e0d0302030c04050a06080402121c05090a0b0403200d03050702090703090507 70
    0xc00c1e44000d0800442d14552019040d1140810420b21481c280a101308601c1008605070400d0082d0701c0d81085954854102410000500800b50920414060696002c1500000749180300e501820301c0c405442400095800d001d543e03000b00d403a600540174240c07400c200140c000d84095544500f947c2102c8402021103140301c6403407034024060b00d160041161402503103000441c0c01409942520255a541d60003810350503110305c61807816114011040c0c4020301e44030744182c6803080304051001485070840d40e019142800400d880f1b40aa0b103880954909460101c2da1b615032207001c9903004900c0c00c60325000da20394881c1c4003420118400c952109a200600b5000001c0f1150003c0e00648954000c81d800c0d0344002c4803003102034a135000120050360146842d01c415483c4c0340202c0180c01c00c902d02500d19180551256010501da6010ba0805d84c0d80c070040c0c0b4180711041c0d00482d400000744005440480703419a660350050001e000354440203110301051000034020350b21075070110319425040021640020b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 726119136 1250 726117886 726117901
    0x30810031707060b031203042a091508030a0206040f1518030e040911010f110f030403021207060503010308070602070b1609061e1404090c180519090b130203 69
    0x141c2c0b00b450211041ca062a035407402c1c034603010400b0401800100c01161440d660395881c6c204c040c1e1a0510001922000c00410900003010398100b8043d210700c00300010031130b000d0741116082000540c44025590700421204040750340c049501900107520050a000440341441e100e0000c202100d09100d00924042c1c40c00181800c0c00740c02002140252a42e40d04008400c0a0101b0340e509210b004d44984429501b140d01d80d4454030340e844100007546807003411003038020307401420b0040f45401d111840d40041403d1096191401e451a9480b80314402402064501040a06a4001444090040440801d0003002d003d415011141141d40c840005521460403c11a640402c65208440002448081c011a440340905070746040310700e100d0100c01a241070302c4002c41d950103803009a0600b60100b800300090061941c061809105000c0d180c80100c0007400201d070007407031741946c407442c880c0307041a20305810000e60f404103100761400110301041002c494804105907a1540c4000c10b1803c4c400030420040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 726120386 1250 726119136 726119183
    0x6090d03230a090e0f0411011101020f03040b040b070c03020601060e0d02030a03022104050a21231203190906021908090c0a0308310e0a050604051303081003 69
    0x25112a0300404c04a629070180c00c04501c1c0048a00400780e00760046240704a60142203100076200c00d5078009841c22003e94a4001c44d504252411214502c4040c10f01c0101300811440a0380140a880d000d03484200b140c6009603644018801c62051003c01c2143c0003a40c1c84100c946c6440d0f80d00031b011030b2041c000a1800940d122841d0754027005d0803621030070311840745000900312411144020800000d1a0500c1c04070b40442210008c0c03e21204100c41c00c00001650f010441d51602c110a90600842d801500e4650708090110310389101c10201082044070b0303051810601a070400b0f4420000a851101c2e10340710300207100d84000640301d40c0b5800f240d0404203511809543c82118a00c003036900e124031003014007004844900005244550510252000700141d150444c600078010301c51040e001c008405980b031b6421940c01191807800181f04200940d4060300680340c01c5201a01c040250303107000307910341c000d000745403400404000046003c114206030b0314a0a102179030304032222a0340d00e1820b400c0100c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 726121636 1250 726120386 726120389
    0x3070f03050a0e03090f0f031518061b0a022e1a0d140a060c0519020f100c020705190305190308040803040f06140108010b06090d03230a09 61
    0x40e0038440010181c880d1800303914003c140f028019420403070030030304115211148406182c0c001042d07403d11040c80da02003018024511000130100603605005240405012603940a018558071150a00c540360f10410103002c2e001c18445180c41d1943cac2d508104a0400750f80708158244030b1005c4803141c61940640c0c240700d04007002064104441007102c0101c3c070715250b48841055000111032401400700e00150b540888002c1a4400e480c0c0102880e99200211400000328030001000402d1303208501c81c1e4400c07403500300030b00c600007801002466038405941c1c00e640015544042d441e40d212490584c02006004060000181000c40304440c1c3e90309202c02d590140f0003030b6424480c52003030041032900703070211101450b00759403407011940c0d03a529030300a145d10140003100c2005900740810b0100d501ca00ca5451aa8000301000d4030030b5141c005200d081d035040d010350a20680b410808a0380c6030385c131a0b40128600d94181003000c0c1c0c541105825900d08034094440046881e80002c058003c144d1201d001c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 726122886 1250 726121636 726121667
    0x14071413060e06061309050903031503031216050c01140906181b0a0306050f0118020408100f0e0703140114070507030e031905010603120f0801090e0309060307 70
    0x3090808021940015920503126550800128a020640d1410a840140b4600e010350f000d0f2080142da64400300300b101c00888201c4a40d410110a0043e2690499a00d880c80e420807001942008454030a8000d8140c0241c404020300115641042025004100380d1710b0038424a002004842c584910b081d140401c1161103040c40d00858000501c07084107000c92285031b8000800624441d0300d5400682100b401100909500201252001001510030700486110340040034602e5429403509820410101d100d401301100c0758014003081c4000c070400142c0c6d02030072181d09404a03a1942c0c5000c2ca0002702a0030528045600480d500032052040a030380902d0700130030540c000c1000d090b11903540490300c50181e8004000503000c0140030702191041c3d920425000000f025070b261280540c44448601c45414000c4070142d444c1d0380104103100d5181890304042c007040c10111040e03d01144000c0414005014210700300790f0300c903c00c1010042c204141d65020a003c0c00141c2d4070b00b00a200a0440660784030aa03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 726124136 1250 726122886 726122899
    0xc0f23070606031403120c0a03090b010603021902010b0f01030504020f030303070c290115090b0c0d1103090a0512013206030708120d0b060d0e12030f070c140714 71
    0x20040013000040b80d00c1079a203405140580d84403004440c00390f500c80e90b8194101078544903c070000c6115684118000d1816880040c0d48100803101c1c54410380034240c3d00810359140009100321600e501511f580d607400300b460000345075507480c4005840b524100814940611000c0208481c0c10342050740380618502032030703100101c010900485084002d405da250081c903003800004002401c81c0e070a40f029148144d0406564990700e821150070150041074404241d070340200100c4041030b80106002058401142c051407a0144000c045101c1c0703645071050702d02134141d15451007010102980180c00ca8148200740c50078901054601150602c144401440e0351030002c40841d540e4a03001540c1001c8035000310280601000c0f4511201c2590045400000610344032040c001c1569a90030080030386110b02d8200103442d0310100d01c8c252800180981c1e50006030410401e0141c0a0b40b4a08915405081c5142c0030150305c0003807034104c0c088580c0409602c030921400c1c40108034103690b070a080c4940d01d000d0351138 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 726125386 1250 726124136 726124163
    0x40609030b010b0304080d050a0b0d030807090819030c02060c06010e0f06090403080c0d110c0703050624090408220302121b100203120115030507030c0f2307060603 72
    0x3c06030718801600d00170030400d010001c44051990700e4102d6035001c8080140001e00c1c00e0381c03201080c04c01c004842c086000550040400c1a180d8001240c0780c0507101202c000d054410040c02d43c42019000c83d03070090280811030102104541c0c3d200c00300c0345007038003090940308556518403018249180c2aa820304034204448002051800c00d28a40380c89290543d485080340d0b1a01c42c850001c0d41e0100000703903401a200c806c02d00c0b070070903510002c0c01034210a13402000c902e403035410210704200014109111101c0800503544030074002c164481e11103241110045032030b4440c1e2620590310b100d5411032004d03401001d50b60360310300d094440256080b64000e48030518a0380060f100c50b80c48489040c8090b000c030b83c0340500c0c0301c43c5091082c00c0340340b5014180110703441c040d02d0740f011000c400000da0064809044841c2203400041d894002c494012540b41030522149000030400782c15000340409441c00c1002010403402c00b070320480012030700e07a40480c100b02e03034810b0b0b0350a01c00302030038030350105542c0c040304100c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 726126636 1250 726125386 726125399
    0x60d081909061b0503030613061a03060901150f2a051506060a1209022e09080d0503010e090c04150501090b040503070303110102093006010e0106030b0411040609030b01 74
    0x42d000c60f2103a002000c0c600d15581c5400b0400781000301400d00d100c003a035550012402c8041140c040c019134522000d80c83d1249407000800900c001c0580210440002103503056034040e8000550081b03d004c1418074001c03500c01545c0343d903990f060005960070440c00744409602444400300e000d010041601104007400e540d12410b002161043d181c800e80003464018080c09003040b00e9000101c01c900c010042c09480c001c074522100c82c00c1c85140c00f01255001451280300d81c68024403120028106100500080d80d0b28100103031090205100b503812250264001030a5183e0903c07505245a40080082100740d44002c1080000c8e4154019180421100ca001081c0108071005480072514010014210b03141555401c0354104564240c0d028191340034041035144d03940b800d00140c624039a000542450b40445204005a10746000352110349810450050002d0001d074051a4155000b03818041801800a00810300911503c0c080f0101c016011a000c10044c2e80155010100c030b004013111540ca0f40ca0340b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 726127886 1250 726126636 726126677
    0x1060501020d0302091c060209091b090108090a1a010f050d020a0b0703050d02040b0306041107020108070311070609060b040501150c030e0a09020c0f12070308060d08190906 76
    0x8090140e4410020140c809200e0340080100c070401412000148420701000c44c40614160300c1102c466401140b030440b54101041200d0380318040b0490011454103140707103038440d441400c2d5014104503a55001500391501080071070702042c3d000e0065220700c614001403003201d101c280114050314007000400200d80c580241c8400c01c05030010403100c0903c1c940310400445520481d4128144007040c061885880a80c0c8050b000416490030b50719500c2c90601c0c104011903011407100301403c00306000040150760b0010b113a941c421818200043c0c620805da0001c0c002d405180c60041c00c090905030f80004000d11900005c0340e440007680c007400b803030340c8602066041d400c542104200054040e541c94011912a529400c0b1103a8003500b501e0619440c0c0ca03100703081e6406a8051007040d0b00060004840080820000080d01d070043c0502c0e04150a81d82c000b06071000140103980f140c0d0301c0c1005c07102800102d6048400c0703c030414000412030a200c101c050100ac0040c42404081040f02c0500c801e03564291 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 726129136 1250 726127886 726127889
    0xc0e0102010605060d1d0321161205070201060b0f040801050615190e0a03030e030c0a050a05040b1c1a0f010b04090c030902060a170907030c050607030c0b010608090f0106 75
    0x140094144030480b9081700061803454824201051210f4440e190000140003d1160007540b42c48250409001d440700c540c2c001000e810744101d07080444800414039131004d064695885404004140d40d03c030b8000807409000d80c1d40050500348000100783c4024045d54000700100c403203510080c001aa00c810401c61074242104030b01410540c00c129068080388019202134ad0407131942055581cbc98911008140600c109030030460102c0c4840b185c40009141c10130a4094a4104440180c0301c181444003141590781107100c0e0074065521492a5150b0b50f940300e80d60034110004174086141c850700c034200300307903800900d03d03c1c0741106600d14040703005c4450000c0024144c9108c044408e15151400c0c002d10000c003001d0f80d05d1001c00d642c407801d47e00180c0d282d800815012502d66a040c0068001080b1302c1d5404d00c010303042441a40c06400100001101256003508039002241c07141e868038264101a9040420760f500101020b485000125449400c0072802c2d001724191030444051800414959080f503d05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 726130386 1250 726129136 726129139
    0x103050303041b0807090906200d0c050702040e1c050909070c0f02090f060f010915031d01020d0903120212041511130519030f1b030206030702010c0e0102010605 71
    0x10800500415031500d80000f000e004044a048159603070001e5500300945600300003052600d81c80080c042c4412809103400d180b072903041c040340490028200c1c08481c425540307950042a00c400511440c40d00074425076504580240c024403452044501550f100c01c0074440351003030081c00315002c07c003003481303841540e1034280003800700c06041c1c4854400740d84500015000311900c61340450079100503101d84002070f01400c0200c2180000c0c4c00c2440820441c0c880d0011501c0c10805589020055200d1400411003030a140e4280040c122220400c43c04000940c0c0780c08200c158000901000f448004d036111072002402581c416164443da9880d200036803242d14007030440b080f01d00c0c010902040c001c0c905140e018a14031030029240c0302c81c0c0c00d0b007116034100c2c0d4402c40310001c061204201c0e500700307100c010482ca41203610b12410a415135413079982c4065000d5028211819507003491389020802c400d0703c8080c1d034004112949a04e04614024080e02c6121266000180e04801c0c100b1603500500480003038890 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 726131636 1250 726130386 726130393
    0x1060b070f0209040206070609140c010e010815040b0a0e0f061c0201080702240402030708121912050c09130209010203313206070f21030221010305 65
    0xc542d0200300c504080580301382e92000c010081c07100003ca50707208510740d0301e1140604802c18501d2400391070915608480c406e05000722580c024503681c0e4481002640000b861124400120441c00810024180080000d070000c0b0580400300e80700040035145485500e03000f1b2030724103540e10340041c41108144400c0e071011400c0c0300c51401c0e0040d030080000c03560141c80f40c03040307500000140b000e410030ba103030105405a40c00325602c01c3c8010340c01c0601940b0701900b0180c00504a500c40751403210814031900302a00705084141d520210302034070a035800302104800410074071942c102094264220780c41748805d68031588080e4000d2560859500944071050070580186040c0016100ba0005482c454840c400ca540e8880101e06940109600307884060a468031030008880012480400905001411186206542c6150b2021691900121496a82c0c80061102c4001540c640040300d2a0f0004250340721040000b40961200d074160701520031000c0315504140a4910041164809042030001518030340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 726132886 1250 726131636 726131663
    0x4050606010306120f0201030b091906050411120c0903060a0501050418150b0406081905060703020301140d1b090213050906090a020304021c0f140c010906030c09050d050f01060b07 79
    0x117820411541c80c03140103040201c0c0c10307812013000a010403022103a0b500d03a01200c8046c1c4244103080d2150b48040c020a441c10842004200700f2404c0500900130340c1602100d80500254040030058183da40f5080007600b01c1c0c0081c00d2840125010304424001c03a8043c0b40307407405610a06030710304450351141c1d400140e00700d003405c020340041021741018260281c000da240c200001d5120f004101e9140107660701c0074210840c0d5110300d005403c0000152010041500620061000116403018001040c400312140240d65882c1d04e005140c44c0700e000130448103202c403c500000c03920050303001070031160003155401803095180c40030030510003029a40d940d0030111a10001d41c6144880e401590040c4c00180100c00140d006041e4840c1042c1c40b030012100d0102c200c140c50204115040090001e00988000d4040c3d0b00d40b00300001c000b20014800d803010542c0300c50803502c0c5540280b0700c1c080a07160140050f0040346d1241802d65032003100c00c0c0c3d2034040790729199001a00d0780164066481032035020f0500074280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 726134136 1250 726132886 726132893
    0x280b03070c050f03090a05011d0609010318120905010c0803130c030b0c04090f0614040c1107030515010819031103091c05060105030c0f011b080f030405060601030612 73
    0x581009004009114001603103401040b01000791801c0c03012020002c544d2104401c0610060341680d500c0141446004441c142c100340c207230107004201640035142d90b502d4241c980012800341c461030354a240d00e004041c2013072043c440c0d802040460265207840f28103101e40d84800460320b40d4000c035000303002006e080c408180030810b042025000e5074051503107428055203c1d01d405507d80c00a031113031500b801c4009002c0004164900451803003440595040054078609800100c004883c0e5220301c1c8100c0e5200d03d13510303445000d164104140011041264a8907440349042c030340d545151140c0c4184048204c000044990000130610940f520100d0b0b0881d400c08965419a043c060389a1400c2c3c0e1400240a0f00e1400d40364104455200b545904148035046030f1030900380d0030000181c018602036000802c400e0502c0d02c80f4401c180c02d004080c03804010802e0103002d45000329007602d4004018580016503503141001c0d403030186025500440a543c0543c5600005400b255090300c24000d0100d51440c0c2078010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 726135386 1250 726134136 726134159
    0x9151b0c03060c0426030a021f230415060605070303150f0e13061803030e010b090612031303110a08060402010903081c050c040f09020306060d0b0102070806041128 72
    0x4110390321607509142012071a02800c54000d40030714001a0701004400d102142c40c40074214070044130071000c1120340c0c040c041d041c2b1702e4103042840d5083c003001c0401080030031500540281ca40c00c0130381c0e01046440c1d1200001001c681c400709040c0c002904007010500903c020030380b240c00300d0300c2c410b01c1c41034814500011043e02802c010040010b45400c14103900104610f030042c4042e2000714800403008262504d005000c40c1c8041c2c0000005030f150040700c40003900c444d11801d07040381d0220354181c102e0a8041c0c0c0da078518820705000242c00000d400d030000401149896402a21030216200717a012a00c4807070050343c07001c08650183c00a945210100b021400c1e0800511200c10349000340c400c1c504203164606c0680e207003602d1555402100203010081c062748003012303002402d004801503107035040143c00180306004e141d100c0a0010b039103000e1614070344c0c0204425030050001c034098841c2803501e8140310018440020000b401044440d0301d184400301400c48a507400c009440d101e07812681054a000030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 726136636 1250 726135386 726135419
    0xa02120708010f0e0a14030d0c020c280b090a03150f0e030c1c0c021f02060106050f0403080a020102090312071709010f08150d0c080c060702100509151b0c03060c04 72
    0x80c140010024040708e200303035019003030656256400804010b4484030901641d02070f02002c42031983d2010703015941c082625030008048608020382c45440c0e09059002444000d1140c2c80200b00c14105044001c003038000e034000142400280c0c008000c10320380c107001c4039100e2041c00b0031201107404c41d800d00307803d4401101e0421a8400b061500882408440e4042003460611100c2903032595000408605440c1c0d0401c031280c0500202d1034031606001c0323808507081c51070256000041030b049001c208201c0242c0b0035419607110982c000e044078640c4100a03034100d91540080d0b025622000c140420901c07262243c02111400780060f034031084005036000c0101c820300000340098000b0042901000c5817a0360b4644107100c3c07a030080c1401d01c0b51b145007014442c0f411501952041c000d40d028030140f000740e40d800100010080040c01c01954504903240010581146aa0414440d040102e10880700400d20030001104202240c06c460080541d0b008160340c0d200704503070314009008100014000076050b1070804a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 726137886 1250 726136636 726136673
    0x60111100e16091506120b0607111e0d021309050129031216020f03030d0b0103140402180c12040c090f20130503010f022703060c0c0a02120708010f0e0a 67
    0x2610112200008c280790320884058580d10355824100c8214541004172010311200e044a0401d034000003070200c0c40c1c00d510040081c0c81102c06c03480300340c0c0180300364121245c40750b484402041107001c400c1480d500c01242c0441c1300703444250013021031610f00703001411200c01c11500d060755081c180c62a4001246110443e02240c001d00840150f100544040024266414128002080c850000000101203078050303010200d0440c5050284409a1503050080c90b0a01203a210715215680f4800d59000758861250b0540304031005a0400c401c0c0300000d0701041c25100c400d542400603242c42012082900c4407005591100104420400301401c14540102034519100e050241030340c0e41c03080020f0855408140c089002d540004864104101c07501c020480a100d404500e0442d2100c000400ea881900500c0b07010788000c001003103074581c041080801c1000f0f40c000c00c544030302c0d43c0c1031900980364952071095214941c20081d1400182c0c1e101e014000304d110781c6100804601c0901d4039011390544003c02540e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 726139136 1250 726137886 726137891
    0x30801061e08012606010b1e0304080301030b18071d0c13051e151207081e13021003090302121c151d220209060111100e1609150612 58
    0x164020000740a030724000c0401e400c1c03148d200c3c01c2da40000c0131800c81841c410b09503088200104000140d60301e040d0307070540380c202a00822036643d02c00c640b0500400110140800d2080000010348030b8081808001c2c900c1c021401440c403030701ea0903c2e8038054000c5910100503440914024021400c041c0c041203044042103180e524005500750204102d4500ca0300f18440040f0005081023404007406240c03604a8903070b162401c410301d0090f064102c0a03944e100d0040d50b81c500324000c43c0c1c0003070520703c0c50030b00d00b600141a0f4007614003040014000309420201140507029603582031050304802030590b60082e540c41384a0621842e8080700b0401007218a40000b094048000c011078244002c2d141c000354410b50416403000c03414003045640d14041280c00d01a42c000d8020304910068840b640c1603a04143c2c20708010348003202889419080c09041000c002034185000c10b411f00d021000102003c030480c285084c5c0910769121084041907034a0860142102c007040c0b9070400c601482064140c2403100d2e4071900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 726140386 1250 726139136 726139199
    0x91f060b04080f0118030203070b0603070515030703050106090b0d0906110307051c05072001330e09061609030c030309030b060103050402150c030c0307030801061e0801 74
    0x6024540e0426000009a50700c09000425030341c109214066400c102c6441e00c480668046e94025524411104024051580700010440c0c984080000001400000b480940600d010f909820141e400c01c8a640000900300000055200d00945041003601e02e01d051241c5440c0384049000043c2c282084119155562048006141c0d80000c01960040600fa070791030355074078856985101c650308007100c180e034058944028030a8440d0418080e001c1514140b4400c0b00c801c1c000040240103000652440600d9980003004811060300304524019002c4503100c1c03c08942e480b811000e19184048500322074070707480480810fa8984440f10340b01d01c0f1103002e00d13003001201d03144c1c2d03940c0212061980c421000709a1401d4180104015003440550180080c84c0800461030326400003852000046418141264001650040341000744102c40c54000760b60101c90f0b4914907450001c0008e0000d2107040001407000381e41103d05005070340030305c0d64041c044c4d0765864964206012040301e0482490f08498141081e201d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 726141636 1250 726140386 726140399
    0xf0f01120f060507090806073009150204090c030204080c19030f050109060507110705041a060c10060e16030c1b0b0106020d1b1b0807090221091f06 65
    0x465100c0c0340140d0b51300801520304080c1502e059800380c100000d100a2990031070420003c0c2210108030038401100c040700b04927810b045002003940550182404162400601010b5031a800130000c80d80842e200b00207107400302100300c049003c0d9000b001c0309500f04200032440e62600b11303c0d100071140d02010090031140e5a135110052191840f0044440e6511210003200b070009520590740e20003030038204282107030112411540c440a05000d850f220355507480e000b0741c0441007500c02c80310b010405050342c0e0303651854491303075a518592808850419401c003400841c20700608041a0300400410b04144102804544190081e02c9082e0f044020081401ca1001c05561005002021103004141541d51941005802414030050903100b40030310000a125941409085035180091600b144800c1000140c5412003150b070741150b4000e110300c0c841c081c40803540c004140d0040034111200d030200031140810f002601d40200c3c0465100169400014038140e0a5000000b145550552a500064190b03128403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 726142886 1250 726141636 726141641
    0x503090a03200906030d030f0f09110a0504140f04060207080d0e120418020306030708010905030a260708091c020d020c030102131518090c080f0f01120f06 68
    0x40c4191501104109040c80444985003200b4102c1c00c15120600945001000710f079845043c1070f2404201a6504c0c800c20002d1026484401708a90628081c010030f0a0780c24004410301103420701070710a0900381c00c0050781c0c1c0361a20449a00100f55440055a85d40d031342007601c05080c00a10540d644d45d000c000360000101c010008020204100000045400d4810251450310111440401c28101c04104c18806070081c4004c02d4130b681800a00940c0e030f43d44a02c04681044400c1c0d002039159820410391104100c4080701034000b1280564a02c00702411076408400104841d462030a40a000400810b2400e44540b11480d4400558400ca9019414420308001c40c2260345c200d1200580011030302c5080f09a050220030002d0408900a500788260340301071110851091007031103a52043d03540614070b990b000c0e041a8414114a0441147d9940d45000401c040c00d213030070001d40052007100c00503020110b520125801044041d20280b5244c2c01d104000d1071492580d0b4090300d042002d003082070005040350 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 726144136 1250 726142886 726142889
    0xc030f05070501110403062904020c0c090708070f030501050619032004092d0c020703060614090105030d02060109050705040b0d0b2e08040f050114090d09030503070605040503090a 79
    0x100038030b85c2d124518182981298020500064008140c01c103150031a00b0314001084a001c0c00c0b03c00503919100360792074500c0c141c0c0300e0b000a60401e00e03040c104141e894106041901c00d03d100c2e29a419640b0100b03c0403000c0798001d00074a5480001446010f00c1c201c2da400c40031803044001e040006034000541040d06400b0442d0540c2d00d16048001014090b924860180c800380252486400701225080320846c44015200010940166900c0510ba48000e208110700c100441d0060b00800c50651928030758103913910503181d4240101801800085c50b810002400d141200b411b40c00380085134246520a0042c0c00090315040400c5024000400c1c0c2008460080006540c0ca110000300702e54054244a4048510210052840788203520500010811890310601c2c41503450515010780d114a441e03076090441c4075000d8400e61030411018054150785000174016103014088400003803034a4000c9600300158000146903400034450540020345507046140c0062140080d070b4100707030800c0c01203503405096 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 726145386 1250 726144136 726144161
    0x80103061d06150f040b0f060d020f07080c01060b03010b0d110d060b04090f05090a08250308060a2309041403030c0d0608032113141e0d0c030f05070501 67
    0x100c0c1032598440c82d001c155080508000d41c2c05204074000c810006061030042822030b4021440012615127101d043d504580342c81885948250b190f14a50800710321607003040c04243c40c190310704440840e01441fa2400e907030407aa00004a01d280c807080300007002c050040303407012400d144400e104040a0161740d028004c050145128580c3d1214900311445040d200c0c611002c0803c03a03d00b80034002220b0000c980211010b421450060380e40c102c1403c00580c115036000070710844101e4005050030191300c00d120301e005130000c8030f00c08441f580700d803c0201003000d015041030040b1504104a0514100b811146a110f402618680d540d0741e52040301c54115441111100c5c12031000051891a841061042c00c0c05402d4590066013042c40b58201100700004510b09440d26000110020311481070100b07140348403035400b015203071444062905556450080002480742010521148400c100d0001a4a4064001e658503800008401d0720180d130300801244a0104121082280d0340c0414003d0180040d105103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 726146636 1250 726145386 726145411
    0xf0603020a0306051509090712150602011b090603091515061803020a0b090f0d030806040c0201090b0103020d0203210a110c1311040504060b0c0f0d080103061d06 71
    0x1000707a4010704030f03581500b11600c41d07031820201310007540880342510b0070041300b50b80805850712141400e66080103c0c0e50b180b9101c1d42800f88443c0c5040d451150001155816002800306045030f161040c18800b0040201e000200c080300c04104580c482d0300b110340d41ca4050781c10f0b80e081d901901c2c1000261780e5032090f81d119544103010200101a4003808042a12080381c910401ca18210303800030784802d61324030a100c1c85810128016116540700c1100040702a40104402d8103070707003140b0f4043d260301c004a032400d01c00e600d032048120a0070300600030b28420945c4442c1a80305a803d41e420080c00034801601aa010702c11400440310601b07c146402e1440b030320301c003d855114101104010800c03412103070b60a00c0d640150340003030442c1e103c2000d492101400403001203208002d1840769046c5028030b80c4496401420680005410a6100d0040408030000c5082d101c551044103807041c7d80e555108a080005a10301e8010800300d000c50b0300c00d480d102d141c03544103055800911082c5250900c16144c00c6004039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 726147886 1250 726146636 726146647
    0x9060105010f0503090d08191803030b0607020d06020d111605100905100c02030c03070605100902121f0e0c0904060e090a030e030703020604120c050301020708031801060f060302 78
    0x1030b002000300001d021a89440c0d851407400c00d0096443c1c00903480d101c028030214201048000420910041c20001c0c2d20408200000c441c0d54a0301c1003018244055020a142c0614003c090600108031420103030040c01c0744021008507a01d0700001c0d40700041c3c0070015540d51881001b03143e000802030203c0003c010005483d2500740c200340d0f0030220070902a0603c540360035011000a0000700c0c030030383d1034042c034480042c0452101c0c1e0280d0451140a01c2045280000950b030010043c0c00d602250080e03c55000070010300340c455052074102c1c440c0c0480c49401c40803c80010703142040c890181c00c85503085800c611281c03030313450102c0c280c000d00581d541a1050f001003640581414544030300707001880800c1b40c140e10350800e51680c030340302c0000c10405402c1240750b40c2d20480340d4030204402401943d0241060365a55640e018990075a580114111f0710300d40010000141881e05000b0b940c5141d401c10030003403840d1501175520f02041c030044500c40e000c0d52512030008120120320382c2d000c01000c69803405030781d65 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 726149136 1250 726147886 726147889
    0x51e1b010c030b0f1c05030c0f06160206060907050d0c03050402030c0d032f07060306051302040320120601170d11070b03071202070c090c0f2307060509060105 70
    0x548081d80d284003010b1a100b00410b09540d000c1d0a080c01203c02d403000603d1110001201d5240a69024050a980301c00101400140c030001026400c030040340b0103988241d00c80080000b44003404a10801c0182d02c0305000c2112407402426294120091381800c91400000100da002902d40302d807012008640c6e2101003000303504060144400e20402128400514041d568018000c485200d0001480c81c041d0401000000d40d4220002c0b03c03501010103d80329941c0d2414000e02a1400c1c0c01000e010310070b4040c1d0080e00c11014002c0d030782034039808442c19104a00300d0020500c8940c43c004000d500c81132a00ea800d10b01042440264007030045e0351340103d03996102e6108035160070003845500e02003110034004224000004030b80740080e505400503155885c2c82c0c2c031074100c680040c42c01140c0b601c20310000f401c0080096101d0b00700701b1150201024048115a650241d4000d422182e82c2000b00e410084600200d58020b010780b20b0b100c403071202440c1001980c1e01c400f4100c1c1e400716000c032215800440140201e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 726150386 1250 726149136 726149141
    0x501050f0f04020d060507030e010204030c03050708070b040b07060f0504050115151d011115060a140609130f06030303021e071e0f1203020d0c081501051e1b01 70
    0x40301d581040709001d8145607012640c51024214064480c0d580e070004910080d00c2a004000301004c148002d54469499003400200b4603502e100c212054402d0800005019201241e5038040764070040303040b81820320384850004a0382c0081c10444050346d58541009401c440c3d0b00c5060300a40c001c400002e10601024944040c996441e000306003120ba150300300d640001d13441050007040d84540c9003014508034240c80140c8214001c2c80042151b4082e04040d1407020011050061103402c0450350802510390b0f5900265003c9682e6156540128040180520609000d0178518450091031400240c580341440407208940898104900080e00003d080710403003951914803400780da0400c6954504000b40d901e14005c6e0004180e024503a043c41c210707d009120760528608010b0360890000008000c440c0300040c000c0d80034001c14104140340921114406100d458464814009c1480050203180014010b68540d00071a14050782410110300e0101400100f070080c20000125080d10510910300f500c0080c203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 726151636 1250 726150386 726150391
    0x70501020a0f0e0a120f06020a2309011b03020708010204080d03060e060307030314070c0e04060e060603061b09040e0703020a0b120a0b180907060f05030606041406070f0501050f 78
    0x104112007030b0a1075280c2c0d416620808a802c01d01000911031703650b24014040031200c12000d0011407001c0382001c01580c02540c17a800848140745602005211043c40540c140100001b40d80061118041c84041308503000c503003030103e40a40126a021551205a5826644141c001040c0c54216201e1a05107980500526018143c8003a40c001c1c0c51030705001207030707940c001480003608001e040c0e000c040203460701e0f0040301e01c02500b1820300082152204140c4045a00c1501c046032500e00e003402000e0f208001203003d5028410007400381001d0745850180c281c0c203824014000810b4041044859403650b5203100700d04900340e80c00013601171784d85140104040354204e9803050110704010420340c000d030328003080050741c000403151001803e00b00310008252402008a07400c07030b17044542c80c01c4c405044c0c000101081291100d6072468641c00300c280c42202d45000548030f0640201060106000c500c5200c907842c0e280c084058405424005a9118080f82c0c09820300d054a4603550740e414455089140302c031155 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 726152886 1250 726151636 726151667
    0x6080c04050103051005190507020c010905031c050a030e0106080f15090a02040c0527030105160203030a05060f18070f0804081c0f090813090b1e15070501020a 70
    0x10342d031540c1c8607141c40b07152400c00c0e001c2c13590390f850015814a0201001c141100e1121800704094035000501079074440408141d0341c041580a132000506140009020032200c20b40c0b0400340c8140c00b070010070b9a107500202c0d1503805168554260340e002c4113003446150004c11040f401000f240307264002c1d007420f005424103270007052405c5a04001c2c0c4410300007101120103a040d10001003490b5548000c8400e4024059080064151200404a04552080042140f00044000700300b02d485515074401200b072000310030805a003041c0b0004040201a07806507078040009030040c0d00c505504d00001d104000c140a802d0700380c00e140c45c244013120b507004a1009100752035081c9281c15040c50380314000c8600803203501504004440c0c11103148131600d074002c41d40c280201034007803282914a01e090072203500101c5851224040008000540408034002c2c1902d6020160110508000d50340200e4103900703d14050325000400b20300100c400c501220000c14200f4051400141c0b11000c07a9002002c0c441e400003e036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 726154136 1250 726152886 726152891
    0x9040e010b091305031201080c010e010e0109030b041b060c11090606091225051801050a0509090c0d0f11300c130e211207020a0606060306080c04 64
    0x255015100c1920b0b141e008002d02c0340000c292003003441c3c141d1540c4243d030403580a614180c400043c050400180d62000340000f41c031600d0901380c08100440b1100710b1043c0050009a141400700f0105403210307001500940140000b13849603040d900710704420402580a1b82c00a0201340130101444161514405009022980d0441c00c0c1420390000d000d5006207a40e603031094544014940f690350042107590440c0d0100704168134407055442420020752058400c00c5c2c0503007441401202c880c1c24440d48141600d100402099000c1c0c100414000b4800c0c2c010620403c5120340908044542d50394030340810b8043c0b1401040781042c1c514603100d0a000e4140410381d01646220304160141c8c00e5107800b6080003207810015110f0a9000c5540600d003148200855070041c0d200b41e540e600c81d0f405a045103254020010440312245229503e001d5030b500c50a00c0c00090040904c00d00c0000c0b01a02c2d400b641104c035602c1200d118014a440d4801100da1035805138000c82d5881a00304009401440036011006d402c0741e04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 726155386 1250 726154136 726154151
    0xc0303090c0e3c0612010e06010603060f1a0a020f0610031202060601021c020a0f12030506031603030c0215130609170601030f0f12030b010206010902090d0308060f1509040e01 77
    0x110079500041c81040f0500405000000f842529407004003040f000d224002030280b031081640c601d84948081c040d4000007418501d01080380c102d018112003c82e480e20203440b10b40d02452800350f100340c1000c5807c60450144000e44a51220100049401001c6400d840f5110758510300d0300d0f030452508400620190b402240401030305d030ba00401e03580792640c0c03641c0e412a4400c4000c3c0c0100d0810508142c000c191040e4680c0003c1400a02c0c03207401d4102d6840d440401079a25020205641d980c4141d03c46000034004850520019100f880d0000340d03a440039000702002e600c440074800310381d0800450b00c0c89080200c40e00b08809a4041e00400040580000a000701c046500b0019114030050001604907441062400304000c3c50f0100000181d400c103050071100b4603e0a0010f0180412400482c01071080c00000b04e40001d003807003150b01c420340c003c080c1d805004140d501641d400070000c107181d83c855036132100922244c803000000c544020101000036501d442c010704000484404094043c1241e150910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 726156636 1250 726155386 726155461
    0x1205010b03060d0809130b0f01080c27060705010c08241207080d05040311010801050901030b06010306032310060e010506070f05031321080a0c0303090c0e 68
    0x450750444000d4643c041100000c1c18101014410007030016080400c00303605414100d031031342c01400c5150b4100e0741c40c1000300824004540c0e812094582441803182000070a003074a4040211a03081b03660000c1c602640170011340001e003642c000f180256216511a85210f003440e174400c84859002c810b0400090b1041e5025110341c01c10310070304002da0b02030341d421140a600a20b0802c0707020002c00f00c41040ba140e4402d00c140040040e0000c0c8022186243d80c54900301e1158014101e10f8140d42018051140c1a8650349400d01891000340c1084c0c18076583d4840030000c03030580c1103540716542c08031440614000411000764a4445e190442920091408405010303d0300340c84805411180e046651585403881030a14405034245100020054800000d15440411615801710115018002c0c250040c1814a01c030090050854100800c184402c0000d0b0400718020411841c50314000c0c5000550350103a9a1042c000d60465080451441c540b0700c10001203060343d500c100703d0b036010786050348003040c20000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 726157886 1250 726156636 726156659
    0x19030f030507260406030f060e0408040e0a050c030c0d09140115080309030a06050c0d0212041e12110712060f0b060c070306180b0a06080127020603070917030a120501 73
    0x981e0040644500c4001c001f825075821440140942c10091b034007605080c07400c000f891b44644644040c4076020310001d100d0034040e01c22544070350785400c0018030755640c445c10081160b00914012600d1942e4482201c0407400a14008114048040c0005030956441d6400c07020903039540d01501e01a4020880d1401684010443d0010701c0d0380180003003110740356070740b440b0f1690042160004882c0d101161707200c0d06141c800c550300d018a00071303c1410369200f44422140048a5064005060700300b140c4600e00381c05216507041407203110304400755110103071160300c4924801c20111007034580c903444a0592098010713903c6448102c0e00100d070814505400c105c0855140c4e081c5100103402c50b40c0d260007140319054000c0c609034285500640d40f50603481c2c1b80034071400034025406090798a600c0e010101100440c8034140b8011413589080d03d040c4440c050703081040990004154104000712078400142d42c9005002c0488441e0465028540b51a0341810003802d000301d4106806a0b6420600100559207a14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 726159136 1250 726157886 726157889
    0xd320f0a0803041e0809180403080411060423030c101e0e04020a020d02010506011112030612030325081014010e0909010207030e030d02030919030f0305072604 70
    0x1c0ca9101c0c0c1d102e08015400e8011102d800000c0d560621158041040240040036103840c126602e00d00d4500000c0d4803c1c1a40c4115070040100d1480070219002c50f400001000011400400725441c00e9110024003006000495001d0910715107680b07100b00f9450103010b00900e0710320640b800750908151590013040560040c062296181045a1480c0c049102e0141071490120181066556101c4000020360341c1ca070041c0c180b40194a00800f1940341d43c4503004110002c010351000700800e5103103983d500500c4c0d00c058140380d40300b89140030b021149101400594461001041140441111514807107a40610f0029410811002c401040001c0d13008103800300654600380e41e4880810100c500680e603075400607215035032040c0103070200708000030150014104544203550701554100201c040c5aa076040848a010158000703011115190502600006000f51050f003000840f950340e07113800011a04c0000c0c15000074200080034420721141c2982d20a90710f603105509040030030b400c4407210180c002c030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 726160386 1250 726159136 726159143
    0x60a031d010c0f113d0504150209010e0409060501170a020d0308040f0c03050105100501111c0c17040501081e061203040f080a060b1005040902090d320f0a 68
    0x162203c4284000b00f10320f0307144d8803c020a070000c191050710040d001ca5200300108002801d841c240c1c5c03000202d240155805103034044406240d48102e41c2e02e10005e074015403609810441006200007082e03807140203203003d0070b004490004895040000758054070500d420448925480545200016214074480307003411505031070010115100c44c6003144842c200300c2c1010b82a0f508405011090203819070000340503031421441e08440320b03a00c1d8019074990182c40c0e1075081d281c1140c00d82404d5150fa200d060001d070b50103480d064800621a50304c14540d804440c45400c0c1c4264007007400d00240d40c0002605401000207903042c0322410442d0b921040d00312004280e540a40526903000700411410000c0c0c41c06003a410740e00314030a90301d0f91900d03070352010711032010b9806074100b084040c007501b41703a110707000d01c02c0643d514186084d050043c1180079510962900b50016051445807020540801e0511498058410074090b50001b160b940b81644858045031541034100034a400396201e80040d190031000e51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 726161636 1250 726160386 726160397
    0x8060109030b130609150b091e0f0a020702030304120b0f060d0f060e2b050f03010b030705190f03050912120402041401031209080d0906110c060a031d010c0f 69
    0x1610702c1d040b0040c02c101c94001b40b0161040c80484000318154100400d00c40007540d1000b803e5651607400030200c074450010300e00c041500d0010800c0b40b81c0342c1d180c165010402c0c100261a0074500d5012a18550203540004192081240c820040003410010319412418801d40c07a41c2038200000090b640c19600c0d0340040c004903201c2e07507003410401d80e900642c411007003110a4511140d144640f0000b26040603031071741c85540000000190450240c0c0903a0540c0b584041c0b41030543e8200b920001007030f80003420603c284202030001c1102a910842c00109000b5540d0714005003410510000e01501c0f400381040c80d2a400c41c0303052ba01110242c4040d54003885141407480314035203490010800611040078180c2c0300c4d420040c0044148000d043e91148680c445c1d503580a07030250707036841e000d44600312600080f0000b01464410080c20303104107419031000781e0050544004000502c0040c01c15030008580b0404a5140c41ca6040c0007040350011444290b0164024403410a05070002401150566058400d100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 726162886 1250 726161636 726161671
    0x304021e15030108010f05010e0f0412020c060f0a0f02010b01050d180605010305010209030d0302040302030d050705030c0610170102190c052415013b03070b0a08060109030b 76
    0x1a540c1500720440d110040d5000e5982d43c41d840e240d400303049030f000805c0c2c030301c0c1c1080000035803c40c03100d44883c85a6002560300016848641d1400141040d8107058802c40c07150445148031503450074000c10f44480003103242980d6a0707078a00050650010007000e001503924000301e01f280b80e600481203c0c40210389020005e803d0302d8880450003018500100a07064038600000403040240c15030052400d04011003c5070756481c0303203030380031000c4c0c0c030844c00300a4054005000310411280264041d06019106600740ca00341350504802d02d1405a04407001403e0b5490031408100c0181090841030095a03252300035894098a00c03205864021484424070400009140010038400240300004010000e02d58034109d00d15640d0f1790b5100800e003a00d84190440c11342c0701006141d8001e00c08601941907000103e0091110311907025032032400c084100565030329000c01c02c107507690180880c1c0d01078920131203811744a1000b9940107111f0400200403d062081c41d04091001c100c00701c520742c2c1d1281c080003491b060039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 726164136 1250 726162886 726162889
    0xb030102070c18060e04080f0711060c061501050c07121e0305071110020a0b0a0f060605040306050a02280507150e0d0813020405221b0b0304021e 64
    0xa100701c0201502c01e101d0b12202041c002e0400c0010b00c180c1080b48014400180c0322602c0d442d80700426540201188000c00c100060070030300c240a084841d01603000c506800140c4c0011564070350024005960030341142041241d03a41c1d403081c500804072420718200d400c180756101c00c8c560320070550254405840e11f031071608040000000d91840700841000003090380e4515880d0244c013a401aa204440d4100507461142d4a810031842480e400750b20340d0f00a2681007490b0311541c190b03900c003030b04814905850310010040c2d02140d0240030000d140550700c0d00d0782c0d01e1450800a0458501400002da0076004019603403c46d00c030005400c4550900c5030f02200d07a6091610b01791590300ca5000d00a103030300313003c03260310450008503400070307240701c00c90016180b208031004070807101040c007103940e40040d00c5151b0700c030005410b0907031146a0003e441e8a001442e5402100790b8007100b2440703041110044002c00c81014040e810000100092100003a01805d60a060740003c0e44c0c101c9a0340b042070315a08030b400c070400c0c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 726165386 1250 726164136 726164141
    0x203030d140f09030f12040c051518030f07051207031b03050c0f0907140720011b0c0e09010b04091b080a0c0b03060303040815010302180702100b0301 66
    0x1006409208102411140c4802965a00100c402d00340c003141400005501140100c2280e40c414011042140f5050413601aa18902c1000c2d01c180c40110321107902107082c0e1914041c222061040740e150305d80720302e41d81000c400300480054411307001303400c40d12054010389000901102a01d504a40c100240144c490348030349030640560025103041006494042c203a1809402442941d008506403400e101c10710050000c0d0303c480c1d031000fa0b00040c48000040180d40300b02031440c10500002d0000307191109a03200d052445058940c40d218001e103410200207a1368000d0000d44000c05401c80c10f00060110303448072140b1802c0c42c4206c1c400707504044000307000b540d000e601030056100c000303008000c4200b00b41003074030404c015007010100a860705100410120000101c1c001010342c00000d80728081d080440c104010740000d892190148402d00003c5107074102400700360b0ba1640d090410305200d40c5103004010500d01c0c0b0004441c40c40840005200c151503022600d00345056541102181680000340403e00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 726166636 1250 726165386 726165397
    0x714060f071718090112031d0d0b0f0a0e0a1109181c11070f150c0b0a050604060b070b070309050c0a080609060a0605012109060908120a0213050409020303 68
    0x220380c20700181c212180c3c0350844011800180941d555502c030383e2a030034240031020034088064041505203414007869020018101c19280b4041c090707100c2c84e1410b41e1528012902036880100c820304110401c0300110207441440a810f403040700410004031152141c4490704206401140145140310008807520040e04844000707042080403952007059031010760907108810120780002032030017204100e03a50300009030340c07040ea0ba02d141c041d140d2a180061035244040614403100601c00c0101604000c51443c8400c1403092041141c00320b02403424508003c12110346402c001080d90081c0424000f0030701e0302c40d03110b5001400381400030743e507149400c20380d00d09002960156030003842c405010030301c0c40012440a01611080003251499183e14500c01c00ba940e0f680541030002d0b044841560310001030b80d2404800c9030b458840090b40b880d031346c1c03144400d85d094400c0c20740d103072800001d1a00440c0605e000c480e6010340106400c60500240e9401c40c45085d2892007018400c9071145085d00c01e55405008032030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 726167886 1250 726166636 726166673
    0x1090b0a180303020a0515090c09041a13060b0a0b07080c0106210201090f06080f042103020901020c0109030309120623060a1203120216060f0203090714060f07 70
    0x50150380c0780f400a50b116080a000c0310640100412054001841e101b06401841c174603014090943c01041400410360b4020406d0750b548800403641e00c03100c9900066070307020b161940700f510340080035803e01800f074400c80300036680605400d200130058000800b09403482c1c2d81d070000440b543c1d54941c0c1401405048142c0114003075281001d490b01984100801c022040c901c01e0b00d403460384c10b81d50210303010700790f02c20f101c2c2c0c4001c5034421000410f0103d488111a40c41403140d402d800c10304003400d5084200b082100d01d101d010aa00080c0043c40e50380411601d050500e09103052010541150307402030145030035102d05001620006811800c1000580100c0c00e4144807500381c1705a000a00031103d003e050558000c0e000b0150205e0100e21005071954004d003c907010340321115150f81c40741d4150001d50003401041c2400084100caa40001e065000310a100b1140000160f101d0401400080c20000564800d2544034080c0091003c551120415240b441c0614456a83c40741041d0800b0020f10744d1081265 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 726169136 1250 726167886 726167927
    0x62d0403080910020c12010b040b09010e04060b0303040f0807090515100f0e0402030f1608130b0a0e1e1606021f060b03040f030f0f0203030f0c0d0f1b020c01090b0a 72
    0x10071890550050200d540f0849e41072100b640802c06004c03083c01c0038001c04c14403811440000380810065000750a1040001d0102c0b0300d02943c89190030304082050308010240e401c803c0c6c04210245560180c19006511100420580c0352001c0004040e80300c1d1a00e0f2030240041e0f60041c8441d20300540701e8000354540600190754274070708002410703c1d850040302c9090300c440303031040060781441c4900c0d030952241c2c000c21000118800d40742c03201540306900502c850481030302c07440741088800f804d201c1880c0c01108900164980070000ea14241000358500d0865410040c10702d040000b103500050910041c8184510006080e84222440002d428107400c80d0046401c0081403004111a03480c00c407800c54002d03603d41c0c141004e81101110f0141108100c17900582c02400400d10800000d455150841441040c052030700b1142070444081c0d0b06030540018085540301d40170041c42c50070301c04010466145202801f0b1032481c0f0740010f00503401500400300100d4001c501041d080d40660140d108080640c001e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 726170386 1250 726169136 726169159
    0x60f1802010f09151e02070807090b0406050d080306091b0d05150306090d0201050906040305030c1c110c0601150c0b1302041118190501140702062d0403080910020c 72
    0xc1c01100305c240032281c0d4401042d40b14032000b48003103440c001355107081000d0700a144c0b400c6c1c41d181c007826604030708651143e6190780008403070340c42ca2002c0b80441d01c41e00c0c00756100d00c0d01d001040400080108081c020520341100c1c009412201710071103c45a59078080000c1031b4440041c580001da44020f101600740c401c0d0030600c0504403000403190807912859009000b16a11071801ea5140d0b081035800601007034090010030203d00360003010f0b01101c17000050320b4020200c12108542038400850750203c000000040750f529802081c0509070150002d40210300f802481c6038802480400e14102c0904106031007400718000f0f1010034081040c02d900140280199900c1410f046d02036032010922018010321160a5183c07030400c24508000000c0781031408890078504001910050411066104030001c00c00281c0b005a851201400c9035034850142d5010040420700c100342500c640540d400d4000d00b0a21041000480301412540d50760030544504a250500d4102a45058401c0d841c0c16400306010b40c2c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 726171636 1250 726170386 726170429
    0xb0d030509091006020304090914011103010503120c0a1e12170603011509050613020d060305010e19060b010909140712021303020d02060f1204060f1802010f09 70
    0x5000415000c5442402c282c5440c469034a1001c00c130701c036040c0982c20500c010483d584007035001c4c26000d8002c11540c02e1710291030712141d00b16802c030040201c4407a000701c01400141401c000000392002041600c51500940c0c040b1241d6480145500411950781c988402c1c4100901c81d50340391400d54441020600a402440050b00e0f01c2602c202c0303104410450800200c40e40f405009004a054080c410442c4880c1840c80c10f901a01c0003c1209400c03001007009442d80f4041ca00c010041c041405c800066114210b00d066425182010000c140701d030b000c00e01c2c1082d441c0040980042441c1e01560002d00300c1500401654400880c1e400b10303060368500843e0300e600700710303683c9032034440c0c8802d41e682c1100c214070b02c01e403004034006c10703500030301a0000208c240018200302d440c204045000070003d5062045000e0b00c1c5085174000c0045c0001c040700ca1060104100041c000c0022030103044d2810710030040019010803a10070700741d5019040120603c5030024440c001c20003175003e4a8031f61412080310310420f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 726172886 1250 726171636 726171647
    0x1311030705090f0d030c030f03060f24232109011a0307080a11031216030e010813020609011e090f0e0f0c07110d06050118050603060105060a030b0d03 66
    0x54081d0b00900401c8032500f05483d101c0465090590b040d20340b41d120032441d031011210541c40b80080003d0682e14000454254002c00740d1200030144513075510494407040380024982100c690020003032111000c4850340340c611a22205200c03020308544141c131801000031080f403100e0304020900310410340340305001c010312064002045210300c1d140000f940101c20800c0c1991040581325147c51504142d9120000810902030b80e582100014201d444890b00d05101d1381031688400c81c1c00c40344903404181c1c0b10815410001c0002c03000001d08003501a442c00035a0400f5602c691b16000f445408005080b1130306a000702180c11180d81e200e00300c5021020000b101074038085060107464610311050200207074440c01c0c0024188141002e80d80d00b034440d11481c0c6140701940000008944402c4a20603440403919001907600d481402030b03c0202c1d2071b501d40f000402c207182c1048010300c050790a200c200140e984001030400e04656064a809070748024a41c000c1b07004000c21014241c0c011300c200400c609255004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 726174136 1250 726172886 726172897
    0xe12031b010216031d1e03060907140f1809160602060105011e031401031407120f0f150f02040e07020c03060103030e011407060222060c08070f1509050106080a111311030705 76
    0x140c086078a15112780307545680d941030341d10414081c1c0f007100c0041c12840c00d00000390806950080c0c50320411680003042840700c0542180c004c0410f60062007401c000204440808001300140c0c009405254101070008040ba80e05400c040c0c4400b4600c150380f100c2c00e209034840c0d03e885607030741c403200100d5840b0310301078800c0b0b034903100c64940501c15200041405115201c0a6040396031011050204841d56035484490f042140710035912090206c0d100005e1080741e001e889070a0380c20300c00c010382d51410007102d0304442c41c000c0c09810455001e10309100f042c0e01c0004610303042d42d8040c10000107010700f10004070b0321034100e0800201c0f00480820018204585a0050411150b10817030700d10360001c41c1d001c014081c800e103104a900107403a000f103100c0880c07912002064294014402c643e003c5250b5141c828148144541001c0700d540c0d114117440503c1800c1c81070002616250000c2c002c25856900c4017044114018841c81c0f00e0600c008507a1103d25095102e100481d508015854030791505880c060320a0300300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 726175386 1250 726174136 726174139
    0x504171b010c030b0604091805031309060e06100e060915070b0114180c0909010303020d08160e040b06130b070b2a03070e12031b010216031d1e 63
    0x7042c181446060090003407100c44800645034500300362405000c10302a20220b841c81012042002180003ca0380c02d0004202c1e43d2413400a88142518280a2904907181c40d0700095201e0010b02c1440070a03a110340e98449500c03500d18103280030204000015800744107608010341e1246400000302d04004101c00600038241c0204a034a069030782c0c0750044510b5400c00185650f001c8044000403882010003000d19822001c080071040c00c003000341d0042440e005081c0c20640140c2c2c410080080344030380c0b10b0985a4400745038004540409042403003e412007810190040c45641c03140703000c0c402d0382c4440090700c180034500558609581c0c1c2d0740c003015816511000064901d0740607000010102031f10424007500c1c0c90244091840440359000000340c958101608450420070091026034080e99003c01c0310810b51250400f859946c1035404802c0c000b801c0391200c483d070f680d005201e42c400b112201603154400d19058100706c0d041c40d4000410524800d21140742c82d9125641d1a440c4010210003e1101d000c03c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 726176636 1250 726175386 726175391
    0x7171e090a4d060310170d050a2006010f1a07050c1309020a080706030b0102190f0309030b1003060608030c0601180902041a0103050f190504171b01 65
    0x401c08a40354422522000c0500803101ca00c5a0422241c2d410028842c084201080112510440000180c03641c0c8240e9040c5014500d568042c04100811640c01640c86c41560040200e0014a24043d106002d840d00c042c050068000e0201540315000881e0b8618440c102c2c181c41c1d8940e140c00100340851014010564030780c81302e2140890440700c94003225007a1b50040300070300b08110034000b0032004400a0300b4034090951108076800058440407195005080d515014118980c140080101141c00a05119045501175180c2c0007100012081100c540d60700301020310301507001810151018111640000e022820307a0003041480f081601481c019070f840307040107018141d5036420f000c1ea64040d00307080c0f2100703820890041106440c110707011080b1b11440003000c40c414500e50000b6040301cae20f110090a88141d100c4040d01150b130706100d03055202c0e20000040f15503003010000c16092000000f1250111075031900450240200030250454407005580c215964014a2089455409104800e88001d60 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 726177886 1250 726176636 726176663
    0x1e050901090308073209060d0902032401050909120d060e010e04121d0604030308010f0b0a020307060203071e05091905030a02010e0f0301062c07171e090a 68
    0xb4401c2681703030701e1001c440d11075406488400860041a040500b80700d01d5908003049800c20036112280503041c00d81c039035440020344800c540145030070035450244c280b52907142c80800844080c0e56184e00782c15110103071080b100556400750f80a15200e86120407500d407036004621103c082c0c52070740040060707988000311813101d640da86100f9060b411055500400504c0da072540c400c07110384100e0380030740c00200385104c2d20b5000c590400421070359400354006800050490f40180295880da0072520010700c0401c41d103c2c54809042c0c0c00039100d000d0701e00c0041c540c40d000000b040751035105030311000112052465108000300c1d031950243c010360107060000c2c01560035500b80a00380b4040102c2c042220805130192001c0d108075030045030001054020a503001c0c0d10302e501c0c0055600d01744140000340921403850355600d149a17002c00089030b4003907900b1800c08050810400c85036485081d80c1c1da802500501001c0300d8981404a04c1c4045441d04c0c81120b0594610420010341000103814640c680600c56040c03440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 726179136 1250 726177886 726177901
    0x11d0d0201060816120c0509180c060a08010e07051908010509181b040e06090703031d03100906090b04110111070b0306060c030412060c120213091e050901090308 71
    0x924208680848a14a84104105e0f910990b00c001c80404d218440c5415000c0c1c0300d81c0000e601000a80300044000e224038141c00340c40c0020017a0205100d0102c44040c10203840ba000180101014000d289562001c0d2001c20b060754065001c0c1c2e1090150508800080d0800041c010003502d0240b01e118030911b20040841e031201c03032022400c01f01854a030050305100340d02540c0c804031090100301c00e5410507030300c406840d40c040081c0310640c041c0d00201c01500516246003401003010302188960421041c4498901001d56000102c070030b60070440c40401f1840c00c0b1503084c2200102100c03407020b001c41c0c020301c0c1044200498254030030f2428030242c803000e5140e020100d040c1d0344d50b5454091000c1c260001c2000c5111480e01c04080d0035084100070890740703001e8031043e0140c00c1c00742480f0201c60242d1214181809250841030900081241100441c24801e42c080000c6030000c851040c10300003969100d052105415502021020f180d1000d8144403a04040090a000b05018442900012035010229103030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 726180386 1250 726179136 726179143
    0x90809100908030a0f1b03030203061c0203070302060a0509060d231501031a040203090a030318080708030901180804030204140c03070315260610031a13120c0507050a0b0714011d0d02010608 83
    0x50cd038010340240381260941d0b0034804186e00241419081c0b00040c413001d02259208001044809210580802d50f000d4610b8180480c0040d01c410b000340c0d1134600100005400320101c0070b0f5102c4002d2030040b402d032107120011050019142d080360780040c000000c0080d44480001c041c490306200360340812540c0700784031841959940c03903580103000b004104044400310301040041c40d000f110000000402d0b0703482030420030404044020485016001040400542c5020b119041e00004030701c082000c0c0d4030b88206407142501c0005e00407400c2c0750ba2034104800c10f00c0804119001b80c1408130454643c0484929541d8a0301c0014507880603510902001643c019101d21001040b82d80c08410f07242d00040458203104400d100620700c00c3d010310301c0b52002000c50048000d01e440c1c001c681e1075044a008281c1849400e0500d1a000030b4010b54048804001f20700d2590110707a10300750080f400c011901c0380914824007411443c00c00c0880d1014485101e45120000301395900b10741603c1c0c008005440e40c1c1c00c2c64030348 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 726181636 1250 726180386 726180439
    0xc09090603080c33180601060c031d092206060f170a0b18031603050c1006031101110102090307091401121505060112090809100908030a0f1b0303020306 67
    0x38076040c000000a504540510194201445c1400054000500d003811441c01c0b400b42c0c008000281e0400180c0141500164201082c80f001403d28100848190200304024005020b40c141d64528046005c0c2002045454800075a030103170042c0401070b6280003010000800740210b445003c5947c40c0260020000502e05c003029500582000e40c17541d60a040001c84990420305800c117000400003401010505440038800ca4032a40302c660301e40640c00081445c0030f590030358103013030340d46002c03000d0000c2070f590750941c90482000d10f00703142915000004c1c0b5000e17000e442d03c0980c16108084c808074031203450350000107168641071300a4429030798400e503564181e101d00030040c0c200010b02010341241c000c01d0b045954008818101005034009403c0100f08503441908140d41042d00481d00592524140020081c0c0c00e080740b81c000300d02402d0118a41d100d00c241c140c51018030200d015520b4405004030b400c0050701c1c1c0740d03820b400503002490a0180107507208441440c46840d000714891444180c40d210480c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 726182886 1250 726181636 726181693
    0x6020d030e07060809030408070617010e060d080d0e0f070501030c02120f070204090b0f040605090a02060d09110a15140c1b190b0c0c100807030c09090603080c 70
    0x103420b9203410001c1c1c61038480586202c49a01040002061501040002d00020412a0f45a039600d0243d82c42c0e94070300300c0041e001114210b240000f0712006a440103095000c80c2d400042896441041050b0700004005450205016024222402002c11070114075201200e00a0b01c0c2880020203902e01281c544401ea4040c1c1c0725445c0a000d660701d41050000036040c3c1920241c00010006043d4450941c004000c444415500c038444042104010040c028540c202c071510f0024120414294001030043c000c1c1500c54082d140c0d154502030a024886110179241700010f407021402903185d0005c903080c040d5505410b008220b200b07204445003581102103600c1440c0020180100d01c0c2440341400c0e404074030070200e55012060880d00e4025084035480f040c020300b910340007159074000160009060510780901c840c41409181d0745404c03420b8000035501e600c01031902c0e0028248040e52016541074041d5046054440d1414001008021944006001291010040722405034243c5e40c2102004c0c200324000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 726184136 1250 726182886 726182893
    0xa03060b15131206060308040b0703020c03031305040209040603140a030f09050f12010e0607050717071e290a0e0d09090b01210c09140d030f020307050a03080106020d030e 75
    0x100060200c049500c40f08510403100815113a030350b9103070f110301d0f5085904030095504001460108054040200042800e016000707141010003001e202e001e003404030700c50280101d800184001c46030781d0302d50044000c0c5034030012141c10b02d070000700602d5070751240040840c0443c00b01900900214022016113084030002010601c25040707803418405054100211030450350b482c0e40a045030850240081807140c0410b81c1e51585a612a08100c0b080032141e8091503075104081000d09c01042c102100d02032940c81948580391610320030301d42800c45c10399072404056140c840e0f10300850301030815148a4010101c1c448103001420f04074403969100d000b44600740002c11801c5400f0041e03880075130000140c01905040469242c103403804848a42250385079400c410990b9900a500301680010041000d48404522028080000808140350110403100a42407203000244c1d011242d2080007200c8040b54081d0648030100300750f12b00941400c0007801a540940600060543c2c4075119100d205011a81d0708003c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 726185386 1250 726184136 726184139
    0x20414010c031209050313061403011509080712140c03100b0d140d1107120201030b040204120b04050c1e19030803090f060112030e1504050a03060b1513 67
    0x107594480031148200c0070302951456020b00c2c00854880c150402e8042c2000c2c50307540c222140304842c1c0c00e603250020403d020001000744640c00e4008181e07415a5004c0504510f03850200c0f03015618028590b100910a1250a10100e080c101190211030007512400441503024014800691540103500950b03406501106e001484010590000343c3d070440058000c2140b19890340f0350b80c900401000161403543d000700c42007013210341d0215540c11010215405028200d0501110401d5885049400303030400d610b90680c3d6005d5031b0351f641250000d08040040c280d9102c4503107031100c0c9500c4d04031016101d901410507c100d40b41071000c0b9902d050b50b04240c0c080c000140c0c2c4402c0000528091078440d511241003100072000807005802035010f6044000248844004400e00500d40081600000640c500b00d4103110002034000f0080201218221503c0f62034110300c4070003411758012540015801241c0d030710008240001c1d6404400305400030340e009000940c0940540150344101c107800b0030070326900d800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 726186636 1250 726185386 726185389
    0x1107030f0e060405130b120105041205070c091a12241503031201150f0503070e01030e0d05070521070807110307090605010806180c0d0b09011512020414 67
    0x100060342004085904094507940810200441840b212010940d50400306e0381501d49560b80e5414061158004c0c8203c1c40c080e1341d5a4442d404a0304580140680410100d0401001d02054406000161400c0228980901e002188490300d1031080d4001c644800380070201c0c01000c19055825180c40355842030040c162001c0c0454000010031054428643d0340d071006241c3e0301030005103160300003152080d880e541011890202e15440b5401030707050120860700400742503041825280e22850705e0070a0782c1d1020845005030064003c45100348070074040d4030b2130042c01581200140c0109405581180c00c040001c1c192042c81d00f0303540d10040d504083c1409050b001074140d500820180380705071000020b42e014440403034a0200a5000350382c19130b840f1a000d010b41d503845140740707501c41c4003143e2812042c80f40104142c0300000140c1341c0d10103103c001441c003200d00c0c11074000e1860210040d006416560303540400e1b1109810f02505071002510b1550700740c02680f0680207035800c0e00e00f0740441d022844038000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 726187886 1250 726186636 726186647
    0x1b1a070615210f020904081c06060f0c020301140a020307020106050406140415090504050715020a1a0709120b0901150806160e130b01081303080414160b0c011107030f 73
    0x300f00e5000c1c90002c04000161074049516010700d10a140507038480b0050007050800c030705003018480031186080c1d400c12070242d000145141140c03403410070300302c80b13202c500100340501403d240c900c0503801716100780003104109034011032240c8a954000c001c0152200100015140e10f4480d41003103000b00f0a22599510709a0f001c811819441ea641d030f00d416a8486180c001d03114110390a5070f55800c05503003040000c0361404c251000c110184081c014508003a034401c12100071440c40300d18000780740000900c60500a11903d00984480346520013030362994640070549440841d86032404c0c0d4200403803501440142d00481042d210850080d040540d40c02d080c500408203c00500c50070410000305400fa25141c0c0c044d00411038864220104042d02c900001400aa20240600b20064035807008907010907445100d090b0031641c080a052511b6000004603494404400b001403110a0115070004103048d03010002d05502100e10001c0c06201c840c1c6032035900030b0240400180100c0c0340054403480f42032285 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 726189136 1250 726187886 726187949
    0x1803080c01020c1006030618150c050409020d2f07060b210607030b1509060309160602150907031104020c0a050105101d04020604031b1a070615 63
    0x14001070901d07a5003000f203807a00c420440c0b0522116a919410b105011840c010448078102c00b401c0403020403d80e6584003858100100402e102300c0c0c2d24188444040d20a80494000301040c1005645503441840010010400544180c0c0903011860711b0b28400c42c6217160050b03400d603001c1861402c00e081c0c0d0711040c003c0c240c1c002c407141d07100300f840103140942d8040c0c4000d03074128190356004004518000710003508a07004400c0040c030660750304c05000e034051065030455841540a455040d00ca0301da001040c1d103095400c503807d03a8014421540403401d00c0d8000344124500c145440d07008525155440350b651034484a003c06480c07020081043c40460605030000d00001511808440710004d01e5140c0a0851700150b864001c07541e0500001c1201c0007401048101084c2041450f17015401c003503000503000c0c82035100050100d40781401021060009440b0840248001100700a400c2c02c00c0d0301c2e80400341d0020201310303411450102422a02c6800b40c014100351540c841c8400307401080c0e611040341d0b540701d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 726190386 1250 726189136 726189157
    0x2120102180913021f1e03021c050907050103091703040501140114090a1a09190606020106051008060a0e0708060114031005010e030a2102280204050c1215010807180308 74
    0x12002c0e00c000d0503240c98850f08488281f41d074016202c2e5036002c0c00c45e003248170a09031046024282424410b080d1340c0403902e40e04031070090800084409107441d04445821640d051007180e0900071040106200d019040441c0b1844500d00111503a83c0b40d4560f01c01401d500e80d9855000503440d4000780b07512680e035120080c04c00405c03a440d0301d691401d40002d10100c130200c84182560310654240c21845005010700c40184c00240000c1c8007050410340860052180100018104680304000c070700241c1350324480c00040e048880c102e020701d01d003025000d00003000a071345081c009060041031500800400040da4020412030340c440f520546803c004440d44500b14880b1a458041e02c40d050700010720040c090490342c0340d501034140c1c2d80c20180d000603007854458003503d45501501e04101054803940d40f068004958100c900054589400e2400200c600421000c2811200c0d014244420fa401d07180041e10524800d980e0025250340f100e008840703020784c14100b400d150109400c00d00010314080e02a0000c00b12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 726191636 1250 726190386 726190397
    0x414090c0414010e0324061002060a1512080a0906090b0306090601031104060e12060405100f0213030312060f15110a060c09030c08010506010e01030902120102180913021f 75
    0x1400d10010f8141b03462110b440300c06c84140c0c1403a43c40e80341500c2102c6d030701180c202e80c030091000d984040079440c0c4000500c3c55403075a43d0b400d00d40e581040b48050b094040c198000c609460105541780c640d000368462001c200201d800d41c400020310910502c207560640c0c41298019003141c52b0207090219035074001e45941e05060b00c40042480d03604142026100401c1c4030703036980b140c151900c8280500d4008800c80308080b81c01c454100b0010500002c3e508043d0f03010740d24001444d807029000c10b0004c1c01040c03600044207108403800018550710210750013204c840c026081020580c1c03014840400006403003051040000ca84030074262078080e003105a41110f125041d61000c500ca0381e02c2800320344070304221a0101e00c1303005060040c08894680761002c1c0085d103000308204d05160001800920a101c0c07885d0406031200d24000854a40041440301d0741c00b201c0c002d6403a0042c030807640511050103040c0324043c0c40840000f6070344640c01d6a8401d600c40d0040d2495401d403070810f524900b80720013585e00b2070074001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 726192886 1250 726191636 726191657
    0x10f0e160c050c06030c04051e0d030c260c010524060d0b04020403081e03271c0906030b09150105070519052d150a0f0e01020414090c041401 62
    0x715494002c52143c201d603a003146d03869003840104008003041d0302e00f1842c9c01c42c00c03603030030001c0352240c0d41011074080d0035040100300c220452a01d1580d180e11941e410702900302150480b03040201481c040c0066041030750003800b13a6a504100c040c4041c1c0c090404412032151100d00040d2802d140004180040a01001040607018100841c00f030360b00544c02120360000010703031740440030390180ca80207500c804d0194440c40e504003980c44110740d07030700006030340704800302d17001c42c081c010408220018441150b23140c4205556071054004d8000d0296205e44c03004241802040d000c0d6190030810280720700c1c1c00c10001d901d540d050a00449150b04640401c84087c49100d6150242c080007490f041d0360b80e407143c03000b401c0f00114409210600080103400064070940c0c0c0280300224040400c50702c186c4074004141e1417056985a0300718000d025440c0c4294105443d00300d03a448004810b40003402592045204c1400c420041c409100880500301c9000500010130300041c0003043c901d00e800c0166080500d443c5001c003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 726194136 1250 726192886 726192889
    0x4020f070b010f0506190f0c120206041b0e013602070c1a0a180915031407050d0f111c060c2a0f08040608010f0e160c050c 54
    0xa600c00302064400761030950040000c01d010380c0401c00500000e0303c54505107100442d91130390000c2c0ca0392010040c4801c4c49040742d6254442c043c114100340c1c104010100380400600003a4485000740c50a5802881403000360b840c0514092003c411035950b03100000303440c0e2902060f08818040082e41550926503e801c1c07413414030b01d02c500041c125000e00c200507600c040324500300c0031600c0700394484140507a1180f0504600800b0106031042c040140c2400115104051100c1d04051f0407a04902c4009140c980c1c040280c0030400e0303e10081d05c0c840c00e010140c1101005407140c4c0d0703d681c0d1040e90b51242400003034500190005030402442e52054110040070801400068111444000505190707964070390550240800c5000329181c01d4094142030078131b8102c107001550b003100c140750f0216680205a400c001001180c0701500c2c020f0741c2041070700d6152034480c000140300003001c1c4202c52440e4140130300413502400303c10915003d1941c8103964504140c00e1034090b00e904120b108281c030503004803080c40300706 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 726195386 1250 726194136 726194167
    0xb19290c0f0606040b01050409020a090320042906070c1a09011b030203040b13030203030f1b0c03031c150303050a141201091e09030e09010b0c12090402 67
    0x54004501034004020503000703107481d241004000521a5040c440d82d03403441d90b00a400c032410b95082160240c0d54181884007074607044100d500081507116411441c410020121a045100b240215002d0114a0841c1e0100c5d42050360a246410038000d84260300d195490b203c0020010684100c1070384845030740d00c0c4a101201c0d1511b010110000b50000b403052102d40c0d1011026030050900440c3e4580404241c50003540d0b8001c9024100002d54001035050ba054411030001c0000c6a0040071a69034180e0076450200350b811006090185807039000107111035a202064200449070b015000314140200c0c04214441070304d000f4401c5039265078500101c1e4408000f102444007441c000c1e291036546016080004017034421004000b01c9640040c05600b01550004403071604454010701c0110740003100d4040b03400c02c0355001246445940c80c10340030300105a0486544c60004001b1a40c586007a070303949041c05054814002c82840e02d0304601040040546460064031801a0203800141019001c00c8041903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 726196636 1250 726195386 726195397
    0x20d0b010618050303030405071517101a03041109250207030b160507060b0102010b130f0c261f081c02030f0403140c06030a020703030b1929 62
    0x2c1405041c0700200e03064070441c2006140c190010741ca5464551030702030f1501280c0c0900c80c80400301001c01402d0900c07a0104008030a101c4c814142a410204242180c0b802c591081410083c903880108120148070300c10b4034403454001b40c0040041d0b02d40700401850b41c80007424228414041400d0032118141001505080901a002000c016003141001618980005d0210001b5a5018016200c0300d40c82400d40c0c41c0c481e4800804245181a100181c0c094980307841e881e0741041c1084c140d000d50072001e800c030074050140c0c3c071001c20103040040350450707180c0076600901d02d45000039500c00039800c3c0c1920400703070320241341c421074451462045525440c444940e804401c050784622401c070003407525014031614200040c00118604201c801805819005900c00988040700c0f0310046031300e0708820700c501b2000400c0100902e68074500802820020f411407501a00064600b40700c9030f80c0b60a200d0316031865500e40c3d0000b19181c920341840d82043e4030941f41c0c0007050401c40c1c1d101220103001c6102402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 726197886 1250 726196636 726196649
    0x303090605070f350402060d110414031204120204091415180c0904080d050c04060e0a05090c0f2a24010b0c0a1506050406050114030c0304020d0b01 65
    0x2488107403442c000c11130f40410110010204404c0790100c0300d04504421a540402d0001424009035198000103400d801402001c540300c40c202450903003101741500c02803007a20781081c000c120383c10b4840241940d5654600fa51036034008204024050300c44070240b40a8a0b910052002c81c1c0318043d541c91a80d006071500d600c0c4480d60144a5200c103421181d024244e00006041d1030031020850000c44a68a076a0880b00500402103800840d0500c0301220071502007088030401444542860301080c0b0450b446403241c80300288000d61513605a2810041250848500804481058407071b50340c02d540e2580241d600f01100314003000f0605060054407007103c400e0540408800040a94501e05820041c0c0c00c45002c2807040003610354212828a80e800794151014107200d0b644a42c40d60301d10907e44201408054003031040030031160340e10b5110341c1143e02903c60544061001c0e60b9903100544012a901c0c41c00ba500072070a00005d92001040c82c041d540c0580000d15030401d6507080d07181c0c40307018407007a0040b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 726199136 1250 726197886 726197897
    0x10030506010e0d02150c2406010906030b13150801050414060631110c0106171b060a0903021206040201080c03070c110f061206120a0816030309060507 66
    0x3a081da041003040c90b8000e42607800c0f415211040e030000d10000ca0300c812200e1400b03000305425860060811101c005058940400c10302c1c8031044c80001c0d0319030300403503169000451075000031581a00ca07000c4c1039a0300703030060300ba101c0e00e044100080018029441120b0300620441c0e0000533410030074026103014a000b201d008280c40381c0404d03258244480204038502400b2201c4085c00e051b003144011292300701201a0342d901d00c200e0322002001501180c001c10f02003660204660301004010350002e0110354000c14410348007224001015241c11902c002c071541e002c0340f5180c09409090034402080146250318201002035101d23800240300040300e208010341503102c9001c00c000c550f0407012407600001c1003131009095141c000e400403c002d1740e80c24020700d901e41c40c85940c04651a070f0300c1c17520b01c2130100074201a1225415200d800c191001100c01c944520b1800140394840303038010540071002c5402a10492900381c80c14100c01650510079022400c0607600d008030f1010403082d2113214001c440c0c55030354 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 726200386 1250 726199136 726199141
    0x2190512161a0c040b0915070b06041d0a03030f0b030a0302160506120a0c0c050f2104060c080c0f0d05120601080906070c15180b07080c12090309100305 67
    0x100b0007200211624500d07028500900204401040a82c0c0c100d400f100d1070a5130b2130380305a0100c1c02881900b66110314040c004181c5004001c40074030140d205a600b0340301004103401d54250a0300041d07401c8200c80003900700704910f1f004244a80c104a00c1111008000b10349c40c01e203036002c245400c003980000e0b00140c001da080001c5150540d00c2c51001080201c44650520401019038150703080081d1041620b2035551400580d1075015440e40a0b030141c00038259520340c50251074003034840481c0d81c0202c02c0c0301442c0502200c61900c07481030305c040d500160748504408103c0d0b82c807050140d003c0c90400155220303404c00c0c0310b05e0240400c20740c2e41c040c01540c1c0c0c1079124a4064550850594094540d50602c82030001b00941080d0000703103598004900d2620501301801401c0c0031280309481e078012048103080c44151141072145144564003680b081300c070103100341c0c4c80e03003811291600143e8080c3c403500d408002d03440b260488400c201c1d42252141064900e0103015000160401030f80f46603010100740c0780c404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 726201636 1250 726200386 726200393
    0x70c120b0106140405030303010902210c2a060414150c0a0e010c12050f0f04090c0f0206090703031d0612100602010b0306040206070609020a0f03210219051216 70
    0xb010300700058068816040c05e0030700f00000d8403030105020328000c240c0d0104203641d207080d120a011001d843e1007400203501e420300d11520310965001800302851264440c001c00c0b4601c40c0d9848078203c8100d068060101e80d15166581501e08900e01450021445030802c107842610b11940820300459416201e5540c5018039031018113a001c0d1900b00b00d0600803400706507404541d00d1106a80703000001d2074510354032003100b401c070390305030080c1000340304040008100030803034281a40c4003032250ba00f55120492810103451040b6600c09003202c1c0c0052540001c1d900b0400240108680400c28031030840c0d0400f480f00003c08170301c05400030190b01d0f203000404410710848200e11080c0303401505a901c028441c6282c0d10020a0381c40d64040d2000340201c0c4001403200c00c0c000303554001204584d005001e0215250380b95000c603000841d0f03001c1501c2109155a09500e41103c4191000110045801514650100b086c0d000062070368584107480c140564240c0b1641500010b00608000c100c5d099480241001c605 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 726202886 1250 726201636 726201647
    0x3102010e040b090708041e050a0203120723031e030f011a040b0f0408010606091508010f030809040f020309011d030c06010e0a06090501060e01030f11040902070c120b0106 75
    0x18030314080c81c50a118901c1c2501ca141c40d040e0310071102d041c9a100c98560703192080661401c2070880d10701d4101071070810108000840d030180094004c80c1150500504403902880500c01d5520040c80e0b1003c1c007240480c1e25018a00284800c1102401c1e2402c01d00381d510610080d00f1141d01d0040d529400000f000111540c64120134050241000f021005010f95561034a0a100e2400340d010300d0310f0007040c800184c1800074100d901070300c00c0c2c00003808030544c3c80a001d4041d5202c1d0040440404503c00300c0d0b40598031980669041b6000004501045c0d840e5807640200d580c0014000c2d6003194540c0010010000c2e9400118058075040d40002564a03600321201c21131005055529039640040241003e0300000103480da040d02d44000c1e0031102526041c0c9400024000341c0d002e4070110342441e0001610503001b8a5100d041942a05d05205071449610903d0843c0c0721040807030719240c2d0501c02481440c07410343c090801684103240c4500110345604a49202e8181ca0508403440c24018005000701035005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 726204136 1250 726202886 726202907
    0x3060703050f070309020d0804090608070b0702030a03050304020414040c060f0305100e09100c02010b150c060115030e030301030c0303030b2d0a0b0a03060f0609061205310201 77
    0x349410403003810070704800380e0703506000b5007000c0405869040440079503444920103026140d01c0140c20380e032280c2d03c640702005400303140308060f0300303004d0485d001032414100d000f100c0713040d54028041c14101d0b0301e556042d43c0640015000380c0c0c2040d55410321741103000398555241d0003907029210610389149064402006804c0d4030b0018801c0600301014481d03501c02d500040d4081e034010b1000000c5039514640004e03d8500d040c0d0340003003400d0608545002060301035000d142c494005640c40400c039268055899114800c07003c02080d075030300000c0100034000d01041000181b060714035001c03801000d001c00c040c0c5541c00030f81098035a65a26001001015011312405c0010b40e4203540100a0148040302c0c0703011659100d01030301040100d5070b1066455506c1610079009040d54845444d203036207100740010000c0941c2d011302001e0380c40030440441c04034080c42a9000300c8501e59074264415510000e420081c00d0090b001c4205810340c100ea5002c0c0c000350151074100420422402d04114815000041a08051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 726205386 1250 726204136 726204151
    0xc0201090209040209131226060907030f1d0601090f110d0b181512070810020c01091a1906230117100e0c0c0a02011d0904110306 57
    0x14120440e00507203407501e0540e03000e90102c801021942e9600144258200c145600801c0d040d580495190519007011382d403080320a0781c0303062240c500089000d013450103106407400b40d40010b074840065220791107a000365240001e400c40c0864091820821140641e4040c034050499400100051200100c284202003c2c0b10000f042880015403200c00c00c40944034803d480c12099485280d54030064071608031081010003180c449140c0c1d842d020b58405809040011136501c035802c070f110007a0b1100d000080e11800d80b4400c6004d40301003030320358041384020b5018260a03031540d52a2007039580800d244c044d0381185035440d0149516180f03021104200020130031171140c0484c900c0d1050a124035034061441c80001c5440050004141015600507605562080c07284522011680100222407003510f40881c1140c1c0c8109060200d602e4031151100a0f0055030f004040a6012840010141d841000f1a6404000c100c0341c0c00d640015403800305206c00c41c12074007521110604480b4101170308007000340c40d41c020312 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 726206636 1250 726205386 726205391
    0x27030a0c031e05040501050c0316110405090105040305180d120f0906110c040209060c0609030a3203180d02161e0303080c0913140106080106020604030818061305010c0201 75
    0x690b68015002d8021070155504014001c9607205480d0320401c11101010b2400030501140419840d2280040c0c60140c60386015038100400320b1841c0c4414002c0f01d00980c0d1503144d550800e641d010091301100d07541c040141c6d0005049000b140170454080c211b1645410301d59030b12802c00318206d405060042940c0c0000104820020b02c10041d110104406e14246c034101c03405070303481c2c00440000c1c0380780c0605d25a01c0700714000c03141407100d2110000010043e5003115141e9426164189600103070800050901c0d11491015101c09944010148000d6500c03005050703109070341c00394040c030007407800e1a85010140035a11041259001520000040008014000f1f0100d00d82c1402d06d00448402d0b50ba1000500b8800c0e5000484c50a076440429110103507000341038207080c100c000c4980303006030005070902c10008103844000f06031a8070500d80103040e512950014039051700c8943e01180c00c100010009901c400703828440490035213051050b94000e10010b00c54111203025401c00c1821100c0d0810300d9020b5a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 726207886 1250 726206636 726206687
    0xd020c03040f080304032d3509130b0102011d060712022506020f13090e190f05010221071815110a0c0608180601050927030a0c03 57
    0x20141140d501c030548045080960300400d940820151f10f901000c0103001d100995a02c84403a20310300044002c2032070608160110404000f200010780c0f0a0030303c1c00d6040303040031a5007030120009400881c0e100006100000c0c2c0c030b0690f000300170080020068007081c0c40e0806014010041d90000c0c5d5400044181c5100b1850021280710740340b0688202c0c100040706201070400001840b180364191f914510700148007569070071800810039040f500798015080507a00d45203003498014800595102d074a15250b40208225115441f0611401c0400400316520741d001c10034141d010805803000d018441201107078101500700707102c000c0c14440c480a0f2064024000b6030781009400c61006044820485608102025a000511445c20004c4c0c00c80080c001502c141000982d4540c0309400f0781c810650442c0464064070756988035510303458203218065000c040100030071801002c094416000910240b800e0000b0b0080700c070701c1425600448190000b0640e200605424141c01c40c80032804a5170303060f403145511 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 726209136 1250 726207886 726207893
    0x4121707050405120c12030912070b030118060b120105040f05090c0d0515010806010611030f270a081c030603050703171b010c0e0105070201080a0b03030d020c03040f08030403 77
    0x1030080f846150300c60740b007410501020f16002e00c80d1104150000d418400c208001c030100580d00d0340040c0b0690300031441e0780c5480d1000a40810143c00792002c01501d00c0ca140d00c0c02c0d40b905812503060403054116682c544001810411401c02440755441142c00c000e215823401d810082250700b50154202010f09003c200940c000d0045180380c1131030380c12264203c0092030f500b07286180803072803a0b414030195121400071505c04c00000710a4121000d0381e941c2c0380c0c1d1107108848582c49004902c50f00b42c0348207041c0034009811540b41c01d2240c01d20b43d01010b41401017251000540ba0580315840a400c0360015207002c0c1100b66032855094222540f41018410a4070350358625686100b188006041178403109580c083d01c4c40c8540850700c98100350145100104010b01c02d2030b000307180d030800320000308000e44043c1d81729500400564000d207805848400032507032030310103c1000d0100680c0081c0e06000421201c201d410b0544054104614100c00a5071204d003820700015030500c03690800e4125610510040000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 726210386 1250 726209136 726209147
    0x200715081f0303050d020702030118021005070309060507020f130c031d0304050409050a0f03020c01020607030c081503210301050906030a05120d06030c081011041d06031504121707 79
    0xb1aa41443c0065850321031500400080c0076915000303605500788850231a00101000c0c42c841c80c2130080b0f80107402a0280c00058038079100d42c040003008100303118001c1264501800240000c00e0003d0400d001c1a420274001802c01d034140e1a0b03e4405584d5000164003555152083c80080040603010884040000f55016500d020303510840d44140d803a03e003410100402400b143c41d42ea544400b8100030401180390280d19448052035160041c0309240c00100c10602c28011102a07000d603449403013a50b10741d100b080c41c52444441c0102c0d0540700b0307548042900000d60040e150404007001c00301e92a94108810031042a0019050741d1081d4040c400d0040420004078403600b0a00358415000d949000001980d0040c14142d40051300f407010002c40054044030218890102450001c000c20101001e070345a5015030156010304403840d4004078201014001c584030302500000d00400f156820410107046001d1400120f50440d20741072940500035146030043d070341540d0640e00e8260f900c801d14010900900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 726211636 1250 726210386 726210389
    0x9071401170406090f080307030b0d0c0e04020a0e010b0702011202041d0901090507090c030c0f0e0103020a0210020d150605040b0f030601050c4207200715081f 70
    0x320540401c08142042041da200b801ca9541c85078086000d0f0415082010098004a82ca200400e05040d030307a070040e18016200000d440d6021004000c11401c0000c2006040c40c0204102d8003c00c900d60040f03580c40030078241900a28038040f001e503407100c1d180b000409107880b900d0000d044500500c4144070b41d501c40e00e600590840624600304060395041001409058404005859802010000300b85c280c00e0b6089004402e409450030300114629940483d07401e0b601071901400203618000303e03c020740c482c1c0c000b409529860700c12100504c085030300802c00c07a0701c044036508140c1c2d03441c030340c4040340400300c82c0d040011300d928100941003d1501ca915005803003100c100c1c0c50410000000242c4aa00032402e403180200c00b0b20444e400d8001400040c4400d41091400d05546000303004005000f00c040c60b450129503249004140300303911224001d5820414000144000301c409000d0000580c0d130400c40c0400510f120f401088100e038240c0700c007400e980130143c40d8150740400b40b6584001249076081a10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 726212886 1250 726211636 726211667
    0x270a0b09010b10054617150f1c0605090604020307060f05041a19120e071406130b031006030c030605030a0212010204090905060a06050609030d2706030509071401 71
    0x4d003c00103403000140c201c2c2d00b41a91711240c00c00caa45141c2d07002e0784409040c81003c18601c103d09103481d100c259426000c400c8404d9940b044011000200310300748030041c1e230058640e01c0d111110740ca242c0d541e034205039841250107113116440301c801c0100358a403c1207144014a8a0308180348a050008001000b601c200e0180200d00348020074403140208a01c0c00711218000108030401c402801200018813000c01d11140c00c85c00c0e82004150501c103400400c0450460b2180c0104000500540c024000d00307410008400f00c1400f04603c0015a003440030000314880c1c070102c2c0100141d903060a00c080d048030445182601010324105043c0029100000c0095000350101c4103001c0c04240303c40300c030b40a032040da0051940c032401d221280007001000250123001d83c0c41140c040c0811707601d8600740301480c00760400b41a17040d4848140d01002c18099031580403200455170310883d40182440c85030805203840c0e4040c4000030380d04d8040000c0e40005010600180401c0c1d40c4141078520301c0c000007080d48070015080c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 726214136 1250 726212886 726212947
    0xb0f1e04110102150123060406092310080a0606020d08010e0916060201060302010e19050d0611030c04060f0c02030714060d060303170f270a0b09010b1005 68
    0x501683c0200030f0b60601001004840b480d40da19041d0b9900c2c20442d10080e606030113080d40000c562450408203031016114260344000b00075203041400b881c0184074000c1c0c1c01640ba440b4a601b0016152000a000307040c005846181650420205110486000d9800601150030010212182d02d81c80905a41110b11041e0b0f004c845884004000381004081c904101401146034000203c60707030190843c0040b28002d88031644140128001d1003299130b941e115911071400803d5050000b4030f031000b500180503004000004d002c610055a5080a40c07060710030345010b00002c1000c00580b070b03000150034680e480c0c81c1380c20313402c0c0c20850740400d903102e140e03019404000340310380f1f4400041c0c0c907401c00b981d40c0c01404040500080d680c0e810050480f42045003a019918014000100001c01c0020b03540e000c0c80703403000d1080c29000c1212801d506641d00d268403060364022240d40002054001204038040c0710190000200002590104584c0c043c40c2076242d801c1c08410f00003800031441c000442c0f68000740d6180803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 726215386 1250 726214136 726214163
    0xa0504021c0f032d0f0906020304050901030f14010f0518210901020f0a06060e061005070b040309030807060606230403021509150301080118020609010311090406030b0f1e04 76
    0x100300415225081300325000200b20407640c150f2081e44410420b82d82c1d01d8201c2c446444c1d00080742c580c40b607400781c103800821079001000010002c180500c0054003900d40c01039130070a4208245c2c00c1d04c01410b41c0c03154103a03e070014000029070000c40c000c11950000f0081c58035445c600c031100580340c5a44003050b280c040218085149900a00c22041200f09140540d01c06802c6441c1c080000e10b441d000c3c0309541c8128000180e42414500d0b0b46182000342616400d0a040f42540d802c18001c0c0000c008904000a4110000002d031400015113445480360001080b0a803e152004140d1240c10705036889400780c84010503400c2700201c0888054a8040c0d981c04500c001610845035244200030322160400d00d4131196921100d1140044c50503110032000900420a8210010600d05400361010b94002e000300a0b40a16602070b601c01541082d04e18400b078142840c1c070000404482003540701f6140310103042e04014900580d25000c0703a0000072004c00b0401440c4140d18404d03403d500401c002c00d0100c11005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 726216636 1250 726215386 726215417
    0x90603050f06011d040e010e0613080f07030306090203151302041215060e1311010906080c16020402040b042d2106060f03050c030106081b010e090a0504021c0f03 71
    0xe06407880c05000d0011b010402510801078001c2c90005010400350141c18081405012110107001c0c0f001d03006801b0303508044800890400b035500010f0110285540c4060008a40d140341c00590310a5074030400d41240000c80d2010721900b84150204a154248100800c0c01800b02d044821202243c101c01100480e10032000c490004100b1174200d6003023111804200660001d01c1e900102c41184079096490440b01050010349090001d4001e00f00491444070010742e449512401900990464241d05501c808460f004507040360b0141e0040481e00800240a221101c0e0701841040c44140c215409420b200f0110040e5030902d0280c01842480100101017000410040c020309000c0780d00f040b02086081d9581941c84407040c41c600c0201d4081c01001c41e6404546018030510040340c5c4d42d4000707084000400c000c2e005000f000c100550f4140200985c500c40e040c0c48420506215030300c0c940c0c00050f541094010042e2089065000d1812080c06983c824001045442007030f60303040e411704090090b02051007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 726217886 1250 726216636 726216677
    0x408061008072c0c130b030f04060506030a1a0108070e0415110f0c011d0115050111160b120c0c0a0b0a18030206040b070306030f1401060b0d060501090603050f0601 72
    0x160f04030300303101401050201c040807000003000c2400d0820b803240d9903c0e55807803904007030f07000031520280840e43c074030001404108a50055540401e008085d681c002c0455501c7d4140345076407602207415250504014440340c00c0400c41000900001c5111a40f1450180e80d0b102c100506807920400964442c1c000d5a107030310008007a118400c0b2592081a1035002010b071160080000c00c0400000440300c00b04c904e8010418452440e4003045004007052842c1464015241c0003400381c040411441368440c1601181291140b5801400c00701c01e4441c0e54458502080d421145c0152040154030420045040c1c00107002403102d01c0c09501c41d46c04025961507480100c01005000c81c00c413030311981c1c125200304155022948500c03803441001c2000d003607110154120200e58003804003c1c460165480511f010904034808070111a1610001041c0140c80350a1400f554000c202c0c11640d140d1605414401582c00004000c00b800032445d0401192600020b50520004043d08841c18050302d044481c429200c0103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 726219136 1250 726217886 726217949
    0x6170c040218061909061b230d1e0f080106030c0c0f0602030702010f0b030d051e0c0a1520030402040b0a08070e0109110307111011040806100807 64
    0x400031030700d88030040300b611142204c2c1044400020320520000c80d0a41c01808511000000820a10340348100d5079035400e0000168242e06031030b442d0b00b11b989003498000700300101070040b20380e40f0145010706205807102d0f150b803260f5020051040d100744940c0c035254004045ca0441d5001e19000c51181180c0c4c90070740711510801c0001d0a4900b80c2c0d0140c106000d42c9400550040301c55900800007400e1504299003280d0024040b50340c183c20031811100100d11030310160540c110304004116a0318064110008103610071100502c40c0e4008003910801d02880381191f0a94000040c1d0502103020000c003500312080415000200461f004004270f4150340b03480e4404480f1034806882014013640707480d1416541c640505c54104e10031640b40000c40d1400007800b803c901009034810003070540d1500403044e1084955030000ca402c03441254a281c041d00e0480c06204d0101d0420307804569518240b0620a0410400920b9100c040705114410030281000003540c50403680452002c00740c025070b4941d416580d00c2034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 726220386 1250 726219136 726219139
    0x180b0711030406030912111c120212010503060705030f011203170106030f060f031109060d050703200108060307181409070602160b0a05070c03081207020106170c040218 74
    0x881c020031030f59003683c40940d1040c05031000c140101c2c0104011103048114010000e9a41c002202401c0f51400d20203c1d000c65045600307000200c0450031891800300e8101c1c0701090040d182200041146040c00d000741030308078600385001c44c07071407401200e41400b900c410720425010044c00316650f421b2500c104001030001d07494420b50002940e44183c014060148007204038451442c1080004030b0210350382c205011a540328000f14176050f41c00b41044040440104400d8006a0f42440100004e20602001c0302030b500c2954500030000100350341d00d60000e04003c4150500c2419010b1159a94000507035108540340a030b49e081085140d032481d80e024014940900e010120840244010b814000c1a01c0090b5038613039084070741048e50355189050300580c9104240010208010004210f8400c00003001124026514004807503566a50081154003414080d040300c0995014801041d6081c0a400001c2600c20b0015003c0d44000c0d031886e84802540c84403900c50381d0b001440c4c20711600300650307040c1c56500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 726221636 1250 726220386 726220393
    0x702060715050601092903090313061701060801031509020105090d0501051807030308010b070302071220030115050d051509060103030f081902070501060506030c071401180b0711 78
    0x21149080710140500781c1e45103001c03030060078002c200e413224001c009003060345c4c060340d03c0c6020060910400c410350019282c02c07614041001b4a0244c60058400c80d401401190b803100340000781440d140c0040c02c01070308084c00300b01d011001000400c0112050440c81018031600003044002c6200503174040c4502d42d0079030741040301000e1801c03d018041d4005032007030003482e80f00703c0445840080f50b80c0f903c059000060100b00c641d001400340300c000401801c1903501c00d0040340c024903214071044080e090110001c031104900d2503c14400c80d4040040e0502c0c00303005500901060303480031061692641103000329401a15201208003c2c460100060500a60003541d85086803c1827000c003902d03418240029070100e180b01c6240160544500702c074903c40ca040c40c000e280e03200301424502004c2d5101103001d4810303640300d08021503030b5640c98000354040d40010441d80c1da00c080c00d29140d8048004a121900c041e454044407a8030a1608054513401c0d40e401810400ea030390b80e142c4251440711441500e40304920 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 726222886 1250 726221636 726221663
    0x1015021f0b13050901201e0c300d02030a15030312090206040b030c0304170304050726010e030306030d020604080403060216240605041b12060e150406080604030801050607020607 78
    0x200200300030401e0f80d2983c8080102e002e00300d803900c0f11521802209239015484a000f2010f201c3d00f40d01b0010200141b0030403035003400028090782d4800e42002c0607000070a58008180411240d8501c01c01e509000320b600d00c1340d400c614545000d031942d602e04003100042d94813840c0f0f01c0700710350390002200c0182068150454490a140300e002d804d50b081210121141800e106c20300e04085415402c1e280701383d0f84000100365840c00c0060351508501285403040d8003034004104c04070026000e0003540400c000c540011502c07031a050003014903100d480c0d1200e50035500f0010500004c5109041210700f0740350440000341e80c0d10781041d44615095421f0402a00301c0d020181c03410b5001000c083d09000c0d107100300005000c800d44410400040f12010fa0801c040e5201240b4440100d41c0110101c40b80700300041c0002440d96500e5006101260b401c41d00c400980d0302c1e003280b43c055490140f060700c020701402c1c2e004152625050ba0007034654641805014410f001c003050000c110741c0c42c541190017065100c0e60801c0c106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 726224136 1250 726222886 726222941
    0x30a06020705060702010b060f03010513110a020d0f170604051b0706020d0b090c09040510170c1807080103030c0f08040b090907020d0c06051015021f0b13050901 71
    0x59070f054602100550920140c441c880c42c0c40c0b410760b0b0001c8407010003a0300c1c5034a41000c01c04280103100c00b84085d20340b80d040c3c1c440400202d2019144440540d00502410707405404002c0040d0468030411013404080404000075081075032046a00c4407040d00c00003000e450f10324545408140d44882d1005580002a5040030807d164020300810104900e090006001c008200242c503002110ba018454070705000301c889034075164003c41e80000881107800c1c0942c1e194800e60140b0410800060342c90f46c07151403c2c4182d41801921200712100d100320310401818540001085c810f418800a010080082070840138404266951040242e000003225580c60741c1f001c841e1415003007090447e124082e448005545240003180e040c0a0010075681d510300c1c180140c4d51074000f03001c090f00700d0640507030070030010440600140d0701e00200c8009400a02c00c4c90011007801c1094011000c410f80b40a0800c0c1d4006c030b254880c030081d40030109142c01c01240f141d4900220600500d010985c0c000071030f4141d03074980d241 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 726225386 1250 726224136 726224143
    0x30403020607230d080708061807050403031b050c0d05070b030a0515010c1101050f070212031b0118030302072f041404170c07031205030f060d0c0311030a06020705 72
    0x840402c110419108410303801940c4e180d0180450200202d400b14001a103200d1250300e0701907000c00004c10a5004900246c840d1140c840d045961101003100050144203241d006150741c400c22994402042043c1d640790354191b21401e034403001e07900840155802c082005024031000c2c01510824400580701d05c0e0080300e160180005036450320322180044803221103544690ba160011507041407945d03451015080044400c0d82c40b007080355400c103105111101c01030381c442c6041d4882c05107410003151240f03c000404240c0f445404d2420303040744c0c9401d03031a101c10b440807000a51440d400d810010b89032003080c1048603007811584109071030141142110350221403404200f145840c0c00361020031041d11030080462003005d0640d4050003100b05010450700301344025000b40841c0580707100703864145640e075440380d981c07113809020840071800c007200304000c4c81d002446450b80200300b101c100365a100ca0f6210380a0424440c0000f41c603188490a0607500f6031420014480c4260b4405000c5690742464200740e506d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 726226636 1250 726225386 726225413
    0x210d09030305070e0303032505040b03090a0c1d0c03060f03011b08100501090302190806010f08010b010903030519021e010e211215040e0307020102251403030403020607 74
    0x450b090054580c1380303040010650388641d22100b0340b83c0400c101001218501f000c801d522034100035040001056410011001c0d600541c081d0b8002c0c94060b44c64580080c001103e9006014550017440c0e803030030380c452107030385064001c1018155682d81e511050042903090400179006605507003040840345001e01c0c031419581954441d903581c07405940b101000e22441901c1c81c41581c0c0052a003000c2800540780070210346000c400100d41001d4241d6580181a06280b002da00031584d0001d004e5003044008828010309100007424600700741e147d4115900900f1502401e1400680783c0c100d0b4400c8442c5500070480c01e1f032030250360309440401503600e0300100e02071f005d02c076101c54145c01101003859001200c0c17901c20801a20103200c0d0b81c1401c0c0880b14010b2141c4000303080429503400c064010345203860711310403607103102c14510207150380b40d4175070001924082e40c02d60494900c078501d00410400c1030f1241c0200040d10040c003900100000c2d14030009295000780c0d0000f950080d000603810f42004800ea02c81003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 726227886 1250 726226636 726226651
    0x60c0504122105131a2107110334150c090509060a030807030302040902031014010c0b060f12030a030b010f110d0f020a0c06050a031805210d09030305 66
    0x1202c901e5200000c880c28080e5003035143e0b6034074120030700784500a4000103519001078038036011030038400404540e280c5581544400190700031b120040c054115030020072010440e810700d00961611031103804894405c0c0c1c1c08400501c4070300f001042700c100e18441c8580b003422942c102d14900364190684020000600d407941407040031600c00280090907042ca001900e00c07804000301090392151658492045643c005101201099800c21011900c4520342c8040c5004002840e03600001608085404880c11030b00140e15061000d001d40b13507070010300040625075002d030040d40d9400180c5c0c40b100100d95900650400603050f0b000205060f4101030385940b00400d202c1003640c0d0364038441070000003503d04107500344021140c0d07008880b0842100780640440c0c1110383ca14030440d0080841501c402290304400d0300110001407000400c10f04040e8103000b62074903880d00d4011058540aa60340340c9030745142150005800c0540c122140310140c0d03106042c3c130b03c02407065030280701200180c44c0040003004100c2c0c5c0d8a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 726229136 1250 726227886 726227933
    0x14031519090f0f1e02030403050c0d0807120b03060103030f02010e190b0f0c09040b150a120606021b120114010f0306050a05061311090d2010020a060c050412 69
    0x18070680c040d50242c080e04245420088858940358102d20000c6d40c8010030903801e01008000d400500442040782d817a081041d03585590f41070601d96401800d491550f60b0340324005051100003000c1c0d0340c0c0400c001381100c0c1d260805003c0c86c080c4240c141e014205104c804d100c5801001900c0c404610111400c12106100b200342901c41d98444c100e940ca00c80d0b003941c58140000042c800407105003010303030044201020007001800c104045200c0714641c0d603c20000400028050782208203031290900801d000703007260740090301482c0352485400c40c08107107211110b8819007003842c01c4000c0c5c91083d032003030180d9101324081180c5981c442c801000d000802d840704580c924548800281d00070210721503640a0341e0000d2500c000c4440240310341c0c1c06011111441e055548041040615a99500141403a2a0f118084158140720b880b008900d100720f400d1401030141e541064840c0d1000e6001c18480c1c9a42e50140001801d000383c070a0445160103260480856244280070a40911421580007000014400c220303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 726230386 1250 726229136 726229151
    0xb15151c0b06030f0c070c0b040b07060606080106020c1311040b0c06150105030c0a02010605120a0303050f060d030f03060503030d0e1b131109030109060b1014031519090f 75
    0x61100610040b03d0315940402c0181c041031040305c1010052080b5406144500d54043c5c032110403444541c8540d004541e06100002e5084c00c0105900580004240070700b444146903150082c042d4440780300c2e076415071140490f46400b541d40b03900c0741d0100175081c00305151141c80342e4075914004440d9002d44c000542ca4411a000200812620541c038442c505045c3c2d2914190b03110407000c6086c2e50407400e4030006554844101141544a000e0848902049080140081c03401801c015045500140800e06044400c1c0200300b0700c0d444003462107107020b5052038031190718040d41034110b006020390b41007140d15001c001000d099031801500725a22451403482610b90307140075962003040c11064401d00c06d400c0611381c080d40d400c00c0c3e140d81c00b803104445024011481c0a52440000b821140e0100085584594a030001003007802d2001c0d0741324a50030f80b4282110068407084127420140402080d4148400c00b03940011407944031300364800c585a6040851f08103e58803402082e01400c103903032a40c0e11040c9000710 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 726231636 1250 726230386 726230389
    0x8011806080c010332190e0c0d02150a051b010b030a140109230705031f09020d020409061406150f0912070602010509060a090b15151c0b 60
    0x400085072501ea00030240764415600540c0900901c0d49580d0000300303980d50a8035048a04c07603c036100300c07414507030150789840d10100c0c1c005034200070004501502d10705405444070070000a10340320030840803a912080da0341c3d603100207554101c482152580761030000c944082c8240c1c002c4007070540320303181c01e10015070180503d85140c207c800d101d01081c0d05a0001c0d066802191402e02c24404501c02e100c00402c2c56141da403200010958060070392868a03525000c82c006024007031120078060a0308802803c01411800c0b81503140300b240d03441d0600e1207079aa45802046648400b2991080c0b9400392090000e0100d5007014030082945407142c22115900070001032880c13400c8600504000201424236013042c00d0b580d150211031b000096002c0d000b03055000c0c007100602c030400420000f40600c0d0300120f9549490b070a802c0c01c042016061101c09414144040001461b540520390b10900e80018560030010880010300c01d2104280c0c08402c01d00300203a030300d0f4403004003e180030021401d0074003800141071450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 726232886 1250 726231636 726231641
    0x201050114030c0904061104060905120d0503040b0903040e0a15150f11030d06032103060b07140c041a01110d140c250e1b0a1b12080118 60
    0x141c60303540c56008003101034814075080f40c04e242c03c103000310000101c0c0e9445184e1580e0b15480307504000c0200b0000034007084589040e00340c0030001c180000250062a4629201404600000c0c0c0001e022506000c00030b12505130400c1540d00501c03008001c17203054242581440e0080c021001030040790b201550300800c5041c80c1018001c47c44505a481ca541c40d500c1510413521021603031044c008a01081104039803514050040b08051801031911104001000c01c2040102096060803401d16080c09010804085550140c401c0603400c030f11a40200c1c81c02030b02003400e004244032000d42c002e01d480c904a80418107445040e0381082c003a284c1140044841065513541c1810030100e07000603500c88103c00c42d50000303002401c01d82c00080115102c0c07606290008211a105440481819075000c0082060520058030316800400ca1a4032a40380320400c000c0020b940710b200154401c0c8000c2001081e5400c03010840d110b1003540222030340e41c0304203946000500ca102c003031041003805080700720507205491051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 726234136 1250 726232886 726232919
    0x61b01090809131a1002010608070306020a110703020105040b070f020904050d14070c060f0c140303240f0609061c0914070e0106120e0102030a061a0a08011811070503030702010501 79
    0x11091003003689400c010817507146400c0110200319525060001542c08080008402841c400c140160b20b44a040e14028603c15180c207828616038454541000941d800000321002d80e00c0203040b8940e03030384403410400450520860004d4201c2280720821060250100318802d910310580d442882003280d66018520601821102030310f07032030141000308407030b0380580b071003c03001102ca041040340028180c03034140515500f503103030500701c1e0000410809070b40300e004085c1780c9500d005081d074070b051b00c0c0303003004100901495101180156000103408449a40d10426590102d204080f9455140000c643c540080d10211100b1145601814595051607a021032040256042a184850140c0c40c3c00b034212901700030700310034010260392050705403071000c1c0070300095210790982c0c600402c10500d82481100071001010281c0c0c3d000c90244040c0140a601c07545290440d2044118480f2407400f40915200510325041181ca510300d0019800d000c203c004006036121703106907002045540c0e80c4085140445000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 726235386 1250 726234136 726234161
    0x201050a020a120509010e0d0f0201140403022d100e011104270906050403030e07080d050d150b07050a110411040501030903032d1d03040302061b0109080913 69
    0x401c12140c00e840e0581c4903070b9005060100115004221f1003045040c903828a102000140c64190f00b082e1041d024010340f4400010b400c66a0b85500e0192030085d00d6440311080c566010a490031101c468424000d94091502c105000392100b0014a942d50303002040421200c841c1d0b942041c03da208075111040a40d801c83e5074000780543c0f03082c008114007840003100070301130f8020762f07032451900081085842000e00c00d506c00d0302c000542d526000724403441e00c03142d54081c614943c4140303814003059910030241e513034031881c011021409800286843c2403070021504100500d2030003052007002d00030005660510240031352401448582100e05000603038a09884000400008000c10852544a031b8441060a4020b281c0041ca412503003003001c4103115100c103510060792004481c011551114411011040030105003044020300f0804960380340d001d10300c0007a22884022500340100a0140300b00701d07034001c0c1003000300840c5c0440d1400140d60b800c5025100e018250300019071003540000d101d045c40754202e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 726236636 1250 726235386 726235397
    0x3010608150408070b160e0d0c12140f0319050a020a03080c0c0708070602011a030a2306010e0a0e031c0506040e0105151807080a020d2405010201050a020a 68
    0x24045981c070311401500803900407a0401501c004540c119441c00e008107400e00390034024083c69040140b150003940030b280e110b5100c24004038002803c42c4003410850340440000310b0130603920b0802170060098203154142502951000b20401c400c04001481c101a1031800fa04034100b922030121510300a0208080140e4007600003d0f0201c0c1c0599251039000c4082000d451920b09100c00044c1003824a03440300c0a6540300c00c5c0d00f405081d8080c05184810030700f085980d00300c440600e00199645040030009083c005102c81100c6022207825124101c1484410441e00156900c1100218000d01141c070440900e260046142d0078100100c1128005e8040d50405002c09400b440540001c0c14003500007036210b6510740300152001070a00a861141406140e0013454140c1070051210a030b002082d11010101c0840411003200d0f0484000ca400a00707156005890b0b10720b07600e0b031500a03e899400c940e03c02c0d440c0010601340c2c094505401098480030b0b4001d200c1910740b200104280c0c000c1008400c08181d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 726237886 1250 726236636 726236653
    0xa0204200f0d09020301090b0901050c09061207020a08070f0b0a050106081b160602090a0f031524080a1205090f0d050c090c190806060f0d0608030f0409060503010608 73
    0x41c0340700081e14042c588a2000107001000307a00107800c507200c00310111410284001004061903082c030415a101e05c0b401c5050f45400c02540004142d8421108040c540c1038802d808282150300c02c101000190303600c600d800d0750721811418601d24914203054100c030720254110015080c45603d000340390403260039855815007902d450040001c5404401074540e0b500005004a0805110100d80c1d4240070b0f01441d80182d03101a00d13410f011100f0603d400424822001c03890405c0002e0f6403031101c010500c032000002894907010400c0b24a07440c1c1d10031044590704400000402d0408012074114a41e62050381c122072440085001507400740140a00c050344160180384071401401c080001005003071145041e901405544000100710510944101ca940c0001040400f016902103e00c050f184107203080440303052070440c0005145108101c1d80c0c040c0c4540100310001400c2240d00a580a071541c40143e0751034040080200546400a00c191441d06040c00700003e03003403c0c10310882c015074040c00c000e0030f00d04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 726239136 1250 726237886 726237907
    0x10f0e090402012717010b090613020d0204090c02060f0f130804030b1303110f060711160305010c030b0d260d15051201050f190612050a020420 63
    0x1024001e2050741402148000a06111003248980044094103003a5a0301d8a003000051060343c3c203110040c81080c1e05d4442c50215a5841a03103440c0e010901315641c03103814008100c0c880c082e0055440c110907407400030401040743c0d01140c101c003012a0040e82210b08640d1050720720305100c2d400381c0c0d0418000e4a21380105000d42c1040e0803404043e0300580c411450b09d40c1e01d45e107440d11103400700e030034810000300c000b800e504156118810442c90800440100007413415515101e8540501078880c0c170030712815490b0010101028458080f100c0008158080155540d04100740a840058404c1c40020b2601045003ca45032005000105640248015454420043d002c0490024400b0708101d4000180051103400e0568006e490540255080e000b000f40d01e00418494014421010905181d040004006034961300d00c41c1250b12140f021601c071521144100f1810003000035400800b086030b10501c0c0001841030016981d520b07540f0a4908000d41903065030a05418030b0b181945061244003007010032041d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 726240386 1250 726239136 726239149
    0x2403210307121b0f050f0c010608060c07050705040b010e0315040b0a02130306090c030f0309090510060c0f020a050604090b2112070303110a18050603090a140102040f23010f0e 77
    0xc031000c0d030910516046c084050f600031034000d1039190368035a440315001c1c8202030091100380d800c5803207010030b00d04000b107503130b18961100c0c1e2600840d40104d54403000c0140680c81a0100f0707403003110142c01e88113550307401002c404080d07070708481c1550141603040202c2e003039002920072902c4000c11280c1d007804141c01c0d0341c0c0302c40150100c80700c10b48480c032440e04d0120100d055020fa900002303200703894503203030301d07250090100035910020101802050301c0c1d80b040105c541c201000c0807203246d000d490760150700851702c0000c00c0d410050b00b0441d000325021a02180c0c21003d98841155240100c176007129030340000c68140614118083d8811858214130032400f64011000060304545110b802d0110b58080422128204c0b600200356a4000896542080e2505081540090003412041c1e41c40c0f441e61030061003d90755003040782c0e401004031411000301c5910b54000e5055401400780780074000c40b01a0f59480900d069414000d145c6064011000c02031000d601030901e82043c81099250304600c4080c02c81007006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 726241636 1250 726240386 726240407
    0xb240607031b060501080a1e020901050909150106020c03010f060302061b0f0132220c0f060309020a0b030103021f030e0114090d082403210307121b 65
    0x2408080804402c00298541c000e29000e8030b4100d0052440e0040380c00c202c040b4184509602d0142c00a0001d0301025072100003506e815620166210a819142c03480642d15101a0045010035070781e84a0000c0782455002c1090302d43d0a42c120001c0c4100d600c0d030350b200021950944270083d0300c003204000702100364020190340c441888030740701655a000849058142510808515400d041007100720b1214045480c0e02090411501c4080c0c1d25072074a03249100c0807099190141c101500c40b039040029007045240c4000001806041c0e0a1450542d6541409800341030352940803407155039078042c04038245961105481c1200d80003004400a070003104040c901c0001401404010551140c140c480c0f081003d0007540d1032448201d120031014603282c0d1940741400e40132005001007064100903c600e22003600740d221150800c61412056400d814800170b840c1c03c04400010000d05110105423840c4c2c114900078510a010f1600c0f0300280307140100b03105040312080600c0c070003842c500c00c011031300c064400d80c10000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 726242886 1250 726241636 726241667
    0xd060b0f012a03050c06010b03060405090c01020a0605180109260a080a0902120d1e020f030f1b06040804150305010503030a08060f060c060402040b010201020a12110d05040b24060703 80
    0xc0c5415145c1c03071860b08200d02600b00e580100d10000610401d81040c0c4102540302000c0320190800c4401400000c0d00d814080301e000d40080e031202d0216000c500c00e01c61450740540403000803c1029074a00d455442c1409050a040600000a15082c0b04c18014001c4503074440366070b51485030594444030f90030010f207800701069030842c54a44112031400030403c6484c071140401c5d150040c2d0f407806800650740c0d45403190480021034000c0c1d4601085040c00105403080725415180150722000603004a1521003d0b00601c2c48451003201c041c0f200344031210001b801a100c8031031807100324060180c010f50981e50213100d81f0740c050744104072820000c0d01c22001e483d00300da401451a04001e400000180007030300884021400d0760000401d000843c0340034814860000400e00083d41000c4103010040c20f03415417880d00c1010151240740490000081e1000c45e14007585401c403c00c404d0030981002e034685401116040348450501400500c20b1103552410064100020101e500d060b406540442c6d0b110708005168 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 726244136 1250 726242886 726242897
    0x10080a0c091d0a1d010506040e0c060711030a0614090c030705010e0108070e090c21011a0d061203030221060a090e0f0a030c02031203040506060d08090d060b0f012a03 73
    0x500050501d224020500120300004202824240f0030801220840b1649140d40e500034ac00b038140f585c60310720a072424650841401050780d8254400b1034180a041c0500810961906110342c1c85500e18403001400f540c10803045662b0303d034140c0706040d0754407454010346022403035060540740039611407461507034400c600b8038003241c071905990003081b000a0241e43c01c40712418046103480030692503500c2c288044809044a40c019450f200e00d03441075290a092804007080700040800c43c007a16508514020680094480045200360070700900941200b03c40042e0308642c111019800d0040520f81802801c00500da01d0542d80781c19000d0000307000e1201404114001c1c20820b81804e10103014100d1141c0c0280c41d40d000d46110f61040508181105100240e4660306105020108a001176041c0d8010000e0f2000041c400b654149414103008585499900000038586003080215030781001001c1141640d0280300c2810000056071141c5903d280c49000d0071694031100381c0010028a03160005001e030601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 726245386 1250 726244136 726244151
    0x5030403080d0e01062601050c090f06120a02030103023d0e060c03030703050f012115051e01080f03070605061c08091c030f0c1110080a0c091d0a 64
    0x5903080d6580d40e4030001d0080130381b080708078005140480085121300c610000f042103186c0304d04891054001c044415010784c54440240d24562030b020100d07400d03640c143c0e03e00280c0303183c2015000c000e54801d00080b4080c4c500050045903038485010711204022030300000407000c0300c4200c04040d4104180e016001040100c400ba0909510f4800040c10f842c00c090001d1a543c2c5848100503041c0c3e2070142c15a541c0890000c010420b046010382c00b00115421001d2050040540f410240e24403c40002c00d081264030f05800d000b1015003032048140750103502800250385a07071302d0320b216448105510b4040c2d41e60b001007000ca00090342c5548000c2d0f018000518090142c000782c1242046a1b070300110071200c041c0d000420260b64900f001d0751000c102c0080f4180b00c520701155078010070340030b62003101c001400400d10b8003a0800143c2c4000c51580c0398080c1c031104040d1340300e01d00180804015154034540c50303d810b9841815a200785201c00944103141298000844111000d018401e0010704d50480c46030b88050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 726246636 1250 726245386 726245411
    0x5070e09060414160905091c0c15021b010903030c0f170406021e07141c0503270304060e06071a041506150f022805011b030603150905030403080d 64
    0x940304c0240c100f00e00d00046c18a04844070500e4104107107102e200803d5854070260703030180e010000040e42580001d07140541501100070760040c1c000d07000003078041d1003103440404110784158040c00a0034001d98040c00001d94126090b141c0900c503401100001e00c042c4481300b40829460321a0341c010748603503001482c00d0368580030100035070140840c00c1d2400c82c0000d202c400740114006100e0304100c0800191a030b00c418021000c100ca500c001c510400c0c0720020000440e6440900e504c10404240802c2208501c842000d1103502d1b03911500401011851404e200d0315a4207011080e2501503074401d020014100014030389040760b803801001250400c2c1103c0c0342403400c128500139a40204403200680303a44044002c0c01a0000c4804d05030b44045500486004d100d4170030300b80400e13101c1241140b01c89034081443c01c000380900060303040841d508103119015201c01e43e05034081004c582c0074a0703d10064141448a804c00c0e110348101c0075189a00c140b0060010414140003004140310980c00000c150342c8800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 726247886 1250 726246636 726246673
    0x1170702063c180d1b1a0c0d0c02010e030406050921010f060509040b0109390806030307080301090b011b140c030309180a062105070e09060414 63
    0x2040e020700007a900070301105604004803e080200c3c01c201400d8000e40d180e20080500c902101c80c0141e8130784400f145024406445040070f130044200c0820b00042ca0400c401440e41d40c003180383c10354900e2408103d90030840c4188648038003481100c000c1e501d0285000000c507407e400c081d4510f648038141100034412000b514954200f02d0388030200100b035501d003100e0600e08503440c590080b80034003422420031001401c1c5015a5043d80c6880300b00103010745000141d625004d1459440c2280c0c0000707140f900c00004001e4500a00c0c214495032998619640c28041c19140c0c007a8601c014810142400140058021038202a030006410f1402a0210b500c0301e60317a0317510020544091365106020440c0d003007440b81c140112a519041a4000c0d03291510290100d182c0c200c9001d103d1400c40388000c0451603000c45900700b80001c1100b00038168696a450280911420ba0130b40102c0d10b41c840e0080006218841c8801c4d14854a00709020300b403a680c0301d8803003090a011504a00b03400c2d01418085460000400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 726249136 1250 726247886 726247981
    0x9090906140103032a0201052a030f0405030f0a0b0f06030a0618050706110c060904020f030708090601060f09060e0301060503030a0c14010203060f1e0913020117070206 74
    0x3903503225030992400200300788000000300c521061503105d080078000b42c0d070082c04039002602a0031020688001c0c049401d00d02c6a6a000b8407400c0c0d001c0003444060f162480c401400a4850450035034902502444000d035603041c0800300107006481e071300c000806455038107140c070380d1202018082d81c021420070740c0c4110440300c1c03503044a11080c001c0303014201808020030480010700a14104410f002c60b10006080d6034411080c06c8070b108103000506100d06440326019038501104c078020250b180d04202c5000342900104407100721040c42840000030b4500c0c807464100303e5a96a45d240e05034064100f9900f2a281c0c04c0181080390190348610700019262401c100401d81a04039940350003000001c6d160440f1481c20481303110000d41c0c01030084c000070340d0301d1828415181000319500c10103140c2103034103c580e590078446a00e9101da401020800c1d014800c200020009100f6a501802c0400030703034200d11103107001c1e101100180c6c0820300107050b46130280003001860409180340c60111140800c0c0980b0303840d40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 726250386 1250 726249136 726249143
    0xb0702090c0313081e0706050108060702010903021903030f020706060e0c090f371a04050a06050a1209152a05031b04140a0e04080a08040807140a110a0609090906140103 74
    0x5230001006500390170b10283e904101e02e44000c2c072041d5a079440c004e549802c1c4060440ca111500141e1004041c026800079402d00e2540c042036480300102d0521030014692031007075882100c0f207403001902c040008402c40d50314250003041041007018090500c00c001c4491404110115030154041501041d00d207030755602a407000c0b40341c03040c442c02c1c8440e81148090380b988030317510010240411b020320750b24400301505642d83e40c9080f9448140b1901d08503032481c04e850441e68858907020340441400f01c2c035075041c419045c00e0642401a030410395410f509100c101510381e061400140307645000a0700c11001960014029103000d4074204248004103d55880f07a80040440c11900382d1502c0b01d0308200c0d05140042182002508180c50261265020f52091103240010417140c90001130070021036001b0395143c550008064050408540303602d55481800300d8098801c08020212854103180c0702c09460255a413135940e2030b18003480c1500032000b07030805003402c41c0c2c07181e1503400300401c80b5041c4041034021341c007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 726251636 1250 726250386 726250391
    0x71205090c010201110405091609031a060901050904080306300714090108300d0f06050a060f0e0310091227030f020307050a0b0702090c0313081e0706 66
    0x1e1a10000e8215200398002407040c0b4000e10080100e80d580c410740541c03054103035103415219040c03804220391402c102e1304000c061000285c07050050105c0402068440c07142030f0346440d02c0b0703625070b420070803a81d6044500900701c400c01c06c0003076900c0c28145000804561224150b040d2903c4006494064429a4058051613401100b040080c3e134104905c4104407034054654000ba03506004489403604072132003540f41080501d01c1e00081c0746400300b241030799803491010350940b03070030b01c0e0114030000c0e140c00c40c40030407400e080c101c020410b40750038403005003120352584440c1110301c81e80d601510710f00c1212440ca41d25014240841d07032040b105e40200701c0101c0c0700e080d2510705035400500161602010010707000013002010449110b051500ca84074080e00c2e0001038002004140c0c1c4006441c007100c03038128070f40100503100000340249402c0c01901d8624400c032540c1c94583d0b18050038102a0204840d4014000000072088000c6040c160082400440d061070b6a483d00c054010b42c0702081d40206021a1a1039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 726252886 1250 726251636 726251653
    0x806070801060216091833020f040e250509030d210b1305090d110106080a0f020d051f06060e0a0b030c040801050114011706010906111f0e01180b01030b07120509 71
    0x2ca01f00f812001d206200001c50a102c0d02c407031042e000d400f90303000d0031002c80c1c05007020400080300c07030f0a0103010b0600d600d5003042580b07901400030982d0f001400400d000f4400c1d0050455924014410065001000605102d03440070300c850160240c150b0aa1a580000c286191952840218000d4612510320300c401850400d42072072009004400e054802d256592600c80140070a5002044002c001034210300604054901400040d8480800341d500034402e200d20503d50f0031100c0c1441d005407801010500400c030b4070769284401d88003001d29540f001e911481001d01072100c4409400a150048501c41070340d0306041c1c54003100303401c45800303800628026113031001c210525a40003915061805900300b0280c101d0600d6030003e00006640d024107030030721029401c9042c45034001c000011030707850182e008411000010002d04000d01d2103841e4000c10b9401c4c540d0003005412903041c41c0c2001544454110701a81c82d54541c051081d601911550811003800300041031002103010700f80c0908080d8010f880d815 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 726254136 1250 726252886 726252953
    0x60606080705040b07030f05090910141e060f07150222140108040203010f0603030e030706022d0309221b0e010804060902030708060708010602160918 66
    0x5400c000c140000700071041106011441c40307041070341c541c240c0c541840c121030813403580141c2c0c850007003154603a0000300050401404200e0269580100c0395118018031490b1701d50000c0c0b0030800b004606040c2100e5200b409a0050b05190004001d810304002829092102c3c0c0d6813040c2c508501c0366242100310340c0205200180325442440c3c2c11845d4010360b010800c0300c1c944404520f00307c65032036141381488005000141592000e400018091a5000381081507680742d18000d081074200c0d20f072042c0130b4824a200803c0590002402c6003c02c1c00e0151455601d801c000e25146020440544001250005004441041d1210b80c5600200303d02c8a4a2502d14007900405004903151220446c0203440007a00380d41c1c2c00340c2c00101c441c41522080c41c00a03150756950401c080a04034464000790035200320360000590980206815004a50a0341d42440b0750b640c541080b0fa45001042440c144041c02d02001c01c202c1103140c0c44509109584c000904104002c1d84030075080070300049400310b065602414030f0448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 726255386 1250 726254136 726254147
    0x30403020f0607090513090303060806070908010f0e0c0607080705070f050102160e1306060308040e040b070e130e0c040609060f0806040b150a12050307021005030615030601110a060606 81
    0x903c1d81c50700614a520b4680011954802c1c445201070050382d07588180709051180d000100078084031000c0304c40d00c0c140410020700420584c0724002c0c15500c0c0011200604c03101d40500f40050803c1070040c02c1420038842004095480301c8000c503019101004000c0000380c041c80560010010341e50100d096500d010000780c1410043d1841c207100f4a1403100030320245086100c0d513134204250444075034250041d0304c0c000005050b1a000a0514540440c0000d03180404661141c030903032041c203814070a41c0722540f050341d0b0f44030000001c0b40e00080000305500b620041e540044401601e01041b101c0400841d4081011920b0a13044a9001a1101c1044c0605000041c0c00401840500001e10840c6001d444443c8117080280030071100c852841007800d4035649101e088001f800c0e101e40418000701462622039980d9111802c200e000c1d10070994040491405201900c5c42940064551248054540c04151a940c8020503050500c900c10710102004101001210f14042c40780000040150800102510307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 726256636 1250 726255386 726255391
    0xd0803091e150106080910020c0a0b0c041a0a0206011208210109110c1b03011b0e030d141b0106120b04060617070306090206041703090a080f07031b0803030403020f06 73
    0x40c02045024031506d400c0002c1c2e010060320710344100680f02c0e24440c400034101428400058140c02138041401210f45c5a500107100f01e65507400300f200c8144040c4480d0303041740681d40c1c030240560003020041002c5111400c0c41c1c2c1505201d045810b02c1c05841244017881802988a240c1c1c01c0b914132001030020b130103644910680300c442e250ba0036003030400c4010250340ea2105c0c841003611520404140103025103094008400480e407888041680d800c0300c002c010a91010608528420b01c140340c0350250f5540a0b0401550080164003014a05100702c402440605040a05031110750350f01c1c0c2c00060360420040125940a110300f1194900781840d00b0300740250f403044d80110300000303000351540c91303600f10004c1c07148200d035030040010500d801903000142d1180030f25031045043c045070300120410313610044000c111030030040792912505516031205541c1c5424a03001000141c1c00158180b02042903550f618818480c11500034042d240c0f218142401c5400035503085000d64000c8002e406543c0080c0102503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 726257886 1250 726256636 726256649
    0x60d0b040f1b0c020a0806161806052a0304060309051e0c0d0813060c0525050d2603040314090d06020a0315030308150f0d0803091e1501 60
    0x1400104110410810b94030300d0105052066040f4040c04540718181d42100610000054445916121402301c2c81141e401c0702c0540040d003008a002c1240701c656000c4d8080d5506540d4003402e118465841c00214891060100d1007544114402240450200b00a0028000656001c02d06d03c1803850042d03e003003a0756003995410350071420380d0305158a00143d0842008001c98017070042e40403034201504640300c0c80c254101c4504c1404d2000c00c5480d00001200ba140740304808590310070810444030155245245000c9000341c1c80c800d400c100174600007801c00e50b080e00414140503804442071400f44081c4401c00d035003200010120070801419004405110748a842c2109c1d9803504c04038600280e09200300340c4004040b50350110b10b42001c60311036800840b81450b40c04804203c0740d2242409401032070122801208100400e000c1c100300d00b00401e1000402d1805482c20308510385640e0ba00c045a04000d00d0310324144104003200c4001103d901021540100d92405480826020500364400d0941601b168 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 726258992 1106 726257886 726257891
    0x17151f06080f010905090a0213060b04090e0c030a05031207200a110f0607020d060b0919050c0a020607210606080f09300405060d0b040f 60
    0x20740190381c0602e080c0b645a03603a400310740c00d45004954000c0c2c250402c1c41480014100b2800c96180d0a8a901010035010f89680a034400c3d81c01a9200340e01203500c0f27607410317070740c1020030f000703040c0700c4041a0050600174501e0349900340d40f481030040c203420340c80342d00740020300325441030300308008501009051405505405102e65030f1811401c20541308800a91620a464030f40899022001d110151105e400e054058080015a500650040c0c549a0b22100742d98019640c0ea00860300c6401c0180c007003101075440158040440c2c030010801c1800040c200710041c041d540015101d940030101e4a07111000e21008074201900d0850113004054040c1020400b10741547c02c410b40d5441162203043e5606150355015443d5659030008001405202004807071102603055900342000600c101d030001441c142c3d0700d6012683c90f0b4005082c5070385003607540700c944840b032900c0d0082c46c81000440006 = true := by decide +kernel

theorem cover : BRFrame.Cov 726079136 726258992 := by
  have h0 := BRFrame.cov_init 726079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 726079136 ≤ n) (h2 : n < 726258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
