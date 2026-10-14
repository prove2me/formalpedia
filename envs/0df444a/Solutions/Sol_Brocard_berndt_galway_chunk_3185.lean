-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3185
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:55:09.833578+00:00
-- url     : https://prove2.me/submissions/8eba320c-5af3-49cb-91cb-213ec8ab4213

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 572661870 ≤ n < 572841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 572663120 1250 572661870 572661937
    0x40804050a0e09010c030908030115171e01090c0e010806040b032b020106030b1305070e090102190e090114040b090c07030e030a05060f0c191d010302160602 69
    0x444202c0200003080b000d4a028031420540443d141828031240c1e02c51784e2458500d200c140580025201c0e80c42d40070074141e00c18114502c1c440c150b4403000c08181040b40825800c8202507a018038000c101500105101d1203a000c0da20315071406807141c108014021006441814000b010766130840c2c3c0e89c0d20404070f207030350800c842004104526407400c01403c62244440e8105550740f0f0060075a814000100f0000c3c030142c1100d80d00c1044207950403c484050b1600c40d0601100341d0150f40c83c0c581e02c2d41030240e40d05043d402081da00c600e540119410003d05007050704d40c072403c01c0b41c00d9803000480340104000c00d0512460004221700a100040710808003002400000c0c040c0c69040001c040400d04804040e04075601306109030044000308040d0005c1d07503c40c0e07940e040041899420161590210720182c00e46000d8444001503144405d45030a54044000c0c800082c0300c0e0410038000003a04504001d500902c21038550780381c1044110400c00c13081c1c83d0030f8043d5000e00b200c006003074000c5101103d64114010701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 572664370 1250 572663120 572663129
    0xf12060b0f100e090705040b090d080f19090909031d03031605010209130608071205030409050103030806130506011209080d060e0906151f021c051e070206070b040804050a 75
    0x3e22028003e41014028161001000d160511a04010602ca84c2c0485020382d00034000c1155140c921043c0d40c40d215080e0300440d60785800900c408038041d8800780d6404001c1c103900400b55112480306640325815800d503a0303a804040c0224240b01400b41c04625030082c00c4446800107001c0740d1030000d24208a00c01e1003001203003a101654041030341010752505072503510101d5442c040c01d1000c107040c0302886845142c94881c0c810020b60312004482040424410b41d8000c2002d04410000c66035241805030094800b03c03141c920034441d9480f40d0104546038400c0a0241d0010b81d1034020729140104001d000b40300102c81910030023410701003140c160002d4001c050180c000300c1031072105400c102c81550300c0e03c1e10192410314030782c440040c2c901e4a926600f1602980c1e01104190003c07004911900ba41448565499011401d03000c030340d0540c141d80c00c4401054010800d100d90074a0901103019940c1e14040d83d0350003580079104202000100e02c0c0c5511060b003250045903000d00d0300380c1d40c600180102541344d01c0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 572665620 1250 572664370 572664377
    0xa050d030b04052d040f02062106010305070e0d02031005010b0405100219201806030c180a050c0c2a060a0c0b0a020c031309060f12060b0f10 62
    0x2080300c1c141030003104d0704600581607a00840c901c89692607025541200409202c0040c2c100060a00c080080c0070503180760040c00040d92450010140c00705414500440c0f081300c210340f408207210b544070f449658450b944035900d403112203202400700860100c800c00180d906229032452600b5031211845201e008103210a24a550f80349802c0a0003000700c400790742c0c034095400c002008800d0000144404030b01c160300200e900c001100c02d5503800916000c01c1c0c80c003504400c11044d01c0300485021500c81c0e000b40c004070b0071208182c01c94410011b150301c18008483c214000280070820503203c07904103680240320040a58100a0414103580ca002c003124812004414525002e515075245018000040701054078076170b1621221070009803252108100c010711168240b0002828100300b0b0f810f558200e4644003d40b42e68a516038a0f4a09114040c003950254500d00000020186280041501255005100740a50351038945070440144030030304c00c00707400c01844401003640340d4030242082608a017548 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 572666870 1250 572665620 572665631
    0x307090911060a14030c0412060504060b0d020f12071502030a09060503010e04031206090f0614030109021c02010311030a050f0604060503370c140d110d050a050d03 72
    0x10316846181040309070340c1c0518810403805001d5a4002400ba07092403100c103500b5929194858010b00c80d101e240d01690a40c0c40200c5801704100301034201030f00950050005110f010356071420000c05200341e510095120040442e90031050038404052444804039200b80c6a005a07505d034281d0244d00105949801a080000c0400ea0107411211841c00391003a843c3c003909660401183c1000320201a00240074024100103050056a0320b0300140041e14964100380306800030500d10390003814050180a0b0700c10703100f2011510074201403160901654000380302a40198492402c84c13800560349105904060b200c901503d0003400c200003d40c000d805040f00000c0a14000c00f040c5034550024069903c503605015040200d550700048500c2c1003649060040c04c112103001e00d043c10b8400203460890705c07200c8600480244045010442c084070040c50410300c80c01c100d4000c00a05921240b80100b55100c041e40012207800c048984000361441030003102c0b01c0304041e8841030303c0c01d545d0541220000382c0b40c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 572668120 1250 572666870 572666873
    0xc0906061211070f0813082a09061c0c0308120601030f0603080f0a02030d1a03070f0f260f06010801061d01030809190311330a0e03070909 61
    0x3407003102140e142c1e5550440c18050f99a8030107103241c1d02c1d04006808510042001c03400c81021440980003002c0c20421585c1d5101000160b0030159110104111078070718504016031b81e401c03e100c04520aa200800714440c108500c4034082c0800b1010030103940c1110f203110080700080c0070f00020014a0b8002c0958403940c0307071090006080e05d01090f441c0000d1402c000c01000060320315402d540b00060303041c860303c0d210007140000301c0ca1741c09800441403042d0b08001111804001e0b110307504200352030a07030540c1c040686032101350412078207505c03a81c1c2c1030b400003034000c12152046200c070f0100d400307100415a900812000e80c462400b0f2113000c10b04141d401201c01001005001d04c00c01004203008038403540d041e0900020100c8456051001910000002030300442c40c0e43d075070202e03140d060a0100090817070f0b40c80342000b03080c41d000031044034020100503681d802a014850303410481180b26100320307220200020300c2d0680a401400400341485100515641c85039801c1c0128006000c10782e20010b804032a6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 572669370 1250 572668120 572668157
    0x919030909140a180b06060a111f0c0807020a080a170a1406030c0315060f03060c0c0106050d0213090206090a030609170c0607080415091b0f1d040c090606 68
    0x4c1d82142c820480c00f5444020024459410385076000d00b0403900aa1520080c00b801d50300416450000d80090080c8170000b410341a03501c21140b24076201c1c12003081100e400c18401c4d507003900140d40a40140e8409d191000c00641200020401341c42c0c0c0c0c0c5403542140820401e20741c0c190303030203031030a14655031110400280015085015548840304038000e20300315049a01094803190805100303003107118568002030f40b80e1036141da1906040400b0701110342503c4e00a01a8419800c160000c62840d400c141380000e07680741110046e240d80d50000c01162103549205810001404c8000003203070070240510040e8000e039a5211090001c60203644c011a4480032840d00503c1d0b44069910030300088014010348888080000350075a001440341080103164a540c10000302d08020780c0000c402c0e60b42411000d208103d0000f81001e0416584210151607613121000c40034034106500a948040502c0d00203820030000c050700384d5401a024031400d4240c02d0301c84901000740e4020b5000711002c03405052070103095181 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 572670620 1250 572669370 572669381
    0x9010237030507170a0b060408030a020d0c0308010e041a091b0414011a090415060f020d020d031a0604030f02090a02120610030b030724080919030909140a 68
    0x528003080075240140c0c0192241c2c08282c140c1381140d200c000040c1d031641079035000e000740c1900180000e840c0e80d03440c43c000c1c0c2c1d0399015500013030043c096500705400d60b60060900000156041d01d8441507682041406501804010301c15510f400f202118400201c40542500c0c0c02118801c0280c01110b2894610614402c512854940240e01c1d00c50340954040050720700364150b409095118621544050304680039002d00d13040e46500503e061006c0c0501960304040104440c103d4a494510515610003aa140d41e6007144120150304842000201c0504c00d5008051440402c01000c40911900000c40d5803600641c10450b5220440d103181020361414240303403a44071a002d40e09501c0c01c028000066040c0307001500d001d019404c80105049624081c1e040462010401b40c120380c5050751f50f19040142d546000c20074203c800c050554032703901d180318124a03880b944102c0001c22405c82240d401d51110002110b040d810400c1546002c00c91000b54040d90b91902c01256145426003461a1454202d88 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 572671870 1250 572670620 572670727
    0x1b070c0e0a060b161b21060b030609060a0e0f070f0303140708040302010509130218040b01031812050f22060309110d020f0d150c09031a090102 63
    0x38051001e080c104041908032100c0c2644a1807003917280c0c90403000b0094038200ca4001407140c40d08098440c0f89402c9400b04145524001d20f018401d883c010320616440340c8040d01c580b01c8682016000900400b0360b03802c181400b01800c0203c41c0610200004942040d1040d0070110b800a100101002030640c40805403a562424440071031802c006540c95205500c15880000c2c140400820343d041c9a5491070b81e03400d07034402c1c088420f540d45d9581c0b1005080c0b8600c0074038172a02c1246400742040c0381c0c1d44288180034001001203401290161640c5034101004c000030781010810000300041038070004810f02a01558a0301c450540c0d0509040d56103d095080039046141007618180403c804110b181040490400042d85d012029200b5400455400b00d01044070940120501101501704103454120000d0807040710340400081d45814403c885900d460f10019241c0480703074191040c10300100e00b00c240c00c4959000010300c0d010f40001c50700000718110001c099289101003120300080c2c200c44c080302039007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 572673120 1250 572671870 572671889
    0x20a0c050c0a1229070225050d23010c050c0f060606030114030109120207060207050621090c0d0b0103211b0501020c0303010b03060117040201081b070c0e0a06 70
    0x143c1030241e0b0b494600040032000e0004500030304000080080d10790080d290070280306440040785041c2d00c029580304030b40466a21a480c50314006154114140031140c00d441c8001d0020841d40c1154a8140c008002a0b880035284032a000d8105400c540910608140014a03100d058645c081a0201420b00007402c03040c4c00250440e40800800d59110000c4a0564408030745902e40015002c001c603005218088004010071400c4440020160700040c0c61421109180d00329000c4513181c005002050080001c103a03814403150407143c198608001403a40d0142c0014100e414540c5c54500040b90160420010360b1110422001401171040d82c480104071145005079000d0840b41d52200200a040f00501c01300b944000c403200d04007000030039011501011410000c403030322961101000c0304164410348007035020070290725120030082c000c450014810f58058440d0202070f07944030b6007200c0400700080d0840e0120020040507000401e074002e19006400400c031185498500500f003007040303030304a400146d007a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 572674370 1250 572673120 572673139
    0x61401090e1009050c0907030e1b0d03110a06020f07143408030304110a080f030a14040b19020c1c02060d29040b04020322050c04020a0c050c 62
    0x2550010300380b41c00c81d090b28800034650180b400c0860906020302203080c0c0c001c0c0080b0078401d41a6040d000000703d030175840151004003040501c1260049605014290041d03282005600440d0051070710407142030103503060b520001e40031782d03a400482e40b20b044041e14405010498905200c200c5060103406040b410060007218000782c8028150110203070b96170030328000f070841c030401d61034468004030003800170400310713a20387c1054030342159507204d1800458040c50b203070f2000180d4101c0000b411495050a00c000d5450b082c581c1c3d034103e03110050300036045014401000002a0202604e0007045402d40c50200028140150701d03009040c8588541e80c1d501c00e010704070203080e0280d203664003408201d90403144030b40c0d02e14030700d0b440d00081d0910020400350134100300c0350340d0055415101d90548502c4211000c00c01018130030b0810040740026514032003c050900d070381030b6003815030b202443e030f9050141c2c0450756901c000c0400034061b0381c40790440000080440116800b041030030440549141030854001c40d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 572675620 1250 572674370 572674391
    0x60f12070f08151f0306030b100b0703050901030605060f03040204050c0c07060e1206071e021204060503130b1f05030a050c21070303050304030f02012714030706140109 74
    0x1074042c018011640c2c0c008a0900c2107090f56440e1501d591100001030a0844550003940280007020b04d032105448100180d40000c41c0400c109000340c1c252041102403900b8055540c8040f80c00d500b0484000d0706260b0364030400300e101e03961200507080003903030706013003070f41d42d2806105200c10390708040c1499500702030501008141c42408610441964200d00c3c1030480d0601c03080001d180b001c2c400340718590301d00900042c000300326402030114490f60420407026040c001c0f600012a55400a00402d0012000c28002805098400d4000b903800c003d02c0c0a110740300d480b0b036890355070421105907192410201c2a10411030003482c613144000c000d00c4120094040e4401c207071129130306d41040d542c8041c1700d40070707492a85030002c284005805050107001d007101c500c580c40b441c01600c2da60091300c06034041500340c007034040050301c1409140032900ca817224071821080e080010800c85070a140c3c0c1140c0c04140007030b0a49600c903040011301030b014090100401d56804410940000d0801a04090307440c1c0d007414115807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 572676870 1250 572675620 572675627
    0x60303050912070504050109020a0908030304020904030815040f0c020f1903030c0c05030a05070317060a14010c0503220b0304052e0906050a05011202030a0b0c09060f12070f 76
    0x10000001034442440b41030a62880904261003508190341c000e1030040049941245640601078155064440e401e849481da2281903403800308550080d0f2202c00600080d0000f482001e041d030700a5400d41d00700590794007520001e0183c5148140800b0810358840001e00e076580c2c10000c00f00107070084005010f444049204440c03484460070809000d03d6110350340041c000e8414039000704816002810f407a201caa411a006001d0380c0226030541c00200f0304408038600d2289081c60724056003004240e00720040ca00745003180035030005070541d030601c01813480c2200466418001022406250400780da088042200c402104843c55080540308507001c0c005c0000241001452445181d1150740800601c504a101e034011800c1300c59881c1d026034101401d180401c005500a507005420194080c0802d82c2c80366000c86103054aa00043c0d4154081032008000c208025040c0c0c1d00000c0c10b808a92809118802003400c640c0b000040088418001902032143c055040d1420340190440c98035440355110040e006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 572678120 1250 572676870 572676877
    0x1e03050403060c05070804120b060402210a021b06060a0b0c0d05030627060f031b13090b0412020d030203010f1511060117060c04030201050f0307020f06010e180106030305 75
    0x82c0040d41c2c400024286a000d08180e07500703903900c0302c405562691a9490755805403200c24048841810380310206101c1d180600a8544a03001e5030002d1003400003296203e004250058603050445a080043c3c00700180605100300c08122220300030042800c00000340480e100301984855220340c41409400c0c001c6c0d0300400c03500001121841c10722303100c0e10380c10000344140381c40c012560311015854449090a580e0340040602c1104115040c24403e41071006240d02e80c0a505031200070183c000f00306050514191400200806002100050811840d694010141e6040d1016601d017100e4019419110341c0c1040710180050716858203500f554500301a210803400c65020706a08189180c807400e42c4140706400c20307005008004100c2e0110f5035175242401c802000b51103465114001c20b4005840003400301c00726000c07698180d40e614a4400c01d2100b40c0c40320340010b4456030450081075901c11804004006460180200c98084041810711007510300c402401c014401d90707241d052900c00c00c042500300064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 572679370 1250 572678120 572678123
    0x140303032203020715031b1805060d0f0f06030219261f1a010c08030109090203031e03071e09050105030a1404060903141602040b04020c06090a1e03050403 68
    0x56820486071440c059003040440c0e000321002c00740019003015a5035064001c45041103c240420340015281d113001c4442095000000c0e000d0500300004201c18148280144100c0083e0b0300001441c5507400c03688410381d4554503011201c1600c5640c10b000b94500a540309044801d0b4000981c0c069140c850308140e4010b6818a06184030844440d034090820180040002440023102d40f0150768599441c1800420000111108041010705022165401000941006500034409906580ca880c14103c0944200d000c200e806020912560300240c40000003c80d9010110040319240d04c1d000c01d00500348135018808400044500e2898200d030307908002d0040c2611400e103000390340ea50b5903107140800303007004140030b4502024400c200001e2180980c00300307a0b039070312a039988045091034108001641c05003455a02040341801084801440c0c030341d00ca040361035405400541000c60b00c0d4182820710308120f5042100760409203100007000b0420b02180302c2884450380554440c22203440080041c02075000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 572680620 1250 572679370 572679421
    0xe100305060a0527011508120d0b010e03031c18081801111b03070603020f180a0b04061107050103060617090109020603073c03240b0414030303 63
    0x1003240c04008050721813804501c64a10000744421081482c001c05000c690041c08101043c004070308000c02149500414840c0c50315075003080d400203001401003c5c28414141886404020708240f61410300103003012110702d0b10300802d1039045900f40c00a4440d0720b12001d0618090082d504001180300084e00d890f015400b00f14140b45c0e1240d40161002100ea4000384d0701c610400c0010b02205100901078214840305a0a030307032840e551040700398140c0c050304040c1801a00c0c184003c1080e401d6a60000c183c5010080002504a03030702e42d11400180e0241e04a900003c001a6102c1d11005041010b00020038003841c0c00c10100d840c00000030004894003203a2030303640d912400400c2c015003003500202d20b003c0e001400141d59043c0814081c0c03c03a9207105180e00300110807100280c0c04c10026107081e5200d030811111400001d54600c0071401095042c220381030007116032401000e0305429074803020180c41482c4045549a00702050542c032948510081c6109920030820020b01002d1141645902d50303589a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 572681870 1250 572680620 572680631
    0x603020117101a09030f06150d060f060b1801140901030e030f0a17163e0f0c0402090604140d0605070c03110a05070e0a091403040e100305060a 63
    0x40020090b60b6142c3d00c20340810411040244040030000b00811507150124100d43c0c4003c400005141c60740021900a102c601d044102055282002c091200000e0721902c2c00281e01410b0040000480340a40c025074100c410119034071a02c440c6040041c154035000b400c0c4210015500c03040751845114280049041680b10a003040c0c808204100ba900400e40fa00c4010b500c3d24000320004000316078100c50851080514008190700030744003060304c4181401a511048a155649060180d40b82c5800d424003540701031941d11382001ca42404400d80c0d42d507040380600b032080002d040462400c440c560821784514410001d25400e603075180103c03022128140c20702c40d070040e0400d00260404404c218003600140c101420060b2145d4494451011076100b9252591190010780c001a030303070520010002e089030300050052004000d12948a540700e11002000b00301c6040a60f10742401802614071401d1781e0388041414850105004070b0356030b001d0f0221440f08203892558403402c0e9a0040502811720440d601e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 572683120 1250 572681870 572681881
    0x603020c1c1115040614010815100504091104050c04061b14070e0615070b040212190605040b250e030c09010305100c030e0a0201141303030f120603020117 68
    0x4614030140380b000103007a101040c4082e400e10b0101c0f98100c03400c4444502e041400200e4880059440e416540c0c00c0b001020b00c41c1a2480d9440c061201810341c00411020340b03800106d541d554051600620b104000b0100e24445010504c01654405018a21180c6080c80180f1010703900049200b100c050488404050700c00900300303104041000104000f95004d4810040f44d0850304000890141009a5151400440409030340c544d6009102c8024060700c1c1490205000d89000f07201401090584800d81e49102c4440c0e00e4524003000000084402c507850354100014040010b048503031050358210500d146103010000780c40300c5c90f000d145102c244400d1008010894500300822152140003a058042c6540c413424500c0e40c80445201c800403d500f0f084009036038034807078001e000842c0310b100300509191585600560745100004c8101186030070034031210700d1100005410740029402500ea40c0d11840348954010079500140c501c20100900b03000040005036070052055102e80105030300c6501c241c448 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 572684370 1250 572683120 572683127
    0x50304060615020a0c230103090c0f14010305010518040f0501060906172a0d03050c0a0605010e0c0f0307030c02030d0c030e0106090e0616021903020a0c0603020c1c 72
    0x403034112900101142103410700c0740e5000a950000300c2c5c040c280704901c00e951a089030080400c92108458101d14225001c600795000303400085209104071103d80c10961662030411041c02c0c1c42e80039040301e5032a80780303000d15135030940303e0503024000a680d090811107039059110035107403002d84010079282110021a05011081d4840c00c01b0304154401844840d0740e4080c045030180c20310440d002e040c02141d403040e20341d07481118001086611140d031031383d18107040c104210104075000e20540c103000080003841400481400900129403141d8400203e41d41490712131040b026000301001003101d820080303e00700850301800c2d6130b400603a6203801710368800140e5040b400c6000784242c0301034403070911000d142600d406402c0410f540c05000004c00c080350759404944295080c0b4640040d19030403582c046110580300c041d403010210710a0046a0344e0500641e1080d0307071042401e00a40058121025101c00c01540c20b00e46001400c49150541c10034012180c4d6688900507080c2c01004824490070364800c2c1c2e0300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 572685620 1250 572684370 572684381
    0x71b05060105122503030915020a03030e0102040b042301020d020c09061c060f050a02160b09160f050301050a050f0f060a08010204031b061713020a03020406060203070312061505030406 81
    0x11449502c0300d0125800301c4c0042d2039001804100d0218204260103c0c10160f03003811035496a2070350b80208034100598405500030400900ea03103603255020400418a00d0344034005100502200599034048540c81401e44221840f25400e0307411500080d10230500c080e40022402c0d900b1078201c420002c1911260001045003104d4820380044041800d03079001440313901d601041c100f290500040c80340d40d0350310300c82c4401ca200d0180b01d02ca0410301c440d403503004500708908859000600b00100ca04500c031408a0030029551644541e94074610850300740100d040a0240a81204e459001030010b81400b500100704034200600054450303480c0e60008044e540d81802150040021000840d56580c890514003485042d0b119607403403c1d0329915000801600ca0389032089040005101003901d51600c001c81c10103500c2107401030381e03c0412404080056a9284140e000400a5400940c1c1e124010303e0040e00140104a100514a00e040020044c2200710a00340101284a1600550b29682c5103004002404c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 572686870 1250 572685620 572685643
    0x6060801020f0f0903150405011401140102120d020c0106032006040302060f03070909020c0f12040501080408030a0e1911040b130b01020307080a0903020a09110f071a0906071b0506010512 82
    0x11b002401d000034480194440617200d048006050030396a281c84003079640c0701003891001c1c010390142501c241613501040c050b0000b80b030760b2079015150001e003510081c25106107400c03e8500c00b01a4034110140100d141e80c0005403007080d2919410310b461900002c100f40907030b0700c0354540c00e0380000000c2c20103445807400c03a000d4013244504544511040c14039640e11800c003a104981440740c005448600301401c0107031021104160358060140d541c585d07902072941c0004c2c00151002d920782c250400b01d01004c2c85110f4103104182001d0800c5400f034103000171200c03403452090303021750715201a500e86916840d05001c40342c6007050000c2a001c0412004034990710821001401c0d8440100e20000820b61242c2e200c82242d0013158051481c070748492100040b1024401c124002c404104510107176888600c02920b8664059803692400a250903949001c214049503c4001c84e0440c030100714109070080310107201c2c80020005443c2000b000e680791070b6200b40c103019603445030088d04060300e21a07108000314100c2c0c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 572688120 1250 572686870 572686903
    0x11060103140d05040503060a0c090f0e0f01061b02040507021603060c080105060a02030406030b0f040c0818010204182a09050f06070b042301110706060801020f0f0903 73
    0x15a52800d14001c0050301400c0038205000308104844003034415002d0398241c40006001c0d0280d17071520350f004002420707442d01810520000c441b000072080400c00c05007004180c0d645c00e8040e94500b1242c01141550140c21800a2000402d0a00d6050392003400e021030207a815500003d807910f8003401603192448000b0800003014051501001704040d94103c031103020b045886810940c1d1b242d000b001183c1c0100c02e10f44006a00030302040105c588a134008031402d030409004002c1200f00c00e004182540c0c0c6880d401004180c4060034070212030315040d103401009a4030002103040c942840590800007030307900c2c2c8006c100c42d220846203441c43d00e0a0300d1068203034580d0b40034180032107225001400078445882080e1056100344000e0a5038105201141c00e00c82d800381e1804502e42d2140d89050000200c09411400403540c5143c91070038140c02d10a101507021201c444030340b2003095151210903101d1581006040741d0040c0541d0300d1a90040d4180c8142c00b009078650380d124104100801c0c602070212000c412031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 572689370 1250 572688120 572688133
    0xa14101805010506060703230714011b1107030305031009151805040f020607210908071d0612010b100e011d060313020f0d14070e010501020316020111 66
    0x1000c41222200c0350561103000244000e40e10b450070001107005803000680030034640d141050356031355a16030041c1c90341d071a540560700300031300c9451f0f400e012642c01d280040c1076035440341d45060080c4510142c200c024454680401e80740302c004043c0b0740b1500303e480010140007020022820707003190107001d00702030084400204954602c1d641d90300003224051054103038410342092800a8009903014191080e40c019810b4800416194280303e2103038403a40c0f06030745c001c03451581440050031009032000550050355940c9401030401503054100441607100c2e450000400030034405001240c0c00c5560b000c1011a849404040c4054216001d41501001c0c1079010307140089410300c081d000b140103401e106080e43d4191000001881c01d80101c00d01c2484254000400e100049010707180c0c0e440c0103d81480501005042e02c0c2610204d81d10b00b02034002110b1400300301c603c00c2ca083c6420000e400c000e01c3e128071003001c25490322002039100c0c42030340f41004502061840c041c0543e40100c40c0f020348801070004a464 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 572690620 1250 572689370 572689391
    0x606050d120f090f0e041e05061e0907031103030c03030106120b0627280519061704030c081201050112090c0b0903010e150702010501090606020a1410 66
    0x14800004281c02260089029940442c40f488451042c1e41d6002c03040542c950801c10304901c1c20000400031030351243c00c1e840034141884a248030715102072280d0014103d9082080103014191940300c21098031006450810100400004500b070490381c00c1246058015101004a4118440c2d0702c1c04440d03a21002000041c0300794031807151034040302c80c1036080104842c1d000070040b603441000ea1120f003142c402695880c0504010001803440080180f2515a200c030301d0390b1000041c0c0620000340d1100e14203000c00c01103800c14100c04410000320034644c40b0301506100c0060140c600e0442d040c41468494400a0f04147c000e1f00c4296100c2c1d002448a600c0d6080b03000300f403105001c2406007a0000d07080d0141120b80a40c2ca000b440c60050380300d0071400e405800c0207007100054001a1301f05501d5034807500249000034051202c006000e201c0c040103000d43c5449403010b8256141031344034114051401400b04903a07680401d2400f5482c0e80b0180b000c2010702d803c03002e5032414884071a83c1810610b8100b080d113 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 572691870 1250 572690620 572690633
    0x15050c0601050d05210408070902071505010b0a0c0305070602030916090c05160809270f04030905211609060e2203030f0906020c06100503030a0302070606050d 70
    0x1504102100444410381c0e26070040c07111059141c1ca0081056004440d41038000d5145408a00c0441d0041d01403070800381c1d00d103107080ca8900c25600c2000800d40c001080414041401d09203001d010380b0402c184565494072559016038400c0021403000c0000100b56401014490307000c44043e00d070014019034903810f000c05016180c00c584400140360f04040030000600041600451400181d543c43c1d5a01305100700303420b80d121030480201240d00360010803031070b0b400396285606680c400d0b0b29000100c5000c0306810031401201405018103041203203c50402c0b0001e540100c0000607200160307440c80350402c10f500701c01c0300c016100c4036907003d60245900804111346c0804103c400c40d40d041c0300c1030041c240e031106c101c160540f00303485910401c5c0d03a0007035071501c00e5080d02e28141c10610130316001070501c032050b0f010000c407441c074501210310300d400156101e0411000c201103a0442c041c041300780940381c6030600203541c83c4a150303441800d0603000f0442506002059010400400c0d004c1d0030041d00e40e40a00c1c20741c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 572693120 1250 572691870 572691877
    0x30714011101090c140f1f032a08071101110f070602090901090f180218070c0605160f08070206150d1401090501061d190609020a120606050702061c061505 68
    0x171809003002204019613891700126a10382c0070030007c01001036640c5c2410403805032140d00030b04810100d09514040500d503400c0004c2d143c40e212540c450085060028000340041c0020f010011140c0c10003203000b214201c01030443d1036042c4459032807644c03009180317807100184c0941d100301036001d1115400098212450340080c02030f142c2440c01040400860081300101014500010b900b1444001e0402d1090800081c0660071406d681884403081045503980d800341d031400c072920f4a020325440202000180c0101d409540c852260502e4004c0c1e2400c404c0003566540020216401710401107c007103140e0f207416101d6201d640d000710b0801c482c105e941d0400f5000c0c00c0d1080b8215219842d01d00009603018810a40c07540048015034200695128100c0311003030740000035100e00302c03555500d10014028219200402400d0344c40e4680d88030031400801c50008541c019480f0b00203101d42013003002e005031b980310105c07a042412400300700c0d8101c08000c6014002c2009800c210303451281503980000454001014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 572694370 1250 572693120 572693159
    0x5031b0607050c0c06090619020a0515161d0612060a05030d050d0510150c050f1c050d11040f090b03071809051f09050705030714011101090c 62
    0x3291840e4407800c1003150310784128101014960014202e2a180386440401421841e02c02811907050000c520320001e681003140d01c210001d640a201c18604100c401d004004007100505440001c9250203030602082100c410390f0b500030890400004160701c0300359550300c809610041c200c50b8a420107107240d83c6440c202510b049101d0401c904000802c1c1c41d000880c00d444080543c0c5181c2401c0e0749038024030103804041e002142010043e1000700b0045e01e03071925528424440c1c0d455109510f10307803c260742806d0107049000a40c0e00048445070380004a80720700c8583d05940c1c50100d60780e0400c0102d00c4000c0038030610304204400005000148a08412812130690f03110600c100b0510380490105517440c0f0440c45401c00790000301201c004101070a501520b9000c2c0510300352424042070780d0240b20400e4405105001d6182e4540319a014000b0401004028000c140c000345412410034010110a86605490310f04000001c82c20882d03000d020342100c1c030102c2c0d11141581c03070b8948a07075007018000707400e150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 572695620 1250 572694370 572694373
    0x111623010f0c09080705010207060503040f020d200d031b0311070605030415051b0d0b0409030833041509050901090212030702090115020a1e0b091f051305031b 70
    0x482c4c41c0d2404220340007107920580060062918182d401e40d250341000b4801d480750182e17080110096101c025036081102d03c1864400421403018030301030784520f2982d10700c1e8052558180d1000002e13401c80a05102201003440301c0da119140ca24044170103241c04001015140541c140001e50301e50403031302a50040744201044a074000b20340c1210011940200c841d0048200c0c06e0344c141e4080c504200040001501094020400c94800e4003c507042d20307602202103001030180420090222401001c0e541107000042651b00301d054441038194101c04440300342d0348141c3d0358400600d0500400d810940c001c00c071000d4180800d180001c131440c02001000000e0303000790303034202842c4444407010044a1000e03500400c225403607402c2448140c540003410884000754440d40c0251004500040c45824403240c0d41c450b182c01180c014985240c26a01c00792200c880c6078408c0600c03201c0707840440018480c50307841c1c450004070b0741c0c4e0381c8800c00b0303680300d1000c3c0182140c000001c2da03080150b00c401c41c2030031007a007040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 572696870 1250 572695620 572695637
    0xf0408071a0a0e04021803030c0d030b060a0507020402030718170d0f050304141f0203150a05180907030807050d021606090e19020c03030109111623010f0c 68
    0x1004011078419540c0c0301c0000781007001e2070780783c0e40341c0341e405032882008104494108210003000300b40307182e02507a02d090450784804c00c0801c8032945401034140110051711818208202c4080c003600b00c2c005c6210007446280c0110008020714880d4803010700004000200030b0b422646e81000c2d03038081181c0c01000352580140e030300c038610f00c5003d03403c9a506411559a09443c40d69641c9926000200d0741100710f44600400144d61441c000c801440300b08410044001079890520001d18071000884006c01d5001d07583c290320801113a55150b840702030041441c1400c681c6c60342c030311600d00c3c01d0182c9604001d2814902240031000e000d8005091200d03a45181c08541005400c1300c80725a014040c0e01c1400300065901c4814084042c40c1d42c01140c00c0000c2801c0705040c44000c40501d03099802052000426a00101c010402000903001c1c051000c84c42d0301d40310346890181003202d0074a032408107020b031800586010140031b000e040152a100d1017982802003280510340400c1001400300c25181c1c000084412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 572698120 1250 572696870 572696909
    0xb04020316030f14060d050a080f04091409120d0e0d0c0b1f09020d060e01091512020f2b03080907060206010f150504080312011a0c0c13020f040807 65
    0xb03214040201300b8400200c580c81c1d0b1154204841401344110459082c041d000001c4009a502c40280019143c1c14041d0307526a424054034200f15509200c1c04041181d6000910101c2d81000c42c0c40c1e40310104984265680c4d00180d8005000b40000d584c80115a101c0c0d2100500d8042d03002a6016400340305072844d464641383d070003150310503041d09240321501c44c000b9a001c0020300456401440407400c0000d01007411a039030060800a59000d0f8058080103440704480080c034610501c07800d000d440d451000e01d001c40c100d5004205002031140c18540030b141000740c1d0000c104031401c50200a030a4104030503240c018a440c0060890304150b804c07081d148600c120118403580086600c42c107a0f10f4440004854900c1c10690b55070580015160900740401080003050700d0b00d0920042c85c0f49500d1528102441d45401d01502000b210194803e02442003486110350311880400c0c0d01081a004895951603441407200c140001d10a0395074070866a000024006030400001c82c8090444500c10212b00100d1070b0f8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 572699370 1250 572698120 572698151
    0xb0d0506070201021e0c0606100e030708030a0809060903030c070f0b0a090c0b09010e100c050601031b0f1514041706161b0b040809040e0318100e0609040b0402031603 73
    0x201c281b500510f4016400040c50703030400c841910007908140c0340c030090950f18100424203090454100c92019000000c00c0c01003250040051500600c01c44014002c52074401c01c42a104d0102604000b84800e00003295030070b2204115030b004009410000d0b03900281081a03601d00140b41c071b0442114030500e004400a21628260240c3d00601011784484805104010410406c1420310148405100400b854100031a0041000c4c0e4040c500c600c002140d00758400d501c2d03484448080d4005442e4080700c1e0414000001044035542c00c100d06800c210a2812010046020342d0060743c10100021074818407003100480c00280750350141d101082c5a0101c040c0a0f14102c40f001e480811802414080e046100001188100402d034401d015001132405d0a0301e20b00081e050b9910603451071921780c4003242440c04804200300003002080b00301c0d0084049140710102a00303034065849000e11030240801c8607001900c03150030215003040020421581c0380340c5841d000310040c5c004c1e450400001d1912004c090b24420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 572700620 1250 572699370 572699377
    0xc0506041a031306020301170709060612090309210c051801030807050304080d0c02030105151315240f0c05060105041d010f050910090b0a0b0d0506070201021e 70
    0x103405440350404940006441a154000b40c00b41c1e040c1c003407001085004c102c051001e14084e042d220364080c2195400c0c0003162409100d070304080c004074540401006055040006248080303840301010802243d503041c10b40e200701c003540c08030b5010301081085031000020201c00e00c4209100d038023810150341d2620148900c000d094086003040441110061001c600c0e08005064003900c10003c49280c1a141d001d41c5007040650220700d40801d4002c0600c4007146400e000e030540c40030424000070680c0301c66000040d09012151221250b039952040b00d10940102c1c800001c001c0c20800303130110103004231440500340c3c0d01c03510f00c5608000390442c0091035026200c1d407880040950450001c03c45a402c2000b00001001d02c640c3c10603141d680c2c043c101a01003000e010300a150845080001402d150000019050919502c0f124400701d1400d2414030000d000c880009402c03030f41a640001c2c1100740301c0085440e09480c0c200207003c2d842020200110140d054000f48100b40141405c2c9020a07085500000c0320b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 572701870 1250 572700620 572700629
    0x2090319150e07062a03110a050706030212010e060d0605070309081201080706090308070809061b010f0f14010e060109050a2405070515062b050c010e01021b0a210c050604 75
    0x1800017482d0010901c500c90024504414405403820091260b030b8603460020541d10400100c0c2c0c000c104a0034208082c89007030b0050003011098010f5190003800219807010100c001071a03182d4440c082540c00e4400d5200b604500c0e407041000e96110000303140b12a0444d024451070001e0300c07514202089280c2b20b491584100c035130200c002e0f0300300840d9944d1450250030015040d03400000074801542e04400b40054041d0004912380006508400407003040c058501e288040ba203110b003080302900e0f40c10b80302034440b811034500c1e021483d41c0352142c50041700e0400e0960321065005a20301c3e804034451848140c900400f21a242c03894295002c506c400b651a805142405029170b00a0710b50781b80d981407400c3d00160702c160020f140c0540341104580f01007400090340c48980030314840518a904000c800c02680e80d40340800d091000c2205030550000350f84103550002c002d00740031250034500054940041d82c00180100c420101c5c01306200e100100d503000e20104080d61265042c2c0350000340c5041a100321000d55 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 572703120 1250 572701870 572701937
    0x4031419020a151b0303090b07080601210902090c03180a03200106091a090a111e2106100f050f1c0207030216080102090319150e0706 59
    0x2d807801501d0f4101c20784090b03100040c401403040c40c403013520352a070820803040c0c400e44000039440d0880c2040040400005c00310380070300c9241d50a111740360785c204c2046500c101d240b903030702c4074940c51001d05400a040c0c00580250803a81b001c1c02e114bc12200d100c081d5200d0384040b01c654201140902000c0e41d50385281401034046092070004050000026103007240300c41c00c86002040c0d079a0303504001011580f9001e6001a108282e1840d03141600c1c5c607503200c681002c0980c10500c1021001468640684580072810310850958034850914540e44000d44a42042001152401810083d40d030500c0301c508452861181c20b20324006000c1900510249070300d543d007640c0b524188402c04410020940c0440b11000e8501c00c0207c4d166900d44450000301a048e102c1d50150a00b0040850b9031104440250044901e41c4d0040c0810400c54400003149400d0704848031010032005402d00b0040d58413034126081c0d221240c2403e250a1507520005400703c1120540d0340e0b0394101c54407282c1e1000450160240c0100300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 572704370 1250 572703120 572703139
    0x30a02031602190201030c020f0a060e12030603070501111501080a0b06030303040b0a050907090e0102040f0f18020a1106040b04050f2802180114040b040b31020403141902 75
    0x245d40719a100c1c0e20089842d004541181c00d41500c6545040c040b503108950321500c0c1e800307401000c00c003402644418600080d519007142002c100081c1c45034000d0065904010340c10000c4c0200c08020407407403801d801071508281007961102052521030b024028155881c240000114000b8240002142e210325041b001058036034407498549005413170054840401413084140200d00000113120b40b030840300c0404001a0345515000c40c03030000d041d807544040300c1f000c03185004000c4a1410301b500002c41c03615175001a514440301400390303000c4846101003030080c8a214200700800107950100d0340075900074411148100c410000c60f42d070301c0c0d860030032400d0198000410036001e07102245c410780c00b0300d10007020841c2d0407040403001028623400761302140c20851081c05602d218142031241300754580f4241e4091001d21101c4020038201051001d2401104003030020850080306002d24a07503510030150001d5560715903e00700400001c0742056022414000d080d4415580316010058100d0107074040c005166 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 572705620 1250 572704370 572704373
    0x4060b3a11100306051e0f09010501020607270902070b01230d0503190c11090c18010e22110a08040305030a020c1e2104050f0109080102030a0203160219 67
    0x5201003100c4103141403503101c200c0441c081c1c0d94034020501202c0072940301c0b005805008200001007d11411242c040c8a40702d00600090340c4c08540954018481c1c1400100407080c280d04104548080c1a0b000c0d0914100c540480da07464503400038800d41d40181202200341c0d0700c816004100410032650014114144810aa45400c10304554070752a070181051300e08106120080240c0303a0003118000c000560000c4082013084036039800855080b1064400051a142802c4103580501c00e02c0b01c4403100030144542035685070300c1109804040c2501800c400040d01c2d010030b6004800500322910305003141001500c2080038030020640709000456664401300341c940380c80c02d44007039201400f400da4054080207200b40390001049814940445990303500e002005070030307100b401d204041400c0301405001040c02020100c0710000d580c207480c0e0071600c1503107000d503080059946821580c014046540048104030b40d411059014520035038048140080c440c0c05802d08986440c1d4003000d9250030b2100e40300f0b040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 572706870 1250 572705620 572705629
    0x120f1e020d0e0a17070e09010c05030109180212061b070f02060901110114010e0f061e0301060306180302010b01090e0a050414010203090a02040b190e04060b3a11 71
    0x814400b00600303044000b07501c54200c8504110755102628242c0d100c140704100340d0051008155001c1c10020007084100c191003002046840103101c2c40c414651200100f918000324042c4005441d03600402c80c3c003403e038024001685409003120715440c0c8d440030f03102320b51000c11504211444558090f4540d41e540259500700030302034010200187c10080c0040c80400000300034414034661400b984040034007036151140caa201c0d00070050071004a56003820611240e6180c0160035a507034840381a58649101c0c9002c0400d00620f40b50f84060511424152450342c1e07809040c001000c00c9010303500030310100e807500700107481c0b0510038480c14082078840000200320505030381c4040e030001d114146078031801d078105280509a8206482038000381c3c101d41082d900314549441800819101507441019021044400c4140000c82c0d11503114241038242c000390030004558400d5040480c000e00109603060008144028004c2540e01041e8260301b8055156005038244840c1c180298005104804d0140080900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 572708120 1250 572706870 572706887
    0x120201091a0c0d05030105040b042a02010b0d030924020601061112030106050d051f0303030207050c040c1808060c0906131a07151112040f120f1e020d 66
    0x12400d000d010701207038800e800288051070f030110040e61125201e504000030031040340c3d0020b180d948178034038100120f0b1031212141d0908074280000d24000011108242d02030b409000c201c1102a408040381c03521004140e0400c80c3d8505407210100b40c0420b09580c0303821414110b036035144110140c1e00440c01004010300c600d103001c00b032030036001c1580d02c0c03c400f0122004042e0802e0b0808000300e0000b10b440e01049100d03102d1540c1c05007812940c00407020100c0d1242c00d07003c5460101500301600040c0d00414410108095855a500a04200440106184018000b1040100c90304020608001c0080e1000340020000e006916404855103420450002c003d02540070039040319010890990005441100085407503003018070303100360343d5103500c1840c06951300540c082d1500d21291400721002e288072065016103240188010314010340f501e85003007001142d51101d030018002e21442250100150703110300c03014803850036900d4001549045083d008440c483c071409036401030f8080070b54a02003612030301c0300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 572709370 1250 572708120 572708159
    0x120403020a120807080702150c16050a0506011d01050f010f020f0d030615090f12150230060306040215040b030405011d0706120203060f09070c0203010612020109 71
    0x403220100101d80e620380000c26520000c0700420303d040100540309410508580c2d01c5446403000c0c0240b45807141051411400180034000910004581460000301001650910a40190072144110b81500d0810343d150824000d00d442c0038860640c21820014402440d8160740008022003003101c3e202c801110f0b040c0c501d880141c02c6200b01d141441a008050145801c02006a9000f00b203107410509504010041840d0402c2084012103003044000c1c400381514040d13800074910400c500c0c07a00d080c15880c00090406613001244005800f07504924110b0300103644207044100102c2c3e404029040151140c0b0031030320903806801c2007000400520b083e0600c09041001c81000c0c47c01d2584404180c841a04119400c841582d0340724426001e00050b07201c00e81295011000514190303080880c0240b2142019007968044d0741c001c030100b116a91074440c184402e41002c1c0c00d0841c107141058005000420142e0301364001d501c0d1440104036030b0382d04c1c03440c4016030780c040e1520030195150510044801512011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 572710620 1250 572709370 572709373
    0xb150a0c0f020d03030c110a0b06060c0313090501030c0e0708071413080304030213060f090c0c020d1109070f0c020904051207030c0506070203090d0204240f031a090312040302 77
    0x46040043e56101d0700a840e19002c0e0351700007050008020b01074204a0200c9025400f58491459000010920b02005074402d0741030303400303648500541103a82c1ca0340c0500c4510100004055501141004203039011a0489018000e00300780e0b02d40c0c4030440001c01c20140c0e1a0400240114001084980503001c48a403800c0d1000041f85840c1208901c030741c0e200402d8010480c5d5400006040003946414142d0301d1000000c541e04101461a00320b866040145c9441102c04040d1500034800c4594003c540b40640d90341c002c0c2c10041d0502940c98101c03558852100824070a41e443c0000c07401d51882041c01900070f1400740c440304c0503000036400300200058010000c0710b451281644400056252034050081c00d8401d45401003524802c0c40c0c504e08002c0e00611034000c543c018032103402c41c0c4d5201141c614445405079000110100315048410852140d5129559145d000b042c0000380c2e010381c01100c00c12680100703440350792810958002d0006c444280d50340015540180000586a924a02c406070024070a00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 572711870 1250 572710620 572710643
    0x9080c2503063318021801110703050102130501020f01050103051e031303030e011b03020d030f0213030c1805100302090c071406010f0b0703140307090f180b150a0c 72
    0x88400f400b4995000e89841c05402c0003820801c0104115110300c1c80d08500006601317010001001401842c400d640b0681080500351440b02c7c1300c2005c1c0001c0000d507030411b00941d501c107003048070036910544e54070441d40144113014520206120611030641680d92142c09420683c1641203034a940c13180c02800c900715400100011500b560064050600442c425150700500300b96100000d40032920b0a5a0444481c0b8210452000a940440d010504030b2031403d002a00c503140750522070003401803082560021580c1f00010082c002404950743c200d44000820340e440d0b040600600b0b064034400d44a0a1103607600c01824001850581c282c694025103074060b01d401c2c40c881d500c031030004000c120b958041a0304035200500c1003120300480d400141900f144090703d45000c6035002081100c10700c00f510a01c070320220100d1805807143c00044014401d4055410f0125114400c41108108002d02d10408503d000c1c0f004c45581007004560148102d1180c2003803c001c2c1c01c01050720014040281144c441c1220b2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 572713120 1250 572711870 572711921
    0x1031104031104060806100e0c0c0a0b24090c0a0509030a06150f2d0503070603020d0c0201060501020a0b0406060506070614010902090d020d1509080c250306 69
    0x1600041d03015420358411590071000b4402102c07002c0e00306404d10340001c030400c404020068603001c200d55100301c680765503036101d07803211045000d0500c3e010401d0082c5144042400320036240507014011880106200c0d0ae90302d2001d96400100041131038200c1048400507001080103005414071400d982805131800b06420002400c5c42c1384a4401c481c11513462070003a0900008034140d0018116407090b940b281030410300c110480011030322030300050302c1841d190080c0e0384840c00307150f0703000349006400ca6040546a45018019400c0b41051800c25031509404889980c414020300d0103c0754182c0140002c681103480304000030a0040c0241d6030030703443d0100020151603880007070889901960300095a88144400c82080880680c80500e400f401444101890341d1032010191081d54125500c1b040c8042516125a11803161400505804e182c01821428020b0a030b004200301c0782e070f203820b0f15000307107030381005008a03041c4002c0395245a81c2c40c8828400182607034040030300300c0c292000c407200c4c10844 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 572714370 1250 572713120 572713151
    0x32a050f070501060b032401051206040b0603070c1131020f030106030912020c0901050d111005030105180c030411210f01060905133215060103091a060103 68
    0x4c0c0c0d40140c070a200000104000d501011490075603208250498988104204000030140c1c09001d416201d9100c4c07004c0421100d94442d0300285081c800500030584074604000042c006424446c81030b211102c3c1c50300c3d2101d440c640301040040b40c0c54403015129100d880195812620100280a020007a0703007040a51000003010002d10300800d03031a41d01281c116100c0c50320300340e65108000741e4029980100c0c2d2141c82035030380c00c0e41141900c0707060320700c0d101d51011401d008202c500c507a070300c940d001440c1c20442101180d100d001035058075401c1c0c8024000c2e0021842c8080540740403140420440c40504c00315000800c000740f81c0d0b2010f41c000305003000700e441c40040006100108090401d20381e100b10311880f0311000a005800090006003010002890000c1000e10300c0b0310440c4004000d0001d40b541e014846d00342c240354a52601111a140c00b4422070380f4805a5a8100402d40480c410100e80001344213601c00e00030100c05c9580301041601d44c1c00d500c204040c0000014003580d05158599404c90383c8041c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 572715620 1250 572714370 572714381
    0x100302090d2a06050306031002090607081206150a0c08090406080d09140301020906070605040602130f0608130218090c0303070b0f0114090c090d140c01032a050f070501 74
    0x21507411110307810090801032900482c143c0d202c41e00b0300c40e052003080050b0790042030f40180c03982303601405070355a080200082c41c18400e0a80040044c080400c5549048400c8a003a41c0b103640252203001200d020a1044901c0d4050b200c1e407000001e0f00c0d040b00c900080c0044000d8503144a02a10201d041c94803130800360300742001c2003060000205403120401c600407020441988465054008602e09450900421180c1c0300d003800140c850758035403000c207041042c1382e4111404803010705001c41c01183c0750350722406013503102c2c8150000282c030b142c00308007046001c1c0d1010840b00d0707004000b0680820400b9505140c400e008020701098001c28041403a039860a00003805591322a080041d081e28111070340c5504108180c104075040c1c40d02d0400c41c6000e880f01d80c091604004515101511001e01e680011080b81c00c11800904e00c07801510040c20808000491380b05003082601c040c4031b180207041485010301c581884605044960070305155113140541700402a0141403c40da51800070341d610703481d082d181d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 572716870 1250 572715620 572715653
    0x15090803010810050a05010b04120c0e130516050a180905030a020a020a36090609060506040b150d020c121612050f04090b0301020d140a1a100302090d 66
    0x41100390843d803075601901c10303c2d42c01030300500c04100d2541011400756190040340551340703403c891a0710170340c140710f071068a080061034408100c2105150019250078408100d600403122882540d111040030784c2419046000d82e41c001c0c1801c0c03a241d1500d030f1154000560744581040c00c50390361344200b01180090000b040c55420f2500180b150714068410b0148900b42c507444100c080c6400101d0f60305450004d40314188030712256500c01c150201c02510800206400a0000e2255107000c0b120400c1040640040b4807a10048608102000b418028442000b40360b40002142f500d0030001d51541d0030055001d4202910f01c1021034868412058030350045030b2040c0f91520010600809800800c0020203c0740106c2c100c43c41c189040c551506419200c9001e1030140321216134881d0b0300f428068409605940d004000080306215910320840e0600116000741c401c00401400e00c3c441012411286008a095040142c50741804075680712048001703400061520354091a0035050001040088504607001d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 572718120 1250 572716870 572716873
    0xd02130209030708060c0304121e08160c051f02091207030605061c0201140c0303070f0e030106300213060905060d05150601140c01150b090d150908030108 68
    0x5212070010186403101c01c0e40070740c0c45a0701920801c801940343c04162604980d014845901d40025114240c4241104181001340400307000d0700c00b407803664417035034190081900082034502d21402c05001c881c4021542c03405003640d8060000d0310304545119160681602400d903006080082c0c540009011106918050085500540c002d0090100d2441080d4000b0811184406500c11f00b030800400e84041d2500607061000000a05003841e560004503a05148402c044d01c0c1c0e41e140502002d03003001640c52280002505e580c5500c8840d041c14032840007500c440d4450f803000c0490810686000000041801843d01e0001c3d01300001600e40d00c0c40305070080b0a44801280381d0741800c01078002c440006180602ca0000350b4903200200d940415049480100c1512402035641d5140050340c11200400a20302d002c04002030880b103c003019441168150040800a6842c42d518103911780301d80113908001d40d10141c90141000040d102404581e0300480158021401e00c407161204411a0000d03440204203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 572719370 1250 572718120 572718127
    0x271206020c0f0c090c0a030609020f1306020309031513020303210a1406040222090b09130c12060612030c1e0b0601030c03090f030522060c110d021302 66
    0x50410b0100d01c81d00300b480c500502c1d80112110028080a00c0900482000da40c0000c4400d070701413003a004140a8800c0710015540c85608040001c3d05d50310042c11603400c10340d03412012805e24400701c205d541660000f8020180c0030111803242140c80c5001d0036001c1d40c40086480c40f00180c130240054400815448880c0503212028200b40c0200e50004010100c800d140403410546c45000c40d410a4015106072401620f035101c0c1c02d407110409080c20444840b11011300400201e0b41c0b0a46c100071000303481a1024a0f0303640711810b41d600c1380030110724020514000c0160500c146d000100c2400341060080d000440c0c5130350744032401c04000c104030300140c0000d21001c05000500a000c10150f550054000304540d511403d030303ca20303058820143c1000c0c10036466200524102d4802c0d003240701c50540050340060f01e01f00600c0c1c041c002d54000340b0751380d4a03980c1c102200c0380912030307415182040760417988641045030103a3355107903031303030b0030450040e0b40d000a0140400c405030b22800f0510b070444607217450041c0e8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 572720620 1250 572719370 572719387
    0x30106090b03010305031b100501090f0c14090d032001060f060f0905042c0303070e03070305061303120e07140406030201021e120d1b030504020127120602 68
    0x44080d5004030322188010030042001640000403070342c151040c142000c21061503040140d06001d070240ba89442d01c2c1c00c06001082e403401d19406000c5d0f100070b01208004000b444001a1004860751180001c2c002090021515505103a484141c66074400d02c1c000c1070415000505510707030000b88128000c942c1d501d0100340691200ba450318400341c040b604140810095482c0000e0001d140c500038203014035181d0098028091441c034030380201128201a11107070b130304030302c8c484c0b661780d001101c0710700004581045d041c4881c20041129019a40c0141c0523101554650200001c0c2d003000d424202c2c00c02005400034105120380707200c2c10b01340c03480f00009050103601d800c020b10b202c0003042c15802c0c400c070301d0702108000503a00082c1c0301c42c5189088103403d56603802001481e08000d100900c201c6d041c0301c000754803146614143c4c464001d0f004604148110003058003c11000c50b102102c009021611000ca000b4030101d0746400104d01403103580c4100c0c1100e07100c030202200b188424000702e40c6250003007074280 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 572721870 1250 572720620 572720627
    0xa030b04050c070b04230d081603021603050c030d1a0f09150409060212101a1204080309070f0f08210405150403020901061e080106050f0c01060e0c030106 68
    0x1608a11140100e03403e041c00c43d2240c580c5540041e01c02440d041c800c83c8084140d440069900101075201d4081e01d6000d0407046004d0f2488900301c451007404e400001030383d55841c2c064070980300f03101d00750360b40f212811142340d50a4480380d1120b603802039980707c1800320b11006842400b03400b00110042403064800c4411b6070911441d030740c803851828450f0001c0010042e0800001c940385034000400c0310046121401030814000a110b030101d1000c1c405c90100c10413000040800d129400c46a04415030310300e02006181409090241ea0b041c841c19005420200d0b002c6039134a4099600003403103909882d1619913500e030b4400b1000d0320b54090b0082c041c1c500c0f800c2200d001c1c103225010401001c0300080607006c10b030300d40c51241880703075002d05445101e01200380f401030340091050b02c020b5a4080d21031121941c645401030a00341c50814080c002511841e01d801510f8400c2c18094100d50058503031b1403c00e003516000d0840c0e0f41103103d0948066681d50000984a20401030850280c034420682607525414100001c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 572723120 1250 572721870 572721881
    0xb0a02060603060c0a0e1816141903020f0d1e0f02092b0b0108011b021908250605060f010c080f030415050907090c0905010801030f1103030a030b04 65
    0x5100383c1200c810801c007002e00c082200c84208480c034016507448059070005070083c68007500b003001e041c0b00d88100014502e500051280c42c42007519065504040e25809008034860410011101400300051a00d46d5010360058a140041108151b0074170050720521401c40d00c0100034122101c520496903806960180b017010005e985560056151005200202c1c03602048216040d03e0540a01d28520459040a0b910880607500c10620919075956032100c902806101d51410722400800b407030680024000241004048100070350322000c0b10b56070305c03010307800c4e008800481c5585603020b40ca5640051051075907900c140c420003000800b808c1040a01c00d001c0c40308103001e8144004582c9200105500c1d43c1602c03006a20302c11055541d544504d0010b06560789000121101400d041c02d01200740008210003094540e440c00030080740b21000341c100c8a02e045071042d940480e8030340c00140081105550541c0d00e090048154420141c03100010074039503486088a50b00003903076610701514074500fa0145 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 572724370 1250 572723120 572723131
    0xb0d0506040c030e0a0b0402210609160303170703110703020a1403030c07060504031e110f01020319020d141f05010302040e0c030424151a0405010521010b0a0206 71
    0x30072000c00c101003015a05c0c03001120181005201d20002000c546d540c8460000c644800260786800200c02030303801d540c5110039141c82c10140a555104141003809a0180c0205c0f509681c48894182402d01c20415400004d44603508154503500501180880740d00200705035486640205050f000c3c1e0b041c1052000d03413290344001960020410311200040ea0002da81803e0f030000340001e00350b15540f5056800080008696800b042000b9814400d90b80141d040c8440c0340c0c504090720544005100d00c80d080380b20440301c0c1002810014039030f030030111041d40640f0300d00c1d08802c4000b84001004070000241d86048542d100c6924071102140750f044e00c444d11500041ca02803d00303506003402d1490b10761040b8001440003d8804012001400340300c22880a204182c51202e15501e000e000c02d55108054042e50842d051243c0010500041258007206042d8106200c0034805003401d040400441c1d041c0e20804c3e41c403440005010511101c000700c0151180207050b00765a86a035104c00400290904130700514 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 572725620 1250 572724370 572724377
    0x70503071203120b0306100501120b010813020114040f050a09060b03150d06050106021b03120406180e100302010305070c0f08090111010908181017060402040b0d0506040c 75
    0x10411511107408000c540c1281c1c1401c0015081580400381001401d00b201c461398184103502c140269020701c04c414400b40c0344281d81d0048480c2c8684004c000380c804405080740001c4c1c01d000003ca0000440c8a01d00350b0f24070514207540c020440d2002c11066401c50341140400c0c40601c04108968600704520720000d0074404428040b80f40b9001851100d400300030320110005800c000c2d003000c580d5681900c40480c1e40e103c6030402c080d50311200025075580c01400d20f010b4054407800880001c0c030340003502c4030300d11240070030741442d1606100c81191800841010724000b401218804100d62101c0044d283c440c02121946000f02d5140d400010103a42000e403a04052004404107030010071a2020181841600f0103511035560000600403504508040c0b9404819480c0c00303850001c00c54804014041701c0380d00c0e0102007007071652030100690040c1d41072005000c1204010f0784060340d600d030118130361301442c000c00050034903a50380501034455100e0800e444c205990b03982008050303d090712030a4991030480c038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 572726870 1250 572725620 572725633
    0x1c0203160809062a07020310050403030b2b0203030c060408130b0f090f0a050303040f0e010510050d2415030e0c1806030a020d0b0709090b0a0521031902070503 70
    0x419404900e04444402c8146800b90710780c88281c0301310581107030140f50380581151b0102c10801600402003400351011400030741070a10007500d500d400042c40ca03143d040000c481e000c0c0c13044040344826607500703500c08980500040c40390303c5911400b4410305209502034100287d407038189000050750030b811500a001d40c26070510550001507040029a90810429294008001d28034400a40000503a03803090b17030325200005020410010790140e01c0c0489040c100c0e14040769803a98108080d03808079503800790002c0c4c82070103d9044068a50403c1441c0043c00350901b000c444040c40034450004150440b20103a00d00c401c1c1038059036403512505817001c01c22006400c040c40a00009058200e0010410000000b4a0b011030340d603641c2846020b4010358000c02e02441c50156290807500c9000071078442c0081080a080060542c03410f009070f565405008002c000d10a041c0000c10811901203030803801100580e40c002d401c050b500b00b00400059400440298240c948044000e01d8040d82d500708900941122 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 572728120 1250 572726870 572726881
    0x6080601030504120807020708010623040207020627030d030c020f21070c05030106060309140304031523070e03010e0708060723040608012313021c020316080906 71
    0x21442070403030392150315000c201030316018007c0f0b02d0800d094001c1170385540703010400a240c00c01d603079070346103840011074030f0303006200328241040100d008030b40029402100c1007040d0b2000d114006580b034040d0198152010031a104da60209141c407043e030f115100031a54075440007114940401107280d913218980300400350340d41c880c5101c410403c004483d2034113003140801e1000801011140020280c800a0020001c05984250040103815180703030079100d1a50b032100c1c0d59104a004012903069a4214455009a2800c451840d0080240b01c8668008c007a854100606c00643da51403140103070040d6031010103c81210080508442c003043c1640b5650b80040c00c100710071344000c900702c2d50190705420400c0080c107060303c0c00442d845001800008040b0000740200d2000d0f0044956411384500c4819034540351001e04101040a086140b03031544240c00002c0603c416086400401c00c6002410940902c5401e0442c08400d9030070540700b500c042058114071041c030b25801103a09a10a5481c0300411860505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 572729370 1250 572728120 572728133
    0x31d011a060d0f1112160206010311040f1d010e2e06050d05061b0403030e090405161205010c080f0f0627090c06040f09021303061506080601030504 65
    0x240d40200400308681080b996581d000c07000080c3c0101d8244a28004101071000c0303540b0101e008400120311030b01045683c486035214500c210301640040c0f48590031030b02c0d1001120403c481883e4401e85a000c2c1555100717140c001c2c43c0d0482441e0785c0304a0000c42044140c0e00b0342d400d1a19006c5940c1c09183c2c1e80d2900201e0140503805095070340d02803a2000020403150029061603000346401c0b0b034100105000300440010321a21a403050040d18404000480222401d40300e14400a400580655102c2c000c03464140601078005100e04100d9100060940c800204012a5030055803805070011552060040078000c000c41039490389019191850617103012004100040c190801e50345c0058001106500c1c0c501004d42d180d0140300c0c015507030000301d10b45541c07148030449079000140181043c4545a0030000161012303201c00c04040c0d80d84c0c4d82041c01c404025040f00b80c00d440034503030380c420000208213188901500640c81185003000329082a0780600081ca01030403440c10585850108000314a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 572730620 1250 572729370 572729411
    0x201020c15091903061b1d060415030608060901200909010e1503010203040804090c210e011e02131403060106050a0c0c142106070f1e031d01 62
    0x8101c0310361442070b464141401203520684c03c020240751500000b0254600c104030303d400400003959500c101c030300c0f00025000f41c0804100d1426040a4148810305c101d540c000140c0d0348450480c40d001860b03640d194401864011f080c0c501050036550740f8280e40f042d1005c6071010f15584003100c48249030000000c0810360309031f0140b05400ca509071a0000c03e0103010340700380200c01150000d009644a003402d06102c1925409072140802c0c07a45017404d0140210b0184c52420a06106124a400704e40804a0610090300041600e520203550316810031448070800e60000f5404201c03120016110044003080c0d80d9429015045080da4010b1940c4c4132040d46c3d800150a419900740749012034403155005030a0300d6041e40031600801d1900540001300350803001c1010051500001c560a8040c80043c1c0b03940c0e15114040301c42215650480000502d040e40200c1d020320741d802640c5054040b10707124020b010720304108081001d0000c2d8a03220840d62002d40000303e900c85442c4500200f086900e40c4030b10b00d882c0403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 572731870 1250 572730620 572730637
    0x5150408101805030a030510270b04060506031806010b0705101e0218130902060301050f030c03060a05071e0804150b031b1801030308070522120201020c15 68
    0x251a802c03800602c120b0041080322180d032050849407140100e02d40600030b132008461204500194240010f64050006801c4c020413071400ba240c020140f12500713150140280340311340c64000b40c9900c00050380e51100c0000718400ca08501400c02c0d03400e0240d04190801c941a4004607101d40d003400500f0124101180304400348016686c0084c1e80d0320211203071221000221410007002f4404510403540c1d0503168249801042c045401085901410001e001119403401000e50000810700050040d0f003440f8640108205e0700034212194030507540c000034504075084802c1c0242c0740d00e48040c8030416400113042c070122008860b103010402ca40450082c0b0101000344080c00362000b0680e203405500d403d03030000c040b00401406a502006940c42201620704400c44118042c82820001c85005d080c0300e04564183d030303819a1900b041d030b00c07003440c00ca40f1600300d101e80802c0c0003400c02060811240b038080300780080c1821081e14080303602c980006818000302c03010040c028012010f01485a049160481c0d9488 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 572733120 1250 572731870 572731903
    0x5092e27110a0503090705040c05090f0306070c15020c0607020d0e03030412240608010c0e06030c0a08190606081e090c01030c2001020715020405030c0114070c03080405150408 77
    0x740c5c2d61822017440c0803500e40c411b5811034070303100d12260010381c0000141620142600d500c5400b0200318141640c5030421612100011341508180700028410040d0004428003d0009401c01000841140c01c2080581d00340d00980e0010404107503640d00709070030020102003203000e0340c203151030501c1c000c00c80c0901e10001843c0701c2c0d242e007000300030700c0004046460303921100c4010000c142d1641c45550082001d00c2d10080890a0203c0050940c98200210303889000c42c84a40f50519048a005445401026108281e00321000250316032200461184ca401030140c0c1d6140401c9080c6240c044488400e04071843c4105c42d209010800c50f10340c005a034020026007880c0006244140074401c4840b400c648000d408ca2414200321100900300540150510500603140500010b09912400c0200e208501c149505034114032440b1b5030a60080b1000b010300c0444400c0300d071900f000d0b503803048880211604101c440d00408103051006060046055a8141c071000e01d9a1409041c10396690b40c40c045690002c128 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 572734370 1250 572733120 572733127
    0x25050414120a0506090318060301080a02060306030a0b091501050d030e1c05030309211c05130f060504050607030614100201090b190c080105092e27110a05 68
    0x50703410041086890780000595600d030038141000b80c1c60f0b034840108800c8502c0110040c02d19843c203141103074100c4a060340140811040c9600b0701006400c01495141d150040028000c0881c40e4080840e00c2020b0741d00c0074060f65040d1300b02910850206800950041c0c0c011706005000907007115100c6401601118600344a01c90355074408500e1004040043c203a000100034040101d10008200315509159080a4000041c01c603a243c1d0130702580d019101e040e00e00114201e403424560703106580101c91404003042008075502c0c0d120f00d202e2042d4080314841d40d202c0802003840014020356800182514060012500d00403041601e030b000010100d10403900d8550912900e4000d6024840035584a40542101c1c580786280961841030100d58000c2e01d81011f2302c26003000c0c0b05c1e10406058590003484000303d5150a03042c40b598190008501005002e80d00f903400c1032604454076400201005d0010000b030202c240c18450440e01c004070071810312800c000d03441d014489c4010540c0c0c401080b51410545 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 572735620 1250 572734370 572734399
    0x80d030c0c02130b0423090a03020714062119050903040612020d0905060108120307050d203411010f0207030c150f0207050109050607031725050414 65
    0x200b0402c1013050b80103240002050544079451880c1c2114071580c501070b200d41c2d9035048007548034000e010004005801c025810301805040110300d207600f02000d040242040b034103d009044c2c00c001c2d00061060314045000b0001d0008a0b0f070300c039824140c0c00b08010700c06070600029040d07484c0154055901441400c84803240688201d80c1910078130003038020305014480b901e0801d41d885020078050780d0031038007440800b401210761100841e4003c0545541d510300d85101030143c0f000a10050150501000d0404400d80100491401524116000b03441e42215501c081c202d21400307501a120080c041403c1141c65804902d101030280603100080c24880a00941800102d06210032900014240401c0d4000482c0d80b02c0903103512100d0701c1c0706885000c00801442c0090f03036103500034032610b400582c10080900027130a2820107009214401e003001c1c9200c4482024600e103c9208980c40c0721700011100031031050340c03181e042010000f641410924039080c00c0045880390004202c44e807a01402d101c00c2181c1c1e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 572736870 1250 572735620 572735659
    0x20f07090c030b0a0312021504050a0308060102100606050a110a021c170403061d0313051c08030f100506030709261507080a11340804080d030c0c02 65
    0x10300d841802407034132641a0b240d01d45800d600c091408400014412a00c01e20304807080d00c10194012600708000300144006aa0100d0302e0710b10061902c0d04600844400701e01d1070180b40200000f51000c0d4480310b883d90000003000303000c0e41c0060301c0e036641980100300950150321507401440c0c0440321003140341003500355070800c8240c00c42c110000300e01c140000100001032040c3c070750041c44401e0000340781024410350301c00125603e0040071700810b4070b0742903060100018035100703c180281188108800403506a25280c0b04582d82040310f520812400b20000c0087e0b0704044000c40300681000c64a07103056040030000180501003d00a03401c0340702c80030f01401d04502c0c08040505420b48171000301c583c1140d0000b610044010240d41c50000b2421140c086860552140502d0b107840d280751a165040480d80c12802c90403810707080051001010b420741e9240030b01c00150101045501400100355030b685050445032400350b04c10019010549056140111030784d0140c01c2c501d08680484a14200c200c9052449 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 572738120 1250 572736870 572736881
    0x30a150f020424021005041104091b030c140604300b130b01050a2102120d020313240c02040b1017060604300203031c0c020f07090c03 59
    0x2803c00c20900c01d00000255100d4900020000c0a0381c20354409103a040180000d03500e0544005140000f000c002e0005410a68000c1c10b0076800b8070481d80e100783d8000509920380607103410503100703140c80110038011985c81c1500004224405d1f41c41910385440c0805145480016a40b061010000881080182045100c1005010350040d1b0080304030300b4801c02e00c01d0002596a030072200144120300000d91417030807040b09000c44540c14144410014155402070503840c0d0054200e0388041c0d500c001515120301044500c607403041c550004c6a8079801d1070610b01d004c44080d0b0110340341d141c501a02142401044c08807944680d45410a030300205000d00c001005003040106440d00106400c6401264aa110f86806240444002c07a1082900c07480203001c1184518000c820081600c50350a101001c1544203011603007841c0000103650419603800031381182d000f030707640a600035a02c5411002c850301d40d04c943c14180c0e0840c00284444115a50041d031140b072548105226031303a80c0e99281c864a80070790483c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 572739370 1250 572738120 572738129
    0x50f0f010e15100306090b030a1e061107121101090c032310020301150e0a0608060a0f0b03060f010c03021002031005150a020f19150b0409050109030806030a150f0204 73
    0x460f06038180c1d40050040400e80704513180b41e4100117205200e41004a180826203070403110750f050342d400b08410f214201803081411101550b55407c9140380340811030241003864881c5070b0504040800e840001c2c00714002c803000112507450000f03000005817003402e9200c1142d602c0308502c4150362046e000c141e0a5060202201624000c1411244041846034000c50586141010000308030301c070b501c82140c2408550041c5904050f00010600585000301c0c0785680c0701c480180f01c01565515100113040b06086680325035410303040801030000f50b14040b4000c14640c40d003071a0148004005840095407188034000075500241e0001c00b280d41200009501000b529000e440c4040781c164414110503151b1250940c1e80c0140500c0d10305503150207000c1050959082e600c001d080b000b00d0303a622094940003c8208125106554648a243c140c5a070701464440d035000360000201c0d00002c1c00c0c0501108001050240b1a0300300c19144030003c1c214a0900245201d010320000b414090000c10000034807480c1c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 572740620 1250 572739370 572739379
    0x3030e060702061b06010b0c071811070f030e04020c03190e031e0607050c0304140a090c0809010507020d121a0a030b09070807032a0b040902070501050f0f010e15 71
    0x62001c1d0303600e04c14241000c081580d034125140c980c0e81e24183c2d401401481c640c00029040000204142d0103802d0b03240d64140302407400029484440c81c80d560655004a204440f020f030a1100d0314141034008a905a404805980030751501f4000540b81d5242d125841184040760011081c84070450b109030540000c818002d01202c80700b80021082d40030132211440718030143e210300400208618403d0007500c08000920005504090911055454407001c507401182c000403036880000b000c0c9154001d2405089241d15a40ca4600b48820007d0a40700005c0c55002990301485000c01e125034401c0304840220544440041c0066250701608078100380c0010150740074051480110600120000e168002c030300c0c041c111540c40e07030740340e07480c070b840e07061503c40a0003001c65001c0715a0014440c40c100c2060340c01c5d400c00340e03580350b464100007400c542113a00030544660b804103002042007000d104a40d0043c008204840c0d807460b000c3c100340e0002405018410704050000b0100c0c1c3e0010081417039900c1101d0050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 572741870 1250 572740620 572740627
    0x9240e060301090b09090114040f03030905100902040f090803012d0806061806030a06020c1908040627051c08270607021f140706060305061f03030e06070206 69
    0x6580c6002c0e041200100c5c0c03050050b9804209015070500c68000c4142d08140c28500541c1c039502c0302c6a21140f004001c1d018103868203010360004205000c0030b6440910380f03200003494140380c0144021107011360742c0ea402c501d141c08590300101d400700040d81d045600c001003014101c20300900500c083c0e50050140c02040103807010118403c040829141c0c030614040c0d50140d442ca510800130800400d05440c402d8054010b91340000200d4225002840010300c640c0444030000291005a904107030034180a072408070300800d0038440d5a602c0b01005035542103a48442d540d003580c8a085141000c40c51081511070380c1c00b40712000310315200109011103a6006201c0702c0d02c0c0c50a051111074503001c06050701704484a038602071010351500c4015603071050780292030030b100c800040d5100406600d4000405090180c41d81004400714a40c80090a40512030500899041d18501d0302c24945000980214502c090030240c0408400084486070112a014903100104100c2500800c0040c840c603d4080d40140001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 572743120 1250 572741870 572741879
    0x15090b030718050714030c090609011b14010f06060210020d200309060a0c120c020115030503180a0b0a031a0a08010504020a06081302011404080d09090c09240e060301 73
    0x743d00052080140d5107481050400c2901c40480c01e101c00ca440c2030f8501420301441c14036042a1000c1d188801040c1441c40ca4041c040500c20340c040c90302402240d4010001c100034010400038002d80399041409042031041905111003c1d4441040b04207080949a002c00e0040c1c2d018002d400180300c404900d12541ea44e10318600e9200a0341c1e2046800c100c3d10f00c03414012500c19090340c450240c000701c80350b40c0c03040c880e0b01240700c050107000c071020703141d0440d900c84221400410031f024050000b144940021580d85c0c81e080d05514044111701112842440b90500410042900004503101043e1916001980080c05041c804420a02800076500920280d2010510745c10550041b80941e0003100e001d8440755031100d041790b05140485190003150108c101590055000d401106480c942d03501c8054101a19241c000e071078150181c10740c02c00180b5200c42008941d05502c07402c0046e101e42d103410000141020380380280c0c5460450030594864501c2c007030004091003140721000303403e4020429035980d45d46 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 572744370 1250 572743120 572743169
    0x902030f04060e28061407260c03010312050421030e10090b090604081b01090b030105010c230109120207141305060d080301032415090b0307 62
    0x1181c04031140ca02e04034921100d500e001900d0708150301c0b01d000180103111241c0b003072644407500340f80c111195610b07003004070003a001540300c00b8410340311940c40d4618440303401200740d07400d400e54440d1441c08080500f801303c04a82c00d011241526041089002e07884070a01c0100c40600c210351000c90390000c0e4104405050b401c1c400c0e201140e60096540c81c0c84418090104401c4024800d6110081104490100721143d03c2d9000340c18030310f400405003401e0907610503401d400c10403c07800c1e5000701c07262010958141d60f0082e0240000d0009008920f04643c1030500103030981c5000c04014190061008181c03030580800d03070146405000f460000c1c451458075190503c404040024488058003c00b9400301e01880d042c2c02803030701500c006103004807d070004403080e0014480a00a5078001c21810351542c0400e40100046008501c6509410301c25107140c0070040f404040799000004203414a000d4200d03d143c01c0d03240740c003580c1c0600700019030039209400292138031205900605030494080c0b2500030442c40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 572745620 1250 572744370 572744401
    0x307050f070609060201050f150a03320d0212070c0b0a080702100c050909090304171f0e0312090c03150609060409050616050f16120e0109030219090203 67
    0x21103031240f240d503e4950300180e080e2042142e1055910601c04d000800c0c0c02402064805080c0c0003600794610f2a80f03c0c1c543e4070070401c0d204000800543c0c0981d04560100307408014101d008030602c06080c0f00941e02c4002925900c00b110b9030302d602080410342c80d0500003103180c1e800040070040603e564951a41c900900084811200c100141c001e0448101015010380905a030303543c1c2694800703251a100f00c00300900d1100207031840045210511020803a0011201c8140000c40810000c0c2000101540c905542d0406104071144083c1000d411100c80c180000548000d122030301120350f02542c0700c0a91074030b4000720084040c0d0503c600e4011030031039024118804c0c05080e090b0380c400100d544210a00040ea518000300500e65400300000440c1709000c0c4c26400140c4000d4a00a4540b244800d000c0b003003038001e010182850307018000c0000800c0141056000b6842650038144010900240081c003004418800680101403580d94040020194003400001e0102c00e40215202d08000410032009503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 572746870 1250 572745620 572745629
    0x1707030206040615050114071b0f08010c1403130f05010c030b120606150d02040306060902180f0a0b2104030c050d030603050601150e0429040203190c020307050f07 72
    0x62900004100c1c104c0c03084146410303203006031100b0340800d50342c680040c0207500100082d2140f511480e0b0340c5602c44044071041d0020042c90345136050b03242c14402c8290844068001f04030920407503400909087c0c40080a5940c420019100900b40604c1400c1050344042c04a100400a500c0e040722002e0305500350780304078145a403c0c0c480010500104007132650303560040d5602e940c400401d103035400321582c40358002c2c8000e0b140100050300740b6540e9a104d07070640d00c07240c224007000340c2c01141410001030100c4096600040440340603c8031211100814000c01c51406162500003000500000e1490f90005a4000600340c11501c1c0462929080061a05170445801c441ca4040e1040d4000c034540304e0300032401a03e40240144c00141d01c1c1004120080800c1131610302804980c526a000d42d650702c2c40740d040f07612004500d0a60b814400e106180b4849881104148194030610522074940341014440c9001f006401000034078041c0d441050b0300c0c600030303000002c1031803041018990341030f40003103600c1040b507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 572748120 1250 572746870 572746883
    0x20306180c01030b06070605071b030f17040f150b0a081e15010905040c081b041b05040911040b030411010215090a030f03061703040f0506070506070507170703020604 73
    0x1407000011016501030b00c01ca19809002440580d0104006070b00036600007a040c20607480c10b201004501159080c02a000da004c508490192041141c01401c800040020780304401c020313141c26038070351040c0d000280317014040040da48003260952600368400351944400405402030035a5a07448181d69920302e0700480703041d680401a241038900c0000c0c046000d28140340060000d40e08202e001d00052200400030b941c0420700d0040090307907440510020b47c612035500e040303070887c01c51081484142e40c95014124000203001823940e0355103a2060503a0140c03107000c1804a80d02003241694002030040d030300609040000001030004006000d4064902c00800ba000d4504000401c640021813160490304010590040b080c6640001e103d0b03548400813007071a040010b2240e031941c094400d9140d00202d420002d5100050130310400014862280040404540843c03400402c1e6843e152107510181c48072042c00cc0c04109a400c01c00320078450580c00400e0440c440d00e0300e051b401d00a5803800181d9040d5800d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 572749370 1250 572748120 572748133
    0x60703031d1e0c180a09060b0915040606020f0703260a080f151806010c060c0906110307120813020612011e0605030615160507031704060f051602030618 67
    0x134102005494281c1c81e01ca81c00c1c5405941d80302c1000b02601d0b100b1000c541380c0c1c1c1c1d40e41540b40703203555500d5018010300303a8010745140c00d2000010700c0115480c03504041d00303660000c0812500305000051041c02d0b41c0e44078040780d10070740d806d40070000d80d0070018800b03244600021400b2045145d00c083da080c810404021300c20743c42e4039103000420700704010520482c1c00c005000b50714141501c03032502c11504150189031004004803151170b00c0044464551492000a58a510070492594061712140c04c0701c08010140d40b9202c865550200449140d12406043c030002c0340014081d850071f010b102c0d01c0750b50040c3c529507544a00314280c03641400240100314111038005588032031590903140355411b490315915840e107503886000811401c0100d43c41008450342041000c0560540c4128100000314030860007001ea642c2140f84c01c0c04503007242d48005144410901003041142d034001c201507080da40e1810310580c2c3c1d16200005100c01c030182031019405100342c0c4140031803100b560011254560204041c1c504 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 572750620 1250 572749370 572749393
    0x304030219020a060f0509180604060e100608060d050a0305121e06060906090a0f09050601050c0c2e020c040e01020c0604060e0a0b13020906090105060703031d1e 71
    0x2200208207101a4010500940030310010b400340c100c15025030f1035424020f082c849140e0000305960070310015250746403051402d0042c1810240030b0040a84440ea801c000139180280c0c4011502c20940703d00c070100300200010806a13203a0f4080900b900f44c0000565052101030704003e00140d020500e12080e07460303850000707002600450320b00345c80c5407180c544920b410f40f00c40081200c190060b11465600c0302080100801c0c55644a004030000c00c490325611091528041c1c1c448100e5000820650501c00108500c2605000200e02c40140c43e0b02240e03906803104042d11108041c2104000b9100b00c1c0310707000340196506400141d030494500f8104e900f402814411403005007070740514011803003940d01070070101d80068004c0e0006e20610a640c400c44074011005c0c2c881c0000e08400b40c0b1031204080e01c503c0c4540940c00c11032038942d40000262241482545001c0c08601507115100c00a0101950b480c080c22a0b9080d8107541d00082c2d0b000d20032603c00400c80e5941c014995041c01d44540c951040362003040c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 572751870 1250 572750620 572750653
    0x30b100f060801080a060b2101051006081306090501090204020d051501050408120f250c09110708090a1e050909060c0403030c06090203030a050304350706060b070803040302 76
    0x1d042c1d1340410050003007600f02d039440002a0240b00d40e11544142908029141c1e08009202100c00d6201c401c000f144604000c0e9180c0e00e008130f59004030007084428020055480026040c03500d240341c0c005000252003680d41080c40c0102903005000350b029000240303c654015150b0442ca01517440700f60100c002441520054810b44941d11807481190803240d40102000b8810000c2c00a0a40590110740380c0806418002d40320078034090b42d01800c1c0f0440e543c500c04d208064000c14003600505c141044111000c1e040c105031070288243c003e000280c00211403081e920348071140002448840ca541503e06002c0818a208100c02d015540c054000300d00020300c039440001d0078034002c100760358890340342c1800d6841c03c64200031461802d81c0c80b0f0f5240c000c11001601d08000a1071085c0055903043e417682400d20b0852001e520030701c2400c80c1041818115290681708808086e25416800c0107250b079804c045c03034500080d040a42c8844206480803c442c3c050000e42d000442c8035522035805e42e544c6000307082002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 572753120 1250 572751870 572751887
    0x7050f0114011a040506040608010f06090b09060f19030501060f0203040f030b1003080a030f060b0a020c040528020a02010b010f1704211101050112030e19030b100f06 73
    0x640c0003411800108012841e020141c0591120b0f0380300f16240684841c003003a52a071107035010394001210300f00100620b0f000384128a020f0500c0740380200c22903150948032805070050b07211180c072900d00040d94294500078102154184d11050345103000002d0307082c60190051009210303c0022903503074000690380c14404011503043d540d04641d000300e41d50071611071a00746200249481c58001c2480400320114802c00040e09002d4481e56011a601c1c284581c0402070314110361241d11250003d00c844001180c0119018036001801d81c1d0000b49a601c2039104080e440e070b064024034050f07a800e030340b140245807a500280580311858000b07000112590004441d020712241000e800200d04401c01d01207901c103c284103420034083c6d1102007602c4154401ca40c00010503220940100d140d8454500104100f03006887c01010711400840a446c26502d000c0c018070034030780b203080c0300305d0b035002c1f84000c440044041480070f150004610510343c54070100c8203607441c0301405203942c038807017014002a0480c400d0004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 572754370 1250 572753120 572753141
    0x21005160605040305130807050109060f02520803030601090303030513120f09090218150c0a03170a09150203060a05060a02072102060f0c01020f070807050f01 70
    0x562030021000e48600c1d00a11000e4401c608100d0100008003040160460301405011010040d02d04645090005040c028255020038244004454805059030300030a4000c040e00901e100c00e24905200e04030188190611781c01d6410010205111640c00c680d000748681c0a0f0720304141641c03056880b04044c651740c1c00102ca429002498408040c00041d00c01e811a603001100c144144024040941e00c1c1c2c00e0b001202d90b546400a0140c5054421296001c1d001400900002804606e000b00e00c0c4074000418034994529800703800220302c3c600300100014103c8515142c00002e9488406442c90002d00e028010070216070104401004902262107502c102005554840300c4110685015a00540650801040705138020081000020944c60b4400140f4600c070351076015094481c00c1401241c00c00003020281c080d004d05140000740162141307000c880740000c01003d03054440c103142d00c8541c0a84180600b0702d68900c03010400e01c08110054010309a098825420741c1c8841500b51001400c80e044d03080c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 572755620 1250 572754370 572754397
    0x150b0a02031314091f08060a020307180f060e12060c04170c0f150d0906270c09021b0106030c0e0703140408030a14091b010f0210020310150c021005 65
    0x10400403030307409180340501485ca4115051080e03544000b141040e0040703071920f500940001c10060010b5206040c03480da1030200482491070360400c541022070540b10701500302840a070b000041d1207a44c0790b4803100020300018044681500c0e2507081010300307410a1044132040320f42c1442c800d07500e41000c0b84c10482c100c1c016240e4401600c1d450100500840c03c0544858101c03030800201d00f8000083c010350141c01d002e03220100d4100300b02c04004a10070041c0c0d071270940c0d2111840072000001c542200002c03c4807003c1c10056200e884028540f10030200d02d54008602d0740c680403001007080200c80c00d15044440104141c0e005a030387d0130080d0182e9a4481c0340c0802644c50400180020319017801950700500e42c0c407070000b9001d541c0f10030b01829110980310b40306ea9501c07903504144d458a0355044410303180300a01e030002e01c00004820280d600c1ca41980358900254003c40001c0c40000d005e16545c00070307c036009010503081d03072271b0030302815070007540340f00ba0f014200d4851300701c584d64001e2044480d5070a803040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 572756870 1250 572755620 572755639
    0x7050309220216020123071202010b210601060906020c0d05030c01090c05100e18090c09131a010f18060902070503180306040213150b0a02031314 64
    0x408100360a20701d40c480d02011015031a074003a464001d440600041c0d40e92049820240401d0300024150101d0700b58142603000301d1440c00c800e11000385054a291071f9004a80c090307a61030380002030340901300d0b00c0c0c20030390042e40c0d210f01400c21020406404106100e803d0070b80e40c4a903214407048a00366941e01401000d81e026030315072012410441010b1103a0780c000c00540741403001d1a8a01800d491015030290b50b1a010f48409101c5440d0520604004a41c0740c02e24001200303400011904510040841d08040c40c444c80c0021040381c8144010f01600100401004580c58451840102001288801d90f1103103108048101d24180007458181a205903101b4507454510b8100b500314201d008504005c0d9141d00d403940060f1103031440c0080e1100c0c40c80f81c80076580300c8508041c0002001702d000d40e243e119600210520015844014008810b4141a035000c110704840c144c0d00c80009442d42c1c004207040400080386103070039601201030410913011000f1144c3e26075403040041400c841d81d2210941c13103010034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 572758120 1250 572756870 572756887
    0xb010804080913020d0917042702210a150609051311040306060501110105041505060d0212073602162013090c050f040b060d0e0d0203070503 62
    0x1074081c1040e0710b03005101c3d607201a08480d5030300c107a0300040d1118030000d0702d44d6070400c2080860007115138180d000501140c00c05141c4652241d098070341500110070810501c00b00f0554a156030112280102c8100c000028602c1d5800010a030043c210703a00190203280a611244260604c49144110b0f1240d03910202d00500708010080c2c03213042803481c116590741e54656040303881450000740000303500500d0001a090b01d01030025000c0420424100c1c4c26900d071204002c0041c100010030860b4011010000030a940c1e40ba000c43c42c0c120b44220060342c810032003c407100d0a010005040f40c16100c0b4041d000903500c000390482001c0c4645145015403646600008100e000341c20390140c240f05405019062440a460319034552115801d20308022031440c0b8141c2802c0c6003811644140e5001c104001005002600e442c0e820310240580180d900c189110311084289070380d2504450101c5000400785a030380e5009107044002022030000743c00613030150100501d521070003c01660542504035010b94944030b00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 572759370 1250 572758120 572758133
    0x90601140f04050904050703050111041503020703030b03031210211104140f01090c210c031d011406040207020a1716060f020c030715080a06170607120b010804 70
    0x1e2005900d180006001c0060350365660400240a03500400c09020442d066040c494251200414290b0b0040c00170401001205410300d01100c0800e0310703140044e1201050725080300074089d20660254103100210b41181405030000441b40500740b100e6030307200200d03541e101a000c064600a40070030303002d11080f070410109001c4180c620124500920014410101804811180c40c059640601c01c51625006000714a1103218451a2800908110201407095031030310440046211030304190a071510b000000e50ba000e5000403080b4044012807014542d940c01a65008103c1c1d421003800b01c0c199003001c25a2800d0500c00c44003583c0e000743c45802441e08018003200650b00a91010910f840360041c4000039008400c000c0b0050034240e034841c583c2c0e41c0000d00082c642102e88860a01c6500100401c00241125182c011700341a81c0b41000c401655034603540c540107107001d0340700d1100d03500c0a103801001e006012031505e2246480d81c54981004052102039011035040148540c00300328418007042c0030807031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 572760620 1250 572759370 572759377
    0x90d0e150708090402030108060f0106170604152607090c0c081c020703030e0105060109060f0e0102010608010908090109060302030f011211030a0b07110a0c140105120705031509060114 81
    0x2119090300e404100782c08641283d009a010788030755000303407051041894001072881cbc01061a0310f01103610205500340040140c0001d0020740c8203c1d41d480c9103090200030080c882000384070141680403010002060401c8501c00c1d000708940a0243c0c103404198500386200e0782280954640d140000000290b030342460540c851820421a1901c03920b0480ba46107490000f000c0c400e00c00d65004c030720080e1203401380c2e0070749001400c140e040c0038007103000b40314290f0312043c0c2d10103a0700c0c1752900a11400c40c0c40c005170300425142c0c020341c2e40ba501b030843c1c1200f4400b21200401000c2000e036140158565a1b14080302203020a4411542842098004010110085200c02032507030042c1207600e09500c400340080d291050206080360007000c04001c004100d50080c4036202440410005804110070542c3c0e076840481c0d060040d5400211060850003107644100c0945940c5541c1000b00002c6040c10340002d4207541044926505541e00502207501500b3326145603405400180c445012101d400382c2070b03550030340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 572761870 1250 572760620 572760623
    0x20106080f0d140c030414041b0804120e190e010e0408120402130e0a031b020306131106030901060504150b030f060f03160e0f2509030606060305090d0e1507 69
    0x102c10701403484ca000c814001000201a001c040c0b000d0b080005051105841504881640c1d114135074800e03012883e002116190f20a41c000c01030901c2610a44040d612805070708035944d08000108904520a9248012030055903802400e00b00305a9960700418611442124020400c04c014002d402e258403041490a420030301c0240b00c7d02d02900e2000041044a107600610b8007140e000c0b44180e818960040080d001c80594803030a641125801c0c1c010941da0600a40555842c424400800c0c0c244a5120b0b1a841c210000514044e502d060020295000e030a09001740c91050f03251000c0c00c1d590b404042c5560089a030119074881c1155664032041c01218002061540c11031610b0300c90060599090110a03140300d144012410040c2c10041b9a030f0f084000105240010101c0d1030034424586010302c1c40b0682611482c0c0072414a0b888104200c0f010042c83d80001e0a240c02e0100101e1880e07056001369200c0c00601c01112800416000129804450f070b0750700542003418400790500701e01c80c5100610070036 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 572763120 1250 572761870 572761907
    0x3080d1b050d060501020102031509101a07121b03110a05010e07180e06010b071407120b060108010303080a090f02030d02030a11070b0301141309030f020106080f0d 72
    0x41050021a00d44001210206002030700004942e001c440c0c2512921000c0c080a04c000c41c1149403810500c001e8140420741b0621916a0500140460030800780d48400340003070b101203851556000110703468079040640c04949903002c11a0703040005200c2d030030f95a1800d00f09401420a02e9aa88007629052940c402d614010302901d461340c004105e0902440034540040001010698600149074110010010b401800c05082407040c418124000a045040d40c90340c8907469034403145890600a090a003e40f03501e454050314400064490400b05801c00740b9006507a4003619075154401124558000d000c0200410310580100f0b010000b194801d03140c15200c0d000b0341c060013011741c000038079040184050070016400010350950380c44c0e03c070039140501e1090b031000b0012141003085c010030501050042000c00030f1002001c4e070f41ea5440c1c00500d0110f00f1104000c00842d500c3c1d0030010314542481e4245000b540c00c040d0002003102c400148800840300c0c900c060a0307000350703600041741e125a01820f10f1600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 572764370 1250 572763120 572763131
    0x1b07030f0e10020303091b0a0306151212080a15030b061504030b0105030d020708190c1805010503012f0903030f0307030209010f17070818070b0304021e060403080d 72
    0x16102d0700e800641c040b0707154008684074680303007501510b011030136400c403259590f0000fa006142d80705da40c854010780781c0c4075501041e02a03907880c43d40d02e03070511a80081c8045400c40e0350901030004148101803c040180d030f550200366106120b2001382c074403a161151040202d09070802c00301d5480c20413030f501720b02c0041c9412560000200c10001c3ca82050304252900e180c400d004018503d03040000d48400050742c002352180d43e15000416440d2000b40307031000300511446840300308000709080c208010300700700c0507400030941c0d1082c88400140001d0041c02c1c000d61070215401e034443d00000307400040750500101881a0440c8210101c91030300b044d40384540610060118030300c4010120080c5103d41029640142c0300c440c080d00041640646020341018052044c42e11001150740c114010780c400074505040c0c00da920b400415800181c0400d40304807590040010110b119a8403400540c0264001c56201c205d202c240010b10413100e643d41c500c154018000c0108100041400018281d0101043c070001003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 572765620 1250 572764370 572764397
    0x40816030e0d1a01140603010612020403081c06060e060a0e0d02091617070e0f1305070c230a241e0f0605010e040e12070602070b1b07030f 61
    0x140c50304400085400500b00ca043e52030040caa010050700510314200185603000c1c407000411000d01c010300504082101217811401c8030066501158021503226016590b291590500d04592840c2c555450515904080000520742d00c070340700000403c00014185c0d4a8070a1903401683d6410300031200a410218640c80000580c2e15203014a10501c0c8041520040c440d100800602c85400040c0b440000721040051250080c5e00018400c602c0409841c0e10300302151079000215020f60408030300000754108001c20503112750100e11005c4c000d21400103903044500e005040302c04e07500e041c3d5070402180d000809200105d42002010305280d1010b0200f40b00b80d100101c002015290041003e2030500c02c00d13884012086824801c0000903c44000108800303030404000030410915007160500c0341e61078403403501542c01c0c140401d14420071150300c02603842c42c9078504100a504003003c203452050969002500c0c480742c400303569415801c2c070501180303000c0c00c43d03800b5241c2282c840c2014007080320104640c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 572766870 1250 572765620 572765629
    0x50a03060302090a14010602030703021009140f010609060602030c0c220c1d1008163c02030c07090207080705100f061208070b070e031204090605040203040816030e 72
    0x600401184c000403c0c4403178649102245040180c2c4003030210351003001a0001700764086981070420800c8000401c002d039940c00e10340d0b001c2c0b072240c1408000d4003c041900458001c154000380483d0714544091140542e640410b90b12801154156101c07604404080c0c2c140e450400040c00c00024a001604100740100703070360404854181c4050000304000c030000c1071010036111288d4204c81000c50f0f02c600070210342c0780300a100c1440941030590036504440c007590181c0c001d0300c268441c0c4501001c403042103068400c5403120b035024130402290b00e4000302610300000c0d03c08802c6400206940c2c00918016141407400740003507002207010b40d01110b040c0000c0c40021004d2200020800d8070314000700c0c0120030010b04408a800c0c940c04403c0188907941c000f07002500d107000b0b88000581002c600f1046542c1c000e4280d900c82c41400c500c541c1401800041c07503982442102070420343d844a08200503407500c030410700c8100d11045d580076054060502c691404c1c603a81c1d4081c0d203000e81c403e14048070203844d0000032a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 572768120 1250 572766870 572766889
    0x10906232a18130e0a02100516030206010e0907060801140639071a0c010e15041b050105220506130e060402041202011d0303072d0503040501050a03060302 68
    0x2038002d222484200380b40c0c2d2410100c0368401c038081e000100020001e42606076552056000c1c000d001d07000e4aa0620740560050007510103900c0200d00103841c805403031070003d4030b030203003401445a4414840041103000d54001090011340e4225161900f06900303005101d1001400940d01f103510507001c108420713603078460002c40da001041480300e101011540d040e00390300642912500001c40c0d808010108003801e0215091204041c11106043d62030001107109405411109070f03000e42403082d0b05d84104c10034100780b82503200740d005070a10885401c21031072040d0414590300c2000c0c0041c00c00d0091814115131108845000894441060301c45a61030000c5082c1e50030420448500080b42c140410035101401c80c819440503003214110314103420100300f2a803002001c00c002c1c0c100400400c01103100469103d00d0180b01c41c000701100d0f02d809007071810b18541180c1c0c580042030040c4000c540a003110b04d0340c52004100b68001d0195040c1421f00f001121250030001d00181019203c0000101584401031071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 572769370 1250 572768120 572768137
    0x91305100209040f09020603060d0816140d0203031e07020a0510050105030709290a0305062503050402030706110114090d1b0c050d15020309010906232a 67
    0x25886441400803c800c56210f11040c1d44541d00b00100200141d8880741101d5001c2822500d0702c400c11040d06022540d4000d0030b1a1880c0e0036204844442030060400900580380701313910031142a10381081c8202d89034002510310081c603030b20441e400e9040099031044507a01c0b40343c40c4116030614400741c4615280a034070103808488a42c1c1c88005200e28141403200502a002e00c0034240980b60840c660345e403e88080e02e14458540034410f489881c25600c0ea642c0720000d6405c00115200d904102c00300d41121000c541d11030a40903070b00e0a881110034000c1c00740900c03442e002005000f0300c0d4075054068032030302c43d81c0384001cbc0b0741d540e2050303401039503403903c40c81070300810100004004444030340c0c1e00900004005035041e080200e644040314002219510600d0580d60260344407810125146458001282a551141819400403040000481c0c0540c0000b02503070040d50b0600007000044007007c01c000410400c008101c00c000c00040d11084002140700c503070b0390390541d00382e80301003900d04100c403e80107280d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 572770620 1250 572769370 572769403
    0x280f0902090a0c020706030e0c100c020d0b100909020d020d140a0b0105030709050c1e040905070509040f0204121e1407031a010b0405010c1a1f17060402091305 70
    0x22202d203c039a041041c0c0c4044e044c2401c08001404484000c1035895101c14a1588142200f4000c103140d1071041044028550780039212240442045c6000300720460221410718060440a800240040080c06801000c94002e818542803c4042e02840403c0700194019188030400010170304103000c1c2000031300d01650240e00c0002c103550504080600340b00c03540e8410b50b4401d086c0800d210026405004030707400d500344040c1082d0b01e100029002e4840c0d00443e4065843c0f985400104100c0c80d030410020a004182141d040044420301ca83d128124040c501603003450802d19400000018035007503040e212070340f4003424000f020303600356601481041b000fa10440030340c00080c01082081250000c0c1c107a4000c942850401a6040c44043d400b20701131441080d0410031713500703404010300903004656060001c824900c0c00f50ba00e03284600080d155200104a0030b041200d900c00a040004505021401c6a0407000341080c1d85568003000780151000d000f0000805219500c000055020080041d41414048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 572771870 1250 572770620 572770631
    0x1403070302100605091306090c0e010510020601060905041503050a080a02100506030d0c110406060315080c0f12100203070c140c1012090602040305030301050306280f0902090a 77
    0x940242000740c08980111000e003015401e00c242c0c0d40314040d1030750000300c21042015402c11807c1000107003920390005001c8144441c1c001c120102c02c160418160380c07064550f524025950f400490f6500da00748a0500010481c21046c013043c58560400100001c10451050714a500d1761202c078200060383d01c04852500002450540823501441461240381d280081040f171898072402098444000340c520f41c041258019400c020071000724440440100050000c2161f030303481f4a0040c0c01048a02281c154807801e038200001d0030030000480380c0100002502654020080d0014418405401000640d45000d056011010492070384061841307006943c1e1101004503c03401d1a105c0048600c0401d0703019007088040c070701c403034440d803920320b9030907070b05140c40c01c1210001c2000d00300824500724000d109900008000040c01400000b450584404405a58503a1500c40040007100780005400b1001c2c0400a4040007211440c1d00c040315180802c6c0010854410301d6000030b0640d14200c0c0d4079004542c3d44d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 572773120 1250 572771870 572771873
    0x5070206130f0f0b030415180332180604030213060920070f020111152202031c020307020d14070501030b031015090e0d02010c0903120f0c140307 64
    0x3000000b0050200c14802c5401c01d0500126a0f8280b000910103014107061210b042c251421365402003085601d030028005843c00c3c1071030f00410104900f4140c0c4410301d02800203d408540340e91041990b003042d0300c94280b07480c05442c807803100d040380900019407086c024000080542c076400140a0030142c40c0398001885420851408100c0e061150024824990068144241d5400744222403c035a040703c101100b24400f0710040754603001100707042e1030034041c0b039104007051400003088901540340324070441307a401c620203140e503c1c408207490069459400444070401f20601303601c400c0c10030380540c8166460131003a5000310303200c04c20800741115503e0890b103030544101c0050044101902d030901e0144021104c040c0000e60300d501d189501c1c14101e980d4003443c8040703143e806c0c0890042290480030712140c041e8240351350300e4510b0710f0980d1000d542404600c070304051049080c0829254000c0c103803190002d03daa02152038412580c581f00c02d026403c040302d80450003040300f0320b1562001900440c1c0d11805ca = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 572774370 1250 572773120 572773139
    0x14040608151e0609070305060f04021b0601120305311511060106050d18060e0c0a08070e010918052506030b0303121e130210020f0c100507020613 64
    0x240c01d0001d01401809016581d134034038080725000205c0e4074022589896110024101851b118807240d80a4400201101d480c0000405908014150425500140e0340c58000c0c00c60324440400003400031300c0c02c115100d41c6100707034017190f0206810002274401403030614640011062098210302415120792242e80305040d48030001d0021000c641014201d0ba502d4400044c00e01d00813002511103240d1110502c01c0c800d82410a0581d205030403d07070a01c64640c640e100c840d210007224106074001c0c148440007060b24503001555500315a002003040f40a80e10b0300412900400c002014054000c220040c400c0118130100103400c5040030300b803510100100204100c4100c066107600460916052540d03015113036401100741d031200800c6040c031807a140d4880000c3d00b9045003040450000c4095881440b401c2e40c0098000310101d8800d40d15490028800003007680d0320545d4070140c80055000e8903400046041026504501c000d8508295040000507030000340720360000448851020613500041145800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 572775620 1250 572774370 572774401
    0x3040c08150a05011509090b011b110f0d0305070b061c030810051504050d02010926010b010305150f060f0408030c060106050a08010902031f14011d03071404060815 72
    0x5d000134141628090044043c1201020f0712a0b21344035a03503026038800d564018402c0300000c4180540ca410008480d10b4100c810b020018501da025900d0108140060b060059500050580585819050024950720348c0ca10107002040f55030000720701c030b46e880710080503090000c001c0f9129441f00710f001d00d441a4900d9801400d0b5010b544079444050f28248020703000300480c0d065400035100320008000500043c0d0b103034515580003003100840420404c00c401d00c0f40407002440074290000344101010140114190740702a51042607408004400400328a4520743c8854481405850541480d40705548422542c110750701c040e8460b000080c503944224401d000040c0500710302d040c10b50603e0f20f040e2009000c0e44050054000745640040400c0e42080c0d1500d640740100f4034003c154480a840d680038582006040030318502140840158003840c00720b48090300c8041c08041c2c020f0100b00d20740724056203d4a1000b0109812658405001ca0442818003a458404540d000350503039508190000d032000b0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 572776870 1250 572775620 572775629
    0x30c0c0c2709011503060e0c03190302010b101b060b060c030a02150903030c1b070f031a01080316020d050a03020703052506080a020c06011401030b04051b03040c08150a0501 76
    0x1d14000191003050b00349041380050381d8003c0b40004590520407146880c0882903010035038503200d10401f914600000300984070403d071195000303204502e003000138030500400c00f04040e004942e000da42c0b00c0e140c1076082400600b5501820f804201482c4120120b030203944101201056508009100045140c04128071118203100300303c04148c2d0714100d5901a100c2c00003030200090350800040740082c04100082e807200707041503030041d50201a5a414440c060740401c0c03004641160300307083c5020b10709a500f2140750481c4c0081e4041c615029040d014542c02c8480000100e80c0002100d10000220b04200164030007035109400802425046080041ca8015528003080307120300c1c0c031000000b02c0846071080c0b608954030b5082c1519103031240030b0344a02134020401480c50900ca01300000030480d101d650142c264050a0f20100319108411050209a8800311004000c0c031030f0960710707240481c03070f00e00046502c24007510740320701d24a4840704001c0c101161485003070501d010281c01e0044000f2144141c03030041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 572778120 1250 572776870 572776873
    0x319050c070609120803130503041d0f061809030d050f1e04110d030c05060a0b0118050a0b0304020103020c060f04050c090919030519110c04020708030c0c0c2709 71
    0x41c80d0070700e500c84c0d450038403500820041011002c59002003c0d49562078445a02c4410b40f0303201d60321200c040718036050300c0411030f4a200c28400480d0341110501200390068801401c00c0c0b1030301d440c451a08a0282001c0c29103e1071f407000300a4489003012601c43d0601883c00b10000c041075041c00e00d034070900d8100304130881c02d820941e02c09100000703c0c0081a10680541655032840d0120182801d4512180205002e81240a01e40170080b0541c035680c05402c1f0444243c071501c152400304c2211510820490023101e0f01714014840500030030070142c001d564000e00c14900540380c46007450401d07091000680b0902000c07003100d0305001c2005400e0004c4120304000b541e40362101d151025a141d640c1c1c006144031a4080700c060011002d05104008465060000201c5d00304800c401040c002d200c44400e41050b13806010300d0140344580c0ca0240211a42c0315042400c0c030f0b0464441079103407001c952040f440d00a1a210f08804c8452648030501c8021941c5402d07400c058900c481145a44210b800040052899 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 572779370 1250 572778120 572778137
    0x1050105010801050a0909081911010501171e010b030a03090923040308070c050106080c03060a060e060913020301061412070602030a03180b090c0a0b090a030303020a020319050c0706 80
    0x1350b850b0800018200d074900c010110b06210b16040a1440c1e02c2384400c007a000c2840714200c0c1c2c911075040651021003200035002005183e80c0c44954442d041c401707000d00307041c0d44c0000803420b0b0b500c0001c202d400702c0f4512000001980c002c0d0800002e01c0c0406000c0e0440119021100800c000c450510030241c1001103120703480c1242c0b44662140544500080c4005e007444041c0e0041211305209141041845920800800100d0b81340c0c0403440e5035502c54258984244901000903801800900031304040f202c01014104081e104d00c01008089000100003102c044905441e401c0965400d0080b50010501c01d41c02c2e0305541080c409100540c2c4038004000900d9000700400c00c403031980001103440c0e0380081d1900042d500d968010401c0c00091034480540302030000c90074403010300390104140d4580d580850300910407580d40c040c200d4560060510056000705c9019040010a00035002028240042e20681e4903040b54550346016560000c0c1880001a4000c03400150340c05080040c1405041182041e180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 572780620 1250 572779370 572779379
    0x12170304150c020a06140a0b010e06031605070812010f08011b0f09120c0e180606150c030a0c0c05041e0207110604090c020d2105071101021b01050105010801 69
    0x40c0d4840e2514407040c080e500c04961480d0751081c0180055654424030501280c0c2c0c001ca0020000c130f0040e07401111031450000c0c7d8290329030040001c2d8110000107000d2a05541ea01c803058104000c00103184024407508109150000e5100070087c40c0480322401034810701e504200302640121116041146036a01d483c54030300401c0d291440c02051103880c0c0c9001d1105090a0380c00303c13114038460341b021081c0b910ba400d4000410945100701010307180c0c01ea00499140c1d0b40d1605200422148458402007074014001181d102d0409964100024031640903c07840d0461000b0394520310303446940100002658120150200407203400400001d01e000ca4080c8a00c512000d0440340314070340e047c07040f8041c5600117816008c10400000c40008180018041c64503950796800c00c10107000c40d114000f006000300c02001c10349602451070050303003400c08280320800c1c0405a00ca40b00400029041109001c0007002c9520720f80c009000804038040d032a580f80c0c6402104103c4113080d82c0b010f070096818003550f03900500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 572781870 1250 572780620 572780633
    0x3251707080d0507050f0c0307020f0103230a1104120c0b0c120304020d080301080d030e151f0302041b03060801110306060d061a1c050412030c020c030712170304 71
    0x10040c280b22240003d02e5101c2c12020758a40c460100c0c2c82c2c814003808200324045940200240824034003c0e1003c04d418811140110201c80881003004000260940460703038540d460903105612500000c0d0016000b00360f044443c045801071390001c0540c00e80c0f600c07404c040110b41485040144103445000303051405810313600f0b40301d00440399041038504010001a0035036950000c01c4580580007071442da669612400c0c04d580342e40c91503a4000c04603080841c6010083c10004180c50b035110780d03560b800243c0e2640400000100d185405d00c0082c00445900440981e503503215208000c40500048041c1c415810805003e891b810b9000705542d0b49040200c103414620281100e82c410300440b0000c2d40c4813690b4005000500e1b043c0c02940c08001244d03109c80c0509041c1001780701110040d40c441c4044100c03d9410001c1d81c004640042803094940302030462503029820031414410700e40140c036401f00811000c02d01d01b258590040c40030310460b0071284280440c8013120368200c41c2c090342041c5145025103441c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 572783120 1250 572781870 572781877
    0xc180c1b02030601090c1403071106071b0f02040b1509010f0903051207030c050609070302010306050d0213110405040f0c030501060f171008060a06050909030a080f0402030325170708 80
    0x181140f58841c840c449002d07100b0030250200c805032521094a078102081c00034081d2844000c0207002e0f21400d0702280446010780e40100c40f4000c00d078480390031900cdc07507528042440280f1070201d81003611066180314503600e01d40f0f40300701440030500e69511040084e0006101d010555407442c240106400284080790004c03030200c0000000d240010390714644c926080b42d220020940c06400c5000f102c1c1484116400441c0d0542103034006d903400d118a5464100b049002c014101d0000c2d4401d044000040c00601c164001841c40d9000802042c103081d80e410200f02965000340304850015568810181e0540e054030a86014040928100204402c806000780a800c0c001138020105038901c030004110403802c8241c03c0161080070240c901504000d820300c4090402409084e108140ca100011003012002084d40d1001c0103550f41c0c002140c40d0b00c8502c50b1100e0018005a80500081100189102804041000e0480d01c0618002c5c4c80c48142849001041c100c8004858104200451400309107a001a0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 572784370 1250 572783120 572783129
    0xf12011b0c11060c03070b0906070905041406010f030f0e0102044403071a0a051f1703041e140301090f030e280f050303090109030f0c180c1b02030601 66
    0x1016130300c024542d8078034598011150020321001200040016240010480900412041c0c580d90021600e40c8100820783d41a040c00a0820103104009081e03507200d0b514421244043c0d00300048c03080300d6188a5800c1d01c940d1230720190260b4000604000400400e00c280025080490248030200d401040398405201d2103285012803002c05000c01042000520898594503030040c00c041c008100311030132681400c4120303103202800746007500049650250080b0081d0400751840047c1d4000e01340210844011311204540b40d0300d00c82400007284207654003600360311007103401092400e400e10741406880008002c0c000e46010781d04000d500300010313440d10301401c00c40343d043c104140300c5031148000c20441c050000d13002c2a0f0214000808500a03e04000300064139800000a040329031a9410705a0301d1180d044064009003d0306c00400210303014804074204940b2460441c8081569045402c00300d0012084610034685d41d080880c6090350024510300c008c1e206005e03803210b621529000a6102c1005204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 572785620 1250 572784370 572784379
    0x90109080f0d021201030c0302030c01020a020901181506030501170f030a080619030303051006080f010e07090e090304090501062606030705040e060708130b04060b0f12011b0c11 78
    0xa80720b48080030740e015642e207501080ca2038030707207580d41c4c0c181840d400886210a074020b0044070450805540301150700d4100640240160401c0d92802140b10450718180041c247e00e90f0b82c420300c202c401e40b01103c0f540c00420345903902085550500358a8000c92422108084c00343e8800c0300c0103100f8480110944c0c080e000181080560b59880d00c000c9600e400942c0c00461401c42000800700800da0035512a6005045141c00c0f609025210b48050302d04110580d0300d414100c413a44010003130000301414040e030102d030901d0180c10313059841c0420010a80c00742c40c5820142c101240500000c4990301c54180104540c0c03412001d06140e1219a801c030300d0341d4007403641300d2140b5180020031a8508020070002004007500411100d85809035107501d45c1020340344040010300d02c901180d4001d504201684480b9006101c43c11242c90307a6840400401000d2585600b100140090b240a617403845102d0280c101013000108034894006600380705000000008400d00045444640c042100c4140d21b0006c00801d55 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 572786870 1250 572785620 572785627
    0x10e04271101050c120a030e06090d03051b03040b070302120f0a111c0b010207120b04060c08010302090c0702040b0603040503030702060c210402030304030f080711010807080609060135090109080f 86
    0x80701100030f050000008d03a440d218001c103100f0b01200000c0c426006181d40d80d410006601d90740c400c0d1109041c24041918103800510100e80850b00c407200d4182c01a065060051410740031508034900000d04407050003130b12013500c3c1002203d0105000d030f01c2d807028410600502e40500c0010910000808840040310203503034013410b001c00d900812511000d0301039480042e21803142c625207040e00740c0b4211402c880403414100c1c1c0004542c0603009043c10380394014121941592041d4094400750071980e400c0e40d03c25100c8201003550303102d050084d07020300d0240010b90394a140000e4003a01c0c00704058001104030404002282540140e69601400c4032402006480d2540303071800020b10314040d030782010380b450314008280d0040250b071100614001380b0410090080c108102d0066a40d90000c13182100418080000034030280303040c0d5032650b4400d03014140f0714a0602c03501b40811480b001000442c042016001400360b1011641242540c0450402d00070f00040400340d48401050049044100c0c0d00003021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 572788120 1250 572786870 572786887
    0xc050a1707030905030d02040315020a09060813060219110f120a0306050303220602030306090109090f0b1603060806042001050c010c0e0405150a05010e04271101050c12 74
    0x3c0c0c00c040c040c903801c8012240c5581c50f50308204025070241c44115840d03402c0303444550350b904480c02503c600c0080c517214100b07403500e40302040e5440c1c24014404039007a5100300c0480000742041c805029140e00300c000382c004030780c0c0c1d0100141c410034142026090315484030b2208118103100241d680e41e010102d0a00307a4880302c601c0d00a402402e5103410007581800003145086002070000d040901140050030000d5840b9079034003080e40c692005440d1250070001100c01441018880d0b004424031074420340c1446d0400c096a11410b400810039150396003854031411b03490090716418000c1001419900002e480b081c140340c2c2c0c5040315a1005210002e010b1b09018604440e07a00030410389600c84d080a0091240d03a001500c000c0c480d140c04043c40f4402c41c5010040381c904c688800301e007040c092014201d945114201801505d0321140307401c42e02c0d0b01c41e480b00082c5203019414800158a01e0342d4100a13070607215180741486000202000b00c0341008030501c42d159280100083c91110303c80c6c000c1400755141c813203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 572789370 1250 572788120 572788127
    0x80c0c0c01110307140a02041d0604021905091302100f0e091b0a0c2102031206060417010905010c0c02090a0908040308030106081b0c250305010518010c050a1707 71
    0x9044c400303050160340c4000c04d0781020000c603484418501c03c5804000d2518182e8501c9a4050002041c800e103500020020740141865882e01310305068030329411070920390302c00000d5405882181c0051200030340170404070441c10441541517030b164050408840d1500e00e403900402e401c1d61101024418030704500031030084844e41500c080800c40909190f170303a030402c03203001030710601e0140821102074221500c21248403031400e1014071042e40d40da024501c0c0c003500d0400e8005000c4098041c036480300c0302708030000e5507503824003030601036000e400000b00752082d5505285007180d8020044500380845008044010b1781c0d07a08a0300d601040d0b50400243c00ca01c1814805028001d5400043c11201c00000204600d80c202c3d030f82c14840d6103611038060480c903075040e100c50240100110584994820040103a04e460340602061010320400368058015680c0d071240b5003035907029034030007071300c0450700340f0100b02e0003800e024410081c00c0714140540303443c42c4950020b18400291540c120003048820200315040c0c132 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 572790620 1250 572789370 572789377
    0x1207020904110319140106050918010e06090d020c0411031b07020d111c0302070b0d0b0d14071410030c0c050f0c01090504110910020316060c080c0c0c011103 69
    0x4040e003182c1034240d80444c0c001c44019240c5003070340d0070024000c03011103401c4140500b0701034800103044c00e041170701c80c404a160070700c0c0302c500228250354035841944604601041190300c60008503004010f80100003801a040401a400e0140500d041c1010040d901c0c2a003c100c2e03410116948424254198943c084081801104002544050041c02800070b000c90441d00360421502220441900c966035480c848181c000b03000d0080140c1c206460401124102101418030302103284404035846211000080c00032401c403034200c401507489221103000d02c2040003e40b0141203d02c40895000300014005114280c103031560710205038503280000f0070b551003403000721062a440400c4480c030707002c0610303e240c850441450150024040300d80c001450715007130142411503030b412a10980b52103448804c0c004032a512008550070342c401006031041c0c1c50303041d10001e680d61f07028003000117001012007c000c0101c003018045d0407142c4000d00c2085000c00000c0303003a03407204409007000501d007503c0c241180c0c110b01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 572791870 1250 572790620 572790653
    0xc050708011109040507210b0f030709020c010b032e0227030c010f1b0c0302090f060103110a1209030905060a0c0b060117011401031e0903020f1207020904 68
    0x142000b400030024003140d009070015420840d824081507680800841e02c445541d5010280707050281118496600035600040d94000c0c09070002d50340e68841c0300801d01e00a41740e8000522035900103810541c0850a00c00c1e0313a1248422030280c00700306603115840030401983c0c0890001140207002c2c41000082c01d504a47d81860120450301c25050441d013401c02440b81c2191241c024050012a40060340c410b01010401c100c0c0c64580401000ca80054501201140c150403542c1c02d010180c003201507650480b0441c402d050030918503040d4501180010180ca14882166182450502070b104402c1d812410140e0300410300d040014048403141400c440f105110f52015811110004040c001594040c843c808054018039105c161030700c440300111083d10140c411410417210500040c0300041300d92031241c0700b0010524000c50303510202d0600101b560b40b9824811030365962a80243c04140d01800a4950311014402500301401ea15070720107401d100e4407100a10070081000054108600d40d6401512003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 572793120 1250 572791870 572791873
    0xd200c09041401021e0c010501060503010f030b18060408070501240b03060f0604060228020d02060a050c06100314060f07050702010201021201060810090204210302013e030609070c050708 82
    0xf95560200b100346e40540e807203c5441d401c140002c0317452406181200e0494003031031a00980a031858540c0c0752803610140100e034102c05e98009290642c042003028501a6004040700c0e5500c103801d240c1b103802c44100100d100740110319001c0d07041040d0102c1d59040215140244c45030368035031315207000441c2c8a128000d02075004401040c04180c60380c3c001081d0340030b0700704c80c0446900d004070240350482c0000c010100941c0300081140110050500501030005000581005800c113445502598184101202d08141c2c98440c0c1c5402c0040c044a400c0e0701800440c240041c0c038150504104c0d010505100404c0f580500400003459000c69200754111480118603150108440d61254001049036400b61000e4800307400c0c40c0c4000c2100740b0144211021640101040c0990a18074104550800348000c000e509556844e81e200c80500071041021070001e03800c1a034640b48070402c09000d04001a02d0803281003812007442044110344406101642001503810600b2030480705142c0180f4019181e000703591103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 572794370 1250 572793120 572793157
    0x90212070c1a06030a1406070e060301050d1704121a07030e0709110c06010312081605091e060327010209030a08070c1505210906070806030f0d200c0904140102 70
    0x1b030201c0850042e0007030b01640d881050602e060020800140070030301038181c3c8000700729848400200b060245560f10b110400e940343c140380c0d55030724404c240d1410341401d8401c00389a0b100c0307405000c001d0300803c2c1d01043c50f04041240f071a82401955450906004496100d0703607891440880c8480003080e2140d00c101d0100700c0d4550340e12490300c4800410800080b10119040030f01062500c00380c415103440b280601d50301c0504008860040007030840c031507607520036802010b400300e18a54442c030000b1841100109100020320003030700841d490800c51203208205d035910612030110360750340100300b107007040390800c0041741c42d00801c0c14a0501000b040e444546111a0159102c00194122000d02001400d0a24003205d0002c01189503020390800c5461150030b0b0810800030b04054020183c507504410302500f11101058440703d40c5190082400f01b660105000d00d1485154a80390036520003101740101c0a0111036080c82c0c00b282410102520040c00340701c040d211001900f0096042d81c80c00820418038044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 572795620 1250 572794370 572794403
    0x2411010e070503010c0f08070813080a0c11040e101d032703070308030105060c0f010c0c0c0801020702150d02070c0f0501030f060806011707050406090212070c1a06030a 74
    0x40e6040c003840b4041c0603500b08810411440e010342e150380d4521403da125903c4035550104101d40c04032008207080400c010300e075004404a0421405400e241c0d440f501c074441e04003003d040880c2d26080e0203104038886c0742003628903020f1500200e480350310025003510114202d03502c29140304030440040700030070ac94400030075610841d0300c0c61150100311030946000d568440c02c81406050300c4450500018000c06d504100402c900e0a0180c002d000c0b80d10304c03906458080b02c001c80101d0a44480c0340035840002c16042080050011003e5003070b00614200700210b00d003030355560204003e00c0308507500082c14400404c004150080d950116405650301016108401d42c031a01e6008075032403c0d018281c002440c00c10301d416404451f100304003d80320054000c2c1810fa203000030700c80580d5014007180c11903010b0650000b4440d00c40f40a84030240c084040c0141c0c0301c0e1100308030030348442001040c40d400c202c0100442c401181c410320035928158890030007a407580d44c410021034034000004100510103d8880030511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 572796870 1250 572795620 572795623
    0xd030c060f02091203130509090c19060e0613030201031e0509030d0b01230904060b031302270411180403270e1807080f0c0414012411010e 61
    0xe072210110b4919014071002c101300c503030f00e0003154903144010030894000d00c813501d005020117500c0168901120581c0f0254804506000c03d6801c4803040182c1c20b4106200045d00154040aa91000d448042c2882c410144440000169202c040c7c107042c0d4540340c10018420b08030003140c0d00110080c050206052003001d480c0d90307601203900120381c2803402e1040d0035607621400c400c2c492040e0a2040721049505040d040010b90300004030341d54810740d42c01001a039103220b48051032290400040e002c0010f25103006108140701c1b01150603c01d2011800101404840820782e02d03042600124448182d0b100100414a1104400701c00c8040c862050104801c042d0b00061840b040d05481c043d50b580c0920030012980b0425a80c040c40a44641620003c0c04662440100300c20b0031724407c00300c7d00c0c0d8959403103100e030400c1e24008480b40369030058001124141850301800c1d02190f02d540090702c140d850b00d074810b2503070303030406860107442d01c034203543d10000e14812081842c4850040000704000b912124100303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 572798120 1250 572796870 572796877
    0xc02180f0105010306030f0201030e1e0a02150304051504030315080c01090503010510030308090c100809150c0412051c0c020f0a0501020309090703060b0a03020d0b19050d030c060f02 80
    0x24004034401000807406510034041e984c2142d038800d40d150420001c036801035020b444504070043e158031a1141c4007402d180c0200900b018010b41102400000101d030050085294941d41da040044100300107210004000040d00c413328102d00d00802070319100c0d03181c218040c242440042c6050b100c001c00c003040781480410b11420320308013600c2c1c016006544400b4903080c1c03201102e2140c0048200c41c0d040011134003d00c02c9a074040c1c010005c0d64401180b410024121824124000000501c2d1030100044e4070420081610501200d03075000c58249420500e40301c06104034028001410a00403001c01041020401c0c0c00d040c11507a1031542141419860003001034030301d060142e00c1400584514004c41c01e020740900e003900c0041e4051441d00c0c003070005101c41d0000107411401003541c0c880c0c00055141e007900281113004d46541d8007580c1c800c215a90300c3e0603560b00b51821880703011a00400040e801010340380000300c490070f0319840040c0e0280d003420b40309004405c0380980368500b45126004100b8069005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 572799370 1250 572798120 572798131
    0x3070c090b01030e06131103070605030601181a0a021e0c0a05090603060f0c1606091a0603060a0e0c0303160501060b040b030f190906090308010605280c0218 69
    0x3002190740600044040c0c078582d203181034450300044c000c5603908020b4603d013081c040c00340114030300040541c0d010900e0500694041800aa40802404429a4816554032902030b503035040d0341190b41071000b180c01c0c0750030740d8584c000144000251418141c2c001d0100e43d505000306c8108042c60701090317160907140d04035040c10511841550001142c10300d4122142409500c01600030b0000c0d5851080007400135002401070100f030305041c00480740d00c944d800d076804040e074031170900407482880602d4003801081442101c00403142d840c004000c0c0a4038001100d541c424446000070982d07803001c1a0450620000c0704c2041c0e014040000c1c01e094054003050740501e0301e072148000708802c650f505e01500d0140214042c00001d24000c10104c0c40c10311041c407a4680000d1305812500b000c0403a450302c8812901b8083c42110f00c0c0d525102902c09041e04070440c94014100303811f00901d01410a41c460b0001c0301010121500c0c441a8040b2001592062460f408a69405030000000950f4440000c0c54648100c90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 572800620 1250 572799370 572799389
    0x3071101050a0608120a02060a0b0103020c060a02040e010b16060504030e0406081e0303070c0813120f020f0901051c0611070521071124210609070e010c1403070c 71
    0x5d680c010300c3c1d06481107402403e0b080e80580389a0716102001d0003e09600d111160400d6005e1041090800e4203000281c054004420016902e524111035010750310f0050f40403440c65075003408a2801039101840489103264048070001e5259aa45815200115504070540d007051411001080744440000e600301000040e0100b500104800382456681b23110442c0c05000284c00c03e0001d8000400d608003900d410700e02030859840050701d8114000c625130318600d0a50300200388180710750a5050842ca43e0710783e40d1080c1c401c0303c01981020042448000303800c105501c2c0149806001060003d00d41c4203407003c18000f04004d56170390403418055a100800301e19145040700000c807102c0c0c40000c8000b02c035280c99200503912500c10100e0b04112554042036810380c4c080486407003004000420400400400007143c20240100045140400702181c0040006004503070100c1406107583e000880d4004540c0301346405000c8102901c5c100d0385444490800c02c0041c03001140354402c12450a0b03400090b50500303c2d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 572801870 1250 572800620 572800633
    0x20d06020f041805040c06121b08180d0504170a080f2a070504020a030f0501060210060e010e040b0c04030f05010b0f1f11120d020c1905070b03071101050a0608 70
    0x1a400402c4070b1054500a06c6400400341c10040203020f1030740070580c075264080c00610b80d8074103001616101c0c0d11140150010b402402000001c2c0300c10701940913a4000a00103003400f00103c180503210784954010b1090f900f590580c4529200020800d00d48025030190303506443d81703034902100350b0035008440343c0c3c1c1e02d4502d540d08440d9000d501c03000035070480c0c01c448014030b0f041d460003040c0802507110341101820036480e00c040c0d28203c2c2a5014680c002c01007507008040400320840043e044071040d40102003000030700d2004009040f0808000f40d04140c02c0b000450007500d640740610040c4c880c96100411071050504080700f840b00651141120500c1038030000c0e000e4401c0401c00c490007180b1b02c90484583c120380740c4402d801e031140c28001c560000c910100c07a181d0a9031455440c1030340100c060444001c0e0002900146400280021400c4010254034552510b0043d610a611a03d040c05481030900000c80001e804a101d020412101101a00208403070b00300080050040c02003130007013400078866107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 572803120 1250 572801870 572801909
    0x90209090d08041b170a020310020f1804020910031413021c060b0a0b03040510090c0b090604050d06020a1707170c1b0318010507031b020d06020f04 65
    0x41440000070300da9540710078166555668000600034140482c0740000041500480e018205a50603002c0000300c20041c03108007030321b104040c501101104c1c12a14240140a1420310b0512102940c2010203500c0c40300c100310b81c6d43d00c04280280600011a80c0c040e0403403010901d1660140e010300c0306529010203410301596000c111101c3e1510700500290441c1048603001001030340d01080c030400911a603c003165180e01c120020b010741d0b600703401c416001e4a00200b03100422404010480c040301084c034062040142c0d90b100c075000c03d800e51085143c0c51000050301035083d0b0365003003190082c010040010f00e0100c0c160506c4002904500c48585c00b003001e548501648010045070a1300c551115034600c02e0003007810b00d000f220000040d1400908000500c2440484c800c0c180e82c0e91600e03401e47c4000c0d03440fa0107103c044001c41404109050600c181086600302007035110150f542c400c4c00c0050380551344260752008c600d40c0e545040c000741c0f4607880483c034117100c035280000070022100072414090724003152 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 572804370 1250 572803120 572803123
    0x102030306061c0e0607050a021c0801030825080a170123010504170d09150215090c0a0f1a04120f0f0f0309030b130c090213170109020909 61
    0x180d40c0326502c2901400081c8800d00007952404040a21420124182e02240407140c50080c0988412010880c003043e403114891341007280843e04171030010b0040081e2480c0d64050496030301800041c201c000001075a42c401d206014500b50018001c1c0720340c144803c0c035401e2080041d0022521003002600d40000c4440c1c031100364070300905031460304580001c851440056540043c0070039807200d040c03020070300c40060b8468510242012032070310351000d0400038a41c080018170401f080d0704455119203c1c0c0c1d0304959010b600207220001180e5104070490b032501d400c10303d585031030101e180c0c066101003180d6011031040b081d92824400c9907400800e0250401400752216400d010754042c0e61203400c069280c02002ca206100052002800f4403400500004191a10103510701c6101c4240d000c2a002c01d010010401e400504d558407110401a05807003280c01c0d030790380704900e42904c40e043c0004d0300451014054150440c11000030310700c001c981c0140c103607003079000b41c040c28100300142e204142010000340800c60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 572805620 1250 572804370 572804377
    0x120807050f0c1005120601050c0c090c04050a0501051e0904093c0f0b040f0209131a04120f051303061508070810020a0509121506100c02090910020313060b010203 71
    0x505c4011403c030b42c1e64000045a8a0b0001a12007440d807203102a82c2181d5166504c0241c020091200c6450380c650030001404052002c580c0134504202d02046195100c1b100d0b01c052401211403415000e40d110070020014018005082010745003180d09031220302021040380150000482c45040e000d10103002081505080c6c020342c80240c0043c145900903000103040b4030500d5406442179010050415480e00459044001126031801768000c5c2c5454105001c120800d402e040c924008011088c0d1030590b51b5010742d40341b849140401d200c43c0030320a05a860007007081d01c040c182252003c5120f40e0b40c0b82003410203000c400503540800c8003120000b140e00c1c10b0100701d940648188200400741c40e1041056400254410302052041020500c00c0b54499590300094828117050b000080242001c1840e010010700c1020f4025840f48042c09800e509840d001500261400d030100e0b1581e0300c0c0c2d510255554142907018101442840c0300108110b44902d003103004d4400c1c14010082081809051801660ba911 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 572806870 1250 572805620 572805637
    0x110d0e010515030d36030c0305060906010f17010e030c010605150f031b091809010f1a01050703020a0807050a050601062307020f131a09040c120807050f0c1005 70
    0x28010910034076030750a48210041e200305c640182c082c0704000422061035020558204440480404d8000c0040c880c00300300441d0480104005000594175290741c19038076400c58458180c40c035821001910300b00c002940604010010203043d250f07982c010485e614001c20903400b070580300381c6903c900d002545865406880c48400039145076807440d21038000c20014000310405403485100100070544c12901c03400200110b400c80c031016184903040142c42d00b82910b0301940c883c2403103440c04081f4015400d407402c5240c5090400e09000d85e4039009803e0880c140713407041c100a862460300080c460308000c000242590b00c035024000707407011662900c10885000703c1941e5442d02c4e24107500440c1030115200300080c44842e2000306800180502280410b06d41d003540048201c24a03074580070301c43e0b00c0307803040f04001840d081290114218a880c3d41c5000c0e206002d4000c448100000380381c01d004104010084646154110003100d90644801000940d10701c4403811041c02080d007080e5054205000f80155181c06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 572808120 1250 572806870 572806877
    0xa0b0f0304020d050708030d0920100e01030f180c080328050d09050705040b03160b0a0302130311010e010801031a0c04090e0309031c080a110d0e010515030d 69
    0x103481c0d40d0204529100750440c140d4450007a02c10019804504100804050b40a007901049880150612040d01484030b140c01003408000110903010303566412000c542201e95040245c207004110004800030a0f140940e0001103160540380d001b009058110000301c28810541c4c100078a0310340701e10301c2e128060410201000010503501554088000340103802c81c0005107001810030b00c00400b12801d652010000340c0d142d401c40035080c003980c2418000c0c0c0c40d003c401680240842d07a02c3c1000060b44a0303261140001c0000701007509030117280310750115420050031a4132087c1660702d03402c290b440314084100080c0400c10f24104120f83e54000c40b00e40c5d048035046100f140c17051415012032100d4020040400700840302c1003201194100883c4103120f2043c009a0045440300412020716203003001c6540258005e900f485843c2034049e40c08001241c0c05020668003181c00081c07a140c0f41140e0203045a010512030514031400047e00c41503111303034464065a0486510742030340005042e00d400f21004643c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 572809370 1250 572808120 572808127
    0x6050909180a0b0c070b0f1b030901060f0b03070f14030402061b19110a03120f1b06050406051e060d08130609230604030f050316110a0b0f 61
    0x201c0c50840107040c4144200240c510140d4a50741d071002c441812181d4641036040070840340203200c0d03050411035004e441c2c401c000c00b05040001d410301d040080021141c0410f2800400a460f0110a4201400801e0340101c64228140c8a02802142c1c1e001152500c001800c82426241c0e030034450003101210b140256042c5141d502c4a400384040307980840d48a282400740c0c40b880380303c0980c08218038070340220b078003001c01040c03c52440c1146401c0620611a031180022002c2407002c20802814603142110314203040310240f01809c001c2d00c101086400806007040290b0900091003a0f45d08090f00c25031054074100125a1103c42c0c041c0710704540080030744103450b8a000207503d41461124800c0950080300c4850030f1210f40301c841e0f2001c03c0207811803000605100c4007007244d4458180182200704003245e40c49020440e981c08211039005901c006001d03418a8614a014000705000b11440b003014801010100c900c2410700724074010f1411203403070050321148070028031360340d55406460511210998080c039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 572810620 1250 572809370 572809381
    0x303080a0b1c240b0307061107060305060102160303081021060c03110f040816140d0206040e1005011b05151b0c0a03090e04151a2806050909 62
    0xb24814540c4100c845009a01020541c8009012021244010410040740f6079a06100b450304200c43c0303074054024000101c0d14480d124001050607015100b080c44c00050310b81c1c9080c0102e1528122240d9412480c2d84540040181a4408100780c440d48592003448080c0e076950908032240841d0600840346040900c0700080010100e8020399641041c0d4035001c07500d81e4481c00d0b00450f0b0b0b0b021502c400c420ba00e00143c10411100d061085541000840300d64540541c988051205001100011548941e00c176001c074404541c0c82000790b5002e070408195116413854246c01d42580800e0070700416011400000d0114004106001204030030b03039204010300501d8444210100034403201908009000c141c5041c150a0a00114040c00507840c40000602d03801116003005003088215400c107c600c01010010800405e511020540302c2043c81c810000c0c002640120b41010071401400007513101101c800706800601d610499100241401003040c1c500c1540da58040d01c1c14840d0046058001140000190 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 572811870 1250 572810620 572810659
    0xf0102030d0b03070b0c0a06050c032203050d09030818060709180209090708010e01120c0b07110312220510050c0f030d0504060c020a05030f09010918060303080a0b 72
    0x146803005000c651340d203903d82c210a045130f04410040100350b030245004200744900c5000e8650800c000c0c000061030341c1001414401a40503c24a00089264295041c010584150200c8210800410301044440000e00c3c000703013000703410b59110359240c080303004c1980ea00713401003600783c000d0046444280342c1c02c0c81d04614502600401d800c40c07618a0b420b01c5500c040762a03003c0001d2140b03019540d003050540c10042c2d01c102007a4107810520305a03440f14203510001c1c2c014040e190640d111900142c1e1030320f07440d10703142049440e10720405426014000000800005c00e0001d414034110b083d4106980447e4021f012140345c40c0ba200d4150f2142c0d58164103000d071801040109550345440043d10070310b5203800d50b0145164001003280c0e2026a6940801041c85903500c10780080b01d5051000d09604203081c1ca4039a564003401d5101d800f941c07000034500c5803076030043c1c24010045c412a051000000da0418001c00141660b00c801c2d00410705210006500c0d88181c0701c1c2220b82c1c9001845081c00c1c00b05203950700c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 572813120 1250 572811870 572811881
    0x1b0e041104090c050318010c0509091f0311030c01020105151002030c070e010501030f02130308160c0e1609060c061a0301050a0903022107060209011b0501060608060f0102030d 77
    0x2009409010070000c41c403441c2600800501c003085889943d500d0034206034400700302540760081107280c0d01d443d000f40f9180fa0300400300c40c942001240c50484a45941110081841840b42d002d054104081400820007003006110351170a10101c00350350781420744c03000680c245d0710120b500c2e502c201ca510b4100c4449d460000a5008209024811a03040c0244103600e28600700658101c82d45d80506800100002d69141c0544002c005400c082542480c042c200780d00300206442c0001000c08038007069040c180200300142202c1039402100c0003c20543c1d862140d290140251803400395045900390000401c1d000d600c6c0c003c1291810760fa0607180c4000c60311640c0080c403500440b507841c0c151080032030516a03800d01801d80255400f01000a913000189406490400302c90b076542c03007034003002d1131201070a840c0105a400f00e58000c540035a64424810040741c18605946290003003440d070a10a9050080541c09801691242e49807112591102d40c1000484801500218016841000720300000d0b14a900007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 572814370 1250 572813120 572813141
    0x227121207030e09071e1706044a0307030906030216120e1f0207050f0f1503010e0c091f090512010f0501091b0c0c0e0f0601031b0e04 59
    0x2501c100081c0001007121505950b417074001088039080301125031002c100f00390a0398050420342c51a402074518000100c000038052403045a03520422a1900c030324181c40c05172544500d41500510030004181c4103900c020140781013030a6414500c00218800000407a80410b4154480a0903039180034800c03400303580040841d8090000c00c04150000a164500c03480000d146629128840503154050041c3c802000d80003240240030390100203031080d004202213090351001d480c10104111008042000b40c0001001c8076004101c21049940301d04440010394140c2d400d01030700092030349a40d039105c045802108413255110007054400c0c181d0f0014880c1d40300c001101d604008440a80e903c000840c0c040b0b91b0107036958680d45030503404200c42c05070300c50940900009482000a2400701d017800742c0c1d44c1c142c3e041100c00e006250091a060007007800540000382107644103401c3c1442e100d11007944400080d1400c41c007090410409411341e0981c00c08030114941b10369181841003d084080001400e6150301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 572815620 1250 572814370 572814377
    0x303190e030a030e09070801230d0b0f0103170a080c03091c03020c07050405010b040611150411101704020402030604091b0305071d0a02031009022712120703 69
    0x94920a5440601c9501100b5019845204a02e00c850f070600c840d4900003000381c0108040c0900501203445200694103010541b034103940303c90082500401c18000c060500542a0b0843d070b03040012040e9281c1c40305058a02c1405140b00b0907506c41c065003160702071820024041585a0002402012020003031030b40700424208903400340f02c00d82c1d880540c1a9082002c0c500003900065598a503007420007910340182815603040000d5890018520124080c1c2d004450070403005000c2809e040317408000c44180d80d01c00074030441080c10603180c0034902724030b0750210b2401500c52182ca02c00140c05a00580500e280f06c9014034659070b129802c00001354402000d0582c06540c0340501c070f001c1505200501030300103001446001e268114141585062295488141e84040704000c16500780c0c1545401038002e4110a0301580f6525000d2817a070503110103800c15940d10b8800310340c3e042c0d5400d00c4090b903000e200c0a0a0201681c50010040c48002001003580028690000300010748049003000100101406441d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 572816870 1250 572815620 572815637
    0x3060306020a020a0212030901020a1209050306070c170909070f11030a05130b03060d030f0c0209130312050c04030212120c030703020c06160f020a0305120a02011802030319 76
    0x5940d40c04981000c421440103910240d2100d04506129040410000c4030200560900c0d0304000000c0d51002d00140090a4000c0c101122100d2401886130300043c220003000c0e94458641404018860704040c0c0007501ca41c0085c54407550040341400849095010140000d503982d43c2d40c800603180d0080c410001e804000f00c0e043e81100c3d015060004d881088030503a5041d40c3c0301c58090200c003070031540340c1140200003010024026503640b512082c0d0f034008c2d4075041204040354424001e40740344d442460060f4012200c0000c0003241c5a402c104070307508034030070f441d4040c24a00d601018000c8a01c116010341d12004108014409171a0a0640712048000c0c142212008401650300100507040391005841c0da91000c40d80d4410140c040c44046580d01c42941c600c0d042121100032b16921010280010346208112459041036444000030741c405140c00c032007242c00c4c40300c40c0b100041859010a04240042d448d05150303080c000d01403c020001c0700e030000c00550514005008150450007041800c8003800f0303042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 572818120 1250 572816870 572816873
    0x4061d060321090f030f0a170702030712020405070306030c05010c060b1507140a020906042a020f0c0f0306160c050d080a05070c0b040605272407020d050a030603 71
    0x51038007202036400e01040c0340c403005144103200101e52180c8a040c441d800404403d140701b8400a10300b0940d80c1c2000000b51440700410b8800550312561502940502940c03501103030840c09200b8411a80b48242c42c2008180e4501030110100e60342400010050b070000c02e41040b6540c0f01754252119140104000601c211007070b0300060100324900600c0c1c0da04c038400301d508800c1c88920300602c40c0b0f044031034004d00240521540012004207000348910301c240e42d10f110b03e180001882f11a029406004074007405a04440c0d040a50344031401d2210004911a140b904440c0d414200f00691002401800038499500c90215115074407400b108014100008000c1400c003040081020000154243e240d04500341444912082920070040080c41031019801d01080003844d03008503182c0c45500900c0010300340e111041d400d039905500700c0002c011110b0480c0009001003010405400081c2d4030b080c8011140080032440e062448110380c2c2d100987c2041c04030f031203810302510040c00c1040c4146000500142c0303d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 572819370 1250 572818120 572818153
    0x902031e0316110a08070e0a110403020603100533070212030301030c0806060f03151b07240b0307090b180108010b0f06040f050d0f050f0303041104061d0603 69
    0xb10007042c1c03803009802d41d540440d400c01d21600005860180050b11403241800e074514103502000d4400519103642e200e202000d0803001042c0c6003d59401044996241441007002d50040b00c2070240314401c1c16120700d0380705c0c0c0001d0b507204a240728a40b2604e1114900e05482c01d85c1c000d41002c102607800c82020401c486078040300303000031740c046d40c8151224240d003402d0200e01d0b80741440003032859001e50301441c9503180c140e0380010b5a40d22402207002c012a99a150003a100e0b028803004615141c1a0011800ca401c0228490a5a02d6030801c50f94040d4100941d91440c02641c004040e050f8042e00302d8107050000b030000790440c0d00b003840068180c800c1c40c1459800200042401d2348204001d9544400703c040f48d01c0c1076020052040c20071110103040a0424441d00b049810703502c2001d01c41c80075a1040010048150200143c0d40e41000680e007481c83c1140140e278030f980c42120101c40d0844445900c111074941445440b054400b200080116030010142a003001000a41002d5042c420114200c113003030344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 572820620 1250 572819370 572819407
    0x1b04060f082b09030828030e1212060603070507080d090210022d070504181209080607050c030d150f06080c030621030408150a0902031e03 61
    0xd42401840410b10b1084069400d46031804004600c0c000108000c03011a405482001034980141403a60f84d42c84001107002000120031800d10b0031844104500f120980590040410540d804c058640d0109002c000c0380b024810f040070381c000d000d2404080345450800502440c1d10403551700300985071142545603106603400602051012a4032059844214140186003240400503070006210003100100c110101b41000450054001c43c1c49401d4240840104100780040001074400c000c0300c0019064524680f843c05025107400048003047d0007020f1017a03030600110b5002c500580070030380b900f0404480310b5101c060080c0740d601c070600000c000c0d0406481035445034107a040c84d02044a10384030103070802441607032140341801410790412100a80c3c000c1203079030004085803505051302c810803415802c1580d030031032560140700c049404a010b00c00014a0000014030b948070040359a034403c80b02054071075a00000b50550441c61081c0f0040e00b0301000c420400e61580196428a0302da461300020891 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 572821870 1250 572820620 572820629
    0x8010f062a060b0a0b03450d08070203040f0302010315030213060305010e1902040e1507080f0112030c06270602040509090601030c0b0702010504090507081009050106021b04060f 78
    0x155102e00c401002d107045045500140030701d212803410340ca44600760841c00020500340c4403200c20761080745220480c07001e40c900119010080540107003e047c810301c03652418a82c039540003140000002c144014000010b86040318481d040c00000ea0b07055a00440240942506540700c5400040d80840147e48880c9000c090030032101c40001c0300c0d0310710f080250942d181c0044418040d00b189a4248815900d490302c15030031501540c0214142c462083d04518000c049030074075034034264003020320608582c48801e050141740c1d01042d4002030390b200c00c11072014402c0b520000340851804071002c000941642c00940810004407150992401c48859004403101445c10881e8141c0d40020248880c2c9030000d44181c000301c10100170145581181c0d106484417500740a041c0a0060100c0c28108580c89041114058400c6200510603801c1c084070180411303a043e6031780703035144082e150080784c10f030024440c0c1412141e01ea030061000b80844814030003900020390b0aa80c12a440348008101601d402103042c0080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 572823120 1250 572821870 572821883
    0x41b0f090e010b071b0f1403030409090f0b061f0f0e04060b070308010f0b0421080d0504121403010909060f1107140307120e030f06010f080d08010f062a 67
    0x1100b240c6401882605c50410a10001940120512585030400c0004080c1c0301c85a00d006003000c4440700107440c40c080c607440b540070a800c4c80070f60b80030003c1541c030381d900103403007492541807036101e0004000d2a0703920340c9215007007010003c40c10140725115040c0060a41038505148804010340710100e410b403843e42d008100c05003400219682095480003042e4010944508030001300750410030001d2151056100b2000d8080d400740c04011400328400c3c00c60019a40014000c2c0d581460b81d1060010740740488050b5485100c106648505038041d81c07900b11a0080d00343c540340f079a820300c1180002040003040a85ea242d54610345020031008a00ca01044510131040351a00e998044c50000b031000c07100351480441d6001800340400156041154500c0050039090000000358143e000c2460030945041e1800300740309160001038212424682d050a40eaa62016036909460054040d104990281704d50b098503c803002007003040c03510620b115510844185041c921204242e510b4940081c548402078818 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 572824370 1250 572823120 572823127
    0x1030305250c0b0307141903060602060f04140c0918071d0114060c010c090501120b0a0510050c152410030b030c0301090b1005041b0f090e010b 63
    0x1c10600c0c1d8154603022888a074002803007070180c1e502401e080c881d02c1565016240440412655030003280d03814000c0c100440f640d03440f01307a031440d00d0f1101c010862991001c01d02d4040042002c5101164141c402c98502c5130f16042600c030303943d0b0340f10462400780c2041140e001e030790318031070903561a280214080c1050314011028200780c51041401c02210b50f00c00d200408030040845c8070f0300c0011040134112100003140484510105001c66528410340042c034100f0f501e0f042c3d0b5890616044400b040c01e84800b81c3c1c6508000181c2040c14040302c1070051282e5202c907001204024602c1c0400410070118248c1c901607040148040da01c528000c05100e44650300d000c3c4c10b0400c022202c0540307800f0655444808490090303040a40800d5580e005104807004054030341d40300303940e240c408009140186001500030410292181000c0c290080166258000301141e803000280a2800b400745078040000e00001e1800100c000c202540d061403608122018041920f100141d00f54008540038024014918020354 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 572825620 1250 572824370 572824387
    0x1807020c040e07140603060916020a12020d090902180405040f0204021215010c0b0606220b070312060f0b0d0f06180e01111903110706060e0f07050a200601030305 71
    0x91130030a140d00107001e140203108005803a0b4940c0d2819070131140555410300c140b403540d041281800802040506403041006d501100e031540062080e10000c4950f80381a04142c0722f04250050b4400c03030781d4140c0c8202004661400318a0b0070740c02590001d1142030410240410340d404a0283c0c0c110841c064500002002040f080c2030745c51201c50075010b0700346822002ca02003962540c510308400303071016015180200300e0003060750100f8403068480094250b00c008490b44d41a80010315441200d00310001206403100140c00350300c900515069402189800c0c0a60382400750110140c0c0082c244c1c01c810707544503412628050446d00c102409070a1103003a25481c07100f032006072002d80b0064003140e4640c3e0301d03003c40c120941d80d20704180c41c4a141c407801d40503003035603900d0021400b1b00804001040c118900142c40740400103107601c508100c0700c00401c8000c040c2d655000b4009070b100c04440500104508114114601d8482d503811803600c00f100103030203900001e91030038524000f02600202c0200d58002503041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 572826870 1250 572825620 572825639
    0x105040c120201020307060c05070b100f0801150e2d0105040b010216060f020307060f0c020f121606020f0d0515030111091201061e1d0103021807020c040e07 69
    0x2030305a41c1d180305040380d0242e000075035038130070200d002d0300880d0784405040741a48500e0440d540b49420244880170360514000000b54456140720f481100708a42000045076441809500e84c0e103250044a603000034074100400e03611040050084240c54074040c8245c071102088094010354580c40c6210881560420f003d00048030390351030f5100c0c15948000690025600b000d00c1c020283c800c5450124404224860142d10b0f5001d107200090001d803d024810414000350360008120340166800c0300c034040300a031000703074990011402842c040002040101c020740f941c14480840144904d40042c9080c500e10308681c82030b042460070070401a103d001b4000c010b0340e9410103421900c0c0071070080000c54400c01c025403240c480c84089601501c03103210b030640c040c1000c0d840b001c000c00c0400d201c003088500034a0b01d1a000400e0740200106964901515042c90961501183c141c0e07034041d01000f11081d40b582d0b50b18071004000c20356011032144103811039160719a8001e10846000c00401460f2090804e000d29 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 572828120 1250 572826870 572826893
    0x308030603100e10091403210f040c06030203100914060a0816030f06061502030c06090d270503071e0b0c19110a0f0303020c0406081b0301020d0509010504 68
    0x800341c282032070007030110f1040102e000c400b450005140016215a2860144100d05104000d02c5030790201091001002c48014144c0f00e02c590720303503280c80d50b9541301e5181c00060b442c01d41c3c000c0d040001d113000074410a030180c3d000359008418221b40501603940c904407141641c00320784600c0c800340c00c032005100c02c0381064901c403000341510001078403d9540e82c1c50001c1600d036643c030019201070a207810034014800154084409800407440c0001040d44d91203003c1d640e07510540d401c1c40c4500c5442d0004081400204e03c4442280c1c0559031787d440f0012502100d142d201c560711111500c0c88001d803001807182c0c0c0070401d1a0041c01105a4544010100400c0d5450b00c03009034410b800c192009c200c6c044188101254540300c00080c2c441d661010b00c3e541c1401100c400082c10300980009400401050740c02c101d00e04201224481d40c03c844100c0150001d100c150f50a5200e45041c0e580100b42446000c1200d052403081000c1c09070005082040c500809800d036801038504c040641d540d003051000b400350622a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 572829370 1250 572828120 572828143
    0x80606041109060a03060f12030f0903020d082109010b0307050402070b1f080a030815031c2a0f020f0307120807020f060c0114130f0b060312040308030603 68
    0x10040010781c44000d064a2203005003661003140c0000345140d07554041e41c0b00c41e000e48000240d1600c03490311082ca048286080d01001e03808a100c1c42c24214005100341410400c1c0d070f034040c100000200700d59440340969040012a0605ca40d00d900203442440d17584d5040c41c4c420b81a0310000300701010440241814402150001c5000d1401080b10101003100303410a00d400c03444030300a000c524122070706828221400703500324901a000c0e4030803c00038140c0c041011070260000c7c0840074030b20341c61070040559a80180001805086c801c503c0069010302410030813010440c4040020080b202c044240300c40900e20440440307490302e50074000d00c00d500301601c0c080190322046d0000c044540c2040003484020300704900040c04100005503080454484004070005d80b400500016200d070380c0e80c840f1502a00305030501080042083c4001510220f031400716a1303925401080c00304000c180d41d1607561605100404330f60700f40c4191b000241410f00407400500003103004034282510b03401c040c010542441080102c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 572830620 1250 572829370 572829379
    0x60712060305030f07032d030609060510030e030405120a14120d0e10020315030c0f0f0904020f060705070906060203030c0d0903030b09130c0b03070c0f0503160c080606 74
    0x341070000072000811505080f100c1c1c526941c03a2882803400311201030161a89850100011800c46885a60b100c01511320042d80e803001c0c84059205c008000481d1464410541d101c14046001001940030307910900300a680b01041e80c0c40d00e074680d8041035240844414550031a44809080014450540500185040301d03202801d40040070a8001d91a07006403000c000080380d5650941101040410100140c1404034000755264507045c0814000b0012240c1c455010340207001c0c8004484c034100100000c2c0807801080c04841d01c4484041c0150100020310498211550101d40d0125580d02401f030a12240b10788024024141000ea100055070b205501140541d4014014401c0b0b0481c14004c1d100543d007a92400141140a420103e001d03003020803246800420410038011920b8000c409100042c3c0640c80d100b94090f594000f52125200441d6824001500500c0d07030350001d00007241304c09500d07005030704072424002c0c00c0c2c0c0c490108040c07203441214141d00b03030281004103002c2030090a0340180700300d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 572831870 1250 572830620 572830631
    0x140c0702041d0c01050a03020c010501060f020c010e06030c0702030c0301021b0717061801180602042108030f0414120909010b03090601140406080a0f0203012f0a0302120702060712 79
    0x2e126599544200c901181482000306503d4041032080d0706868465000e000284915603450700060000c80c08491160014042e55194100a50081c3c09005101d00c001c0c0806103169504000346a06801400c1e0403a0725001c0c110644a603503800740041c208241c0382115a003014072002442d5442c1082e15070250a0122014461021f03484000c0b07482548840140c5e03c2e4a100c030040180b641c010b010b05007080b4048400398035024141300c8541c2c0600261034585c0802410440400002c2c083c01c8601c1000500c081c104100241c0304441380071550340c0180c0700e10b10840f4140050400725060584030900008010008126008207241000040d0300611481e11424a142051108076072506014003c0421400c02d010349450240c43e940c1c003c6006104003c155214034019141406000003488003c0c0d12a40c2840c4c01d044d8103040d4800509110800c03c40d507012400390031022442c481d0484007010741410343c2800a8844a19854145881a0302584c0a000d007841c01034806031601040d2011900041d1401c4c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 572833120 1250 572831870 572831921
    0x6010c050321092107030c0b0403080105012307111516051605030a060506030f07090e0c030c01050d0b0406090905010c020f120904090807061506020d0f05030105060706140c070204 79
    0x8203003160b14404604c0515540c030001e04003695101ca045070004c0280c1c004030304010500d5070222116042c0c5009136650340d0120b4032030a4401901c102c240c0c410107680c40c20010030000a81c43c40020700c00c03402c003400c00d40c80404403100034007698000600700403003c2070005002c1c0822a040c00710000c2ca0003500e424114650601001c240e50302407101005100a46e1400401e0032640c0410620140410241c102c030a516103580400c00644024801c02031035103e1100940314a150104015480c1030041c4d5a09042400e800300300b802a1085c103803059003042d9185000700d103104ac1c50040501c01030140c400481c03401803109000381341c8482c3d22021b11203504050421011010402c2c1191100c0100700d0b0042140c18080c14007107202d1252074001004c0e140340030300900740c1500015680c0210343c813603025501181548003058a9041100c011000040c00c01c20062200740b600d01c0c007a01c4628000c1c0030004082c41110060000003004ae52103000d0307030340301107200030461919004101e0311210780003a401a25081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 572834370 1250 572833120 572833153
    0x3020f0a0308060415050907050c010b04090f24061409060d0c05040f240303090b07020105040303080901180c0f060903050d081b0414010909020c07060806010c05032109 74
    0x9059140300315110f500007440d04280c8508207021b0540149400c0040c02c00c0100175090350300201d010782a95081c1134103405240342510610304034a4111480f101c049006603284031040100c0d02000810701000e02c0034025034441c85c4540700282c0640004001c0b1040c4200c1001104000104507601c07480f60316a0110000e0030980406003110400c1e1408244506107180070070181c1022803001d1030380d070500d50402c410000308042400440c0d000e07442d514141901c50b10100614410840080d021500c200400c10000303200c5c054441e40710348050000640e880d1741107400344102425800030f0311190604202030010b10020f02c403520040802e82050500300303246684803503e40000c00407604c10300806200044080100c042088200103420b54401e0fa142e894002c401000e9501c0c14156001a54110000c0307034201e0a403080310040c005d00401050b141e0300d8498100c919102c020b242604011b10507920200140007040905035403500300c000f0f03501c2000034518920b4900b400034050005035102c40d4004c1c042262 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 572835620 1250 572834370 572834387
    0x8090c01020a11270a110a0804080a0314160905040c0c060e0309191409070507170408030408011b0309080712030b130525090b09040f0608030703020f0a03 68
    0x24003040715281e80c0d0683d030008004080650b40800d90f2801c1002100308100305044140c42a040d03814208129075001c030400d80c103070048131500408582e40001040c0031618040162582110360b02c1c000c151031320104110452401c1c01e454441c0c40031944070076244999040f800303420151205440c100003042c42448020300051a151380500b04d9942d501b200326480d1402e1045403c00500a84449495440e0b41034119440c03000b482903110041841c503810801d0b28190342c465000307604590b500da05000451315030100780c1e1114001e100c515681007200255560381072024100030180c3e00d000060000460344030301c001c5c444a81507507003058903040004000911103001d0362300240d04054418207241e4603aa05a00404403140340683c803040518100c001900300b034204904c10740e0345105c2070411481c962000c01da4440c0700c20b00b000108580035030602c1109600405480c1400d0010800300d00a01010a240111502900071030015000007401e1010303d9010441d040a44512200400303004100b510001c00015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 572836870 1250 572835620 572835623
    0x30f0d0809071e080c0f010909020306030708011b031404020607230a0602031e010819080d050106030c02120310050909010e0d030605240f090315070503060108090c01020a 75
    0x3420003140192004110007806030065055000507820107140c404091001803141e40e6244c4900001c400480c201507030706940e100d00684a1811150800320000060f40004003144e41511500c0d00004c0c140300c003409041c500b02609a10001d00079103660b002003c0d520a9650340f03805980480a201c0140c07661002c44032083e0f007090300c4098040a1141074204000e060070101c03800d00c14816031806125150b80291701441c0e192400c10342001e00311040380c100b1a002d101e42e01564101740b0000b034240c001119403000244c441d03621036140c10300c0202d1441c2152401c0e040700700040e5903035000106a503010465110712401c1c50140e82d0451410343e1800d44404103601886000310310101c08903019000940208008484a4068030300007240c0303410040090820b4071850b40f1440040e541a0103c04000000f1030888038244201450a20300d410000ad180d03200c0c118164062285440944008200200c11805032150341e9640d5941d050120005152030401b40081c64660090120143c081c1e0f000030300d0002e800e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 572838120 1250 572836870 572836877
    0x2030a02030703260403021e181f060305150603100e040804060e060711100e040911090c09030613111207091109090721021b010e0601030f0f061d0d02010605030f0d 72
    0x8230354610210381c0d80681c4002990f2000e0603030041c080c40160700c0001e03c0d44075400d0a68030016a0343c4100840503150280c40c0301c3c4035100e02c80d14540703043c10060020360b0320801c5000e5440c0c0740790360b0300085035085d4003c13039040d25140c201140c1405059840740d507449c0c503454100ca0030343c00e095054540096030b0b01048030541c0716882001c0c441d9005806403980b16444400100704100100369820b020100403000113456114181001c0020580c15a52040c1c0341001000740c02001c4507030b60090340b042194800038042da0004014081d90244daa5045081d003440e68195015150a6181c00d46032025611485101c03441c0701d105111890540d1103428401c0c1d0b0020302490038460031248038404510110205070942e141740d00010720580000b01503104030202c03200d21402044018814025103403513071402c1c08002c2121003401c82c2e0788046100c00d0b01c4194040d020715000988101504070303058814580150307032010790300710802c5c0c0801c054081c41143c00500b4150701034041d41035541c4007076031a42c0750440d130103061 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 572839370 1250 572838120 572838169
    0x91503021c020a0c150b01021204180e0a021005180406051509011404090c08060301090308011208130306052505031305070e040507050307230d02030a0203070326040302 74
    0x1051045002001135900417a42e040703502c1d1a1455003014114030103607203004d40301c0d010584494642d140222021207102181c02104101c0d0010707000c01503c1c0300c2200b01014443c2c3d0009801684d030f151084803c400e06a129240c0d51f20000404c001c401d8803111849100c0d500d0440c04100303644a0760381c0324503558178550511350740e0480b072001078030449070308080009542d0380883c001c50602c80c55400302d2000c0041d502c0d0f0440503681e0b4070815090712003003c401000541c0d160010403101c402082280341c01441003c509081c9181c10600a21801c0142d1090b21855101e4061200200031413484810f1002d1040741c00d00c00110440000e0094031000d052503449480d04a07032441400424044000a000b03402e020940314106814480c0d907030f40c2d1a001d804e1082c0200c10340020000041c41d00525540c5410158550005007841002200d45074070b401641c05000d0b040c02c0e10700507070b020700114024520900f00501d03c01caa0842d40c444485403951680311070b0800700024805a50b0380d1124110710201394084400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 572840620 1250 572839370 572839387
    0x90a0306020d3e0c10090c2d050d0209010e0604020d02040e040201020d050a0c12030f0e01050411010c050606040b030a12050c06100b120a0209030d091503021c02 71
    0x80c0b10b00010594480c158a00c500d4081c1604030814506140801a190f800c00e4281503800c050711400f02820002e510000150001d1005600031003441c07809204130401c40c03030f50303428000c0c54403042c00500c5000b082c0b40410040c3c1c2100d075040740740c042c20069483c600740c1041603011900003c0103011300061140c907440010034556994040307800a900c8040d00f07548880e42d4008040c52134a040c0c0d0101e0160088035000d142886c42402624450000c640e41c10103042040e40703501e009d64207000a1a4205900c0703400e20300d600364030750040a01100009000180601e0a8100b6107040f1408032001410018035403c0b4030045000060190f800c404100c0300000e0980720700c40000d15140311000300a00d003190041c41e4408145d0002e001c0c0c0043e2590300150f80007941c034610b0354030103030006000e4014602000e10034246158a942c0c1003540c41030003002d00501d0072010900182c641a0038244c288005640c03210144800780c00103039101d01c001554201907050a480c4090b0003004800c00704a40307079142e4080b5500c01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 572841726 1106 572840620 572840647
    0x150a08012a1b0b0403120e06060a05010807051c0612030903060f02040308190215010b0d1409031b032505010e0604120f0201060510080405070b090a030602 68
    0x107000001d00c3d030b600084a0006801a0308101c0d00074860310b0100c0d001c4c0b08011004c8008002000c00e40b62002c20001e00c0750701a00031604000840040c44040d0360828207940d4485d4101c2c041d00045003030310001d0710050203a070f0b01c4a980c404085480b403050540004c921000e60b40602ca061018030600350007241079128a200003410032104003c510a000c0c14110041000d845a2041da12540c141e000a5a540403080c3c1085441c00c6c800640500b43c4841ca12034102201e4580000300140c3ca03001505984901a0782c2c012050700340b00f01c0030425048014011502040741e03141046031005500c5041d00508903112408940542c07a100d45a513800303400103000d901ca642d0040ca17840004161002c00ca5208078a200c4e03120540d900e94502007882d540d480d12025401542d5500c01c0031714038150916a250420ba90b0200021140800c858a51515148010400e60342c0000016980d492541d4414 = true := by decide +kernel

theorem cover : BRFrame.Cov 572661870 572841726 := by
  have h0 := BRFrame.cov_init 572661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 572661870 ≤ n) (h2 : n < 572841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
