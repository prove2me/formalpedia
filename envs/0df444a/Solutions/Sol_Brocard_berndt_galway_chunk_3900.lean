-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3900
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:10.341411+00:00
-- url     : https://prove2.me/submissions/7d07971b-2f41-4ca5-b58c-bd98ddb3eced

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 701258992 ≤ n < 701438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 701260242 1250 701258992 701259019
    0x1311010203040e1e151810080307081201051207030b04060902120705010318080304060903052110050d0b06040c110706020a0506161d030a060515030d03020c0c 70
    0x2042120040d00d201c10203440182040003141c01c94001d400800c0244d258154000349280c40e02d0100e031604040300601d07859000940100402c030042003d40000060810f4000208410f901040240f00151003080101c1d0756620340c0107502407640c13060b04150310410303046c85030102d540300c0040c0314020f480d008031503501c83d51910710f4240014115444000d4019018502c030b07040200d80400c004088075000e0f201840303950032407000e0440c144001c940c01803400b0828400300700030844540c0103840140c400d0610074500460881d02c030b20510954040440c000b0800410484407c140700c0c0c041c0001c103015200991081c00c1d5599556689800510301c6004903915104c01d600b40d0321903444410728a1402c4140d0b200141c54040082d2507621500c004e0303815119450100382c0c0e003224602e03124601a80c1d1384c0d4102c240d02158031094003078500b0f0f040280e031620400c140760b00401c0c428442c0724007036040d07020b5500c0340707503955410325060900444140c000d2501c10720601c02c00d0f181c041007140b9039400455840514954 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 701261492 1250 701260242 701260247
    0x706080702150408070606151407020a08191b2402010b0a0909030305130506040b04060f0203070f0f030905030d0f020d060f0e1b040605030408091e1008131101 70
    0x79980110700c0b4210b501800103200c0200001c299060040005121590701c80003080288942e5840302c1000543c42c1610701801d40105000d070a80314401451030100300c1c0c2e240f400758a000240041c1410000070042c0c810304104001c0c0070410b4040c60b00c080c40041030301e412082901c0781000307940c0d050103807408903030103091a1007940b100d552500c1c005c142040e0a610360041100520340c0c0c90044000c640b600313000c5826042c1c1c4054409140368420f00510710b5585640c7c540040010282044034825110084001641140c0c0091445581715656190314881848402041c18801d03c13140c0b401d26213407800d2000401e4012003221040444100082230507213010350a24000e03c0f0f150111454546080300c08210300048032842400c8070200106441951580c058001c404000c0c4040d00c0142d100c100010840c003400384018562043c0640205801e1001c00d1010586242c0c000f00c400c0f21141c02209203400ba07242c1001a00e0b9108081d240120551508861040241080c00070142421011508c090080da1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 701262742 1250 701261492 701261503
    0x1050c0a0c0602061801091101140d050a090c060c02010c0210050c03030123120a02010806040b0d030306051e090c07020d121e050708070f0804050312031005030c030706080702 77
    0x1e61215007285182e0350b07150b00a454401c1641d40a00c1c04c0b41543c44503200c00d5050080c0121030380c02416003524064a07600541e21404640c4807a4070b0208184440a07072600c50b4820030b88205100f440c046070407400f514201d014414580c000c101030204c105d60007005030f41d01c07000072484a03605a442c0b07000b241e150602030303c05014641d80c0c409944400400070401d403440d114602c21040103154128600c00ca41000c10488491515406020fa8081101140550b208032103c9030001805040010b0b5002514080740342200110001e40200f511000108070505040303410382c4000380020006c0c911902490001082000050000e03840d120003c01e03038105560b5003610414185c2e82c0000d8140403421010400380a080c9074580e807200044080d01060103482c00394086640c56a4800701280c40d10406030380d040319020102d00c0070b03100b003601888042226101000006940340b11000044c0d180e00d44100103030030040c11504032074020340042580c4a11514005195419151107007030a5610399140e500072031801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 701263992 1250 701262742 701262763
    0x180f0b160501110c0c030105150d0312020f19091a1204060e0f06070206091c0305130803010621140403051c1103040308090f0601050f13060608010e070908030901050c 73
    0x90000244104c0c1d9554001142d4000070010380c0240308a0b920000c201c0614046017009507003091500c40144002441a411140e2040c01400c005041046504c1e10169a070400c286980c008920300003c03101290300140081c0040c100750480c030840ca82c410141084034001c03400101e0070240c16101060401a46e90000c0d0007080d6417038115115040400303502540d5078800c0d5107000c00760195070b0103e104030802041c1c940c1103510354041c15110b0251100d048005140c02001040c50245151080000800300d000a60080c40f0564a032058450034005605000b4900390007056010b15140c250f09400044000b03041c3d0103609070500603115402904070001c140140101e10172414906044540b04a1440001d140264000ea440810b681d403661800c03a5030381c10b0100007800e6907105000400051a007045aa981800c0140c040649100b080d980c0601391802d43c1c0000c03000c40c44000043c4040110115180d501c00190320301414194585411241c0b2441000710042c100312001a048103800c00c100040000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 701265242 1250 701263992 701264021
    0x50d09020607020909010c09080109030503061e0a030c08070828031206091e151701020f031626150f030d030906230123030d180f0b160501 61
    0x1140f400c0050b0b1750007441135503034145c080340c07078090b0100e83c0e140c0511400078190b605868071444e50704c84204002090b0000c218038200c0c0344250503181031985032507a03070b000110b00c0b03809940d048034240070049003002d00f20b80001c1203e40c041c0f1104100341094001090620b0138001421484c0ca40e80e00f8100c40107002512987e000a0604800080c402d030381d5842000d084802c01002000744800e10200c00c02e1304e10604d503038002040e21035018030082c499880c1c0c0c695110701901c0014608031a48800c030016400c120344801e00d07415404181c00329180c2140c605088200140c03800c030b03903890283ca03c0c4003070444040c244079004c41c81030358051003507100c0408445240c04002c1c216a00107030340071802000f50280d0241100c50a04080c5920152804c203194003200b4680d2525500c401e03800d06030071151200810350080303599241070190319001d4505000400040003d0b558940714001d050000c180212403a41c04404400302402c0200112040501554503451060b0810a060740440c00c289024104080c1e07040301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 701266492 1250 701265242 701265259
    0x1090302150c12030903092206170708030c030d050a061206020306012a08090d060e0609070e060f04020d0626100507020a0308070215010e15030706050d0902060702 72
    0x511003080d00541a5948410308482110700c8485002c1c0fa240410749100005038410700c04280da902d40b02d11103200c440006207690110141404a80c000c0d00d08070b030300000307060402d4802c95056140c181702150151400130011880c000762125429524030032003010880c06a0342d600170449000154200400138900d50386501155074060402000a50003034800a0124080807124011449080000d040c61070940c5e484200e1440070740ca985203954040710126601103c400301640004980c0d2203807500c489940c0c001400e00d1718200c500c00b40303044101e401681c50540c09000300601036841500c04010030306c040d500962610081030400b00030f8501c0c0e403c40d25445203c912a203069500844039140c40c0d5140800710307088030103550310030b02c2251010340e64a00140c1203240c0c90301c0468000e64000b40c11810314070440d038480200381520390304802c1c2070300100d60b5170b952003090000300c02544144140048003180601101850b0800140803072003001801c0c41800d840d14075400c103541e10300099842e17003030300600b040c01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 701267742 1250 701266492 701266519
    0x1060f02030f130e060a05030619020f03090c1003021312080d060b0a02010c030e101e11031008150412031103150406081204030204051305010c0801060e060f1801090302 74
    0x50714202e0340194454140f813100025514508201c511045410280c080c1005464010042ca07001c03090400c18001c0c99001c00800390300e02c00000c000e51003011484c0180c135900d00301c1001c1000d2034184000c42d80c00c050050107403011001c00c01446504641d50008511204903040c5068000c1380203061041101c6807070800001000c0f82c10000406409174940e008200a01c030001058080701e0302e070014032006500c1b00050a144481680c44602d40ca602d425100113403040e4013140b041600d00301940d8080b405404014070510030302d100c043d5030107000f2402c054104400826200824840000c201130405880320700c11291541c000c0c0c1c40491603d501c2e00358181c1c2c2c1e181078074541400b01480c58076903001314640040003901c4032000c50302d00e90611800f220146003501d95002c00010b01405010881400c84444805000800c03d118070b1040d008581c03184400c40d858040060300608074048828040d4404011002e44444054104c0310014100d0380030010402d04940102c0b400f01ca6608003d412109850489 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 701268992 1250 701267742 701267767
    0xb0d1103040b0612010e06190b0a03051f1a0103050a0f181202010b090a020c03131d0601020607210b15130501020106060f12141005040b030f0601060f02030f 69
    0x21031080d681551040030045132900300340d08035004c01c450000710750440800714404e50003408018142801424000c03980c0c44104000a20b00d840690045426a0061901043d82999900ca0307141c0c3d520a40420480210401d42842c009174100d4101810075a03913800003000e043c116405081418007101041104440306004401100c90012040d40d030794069812540c500c600c14040c10490b004081d00d00f03c181d40b200000d0300041d4001001c5030509000500c046c05c0403040c00c4502c0401800054490384110b038131201a440000da02420f05411508800304228505800075107c0800003003810300c0100c40c085007098480102068849190f000b101580c5c401001d2200c0340140418070482d6220041403540d400c01a400c8802d64803d81011924400f5800325050141d1220140c00380510000304507402c2041031340700c1d902400c0f02c2e640400c810b50f820030f1010b8200384c4589032200c3c4c82a0001c0001440c3e9608103a550f040c144030b14000c1141009014540034420300c290340030381064002c0a03072550855000c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 701270242 1250 701268992 701269013
    0x5180706030e010b061908090703060f0b040b0a08060711070b030408070507080a020904080d0216120e0406051f02150703020304210c030e030a0f0c0f0e040503040b0d110304 76
    0x82d0881507080503500b203403900d0b20380d08403412164042040340200300b06100a40303901e000103004000381d0042d4039001010810318010111048844a00060f03107041c000c04000c00c554401002a015100c1c0502c18404c1103400205942c00040e1401c0c1401e14401c0c0702d00b41d07854503290750040c0c2400c070b0b004001d1008100d0360741c000e04007440c8960165004682c4800425070b40d60200071010f50300c07400740e0001c900070a1029008101324a51440d016140c00c18402d110441004401021a0100c00343c00c00311004036803001e41850504800c03542400014a0700f00000d81c1b41206842c0c2c080303200907004540e03d4140c002c0251070054114400c01d49610f140c00138025000b5002250305950405142640509c8108034441c1640030740c5003a11861301002d81d81c0c900300d40c40844a440d0541501c5100c1d003180104040e501220301e0354bc40741c018038201d103090018001e108440d503031288010508000c28880000c41c08801da4040d1850b6400003612100e4035058100640284100940d070003900009100500c460440d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 701271492 1250 701270242 701270261
    0xa3e0c0c0108010b0310030201030c20070302030f07081e03160b010e01120f03080432010b090103051005060a0f092322020d1703011e06120518070603 66
    0x2c0e8622180c0e0784240700407262104560080c1950344944003800150300a0303000f032186200905e07045040c40e5005800c0d4541c1516041c64030a10341c0107080400441c94100001090b0200303950260540c0c5180c20300555a900010300440307191040100d0940c0300c0750080003601e091130b0340505444c80f406000e040c400c0a01200303000d88003000906000200c0c840e05038000b115903c6520000b50340c0301101e01c0e00d04444480b0081d104a542c41c8100d21145c01c80300c42d8003046010104000c3c0b420159480c510601421101d40140c0b603405808c51038010004280017180d10100056186004181603131004c0000707000c1d1603c0e8000e0104191018030106100c40c0359404901214041d0340c5000105508080b90120720008031079040c0044500c0c0d030030680c0d030a40c3c1845c000c2c0e001d1000e00180003200c403035038030f80382802410980c030038001e40d0102c010000050080d084400d903030b000325409501d0718140013000380081001c8802c420100d4990011801e0205c07040422000c440d24201a6503900ea2200300080142a0541 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 701272742 1250 701271492 701271497
    0xc0105010b1c05060109060e040e120d1a0906060a17010909060e0c0a1509031a09070e07121d0a121706030c1005070605070c0b0a3e0c0c01 61
    0xb0902a01c1400c28800c150082a05071144001140380520495000300b500e400c480e00700e83c496a070f0000d4007904001c0c6202405080000c1512140c00c00f003002d003120043c0550525100c80c5141181440d210f002921f900244259906640d0f0b0340c0c021700a40d41c05082c10a409400700d8084000585c5500592142c103a0038450101488200400704907290340d0180c113000640e000b140ca01c0200070065420841204011690070928090b50396500c82941c5403081210341d1080b40c00d40300c10012120000d1040f0360140000301d40c0030b20355080c10600142202034500b008031041e0b07543c65919100e4900c0d8000585610f4140003151040c114504d00a0100700c5d800c1c1180001c01c00e522a0b4901006c00d5a01c030522844014004040d448001d81c100480508000040420301400300904804200180a0984522015220319404103000e02c1c060388119001010b61200324a000071210b40050580d40c11143c0b100031b160048540c840c030059000c0384801364000c0d80c8401d540020166503075040841c0c01c80c40d40d2800d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 701273992 1250 701272742 701272777
    0x1e0b060915010e01030f062105070503030711060304020f220b011112090f150711100c060b1906020106050a050d0b04061a040203012909180c0c0105010b 67
    0x2006111099075501611030301080c15551100d000b54802c0e0f121541010303001c007002c102c41da0703126800365140c0007003c2850745a2021b00380c5207040c00300c200b111030001d01d400d40041d8504851920b0b042c104417413006105106420000c045415940e407120001c140c2c0000070088917503c0b285d181d000a107043c0c0c0c0c1c8a0f00d0308039818507151010940c05403031175000b0504100d0241ca00d03a68078044800c01588844e490a501c0b421103561100144c4501c040b10300c20300d83d44000c05648191034100300310001c550307024851250004c03010003c101d5500080415505900c00c4001c1410b084820026001500d0b400c1c00c80b503550071400700040d080e9070540000d0101c8009407003140941e5210401e00030004206100a0040b03646440401c0024003a9440004424a42140c0c0407185103803100040580e030082e4890510521154003121041b00481e40c0552881c2c0c0381c0d00c060746000351703800c040f07400c801c14220f1110850240e0000070303900324016002c03149881092002040302d581c58207050b01032600002d0391012540c800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 701275242 1250 701273992 701274001
    0x180f1501030608031c020f19030b0a14060705010e160905160c0b1312030c080a09021003090515041b06020307030e040209061b011a180604091e0b0609 66
    0xc2d100d4101520050f00285180500381500d50000644044010803c03642c00c000243e01266100b01030802203003504005801c0f420500b0b001001d44031130700c00403442800800000c0084914459031910000350a44882c0c0c0c86100b10b082c02801400a048a41000e005801310012100c0f00003143e0410303144080010440c980383d41003c900303120034001641021a2600a2a10204201484e6240c4c0b01410008a503084403440d59803101e010614003203d004030380c550050801441d0003a041961200680408014600094001812400c51303005040141a42c804140c81404801d200e0603180750617940302d049071806c080c81d007006421030005000c0d801c140b4510012882903c08002c0b0307050181c140c2e80d540500e4120404000007940301d540b144d54820420041c8040301d80c500e40700f15042c9590034000182001e8042c0c100c80c074aa20b9114001d118070762803280c102c08503031040e02d10358000c0002d640020740c40400346085549000340051040c0d510750545080c50401003201c100e00d00c180010f8500f0915a00e9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 701276492 1250 701275242 701275247
    0x7021c15240b0f0c0a0c1e060507021e040f051602060f092503060c0e0103060501090819030311040b09010e04021204021002160e100803030c1602180f1501 68
    0x10750b02030304104500400070b01c01c3ca14100000b400100c038044041c1c580c148943e668200301d881155000a5104035205c1100c0324100000103210014000ca04081c1d107001c0c2541e0018900e050813141e0324940307800700494883c40342c45580c4a41c40c8110400420045d03070800566a5102d88a09010300740148126000100071101c0d010540c0c0c01611504010000304469804004c0410000c40a64000301c04400b40000400c04030301400c0031004480d00c4580c00540000001000d8402980203941031154100c3d0403c0900340029201c031162031a542d10410301c6000380340403000b400082c18030b0149400007190200e00403800310000d220010b400d895904c0030696000503c070a1f4040c0c1e01c90f1041c6540302d80002005400c0c03440400030425010710688041030360440b40e081130341347c0c07d0708001c1d00800c00c80104540f14503800e0a140144c2210b00045003140f400d413406501030300ca410705c00e0b0f00101d03658000c0411034459500c3c18110f4282c86201c0c903014034040d900804c1000c81182d4034407004101d0210f1031003550 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 701277742 1250 701276492 701276561
    0x70504060903170d1b09050f010909021b0a0c0f1a070f051e0a0b0f220c0e07080601031802031c110a030e0102060f060607021c15 57
    0x384903454850069103151a0803402101c81c0340300e81034504042200d0301c60034041d482074025949418082404201094500070155942508407074060502c003000c1c0d807c66a0050341c0c900481e10b1140c005691b616081840f104400c02070a40c016151003944c40034000c1182c2010100b06a450600b007010f8075595842c051a0225080401104c81000c10046400411081c440c03540146000c0e20880c4c00e0300313078090a80d110f40c1d11100000c4155402001880081028959284d50001c0360451054031030308141c0b4051800940d121410074411070302040300810041c401030182c0003401d01c10304c20105450702c1d6801400c4039104444c641e0010b45803a03a08021841460a40388407e0f07006001040b40c5007242110400c541c2c4806031010602001d0710317550078216402c01480c0c80c064070035a42d0304c0361912804006464010081c24500340b5500840030046141c641101b0388102c0c42d0100c0309032045a44a048107a0300c07034021744000e4042c0c608100e1101660080e03401c512910300c0385020a15040706200406440719 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 701278992 1250 701277742 701277749
    0x2d2109010501140d0201020a02090c0c0723010e0a121112010911090601090f080312070206070c151b030606110c03100f0b090403030b09011a0a111002071406070504 72
    0x1241c20241c40750060074080200c130b08141c03040c0112041c1003a1a000101c4c5507008852250501c07100250f0380c000c804091041c0f00041509000c1014800d11003900e030501c00607a903600354104003460070412129500c0143c0b010080510001c14508400c01c0d003004000d00d4a070414582c050302d52000c00f4510301c40b0502c00c0360502500000500341c03036005c1504104940d0340c090013081c100301e400640429404c440c00c0c40000109003c1c00203603601c00100c00c49004003040200312000755004002041032440d00b04c1c1e10050040d40c080504104030f80d04026100040aa00c00c10b00c0030b032000e4150000c0300580690268043d2042619100c0701d02890746080c0b85e4541d0720224184d0940c020002c030104084864006101c4820084c4010414148260200e410403c04a4040d00000c0d1203110350f6286043c800c0105015000d491100185100b031020030b80042e2188021400400049681644071020184141e1b1000b0582d044155511102420030550316502d550b42a029409050040b44001d801007040790101c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 701280242 1250 701278992 701279009
    0x6070806181503010209040c1110050402030706030e030706021801110d1706040b031522020f0603130b0c1c141b07051504060f0902062d2109010501 65
    0x7991140c81c03041800300307442c070103a0b0159003d0200c80d06541d542e00035054500c07a09d0750344e1855a248500c02d68a030040c00760400c0001ca10b0303c0140b00141e00c001c80c00c0e6040e25001c0c200482d01c20001c50308035280d07109244016051a1000c19644884d41060689108001c000d9079440000c079011000c090701c4000d50b0f40030b50003040c1c442c851555501c42d14009240e2051008000003080f010403008213080c50021041c45c00c50004000403c814000850f03480c00141d144580c11112468807a030100d09020f80c8005500c1c0310b50000701c002010140c0d20003a80c22125800340984c465400c10b030b158804030b9003100d00102060030303034000c0c003d1442c0040e21179030501c2d4100c80c2c2401c0d01034880c071208280c2d44948140c3d8081c0c81c03000300b2100e40401c0c42002068002c6401183d400360600e02410300d0001c640c8000342041540d420325898002594614042d20040501c000610180100c042d484d10303101c000c0d242508081d0f54000c9981c00703040d0a010041d9218040d1b003c6240195585c032010203089a00034010400d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 701281492 1250 701280242 701280289
    0x509010f0c0e010e06040906090b03060702030901141c0c030b01021b090105011107080f0307031103031311060903070312170f01090203151f0f020703080301050f0406031406070806 79
    0x910b0340c8103c0604210404c0640081d10b02a241d48081c0c06980b041c0e0003c00c4890b0300c555041c4200d0a040081d25440b1900d807019500f07103046000000d049065081e0000c0d09c03203502081c0c1795214000368003100d007a00a844c00400c49000384c1e000c060094041a80c142d80503006512003c0c00324603100c01011030014004000800603820700d0019910b1035000c2c0e0b65036283e4868035a01244480301084000d01940c1c1b260011a02c0d0042450010700c0d42450703000e101160b40051050290144540e02c1d2005101d03480104080480380d246e0100b8100c2c0502c02c081541803080c00c5002042c810300719010000b00c009540d40300480c900e9000030082104066170807a065500c1000108251038042e4081c5800c07451882d00000000020700004408a2400d8009a1040548001841c119800900b058075004450014154a030314545030540d46002c14428240654510201184140d885901c00e0002d5a80500124030140c003041c0c019568040840c1c80d0400b0455010101c1c8081c50803c4c0c0000121120486124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 701282742 1250 701281492 701281517
    0xb04020412120314040b011e08030306100e0316090b06090a1a0d05070e1003110901051303060507050705010f020301050d110a0305030a0c03030f090804050d050a060207060509010f0c 80
    0x9030385a44055602c410180e440b015400092140244180946d014110400e5030b0f5050040200b4200110300000c00ca4001d000420040740e01d020054a0780284121042e11984c0001c80080c1e0341c2c4526030210b0f65140c042c049540d415224000910410303919126170400814401d501030040d5445041c1600703901540610781003007843d44118180d4003140a0408149c14407020911403030640c1c800f0f0761428007059682c60340c4092401d240c0c0c081082c05006143c103000d502946401c2c112030303200300c0400a040000009003c4140d10080c58504000c590000f400c204900e055140104282c0210008951550903c0424006800c06000f03481c10307254010039440d4440c0140d43d4038401a18440880c94000080c1400080881d0003440940041665501c0d048660f480c1450700500320b07010742c040c02c418a8503200e0302901092820081e502540d41c1500c425420a0a5090071440c142613200010030107400025800108801508017600600c4030380e0007403103220301041341802a81c2402145100140002c074661 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 701283992 1250 701282742 701282753
    0x1b0816080423010203040606030209060a0311011b050304090b18090d05180a0305010c020f19080a02070e1608010801090201080f060105040317031f0303090b0a05160b0a0b04020412 79
    0x10024441c581d048881c2d200c0714808031a007a608121415034000e6540c210800960a0002080f81c1c086411030f01c005e2900c0c1035503559800d102e60704001604008c1881070b541c02c80702040e0002c071800b07034101c0e046035111907542c80e20304041d1100a0925000392031082ca50034191942c4422240969800000707482c0c0b2651045d0111240d41081010480d101e501c0f004440303603a120300c80740b00d01440c003582c0042a02c10310581c01901d01401c00d002101aa8081044018012010040b00c018164041c0c03110350384000c2024101e103412010303007002c02a407030310300e0921000f4a81c02c80c582d0f480854503260244135a07a01d40c903c0c0e089800c0d204002c3d0118007260005040212000d100590000d41410002d0034951a40c40c0d050300c90f10142007901c800207000050010061414440034400b407510b9071880e16850645e98000d1500f005407140800840c00420760307400103030182e0300340c820040c4046281c401d003407a2410b11403003c200550318161036a00d44510103040e82054000ca0b41a100743ea0b4003103a48038450b40d01c0c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 701285242 1250 701283992 701284013
    0xc03020f12031204020d0b1306060b1813061a04080d0e09060f040e03070c0f090207080a0822050a1401020a050f03130204060b0a0e040b010e0d020a091b08160804 71
    0x101d0b4401b8101c41446c0c00642030fa0b9066010f044045190070101c459860700100702c8205800403480f0f08410b201e03e1141903900f541c03000300c494041c0c0f500c0c110380d4038081803000904816085007402107155509d00c2c002000703850251045480040840344a43d48043c030039600c070714104080c0e0340c01080e1a40003800c00d081c18001078850100c05080003d06280c20345c1100e043d5088540c0840340c0400c2800d040200341c1c1c01111810207031400010031031500240703541e0940c2234800c1c04408002e0200010000e0419401da91140071805002c8002c0b12203d81c80d4a8020f880b25404070313080324600d525464100c111181482910105412500c031079203041d0300404000c006400042ca01c80b010241c0d0103800006881e1805600010551560300584588045a01400e10000d9481e40d40c05103140c505010f0060380d001020691404d0306840301c0740c0c1c1d0743d11400404c42020454000300c00c2315040007030350a030f1580800d144031a0280d1035a12035817652540343c0141c104200d5501c00d540095010000300e404980200f01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 701286492 1250 701285242 701285251
    0x305060a0e040c080105190e07081f0f0f020910030c1257090e0702010e0d090602120408100c0c1401020a030506011b0308070e030a0c03020f120312 65
    0x20400c283d80c0d1141c45074255001218060392a500b1100e0796081c614440c0102d084204e280d601a100007810150301a03a26840031000d001b240d0720040042c08000115130120040546c0d010b41803105400000c0c00340701a41c482c5040c00d014401e002c10300300b001d5100f40700f102d04844160303441c0d0326a011903405a41c0540309544512400022012000c010001886000443d91101c44101c02180c1c00901c244000110b159540900114030420420314440d8007800601c1a5226640041c0311030321010000c07401030001805940c02841420980000e00381c10a61101c00c85080c1d600700d40c5045011682c07003540323010b90312959209a01100400c012100b060b08180502086850100003151300342e1036070544c190a10411a18595001500528240d85030141650290003030810000407801c2c4481d801e0488200100501003055020101e4030a41c440d00040844003030007811103c2010310b42c00c1c03010120b41940300c102d20603201e00201108a042000c020001c480b541d201440c01d00c03044c0704103648541070060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 701287742 1250 701286492 701286503
    0x9011b05060609060f090f0f0106090605070620120f01120f02060c0f06070801031a0603100f0f02040e0901051605121b0a0302030f070306050604051e1002060a0b010305060a0e04 78
    0xa071080286c0d1551503040307114001d20b01e0030300120300700104036248505040c1c20242c100328031340c2010f11945400170200c409880d803100300040d40c21050f031035030a55140d400b291458081c1001411080990301a00301d140181e90950380c0303803040d0740e0b10f81c5100305003550380342c0040040c1412007141c805031a2000181c8084c00342081500d286600c01e0509a040c61401c82d80800402c4800c401401480030382c504500000d1a6198002410304040700041d6841807003108200310192201512900303100c0030b030800640c01c1c076030322415511aa2180d43c42540d600080395142c8403036181800142d0b916400b40c4507162802c4241d00c81500d0210000c40790600c5484c002c1c10995500111144c0354000703080e01c0d00a01410384540d500503104e0a000d00120030506010340300078201410810b050000740e032484100d0301103d03c11038840030700041d00155500c021400804403648010350f5885885e40075004601940300b07205050042003805642401981200e40555030349401840d03c2c603091094030300780c0b00c00b0381c0c001d030203003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 701288992 1250 701287742 701287759
    0x40204060c060f1407120b010e010c0b25030c11010507050910260106110d141810080f1012060e010207051b030c030f101104120809011b0506060906 65
    0x84d4800070002c15108000000c02d510341003049205a80302c4d030700804001746000d0341c1d20395a1200007002501d11010140188540c00081245c2d841c141e40c1542da0741c488600d15a8040d445103901400030f2000780c61950110b0300c0d03120003000c04007040c0b0490744201010745510342050008800c2c05001c805440c142c0d000d004e1240c110f405007041340c510703082c50b1101e004403000c1550305007039004098000100701560940d2001d40c0c40c190290304410f0081000702040c102d1526035070020700840918464170f0b149904060300c0001e42d40c006901600d802d114141d161440d04103501c80311a104150a20752048a01400c4154120f1000aa440d0002c60341c0c0c4207108009070074101c60b501d070300b8140007005002c1060520005803142d41ca080502c012104464120040c0100b0320003800019261301c1d0500401308169aa00100401500d410007a10044c1c408629501c00f040340c203290503400365200c0d402060129614411203e2220b44094119141c00d0303001018108a03154001803100e02d482c0030308041e5000d81e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 701290242 1250 701288992 701289011
    0x30706020913140a0605060307140307030902061b0c09090a030c0305070b1e13050a0609051608030c011802010f0c0804090c0c020405070201020405030a0f02010c060c0f0905040204060c060f 83
    0x10b0040b04071a01d070b545403d0b03c0c582403c070798a40803221030b6880980218010f1003044a60340d0400340d412800d013413103580140d8903a84c4000c01c0f0010544102c1c02940610702160b840522800400040c042d80720040855018174207410401810401c221030040701503001c10034040006c0d12500d500240c00d4400c0c103203e41050451385c0c4807021510121f40d61680c0c40c2c2c840307425200e08a00750320351541004516140100428036922455241e1001700800360820f620394003d8400c014080103112181170051074100e4206844200d01c40d00c90b88051041403885d820000c40e40d8403003220b6906500d24a605071265400801d10303603407c1d2400a0714100540301040c00f0321000417540c00b58002d41080101c59500d660380409144100800c0b41c5016200004581c0b041c1306c1840350340c0740020030022041d00f240c0e00003018001840100d40701d19820314010452814401210121b68100700c441d002c0c1807284d20b032804d072182c83d02c0a01c02240214444e000c0003032981106c02c40030030700981c41019030300740d03c10307021507a0900c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 701291492 1250 701290242 701290279
    0xc02150106050910080114270f0103050106050a1511010912090608010e0c09120c030a0c03120804080901180506120711150403050d0b04060e100e01080307060209 71
    0x241d00030400308100144015072490a0881d141d074141c09030a000519505190b200300301c4840c00180b42d80500708030882e1034442000c01c1e80c54403d4415802c400202850840002003a6520038030084480d0b6091110200b1289002c48020050320442c484454080d44081e07000c0b5080d410301885050340d5542c400c41000030070703801d050034103403480743c0c3d126010b00c540b07003035001010080141d000c801c11660706000e002c1120a41c800f1111107110031a542c0c00450309054820382881c1004018591602c1040301050410000201160072a80070740401c00e091a04004183c60320001182d0050101c102000b220b03903198080d131003141c2148003800d9160f09068980740030620a40c401d0300a6801040041c041000e4158418410900d00442802030700a28610341400c401501e00030f4801000c2c0030012075401c1c1c0769a4607901504244400030014090aa82c5200b01c1402d080103407800050280b11400200c3d0180580e10b02c40d0480b001d020082d80703410b07100e448050094111310246540710a0000500300f0242 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 701292742 1250 701291492 701291533
    0x1101110703030f121503060203101d04030311090901150203040f0e0a05090a032c0306150114070209011202030a08030c04052e03051503070801091e12030c02 69
    0x501c00c0e00d805034000310304a03014045a260713055400b00c180c00c0007800940100d00f85d81c0007040701e070312400c0980c49072103800c0c40a40081098020044040010481c90040b0410801c1036020768084e403000c115500c80003082c02440d104a0301c6040c1c00c960603800406c22031691480c0200c625110f441603d06107922015102c03084101d030380c4022001700b400024001c205409200f0b1640014065004110507401a038002c0c01c43e03d0a20b008503018020190100040400000103612407176008040d03c40da481c0c83d90496800141580141b400504499850106c98410004440b00c04e5001001c0c0215a0702e04825850b50364410707541280c050148141c1030700090355410246006007060001d1a403210304050a2020070784503558410b03c48580baa0184042c0305111901184244d81c80c600803800342d40d04201070304d1940c0d2148555070940b10f0311a00140d202810762003100042c0c8643c0c1041600c102c841d40e24160403004040c081c3c10741450729000886180240d1000024074100c0c019a0900b42d00840c880c114003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 701293992 1250 701292742 701292749
    0x6090c08120904150b09240f070c1502120a0915020303090d0518040518070609080d031a0f041e020a030b03060606040b0711030601122a0501030905031c020403050607140711011107 79
    0x10302d0224164082112b640e11f40401381502d4003e0a22038a42014020348d10741c44401d80103640c3c000010503c8101d481540c00c00d01600c0350122424101d092414000e642e9801182d1510080c004c50112a10280c850011501007908a40300748445207542d00810004010180058044005480800d0801e10042c8188002040c16840300d80910b407410340c50300e00b001522003c0d0001c2510700840000a015085104004505d0684d084403140c0348010202d030003824181c0c804d8054140d0078254440061458009040a22203581c090080942040915070b6514040d03c01941c0710109100c10301002034010050014035001d42a41d410207850030001c6800c040081e000240310171840030300c1c1000d20031440c164091012049440d80c850014100c80464611014054241055144c080d05070a1020401c241c5011000200d61104d03503c01110300e020081d40b180c03200720fa2038007032840007461a9001300405015030781400b1710b15181c284150f68242d0500325034009681440942404800e11160420451015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 701295242 1250 701293992 701294017
    0x4080d0c051b0105061f021c02160312030c050408060f060a09140a110a0c030809030403081303020118030c1806090c02061f0b040306090c08120904150b0924 69
    0x680c1040780900c034040d00c0b20380e0308400380c500d000c00d4801c8860f4002042c1c010b10720007000d207082348078681c04102c6c2021089103074081e00701075070100401030000b0301c0e0703083c0190300007a00c0409c00e04004800c16501c9002e203100b0313202950400d000040c521650004c0c2c0c00e9202e1001040c103021140c60b199003a041b98011b001c00c00003195000c0401c40d0240b8503101f6404030710f108800d828101003007031800508208804c0002403c02c691200800c0f0001e000b04141c4000e1640001100d0302c42881d40300c0d81d100c090341407000b68000b956103103101a00b10b190041960560f90805100d0070b15a040004d01801c54149454480d103440d0b03244000503400e01244036034070000c01d2a03800b4000500b04001c003502d0038220810380c0403220000305401c0150380301c400e048408590b482040031440d403603e401c100500307001039440324103c3d003d48100c0340450245c810044c030180004490821100c500d5400c40261070040d030041100c0f11500b00101c44642c64100861314600366804d0f2040800c0e00385020324070080e00800300c511071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 701296492 1250 701295242 701295251
    0x2030a122a02040c030e0c0d1103070303030b030c090705120c040e01140a08010e0a0b04020307031211011406010507061a10090509240d0f050a080a0206060904080d0c051b01 76
    0x110328144c05a25500c02007858144000795214140d113440d45411a540c0c1c1c820058010207008024401402d24000200103003038500003035480c1000350141044010086c42401103c140a00d5458001c1c11103004500079a03403079013840c02c246207100e001080a00f101520560030304c00003034092001c0c01220301800c0445840c00c1c071001c00c0e41c148101d00c9182e80081040d07906214950b00241d2000645012140c2c0180074884030361030b5030002c6410519180c101400740c150000c0c010359601c1c0c100c3c0099021907030b000d000300405c6940d690800d2071010150741c0680014020031603c004519550004120850b001c000d1a40c1340019400007440024160140d001048035840d0400007458800b5465905c581280301c1030903110040810300f01640088044148074118200e4000140036502d00e90b115642d07400001c0300c114608a040c400b8554000300c24490051250000094117401e00c9043c450107580e100c402c0d01c0c20920042c803408d000d003980105040810109001d01244030315440c191102c680f10180c000036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 701297742 1250 701296492 701296577
    0x20f0703080a1206030215130306020703031b2328121103010530060c071103152a070c0303090812030105040b0a08060702010e070f0302030a12 63
    0x70aa443c001107a80c151500e0110108003507120329083d02950025003140554502d510705182d6800340054102405447c4042840c00030140c041d4458040809008032816040900c0c0c0021a002c4551152424004110305004400802c01368090b128410400c0e400307402c01400c48042070200b540c5041d00500180102d414a04030345490710030790380c13250382100c400351440d030600d004100b58900f110140c40801c0740800d010340d44105014150741c01421004103803001e0b07051010310300d0110f8112060680b212404440c1e04c0c01e0b6883c0004203000700e41507810410084c1d50382c401c1c213030031079928000b01c8103d00c0081c26604500400c40d42c1c000c0145920075a0a604131074114180144082a42e8103d0982940403c0c0c42c02c0c00c040c003401c12b50703044800c212404155513400e075012501d1600b40e5402842c0d40e100e48024444200c2d019000900200c544104403a05c15a980d0038000c003404117407101a4041c3c11504412000c0380b07880302e242d44100e0450800801c41501c12110040b580a28a61111461495190032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 701298992 1250 701297742 701297747
    0x30405010c0e04060e011a040b0d0f0513050d0810080d0207030b07020303060a210204020d092f0103022d0a1d010f0c03140c150a0c02030702010f020f0703080a 70
    0x181070316420349007000351078204141c130070f4034107010300800600020714140303c47e00401d902c0854024001903c0344c6901e58030041c6821010300342031000300b4913043c02d103400640e6822a18030114101500003000b45807410700080241c54181000e80100c40102e629000842d940350200203c1b9040482a4014a052813450404410b4200c02070485011134008005105a5996481007013042d039a540303407000c00c0c41d42c910b22200011012840000d411600108040c1c0040b0041c0e440403034068040c1905260f83e0210348a82c2199807003d81106078440020383c0c0034855544258068040e03101c0e0040401c484840d202c01a4481580420360003000d940b0015950008980c0300b4001702a0800e5400720b000d002e8003910010300100e440c003d51070100041c00b60362900b80341c8507800080074071182500042c1e41d01c0001080340c2d154100d0703918040032a10b50602003152050b86207d6a40301c0051580a1410912154011904108048551303002c500c00c0e1540942245418410900258800c2d4041503486600c00d001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 701300242 1250 701298992 701299007
    0x15030c06110f0105040b07260c0306010f020c061c0603020901030f030f09050a0e070e10091518091d0d120b011e03050c0417010c03053117030405010c 66
    0x1038801c1c0f80d0420301800001504280da054115a10703080c0409444104040c4140784940d901301088011840703420b11040b0f0402c0f0000354010340d400c0c0d81e103010542c44110240d030f071182900c60300c0b60840d20400844110032503500c1b00944240c5102d2000c100e2660305e030001128003a007030f001a60394182001c100002c0513003000c0c0001300301e02e030350911440311458000002c681d0300b024032442e8980440d07a4006495207204a81c044540e4100a01c1158500c810407002810403483c2d00500a0300410003d00002c07260103504111031941d8801d43c1e0305012810001d940e00900000f2014a9010304000c40501402005014001c8010100e640300e0320107142207030b1030310185d640992019062003038030454230301e0290702d104210344205100d00380824207451b000700e84042445250703c00c1441284060f0013614609064200c07084001d000c0e9420321464460308031121000300c80308a144407a008420300030404e040f501701e50581507401036401000102e601c074a058084e0f401200c04030f400740d655241d2500b0a5801006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 701301492 1250 701300242 701300263
    0x10905010e0403020c090c040305011e061719030207053706050306040b1219110303030c2502040915110315010c080403020a081c02030708090415030c0611 68
    0x9000c107041a44019480d82c1e944451740707000301a20320003c0c0c01b01003010100d0b00150b43c013200812201135103049144041e41c06000c500c0c03140d410f01e400021f0043d0212004554145900701614100b40034014158a244d000001203066024542000074565100341c001c5140b8064038007a90464010444262250003440e440d00c03500701c0c7c540300c040c89419401825a40c0c449425100002e004510100060301910b000b910f04a00703108560410100205000c0d004800c14441c1c0e40d00240d10f14107108050310b900085074445c0d0b100d502403000c5801a0452221000c2d038800c9054240011120340d00460240e520480c0c0a0324461210109155401071038400d05602302c02445002c0c2c20750404441300c9883c0b501d100c1410341080102d803501000e00959104840046900030060300030281d0741d445180d190641d050391641051800d41c60f19041d28000f0048501e6154041d40306844e1a280c1e4007040024107103000c52105241c402c89d008000150708400360340c054250340d10307a48802203010561500e0b1200204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 701302742 1250 701301492 701301509
    0x903070c0501020607090b090411041401020c1008070f030615031a0919020a27031202160e0a092a06140702040203060d060204231806041806060306020301090501 71
    0x30010b85d01e80c003200c0d500c1580c0004800702c0c0d032242003100150103022821200c840d8030300000b90014004d24013290501c80e8031000c1e0203840f02080070300b0030481401c02d052a140301041c1001c0001e01d126218414000820445080024201d5110b500c400200400d108084002c031390781b80c0385440302580703c440341c200005085640304098035041007044090ba81c0243c100300459004a51234004901800d80c502182c500c00c455600c1d08011a50100b04902d030701e120a50f00c0180d420081c6c000c2c00d20100f072992001c0a146603808080b4540390031262422002040b40b0b0030070341d80300c00000000d00d045440c1c4220fa105010b40d40904120141c04114421850340128141312042d03100e440000c0170f410544808640403640141c40c6e994010120b40c4103110140c008040c1440000c01195031041c407856411416039002c40312150608400070b00c08072980c501040c2d44100c0030b600000d4601d24045e001807110a00c00171004c00300b0041650f84000741c075000c1c2c10445456401100501800741da130702c01c2500511000c2e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 701303992 1250 701302742 701302753
    0xc27131a01142809150e0a09060e031204020f0d02030d0c060501052e020c0607120e010305090303150316090605030607030c08040b04060b060711181e090f01050903070c050102 77
    0x80303c05850300c4551013500c0086031542d000d12040d1940d090700c040105032a4802624500d083c030700b500d00400801d1011980203140040d00c400c501000001d03951460441e9031071311596115602040340821140f441c4503444607500703441c1e00040e00c0601070700c141a1142c0d243d68000001070300c1e100060710390580026014202900301c80310300c0f06001d50541445000580c03011602758000c0700490501031407800d00d0b0f4000d840007402c007080281e00c40042d40c00c10070301d07554018040c0c01380b001102540e5064996003455801400400c03034240d0741919040030b03080000d00f100d86a108410f44a00104001c0e80051882c42e500d100c02c00283c2820b000551307100301103180401944400030710250603558003600103015154048009170821600e07900c071070b5555500401e110740301ca03520301d001c460308001c0341e008e05d00a100a40c403040c81034110070310315805042e000c008082e20411080c02e9808003030005101d10154400d46d5090344255000b8816103010703441003009180e6230102820100c4000c1c589900044c1194880c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 701305242 1250 701303992 701304049
    0x20f0102010e15040503090a18140403141810090504180209010303051e19030c1d04090326250f0516020406080c27131a0114 55
    0xf050001d1021140c00050601c2c0d1141c0c28034078910300420f15426001f4001107004158100c8400c22110b050540007414007607040c03c10480c8030600c2058a004000c035010b407031b4140e14080ca51000d400c14000410014543d2141ea030300064214040b15800d0f00800d0004406010600301802518428a0300c140312040c7ca1881c0d6000c110341001c144400760070440c0100d9000b841c0c003041611008490842094952074606225800303091000d00c03030180011901d031101c00386005000c0d1a0006035212200051411a881d400611010740381e44003044040048200001500034a030311a07080401111f51941403951821030307450a041c1c0500d0010040030036030300300e5412080340e12041040c3d10303000e035242190702c40031074501c104d258020920340294828102040866403000001c5d2803002ca50046420350281921b003280351900b07203109003106d0b200054060000d070000c00010f210103a002e1040c10403019041040a0082048400783c1101c0300700700480d19103400728a06514104013905000b110120705480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 701306492 1250 701305242 701305271
    0xc180603080a0c0507080d0302030114030604050705011202070215030405240402041802031b010e010507050a110d0506040b010501021203071704080f0f1b0102190509220504020f010201 81
    0x5248104820000f0100b484010044d00f80107080091456100701d403007181004002402a40090161340212441e55031099024640011603d0040b900310026203055420440111600c482c00c03c01481042e03000c210100050304d50880c0500c8009545040d65124207180c6042814080750620003403040d03002d01410407a039025508010381055040341c0001e0403802204400e6054101020040d5143c000c0c0000800000319030300314514500800d90351910b01c0d5803c2d0006403414023840328007a205512002c940c0000846041d08540b2a00005040f120441e085580c4d0616040044404849007101c040041225580401800c00c0c440300482d25a4103500d051080203101d070114014a18800400801103414020f4600c2219154180280790b43e6468000c0c642c1c0810760342c40742c00444102041440043d0910031706100340c0d550300d40c0c0d03840310b80310142d042e01088540b5000904042c1c2d003c02000414a005882005650310303420039800c01040b0351071300b401082040003c5160083c15641003551090300b084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 701307742 1250 701306492 701306497
    0xc090501030b1501030f05040506040201200d050d0e0f0a06050c040e04030c0609062318030a110309060310050f0328080c060702060115020d0212090f0d0c18060308 72
    0x50f01032214040000b01c2c00100c0c050800300045500e4540780006000520001050b10303403003075000381c03140c90380a2460361700d49188111a181d880443e421410710b0207403140c8203100929140d00001c4001c10405040d8490130f0030540101000100c580c0a0341710789007000314034004c40ea400181403072031030b080500d806035a21003c0340090004042094100ba990104030ba107030311129409800c04420054419125030240140b40440c9010300881031070000680410380c140d00d15a41d4561400165091100c04c01d4159583c42034400000244e00042c00503402ca0b4441001440c402c02041503e440030f140f40005014803030440340384c0c0500940000250417102c000121160345c0c92400314524680c070300c0782401c110000b4000c0107500034a6020719001d010000354001071080c162241e148407090503c260b00c0e030603a510700c0c9420603036025270810004840e088002e03502801300d04401901e103403114441400041c405400c0074808440c48107002d8400d000c0d145180480c07403202c8803246000c00c241030031500c07070304c4850 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 701308992 1250 701307742 701307751
    0xc07090c020a0311100504050304170604150903050c01021201051005090a18090506040c080f070f35100e160506031e0108061e060f0d110a0b04030c090501030b 70
    0xc10326413500507104104000042c0e1a12581c042041241024500640c0b40c0d81300388180d200508164500380110140801c0c490301895001350031200e00802c413036000f0060085800203809100d001e100c0703041161400c2c00181a85003008251504543c1070100300a5030014071600c1c2d000b001814024034849456152400c410745040580c22030050f01082e0f911005001d25070b030010140d004040134002041103982041c410754078484251152078201c010b04690340d43c558402c0021100c940302c0100120007036404c002d0201101300b000c4414105102400c28420f2020424a0342e46901c000300e41861038841d481000070011000001d0490031b485000c8030b075180c80c071034006d8034070901001010405c420610000c20702c5403449000700301c1080da900d49255490790811259240e4980d03540c1401c009140c5941c0c2c411384901401051103c00107000804c2c440040b94640c001c4030741c01c8540342000390710750325803445030700502c0359104c166651410b500c0d140b091126607501c070700c030260304000041c40000e8070300e804694070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 701310242 1250 701308992 701308997
    0x140f0417071d100e04051e1213080705040e0307030305060103110a0c11060a2a060e0a060f06060813021207080c03010e010c2304121110080606180a030c09020c07090c020a03 76
    0xb20f141b00500d080c141c007010058000390700003c4040b903a040c201509c01c00c03212203200340d0b40c22569440c1801f040e034041c1118001c2e103030070030032007080040e01941c840380d040203040c50000b0300f8010b00c0c83c5090b020342c00382d00101c021900445680c010007540000140511005460560614014120241800440e500a00320407106083c0e0301c0d1080b4104500006100c0e04940c0512054840c0101d41d503c0390790508007900d80c181440e4442c1e104030028042c18040344d48541c1c42c078045a440104140039080c2c060310490740300e00b0001515096050810040b40030304850030185c40300c00030388070816085942081c4190303c0c0f6410324581c80740542d000205005400f00124040750f40c110400881c2c51984200c0d0454403002802c200c521080c44031031420080c2d40e8005071840760740a11411000e880114007196060390112041001d54001c0004810803905004003404d005006500d80d510261502c215820042015502055031300b10900100700d600e00912201720b0410a011050100949400c2440c00c05010f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 701311492 1250 701310242 701310283
    0x90f0c05100e062a1204061b1109130b09100c0201090f0809180a050a0f021219020c01051302030105010f03050d03230403020d140f0417071d100e0405 66
    0x42c01045842c0350010b0304841d0156403d01c03442d18400101741d0402c2c02034100180002c004005e540c20880070341801e05401c0050706400d00c5100c0104004000014015140109910072960004402d078034054095918140549000e000f4806044201c44010030201d0441e81010801d00102e40b6004050540c00c4d0080d9035143c1c1c445000010a290310900b070801d5404501841c10400c420f400303544258010040d101c2e05200e4883c21045d640141c0c09010207030402d01083c9c801040424181803d481c0302462060320240c101018003120b46d085500c102c3d02e42c1c0c44038408140d103c08600e4288101800342840c4d81000070001c1c15030b114107036a010310720700e0201030503558080f00140c242a1051070007007004000c0189014901032070001c1d180d15081b070014012074500c280f104100179441003611000010200c24a007005d02e0404050080713090a1000d00380390284805c00b180291464010304803481081506041c00e0500300c441d40180e2006600c054004025402444000b0754007043d200d0f594500c0d006403c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 701312742 1250 701311492 701311537
    0x6030c070206030106031b110303060907030f0f050114180a0b1c050a0506101401030906020405060703051306050403020f090615030a0938040303090f0c05100e06 71
    0x210310800c00041d610a4001c40006145545a003152a00c602c1a40b80d8000d01c80390721200baa0055005410030000341c2003800040d6003802c020849561181e494035010880210503401201150f4004015105107a200d80040c042ca030542107a02c0c0700000269072214086c28030700b036854041c4401401d125810b640350003030b01000395503400b80e000b1a20741700ca0016009070490701e042139036007508040445c0c407400b46070b000030800c602c821000c000700c0307055150100c8149200c0300110000e02801508641c0c1c07960030301c004030b0a6184c65012b000c07500c1c40b9807078407540c0c0d0800204542001c48164417a80800104001c14001a1164031011018107403e854100d110389a00001070b0b5403000400005840201c08020000c4909581c3c0140c0d4901e4000c075a0380da402c5c40840d4202810a0100d110302d00641d101c150846d00c900303428901540e0290107841c000a8103465640e800403244c0e0788000c150b684040300f40060010340740c02003028901810504100e100e42c0d18101c0818000c1c02040c007a03800e916400070842 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 701313992 1250 701312742 701312761
    0x3080a0c1506060305071707050c03040801050106050319060f0b0d0f090822030b040f141605090105030a0b0f06030c040207050303041e15110d0e010b0301050c0f04050603 75
    0xa0340d0241d10116444800c1035500404000b4102032144000190414000c01d000d01e0040603200d2041140c0351049080e0b0369040e0301600c481c1d00203d0180c00e144030811001491507020700c1414042c206035524682e40b41001600354082490f14201311002c5481d0020420003036140e40748200407a040781499076143d85c0709908800080406d980b07428006c9003000902c0040005210007440f2100c01c3d094100943c14000301c171200038012501005010410510104001c0740c041c81c0c003110f00070b11030001c07046000c02c502c020505040803883c1c0c92409541d141414030540c6022403016000d080c05500400d11008161200942500007501407058a10003038003160b01d540701070001006840010744295900c0e26207141c0155227510444054a1800001d4442d0040580031030300e205003641c01400b0880445051890307280200702c2c80742c030450481010000c4148031116409400b20b0440101d00000e840000c0005041c2075900051003402c01c0e290410810200c09078802c2960190742050f9200c0d51642e4481012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 701315242 1250 701313992 701314007
    0x50d020a03051b1e1315050a141318030c060e0a0b0402090105040902013e0f0f030c150a09020612010f0e04080a0f0905040c020d0306080d05030103080a 67
    0x80c0c0309003d1160f00f04046200c0f94000f1501241c03c1e10003081107409814144151410700c1d6966a001c2100d94208010800303541003003c0c00000500c43c3c0c10700955800c0020b200c51056403000d000c12590036203034180c0e4502842802c02140482070b05002220b01108920f0346104406c0c3c1c01404c0c0104038140c0c0080c000d00d60310544041d120b007802c441011002d41000250340030102c508031300c14182d0600118581c2054000c001c2c2a95040c0c561000c2d1190169103140c0524405412000304d0209103c403d03a442900d8040c2502c035400302c805041c0d2440b02480c42c40c1000045045c00038941d1003009023926405000402802e0350318500b1660003030f61903543c09603001e01605103000e58000c501042c0000c00b03c200c00b12041c12541c03030124200255a403507030001c3c00c0d41d1080702d02501200e0b09000e07038100300d400303480521000c480d50700d44848000d803694000340448030b003041000010313032204031080061901885100003422044000307000c00b695150000744184070500009100c0c0e6000310b041c400031401601c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 701316492 1250 701315242 701315249
    0x41101180e1305010b0d030905010c06200703030f060b040b0a050d0c1e090608060405060f04050420090f15030f030706050a0501090b090723160c0f0b04050d020a 71
    0x894030414208404402c500310b0550301c0c156120f501e00b1445c64120b143c0340c42554441641a1140c4030a00d00d40401521070049420040d82d00f0358450007100b06024040b5007100c10301c3e02030445c49441e4051030038014101d86811030402c07022454000244000900c5c03909842c103c1c0e5000c00c2c0c044d50781c00900012641c6025450840303c0d11800c0c51305403080b45400556030840c65003010010107840c2c00184044800749018420f00001c10003140c04a4141c1c28190040703a40400041d00703540d1945c800001003801c441003114266000180c24100101c0d48060920064a2a40840c1c3c404001e04080009820500b000303840d26141c400c4400c19060251014010300f1116012401a25214011405d010700075010440341818814a81000070411001c20300c22005040c03030117040510390356911038055526018013407000d114072803400030811010540500500e803101e0441302215290045181c00540706001d5004003903241003240d0184002d174100d80a4030100c8508980080071007081c0e00124614581030740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 701317742 1250 701316492 701316509
    0x31f02160f0203120a080412091d06100518060c0f070b07112706031608010218060307022a09161e0905040902040f0207050706030e0604110118 63
    0x203601404129542040207500079403e45520b5100520208064403e45203030702c000c2a191400308002ca04403860b01c88401c0f40509118500c80d49402e5050803070840e0040c10b4101d981d0f00010466142080d0351040b050080f6410098101442c4042c85824140c800301ca0f103014010210711042024010010344460041240541e15036540f03c0780b14411582c407003031060302c900c04903881c181100d0414a80c03c0c01015212510300a0301c1400e11a91019000050401e560601c940c01c1915000710308114914001d0104a0005a0321101803000f0038000803042c1e042e61040006108100c0215004159407040264040009080c80030022228214482900f601d41d00074410208001c0c03409620340e42c00100154688130300c03806a0007d2000880300307258208200010303401001c10402070400303401c10006507200510114000d41c42c40c4145c801ca030815007040c5c1d8a5444040200409a0940f09000c89400420090800ca1074140c9070460880c142522140c100014200105c0303074100600c08800c041c06081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 701318992 1250 701317742 701317777
    0x1b0b0403120501050102060f040206211f09060b0405120f0114060306060f01051903060302040f0c08070c230a0233030f06010315080d08040b1302031f02 67
    0x1030600400d48280040c41c4403445203448004100f56000040940c45900d00340c92a00243d42c0d42c1d428801c16030419890100c0081126400441f1016403a0201d03100e200030008808040c1a09030300d08010b485103521101c80d140c41d0200c00e2205c0b2214804440c25a80142c0d6543c5c0740060f0368422520b008140000000382d946840703101603030200d9124140b80517203821022210f035510f81d02e0030003001c04008a84076003c00c0040104050140c216010107d9202d054100015910f41e0303500494203030b80740740140c000c00b036695640c3c0020a07600409581e03002030262401d003c1091035070f600c11505264140911104201e100d40c1d0201801c001c005400c003091380600300c1c0e54450f4005c0030540340b800c0f1b41000f55950248034102c044ca500001c000b13407445092005440c9400c3d07111900150020031454021040c940081d48012034003a0080000c0ca8a40c1c00b2603a4001052500d401c00c3c5840b036101502303503c2c084d11024281000740e907001a11501d6044c0c00b06c810103505c41900759980080c0b080b03000700f02114228 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 701320242 1250 701318992 701319001
    0xc02010513140901051c03030e1905070314030c03090f060405121c0c02010e040b0d0506011e120503190e15040e0a050906070e0402040e090303090f0106151b0b 70
    0x50b01c1c031a401c0d55030a581502c0540d0b2030340d04011b0111140d002c0c000d82100d0000806010074400d4104014914590050b0b070718418024007180c0d021004d9181c295400e6010907010400c202c0403200e850603407003120000e141443c01015a4588038400c400035540300d000201d0301c0302202ea803214101c40c000c00f0000d0810038110a0300350781d1074440768103403020f01d10b002159208515190140520185d003032f0f4142d441c0300e20300f00301508000081c5206008103410240015406002807401c00585010340f00010503842d203143e00280404c085241c03030b00316a441410f03c140010000d08004155100c0300a0b480441c803204c4498501100ea0b0f012034540c850340300f0020b03074003181c6900a0320020820384950070007040c41965100368280540c0c000791600c8540c0e03400403000941c2c0511610b00d41401a00040c8003500d010b5480c410401840c006450752140c030340002050160000040056a0300c950043c4001d000701850801c50a50b403808804a1009008096032090450030760700d0f0541d01e00c41d50100c8907040b02c1c00c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 701321492 1250 701320242 701320259
    0x911060c010b090c1606050406090204050c1207021204063b011202070809100e041a010f1103090d1b0801050106090f050d02011b3513060c02010513 65
    0x4501d00b50074054141d070f4000c20250780c050411280d0300280ea14181c0054940c03030b592400200001441660401e40e0b0f04002001603446015003402011141401d98507003400c46503c2c0c120180203840c0760709540c00340844100c0e5141e0700007941c040300d80500704002031403d551a20705211862408907410040a0b4000404008450704078040b410402c2e0388508580303071300a5043e001c030322410902400c5c2c0502030064140c03074900001c0712140c0c1c0b0510f14003951446c21000103d0b0a9a82078045030482d048602d166aa01e9640304c0610221001c00e0f161900c00d220410714500c1e16803240b07880741c60003500346400d05001e0009149452203051184004462101c3d079407034405000305003e011302c00004011400014100c12940009001d50303500401c103c044540300d5006444039211090502990444854900b0120301c030b420000159040d103204968114194440444100c5142c002c0c02104035014009007854007007203814a4151048c0e0700701003030401c00a0005035101d000f07405880720700d0a5040d601285805 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 701322742 1250 701321492 701321501
    0xf110a0b09060a06290c16141201050709091a0d21050c030901080714070b071101061d2e09111c09060e07170d031107060911060c01 58
    0x943d03070008008041d150040c0114690400f0341c0160201c0c41c0036204250a11602d0051140010440446040c1c40d640300c0b40ea50f05103210b6224244c036914000440e24113040441454a800f09400001c105d245013812002d411440b8500590042c80c0d42c417401c0072050b0b0001403c800d0754010041402c6100308807032030001e6007542d001c0100d000c0300c13503826100c0c42154012015502c804181c4000365003030408010045451030001402c0100700001e0140069002c07007068020806903000c0c0d400500c03140741c0742c0d002618030312044070284003507071400004000c0303400090180004001c0c27034800e15043da00d40244408a80d0b03a411714114940c0009258502c0426041d403850701190160358007840140000381a9055030b0103000d17900c0640100300480040390030920743c0303d184000c3c49036200090a80e40c0e6000240350003000e41050034214030b807400603150082d04205014204140b464203129505202d8541c8120780140c050040c40c441c0c4410702c0d40d01304500301076502c0364000c001e0012621104042000341c041d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 701323992 1250 701322742 701322751
    0x411041d010b070803090a0609050f0111160f050a0b1003140d0f05070c0b0307030f05090714061b060c0301061715011110020f03040c12030f110a0b0906 67
    0x81900309141101903031103509504851050a8560819050740c90b401810b41c001082c1c41c030a40101c00d0440c00007180d5100b40c1c0b403401c0c0103500030003400f1f0b2075880c45421110000c4072585404400e204e0001c1c43c03020a50300d110016804030110180000c940f4110345043c801000080604d0080800c101408880401840c00c490042d00001d0176428901c54903911556081010b03400520165802000076008400034403026100c2c01d2400d1580740d85844114a54000351440d9000135200e5000481250741e60082e40c1e004000c88000c0d010aa1801c0412281100c2809106004010104000d1100b0010a0075050601a808151843e40c64205108a000c0d4801d00a990204801400300090000c1581e400e03403107107000b1050890380050041c010340d02903c20451658480c030030740040e900345e03410030300141044000303c8910304c1c2c4a05040c58610002040c941010121440d0300c000d0b10082580510485e8010003175040411600c0030449070310382007080d0010094404404082401600100010780c103118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 701325242 1250 701323992 701324009
    0x2070302070b0903060106140909070305100f05030307030f09090606090306050703140f270f12071a3301090807030c090e0102120403050d181a04030e041104 69
    0x2103940b01c0c5101c0c1c01d5806a0260240c165000c0001440203500882100c06488142c0d10110700300803103c030004000540c101c0c0c41500103602c8106000301680000b980300054103004079a48103031418040441d65901404602a041140e1182c158680342c0c0600000809004010000d2000f6a03c91101800a610304e00c800c5905038030304000210194070901c0f40031040003c00b0000780c0607032202142040040740103008280302c00010300040366011101c0c402d4008000000000c0c102c15095400101d00308a020124083d100004010000001c0c54284059502c848445614041c648072000d80c1013109031052900c1032202120b040587c5080314008503115a910240daa1010280c0c8031440d1545400382440014a6860b01c10024031000456820264841c48800001401d01480c54814101d01000b6102900442c0c170004070f4400710840d50080120403008142955082e00f00e9984907020b581c03a071a484031404411030003040405215400303a444210f00140140100100101444841d07031181c40f50300744 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 701326492 1250 701325242 701325253
    0x50411010c11090604021c050f07020a03090e040302011803030f0e0111121317030108100c1b1a0705041706061507030c0c03080a030b09010302030c040213090f02070302 74
    0x61540c440c01c0d2030310401c1e0307018a52148291903070042c400c0b01c12018150300c0d4450780030312410b49581c40c5901c90b2602c2d051707002400300703440c140700c42c00c16102040500b1030011500800014004a030b00060a0012111800076000c042c1c0e8031410201d0040020f00b424980f44c00700d42c0b001505142e85074000d400c61b000284810004068025042030807107446401d1608800000d0080268041d903c0c0469544503210541000e001d600d00d5845c8518401c201b042c0d10300c40da20100051051807c1008890308403840223a040008042c19030018154000182d007003c02040000400c5041022206c589a4881d40075860b086842c2021172010700700b50040e01400f08258840440e1700d0402c500001c1c0c003400364601610b513002034240b2034410078066000300d1040c0d0500840400c4070002801e1800f100e80198002c140d000e0302c0c0c0d0075400d4010142c440c030701c0324034ac17180880000500159074085980903000c1e00403a0016a19403545004c0c00308103025a200f41709840c600043c0e0420781c4120703001000442c0c800c2d42943e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 701327742 1250 701326492 701326523
    0x11010305100509071b080304030503010e0903031312020109051c03110304080904110421120c0201300f0c1b030509060a14070309081b031213080708010504 68
    0x2860450911aa5030f00540600c00300d114a8010410140c000c54561260070404540d5101ca0f13105038010740701200003c0000004110400d00494000e810a00040140d4654142202d1101c404081d5501c0600007a9036640c10048450007540310043c21503200b0180c1725154861010116450000a880c0001c00d00f481355107030b40580000704580c402e9a224140e20b0402e65a10103100c000e20000130381c1411180100400300e2a0b000381c0d001504d01c00f00f1314603444481c607840d00d890035107403840150000a0160390840500140c0e0441c1461030340800c2e20b40c0c1c581141c0605200c1c031103225029042c4611040c5841c0401501e8002e0303812500071540ca03074403103406001130880d0480d0308844d00308019002501c01d010242e12441d040004001240280c41d100607030415207680855194030086044000c04c021002c00c20107928140525100380745e68518405126450001003500c42c566004401781400c80060340c0c044403000e040700000604484000c886c207083d101c1c10180e009103419102034030405010011071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 701328992 1250 701327742 701327761
    0x1201050a05180f0601141909020711040c1b031b0506010e0717011e032306060f030d0e0a0f03050a0b0c0a09030605060f0621090c060a140f03010311010305 68
    0xc2c3ca0300c3c000300400b0168030308008501030740542e82410b507010f0071b6102003601d00550740104401601c0542e20050341c071030780c61800e0800c6110303d001007805181080060811030790028405e2180340070660301420b62020a01d02103402c0756900101c0e80000e21284006000c1c4400003800d503040e80d080c00c3c01040280c55024090f9400381c035454040c03a8402180d00140483d202e20910070100034540c00f103004583d0307200e66a26810f217068401c4008030b02d020b052703010000502000920341040b002d5942400000d48000440d84501e000c000850a014203003562014a0716900c10303c4008021400e0003d24460f00c0b80f515a440308200c3e0780035a2131b0446800483c0d0391100e59001c640026090383c03511406a4916561030024240c004c001d03a80c404881c0402c1030058a542008140501841e4052404c0751050b103500d03c1c220f64080d207103101c60743c40502c00c041c941e01c81c001103038100807850508100100c110b0f20320000c240300d1049024031001011000008210340c410325140752143c00d0302c050049a5400c07446 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 701330242 1250 701328992 701329003
    0x10030b0f040f020d0302120a0302180a0b041707030503070605070810241205190f060506040302040207140318040c080910020d060b1801030b0901030b0f061201050a0518 74
    0x14240960800e80b8500620701040100340c400c1c42030060b1030b02d100c2841c51068007a000103c10001007600000e00c0b215041e45410040303144181121116112810994598030a01840c0102452039120000001244074104404001903030f201c1c003240d9441c0c0441c0f134590041c1c81d0a444441c0422042e401240005204554860580300e00341414040b51040c0e2028442e5040c2010303a0405002c2c1c801cac1060010f40307070750003524440c00482c01c1c0e50300c0360712440144604840e0a030021401441c83d080090065075604c0e8100d50451741c0485c0c01588552031703070404200000828403100b4042c071002a01001ca180404114280e84401f19010401d01028400596080d801101c10768159002152810090345095000d446079041d800000aa010303100c0f14a00c0701540289443c48102c00307503050758141036070705010b0b0041c03280c0b05503000b5120b9403441d038400d260220068038058103280700d240090728a84907203900c40c01c81e10a000090003e030400304840c10003400151103036901070140002d04003c0c01d0340080d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 701331492 1250 701330242 701330251
    0x60c03110a020d121b0c020312040819080c030a09090501050d020108071119060504051006080a03142502040b030f030d0506130203190f060b0304020405061810030b0f 73
    0x94151007201c3c1c0e504803140d00c040c1d1404c2034002d0f624160a02c0c001196030380c2c0c0c070f800156911640015004c0d801014070b40307100c060304074501050421060040040111300c241c00c45c4017442501c81c0c007902510707100c0c01900a00482d030020340300108880c4d841c59031140e284000c813000b080042006913282c0d82400000944400064046101d03480803410f80ba1242c410480b04416600075510000c000c402c4105032a160103006031130150b150340511092000910242c2440300803034500304540d500d80a0203503140d0048240180521458081420080144900322446c02a88400942900b5000c0c01c0380603032038005150984c002c03450301000c98105d0800103541c1c0b0500140702d00445c10b180c510000d02c0d001e020000c001c00d4000b001c840c1e610003d0316990001d540500d840225551030b02031059210801c880c001c61508900fa401e08100f0403c04e000401200d81060f016500400c095890201003101700c0c18100002c03108049a00400212141e0082d070542540d02c900418085501c4140d070318800160f0503034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 701332742 1250 701331492 701331497
    0xe1914040b0408070f05060a09020a38120c04080609011a040c12110a0f02030306060d0209030109021f091e0e061903120908061905060103020c0109060c03110a 70
    0x110780800c0c004005440c5041c4100c078076502c3e005e001e075501e80c2428429611254050b8407144444214980344050f200503107542403c0151070307501c42d00c0c4000c0010b45e94000000b1400b1418a2015240b0408200c0340000081e51260019042c509521117165202c0c2c401c58009020311000b0840400040c0a8107426500c20f00304510560120020400182000c1003a60280b21046a106860314014010040a0240c500c00c0036214203544001912448503140007108540040007080407682d0fa07141a103002c504030301d000589501d240d0b4080f038018070034100080e5001c040c2c400d026006412401c1e110480840c0d550f42d1542c0650b0364449050213003c1ca07031000401e000c44540500043c0100c8844640c040c0c0001c0001400c80560360102c404409190419190041c8031075514144641100d941402412850028009403604181d0351741c0354803032824508a00d07034840b0040b4075568401d0b016164240b40000080150700300c507150401c02001c24031030802c0424101b008100c248102c510507501d00424a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 701333992 1250 701332742 701332763
    0x6080d0e13061805040b0f011503480905060d0b0f150301050102150f0403080403090f0608061005120c070c03210e1f050706060e191404 60
    0x1808004480d03016821040072036540b100001500da20070744a905400da5111400642c90800c0c0c202000220740003000c074010311011900420240b082281900441d107060718000038060080304100c410b4400b11500c1000c9161400c078010190586049240288c00401c038118401015001060b200c2e405e00d4030a055002005001c0721800c0d21080e0084181100000e141805840692001545401d510b481070f91601b0400302c0180460b503010005a401c1c0040c1010b503808900d01501d20140050000784020704020251000c0b4082500408411010740b82c40c18110700d4441e11101e000341110001c9070100d204450200d400e00d0900d000780221805100540b4190340d09588090303115201d9800008201d808480284c400001700b03100c40060940c084405d010010000740303020009080312024040984592031400c200030ba00109070702080344104190501ca91075800d1401c000006042940c000d07114182d80c0000c0000340c0c2c00d9100d8280c003201d100d40c1c0800c10308900e01251003808108403802440007494 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 701335242 1250 701333992 701334017
    0x5090a021f1d1003020d022809060306050616170c0a0209010b280e060406050d0b0901150e030109050d09030201080703020304030912080712030617061501030203061912020406080d 79
    0x94008103031b001c100c4c020144c9000c0c2400401d2040d0040302c0078042040c041e001c0c0e107ca5050780050480001c00305490280b220b94184400174401d031003400300407600c1c9805a800c440400401c2224003088000c9084055252498514016154a0406002c174416080c030b4002043d9881d40764187c0d00460f41e149072800d03c80d800400c1d1001c060855404010034022220807981880c1d85280040010300300568460341c8403000301540301e05030780b410741c01e051103541c2c0d520042c0000004080c4201c0560300910f05190220146c90201f8014103002c038000d0014003800350302d244040e400440700c400700c1c0d200313070382d1001c51b5660400708030124041500d00900254a4100c01c00046c4080010098140e00410b81760345021813554038030030f018070311603210300100b500c0c0c940402c12071006131440164180d508024000c1490003401c0c000501105190302c80c141a40030010a401d900c07030743c84043c1d24040079034110410680b2181d03904884044020224072450400b030012a0b40c460200e0a1500c2c0c0c440c41d220440051031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 701336492 1250 701335242 701335247
    0x3160320190908032d19031d0c100507020d08070308011509090b180a050f01080d020a06180f15050a23040201110304060c290a05090a021f1d10 63
    0x400c00d070007061041c0760000c070f6140f2452000051031a1a44a46d80510000c51050041d041d80d215440d00c05100d0010814101003603008100356241c1d002c215100ca4000540d54001d0321303d405142400394020805540d01c10030003008100602c107590094a2342c407502d03a690140003203043c441a640c03100140c03404000b000320041da034201004004c0020208000c40710030003008a400b480448444449a86500c244415603010309440b9014240703001c050402c48a4408020f540d800034800010501a500d00f005064654002142c811490307014040403100480c1e0704240d030b01d10b1080b41000300c0d22442c0c2400f086008005118001181480350145019054850044002581d0090007681405a00000c1d00100030003800200050728103501e80c01d501030600c2c2041440c00614080d0003450250031688004100345620b241035101034440d43c0810556203600303a050412000799030080d0030200303201c45070a5102c4502d030720218204a075500d503060340f0301c95542007401e4181004020380080d43c03800b00508551 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 701337742 1250 701336492 701336527
    0x1060c0b04061d0309040c0f05070b0c220602070501030603020a06031a06030a150506040812130b040b040603141b0705070e16080c030601050316032019090803 70
    0x7400b60000007801401c0304800c54503c8021580340019400000700d200061400e803044040490345445d000104c000c410b4030103402803040710409494100c48000040e40c44003020700f1600742200440c403829070365650000511840703030140641c6000d4042e00d070000c21039500c81d03c11307002107a40080041c6d910034503040b400c8c1c005002a0100b004180032010801e401504d170840254010b5400c0c8100240040420400141c03503151600300364450081004100304c00003001031503210340d1111f1b85459035a07414409120010404643c00101004c10100e800160241c103100036004950081d20f0500c1004464101d0200ca03900c215000060281900390004002440f84003401403a44070344202c40001340c40c0e56040d100c01108507010303c5680c020310b28101035598800da81e00d8001640484045c21400d1510000c0c1c43c40c01f006003003000a103040d1242c0605148a904000400340c5500040351141580e1840d0750015404801c00004061800d880b41c80d1076446120034a00f15804800a1070078524041c10a00c042c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 701338992 1250 701337742 701337751
    0x2040b130c02061834030c0807080f03040e0603150106093003050f09090a0515011b0305341e0305070605040203030417061005010f080609180d020307050c040501060c0b 74
    0x2c400c0c01d0345c0c440714100011900c1026500411103d80b03003a2405103d50710701881508801a15000b030020b03c030506100000b40c0d001c0d10644a0414416691080841d2400340300250010343c48550030000035055800c11051025641e40c185000320f84a964000320400310541c0015150840d614201030003c0f82c4101d0203041d056100b140030790301d401d00c0c801c0054080001551001000c503918418046140720700314011110240a00b03244241070076007008242c1d800c2c2603280140620030000341c040b0403503260762461414002d020403131075407109501281441800030040d0494454107a40e25900c0120b50300050b600751281c2c1551039500d0502156120740161101030000c9070944402d10001c04d003161505102c54500e440d0700018081481c01c40c1c44c5000160315a804107051202c100104203410350700c0300c10300e40e00400c1500d0420494690090081d004501e40403812100d009400d00440300c01d50120080070710501501c2151448100501080101e803070038814000800c50641140740000c042e82402a0310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 701340242 1250 701338992 701339053
    0x61a0d0518010c021f0b1c0609080c0a12021b01030902030304030f080a080a02120435130b0405030a02010c11061b16081902040b130c020618 62
    0x540103120150075120000c01403c09030304580d59000c90518a0b041c021030124820781c0c24002c815620021404a4000340004111600d641092509110168000881c003990000f01180d86000d070170082c50b1643d00844084030456588014800c003103100250300068100d602e03c10b1800e0342080c01c01075000304078001e0100c2e0940003e21002000c00d482c0d503401c3c22500d000d012181c1d6282d510000c0100b10030070003840c52504a105100400460317807100c40040c0e00079400007001d44104042c1020314010114101341c1c1e142c0c3d01c8144070702c002400e118009044584001540303035042c80e0b1550086080c0d80160f00842d40c16600001884000d584500c0d0800d12450055000f110350300d14404c0071070b01d40d034011000c10303510300f0307090280c041a0081042004080e041402d03031840d0031418a140c66854010f408400c902c01920200520705561756a40002d44410300140524490410181c10501428044002c40c0c094064500040d10091070300f024045224050805441400341100f82d41c201d1b4041d0143c038461 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 701341492 1250 701340242 701340271
    0x90b030a050f15180a0f082703010c020102070b07140f1303111e01120b0a030605040210180506030a0605030f0f06010906050105031821030703061a0d05 67
    0x1190040c011061401c03035840c0078145500070021200e400f0207000c3c0c207180f1284032a19208501d01d00c0840c05500c40ca500c8444070004d4035041c00c16140a014413040c212400c14504652050316114850606100400b07400a00c88442120005d0b03080380504c00d006888920040c002825040c0f1407201181009080841c150814015000d42075007a0000721035005194802076050050003a902500211a202110300364405007482040b40108810440483d0620040154880701103000b038100d1000c1030406400031256699a081201c090b040642d41a800f5001610882c52042d201c0c2001610700410b04000c401c03003902d05001e00002e40e000401500250382c0d00c0c103010806603414807170310300b00c541002c00507e50a0100c03000300b410a00d060b030040c03803101d141c40010083c50760400185d80e8802e001d602e0001c003035645242e450f42407501401c0d084007240000d6405000c011881805036001d1101542c0030804a61240d40e9407801d140c2050b110085048180007001502000d40c00095100038080200403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 701342742 1250 701341492 701341513
    0x60b040614060c0f0f010e070b0408150601020705060c01050109050a0903080c0c10050408070b070e010e0f0303040806010b040f2102040b150309010903080a05071e091a04050f010f09090b03 83
    0x45c1854034203016a071050b51500100401880208001e50182c80c2ca40c040ca403800e0318004140741d80b04d01400c0e2088040c41d080c00010074603802840040e00412010f4500c81e590b41418507441d009110900404034010718003800b1850303900040c4941d8001d5036058807504a1922050f15440c41600540400d106510031800003c21084207030140c1402580310f40d0400c0d4940d4201d00d0b103610b944100520700c40c1042400d070b081d00300581e0700c0134902245c444103842d07a965080504000ca42540b00703a403c081010300c41c0310300004820203a100280112841c00200d40d0650b500c0c5d45183e0309138621a2095a24a0065281d2001505d030560144460450050100e400080a40b01e441d031a60030403141d002d260f0f503541c852002490f4000c50102e603c454004c10030080c6103400d460203824a0110344040f0f0b6041e950300360024000d0702a54040020f00f40014405001d107402c0c001c120020341c854043c443c0202102001400d442d4012142e64809140c6a00c031404024244405c0000a204ca05401540351140301801c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 701343992 1250 701342742 701342773
    0x92303070306050f06180c09060d0507090f090903051b031216110c10032301140a051c1104020f030a0c0e030f03030f150616060b040614060c 62
    0xc001944200c02c0810f86160000000c0f0315420b00600050107403101d42c046000141e001c202560b07004201c51b01d5a41c80760030a002240d41801040e061100091801c401e00408035042000e010403a41c0e6280c0000407603032520044010349841030303001800700f442481203003442c4000303100241c11110b031001100c4c02c0ca03540d540381c600403040030380ba07454011502c0c03080b1029041d84110601624600c3d00f00038002c01541201040d903440c88024107100305651800e038098025007104000d10901c0c50840489600c0d611450101620034400244910030383d440903000406041c034002c42000308100d43c0d010003110700c40341c17280a880c2d482c140701e13144d000341d00308080c100601900f0b001d076005d03410944000a1482c00000c01a0840c40110f0b0054429031180603070010f00c0c60008220303603100c220b0202c0c2040d60f0b10b58000196510058565055201c0c0001c60260243c070340751040d110390180a46c1c2c082c09143c02000900049074118003e4850000b00310038111001c0c00c2510040c00910100c204540340c0d0340909684 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 701345242 1250 701343992 701344003
    0x81501030e03192003071217010e0a05280905030910050d060501030212160c080a050c070e100302010813140708060105010509090121021002010c0210020406092303 72
    0x18103a4074030182022841440c0d100480303100000e8a400482c030b41c81303980560740784d481c02640c2e001444900004951151030b44191044846040c000001c8485542c481020440100088500c0c00000e803030540061102c00d10351180482001c13411800c0e40d40100581e10003c0908444241501c4910042104204503181d4244001364005a41c1e00e0580720340380c200402d006d4810650041e030406006001d074000e0308841c1062a5084114042942c00703c0071294426208400940030240808501141500708a0740010003054000840401e80e0302c00c584030b64602011314004e03115061010031040c8240015401881c0311900700b01044c1c0c1c186021222540d503d0250500c0d007149003110f801c078040401c80c508027001054090700003400d220741444100004117504640501c1030401512011400308044000e5220240f403003a000f40040c40f1041000d840640030380a2000f240005200c0c1100e41d00d011116407082e01c090380c40300c0d928101e41503d084c1c000720030b180f00800c0c52507114042d0205d161055408208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 701346492 1250 701345242 701345257
    0x4020f0f1f0201062108040519050409080a020c151e040e0108010b0109080102030c0d05060d051005070207050910060e06130806060120060609180703050c0a0f06081501030e03 77
    0x1041084c14041441507501d101584285005c00d80a0050001901c80c026101910420b55181001103071280503d00064103d900854215141444080074400440001d080280030341d0201d510441d80301040c841086010a81103030b682c0b6050046c2d1881c0440b0070120b02ea044012420340b4185501d821002812840a0b03215214031303991043c0548155822130130703940041200000031829845c29480010151242d07201d420b9000740d8441c0014401c3d80c940000c2c1000036006004c603901101c00394462001850151200c101511460100044c18a40040e03860310448412104901041c60f01809480941e50200c003580e00040c28010345e000541c0c120080c01c0100f40f048001c0c1404d0038648005404c11649101604817245030702c011020005d07000642c1900a1000d99080d001a0365100b8003010003c464030440b5101d0007817000c0001170000c0046c194603454012105080d20658501d2401c0c5180c84510800c400714140d10002030003600c1c00c0021400c5000706060104021510700c0400342190700000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 701347742 1250 701346492 701346497
    0x6090316081e07050123160c090c05160f0f0804030c05010509061c020f1c1d060a0e0a06090803100503010e07050607060204031e11010804020f0f1f 65
    0x66040114440402415a08202d02c0d4100d14882825a002c99200e180e6401003a06011140300031010241025440711184900c0d1800a07071560300390300101040101014003551000d40790400440c50f44880d05c140c42245416458007032070131104090324103850411a00039209445482d4080c004209446141c0c9640c51003403030300f240d0311415440c2c5000204107070303088903042010505c10040e01c4d464030030803160300b10310301e0500c0d01e02c040090203000c02900c01d02c2c5008106640114064a0400b442c074410740515445e5032041c802c8084101140c05a0007502d680c02c080307580140081200c031580382d0700030401418054191059001c1030340320702d02503503030003441125000f0700042002450043d072150b00d0082c010480c000e00c000300518080ba6034612890191a00c2803500050b000200700d01e6904850045611560300d140b0f4441d40096484045513280090340c9890402201c03113110f620408400c1d1255600400240c4d145060509111800c41c0180010750040d1404551480740d01e00c03c0f01610b83d401c11075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 701348992 1250 701347742 701347783
    0xc010507051b010c052a03220515040b0a09030b1e1b0406030e28171c05181e0f011b030902030a0b01030c0e181b060903 53
    0x94101a00c0c2e00c0d100c0321020300e00d0f4501440758032950751200848605e00442814807a41c03009031040190040e4a40c4030720082c0744000034104480740c4000b03030541c005500d0108a00403003070781c600c14010382e00010000d000729584100002c0c01218a484c000d401c0c001c2e011700e00746c1d000540ba5615400c050307105883d0f0186102d0200f03031040001103411652a07000489500304050200c1507540a1814010b90044805040c1c0310700080135400340402070b0200c0c0d500d10146000c00b5140c1445814a80494080e0646048141c0c118107032424124008461006003460f091042c20b0a0342c2c00c01c9801088050040410356840d001c0b0600341001c1013013169600190040d00046403805007103014944586841c030103203541d0420203070703005129141100350119140c908021038101400e01c0024207050700b50030700030000c0855100200510024075010b0040d80c40400c083e15098581c01b02000b414542140d5034840c031760140b46152003100d40c410b07001c083d002c0e0140c040380c10102801700090405c0781d00c2c1c1440403102d83d407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 701350242 1250 701348992 701349007
    0x5070312050d0e0a020d0201030b0f031e0c060f0a0e0f060c10050a15151704050705030d030e0307060c1404060e0f0a050d0f08190807201009080c01050705 68
    0x503214410340301c0c440f40d0080201024541c04102200e80902e0081c1c1030650300c4c3d51283e084e40320b071904600070b05001010380b500307000714403210300070000d1085020510384140d9800d0307203180c242003040320314100b20022220308011071440101da841d84550f86843e00004040031800446e15500c3c00350505050b00806401006000b00c0603100b1180001d0001001c51304002c0c049001c3c045140440050b07504140040c88120355a01045c0c8600b0354400d02103028504190402c824080c0201c1c450040c1d510840a940d111038502600700c0580c2c2031040710080300c0c1c00c1004201f0010f84190300c01c1e809507000c0e003800701981e8202c94486200f90405e52004010400d066004c0b15140f03070031004051400c1c0103c0d4001c440c03604010100d012806015801407091543d00c0141c4280800042525020303240304003944c010b001072100003000c042055403c0d0012468207035003012148080400101c504d5200801040e100b900c444c01c20014123905082900c51540c1048018100c4401b8003500c0d1052200303071075890380d4581c2e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 701351492 1250 701350242 701350267
    0x501110a121401050a0b0706090203150106020114100e060a0b0a0c02030610030f0f0807021009140307060503070c1406070903020a09020405131d0f0d110105010503070306090507031205 81
    0xd400710362000b40c031002c1c010711060b922070749080103a4500c1d20096407030721030700d1070800010009164040d44c184180c040c200031540300901624162010b40d8001d1190750522030136000000003d9402c0101c00b045041d060007010700c0c05800650001c001044207444550f01e20741032801f548070b56004400175030703102c02c01810f60508010a5801032030259002802c5403441d2144c2c900c5920900c4000d00030098800b000b403d205c1c02105440d40c054008124004c865502ca00181c180c40e5176120307440f02e10030180d8040a46140100b038050840c1d4858541503e513a031001000c0f0303244101c41d1012944404e080305240300b092010030401c4e10402e0151a80c01d00d07641540104240c41d04250301200005004020a021544800b6110017101c40a0036010580c60204c0b0801240c4012104048403588100540e6a8129400090485070300070303d9150705200d01080d8031070900ba030303009004103601503010310410000586564400010f560060095500a640301d0351004260340c0f00a641d400014004600c070f482c01d0301c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 701352742 1250 701351492 701351501
    0x30e01030225121704021c081c020307080112030c02040e120d0c030e0706141305030f0a03080a020909040f0f0803010e06030d0903023726011401030b040501110a12 72
    0x11301d100d001c5401842d0545c0010000044142e1602040600d003100380c0402c00c00d41e05075010481c0c4d0f2700030a002c0d4107150903801c00940089406100048104000140d65001e50700d00100c0c17140c0642da42c03c48010940c0030701c1b01400d02070241c985d81c2d00c101c161b100540789021000d000514800c02c80400e1004213100003c059602c1e501e141c6449401104082110030b400024800c458101003452548038000900607400180751a80701503010700030071204080c04500803070030032491403094680e09981c0c0c4800c40d4400880c00340c0106590010309010101303001c107007411000c007800e510505140c0c038880300c01ea0321034202d84c100303030300c011041009a814803000345010301240340408030030b217411401d070380c5180c0014140001000c101e0700c0030300c1c240440e4401088c0714005e10b48001202161044180c3d51070145000320340702c0e150200882500100382441958041c0108001d091203101c00090f96400e42d01c3e0390380c080c0006081254250b5070303840316600b030304c26240242c003080d401c03500c99200084400360564240e5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 701353992 1250 701352742 701352767
    0x141e01090219050d061a04020a020102130918030818030a1e0314150406080102040602150108010e060f100503070e091c05030c1e0f03091504030e0103022512 69
    0x11510b8000500c990303121140d0035445203800c800082041d4040c0050440001100120140c005000080600c0ba164054000380600040503891504032540c95104500f1140201c842c03c14100d280b001881c0400e00c43d48115800018074035203200c125552801035441d6038000c948541c00300300510482c0c41c030311100e840c01c1803c640b202d0905211048514041c814a01030091943d810040c250341c4002c1e95482d030303500c48409400209c0085550307545400001c0d40c1c0316801c0d402c02c600b441910b40007054000c03060040c115400803d40081c6100d46034054029a50a030080050b16a02501000083c9640e002c206030402004211a110034904216400c1d42c104014842c140055000c1c5a0350b0b40c800941c0318044035486020921425100c0d810b0030120400301004103502102c010b0046900100c6919500040d0b018858410455040003d03100c0b6138851000115800f80c00700d800550701c482c0c0d65000b40c00801c10358440f0080c081c94540f81d00d81101290711042c0c03003038507203110160341060035071b42119802c01c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 701355242 1250 701353992 701354029
    0x50913110315130e1e0c10030204050307050111060f040201120207081207170402061b07092406050d020310150309060b030f07050607061503030c0308160c141e010902 73
    0x60010040c41c90755262002d01045041285a179032a2900310028000980003c0c4000c000c14070685c0743d010010040e4210380280c501c01d0041e11400503056010b28860a0f4044c00c1c10040e01c1c07103948500c514002c5000042c400d07410b10082480035114414580300031b1441c01c0c0b051a03100d495110610168440450040120307040c0640c0c1e030140541c00444420b0594016411504540e035191205071f030145085180b03c2c03020292080040c04101042d094228135100401d10064481d1282c903c200b400510689100b00804140100240c509002c59a0015540008100c4808001719504c01c540c0d00b4a103410342c00507000030354461b0030104001c0c2c1801201c1e00a4001c4004140c080b80d07a1031303040e860314558405c2a1241c0400607010301005000c2d0010716429480d078850900342c2d0340d2428050040c28103031070308030009640500020b80e500348040a50f407541c40c544d0b5891005084941d0350000e52001a000721686124041c0140017946d81311880d000c5085d0500c0001c146032040d03105002c207a480c0504035128 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 701356492 1250 701355242 701355251
    0x70f1203020c1f02130801050f0c070c090f0216030203090f090c0a05030604060305010603080c0d05030c09120f1902041404050327060301030303091101020d05091311031513 76
    0x9090000184010408400101200e81c2c882010500c0000f031260300c214030801045c84100180c8a01c042d40001d12500d018082500b040d40d9000e00c0302045e210740702c4014114000c04030248000c1c103c0f584110240501407000601d0002c50f81c103031410b0021199422001a0f000003070002e59810700b034000c6022104199002c070941d00b0884240c0700d00b4001e20080c68100320001c0005080c40c0d443d904000001e40d0407a000300300301c1c1c2d01d9080c01d03500c6074444000c0079400d00c600c1e0000c03854184544212403207040010f01c1203040c40031510402040d0054207000c15414071480d01c441c100c0344002e000510071059844001070340c081251041c0410b441c1d0150305110f4444841e010800072413404821a6a060006007944004020b441910711100b514020490b800c4800840003004050705588044103550103000403102040e43c3c1c100490f500c205007525040003c000740312025950821420300040d0210000000c00e000302c1c400d031202e646d600b04032100b02800001c88100030540c100b644000384103d008450070300c0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 701357742 1250 701356492 701356507
    0x2010c0c1509080412050607080f010609050d06022b110310031e1707030e0319030f02070902300f040f020a0506030a0605030705061c050714070f120302 67
    0x30160703440e910101680c5600e5169800030060550b080714040c0c80c0c00c00c9486100191030030200d544443c121619008a1882e001103001c0c0035000407294100c409581d82d0f1003110707041c0414810040094103041759001c3d001d11404400131006c3c10301d0408503100d03030501c07021006125907000c1a40d10503032224044080400c10b100c1c2200c9101020825245c1200d00d9003040d90202070310b050b0f4180ca141025100d03000c0c2c0c1036406c00400f404001071104074040d0395580e80c0c407a00c001c10146c8581800044400e90340c04e1260400000740183c107003810248030790050b0b41c0d0455803002224185c4c1e0242241ca04a00c062080700d1810242041c00fa129082200510701c0c058a04040e40b51081c3c400500017030900100c096650741195a020b14403009410042c140a4a0781080c081d204085c103018050b0300d10a00680744003042c18103003442035811035850f80707c404c2e500080b0301d503402008003c0608040300b0416180d045803498118a030090090522851900649000038140b4206522030008550101801044241e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 701358992 1250 701357742 701357753
    0x1030c020606101e0513150c110301020904090812010b1c0f0f0906050a0f0e0c0f0d05060103030c0323090f010314010f03020f2719110a02010c0c 64
    0x80360b0000301034450108038400801c090395500101c41c80c1e04080c60b51800c400c61030a500030b014041a50580350030422842d19248403e1180340070303005540009a40407151404581c01e0010105c8020000e4001031601c1c0b0054003140540321088070640348454002400700e074011605801c01d0050521410150401c01d56030018940501110b03e14000a03458005090410090303030f20500215410207070410514a044c030301a40601401c84482520740d01c0d00030820702e0400b2a000d07600c07041d50041c0207031041e00003000030440301e030060b405101c1d000510f611302500051020000e07039010350301988569401c00c10314500104028103d1004a0703e40888490708018000c601041e2100440100c0340944d00d00c11810049000b040510450a80c0f507110038000119030200c0b08003141924000e8403841240e00040f418025584104100c00c0c030790917201c804401c0341e80030b814040303600003000d60722840505100d1409907060b10110907078070302c804500092071807100740c092058400710704817030610f08000d00007601d58 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 701360242 1250 701358992 701359003
    0xf0a03141219060906090507020f28080f040603050609010807030c09050a1515120204031e050a1a0106030518100c18080309011b0b01050402072f030c01030c02 70
    0x5500340104541d0140b5800c694102c40d000d4004803400f004182e68525200c80940b109940040c0940201c0140c003680d0100403829801840801c0400c040a402000c1c5030398214034040400d61700c80c5803d11100642c1d4800600402c010107041c2e43c04141401d281c4200602804103070b1249510340d00ca40d0081000842d94099401102c1c00c510001070140d403042d24840240000320301e00b01800040031000325150903090f0081180d100301e0717911030060003a9a0511012840b4034000a00f20070760441800c0d00e00c9044000040c045880384042d50b9a8004540c3e9131341070000109000070740034140000602c15a50b0510503907900c2010b4082242e03541c034004210b00c0d01c0380e81031a002c00c01603844101d00c56006003d40c0c3c0d81e0300e0030907212001c1c020300343da68078415071250010183d1500103900d1091140c4031074200300b01c00c4010364020302c410400764038020801c0003c0d401520201d5030303e0494403a05c4031754036401000800407400e180b0b840c5034110070f01081505092180006a041c50318001c0c0e04103145900050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 701361492 1250 701360242 701360251
    0xc080a05070b0d06050d0c0602100b24090a14240d0905120c15010f030309091a0d0b060a061b06091103010518071a0f03070309050f0a031412 62
    0xc49070341c0c844403541010082c207010303080546c0102040001c4001c00100f072216004449051307090302c240c0401d40c001d24058804030310311030b43e000301090b00401c010440549180082310301c42c80c0306490136417204041600c8090690090307000d501d554468a00c2410590b0003566442003510300214940d01084444085004400c00d0045172a82c0300100e0003004070821203100c100c07542c0d0004540b6056098100c0e03940e542541c1c8050aa4402c2e100001800491500e001050729803580300c101c5000e0a059610b00100f400e0018411080b015050b605504c1d1502c0051400450180040741c60924140040c09012606d070b80c8210104202651555011500400101c0340b05030702c40300102e5400500d00741504803202c8080b409030f155281c0b9050041c1c451941c50100d0254202d00160784031300d03541745281c4080c000419820101e1080821800701400c0c48400190350043d15401c0015440480792206840c101c0034440030a12903100c01c00740300505400c20681c0f01c203410544003442c50130080200700c0580340700280c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 701362742 1250 701361492 701361509
    0x6180b07080715052809050d05030702100504030309031b020f0609010306080102030907031e0206030114030f0703030e010311130b09120303090a210918060905040b01030c080a0507 79
    0x3240d030708002c50040308030207609003503005006504280c017000f069101c1c00d1103030f400342d415125a143c501e500030b80a500006c542000280030b10144d0000c0594195000800a070210f0040c40e0202001642350f04c60a4000c1f800780e40e0008103075242e4038002d81205628880182031303500c201202c0f00169202d5030020070082094800035141c400c3d200c01a40036140315040104254004400c11002020001d10001203a010304009094907401c180c0c440c11071084820040d4200c501000140300724200401e268020308406030455a40500b440c034014100003240d002100007416160b03802c55550782c98001d80300c0d002c03c02c0c40c0403031030106003440c01d100381071007885102050180443c01d4070725999040070382031450301c1400030780f0341d28034014180e06e40360040c050013140e800346ea249460301145002000d0802c9072107640c0301d034140c1d60701b04001a6084500448402c40b580d850304030108143d03840c2d024082c043c910401c00d01403654110b16144007620410380114506500215802d80443c030009211011100f124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 701363992 1250 701362742 701362747
    0x316080a020a0b1e070c050a0602341b06050403020d020f0a1401030612020d030305090c0303040b0c070803070b0c030705040306060b0309011b0e01082a0406180b0708 73
    0x4020030307070900751088030140201074620704020000400c4c010403102d06607080c2c406840c0c0d540c1d00344161248002060040c01c55485a00c00d400040d40550041451a807800702086540d41d8401c424601e44c07005e10101d401c44406c01040e20700b007045007091a040d602550b0002c2444605080d0024598091840003030300c40c0c03d413812801c0554450781d030b803030050040213004403124503140d5000c8420315500c8600d40340000d141050000304007000d04d8503d80007641c003c040d45d0182405490841c094071003c2c103102118090000c0e5240140d030100014030050031b40c00101d03921000d44050321401d1003455401000d00e07400c100003442c00100000076903503000c1090b01c241503c941f2182d60450746070240740c0008108070701e02103010a84800c034502451191410400a000a00c900d207004403a42d00d100f01c220000c6000764101c5e51701d41d03020359581940140d95400300c102075125030714007a01c401c3d19080003411405c0001424048030398001304240300c1484401c041742104c1c2c9000704d01441803048101c080c10041e400b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 701365242 1250 701363992 701364007
    0x40f0506010e060f091c03020d030b2808250f060503180f0109060f200315010c060203070807020f03030c030a050403020a06092a03021c0309030b01061808031608 71
    0x15000c1e00c01459002d8140c041014803142c640311b50254070308054015202d000740d6045018403a004106140c0b2340030b00307240c0300502c840d2910400c3c40c9c13030aa54062900784406002c00c2005003004501400c0440748a040d001c0f0a607664404050202c035080145003801481050140c0303038010040740c1d04171558028001c9081c1c2150000e0b828111820119005542450a880107000e5150080c10440b6242d8504001c042402c004089800400d0703031074901d0303043c01400091819049440c2e034030700c03200060420020310306085d92071104907401118030202046000080c080e42176810801c81241040c01001107103107040c4000228034078080108a0005d02d921500008c0405209100200c1e03400d52110040c000c080ca14680002252b45001060280500611201d907101c04030000c400c041340e402404005110241c02d600351160200c401055040c0074038100004000340100c4c0071940240500e948a08c0b030000080b400304000300096006802c60b0340f080c8410188040b14514003006250b1154400d540c940740b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 701366492 1250 701365242 701365267
    0x1b25030819060305031231030806010806030a030806041e0c020d110a060b211e0106060e100908030a02240601020606011121030907060201062d23040f0506010e06 71
    0xd100d8030b000c0c014200082d02e210348061f10494400901c0390b2a0500340c2e43c0c800f00116030380c040440340c03168580d0000307580c1cad804640990a005d41280e4068000703d50010044000f040c800410580c502010b5650301280b001c40364144984000c00c4810720b842d0880e41030070a03c03d90b803112541000380c02c0e40d64950408400da0351b004004203000e07080c41c4000429180407182240c561050b0715002064107504d0000c840800341c103120364000e850b080c5d03d5100f009510441486000c020300c002820600c08518400320359140104050654000c1d150300030448204600c1060340340e011290099921058140700f805070f9070b030b00800e40d560f02a4080c030300407914040000000c2d00d03284246040101403240300c00650704568003900150320034a44031040710a200d42c4c68204908a40781c41c4101027100101d00001400840c22410030b240c0c40e2080e2008051450320b0b040302440c4d010003000310684a90040c0d00c008031504260203800410b1112120801051032b0400c000f030503000c5090034007032003482d0019803481e0310315 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 701367742 1250 701366492 701366521
    0x71e0203190c0b220609030c0c080303060120031303051b06031501030917042d0b0909100b0a0e0906030a1e051504030c020310051b250308190603050312 67
    0x141c20417001d100f100e50f54180030308030035000d140548164000030000b042044000049902505041e51000203242a034080e000c20388407141080e446a00080192520501c00601c04401841c082c001414a205058401c11552540795225034000c5100780704100c80b0010210310307002c1c00c0c0000c2c24040b034035075132a00d41100b80c0c850308800c12107460408900490b201c021155200006080d192044900541d064001d80c0750b415184181425088108411041c50410f44d0a05800c800f0f034a08100003203481d02d0a03107060340c20503404a0005200100b040080e0b180000126401610a6018011004694845a0114511003e40c00c0d0b500480340e003110420000700800c0300440c68540318404103081034900109400c0e0014400d911902c40d90510389076a41d050f105580c06034120b410501e0600e098003e80c5a80754202c592803044407003143d14a19001c1c001d03010040ba41900c2a0794172929807508041111000c5038400d441c4030b00070715100027400029000012201c4800218010f0459580c4144103095400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 701368992 1250 701367742 701367811
    0xd08040c0b03061306080345120a050d030c030b1305100806040b06040c080f04021309150606090b070209011226030901060608040317071e0203190c0b 66
    0x2c910304500044d40790808409490081523000c21483e00010071201c0c40076800001d40f50450101c00c046451042c0c15210f505441c1403800600440010390300001c801e8100348040800384e9081d044020701001484c2d152141c042c1c200d40500b01004040d00100200310210254000448501d0781c0300c002c12144d00d8425032450040002408032440307807409140500300342c030083e03405c40d02417400c05800c0d101c02401001e04030301ca000d040c00488603e80c0c903502000703400c82d8404014981e0f99515140b89002c03603002c0022001c4013070301d0240132804500d4038000030a045030991110760340900600284005a80328980b81c4c5c112010b072050842e80e44202e05298a078413040c80e0007c1071001301d2208a00c0c00030303010000341d441860550000c0080795601c1c10180d884440840d0003e000481120000c5014018280d40075001013a9180800007540b10740d50005056001c0c0c28910056032000c14008003900039600c1e41120030b401860030642214055590703c02c244409055003400000e1440310102100e12688240c0c00b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 701370242 1250 701368992 701369029
    0x102040504090305040e1e0a050403170103050d1709070608040512070507060905040c05030403031d010c0e030f120405120a02031b1903050606040207030207120c080d08040c0b0306 79
    0x41043c5005885548240f00358030301c0400300360000c0c080d80900d4880c007036a814070b41c07880901559041c510350010703c0c2c024012000e001c545121503495000c08035805010710301ca0b00017801b00010b031181c090704521a03451035020b1612900104600300e5030125645044a1840c1002840da031540c0c034045007050f0510780c6c9160451070104141060190004160088032081d456400e01e403a00c0d02c081c4010b41f21039204950218108001140000e13209034030007210242646000c0301d0012900ca002c40c207440052407890001004004610f6040ca4184940d42d01c072031019006082c0e26803440081000c900451080c0c61051050013610010150300b4460103e02c1d980c002c064030148800400000c011042105849001c3c03040e039102c400b2001e0300410000e080da600030006100300c1d0784080411000e50b1000c041181140901d90002410061001e006c4403410b100c5c58500c980301d420b1400b000c0c98000035441e1003080165000c1400302044c1003040080c1510440d403455541c81d600c64003c00c8403070925144c81000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 701371492 1250 701370242 701370251
    0x5030703030516030b090601141608041502010b030a0b0601050c061003060605010f0c0b060301060e01090e06060306100303050f0912160b18042c0604030206060607080d0c020102040504 81
    0x41540c994030281c483c008008a052012002860480c111954002d01640020301100070556540c010b07809242403030620700f0b5107803a100c40400341c0c00d42040305074400c80d5240030120342804191502c0c000210341e603071740788000c015014541300080c1c0d450b140c00034094119003403070300464500c2c2d21400890350030360070880465145007031194400329001d8075444151004da1410901085542c4650051a03001c2c0700c969543c1601002511384d1103000d040039145039819940c44400003503d40480c1c459038003e14000e1400180c090a031070b41a8204003000b81001d11a4001d402004076003c1400c0224068a805203040743d11001d4640425121303106040203150b11410703450b038022803500f00040c180c189409040740f200c18a940d4001c007003c00c1c0141440102c1d900860503159586003003552080c504103058404c50744200103058070160011402003895285d98124400300028150108a5190440c8060b100c00c1d10b003c0a58035102904c0c01405006454180c490100b669054400d4041e50040d1100034010807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 701372742 1250 701371492 701371507
    0x90c032d03080f0f0915070909090b040b0c0a0207090b06120c1e040501020d120204030209130605061c030302030711060a0903080a0213030312020d050c0414030f07051005070503 78
    0x806035030044070302501c00c0701180d000448035402c038005103001d4401c00d40180340310950300081c034000351b40041072081001041a400101c006046c024101380a005070528061418542002000c00710001c02103c8555401c011100040ea4005015003c454080c40e0000d0501f403404005041882402c01504d0300540d0f4005218104190000408070b501030002c001c4070135141c00d01310392100d0245105141c0507801100d0207003000f038020803081d411850884001407520b40c03607500090b03403800d064608035103402d6010940c0040041c90710901e5007040303048400302e004c0e07210481c110b02a55128600102099008000f0540b01402002a03009111544c000c0c3c07040351a20b076410200a00034040d090780040d039040041003100761940301f215030b00c0c181340310100b500d181140c90503109078a07144950b28455500708050103040b8103a2145170302074103e2204443c0d40f28502444888a07840340106103100342c001c0c1a014064a0707000cd6918203e0b0410f031000e9200b6021701509684a0140160241042c003001850350f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 701373992 1250 701372742 701372747
    0xd06090b0403031a03150c07060e1606140301080307020114360409052e0c0e101b12090b070f03090602071d2d040213090c032d03 57
    0x10b2000c0290802242c0f10741c00d0207810175039108080880040d4802008000c038030500c12607001004078034040d05022514841d40c03400685404003000e8900512808104c00b4000c1a5102c09a42010840441c0c41030545d410028015124441d555009041c040400d0070400303003404500550700b01021304014983c107081400c0042c800c05040001d25542c2c20b00490040d03055103001c1c46611101a0807000500c0707000f90061949a00e000702106502e82c903c050180c918080646010b40ca1040700c0a590741840c0490180500104228541002c0e0030302100b080640e00040e0036101802c54960094012401d500740c0c06400c0e1041003c1d41c0000b44a001300103002018094038001e0348110320700c0b81d9030f402040743e5a80401ca0710b400c018043c5581044510b00c6001010701c4508889402900f102c031741c0f1a4603411000642e00b0f0f51100300034040e88154200412042d860300b4141403004c512491800d1010701c001d03980740c1440c40302c42d000040c45032a540c0001840103010408003007184a0f421007080291401d410301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 701375242 1250 701373992 701374001
    0x2071527180e06010909050705030f0304030201170f042402040b18100f08151c0c05030f0705010503130b100e0a110a0c170307030c0305010b0909060d06090b040303 72
    0x942034488210404426041054860406240655006003480380d00b0171a82001800c01e0103016206440340d882d0114407070f9018060001e01d40304c40c0e4002e56903038ac5144005001c5002e504804600130242c00104030124802c10656036006a01012100300c1004550f45144410643c90001c901c044c8085400f01d94035042c64002c2008583c69138590f842c0a06030000c0080d00d010a05000e40021030401445003036501800c10603070080d60110400c10403030448808180100d0b201141800307003080004009041c0b0103815174060282c041900940441c1c0c480000d99692140e503442264100000000020030b420080c4e10f200003210f5101c84040118103260703007140141040c0e8010b4001e10681131001c80c910b5903d03845980e5000030311070310180c20100031440554021021003019126100c070b0415004c20408114011071140325551400118800042d03001800c442c0305030072050a507501080400303459520070740b5860b40b103d0100c4401074101c400303140c080050800c01c0310040003d50390100340410180c06401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 701376492 1250 701375242 701375249
    0x20d0b070903020414040c03031101060504090809011b171b0609010b030d0801050a03022101090602130506130b031009290108040b06012015151002071527 68
    0x2800c1c48042d607014600c90144c1700a83d0000c0100c10b03000004c0000074091203403902e50013000f4000040c900c0e0307038034041426140c0c150700480d400c610020380701c015507810491022520030b203a140c05601d07a0060f40c544480f29601801c441c0b071104089849412091100d0071460b480700c0200580740d19003800b082250180415281c0148039002c0e880156030641d00c980110f0b8122900100030080440c5503409102d43e0902d500501110511007a002400c4c80c0000d010700302c1030314441c01c3c006a80d01c03d60100e00c07020454507003009104003000c01405190555555204003501d0722100c42c00d503251200f0680b040c230104150320000d0b030782d800c10500d07411502c1810200c07158106080300c140c03403401c812001101c80c454207d4006161001610128816520481c1000d10301c03c035403800301102c0200d011610349408081000110350805480c1004480783c0407550340340c0040c1d0207680d41013220107042d80103174443c4050701401d502491f1085010381120712546c9101007039024040c1000c403255020700087c01c035000501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 701377742 1250 701376492 701376499
    0x90b040605030f070f0617010b0d020f031e153f060f0a0612060b19030f0210030c081f030b0702030a090b0a02070915081203070e0409030813020d0b07090302 69
    0x110011b4064000d0410f0a00c4d81040c0200f03000c141c1c01d001c40d030325840e00308003003010700382361300f03100204400d1090401580100711b11400c1c680c00b01c7c44455213400701140103041d022500c002400da40701548480410000300300c007031240996140c1d0001021a8541d225000c0a9400208081c044103011008100113004d49121010019150340b0586130328140c60302481406001c018201482c00421215884900340c0d50005000210018007002180c1035244a50420780f00402200e244208601c3c0840c0800608a1981001e0010784031604004d0503070400203001400754040c52406040300c0000107880009198070580201282c28181e400941c1c07a089240310740c01041401ca404902c0c0c5641030141e0303043c0c26150340103202c000e0424000c50090031420061401c2403208007800300d0301c1c8800780005030728031515042a58491a010100a280c0309854501c1d0740958502500d01d0003007688840784a6028240050f62403400c0e000d031002c2402c4200701000904100750403002d00100c40d902485850842e8004c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 701378992 1250 701377742 701377769
    0x61d0c0d1404110306011410092d1203090e040f05060c0903010b010e0a090209010c020a030302010902100302030610030209031501170d11060105090402060c07030b060a090e07090b040605030f07 85
    0x40c20703d40d0b144807c0c02103240541464141038100d203804108000e0f507181500d09020b207595650305011550710b18441d4440c10044401583c944c040c0c50584c89002002d20701c0744400004500e880207040400c40b40500742d2070600c01030010701030005000c0f2a400c4035901c401200c500d0714195420001c10b4004224142c869420515104a5036200349044098400d0051482c000c062800c2903650081d800011220705000400207900007607035804c1e460f10000c1d8029000404d101030544100b007400400d084c0c00c07006151040c000d10034240c9480443c0c1c83d581005007401a030701c0100800117442d04962107650100280c103c0c0c0007264004594100d0181035264000301c40b00440784100c2a070f05041c1d501d4817400558060b1004004500e400c00701c054010b40007418440c54102c81e43c10503410286a900107891500c507940900800d07040581c0340038010a200c0c00c0400c03400306600b43e00c0e52158500d1048000c0075071181c08614507035841e54400d10007090024100c0d0302c240603400b0201e80ba0440b0307204000ca0340001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 701380242 1250 701378992 701379023
    0x281415011b111e281d160906050a0c031205090705090a0b0904110d0c08030c101116060b04020c010902040b06030108070b07030c120e0310061d0c0d1404 67
    0x4601c0700c50540b500040c418160603904040300e280b451241e41c00c003520003c90315000222034502003507403191750403a00f10280040c0740196940c0c018250010807001042040e242c20400298440180d070a020014a400550601c403420100d448110807201e14070824902810301c0b038154000a641000c0714000e8504400503507604414070102d500c122001c07034010754a0400140080c0000c3c3c0a40058403009105d200c080da8030f81c0358401310540c0c80d0031007030503139000246803503207518100070080000a00308001d0100403508503c908450180a4500204960307103d08001040200e0f0800300300440f01130000c540f602210001c540c040c292650007139000e680303420b0b0a040c440c10003d0850303051707c21a40c010184503141c10440040c551220b0010380421880364009d90019200358000081011684e94000c4503018003400c02d8209402081d080041e145000410807045070507481d512030103450300301c8400d4283d5501c0702909103132280a41c0120380c0c03841c2188070001100c214550a00541c010002620f04222 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 701381492 1250 701380242 701380279
    0x2132105062202040b0301060b1b0601210312110a0c0314031b030411040f06081c0e010e1201060e010315051b03040602070b281415011b11 61
    0x22848102c0d203a51000c44084070150400d0b070010011450050000121141c0e5609640c9054000489444a0f001d0807134007150350103004c10202d070140001c0880c003004005c210702c00c15044071811100501f4000c0102220300d000701190311402c00401c0d0400503542d00c17264030340000d25900c01d031441100403901a100b00c0801c9441c0c4002c0c1d80c4205030300d035166501403100c10000072494000500c00ca5032807144580328000c50715580501603540e181910081046400c0003030b440e04105201e802c0c14110040304070903c54950b4000c1003402c620b20282084802c032180180030595503544446404529820030780b00140c8241003041090480b8051410b10030082d01c192009001c3d10401e03140340041c600f5851291041a03021001103030018481e110040c50900d05903100c0605850032505120484400c1039881c60040d0591030b800d0422100541c201701c0d040c0403240702d240308100600140c56080c010700014078540d000d11802180001e0b86012520f0440d810701c3d15000100c01e2001d42401a942032074130708004503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 701382742 1250 701381492 701381521
    0x60106021908090111030d02040306090b0c090109091e02040e07020c0a0b0304020f010324030308070203130e0912042d12030e0406150201090627060213210506 70
    0x10351044065141c04099001160529481c0e417034145580400c11060000d070640784000c00045214200c049034182450426114800006011801e22441004a240b4903a03008000344140c1c0d62130725000403d07400c00c18800c03881c00349500300388003030318400039000c6550024042890720540c5154201c443c00404042840b0070325406204030740c2241001e002040c018904480e441300890418900011004c1c410020700c4404034081d2a82032078078410315814018160f02c03505540d031145280c00190310308a1104041110700200e84952204c4007851804500203d80c2400035946007100014900d4445813280140365240320328a0050008032980b01c151922001001a10170440707103803004482e00102a51000c0e07550050b03180700e030350340b0550303500020034070500c4101c030b00c85d07a803003150300000b040c074028641304040b9107685882c1292650000401014046e9034110f81003010303072110380035031140300f5054202e81c01c04030358002c1003c0d154090f07100002d040c0303401910a011030086085813102d448141207060300c003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 701383992 1250 701382742 701382793
    0x70302010804080c100f050609011e0506030a3c050708060409021201050108010606113c070303080619050901050409020d1e051507080f0702160806010602 68
    0x12101d034000390200348407a002e42035210000059079112a00c240c0c0c583c00701d82c0c09900c0e601c15103a031103052014504204000a01504240190400e000700001090107145070b10b01c00e1508c100800400111961101e8010102a103010420507803e081c0301140b42a5071816194010f8600640c081d13004108026401510300815980d21440b6490315901c0502000c2c0034661801d0b81c00100c44921408100d0091007000c0c0201426400000e21500f0000004c100820300710301204103074050200c2342000c2441d0f4500710454007410881c4441403101c40301c00040c03984d40c6180b107445801100b000105054101460502c18181155034224001b080041e04020880350f01415800c401c82600500c014201584124482d81c00200081e5545035141d980c902402454807186d4409074140310204100700d010090f090500c48100d403400301902c1e201500601c540c10041041c051029503501107041c440c000e03c00418810201c0f00c1543d14940c0314407566607560800e1040d0801403007480701514002c2d15070340b102c0100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 701385242 1250 701383992 701383997
    0x1c270b0429120f160c0201110a050601030606090f090206040e1803040308090411121825081c0c0303020706020c0f0606011209150218030a05010e0d0c020918010b0d080304120207030201 81
    0x5e020250011903080f2554403500b00135102e41e52010300421001c0007102c1c02103102e03100100b0039600b03010410040d01c50b038082c2070400a0078401c41c03c0040c0d980d903050b503050faa02200c4030301090399106041d8059603400352401000713000016022041c04403c0c0024403400c8429a418000c50503081402e006074840e03061f401c24174601040114580440c2182c40318042c00715441100c2c04034000c01c005841d40d41c2c4102c018522141050b0042100031010311030704170f200b2899810400c010103c10720207082031041d01c3c4004d04140d1f0000c3c1ca90100b1015905a604c07a02e041170031503041c4860348901645d61803081e0707020f0b400708003100d038115401c800f14020340349040c0d480a140c50010a0b0a241c100203074000704915210340310861801069510704000d0315544c3d0707025030004900c40d40110303034550030708190030000c50800c40d0010020780540c5401d081d0300d421003007135442c2d88040018070f4403090041c0121425203501400014005040c00540805140180e000b15425070303011011701e4059aa1b500f0500c0001e02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 701386492 1250 701385242 701385257
    0x3120304080a0f050f28050f180301090f06091a0907030212010e0d02060103030908011103040f02030a060203070c060b0402030f181c270b0429120f16 66
    0x41140c460910622140f460b81419030420302030b00c1c40c3c441190484c1c1203000000031080359003440704108040c03c0c0300034495424090329000354001c440001e440b414406030b140c4152010001601d85096021100c4550026280080d803082c03403134040d02910040805582c403104004124665240c0040319a01400100b001080d40c185941c0c20301190305040c00408243c2d540c0c80c00c512a2288043c0f107011605145640501440d41c11807030003510030802900540e000303a00d88141590300c0d200c0d0030203c1e9001600202c403000c42c01e8162002034540503990100805150003c01803207803054120b03001e807408a20500080c00a000c804e01032004a000c01c40305008111068004201c6090f110040820240388010540e290f9803031240c80208603201139180c1d8000140c103454041c905e46035111108100354981e0084014091030862054454007460003806286c03004000052008500703541480c501000001c0d285440c1d0000f0041141141c1084915001d61010403000401d03180c1010b00307800c0f541d0340d103803503440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 701387742 1250 701386492 701386507
    0x1e09150e13020f1b03040302010207060e040e01060603150501030504080d0203091c2606030705041d0708071e030f0f151415010c0c0e061f0e0312030408 67
    0x403004090444031680280d80301c40030780094021400140740a041190001340e4803140031160450003081d041ca610700a800600c030600040c1c0e40440c0110445065251080d0394000c0c40b0002801806854000c050541c80c0c1800000d503160140c204075040308102d60301d00500740c1c2ea00010340a5034004c80d40201182d508012103010001958050742d00f0038000c00440d40c0d0303078080c2d01c00028244400351004000c10350407141d400c00c503454005840d0316035a081e12241c009050500200f070380c0d02004d02850344651384450b4503407000d070a01c00e103c020289040045811345584c407101c003516800b4a004071036990900c0038040c0c00110b0030100034400c403540604500003a00c05901c880340602010001182d0104111641c0310000425004209107414103c1c12110103061000c43c0156121005140b14107009465000801182d1940b80510880d500c94081c985ca540e541c0c80090200503580b90201d015010300c030a080f00c46a8083c86030000e008060b800c540010443d040d034406240402c84d40181210800c01190 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 701388992 1250 701387742 701387747
    0xc0c110102010e030301330c06050a0e03090f280513050705070609020f150c06160c03050d0e0a081b03270307050a08010207052404030c110a061e0915 66
    0x60008141e81c3c8a00103118907d2210602400c844600002010307000710b00244a0b903842201d03048090070717408008000c048420940ca034000c100351684540901810000d10f51101c0c1230503d01000c46032002d07803e9404c1c1c0014102e0b84076440c01400d016660280b140c0b0300b018882c0c46a07502440281d04c070142070080e02d945081c0941140d82c0100e03000701c40304040705002d495241c140c40c200c0001c9035000b501d48081e00301c11450040e005101c148a500320030058094941c1140400485681500d84030781d0320500c40b0304d0b04000e00300e01b10364000c0f18403804020109102c0303048040c2010004214402100300700341401695a030007108410484004034100c0b42c01e8003240c000c1d540031031410103802c0d50201991500060340000450f0f003c07800303a07500010500108901401200060381c0d03c203040010820200e08400310360b01c0d00500042c14007540c08041d4043c4110038006404640b001800c0c0710035142c0340e8100504005186482e0f1a005050000601542d802440030500b552800c40c001c0c1600390302c00b07104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 701390242 1250 701388992 701389019
    0x140f06180c070803010e041a0c0f16021002030a090e0105010516060e0a1b060813020f180c07061b020615040603020402070b071403041101080403120c0c110102010e030301 75
    0x7195030750740c080011000181e0340401440c003c20043c41c207281140741504102541c0c1d070010148891100d0105d040124005200301a03800c810301d075405a81e00d032200302655015a41610001035440f004240b05050065070000051001c6412541e5850850355540c01c6040140000e000f480d0200d08148200f40c0c525070f04444028800e80034a10103d460b0b85185540c1d4140101c100040c5c41e1f0380610405011410f1034220b01c0002000a4640b080542c6840c40700b010071480c081000900c42c9602c034490485558460003d00f036a500200d55003603040c14041c0407042d1550004008403052802c192034042107100a160394410340000d4bc01600c01a80d40f038003100440d0b0344100980b0783c095600c000100140e00c3c0d03032000d000421300c680440d0501b410304c440c3c040c00044024800e03403407982003041080005410040d0140140b8803c8c20000d4650300c4500d02950b040000c2a244800d41d0300d409203510241c6e601141c03010600c0d0181c90341080c84a010001207080e02e01e20b0001800c1544200010809840c09186 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 701391492 1250 701390242 701390251
    0x30a05100b0a0308191e02101d07030212070f32100e1215100806011d040501020409180624060c02030c0307032d0201090303080613050a140f0618 64
    0x1b0a0b000f4900c3d034000040035505034200706001030344806403541010384148210068404001ca80d00000d0050301100d9542d844c00707000007401504007003a04040401c08101141c003904c401200d207903a440d10780160400955a80c1011000e02c1601034041c0200617214501201c1c840014043c04003001c0d07440004e44070f840da080e000a030000c001c0b0b0135408145009101c20a04002900030141141c28401055035070740d01c1c0c54000720001d81003d0010408070b900070030442100000721000c00c1450342c070b90505500a0040e0b6004c103011078145140c4400c8600d0b4900d04120082c17241c141049100410800c41c10008240144500080540c0409003d0707903020302c000da0002c41c0300904840286000701c0200c1d00705044c90f40219880c44101078101d007500021014a180e481c0c5151001000006c1a00001c0840c0c049100280601001d013011490544a80d070040031040c101d0300b4127125509210201c000100544104800e201420034003045031045109015802280000d1020950b6500d1201440c0a80310261 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 701392742 1250 701391492 701391497
    0xf0306061803010216030332040c0f0612050708070e0f1c060603120e100e010201021303030e010e1903082505070f0e2e05030a05100b0a030819 63
    0x1c114a60700c0c0d900740000d001659200c050595004483c3c42d018065420301c49808205002082800c403040100d0307841540c24208034103070396000740c890b0308088020b0421a042401202c0c6039030400b08041d0707080100101c600e00f585100f00040e0355080700442c0c8980c0c0a032520000a0191908000f02d45015151141104030050820054641d116510074281c583d410040f1481511003108100344500d086101030021803d087c804a02154280060300d242c041501c18024811440030008040c1d1003581078501e0f00c00080044200c00f6201e00f40a45000c420084450014101d28101855410000300b9039009040c10040c940a15041d030340c0300c42082c0c00c4600c00d82d07808034081e1028560707540e0b613a17801c0c08442e0042c005080e00500701818001d581d400c0c0e4005400c451445410310050040f1036100e120301d20310f51142052030645104c0c2c40702540b03074103a020b25818800c1e0420042803100200c0d0150109686000c02c002a89440042c403c0511082c40040e080350401d205010b00c080700d0485107083d118a52 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 701393992 1250 701392742 701392777
    0xf0601080c0c120d09050c010203120402060703030603080304030c050c0d03120203220f05060105010809060a0903050903011a0a0510091206110f0c06060a21050a24110f030606 77
    0xc0c4070f4030000790040b000451149885400343c009205003070009a8a2840a101035407603c40c01c03034942ca907001406003009002d0180000c070301c000c0c18400d41c4020091507001821544d00d040c503040007090640d011109460034002d94086102d10300d800c03001090150342c942c0f161020342015821030b0000350002818020030388030001d540d113503c4503000b204100f803911507120311010720018144a807900130140c12540c1440308070010f101000c0000074000b5440f0781d4220303020030100946c1ca41142c003401802e03682d90b055824040881d40016400d040d900c2e15603410f036028045a9611410007140400c00d641040100d814880b00703000d04d40340c01600c0419207009a4000c42c0038110500c4262a99000c403495103008000130440c5058043c05000054000e0800c0f10003841e000c0c205001d29600b1490041e20328060301c0154079440421a00b4406080030b07980001c50902d62544100350003103140b80100e81c0045541c5429818419142c40b542501ca8120388040c0c030324110707980d0748103002140e0b04c011110210310828 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 701395242 1250 701393992 701394013
    0x50601093014190804031b0305060c09090f0402060715060b0a030507020120180316120203070905190509030c011a1504080a080703180605120f0601080c0c 68
    0x45003020a0a600c101c6041c1c6030058204440b9060508038000c44000c010b4030b001110104900d40306540640e0b40141d00c81c0444100700400b10000060f56000804c00c8c0a00410440000d5624001d851090000d4803106801c0e80c44a01000c4103d5086034025481201800f41601103068405800160b0201135070000c1d90981f2001c101c3c01c2a08000c2403480080e8441d003c02000c1582030103000a030000601003513005580705001c0380c0c00d9000d00f6000480032098542e008000360380c1008030170503480f0f9100000c070409441d1505800304034944007041c0d002e80310300e80f40051191010304c20340744200c5c4a040010400e286201548014282c00b41580085100510801d031750108284600d0801c03003081102103d4142130b8609000c6c40000c80c0d0724250441506000401880303c01040850f482503100c0001c55680c03185241c04d8840c0311103d00e044606c0d00941c03002040c11500b001c000c01c298144c0030f0020040c1d55800c3c008000b81c140c1200d1590028444102285d40c40c02000050300f0b41141c0e02003070701c8071410f9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 701396492 1250 701395242 701395319
    0x30a030827031306021f05090a0b010902070c08121e04080f011e0b0a0918080703050405150304021c0804080313030606060f08070c081209060f0a05060109 68
    0x8600003005036802c0010482e41d0324001c54500d000800ea140054900d5500342c400e101c404425170040b0948880d00d035000241850428001c010b2020360000b02603100b540c58445c003100070740007108112400d2004050214800500041040c541404040b0580c944200d80000700303c1e007042100ca40c40504030031320011404540500988244421079400066081940c05082c007101d021407842800e1185801d80c60700c1c00d80c0700c0c20054404d80c0e00b062800700720040001c81590710018070a40242141c40041040b004156110700140b088500441c1c3c80b04228030b0340c80820701c140c0300c00c0d100250b101d00e524400c0038103500420428a0124003480320f850030079aa6203540d50170740d8001146204000750010041c02044150720584010300b0403071500348581c4004403005040240301500540c10701103542000d0040280400c00c40b000c12004941428450a00318981076840f01e0a807800e0302c0303540c1d61100107a04201a0300c01e441c451a416501d400c11945407900c4c0d25100e05084800c0e640e41d6a00030035407503d114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 701397742 1250 701396492 701396551
    0x509100b1617090901170d1110020c060a05240f01031506091a04140d111f1b0201120b01091a0406080915070f120501060503091506030a0308 62
    0x1401c01107002d03038076200c80c3e0030000f050350140c00980a0f00b500780c1c140300141c072000407403040300038050410031802145000700070324086c82d0504503961702e8000074040c9098035000c0350090155070704d01c40900080c0c503000c9800298031000c40301d6412a0045100141803403a11280401e000c034070605000420401c0d002c000c0c201c284041d009100407807850720040244582c070b0004100400e20085003a41040d06102000e03140082d460311692103010403500d200b05000401d40b00840b1140300804245c0130081c0d000250800b01c00a03200030002c20380d452005441a070081d0001c404007a4140d40317000da4101e42c2d00d508402001c070115200d04000d050071000c02c1200000e0308520140404000d00d42d21a4500712005040303440c002c24910082d0404000344c2ca50f044032610903504805141010f00b03050783c1d000c0c1c0840d00c0d450245c0705102d026090200020f02c0c03540010085000d882d00d0300a5501300001c01d0542c010600c011f5480c0303909075202801040c0461301c2140c000d90000ea05a85403540400344200c550b4861 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 701398992 1250 701397742 701397773
    0xf0d02010c0b0a0507111b0405100b0a081008030a170c0d09081905070309060806220b040e0102070507180e030c0105150a060206070f270f0509100b16 66
    0x5030349405014000742c121019000c246d0911006142c4c1122030741d030200c6c007201c0384445240507545078000719000c0c9040d05001e1300545964082c990f168804810010150382c01034540e89981d9210000204130f1060101c11545d0034045920fa410071020f25079640740c0036107001068001103201c10300844208100368018000c46a01a07507060b0b4942d2640e10074008486c4003400d904052150400003000020703007100140d01100c4081c2080a01130b076940c004101551030040601903800ca54810700050301c40c2c143d03c8031040780004d503410032031040030424241c03c078860283c0103803141e804203108001510349040d0251031151032010100303100030b90149091460300a03c0c2110805e9442d802000016040986c52100074002161019400b80c034280c0042c1d1100b00181204041200c4000406000350180700d00304404805d0b0a00011581c41c450802d4458403554000c410000551400c00255031604003240303400380e43ea004a13010390900d081d103407000a9001902011010074601091004141003000b0324100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 701400242 1250 701398992 701399011
    0x11010e030c070e0106030e1e1e0a110411040e0406060803030709140604060c061d06090a063b100203010b040509070f05190e0d0812070507020f0d02010c0b 68
    0xc14200800c0d0f010b04070050304072070700301761422507028881100000c0c00c1c06100394032102c8407520103c038041a410300b4181c512241140c0349291611146030800601a4501401a041801c0c1e4036107007030421040e239071103018117894041d003844244400301d4441e070111b4000e40700307840002e0520350701c050300c1e030071a0412140c20340841c2c140b000400c0610303014a2200c00c41c00c0100c4509161a04243e0b0151058044860192803603640705091002201e401d500c0404072242d5504860035440e00e0f41c4060740e504003102c4103c0c1c5090608400702c1c20388044010060040d071100e4036049456020120107101c06038486241c4c811846031018807204488107100550207880f01040c4280e41b5401e10f02404000c6a014000000b0400c902003080281c5a01c0300c240c1302c89020b110f03008801090459000c8506800d007080c007643c80042030100c4410042610010445189254000c3d40039945c3c03448107443c180103044010b03412148405210040e494504130110005205040440c2104465142c940c48408120b564881 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 701401492 1250 701400242 701400253
    0x91503060c021f0b011b02060c011e0e030702030601140a0f061805090702210405030114060307051905010c0303020d02030709080c0301020906090906060903060a02040306180302060711010e030c 85
    0x110081883c2180800c012400c144005810240000c0c01d10700ea6002000641116406000c215a45c12048039215141075000340014109180803002020704000c2c00f0b61410b04d0080542d00d01caa02200f0b441c42e40b500100941510b81c6016987c5c100aa89910003540c0a0041c5501140c19085d05a108020346501e644860b912482145050000d80c1c0c9500300074410b40506040010b81580041c0420301420002880f80000d40001580645c07405607402159240d42840d510300c2000c55060a9548540d0088080303e4a8503a200c0c02d02190a0711075444803c0031100250034000d0394000d905030360091780300303160051410365101c902e8000c9800945401c070019805000810402c8420451010010701c00c6001314913001c4504002050b81c82040d620720700942c01c00c7c00094955030340b2010b540c3c08800280585440c0c2c603000300100c0007507100e40000c98910307181500c4010006c4007000c0c0c00d440154035070010b04040e00c44171010b0350002c4980ca11002290b494170323403000c041d44040c00504010b4080c00014903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 701402742 1250 701401492 701401513
    0x60703060506121e07020f06061e010c0203030d0204061205010905011203050f090d1119060c23060c03180d0f05030405120f071709031c020a06020304110f0d0c091503060c02 76
    0x141041d070701411403031054040b104401c1d408214480314090ac0c43d4242045450610b2a1002c00e081d40560500504104c0c404580020010380181181d082c0b00c0c0c0c0354501300000d0b07883d922420f0460300280a0f003848500308000300c8000034011001000b810f00408000743c10b1000d000009540955400001c841030441c1061034002801d0421140076006640b040c00b00b8201d0034420000c0291001d0540030300071480c500c512110f0300d0100b00950b4800040c0301c1c25544949485294866036034400d4070b840188400920fa10034402c28042000001103005999504031184116011110307a00058002d407814040c0307102101d070030800c100c0140110080741003800d8450405080c1860700e001c4001ca58404010108180501541d0100d50307070110030002d40b282d240545260900320315101c3e4030080240000c0c400007d00060000640508111000440704150501054018003a0300c0350090f1004120400303c0c5014802c01015400412200f82c108071100b60003680c03a2030300070603604a2030184002d6086000d020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 701403992 1250 701402742 701402773
    0x1030f03030f1a100c050d1e05030606070311010f051801060602160510110d020703060f0b09040b0c0c1c090503030f040e0604062303060703060506121e0702 69
    0x4000303000e0311040140f4582180d1144203100e030030708018820707000010070b0801180200c48602030140c00030220b5178400b101c0d0101900c6603145910301243c4030008104003c0e82c3d445101142e22840c1c029000b14104201c0e507a040c1c0b5118115002c020140d501e401842c031140d0747c903100d03651042e5101e07a821240e1105003001242120541e801c410115003005455070904506180303c0811958141c03075075075104104400455900c0d14045140015000e0743c071240941580c000745280607640601410021a0b550342c54020442c5c040c11f0501c0d8004400d03400140220394003a040c0b5503c00c00400c0540d1820b41c1a04026051138008006141e00080c00e6681d0301140790301009440c0030300307800c0e00103600d8262030a00689140c0241d10400b9441c4030803c002519688858120358014144d5070000b01c04019603504108035105444541c0340240b161000007880c0a11034011102281d10285c051f40c40d02c0c6490190854403880244500282c1c92242202c0100d040500a000c0c0301d00e40c694081c01c210740305080304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 701405242 1250 701403992 701404001
    0x50d0e09011403060402090402010c020a0b0c1c020a060c09120b1b0c1c0e1206160206070e1e091015031a09090f01060f0e090a030f080a0f0501030f0303 67
    0x11858010410b090a8a10345000582c5508650102c888040d25640c600c0125614003055100030341045110f50005206400180503040e6544490169558501e90072444950000280b0340d500069000880b4440461111360290703404041d2840c1501d019074944411600c007698070030080302c64a580702c2c1001940100300740c0d059202c04051500901e44a03030700c01d1a85c0e68000c441d80006a1110b0b1000b20255a8000c150765003080201604919004410480382e070345584046500914400540f0b22034601d007440410070520652003500c4170040862801c0902030204000c0c071450030b041c6420660111142da513000300f14800c10707103250562880c40c1010403031861002c5e43c10466050600381051007683c456038a080048145d82554529801c4d5143c840d0185810484c2054540f15446e01c070000c900180d00094a4068445204102d106600e0300c41038075541e1094480d010780010400072140b04c90a115250454110120400100d009410720102208a944c20381c01260440051030140c800c05405005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 701406492 1250 701405242 701405249
    0xf030c1203051e090a030f1a0402010f030e0f0a060903180605090d032001050105010f051603030b011101140618090601030206090d060e0c0109050d05030409020a0507050d0e0901 78
    0x980360320035603940c0240c03240c09440c1165003021641001e04a40d5200303601075519410004041060b100d9072420a000b01980a89082d605c039004035110290068980748003c1c0940d0317042c1d445a01c00d80c1d07903680c03c400a080101c0d40c4411409100580c40007410b0411200e40c049005400c00160042d43e458003078000142d007510022079441030042000629080000e80701c0c40c070780c1500c514034807880601d0103c030500c1081394050004a0100020702d40b9450550005050782c5082e21800c141c10001d1006480b5030080c0410001066550060040003034401d400c83d2a03200b40c1814000301ca18403184040782945d4a49231101401d846200811000b0b16081405c03802003110812011000e06000351000c2d01c940341400007a0040e40d00254400c0d0684034585401c400541042c020041d881c0e205007100d0f1200b1040100c02d000900144003c00d0783c2c9400d06001030f000380d100008516240ca000c9070070001e900049440070501000b80940300202d1800d0081540c3d07141241d64000300a1116002c2004c0804182c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 701407742 1250 701406492 701406509
    0x20a120e060105030706230702040b030604150501051206042003032704050403020a141e031305011412091c02010b010807030e0d121113060210090f08030709030c0f030c 74
    0x8190300491041000e00307c81404413802c1d5a40c070100d074004140034080000385203825109070300412007802810f01d50240c0288e1414824019a45da800802a101403418030000d002d80000005c00d00191b2a1195206170300141480d5504d42064000080e040d07800c0b07610b6102000307408810141050b2418843d51082c407031f003160304111604198a00039680e040030100100100034112800c0c401c1e10082186a0a04406481030710140c0344204445880760441401c0140707854044501040540c05040b03002819444804103e0070300c00300c50400c5a100700041c1c02c13000b1500440e10b0340d0007401c0020071034900c030712400c1e000800c083c1c0c15000010098080103100c41c003010300c0c001442c00e200c000402c0041900101c0c0c41e202400224941000d0001d01002110084011000410500d04843c1d5180c0304111810307902581d6546140007044410b90300c2d80e082c028851501c02c00d0a4000411000185801030503c1c81c04400b499120b41d6104085203168201d600e248a4225041003041529001c0d07402422a07403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 701408992 1250 701407742 701407757
    0x30b0906011b15141f3804060e030f0c06071217070e0f1008160302040b0406091806050603010509090c090103061505010504030c0905181b0109090207110103020a120e060105030706 79
    0x9041b189800d010405c9807201461381001c2c028548100841000b00311175410707090360f07129500c0d00c000d4000141c90250701e01072b01030f40b038100140000200d1003c1d405840540242d260414681c2c840300b240e07044100036014001508681d41c200e401555a162048010382ca50112041d914401c014820883d00e40407803003107500c1f09000020a90120380503801142110660580c0c0100c820194040e0040c0e4001e69010207000c030f000107509502140b40382c200c071402e001140144448190794810380350b0a008030f84c0c100c801040100001d04081802c0c42e80118414142c2c2c81042e5640009004000c1c280d0081e0383e0b05444031040042a08002d140301e0080c2424280589000d103190f0b68941510500d10170105a156501c000900c0340007001da04440038180304c015a8030b243d80c0c0c0d2628211601d142c4180500040040c140491214202e01c02c9901d100e4120b603420011220060044001e5404032800c1d004100c104160854034250317034040c003040c9001c618040c188030340c148002c0c9031403c0c0c5258810f10400120 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 701410242 1250 701408992 701408999
    0x1e0e06030f0a110a0509130605070c0f0f0303020417100c050a0207030f0314071a0610050313020a090e0309040c0216030b1024030b0906011b15141f 65
    0xd004540c1c50f610075040c0614981d08000201d0006055103d660448032001c200030780c14098888a541d2184184403c20481c2c40e03182c82100e051041000c01440300400164100100707240c4200203c0c9030f44245000340c41e00ba2104098222060748441d203a0302c070b5008807a52140100b80b0301804540006901d0038500707001c40d0311002951240d4522002e00000c00106518044c18412130717001000ba8240408030b9a508241e142803c9281600107050040381c01280200301140b419403500110000c90340d035a01d007192249140d03a0340070480075000302c0c1d0000340749000240c1c40100c1e00900ca20281ca0001454503201001c00780000e0360303015440c2c01c0031504500081d2400c0307e03040c0f039000e040c1ea42041285009694649902c01561000e40040074604100006040b00250398040401c1040e0a40e400740021484c602c244811181c0070b03640940440c00d405810a44a14201100610385009031417140031107400e132003004103d0301c040452802000e1480c3c200000312258889c4a6407140705120b400c01d0b054503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 701411492 1250 701410242 701410273
    0xe04020a050d0e0a05030c030d0b0306060d0b091e0d09090203010b1c0b030303131a07080a110d0e0c01090b0c0a080304050c040507050415050f040902090105041e0e0603 74
    0x40c000d0811a0b5950360700907030b01000010024000102d42c4003084a58034100101d8060790380e00105088201141000404490707030901045076401408050014061900d2a0342d8030300700c000d0010010180c2d44100948050802500021001d103001448050038155464100041460543da040400824010401080318020040481d1001c210f000e000c91040c0c98401e025801a00d50032813865490300c00801030181d440c0e00450200301d00b0b48180484007541403510006072000004807026004504e0708400140542c04981080c1c1c4d2100b240345110345007504031300c1e0105c100e4102c0c444064040d844810544920350300f00078010080d00600f10712a040045110b102a580c4041da04000e0900308040701090422408004080140c0c00003002802986880e02d070051054205100e0000b04c03107a42d020b071240a5000d84102c662900d01c05116070b29281c2806503d10282d032000c0012410003808200001c0c440d00c41d204d1050300034101c9402c0711080751a015010401400240c1000d1294103c600350195001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 701412742 1250 701411492 701411497
    0x70311040e1e0102090109210308071412010509100f0605090103020c0307050a02031204030201140a020f060925051804050f0304060806030d03050702030715060b0d020a0e04020a05 79
    0xa02150080340c10900c41401d2414100a020306103011800700503000d014810640142401030741c2a43e0f03910030243c0d01e0905a00286a101480022103020440080440d2041458070741c44201400c00b5038040c80800d25801d00c0307030301c4000a281c00c003031a00014819440c0c0300700895084a034501c200c0340c5090a1140960300e0408500c40c85007441b0000801c41d4440e406501030716a103009400c2640c0d120881410070f1a06d07140d490000f248203001c1d02d07a415107080ba012060f036040e00d8069448a4071f8000c0d10510000039880000910b0a40c072456030010140f81d000c0003204e20420764200500103160340c800242d141d1400039104021003e240172424020b94070380d001000031071602081c00c1105500c0c0c03414480d041000010841d60345010000c0c011520075004580740b07007d0f42c03007034045981c0398100840c2101120000d90b1240300680013044014041005030902a50b180310740140024503a030341e1083c0300360f82d60201d001101595004079a8608090f0880302c9d13010700140640e4194900242001e00402c40c1c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 701413992 1250 701412742 701412773
    0xc03030a2007060b18090d0c0501090219080c0a0b1c0608010e1e0d0206010509090c0409110103050f0f072003040902040e0109060b31060801080f0703 66
    0x99a44800307a9001d821406810714014455a0311196200d466040035400f4183c5810154080c21551000300103030182c0f240361a11800e90200a4004010b04850403140d05158031826240d942d2202e12101c0075a80741c1418a0303594180390b41034031545141c10340144c189604e5241041c402d16813407000304100804501240e0b13440c5400c0480c1800f01804683c02c0c40140f00c40d0b000301c266986403803105c0c1c0e4500000104514501212030060000c003541010040e41c1d00f0702c41c0d01c0400141c100100400c500c0c01c04104031a0007201c03c1b401c1c0d49200903800040750446065040685409441b100d280b0030350350f0144a05904021a54180d082c90314000300310084421303014203284100300001800d8480154107201a2540c500002d066036075440c3c0e594255000f81d08140200010b040c088400050b07400c50074801d90085514800225013081d000c01564900660000c13289001407a05c0302d031110068080480680c00b400b5107803600d14280d41050b00980c0f0f0105844004c9807281d02043c3d0038804150000c00c0d00810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 701415242 1250 701413992 701414011
    0x150a0b120a02130c110f030c0f07080d030207080c03031e0f160503070512090a0201111902011d1305100f0810230414060c040524160c0e07050c0303 65
    0x90300070034001280c120801020118103400f1b10307071644030301c0f1802100034041c602100f41111005208864001c1d1501000d110303a2010364014840380003001c0c003e03006040340c24080c4049a050804a242d040d04540c0212540c204120316501f2203d401025050b4180c0c00c07610f100541440ea150a00c0f03c202c0000101d600304061010100000742028400c004070f80701c0c10204c0c2e030072071094140685400c1d60f4035200c070303400c17804508020031195200c540000c00f1000808583c03050080c5424580040d078030300d1640e44031003050120442414880b07403591042001c6503036180c10000703103518003100801380704407841d0010112031404001c20002d1001c0050352011264604000050a02035029241c00001d1241044401c5001d0101044240075012040d8103510500c041550140e0307940181c1079070584a140a00d40c1d0200080304c45008606000702240c2056085264051410400107103410900c07041100881e00f00d000182d060100d2044914030a411964504025041800c3c2116494803404002c154019 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 701416492 1250 701415242 701415251
    0x803070c021207031109160801120606030c030503090103060b04080d030e01020408070b13080105071407061509150504060303080c130b0304060c0201151511150a0b120a0213 76
    0x159610103400101c01c150b180c048680082c2e50b40b034050380107010010b8051084034010300140c1852003c0442681201e110f5540306016802c0140003090140060070035a8105e40c0c40a022000500f14044500954040d800640e205d550300400102568025002012540340602040100c01c40008151140181a046c080b807541d00d681202c1e03009004030b902100c1c81d0311400e07400107280f040c03203c0200003482403110b103914003035207500c451401c1c2c410940b804000190f0304c003d441c40b44000340700545507041c424900416040b85603028002100f5003034100c02d001c04d03501c078100140215091b10724401804140e50911855245480150080000404000010000250b8a20b20409405880c4e0140820102d465203e003040c0c18800002c00264076041d01540c0380c00c80c44240c00d00150208411105200030001000e0803854080380c0f40d040909004400d84114210a1302100f00c5c4001c052240404480005074079507414100304071400700210803441900319000b40c0c000b40c0c452003000040b20b88003080114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 701417742 1250 701416492 701416517
    0xc01111c0c0b161404081207020301020c0d0f0f080f012105010c0302090a080a0c15050f0d0c09120c0b070809040e0601080606030c0915010509102a080307 68
    0x21288001400000c2c1151203010400055190354000844085040d0f618203010b41c0024444020611407400b42402c45d40c86030001700110b2002c00010403e162000c1d001500b421940e00c15603160184488611020895085840d05040d610010062030799006240590320390500d200c4050045006002e43c5010040c0c4040c0c1e0b03041d685c100b1710306d0010705612400800c8200b000400c018000c0d080b13541d40d0340c420b807020400010210400580c40c1c1005070002c440d250410315000d10311901d040041c002506209040c030810520b8500c071030280030843c070004c401013600c20460500803c00c505c0d50700200c45000090452002088c4030700704000c19100700810300c84d0350310020b003012400750003045469a80541021602c441640000c01c1441c1210403807800c035001c5031148810991106004290b41f50440c2c54100091106504440c0000740b190041c10001d2805841f01c0c04100c02819104140c0c01013a0a4000d00101c449861141512070604401c10a64040240d6441c1c525200141c0b0381001c100c2d10b0403054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 701418992 1250 701417742 701417747
    0x162d0201200a0e0f0618040b04060806010f06081b07060b04020721050903031210080708071502061603021e0d1a03060405060f041406180c01111c 64
    0x1411003806911180301410201c0003000015480185580e00040041030038076114142031904007050400100701a040c42103204a07000541c2011034840d038000d031190200b1034a030b100c1e80700e0032b0080c210141c06402c0e558140040d060144500c4e0303000d6010042e5200c20050380182514460301d04070070f00c0d610320390784109504143c1c0192805081c443e81c802c1c80000d850040140040c014842002ca00d441e608010344907840a40d014042d01c1c00141d09078004020210702c01e911114490b41c02480920b00085640d140e24809182c10303040d400c15410303070780030081c1401144046008001d0070314241c0300901d0300d403030441c0c3c120a4600c100704007801490340100d018007850015070007001528000d045e5070768454a003035003ea0040c1001e04158650044600b800b0070300c5040108160b4070507900a402400e490319446c0480f40b0150008009a40145107060b030041d0740380c01404402d02902c244140c00b40301d0740d0040e801070305044004443c00c1c18060890700c3e41c41701030f0000c11804204070310488598584800c001d810b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 701420242 1250 701418992 701419001
    0x9051209211f0203010303020c0415050f06040918140c0d20040c18060903110906060d0e01140622050a020705372d120305162d0201 58
    0xb40c0d6210601d510b0241c012002c581c040e40c101c03400f07607007150300c0c105035203040c1300072102110341184a0910220051089040901c1038a103c07500180ca2203241030b0b41d541d03c1100301e03041180c451088092030b0340454103014282c42d50b00100c5c4841e50250405001180000300611030b070070070003000700031101000a0500e0110440c43d114060150041c0510401c2c40c800a00b011110170841c2c0b07189134914008101035209800650651354010030307411101d10a1020098007840c0240b0255000c6c4c020007660003a64000c1c02281352203a51000046005d2504181010076148000d181500403103241c02402c0381c0d81c0c0641060110030007881e5001605840b4105004080d10640c103010744a840388070300c2d41c003084a071900b11850403035000c1e0059202240d41e003c2d107502242c12402c090401c440c03020b1000b1204c10b520b2040065140d00e400c0700c014803134243e038402506502e40402140800da0380c400300030310050141c80b20078520200785800c08141c07610324020340c901071141e03200c0808142c0301000404a54000d510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 701421492 1250 701420242 701420263
    0x721051603093c05060306040209060f0414030c060a02060708040c050324090a05030403080a0504180903031b0f180b03090715020307030c0b0a0906020c010905120921 73
    0x304554008403a403075440070320001c03956010705440c8098941c005100c0c3c0c024405131840109010702d15103800702040065005130811517030141c01005118510512500100018490740038001c0c0400c0b100300030541070400c0c58124a0054034200302855400d54041035080c1e22843c0c5090400302500c440c244004a010150021905889480313503040c2c123070351841c00f40b0000c42c40078140e6526990300e080322213803180301885c4001c00301d91050000f400042c000c074000d4562412245042401d041d80d91071404540140020341114080d0360340c0405060640c1406151580d0491002c01e059110220700d008040741c03030f002c11001c00c1042d08900843c0501e82000d122000f00006500c042d12401d044d80c16948444661040c0800110180d1150080074008400d460b2005d816440b058082041512141281ca4001385414a0a9a10403003040014030314070250804a030303400000070b1071000c0b62401c580b6000040781c81c042006404c2c00851076540c0c9800c02c80c3c011040c81d038404002084502c0e00c00d4a0100b00b000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 701422742 1250 701421492 701421509
    0x90b010c023f1015030210140a0e120109170a1e08010815040b01090c050c0f06070e0108040503030604020901140d0c0e0111060c1e0c03072105160309 66
    0x101407030072205252070700031100e580c4419030f042c0030125450304049030280c000c1d410b8074402099040025107800341a18040c0c112505080c00e40d208507800d05081588101d12940100e200100285003074100380c107040b40c10051200081088601c580c0307501c00e0768410b00e42402001e880000d804980176200703000325055101c01d51007455411000c1c4401406011090144d05080e00c54016a080f40b440b44450a40c016900446641ca50364204407000c8051302c1d940070b00e08248102081543c1d6003010801a01540c000c81c1e001034541401c2440d0020511816401c071075040004007010302000c21400b00869070041400c4800580e12000d00d00186d41c000d10f0304982c011016800306451120038080d8010100544444d42d54226048681005403107034104245400e05030741c0900b0004140340c0c103104c01020804a18038040c5214004904842c1082d0b2080011881507000403a8a074100481840c10114a410001d0650881c40141f00024854040e8090100a02501e00540401d041c01a01c241c3c02420002c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 701423992 1250 701422742 701422819
    0xe120c09131b03030c03031a03030c010c020709091104051e010305010911060a0815130906060f0b040326071a0601200a0803060324010906090b010c02 66
    0x2490035a078141e50140341075031018141085894200302c0c6044030380903079030300d40c640c214600700d2520114010314010003070038189001001807410a90b02000541040840b134000440c07c0350403404000d041050070b61150b50801d0600040340c0000300e011400706030700b00b0141c400040c103580e290007000918100c0e080d80c04040f82d08200100034405e042d0000c00145001d0a80c164004801a051003068480c40700031000041c411070210300910b10380c1f03c4180749004001c294098500032100e2401c1100ca040034100c1d013440e51203034200095884600798000521003041c8450800b072454860000c0d4000004442d0300703060320703001c0c600039801041080d2000c082d0829503d203c6a6107088600402d1a019990240451400942694014211421103549080030406400d0081c003565624002d03410103403c550b4140580d41c00410b00309000012226000c5040c20a54029450040d5841c01c40e0040c0c0c000c01140e5040c160b91015a0344c1200e07803003080a6050ba0840c44800c05510359800c0e10b10000d00c13840071400070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 701425242 1250 701423992 701424001
    0x10142805040f0b0a1e02100c0504050a381c0c08251202091c020111030703020303130201030b040f0b010908030403020d020603070207120c06031b0e120c09 68
    0x90180041e54002c0800240c040d80b1001103401c1d0b070050500349400610413503428140d100c841042c07450b950071039004903002440c4651100058039584504240015400724003048946800301e5500024a10b0040c0ea5026070318482251b00092032030600860700e2a0b030301c0d8240b002c50500c1c5007211401c00e00d20080d00700c40b07181603410902400517041c4041c00507030307080042008507100f0303118680700009068019202880303941e07003a0303401e5441092061040c0d6091092000070f0300d951016054444d403000b2205c1c000c1d8103d20014101c0403410319142050340c414001e6100080e0000122030f0481c41c00c010054402400b40300481c080d0280b60070075508030b400d160110200070429000100417080036210090750b1900d4095881c1d40c0d014610010354088840310380c03030703001d418090001c68002c2c05610588420586a0700c11144010760108122035a4040500810030b05515100e03202c0c0800188001046101e0380074401480344c0c07148100c10307110390008000510b03903410802040035511005030450840341351 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 701426492 1250 701425242 701425247
    0x40303020715030b13050a0603020603090f0f0f033405010e010e0a0f08030403030603080307020c13061401111c080108010b01050a0f030e0a0f0b04020a05101428 71
    0x200303482001c0c2009880700b559076210b400390003900201007003d003602d03000a42c08034840c0b010b00b00140403030910640c0c80c50080090303200c000081d449116200000c0658087c5002c6940c41d0109104100c03403e5008a10702243c0e07a03070003104a038003049400c1d4107201da0b0b9a190045e10224a100b200340500211003031082c00c100001900500300c4a02c000d8000c1002d08801c00c14036480e41c0038254014000710900305600c0000703a004007d90f8000d13000385000100e058a0340d9a00b4000d503c240c0e2a5005039004540700c80385842e003050036966541481034188450342ca400d56400565440800940c1070003000c201224450000308490b1840510000c2e0003c00c4041c41003014101031028060341d0025400c0a007244000c1d4090b508590400c0d079140c0c0e0b0404020700f2480308a00a000703030203029240c1c1c0103040380070b070100300b10032031060400d401030884070f00da420680304005411040c2e0703010501641c4201c800d4540b20b90003020541000c1c04449114bc5e40f0b45a140441c1c18071440601100201c507101504401d020340d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 701427742 1250 701426492 701426503
    0x4170109030206070207181a030a080c0106140a1203030e01180c0803040f0b0a020705130501051809030409020706020904060b0304230a02121c0e0a1d0f0402031204030302 75
    0x180030340c0039203c540e01c0c0c0704401c98955107580901c00041045180784a0780054651144100b903e91880c0c12004801d4030b4000707418801c0104d000d90380070101094400c9840e1081c45004d00503d1214072220801d2106008500080102d20800c0c010081441c801e60926020342c01c506408498200200650b45404c41c5600e007214141c3c00540700840c1940010840c90400800c42d030555414400020215140c00204226980a1000403086001e2071000280c0c0ba280d03007510100001c0c880c5c0000c00c0a605110600024140c5503c00c18240c0740804184a40610f012044800b50341c025100540d07180403608051000e8800e2100d22504203182000008610030780002a501891007050904440d002a03101d03042881524084402140c000c030340158011300c2c00c2078940c100c0c00458419a6100c0c0003003006440c4843c01e40400801051005803424035a2803e40300d081c02406820a41d4001c08200013601d02900700c0092041c2140c034641c9012800390340e4104001e05c030000c201d030034a5a60325200d1400a4841d1f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 701428992 1250 701427742 701427761
    0x20a09051005010e06031501020703060c03020d0b0d020108010515040e040f020103142413020c070305071d0c030c09031c03060614121504060303110f0d0c0611041701 73
    0x4581d1a002c1a191320540403500400c1c0002c0882c0d04507180c0a00626040f400000100e05510982da40000050365602604203c0101500d0050b140e80892032401c00b40e440645031223106100030300748440142e80004105066880a03503401e458034540200c0e080c000e20940d04504000100e000c1000204902c0c4040618010f200781e85c184503c1110048402c0c01c0c00055508011001081c0b14205460010742450340c0c89803401040c98607003880b4444034004130b9001d50300e000840c1d08840d6090007400710030403161000b0003030009150441040c40300040140301014114180c410700c000301042440c01c1c00d0f801e5800d0301400074103850041d9a00c0b21906500300103503001c0c1d408203040c034030001009801400112100310403c02031901c1d01101306084507045100406080d400500304d8a074404544031340c840e070809180301c2d8a500c203207110030218003460846c1125030f09085134080051080d03200c1d80184200701a42d400200400c0381403103011400034a000f00d401c0000d174507184c0b065001c80d803001504881101d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 701430242 1250 701428992 701429011
    0x2120d0603051e030301090b030c060403030201140123060c01110c07180b2b290f0702190606030f030509040e151306150303021f060518070507020a0905 67
    0x10884404886412043c0784881111241c2040c401000100040d42042c45c40c084014203844980000f0303400079000d0340040c0c0098005070341d14a8070304428240c0815290140c8000c2ca130800406c1c2c07403021a00b400c060b845941c1f5004a5021480da8200c00094107c0d403c01040c845001c1d0702d51103c03440080e600d6035548a01140040900307034840402c0268460b903400140054850820400b8248031030080000034400d48003a400c40d16469004a2111f600d8502d0540c00c18204406403103d440b5034170081440035144c02c41c480d00400c10b0114040e000124055882801c00800105540c00d040000040142e5840545081d4016030202c040660000c000d10758044110b800b008020060b4001c9540d03042e1000090094404030000b00e004800440c0380001c0b43c40c407070030011610b000c2070001444040c0e510317070003200581c0c09659840c500240900f40628003202c800c004001092400000a4410f80c0c035000000d0b03582c200c01d000c100c3c45880f40085030f2409401400c07a003880d552740c03103404000b071408480185d40d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 701431492 1250 701430242 701430253
    0x61c020d030e090703110901030506011b051b03030301051f140408060402130207150b040914031b06152b051b1504170109020d11360702120d060305 65
    0x7403140170344180040703900c0124266003000c180d038005500902000c3d0206060180e03050841c0800004500200d03d5140f194014107411203040d83e606441d001c4504849210790400d10041c01252511419400302e001c5055440e17a00c0d600b03480003901d1103810420b40300340e0510000303400b2038040000280756003d14801d8429141407007045241000f24015000300402401c089c2e401580301944580002c1010078005100049066450742c44092190a004408d091b80d000032a100f071602411040324800d203000d15010388028641103210103815010308903901d01c00c45a0f880700c907a00f17000d40780d0116841124000080c021030b506080c4555540d002500c407810f014230480701c144040c20030050b80350200c03980700085070625041080a000c02d4400d0018100150350b214185805a5542c0100410703041c0120252580e001481092000c1d5034604141c2d191008a091401e5000d90940e100c00d6580461805421805072116001241071406008410003004c4010482d40d1085aa82e80316404076441132007250b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 701432742 1250 701431492 701431501
    0x30308010b0c03090d14010623041401060c0f1e0506010602010e100b060c12030114011e05030a09020a06121a0117150d14060a0e06061c020d030e09 65
    0x4040c0b0500004441c150000d00400c103290030311844040340303c2c1c800c1d030b8040021041207549070308460095000703160283c0110005122180b20070200403090384251414014165141e00400b00402c040c0719100401c074103001d9040901013101d90020a8980c0044903202c1240610300d00d204000c075120068405000d001c00000c1d100d4014480c1e400354440d40c0d00501001d2283c4001d00004240f1400559040b85082040300d0035140c3c20720402c1540528440710b59202c0d41410103d035026a104807040d8180150110206407506031480b00e2030304869185007641c3c0d6581d80c01c0d030902c090542024020740160740a2404280c00d500309110051076803d01908005a0303802c00700c00703070042d0101d401c0c20f03000c105400440440c008800e5546503001200c0b0f61026013905c0f03a400884c1440d039560b6820b0f200a52540208400300400f40b21840c1c20010710081881028002400141c54000c050042c80c031803030540e0781a0116080c0000c4142c20f6680050134841c07058494103010344146042c1c4051440b8042c41c00004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 701433992 1250 701432742 701432759
    0x70f26070b071106070f1101022208010e0a0803091c0e030c0d080909091c050a03060b09091801060302030f0c01080603210306060706150f06170a0903141303030801 72
    0x5903410443c3c0303004103030b9600c980801395004141c07650b00c202001440300e5600030203a02400140305a6102d00951815000180581851032145402102642e41072961007441c001c0d000400e05d2020b034210105903502d13100d00c030107180392049020071100002e05640d018810181c007d03030ba9400c125825000e9901c0d801000080025009400b0801004680140700d0007045080c00d00c102680304220030f0403503201c8034800c80c5121540b400810000001540042c491400e00e6140c050600105205070441e42000b4001c400a286044000c2c180c004500b143c03003e407000c00c4401d400840040d034028081c0c170510140c42d00004d0b1128480d10001c2e0102c1c1510000c140c41d8180041c48140c14645507200b10f0f0902d80340000c54605901c003410b041d9022006002d0180841c24510840001280310200000c0c0310b4500201c0c21407562055101800744400c0020402d4844140b21249034800f4294000140d0b0464514094a03040101c2450010644003c21801c1046110b0002c040030b6070b0090300c8000311a82d9550f81d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 701435242 1250 701433992 701434007
    0x1b0d1107120831061d06040b010504061a1621050403111206040305030403020a15090c080d0c0b040c03080c210f0703261005120102040803070f26070b07 67
    0x180c00c492910040070102103406640078051100c0b219000c0d2000705c0c00c0712074103490018150307070903a20045200c004101030f10342071040350700814090074940001162000d000601c2d00850b803082e00e9800e900c0c40c0e948200304004820200248480960101c00081150010100c1e042408112290f402c18402d0341c101c1d140074081d4500722a900b0000b0017080d91548c1d401c40d020340000d401281544103000101000a5440b04104800a99214001001394050030a014040203030b5005280740d4008100c42001d4603440502c16413841d0304400e2100c86500d6525040b1544072880e84094a0801c010030110104400480e84c00308803041d106400340c503481d582c84c3e000203602c40c0c100d4141d48a03504011032000680960000040030044542281c0e08840405103011401411211a4100c00d4500c0050080e80340241002042c0310f0004000c50500b4103018816030743e440f56003c003504913a1076070401c40c01c1095100004814548984c8000e00c04014910404074a420100040303811a4840340001c4145104203072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 701436492 1250 701435242 701435311
    0xf020d0b19230d2a0b090103150b040906030c0b040b04090e0c030111031803070206030f09100c030c0906030b030a0201050f0903160302091b0d11071208 67
    0x301205549012026140e5901e00e5616050740340303205400c4281980c030f282005440900884006001c0010703030600c980d603502003110b14803540204500034044508600c058824a40c02070800040b074000454104c000740b00d0701e07030000154400c001008110001280c01010440c0d2080c845800d415440d405040320030300641c050251220801d1100300320065842d00555080c50024058074520504a00402d0a640c4200111881110000144801d251000c466070302c40c0a0018080d43c113081d41580050318030b21000d01100c0000e030054010814040f022b01031900545441c100070004501c5c1942d020b000791950403c4c0e500420800a0001003803802401802c5400310018080c11047c06546c1c0190b036a03821041401c21850070600200a0680b8204001c0e0024010108000d002038554410003042c100020301d04482d101e0340111032803641d001c01d020380d241d090715000c010400c0010000182c42c180101c04002c0c0180c055195090394454011340ca5600844003120000c1c1103080344c880e0015290503404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 701437742 1250 701436492 701436529
    0x20a0b011503140f150406120c150302040e1603060e04050f0607090b190e061206090c070b0406050405031c150b040501020a290106020d02060a06050a0b070309090f020d0b 75
    0x700203810311111454201e40c40200900014543ea29054803800c48c0c0c9042c081110300e8586082c081c80724000c03611340303c1048181d514042d8949824082c9100c2400e202611441e032803800c0c501c50340040c501030b80002c0d000d4004001c4040282c985030a2460b40c0b0481011014990b000b09004150034034070440c2590180d508c2c1c114400d24042c1c880d9002c940305201d01038504100a68040400d550b6a00d00c00201a03030004500d80f00700c00d0510030704000030b8403001384c040b000101e410410440040c1d15445403580c040e81002000450ba03855003801811403045140440e5203039904030800440d0002544800004074100d100c01002640340c0001440c98440c1d401610b0140e0f2222204100007110f140a0ad042003a910121005200b01ca42d20100703400000e8200c0000750300080014900e0b0b642c100100c40e444042032409200103403802021908000c200d006031400d4010000f40e0320113141c09222281d00134070b103500b0f040107034a40e00301c80040250011840341d02c1443c03c060b03140741d0a2a15915281241d03e501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 701438848 1106 701437742 701437771
    0x3060f130314180406091a090405010216030807080601090303090b0903030c010e0c10051303032715121505090709090c05030a140f0105010f020a0b01150314 69
    0x1c1c3c0004400d9441c003078030032400e00c41191f0402e400e00025260344203039440c0e80c00e0040c0644100005100c22501c00c0c41e1480806d98084c491030701c40d10859840003101e0316544011200d01da0a03200103000520307201030a1003c2c40c403000c0140314504006003220300e0180413140c4603081d250302150041c6030303801244c244e181905180d410302e1032400243c0391083c600702c1f6600510240141c1800060200003004540f04c202d220003a402210000e1043e0f42607203507994800403078041c40001d0700e10500050000c3c801e000c4000319801010b1100403130070b0442d1101030802c000d1001c0c21800a085508028101e0f2001810b004640302d06091f2421036518542e80b490a80b400c1c0b410740c0c0ca06420707921040d031144200024a0362045405055803c24a800400700301301c403004901d0006800300280c501c01440d0700000d001e0152881c140701d4000d5a03101401900c1c4020903268030315104445090360005c11 = true := by decide +kernel

theorem cover : BRFrame.Cov 701258992 701438848 := by
  have h0 := BRFrame.cov_init 701258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 701258992 ≤ n) (h2 : n < 701438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
