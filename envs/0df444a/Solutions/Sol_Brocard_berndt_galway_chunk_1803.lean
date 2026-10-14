-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1803
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:56.528986+00:00
-- url     : https://prove2.me/submissions/c9a98cdd-2e0c-4e43-ba82-a98d965071e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 324100719 ≤ n < 324280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 324101969 1250 324100719 324100757
    0x503060d020909061009110904180602030903040f170c1327051c0c0803040227041202010e06010b09040905120a020c0f010816050c2d01140117030909070c02010e01 72
    0xc052a2340c829500c0d00120314582c140819080714890300000155600e2800c0c0c207909079030364043c0c400d8452020314580b00169180890b05200c075144400300207002060395481c10012044040044040f81c1ca6a483c41140d0b1000c00302c42441d0351003814440c1c5a00c0316000e08025041c107010f03220181030074800021007031042b07601603c0950516407028280b5140d8542e8008a0071703800e41d0b0700004402580c1d202412140380c07a00003007035101c0c4d8402c48407211a090303050b50480c241d038414910022181d04c1000103010b100c200b48090b04402c2c80c05400041c152246880e10751408406c1003000b43e00c0c000011340c1c0210103605001900150b0400d81d455440901c4520008090702c00041441c20f07400480324001010600c940200c9200022490460700c0c01d08200000062511600d4000308840d08411607510420304180100b00708a07030141c03801100c2e60303e44101404016040c041d080402d010410420155a0701d503189035000c1c0841e903484010b2072070740d88009041422551440d13814000b920380c20344030009a03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 324103219 1250 324101969 324101977
    0x60105180408071e0515091216020301020d020a050307110316030e0a08010606050a080a0605010804030c0c05030a03050904050f0408090d0c080706020d1409010f0503060d02090906100911 82
    0x4411000303542d440c00784c02d0041c0c007010000c11144855607a02061000d01500050075821060340b140220029122100e1540d51000300e41c55045002e03100f0300c0584d0030782c40c41e00c54111280f40040e001525190f40b2509920480c1c0c060880754004c2000801030200301d5a00102c40303096a20f100d00254034003291414110000e40ea0360b40001c08000001803500c6c600d407914185080101054002480f00645500015182e07400c04468040040d5407407000510210f00b0340254400c0351810385400380742e034480e030b01c040f242441c44000039101040702e00d0001a8944041004c02c000e18065520f141c0c0383c0c0b0242d0b0800c02615405003004442072001c00038000071940e100101d6000780c1d011148413501d811180307400108082c041d80f0011442c000c02e840000c56540218074110111525516480280380a0007211000e008114174103000441100101d00da00303006100654009500400302d200c000c42945c00100750714003c03140403410745c0001c02403100245040e030258018001c141002d01c1003640e43c03940c10240d402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 324104469 1250 324103219 324103223
    0x13170703020d11190f05010e010203040e13020102150906041202010b0a0519030f0b0a0c180603090c1701150b04120602030403031e02041a0406051225030e0601051804 73
    0x140740c0078034891640d5034134540d070303502c0c5050441c41c0c16a0750f00c10541180802c0c912a0704e01003174050b4450301a541c400f00032a002d0318486440301c40903443e1200168948881c010080b815071141404200300c00c1d201c076807407502c01c3c0c00e03010082800b071901c2c1c644028140450454401503a040410f280791503900d511140060710420354040301601e0740120a401c4505d060391010382626214a1036a042c04420380d5101e20485603c1c90a11050390310410882d4851000592141c01c180c46510500c0340500c65040012014000c0741c04101d10b40d201c0c0c145002d11110082001803580d074506c0c0311100c40981ea490071008001e0035400c0c6003024902107074640030001caa14014041355000000408040c040d5018050072480f0544a1144142c0e6083c410300a51007030203010b84540210040e0311144400408840954620740c0d00d16042802c2e000e0306648850014241c142c0c07011180e44400c2e200c203401c42418580d00040c1c0d40c0400c0090f09010b105003410410b0b0802130140b451005500c2e0300002d510320080e0029 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 324105719 1250 324104469 324104483
    0xc050c0108060a15020604061410090902010509100203090a0608070f050c10060f030501060504050106050a030b01030e03161e081b070e0a140a09121d030313170703020d 74
    0x16a5103400200c1043c50360300030030301c40c4007590440f10300c40340e00040c0280f10383e21a940c10000e0300850301045070600c0c0225940040a04d20400c240b180c2045034105100e100d00c1070511904103680f40700043d032555221a102c000607480414a8401c0e860981e900c04028403040c10043c1c0316003030907000113003089458404074080c0940001d400c01c0c0600100a400182d4004020030024140c58a6001001960510040d0344075070078441c010800386010322829041f6800c0c0e4a07028582169500d051f4040c101542d40141819900d8804440183c4240018600c1080d41480008441c500f03160241b5455003161507a01b48114151000002900140c1180e41c2c48040e00b4020078082d401c112114a85420342d082803900000743e2082c403000070b505070441c1c0d81800c042e00100380c0c182e80d110007081c02c81d182e0410261a4982c8084240e06250154016002000c1e481c0242000c4450b05004607141d42d2001c0080e08083c96030340020441c0c140141005d0810910000203409139510355000a846e05d142641d02400030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 324106969 1250 324105719 324105721
    0x150402011e02033108150417090a03080c01230106030917070f0215090901050402340b07020607090612060512012f040e04021c0c080d0c050c0108 64
    0x2503000f081501c01169001071408030784460a800c0b12a440350b000440c1d42682d00e0f612003c030716004017081140c046500c0b110042c225641d1510b841002400b07070591030301a8081003042040c1a04c403513848034083e40c018804944d5541c1c00740c00c0f407401c58201106032075258081561500e2207800210940341181c1d040e150200300342c0344a0a09001c089000218001c00140000d644810030a803000480e408a002300c805a031503000d0030101050034070400d42c0740c0c0d0f44601c44ca030050101c0d18155002d4141007640c800044001540394210038581c9148603040050581d80e084070504118010001d20b500a1280c03016250a04004001500c2c07240c1c140038060500400000c000b04031400e59100d14003c00b001090120603104155099000b8114818461211402c10344425001405901e0a00d2810a05102245800c1c6454100c3c0d8101c08060000c903032001c6510700a1002c03550003941800c05600650b8003400300c2d4034100302e25184c03608800340c02090100c504d40290215002043c43d0006007001c0c2818009 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 324108219 1250 324106969 324107027
    0x25170c07050f03010b180108072103111009060608010c0e09071101090b19061403101a0a0b18150706050612100f0b060c0c060d0e0a0f0515040201 64
    0x25141c03e507003003070701b004004000e070150a10290241d030484000300240c4500b50744a0140c4140c124000c03207407524030a0051074810003c5d11680342c07c1c03500303c00d0354103690049500507101400e95400e18401c1d2000c68807004c003407000311420b11942803682000e00f0003c45807103003030000c200092801440360342480303000049062400700c207410412600740e10845858080c81c0044540e0b0440040701a6811050318041c0049000307551032204825403180200100201e440c48400100500a0f10460009805665413150217a07102e0b00128030292003040081c0c0d8649010420300c0c004600600850340c4500029441511081c1c810300441d031505401100104160751004041a41844004a6000b444c0f04450b00545c80c800c095105a5004508480a03c956201c540c2008018020070052a0494001c1154456140340900007070400b4841d084022903c0380303000501500313010010509542d840c4010549404000080c40401c900c5087d0f050409003c0c180342e00024682810100c4d9505014901807070458 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 324109469 1250 324108219 324108221
    0xb06090f010c08090934091e090e15070203090105120601050c100506100c15020a23040302010906110606060307020a0206030109091101020d050d1125170c07050f0301 73
    0x402414098202034007801e1403140c1d0b0008441d120055002d00403400781c0c50128946c2d40200700521015079036890903040c18036013208500021744100c5281d5401503000020a24100d01600e00b044580760040d00051101c49a442500c0341d0050100741190002c1013006110381e00300d400d4845c80d4503072010034441580d400340103880c0c81c45200908505403007689103d00144c41d2642200b07214a40903038806149117034110b415103c008403210000c0c407801e1111190b0403580c41590203011444010300d80b40189202207580c6070083e4041458504209000103824000d65070880714a8000304013078034161030043c1c0c15550b01e40e250078014106e03610640002002c15120f9200f004081c680c40c1e0002c280c0d07652565503240720700c0182110700088400e0700b140ca50350840e42d0300104044100b410141c03501450700501c0e00590006151031203003014240c0c0e0900031603441e0301d00701404000401032401001500441800d00d4403069500031000f120010081222007203250000c0f0740441140e40a80f40404240030b2003000038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 324110719 1250 324109469 324109477
    0x1806080a0b010e042c010b06032202130e010b0a1412160e011a0910080408040e070e09010b0a09050402031914040b0a060f050111010e120d0b06090f010c08 68
    0x56401410510040901c4994048030045c012031216100c015803c03500703007582a038084001c3c0a50242c005c6c400618050044406203901211000c1d04090b222019400140410f42020070042480e42c1c82d502e040e2501401d100b090403840c03046904030100c9280400ba1103928084000d1940a40c502e4003c030114880200f0170400c01e520b59080705034005859140d0015140002d120ba40c0201c46000104440801050212407041c0000740000d01010341d165400e407051080a00200c400d074008100002e00951202c0b0103e010355016524410f602c44080100041d40310181c100f07003440b03a42007000304241c5d80c22806c0581292400c2d500942c0300d5445006500e80c450186080710503440c101360f18001c86503118503000d440f681c440e140c0c1011944542c00320383d00f100e0150040c0e011401c0b9180092209600403018060308484003000400e0395000384850a041c03110a074121151100b0200e20509180c03078900a40d8000a41559402d042c0041c20001030803050804d04d015050180f00055042400030407000c039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 324111969 1250 324110719 324110747
    0x15050a052103042d06080610020307080d140603120a030c0c05030c030a0f030e0303010303050d1e0b010210020f042d0e0615030403090b030a0204050d0507061806080a0b01 75
    0x70301d49403a62984813804440340320700310f8070f02080b800c41c8102d00c1901040d0b00101780c0303c2075035940305160354403014865001402c03540710003980301c00d00c00c20000802d100d0051141c10720300c510106120088078000c040600700a800544240c1001d0451000038620001740c451b1911186008141e908001c1812740d900c040d014030103400f900002941590500000004122402c1d00c2c0e1b81d640c07550150520100c0071140c402d40c5903080d0340c004000410200e445040034200f10107803c030b800902c184081600c40e01d0f414a140d5001461921280b15544c0703580c050000303c60710300c0608029880c1c0045d2000198107442580030b41181343c1040710b0091b0804101c890030283c20b004056440340920b032542060308581400700d410310301c190090540a5610500c4c0e60980780125407545554003030030300f400e0703e8141d150801000d110005509000001d01c0c1d503240c04a03401020701070000f92062034100107008194600d00d80b91481c0d40007081c0750402c255030f0300107600b41d44030f550040009070800c64000103d034070511104403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 324113219 1250 324111969 324111973
    0x150302030a050102120708010303051c0f2a1404051c080f120703140f060f03031218010603170f07171b1924020304051015050a0521 58
    0x110078200a0150300514803283c0340300490105588036a0222410350b002d00004000036000d01c0340101c0c110419001d030358595014a00401c0c00d141d456440412241e09500c9174010340502486140b200c0c9a00891b44000d814619108100500c00d91846000380b25611410740a03040d801ca00b0b14440480c81c0e0105030b055407081f61141d50340345401d005022a084082c0d84108440304102080b82103000344200c410b10890507114980c45d03900c50a0051000b44000c0c24180c1002042d880c001c0d040c0c1c1e0a0004014a5081034043d01c00c40c1002105210140b503019070b20075031689082801d0000c51070464085500f03c2c11700c1c0c000d66035125001000035090241c084028180c82c001c980d0110f070035240d4000760004090010150b60004400d898090ba940c0309104540c43d01020042c08074040707141290001b252884d400a0501c0f4005210754a40480e8812541580c8a8200d191140f0f042c221500901c2da041851417110782a01d410070300001c03101e45407881020710528420b40ca0490041462200e06854585c0d001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 324114469 1250 324113219 324113233
    0x170603061b13080604030f02060f040309090b040f020a171308040b1b01140402010f02011505060702030a0507030804051c05060c03131205191716020304090203070c0c0905040308070315030203 84
    0x46c002d81514000e078511000342c0181e5002840084455144912550301942c03840d43c40c1d403030f003800d42c002005107803401604261960382d24000310441d0b0004000c2c1001c40e607160440b02a4002c1e0707105600c403014202c410030340038100c000b03c08644208280c0b0159075429516036500c8405545c000844c100043c5c5101c015420103a1100e00e100e01349100761b11803030003a00c40d00514054184103d00700c941c107070000b02c0702c230403203103802d00850418401038004a41f010b0115903500d680c54031450702d41030f42070f40120b1f0704450006051110703062a403800c84a110341d0b51040c40804099650345911088020020a9680d9020002683c44040643e4140351395070417103000010700d02e04c6080241a0b90002c100e415000c000000c03280100c40c4500e449200190540a07a242a034894000941c50b50780750f1460501140700502c0f0105074030f2410710003580103003815140c000850415240a0070908500d40c40782c02814030704800c10000c1f0b40c22451590b8080041e140015000c0940c1b40151010a101d400294251084d08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 324115719 1250 324114469 324114473
    0x80f100b100e27010e0f0708070f020c0a0b041401020d0801030227040c03031404051c0c030b131b050d4101061212031119170603061b13080604 63
    0x43c0180e0705032004400d07000d48035551141103002081041e1164030014503c00e0000381d90340d11410000c8494030f03492041e40c0c0d00c450110000380d8410310701d400103075040c08006800c105424944005e103802034020300180c91200425440942075400510020740a40307504030300c0c50800701020f07040a00da0101440000c01e98103003801e04400196a6000c11804554440c0c1000582c56414090714222540180001c6181c40380c52114101c044803810100d4034041020300100000c1c01c001805c0b4800c0301480d40c01b180851150a01e51100b260f00264003036071041c00c00b000d000544030761000b0181da0b038000b1044840700590540d8a00380c0f94008405c140781c0200d080950058074483c885075441c4006c080003c0c4103a40c1c50340f0440e103807803400035130003000412081e1420080703d000742c01041001d080e011849040c403012100005031b0555180444001407040e0307034207030841040718200640106081d4000e1030107162500d260100100295001d1120707110105545095481c40c00d000806002042c05440b00e9003024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 324116969 1250 324115719 324115789
    0x606030506010801140a0b0c0c181501090f0e071e031d0f061f050a0e0f0a060b030105060d020c030f13080105040201020d08090115080f100b100e 64
    0x169074007400034101c0800024600d052404403074001d603006150301d4a2178a0f0800d1069240c2c807a1030780311200d000b05503524410baa203803200d000070500d082c030f400c2416152151a11010b0040140028140048100c040c07240c0c520000f04081a25024143c003120b503114080261414003c200c43c0c030b04007002e146078030005107905030406009009440d008071640d004505142e502e0703100e1045054403d5002400081030062800541a0100740e10f503003030724016480350082423080c491a008601c9000940051000c450014400180c0c48035620300c082000394241003203405980b10600c1094452080450003194031610307613045588000c01403084030b03520201070620f03180c0e41d08401207401d582c0b00388440001d208081070080500c9140c0c164003814594401040550702d074800030388220001c0d9694030b24260035480b01c5030305c5809860094000c100851040300c045150004550140c0c030803908142c10076501e5110440340545048003400c1c0010f240100c440400c10b140345869514bd2001d06040e032030b008080c03030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 324118219 1250 324116969 324116971
    0x70603060f050d11060304210206061c05070605030601120e010605150f040603020d1805010f0510030308010905070e0306161b02012102091324030803041401090606060305 75
    0x700c00c1440344140c0d85404000090f140700d080600b14410715100f20007180f42820045503c00d11840303c81c407103180441d50000b881e2001d00c54140159218900340031140c1341a8a01d140d10710a1150030103e001c40c50313518203855078100d10501d01480340200114450317038081ea468a42031000c20310304002c0080fa41d12100d01810051103840c3c0940c0300c1d68044003211103080100d4000400c40740d2940c0c80c02d0311308282107009501800c013003807001c1d039075001107004c105555405a602d540503000205106069503c0c840c220341c1c0203013083d43c0072402200308000094100c0003803411208688400166a903c4030800c2d24400d042c4001654140030701800c120078280c4402043d88002d2050b83d03400a00154880072810029650744007038041621212a04000319030503180c1100ba103500b0340c0c050f05000400010901e4510350b2217000d4100da8980c01c0c40e40704003064420b21f0079500540086508854034544404440340300281c8082c02a500703002408030614800d402402480368803102c1080711903500d400c02401060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 324119469 1250 324118219 324118229
    0xc151801020a0804110105190c06060306050408030a0f0b030d0c0606031202060f010806070c0210140d0e060901090b0c030709081009031805130b0102160909030818030405120f07060306 81
    0x5e440c00d0320078030b501c01c2054480f920452014101c004a003210251010308044004503074550321085d010000413624041c00340070710304c285912034603030411003840c030140c682d403040b0106d4143c40d0804c0314003140d9000860301c0d14000c03141040c201d40000c5050180c00740c44550405082c08240b685a0450142e0019905200e620fa00f0017041090b43c89100542d2030b07010640d000c100141c65680408054607041040d100c0403817807410604543d541c4890224141c2c1c000609032041700341d5800440c640e5440074003c051344001c103800204002e2101c0e0b62840903254000e007042200d0280407001492242c028006e281c050040c0d00c040354107110b2049564009810070b12400c80c00220000c424400da00d10300b5411105440c001840340325030b0ba0400110100510040c550503045110710007801c4080d020806201c07004c1c283c0342001003103401c828103014081b540040c151074030007850610b00b48110760010091b80c0c00c0d1b0700700700e0f10b1080700f40305680d01600d80100881c0007509401000000140075070140c1c01401125 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 324120719 1250 324119469 324119483
    0x10f05130b0a0e090703142e06030b190e07030e1002070f1a0403020a1b0e0103110411130b0306120f1507110304032303040b0315060c151801020a0804 66
    0x56a0340801b103080e2500000212547c040000206485010900391030018009244201041c0c600030744240400301c10710390116020a98518bc0d00080342030128440385e4109180c9180b0f6103042c501070301c0b84080341c801400c40303080565072105d2030b404500a100000100482900540d10360310a800c141d5600c26924501726049091078244400c0c241200302c0141c42146c03d500603240d424426103031000c2003801c0140821040e403a805003c2000140d21440740e02231401100c1094181034180c05000031510014100300400d001800300c16101c407084201007055a000303000d01c0d5100c0d03c8003004900c3c1e03030207180101c1a0b20301407101000b85080c0700048681c506054002008141e845c3d10f4000c2d2003a80301e100d08075606810420040c408a0010940311543c0141c4403244000000300d44012402c1d40c000da00b1160115000100f032015030101c8503c1061070520845201c2c2c6060740c0b0f800c0e4166611f0366052800c0d000b01541000501950070400103845d00b241660081d5130320070f040781c00181030800842d400c503162 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 324121969 1250 324120719 324120721
    0xa030b0103051e1302010e04140a0c052502010504050a030303091101052109160e040302060f07090905041b080106050102151620070b27010f05130b0a0e09 68
    0x80c4408a1440f00140990204071454440204880b00003400480507414818103400701d40d00f6858500c40c0d0219a00c20400d1120907042c040f48800507100003165030070820000380120702c422a1440041d074420740000c50044002d03c040d20041e561801180d00040c2e00c860040000028141c2540212010700d2180c1e00c010055020f08005480c203004003000c040344401040d40401348819603500c42e54020b400d000032101c3d100c14a509840440c032494014549903074071901408205501000401e4000c990040070206916040e88000c0440e0361a21581c11555103500224040c046010403030000070030038500c00201c40351501e02041c06842c2521685006100d0345c40c5069108181c15100350095a80008140030000c010381c003150405d000141a0b040741c110f40c500e01201e40b404205110080c014030981e01d460740d0501030307130100c01940224000c42c0c1e0440c0104400c450b0380c1c4100f42442040003400d103291207003894a055450301c0341076088080d1000001130403035401c1d07400c103041c0c1c0170008085a13542c240b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 324123219 1250 324121969 324121981
    0x11806180207152c010f0203010b121b030c0703030b0d060b0a0501090311040c2114011203090e190e01020705010b0a0812071109040f02030f0d050d05040f05030a030b010305 76
    0x440b00040038180c0c03184c1c00304001c11102c5281800c40701280110301c0011a4851018520804a0307000f039010b40240d400010301103841460600320140c1c80444040001c00000400410500d2480000e24080703003a500001d46104045c02540220b180700005444141d44a060b031422a0040130011000c1d48280345200002a0540c4205100d00076654049402c07880c0c031051009000242031058010010311441c82c10b0f055101d0386004c1941507503418a5030118850b5115a00426400b406030050080d0400420451002c01d412040d0901191090900390341c841e0b88100b030040301a003170024200441c07404c00d0891100c00c8030540241008074002d800030044502143c04100d08441039100e101440e4000c401d002a03a400900041c0c42c109008a01e2080e80c0d5618070700180c0100707800c03202110000341200c00c0400350b041c10001080900103950003401024a00203000c0c003180134240034400e00a40320070001c0c040056001c103450150740d0040449403221040d9030040d001d405043c668a000919002c00141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 324124469 1250 324123219 324123221
    0x7030506012601050306162a0f03031506091202090702190804140409030c06020903010b06041d0f130b06030a02060f0a0f0e01080f04030e031209011103040e01180618020715 76
    0x24041d05645640a102d4403005041c0c418540c06001c03103407140310f030819520120700b440c10040d1520b0300c070384ea002334108041841d40d90340c269160014810005c02c0e80092040300315414001c0e100781e80403101410300e03a0700c4040403490001c408194010081840540310100300d0150054016215000802604030500c0e80c2070200300c41100701c0150002e0707044090039000c40c0301c0e0341c001d041d14400600041001520a4040342d0558040d61150209c24000c1d0300506900140002854201d01072440e003000700d00b05031914000445e04d074070010b000c09504e08013003280e03039a04100c29821240c1c0034042c82d8481140300d902144941001c0980c0b400b0864908040340354030722840c3c51403103251058581c1780352500e46480f003c0038108018412400e001400c0042955568100300005000c4502051a56900300300c0300010a510749092640403194000d110600c804607c0c00c16150549800461440e04140404050b501501da07650003501c0070030038105581c1c1080744640040115a00910b0320130a90000011000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 324125719 1250 324124469 324124501
    0xb0a0801050f031c051612020c01030b012118140706020c06040e0603010e070902130b03040f0f0510050108010b0a0b070b0105060a02010e0708061b0304080307030506012601050306 79
    0x942c0743c2c102ea040400055400b13100b440d0580c0d0f451400c00d00b40f00a0004049021a281000b680c403a1008040c1a00065041000c4e00d403080003841d06001c6e00440d44000303080500072f00c407032082d40803419040c54003181056105084100501082c025402e0040c1445030216102a502c0d0340d00b03018030140440c0703290000a0310341030307240c01908413480d03c0d180c0745400c0210b60001d4100f6a05548800042a0070a0b0812011000d84880740300184c2d40c0400301a0047e809480f50308c0803410070800d004200100c1d01c0108032003110354000101615220322454141d0030422452801100781340782c11f00204140e04150700c9005180b00c00d6404203402c42d15040c1003a558002c00c0300040100c3c017404014001c50424002901844e00603000101d030321050480c11b54141541c58206100a902c41d501b0489014081e4a03034101500013003550034a981400d40702d0006500c40180080e05040e00c42c00860020b074032601015500303505201064540e801a107003c040000828403850307103c0e1043c0f80110708404801c41c091 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 324126969 1250 324125719 324125749
    0x118080c011503050a06050406091b090b010306050102070506030417130f0909020907031a0406230f0105030703021c020406120b0103020c0703020f040e010c020f01110301050a0603240b0a080105 85
    0x1803484030a560381b98400b41400804c00c40b040ca44400c0e00300d0002e00c0c40c01c18030300d2584800d1005c581050038a202c0704101d50115000303030304260500c04104556600171070701d00c05545013640da5581e01e13540c42c100500070000741515180c4e44500051251520000a800001501e400410700821590f81c1c0080c0c10135a41c00b000065400880f03240841c541e24029806240700050990480d012405024001002c4070890380c0001540741940d1280ca0344d40c80c101c030601c81c0c4038404943c088005114000020b01c0f07800010260018580d00089051605030042201c8028652541c0195512911410020401112060040c1e0f40c5c0d030500d07101c2c2200b503010340280e07225400d00320001c1010760320f1602000054489040030350380083eaa4030385440e404c0800c1c05403014406641d001401000c02da134442da404c41e40011032429009030180b005022665411050504403050b610f001f10383c40c4248030b09110021000c04200c501d44000000000c1d005603000c01910180081d40c403024031980c1c1c3d450a20502050380340702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 324128219 1250 324126969 324126973
    0x7030207080114060f0a0302040e0a0605101a18060a0c020f0409050606010e06120403200a0510050402030f06010311040b06030903190215280b0a05010509030118080c01150305 77
    0x5289800c00161031481c1510040148017055a00c0c0c009c18215140c40907060800c0e000745000206211140c00703000c1e0460201d00c4114041407900e80c840422000d40447d50010708000500070280380010724800810783d030000d040c0e43c1d40764940769024120301d0044200f01c1c029010300c59081100d203001d01c500a000740d00000646200d6503800300440b441d4080140300795102c1c00900c40f54a1011448090314410391007a242c02080500c0d81c1340e4110654050314000500e5444640c000c1c0008102082c40e0040d13090f050070100f4152200d00c0041d003030000301e00704001140300f80400041840401040700341d0104055404100b800f203444203101517480100c40000f0164010070080144040c00c4000060700155441540c01c40d001821856441050544a40c0d91824115006500c50300403044085112103810341c0400626002601040725000f4601c030342030500c45c02007200051514290000004c8603c416080c05c640702283c502044682c00c0f03070700d20034169880c0c5126040303540c140554140543e900240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 324129469 1250 324128219 324128221
    0x31603020114120103050c2e0309080f0d0c080601050a1704030e090a0504031701051c05011112150a0e0408030405030906030a020d0b0901050d030c050102040b04080307030207080114 80
    0x159000d0b08501e1008141150800116072000000200e450107148590050180d0170706c05000c00c213a5030b09003160313090220500c250f0522901700742c520360150000d15090100d0140158180001d141c0111011180801c00c0003610401300d6030f0903444509000c0841c0c5510411b52a00401107905009200012011803810700e00d1916450648071a103500a109240000d10001142c010445001007692140c005c2c944a070203020801d60020343c0c2a41d12404c0c00002c0d112985080e0002e290303948107800c04106290319103442824000290072803a800e010995101c1d54501d54080080032194046511184410700d03900d9042003458440f5014013120307902c0004c21840d0b2030381c0e251406640d0002d04100c80707520003008803007101d40f28030700618440d0141c5040140c580880402080907100c04003142031080c1e113403800500c0569a21f20344003907807640500c1e00070400c10381440c0042c0207110360f030401c40b03e86c00b0104000426800000041181c140719072b082c2c540d05503072030100600303a44c0810003075010480200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 324130719 1250 324129469 324129473
    0x6020303131b0801090b0f0105060f030c03070c0b07020c0f0d03020606150d06180e120d0906021b0d090e070e06161b150203071220101a031603 63
    0x910911500ca0200e041e00b0000c55a481d011400c40d80b410034111401c100b04420008071000b03114001e40100030a0755038030700c3c1c900109098041b6100c020114907102001201042205205459074214030303034050107610b02c909001030065502e03d1456105803040c01001c8104d10982008413011340e070f81d0360540081a288d22035004000851240142000305d014003030010b05842e010602602d401020b0204d0034030070403080b070402d100c20344280380720b0002a54491001c2c007961020102c200e510300e101c5260300091180301450b10394080e204004807520a4609511050282030003c0b450402040980d1a4101150f175a48008000d9100c11070700c0a01003002c40800c04154140000200001651310383c600c500e68409507941000403418840f01c2032418002a4144030b183c040081010301c20300d260005604050280da6880c5d42e10300c0d900b5400c1c1c2004510802c8880e0f034003144050820b5890210b0503680503005000303022004101c9035000c00b11103208603c09400b1030030b0101d6075600d000032000891603828256 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 324131969 1250 324130719 324130733
    0x190f1a0d0c020a050a0606090506190504050717160230281817300a080f060a0b0909040c0906240f09030f02041d0d090602030313 57
    0x11800642c00baa40410f80091010f1003d00780d618403582d400a01c032404c00c4a900c2c200c940007010103005481400000d8111264940300b041140c0f030884000c01c0e41d50b81c44038211200a50040f01100707800d04101031260104070f1024031082208107a017160170302f454a07241c2a407114080d80070350103451040d000941c01011610020010202c22181e0b5500b499207102101032001c000d40700c007900003500032550310400d03103505404000400040c24400c5641c0c140781c98082c0c4941100c000842c8039035803861000300c0400310341c0d2800c82002241c0e0b00252103480300000070349040401c5070301840b00200c0600084603072078085201419208a210500e00304410b20080c02503000c0003900c2520480780000300014061003600441c40a840c1c85851014096002c100d07428880c9607001000043c08071a4540c3e1190070340c030900070340c2104d400041c51032400000380007142c0188018401c0414003c000d41c0f42045001c070014010705540c08907070b0f80460399603460004a880780825540c1d03080001e80500c14102013401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 324133219 1250 324131969 324131981
    0xd0b04061d0114090609070501031802060406020a03080901020a051b011b020a03120e0325050d030e06090a02010f030c090518010e010e1005010f0c02190f1a0d 70
    0x400e4400107440005105800e4807004006488a1503070b4481d0601c80101150100c0250007440050090806003004101c403034075001c943c000c090415581c5c00342c2c1e520017440c0401ca014160780160480e43d6171a140d402c02502c480e1a800290040341301d41000c20031000b014400ca81d404100c555a4030305041c0600514184038080c80103c0400d50740325140355850841040040902d00b01640080402600701d10b006801c40304208000342d5028509a03001d4100e080110803030781448080e05004190f43c64400d41c0740c0060740796000103010340c03080c1c441d001003454144d03000750900410101110141c0d50340c440385981e1981c0e881d0700240054130b543c06c0784514070300035004004801107074244410030a40760380218942c2da000c02c1c2d226000e07034000001046022a07030340c6000c1c05050a5150010741e89003800c28040b600d049072040c02d040120541107010798034880c80e6800b9542d58010840350000104081c0060308005501a104d03220480d01e00018811151600c1c45011600040f1070034140154200000020b0031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 324134469 1250 324133219 324133223
    0x10020304031101141e060307030210140406020a020109080d020a062007110117040503030c1c1a010e1008180118080d0c080c1e0d0f05150f0d0b04 64
    0xb0400c00d0001042e8080c056141020300c0140c40342c800c1d292808440c00915541d14810007085085c00078002c0341c0d1030104010065a406079840c0050305003541c3d00b1100301070010300d8103c1a420200b00401d40560100e076200703109000366030b4950003075100c81e132058a41d402100d038400540e1001104500207105508000c10a42d41d048009503113400180b010220740d03000c0a021034005030582c0d80d10643d581c0010000d00342c00760107442c407038041c68190b82d07181c1c1d40d200c09005c1c0e842003a40803400c48007103140d01c0480d2451881503034050103030310314110340c11810314104e41005010411141d1074041c40c0c181020300d10034194156448540c507888121400ca0311002d00c0754455038a5488030f401c4a068161140c1800405108010803980c440410502c54202e64620f04d141c81044008810b202031441004140d400000c00c100d00d44080030034107201c481062181c1c0e03c80c444a61705100d6030001992003603103d24030076400401c1c0d10074080c440c0404c1203829007131050400d0784405000e400034003042100302001e40c058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 324135719 1250 324134469 324134477
    0x8040501020c0106030501140903071e020a1d0702011d12071a180c0103110a05090a030b0c070c170307080d02043308071e090b03040303020301050306010b09031002030403 75
    0x10122004083c00e60340260029115a9100d0f800b00300f0202c90301c100d450303100160030080d5007010131507a500b08486a0203016141c0101000384d010003503554001151009008a07034201080d0f440d2510000d14080c0200c585001651a242e209050140c40c100003600c0300b0844409003000201040c610513968204010a8920204990801c0206c0b0603110030180101140e000102c402d8905a2640f454901c00d4440340741018180304020b083c40c010041602c3c00b01c0d0050800c15151602200483d202500c00d03030003d0422200d4400384060110034000805046008458081e112503c03500b1508420b480003104521030340c0204050303800f25000b139000c1c222010080030050b00c1c2694440c0b111282c40c14805446030110490140508141c00e8140420740c1c0c0841410f0003c03241c03030300940103412401840c401000c42c045642c0d500b90024031505100d070203402c4101c0d0241d140d08140c1030090080d0000d020b024024460340e0004200c1c00034910588013140030007801899a0003118503080003a410260088042c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 324136969 1250 324135719 324135727
    0x1030209070c081b0a0c06020118061d0d1d0109031101180801110909010510080f10030812090607050c070b0a121e0b06040302030a0b0c120403091e150804050102 71
    0x350b400f41c0030003030000091130f000381003007451810803d03040b000581c41402903a140030260040101040048030402d40c006800081101690b070440e403030301c0301d0301102c060180104100001d220b07400505801c03400d01c0c164081441c00480e000151001c0c100d6000c090680c3c61110b81c41103043d88607582d60303440c280090210784112540ea40d0302c41e007910000243e481030a02e012074030302d00074282201145e0050404580103c2c0a005820024109010141c40e4039000d080a5000540c1c0c1400d1240d120015680118116038811854070f06016a88040da50b041150082030003080c6805e10a04c251860002030001a02005103014003030300c07440d4050906541840ba109100e110007822038401d820140c60160b104020b81c0c0c0f4170100c0b501c21150701c14009031081e4428402440035803800a6811507965004100450716201d0704641d0724035002c1c3c000040005195041000101507000360400c04440002070107008540c10981c0200b22243c5038043d090060030140c01d45501d03648135010540d04140100001454 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 324138219 1250 324136969 324136987
    0x406060c06230705030f150105030406090204060b0f03010e0114100807020109020a03051b0604060219060209150705012003160e1e120a02150304080c03180108090601030209070c08 79
    0x10101d049403084040703400441041b03112211006901d600252402d4281203956036400080c009010241018044a40c2c824540c000c54441e42c0c1702e0740c05046d080010584401202992034803030f034001d0181020130381300740b000041d034940358209070b0403520740081c0762403140f50704c10030101e8146500820010444d0340341c1000e800940c4880d104000a9800b80d0301405001080c514050081d048101b407442c01400100420821213a000c41e80c8900a060850305044441081c100780c8040d001d0000096440100b010710380604c0d00e08400240910f500c550028004131035240034810b89200d0f41c260200c222002000019020300040401c400c0001060074079174a0500c804000c90001303440300c22410442d41006248440e146801d240c02c13640c40b0311a00c01070040c41c190f0350100d5401e0082042c0400300c0d02010001c43c081110090590768662000411a522012801c081280742c003142c1085501094460002c81c00d012404035525051301c1e0050b001c0c600c6603c42d090101d0b000016000c098400304400d1210741c070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 324139469 1250 324138219 324138281
    0x52509200f1e03270c0a05040f0b1302071b0315050c1e041a0705070e0c0408010c091a1201051239010c1511070503160b060406060c06 59
    0x8000e0304446910301240301c4c2160b803e603a60301160901043d5910a8107200d02030368491500006655080c1c0d80407880e6104640442d014102880c0c01e940e0000740c404a01c04001d0495010b401c070b40e07026416006021008070b90703844034034603140005884c9544040d01e4070054040340e0400e54002110080c940e141c110700d8849819031100007203940c4030449002408101c0c0d02440709042036a803042042d000d107000c403690341d11a6205614030454150080950000d00100340687c180ca00030301461000784205002d04000a0050300c1034000c428001c000c051040d01052082015541111000d030484406a400c080401c580f12002d0304580c941b900c228240e42d90305504203003400d0134694002d50b00349440c28078106204851030102c151581004402040c0340f01040b01d8151250064007000307030010740e00c14800882c00340b900c2031160240480c803000941520703032183d401c48405040e001c3c0110a240d52283d03020003094600502c41c01c00010206a0f10602052140e40144000200e40c032248084060400b4010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 324140719 1250 324139469 324139471
    0x7031b0c0302100311030a0e0a12030504060606030506030a0219050d06020702100507083004050f0d090f061419120f05061804052509200f1e03 63
    0x4520800c15042001182415108030310002c0c8a82410300c603c0d100305803002170602000f080b0001042e00d884840151550030b000c030000e41504148000c40403e1010409405000b05440440303010740740c4040001c1c0e540c031920906007d40c2c2c00030090b0421500341d40800c881c040c030340c10a0122109441d07000042640d82c80035a54552403207108050303101c02c014010003441110003140801807240070000400010084000c403450040c40d050a1000122500c0740c0c0c1c0c4070b064140040c0c11a0040e000107101c1407003000101d0074030601c1d68104450403440540f004075001e00750b0348108040c0c05a00710040c40039030700906c8050410034442070300a08140f40c00c51180c180c142c80900900129264468a001d4181a0701401e0005a9800c0080c40b50f4102070022070005980302c400c45800d032041d003010500b08103042c000039131446030b822800b000040c280849c9100c0d188952060750710152a01300000c45064100740100c00780b13641c0d00c41c03ea0070000c090204901d10750140c0d40441400c0c0541c490307600004011300c055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 324141969 1250 324140719 324140723
    0x603020a030e1c081e13060f0f0e0115030305040614070c060806031006150f020a0204050106020c0307050114090613090203091f0506031c020f061504060e010803090607031b 76
    0xf074520403001801a00895010740070114100410001c1d075820030342c2e00e41c2c1030b410070505001c83c59141c0d81b03801c1a100900303591030301160140c1014030300c000888058201041d080d070008020400c5168000e0104624843c0e0b10008000c070f003040c003081043c1401250b4858024001449051400c100c503640c1e801038203501d40101001c030341d42c20180042030404001c081640b484000c4100012410510105401e411502d4501c2c208442d124000b11458801c1c044141956030140092040396141c0801035180c540500246000c0d104140d00020f0031340c41540403402084810020310300e028540024031045611038605040d240d00450000510101c0c2440207501c07546400c8094901400c48010540c41c256040c010002d00905100c18041c0d40e542c0483c040407405200d0f43c2c008810284903000fa4100f4400c1c07d041d2810b4095501081a8008050143c03e84400100c400f00110707a1200c2031241041c100b8000d92520b40c1c800c5c00851a01c1c10140001c14102d80a4240064501c0c158a07881c0082c240050301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 324143219 1250 324141969 324142003
    0xf02070b1207030501150207030602130e0f0403020607020a0c050904081b0d030501050d0b0610090b120f07050307020a0f0302031b010902030f06090c01050d112208010b09010603020a030e 82
    0x2004a000d903d44a407134050700100301c281003515000003000350703141c0031804083c01980c0c0c00076800303e801c5101d801810090500c00400041450b200054251500c001c4506a015019403000580c015102194114500c7d034022500e019060500040c401500c20040085031a10341c1040f404685205c4d01e03c070344002541000c01400c0100b8120b20050130399006900860140020780f42c0703000002c00741001d00358498019200300003c2c003074235102141c130403606600800d48a1400103800c00a40e84071009a84200030032640e45140d80c94042d41142c0900c007c441e0280160401072401c40001d49110000f03072450301910440e81094050503c0e0307000380700c01012000e05a9954426402181003e0114941c2d085c490300103003503580b0306102440c1c0c0b40d07101c03400000d040060004107401e400751240d01c00340500c50103101c565111881c90300d0301502018400f082920451401a00140c0030005000d0b9000c0101e0103083c1c8074880c1d1078007406402039000003400d00207044e110f49102c09041030800608002e0600030b02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 324144469 1250 324143219 324143221
    0x8030c0a1a0115030b041d070303031103010b09010507030507020604090501180e0309010e0409060c0806011b051009060f0509030a090b13140a031e0213020a0f0f02070b12 75
    0x581032603280441680e8060181c50840100036110303d02c0c000c0f0b405000307142404582c143c4403000140080c10b003000146c510400784000f4a0120304006518019030b80300b900c0801c146101010ba49400d400244074500281c0002c00c1886119440f52020300384d050300ca401c0032800c041c1c40354001106074019030440c03840c040d40c803c010466200c0c207100c20901403186010800003051a1400c540c0c0300e204801c1c080b81400665184480c958035035a108045250f0840e808101103c0c2c0780000400b1704506440c1c450008003100b444000c40702c9403e240700300e4254042c1c001d00d0785900001c01c02019128110741030340d4540d41e440b094502c104540c060548200c030940050356903460041d4010745440100e42043d00108018460151003861812508080e0765549101c074002d8074042c400a0005130080d00000c04550348500410203241028081c2c02646100b220004c801d080e010800304101e015110760000001c840c1c4840c08103c40c0244440c07284d585540c0f054907500b07502c8900d424800e610502140b001050100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 324145719 1250 324144469 324144473
    0x70530060402130b09010e060303130306020c060601140403060f060306020703020726060621160603061a090d050c040204080c090601080c04090203150a0305010e0111090a090207060608030c0a 84
    0x1005a01c683e00d0484020480c0d1440e4030041a1419014044c041c041031505001c507955a45c10004e0380c003040e103200300403107811740c032454030a003c7e410005681c0000d20511011a15560140d001e80c481c40780e0310300f4242c0c1040c0c038585a10020300810b08038004482c3e034072030000c4040350703041c0020181207001703800410005184c420251515030910600080c24054000d42700500b040104d0f901b50020400c0343c0b0500d14811202d0034486104908004005c0c0e4801d1801e40962a024060400210b441c192000c21440c2d41e0307070815040d442141080d80d4070b074010400800b5010320308021603510341c44c0507504480e070010801003c030b405c990264001018a0f4010310051009103000083c140d8031040a00c0c2800381d608141209658902540c09011a455001310020701006002002c04005240c0200002a030590340d04001d4020500710041003083c0d42050710b681c01c5500d4900444131484000b40800d03684919000d501c0c402504940000c44000fa16004005200c100800180c40c007000f5a40290891070814 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 324146969 1250 324145719 324145729
    0xb1504020c072414131212090b0906162126010f2304020301060302180a0e180a020d0809130b0a230604090b13142419090e030c070530060402 62
    0x2a0f8080000010104906500d8bc0c8494060704c0080f55040102c03809442c292400781c54015890040060740501c0c1000c0003e1503600c01a42d0030305101c00100006511800c1e84622840c3d070090203282c0c004007804400f0010030101d14201e0280c1200390303448059008803c8005010390b80281d00c2480020703004115514074611101444000040807100440c1003480c1030302d28050b00784001d04046209004611081003241c007403104038003442e4020b1003841d10100d9841e00502e150003030600d450143c0307050300302d100a80d81140b140000480d4010003e140c05860300b00c074921075803603841e42c4c084e1544c81842030401548030540944003030200000003080446106040c0720340c54269024501072541094000540500d520f94825000850240e002505207001d488030032184648089450304000c5031030061481400d9006010266515041d0511000b001e19600c0e540d00d00400d207641c2101d030007224041185207441082c4060150510301c2105584880300e000340070090341c0880511080c3c01c1072040100b14546 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 324148219 1250 324146969 324146987
    0x2010b03070e0f07170106020a120206040f15060f080d0e090c0f2109010e01150501170709080f070906050a0b070b1504020c072414131212 61
    0x20690003040c0c494942540c400e18980080e0020f0000f01a440128441610a2400c40c11100c40c2c041ca07941d15582d110300003940c8000d4044103a0700c007039006000000c00703840803070f0301c0c2d011325000256120340358000d444414130807a007100d50340302c61652028006910b4034101009002000440c0c05018002000940542001d1907c00102d1040d0f0300441009105c010981c1642c40096a0100380781c0c849000401064250030701603942c401300804481008460481500000318201048000b408030b0f0241c143c0743c41040030103000d014046000c079070000031104c004601c0f10303510a14503c0c046ca00a0341e94210030341048501741c41e10143e43c2068a0500c4000200e000c1d000040078242c40f591012442d10110f0281d5004160004040d00a041d01180d424600b1003c01e0a80280c010003c55071004000c04550365a0514420741e5600040003031035500d000300716070903641a0b9555031202c072002d24801d2004000c0385e1261b0a8107840f40030582c400305031340821200b510b1095110310072002100d112200b01a0403660 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 324149469 1250 324148219 324148241
    0x5090d11030628090204201e0c0d0809070f0b1306080105090402010e010c0507230f010509010c0c0305030d021b070b0405061c02120402120a0f0b0621010c0201 70
    0x6505082101c214540f1034540d0f049030050724000800040070310005016200c041008200b141550710100340402044008065040c135142519520300c1c00115203c98a01400d4042c051300e4104080c5504402c0c06450750310b03072000c46481943c000c10b444246d501804462600103620705100840d034550541214000c08020302210f0400c0f00311985094001481a00c00410003410064440841c040590245401141c01c030340c85820f881d05280c0f90111a840c6042031408070700c81701a40803103245c050404060500302c07614181c2d201440c202000006480e6110840c074110343c1c00695003000004144140301510b03640304654400741e0f40781003941c20b0840c4003103440da4242c1c0a4200000030007645414108407012204150784043d110880c0c1d410b05290310704110701e100c0e20140001101e20081002c2d01101c0e204500c201d4000e40c0d4100c0030b8842c503907201c150344401422041990150300101d403003203603c03c2c0c3c4140003c0c009148032041c4010a8071001d19600090100d030744075000c1b20040c0b44c0a00403280009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 324150719 1250 324149469 324149491
    0x200a051c0b031b0901060c3e0f0a03080705150c0310091a150d06080f06010b0a21090f03110105010b1c020d060302120a12051206040c05090d110306 65
    0xa454400080300c0d824103110315000d0003c042c80c2d80d000c00540704400d44241004507230700690354066100c2180b08001c241d0401e0107142c110300740406170b49040e16050544920190011100e6030035aa280f03071155210403029515480703170011010216180700984c0380304280340c07422551a23003003c2c8051000d012068010180c0d483c1403007128507181006102c4049507140072182c0004a980c900c80d995258403070350864140309410b08a02241d0210006402d40300c14820004a40c05a84d0310320540383c89000703e050300f1000bc0c01c401001115510144420300343d248140d600081c01504907542d40401074044c5074114041000c41040b4001da550030f20403c4e00600000c140d0303a281c1469100b01141421200f801c0410442c0c0c00724500301001601c0d4810005194040e10b04581410003107a0503985014449044071005000850740c1e00a40c07096064480348000250205100d4031600c2c00c02c40a040ca20000b0010407006004803140307a0380e00c059101f0300e00c1c0101d800501d1b8046c18414103090120041c4008009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 324151969 1250 324150719 324150763
    0xb0f0a05010c1b090603030806033705070504052401020f0307021e06030f01090c09060e060a0c021903170918040c120c050f04200a051c0b03 62
    0x90b600801410500c41c1c0c819840b84401c5280001c034442d1203501c1d0001c6a4031454144040101500500154001c01c1c04404440710514024a140c0a20300403400090f4206200c03010b00601800da1403150390f0030792003001510b0289440d0b0380440c08a84080b11140d03070844034000403030395070070402203005120b001c01c0c0b000d04021580304c002d040c1d0f00c3c4200da000074024004022107803c410706260480441c3c07203004291a550303080207861611650828041c031350b011880d01000c00d01d0240501e101c081106c110b5200d529980c8015010842e1581148941d041480720300b0b00c0d1940140e4070b054068843c00c0070030040e02c0c01c1d035042d818254000a81481c100071032700d03c01c04c00d0407007680da1048604c4000c00b410904801301e030340fa85000000316403103900012984203000441c01c10000c0c0081444141c3d4020b60320301103078103e09000c02055600c200c00d08000303400716205040b03609801100820245105050942c07501003842e01000d02c008615199001d12641d4407605045032405001c10f1b4135902094580c0d60746 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 324153219 1250 324151969 324151979
    0xe030106030b0c0f120103030c02031c09030326070f0306060c022407050a03090302121507080c07140a0501061a03060409060f1401050909030c03040b0702011e030b0f0a 74
    0x10710006480c03c84045030200740a40d4112041040f03610b820300f00e84400596513540e00e800341c008504004204e119018412500c002c3c0c80d00c2d8134903010810900e03950000401c1c40d68a040c1d81c00c44441c500540c0803441c0144210f01c0769250501c80f80103015698800d800030140135002000c40d10903801810070011942481000360f5100e00d2010840c400c580d05d56100600050030710071682c492404010114002c0e401c40703800303144e008080001164009d441c19270f0400030403e040c944408081c910351b0340c140100740128002c1440345540c4c03980000854100c52910344140c9604210141541c18030007154406100303001000820b00541e4004c11421803009081460b2039600581da001c02031815001d90354411000007480055007140282c0715203034008012003582c0600030440c603c03090007040d0284142c0780100d008108008116240441c12501071803e080c00c2c2100c54405500411050b810840384201b45030070844840740b071088e594644c3d2170004102020209109402c0c000c003041501c144013110302042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 324154469 1250 324153219 324153233
    0x41e03050f19060b0d0507120501140919110a03050703050d0e010c060b0105070f0821220c0b031014101b02130f02090405150a03020d0825030e03010603 67
    0x600b156014002050782c811301d0010541030b01e40e55001605610800d000043c56071a040f01d002d61007030007000240302c41c40041c20310940d030540940b00c3c1120f6500c0300c04981f9051600001000659100d680c500000c211b1100004003c2c1d0840d030800c1e0707115041801c0030405c10800300324068540349141040240c1c0c03440309001902c4039080341c2c0003500098640100e00c120380e20403021141d1080e0b0000d0009001075203410704865503000000c08041042c02005113100072150b00160a2003418030072401d01510203403600d0050241c2da80e80046480031a48000490700f20700e6040694807442e03140501c5142d4900c1e00e480707005050107000c04075000d03107103040801040603440082a000614002156503903464180f01196540540c00d00201c20035141806110b00568280c0040c4142d0350115010701603629580300b180102d07591500baa640c032410100c01007006040c80305201e00d11a00803010b02e4140400d19920350801c0791442505186e450842641a04041e00040c003012608070980003000154255940c1d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 324155719 1250 324154469 324154513
    0x210060503190309090606110d0905060301090c0c0203060f041703010f150e030a03021b011e0305090a0614060901090504030207170109022d1f030b06041e03050f 71
    0x610303140a00c0190b4410705001c0d041900082410340410004282c0c1c0305802002c80c0001c02000309070f0b0091041086603103100c0e4140005a03403000b810146164604140d05000707194031100702c3c0611100e8000b46000d0b80d0248011446200c0e048031044c42c174542441d180100040c081004080b101d41440184044620300302c072340f0305952980d030004400700410001560380100034807400798140b04401042d070800d980800c80700646003800d5810701d080c51090005640d20008448002c950000c0d48100742e080d90b2003500000e030080810030130388082c40c40c10b48170340e030544940c0c41d07491f00e03205180401e101090606e07a010301c0c0185164181000a410702c3c0d900251030340118880c01c00c040500d03d0446400d800203500c484000780e80200041400f0072140041c844400400c000b8034500c108200045803941480308155194049010006403c201e0485040e002080442c440c80d811450030301000c0b460500c0c60b10317480f4806020070a45d0100c9840c2d4982070b450701d1200200846250070481110101880301c20b216 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 324156969 1250 324155719 324155743
    0x4180b0603040b07200307050d0f0c15180b090d1d0d0605151002070e010f06080408160b09030315030f0a021201020c060c190e13150b0d0c0210060503 66
    0x41010315013800145101060800c001d2401c501000a047c8100b1000007008103818420f03885807105036548401c26100d14903803005c0641641c58a180751001c0d03941c10381c024040b50820700c0d5140c005609075110341d01c0c580c001301e0348a9004d903c90f103800d0751045d4000070354201c3c04100070442004c2004030000f00c1e00d008000304004290503101e01c041078240c8465509860031348405001c00036801e5405000a5403900740d44550300c2b90000a000106101d540b00c1108000d460440d02c03690083d454540e2140200c0c0e10428415100c800c2040d00302e00094284c20440e80034000480055441e401e1048602e55034034a48d154551199208402c80e441c0d20340701003810b1200302c0c1c0481c1c1c504008240000d020f40648540c01d0b070130009000354403c024000050201620700c1380c20310040c000c114282c00d00240c904140d003c0901c1d502000c0500d080028407455004a00407403c0d100509200541e2841222182c3c2c10044030800c0d4944c84040e0030759500e0341003001c9a00c51080c0e410074044685090086a210a1418a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 324158219 1250 324156969 324156977
    0x30301030804151202030a0605040e060408120a0e030403080a030f05102102060403121101020c03190302070204090803061201090f121713031e09230604180b0603040b07 74
    0x8515103024030b660070041c4e078030010190754a14000408800070720550007000d00c036a10381146002400000285940310729070042c561072400c80f030380c1030601500b800103180f404881d442d03c440c0c43c0d82080500103800118410b030883c91300d584c03010b071024060301c10202858141c54507000400a00c50f203d003140b40120b030346c0b8084004100030001703203001520784a600041c1d04107400140c00410440e6031144650b064000355a2a15050305e065091420703445603040054565005201c290041c3c13a4924030303a60301c4882c605005281c00c00690106090300d40450041d01d400d0b8010027000041e040c915484600800c1440003048003c601d507527014401d00031008040c0c20b03e03005003409040c1d1b0b400303503801d08440103000d40c10200034a0a91416034440c2032131030381180000c00310036121507410441c040848007445a5140c403043d15042645c6070200443c00d803030081065040e103050750003d0302e90360000c10291601d110001e1041584016401c160f944140a00f4015a030030420403000c140304120180e001159458 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 324159469 1250 324158219 324158249
    0x40507030b0a140c0309070b0a08071d0d05060709050103060308070807020a03170702010e011106191b0206060a060905030d0305060307030b010e1009060f06180b0c03040303090503030301030804 85
    0x6100b4000b80b4106420481c1e103801c0c0303804d00c542c0c43d503550302a41c8542810021602c0140e01c48844150354051a40b80e580400d52000205509501400004ca2501121440b6400285c820b6001405a20412505a92580015040c040c507964440b2507080076100a08007442003d103140c2e2036082500c298800079058107400b2425034115071362509250015074210703181c04115034201083c24035a07840301d01d0490103d08488550351644d40540600341e603201608002d0b020654a40005643d14a160912802c100d503517030b50340c4800c2e0b0081c4e110010010f58a9401055940b80240500030510703407a0308003006010082408102e1503074001002050f1184510b804142a162200400e00c0c02c1c4454000408403450980041440c81000700f403c0c0c4121a50700a0811460362032801100316291402141c04201d81d4130000d018441c000d0303501c208035038540283e142d45140c4c2c580d90009550000c407216a0142c03c0028100141940001d0103000b42c8001c4001e5850741d49180d40d0b4800c03600c110701c145100030120710 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 324160719 1250 324159469 324159481
    0x9080a0b0c0903150901060e100302040b03100f09020108060306040803180c0a06050a080f0103030206010b090d060c02030405100e0f040c050705010c090815010302100e15070507090c08040507030b 86
    0x500341c2d030045034080c0c2140c261100300d4400200c003080843d21645c2c290700e020800628903203200a001e00820725507080b015558119000d210103084052060340d05803240080b58800045244030b03030840c19500c1000003c42c08400d100042650401600042c442e60268003400f002c41c90801c201d0b500b0915407540c1d4000045015451800c0040b00400c0960080c5405400250b0a81100040101c20300c03690352000030f683c5c2c118007039622940a0101a0041c0e000c680140101c4010380001c009002009041042680d21a40c901341030b2016004040b00580012034104480c4c00c01040f10115140a0705111394581000303800704400032404070800b8440c85c3c6920a04c00b08034043c001f290080713a0070400a200c401d61510f8083c12240d034078415050a032051544c0081c0170a00111a80c0c1644c1d801003858240480c40d200840b1408403c04c1100d50020380c00320b0550030034016038024035a15101c1c1c0c01820b509441d000094045400c4201308209100007031301080001600400c00f0402c0c1c036400843c000c1a52681 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 324161969 1250 324160719 324160741
    0x406061e0315090e03030712090c0905060103020409090807030f0c110108070302040305061512030a08040b0a060f060c0209070f0c060518010c03020405030c0a03030504120510110702040b0109080a0b 87
    0x95846441400c0c5030000d6544e0b41000440214400c05c07180e1180310101c001c400b440c0048680705a0302414041d21320a0a10100042c0e400c4141c10680500d0050301342902c41c440e50048030700b2540c0480c0c1155000890400b0150002d0000600f41050308000c009800142ca403000c540c086a045181005110000105140e0080d815030b80619000780c1158000d10308000141614900d00c1c9625120b1420b400045442070000411510303008020382e07610b44a6200c541d18002071180280c04460025290303040404c04464007841100206426034a02928180c1c6005016004c1800307807005c0708000141c0840919203030090021070300f040e40100d000400c1e81c0c40700103460740c117601d54072952059400d006000b00c0c225411b40141050705c1085094400c01850002004203050045c803004020480c14001000301100b00d8421f054518007a206541c07000e0400760125007200c0382c842c1118079500d0003003800c13400e50a092041020a000c2030a01c18102420f0001c400c2d80c41d0441344006100410640c00a00c0c01e06003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 324163219 1250 324161969 324162011
    0x305012619060b09010515041e080a03020d03050a1415030a0501061404050907051c030e090103031e08071e0e03060403090e0f2a1e090406061e03 64
    0xe4200515207114181ca0000d010300f000b12a10791103056100e001107550b140c0858242d0311180e40c001c0c1e40b85824a020720200300f070f2014140c0b141c180ca0740c49400180000c400c0c46842001c602c286e0281c118108a500080c04450001e05014a890300e000c2c0410290402140c2180e00040b0150071080001c1c415400685005e0707101100030815420600700088000c010b000b806052542200c0911039070f80c400c00b11360381e201003a20406a01080c00008030b4170380d06070100c0c80704005019182228000101d00c01240c1ca110017030f4421000030750000e12484000f598540321fa00110458a401201405c064074002c09a0f04002d1440800002c00e00c1d0390b08515000324180c0d55404409070940740145000d08000d09542c1c0c081c400d040d0a4a600740010741103040e901c2c9e12512942c0e4000d1000c100a820f5403500520910f00e00341c00b0081041000b90603818886511000200c0c0d0141800c155107a1012003403105660780c6038040400e0250340401004e0b015061030351003004000c00c3c5000500440b441c1003001c1329100f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 324164469 1250 324163219 324163243
    0x9130b03010c02100c0206130206090607080a050307090920090319060f050f070c0818090a1b030915090507031202030c010c11060f060118060305150103050126 70
    0x864000c540c07140c1900421100c13244120000100700311020744500380e884000860f14807048074140d461140061030010003078210b081010b080682490125030360004140e02c0074a009010620100422982d90740c804c45000183c2440e0009010404985103a122000d0402090031001307080891100d10030b45003009550301a0400d840c2e000c0300310100f4200403000b0020a108140010309103c001000c012407442050b02483c030300c0c1d441240e0740001ea2030f2510250051048881c5042001e075401070960f0b10101c1c15406965024000103024403114000900a00c0c2ca840b03000505040140140201d1025400780420b110204000b043c034000a2130000e0809260350001031010326560008019140d0010140698200c800000c00c5200900c86007a40c044905414071840755000c04002030309004c90025498104106040220088504905404030312440b9000b1000080d40c030300812a0003000321204403c0d842083c02c04010650400072507030b580d496112050021140056010900002d080200700079040e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 324165719 1250 324164469 324164471
    0xc090402040f0f1a0a030e010f0e030d0614060706090c05030d08040c0605090f27090a05061b07030c030c0218060f0f030303070309081201030308091e0309130b0301 72
    0x542c030b910001c61218440c1c0a0310038548180200401c242c444044c10044042450922908107020500110080c3c0011554104e4554841250302da0103684d500801003805c0c1244041c40d1241901200101220000d074000400740404844861090300d43c0c40449416903004080450100d10030309200607040807a44c0041e415100d0b681407800c1ca1580640d515004a11620b5a01d42e0160341d04021078071401010016940403940c244809243d01e003a08041c4020504941d00d50005682a1140b00d500c00045421b40d00c243c100a102004114051080380d030f02c02484039800c1c45044000e006081c4034001c007035004091040b20451041450b001c0d410707130400250b00074030910545c01c203607114030403008059031054060209405000e489250400550307148100280c01141103030340e9003030228085c200c030510546d02400c0400c0101d41c18160401201d02a43c041c0e21610740c24200503002038034102e210102c0c0071011300140c0c400000404040122a4005070482c0c842c0b007980801d280203402000c1c1c41000c55415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 324166969 1250 324165719 324165727
    0xb010f0e150c01150f06110607080a0905010f06080619050906040b041401051906090c0c081605060a091e0c1a0405030a0506060406061404180e0a0f0213020703050307080c090402 78
    0x304a0140b2105c1c181c40740d0742d813002e490841500d41141d0383c5400792860400b1800c62000900c08410307940c04084418050400450b035000300b41392040c1100c41075007001049800c18030400c4002d401d4000f480360229442c54041090786032802c07045403580b0018000414100704640030601384030b03001048158070b03a10704000304030f641032509080060400c1100b441554905116001940c1a468452144590001d4445075000d40075562a2901c65008040741c81050840040c0708011032410425540304658441000844024504090000716180c10400368200102c08100300010b580000c040200c50382c84c0341c060640012f5050030650f9000d66009650580f14903064003041c0704000030344034081c600030303039080140c2c5403a25421207283c030400890540140040008004606011000d540c0307a231130200000901b4500868001d0402c8842e810945400151034a075009624161054801c07008001004610f00802550701074a079003c014904c0050100c00000070700d400e00d2a0044600031200180b086541e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 324168219 1250 324166969 324166979
    0x120c070e01060509010311032502030d060e0906090304150f021504050d0e06040b0414060403020a0b0301060f02160312170106030606020c060a020c09190903030b010f0e150c0115 78
    0xd07401013034803203000900f854001c007407000e884802c6034080d41d40d880c0480680904100c820750050410720f03a03c011880100180000c26a00d8451900030700421003c0040070700b0000c001615011014203122080c0d00200300030403a09c45400000314008101d410308514588000704182d040c000340015030445640b81074200b01c100900407800c094407080382e8444a0840740c4080600c01d00e80128007540d901d280c01000140405100148181035040c0d000381801d04d420b84982c04a00403050a41c04101c4030f000202c01407101d80d400136801000b61017039200404030020a6550400750070340078840541012441c1c800f4809048c41070b50542030089200700c0040041d60f5520004000f00003a10441005004003000c014040c5070500485503c440715600810390741c0d9182082003c640747c054500c03110b901e00b070140203140302c2040c000c209000303010b42c07030029a2800c1000054208540d0a51840070440324101c1451941d0b9031011802d00c102402d0040350b140c00100c4149401040341c61141507000c0001240082c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 324169469 1250 324168219 324168227
    0x30209070c021c030806060708040f08151e130501090611040611060c390601150e21030f031305070b0408031e09090a05070e1002120c070e0106 63
    0x48820310940f083d00701d55200388144103900c810020001c0008002c1400f0600310b00c0d200024106141c010000646041d82d1184200322240142d401200c0c540c0100c1d244c1c08c5500107aa605503440403ca01890100d60341d100017411035002c00030100624008040d00e9001405025803041c609546d0215080204200c1c0e400ca0f00c0d86038100d881003400041c140d4403807840d1200081030060047d2040850030341407084600790a42c59180031039000c102d00d52107400d89812981c2d245a000d950640482c00340c00c055041000c5203038422100c0e11041c090010341080c440c040d4885808400c2014503011829490300790301c48003a4190312078485800d001d04804010302c0002d8107031040841e5154451003c45105584e1049007039a0703805544100d0140703820900005407030480c040322000100c0452640c60b40b03400300e10390005085100944804842c070f0b640720100710005030060030b2906590341c111240c25000d551100020349c1ea05103552418a50b120201d05640007800410212015119902039040c03250b8444400030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 324170719 1250 324169469 324169487
    0x10e211602040f0b09010b04050f0f04090b01030b100f0605070b0907090218030c0409150903020709110a0201051f060e0f030d05030702100203070c12120203010b0c10062d03020907 79
    0xa02c103841950001a09407c03030001c80b8121000038002c1405412020200000c4643c0a04541c0d08951644680c10004c0d44400a0301e010f03503c1001c5c200c450b8142210641c080f102103802803090a01080e005011454000c0180da0b203a40e40141c0f0030300d03107545200d4800d05040c0c090b401440402d0000c100540803240036280d42807079802c181c04440001c00e01c44204010b4030109080503101d03e140d16001c0e01d070101c00ba0000c07032109010340102e41c0c5081d40e5110ae01c080b643e0703880c881c10090703d02040030551558280201034001c0440c0b00d1a000500042c2c80d00442e2401c9841420103101c07161708100328a8540a0041083c004000c1c01d807200102e103c100a003080c0c1c4111440c6c070040c0500704154401068910a0320302600c0c0702d40e1090700206003551030404004545501c101480540c0a030803032111080d00081d4041c0c840071101548910568800520741480c00e41405189030078107409001450741d0b1444400c0c02240d143d400c2d20b40e02811081486a21314135000a901f01d268141004802c0c0d400c01b000d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 324171969 1250 324170719 324170741
    0xb030d03060e09010c0c080d0209030312011707180f1e050103170313020f060d0603031112040b16020d1205040f090510030b071b0f0302010e211602040f 67
    0x640b01030f035400d00300c103003283d1030041480d02144c842581c140c086040f0002a00052403c0d49006280c0b0509400191441d08003e00c007060b0140c9010040c890f090803049490811015540201446c600f440c96019031000140d285444465031500d44000005e0b0b41d40140100d1920843c9001401c040010040d0141009000030b440c00c018000b543d10003241900b0881c1e1042441c001c0111910216a0811202c1d81c2d01e0419954030030014071100184c1c00720352150b80b00841c07294964840c0c42542d100c5e080c5c2084401c480b1059904006e1100f0011034020f076044a0450384502c0c41c1541c203244510002d03003558140900500f94546244481d8645a0020f00038020b17a04109501140d0b03075134600c000303800da4004580398000010f004208000151400b0822504410a4100000c040c00d01524240415010340c0064814501e40321050040c03680a1003201c0d6100030b410068941843c0c07003501002000361030304800e09941d4000a00106802403030440f441856070092080c00880c2407440f030880a40350407551 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 324173219 1250 324171969 324171989
    0x14040b0307020d02210304062414100507020d020102031b01050f18030d110c0d03021b06040f0312020f0c0a0606050126060f09040f05010b03010c08190b030d0306 71
    0x622141c40d800040d044410031041c00f811090141070519585d243d03040075004840d643d072140a140c3d620700042081d803840d50f408e888030440507458240c09151090b02481034502480401da28261100d501200b150400350b01590350384010b018070b200403840d510401c41c1e840c84007072801d4164020303050107420003030003100c84043c64142078a80c0c1e00309400c40480c80c581d58415a100b00310f040c1c8120360755008400c1c514841a002410502d050302d51505004e5411100d100003540000c80c2d50106c017010000c9204040d98100a0a00307241941c2c48100d01d080001029040c4100440c01442c5a145501195044c040f10b12129442d400202926035507103d086e40b045448a083c0640410395522501f070414850700404040b00042da1040e0240c0c05800001d8481741c0c10120b600740c1407420f904c420303802c43d0003a4842d907443d64100c00743d41885400c40310181100d03031003a4102030340400c520341d22920b0340c1c3c0c121410004030741d07044c4088140400203040041000d40c06004043c0280c01440e05580090300302c2c0e200c408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 324174469 1250 324173219 324173233
    0x925090306110a08010e100b0409090203100b060307110f030a03050103020f01020d0504090f0b19050a09020a050a050901020c0307031b061e051b0a06020702130506090a050714040b030702 82
    0x100b01905000d403540c66400a64503600400c42500b090010703903045521441c603c0b60f4152035808804282e8041d0300030b04402915075102008604041201e034601c0b2103031000400c0702e0700c13828002498030310000e8103040401082000a8081640030302103160072800140031a40e41d003001d484058045c2c4400d02c0264490401d00200810a500104010f604410141c2d90140b5041c2801103450007001e4152116681c1a91a0100c1d0f09039120038040b641c01d140c040e20040b00082c42c1408201030303d54940c000114050043c80050419078110041d03503010b5119041c0b950b11503801c140108e00e03260b02ccc0d050044c0d1503c9420130000500030050b0032214802154081140d030942ca031a4191880400440451090202c803d20084079130710440190885000700c1040f12041c0c0340c9032001d030b464a0310014080d110582d000910600714500455101201e0030020424400c51503c6c81c00509603200040c98824010344400005076a107102d8692282d4505c420740030725031616104c41064032507800c04c40d500009446424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 324175719 1250 324174469 324174491
    0xf030807020f1c05090303040305160503120a030218030d0c1502130509090f03120106090e1303030e010f0c02031308211305040606050a0306091a0925090306 69
    0x108403a0002c2c4003001c01010550070900010006849900b00c2e0b0080040c1402140c40907602400240b00a40c015001031900401840c5000041040ca5000034801c3c3c1c0a414544c009100000c1070302c3d03011004e0304005131180103004030080600c4645c840141d040c0074088481e21038a030001070760314007030340102168441075051000c010128424652044045107060302e080156140035105a0b9025a562040e50750014002064525540103007000880b031024040c01407102580c0407c10b00028044640500c146090004082628002090001c0c0c101a00d5004c1c1d80b4560704c00b50021101c500340f00340d080040361008034000f500c039000400c0c078041c01442110000f0780e0b070b0701c0050345c000030400184183c01014000d40408000f540000c5140740880c008200000c1c0f565124812a0000c00154035603580c1c451001a00400301c1c0e004d03030080d402c80d91900000e1000007030b1028030b1004904040d81d503046240c442c07a4800c515505503010b1105214a00c640945010380d11078a008201c238480c01d800c1c41a14045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 324176969 1250 324175719 324175723
    0x9010b2d01050405030c040902041506020d0f170106110109020a0f03031205010509071b1a18060903031902120a020c070927031e1e050313020919090f03080702 70
    0x44e200c2d855141c1d1141c4846600c0745003d034070030307880244020000100c1c529040356a0141d49480d500c0b10b40540c11145644210b16003000d00d41110307403040d00e829100782111050489039480180030305000c015095078004500ca000b58410b0300d030300e0340051185203411307500d268108002401c1d0108a00043c4000f10b01400c4407100d024080c140d80c2c1c010100041d550310041e0803203020b10b5403442c120400108040301c00114040307a00b4098000c544001c0a29185000c03095151a521206013038a2198003050070045046d4001c42943d030003008501e240c00b807040b00003400f10041e0007803100821800c40086e00780400e0110a03401070090300c0c40c0c0c8058425590781c4d43c1101088520300074202d03e520280c0c01a000315001202d0384a02c0b920700c02e0605100d043c0c000c80c005540840030460640114065103401c008500410840940c0c000c05450300615510b408090058820a580f1009001d51000c102150300381e0300d03a074552601040400c104001420060415010141c0c0e01e00c0e050700801c0d11800458281480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 324178219 1250 324176969 324176977
    0x106060e03011a061c0f0b040e03121b1e0306032505011803060f09020102160803040b1b19020a060302040302090f060a170309030f06040507030b09010b2d0105 70
    0x40501e070304030301c1e81c01340010340d030040242003400c2c00308184103600500307244946c59420903c03000003d50f4008003070920040f60194483d48201d03034414052124034290030202c01e684007040b0384072000e2800881c0715002840c02039000d100d18110440340001103020b80350010b944602d9040341111080114200b180c1c40e52280c181c1600300fa40c1c1004014409075025000c010000c00d5000c40030400241e89444a008039441925041000ea440d60203581c255a8104101d10505a68a0240c0e824518003080180d8a04c1544144d90031030002041d0001400c04106010740c8160700d10081d100c07200141c1d404096080074a100c201d11400d40243c010030124820704c25641602d50107049100303a5202e02c1c20b0414201002000240c0c080c002e040082000c00c50710259a20b42c40901c8000d5231666846020036040510001d0307540e070550300101c10003012446c000b80e10800c50b50400d844c803078075449007001d01d40034211001d400f94000030783d84c0312000300520000010054000040c00982d6585800c401100c070344c81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 324179469 1250 324178219 324178241
    0xa0b0f010f03080a03200a0f030608030c1506041407173d08010c0e0414070c1b0f0608070305090a02010f0f0c06050406020c060a020f04060c0816050106060e0301 71
    0x60500034002c40500a901481c0c084900c501104090b9030303143c0d040511980036214000009402a409508c00343c3c0501521001d0001c840c041c606000000c3c0b41c041d61554030000300907074602c6000c0407030482c4d10f499000b41080c0440243c8905180380c400343c050000c003041c03402c462400440b140000c120305c5a22104841882c90300754441c0315501a03031a181e0102031642e51174850015a10000200380100344581440501c4a889030800342010304200021108822607604001e4018020401800d074440000d11505130b0201001105032a0303140102150405a0440c0f081841c00322004104250490310303152088026540c21f200d90380c0c81c04001034030340ca04100000d000c0745042650150140c000c0c80b03812000051841d0801070750703500740c0300c46003692001e481c2a6405540010701c2c640d240024084641d0000080b04154a020b45540e15030041c4e1180b0702c680410480040c4030340d020006041c08070707503c4450745204503094a819040c55402000d00c3d2061601080002d00f4001c0e2600b818041c5107a640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 324180719 1250 324179469 324179483
    0x2060d1a2d0607032f0d02070f03170705101505040902030d030c03020f03010308071b2709060905160503160b0a0203090604080105010e1014040b01110a0b0f010f03 72
    0x1030381c10203000d0250404801242407103126406112058815100c1d0380c03000400c410074071095000b03400b00c5800d221180e0100d40442d04031840901c140e02e0070185000032244e000000c0002c0849041c49441180145417004215002d9a40c00b01c0340c0c42c95980041c8000440008100c44d095501c5007000308072461218003d4150b003000180800c01c9020b90300ca886094030904000d0f10380000310507005100d5000360001c0301d90f42800b191302e0052202d0340c425108851040300700b034803280d414079a6149980d240017214445502580d140e0201e00c034040d80111090b2680007605011180c0a0301d081d980701c0d40d07241120045e10100800000e00e13442c0000300107000c01a45065905014100089544e003a80680300030002c0d840104440c240d9a11000004c200608005000090550404400d442c1c2d07520054484c015042c207105092240300899682c180765841c1c00c590004140c0e546070010f840300c4803442220800d40c01448010703c01c0c0090703440401d03c905096102c201c0d4036030700d41d0002c60300040740e404090550 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 324181969 1250 324180719 324180799
    0x3030e0405041e03052109070f08120a020a0f06090b060a1a16020d05060a05060a0308090909070905180f010c0e1908071d07030903081302060d1a 64
    0x304145902d120704150017841d0a038600b01968021900c40d400c180b110380607809a980c20004034036401d122420191001c410b40f03005a07490008007a69411409225000b284000030700780452078020440c0c10380c3c05600510007800c056903400c0040c000e12140d10151303420104c85001949a1402c0181c050949915031900300101d40c0303107001200e180d081908001115481000040017590b00c0601c009413051140c001070a951402c429000141c40c0c019040d00d0040c01c44000a200090a00302520112002035407144440e69988092500e41191035200d100781510b0881408204120740c01811100c5d101c0d2012102c0c1d490a007036800307080f5816282000006950034281491620b4900302020481141284c0154119107074982d203400c3c445d859100d83e9501c1e020b0080c200000181c42039056006045081c1003102c01d030280c4015150000041c9202c11000060a040d41199503010a03038607201c0410350100209501040801c8854035103036241e078800d5079601000b0b03407204445090300b8610251700d8190340507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 324183219 1250 324181969 324182003
    0x30509030d1505040e010c1b0b010b0a02100912020c0a051305100803120a06051f0e0d0c0b0408011103100e040821040b0105060406081305030f0307080103030e040504 73
    0x5040b610540c00c81038502c4000007403180d40314094103621003101800001c4002c0d008201415110304410301c1c010395050842100042075100c0c1300f1904503442803818035602c00a043c0101d0520221010a103070311441d0070385907030070b2102c403c4500d84221515000c5a101c5400c11042114440c0319208180d40300c0c452030310008542c0b015070851074200d466904d8501d00039488034881ca00b190443d404500c0040a0030041114041c0c040c0203d0005120960700c40f1850008488001400d00d0880040e0050084030740c40b0100a480f03104007242525000078490031600c0d204e03000e000055000c0d120f00c148030b40c2810b0410b91411030560440e400703640517115400c0514a805600103400c94006c00075030b0749071001d01030f44108408410701d18103103a00c81c00c514802c5103414540f10801420681045015100c00d100500c001038201c0d1050f034104440392200b4040040d1858514034600c44d143c211107440d14040140f00c0c03030030f400808050507203110b40c44410f24082c81c0020b00c01240c508440103444900a00c4804034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 324184469 1250 324183219 324183221
    0xf0906050603060d06230f07090503030a0810050d0326072102160803060307080c01051e0c0a0507080120090607060b0616032703140a061d010c030509030d 68
    0xb8080c0c2c40750101050803942c0158000980c40b1b50112050205c40b80d4080103071070904d0307180503540f000701410309020b090700381030201e550703406814680f44c14410408045911511504000c03001050010000d1031500414600185000111026041143d07a0351a541490303036000b410781c6108000310f40e5001c84503007025100001c0401c20001e00e6414640c01c100a401c07851346001e60411030750040c0e07507072aa2420324209051074501e840e4440301c0c1c10303044000c0903801030ba03101d402c540640c0d60362130f101219500b000d00c40004038410901101000c0c41005007000402802241141c226501c0340700803c000e0000924602254019101000c91040100003141031468580058a1154022540003800641303034808505983d116000c0170360800c281d060140300f05a405410110420310340000d030380801082c50180400d810240c08000d2004004044000c4118810081d84140d21f40001040c050384041c1040380305895101e000a4800f542880300044110340a80170300c501904102000350300d0900c82d07005e214 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 324185719 1250 324184469 324184489
    0x2031f150c0f1a0a0e0f01091e020406080d020105060a06090b030403050307110f03190e0303070803040213090f0c0b07051b040207080d02030f09060705030406050403030e060405070f090605060306 86
    0x110a052800c10701151040c440f07251a209403c0e00500291100c58881401d02d031090f104210b6820303a040c181c08600082100c400c80d040a0300c19103000c403c411591000034040c3c9600d8010072103070300c141c601e00c1c0d280c5641500458001c410a543e420304590702c038130f011241250f4500800341c5440c3c0030000310300041c0c480c0c8001d5034050014030700754003000200007245041038103001c40c8031110340c80459020315100ca100c0c005502d0800504142a41c0715081c1c2c0420b07104c3c0140070f80500b0300320740400060195102c1d01580508030200c40801c001108461401940043c0400b10660310100b8400c3d0100e0546241c00440b02c01c5900500200320042d080402c10106c55801402660010340038040b040c00902d00e0b9016111b11040c03807030003584078907140300103254030b200c01001d011450b48500140b14030305802400700e2384c21a4000300003140e00c1c1d4650406801420b405600078001d840f5060401080c00004214034090701c018042d0601c515071740710880f406488860007455030040302000403031854a4031074150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 324186969 1250 324185719 324185723
    0xf0b0108040512092b0c0f051f0207170304090614030a12051e0d0b0301020901050a030507051207020c09090c011b14061f06020a110d060b0402031f150c0f 68
    0x16a00c4442c1c00316041500354003c1030703096010f1720340741c8201c1e040041c9142010080c2c091020440d54162a00c0300142c4510403041c1000080c0c1000c40b680414944248103403005445956032000542580780c141e10b17030302d50051145020441c03501002199141883c3e92543c44c07240014000c004041c401e0702c0d4510300c0c884007840601402001c214030012244641c03c000d482c0607104000035100c0340440d2440042d100921480b52090b4410404801c2036038000041c3d82d010369140c900014030f507480c1c80040c0da40d445603500a007042c010040800111a50009225000002c20794031485a034840f0195107076507113000072403079000c902c00d94088a2024140090040264017a406086030b4204610b680e60030f104042d600b400390741c1c190440c00d010034005548140014800d501c001d2801d21130580300c242903840075000a5105082e465400c07400d111854111a0803810010300855890400710030b030080c0d091002c0620075601401080001d80b244400200303820840464840d920009052350b82c1c0301c183c550544c0d00f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 324188219 1250 324186969 324186979
    0xf071419021e10050d0b1504030305030a0f06030605090d03110405121c0e090f0708010b090d060f2403080f0a02030706090b0402010311090f040c210f0b010804051209 73
    0x6207800e903100c030b0300f03800b8840441d25015500c001100403802900c0e05c415049000702c40c50444008403d074100d0884003102c0d0503250260b02e80d04d810f503030003014004900b0018030042c28041d0100900c84180d203d14080c52150084030480d0048000940594400c01c082c2c0304000001e010401c80c90521070001e8004e4007205060700c3c0d4400002541313000400121012400080000c1044160307410203003010740d08105405c00034001450000c9009001c008140144140310202080c442c1058444c500406a0160301c214240b045034170203086003005003802d40c080c40c400303401403492000120713510a100c82540c0e0010070f4517103845100001010103074412884241144400c0040b20082101481100d02c40c40c031501c20480282040d00005040e1034a040c2034003d25032040018442541d15041c0318448034809480c041400702400340240c44108500e80c2c1031403101040c681c401e140201c0d40e84890750113011002c041003c400d90a004403412403040b80d0060007a40300d4031140001d001c10402a2a031510000c00e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 324189469 1250 324188219 324188269
    0x14120c01080c090414070306051801031e02030f060907090c080c0f040b040b09010f1115072106050411090a0b070f080d090c14060904020d110f07141902 67
    0x200701203a0044100e0300c45d03000541c00b4080c485603d40070350b100409040303482995503005e04541d10021078042c40020040803d46050742d50f00d81788210079241d203580033400d480d0403191603016076840d0001119490583c2c02085400b15000c8254810101001d03510382c1da40c03103541d44040340c564050703011a0194402d030b0b40c01e00000400000e594000c0010708001d81c40c483e20f50940d58000b600046400108006110942c1c1c4030480d00c40002840c0c170400c03110070f40c48415a44546c07c060b01c502c0d0401c0c1c107030b5010401d800203100030348030141c020b142198000d581c20804010010159201400303000b40c0d50b03a1142d84100100000e860f031034060301540340a020b012480c036810f80d5900007254003444044070f03041d0300da525079020300c486440c00c40010881c0c0c00700f0b8400c8528500015010348200da020610495000c200740fa0300c00b0050b0b0000800c3c2042111584e500c1d80f44130b601c0c0a1640040c1400ca0b030742d0b1061500f0f160440c90100f0340c502040d144251180ba40c4403541c0c00c0003140c3c07403400094440058507003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 324190719 1250 324189469 324189487
    0x306070c11040e0109050706080c0301050d022107090c110d0503010e1b0d06050108090f060a020a09050301060f17150106031a0315190b0d030302030403020a050709050114120c01080c 80
    0x2109841707001348a5401000700318500540604443ea0050071003600c0c1105000421035134031550840b20f00c041d030458400c0b4400c1c3d01c1c42c4281c500c2c240711359000603207441b86070b5003c62052026400440404500d03100e511440070708003012681c628002c2c126400284090004102d6612141165500100f106440c40c81500e81264442c01c5904010841e08402d51209000c12103540c0220145030002c3c0d10300058070501a51900c1c065503000c0140020418950000b0030303605640c450b030304040c09018020000d001c1c441d5107070303054142c00e1401c0c001d00d80e11007280070309401142ca00140710004074038a4400b41ca110b0386002d000794018002d140300ca80150868503030800705683c0a0051880c0f509154030384c550306051003800d5015601066010351112860481180807580c2d91034440d1048660510300540d0b2503880b0b140403400e02050b1280102940704070030000c12202c1d129007207070303060f101040410443c1855010400800c2140350820050070380083c010120301c0c2d4868030041c0d902014441c00c147c9466128 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 324191969 1250 324190719 324190721
    0xd0f140a0506040515011e050f010311071401050c0c0c090601050c1f0e0c0a030b0a0e07080a032a02091008030f0705010606030204031509150e06060901050306070c11040e01 76
    0x215000c4a1917001000d400c402c5512030410301d409400c0c51b060440148281d1480c03d100301180f03000d2a84210540c800500c910b07807003a0400030340352303402c0200d50340c8420541c6001183c0b080f0501041c0415403c00e40010502808141070f50103520303400008250b01c3c803080e010b120300340e0005001541000b200300582180040100808000c3c0208800123a182c4940a4040310407100c8200d0500a260007403003d03900507603101d14a110642e41c03c108403a0b015201c03840a00c00401e088280d60b0650300400d64000381140e03020a4041d807940c020380714501142c0213011010100401c48900d00044240f003080030016083c00755025a0113807040601e18400c0c3e455490040c990b412400d41d0511502c00010440d040001c2805090010841803c040d42814159980c5214454041c0107031800d103552030503481c0611404189208102c41418410000083c1504005440c0d2034200d074864000e0041d83d00018943c1000607000c0d102c0c1c0503543d560026040d00750384d4240064486500c55074015100c4040118203102 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 324193219 1250 324191969 324191971
    0xf04050115140a020c06090a080a03020a0b060f0a03061e051f0803040f0b0a03060f0905010e060a0317070c080609070e07080c09040905150c180d0f140a0506 69
    0x248407800101c45800d00d10050540300ca0201e0440b9034102803014041c040e40009459200c0d00c01150035a071104d10300e1000c0380c0403010f19841220103201d50700c040d1090503000714802882070300901c610905a82e0388005e10411007172030851f02e608400000d10400100b411035018240c4038000300c0c00e54581c90711090600c0b09135402922030407505850f8220100524040b00003920041030b102000d141001d01d0032100280a80ea6413242e2200104c002544020310740c403079401003000d4684d8203a904419034a401108000785024018000090140c1c80411258a046000542200c1d400702122000c40308018105100e0780000c842110308400d564000310700d6803c1842100e1082c41b03514000d002141c9407000480541c00c015203003400340803214040c8118001320700304450700740c1c005071004540340c0c0c11403408a240c03408458504801850702d00500000000d00d000810a42c0501d41d01c0480b0f107404081042064140080c00508c0586031a00082c0064000350209144440e0b100590f1040c840a4543c00c3c10228 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 324194469 1250 324193219 324193229
    0x7020919090f0c060f02010b10050a0203070605160e0405040f03050f1b0d1b120c1a0a0903030c03060b090409020f1f0216050108070e030102160b04050706030902100309020f040501 79
    0x1090141c04d1064a83c000560690400c0c1e500c000d00204100304003007050301510000540810200042c544081402001102c100c254084010402d80c9005504010800d03001b052400c002514140440d0192409010711402079404c00c1011000519580d01941c40e0361060300c60211100b0306004101d2003100c920743d090109524000a040180704607100203040d1180c681003100c3d992075080000340400c400781c280c0c1004030141e00f0880c5280082d07050441e401c0403505544c2048070845000c0040e803038082c5c1c110282040c0b00f91002d100e01025400142c0948440b402490a03046d03042c40481c0791450b1581080e042c140c00940744802401c00c0c6000308950410b0750f181e04244050200921210550400c45170030281c0c0c040010420050400000a100f8800602044200180003a050312139a03001c0d81103a0f42016481003510101060b031520907103400342110181d82c503014904001920360702034000c0c18030311540140321010040d406107055006001415041e600704c0030400b07030b018241d21240301e0700380a80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 324195719 1250 324194469 324194483
    0x12703060914120703050d02191106070e030d051602100908100204050f010804020a05030d170a1109011b060204030b04141605040c05070203030f03180307020919090f 73
    0x11060500304a00d2220b603038048401d600c0f40c6040c5100060290a40d100a50306191140da0f40c907414911401134015104010300301001c036503009a030150094400d08083d96000c0560703c0540d10300308192009000103d00c15016000b802901c03001c18403903c0100fa4403c03944000f04289103c60b00803414088000301540701050703a1038401d2000c1c0781c0400075404c010000000640c40c0508004c0803c0f0f10039010f604c0541489083c0000c2411945c1c1d4245820282c0300140455904081c0410010607003030341241d40c0301c040007000c40491a1074585014000314031441031036440c5802c203403100444500940d2100c0d10410517100c0c030030200248441c0001d00065008422000190400b41440348980300581c40d845102c0c0e0000c0d41c2c080b04c040340c41d010703001280d00845000480c15508402522507110b4140700079854000028005d042940c00c002450045000b00842c480080100a00d1562031281610207036000d00d09900041c0c0690340c242c1d01d0719400c1a221400718002400e6500c82d5405a80350004075804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 324196969 1250 324195719 324195731
    0x140a0204051201061a0d1401090b1c080a11010f050703020901180b0702061b10060f050f0a030809010302071401090b01081207060b04020d0c08060102060705070809092203090503100e0c01270306 85
    0x24541044200701c1900c081b0341c008240b0300241d035033004900c0351502c8041404450540001100005e5000100c030b591040d074184828540144002e000307520142c401404501e0400300f40b00d500c984c03031080c401a04c1003070100b10720304040c1c0c1d0200b00300e982028070300c800c800c8803121454a031490305100c00d50941c03803603502c003150344d80c00d0103c8500007121a0704103901401040c600c12085039601000385084071703004006a0b07900e10795980100c010781f007480e0300906403d5100080d08070007901540845101406000710100998a40e01c0807611400001c00000003141c0038440c031008074989034054503036094000d20051800c04103200000540713103070321401c030003169100e0700300440d95030103203c4107610000c0780c50410300e001c090f5600d0020f240a001c070074500a0000308002454114440081c59800822042078034464440c0e16004090510500580c0d000b03000c0c0120007181003402c3e0003100d20200100d0060000000a40011200100898203120341850074020039107440400a160b100550b0281c0004551 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 324198219 1250 324196969 324196991
    0xa0510050306011d010e191211030607020f0a032a0807030f02010b0a06030b060409060e0103060b03030f160309350a0b010302090406140a0204051201061a0d140109 72
    0x4100400420310310740c0070b0101007040d13103a80c0c03080104198840480351000d405880118600c0345d40c0f4190030084000070310540550074000d01c1445c044000c1d20480480d1030f00d0b5644c40e0300f2070b110220311070a1030266100112800001c0d0103100154940b101506403408200d8214101903001d15080c0004e541034000081c005061560000d00700762a4101070000f40b108001007004149450910720801e030406a507140546629030b02c01c001c480080580c0202440700d9919003000c0e0038000c60030302c000c84800746040e1340d10740d0b242004000e840604140140150610100640e2034034203032a612022000c0002000d800f04d481c6e5803510300c00c15090200f038595440507400048950082030f101100e41c119034090001c0d080041c4141c034050381540c0c6d0540d01a4115103661a0503005040d400b101081240031000404c40d480c2010f45c064411150215000540451800703441c07402c1302d01901588031214540c9540718000380e112001004244d802c0b002c002303603080c240016081d0f0301c1421380000f1800c0c0d0b03ca480d0226 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 324199469 1250 324198219 324198227
    0x501140906060d02010906030e1603080c0d02010b0a0e1306050708070f0813240221010e06030601051002160312110303010806070c0f0f030c0b0a020421020a051005030601 75
    0x2d4024400c0d034034000d4018039900040c100032000d00c200420141c56804281c45401c3c240944200104580d203200d800c29101c1c9080c030040e400042542c0298412803507010903070b61050090b0706005401401d0051041e003404582c2d0858038000308800c101007100c00301e460002d100b84c4940b5104090f195070792034090601d001d00500301e003100c00d003e43c10003e0034014016102031205030140043d0340802040b810540550750004099040c00c0c100c4003003480400c1801c041071150004800d410000e8500c20701c40d07038940440003110082901d4141c0c0503880003006010354100047e02c800c1d01e40c1ca5004850903401b500307101200405e0030741c10440d818a8030b1201001c1064000041210f001402c101850442d8100600503690390b400a00e49002c03c84946840010710034054900070a40d030300503070607007868012414041d0156085440480c0c00a06c0200001c1c3c805d43d0503c2901c0644100b1300848042c0b203080d501c4208600c2152074280c0e03004514400004040e600c1503c0c195403c40c0949800d81c60740760101c0050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 324200719 1250 324199469 324199471
    0xe040c020102040b12040c0b030f0702010b090c070f020a0f0b0903010f0b10032c060f160e01050702190e0a0b03010506150c0f10240605040e04050a0501140906 70
    0x250640e030040c40140404007040d0280e405050601501500e59912418420915070007039100075085c0c2800000d00c600080060b5142e0322a4120390028040640d000c0305002d01101e003220303604607961007880740074009407041520f060250300040284491513140c010f51144284558041701210a000440c07c085003001c0c0200710f040d24903070300100003000100c0c0104c1c020001008044007010b9541d05184404079048900d80303441d017034241d07510702c04040408801b5641c280649030601c8049880300040d0a0344500440d0109850042e0307181d8400700a418015105134202020407070344950350f56501c8000f02d00e080122001040a1111002d460a140300d03c1e01c211032a0700d00a50007641032100b0448591a1411040d100021000314240c2c0c0340382020016081c40000001000c0e80c0c004e00082042100f10758205040110031982c2c500351400300720100c01c600c039180703201d00000718409120400190790f101070521760060150b803e58900c403d03c4ea8602d42100c108416130040c025107001032001d4100104a51 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 324201969 1250 324200719 324200741
    0xc09040e0307020901050d080c0105130618030f050c0c0d05030406200d050c0f07031209080102120a09020a03051212241903050f0f0d18092a0e04 64
    0x5946000050f80100e4a0440d05014060140c482c100c402c40411032124100e8000102d00e40080081c1e00b400941c1038040c089480d4103035407142c108940c0e0108000c64207010a202c070340c192203a001c071040401040e600e41d000030341c64180314000c019510b800c5031210502c0402d801d125030b01540c1e8032420200013800c801111541d28807042c3c441903402c4a80500020340d20384407150390400070b44495a100c0b14925001d54010280118040c11100000300300c03043c0c4030000d202c540c0391036800f0038544403082e80d4200e0040c1710020613000c002a001c01d0907418243c0c440c060f2140064294083c5985a071600b42c50150b0600c40741c0000039000510201250f84c03202c8441d00b0030308a01d0721150403100b94a000041050f5208041d10904405108a604204007401c0c0700080d54002c060fa4003100d0340060741030700e039a4548500c8003140030322202400b01c2e621035900302622180100812812a042c02e00540003423132400e04851945000310380c0d4101c09075414921458030219030780e4801a0826000038802030b190140c8403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 324203219 1250 324201969 324201973
    0xa03021305090708040605130203100e1e0c06070c051210051608130f1209061b020f09060402191e02010501050102070e070c0804090b03100204050612132108090a0305041811030c09040e 81
    0x14de4420400c012442031126281140c0c25620346d28641401c0710704504541c4010b41c800c14049038151041d0010856141244940404100c41e41c1d480900714070898400c4a00e800084440e0002064400d000409252072406a10440e00b0020295102c070a1580481004000f0030386080d405c000d0154040b9184400041002d41d00590042680c0815010030740300d20401d1180d20b00c140011900d46455055130880c0b0305606040d034a02180244c043c182c400403082500c0000d41c000130810b0320a0050155604880040c0c2c002d02529160404502124002600030410081c8004010f404102287d0203480680001800003400c00251000c00d880d220040240c1401c060050000300700d150b642e001500e06180e0580d041c1e480e1542c904d03a0a00101c01122001070840201102c407082c200c40c50000b02203440c210b034440d5051034441d00707000c540e64051804000c0c002030081105003d1903004500341182d5501594000c5405103414815456035002100d00201160000c0380d40b20035441c007805500200308041c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 324204469 1250 324203219 324203263
    0x1061a07050601050319060b01020c03010c030b0108010509010e070f02010207080414090711030f0702180c1c020c030403030f12060303020c0301140907050d0f080a03021305090708040605130203100e 87
    0x2000b881d0030080c1070401f170011950740c070320a81d203a4003c1c0f10069442e0b01c000c2c0200281c111962001d0000c04080070b60f81d0004075240c00105180c03c141403401d050701c1d604061f104031982c440c0300448035142a417a601d4210b54080c015580080c41d4480a00064548280d01d110302c6580030040c010a04401040d4400700603007000c0325200e103600441181c0c0103180181c03041e540c69100d8008032710300026004911802807600e80400c1406204000940707100142c2c40c40c207880007075042180b40240e010392008109070f60420482000000c0c050406e20400b0b9015007004010011070300c03500c004840041d802a00983c1002d1000c00300c0303140c20701c1070305c000100c1e00001461038103200004550340c107628000c00c0d0050600341612010f006a1920035040694001000340d66984881002006508034a0007102c61030300220000c078080c034014a11511481325540c80722400e03a43c0d512003030042e00000e070880241c07009003108000540c0701400703e40c0340798040000115081d88004111443e000c4945042c1208000ea21 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 324205719 1250 324204469 324204493
    0x409050f0a020720030a020604080102030f0105030a030207140a0e0a05091606080c0a053f01030f0609021302070503070b0a1103071d06210114060706090501061a070506010503 77
    0x4c048218104040045548080340c0613000c00c0c0b41004141000e03501100218000640346415001188030310480c1c002e4107903d90341e800c2071641d112130350350b801400760b0080344090001c8160840b01c00000e5400420310a14146d80c0c10000301701c4002039450410303d903210703000c1007035100c020404145250340c40501d0303904051070414014401c01c00548403116184000620900440c82101980c40c2070b000d03030008e0001c50361343d0201c900c8242c0361100c1180f0310350704031400b80c0c0c4400d00c00c00345d0070304076500520101210f101c5da43d2020014100424100d0740020b5030050b6a5140c0d00610290045510650040d9901e03001ca05181d011400010b11801229041c282c00c540b201080c8415290003003400d04244100c5a0415041c00752504020740c1907810840200300e00c4450251450303150450400450990101e90300d510810740060006e0001a40015007041400300042c0f2036403180c0c0380240914000103500d6219442076074410351035184400106404580d54003030241c14000710340108002c400401581c0c002d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 324206969 1250 324205719 324205733
    0xc151e041503091514160c11040207031206080c18090c01110c0405040b191b1b0b0703020c070f12031116180b04090c0e06060d020409050f0a0207 64
    0x908500010503846003011810001100e030b24114040440400740408070202d0216550743d20125a9490705100b201c41d41d1b2140b074083c5440204850f003240828414028050920000e03601100003102000100e01070070803810114031904020b4049100900000081c080410115000141c4070a821400c01c1040c08032171000041c070a9400c00d803e007015280308101e07141007401d107110409050740160801c02003008010921841c81d114a0342152802d8030003200d0000c080c00c50341d00d80001d29007440a07003615564035005100c3c4102d0b034486007080009820311941d8104802c035043d54031201103500403506001100050080c000540314040c843c034210b51614100111071008400301809028404000700e00341402400090411062000403110041d40c4607841136210040701c8603418840d207010701e50401407034280290403d49801220f0000d01508110a882c4a80c03405010142d010004011810014440380064801082e030b100d00000c05180000c1d07034802544e40281244030f16841006003400040c21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 324208219 1250 324206969 324206999
    0x7030e12031302061b03071505100605090a03081b25030b0a0204120b04060b030f030306040c0215040f030212030c120a0216060207120203130306020c0c151e04 70
    0x520364190240700b00e0010503403512585400703407070902c0c20b0028010722050000007028024800c54941c42c01001010090048030410b40b40b44a50031000202080000d00c80e20240044034030003404501031580c0c03550341d80100d07400508a0701c2c00890b541e210341c3c0215020b00420030700d00c2048203e4030140c03400245011504c50380d40030043c186410007010469101c3c4030340c1a0b40252201d030095801c0510141006032092200321030464540d41851003040142c00c01091034074000380d03410000c41c29030711b405003008050b010100a0404512440d22010802942d09041074081c2d8010000b80c40c04400e1814002d040180c00f00c07800034040c004205010710441e980e0200d855012540c105000e40b13480e0210410042e1280a20380d405072003010241c41c2c2844595401052001e01c02e040a003903000d950b030340c00d80c2c490203110813080e550240001c04002055240d001810b903c8095415164444c20420000e203841e103007152807200702400454030308024170364a810503004021803003849040c030b440d16040381c8056031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 324209469 1250 324208219 324208231
    0x50d030f031a0a090f061a0f0c0f01110c0f190624180b030a021008070e0a0e04060b0108090d030f02070b04050a0308010e060901061d130507030e1203 66
    0x2d03032031000d40c00601070000040328401008240d042281d5075000c414025121403106996070a00d08180015081032101003e89040341050040b810852010210003c64004803074010356070285450400ca2000700b03105144d950625000015212105900400e180040354a2440c540707600c080c0803000120008001c03021b80366801407010404c0c2b04203406002051480d1074401706100242e00e000b04036240c0541034800c0c0c01c01a00e03003c2211810040416548201e82a800ba410504602c1407035103151203055100d9000d4a01e0500184038105840481c0c4c40314880e5000b81c21035017000003844200310701d6010b0f2610b00c603024030301050a070811021003615190712544c07034414942c3d20494205540c2998050390341803500500400b100c0e00c0e0901f005070f101ca56030316080b0009844200040340000e035034110b0500640e40541107141680c204481601c003400004c0810810301d48080b03280065942c1c2c3d048240701d0000840021072281090000542075440c2c0c007550326080d42000f41401d0300c8074405000e81c5c3e841a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 324210719 1250 324209469 324209471
    0x702010815030a0c09063f1403040b090a082d070509100503010e030f09131d07080601210602030a0603050304030c03030f031a04090201120204080c0a050d030f03 71
    0x4107001c002842c064403a040100307891140080011004250742c00fa00403504040c820130384043c0e5403803003012913a000289204801075680c1405c001100718020a20074180b24004612031410b001d460180745800542c028844135800040070089400d103040140001c0810400420302d800000c04100390f18241004030224042500b240380380d08032020031051009201c0500a5405810056964410001c150180700c0c042d608103190545000d00020466007140c070048001030404030700b5000c00103000c0304083c205c01081d40f1a0214214038052100c04c5007a40002c0c0024054a440c140300340c0d00f0500f050740f100601c41200c004086207120603c000048803588502c0060341c9645e8580b0200040025810161140c0320101d8040200030051580d03500381c03402511400c0c0c0a440380201101940c41003d140c02c0518259000041a814190000c003400e51050405c240c0c2c1c0d6201c0e0249400300c0c0c00607805810070ba405264510041d04110441c20043d040039100d2800c0e8100341d4a000d02003180381c01c030040401d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 324211969 1250 324210719 324210751
    0x1080a02011d1513060f051b0c040f050f0c18040f0e0d0c062a0c06110c0c150903060609040311010504141b030c01030b150f0a0f0507020108 62
    0x12007900105110424003d0000180c80300b04030035030744641c105902c0031070038202e10710b000700762079001c1c1b049007800f200c09a070740500d080f60074030034040c0d01404244108000d2041c0400440c1c160b03610701508550100403200001c1528120900c40e45a50001d40885100101041186000007041da614101000d007645c0100740302c0441780e204001403c0d100840501400303160024442c5980c0b00d0514451a805610103103d0048002d107500300600300661000d040c0a4019038880c12140180c0103c000280100b81c00940410345402c18580e6521040b040c04a5400032000c580361351914400301c103000090b000c0703018108020540840e950f941e01030305c028464801000001c04061140204030740e4032007860000d02c4582401d2801402c040140218005540900c3d00540450954000d000b8004580140148100141e0400560040c82400c04807134110310740c0114240d48500c01c0000b04200e10000304d42994980781408001c0111552800390780030003c0030440000540c2e0b2107907806030405c021245600d05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 324213219 1250 324211969 324211997
    0x919030807051e04060309050d03060e0601200d03060603110301032003100906050403090501110604080a090b0412030e060403050c01211415010c08030c03070c0f0606090b0901080a0201 81
    0x80c0800303070f41d207202020000340401d100c2c1c2e01d80c2112521a01c90000c40d5007001c1d44003001d42c00c0d40d83c1d50094804008042c400100150710a4480c02c3c000200380021000aa070a44402800e15207100301c041d006c2074940408010b942d070715202c0d01b80304202c020320150855042d60b039405a00c190a52151807c1200c226524809030360610868010718480c104c10030118071540f4014018080440c0c041e00824000500000c181d40a020204400e030304007005007466039150342d10307200c981d00188030880c02c100d00c041c00031501c00403000080c0094040c4c500a004030702006c2c41d00408001d05112801e0007000d09001c10000520000383d410300055003405e10bc2005a24070007205100c030044a03407a5100360611103581c01d10960800c51034000c010b03c00c1451401c034181c200645a94403000c80c001c00c1c1c0442040011a40041080603541003901481c0807400d840f42c64840800c12481380d4019544565108020031566000384140102c0480c103076020342080d89444005502c0c0e481d40b56019060215422440030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 324214469 1250 324213219 324213247
    0x1b0103060b071416081507140a0c1124070305160605040b07030e03090d020a0302150a080901110a0c2604030b0c070b1b040305070e091903080705 64
    0x107440c030344003901d0300e4004074246111542d4562003108031500408612446046030b410180c001e0700c0d912801000150121405861101002801c6004010790500b41000c807121401c020010110a9070300c00311111018245000824050100c440c400c0f07002030750025151071032a508003040d185c0e040c911519a07201c0d040c16102ca02c21780d1940b100b00c104000c5c907401081a154030081c0203600a0303000c64010742c3d4000081e803c031041600b211196034824821441d90b80303448810b940c280c603c082c041c120f26503903960100e11565140040484441c401180310742d1010303840b010741e07a40b0803000e9000344400d020b1045195090310a0094032410040c40044403024013244400350050b8401240b4a80203800d40d00d121061385070400e001c00c86280c1e1042c0b01041c91840c90105039407126802c206104c03038684450b01604804894404030440c044401d00000000c40c6050184c0c600810006500ea200c034903042c0d41440c1080000741100e00c101d0242100c400c00300b58006881039221b0720307a0800594030202c09540721 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 324215719 1250 324214469 324214481
    0x80d05031918060b030c060301120302010b03010e01020415050a0906030c0e18060a0e0609060d03020a050a120e011e030b041409070e011205100906020403050d17100501021b0103 78
    0x40011814841d4008459124032100b05a05000d00300070080e840c101020907441e21184942035030f1182c4103200600100040110a290040c442e000014034803050030f01103821b44a1170114201d45960110701000003000d00c14a1042c085602d140c1140b6043e80520040e042d541d090190008260740e609810a81502507144402d960307600030003c5404001c80f10455a04900c102d5220b405440001800213682c40710914040c001c43c001001c0c00120f503181da0911904a110b814140c0c114171940c8103043c007064041c880e80c0c9500c0d005401130b6a006400c00005091500c00807403050400c1003030440d003000646850b40f1080203a5151401142490440000501401c2c407079001c640003483c608140031003014001003d03021690a90790100b0160b1342c070505108031020b00e1101401c0e1307401005040780c448516901100c1c1c0c0d54401d03a001030615840b611100d10300314102c010a00800e1074044080b05680020074a1980700c0882e0301071021356420900000e482e0000004c5071b96000044a00b1111280e00075040700c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 324216969 1250 324215719 324215761
    0x807030318081306020f010905150a11130312050304110d17040801051b090607030e0112020f0306090a061a030c2119060303051c29040506040501080d0503 68
    0x5580743c04210b0b010300d110070b06078031a800241c821851100721034001070050042803500310026100304e02c00d914084580c0c590007005000032a40d55550011040015406007007810f410344034a40d20181189012840b02510002d80740500c1000c0c010400015101681688514401d9901d0034003004c5a1402c0702d100c2d1000b68101c060404042000f08035014158819889002c4007444075580082c0c440c03290a2030f1160542a5030840410886240031901503004c138075800c803040c5003102c0502008511070040784c000e04240341c1c50203000020f02c002444c000381040d03040b00d0403d104001e0603203030900001180d0315445000540e040040001018000f0900545000c0000c0e03000ca5507000d01901514118950210f03022901c0700703050403c19440044510500041e2541510b40c0352070008800b84660b0038084241d0b2403420240c561103015058001420140b00c3d01221000b01103036a904a0104415200d009105900940c5040010000c284001942e04040001400c00d2552902e0f042c47d00f0847c2c40000300d01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 324218219 1250 324216969 324216983
    0x130203150c0702010311040305120f0f0a03020702101107060e010c05070603050603070e0f0703020c0109050a061e021206060a020f010e060712020a080a0209060d1112070207030807030318 82
    0x204549150140c00070b008442c400da80410043d0381e014001e40b054011400050030b03544c0a21910516418460010a1400d5204195a0900602c4080150b072a80f10a00c8a03002a07001710380c0d80110309040d000c010f09400c01e428142c070020f1030358a03060b80d1040940300301c400300302c41181c0040361640207058540c8040d03000401d89003600d445400103405131a05075840c0b0b029205008000034002880003409002c2e5002070000c910907115820114065040400c200c0708070b550f80c507440000514100840e10701325114240100300e6001580d142200e01c2c0351842e9503800703940100805042444441559684404100c40c203a07100c05180f07500303e21340384554610344446d40c81d010110000c84c0300001c0b0703144500e400d80d4500302104002c0000301d050340102c3e070152001c01c040f88003140303641259070050030a22101502250416441c40522000c1c0d4500d2140c0305452100082c000036140301c1d06941c2544800140010914145195121407852186400180800d0303907c0d03c0004248140100340640c3d5900012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 324219469 1250 324218219 324218221
    0xd060306060b03070f0f080a0c0e03010212070e03030c0705191517160e0d2109031101030204081209130c0f0f0e01090b0708040e100e01050d0b13020315 67
    0x29110b4415407098482d400070906014200d121540701d454040c030a50a20341d80c0340c2c01a00c81c0f90607080a00405906042445901d40000d43c040c0c800f48081d000001034856194068100440003414645982c8030003402904104030503800080001000412210141c0d203281040070148566411f1711101c4d00900f0303103104410b10005c7d507680e102c3c0600682c4101c3c046050150380391424a9488040d0b48584034007c5280442c2c194107070f243c15400140101d0049028141040502c150700c0001100360040c03a002c02e030881340600920a001106481c480300a0800b10701c0c080c2410392071540c41c0c190f584d5620800c0000580c60100d0b8465003402600341c210840103001e145d900b00009440c19000214040004204c4d41c0d48c0c24604d44101c103203049180c410b8442007917050510304400f60ba94004081518020f50800001800d44051000d03288182ccd5003810350b0f17004a007041c08000f4100c0b4107134070040c858200c0c10315003804116000251500114446a5071940301c207a4070109040c0260420b80c0602800703080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 324220719 1250 324219469 324219479
    0x7060b03030f121b0406090306060518040602031e090706020609161503021e0304110d1106130f0807050a0602010606022a0a031103010f3b0a050106031509030e060d06030606 76
    0x209140181c034410328081c080a9203038be0510078902e180c01a0403500450400204001c919168011a0071514100b40c0e0b20b48040301c8454003128101c10765100442d40c0c00f42c4020001c1990500c52943c0000700a0040c0c00d4045080100e10b43d07034402c90040d844001403e801c651085800382c3e044425482c4002d034542c038181d803141100f03015a0003c85082c1e900100310441102149000000e00035081c1e03001031000c103c86042402d202e0190403841c00e0200c0f070b555801d80810b01030300c415003d0005043d0310009018003810310b0140103203085a61b00140c156030400c941400b8180d00412421050081200303800c289484e0b500314442e0454542d00011f801c001c030740350f000c8180a44580c001009140a03030092001e214110400b604581c90883e0305054904580e140340342c00e002c40341030b00d25072204154007030708122000394855040109401c011136040e90340e40d01c100100b08900c04010804000c0038030400441e10b451324082c0030b00e030345174201611851000070004000280c55004e031001d540c0101042052a44030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 324221969 1250 324220719 324220727
    0xa140a081c030f0c0f050307030f0203010f0306140412302705070b0f0903060721090305070609080c0d02010b03060a02071709061b0307060b03030f121b0406 69
    0x104801800007410100703490007030407042c06204440d01340da0f0b0b10f10f4a401c01141c4226907a40000d0012000c2545030b050468070100240007560190552aa002c2c9a80e403030351038070008607540031040c0d07960038003501c0c10800800e504062004410a55041007108282c0100c01c89039004410105c9241445c1c0140c5415840d4181340d1044100c070101e16480d41d60f014a1550490501d102d840d03004240e42e0000700c0c02d00c4881044406003000001010340745060088089c00603003003103c119040d00020b20000e51408442d04c0c008040c20410030b0b200310400400d1101c2d1801051403140c1a000761031076403a810a00c0400c82d03450102c03402caa0503401603a140d07a0b10450f000780600000c412061185c07103505c0c04500d15804500c211070701103511020503000017071541da1114554211a07407040c1d2007401803061002043c0112244010451424041e40c1c2c6d4a04500d4074400310380304c0c8081c82c0c1c0254070070f05c031210049142e8011129500d0034142134030200c0d0b8881002c0240c400a0300100340e182d0f68081000103801e600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 324223219 1250 324221969 324222013
    0x50106020d020d0203031501110c0303030403050304061404020603060603070c0605010f18020a050318030702060a05220320030c03101b03020304081204030509220f0b0a140a08 77
    0xa0b582541c41828003984202c0e520b000c151409003540b085070240c3d0005600031900081412640c07030965203500f400d42d00090840c0c00c11078040d07012401c0002081b040020070b10881058018105020b10f42c0d0a1a801040300d41c000102803a01030b20300040400d2606001e8148040d149030301050a001561b160604402c050741144103c90a030129103071483c0c021013090080c0e4400c0d25059840324210740d200d0028012018808141d995140810000c00016803960300040000800d2901e82d65502c290310640c4a4100401c0301c02c541002001220131f00016854025155880d161425060380f0000c400c00000d040685c25005183c1c1442030200c44448801030fa00601c03c0f40007211088004540103000640036480100e80040c14504204882c01c0700295041d80c4580040c02494954200f404040204446000c00d04850200d60075800b121000c1610a00071941d42150300c05050028806800108540c1100ca015a00000303412020403c03058440880300002049000101d411041c260710400343d801c50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 324224469 1250 324223219 324223243
    0x90106020304140909150421080114010e0102060402220921080411060706060801020304030c020a091503021302120403080105031504030f0f20030c010506121f0f05010602 75
    0x41410342e00003044c940501c10301d105800c0003010340006010550924603140d03000b00200c450305514038100e000c3c44550004444980a135031661022541041030181841040c0c881c064104a0000344c6200b66981c0440ca40350000d50554544442e0701d907242c440305200300300700d00c2810020b113483d55141c103004403182c450810920031080700042251002c070403500f81d01c00306e8025001c0801c0300e079810540e080010040c01c0e0305029443c00a2901d884030015420799109030f030b0981c00207102036544000d510b005683c1600521038450200585408501d200e400e04402d40b0000c2c0c41600145640c408c01641e0fa0112115030404840004162619240c0030b0000f03182801414003900c50340340314a40c080040a007950240d078040d16910019500d10000311241000b20045604110391030010746002000070b0241c410720401074001d552100c02161905003140c0000b01464411400340b15210241d00e008642641200445c88185800304c050f40c2904004d07162110b0343c990b10500e0b1400010b0742d0340c0c0c0440c500702c0002e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 324225719 1250 324224469 324224489
    0x6050d03021023010311010c0b010e07020106080c0f010509030703020a06081b03060607020618060412051203131502160804090e01110412021306080102031f08030708070f02090106020304 82
    0x41c1d2001416012400f0600f011801c00c100041c0042900e51050441120052614585859407030317440b15a42c0c0000e81c4840b0b2006003410522050341d4083c01640003403c010001400c502c02c6800000305a88401001c15050000004040310f19840500400000d59000780c011440c0c6580c1e003000600da200204e62102074404816041c2c2400704a8900321f0703006510080215080802c59002c011159110b9110000c680342054520382254076401c0141006080c1e04884052050060601c103082c40d010ba02a0703542c102e400c00800441c041681d09500c41e541c2c010000c09030070550301086400920401400741c040f503240900310805c100d200070091094074a002c401780305000c6501292402c0c0c403a0340704030710a810000e02c42400212002d451031900306000a1410300d040030180c40440444440e0b8002c4004ca0350000200b05a0107030107206925030280e450b2002c12001e1400031003941304e005441c0e0040c0808000103002c814052150013420056030010604111542d44c0c90019660342e0151091003111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 324226969 1250 324225719 324225731
    0x1407141b1305010501050304020918011b1115010b0f0f04080d03060b210901020904140411010c030801090b0a0302030102120f1305030319180c0303090b030c090d0606050d030210 78
    0x740710030301910b41280c9040e1070b840d040d9200c0341c2c00c0080012004204000c0c2803403240c03400549540900642c036642610b01c0101205001d190350041c02c001d990104c4070441d50008003015413911044410504651404040c1d607240c03040031440121610407036904038034031000803802040001e40071844102d80d03041514108526681d4010400303003405003441628807040c580d449052000c0142030410791007039003d800103203071484da400000d08036801c41101100042080e41003004207d9038600700c64084109003442143c00000703a80003480300d8814028605015200c0c0c040d400c943c0c40d034180c0d03840a10ba00a0003952112b030402ca0344400440111211500720010384d0201d0031058804081c210420b412802a5207035580380040c3c8140f40c803070410076141641c0d50300746103c020450500381c00003075032050000000d9a45981001400c0c06410b801568444004006000004200c81c0440e540b00720150382680303c128040c03c3c1040100100c1d8491504801c0b14800344041540c0461505000390040d1420045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 324228219 1250 324226969 324226999
    0x15030108151504150f0f0302090f0906070c0c030b0a02180a080307030302090a0e2403010c0807032c030408070b2113200102010c020d1407141b 63
    0x41042582d02d070101031030165050080303003050b804c43c50300420310303c4200022a03507030a80520640702a40c070680d0f03601c0d5074080500451a1039458242c012444040c0155181014514540c036030701c020706a903081c402200c02440c108101c80c070130607004542250b19918145440b1003107101952004885465902144101803140e103040050282542d00e0a801942018400e540070340081d8440c0850603481f010b6100001140780c68045154803c3d030002000041246080003c070004a1b1012020b40c4680d04101030a031003580d0040341d450b8040744610380891a060b0881c2585a80d080900000c41d82083d0040b10718580840080184201c0b0380c058203d0b594a603035603961096901412802079804503c8007501c110180e08010407070f4006180c5100310201d00702c203542d0080d005c203051030840c0000300e0740070290000c0c0d80c080c894106951128000b601104500c0ca0b0002c045541c81d291002c00030307001041c1e24080c01400c040103412941c0003000c030303003200603400d5820216580036510144140315000c14180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 324229469 1250 324228219 324228253
    0x180d0618150f060b1b010605030d020a050d14030a0203270c0a06020303190509030f0403060f050a0b030709050c0d180b0601050406080604020714100c09090b090109051515030108 78
    0x125800d040004d41028400701401401c41c003000d00d030700c40d41c0d0b4a03100e01050965083c40000080e0030581c00924103200e486c6000f905014004266405000034541d03095203041803a001c80360b100d800300c14010f0f034039942c0e1000043d1200107002005400d14410048030740550000503038040f00e0300c00300c9203001e405039101012a601c2c402100c6516441102d00302035090681560003e903040401c181c21750307080452405078002140c200e81c0c0140d4080e07849412141986000748034580c0c003d40907107003e1006203030040202e0340d42d41080c42600040da030398200140301525920182c030314051070705209101101801d07042d0041910198001d41d41e840300203020070019030142080703c084465644440c0b24a540311b504000003500070580a950329001e0301c0c139050100307005103d4a00d080381980400910540b16010007407a05145030403100c1480e00c2c0c100801d009507680715840341160180000400e4035601c0c24003c4800f032100101103500220044044802d05071102c6c00b46040c0d4410500301c44440450b44a900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 324230719 1250 324229469 324229481
    0x80a1512020907020c06270d020f090718180608011b031808070305120c0a02030d092d0b0a3e0406050403030207080102180d0618150f 59
    0x1035003a5100c406004010b00b4049402079102805005581100c0c1880000c41c10a41c001c041000100a500e400158180c6120035242c92650f800e603003108540da02035001c2203900c5904054240309800070700c00110250301c40d00d01e603880003451000450340c040e5100c0f8000ca8210300c040602305010304090300490b00060500c40d01000d0861b5110400504882d0708081d030081c81d1011a501004030b101401d43d001c10b0003600180b0701c40348641d0b01c0c282d07100c04410f24030642c2c403801b401000e07481c0020420800c10319400000e80345032544003140000c0190840c03030420210681080088404d6081c1d0020441c06920f0003642001540a00800a421350b26184c0d00340c11103081020b150402005440744600c8148445691828240c1072103400c100080e8100d485041d41e0030950002000a01c00101441050342c1404060020003050000394180149590183e0940742120a91405602420055001c0c44620f0b000302211a8648682040f0000d003810000300d8928184180d0007564100220184401ca4600c500c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 324231969 1250 324230719 324230729
    0x10030209042004030b0c071a01030b40020a06350705070206090d1b0605070804140a0e04080a0e0919150e1f0b03070c030f03020403060c080a15 63
    0x18030f014150307581c1031319401002c1c1c800c040151040c0b0000300018496100240c1070401703511480b003c0e614501d441080030038000e140b06404159070340300464548020b0a00340302c000d000c04103a04144920781100d011f80c884031038083d500c144042c80016510340c101e031461100408002491103200208000717814020000c1e00610301d8465400c0000c1c1c035080c403610242030702d948000d2950b8600411038002079010700403080c003500c00d11001010220b4211181e11082c00500c0c4908065003080e2654581403401d00591040d020841e080402120007540c405418001130a00003400001d18182800e002800380c000030280d0001c5643d841c00c9509a1801e40800ca101c0c2c03141e01a6240b64410084050015110100032a0b40031011000042484203200c1240361299800c000040303080d031103c4201d042d0498041d800448184810030622500c0b507070056100001c140c00d4201801c0011144004800912950344050074041c5032107200b40d5040e900c4000140140707202d400c10304c0700f100e003d900440389030000d00c92 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 324233219 1250 324231969 324232031
    0x501080601300b0906070f020f0601030b0c04180f0b0427140304061e11071505041a030402120c031506030304090c080702061510120b1003020904 64
    0x2410140307004000204601d1001035880410420103641c41c18243c0c00141c030a031031030343c0042c0c040010340f40d8440b020629000491000b00141d18441651035220001808050320407402c1c1c1001810640c0c04204a500910f0300b10f02c602900c3c0d008170340f105c0081511400044140b0700f0400807080c02d00e498001c81d4924840603c900580d92030140d000d02d08251a07600c01c58500c40d0714410a042d1201c20701c0a44011301542c9c0b19a0303c03940b94403041e03207680003454034100103108440d0780300c030704107540002c41c581a1404c0501e194010307203602005a41500856021050b49045503825404500e228405580158401c1e1440b41681080400103911401c0c004a0140c25501210009181382c0c0c104425540119024041d24034244d184c0910000707442a0706584004904103000f03025901d6070411000f07900c00c3c003520381c0040e080c0e41130300050829045840ca0004101008843d180507400c04d45c041203003044001e0a1a041503500400070380650410011140700700c2c07600050b4904800188074500b20700c3e056901d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 324234469 1250 324233219 324233249
    0x6010906110c040c0e01090f0803121510030c12060812070c0510050310080303040215030a020909040c0519210807051203011a09031f0e1f0501080601 66
    0x48421a034820314001e400d2003506802040c40d107a41c0b0558824215a590310600070b041100090700c846642d40c451301c41100038200c20800284081b06035140076a04840d10b00300c1d40c81e00e10407265041c40740422103520241c480d03600f03001e40d5010f508c410701d1380e4019141c0b84c0c500c415405611085500e02e102c0c0f0061034101940381e907010b00f45034006041c1144202c8680f81e100f5140c0000c1415003080d40501400302d400002030100d0500306000080051600070021459494554040707000384042981554080303a022000c0b4a060300305406071902000050240c811503d000d0910002c03002480c41240d01400ca10301e07032000e810354a80310725000c1d1038186480e0303d4100546818021a480000750544140740c0a0100b800092030a025144c2452000b400080d120750503d10010080901042222000d1030100807c1800d5100414903034003201c0e0b03010301c05500ca94201c15040141c0080030650419026022285840050007140c540c01610148020042030f0303243c2050a40e200b1082c0107441e00c00301248 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 324235719 1250 324234469 324234479
    0x10207210215091006031203110a05040b03060d02060a02060a0b030f06150d05070909150606020d0c05240a0b0d0822120f05250905040203030f0705070f0e060109 71
    0x800c40c0743d000540742c2c003110740034158074040c0e01c215443c42d0022140300d24034101c030f10321141e4540100901c0140c1661081d01e070540703984010700b4038031543c800d0701410314021001980f0783e602c081041c2c00c5141c02801e1a40c2e0790290120094584a086891143c1c140c40d1002d201500e0a001580005000c00440201001d880302c404009102c40021001540104501e0013000054010700c034500c020a402100400c50b4003051034003030311504480808122080c503141c07003004800d900051100580004d1700300080009020304042d0b04001c0141204001e00d800715400c2100303002d80e05030244c441c0d4401c0a0400c840000f490400c1007800c0c1003071005e03150030001c0c00761081000d4034050400004200e0702041c070009946004016138801741010681d004000e0543c044144441401071050003100c003c00000a04a040782e1070700804240e0017585c6445686800040443d00c041088407102000000803a403191071070318006a44034482d01401d4001200b10400150480120106a010781c030161108040c00c1d05207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 324236969 1250 324235719 324235753
    0x5010207121b080d020c071d0604020f0d0947010503071802040f0b0d050702060115140405030601090506030708010902100c060b090403030509010b120a11031005090102072102 77
    0x4943c0b14484d00d034204511240301000300803100c010900c417581c2103400e0140c1c10350f9400d645401000d480c096401044108004040ca81c2151141d00100e01d00040d2141c00c0c1c10501d00d00c098500c0d070b08481502c4084168070009100c1c000383c00c0d2449003503404c207503568a02d5490500500a104164050344900000c1c000f0361140c80d5441c058030700e050300050030256991095032010788140e0180303200b00c00000c1e540102107001d0140d640e110141d80000d086951402d084207105000b0b1030800c204210908103801e0044030032030b0031203004010003002c46070300b940c40c1e441c070000419080e22954403078860f103800001d8901041c000d012560750000c148a010a0303203114151502c02901c1c100300c9546a0700d08052041d9940d40d00035070700813030103070741d0005152410b81000c40c21180e5400c1c40707074450582c0720304040142d80c002607030302100342c1e0040d155400e82c1610404a4a400c0030041c1040616080108000d0f00c1d4105502805666009180801c0b80d44060020040c0440702c1280d40070068000203c1c800c00c01d101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 324238219 1250 324236969 324236977
    0x16140f010e0d03210203011d1e0630300403020d06061d0a05010f0305030d091a01081606030626030c15040209010e13120207090905010207121b08 64
    0x13940d2110748034101070082040403a40300b6001000380309131189071907145690300310b102c0c0e501214001d54014000c1c4005206082c0c9080141003500c2401d84400140d040001500c813405200200f14a91140c0742070154803070b40b00e0280c1180344040c42a058021940041d00c0000e501020b144e02000c03c1c60582940c0a00c0a50180c5000a460f015111000000c40882d07540f54a1f0088007100e041c40f00e02e0800c0c0382454241c1343d06a200c0091440c1030a0f00380081034000c401c8500a6003406400598600345207070800c0c241c0080c5002e080c640391000000240a1004224203191149142c550022161519000d904032050f90040d00c614000c48104202440b0391052085082802002204d0a26500b084501d1804550102d00c0040d0f02200082c042141040c0c424540035101c103180260091a000c0c0c402e6483e1850103601612900900300c802401074000c1c030100c0054000c19605008894041c1042350103540001d4084456009042c079a00801d44203c20080c0c5007040340340380080c080066202c422842d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 324239469 1250 324238219 324238247
    0x403030228030b0306071b0516121401150306020a0c051605040f0903020307081b0a030f08070305011a071112070501140a120c0216140f010e0d03 64
    0x6420054015078148102554030034031810600241c00c070396421401400c1e107050140c2036010381c0c4580240031703004e0b4104500061100c0f80c1c002280000701d990520519128441107071004a000d402070101e9025070040d4400300e46c43c001c550040f000f84004001608903801c0e6001d03403992070080750091001801540003414040d0035840e00c0e90f610183c0303071035041c02c16283c414042ca000f52283c0c1c00f00090f0034640200900e0352101981003000e400542c4000e904c80c031400c04028104a000a40d000494180dd12a07c1c80b22706404115428407015150107012005613140b440b0204e0302200006000e03601c00d0090701e06882400a19003410400c400000816030401c90045400c0c6490403039660283c4c55007140740e01e0310080c4000400c0c42c240740c00005800c1c003400754030540100b03000b00200d0580700e0f009074180c14100001c010001c2c5520107030204034109280f003824206200031014000a42c0952410703c3c400c464421281d01c201d0310800300041d62800f00c6969107580003441d100307142012a00074035403d11222 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 324240719 1250 324239469 324239471
    0x501081302190f090e030715020f12070309060b0d050d0f2d08010e1b03070e100306140a0e0f07031b02060f010e1302040506010509030d08160302030705040608040303 73
    0x414010b804840c0d0511a00003d841d464401e004218a800d240602c0d1000035143d4007442c680a001d4540b021510b0340d40540113a044e800060f050904140c0c102101c0c0c844c9d032146045049401d00c100000d0181024200c140d41c800d00700300d403400c8a498a0b0491a007070560000c000e040228544206588404203041864184090101e8894010030603044065503005601c448180c1d1710141d0401070002030341038000401d5050364404000401190307050441d04900a0160b03940c481e55402800c503245e94401109038ac014081d04828440a6095040042619090749084000482010920040000d64481c0d1a40e402107a030100c1c2e1540001c401c80760b0000390620b40821200056001d100010110a81d03003001a4026010448100408204c3d10f014003103c0400380b50900f03003401c0c2218445540c02029200d180d03a030f8007198207030b03020b58121a0451005419540d012080403400707000c286048502c8880d03000325801c62103000c0d10034401c882c81040146c071414182814038204451402c0d000340124281 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 324241969 1250 324240719 324240739
    0x50a0e1306030302060105031b090103060b04090204060303210e031605070e040c0801061a1207170a09020109150c0f08090d0602090f0406050a05011404050603070509090903040501081302 82
    0x1030358080c040c20014600980061105500d0041414a4800303d0420100320240b60b07008414140d444100a41c1140d42040d800f15035417800034005001451b490300e000754000d01e4000d00004150301b010050107208117121a13150050000469001941d000d500d815a285d0070030882c0351480c14480e03002c0070f2314601480032514101e0311803a1204001c1000d540940303421582c1c0004000003c003d001d5900034208a075003e1880b0b601d03659404169000d00089072480a0322500060305241c070810203600c0345c40c160720034507a1714103029120300000c240410003a0300148840310301090070308140048131180c41d1180d94020070071003580c4411450144286040b1000881004520f0903640c0305075074a00075030701502c0010b03a607011400402503084043d001d401c0c015801c0020030011642c0d0074003007504598084c01c00d40800f658028110b162031040b900040d5120801006002c03405070b0090140440c510140d51544464444d114801c0d036034000d520403a03001807444d1001441c00031092084041c5244041c21403050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 324243219 1250 324241969 324241999
    0x30c0c0b03070906021504032f2506030606020705010804060b210c09011202040504080f030f01051e010c0b0604020702120601060314040b07050906160f0506131a040c03020a03120e04020a050a0e 85
    0x140030041c588800a9003d8503440110480c4ac145003000821050404010303882c40c140019488044d80d10900f810b21a0582c0042c0500c00190080d64408400800d02d0359003041700c41c0c011110000c41060180103100d81b40b000c01d650700704100d030203051f40e034131080d03260340d440043e420400a03141c010030448403210103000411000040c1400345002d00348d1304000d814a50f0400c3c040c0440c0ca1181d1a21203428141041e5011060740c10900c88604581c002c00400c0e5a95508000314008c3e226640c002900311102840c0940c40d0351000c03881c5e80c1030302c00954041c13010808840751442d907001c060b40c000c3c1420741d21070080b4002c175010310020009141b02508250a10a030354520f01904004002c0998011240070182000c10000303000c020f500598008400000000c00d494500a0110310440c2080d1200020045001d0100c03880300c807001154010951640c0c5522868a294110b2000c00141c0102c0c6480400c100c40e8580b5000356a820803032981c9150800740503040c00c031a444d2280e059a43c0002d40040c114074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 324244469 1250 324243219 324243223
    0x7030c031505060f0423040f090b131b08030403120c121d06160b0703020a0c0308040c0306050420041a060d090c08010603150203060904030c0c0b03070906021504032f 73
    0x3000391349040f0300d0b00d840c0480811b000650340f61840c10403008d8a405e110b94000f903c40e8000c150840030310000c0d04650032142c94081c0703042055000030705490010f01400070b42000000000d0050b02d1042c0131200c0c1c0c0c103040ea00c1c20748103010202d0000b050020350741840030f111031080141140e9000c10b2460030302c29180c1407001c40d0250303004181410070440055001030501c1880c242c029001803240c40c1c118604100a0300090180003c1200102081900302c0030505001102d0f80c150051604894100454280ba03e40302d45c4241c031424280c0252407001d01c4e00a10780c9841c0c400c045c40c5003d98a0810045031640702005015804031504024150352100a2030114680040d0341000d060400c000245460650910b0948402c00c42e902e212268010020000c1c913860700702034581c204e039050a101c91044d0092600710324070920740c2c1050098150200c20800c00b245e01902c204c0817941182c0035241c44980d29080c8800742d4504036000b030007141210441c100003202402d06040e05a2915010292007124803050074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324245719 1250 324244469 324244499
    0x13050405010f15090605040923090a0203210307030c0c05010f0519050606070f030c050f160902030403081914150f180402210a050607030c031505060f04 67
    0x801e400c00303040c00600c01c0e20440f009100003441d2078102004039500d040d00041c03c51207540542500981c542020780c80f00000c0c0082c00c0030f0b03580300c1c45c1d0443c003e182c285a580c0c2e8420301c2240580c42441410b14880740500c09281c680801c140002c6114070319554a101500030745806110340e81000107000b00500400c00c01e00c81e44688035039802001c1814140858441c1c2c1002c030740303905000341510344002e002c00b558450044038407250b030003a0041c800044d81d00b82500c26228946001d0110f010b40314907410804804a20701c03016084454520490540f500308100803401b00b00c40080200710032001140300d02d0f80a1500c0c03520b10202d0721010510703c031560501070b407400c0299021550001c004122246616001c07072101044c0d8810380e000240d403c1c00810000242c00040c101a0151a0780951190944410010003540850060072641c50395100e107032a9640340000c035070340f10009103802400005980b081c000d5524a0708c40400000800b4106004c00001da8080c040000205008100000f58055901291 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 324246969 1250 324245719 324245729
    0x60109030b071707031a040507030603080403141507020309040b0f03010c02060105030105150306010b0f0915070303050c1603110703061103070e030a03050a1d030f010b0f030616051305040501 84
    0x40c00d0003d01d070106040100e40140c2042c0905040803101200c800216105250940084501046c1c54a032082c0c242c0c0100b8042c0c1010b000c56400003800300c24000741c1c0b44024017003121541160091401c9403290404840150341190051300204100752052802d50003201c2c88c128006c01c0f0214230107402c40020b08407010104244007580201c0c0040210f0714083c0318050b841101008402003a420b1800000e8489005024096030f905002c86c1d030340803580074032040d1201a07802070314440d000c41001414001c01d810000c42140001d080c41c0018808409050650b0441e00e200c00c042d04004c00341c0d41d000c0d12603d031542c0c5804083d00c41c0b9007000000c152240900e04900260481490340e0341000c40c0003c01c40080302941d240240d001705040e000080d400310448204407640e1409000d07002d003030407000c11044a00c155032070341885544446a21001d06620030100040d046400403c82e490701001d00d0b86542088400503401138443c1c441911075401a8001d0449940d005904901a522000000d003181c8003030b008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 324248219 1250 324246969 324246977
    0x207061d010f0b090702030f0a020703061a09100305061909050615130204231206091b030106050d140304030b0c04030605091b01030b01030e0724050406050d05060109030b07 76
    0x412680d40802d00c590f2aa08500740c8400701d480ca031000d40656203101c0d80341c1ca599a0040003c1e1020840d00c00d1041601440d03100f0300920042c1003580b5444801d9800e0050948600c03448070200700302d6910016040112640207000d4802641d9140c1004941c598a00c40720001d26115200c510002c0c400348500d510501e8a09852140d0301c00000070300402c50380708a920780080e4030402c02030000b0000001580c0b0688480c0c240c1c44000d40040700800d0142d4031122481846104440c14407000d0407003c149421800d031640c8030003542042d00c1e4101030a94400784162504a4110104000400c2090400700109000c6800b01c0e8501980c80c2d448135880802116126494040443c0c2401004a40d01a41d40c00503411001045d0854403906042450203041d08020306055480000c180385900940241e500401541c0030380d11420303034a0524071b0100342d4074181e1401054419090a03601e50281094900fa141e1903135840b802c0030300d5015140002c0c64090b1225040c051003200c000300040151051510a41c126a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 324249469 1250 324248219 324248231
    0x4050c0a0806010c11150706050421020c06040308030c1603050c1c0f120608030c010608070e01060221090607060f06090533091e130c090207061d01 65
    0xe0300400d081000b400b40342c100700c000d03440480890b2400c01803804440049a03050010140052030101d688a0102e009000900300002c02c000d1040c06004443d2100420001a54940740e004089845150b1982d0f4290302100c00e00050000c242e12030051135001210908941c9401c6601001c00c034851071011003200000c1e40000c00c03544800b010300c080d4541216800c24411641c41014003c1c0641c801e9441102c104200714921820152454004200810a0304282c0f030343c03001114865030180003035003c0c44a032441b03885000540704400502c00d40c100c0e50315602821f0301c00040000c03122901c40c1d07541c1e0005081020b2040040070f076698030017401e500f4450140055240c082210b08800da94040c1d0200075007a141c0f82c00c11008010190b10021681d804195001d11108103000c500341c1d0140e640801a003041c400c0d0200f182449141d840c1400e150040e10000c1c1150365410180140400c0d151b030000c0c036003c4244810403422170250044c040b85482a40d0118801c00561190107030003141c1d415040c0140e459103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 324250719 1250 324249469 324249487
    0x607061d120c10140a02090411040602010c02120304030905060705010605040c030207031206080d030903090e070207261c11011406040b15031501090314100e0303070903080f0904050c 80
    0x10103c00301a8a8024400700081c4044810a62401070a120144d070b0006000703c2035a0b155442070390a03403103c8903110b45464071000d0081c0200503a06828025115030002405400300398000d9911a07681036442181341c45c1440c0600000da00040011207556480e0300000c41c13141c1da03030700415102a201c0d03500142c5070481070400a0000000c01c003054030310f9160400c280007404c404160101813400320b00f004103c0030343c1407078225a000150360200c0072219160003403200a03170307020540b401142d4500d44c40780f00c0c0408401d07070100e4031a05c8481458596111407185044800c1341482c03908941064100710040b5046009590b00b50380062a20180c4840c4400c200191858248560495000e055500a41e480303c01da8040703119110241a5000740502e0380041021a0301c43c2e21008099648185450030018080c046203507510440c00e2408075031030800c149a020700c00000305803407103010f0300d81e129078006c3c1c5140c4070075846074841001c00700f5050701002050b03019104c44c058a4004d8100142c625034400d440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 324251969 1250 324250719 324250723
    0x6091b0f0d150624030e0c09060607020a0b0301050f0109060906080c190c0203010f02070f020607060204051302030717040203030712120c0c06140c0711040f0e03030912090607061d120c 81
    0x80200ea0185440d0450a1241b03080005455900182c1031b1543e290a407078110000d0014012103c000f544010940c00208680011030b01541c100d8506440040794840140c0041d0741483c100d00851001402142c02040098450001300d1340080c41d22141500c0d01182c0c421209488200d985180d02195141c0f4610085003024402c1e002503045200c011420400d199403201c0040028007000f91007013001090b1281404901d504803001024002d1440440312062a50311029403c11610700b400709400342e000980004030002e040d8491680200030754605501359860445a81c82241c0c242d04200e0074000c001e05625041c4100c14200d007003a207a65130700303244c41d140a50a42c7c0b803400684045101c560140641208144141c0354890b80c0403d05007041c450010211300202103100000c035085040158074040301c0c0002c001103000d80e40e00020384840d040035251300400c521130510f0554000d0020411480420480d80c4007a0f01d0011409601c0030f84c608403800d00349004104c080c1201c03242d0002030000ca0b00c0d801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 324253219 1250 324251969 324252029
    0x3020d141006180512031b0d0e04050709050d05150c0d0f0b030607110129121216050c13050910051603020c0a0c0806091b0f0d1506 58
    0x420300d000140842d4504161100c0c40c0c6134428039000700000210032007126424000d9070600d074502c0c20403c54100c101d6a16a40d07404d10f94580030f0200d0041d0320080910b0030325004407072142c03101e500c8510000b40b8003818401c046040f51000e8a440c003c403520104070400000c07000c0d0143c2040300c402c6840d000d19160f040111461030f0345000d205444e160048403d5200850f229034002e02608040715034180340c01030300d409014091002d40342d030501a248000c42c2e17403524001c20386000040e105101424100b03400c00b9541c000c219032261940da0184404017003446504503528180307214000f41c5142400050201c2c1041350840b0f190b4011985980030045080070030044c003041d152845606000c0f9040c07044044500c031007a450700c601019000103142140c0c40f002c01850750b9890f4010b82c264400d0380e17640411912541d0998800c5c0e4607000c0c12000010129400c4035529000034000d04c02e031440d6034844100600001d040d101180c2100201e012494070030800e00c201401040c1107000007000207114510302001040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 324254469 1250 324253219 324253229
    0x40f09050d021006030209011e08011506090b09090a1a03060103050a050c09070801180e06040f020f010f0512070908060c0d1508060f07050f040902070506060a1a090103020d1410 78
    0x125200080005d82e5400b01f000c0d04485021030b600d034000300450140c0085845c0d542044000350300f007440c640715482c0302d041c52070708840c42c590b0342c855410f8841102e14142c0c80f5503440c095012070b540c5c0125880c04140c0d485a40251406044102d2910b0004046424450242e0040c0c0e0aa04445650014050180700542c081181181c44004500e40104c0185c14801c040c0a00078444200c85a0100c00e4401c83d417108000355080802c4440f41c0c941450014422880947c049005251045141495500a00000d1041146070319414180301c00ca0001c900c00c081d005040318104455408005168a804d100840c01107030f41d030303280550701e08020784000706455107542011103a17031004108010030900400c0803500b215580c0b090350481d850310303030b81210381d80a03601d00386425800015000840c00130f60b034002c082081c85202640c4003581d9040800907980d125100e4007090b0010500d4082c045030001c00105078040050400509020740d8024100c01c03154072040c141d442007806014000d5000c031001120340100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 324255719 1250 324254469 324254471
    0x105090a0605030a0b060d060615140c03040302150d1d0f0c011b050f06091b0604081513061e0b0915010c031e09150302090307050f040f09050d0210 65
    0x6180c0b00110740d81c0c404001001d046044440301040160340c2c0c10310f03040310300c54000750113101c1c2580b12074861440b0007500325075601107011455140d9241d0041c00a1b0784280704030700060f50a107840c41e000e100705e094043d032010341c0005040103586007a4115110746642503a510ba91100011540404946440040e10b40c806030791b07110000c40d482507039000d82140d4565a0b52140002d401c0c40c1850000d10f026800e9040401d5070003039a0401c00d9a010000c1c041241441c5224424181c0c8900c46c2845054490b6009103d0150000d1104484d050013207483c4035002012505502c50804c455200c6a007150040403200340c0c6102c1d44011149420b0b007900816030640320888a02d04640bd1082d2a00c5900354400907984c10300000c00040e000f454092070100d15002d004926040c8944031801c4003c05c3c0188900880445030203035086044401c0c0b00b4401d40e0b10a01c000b4000740901e0781800c2c1003040d5010078070744865210351a290500ea21503414001d41851a2240380244905140400f019007040e00c00c00001c2c0f049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 324256969 1250 324255719 324255731
    0x30f0a1205060a0b070203030702031b21030406030e1005090d0324031b1703040302030708150a1503060c090302090112150207020409020904110a09020408030a0806130c080105090a 79
    0x1660380f110305104480040b6006996031049101090560044250196241c02054003c5461409102540144040803280c05145904215071601031a4491440300d005510501040c000300380203900a910150040040352141c40b41800c81c501600c2d021515401c030b40d088034903402443c1e505409100d214041034008045804601c1c00710580300e00d0940f0020382500611400070021010181201d4090310095108070469400c5111070f9640b42d22912049000c5e225944000070640c3c000700e1010550305091990844e107869030841c11016251641504c1c18003404210004001002440380d840360000a440c0c1e01a400d02e5030040202840c0c050340f040351500061600240001d55a4103414070a0706400300045e00c0e07103960700201f0f00070311580500940055060042c0018810403160018283d00c0440700740c4205500c914030403050340039a11508d5510740c0705015094006028401441e4425000b801d16014100000341d10016540003040b0f42011036403040052005081504046a00191841d41170001e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 324258219 1250 324256969 324256981
    0x1a010b0c060c16030e010504120c0305070506030405030304030302090a170d08010e0907031e0b090a06050703020a0804030f0e150a08010801020903030f0a030b0a0902030601181a0c030705030f0a1205 87
    0x3000ca03c98800400f040102e4042800302d030b00880c2590701a021802210503013414a240001c0c000b00d083c00141d80500c29084006014a00381003102e2056074003074044c60454445035426400b94009850090344044030510108060031800c0051482891100080001642d44079000d0201c00040c0c010301d10300202d107010072940842c0010040110791740010aa00c992a030551000f41140b00144014400d4882005001a41d02c001405801640c00785200300035036150f04070203800320700c20003098a0128505070002008640120042d5030b0410f5142400328401c034580002642000d00260354021840020817048001079000c03803400d000d4265078000b1450f000303600c00000da4130300840060350600000005d5070385103103200f0740007441401c0000c1c110880041c0c03514607000103900105c2ea114000f40c01c2c0d1a021004c5440324034040d08503285c2010003804043e2106101c2d5966011103078100c25880200807030342c0003900c00c00003001080a0a085240c81e0644030400a20002c00c0054441c9420304010a02503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 324259469 1250 324258219 324258247
    0x30f061e05070818010b030607180f050d020f0f040e010c02070e0f040803271c080f07200313060801150215130501090c140a06020a0f1a010b0c060c 65
    0x70f003002c1d00154050030a004100c9541c00341007100402d1f42c042c043c10051054981e0070460150510f1455050002c500f901d8a022030070380a918818281c0c030003400140c56000d81417035800d20651060150541b048450290041015184640d42d11030b0a0782d0340702a84606103505200c048003505040b80d40780d890381406140500e072120040c0024291510020200d443c6641c00c00c0010741c070318083d14134078040d058803500403503c3d0076004140c4113090076000c945400c114032414466200c4c82d20a480121161160351080301c101c0e05100c500f01c1c180c5010185405581d00410150000704d00258041d0030709802c050380108604e4045e8000da4001e981c00408070046500440c00c0002208581112681ca544011a80e400d8440000c0041e016518002042c0d040c8039030520904165007591899a401d03503e0203050040300100e030711031800141c121030900e00024000d0500b21031140d016001000c200007284071100b952850a900072000f0f00400261401c40100c117000259000c10380c0c0c4425402d004118501c0c00f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 324260719 1250 324259469 324259471
    0xf03040f02100c1112010e0a0f0c050607031b0816150e1501030311031201080c01181406180907080405060703090b010b0c0f1009110316060513030f061e050708 70
    0x145c480c01d0141940c000080e002d40c41400340e824171808841280c90142080c10301d2070030852040c0c424080d80d01c40440d0701d007040000c8032102a0b06503516076909405007010095402c07821030031500d180c2c0030045244040019000e1003101801003844000c10783c003185043c0c1c1240c034181010119074024110320703207882c8041206681125050709049804052030002c09065105244c10060761200000010920181c00280d580c540039080e00d039499504000e81c0c000b4241c0145209040c0310034a008234034041d5040000280c1120ba4005c000204808910310000720402c50445d011400502150708000c20f010301040202e800880c02d090420030911aa1144598410140607581040000207036076185c2c1c40c0100440e150302c00f00300c0251149031596032005005031083c041c09413101c41070417260a442e4600483c4101460805840d22880245000419178090f0000480c1c4048081701d81800000318201c460008055441038800080011304021605402100750007002da80d5131400c0100300566030048441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 324261969 1250 324260719 324260753
    0x140610050f0a03020405030d03060303110f21040305010f090b150f0f0d051b03070f08100c020f0d08041a1006080c070203160608071e140f03040f02100c 67
    0x242e40c0311804201030703000e4461a03004035050b02c15030821882c66030741a8001c800b60383c400d40ea41e20070310302d5009440e0b03581c0481c0094883c10f500680c031080314000440c0401c00080c126071035441c5c106030703980e1110750854014007807074400c0d02c2d100d2210104000030b880d60542d01460852410125040314030202c2c002904404840b4001d1084207003810b00c80ea20090500078081d071040464100420010070184c12440b406203035402886041c60101c2d410750303038075007820036a00c802c0300034038030704d0041812000503203072507aa107100394003e080740414001400c0c031641c2d8252107291154003036030610b4580325150201e0500e03030440b00d001040c2480001140b80d070780e0b80c003183c090b458800f01a0315084d100c44280e108810000354588a43e0440740c5d5040c82c58503ca80480b542a16000e00036a03d40b20705444c2c081b0300c00401d03452100d454076010300250103910340590404004200b0b070700342502c0c1c0203451207581c4156000e4542140f106428011407070301243c40100c405d210700e080d10703085900380d41d0002d00820400070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 324263219 1250 324261969 324261997
    0x1141210150c030c06060902030a0e0106050103020901121a03060f01061b08090d1403070f0605060102072d1a091003230901020708040608040b090703020607030c03120f14061005 78
    0x2c20421720025800c1a4050528084d08560724100070700141c00800403008140c1c055400d1401c005281e60103417007528a8003a0607140c03406030700c082030020001040749101d55604842c241d00100107035201040054400e845021818026504101010f40702d0742c8c9964480e8454225000742e44001560383d010b0303034400142500c9400c00b414082c070b410031488944141d0b100745c501c00814100c06120310f881e0050946800341030304000300c1d22403000498407200c2340d0140303e4814688050310400b9038200b504080d89030007000e512480c219210114404030b03d03c4503601003c0648080340c008568034000603403040d00d12040c02d04201c42c1e10390f4120495040522002150f500c001c4000052003801c00390121403c540d0f0018002c0c1c1d589071643c50242040d403054509035554000320b8000750000707500107004000d0b2900207040758148000b81d54100ea000f00500422010818002c4403822410340c24040c0b160080e0303c1c00400304a6403020403404080e03c1c4d004000b248a140123a11800c103050300081103c41c103a1302008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 324264469 1250 324263219 324263237
    0xf0305091204381201120b040201111002030708090f1b0409030c02060d0203010315020a1b080903010c051b061902130e0403080f072c01141210150c03 66
    0x1400440300c0b1040e08112043d2541110541c8807000b0620082c685113200c0984a0301d5a40c031203840700400003039003500412224201002c074000d503010b0300e200d0082392a40011038507165208030250090b40c00a89514000ca00040d05216604409111155a003040e01004210288002d0041118120424111401035540300110300515203c2d11640248a8014014a40da600002910030080d0b0007444151442c000a40c07045080040500898201c400c540d0350f100c03030030000610b401c01c0c0440030000485094804024031140d17a1800c3c02003c0484200f038840fa40c80f401107010f810b60602011105000d2600a00c0810040c6028601c42c40000c21802c070005031217002c41d0681a2480038103801c50703240401c030f6030b0400c400c056001403d1440380440c0070300302250b51070768034003607038006001005a007650546505401000296044200c401c0505240591508400c0400c084a41c1e101c4040d42e200084400100710015000c0c0452400628030f1003084210148101001001041900d40c01010010904 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 324265719 1250 324264469 324264509
    0x604030f140315010305011203020a110402040314070e0c042303031c0209030c09010e1302041104080102090a1a300106020109051005071b14030a0f0305091204 70
    0x103000304041a9007000315540341003d040000c00011180c02490000b07007041c0c000305800c6140d2281d0a03215a0503002000d04482594800140b08040300f003442c0c11582c24040080071508241c0303190701400956014080d002d09055050301806130042038182d96a50030042081650200102c01944500105004079441d0b4182c6c00281981b140015142c21040450003500704082c15030b0041c082c8150440c12a500b100001d800d001d00c81400f40b0400c0c840e0741d80030300080c00320301c140403110322510700c01000001c0c01c1650b0844020b264211f60403405403a0340c042000c40080c180300a42c4400b40094185500f210040104244400e03c81d40f110300346d0202e04210401c0441200703281240149070860789450300366840c0e0000900074007030014182e0352032080500c08881420144070341801410b00748c0d5800300198400d2070340ca00200c0703e120b007200c4090b0443e643e0200c1d82028070180c000350255644480143ea046c440080c10340300050003409181e0050148080612648021070301100c45c41e14482c1002017102d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 324266969 1250 324265719 324265727
    0x50c0109050a120f09060905190b0307020a02040501050d0804050d050c0d0b0a0c17180c06070605040b070215240a030507091d0c2202041818050604030f 67
    0x400910720300c03580002a080041c2c50b032010b00b4500031540c41082c0c04d81005022980300c0e01c43c2c80b60b9004a00400e0003881503040c1500d2000c0585144500c0c1c2e007802d545c2d102c6540a5500482c1c0c4800182c204140420461a250041500410b0221940400c8080c0703034039511410700c41d40c0b051504c40d445081c1c0860800c402402007030f4485000400940c040c1c115400c01c45000ca1040729255009480d251100c90a140a681140320300c10b03501c074200c02c0c0c6030799411100c1070740b01e160450320065102d03601d154143e030742c0c54030024080a8810100410203041a1411442200c006488402550400d21540da00103107150551a8440f400103e004d5400c0388040a4118a800308071342d243d04004940c01c007205105001460408680482c04100000d102010000e1540040804c0e0700d40c041d00600c888042c545004504e0007542700000700040244120200c1d40c001f00e0b403083d4400d042c0280c50391000c0d1481d0304070744244a14038030380c0104100310100301d42d07540d620b85c0d00081004081c0700220172021461441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 324268219 1250 324266969 324266981
    0x28231009030b0f06010f020a030f11070905090d020d08090d05030c0f1204151a040e03130305010605090c0a080f0c042c06010207030206040e280c03060609050a06050c01 74
    0x110140d00d140c01c0620086680f0101100d0f030502180d0400c0151254500c0084c1c1e18003a40d4256403a42450200c83c001124180c000e145118071502c9050380101b0503824510646000e9041d2000401c000803120038040d04007600102d804c024030400b1810822a0000440c200c1d0b003a000f18900142d0320b540ea0b001444260140007a011503030b00d808514029402080d102c91401580503143e00d1006451140b0f905058800701c16450741c1c46409405098203506042d000081115940d50076a4148180344080bd03030003d0180c0d200f65001d07912001c0c2004141070241b1419000140f46002c5413070040011006441d4600250400e500e2903800c1002a00c440250820345001e4118200480703080513200405c40c2c68401c200c851042c180001d074000c252903600000b158021298003410081c00c10f85484080c5481c01802408002800c041c40c4008c00400c40c9100412810103105100044140581600404444140c1c00035814044072002c10300131a55115581e50841c3d82da4504184c0e2021106401c1c0d000d010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 324269469 1250 324268219 324268223
    0x50a0f0203011e080c01020d0804052e0c02060c0910030b150715091101120e06070c0b060406051c1e080403150b100f05092823100903 59
    0x44040000720f94607100f112595100c800b05448075100503161003c1644600013600c0283c0036903c0803451842141c001e6180304da0060080c81500c1e08254070789411078040b940300400d004003030702d26008800d101702144200f0b00060203510047c034aa18040c5001052441894152446a02d0600301852080d110f0b4100f060003020281200300151264002c40520303800c28841242c6402e544950381200302624030502c81c2d410303007011180164000440054851482c0f40c0702c68000141c44523020051020108201c0b0b0150005503a101041c003e941014010044040c101900c503509104c0c04101544c0e41601f10140240005015601d04886241018210449405200c2c00201070704488013400702840c040c0c41200d018446080354420001c1c000c4045480d20070096900c9660050040901c2d84a0703c02808008142d003484e0f403511240c240091100100706801040f8407015481b207c810200d020020801001915a204012008861504604400c07030403000e01410340d405051840038452400300004603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 324270719 1250 324269469 324269471
    0xc02041b080108010b0111030304110d0f08030708090c0906040f0f06090b0a0501050304030504120f0b09010b190b0403080a0e280b03040f0b15040f060305070803030405060703050a0f 80
    0x180e8103220140032410244150003107540b0b890780d59403607035002d4815080b00038000c002031850b50f6640c0ea210b1f0080e001c2881e00540111b4000400400a09401802d0b02c0041c090201d45840c2d01e00404014203030580100390851641103444038443c44d0f1111204550001d04c201e50106404514485600c0242030220011402508081c00007c66801681c4000c800740e0068440b0354001d0740b200c005407111b00c0155801400035104210812100385003402001304640f040030130301e41e030b00010385078003114081c2920300050350303555000c8a101614011035001c40c2c4030513804c0c10124003450500000142e029902c80a03100307150008140c189a44601451440010f0040880703800140003c0c8031700542d0b001010500034010040c0010a000040c103083d00d10881e84880d180401d039003540d94001241d13002410802502001b2200c0802e169200d0103400f600c2000100700084a0348ae50420b68038118044e440042e0b150070810520000c140301040c002d501c14040c1c2808200703920391000c018014049006001e0b041c1e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 324271969 1250 324270719 324270761
    0x81f06061205090c0a0e090609030f04140d08030106030509101a010e03010b09040f03030b0604030f03030b0414131109070503070c03091208030118060f060e010e040f050609070c02010905010c0204 86
    0x2884171b00030441c000c244160481d0b0040e60313070021080e0383c2d00c1928503113440d040007408100a10320740d035041c1028901018000406520040d175416502d41c0007a000040400d4580f410048546402c200d90300503103195000610100200b000540c17112501056454100401030000d468507803130075007101400072005058010341c0d00e01800c1c01007030064048001c600084c01c26502c26500d15003101514250781c1c0114440342c050095a030b09500070103208603419001a228450114400c2c841492140301d00d4420310060100c030010314050341d018041440051082c52880305200a15074858103481e030050b040c1c104a280446642029900c5245a510103c00d03540043c9681081092410165040700d5200401c0c034080003207064410180c136114000c1d1030114405e82800c000451080550030400001030506031928000c01010409071100b8188149409880b9428000d0321305004d18042d40c0400d00f46480c01d00146103900090403030086100f89410440c0344240041590713500c0d0b10446070104491103090760 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 324273219 1250 324271969 324271979
    0x50f130e15010f031407030921050a140f030a02130b0f0a030b0111061b070204140114010512040f11030a051501080f061807030507081f06061205090c0a 67
    0x41001500e019001035420410056490300a02030521120b01440111754070703540e0010214014010b4417000d82c0e40c4c141045c01807030005241d07440000060025600e0fa959251150406800e5041a90116494040400510004c00705c035030180d039040b07a06244096a00c0505044e0f014090f40c094005600e40c2c02d001450300400d400340740c018190ba5115440504c04003614800540b200440c03141103c801c0e40003000001d0312400050414060076181c5024507041c0641c0f03401003001c56050318080d489650140700148195820450703484441c0302c0c00d01e0f240313150030600d03200c1c516400383c003500003003003101301c2007a0a040101d111400781d00500c001d012582c81c20001d00309140c2d600141102c08002000910000ca0f0720400840c460140fa40b640300203194070780342c049024501c80d4400c0042003184c043e0f0030020001034014001c0d18001c2655600031f080c1d40d52030103030a42206100b140320703100c000c0c9400c900304089030304000301910031400f6520004090b510b01c011103080c5110320a111768403440380d07400411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 324274469 1250 324273219 324273241
    0x80c21150f06010c02030a022b061a040e0703060b060d0f0b090a151712030f011a120609100f06030f0f020c0a0b1003080d02030712090201050f130e 65
    0x8403445880d5030300da9090b101c0c41e00540b135400510380040c3d015000390000340e02605008600203001100e80f0744030601c07210000416010b400050303074120b07480c030749460b40c0b00003800d6004020704800d201120104181d01c00c142e035440da940303010700c0028805070b214401144143d0390607043c0c0340006030100040c00400ca40d034034140f000303141c50b04d0101c2c820390b600700104241c00c0a0b4810001c0094806208603015414829900c032840981e0300817891511503940141c41000d00e980c05540580a90281f1035010350400400c1300c60001000036112407514180b0500030122250f41481d40c0100d400eaa8010964813107444485040e02580c10070071040f290542d0000e005540740e07002c1701109190090410000400e010180140d20070a0715007d00c99100950900c046200ca1a240d900300000c503511006290b50381d95049095045000702c049815030110401c94100d4201080e00551603440c1c404119071316582d40007030018080c07030180125440010070340c200070220200d0780d07030040c02200102c119a4940303212120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 324275719 1250 324274469 324274471
    0xd090503010c230f04120b060102150603060a0518150a060b0301080a060c110a060527060c0315040911010311130b0d090f111504080c2115 61
    0x3402036180800c615029403140e00401c58416a6441c54985500741c8498208540c21442a04201000c208400140510180810f042003845144802c516103404000613041c02da0720104d80c104407400b042000102d6501046017503210901400c000b840e900c84190720004c540c041c0041181c24441c0300140c40c0c041d200c40142511500545109202d5103450780c007118407a02080c412080a98020111040011001d40010f2500307800c0d49803a000200300d10315024541500c51200303858041d41d0b035089c01402c85d104460a440701e0302440c0c00c03540c0e4041d021141a0340310001000c4c5020410040041400c2041c0340056200703060000b0003d100c0c0e200b080c18410342c4500c0c00c050039400709103400300204810340e981041d5000c0e1402c0001030342000b0303d40212442c0c290b0007006007082c001e554080c61000124203411205002c1d009102c02c40401d0040400e010043c507a03c1c451a51404041c0020004d21400054400211009403040d90405c2403080304501c2c044c0c1420b00c91140e90087c1411016a410007144c82 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 324276969 1250 324275719 324275729
    0x1b0613050706031503062d0608120f16050c040606080a0614010807120b0a09020d0b120c0609030a05010e0a110f060702040e15130501050603150f04140d09 68
    0x2071101142e0300c502c1070f000ca0b071401c45000c070100a414000c00c0803038a50b40c060b80d520a0010301103c0940c09002c1002003690403507444008860b0341c1e11052003200002c1280441d02e0a452201e04d241080d135601006082c01400203068910000d800c08500301301040c488640000750150081c4a4a03456080241c45103204507007610b503040c60000300281100e03186d014000c104006850b20f802e1912490401c540120788001da01143e2511800b040e01c403501c40c110020002c00745024016103680c125018002641da80c0070365a80305e00c100d442120010745006c03900740114502151a245c0c1c0380e12000200e4200095420701614039460031502e07034501c100c0400d9800d6190303c41c000015500d00c5c0801002105064140c00075044181403147c4401810302d540201e40c5101c440f412545008900c1041403003014048500614910240c0702032400c1100c00d000c1e06400c801c088003d0036081c2d01c0c01e0340300508041c0062664a154030b4403400f140a2008004003641c09080d804140c41054030420806001c40003203100f5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 324278219 1250 324276969 324276973
    0x9030c021c08190e0a03031710050a03080c0c040509100b0411030106080702060915060108070c0c0306020417010905150606130803031b09090c0901020f060423061303051b061305 78
    0x181390034902c0c1c414103120a40c1e504d5214038a0a050716022480141002403054844524203480450701d5613894a1142c01944546481640c41c880c4d9066035003040542090140503e08000902401c02c5020035544083e1016806c0043da034000300d000500541550b840d8607510301e900000110303845a025915034400d2942da021140b00362107020400b66525126681851000a06000328207903610400440f500400e26103070059014040d0f844110b05000164800c65081744d000500f00b042113901c16a0115001000000b001031625680342d0700d4648240110908050940400141540e40e0342c03003c8e0782000050411600e08143ca03010385907941c1d07109544a0045a00c5010380070034220ba910200c548824001c0c1c0045019140c540b148489604803030305c03150540c01011100600210208500351241c2c0c003d2810464201740300c072003030b9643e0309851540b5000e600100c0410100041040d07001c00240d50625005a0f140550b8144400803800c1e0a80741c01140201d0082c0318481d90484003000700d00e13000e401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 324279469 1250 324278219 324278237
    0x90604030f021b010e0d0204020a18080723010c12090302040b040506010f081819020a06030203041a0406110307050309060f061309050309060a0f0201050a09030c021c0819 75
    0x1c0c0980e590300e66000c600100c840c15481c9001154810140c40e03036882d1002c0c0c203280f01301e2003650014007a41c10004d001c00010f45144640c0014039202e10300d10000741400030103010901d00307040c2b20440c0c0700c800c00c4481c074015010140f03c1d20240d20031400b144079550040b40c02e10308801c074400020000c4c0290b00c02644100d003042c001107420302d441d1040d00d000d084140c42d22003800c4055402a40c0d0b84c100200340c4880d6080e900c1000b001181c0500c03000301510700c01c01d280d951315100c0f0310405c0b440e5043c81d000142014818420040080d42011010441c414060540c004507512890884003415003065425120743c404400d1061480c0c01002944c002e090200a0b6100781c0d40d98528400410404c9980300c0e4003200040207000381011a5112900300d40c003410a4902d41030102011582c81e502502c28074000641400741082481c0d820300c1100c0d00114950002d000550007a14002c0c44203501c840068400c010440300f42d40072580000800e000a9440b84420b5202d02c1102c0040301c81000311050400814501030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 324280575 1106 324279469 324279497
    0x2060a110910031d011e0903051c0221150d0816060608060f011707080a030e010e0405040809190e04080c1203090a15020c0d030c0903060509060403 65
    0x1b2461004240f120840c161450f401203210514010000000039032000c100c0c0c052250b0080800c804025081900000348540384940401e10f40e41c1200c6041d62401c000d100388108803103106211214002000e0020807642140d00502500042000c40161031b4a24880b0b60b20600078007001038840d8507205040d2800d00146e90700340700b0300c2c0f4031401005811240002c00c6803c0b84244050300c0c0340d601c0c100d4a503584825004008007400030300103508107680d200d0b403120340144200610a0040f0700301400c100c2196403212101c14003174580818000600d001d1003110200b107801c1015071021596a5440b0b4079843d0300100c01c00703902030040100412081030301c11701641c011000000a80040c6015107400901d0300e2150400e0280f0718010301101c1200d4202240084003145c0c141804504e6441900046460070525000100840d2900023400841c11b000901544a141b1907168601528101 = true := by decide +kernel

theorem cover : BRFrame.Cov 324100719 324280575 := by
  have h0 := BRFrame.cov_init 324100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 324100719 ≤ n) (h2 : n < 324280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
