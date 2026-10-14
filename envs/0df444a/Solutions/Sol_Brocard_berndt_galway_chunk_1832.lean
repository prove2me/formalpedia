-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1832
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:50:14.667781+00:00
-- url     : https://prove2.me/submissions/a92ca721-0b05-4658-a1a7-b19bbb80cb2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 329316546 ≤ n < 329496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 329317796 1250 329316546 329316557
    0x30a06060503070918021c020c1603082502040516120e06130512120406050105060304020603071d04060b03010f06090f03351804020c0c0105160b070c03 67
    0x48400c0121460b0005458410218045020600549840201c090051340613001d0050a081121804001c019609a00c43e1241d81c0c0c0026151841d40080c0b000d00b0325401d0000c980e000d2103113944c6d200681d521404080d28031900c0c00340c0030741c3c03140030702c910700540e502da00108184950704098910102031404400d407a00425014143c031082c02c1040e0080340040346a04010700b10030365840c1c2000b00401c00506040700c4034014004840100718440f006071082c50341e242c1c081d50040c40c0074035205084171010f03040240304400c02e20403c00107170b54417001c80398044150315001c1c81c0c00c0340b03824507070707031403068218965503c9030820b2030215200101c040610304076071010000c200c105036681c4050742c00f41d000d805503041d81c2000180c240f0104e00c04050301c0c10344a040d000070608603c46003c4a42da00704060000104055000483d1031010500e14405050a0012a8114a08009440040c0c0d80d4000c0607052410f1102c0414082410b0742c5130030240103a40e0304441c80c16054a05240c000f0149040c035241140400d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 329319046 1250 329317796 329317799
    0xb0708030610080c0403110d0c030c081002070b01090b040603020913110604030209010303200d0e1215060f1f08040519020307060302030c0d06031112060c1605190503030a06 76
    0x144141007035405030541c1d0380e6031342c9020b055441d6000c034000c8040d004d94000c802070703000e14005045c05005000640c0506d540003580c41c148582c0c41d0600c007005202280d0140140f0070740707011940450142d1b0450303a120b000010901d200b0b40c0070601401d496440a90300104820801490140c0c064418046070711075044000250034000c2008451300a034003012b500040114014000240550920f4880005408502500d0004030743e805180c111000c41041c009407107a0002c070485d09081070303006038501010000d07107808000d142005241d524024081c07031050030f0714a0b00751401e07100e0700c1c00d06200c12044071031168a1600c481020700710710307030a45040710b151007105080c1e101d2142c1c00746005410f65008001d84807081c90301c20110060342016000340a64482048400000000340c4504070046101e403225400400c0c1020400c0781031210380c0c0c0c1031540ca0300a20204031400010700c0840c1c090b409030618028400d1007d051040c50060400380c4200003030613009068050140020180d0704c144210b000520216 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 329320296 1250 329319046 329319079
    0x3010f05150306060906070501050403020705010917100507030209090f040b060306100302010c0c0e1305070f05030c04022b0e2a0108040201140a0503090c03030724060b07080306 78
    0x4032018a141c2044600a00105041c0d1038038100601c20544000c0140382460901e8582c14215401520101c003d40d1140404108a50f0041c1c212401040442a0008e40b0021510301540b100400c001e000852651000002d242502a5040d0380b0610400b80452030b1038a040304500358410420b450584050302208002102458000340c814480c0c443c000a401c1e22600d103034011744480702d50340c80803a40c00d110107101145d0980e20317500c45440b9150007490000445101d040071401d020654108110350056440280030340d80b000240c250b407a82007500c1c01a44d1b00c603640c1c560a82200100e01081000d15182d9208660038034580101c0b003814007250941d51101182c4c42000e14184100c1d80c1003420343c200102100781c80d03000c3c000305540203006040100060408401584941c0d001046007001301b82c000c01880f0303001500304440442241c0540095240003000d0704c902e40f0540074400b00c0c080c44039401c0900e008110541d08610000c14500d140d454944440d450051059001120004d02a030500740440592 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 329321546 1250 329320296 329320309
    0x105040b130f120c0e060a0e16030e0102182101050907031a04020a06030f0e01020f12131a07030b04230a06240903170a110c0a090e19030503010f05 65
    0x155611040c013801d014540740c0b00368002800202050391121440c640040c010023104c008038030440707010040c98900a000b94014044480d43c051200e0913070f03c184840c0084510101a0b0541c4600445920100d00b945c4e6110201c01202010384965035400d0605020030000001004003c2e00d200d455803a400008540b0300151840040310040d510400158040000600039405111071052644012560007485a40035099a0000001c1c0c400d0041c0080d10344052401c14004a400211a015006000c081500d407891190b10078002403504034108000729100e240254404c8009800142090001a920240d075100b040840c2e100b04601880400004150482d544580c40513500441403070300d0202c00304a45c80901e0032042440342c0070b01104910210218941c44011141403146032811aa561a1034600414011100c01215201d512000307440040d40d80e201c0d1a1700503100f4844c0c0025410100100c4103190603c4070840d14854501024101c0030b1540c0b060046041e5011050701010701e59680052021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 329322796 1250 329321546 329321579
    0xb0a1a06090f0a0303020303010611070807030b07020f0a08040501030f0b011d0307120c0302030111041203082706040302060718030206130b0d0f05060d020306150105040b130f 77
    0x2056008840000424946240a0003156a01a1000751421064004648044142d0b001a00503a00100c01040307802c1d48003090040c03100031324014290703141c580405103036581001d000c02041040c0440c0002d01151081100c1010020b00c8021154203a856051031020350b4083e004ea24002400e1a400c048c50084034000d9010701ca8042c0c0d00c1c1000702540108408807075004078565030781402514000115104c14036590035046005922501d8200d185104050844012007000c003010807042c0070410285181d100202d680c3c5130103080420141d17540c00964803c505031029490340c00000c29440c1411103800144261080d4844d80032208113440d6150191441000c1d0718aa05284103101c00c24001402c042d030103000e0b9040055a000b00d820340359040d00807960002da0300303005802e07501c106442404001d801040e030000c1003034503424840072303164011907101c21006100c0e0704420a11200c440099124204a5000f0b202c403a50160b113070b0f21480418035403c0ba85202d0030000c602903140109008850102010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 329324046 1250 329322796 329322821
    0x4020d20070b0c121306290f0405010b0a0c080405100309060b010905101d0306160905010c0807020d050703020405150a0503030c0312100515090414150625030305040b0a 74
    0x10f1343d14161142c070030017840c00c012600c054a41040c0c040902c1c00d032801c8000f246a40800d061022255400c4c4000c551403183d44034819803e140040088404481c120340b00c0740a203140c0714544070440c0c18405102d118a9002d07070b402001d0404d9405441c1e0f8180d2081110603c240070a0181700390f4034004451181140c011290f101c0c880c20503440703040d405000614a00d0f00f002c5d400c250741c5004c041c0028100320040b43c860320380c4414100800801a40100e1000c0948000d0034020b801d4656501e03048424000c14100900070074008856805000081200303800540c0d004105010074501224440a0350324681c2506009858450303011865103008401e540c0c9180303c2400850400c80815100f134a182c50140907038808500c40c040104090311420301081d005024503c1c0c0582c0d42458606000450f000407910300312039010138081c0404894050000c00408908881c1c083d181c0d4210720749a800d074407104c803038800051220741d0003504040d0950491442180030300051562580c0b4030040f181518151840c05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 329325296 1250 329324046 329324077
    0x140d0504150b01272c01060f020a030f12060b090307080a11100908070e0106092c0705091f1e0c170417071701020c0c04020d20070b0c 59
    0x4580003c1202d001d0380d0b04c1420007500c250155540c80d1195503d10100d00b004000e103c01110942c814841c54403c00e0040406250036030080d00038000003500c8404142009007003107200806201c402d48902e55540032030a2482040080c40ea98580c00c01c8a644640c10f045d02038001c103000020207910119a40320119002607a14014110500410000c80f8040d6030440902000c000c0118030101c04101d00d0010b4412050018250750601c1c0d4042c00e00412076000c10b00c2805241258944032603e40510410340d40c401e080b071005c83c0c4400000b41e415000da001441d4002e00c5640c449040c111440500300503101030741e1200e12804880c190518401b0407003c0c80c090114501a08600010700585008541d11030500c5500d814103442d0142400e03400d000b5031084049600164041c0030b4840c0d000070942040f42150300031450000f110810980710740d00311084a110b16408260841016100e42103001c003450f121003510031b0b112050400d01c4950b00445000e40340e1072421000640691001d6084540c00700d1121081d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 329326546 1250 329325296 329325317
    0x6060c0506040602030a1104090506040b0f0d0201030e1f060e01120c0e0405190803040516120b0903160c0608150a090e15010f0815041205030403140d0504150b01 71
    0x1d40020f540054101c09021380d481002c247c0340880e801c081c0000c1c21030400c0100b41d0b42014010801070f20304c03100070544107040c5407406002d90342d55840c001000035420300300402d000c0704400c13020342850001100c080740341310041e070000340340f800691041c01901d050030b200d91a00c0c1d88404c401e8a049040c00d8000700800000041030190b00c400356030003036000d88101d080b1aa440c000320860061040d945000311004040803040c4410031005020350a40c1c4019004000000e601d0401e9641e6440c02501026200f83e6041740441d0b4002d00601c11190a0110082c06a9219942e4682941d1003c00785c070403080022400c10100c0c40050800c0e203403180c1c950703004080404031418100d030103000f0145007001c11070794031540c98499072a50f0341c2c42555008108800041d902e075480d1188041c1011844200300340241d540508000c0000c1020703560500101040c9001c40c0c03291751300e140030b486025101000c0c0c5000b41020075522503020940d00200c6c4598854000b0b4001c605240900f68140d45c1d45c608210f0101318a03c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 329327796 1250 329326546 329326553
    0x80f030301120c0b040e01031505040203030901030f0626070602010603111309230d17041713091a0102010903170c130f030506130309060e01030f02030906010906060c050604 76
    0x1070b41c401c1c10740610320203030020303560b0101c02d445540300ba4080840001c0c000010414440300100c10f580c40f0030500024000384c5050384c0007036101d20a1060302414169503031641c0c84d183d513030355000c034000e44090210030140c000300c2080301c0d000c0c0d0701074100180741348a609404150700f0300c103000360401c890740881c104401e0401741d4104503581005005071005150380b42005c0d4003003008240303442d140304400801a81115400c102040c10300028004100c140075210315880051031a5454041d4000d170403000342544003c3c500003407412403280b8010000000c600b204003003920940c80d40074404001d141560000c08000c0c1070010b80c203032000309901801144a62070302079900084c1c56030aa034401d140744005454600c0941805481b0103281d0030098071451448810300070400100714440d08183d0001103400040301d43c1d5802020040c040c044d070010004080000c11259000c1d401411a10035112815500c0c0d1401741d680940d035440074861492250b080a00001e051030040310101003031794109016002c60317519500c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 329329046 1250 329327796 329327819
    0x10050102120a0c15020318010609110f070201030617030d05070e0603070807110d050304060c050322060f09050109020a0f08070608090709060b18030c0607020d0f050105090a0309080f030301 83
    0x810b48900300c8142c51804544c3c4140300561240b441c907015070341c901e02d4088106086480d5504008000c1c4d182c02000c4901440d20001d88880880c0c0314106135541c901c501c01240500701c41e91200302507024003401c26038002c3c00803000d8400c0700000031003000150b580940440d41404081c0300103421482c2003011400d01c3d803007071292940c040690708046085106c00e1032118034003203a02003808c0c00154080240010405a0b02a54641103940e181860841c108000d81d50070075245083e02ca845603e6101c0d880c02000f449410030340210351081020841c60b021400e00c0d0b4041e01e070400c0224811040340201042c3c8081c0400c1d0300007034601c0380e4000d00185003460010355040c4000390000c401032082c2c10000505509901982010f010841080342c2c50712904011510b4034480401b196200380c011304c401c160640c0300c440c19541815011111413000300c015082c210190059514090110350901e0100444040009402010a807017580c40c081c17803a542c0c04525445504203800800d03076800400c010403d012000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 329330296 1250 329329046 329329067
    0x1050f0901140c010c02070e37020415081f170a02060a0f140412020402070f020405011401140306030607140f03010806040c1d0403121508010510050102120a 69
    0x181000580d0b41c40d900d03200340395a0040a25040d440c0e45410340c80c103219034140729100c002e1090fa90380070b0b01424400880244465550b000d11440595014200c03803007024400d0740480c41e201c81004565603a207608400c50b80481d0418240c02080c1c1074004114540d21424088605007010629110120309003903410800492a210501241c0b140b00c8100015944a00c0100303248611a00d90044080081c113025105408041c40481181000c3c001082003071034080d00f000540e58101c84c01a0746040d83d2400304203900003407001070340003850600045004048500c0c005d00a01c1d00b40c82d005450507003210038107081d02c070840705541c1640040c1c0c003081e1100d000380d00108040140304089428030340401c0f51b80d04540c1003684090081e5202100344810b01c4102031402002e070815148840001140040c3d042003610060300c0201080446003502c4e85500c89035004800f030f4501407420030500e940d10381c6894081e21091b40c5503c4a1110124005050b60001680a00e04104103200c00d0502214040903902413494 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 329331546 1250 329330296 329330299
    0x1170406020d020c1504020f0901080607030b2128110d02010c0506070306030b0601140a1404170c0f0613090902010c020907020a0501050c0307050403110604030b010b0d0e06010501050f09 82
    0x1e014540c0200341c1800aa101030040c5c0241da02240350a00401003010040080d980c060b603100e500500c100700c4040307a102c3c0c1c010840c1c10007262000c0008041a000300c50078845219041c0c04500c6418a5440810400880e28010081d4040c048140e0210410040341c503200900c0144402d01d030a6081c10505203106c0b1090050414213810142d9881d21418424111194000255100014410001203a400a401c40d000f0318181c1140506d8030200e80036031007184200c4081c861b80480340044c0c24403000454010340300d03a494010f002100644540d0707907020703014500c1d4441c5800d40d00c42c1a103814081d00340ca2540010910042c0210704c0d00c2d210034000d155510b0f080e4100800c1d51010310250304d4180c04a80114450340c01480b4521080c04c0990031640c026040c101b0000082040c40740095100342039905807900025540150f405600014240d0b11895100030110340090300002001f00c0000301900c2c00ca214031606001c0341194402d40390305c0b154240102ca001c0382e0140284001e1280d44030291030710010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 329332796 1250 329331546 329331551
    0x1515080d11010609061203110c1e0a151d150304031d04020403080405090f01030201210930020606011706120708030a121509020f04120f0308010501170406020d 70
    0xc64007852000d80d40381746c0108a980042d40f80d42c404040d4410502c552070b00088015150b69034200000880240740e2180e98140300c0c007603440d50b04c45903580b4600c503c01455400c4c00d000c1c2241c030703019000c0c08540080c561049042c0411038030b1405800c110800c01f03401d42c5c5400f40300c0d280d42da49030350a803220060120f0b078030165084070041901d10348a610040c00554007441c00251182e1819042100c20343d802085100002014401000182d0f007003840038a084103403e031030605104d00001018020b000341c180c050011004400c0d00c0c200910074241d4850003501034610298070744010740c410780c4c2d2241c0960306180001c60348101d04040c0099814043d4010600401400c60f544140301030600d444000e030030071201390b0000640b0100803500a2003049410240e544180a0444410400b00b42840c0314400d40c0d6003160002240a80200340604560203070400744004408061542000103030b40000d80000c80124a07050f0001c140796028650341c80031541404a0804c01d5a900d40d41d00c070194021602c40e50030941c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 329334046 1250 329332796 329332799
    0x10c11031e070503070b04021c0f02091807030c050f06072006120a0609050109110d090327090f050f060f06040918051002160813050603041515080d110106 68
    0x183c06000070010309005400318078032410103004000000e82101d100481414007641d0080007d030092001601103078041b12a1002541c5d00f0549842c2c1d1550702c80b84058a015026000c001c0000c00c241c01c07029101d007541c00381580d54554052008512540801500421042c20302000c0450040121002c041d401723412141064564505090480c07429902411b03003035160761003804124050701c201401000c88110510000b103092803060030901c140c00107480c000f51101303040d070145402a200340044a0303000220280405e401c0242c82c02030206405000700441c208014408070800ea802558061442096804030039103500c4100501051883d820700d070401c1003031100040c030148600c200e000032418aa40003202404914246090107036501c0400303100ca02c14040d13810021b107500f040301c0c0c2c2c1d00e60000c080c582e511880c0c1100c48510059a0049900c414004108000c0040c0c00c881400ca14040340428000901410304181200e40c903401210420783c040e00750190024824440c0c80e050781c02c24400014550b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 329335296 1250 329334046 329334053
    0xe060316050409020703050c010506032a18040b0a05060a030c18060803040609030615030305160807081b06130b1315050a231e071e020f010c11031e07 66
    0x2030301700103810742c0402c5010554160000081c003032194810340c110050704680003c0c22581c5640c1220080041005100c15084242c0344c4800185851143c1c00c050f0302680c600d458640740441030760440700b07902c07000d003020085901420011000340c25681e0100a03050b50300d0410b4551140c1d0461a0290b1090030345440001900360814002007020344929695a4845030450514506480365030342c8011801840440c100b0101303501c4415039a010081883d140441c1d41107040c031440c140a61390024280340b00016040c5071011011114500000c1440700780e642ca41d4a490f0740007400100c41d2800380c101520000043c0c002d851003803074103003201d03c035a54454059034140f030554112101107d2181859548e003403450481c20b407403d450442d007514418002c25516003e0240740c107a1420f002c0b0100326034040b4002c114001e02440b188402d2000c60b45030074a1100c01082e0007503560f20038101171601d41d40380240d8518114841c45801c0346164418000307510b480610400380850058280220031005014010700c4000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 329336546 1250 329335296 329335301
    0x60c020d0c0602010b0f1e100903060e07030c090e100b0a030b040503041a0406020714040e010507230c150703090b070314061c0b0a0605061b0d0e060316050409 70
    0x6844603500025605c00000d05015003000310071103c0d8030851100c0300400c0e10400c03000c040e800068044d50000c40c07001e8142e0303050704c8e00c6100344c03c0100690304001c80e201546c0c1c0c00007483c0c4100ca00404054884541d16144402141c2a071031121046812440940d002212260001d021800c0c2c0580841c42c4182c1e00e44031410f0301e25050724211550f0f000014104401034800820a107042d1801600924051501a0180d520050352244100301e200116000429545030740c4034000c00d108010091000b40303850b0328010060002008459010b41c02080c0459600040c8820b41c0d1082c94000010410103400303107041040850010070041c1003646032012071002410000c8034900444c00313500c0c0410655440704241d207150400804050040b41150b040c40d040d04601d001c40e2604540040a01006444150030600174010681111703030460340011b25220440403142d4440e0b088201d4000742c03a4480c10505084900c145c040d2095a4002d4081c000b00b80e01c0c603400140e00401407a2400c281d0f1600d9601d1024006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 329337796 1250 329336546 329336549
    0x1c050412050105180303130f17040b0a020f0309010917070503010c02030a08090a0c090f11030702030715020708041802041a0301060206090a15020a02030706060f0501020d0c0c060c020d0c 82
    0x60780d0b5110824020943d03e5051042d0030480700d8070141d401e525000100311018250b00c1c50240c44800201000d009011440b40382000d1044158900ca80d02c03500d403d40f1500c5503103d0080500140f00e56481e05040c06004000d5542d9804140e5841404a280106240d0f0203460019030050502829800180c030343e40910500540c00107a4020750340300c094041020385801e200400c0c0001b1a00301c13500c0c0e1000210810090000d1700c86d110000108100c0300c0d2044001019001d0050b10b805c03800206000d80142c002002e807951074842c60442001c081c140c03952000381d0042c902c0c0100b00a07001e200c00e001d4501d007103605c00b0362070010744070050130160b540d00358a210769a80240c200303207000004014081c0ea5410b10019502c11101d40c01489401055900d10300c4e02d0148150f144280e070f81c0481c441d85030500c20b004540c0420340001d4180002d980707941402c42c038056207115560240c45260140d41d480740c00340007510740d0141c21070000b810310b0b468090306841d1111228412a4000510603a5200050210403141c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 329339046 1250 329337796 329337803
    0x110406030b0105130504080d050c0d060f090e010209031020030a020d0b010c0f08130503120a021501060c06050a0b0904050a0308070315090c17150415081c050412 71
    0x6003030352400052003140d548043c10140713101c0c148020840480c0b580350446401100942d00040d007079990f46490003c601800d07500c00d0045083c10b50001d101603080c1092019501091000c10040880090241c201e2003980c490903019006840d02060019150f440030040c1342e50400e40f0500c03412402500425a80b0440c0c10148050780030854030301d6072002d0f00c50008544401c1c20401c40540090b156104a0100361400034105200020300b00a40300d511b2110780c008001c00b81c02c0350480d0002d4800c40d00f0075080f00500c00300510403414190840809020494104c9003c1e0320340490307100c0d05d074494102901e00140420007040e21000007100399120041014030590103900606449080c1f4a0020803030000681a0350815013807417030208002c1c012100c14011207160a600103100f4901500542d81101780c43d41c4040090324280c20001e0301d1914142c44012014111030801203044940d450103c3d030541401072100941c40511040c03181054400300d40705440355418042c0c01c00b6594280c55115000d400001c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 329340296 1250 329339046 329339063
    0xc0f1d12120a020c01050301050d14011107060b030606030703030c030f23091008073905150f01030c0e091606030b040f182010031d07080601050d11040603 68
    0x2850143d070500400f90a42024a00036180d0b5160500144c0035012510019041d980d05440c8104412001d602c10a0707000f07403460480752907c0c11401c18000070242545291b01038011031002442501d00070a507201600d070306840c0d4a4038803045440840b5883c0328012120184080e4480d1010003003440d00901240f0030303074400600d5550590130300744805d410010b60780c0d405100714241417182440e0007030000290100741d0300d0700c0701c40c0c802d066541c2440940054220340042a101c511310307003402000319454880c01486030341c562490300c0e2040207000f424024800078118401b60308003400304080703100506400900780d0080720201c90508100d5034400380a640020082380da200a403d02d1070605004140d904001501c0c10800c426403038070701c0218503481000c01001100844054500135416100130b0142c0903010700b051191381c080c1c41c00900103120424460080c02c0743c10301c030b4800202000502c0404d0f0344c401e0010300143e07442c040500c201400380c594116000e04080303296031140d440d03078841d280c010340c005c07083c0703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 329341546 1250 329340296 329340307
    0x1018060e161101061802071e0c0e0f07140703020c0a06050d1d03070206030705160807031103030402030a1106160b0601091d0112030309051009060c0f1d1212 69
    0x19110b104068000440c81c0d0410b03900300500e010011403400311194044025a46031304c6890303e01c3c40c55050107080c42140280c0300c4103c00b40441d02d0107550907144091055403803611000e120788541081111a41c00080300b410310002c0c480004030207005040d110380110760b001d001c4540007504e25072141d0800740006102281c074200c24500341c091900304810b41c801c40104021107031034558172072142203406170207150300002141d0283e00ca1022607034610080d075039441040d6414942042541d00019003500011110102914240408011030b402a60700500401000c0015a142a40141403070040c41e8030090a0000f02020b6100080059250b8410450f60300f0900d0200005450810300380c000c0d800281c01030300551800a134100450341942c07813004400503000064502203010b010b2400d4001c05c10702441d02c114940d10520707000030200302d100302014000864078a00c11600c01d007900d404500040c0f004210120608401f21001d040aa4044d0500702030490598059241c070b020110110b401c1c420001c0c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 329342796 1250 329341546 329341591
    0x7030305091516051603020102060a021b10061505030c0d09080405030d0503011e0501020303040b1b18010e0103021801030b18070206010303020c040903120e0f2508061018060e 77
    0x5c00e042541c240d000f545070050540d00000d549200052500d44440d9001840c01216000c40500006510303030b42c0c080b2000b590034110500040c00082c0f0451843d4a07005004c12202c600490a4030700c580519400141414080c0034081c014000c004000d45034050200b002084645050122041c0c0702d400d501d0705980c952419141d00d0341d540a17551038002e00c1003074a405004584e070210840e0b0308640c00c50108a0548c8030900f12441240014800700d0022800040798800c8001c1c18600710900301c0700b45c9078101c241e141c050040d002da1043c4d5801400c01c14500c01c24000540c0240e0000c2100b04000d0031034002408038011800c0c05031001e0b608440960702103030040040650410076010001800e686c1484503001070b660107841c0c84164051402005d0f125140000751010030482244038903035402c215450002d481c24001503054083c0e52005c440c400f40300d03012525200008441c1d0003804901c280350142450301018042c0080d22032a03003407966840d03078400185109140d0100c0c0c0920304840c00200440716045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 329344046 1250 329342796 329342803
    0x1d0301061e0f0b07140f0613110d08160602041211120a02030c011b1502091c0209070f050f03010b040e06040c080411060408010203180115080703030509151605 70
    0x41c0400c04040700120b040c0114035801003078034501e40c3d118038480c4a201180c51002e0a1400402e4100180c0c400e00f001c021303006450707494442c0c0360381c02a9a04003401d4010818040810916800034108080c03c0041070480000796460070011401640014240381d1034540c4a54803043c001c00c287c0e400d0141606000e424039203201401c0d0600b4000c8004c201601159000c29140d0350040c040e40d0500c09040f541c440c00c00140c4c9a02d14070f00e42e2107220740c6402c1d0b03200c0421a00135046035075241e019010044420940003207020721100d6050b0018040d003800c0d682c0d81000c5402440c240c0c045410001c003403248500100300d080103140606940e001d035544480c2000040101c0e844020700c1644268101104502600d070001c0c840c0350002c1e0800d21540b480e881c8840071400602c59540901d1240d0710010400c03030410301c03034821020f40801110090214a444070142400708403940280c940c140c00c922401c000190044008000d0008040d0230718583d584000c10001550b003050b0b4100e4038800f040010007040020a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 329345296 1250 329344046 329344049
    0x4060209040e0a1104020f0405280b09030a080a09050a030c0603050708040b0a0f020c15090601090c050a08060301060e0106050a0806092206090605130302070e010e04031d0301061e 79
    0x30002884502180d071543c3e13150611000d500c0340544d40c0041d080610b410841e0480c0c002e41405080404628113100714080d80321020101801945500d03440410a030030004200e848080d001401426020220340361091150300810840302406801580000d40f81c40c0c01030034900071809101c001a250f0314000d070250a55000604400030414085c04000005141c0d20703034103410601d07100d00000c0220b400d1a040c4000c0c45425801500c038400c0c0c071042d00d01074050b40c1005204616450a5920307590781c1d855140180d4030044448004281c05100f4002c00900c074144d01503101d4001030002c18020399400c0c40c41c2c580c0100380c00c203400090300011200c000035002503100d50024070aa503000b0491500f60590085504032596400204200124140510009400800d9081d4008008210300e00309241580c0001000d041e046000d03028030b010001d0341d040d4040c8010304803481444d004100355500da404862000ca40804101e80340d0300e50704460b4040d2824401d003409000980c00c00b02103050300ca03c8103440300300315 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 329346546 1250 329345296 329345321
    0x190806040308010f0f360e0102073f090302211603020303041503150803040e070824030a140d0314010521030c100f0e0607230d050406020904 62
    0x3840c01081842da6004083da0100e00d243c078041c04043d10600c48003174040c000151346e60301606084690040c40d2040d401400701c03034410001003441c070100e05090362080446001d0100d1481442140007002c4080008144000c0024641613812686a60002d600300302003551030400220a401c0c1e00403050400c0014010b0b4036005a40e07040c45501d1070340013956a00c503d006040c1c4505a44030308490850003a04014403800700e800b41d45400c161203580090f5642c001d4405e8042c3c018104001c21403d6006001c0a80143c90b01411001210886404500015406544190507110318002240401c011007018080d922050001e04074000f443c482c02002d8a00055800310704115074001040740c1d03030345c481c840088001030070025902203518410483c114003641003134520074001c00b500301e036522810307030f009043d80f200c200000c001c07841d880d403a0350780d0341d040807104100440c1144600038010b0340004000004007948482243c501407401e240f050a44da800e9508441464001c19800c03900e161901816401180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 329347796 1250 329346546 329346569
    0xc1005010e0114150a0e0607080306040b09100504020a0509190302030f0d0e040504020a0e040f0303060f15110102040f122001050a030c050d0c0809120307020c190806040308010f 78
    0x11980002d10f007000c2060103000b000800603030481720704d004004100c3e0707810300145540c0d02c1d10014280784101d54011110f2602c6545055844c5000786402801c080c00ad0f001165508440780c02e20041c48004e500841c0742e40240314082c4210f0687e665020491080c0070811002e085c00d403841e40c4141031a0030f5650f0601c00c11030300004080c014542d8400020000d10305c04440201d01c13034070b070f42c00072855140b0a500241d110800541c100405d000c00380300040f01d41c520a41d401c011a9660f0104074840c042107005a0001c42e803892640c403060340c85405a8804925090300040c40c00d80d40350445100c001c090b81c0200c4c906501e001d481000d024560814010b104030045126600501d900e0000f0407522502c0340941c141075880740910a0284940165505109031a004004054600303201030b0480200310b90307881640c817480c202504802d8201041e80d0282d80c65070000c1611802560402a07000c030488641000513070408400103440c41e00304443c501580c0681c40340305240d41042051804109280c000e45040318 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 329349046 1250 329347796 329347829
    0x120f120708190914030a090f080703020a03020415090e0114150a061b05060a0e011b140705010b030105070503090601060804020a0608150409050c01020f070e0f06060c1005010e01 78
    0x1c0448151245800e15030700050000401c0c64984d45801c1850b0300840035103c0420781e6a2403941117104041540c00044040840c10303500c0c1d0340c0e81d560f03025900000790060f803104410001406d01ea0005e4420020f202c4100140c0c0762150350b44011502c1d48111501c00d0780d1644024620229410b45064120710390401c00b902c64107200001c80c0403441c0074070482040026400814103000f02c1c0003403024116900000342c50690820140b90b0b406010a0a01c0c3d0344254600b0310140450306034400565403e1060351140900c40d10304900040158010000586055480e030001200a0341c081c4982c034400c00c00b9880300c3c1d0f00c1f030818039441890002c0580024040c8031000c0d05001c00343e0b4880d046107084a070745203071000007569000d801c0e100c070100301c680407038000e03060500900400c00c0204460140242c00c0e07084444994041d200190f9400403482400e0358039039a2000300380380c001c4001100340d01c5003000d002c092038140c056006500d081c005040c15055580da80380140103420303403010340500400c0d00d04138002550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 329350296 1250 329349046 329349061
    0x905150624092418010807050a0e09060112021903150e0c030c04050d11040c03140109020c0a050601060806090709060f0c0311070e01030c122102120f120708 69
    0x34801c118482d840b03600081007951080a00103811402c41d00d400300c49644581108a921a0b10381a5503401400f10b42042c00003941c1e14807400903130b84030711525614804050425024001c0d05013000e072900b81000b881d58495504103083d40001c100040c2c03235628401840c228040020211401160007405894004004108100f9842c01c4541c100d4500300baa55501e48505040d82201c0c0306aa000301c0c1c00c005260b95001c1846001040c070200c0074000d6405008261540b003049044030035032003240000c1604400144014041a40174202000c3d10000b1580300c00a6915401c1ca0510240d000c0c0c40010f643c1c2c01023044a06020061541020450501d40c50060810f035019190f0a082085c8408000f4a900c002c420305101d504800300344c000c16015503e581e03840303800050200c1c00900050340c9200c0380c0b400002e00d0250081d40410140d80144212640300c04105485140449203000d0b503003184511000c7c0280c00e042035004089a8141440841d640c04215110752400d0030014401000d11000c8020808003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 329351546 1250 329350296 329350369
    0x807120c1404150603230105010c0b09070f0b30060f0a090c1d0d02010203040e0c0f0301090c020c0a03020f04020d020c0a030c0b01080c01120e0109051506 68
    0x64401446076400e65081400c0882c0003400440240c03186030351000d0000489541503440045801ea890710184107104110740310b20034645080c8100d034001107041040d0b001041807c0030098200f9501004d843c8042d40d41c1e01041024003894004800d09000011183c0702e0300c4c500e0072520031081c40303042d812151100d60000780180000043c13401c1d005201101a00401c0c0c0e40302c44948016080c0088204130f60310399040010b00c403000761031401e503c17031014800b11842850009009003207154141e00642c41d050810202c640490805440d07c036400e0400e009648603040c0420186028143e5800000790348a071144000341317400b00300494280240107120b030034009611004210169098140c40150b071b504041301c1c4e284020b20801080c10101e02804194408242c0d22507400400c443c000c0e05101c2c6a80d0f00e441306d25443e20700c88421203001c0b520919498403191016008010005640c0000203001c8150303840341420b04182c659101c03043c9a0050800c04c0c107140c51082c0310414a445140118000d00700c1000c2c149 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 329352796 1250 329351546 329351549
    0x10e040b0a020a0512012d0b03061215071211090f040218040513020315070206070c0f02060c012a0504030f0f020a09020d05130302100504080c03040e010807120c 71
    0x1180781c0c0020b81c59450b240980d040b00c3c0b001d9254a100100ea6a442082d5080d00300c0081c0401220070309119100503800d0803a8600d4152071060030301c580307940c444c1b40410012000300340c8111103078050b140714400b460030f13151071440c4194a00d48852900c4030300300b040940ac40700c1403021400040d6044c00400b80c252200c10124040d07441c11780700180d540c0d58400b01481168039804c045c507406400c00c4200001215001940c100d5580f0a80172100c07022002450380c0d4120200304c03600c6005030f01c04000101400d02c160302d1079209038001c60002c44403103180e4011480f00d50040c643c1401c641e442e8010289440b540d10340300d03030aa03240740d1400c07000380c406600d008265100b18030000d001c4460303640c80e510601c0070181001a030554020000340b64a643c0e640e500000c2e410588480001c0b500e0310700003810681c940155822500e0703069028000d11000c090054005083c0600140e94419007440a20604032013007000f03102520815444004941c90498203070705e403040603005000440c0f034214000c0300085140c2c0f903110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 329354046 1250 329352796 329352811
    0x7120906020a0b040204020c0f07090612020d1e020607030302090310050621010f0c0c050f120403081b01020307051803030a050307140f04060c020102060f2a1c14010e040b 75
    0x3c0661074500000d4003030700529070161020f00a4030000c50a8200003c0e52504640d041c0c1c02c240500707580c805401030185910704001e50020030562074680043d00c28042d240410a00c00802940c140180e008650650040030048020030342c0000d43c8101d03850200161000302080043c140050300e014804036040c9034401c0ca0100890700401c0d804c02c040c444c2900a07409070142c1c004c04000011100c84000c0c1812500c0300700351068024803451980814021600c006802482202e10349081c0c5190346086440c0d1251440c281a02e40d0b1001441c3d000b80203000550007a41c5e6a500c8a4072040c6821450902c0d4191864080c0320340c4c01000108007880d001405d036940101c0f0350404100c00c0000c230f03001c980148103444012105010004e8042100c81c1c21960448041e4001e908941e85540d92045425000100351400001c083c0e004451001004030104074250071071021581c43d00b803105400c1040702c0640010201650b01c2d13110866011016111032242d13004051008440c2010f081540780c000d016075010301000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 329355296 1250 329354046 329354063
    0x5041b06020c0f03030d0c02060105150a080106050a02150c09030705040209130209120a0308070e0105130522060306050411100507030e1c03030605040f02040509060603130f030507120906020a 84
    0x820f0b40e035909005594103030446107024001200160740081d11203000340070301880307038056180164100c6185810741d002428161107078541c5900748081562142c0001e10302c41c085204002c60742100f06860011036000c1c0100f82c4056486e5990310040609200c0359410180c025441802001102e91301c0d40281190542201401a0359009034004a00c401881403004026885a007003110b00301a131120b1554441c1200380d46144007415407900440d00341c030039030482c21101102c01c8004c0c03109140804501640941507410b0300800081800d042041c0c85081d407003580c2c1d4644d103a04000620800000d9510601000c840b00108241014400341c114000c2c007101404212404800c58516103500c0c0b2240600b007840c0708031070503000f8070b4500100541a540140c5025500301000d000d56103010340252003e5a07000bc124004075511030080c07181c9170b00024a041c191480d42d89078072011400820303d80c05800e0107950740941d107003468181407a130344081c54030480410103a0030040102640c040b07024201a54402040b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 329356546 1250 329355296 329355319
    0xa050d0b0303040806090c0117010501050304150b030115180c050301030f170f090316080d0e0d0f03260c03131403131d100509101805041b06020c 64
    0x4a0302d540565080050988150018801d200c8000a040c130700c502c000b680d580312085550400060009800c2c4981c902040c0140003040008141800c0e030441035000c044001141c140301000a801c0d1650304111810030355102005000d090b0075150043c170700581154080c8600000003000401a2005200c04dc090455002c200c00400203003134500f110010740c0c3c030403007038a400d0031508011690f440080c1880c0329204a103082d840145c0381e484403000b1235007400080c00c18044600c1e003c1d2801300110b003a655101900416800020b202c82c044c0481c1c26000f80d40b2a489000d20015400107c400140718000c0540c0030343c200200560120b00702d907440b103000c0f4202c2107412034a103005007002e0b107191050700060101213000300c160a88000a5011200c549001c1600380d21007e0000e000302405960250300c030410301d1340900841c2032842c1e610380c0140c40018142062a9101c5500364a41d11040d1112801d40d110400c2c0414030081d0440b9080100b180006142d1803481d000000c1d40c5e402c0e8400c002070041440700c0b903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 329357796 1250 329356546 329356549
    0x1020a141c02040605090f010e0f010e040e16031203060f060c08090409050d0909140105010c0c0b0d0c08090c010c060507030e120a1404140d0c081914030a050d0b 71
    0x511082a0728040c1076448a481d407001034115000076041030701520301503511041540c803960390050800c0000c0c20254809600000448650b40c001c012150041d413a10054846070394104843d00380c0e041c85041e5070718102d0444c80c00f100440c000f10066000c00d0304010f030901521005154410444a5900300341154001c176103010350042c01075000c1141d202d450300c0458070601c940414a40c810800640e14050481c0c0c03a0f0482c0c0049500309889650703140c2d2400018409540101400c5500d02e00a01800940c16a10540c04c00654420004c40c026661904012030401b5003007800c041c1c00101c0400a403003040d10300c10008010942e02c031405050b10b43c60301c01085085001e40d210004911440c025141e01c0e803190000c20350b0703aa001028501c00500d80e01e00e440000c00d0700034207650a940b403034a0030951840c001020400807501b19801620186c3ca10200082c1c1c124040040380407a011165150450750501d0070510710007211229801580c0c1c004100040143d0745c00800c0310054071614a000070300200d4a030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 329359046 1250 329357796 329357827
    0x150d0c05040f090b240909151003050c2e0e0a03290c040608040201030b04020c060907060206070225031b031506030803070507060920040e01020a14 65
    0x3884903810a01d41002c40c0307000001030304110074079809407802c6540d58561640c00c034601c056508052100010b03404100e110b61070542d62081e000710000c000c03140c030318007440e0030481040030507201c030003022105400400070071405111200e0b0101c0c086400400006c0050844060382c0c0c001c0d40800c0602e030b00e00f104080035901030301c0342180d000805488448401d03103d162024000c0c1030b4400b41c41c03208000c082c0b13000a008564003140e100d480504441e0341410328000054076400700c0903004a0602d41c50703504940c020307226440504a0504d540e030041c201030601910507428819280c003d601103400c2002009031702a000120302100c0c1841000d803041003100202d8060211000d43c00091a0a9011641ca0400d50650042d401600e000d0341800d0007450380b0348114000c0300c50b00c0c032005120300010700000346e00500400150000034010000410650155031320780b221446600d03035000280c0725000c148507440c1031900c0750300301e0b621741c0c50000c41c50002a96005031100304d00d080500c04184002480310140380c0501e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 329360296 1250 329359046 329359049
    0x906031603091b17010509120f12040f12020115270e210c0a0f031106070801080d020a020a0e040510050702010b010e01031e05060d1505040506010608150d0c 69
    0x7030680c0114070f034a1084111a400307114000e1040003800c146200c03e00e040c49140e02550300407000f0045101da083c540d1580e900000040c4810300418401105035003000104684540d118032803201d49074a01c1e01d40401031050714400d807821a850304ad51908501c81d018400c01c10f4036102000101c01144d9400513080480368149a540c6560400c081080c050300d0000d010100c802c100308030400e04803e20302c44400180211004110340e907210002007000f1641c0c03210014903250103860050945204901e106c0c0c0f070070307109681102c002458400100f06200003440b5a004c01801840688450b50007500040d240d40724901507200c1c0a0f0f000c2d4049401c10100300000c20102940a6082c081c034585200003074000d01b6080d00b000d02041300d0301621030301c56100c1d1107490200c05511036411781124410680100910000b000a41c00c600820340391004284003803200d07031148001e914041b803645840d14256041c01410f900a1040c4204e000c203004a006100700111003191301912110040340045c203000c0c1204011307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 329361546 1250 329360296 329360303
    0x70c0b1b0d090507050d0302030a14071e05101107020f030c0904051612151109030a05010f11090303040308130905010e09011a0604091107061e0b06090603160309 71
    0x41058862155401850b00540204191503000e5900d909025018140000080040e0403c0202d0b40b80180214500340c5100104000503080003441e0381d5882d2101201c404108100c86190801810884104142c000f01405000c0c14004007171030f418079101500455000030f04c00e0a1694040c17016440c10084045c000e51b00409110721800e1500700540c03560200c00000b4407129003184c0c085280784ca8501007105103548601c10358a0390700c1446e2504006c10184400816003c010400c4030303e035135010050804004d015800004540704ca0b4075854085502501809603644014424084555004020b8808803034001180310f61303c4101d52a0704000c0f40103a0850311500d882c10001185e40468192001d10801544000b0055901d820f05022050710758034501d01d9015030108000d100a815503000080800d1a2444645c21b101656441d4030586040d4a000013001102d000038076042c4046000348014040c0070b8900510b4041901c1c04a0014403005116a000c000c000c18032180c0c251099000300030042c1c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 329362796 1250 329361546 329361601
    0x150a0302091521160905040506030705060301091a030c0105070206030a0b0301050a0f1406031b01170c1309060e15030f071517010f03060903271d070c0b 67
    0x3400c0788080c40d44899440008120030f0307000001341c2c003458410868078004420749038611081e207000100710142400274000360b010702401c0d1001426880b0400903501800601d07001080c0c1140c41083c00c01c03080c48402c50240303c0d03070060a41c0300959822900700c800d8680c0603210966203a070794000003006032441000c1190158a803008003e030070b4078190b01408000d5042e001c20312a0840a01c4203209200341a41c444e40e01d600500e88000765802404444800d1140604000300045813400c288425144116207400c500f40380000c200c0003014110302d460b03000d820001000c20840d4180204002049002017064091030314045507502280da08104c401c40d2200d0040840b140c550300e504014001c40c0c2e0f20100f00300030869111051360540a0300300381506070342c80407240640b2a451900c40101a100e540d2046c0e05019522610480c1903100d0503184507a8080e090010b600c0d60701d00303026100740038010030204003501903450601800f194007020b00c03040150005403481700303916070483c0015581c501d135502d40d04410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 329364046 1250 329362796 329362807
    0x21815011b080f0408100f0b0103020712080a0f020c070620060a02070c05030a060b090c0702150702010e030d020a030215060d031202250b06090108300408100605150a03020915 77
    0x4001d500491007d02c0c06050a000380609000190140e019076800109075181511181c0c4407180b01d2602281d105000f09000f2804001c0160900202e80c030070310030404030790030102c82444461380044410785000c0980d40e8a44910303020030840c03511014094011044560009454404c0c007600c1c2024601601009040d034a10107018070b0124018122540d8060041c420480021100320202090340e01550f00540904e0103070340c00c450640000ea0050500f2414000b01444c030300d440761400c0007010925071582d0010140d007a45814064601405a00d000310f04520400c200302041e10344c81c0c0340400c3c0c2c82d418100702c5860b4202100801c080d0107000c00c51800903e0543c0c40540b452480c80d40000610b0003030306442040d417140c006011101109000d10400f49c0d2151024048126000d582e44480950b0000c0c80d1a071200c94881100d1641d205501c2840350303500c010601d440b1408184a070500808044415043c02c082c10058045036004010100003816404143c1c04480c6d2a50700508903040a4402c035541d541c13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 329365296 1250 329364046 329364073
    0x30e0a050915030616050a0c080d09030c03030b030102130b0d06030b07020c1e01080606030405010b090a050a0b0103060302100302180a0306140a091109040f021815011b080f0408 78
    0x5915030b074070301c0c428420311012071000b4512407141c400050a654503d072030424428070a54090541c1c040858547c5010000c02e80000f000b4806c003803000d80b080e580d040c441511030030010b00342c0320055201031007644100500745000c40b800c6683d01c111030b481400c4d29201c42a121102d8002c000c10307030025210b0284801080061940420202101401261001c0b0000030301d111982c500c101c44203403903000c01c180c035000c10f440f0b12b813003009558030602c107500101e40d540440c8003261814030b042d907507054019110020310000f40782030b005030a10301c4020304c0c080003906c2c0342d60000380740380b07411004910a0540c00100034502c0c401c030070060044507901a004d541803036903a1074a01e0090118502420301d802211000c900d06a84a01607032203495044000d140801c00c51404102d00d00502074030413603040c08580000380068662464000c0001e05000681044d480c080340131150001a2403000ba04014000c0c01c0781c12064040e0318039060580c2c10964150700d408000745100580d1066070003491807440744818123000d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 329366546 1250 329365296 329365321
    0x411040906050109060f082a0a031e0c1e05100207120b040b010b0307020307022205040f1103030405131802130203010815071e02070f030f02041b0507030e0a0509 71
    0x310351b07803034401011182d540d86e59a40c90320b030f80e040300c4002c5848d1283d0288424a10107650048220010404014103582c6e6903500c00511030440e8140102014809030030a00c038040700c14100400340b9201c44921882c2e50050b480110000740207003803013202038103c40744050b0720030018800a0050021000c0161040d03040001003000202c4003100c82d103c030741001080c840004410380c2e00481194000b1800c0c0545a400c001101003c00e608ad450700f2600c00441652a0040c000e07640900d004484541c0090f083c0e00f0b042500b86c0c200080c05010380c0c4100003c0006440da00505100041580f030b0024106003c1803000030f40314071411001e0740c40f1501a1b064015010143e006504039620b400803510594681c141080051404460003004500d544506200c3d0007102c2c2d40c4008640e07035901c155034410b510b440b204141c1c26030235003094401040007a10902103091602c601e00302e5000e0004620601ca1425000600d1841090002002c0000a001280e01074450010000103010018480c1503140b6000348800c22 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 329367796 1250 329366546 329366549
    0x1030c050c0c0d0303110c0c15040501021921030504050f070b090405090304050303030106020319140306060307031d03070c05042a09090507050d0c0f021c051b0105062403041104090605010906 84
    0x9c140e0074072440301c5070500c008045031704135001a000b43c07030b480303030780381c2d06c0106407408440305483d00043c83c0720000103a40b0103180103044c250300b034a000070142000d0501520f041d402c1d160350801c0740c1c0403900034032284401c030080c0c0d03006081c121000f00b441c0d9903a805070303411801982c2c40310385c0520003c0004501d003500030000c4e2449500090030208140c0c00c001c8115181c003040484d40f20125001c00209945003010402154005c0c0305080200390204c89401060a40c4c0020058592581020460350204051140c0d040e008190403602444400c00b07103c01440010f504002501c2100d1020103420041ca004011f018001c01440314100714a1805c101c0251450f88415000d801c014500080c3d80451800352004494400140c0d00410303800b4007035602581e02244629880c1c09100c0181f041d6440402003601c010540710b154000400d150422105202c01a00807524200c40c81078107400303141201601e10262544250484030a442145190740070500921078000003401982c00c000000c03c98a03ca50003900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 329369046 1250 329367796 329367799
    0xc0912030d0c090302011205131e020d03020f01110414010c0222020415051e0c0f07090c090f06050a0e0f1c05070b09130504020a0807080c01030c050c0c0d0303110c0c 73
    0x540c01e8a094040c01c02c131401211004802131003400a1004942c8007601440302041c0222b05c0c00e0b00c2c007840c0c0c00240d03240901410860050740101d03095440d0640a000740c180450781102502d042504200200402c5054a1045810040b108c5a86820b540c0d84411001d6406621490380c807006040c001e020019500c5400342d01c0441c81c041d00c0381141e543c400c40c101ea0044564082c010440340080c900001c0a42c050004e0050310322401302c290105d804180440001440100300000d11285003200c0603140390803039072002c511001e4501c0c04100c41d40e00242115a1b501c105e18000c203041c02c410000482000c440c0b20402c6e0842d85800d041100b03072850a4080034403a018070212100d26941c0c07807243c2174030300c2030f001c40f10b411a451141502050840360001d60b0814030061002c1056138071402407520303081c1075074890700c020303030000411180300d50f00352082e40084216032070060b18121010032915603505c0e14940e214020010030031400c050503c25448a14180701c0300b0801c6070381e140e03400a0b05e42d4407040058240d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 329370296 1250 329369046 329369057
    0x14040219032f03060919020a03090606150f0c1b12020a0b3412080a0e06060a030b0612031303050105010b030103021804050f0a0f05060f0c0912030d0c09030201 70
    0x8000508aa4403031007184402c0301e46407450742c90a0521105000140140286d6202e055050ba8804058005404424130542d40098110451305082e010b941641d030098415810050351403140640c40140000200320350305000c80543c140749440d134802e100b1302c04c0c0000da180d061000865040c0000c042000d030309008070380404070103032140b11a100600c41c00030101030010481e0080021100f221300f09042c08201c40320410100c0201c2c0c0c84040d50035484040050001c1e40410401001000b64412401401c1c1580014102440c10b040419038040c0c00340000b0b01f0b0790504000086465650343c2100ea0844c00c00d05c04c1c7c0384c44440e0100e124410000a020840b020350030440041107242011065034104c0c0e0300241040310307035150045050b0341c4941c040c0040d40e0500030511490a1010100040c16441c3e10640b21600c40c002c60303040082c2081400703061020329140709028400c1000020b0166115400100c0320001a2400300602c5840c40c401d2000781d101e03103405c20031014036131900042d02208483c000c0c0c944 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 329371546 1250 329370296 329370341
    0x190807110c090112020d05010525020a2f0a09021c020c1203040503040f080307061a01020d030e0f100606030e030f0f070c180c030b1002071404021903 66
    0x400e034441c1c4400020326048500341c00108295a042c100c1564040d0000d0071419008203580c03038040c01d40e401292141c604c904d8215110f0074002c402c5c0060030040201d44050980c3c1906541c540c02e0400310128040500010f13603c100303484c0c60b00000101002c81000301104802e5645145500107508007145103000140f24030b10500e1180c1aa0003220040005500a4800c0062108441da6160806001503c55200510012440502030001c0d8405000c3c3c58000b1619013401d440c248090b1a098070403c0c030002100700d0303401103130b9800148040301e20039541070200f40004491144d03454150103c6481c2118030032201e0300040c0750301581c018401d683d66582c0a2040324103000340c50707641344222130004809000420081112814460103048000d200b00312640740309507102000e9401100f044d42040b1030a83e501401503040c1e416102d510241982950a103030300040008000e92200742c01d2290b80c4000321b44500c1c02805690315070459500104440700990741d00c1007504014000d2907100c4000340e10702c2d120501c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 329372796 1250 329371546 329371577
    0x2010216060c170405060c0c0307320102030d0c030b10140403080903010b0d030e0a0f140909030f0304050d0908060c0a0c03030e030c0a060f0203010608010605030903190807 76
    0x180d04241c0385036445410b001030080c0d982d818003107040a0b540b910360000f48400318681d580c680051507840c1850000b0000c421042c020517040079020341c40400007158485a048928900003011050b0f8040c642c103500c0d0040e20034005078114400e078200890306914185150460540541c00040180000d858010a515004c44262090a0600b424904920084c8810000140300800900c1b81610140c000308005003050b0101e80722070449001140854071504500585040005e0b00340001c240004803455120318004030254503030008603009020b2004080000c00c40340d4100101c402c0491041c0042e075407460306040a5481e035404401c1000040d042c0040018003101c00104c540c001e214450181d0300d0a80416410348452030042d034114140354491020705030b04038062002c0d02d09185401e003d0041d8541030703d0030a0844485940c0007400c184107200500c481030740041d109040d03840908125980b602c078a18020f00d10b0088002800c50200d12481e030340e802980c0710340c17030034010517407a2901c60808032140c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 329374046 1250 329372796 329372833
    0x20109080d17060618131b05031e0c16020301150801060e0726070c0209070e0109060c0503040b090105160602040518090a03050f040914102c0402061204030c020102 72
    0x82c481006461040555006071410b2440c506100700500c0c0b0025481d17603a0120040c183c8200b2480101107078011042041c0b0003e02b800c0c00c2018a1440d5664609240043c0c40900c0e5010f11000c0c448140004608003045445c254401ea0401c4841441011620307541e01e00640070340458000ca40200a04102240c4028001e5802204898800149201d00140790990508988008040408100244d4050303805030702e4024500340079915a6a42d590044008800900100c0c05640214200281203800c880410f801106031000e550701110380310750f40d051800040b6198014001d0000c466100c000e52071080000c1d96004000300c507000d031070105200c2810158a002c06008850030b6403103400404003e000a4401d030001d0141c81d1000c00340c1410142c9404d4200200c0701c041080c034031140c2d144414044d040701c814540340000c0c041402541e01c0d03090800700e1100900008004400a0714882d800700b403c640d1403000b510308515440090b50000e14280c01c0090188604200a9015000e0b00894240741d01121 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 329375296 1250 329374046 329374057
    0x9010308030a05060d0b040b1006020d02030f0306031212060906040203010b340f051501030c090e150f040b0c03280209030613030324050d020109080d170606 69
    0x1498240c00d65075040c2c2100c020389402440f0036404207940301a80005890451044d000e14000c001c4922103140100718040003001d1382c2c02000656101e9030100340c5035a800800c68042000c82103200e0b8031394a135000400d01d00035140c0b00c103d20440001c14410703910441401480e00c200811108078140d030300d079074092208900c404c0c054551003c40801c018140707904944140c692541c1014000078038400c514401082d06546030000302e4a031200e21600c0024461f0410450300c9246a0241d00086540345a44286019500d0f22481045644694003290b40d42424040800769441d0f984000c0c0071440c00005d988019907080300c00b100c003840d002c0e020415644003401a284540760303000f0003c10610159010032400c00740c9031000c440701d07a02001204000c0d10240180c0740229a01000c0e5800c41c1d0242c900501a56810b0511910384070f40d0301c1c054107010700c036220100704440c0141c0d250780c1d030081d6500040f160801240c0020005208403a00900031507440024880700e02407a41c13540c43c5039141c5408120b05803281 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 329376546 1250 329375296 329375303
    0x21b03030412091e150e0a080a031101020901051b03070f1101020d030c02030d0216060f0c0206070503040c17010912080a0c05040311040e15070203031905040b07051b1e0705090103 79
    0x5130340b05000d18201c00703c89003031200c141d05062419003450390000e0711014064203c28041d0b0032038000c013070801d5003290005014640c168000e40c189072040d40024983d000790402050310198514401201610620842d050b0700c0d007102d040b905401103402e0001c220079005080034014031400d00c0180505200740320380350070002d01e54040e44c54010200121000394020501103940d10701ea500615002075403d1040c008030301040600410f0800c2c00010103420408010071200500c0030403c00c0200181815021005132040740103450300c06c004c4140b265004041621008011020452041c000c482e00200003504c2026000300601204c404118202ca01e07000c1c40c4030080046a49003140c2d0503074079060708008000900c085c1101e4030075021a210005808040d1038140c0035030800420700c004155010b02d445405814804207103d142030540c0c503582e40180041c004400c111010803801c03903400080c40340b007840d00d501008403a000c0e080b905030008281e4080707203410141d100b01c0000040e242003100c0d00d03a0480f80c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 329377796 1250 329376546 329376599
    0x10e06030a152a03050106050c0c010f14070309080f07030c17030c10020702150405031b0103060f080709061401050414010905060706051603061206021b0303041209 72
    0x4140c0d291030300d500511007608142611141e1400041c0e00180105086001e0580700c20f80021010b072000c4c0481d10180c014200b04541000440b0f25400e0002d035000c1030a20a1038110515401e40e48210740010116181c80c0300c1010010784002803560007610074041d2008007050758000304041900c181e4a003241d1100510405421f802003103064400e141307048160484805a0345000068207d10b03042110030104c107044123501107415001d6050004240707003c50400702d0101d02e01820700d0000303076841c3c1e00d05400021025401d440280c069101e6000a4014411510942ca4039070300c1c0d04006071140c07030501648410502e4144002041900604106038020040c0c641e075183c00e04041440d90003c030300000300c0303040c8541e08c1e03000645a2074410050804038091400010036040c400303149101d00c008200031104040c00c0081c140912090104610600c0340c0c0704c02c006a80b044104480c002c20500206494120701006c4104030a00a403640d0000721040140e403001030303054943c1d8510720f105080f01203180d800704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 329379046 1250 329377796 329377813
    0x1b010e07050d08090301051f05040603080d050604090c06032004050a05061308030d05150a031106160c0e090d03050f16030b191a040e1314010e070608010e0603 70
    0x511800010a0b07a0103010301c1841c0c40380c03200210b404e5400c00e0355203400301000b01c0700f0070301d02010000c0d8440241408490a101881c955242c80800340114a0481d10842d13807080400c0e0703560b447d03500c10507400381d001286003491030342d58074060006c040140c545901c0c401c8107451400b00c50440401c95042d9000281800481c505210034402c568006580c0c1c0c001c2c2026140c00403032000002c0014207141e614120007c1005e1030441c100d0a007203020302c0080c1380940031001c0d0500021300701443c40c1540b50829541c0944030708070a11418220610018050314051b00500082041d5910244640c0302c0d03030800c0100c3d580700c29168011022202c044400a1823070081c8404905440c4100801e050003d2462901041c811410f00000b1440b642420b5422103c1454040c200800403120104507000c104200100e801c1034649044200362100040c1041e400c130403104c8440d010815000205098400c441c0b008100f2650b0082c42c1d1581c0384020b008a00c0801e07403a00000481c019020012407041c000600a8107000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 329380296 1250 329379046 329379049
    0x604030f0f240c0e0102060702060703051b07050a0309080a0818040b030f0601050a08010e07170a0b18060c0c0a0b1510051801020d0f0f12050c1b010e0705 68
    0x48124601c102c0e10540340d009042107024440303403400781c5000907150010703000320700010103440607130701c050b540341590080c4c03041207003d68000c100c550344030129060200d00c43d41c0360008808001540c1c01001c03610a4040790000a00100150006269210b0344404030a00d40f501060355885802880c010620981009006113108400d42002d10b00758002d4070200d100381185001900b05207070f00a00002c1503100100410151a081e40d81d10020400300c4000c114041c0c422642648070b104a000d13424134240e424512000140382000821401500040b4a4449050001d0072112003030744044c0d0307910648190f50108504541440481c2c1b03551000380001c0000d0500b964a9154400008000341300c03110400a1440710b0b03031151004001a44000d60f14160750315513154081442c3c45142d03c0c03480c11544500304240209400c0340c2d0302c4400340707160304265070004401d40c8102c2d40e07861110700c0c0200d03507030600040c0f00c03030446888003410060000a19080010820700042401c03074001e55070002c0381d80d000700e004001c82d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 329381546 1250 329380296 329380313
    0x191e02070506010905062202090a030b130b0c0306030d1404170d020c0405160e03010e03031801230621030703090305060a0b0a12081b0705100c0515090102090a03030e03010b0604030f 80
    0x1040c101034503189052fa03507919040503015084844000b0446a00f911408000d0950241a844041e0034000e0307040d03090420100b0355a244400181c0c1c14800000007401000d10341100b40c40082221401040402d902940d001e030f00c42c1908003940015110b000031540c010b2800c1d001e43d512542e40380c1d000380150896071908031010050003400d16010f540c5c526844000000500040d4802c41c01c00b05900b40320104947c00508640790400360207411540100c3c1c84caa804d02d941129900901704542038801d80e0a09403140400520316400400076100c0051050b0070150042020b130100c0b8095415550540d07100d01807001910040b37400705a01c4400320f101803102c00b25800c004803080780a1803e582c1004500d405455684288500d810b075a68440300c01000f907840c1820210119941c10714202c01345d06410f503102079480482d070003500c200500d000000752507001e096061703803000300000b48000e12a503641d040140c18084140c800302d00039420402c1c1d4081c0e0b41090b508640840c3d0340103100682c0301c11907840d103260 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 329382796 1250 329381546 329381557
    0x907020d140306011107032406050604050607020612010602070e070f0228060614041514010509013506040e03220e04110414191e02070506010905062202 67
    0x41c80b01060000e8101e0004011b050007841c0f007254411401d80010108888118402e181030340b201d418448288a25191901076804446068800c01e071210828800901c041c0101c0140d544100310050002070015400240c000407524040caa90449441e806001c0f1018001c401a10b4050303805002204501040140100099072603103160782104001a903400c41611010341c404400071076241c51041c41458180301d401c8090f01002c4124a0701c5150034154400050071105884c148100450030340c545900604039900782d8405012207619003a0720603541c80e09030103504402c1100440c0c1d400050590b05242c440d403040d4044000043d404c0064030110102d00d001d2074604425011003482000600034001c0003110301441c4103407078003c0301d446100284400c903842c0c0b003c10b1034641942418890401d86000c414000f00310541c4010505803054810220024410384106200301c0c8009a2501071000105410b4141c40010400707020f50384400701000281903207122607820000d1000c25514040c8680d500504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 329384046 1250 329382796 329382799
    0xd1101020c0d0908070e0121060212090a060b030f0a140c030f07030302060c0304080d090f120f09050d1a2805040302010b180118090c03030309020907020d140306 71
    0x61034403800120361802c1410703806070100410322001041c04141414045070300a4211562003005640c50118503181c0e001c01d582c0c012103d500d103641c510084c80704c640c040700c2220344040700e1440141815041581e44010741d40302a00c1c0e0f1490005080c1e82480c0c0810280989800c0740c6c0203091f1401d260310b51001c031710141e80340713140710b48039401d58112951410301150564410303a1014004252442c02e004e0300380440144030340100081081000000382000c0c0c01d039641e1800c000300003d81d81081c2c0c5060800c10004030000360000200c00d005484540d4880b1000000c034205a80340c1f0032450341c81e0300f0f106403000001e030014002101c1c1001e8a504110f01080c86922201c5410f44138170b0b0100c03542d40316034040c1040c0c0400000ea61a6410031041c15024001c003190b41d81c0503600c074003890382c1d0422040e442c103078180176414101ca819500c2d03229012a64100d02c1c05150400382c4100c030503580c1d140c040c0007803000050890060240a001600450010a5050f603c41c1551035050100341081c039100d80d5640010250f5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 329385296 1250 329384046 329384051
    0x501110a26070501090b0601110d0503040f060e1f0f050408030a0207020109150f0807080601091a0904021314030307080306040b0105040e16020f07062a081303020f01030e0d1101 78
    0x82c0c022072000d001c2d100345113002da03a54403614100303003000414503041c0c0502c90381582c2c42003440b598050382c401c044039403041e00803c1030034440d02c9610b0408003038000148018650b1190300205480d8480340c04004140410140c1d003000710503900404a425508100d402400c6032105000260a41e08150000c10016205152a91441b0741340c51100089824026000700090004400341d203004d0b0b0801510b94100a850920305010300d0030000091900102d80103048040598460903508540b20301c0a60b800000018400d54a072415052010302d91030355486020468002c1007001072060401008030360510307030403080c840d00e5660342400348030250240d0300840341041010400050f44400310a0050300403c0304955407541035450301802440c02411f61900340c41074100c1030741000021382240110802c2c0007603594a02c08500c1c5040f014911003103164010380501c00014503031480100d0071891205491089030780f1031281c921710004608541b0712040b40001a40503555a02205024000c680802405003001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 329386546 1250 329385296 329385307
    0xb01050d0c12050f0c011706100909060801090c0e07051621030f0b01180306051f0e1902121305101a130c210b03030f040501110a26 58
    0xa1902100000740d00b9550354020044c150344d500c409120070440c051007440c0221091241106603248008050140740c462900700c1025440180075114410003410241c03000c000040c1c2d210800c1e070281110345400c0343ca10414004c0032483c5410034060f180161169503a0b9400e041500c41024501060b460003694100b6000340c11703004403800400c00181840135580d01250318041e450720a401e841485100b581070003201c0c0a074032113608441140000316600203501080d80c4e110603c14041b0008020b8918030503464403180440c248a000c1c4a05001d040011104034a4002083e8540124010031000d00e60342c0c0e10800110b4a03c0c2d20100c801c2c0e105501840541da190442d4040d241c0c100c950300e08150190a0312241142031520344510840740c1552007030014803800e01e0700f08005000034004c1c400c0b502d01c80304454181507124040c3e8490814840e0282c100c3c0d581d4107000c0e1302d444043d08203125190001c2d02c091007801d0090b1010406404455001c01841c0340319802d140860f0880d405008030440451080c401d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 329387796 1250 329386546 329386559
    0x1062001150f050906040b0102030a030f0902060f04030b010b030103080a03021c050a06140f030d032c0c040506040c0c0b1909080405150313030e0a0815070f0207030b01050d0c 77
    0x100000c1094204207002c0c1e901c0e11042c011050001824148034500d0000c0740515660084122901e807825840c0004260b14082c03002d0b0001d04d01444060741100d0f000c683c00c0d1011001c0c4c00240181c9008050100041e07903500c07452640d502c406d00004010303d100303224a8080c580680c001d40306018240003020544081d4015881c1115011240a110140c07902001c00c41c44864408a81041f5800c1c0c0712a400c0b0019000469510f0058800308010583d480c43c06a44252032400c3c8044401500b0003034255211035986800d81d200c00741e5076260301c06c2d854007022810398601031003950346c922070a031900861044551110400c44e04010041c1e10280c1c240c450301c01d119803191003503454640c4155188d80e1101c0c1410180000440c00320001c0c01038100030810b01550b268405925040b480d8980791007140c0809403c0840c10711145984002e0300c5108120305409041d5500c250180b09120541d5800302284608400300d9075000f86200c007a003c290810b0040c00203040c8000d4010800b1b0003142e5054245583c0c25 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 329389046 1250 329387796 329387831
    0x5040e1303030e010c1b06020c1504030f0804120e03120c0105010f090b03120903030d0507032406050909040218040302030a080108011e02130504050106170109020301062001 76
    0x448548914034002014010107425101d19411000000001c2084034801c050141105c2c02c010040d03c42c1c4c8450541040030000039804550050302c0c0c200c1519004002803e8480c81e80f48180c41c02c8020641c155160641e1074030813034101d4032480d00200c807421420030301481990440301d4110f80603090b0140541510301500340800130b0001e056402c0c00000d5542c0350071404003800c05543c01c44202c0c141480711408640d980050044006002803000c9581c40807004006860b500c284081d400d0480d0800f0100000c0c1d5805512501c01c261354070304001c0686000c000d5002030511035010315008168244102d40a40c18451540c0364414030181c400351810700192031610400008032011401a8070005042c0e114030341c08890766005040e890028403245840381d60361b42d890146601c0d00781181d030b40450070481c00142001944001c1c00082e00800495859010081503142010004d01c240170b400e02c00018025601c0c800c9074100e5010383d4407141d0010045144a00f6041005104426503485021a02c100354510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 329390296 1250 329389046 329389051
    0x1d0a050901060504031424090a0b04060603210f1404082e09051b0d020d0c05030c120a030c0507030605070305010906090e070b090307030b04050d0801050307141005040e 74
    0x183ca0b02d03611a46146001c0301110002c21001a40b50011210454000f20b54402c103060038949100200c03940e03582e00f45251400c02e0302240980f1207044001030000b40041c0741d2080003641d0041035080c5569196421101c070b0308210b000f07840300081d5141400342d807192182c00f4840c0203c04422003c2e15007036582001919125540c03c448103c400300d15800018101c2c200802a4006007040f001c0c0140c5100751202515940584c42a000e003d065510089841d5110740c10042c0d81c0354020400108078200d400c1c0185c0c84111400340500900c1009081111498000340410000301c40c6c20044c2581c100b1035400f10f6500040b003100300c445100701e400100002d0140c0c003600c3c1c411425907600040d65858080e402040c0e510f13a03408148100d01c2c15502001088022a1030401d541c42c1e850701e2542c03014040d021034500129588060080a25501400108040494071403542003841e950504d640c1d81301c408054858020b071041b01140881c402d06030386141400160a00020302a0400c941043c0e40c0300701d02500710604 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 329391546 1250 329390296 329390309
    0x306130c0c08030408122203180518040c120f0807030302070206070b040203060a020c030a0828020d1103071e030209120c040e01020301060e06070f1a01090c0f1d0a050901 75
    0x465024003904101c201b01d41d100c400d90000400c0c40d0307620003004941ca684042c0240030003c80c590000010428070780a01e00411001e403a5001c00c3d1600302400444503c25101141ea00112481c000b4107845800c5a500d06070f40c1025040302e00e480190380d00d00307183d4000081102031513000d200450241e030f42d010113001194002c4050b003c4518241c4109810b19000600744200944144100c0c2c1401d80000147c40c9001481d04003010280c0700c01c18403c181c00c803ca54144a000b04080c1080c101c4442600030701041c030080002400054428000b261603400100e40e1040025801c41c1c2d800c184c500e8200b1940310141042c2401442c0400400120702e044c41020040000ca40c4080b000c0051814203100c2c054007107010000850541d4103081c401042454104c823424800c40300480d580381880032203100d0704410395000c04484c0c2c105440107100c01c4020000d12032802c13210300e81120142d4180c0600c003401c18803011540c0c0c00080c640b42050086900300b04a80b00ca0300b091034507401140d59125540c0040c0030700b50303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 329392796 1250 329391546 329391563
    0x406080607030e03120112031709010b030c04060b09061303060c0509180412110f1c0f090f18090c0b0c01060501110304030314120c0a03050c0306130c0c080304 70
    0x10090805015603444800d50811130740308009510401d07008640311030544414035001003400d6101c0c00d044800ca285403806541c132200e441c0500c90240030542c492021030070203078195082d040780401000101e42c460700c200d00c03401e1010001c04d038a40c60074000601100301b5100d54008a42d46a4442004959120142c078010480001d0058900d01c4c21280c01c0c2046c5600c4a450001e40c03405a0b40c107145640c0110b0740340103114004680403e01001070085100400903541216990550021800360b10305488062802140302c22400c4980c45202d150054103981c0b00300103a80b0641c1c42d10301d0f690360b041811141d4461017540c481000002038544c0b00140000c00a0449094031aa40d03d41c281d82102c6440c1d1141c0d040c00304100f0300101d60b000200c26101101d405041c42d9103a001581c410604a1140192500d0100078071000c201c0c3e107182c80d0700503103c449840e40e003c2284d641d6084040d0400c0c801601d1440c1c1c170842e261000702060246400116000d4038900e024545070100380e880e00990b0704103840880b00d142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 329394046 1250 329392796 329392801
    0xb0109031b0f05041803030c02150f01030308060904080412080409091b0b0c0a0813030f1b0906051e0f030a0807020f060304020105071101021903020d09080c0109050607020f04060806 80
    0x6002c4051840604403c03501003091240782802550360090307a08009042c0364136240c2440490b8024885009091095003082c01c2602e041810804908000d000440202d000c08003c21428180b080d0114480d5a000020310301c0d00d414030f0380318035908018000c1220360420030007002c681b809450040b0903259114102000c1e26010840003e5414074644e040758190b0b000610840501e100d00142c044904c41c1c001022030395441e6403032a042185446a00060600c0301020000303010088598203c0c0c0c00a01c1c40e00600342203c1c0c40d00044400d80300184074980c6d11008030800c911103821491808005080c0c010301c1605100c0c030550220707080060304441038501d21804500d00066080840600c081034008840c00c40c6507152907400078140340102100940106005403100c00d150f4020411911410041c4c1480701042a45243c02940c6186440c140000103691140026038448001810628501e058440f0000c2900f090103129543d08102801da910105e4010070140710744803072003001d0103003650704040d04091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 329395296 1250 329394046 329394059
    0x602120a05071e05070c0b0c0304152d09030c0909020406080c030a0803130503040e0601030b010e0a17071502030a140406090e0603150a051e0c0403060b0109031b 71
    0xc0344010480b4040c02101031020300000d0000c0b00800426206082c80f5444005509003c41c0d0310985803c94a803800380024180c94280002014000721003d83d078070440341110a1a00700c4006206416005018007c3c0040e1404092180b46e4405220050318001d1569a030325282c480700b000e51580540c000300e5440300303a00250300305809901d003d800e03984001c1c42c14400358400700c0d603618644400a42041c0021000c1341d00010301e107a2600c90746801101700e139202d40c0c590201c042403031015030300140881d19203100064039500034403081248000c0108200c2260346003a0488007107011386800c04c0024001c0300004100c0ca50902003003a21101030381e00854692441410191041e00320300c0c0c102a18000c2400100f10541c0d1100110041c1c48010951407101c0d200d90011a281c400039a401d80740291210040159040c405c2d40b11a215007232280e120591550300b0300c4440500d01c8e00380e0340c50541800c20030003400442c000d90020594a001850000701859407600c801e000006103003854450040868002c0142 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 329396546 1250 329395296 329395301
    0xe030109060e2a060304030903170310080a0b1902071b1a0c0309130b040504141204030308060904030e0603010b0307030b041a0d05070b0f03010e07210e0a0602120a 72
    0x101c2e075145400560034020302d0740c42d810b148060f0100301c0c8200b0000000504240c802c0245c0d0340103581c403a249581d0070300c00041c02e401c01d03003044440c1d84a00c00b0400740001c6285000400401c4a500080700750115100c0c0c02d90320705198032030318850045603020040c000008820f500d9611b8059101300c03920709980d06110310b504410300042c41c0358404034424860218410004030880d81c41620071900b03d40c02b0b4410400c1c4802400c50051501e500074070f0a02000180301c03100000454100080003030703403d1005402d0300032460340114000540062403400024185092520710250040d00a0038081e013a402d51000052203940b09800251020101100303000749039402d4020700655140c00ca40500c400382c501a0003e0820001030b520a03c22208850400305100c0c00380500345c0500b00d050309059413aa151145807001e41e10030b12411000240c90400600d1451090007045100c0c1030143e01c494120900d041102d002d008030240e600000c4c000c80c0481000210540300906114940079280e02181ca0070700d414808 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 329397796 1250 329396546 329396563
    0x30b01050f0a020c2701152c040b0402031b031e010b0a030b041803030203041703090312010503010603020105030115022d1c020d0f0c02060a02030705070b040503030301030f030e030109060e 83
    0xb00031942012440d104405c1030440c156020003800213084030a144041781c0a00503500d4081d800d8885071000d00000c1e62074449160280c81c1075a0510000448405202c203e00c821590307040c4034060300c684d007151140c10070000c5030840300501060a03c100c1c0868444904402070b4032081039004002130706a0015058010f4071305800d4101c3d0104070010001d030815500c6c2c4220b2400600300f40d400000101040301900c0c40003424042100e03850b8981c41e00c03905550380d0342d01240c07140c004c91500c04000503480c64140580003c0e80c0d41a9502402c591030113041200322502c0c03400c0d00055003e042e0807a030500b400d02c156500c1d00880030902c8003072400d0015205040c9940d40c41a2001017540480c90282d481c1c0028040c40600c80c1850035080a1418060841e14855080c0c0003d50001c400141c182d020740c0d000003c2d15026000340c05503a00503a54055020b06441a0701c87c0c1609500b00784010404201040031004403e80242010001c00b068000002d0841d8481101111003070745e0f4040003043d502e0200701409 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 329399046 1250 329397796 329397829
    0x150f0406201209010c02010507050105090f01060b030603030d1508011a04050604021905090f0a03050a06050702030a020705012a0c060908120912150c04090b0105120403030b01050f0a020c 82
    0x10750a02d80411402c030921407805102c0c14000e00301c00b005c085910071002c03070f241290040002c0055041492600781c40340c1c0c8254681c0115820108045540c4055100301c070301841c4010000e52602d034103d4000c2020b402040114280c8104034100040d082200703014107203191030304504021071802c2c14001c2208039072020b000c0c3d03401540f0500c01c112010040f89000310442da01800d2050b00c5117100400030b803100d801c403c00e240e0842c8042d0800420000006054109030b4459003050080740d840c1c43c03007207981f80949213441e001a40b0162041142e940503e03102100160300000110680240542403190302d448070301700b09c94600e02a1403c00c1a15449a02c00001c1c12840d4050006158244024076180c09031080c491706c540c4000119007501c5c60104514883e8002a10f4a000140351001442c14503030418862820902c2c2400c00051107980308204032440392050a02c490b440d5103513610101d00820480e15694180201081301111246a0764080c0400041a60003002d91408502c107005046d01942a0341 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 329400296 1250 329399046 329399053
    0x2011b08150112060506040311030d1b082101080a1106040b040311040209040510090b060415030e0c060414011403060303030f071205010e01060f1409150f040620 71
    0x811842030799040301828020900c1c0164881e002e8800b03c0380185010344c011940500300140c0042001344629800307078240011415600300f050911b03000c0c3c0d481d050352100700032803541c040c840d0800543d441d8040c0215020b800321341b031103808d07110400b2814214281c00c0f51641d40d0200d40d0076010009404000e04107200d080d40d03d07a080c5807034050341a145010b2804000e01c96407140d0425103003910b9a03819103450181c020300501c005d040c1030041400b000028050606c0340c40c2007554200003800c0c058202d80455160303c2076805210789480e4104d0080092000381c6080303000d503160000c3d00d5070f03400c0040e1029003160324907a5840d9a4400002d011401050f9060390356403014010082541d901105407030f0b0158051100068503560303c4802c0b03c00d040720700040281c00e492f207000410340c032081170000ca061b03441603121420b56503240213007515001d02c001c40c0c0048919082095100c00d040c84142d80c01b0707250880b100941008203022001e29a070300680c03c804002480c18484000480e202280148a54000e1016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 329401546 1250 329400296 329400301
    0xa050415051b4303140f01050c1204030e0d051e010e0307060e100e01022104150b0a0308030406150b0408030f0313050a05060105010f11071404091202011b08 69
    0x20000492402e03449003200580440810303448400800e0741c3c82440a540509070380c015120718040502450707940c02108140315404212604000510405020b00c83d2410f09606101e25048404040080180b007182080070280400102c0e4030b540f503c55010b14440c5008c0e000d085030b020803883d0051031800000003035a04058010000c4a008411501050303040b03500130420302c4484000f10315003e800010310a8142c5441c07810210182e066011b071080c4054000038411310f0310798410149140d0340549019000421102801c5c0940c04107501c151110a400307410489020f64a49465034103030030441e000e030b851a8882d0714071041072121214207806000e1060842d418207080800465680c00340f5035264680c40d4000010a40c442400c1c0d2a4940c0554401e0445d10310010a10700139032608020300c145404159811455440e0034040c1c40c0e00301c0200c600200900c20b0515000d20101c86000c04202a40c22580da2111940440d0283c09503515545d0160000b00384013010202e0203411030081c20a403810800f08406 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 329402796 1250 329401546 329401573
    0x30a0519060f0302060f09090123013b13060e0c0c030f0307120204140102070918030309060b090906090c060f0a08071202040f030303110a0c080a050415051b 69
    0x2e4a41500d80503070750355458242904810b4094071032040e000f41e00014410000400b803100308030806401c0c00c11220352042044210056400507045028101c00015080d074800c0b40307001009100442d8422454418808072900000c02d0101d070784684809000c3e17442da031082c042c1d030720031418094003c0511003181e03241040001002da12405444642c402c0c1000000c00b2440c000c0c4105074880c0401c9500508550710f583d00c0c0b140d1421000361100d018054003401d0740c00a0307000441c0c4503040114500c0030400d002c03000c2c16079049000b4048103408603019617603141d900480da10b4204c0e481e442140410000c00c1182030a00c0a685000b203012107030b520403681000300f1401e040c002402d4640d44042c0b03045c00d110301d484020080c0d4003905604c1103071810030301c041130009412a000d004141103d000352801c1202e01880b811840c01403050f64003242c00700391040252800901020001d1401241d40c1c5841803e094454100441180301c07000c194000840101d0103030303144010000304460303601c100d500030441d4103400003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 329404046 1250 329402796 329402819
    0x30212060a060509061e03180c1002030a0309080d06030813090506010c0308041a0910060909050a0206071703270f12030903040e0c04080f0d081b070602030a051906 72
    0x2802c20b400740c0400300c1c8131407014142030360b8501b600769507003002070300d0740341002404070400c9989003800e0440c07181ca50241003504100d00399800c4400d06501075843e00c03500c01010b0303003e00b490407812248400c1c20004000100110b00c80c2034017961180600319680c0c0801c2c98102c102c1c54441d0484407005140c0400d0051a82c0c0045400a11591605001c240c6036558105050303203c040006201c105232000082043c00c080c0807403540e04204103808100461134840000d08108c48000740e00078420381c00042a44050b203031110141600f1486143c0d5510101c4807200e500d03849810a030f407440d4400b01540c0884000010800d8040204000b01d4002c1c6a101041d10303005688041030401d8100b00380000011a0703660781d05000302c0e8081d200b00c11180340c0900b4001c144044650080c4140003160040d0480180e400c0408201c4074002056951340d02000d80310151440c0d86400403541602c4460001c0250b0380009129001852103020302144c0041e0314500b9504c4030f000808807031340003040340d0b190000500c441000003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 329405296 1250 329404046 329404057
    0x140424020606191a0d050403110727020c030c0703050102040320090708061c0b1006080405030f030c16080a030b0a1a070c091409070b09010909020d0603060c030212060a0605 76
    0x100c0f00d81119441c4c0d07a0001c0041d2144d14944240c2c40d05000400042c550404d01160880c4405001c5400c46555080c0000d007040e803c0302103120101c51182d0002286c80d164024052560a5900346c038502083c0c101c0c2c4615200c0c056204603030f80c0e500400d0030020700001c0030000750007400b06c800305441442c84030001000c00320000c01e15400d0181c000041403c83d203608000e85006229820030600340200c50510001c0b051080b1800601039440a00c013107100c6104140c00c41c0125444001503080410702c00824155800c000d0000b0351605080c4811850500301c640f0300350fa228010011142e4034030480100070199003a901d80c40e80600c01c0180300700400f140280080440d250b5002d06e140e1100081d04e8a4003500045030712018216040404030107400c0f02c2c25400c2c900445142045880361944e800a40300107000d80c01c071960124500e21000c100c0b01c481d5400034055200b000100050380707902d179030361036080340c4581503810002540481d4400c10381c1700c0d0141c101e030000e070120ac02e0082c2c1850002c0080162065 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 329406546 1250 329405296 329405309
    0x30b09010308121e011e170a030c030c061104080d09051323090304060f0e0907080901020c0607050d0b0103050f01031103120715050115020d14042402060619 69
    0x8000540580405100c02c10302c1c03072000380c0c10440e542e40b842d0500190240001d548030000c0e44906c00903104a0702440c0c0c90386148002d0142950081d2138400342c031075611003441031f02804071440c0324200141580c40740750810026550a10348540c144282d0500e0203030010098804d101c1443c03002d0099640d44018040441594600460341030302007980e410007014141404465110400705100300c0490100c090016181c203a074409940c1d10500700201e07180c540d030200d400c1d040b005442c04030349c1c0c2030b125a00c0e5079800742e182000913160689a0003203074900103040312141c0000d01c01089180213003406d4020104070401c2440c0510941c1481d518150a030038061000031303c0070521200a00c03031350b1020303c01151010f5082641585591302814020026040c05850000d043c3c9800300201ea0040c0c2d161103c0d01521035580289441204c604054070815002082940c0c1540280300004130045003525800348905404c291440c941d010850103481e040740506000d21845044850080407407030283c001c0c003101c29 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 329407796 1250 329406546 329406577
    0xf2d031e02030d2919030b0c12070815040614060d15060203120f27010f0603050307061401061d06040509070503100608010501020d03200403050607030b09010308 71
    0x2400030342640707984150200d2010305810880308901c642d11031104015280440e5955401c0c8040150400007442c00355032010900031001403051011403401100e4a03030242411034400e18050110034005031400701140c00f40001000c0d00308000f01c00c1d1802000480c0701d03905940c180b14590418403a4200c04604132226809440e011805014040c0190040c0b290548000c2c1c200804a882c0c1000a48075404500c07a0b00031608500701042c0801540b2003507074812003000d4681c500e60300c07403140300c603030380c201c00d034815145a40d01c40c00c0100300c1c50f00070704c6020000d40c8100002d44e5070349190310f07089050352909058085102e0311800100080364022080c900c203909418140c2600d1048540010803e029a030050764014580d10308106c8116001f000443c052020031000e01c0066503070301401c844030340c800d015860041e00314090089103940a508038280c1101c80700c450525641ca111294586030304030b43e105070b807603a00a03801d00c20b00981503c1107500700d43d8191031141e155819a11a410103200e0084081031070318 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 329409046 1250 329407796 329407847
    0x50703030b032b030c1b020609120319081003110d08070804090e010f06030c09020c0309130c08070813021e032b03060f0902090d0f2d03 60
    0x82c0e051040464034103c2030103a460640048810905012110315900d021929040300c1c40200d41c06610103002141100d0480c00d01c2400f41d50910010707803c24030342e640d00000c0d170fa651407100380c40030700c060301c83e0107080c001d1408204040b0070020941c800140c40c031460700e0014142031000c00c4d42040d031f2952603441552031503210440d6240c15940781c85841005802110040b5010950350001c1e04004000f90211340244016807090030f00c903084500700c1c40010100c0da9410340410454045402130132360081e065040d2070805140350702148402d201744810451080d039840d24242d1864100000c681c0092a914014046180c080d48030407059500d540043d10400030071241c00f142d00700c0105a00c6140c200a01522600d00400b10f40307104c1c150441402141c07940046032001903da209100310002c4450300382142c580140362080400017540142c00d595007017007500b0020340c041983c2411060304644a06054103440e00d50710381300030400307150100c1e00c0d00041e210003205010960080c56907420041107800e03502121f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 329410296 1250 329409046 329409049
    0x61e03020309162928110609150f010608010302040216060e070e090c0609040c020304080a081c09050c1e0a060507050f0f0d030504050a08040e060406050907050703030b 74
    0x1c0a03032190960590781440c011440c403541403500030415200e9481091525440315940c01c0d50b01401050345c0055503c116001c81c1150000d502403510305150905644007010b948440e42004402c0b0781e075031200d500880781c4040401c5d00400d044e0b840040402c00c0a819418000c008180d0441840064480c079008201c0444445a510039011810342c40b110401500c0951842c007501c645051146020f0313000c0041c0007902443c40400c40320211131009010328a072195500811008042640103501148801c5c000450420800c1127140c4890740240f003801d03204c00242c6012050f00c19204d038000c1d41d4504100c0444001b80b03001a0017489035108941003100410340303d04022170805c00c00c40c41684603c04336000204250003c009040050199090700e86ca0850450f9480e5141c55018041c00c0307540c002881d61007034501c640d02c0160018401c00c15103560381001c0c0c40e80040d40e003250700b100c01c0e01c00d410420f20101d8a05803152070b0090000351180d2200d4500306074003411500030a0000740600d5162012810319 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 329411546 1250 329410296 329410303
    0xd03050f030c0f031602060603010204080a02120111040b07050d0f080a020c0a0c0b070c090e03120403030b040c0306050316061d03010921080705040e010b250813061e03020309 77
    0x241e120150f4030b81c4a24010410390200c2a8403400ca502500410300410070504041c0221816181240000c20000c0d800d64240009030b884141850304a550701c403003103404000044010001450030003a1680c0b103041c2c0341400c9042070300e00c80c44c80081c0142240600f500603004062a41d0142010ba00103845000700d000d124200031001d1801803031880d080300085440e1050b00c0c0503001260003091611485034503000100202d80020520711015031003440000e180c158505031299006110713141c0400c003030b50040b02007000d0340c44d6a00302d000441d444100034002d50a0402c1448020740340805c0c2d0754520740c03900001400e80d14401d0200284410319612120701c940b800d400040420f82c0c060101040f200c54900c0c49401e89910904003030025201c1404907410302e1082c010f0301c0035502940f071140c080d07074641441c1c1742a42d480384c0d02078804042000003109940c05540840b00002e4003440c040c0b5620f080082c0e481040e81c034103401101c140030f0a800c0482210038101885e8064070054240140d0703c1d11100b8002c1d25 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 329412796 1250 329411546 329411557
    0x50c150408090a030b18030708040e071701030812090d0905040e030c060a0902040c08071e03090b0711060a0c050d15050a03050f070b0f2703010e0303150d03050f030c 73
    0x4109402840010400c104501300a2017001640b90746d0036021003580750552070384a084006030003198180002c2c0284121a0340b60b03a00840d06040608885060f407510f0f1010500981c81520314500214000e034141860318403031030f0b00454290282400e6201442c1c00b070821980360080790f00640e5130f1401d00001d030100300200c070384d00b500d104211a258541185400041e1800c0b01040740224140345020b400719000e0b80c140c17030288400d0340302e280400482c41960191004a6110001090303207030f0000b0b81c08104135440c114004c1580d90b8480c05000a0f10703000d140382c002d0141030f010483d0714260700d02043d5580f13742034a84155085070081036500b1900402000120b9542280d035104958400000030440300007806038400801009850003181d5640613803685001d03201072100602400c004684100a850600613141216145110507030710700300011038215052840190700683c400010300c01c4414810341c01c3c402d98242140c01d40440061941d00034020b01400642e080091004004074100710b01d04d105551 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 329414046 1250 329412796 329412799
    0xd0b0604110d020304050106090203010f0603110403080a0f0e01090501021002031801060f090f0203250306030501020a0f08130c03140f15012903060d02040b060d0903080106050c15040809 82
    0x644462401d61810001e504c01d840440d038035841c1450020340c0130428020b0b2070403501c03c4916191480d2501c030054018060300701420403405d00030400440003408041c00340840016598500ba0710717414495024165190403c0d22034180244801c040083e41e900003030400c2c04a072041c2000d07883c1c0d240c84150808922003c444501154200203000c100500c0c411040301c01c6421401003400f00301a2100d040d0700320701c0300f5030700e221180651240041031918440309200200e4403500d0001240d03582c1e43c59690032600b0804041c000541040030b190412a40900c2d1b15070005a241800c0d20310400329030710034260700114800204101012001f03468800310502c500c81042c00344038103941c180580c15465030004003090291031fa0031110700c80254003002022841d16005440c1482151035078407100708225102c0d01c0c500c000c80c0d106071210038030f45442d243d180182c84134000c6605c01003040c0d540e614002e000c842050308840d08020092100e1040d4041c00240d8204000003501410b0607601c480c1080485071080d002c016 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 329415296 1250 329414046 329414081
    0x150207050f0d0206060102160515210a0501080106050a08031207020f06130b01060804020f19030c0f0e07080405060f040309030506270a050c09130c0311100e0d0b0604 73
    0x42c819540200c3c0a92141d0000d03820b4401003c461303003000605040303d0203601d402c00b070702142e42680d03502c03400300815000744500c0005484165a5a059100301340440f500c5410a49400041142042c240101c802410040784c0c20440603042012003940d9002c4c0590307034015072025030007150400b4000d11204402901e09001d4034010324040d00313103080b0031200b400c003100c20b034502c40300010710903102e031110a0003564014002c0d1201c4503510308100c00c040b44d00304003092841c00000d000000814000981004104213200e9002c86441d14001504030b20004000f00d0502062004000000e507010400540c80482031000300c050340c4aa0604681501d22508010418800da80c00e02000c054852255640660740e0501c01103400741803c8002c3e115a01940000c0055006299200d03852401c000415030110b00c1407244090b0100c0c0d51580c00b800c5d402603006442c0550620103c1340035041c044240c40340003000b4106000c11412801c003081c2c100c185454040d001a50200200355a0791312a000400c8090390515035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 329416546 1250 329415296 329415313
    0x60e060f090a124b0303061809050d05210403020709050c07140c010f0e040b040603030504030507120b0708060f0a06180e0f0f04080405030d030204030204050a0504150207050f 77
    0x2e1402440b201c482e0001001e0400c0ea002d4041600904c12003046400a2074900d01e0101c1d1080740b1180ca014400440502d5103e56010900481d250f070180112070362000041080c8080e424603e04005c41d0300c0d41e19040180400090707800c1c00210800c51280c01d070083e4201c503207688a050481c03c0c06026040888201c0c00c10040c00802d4502e00050001c06002d1401c55066100b81728107269540340c0d40f0540c83c0416220107441c2552800703031048814a2001802c04568240b07440001006c82d02150000c9020400124082c03007442000c100c4200500540c8807904404840d03a2a1240b403080e004008004000007140024040d07190b0b10f990003100c0c14090000a4407503201d0201602c8690141c0fa080380c0401c200da13001405108480d83c2c80c0c0240a4840070403241d407218401e203422090b0082c0240c662031130812001860740c42c2040491013080c01c0d550b0041e195400c40c810802550f00c05413007900b00c141084103000100d01c0c00c200d9820050740503500165913520a00c1c1c4582025186508031140b406040c1c80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 329417796 1250 329416546 329416553
    0xa11010911131e0906060b04030506010611010509150a090c0324020f070b0603190503040612090c180b090118050603060f01060f12020d0e07060e060f090a12 69
    0x41000410400b22509074040c00342d1080c1c8002c8814041801e1100b008900da094030b41c80e400e40c014110640180c00100c0d184d51904c201d80700560103070f4001c40f034a030300c941c00402c80582e001907100c405000c04002800036081c00d6203555922103810101c04090440700f40802c0c5103030b0050348044021940140c03070032092550703803e0036401000c1840b41c81b103080c402d0315040300100d450380c42200e08440c0301e00d20160400f0110f80f61598181001000706400d48690030741c0c01d18000c071482002c16102d200310300940d91981071040007810104228556034403641403202440020b40800d007007100340d801c0301914075038043c018034400c009850030486180d00071428070004929403004c148612001d03d200c80341400907494040501d503031044110342a10ba09118400103102d030750f115420108010009280641d8004006000141241c0c03040c2608800306940d480d4603504068280a410002c120900780418402c7c00c131343c00b18680340300740000050740c4030000502c83c5c00741d40d401e0a840046c03c3c0904003240c101a0514 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 329419046 1250 329417796 329417813
    0x20106030618030c0807020a031704090b090412080a111204050c060705070902160c081c181e09020c030409111603080601020f0d02240609010501050a110109 69
    0x1a80c01c6802e0074420b150003228114040c145642c10b545401c4545555140c185058100c41803c0764082c0300e031355001001c101c01481d260f04030750100c0c1100d60b4461070100d621040760910000140242c011808020104154829128216609007003a900c1aa030303c14640d0010100604555000c2c04040341680b00420007141461249120707400301c5a075404000704101d0310b4007811900400542c08420b0034000c00000c1c0c0c0203008408200000d60b0000d40003640d40c858020b41d070780c01407032381d5502c00c1d403d0030008415040030310f01324200b03130401c1407000c41d45030f10703001e0105242c2c000c004d590502c5489000300008110307200c10003000c6074481191030320132181c03409407640d10612821803000c0c10408252000008035040f6481c0004919051404120540d0187e41007040204405d0544c0030300080d0281d4441c1c103005220500b03c4a034040e000d140b0001035000e0f981c0a04500814010101104101c1c00d6114201c0b003c1c1960f500342072154540b900703080c003152404115070010701103508103440c40d010044400e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 329420296 1250 329419046 329419049
    0x6080a05060a2117181e04110c060f0c18060c0a060b0112110d0902180c0912011a1504080706080411010503090a20030609030304060b03190b0a1b020106 67
    0x59101c1310a8060004102000c2e010728070244000e6400029003085502d40354200c00041c3c03a61042c071400c0021501d000404903000421041881c4100160342c1c4480d200512004d40d020410a658003014185048841098060389100307207100d15840407a00c25568440d401c1d80d00d0b071403480d411a04100c50384e190682c042c09141100328007190300c0c298004c00210b81070054980c03449001c400142800c00001d00070000e000752107001d80c2c01a114901c07080350000001509841407024440b05175940c03003080c0c2440140060f854a85140da40740040440c100c081812016141460485494420420241e090311580c880d96214991600c1740f000c000420941281d4003510071401058581d120b00c00e10001900da603c07084400c0c04080c2c0006142d003001503102550a5a46004040420090246807000c82c0c45c107041607495030320642c40841040100107490086c42161071081d40909041c0b40300c200681d044018204009001c2c0c110380d400107a03851802d9110422501032248482044131300150064000d0505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 329421546 1250 329420296 329420303
    0x5030f0901080c070f12030e0109110306060103090b0a0221090a0c0e040803270a030903020a0512030a0c0f0b130b100b0405040e0c04140a0b0a06080a05060a21 70
    0x50760a240c050f064450290308002410103001711659641201d074207030450b01c1d0034140d40e8010f0a050714400d204400045218614056250140c98101441d142004041c241094106080140061501d40039160490600c602c00b41c1c403020b1440d880716a50141c07040710305401d00c20305c081203510400024051001ca00403508450b800f51184101c001d6070004a8015260500402c0410034010b24420328400c907200d406100719905004c41911030a009106000350000b88030558107200703504e411105100140002c581c4135400c43c1c0e810a020f40c49005200c1c5020622141844034018403000301882c590030340e8030000c09130844c44d0600303500d0b8a849001000b9160a500c42c000101407880356a200c1054500d10380c0380a09240c901820000a014a860080d0880c06414180042030720386008501c0386544a44202d60030b4546105084100c0d010b039a405845003400300b43c00c00006400c551b040c2d8002c42c3c080c10102c1c456480d04040303103c40710141c0c48104402c0f1690903000c0c4485a5030030700d0081ca4070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 329422796 1250 329421546 329421557
    0x90a080c1501090c0c1407030203070f0501020c2b031e051207230706060b0316110c01080604020306041e0b0f04051501051b01050103050313060513030204050a0905030f0901 76
    0x300c440043c411030f00141c0010000c0740c008500720011801c448100003c45903074808499113580c036a401319050103035a034440f1200e890784400a008568041c041d0441c03042c010789603041d81e140e241f00701c14002480c100d94130400c181600e07060300038103104103010320300d110f42000040c270b074844152002480740d444010000030307a0790000042074420f40320f010210314a18100c540f02e14a108884540030072540481d800f00c0d03070313039655a0000910351a85000f6521589d240b441410340324441c840040c00c3c2c010035900c441031030b8000c5010a003040c0e801c20880c0e50440410f0310b0050b2650341e181d010400030000c250700c10280c4016201614100111070700000010302d8241c40d40e1000200a006000a0360026120f1064038140403102c0b61140d4030480c054110818142c4061410780211000b17503003112070a81054980f0303040080c803c0c0e520b03c40c00403c603000306003503c1e0941c6442e40c01d03081900c1c02c159600000748105d440354041651a4041e80002d50700703070340140540b595000d1500011000b41d00c00d050207030208a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 329424046 1250 329422796 329422799
    0x21303051912080603060411180a06030201090b0408030a030b010c020301020c0109060b1206040b09010b101e1d040c090515070c0e04030c0b09150405060702070509090d0503090a080c1501 82
    0x1e200b103d0070ba0080a001e03005009645aa0340c030342c0c24244400b0075094008094086219400c801d96003c2d0740100703400040007600c03d0650000421420890f0071403451040304000c20070481c1000000c950021060303160004441070b140340100d03440a80c01c64047d606600200d0002004c07801035001512192044104010840001c024480c0984081d07540c104590802c4001030041206548400d80c0070442c0d400000740703070b62a00002400346c01c2d810180000101600d8004024016850a0700161811405c1030040c2081014410002c500c00c1d044460040e42c030350f44ca881d0030f10f0140c6c129602920000301551301c50a0b000111010f0364000c01d1041e1303901c0c0039001c070004012103040000e901071a05a5a2140b09100c10380b00d080e02a08041c0502c0414424030b00218550407601032100d008501c240040c00e03840c203200c039000f440c0000307541205116070703000d40c24804a500001824095840241011605d82e5144143c480c145002d03004094000315002903810b114130004100d90035400d07200086000280d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 329425296 1250 329424046 329424083
    0x14040306020307051216020703060203060604080304030503120c03010f0b07021306060210060518060d0f08040e04050f0c060a0323010311090114010806060d09020409050d1d090a0213030519 83
    0x1103a00d5886c0016800140301400452240e070000c51f88542d0242071945050f81e10109075103035a00c580c3c010354080d0408110b011084181c1c0f40d142e50040c844645440c2154109402e5580c0548241311b2280800b0001a500b0215103642c01c0050301c40c1181903081040d56034178040039440b051000d044403915417030107401203020310b00300301c02c00c02c61b0001002c0b0700116900c013002e0000c0720707032186001c3d44c03280c600d00f1015000900d550018009081003a60903421400d161a00c1403500081610b092602e03004000b441401c0d484a00540d40d4000b8585400f168003404840c17010710910f58605241ca20301361210000c0203100343c0d10803454601c0020794032043e56a0741c95091006019540c281340e0b00203049900465003514201001d00302c0310f424808000342c0a0901d60009003141c0905004a805401420b180503c1c0c1c4c3d001070016128040000351014041507201c00100702200040a1400c81580840d6040685407015118000b45074083c040311024683e40d403400750708402080b400c031002c014620940454 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 329426546 1250 329425296 329425321
    0x2010e100e0d0c0b0705090102120a050d29151303080901090e0f0c071a07170a060803090904060603080a0207230d02090604110d0b030d030c0f140403060203070512 72
    0x10750b80c108450b40195101d59000700d40c00e52051f142141140b103103c141c80c1ca5010114000c001ca07046503100c050703540540504c00000d803017490302d00c2d4240b034210b01e5501c400f4800b000e410102e0148101c445c1340c446d85a081d1410f615019010400d5031100b010300000c41048100c10041017401d2090300d525640c940e0b1078070362070503426003180e800c405070341c2c008046a15020ba02c005400380c1c520648582c0541c1da40c1524040c100030301210b0703200003d50002220b012090134070320920380080304d60301c081c0080350900413a907903244070340364544d0700a82c0340301d000400340012540604080c5a00c10307600750761102d20440007592403000e8025880d0b0441c02244c800c40c42040901000780e842c0700a00224070400080d000c104500c900105203541150301c2d0705400f0051900c0000070211442c00c2400002c500c40350340149442c014080c6c0540c03042c580b4000d000700b14981c00490702ca9103c002407a080b1124070b08071300680c01c0c6000701da000502950000c01403090560708030020307290040d407826a4034155690310000621 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 329427796 1250 329426546 329426567
    0x40f061815060f0f2016050f0102030412060204080303090319171807050418050c0312030c07061803030f050609040b070f0203160303050105100315090c02010e100e0d 73
    0x464030ba20803100f80203009402450b9500d41c1c82c00c198015001008151040015029244980340c00050305150400c40c2c0c00712100182000390398000c440c4980c038001030354911840c015038800702c940d0f404074010040c6035011203019190f440700f40d0f512400d01d5009180d40fa00903a1036481d681007080c0c120740d10079105440540648400400d80c045944911790201a0492120680714160140401c040b505842d540502810039043e4529581c0e031080f0b50500a040c0340359041103a1007034007c605143c25a0421030150303030b001901013154035540c0e402032401d4030007007407002c5903a41e461044e034070040203040d0103a0252002c19440501404207503101c0701000760018003194014600319240000c6049180f24030803601e9060b11500440b4a400080f01e128450002600d0048000988039070040c0040e041c0f880d4040200384050409012212050f662604014002d0040c0001950385022070071010b4801d41080d03030014001803e079148070b0202481c00c000391042d10700c0e801440c820007a9030080305201e01d00c2d005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 329429046 1250 329427796 329427809
    0xa120c0609090e060604090302030c0d020f012007020105160f0809120604021503090106030b180f0703050304090908090414090106060c0206030f0c070209070512130b070c02040f061815 81
    0x707175250000c000040400c44402c0c2c0451100744509010303540200031004242201b80c00030100418000f6440d801d46014100c00819103c9650021258080d0030040d10310250382402c01070f07141d01410840314198044e1304806020485000c6030f510500881200034154804151075020303075035030b50102440e072310310050b1402504981424040d039003000707410015581015210001003040b039074a807200c154400d0282d4034280311281e080d6011746012400c000c000024900c1c90082c1c91501d1540e26203548a00861040c4815251140400010000c600b01240c3d140c1400420400400f03580c84104041d41c4000c0f40e8a00b05503180c218003084007805140500c10481d40140850319503500c0749a40982c0341c0c4003500e1030031440c406021910041e80c6040c90140b1507152540e4040e00c407240340001220b02003001e0442c104501c0d511080a0201c1c64500382d29a0151081c00d01c0f01403c982c0388040340050041064000c0905c1c680840400d52a0609001c0c03101c801e4880014001203445091400800d0158420308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 329430296 1250 329429046 329429053
    0x3050c01030504060b150c011b0804030f030b061809060f0d080d1107050a03020d09030c03061a132909060d0614010f0e092a0a120c0609090e 62
    0x915031180e0000ca500030f1142a01281140c40d440100301199126100c92040703240108840c15505424814040300b0310b5080352850b8490071000005e07080601c05800a0104204001c082c0340450194110003200c0e10040c04256503032250075011030310146141401072091540030049580c03072900c00b4204020b41c00051610171013048075510b103006544800760421000e5142e40c03d0302c600a980b940544041805207001c0d1843c5071013450000c0c18860306015100c18004203120500c0843d80003070429007a40e510800010b40d0450121448030b940200450305030380020b0380c0e05d1804c1400b0b035642206d9454207105c040c4452303140290804a420201d00340603503400020744800148c551605500040c2c442c1d01882c030004000681160004401009030017141034001d00f00300420a08505410700e95000c403000018020303400300c4440109420024071281d0150303091302c0300c5860003561190007110042040070100300c0004900d1400f550882d0891268402044801000056402660044040c0451003e019 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 329431546 1250 329430296 329430313
    0x501050901030f0e161707080c040b0409120306060e1e0f0d0803090105060108060d0c140102030f21070f051c020403120c150902090c03070309080301120317010305 72
    0x110000d000c03d400111006403200c69a60350705400f407048004d040c4640104412580c181607900b0780070b05401400310b5103a4446c5c00100901e00011980481003102103402080d01c60203000000c000d480c040c1000f420b51400c078035681452a03003681c0702ea011190542c9511005640344800c10142d4010130f9180e11b400026400f400206251030002c1e01d028070720050030044004207903114ad40d4590421104003009a5560052007041d60700160965406541140c11001c40740890740c504007180300c50710580182d00c101c40c001c00e10300e03070091040d42e602080c401161601c1b41c0c03400141d030b10748506a11071040e00d0141500480d500f50f10401c040743c2d0202113612401d1500010038151808c40310102100407030141d080c44080700103010281d2600c40c0e18465a034043c0c1000603414207522101205814842c180d29245001006813078a02d40d9070350188580160a0f100d1340e8080702a0050011143d0040c003c100c0000041000f003411003541c0341c007a01a035906191540381d005105240d078401c0c0000342966006194 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 329432796 1250 329431546 329431549
    0x30a0b0a051b0c0a0209010906060c020409141902090c0c07150507020d03020303091006050a050609030f012c0105281506090303030b030106060e1201090f03080f0f0105010509 77
    0x45241c0110301410b40c81050050590400141c0d040740c4500700c400e4100c1c900d4041035180000d80039001d061006810010a40b4082e409419003089100007800b458440342c880e02030180842ca100340c0080e41c001968500d1101900303907111480a00700807407250700c10700041a1481c00c46010b40307020212110080403020b080440d40c0e903901c0c01481b0013904100c0d0070403a80c40180c442030111103040784260002d603180d00304a0031903810300c015440d1504407a45070520801071130355102e00c54001c984050700c138603a5803003010000c80e060104400b0404503030340c20b0104090504290401030310200703141030110000d803005a425542626020707034000c2010600031010407803224540461003000c2c411410000740381403464049082c00340700c981c0404081200c00c2010800e050f05401a100d20300c00440c02000514101310001d801704c451003070640c1c000c0021050704070404e0000d5000850303464101c018020410031504e0000c0401c84100d07104880c0c141200c1c0400c6040054000b00b506039031051710b825081c80b95040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 329434046 1250 329432796 329432801
    0x1d030306120c130501060e040507020c04231509090309030601090e19060203071101091509020d0f080304030e12061807090509010b041d06010315020d020a08070806030a0b0a 76
    0x4006071103020b400d00d40e801c15075448121021403078540c2c4022449624000d03025282100040700b050280d410002040152640800c0882103400c0458000980303041d01700c13040410007104d141400160a620f0140803000e407c8121310708982c041101c0c078420079983e1045881e2a4001d07400401c0d0949d003d8001072200f8020390300b1605990028500302c07001960074203c0500c80d02164002074501590000602229a501084440038205424020300032801240d542d4007110704481e841d030f411a65104030507021591104080d40c191504083d242085840034144a0b000398030581b0100e0100d1181510440241041d43e2004e003c0c149850250580b1b07914400748a140102e038138004003190140c8100810307070080d140b0485d4003c40302c1e0b02c000111200380078140021903411600412000612a03a48c4a068800180c140d0641f1781c0003c61a1480411084000190103441740c0c542d191400810a2404654040491131103180940e4035143e03141c40352401e040c1c03075080214001d0002c103210400141c4244d4a47c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 329435296 1250 329434046 329434069
    0x180c0f071b1a09041e02030f010302040606091a131805012c070c0203120408060405060702030325090e0702150a020301150c020a03021011010c0801060903030309111e03011d030306 79
    0x306001010b45c2c2c4843c46100890b03004071982c11a00e55007800600c03c2d81058842d03c4003a001034200b13191902d0810400c1e111100c0710001c0501c00c04c0000400c01c00707402d21004400014100500b01881d86003451482c0ca01502090040794000c64413103042c03204451186156062084240c0c20301b40300c1e502e40100c1100d60001000c000d0381c0510511003902c41402c0410020401020b214000d058903003010b00d03003141003001c00791030302c004c540c018801d001960b05100130b0aa100b00c5019102c800318100200e064400d10401d90006541000c5031003003008403070300401d400d07000700c1c01400c04081c19900c4442c0c03802280000e0003200140040404114441405080d0700c4100030f000800c4903440741c2e42d84d4002801e0300074103401680041c07040c0000d0302d05000300b4094984d40c0030341420f1103d019811320800802d0a40c0900c000740405880d0345207003060101548013031403c0c03100500018419182903d40d49010310001d81c45038040d610748150383d1447c0e444000c13034030b001310030300006545192540400c003c10040e20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 329436546 1250 329435296 329435321
    0xa0201120203041a0c04080c060903070e091939091d19120309020306040b0c130f06090906030c17120703020a02010807030506180c0f071b1a0904 64
    0x11383c041c81320f0704015452014410b050140c0b065648604020b640e81c06d04150000050296405000c5000d195a01040c80d1080d1100316004165a41e81c001c5121b01c0d0004081e103801c02017040c41c041030b0601c1084446245c0040002d0320b055500042c01c1c5070078424410b45d0b00d810440103118801440f0040b01074102040414604030b640cbd5243c149000c40504000160603140720020740044a4400c2000c0e94040c009402c030941020000d0b00203580200340c1b690b10091004120b810320000080c160314000302501d0b00300c0181020580c645480b12000d10001400307005010101346180310024140300f06009a00941742d222510000c5146002d4a11101705a10307070394031032a4003451004011220420000c1c110241c040c4d401402c4140c058000502a044090442c80425007001c0400c900764550a1154400a01030030081e02c44e40c0e87c081c010001801584440c0c440407000141c001d0a121400025115420056401e85003140d500c05015a040c1d188200907507820a0500c0340314042d2802d90f004500f54050f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 329437796 1250 329436546 329436563
    0x13090c0c1a0103060c0503040c03060c12090b0711070f1404060506070f02040510030f350403020a0e01150509030c180f0105030303070212070f0507030b01090c020a020112020304 78
    0x19503682a07000958880407441030020240100140800c5004d00c0d2003a40c00e03800c02501e94206902c0b010f0000c9081e000140105480c0c103540082a84034080c3e03c041c2d42c44e040000c118920180c54120f01901007035076210b0003c0c560040d141008440840c402044604505245551510703080716140c4810311842ca180d806070f56040c002603103485800040011520075402c48031214810720400c81120b0f00503154180300b0400c1c4400780001008060304001a940101031b0394075120119419100e070400b04500060441d1100a481c8500c10703803503002d0820f89108440b40382d046900e82c1084080382d0400d2140c0d03c042c1000f104d0b44000c040c0520002d100800d009020744540145140119100c10401106582080000410419000e0851281a01500003200a140346003000d120080d0394001c4074001c011881e000103080400c0151700c2c0059045283d12400b0f07112180c0e90707401c200f09080000d00c542c1c02c0c0e41e42411500b17a01a0b10100b00034100320360503151444200c00c0104070070700039000108222503128 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 329439046 1250 329437796 329437817
    0x60305151c0f03080a0f270c03050304060905040b040207020d031b050327030d0207090e010608010501080307031d01020a030f020f0a06020d0b0103020f0d050402130e070302100513090c 81
    0x41102030148000c5020343c96500d2030f070a0003a401022200184012903c00d0b00c0e20552100c6da1501065400c1f01e0803890b002c41c01200c05038100080f0f4003c00d0b500080040c0b10001d00020110340000028040305d0044400700702051042e014003060b44944031b4001e51060070300c008440020b000720340c1c510440e04d1040100060303100381c1c0d0758030380b541c0c1c005541c541728070300c68072075034100d24080c40056954a001500504aa6084004080d42e10801070049240e001d80310300c00021411001d5000e0001000d072040240010b5964a062648a81c0941815070026030220841c1d9100f943c507459840060710183c2c0282103441d00c544044030501d0107a9041c0d07086025810358003006240070490b000c44a8024000140e451200e014020116080c400645040c14018480344007011065010b44118000d1030801042076036a43c4002031081e0300208007158590f18206200c001c40d00005840070030340e0320a4400441310091300c1000d0785d6070300a0107104011150355810620420382e0b03503002100e81e2505828110f00a2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 329440296 1250 329439046 329439053
    0x150703060f0b030a021c05071d01031509051e0c090a08070807050108061c051501080d021e0a050d05030a060e0405030319110d0213170d0f0e1309020901060305151c 72
    0x1f40c41c103464000c00075107240e411100b142515910074284003001d00301000091440340d803a00084076248560707140d0344d64810002d90300410020403820740b02841007a00354103140142107545150040b62580340514100b40c2d000c500100001088415188960001d146141c17030000110350101c4020301c000e40003100070b00ea5199001c51061103040c5680b04001500d05140e50000c4802806016444204c0071350001c40d200500c29000f140e03003c000b1406100801b8545010303492180f500d045444020f1040c441e40e0241c0e0099680030780554018000c400d4103203c10342e61010324242007007003920080e1413034000300042a40d1281d2078842c0809144568404100201d0b4036004124940080d0700c200c1c402e54001030500070090751041140b015003500307442030820300d040320300361541c0c1c3e0660703400502442140d00d0140035a0b401580354100c000c000500d070400d540c00d511320a201030080403c0c103d02079000c03140045511402401581e108100c0c084c410041c103800441046101007000f4603200e5052004008140030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 329441546 1250 329440296 329440301
    0x16050f0409050a060302130b01020f030415112409070e10090b03070b04090b031504120507060b0604030f05010e0c09270d03050105091e07050a02030903150703060f0b030a021c 77
    0x54013401000243c0c0c00518001a0405900000310bc4807608104401d00c01c2c2c0312030350400c5884840034071701900548541420f8514054002c0d01c0e201410911750440780d1014200c1c81501c2c407a064a0081d244101e40d103194012102030240c503c0f0307114522860050041ca5074991000c12113440040885081e00c0c2d03100310a5070740b5401904244a52074a8031540440d504040150b05241c00c40c84000c1e6009103420385611202c154841d40d24020031000050746024003480ba008001c3c1c0020080c41250713a25070381d03d0304101a40714407000300d95550804566643c4890042240c2092240c0601051001c0d512100d5220300a40c0c3c400c1081c0c0c0440074111400414141003140101d10b80c9603460000300d0394100800c001000a005001604014001d240c2210720301500102c43c0d0054490b0406948481188105a00314020b401a041d0540700355501c56a141440803111809561141c9040140d0fa4448641150b1280c160107610040c81c0104003280d0599140d900401042000b8103106415040ca481d07000103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 329442796 1250 329441546 329441569
    0x12051006091d060d0614010806180307050a0215040312080105100807020c01050a0314040c030b06031209041505060304050a1106040501020318030703080f0c06010605070210142116050f0409050a060302 88
    0x15554040d03400c206a00b01d0503040c0613102d07400ae00081d81440741565a9940d9a02400c000074040e54410a4155400010400340c8020315071081c03015901506000300203249000911a040c412008a141401c04600076004580504000d501400800c040d400054600d580408400e4040590320300644400008003000719004503c1041180344281c03a50030000c900d5a0050102440f80d0010758003101000144000c45400703d0b0191004588040c1d0b10107070108040c50390b131040c0e41001c4c00008020401c0300c007040c41c0e803815200303a00000954113440140005405540181800340e40100701000f00a004054944071440f4018110756210342c62356144441c0b40c00141c0c61108002c80480ca00503d60310030301c83c80703024024602e00709060605c2034000861628a04480320306004582c650001d81c8003124040f100c440000440d01602d9030f4004092000210341101c3c81000c0182c030ba0442c00d062407044080724403e8494048290400e414010300070020303c0c014104500e080c0c0d0719000000140c5641a2603c3c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 329444046 1250 329442796 329442809
    0xe101107090914010213061b02040c0c0b0a0b03030d1e02040605070312090201090b0d090803070c11120a150615030605040c08010e0a090312051006091d060d061401 72
    0x9000c882a24000c01240440d62074a00d0f0359005001009802ca0440b00b41000c4422501c1c01d400c842c8101c09015441420a07003004e90028240007000c420141c0008819000c240701e81c1103001c2603502c400a4801b220344101219a040d0400c205144002030726412183c5051218085110344103c01c041240884e8090b0388603d012031808100e810502d600620f844d094400724070428400720740140e000030000c070b4003030107851400d14021800c4841c1120583c043c044a55002003607a91f241483c60014000070038491701100d00e184c0070110382807503080016a604005500b00000c2c0400076087c0d8035249248500c1030310f6000ca96540c64006144425000b040e9400b041030f84001500b18142024002a5a4044030403001d210f14040104400c1d0346010809602100c1220001040032007403408844084d00720300780c1541542058140008003402c0c2003150100c1d4400c0e00d50b005c040780d0710108210f030094840d6020401460940014403181000c4121011041c4101000110114449150800500e081c0c1142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 329445296 1250 329444046 329444051
    0x30206150f042408010e060c0f1303060e01200703051e03010303090603111303030e0105070b0c03060306160207060f090503011e060f030c150c0b010303081905070e10110709 76
    0x260fa010071104014040b40300c001e11402c40b00702c2003a5500d21000d00400e03101c03800000c03c001200c061000342c4e800710003508250030409544e030400a0180c140110a003259520340148460290200f1402c04c202100101810703003000425201a603582c1c2005e0703031b16050050062081078017035010000440c040d52280d02c50042040c204803008040b41d540b09071801c50f030081045000c1c451000b211048049990614107640d0080030140100c0705801030150003444828000e0a2158081d6224091841a00168129412640d074031204040700d03800240c0003030260b0402d07141801581c2c420000421161814200400850341d6034001c40d017114040416406021482e80d200c01d060242c50040000801c4881050b41c0d07842d0458850108a030650300c1341c00800718010040c2020b160040014100c003907000703950455030750796030300700640252030443c0c10301c1700302c010301c007000c1011003c6214941c021221540d9032a540315400003031080610f00c10358131000340f10b5682c800b03001031502001468080c20310a01d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 329446546 1250 329445296 329445341
    0xf0705060a120209361308030609190204080f161a09010912030c060c02030c10021308010e0303070912080d0b01030f060f050f0d0b1b09030d0518090103030206150f04 73
    0x107501c5d5204020309904030007548003180c0c1c07001c40d681ca070642e134104c601160002480c0d12044041440d44141c040004405030012800184e4400041540710b4a8070490059521000e540f20020b420306a4034085c0e408030014800b2160301141c07a0101410040f0130605005001c00d0701e41e41458158003800308100d0000e40c0d540c0b09241005254003500f83c60780442e000460820a00303104042d103610050340e12401c80e40d800f1410b452180011501c0c81c0007404440c000b00324018545071802c0e22030313001300d510348041070100f00e00143d8085480c010800b80ca82021441e410501c03028100c0d00a49140c2c2425030415481c3c0c0c202011070602ca00c00e01b00140510900ca540b8289071105000b102c9200b43c1c1103030b2140c10000c240f40c0101d401d4248440d031111a5544018980c031000f4418480b50045008083c0c02d0f10504903101c80940e000401404c0c0381500904c41c10040001d10200110400d09000050060f08004042505581030020054052100400032400030000e07002050494405042000c1c00c503900b41ca0b0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 329447796 1250 329446546 329446639
    0x20301090e0f06040b07031a1201090c060f0f0507032102190201110d050408040b0408030306130e0c060306010c060f0219020a0b0f18030c0f0705060a120209 69
    0x1410710803003128018001c3c6140a0301c0351001c105009200005141d12405a01c03481110b0304008440c5000060011010b400b400d0031007070082440f01d004842c0001c450001189490060614400003070507540c0e482030b1072451034021240c0c1d400460045007880704480c0190100b201c600d002410390300d00150010b80b50000e003190492205508801e44096900d0003111300e84d05c0022004540024070000d40114080e1120301c0c000d001c6100c2c540c00450301000202d408103414101000460003030208a031b2200c150400071840030300b1a14401310b40103450b44101400001801c01101859210105040c845000c0105071103003030549121001101c4519400a44109002c5422010304400f19443c401844012004c1d035841402d2003000c1c103554200070b4a03130001034800450b403040c418401201020380303403030b00f51404000c1c2d500c0c1d103240072080c2c0500440700045004e06080c000c3da00b140e05035075a80440e040818500320000d41c800e03402103801012400b05080c03202e0504002c80d5543c581003020b10140700f0301d041c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 329449046 1250 329447796 329447803
    0x103051015080f0d033801050c0f0601030c170a03080703110a05040504050a0209130207050a0c03140c190603021324030b060711010302090127050102060c250510020301090e 76
    0x180314604401c55441c0841c00c0900507910801b00d284070381007101000801c42d0060301c0e540122403000130340d0f1140003d860102d43c4c1c0401e42c241200d11548580b02c070992101460322000c0b125551125180d80195091000301e03101d8008507070040164200040c0e10002c41c1c1000245600061407800800d2000030200202c0c1010f00c24503a1022400c0e50842c1860700d030500041c0c1d4405900c03000910984c012a101060040500c0040802c6903c90290b844c002e50324944441114030700c20700e44416020740c7c598407005007492000e9202680384407958007012414514254020342124403002c0100d80c0748070003c5440c0704007444020241c0c1c0080c0c40c0c0100301c0c99403003009003910400705540340140001d000c1180010602e0351190100c03034090030096111007021303004a8a80c4662500c00c0140c024014001000c0520216980140d0701c0c280d0a4622030754541c80b034055980704601c01c00c15101503004005075041e100c00750036041c44d4422002d5480c14441c03031100701c0a0b40c20a80151103041da94520000b0f0110041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 329450296 1250 329449046 329449061
    0x10090b0a0525020307031212020d1d06070905010f11030a111b0123072027130c08070b0405040b010c020d031202070c030f02010806090103051015080f0d03 68
    0x140c2c1c104201928035404a034540700d9911004160214001e01c2114035405100c1c0210b600d00501d6086444240f0200024007a01031036090701d07007210910071448180f09000c16a148128603c0d100e0600c8507150a00449803c40e4402c10b0f00104282e42004044002c014002081034040c070b9950394a46800f07051f021410040440a05a10b07003548104504850340c101400c440c0c607045400d54400401d1130b130000094a4800c05100410280400110301101107607210fa1030b13070605041d641d100c3c14294032611604030710784074440c0c201c20103c96000a021008038a80b105102481154036040c0540da03144954039100b03054021421020021805010705e04051054000380802440c103100046030303c0d00410030524031200041d080110054007103100c58440d4040715a0140d001e299004440d549007080350860714048412400a24180c0120300b09243c0405014141c035007040c054800c60018000c2e61000309032030360358a040c008003445c0003e400402032002c1c0c90700e001980c020f03004010740d16000a0484805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 329451546 1250 329450296 329450347
    0x14010203030f0c030a0b060a0f1823010216091a0a15080403050915070b0a0203010e010e0613110d05070914150c0d090e070212070210090b0a05 63
    0xe004200407000d120001940003e1603009241d525140c400c4103030b0140040303904640d040400000c001c0d900c10f5000b200544641c51584c0e82015641c01c0171400d00c0003110030b1195007182c0070a41d40e40500510441006400c0c0c0724140100c4110301c0c2d104215050f803c0250380850051a641d01030700010603901740d4013102d048411601c04031420705081030540100e04450700c0d04d080203400c0c3d0000302054054030483e19402c0300104406900f0a4507041d0360002e900003072045502c0800c02c00441c1d403044043c002d8a051301e5540c4080c225036800e1000701c8100c117000405455006c4203080c031840800d4001d204902da48a0100b184996030700000c0c0d2088203581c0041c11100802c0310460040280760a0350408044400b000c43c0c04008504444006040c0360246e40890314050160300c02c3c200d07040381c110100004a4903502d00c0c0d00e216a48801040e40c0340c0b402075650452640b02001650300500c0c1002641403496a14280b103200340c0d40b40c0c07000742e0550700640e1000002c24000103801c03a5134800c821150342603140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 329452796 1250 329451546 329451553
    0x30b1b03040b01031112010509070807080c100c060902090a06060f020a0c06050703020102040f0602010207031806050d0207020d050601030b0601020c040509030f031e040c0905010e041a06150d06140102 88
    0x80070707070b11004500014440909440186859000d1030754070003009068850004000b40818100040c40c1f90b00d441c182e00c9003807507510a112000615540115402002180c014103240207154103070ba040d18401c80080e002c80c0c0b01542c81030102c1c0165100360b48140100100f020004059082150141c81140304040320402d550025103458005542020720074143d40342880e110341c40c2c2c0c4803883c090380a8002d5420410104c0000744c40490301d150705501410116000b0360741d100f04d01150103130703412702c0c082c603800b541000400070051406160180e030020130304548080c0031190480c00d0394403220b08114080c0c000303d03950307a80881030001c5580e04205400140508490410550070842c00e4207589c0c0c4901841d188607003001000041c0c445140c140c0c21010080d000d00c0d800c105103420700e04142c0c0d804130f60160401306464140041404078000d9040c0340b28961000c03406054020400a030440518000d1103070364400350b501340c4460300c0400c06000e40500301e60181c0204459003461203d041211245111504560 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 329454046 1250 329452796 329452801
    0x10312030510061d06070b090c090f0f04080705060906060103150f140307081b031006080c04090c0807060e0f040b0102033001030f060506150703030e010204050901030b1b03 76
    0x60028801103800c0c50134000d1404001a5100014a2403c00c1c51540444d020130004140149400034a2140e00204240d9038010341c0c0c070041090607c1c1c02c1e03501c00d0f8508600400a20001503020310785400c14040d507142c80c00d0541d80d0b0b6443d481c20604544030101a0080400c2c00042d5825004200382904040f5180e5009800c3c0002140c0e00740d0f0a108608035124580710500c0c1d44c0c0c07024072406028200d49016228501440100d07000c90402100324240288135005441e000c2c10603a2203903000f500c10442c064506002450704000290510510940c0d00000c1034a0001c0d658100308941c0000300301c191550f07194450460100b181080c15000080c0c01681011b0750103005a90200450300100c0350b4505444440c4001101d04031000100000500d008002d80c0021050059400030705615030320641c414045d035a10310080c0300c1100c0d0a0342995203040c80a000000000b0702940000d042560001e00042c2016034900005414002c01c0e441074403080c41180901c521030380034540c00c1d6401c03092015081d1450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 329455296 1250 329454046 329454061
    0xa050d0c09230f04060602030406021b0f0f0117011806120c0e0a06080304032a03030f031a0415030b070302030105060d05060609041d160b030c0f071203050103120305 73
    0xe291071107010200b000715a14442969403541c12140c801d0743d018008000d016120180030b99030794000e000b00380c0940300703600c0710640440c0643e40ba0f0f9076004000e482d20341400c049006000c6a0f44440c0c00942c180034514101c48040c11021521600910004503c8005111000003c00440381150400d0640300b00540707020010a589038a03450890782c0032141d1500303903507400078120b000f020a900500c0c1d003804002000014880602d9030000044a448421040c10460401101c0401c5861200401043c9140400c0000b02d00a40c0242ca0f4840c0d0024040c1e055030011000408803240500a10144a0503044c240240506810031a90151003030508520b503506100c0001e600303005003400810545d44900c0021200e45030002564072200000d4024080f140410f03000c010b03608040f413000d041078400e00c04d54100e40c10340b1403891411901c641c482c0901e161203600001034194400100310301255810083c840000b40c0c025222510044140d40000f8254194941018040442200002050704010601410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 329456546 1250 329455296 329455319
    0x10207110105070201090b16020f03030a1e0507050106080d03050c0a0509100504030510271509051e011e050106051801020c0607050601030b010617040303090807080a050d0c09 77
    0x315090a02e140c44405510040b00c8080c110b40050b40c1104000c103c00e41c1d01400078412103440c6100f191740c0e4100200304070a0682e640928000f160008035511001c1402c0440c1c403004050414852600c0741c606900380d1511401c2d10a02d034009600c0d98041e011080740d182d8140b007031980003054084a60700c0c1a000c280000d14502030640010701c260a40501c3e4500c0a0052044600a59010064a03e0302805210480003444003005034102900d00c80b41c2100c80c2c50000c1061900c8030f6022030b9552460201c00c0c80d00f0000d0140312421180341c030514412801c1c01c3c41528a036480e20700c0c84000405c400550800703071004104035620180c0c606040a00500480741c110080e0ba075090164040b0340c6114640d03c0c0104c0ca0110210b00c1140c201c030300080c20606110300800c04505890043c6440030440e662010100c0c0d166160f4030a400014032100080b600280c4290440d224903402203d0650600c4060b41b82c00070113038000280c4001003180055004c80550301405031600f9032519003840c1103000d25102c41100c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 329457796 1250 329456546 329456573
    0x3c09081014040b06041b02061005030105070210110d02071b050a050109120302120d06091103042d12030f0b0f01080a020d0f0f020a0207140a0b0706020c0a110a08010207 74
    0xc0500e02000138050b40343e60b8405260099407402950702108240c00207074480c1816641d0001d1519004000310f11402c05000b294090702071030780200325420300c404100005044080750070ba2026001c12900890520780d00160106074002c1495065800205051010200503a40300c01c0c0203e840d01c604102c160703080102401100e030f0001c5401600056442c049051450108145000c12400310351800e40200940c4850180c400d118410024030903440e0f04c00410340402c075401854640c810007800725020303104a25041005000c00b070b94038440620b6903512840c2c0664055000040d6403904d0720340e140760f40c900415039482000e0320580c1c4100d01071000200546001408940b02540018044541300d1580e072141707000c012101e0741046038203002c941a40103580700302c000600501c108138000c2001c64036072a07400b0003000000e001c1c5803402c2c5003024001d4180c200002c00d884056092000b0410303140705200d5103102da44a0707019552007a00c00782c10081d010803590032261150f0710600c0040e0001c0c10103e00340f80c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 329459046 1250 329457796 329457803
    0x3021209060909040c050a09110405010c0804090c03050f2203111e010603050c190302011407020d0b04030908030f0909060607020a0611011b3c0908101404 68
    0x156035096030408146284928855250015554020041403140004544054540440d00c02c860a035440e4901801e81f04080c14104d498001040100081e41c05105d1070480306110740026414555134000c0c1600310b4002200f0180420b445408001440f80048001039100d04800507400010700080049a408150342c80010300303101c150480310351010300802c0560b0290089a04520510849048032030203803e5500c4201d07101c0c811891141528a02364901c001060a18610614294619001116202008400405202010454900541c440780d20090000c0d000d00460802400d16280081040300a41c0c004110741c0c00a110592241c007000b81100c600020446a181d9561155400a001c51180c035000a41c4480f0349a00029641c2d042212508803690440082241d00031910b4101c407100d07d8001503d00051018401400e180c58203510104615407030001030b07044e902d181540c140d0f400034480311790002c103c1b48402007040700c404000141032000306400500203070084100762220f041000c0c0005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 329460296 1250 329459046 329459083
    0x605030a1104090905031201060903020603040b07051b0307031e0e0d060e160e010b1303030305071101021303060501050f0904021002010902061306080a2705070b03010603050f010e040302 82
    0x4101c1e40d80c490103a8002d0800408108039001242c0350869481e03015524a540500d40c02c000064103600034080c80044039000342a0074a55a1281d4409006080c004c00d242d051007014002c41d0104014280080481071001005640e545654140a403041203600c0952840c42803100b600580654006025154030701c060b9410910f01c03520745014000ba0812003008100792040c40403544a0601001c2503c0c21140f48046503130341a40c851030000038501c58004080c0f401089644c0801c0000d12a40c00580e0180c4a86004400384d03559140203405eaa00030480b02d9580001d8000034001d0044070700c0313805e004003002c49480e1108040c1c0d0011440c010b900400192082c0c04107016006032034000e4000d020744541c0140140d64410b090600d000302e44089001e070000107070242000a01d81e071140e04c1905c0c43c40800c001104401d150700b0071034100c414501d400403502e500480c0000561281030b0009103020740300b1502c0103d11850500104011250140d000d074141d000c0f00024007010940106801402c6004031039603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 329461546 1250 329460296 329460311
    0x70b010311091b1b0703080d020318031926070525020d03030b01090e010e010905010e0712110d02073009030b0a0b120a0b09070303080c090111100504060609060605030a 74
    0x40c1e41c102082c69101508201000503500480002270b8000c5120340801d9000a940c0d40d56451a580c1c2c900421540e06d40c076020900d000200140580d20080880c12210b6100c1070102d202c91b104038050b01c041c0c030401c02041002c01d0700e428000c0540398022014617440d410003507503183e03030f00041d480009100000d0207143e61607551140f00e910035106000030703005050545e00c0c1542c0d01c045075000b8100900ca620350035032500c000800c80515060100f80039907040c0c0c0d00c098203241014030580042c6070080140352200010440740201540500140414600611311a001021501441c0c074594444400609500d03002541044801c0c2e041076401064907000010700720540c1d5100c21000041c00140e811503406140300855420480e0002a00c40300c02d480740c41078904580310324051643d64041404001c020400a00014150203031160203451800e40501d09201c142c00406040c60a115043d09401201505e4004206c20710405004401c020b144a10341008441d190800081c014080505040380294a82c02c0c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 329462796 1250 329461546 329461597
    0x1203070b07090b04030f0203011404020f0915030109060e0c010e0114030c042601060623030c13080714030601060e0d02040f0c021006050d110108070203070b010311091b 74
    0x300400607200d14810160f44548a0410101c1b404020b00c4c100d00c05c0d0f0810142c8086c921041c04000d0056502030b006603c00340500c000c01140c468001c101300c1e41013200c82441c06556509001e1408a540a01d000190006241000750f041c401550102c50600068201065140e44e00904010002c85501078940d03ea8980715403455641c82076a1000f610103444042c0c0d921310561810309100c035004600c008001e0595564801d80b1140303440703044074446100d0000c22a0088500400655001075490900c500e031561080c0f030400b0600c81500561510740c41a44140948940821022448a02100100f40943c50302e400108202d82c94076516001c1d422032540030086466a412440c0c01c0d10b24001c0605c0018101d00f0021b5880308414440d005407420190002002c1c109030b211200c0c00c1da0041032614a9001610055038800c1001c0d2880c4211300c01001014040fa4100203158040d40c41a01610082071401c810054021006032801c50807103180c480040c4911884401c54524a1214410b044070900501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 329464046 1250 329462796 329462807
    0x30307030c12110703230d0f0c050109210f110a02010c080c06010905100b1305061e0409050a0f051e100305060c030103062a030f0f0219020c1203070b07 67
    0xf500b0400074031400401000b00300000c11101c140007015a5030100728140038680365550005000c1603004070300700191140750a0b119480034440e050040700049542d0209644511a04120198800b580441040002070180c0e002c0c440540000c4e10b4605036520007886800541c031401d030044005e040c403d0a40c00b800401c000340d816228480410f1091350025070b52180c580e806440c0444190b010900203020100e14250b045080d00c40540c00c020034440110300303143c144419980510b400c1704411211607501004005904000d0010340300106010806040c45100c0109803201c9410390360715541440204000d1100401e11340ca540d86e18441c0d9078085440d4041c1e4601c44070480d8002500b43c0c0112310800c1684541c2200660480c0c2c4611010025490001d4928031000c62120600b800c2c40c26504a000030b05200b5000201d01400b0041d00255101540880300c049078000c21100c2c0d85201d080c00c038594110b0f0107120140040d2400d0f100b0680c1c4c845501e0030b054036807003089001841100f9040200d103450b8405e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 329465296 1250 329464046 329464067
    0x60709151106070309050d02070e0a0e280606050a03080306150c010212010807061418191d0c0f040501030207060b0a080313150f0e1306060e0f030307030c12 69
    0x1d06407941400c24000003809409002c00c1a90207206a98815402c540b0004849040318822030521199440b0a100400a005d5050000040b0b200d44083c8111100344030306c000030202405c0046001801c032615140054a0b11079200c603100e1020240c0420103d1001d40850350301000071548022025141103161101c1d00500c140c814541d8404555500c8011503840028180c520080403075100503a03c0b101181d50520391020300c220070320103205500c001d1042d61590314080c070b4014001d1205e0a071130145030b2081c4400d54030103aa4200c114001200c07000d045000607802c0a4510130305480c200348c2c041c4c415014881ca210b0141055030015500f130130300c1032650002e403640200518002c0741e10f030b84103c01607a0307030003081c082207265084080004585503905030f1300503080129101c020312031345100000d817030500419018580041d14500110302c1460a07104000142c41e01c0c1e05d401000310a58414041021211464940264000c1041101298000c6501420513130f0004007550441030381403048402e030810 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 329466546 1250 329465296 329465327
    0x8040807120315080a0203100e0a030f02030f030a060e150a2303010c03050402180709030f02041d160b032202130507050703030f050708010510030b0d050f0d0206070915 74
    0x10007078013189030030740419031441550084003100c0051011490302001c0b0781100200d0200c0e030340040c200000090041c6940b11400509006407818401402002c1019a0046901080c0071790348030800d005440d0811a0590008074071740c200c580340d2140c5004100c1d502101d020f010300e001d9400701c03c0d244010f655004c8040e44003020f4020301c22401821402781c0030740025501288141441e113100f022407908442c2552141056641c1c02140350300d980c45a0f03000009104050703802030b807a5080c80d00c24501303241a10380c500c11144018820208400110108550305800810100804009008100c0c2841d60b036012a115803038099200c514440c40004c0003e800106a0070000303013050204002590000c02808845001e51014440300c5108480c16080b190708540100c08160078100501031410003140324207011400e402c0001d00380c1080d80010b0807801d004030042342e01c0d40c0103804075541d0586c14004442c101c04240001c01090803c0307031002c1d001c4c19450192105400340d5000d4030039114801c040c0450302044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 329467796 1250 329466546 329466581
    0xb090c030709021e03090601030f08071e020a1514030c0c0604110f060306091302030106051203210105010c0f0201031506110601050105190806030c09070c12080408071203 75
    0x180c2d50303550400b0303401c9685140c410b045107000034201a81240100c0e485a881e0340084c002c160708690340c030506c440170443d040e50341c05000d20030700000031459501d40e01d003090303051203550107d01c1c00c0c41005114001078000c01c440c0c100360341d12036048a822005001800418200e41034890741c0303002c013521090190f5140000b43d40701d032206000030b020302d9140c60b0680007401d03918000d40c8000e072401d02003217200a0711040e42002c50700002800c00242304070400605403005001050040e501c0e800100c0f035280300000c0020f16080061700180403840106528064200b0450071821507141000203800c0e503001c02005482050001404400c580c4203130f2290309201e0b942e4035007195480e00c3e480d0081c854901d40550301304511415002088030341c056401c3e1208100088400100754414510440340c0c403902070201a0184543c41100f9201d0f40c1d03a80300c0b50b00c01c0d05c481e45d031125041c21904021720800c600c40340131401c4c00185410311020903212000c580d000d58018111052260304884120001c21400202440180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 329469046 1250 329467796 329467799
    0xe030c12030f0108011b05220b04061101051501081003080a0806311107080d020702030601090e0607050a110708030c010f05011805040206041203020114010e040c030b090c0307 77
    0x9000402950180760030b200401201d03030322521014200c400f00310032298050950030140700031074401d0300203044603452400d125140c1c07200341342c0c4556180e280e900482c05030070000c24244207050307000d0000d4000d220420000e00c03840c14414426000b440016102b03a0411989000041c56400c207000300030000d42c1c0c00112155076025807007004011000a0b20920711850544900d074540003404103d40350b122481c81107129244581010000061042c0302e103401c18031100b0311581010441c80c2024081032000ea60340076030b4801c100d00c1094103104050f08150b188501d46007580300540d10015106071b0114041c01c00c607130b46500800c0e0584080c0c00710a041042841902808140e0040c040090044803600300003d100c440955002c0c003007a540240981d40c01d03016214983c14002030300d80c01880d00f0600140c00c00d807070192640c0d00d09800c0d0b15001025070250391651541c04585d5180d191060040000348801d10203802c069407011a41c02283c40041c01800341c1d580480c000345000e01c01000c81000081c200c81035603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 329470296 1250 329469046 329469073
    0x120a0c140a020d0801120c0b0a02010e0105190b06040e01060f200a060609021e070204090506040b04021c0203191e0b0a060e1306111309200a09090e030c 67
    0x144030304003c80000420301000001e4650002d0344191101e80c2c80580100d9040c100815042d03070b40c010710414400c5648648000449510a204280c00b4501344109111000c254800d10b4050b00d854401103030040100708030401c1669050520a8151000c914102c500130045c484210750001d00e42d081d64120b004a1402849016000100d220100384030701d0082c00240e6031207801100301c3c0181d242c00352044881c2d40b4210342d014098401801c140344010b0001945120302c1d11014030b0244115021602d03003a490382070000354907110500b441c4a002c640900e003290701540c0e003c130b42c503102207001c000c40e041981c80e4100304008680e6001282007a0381c54607014500c5840c10f1a80e91800c05407403402c0740610740750000c5410140e10200394811407d45d18596400d15a41e9a5003000b00451440002c51203c00c0c403c1c50304001c41110042d00a140251010507005010007078101111f40701c2402000f0b008041281400e0389801042071012212101c800041c40e40d400106241503204045204240b0b019400649099 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 329471546 1250 329470296 329470303
    0x3070b0705150a020712021507050a020d110f031b0f12070b06150f071a07050306060705012405090a14060f03030705030705070f060c030504140d02031c030c05120a0c140a02 76
    0x42011507015070f81c948418a00382c4075403203064bc0d900016007200c00034498203400342e00070142496210084410780318020310f0080c25500054524020440c01d4070282c0201c01080040401803503407840a07000c44490a4550aa1071140c0340b0f000308402c00c000c0001c0c416036a0180d1542c6000f00f50805995206000b01c8681c085900c42d11044800846c40403810307008480c8060706611520340e07030710790a14648400e801c102003034001110403211592201d0f10f40400200e04003200e15202e100100b01d4803411b080400300038031a40000d00030301c031007450880b0b600302901941060580080e01903c003402440c042c2c0021074110710070020064014800060048200304000441e0400c490309840e400600c551110022101001d02010240c00104140424064115075103c40285040010150b026490741e540c082401c041222600345015280308114018060b054001c109850f031951800d1440c15900c00c94090683d4400b9010141c650f50b200b40022000340503841c8804001000502e4903190300341c0c080c00030340c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 329472796 1250 329471546 329471563
    0x30e060c0318030f0304020918010606050304030908030c0a020f0f0a0e0916030302030306190e04120809011503122a02130506030c010c0c0504110903070b0705150a02071202 76
    0x101042c0819140e0400b11000c800e80b8202c1481c1c01d0310a140d602c494003002000071000d00301203c00200394031401d003030306070901c286001800240c4485e500c034501400d02409407080703503122568030b4008100400314243c0214004810300d5044914031035049000c000300b0000008503401d2074001e40004800705a2080d500c150710303c580304550441da0700c08044c0407200000d403568400100943e2060012804a150040300640120602e550103000182c2e01c242692101300c5c15602510080042c00e0903280c41c0764042c20031544003000000070700076001c01500c415400b058901c4040c00c41d40c0b191451405480c0b00d0340d9154001d80c1032a00d41d0031140300401090038171a07003c000483c452142407080c1d00b0b1000003401000d00c107800050140001c2c040c1c482c010f42c0c15070315500e022114203410030404141c42d5a81d120fa0b41401c44454134080d15441c81c1000d2620b0300180b90400c264010301400800f000641c00224501180f00d50301b07ea0610fa2a1121541d000c0d0050b6000205070105043c051420141d00041a59 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 329474046 1250 329472796 329472811
    0x5181c02010f0c030615030b130902040908030f1509101701060f06050415020c090a050714180102010612260405100e010e010e030d0e060d1d12040608070c0201030e060c03 75
    0x120701602000e42c02c540e65440340c650030414400241703c2c1400d09a0ac034040d0240042c00100b0504041c0c3d840103950343c011110200840390400901c4050f03010400130400092003034500818a0800c03c0f4079200c10002e51064509200894801e103040220a400242c01440b550702d40003d11515080003405a800074001c800f82c800601e0f4601400900c0083c18002d45140038010f8002c0d0f071114401000504030007486c100603c29041114122480d102005203002e81141c2c00c203000c0011190002030035100280e0100842403180c020002c040b404803c02010651000b45918900c0b4102c1a03804101d4004d5a00c81d9078812061142d098280d03800c030103030002c0014240c4e5141d008240c1000150384110341c1a681c180c059008800d0441c8542c0580211210b21400802c0d0030300302150300d25101c0a13100c16030a0682c2c102c02000160040650410100c0f03800340c0e511001d41c2c101400d2510003080070300028103c0040001030300e90007080d640a0b50080d0915403091060710700350701d004008100558425510107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 329475296 1250 329474046 329474069
    0x3060c090306150d030e0d02090a0f0c11060c03091e1b06160b0601050d0510031e15050711010e0601180e030f0a090806040b01030605181c02010f0c0306 67
    0x1299020f80140249802c00000d10055080c2195201212200d151200c1030313410072a40450000541d90300c8044a12400d03044502280f0b442d04000d42c9002d542c2410340384424002c40c00c4803070182d108007003400e40c0d12200240141d51079130b07540040f0510b082115500305070801000000b001011002107402804c1010040e41641600070500510900384681600c1840d02e84034211401d00003501c02c10004e41242c030524060341040445203111045960a507481d079540c03c0b0b446010410810305051400300e011001e0101c0e03495202c00e49a926150f0580851024071554030310000d041c16020f071284052555492008111015600140d5a5070310782c01c0c041e400742d220000c032124840300b00f14042c51000011b484050b41c18030580c1042041c070341d040003d00b00184201da80020030116000c02c1010712070390003000c0c005015455401c000d411900007502e18054180c00425641c0c891340009002035801c0f20740e100c11240001c119004900600304840c1941440c0d0419100c603107001d5041e00310701c058481c003200b00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 329476546 1250 329475296 329475301
    0xf02010306061b0210050d021c05161b05100f0b2434030f1205060901050108270c010e0a06091a0d0c0906180e0109020a02030903060c090306 62
    0x10b903008070500f481c5070024858508501c0040c03d000c1d005411504040c142641040e800141e4a016608004240c9080002c1d8019903000042d40d40659508026090020555402c0044000380010160700c0e411860142c80a00c010800c40108202c13840003c0c2d000c02041901400d0052030054440fa5800030301c03440305803850035590178590f088402d40194180d9140d00d0240340015601d000d04035000c1c04507070400d1421141142c0604070f06090140c2c2d02c25035400c4800d00e1422405400c6051403d6000070440c80e0004100741341d29110507490541c2c07002d080010701c0340da4441b554958075106042c1c0b600b0440c0e16066248145000142c40015200c09803615461050714800b806507109403881108005000c299081010400010b0503400d03001030503410514081501080b041070740c0300941c03040e001441e030050400402e50710003283c2c0c900c0d8116001a000240c5004c628201080c2c0600504034625070001d00c0200d294003c200b21003580034042c082c0e490134a002410f010b40b60700a0503410b40207020301d600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 329477796 1250 329476546 329476559
    0x207061a0901060509010309020a031704080d050304020f0f131401050301180c03020d030c0c0f05040e030c061b130e0105010e060c0a12030f02030a1505040b030a0b0a0b0d0f02010306 80
    0x4100b4103854042e0342e428240380d0761200450207800c0c01402a600103400f0751010010540703400d81035801c5018200043d5075246001e00d40c0e4517000c007080038102045011b1051000503510070b0100c06101d80102c51640104515000040b00c9035005096100424070305200030042240541260b81203c500320020880650030001c42159032076003501c0140b0a40031004180018034203d020f40b1701c0d25001e40b07086a80c49240e56035100c0d100300365802206030204404020800341c41c060246c0d030544c01684000c1d5082c81034071060309540f0b6034050b2a4000c4aa080c0040c2e46060085400b900d400080740101c0e0f00a0503560400845c4d551070038020980014000c09984c2c0c50707403e00307a044452080e082001084100e41540303d18154050800d210020181ca82c0301e07038401040680007031405980c04640000d041c10701400d002c00c0c00079607a442070b802203040c6903070880d0741d40d4089100310100b5002410700704140e40300c11401004244858a456110100c0c011400074404010a510700c0103200785c0b03040020702d0321200f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 329479046 1250 329477796 329477809
    0xa02030709180f050c090903070b010510020a031d19050a0603050603030a0516150c0e03060702030d230906100b070b010603090528020310061a18040207061a 69
    0x1021002d803001054a0000a2400b803800d00d02c00c1e005a0a0750090380c5540c2c009140840e003640d605469a001055100a220310006d243d4010901140c610716040c000240107920340352104c90160030300121010031850f4080c0c0999030313546064014202291641200204e0b85c0303168030b80c02114041d40102d030020803214000d100d81405a01d00800135402d112401c50119003c1d400314010410080c507440f08800001d00d00e5001d8103c41d2504500402c9845c9884030040c6501024a0b142d403181d4845424011990b4022048400e06050341001045101c4c0061000810f4030307040b0001c440040003601004000304012540f03c1c000c411400a99004c9176460f05c1a4416000b0028081d04a1007841c004002c2180030b6480300702c0543c03080703081e2084111000751007030504040001038440921140700004c00c515043c0042841c0b20840081080100d050207102210692405a1781c036020f4030004190222403070130740104124200003802555610740c503141480c0034181c01c00709194065070a400d141160b19060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 329480296 1250 329479046 329479061
    0x9170c100b010905090712062301020624030f03030106030203011a0f030a021c0e07090b09010e130f0507080c01030b310b13020703020601081605210d020a02030709 72
    0x140c3d5209250303802c1a00704601c2d62000345c508801e00c046a10b1024110486005100051100c01180b2007030394900c0079920010034400003040c0c1107401070401c0006041d495228043c0051403588848400042c0402007031030018940e046a00c01c3c80040000501a6499001103060301ea050154600326420f0b0841c15502e03018205250084001c02d2000921047d4264060025803440030011164424a1100e004c21180c00400102454002e4a4203200c900c421340a0200e48040555141c0d1442d03142c606c1044030f500020702180504d01e202240f910502a007420011210340d000340a5400a0b59180041562800ca864040340802c0c2003080d868264500782012009038640252a18030880a5100d009031641c1c0e0207690201c1c1503911f560100c550344803501d0032440d07042102d000580da107400742400f07840c11405a1000c1410b900c28000b03621341800c0e005001048a005569802050040070006a940b90301000c0780344e0316204402a07854416400031311061f042c0e0080d0203a800c2c1c0fa45400c0b40308180d03400c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 329481546 1250 329480296 329480299
    0x30212030705100507050403060e0c01030b06120103120e03030406030c0e0a0b0d0504020102120a1d091303030e10180308070e0a0b21180d0201051608090109170c100b 73
    0x384080f0a0184d041076174003009925041e032400c1d0700c0341d0b5040c0032210381e2003100101354070007802d484042d44c06102d0340900603012282241406044142c6501e0781405020040030218418514007106001c0c04c1c80b91f101001c001d050b00d49490b02c817400140106202010000028180083c0c00c2050800b1130080303060b901c0381222286404a901c41003030190101400c228110720444159085204070240500341400080e551f241541042c0026404c001100e01c120a1242c20f401040c080400794410150502c80c0e41030801180e103450074aa0700d41000518824090502d0078042c860184182c4032192245251003034880540e20f8071004000c9400013000e00800b90820361115042c48184213410152000b45180791200303100d04840303460491801401d640070a0a0f04d05000810003104090000178415410381c1f000304460300e0300543c6181c101e0202842c034802e10403040c001c52895002900000111900300b0034404900c40c020780c03000da19602600da8081540179001c0c00002d8100c0901618101c140c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 329482796 1250 329481546 329481553
    0x80d03050a0216020f010207030b010f0e0a0e03070b13060507080a0f0e120d091b15020604020105070206031801110c10060f05041d01050901060f14090c0d060b0310030212030705 78
    0xf60741d00780300561103d000f2680c15440f0320000000061040070f990781c040d2449900503c03010b403800c06008010300300a000061030504001c1ea4491051000007501c54136500600e0300c0c080da4440d840252103000d070b001000b81c140b07030802c01040000c40d08621054000c0c888150204000101900a0402c032000030810154070f070080f101e16910a141c03200035024440703800900085400071540e0f00880000900300b21915144103440402c190702003011400350410050019281a15103079000a200c0d06c156100288600ba011021071000c0c0360509a141c46058180020420302c6103820010350950806a00001c25100b0f001c00403a0350038103402400304407000341c0e1418056504000800000c1d1103424144442c038040c851140c07085900c02d0003510b0044580e00000514141442c000c52a044a81d401c02c400750080e48484a04a44030782c505a1b030b0100d0b90020300341e03d4001044580d405002c080d8004151098080240300c075414100c2c50138000c80740300321024210340c920f01205548900810402414580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 329484046 1250 329482796 329482837
    0x22050703060b1c0c14060c0601090501052e050d020c0f0109061a010207030204090f020d0305031e0f0402010309080c0a0309050a0501111b030c09070f120b0d060209040b0a080d03050a02 81
    0x890b007515040e040d5001b000e0600b41002c6003550303850002c099119002c665190300040145080403c1806010240d1405241000740c401c042040d042980242c4070041050005017103440250039410384051065030000c0d1496484403400140c00f8051801c400d951241c42d20300700b5210b080720003244801e007440c1038007d080101d185801b00300003424a8941551020400092000180c5c0c41190320303040c003482626244e459041c03045201070b11005c0814100c8281d072108040c0b080d805020042c03541d0041d030920380403900b51110725040c001401030b54691100c9101d0b0f42e14100405030040d06420546c1c006850600026946000446850700700d20080580d07038000702420081e0102c0700c4c16880802601500f1a0300d03010006010504200007203c4a4000859200701c1c080001c2c0e00c0490740b51507508035403040c48510581d800151b00c90b000100010a055400030300702045031507540040311401c400a001d01102c558a001158a6150b1940f01c203002a241c00b00107507106041d423082d034840346001e00e0300144a5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 329485296 1250 329484046 329484059
    0x30a1205040f02090103120e0a061b02120303090d1403012d081c0f0c05060601030f060810020a02070906030f0f050a02150a09080705060322050703060b1c0c 69
    0x500d000392058441c0056020764402584a00f8200e9000314814416003804200d040002841c500b0300301d918612842141c0360400c0f000f5841001c5100f55220040c5400c409485880054814288403c2d41d07805400301104016550304003290341002e00c103154440180907010040054200c0c4001d00030101401c1c0381d00e07510000140414881c644842c03089411040c47c5450752211407030503000041c8414440341081480e0b00f5281d0040b80021100c0030303810401d49070f02465866580b03e03200100050704259032141c00786d0300341e0141d0304610018008601692290b441c24800b102c040d51165600c0005481101000601d1003030910822040301c3c0c201c440d0b030040d0015540c0300c031140c40740354109840310301c100300005000d61f84224002005545407c001030341c8140c2e83c180500515401e0b0710100154001c01c00801980d1a0401102ea011804000c40c0864401107641c0807820302521001a0562190507004420407006a002c00d0f14408100c541210790f0704007040381d1512a012100c010040c603100002084036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 329486546 1250 329485296 329485301
    0x70f0b0310030f0501050403030e0a12050918010803040f0f060207031e0210030b150f030a020c0f03030a0509011a01050901232b0506030604120909060323030a12 71
    0x108010103080310800380d0301d072900f070310071010784200b0749550350741d1401c0c481010303014803551154500a00151112443d42c0d00d50300d07040f401d0503055801b800400030b140d2000f561403000c00c0341c440d143c1c0e56190641e56180e03295150340390414090040d0386034030307040007080118000c02c0c580215031041c2d00621a15040d0380d5001b11601c52507900c50180e015039042c10005960350a0500c2c80b40c00256400690501160100a14920089060b408000041080b840207590f080c0c2241e80c40b42030a20003580d10b0b05405000b520b8004100e207000081e020210500083c000c85400c03ca000b4450a0003d01c0180500244801450183e504450200b1401c018481444d405102030300900661504c074246060320728044008035601401081e000000320019014032602c09081080d4a080c1c01e039400c01003440c0c92008284c1c2c4000180024041182407070b40d980515204804000243c0580842440f130143d507840d211074820030901580c150070a044a040641c0500081034035418002607907541d5407419010000d100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 329487796 1250 329486546 329486551
    0x3060c090301021b0a1101030209030c09040812040305030403080603060c040e04170a030903020f07051503090109060f020414030c010f21020403030f0f0503011a03060d06060e1602070f0b03 83
    0x20555001c1c00484c803500806500c40c022003204a01074403484610780b800700c28096844000134141441400b40c01c4190302c0c0010000b401034416284228107880f54101052203004220300c0d012040180c1f020401015031181c05103005921a0701d4901c115100c0d1401c00d0740f103080886400a100308107010402c0b44c0d21030103d4540d0490302a09031050b8800c0d451180e151290700580807040841e458800070004c25504218140b50248000301030708400c3d0602000407140b0400310018040400040041150704100307520940c04103520050400070b00c01d10120700b0029410600c182c041144c0700c40003a42460801182c91450142e0594400e2100070701c0003810b40b00d0b055180c80000c403c1c000d0080c00c942d541210b200600c050760198a55424001244200502c1000d602c40940c08010050004019882a03006020115058100d840b40c403079a5074000301e10b44120140c00505041c0c1414070001d00c48904140e03c46c0034000070408401303418004501079986450038401c071401124801d508001c000d415401668 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 329489046 1250 329487796 329487799
    0xb03061c03050c0601080f21030109020f131d06030307120f0c02031609060f0609030807030e061c0b040b09160903050a0302060907050103090b04120e06040305071e0503060c09 77
    0x1401d0a2696003851325090b0240c0150000da03122011501002d20200044071245150b504405541052104030110b60300043c8584005541c000c90680045460001656420740306101c407600c24958802c61040d070b030002780740d1140d08001003d000c80c14504001c0100c0320040e8100c1d090700100b4030001011103040c4080c0286070308000011b00001c0050303400b0b222000b0b110100030506c40e0810308020303040b8100d413025030010729003a00c01030701045015000480742007240c0c1c100709580d0705d80c181030505030748401a8841c0f0b03a40c80100007803240618001403c0315044182c4240041004030308030001c0c00701704d40000104560201100700095611030a00301490240185858030310719483e520ba58076854490404801c8001d83c00910030004030303ca04000307003001004c1c00d01e814071942107a61a41ca41d9001c3c0500054001d580d5110701400703540c01640405c80c0d0110161009070f60f01d9490800c180c070341605020b4074201d01c43c1000c07101c81100411303400500740d403402030280966817a1000c00490716400b4944a5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 329490296 1250 329489046 329489057
    0xc0b06151308030705060f04020901060c060b060301120501060824100305010207050312160906111e0a050106120203030429040e06271f0b040b130b03061c03 69
    0x4180d40e01c951418000340102c80056860f015a40342c8142041c00007440c1c0d500c8404101d00304805680c401191034119809400c1c5081e5440140c1003c0028142951146030004d000000000700d02149800c01c000d0140544000c00c6400d4942c901c3c41d80b41c282c00900f10700301c0c2185460b0070407442c0c15481d01a03002102e80740c44000e00c980d40d980340d60990300710f5042500c11303070000302d90610b452461140c03156210705080140729140c1d900325400b8042c0c040c0d5004d91010009107100324103d60004100c2c0900100080804042444880d15074554541c50700e10208c0710740d4204000041c0c206182c5030380344800b6900030b005c0d506203401d020028a890300402c6c1c1d00e0050740d0400d45804184841c020041c800b0785603080c52080b8a00d0b0500c24011603400308100c0c1a40d0341c1d44066001d10b6803170502002904028560580541031725106402ca04003911600302c1e00962400090000300343e044540100300c0f00080c0240181c0e60365a401d49010140421100e0341d8104884500a2209040303800c21244818400d0406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 329491546 1250 329490296 329490307
    0x1050f160e061c020702130203060102061303020114010f090c1e140f030c0d0b010f020c09090c040501090c08010803070b04030e13020c150a0b0d1106040308280c0b0615 74
    0x441070038100d0001d03e1103da400141c500960604c1704407800312507007101c015460350800b100000d5540000600412030401d20000400030907200390050f084104624800c03c42550b1201c1844240000a100d40c0c001d2a180618041d40d80d07026940020031103005000001034060801030554103c96408900340b0308007000c110720f80d070000c0038201840c021021800c406071254181000e150844417a180c1403410310200348600c008032940003884848882090354280380a49807081300920341014480702030750003800d14001044404031580449401292999040304a903600d51943c0e840748660305000d080c240c0d40600107400310b07010354100c4000c0c807c00340003409802c00541c2c0240480e084403001c0040c680110100c11007441c1640642ca40002d000c0100700308441c441800a102d08100c0d82c1e000b40940f0f0100005083c81e0756410030703130f0011904001d80a94581c0c19004c503030090300400c0349118104660412a8031100c0c4aa4142c084031030707100082d1084c949542d81000318000a036070005400d0b140400c40b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 329492796 1250 329491546 329491567
    0x1a01091205120304060e0c0103180f03030e030a02032a0d140702060c06100609150c020301091e1401020301030803010603090c050402190809120406080a060305010c090801050f160e06 80
    0x15132085001d15070008410481d01c80a070300b40750822103410304050501e8000c0300407d01901000ca101584800710f607082c1303569480c054010702481282d140780c9000101e040280c0540110041c89060224141c10400411030408002d01c0c20182280140b190f1020740d070a00c0d840e0180c0180d0382c04200c407401140c20200e060b0f00180c5142c0c007500c0042502c2c0c10a1052000c40d0210142d01805040740e4106119200c4c00e19020300564203589400e5003c210b510365815003551020b50009c21405d070412b510840503541d10078200d211304004101110100b040c034411400401c818429281a658000c40c00d0b031459283c00c0c4202d002d0849410180d80004502e100014541d4440c0700a081a80300d201040b80c1c1030819420281c90708070010a5840541c00c00603201c8007810790070044505544407403c000986486012107400100510341000b1311640c03030306143c0740409811190513011251480000d1015030f4400050032501402618041c0c20840b8501400444030b004071890344040b58090070060400f0054032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 329494046 1250 329492796 329492833
    0x11b05070609080d0801140d030c060504080403020102061305060105012703030906030b0a050604150908070303030b1309020306010302060306010c050312160c031205040213051503011a01091205 85
    0xa001c0310105007240c030204201d800901c88403c1111080c01c00c4100c0b5854420098541010448a641701d0f100580e140d00400d03000d402c41e2220103400c40404c228500c0c0c0342c5031071440f03503110307010a0380944941c100044402ca294034803203c62903031020240c00d40b0f918000065070380500c40c520641000000010504010540700b00c008001d42c000d603180032046151000c0541200c5c0850070300c0380181401e000c20311154480c01d048404848a0300c581c0c0d110f0118480701110400c06581000106001c0c100f800400c2c9a4190458070540ca42102c0316200d084000104404680c540f010003501500110010005468810040c2d0303480130041c1001e40c40800c05646e001c0c1154880b009811800d140c560a220180070031b07002c010350100690520000806403503c000d040344a100c0d110000c1d0301c7c0c0b03540000e0115162041d4280705904a000184603038100688808190410f01c20101d0103507180960485010743c680d840400d408034103840349680c4e103040c4542c01c3c0c2340c1d002502042d240c62081280000740d10401c1c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 329495296 1250 329494046 329494049
    0xd1b23010b10020304081b0d120201020406200604060c051308060f010b072022050f0f060a1403010608160e070914040b0103090501020d1a0a060e011b0507 68
    0x5800003030000054010851041d10100d012401c40d4001d1000703100d104000154840b440d50705480c21005031074a4400034480103407528000b002509044a0281036a40540241c801c0d51007585911503000706010340e20b040c41a12000032220f43c0e01c40000310300130500790340c01408000c80c0f914241d841c0403000e0700c04011022082d4000c0c0c0c00c41d0b01007020480fa5801e82c2594a02505440422914100319610b40c4498240a40380710300e141d84442c000c121240d0b5400c1e09018900320190880d040c0003200321200c0000b00030885440103150898400690700100c4802000d100b03a000134035101c070751820905100707136a1244444842d01503580e91004202d2000070003001440045544500f0112800d10300000854140135083e1818850510300038009403000340743c4010b40c0d04003910005204a04a401280500085030001e80107510018000c41e51581c02c3e0001180c035100c0401c02080d4099100c02c0c4249004c042c07240f000040e00a544183c2158030404844d10103484400140d000700a45845a6040c00200d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 329496402 1106 329495296 329495363
    0x90201090312020a021512161b02040b1203300f25081e010b090402130e01140108010512070501030c020111040f030b06030d1b 56
    0x1c101307404644d80c004040a21010030024400e540790700c1000d03071280601c0c030f21300015680d10300d03101c19803100c01269036031004409030441d0451b90758103030b440126842522504880455a510409201d0a1b08494003841da1a42a4081e80c440305c00d0041c8001c4550101480304d0120048501c540741d07001d50900000ca019a9407190240141580c0034003868010a505900310031191380020614810301c5c2810161403900c100b941c40c46a00c40b401d01c10401c18100400c9404d240b820580c003d804000c80c2c055040c0708413070f2145e01d11481c00209800144a081010318004540c0da4000300442c0100020746017001c0d2109c101c001c3c41d84031141402030506060f100d42c044602c5901c00d511000c009400544125260703603c0700611640089584400c3e40d0741030640700450040e203004595005002050340f1404480c108521101c040004160000c3c1c403c041d040ca000c80710403c019054280d8800f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 329316546 329496402 := by
  have h0 := BRFrame.cov_init 329316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 329316546 ≤ n) (h2 : n < 329496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
