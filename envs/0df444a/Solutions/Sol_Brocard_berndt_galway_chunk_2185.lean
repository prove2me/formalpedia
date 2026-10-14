-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2185
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:55:18.283727+00:00
-- url     : https://prove2.me/submissions/a42965f5-5242-46b2-8511-793f6f715bdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 392805755 ≤ n < 392985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 392807005 1250 392805755 392805769
    0x150307051309052701020c030f040e010b0a080402090403030b060d0b090603030304020d1704030c0608150405040b0a1e05151305010e070e031527010e030a200d0c0c06020d0e 76
    0x41003130183d550034032a00c0500e0300244010036074501d60728a0190748a050100c1c50103401c4060b048103416030701c248a1405c003650030900a941058045601100d103070b0b12841d08401400c1181c490075006000810702184940480e0802d00303500c0780c119481920350b680c0e81c061664900086402039440302d00c00182202140c07112000e900b41e1808d1007010b52406441e515825813004075070b400500014604000c002444101503030101429004071424065400c00f9100d00d01d07a080e0140205610b0742c0d9544250f501060022507048280510090a04c62841d00c2501461011000342c0e034075000300354a480a0490301a0342c8a002d068494180001004c0d8841440486107040101460340c1c151244406e11040107141c1d10b40c4611503070012421180005074011203c0c1446501c942e950010781c103102820200020100030795a00303680604d42041d6402d554598503080c240c05504c0190180541694800036075400745200007000e004240d0812080d5480100700e07603807001c49201c0f40004481841020040c60241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 392808255 1250 392807005 392807071
    0x1614030a210c0c060c0c08190b060f04090503040e0f100911120901050702010b0d0302030f2515050612060612011b1e110d0e15030705130905 62
    0x4a45003412031003990b150f144486494001e68042094000c4450400a00b03000d0380c1d01421075000542048021014400b01a03440082c000f040e810001d0002400390310f561172403081c0d840006000740940405030920301c3d100d40c000d0140b88800c8540000003400c4000b001030321401075048413600604949496600d0005200c01400d44c80002810010700c0d6100d1608d060b190f004070b01c800000101c4c0d04111101a00312000100750a0260010f4111380001c2030300442034074100d00c5a018440d40e142c11202d00200300209541c049605c20442c41c42190034000028040d50841e8000101045982c030741d001000b904034002c224030469039006400080c0181001405030192907031020010619103801c550000070403140d085103800040d51220340211455070103520740f05c020454244004041500e020140d02c41c0b41c0d84118400740901c1c0d240707440320b41d00d8100f0f441490120020401341c50741001d01c401417035540030030402c000c0000300e07032804500204148074050140b40f02103511048001d0428001d204c0f08010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 392809505 1250 392808255 392808257
    0x1f1b1407030903060c0201050f060907230c03120103050607030b150715061e05121518100f0b0312190203070c1202031b0d06090809031614030a21 64
    0xe1080040042c03105d0055210700c845a40004c103141c0b8102c0b40b00c80740c00b28000c1503030384621048030600550715008035480241605c03114194800d80e04104455010348550041c034812031000046600c02c1004503c4180e05980c421019100c00d500c4a11003242610541c4442c0d40d4031114107940e161840ba80c1c040100240e901c140307071004816036203c0c0d01c181100c4d038940c0440d8000c2c00e031070b00c020442048522a44041c01003110070406038490b00c11142d60340c01e44452014048030790407000ca04007140080d501d8000f016a001195482d0310380c40010350241c5644d0746c0c011181d42c1052000d400b289808110840c0c80c030040b01005040c455a00c08040b03049007880d001d903055000411500d0041000791409401800d01035440703207001d05131841031610380044030200d4581c20138510403140560340d40b403d03c5000340380c0080c000300ea40c200782d0a00070348a1060440d0680d062061000170103c0b8801c001c42581100d0610810803a056000070074140c03918103041d8000c0c51040d80d081c0200e0504121342d5400c41003806 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 392810755 1250 392809505 392809517
    0x402151606090b06040606030e0c0d03020307050304090c0f03020903151503240c0313020f01090e071206050d05030d020d0e19020405011409040204050a020c1f1b140703 74
    0xc64580000321000c140040c0c0b10651450100b144500305400b840300240903916080110707034074212401303442e43c8121041610900e050a80701e030915200304261440c494001003966074503960740d48807200800d441700e010804584102259800140280b0a480c000040500a043d140c0c0707002d1243d002194009084100307040e071000b0f8004064400300b058000241e06880356500d13024000d44202185a0018421a580041001007004142180401001d070583c140d41c41c0d5544051140182d40100700e40c1c001a0a18514101b0040030a074014121003540342050070070032a094983e010301080c084a0f4901030150740c8208580701c00d0114a40c0200400f04c005e20001a641010510884c1000d007000710750307000d10340342c044003005524091180310700400c1e00403100b4040b0501035002c9058850014000307032045540e0030004003091850340480b02000080810780300481d01385100152241b80d040c4840a00503e00401c125008001c8207501c10b102040c0d448000c488403c2142c00945a03100174012010804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 392812005 1250 392810755 392810797
    0x603050c0424140703050304110913080a170403020c0f030d05120c04030804030b011a0301150305040c15020d021011030c0c0111160210030605010e040e0703050a050d080a05040215 79
    0xd10b005010128829a1b0f9030b540d904050900c42c0d000344443c1c41907441f0b19061000c3c448651505048080300c19405201540c582005050a4600c0f1885881c910f1154000008000c01c15030b0204441020708022a0845540d0011034181980c2e00c10714a5401e01280b0104084000e071582c800095070300000c0101c3c11803400e502e81e62100710f00e0b0401d03030003150754a0140005220204280101c40d008484c00e54104e800e6624158440150b0700b180c0e0300007000e0640e610301160034031002e0107610003d00300200c030803400c011480100940e112001c0c85020018040c8511051000c03400f40102246950048402c1e420742d1156940b22445502802d112943e540d629003540c804081c0d964090305240d41c442d1043c0559400b10b006110507042035455400c20149000c80030b110f240c0c1c1140620399a00c4007524000f0b80c0000d40c0320064a41107058202038030611490010104000e000607905010070041d5940c202d4948581460320107540381900c0095000d407a0540301b0741b800c149030700036003007450701c2e04000d400802e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 392813255 1250 392812005 392812037
    0x90f060f150b070f0213021b030c0f0303090a02010e010507140304051201140a0f0204030506040809011112040603330302033a170f010603050c0424 65
    0x20341040d0031a40464a076010030070000a0446104028076440e44410318100f641d544d204240041c0d0400284242a06800041d06824070380c1a500f0040701500d615148850304200e190340c0e50089035001d030300f40c883c690701d4848070940802031700c0c001c12500c0010241009e850740151140780c040320100e81004024003140c80815074038503210780460303e198003071643ca50070401803007140301461111300e91603814228007251849545030700704d81c01000160001100d21001c00305038060b1085a002809030f11410040c041800301100060500340c0d001d884141d041401c0c800602e0302d9421200c00e61001c8030081c8020403845010b030700030102c000025892904a5120402018a100100d0840203076540c851601801142010401d50401161240050400210030081841c0c010f04007880c038030070528401c013104181402881d0202070203142c0c800d8982e092030030b0368600700300003024451440000e040002087d42c11303010034222005d990342c4011010101c14004100c50f60318140080120401112040070810f00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 392814505 1250 392813255 392813261
    0x3150603060e070807050a0309140f1f0b060703120f09080d051f05010c021302041d0703060302010e0d0c17030711030c010905090901092001030509120904090f06 71
    0x580526100080c04034100360720301c00e140c180108810140300800c0705000a95401c14156460124179250108840d106464003403500880c0b03180410b00381c810001007011000000c50b24020780014001c16104491040301a0f4042c0d030000170b0031903007059040100b580828460312a41a001c880c81c1008034814000300c50b07841c200c41d01e03000b0680320000c02181c2c1444031760b00c80c02556000020081d11020400b40d481c0781148004261003018184801d80c9120300454840b80000341c04030003101c004540b15030340c41c07010810741d400281e141101d040c0d07030a0009907118000c0c483c0388280e0342c040c1c2d200401300c002c0800740103004002c50070a54003040c204800207041c0c444100e84002012600c406103846030710510301000314103200d850f8180b181c3c02150320700c506030364400c5015045030000c0301c20402e1611034120141c011700030420081e02c000311210512200d42c0000808215144007aa030810003540c07081452900c4d024248032069914904004040003032800741c1101c0813050003240098039040742a6150307412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 392815755 1250 392814505 392814509
    0xc17150603040c1d070f0e01170109020a02070602060f061309020d030f02070905010513020304031b030207150302120c1b010510080606120604060218040e01061e080604080a0315 78
    0x4103140c3c140c041c0588800c041d00c080c10501c00d8809481581082c1c6806840000c1714a00b00081000b0340001c42e5003a0b204140545070320100078954034040d42c6810401c0060b50000d24004054810003a0000b50a1b10002d103184c4a1440116400f803207490340d070100403000c401803001c048207c0c1c49249000141e40e0320820001c1c1103200782c4031522065441f54010341004040d038051001503240400402c40c40c0c9954990444000450300c2c0117a4990741c600d0706484c0d4003a030308004240c24668040c01c60030980c000607160b0a581c0c0101c803c61103c0d010010131000d0b80b0445440346498004030011900780c01c100c00c0903140c0c40c0d401d4a0615000c0f150800880c1c01c4807002c0351350b4014030b56010404c1040c6241444032035000031099612030341c441c500228140c0e4503940640010005980010190b2a003400d402481050f0f40c80140180080784600140c540603001c907007e81e030304600c201c0c0700310398120000840c44012107161902034000340d5aa51141c101581242e502d00303007819200c4c19100803c400803803d40700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 392817005 1250 392815755 392815763
    0x6080a1d0303070e040f270503070506010e011a1804090303060b0d0204090506060903030313030e3001051603020310030204020f0c0106050301050f0103140c06030108010f050a0c1715060304 83
    0x80180d201c441040241d4070611046d00c6070300e28003110000310081c5132941c520b56424610f402e5040a0302460301529600c2030180240c054040d400001c80c40150305042c00d8100d8140b189410354041030400b010307800e0310800f900c0301d0703d000d00741d0400c80701401c0682102c01d003240079040004031a6614868031301070781d1004032046582c990009051000034403038400c40c0c2d00803c05840c2503040c040391601103603603448003605800041d48201d801c4810107200d110004c04401c80a0091403508416488900640707052201074014000d00c07052035864140141301d0756200f0040302d9541c0404017040e80080d002513001070309108084030424000320160300e4a00003007524880c440c1859540d503400b81030031400c40f500342d004140300f42d050070144a601309200c9410b80c1900d070090365105040c095826090720b00300d1040b012035005400440005840e400641c44202c01c001070f18810720540d030711030310310b281154045031a00000c14146011924010840e0190303c0d44010603040b40600c001c2013030002460b6802c01c4034221 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 392818255 1250 392817005 392817017
    0x14041b1b081b010e070308040303050f04180504140f070515040503011a0a090b06040302090903071406010501140702060307181d0a06120b06150d0614120706080a1d030307 75
    0x212080c04d12541524070480c802825245041d5525400b55110b180310250401602280030940303217401070101d03002003030043c4120328860303580d540002c040e06044409030b91944a0004c4103031130820100b509030490030020013802c1098180700c10860030400c0702d180e403210f01c5000d01c030201e41902e0074440c208541c903c059001c401c80c40c600040003415042500101403072400c116840c03426403030f07800c01e88056aa0407510103c0303960310040560f2540c012500041c1801d90703103107580c125026000c115641601c0003a070f9440344840f003400124000c0d00c10040e00030341210303042000500d9a441081d200110800320700480444135074810010040d03c44c120212484601c0138010b020707103017005101e00401491410319100060075140c4641041100c010034141c003800c0e02c41c0da100da410038940225480e02c101800c007081400d40310114005001c28a842041c001e042d00f241c043c9985000044100444802c0e030381c2e4110310754404002001810002e04000e4400890140c10030aa080030310186200b030100740e50707003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 392819505 1250 392818255 392818297
    0x130507120507081603150e03030f010503010f1a13060b030709091b411209010209060d0b1c0515010b18060912010c0914041b1b08 57
    0xa0a15030a41d10991590b800b40d03111380398200c07107581c40b10102c0e50440039120680c0c1500310500080c00080c8042c4069000000c1003007060030703156000c141a60000e0f0002c00019007140a5501120384154941d44414002d0980310300c50719100281c034401201c000800f02d0f5007aa41c5101c4c0c041504240e403420040b6102010a10070b40e42c05204902e54800000c036100660f00d040c21001e410901d80140a8000b402c206441220f520340d80c010208044140c991090500c62581d03040560503001071102d80b25042d0710700f011421940e414020b480b5242401882c42c2d1410f40840d00d590020714a4503000790b04054900c4286c5800b492804ca042d40380c0c1d0149010b41410705403040f1500f03d9020581110944110070f11281240310a00980344240704000c1e80d500c2d6030b604004c00000d46203507001207101c2c8298280007030b08080790b81c440c007440200d42d10650701c05507018106d02008291100300d1440126125808482c056031482801c401d0f0b11400c0c64079982c500030b101d030346410209612079481c4580a0600e0078503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 392820755 1250 392819505 392819513
    0xe0405151309080a0f0f0305010614070c05060a0207050f0a0e0f04110301050c0403120903121b02060c07030b31060b03010e01060f0608041a070210020a0f030f020c0a03030513050712 80
    0x1d04161b600d03040c50104820341c14103001601041c01e102002d0a0400046003080400900040c40da025200040456031140071040d00250740e00396500034035000d2940da400d810060b0602410707500c19164040300d04082c075903400c2e11103500c00b50014000d03100c42c00c05d000211041d032028420326003e1003490a07520354441c2182050710f50244414075100c10490008002c0021940f07601d91040c0c040041d10303103500c468030702c11407000791440003481c040e502c41c00014560400c01400110201120f12903c0f02c81055900c54624040310420900c180c201c00701c14201000b0107250314182034a40b2403161000081e0440c5840220342154262080800140c1d0741d0003007444032100b1241944020040e51610b043c05107031956034086840e444018802d454000c07080803070200707802403200521001100780c04546401c2060700003002480345004110101e458001c1e010042c035014001c80700a80d140c100148007000032683c0071802009e0003004034201c001150b0324000064418803c103401805c00c0307016000c4031045420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 392822005 1250 392820755 392820767
    0x216090f050601020a02030607050d060b0f03180a0305180a090203040605010302090a0b0109050409050a0f0b0f0c07200114040617070801030b070503040f120f0e0405151309080a0f 79
    0x856410341d445490517000583d80040c0460384003c2500c3d01036120b1610100790800707408581c0101c804140f000c90079180d0503540c00007841c4070b01c003844400e160141240141e680c45c0c4034034090190000d0b808202c05101d2501d10f203050203c0035005015840e00307a035102c800100f2a00252000c84800e5119401002940342c0341200f50341264011034204200c4110000107440104076100782c030f0050b40c46a040805104c82031121800c516001199905054000d184c41840300340c0807201502038000354408961400740b240151070416610051901903003010100c0f258600403500a8681080070318404c00f000d01c00c8107000f1700020905038452500303110000c031200805000c01002401000610401000881c081000180d040600d50402d103a494a480c00c0c00e1000321907802e4050000c1e011680410032803588104e401c11004502c0d0f031402c40100d21001003005980065070b00c80c1000601c002050714500c0c011261a400c12020000015045417503a10b54038650007140303058000c02d610040d28591150414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 392823255 1250 392822005 392822011
    0x70207051302340b060406051c06050f040f0318030615090f110702091906140102060f01060807030b060705060703090312061a07111224250216090f05 66
    0x4180702c1d1012076070300300c42d50740c0c91911000780a1900e204017051083d100c035070211001d8000640075590b1070244c00000c559515010300b04039401380c64440020141c0c491409468010382e4840780d5400c6c03103001038604480da1000b40c100c64496001458001001440512903606400000e4030700001c0245010502800c50b69041164098242841e0502100941d15421030b0b1150383c3c100c8086401c1d40f101700750368500420340b0260502152604002103100c2110760300c2c0007403580c0702741d085416135039072503002317103840e040c00e2148802148281011070041806508070940c0c0369000b03080c1c0c9040c500300d5150030389816001d81e035010100b035480303c04205250380701d5030043c4c400c904c3c80000d110851501151201c16074000c000e040c0780070b201040b0b80c0d00308000503440c2005c07104000c041520304410003c0c1c90381c64030001b5034101500800080351342808588201007501c0b84c0308804803040c100c4039000b02000d2804030038043c0000c50041034000d03920f0320714610b64040681840741001916030340d10078040f4103d410207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 392824505 1250 392823255 392823307
    0xb030a0506271203041a010b04050406082b02030708070b01050f01050c0d0503060607050604050106301e1208011a0702060d1505040f09060c090b0a0305070207051302 73
    0x441c5156403240004514920220f0020196500d640f41d0518101c204a0381e1004a50a4002400021034189010241041e03410803078042003450b5803071142c40d07a40c1d01e513083d9070848081c4486100d140040701c42d01014a0030001c0c016285088500e0f07803003003440d62200100f101c0307220386200103000c90300704403d41c00700904c230130f08101b80b405c0c602e00805984c40c0c1d0480100020841d000000034603e40b152001e0301d075119442001c031030789800d20385429400380c1001c1c0201c0da05d078000c0c6e600c82c7c003c1c030802c80f92940032481c000800e42c07604506138075021210866801c24074180e035807181c414400140c82ea81c00081503122561811081d504103e440c13040031140041c80c4c1c008074414813094025a9601d41110303401d0030802000205010200003104180d6001d9004941c030504e084002c800700c80c1f1641100349120f01c0f0f20803c03c018100014123480c030700074601801c2503407403013440560722042c0682c1c4501e80020081c0102d03601281d40b030000a41d0000820071007144a41c0100314500c0e011210340040320b8610803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 392825755 1250 392824505 392824561
    0xf06020303010305102d02070b0c040510050f1b0f060105031203010608070c0606060203070c0e04051207050f0105042108150f041b030501050a06030606050306060d0b030a0506 77
    0x99031312090740c1c0e4100d915200e41840d0385c541c1c0d03170022007030019803103640e02c0300b03205c5400342443d94564854000d4020301d4003036614425400008d481107588078100da080e51002404000000d180c10022600d903008148400410b050800103c100c150301c10b00c6122010b50840c00402c0a4000c3c0320007182401c0042c2e000380d00a5010808840020034000b06a0381076070b409103000b00381550b0b8101c046035844d505c0c80740a40010300c2c180e408202c40c1c1d07010005001140c080c3e912007400a0b0341c1c0d100c1e000c40d000101ca0240c100d80100b10340d400603225010003810040c0c002e07021180c40810307032064103007142c60580741262031540b116040242c1e514060203502c03800c049400c00142030300e0820100501080b41c40380161142c0d503100028800c2c0e0790303558010001070a00354118241202412005002042c0078001c0740d00c19050080006010340c403a00618007a2021640d61300e045445010070700c9110b422200e4900c64003604c4c3d110703e000030b49003040b014110b180110f000300100e00b0410104186003000d402d994641e090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 392827005 1250 392825755 392825759
    0x1107120515040c0815040b04062f0d0c090b0f032820030709030201200303100302011b0f030302071a090a0c0f050a17010e0a110f0405062d060703090f0602030301 71
    0x4a44464aa409600400c001c50590b040c45074101c000c1c2011480580031114011808a618403818003a0bc00d2140c5400704020786141864240c070b10451600c01c2c0140f010041105050302131900019540088104d9404040c058020580e8051708403091501706045e40c1c0c030155104041c0e242900c0301c01001841c0c1c5420314505052400410000907808042d0600c02000c0c0031000a0070b40f10352040c3d40952042c142c9440e424840030f4100c2d061440d01c03040c2e0002d0348000240303820006420034104090f0384070100d1500303040641d034207a0194102c44003e54103000b041404401c842d8480e9000d0384550021800340c011001145000c582d0720303030b0030340124103100790805090155485601e640d00568000c3d800c5100322000b458889409800d070040d0600e070314041c409070344003000460f40d50080020b004079000001900100148008c03900221240360340145803524500000103a101c0c419154161f2444100220b080710002c24a550b04c520001c40004030b200004001e0307440041c449901410082c0b004d545954 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 392828255 1250 392827005 392827013
    0x81c0e030f0313090501030b0609150d0609020a0e2e050603280209060a11031908040302060f0c030402060d0f0203010b12060d0201080c160203150103030f1107120515040c081504 78
    0x1407402060140100c1082b0f010030b42d20a60751010505d844001022010100d40782c0c903104003e030400d008202d0090380b2042c0046500c0102824440c841c0400303032001901c1144219103184c4007400d0000c4104418509000464151501001144204020134606c1002500c152446503144600300107850b0b45031051201515a07a80c4078103c943e03100c2503281005128204040c014218842c11000c07602203c00e0307009445411b900207a00500c40c500079000d469040d0303215401500c403040304503980350702e47c18100001001481d04034041c2c0205250301100142d4206a020040101e0344207030411411f160000c01d075030f5031190382e807030000741c3c49001030b41d44038100d4036035a001038040f1030040c1103428032000c0402c082d018000969a1170307032302540050807110400d070002c034415070340c010a00050340000d0f50b80c00754042490003041e04a41411001d0001c0045528140c0d280340a4000c01c0d030115842d0040418401c86402d8032200e0302c0c061400f451501c10450b1a0221071480c00c080781c040840d445130420708110207d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 392829505 1250 392828255 392828273
    0x9060f180f060a140c0a06051f300501050906061011060406050910020409021215030601090e030d060902041d0f010b031e0a09060b0a081c0e030f031309050103 70
    0x3810782404c06040b40300c001d844680d01805a20340d1255544a024403c81c10300401e07410141c0030b02940d10414801e1205094205180c07200d901942203229540101480d40c140210201090211180380314200020319a0760a401e44200340c4200d1847c0d8404c0c024007100d4036040701174a9132400c003401e0a44481e962801100d4035041c0040001c0c00c841e61b60800600503003c10312006000f4400707480c003195507a0311040f140c0000c2d002025010719403074110b070001e03603001c8161fa8401d41c0c0c894000c008103040e03842e000342d00c8041c00d0110082c1541d030106000a40c0c206110740180350162501420158030b86082c0401542602000d1207060808520b000602c11141c0151100741d0540740d40010300e030b035a44d84480410f0922036148140380c0942440c40c040203c4043c207172740b200c02c840e0f20400040c000c1c0004036003040346095440c010590780da00a203240d00054007060f9401c0074008040e0030025108520f01000a0901240742608281900009000c5451407100300350136024141082040141d541161507090752 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 392830755 1250 392829505 392829517
    0x31d1f091113060302060c030a1b1a0402031c1e02010c08012102060304150b0f030c010c02041407080901050106050f04121a01090207050f03091c030509060f180f06 72
    0x1030710b0040410341030301c4180d4000001554014101c9566020080c25440da00da00c03155078103000900300204050302e0180300c0c1580c0300031a0004280f409400040703141956100000e00100d80c140b0071a1841600d10007032804120b001c0c80151a180c102c3d03400f09000030040a040b01502085902d00305560b0b20140d0442d8140d4103442285803140c5001e1452218660720805e892000795000740d02000300030400000c0912081c00400000c01031000c00858801e03c0349801c88a078200783d050700003041d00c0b2065449008003d80b0640010804548080b0a88001003404820b40352100043c600004008801809004c0c40d4018022490020300d400148e854010f0310b409903000340d02c00d05103100d001009018140000c00e02684828144404a5039034a041da0020351060f50100d441e4018000508001000441a100c0e8018080d045030203c22503251900c5280c0403000c4110180013048c45500520388401020300b611100d10385855903948444c4200b0701c0d0000c03124100e10b2148441500c18200781e2103210654075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 392832005 1250 392830755 392830759
    0xf1202030105180a0b0c07061d0f0f03040501051303080a0c051506030601030204020307110f01060f050303040b030c0a0c060c020d090509071e12090804030611040803030403050a031d1f0911 83
    0x41c0c01e448221050702c81e40f103007e0010b49054104001c3c001c24841d204400e1880329242030031203c0e1070001440c15900d411000340c0341e0580341c100b4081040103501440062801d8030038550038026154a80d074071980035412001c00240020071840218041100c20456441c061203070200c01000b524100300040d548110500009015540102c08142154001c19101007050108c13000d03920f90b1100101c88900800031445080c1414003c0100082c4500f000300440b4265200c4000c00c42c41d40c0d440c071180d070741c9592044505034208221078503410f02060040c4210740c0700030703d00d5020700010814424000c240c070282c0e400c258450420b403c103000c5e0b450b0700100040c031020803158403c0d0312400d0a84062366442c0404000f80a000e0030460340e601080035080c024016203100781000c201400c806001948103000360b02650786960b00070008070f00402d005402400e03900c2503e141c04102e28000d41021600180443c0c0000425440302d040420341190444540f103084800c0c41b0100205005526080c20361104c02003054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 392833255 1250 392832005 392832023
    0xe0402010e011106070206090601140d062a05090f040e030307030b01020c18011701020a0207030311011104090209090105030c131e05010b0c060717060112060f1202030105180a 77
    0x40e0075034011814200c070440f5940a80700540760084019407030b01011280420740b40510703800490305071060a5660320400303001c0c000349041c1406541c1d200080840361007644108501c101c241c005188203080c0014594966a1003584601e8034406000400703500300000d5100d0382c142107650214031800010340364008130b60701c0d0125580862000603401c2c5202c9a0140c0d800503c8034915021620b81500d4060480310840f008101c000c007121505400c0b03000b02051100180c1000c07a08201292203101b00c0b400001009000049052030b108054103258850f500c150340036900412545500d01d021185103004080a8001d0242c00c1200000540c0061a0404002c1c11a80d20841d42d4901900c0405854480511380d00c100420f503162288034541d41c0058074110711038030a400000d03820a103d86030110a00c0c600301040d01c2661a00f10042d156501616840034005a44100008110828008050080c64410600c01d030620090050600b51000141068003101c000d07111022407101c00141d41c0c4015070004110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 392834505 1250 392833255 392833277
    0x31a06090d0507060f12050603070e070522050112110f0d0b030a0f05060702120a050d1b0e01020111090a0303050a12060905010e090a0312050c0d060e0a11040e040201 73
    0xc07100c641e240780c003070010300c1200400308130b5603042281801e0700c41482e150b0ba0001c00d2030440071000e07030320100c400c42e4054001c007408020504a5601441e003020480c182a400c0c070408040134030154009a1540e9a081c10605041065581141a840c0500d4401606116031081d090b0442ca051049400500c00c1020010fa00e00c1d0544465102107100c034001002c0c0e070f40c1110141400c0d840e140503600c060342d85004043c0440c0500d130000403045a004003401c0f000b401c050241e042660750307800170000b224400d62201b0040a10414204103501d86070850f40f43d000054600b507000901319080440400c409200130040004181e0701c002e021800c9951616065070754900400023154a48003d0b0510051981014004200c1c840c213078103c241640d2207001c1c841c920741d43d203001440c4d0300d034020140500481d00030303c40c0780c4502c0580d401072940803220804040c90a0801003038178046400c42ea0081e0500c200440502c041005207014a25010002d54070030b03410181412008885100d001d000207060101520340b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 392835755 1250 392834505 392834509
    0x280303050d0209041406100f020c0906150a030c020105010803040b040e1003020d0501020d11030c07021e0607080d1b02070e130606030f03030c051e03040c08030f0d0b01031a0609 78
    0x403511540f01c058001d0110301e0342d00707203a41d1810806a5078a845500c004418884443c440e141e0700480b01e210303034000d04c90b00b0000800e208840034064101500030010542c2e4080341c5030000000c10760825160f40001e480e41850740c0c001d085510603081140315400c02c00003000300290000940f001d0354200910f4258649400d00104415200d9a200a41203031081e1420000c1c080b041d40600b813103410781b4006101c0d050110341084401d00c41200c5e80041c0e000140040c0002d0b0800c40a070340d00180c8104926015160340340e001603215000706504442884001581c004184024000d41038601000a03490107000b00030000651102c034035004000c3c0c941258000210400c0500d640c41071507541080d0100045600c2c0d0915045090250b1410b6022034240300400708140d00c0340045840416103e17004800003a8496401c100507403011b041078078800d030941004902020140700900c00c03000d06108265807040c03c04407010568452400c82414586422807240702003801000c80f943d9000111240d035583c0c180080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 392837005 1250 392835755 392835757
    0xf1208070504030822031202010b19030605060d0b09070906120c06050a0212120f0601110606040b030a06051602210a050702040207060603030e040b06040b1b210405280303050d02 78
    0x10a548149107444004180b201300300328041f003603845500074002c1c09100024080e042010f55800700d04002400e80420108015a102a0300300300002c2010f1041d01054654802c402d00c1910446240d81104070104002462417085074003d0003c800d0102e190b0110703841c1d07040c10f200e00f0f22582042c030a00140c000c155610900c511a115100c80d00780395201c0c0c8060004141512003200c100c425250408041205980030301c002c0c4040d8a40ea40c020201980c2d00418003018100b01c007006a0517202d040d8280d0000b03050703402014850071a00014044109641c103000f4031740000004141034450301d4884444145c60410308441c044c50751340c2001580d5480500c040380080c41180000f5254a28000000c8105984102e6000c00c0501c00c0350240490f40720070080144512079845945450902040604804950f201843c590307030705a141a01c003208104611426010030b04a0300b003600d5040064140441e00e0103402c41d6801401b0b44804076015103484c5c07030b401001f04250201034107000e40810b6201c5d0b5003180d50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 392838255 1250 392837005 392837047
    0x5090717010501090509010203131410020c15010b0a0801030209150d0c050918060609041e080403020312460809010e06040210030f02160f12080705040308 68
    0x11510394440325901403840c000d00d820701440c00d14505000100f02c1d241014001e590242c40846058a51980356a44641544100420380c9401e0300510403580105c510600c00350401c0207001e00a010003e0f680d01004003890816048110000310922050003c42d900c21b2100341035a03410b8400c0c9000347c9440204191152a44d11036503406902680703002e041015002e445030071107909403803107441c2e500c07501e52079605148120b5030002280c0c411000560986070013400150000d00420300d000100114220010000005420031340b100240040c04200318203003002140100310688580d039091540034070520b045420a0003402c10480071846c0b411040380f5000050044c41c0c1000e0703000502143c01801c0c00f82031b94400300c80380f00d400c0d4a848550340321b4039004038016120320790040450780740d011b02c15010303402803505810312011998240460006000440d1508241c00d02400391031000000c40d20b401818051005140d504108296003881826908141918156035014880c2912000c0001c031462907850300c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 392839505 1250 392838255 392838269
    0x161d040f050405030705070e09100f060308070c080d08010b0d050603010e03131a071a0a060b0a1d0a06050421050703031e030c0e060c0c090f16021f050907 68
    0x1002d000030080000010001140f0038025542030aa0311030445090002c207c9050050750414001150b05041a511400f458800d4441c00110031341c132612240c2c019040048211100c0c883c1450511139803604100c1d07404113641324a003c5003a5030602e0710102160048410800c0c920340c42d4030200e03440d81e4080d00300c00c229440c440104c03a100c00103e006050700b500c3e90711820010680c42c0022242c071040d800c04071800b00c1d81040003c10001900114920f1103000101606051541c0e8038002c0b0340315075808010b1040c4003856030b8820a04090840c800c5807551050b40313861284401031000c021090708170003a501110708480320820448218880006100100c21000f8010f00550303201100701034005440320018180c4400b07401011518043c2070302181c0301d501d084400700d103e0741078200d018034049000384090240a0140c41551031800c0200d030030303404191600d50105078900208400c1040c603200d01c0307880d080988010440100004202c018450704c0c8811050103a49510000d5200726040244000812031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 392840755 1250 392839505 392839511
    0xc0c03091c02090a05061201020c0d2d03150501020a0b043210050919020609131401150906050f0304020a0e010e060405180309130f020a0c020405161d040f 68
    0x131541070000200340480d40c185c0700e11944403070102040d03030501c00e43e0101c0001c00000c4c00340b6140b004081e104e00100c14682d200c01207030001940101401c0c09c10b04e01081005423000b081c2449030082c182c060901c4ca0b00400d04560016090102241d90003040e00d03009031300000d0520101e21221050071070040e00129095803040820801d04400310006911085000101030070041d54440e001382075103e0591032280c4603907400700d407404009442c2440007081800c00c005c0206207420380800c076000c02d60701c10401c4041d00410074001003040000a0011112000c00e6240440c0c100b8100f440103001d40c003600b460156250b80c040700045c00c540710031840d100a0050040e0100d010b603984e401c44450b224080b04c03024041c504003008108160a111035441d500392400c405542800d820100b8000ca804811070303010f5200d07407034506c1ca4800d04a03a1004003d1020540c0d507081a00245006001c242c0d0400340c151a802e200079101400002e921000c0c000344030000034540300d00b004080700020080c02da0305a11805d4645 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 392842005 1250 392840755 392840761
    0xb07050618100c050702100806060f180d0b040c32030f06010b07060612020604060e0f040515011d1c0309030c0b040509060a05060d090c0806070c05060c0c03091c0209 73
    0xa000b4000e0110317903100310f40b2010075400000c400c803201c1e40c041d9403031070f0009401d005503a4040000070244c18212521240d10400f1580e000020f0000c0140714010384191030200c080c00240029501031030090b104100020041c0b41c40007090368442508000e1820301440c041001c142d841c3c1e8284410701c0103041003401c40b00a0b503156140c01600c4c1c4c0c4141c0f0100c4440d40741050003c0d0080442072882c40c0e00b50010641c5040610f45107007a100c911114410302c1c1d204e40408511103045d601c900c941da008401c0c40c291440d2031200343e0009044038081402c1010120b80380380c003e205d29550300b000d220080c41c4490142032141564a01030322400e01d81d800080c10f2040c4400701140c012450320182c800c9400446180b81c0d1510348409101d281096401010342090b81000403510340364184e000301000912400f8107450403541c07080c0e03650500074180c0f44500000c601d6001c600921104105060300000300d410400e1425a4000000c3d41e00e10404100e00d0050070010000348001c4441c0e5031040031a43c014200c54801c0c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 392843255 1250 392842005 392842007
    0x703090510240f08060c16050d261501210c080a0605180103110307080a1103010c2a03090504050412030e0a02090c0f0403051b0a0b07050618100c 64
    0x10701500e001c1c6003064140b280095041e5540c80340310120b8129001034a120348405252210301d41c8000366090b000c06040041c0e07000200c1c01c06c4031450920007a91519059070500781040e901da10030080c0d100d000060030b42489598404114000e0400c0c40900b054450b150f9800019010341c8200b0040756107151500c81107051050b0003242145c450084c2d001c0401089403544100801c80c5100300d4002c908600c1d240040c0300041e542403d100c40303a0401000c450030281d990200d00e2402501240c00c840b41c91030040c12186509090051103000d072954104503030142c8140e4810f801d10030701d0b20318240c41d45002e68541d00900d4050b40c2000d0281002920501c80ca14044c1403c401c2c80041040c140c2c002440e1400b401c00884000c2080e1050365070003415080642c0320100306030541e0708411064841d10381c0070032000001034020400704030004480038030300414000450810084485503400f240300c01004000204c0050000f080b900e130b01185032413031182111001961103103041c15410b0181522441e2007109a505 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 392844505 1250 392843255 392843291
    0x203030c150a05042013021324050a0315050d03050910020318060706150e09060906011202131e1a0604080a0206161505010e15090703090510 62
    0x101d040411441c0d181c0d20341c1d00030282280c80c1124003816100d501e100e42d8008100060405141075001001e40d02da00381c803c00043c0491740318001011030783c1d50316902081440070820034642900a0711000f0480b405200d480070f0540d205030b82aa208250380c48011000c16088038541101804014252001042403460007510310ba0041d010944140d06040c0c480c001c680c8008203c03102000c1644995800320296002c0c0300954210340c00481d1141d440381c08290a110441c41c120004000e0401e1340d00031400d01c2c1c264142095005040003031550000c80040c80100c2104014140031941580c0e00440c5400c0106010028024115200b940c1d005002c54855490001c0d04890390b0f4585209181401c0c0c0040006c1008600c03480c82141d04a03042402190050301d0000082c00d490b80e0803440500352062a607680c1e502180000141501c116500c0d8010320002c007030064180d034080c17541d6110002c3e008a0800042e28000010080810107417030300006410000c050040304400c469400052007100310b40e044e05a0301c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 392845755 1250 392844505 392844523
    0xf0b0402011814060703020f030f1c06302406050f0a0324020a02010204030b060102031c27150b01020303160f0c201302091c030c0203030c 61
    0x42e203026142c5010120014920045a40f8002403030543c144180a00609800c00c400c00e500758064003c0d410384201c0144000e00c000321080f41804e0744e03802080c2c0a01d01c101e00c1240c0d4031400c1d034602031051003c3d00c089180141000385114a184c1901c0040c0744480041098050041a000203290340e544413440305684008006040c4006101080d00c800901241e1a0003200d0143d00840745d560400124402014501c8004400419004043c0115003c3c500383e174421011100181c0d40064100b00740212441860380000091000d10b1501c0c5e162078240380c1000128031401c0388075594501c0748500340384031880e6186102d00360307012504682160030181406107100304400c0c0214108101d055080d840402183d224000c6104800f20216803043c1c1201e81080886608040c0010b00c0c1d0020040b554103410207403100404121255202015024003040800e2500309000c42c03030041c0301990380c40c2ea8440380941c000a246242441071a00341c00c0480e4044505400070b5090f0000240f1701407100030104903544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 392847005 1250 392845755 392845757
    0x90b04030806060f070f02041d0304063b03030415050c070509090a0b04050a0b041b050a050d0f02030a02040905030310141c021306061206050607080f0708070f0b040201 74
    0x1101d9a503050034445640301e600440340608004024290001705240e00d007010366030000d0310001f8425003015462005403030490504699900100e0b0400c40d4a0740001e108a4691054000d80d140920700b076076542c44400d01c0d44c0111a01d480e80c000c203020340d032010804e40e4018002400e400a0362403811001500d00d40c040040340300c0303e015202020449040044ca494002c006242c01041ca000d115124034100d8000540100c640e4061800c410000c03510003a0101d010724021003040c12410807260040340c0d4030f24254842402040304080c2080b0603581c50f48003020b52a0418440c8100360100e20000341406d804901c029030103403a06201005200000014611801860250740e2a650b112044da2000803030701030403142c0c400012030302440e503002e081291882c942d10142982140e001e0020301002a2400b9411038000070365102c1a1045070356807401200000c0c50185e8800d480d00020313442d803424500c516036004c110b0701c071700042001c1042910b004030b52210780c0000398886141110710349808500c81c1602e007a8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 392848255 1250 392847005 392847017
    0x1404060e13180f0507030807060509060702060c091009120f1202060c2b0e010e010b011803230d05031005090f150105160f05070e01080601050405060d06090b0403 71
    0x2007500489220b500c0c50400c40d920402002c8002e07960300300d20401d041800700d40078000c920000002038002406407000a20901012a007442c058115a2501900426480131584a00300b8099018980300c112100c400741910540100f41c0e0040e010f9a4100303407640005d01c0070709440300711424008400024883d4501c40d000d00f000c00741e030888040b682c5801c1564500b619080420200102001c1c02082c0b4107441c1100b0144001d80701c000c080c2c3c90071a442d4140c4608640d4440e100c00c5440c0000784240d03540c0300d80034202180b01113021003074210809007038000140a416011020012411808404030541c1040000c840b180c4140800c0100290415550703c8102c0404400101c1c491500500080c4601000c01c0c4240056440c3d0404042d54204580c40c941031240800c03100d40ca84001185800800b40140c0000789403040c9441c045290a10940c0302c1c001d43c24548005001184002c0307180c504503041268042a0b54540400080200d05031840003089d40b450303e85820308100c88880100d2165000c0d490702c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 392849505 1250 392848255 392848279
    0x30405010c0504080c041e0906150b040b030a05090c0a030f050d1e27121509020603010306093908010e1518060705030412180e071404060e 61
    0x542e00c034010303405440d0094010b400494a20b0525a200085407600b00700e00e0329220031000760810407548880019280e09454a1000c44c0d031101d100218001030104455941c0740a107840c51600407400701515088601d034852020445040e810008415854001040300b082981c0c1c83c5461342c815022540b0032601ca000f4100ea6503410380c001c4800e00c55560340c0c04a8000e512202c80360480703110b14200104800301801c1040f61100118031140c207800340140c05040e8000e1012810300380601d419041001010a05141110005031500c5050340e0440360300503008070b5041c14600d099180c208001b07142244452003490282090106420b00545000209203507072411600c4511543c2070390880c00081103030394400010075515580705001c27a03a0050707074044134940d8900209403450618038142c031204001040801488180510310340103c1540056040120682c2d80a550400c0c0c006070500c11038291103601000145031a0240c2c001000303803c0306814555446490390300103000c442140f050700c0e010702030307a40d11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 392850755 1250 392849505 392849507
    0xf0a02160f030308041b17010605010210090f0b1b37080c0c030c03070b0601021605090106030e010b031005011a03090c0405070c05010c03020322031d030c090c030405010c 75
    0x1001c055940580c0e5841c1c460356142c44035009000203402103008405003a04c00510b0300500250a007882408100109201c1d20f071800080c074000c0498489100c00d4904644132000a00c80c01402c09143c1e400424280366940f09e402400c0704c03040524501418600010b100380800b0b917805507000e5030707c050050f6032460710501032a100807411300041d528080360f0140041080200508003030000a003c0d0780031640b6240064000320b045400903001240d080700c0c0724083c00450b40e010702003036950100808078820179030715180000e0234200d0180b0420050603660541222005020b4101d04041d40e0090125410241c02030001d0700180001d00c981c0c51010109000d5001c201c1e03080c0201c0340518103040040c40e9640e460000c0200034003002c0e044000388600043c040c000500280103140888003d81c0700184c136458800c0104420aa04d444061951030901d4070100000e500b10303c0d44052900712011042e120b0b445400843e180000e070b21901640500300c1010080d0004580008502c100d12801c0244004074a00c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 392852005 1250 392850755 392850779
    0x71b060804120e0a1e090b010f02100c0c140c01020c15070b0c0712090e0c040b0a030b060f0c010b030f0c15030603010f020a0c02041b090303140f0a0216 67
    0x103002002c5040e180301406003540324031100c5010401c010040c0c100c1c259600f10301c034500d20244a040c00c3c1c4c41d050090400859003a441248103443e02030821940c0c10f9142c14000f9290460140c10110040d510b415542d1118401c0b03409070507469208140115085800e5200d50303850510003c50b6005226000b21113810741490500c208001440881c003904100d66a590030744007190060691444413024003c6c8000306454a51380da5100d156a114955694101f20240c000c0c0d10b0010407555040e1800c020803c9104c484a04039040102d1514001a8045000b000101c00f072003582200d9040c20300101e241c2584130410f40c010040c0120840c121b44c42c020740c903100c0070380b100012201301d544041c143d11400a514200001150300400007400040d41c0c1291081e0042240c00130541000001c004140301c0d82107080900c074440c442d811440c40b003c3d1064604100424108060000501b049410745190b0514100310098a1030b0000d00c0000303031340b91b1030ac61303000030b55803580024a240e40c040411400074176491802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 392853255 1250 392852005 392852011
    0x90409110a1a0405061b03030c030f160918111804150503070612020706060f172107050c0604090b15030c0a03180b250905091807030602071b0608 64
    0x582c45410a49880c0c100310660b00004c1649101c4c9402000120f9078031001c3c80110711503c00344050035180c0c14000c042c0301d40c200c0014403030005c040300400c42a05458214140100f102c1020044504480500360201d01600d9801c0c4180b03000b503070209016445d820140c420303003210307581a18208079403a82c251002900724801e01c603441e01500480e030700f40000f80c840c00305908008000000540780c200e480d82c90904540d039a500000406000c1081880015251410ba0424411002c010607003000c03600040700c91121041c8000010758170001c0c11108003c0144820840a94000c0c072082d2550340d90101c002c05880ca81800c584160510004402a2000c0d078043c0da0158000c0e0740210f0030007020400c190020300c280703604000f18050700c0f00d03800c5c002162004603910134212500b000c1381e51500e80280c401007020f0341e0180b406102d03081009000c2a2075548005620041d40d101162002c42c001640a0034030710340b5000030b001203000203101e4003440a482050203411044440b1191615603a181c100c681d143c041d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 392854505 1250 392853255 392853299
    0xc0c12120f05040c17190f061d06150307051e04050c0c0c060f040e040c05040e010b012114011512061805190204080a05190308011a090409110a 63
    0x14038802e00c118500090485d600407600012529940002c4800058940203a10103c07110459008034100704007090090f80b0304030b900e10480300740e640c661060040d220340c00200f06018040006010300d940c0c1e581006480300401000d80004901101d0100c1e00c1f08017061041c2d06030040d402d24011940b2007070854201d440484000c00940070000c560400c22105a02607100750264860600c004070300c001c40511a24000e07441010282c0b505441e281c280000d640c1d14074080d040a074540100409181d8101c5140300e2484a0b00d04a110707240980c412010060800d0284055031258910000c5020b002a80300c0026682803a250205003016900310b11066034810b0050810358680141640212503c9400840c1c2120403085101042e48410380210220b80040d40040300c594003003564242406428010700d000d0200e18218032070200c030305840103041d280b810701c00c1504459080fa008440050040c1c2a034030b200e14014070500c88001103041c07a1200700f907076100291241e680030f400041c0202d00306040400c00005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 392855755 1250 392854505 392854523
    0x160b010e0c0403030e03010f1404020411031006030506060c010608071403070f06030c0c02031902040f0509060c0a0c0b0c21010807090e01020c01051e01060504030b0a0c0c12120f0504 80
    0x210b54086407451a601001741d015900c0e03420542500c903143c01071030310715164003141000e640360600401c0b00761a4010780788051719004005100386c100d54800c0307031025a40d280c14040f401e80c6445c4081185880780c24000003095213030080101d4000c038041a0380040740e00814481510256038010503440720340c01c0c03103020041c0030700c003004000c0e05000b5088000304030418200034a400d1500d8021030304000020300e01c2622a00d2044110301145828892030070840c4918a04014a02d444140d04c0d070f03610b801820542d152500803502c48800da108581040000390f1140d4248440e0610301c0f1001041d0304080440c24114200390300c8040601c0c0781540a41c1201c1210005003c5280340c00088070040c03440300540d28041d50204000780e035201d001d0068602038003580301d007407134440c00d0342804298016040e000101040804c01041020903040070400c0d411004c04a0001410111001d040d038210030032580040500340c00071140400c95801819405030700c10b0a113014030118054104180844000722401880e2100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 392857005 1250 392855755 392855759
    0x905030738041401092307030b040f0f060f020a03050a02071124040f06020c01021501090f0b030f0a03080601020705010c20120106032f1212160b010e0c04 68
    0x2401c1a880d58200340500e1900c942e9501c01002c0c0c60950300310000588050781251070300a00e20800d00d0100326040035000c0131b84081c500b955070700e000c42000500301606038101a1820024000c59044a4805c40d40c00b1404208140d900101a406500210700040102e49000b0004035100800d00032145003d41c031004049400315210304000701c08250f81070180c2c804940c20320ba02103500320400140050041d038480b441d0700308d181083c024608448070b00b0090440d00181d607410340310200407010a0541d007000d0004595510403583e0340d8010403d02802c2c680c0b510071210042c1007940301140300c0d00c0e034038040d50f41c44100c1e03516803005a030ba42d8010b220310790000d40301c4084040800c004004000d042c003540612824421600c0c2e0000d0001419804081480d9540d614100204000d1102c1e552440b0f0400411094902c4211300d20707081d900800b081180284200c00c0300c0401ca0b6001d03c40201a28603041d4503949401c1c0c1c080e42030003e00c0e00f84100b03c0b034810302c88001240d09078580249070310400304990000e18140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 392858255 1250 392857005 392857103
    0x140c0109050319050f010606080907120c060507080f16020109210b0c0405090c03010602061b070206211918121101090506070f08060901050616051009050307 69
    0x14031030003000e4980d40a0f450417500042e00c05c0c00f13050020800c90741c0c0c4103040d060290303a003410401c1c554410006c07d100007410400266a041404003160810700b00661a0221f9040458085c4260300800e61900000142040042c0741000347c1d00d0480e00030790304c3c020341c1a21180304888900007446041064013424140e100000c0d90703500381c1d0398030014140c900c03400d003581d60004c00d420003000e03031b241100c6a50220060108550405c4400c0d4403070003000c4122500050b400100d9070354858602d0190165800044e0b004080140d0703071603070b4840c0c504a0064001803800580020302108024040f10030b2134200040e50704542c0d6080d00c803008040d0402e40002e02c0032245181a2000034400c2c004070300701d54032540608042207060019030710401403501d94083d1150015402410001d00405e000e1180f40c0d4072005100039210b103010303a10700212003500c0410040444c14107903c0c148104003003441c1c01c3c0c20300030748808024000c005440c01d64400d0384d000c1824012242a0f010580c00e0122140b40f950f08002e08440ea1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 392859505 1250 392858255 392858293
    0x1514010c03020709180203010f05091504020a150203070b07030b04150b0306010806030f100c030b09070909050a021213050c0904170a050c0a0605160504081203180a140c01090503 78
    0x5c3c81c9030f801c5075000d4422640c0480e0a5540410f020b8034001e540e40108030707a4034010300070344681401082c1c892110f4070341580054010f0074180035140380b000c0003030100d0300706d02e00800490711419000600405140740c41c8100402409000340f80501440c02c0c140c40c0800144040c4054064449801d2000d0940d56404011125200f0042001d41d26229080d15508017603000e000c00180b041668001150b12000404c0250550700c0c002100b60261412008100c1ca0316413080c90301d0b056035403584010405488140501d0701a001d031050004c04003035003805010744080c0c4900d00c004004c1c89001a02c0282202c10200300e2081e104441c0030300980c2c011000401c01c039000358020440f0146030300300981882c12503c0e86a250070310081e81112480e944070140b00c2c0924214250b44814203007032601c103141c40d040071002d5880d2840c232441400341040100100b482c0b00042104c50280b451640110f802845aa0510030b2152800b16640c094a0050001c440c0040d481150907009842014008100c00c81040c1100000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 392860755 1250 392859505 392859521
    0xf060c051c021203090a0c170a020111010b0a140307080105060603070c2405060a05090c07020607060902150d0c0903031e02070302040e2b0c0b07050405041514010c03020709 76
    0x460181e03540c20f1101c0082c000245000300b001ca00100740118042c9407a02da4100c03950000081c002c211408a0241d110014005000c0742e82032820141a00141500d070380584800c800f46a0f208150420125548107240d61221030988228101c0c0c003041e5031841014200c1d84292042900710504100041c1c80300d00488041c40c2880c4070303001d2040301580d09110a01c1a03042440b01c400010746900900203145850105480902412543c07040e2505204a4100340c0d442605d00c02809581c0c042000c0c818401142d11440045401a01c940e070205031090314844c207a8402d44030010310714078001c0303115036442c8188040c10590754540c5421920088081c907170700002042140311411031207404404801603c8034019201481b880310000d00c152030054401456200d00451031701002140e030f03c10016016032080388034600316040003150009840f040402c4440744030b01d0700a142c00505140c01040c04154424483c8103e80d0300d1410724440e07886c076030300441e11503050b00c0c8080d0040c0d00c014014000701c140c540c45540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 392862005 1250 392860755 392860757
    0x302030706050a021f05010801140f0613090b010909020a0909080301030201050c010f110901030629070c1a09041b141804060f0608131a06280f060c051c 67
    0x88046400049a01c0c102c1c000411900300031b03201c10040012540074040d1404114003801000c0030781c0340c0582007c100d545c00500c494450300c0c0c000844180d0784000c0c4d011011039500729801d1101580c654400102400150700200d0150040000000e60740140d813194008007a4407800061442e461500116000e400c10802c82b4001d542c0c0e003412400d02c0c8110300c286a43e940b0340b110b41c180c80d01501c130005000c6801c1c550001c48005030a03070000340101040c0c01e00710184140182e01d41d8070b5954500b04801c102030250031805e0301192400b1282d9440700f60202030b20510604440c18419030b1110300d00c4140c04400c0c5130303641c0085040d80c0c10401c101c4043d540a44013110300213003040104014107000030f01743d81999100d81030107040f8200c14800c0a034864089a03200880740300d81c0c01120469650746213504100c15010213174000b40400b14005548040c0681d600e040c91030809580e05041c1888036003051000e101d65000d0001480c400101107010300d500401c10358001002e080e0350510000008071013018912100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 392863255 1250 392862005 392862013
    0x1120f06050c0c0a0b07090609060503010302040905010605210601060f0c060f2d0509031c050601030216050d03060602010b1309110604150908030702060a030b0a081b03060c03010302030706050a02 86
    0x51410410004403404c40e000d04c1c6040145d040c0801d000e4610850745d00a10204512000c0521a01c1d0b00075045030b04403a8107880008d6010180d003005170040400d0340140d81d0101e01481c50300101041302510070313010314040040d074000c0d0342c2c0c81000b602d03411a100091408070341c103070760030001140c940d5214860084620170085110307040158450703032a00401c194062035900c14260340c0b012140520039a5401050f5400a5240000010001442402100c5c0795880702d5265800140d07a6442034050741c10080030801e11141d0035025181042c0c03100d520000200020386007020020307110344140114000907501411741d40c8483d40f111000000b400710520103513422444642450702c25203615004000501d031400d40c51014209045005000c084164031281880e071080c007069026907100000c9442c984028140002c2100344113010a00d0f100559211440344d02551044c4c00000020342c00401100070304030f081da05950341d61842c0400c9070100303010194256011450511045003e6002090000400e004072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 392864505 1250 392863255 392863267
    0x2040f110c16090b060f0c0708010515033f12090105162f0c0a0303021606080903180d1202011a0303030702060a05070309141501120f06050c 62
    0xd803000740e018418240455124070400c00d041d4040090340c2c07000d03190300790082c481c10004100041990081d111017035007041740082e00000055041040c02c000b0441d2038000c1c82039140603d03c1068101d42801424000d0144001c01d90290120515036140441c0e000e641404c04034607007121090441d0032902091181d18200310a0368007440350300002d8454107c1200106040c03030440c414944036540c41c44903034240942c40e17400350071802c204180310000300a00c3c2a450540145c03c940c1c0303407803c0380030b150071600100c5540000c800e055010a011401880300f11032150b509580340c40c220f5110340c0c12208105990410702185c8a5203000b11080e51403003034002e105240c101d1460300d0b4844581d42010f10400580e41d80e070a0340d00c10008041d00001c0509048001d1030562408400103512000d00614281d0344a076160001100740d030007a0312110a80b0b4018030003105d00c4260800d4030340e846043d002e111900d1402d010001a806030004036000150340e224503102d1045a45540d81c4000e40006088002151014011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 392865755 1250 392864505 392864531
    0x120b030616050c01091103150712270c03030f0c020f06070305071e02030601091b0e01020f03040303030501050306100b04090203063f010506030d08060301090b0f0a0f060501090302040f 81
    0x2a064171030b80501348210940c00304500305403801905032241e5204550020030090300581050490051140340c0e0008254074841d040701030303043c48643e140c11101862041403103060040301030008094901c242c4803140c3d2100800c4081d02c0620507014020f5008414101c0d003006820310034054490648203003007850400802e81e0b54000403141000451a200c8403001c1000e00b940303001c010740790050220702d00400210204000380c00b1000b0705000b201050041020b020000c81e4400c01010a01c82c00c854150380d02d640d02c03441c005016040030704c500341c072922501d40482c402100c0140340108407070308034603403610b410f15061146019400013400c056208034100d440c04000b40a4150414640562441040d030811140c40362810400c0c0401000030968940010082c050714001403002c128000713414290340b1561240700103405002c1d280001007404400300b0911401c140d1903010107000703070008401401101811800307441240c0d4244142800201155010005810725038000d1b401c983c0500d201280c50410641 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 392867005 1250 392865755 392865761
    0x60108100f0f0c1d04060308071b170705010908030406020703120c05010f141503190501270b130510020f16050d0e03030313060e151501120b030616050c01 68
    0x143c0e40703020500d601c4040700c6036010004851048035040340c04000d140d040d6100c00324540a4054018841c44100340f03c810407a5039540310303000078050410a07440142c020640591940c0c15032041c40e01044400c0808074226078044240c030261406075004044152550f101c10a8510100c0da14034140640c520324200455000c0c0213656010f003500e9000b255030400f0440246c0401c10007045480c82400c0e407a41400943d4020840a80d40490107005160040c018240640107001c08140c222041d10741e00302ca10000e80c1d008484000c02030013035280103500d5032010b0550401043c8a180104030790841401c01c04802c05540c0034001743c2885091280c2428402d00715080e03000c61400b400c0d6403d920aa48101d00540c2c02414044001c00c00d402540c03c609040e00001070180c240750000f0280354403505c1d8540e03c03020401400c03005029100341f02115040011036001655501030010b40000c081034580300041100780508160210090024041d9a40c0c119560010a44a03060501040300410807907080d104240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 392868255 1250 392867005 392867021
    0x2e050d0b040203010b03040f1a0a090b090f0a08131706010510260417180306070302040f150e36010e06010809011d061e010b0d02030402150c0c04060503060108100f0f 73
    0x402b000136aa02541000b606c1c3c550001c02c8118264003680c620400d02c01d01045142e099584124142d440c0e204000040d81c40840c150855481407820340e8030105442000100241220800d64030b4031800c014207a011142c0c0e00b1a03440d1040080c40320604010050100d11010b0f911074001d0320b030f01007500414502c4850a40c840c42c9040030545002c00c1d201401d241c02d10445422601509007107290501d82101c40c50305d00102e101d20082c010103d61000c00c61030003039884200f0000000c1c541c40b40206401c2d94070100c05c0054031866072041c4404060b08170302400d281c24078180c0f1030410703a00c401d91340d07403c004680c070001c020f1410845549030741441c00d039984110100c00b0041c14034405003505151a4800000110f90104c0102081c05074030010801440c0c90001c56410665000c00903949a81c0c40c00420001078203480c50903c3c00400040c2c03100300000c08204d84005000c112400d10072599141c0805580301401c0c06499490340010940c40c14148859100c1189005100302c082001d00c040705859044074030b80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 392869505 1250 392868255 392868271
    0x20f0d0f050108030a1202131a0a020c040908090405060111030d0603022d01050f0909010306090308250e0123090111070608062e050d0b040203010b03040f1a 69
    0x10041212005000e0041e103014181c03200056003000c04010000b400d100b2503c0004402c45d0740000c075a411300441200c41d9028284000e400702040f201181210082d900801e10000103000d1200c2c05001c0786028040d1034005a007095285007014120030401005100251109041c016a1138005000c00d80510250035041d03084180040c1551460040c44144842c1c14011032440d540003c045800001c180c441840d526000e180413519900d0911b101c080e1031040e4218a0342c840700e000e000204000305608079004580c82595801c81a07111321000404102d440051361840c4c1ca44515180c403071500c41d071b0316440400014500307034141526203120450b40280301010310050705000900e034681542c1000c40c550180b200742c002031003400d00d450002000d406014005d64401d001c20100160b66a6110340f141005840d52102c201140c3e1b040074018100b5482803240802440c01c04200f01000e190600c00d40303040b03e0300d0b003800320b02d95555695102044c902d021070440c0e03680d11505c7c10005229882441d107204002c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 392870755 1250 392869505 392869511
    0x50f06070f0c180506090f04080c01061401090914070e060403020a1217030f0103120c050d020124060206060d02041803020d0801330302040504020f210714030703020f0d 74
    0x414070b5403050ba100d40103007141c3c498181010320440f500c3d24019141d00440413090505103031030fa450a0503681c8141051b0021544c201000401c0450400d82c940e1a850400d0322141c0c45165561544016510032450019000324450002403006008180d550038068004180501d050340365400210030f490f41d50001c1002d030541c06402da003000400308074100c1c0d0a0412001905520b0006402e20080c2014040182401d09200d50000704038010721007403d2469005094810034600080001d000f0600080e1404402c840f22100b8039907020406d1460055070703c00d40c0642010758950003880b510441d0f0b01e1040340c010340d0303e690312100c08091890b81c00c2c0c0b443c403a034050300d600c0b204004020622041a001017142c50b030039034980756151540741d42c2d401b245010031407810b4001d516090242c000f405560b04c11a000380c00010701183d070101c40c0004000342c800d558040c0c40d00300f9001c5601d0140d00011580100410b0444900d00420074004002c0d50380300c146031501520707150b000140ca54060f00021911100b40d52 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 392872005 1250 392870755 392870759
    0x150d080c0c060705030304030c020d02090901091104021905090613032004060e0105040c030e01050117060c030f06130902030109062901020d05072102030a0206150a050f06070f0c 78
    0x205000d124400700c012541c150800c0c0030b079150240c9a01c0b01a000506100c80300190008548400c410b02080c1500140030300014541604030b14068080d01c0c00442e0741d01e03080c00080c1e141c0e03c0c1c18400d4401202018800580c507003032040c8151129405145c401e540000c0510100d2940c241040300a00618440e04908043c2d024201164094001a60109200d642010402d002489140b4141030458408903004a01c40050740f00960041c40000301d0803589500309400414140c9400660b2148202c41c2d81c01ca88503070303440c6c2032000610300050b2500810000c440000c80d82e20324000c0e0000070701d095000000540721000d5400217007140c081d090700310b401c40d03110036a109913421005070201004c540042c140c5d203804040705c0004c0d1564581640401030040100d0383c01d05102032750000010741d007072041c000402500007a1004c0e40d0f94000701d407130000500c18100011034044a2502c082d104007005409140307420300305420045d05020618003180c210b0802d0142c0d101040e100b000c0341000502035441110658 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 392873255 1250 392872005 392872027
    0x30b09030901020708120f03071704061d031305060702130c030c030c0206190e0c0303040e180f150a110304030e0102011527060b0f0301090c0903030c0b150d08 70
    0x22070b15848010186c1004042c2c401035240c000c100c440b1208014000c5560b55281502900c80c280c909000246401d0700400300010040c00342d105d0102c8018024491908802d490141c1d0794a2180c8805119a00c4c03070b1090410040c1010005420454401000340e41c2074a2582800307070031100307655541c0002079114000012210703018070640e1404043d03407010b00382e03610303210a191407280d02c0b002041d0202e550b141480860040d042c8905c1608000040c00d50b965030b503403041e481c400c03c003055500341420081c806421011410004048e044070000002928171100c0741c0200c42d50400300288800d07007103921600e002d0702060001c00150301c0380d886500c07005481d01400d4002803c540c0003a08243d68802d0490043c801011100071102085503202c405070451108500230700040c11080d07010b405400b6010440007031100c107400203541600d40611041180e411288811a0544494400900401c042d20342d2140454103c1d01401d92000a141e0490543c0d204440032842d42015243c043c0d0f28940b02180046200f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 392874505 1250 392873255 392873263
    0xa02100e0a0f1d04030306050d0813050907080726010605130e0108030912390f1302090d021005041a0406020304210f0809010e030111030a0b0a030b0903090102 70
    0x3502d0142d01d828a928140a0b0806480e00c40911803034543c0520800202010320982021010f0300001d803100c01030b4001c03440c0c15051078000380ca4550b0401c0a044011036141005c044d801d00c02c40140c0d850711299240c400b01a1040b0b0f1414070f084100303140d00001d03140d00c2440008010300900a81d66419502e47c103090110600c1941900440700620321200100903070440001a1109400101c6011a01c09101d03150649804841580c18201603078035079000e07500303600582c8a0200e002c9502c50030241680c1030f604000c9175218007915141e01800c203544110507140154080d02165401030040d54180c401900025920440c050956000a100003018440b00d1301d20f1140e0031001c1c10100400e0309241c05c140000e5100d000d03d008525420204030951017082e90780d149010f12058000718151030010841c24042c03500d901c0002054041a0315603811100c40c00c0500c240606403440c804030b50304540f2503001c1000585407540300c26074800d403204c0011000c80d5204d04403d020f44008030045a07680070100c0060b0130 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 392875755 1250 392874505 392874509
    0x31303060c0309170912072403020301060503070c0609020d050f0f0a0b010510090902042c0714090f040e25030f060203100b0a1101050a02070c050d02030a02100e0a 72
    0x40608105400c0c1c001804204501841002e84c00220788031203901000c142c030811004034503a160710400300005075448890060f200081560702d0309121a00304000d058080c0c1c442031040d04002502000040c1a0380d21440500c180b00d031007504040307030400d40b94001480303200c2c3d044803c0c2c40b980c10040c004020441c08010030242048094060403000010352168900b03410b0511a01c3e00408520030807801c0303584280c40c400c0103000ca002c1f0864483d07482d004c42010621001e150f00040d0090410f48580e1b1818420700c89100c0e021913600d0b082004200d941c40c0740f00360020b46685403c03c12900c40b0903c2603440740100c8640b00c03041340081c140c02000d6505445a02500100e0342d248645840d401d02c04254800110035030385405c4440541d40ea1114142c641c9480d0040d4085000c00c82d0220710b081c0709980c480d40790203100369280000d0049031110301e000340417403003403040c020507a800220040003282420114602510f00060503900e07140e800f0340204216584101c020350005404140c1c1c104281703009890040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 392877005 1250 392875755 392875757
    0xc09010906030f0602031f030c030201030617060a09080c070e040b07030504020303030a0c020a0b010303110c0405191a0402130303080f040b040201230408070614251103031303060c 79
    0x5034924540326030000741c0f48228040c10403600080081c1d100d030500e555004450f903942072000811a900d0801050f484d4503404202c1c000382c00c0c12070008000100f0090b420b01c000104010b002c1e130380c0754102e50000030301c2c4907502240d0040051040080d420f805003e104020240c3c030300151030703c0c6001d10300400b55a90082048082c146403105000140c0c8002080d2175100c40010400942c1d001c000d41c041c2d241000e46103004169005010002c420140c1c000d071801440385408080725516007a02c0200000d960044404480b91490743c41c2002e24581583c00000791b01501d42c070101440c044010100d01070381d0003102480c40e505080f0104200b00360344200101d900100a0030303818041c0c24203999074100c181d0701400c080d0400413401b9100c1c0c5900140d0304410081c00b034000e42c00e681c540d81c0709501901c0368054491640880d500710120207245041404455030324100e050841107a00b03490030107103640e2580000030750300354940c824140c4407614100000c024212210700c56800c0685949413910569031100c00c900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 392878255 1250 392877005 392877011
    0xb0a06080f0f03070b1e07031410060e10110303070c030f020a0c0e070e030105160207060c210c0c0b0403020a05040209030606060f121e07020a0c090b040204080a050c090109 76
    0x9400501d010041d1078038241d0017010240c464130741013651082d80300004440c0f00700401420034400b40c01d4047e80040c140280003200000c855032108034040c0c5286941c40f500700496a00c00080d00145007102440001d01e020b4140000a91030110030075207941c1046071007102003000410301d43c05264000740ca00780c490107284002c240031100c5a0700c003020085a440b90010045c50b403c00728000c280140341c0c98482d207401400821040c50001c040a604526020042002d40a922030108a4500c2403c8840d140358000c484014140c1c0908190310300e89400500c01c0081001240c40c40300082d4010030344400074220a80810b4440c0e0850040005900c034540c845441188104640310061b10081aa168405070468840e0b07240c10507425075a8051203104210504400c85600300652812000000f10000b00ea03021300b1000c40d501d107042a641c411403c01c01604408c0a0001000550310a4026460341d240240c40542031039914880e251410380442c20071521a001080e88911a06004414034010001d000c0d0038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 392879505 1250 392878255 392878273
    0xf1309050a05151003030e040204051c0605090307050316020102070816090c050c19020f1201020403060b01031103011406040314060f100506040302091506131419120507030b0a06080f 80
    0x4101c424049105c02400e00c400c0c0c0102e01019900d5a040d10b0041c0b0020744a0640080780801312a010142500c0442c0d4440c0340c503000c03e00c00c0e5000025207540a5100c401107280040220341a40450f980f294202d0441c0308034100030400c907000703000300682500780c582050301981c142100c6c507064901c0c210320002005401e0050b0026004005146491480310441400030b0072607500100700e10760b10000c0d03425007144225090400e010720540c014030031a4003514003001800413200044003030b03072100c07a02018564002e00040c04400090900440c440200900300ea24180c0d495039103060991072851003500c1604070f0001c02c20480055031185510590404141c00706905010004081d4020b5010181c09444d08000240c00700e0029a4504c00c000002400079403100c0b010b007880140d5181780c0c00f44200480550b44405494201a42000b207400b4081440f04582800c000101040c03110341c4070161807a205038240000802c042101c0f041c01510750000100d11030342000b10080c5031075480126101c2543c451010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 392880755 1250 392879505 392879521
    0xa020a03031b0c02090403020f0d0903031710031209080607120e0c03030f0a02010207020307090501330e060909152d01361a0a0903020f1309050a0515 66
    0x2440b83d03d0350480d40c11034180c5031030500f207181810790348041509200b4a071144c0c81c142e4005100104881c4299250605004a183c5d80c0da00d0344030988014401000440040c0000f450a045406540102d0314021203605e40c0c5810461900c20700361b03030030f03008584084107155194140d409503010b040c0d110b60003424011040c1c0302095a911400702050708905001c40c898500510079011250940c0e00142220f840d81c0c1c0700d40c0c1440003070800307210318615504944852051035266141e2115040209074060309400ca80c80c3c005d03100c0300d4894070340c1580980e080212240aa0311120154042c0e901a02c000700024410003e0011350400c842d00341a80b08030302c184520345010024070500b466882860f04141420b02d862550700c807403010000080c16039254451781307034a500001c079007402103461016000b200e0105460b030070b0070103204450000002603443c035400e0015003042c805220440d040030b00109018a504201c034800c895240100b207941d500072000e000180b240400003d6425401c41c8418a054100603030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 392882005 1250 392880755 392880767
    0x11040905060a1505150a032a080a0b13050406110903062e030602090a06141207050c01090f020f010828020f0d021c05090d0507050705060a020a03031b 66
    0x1e40300010f6220090307000c09a00c0d440e030030401410040d081a103100900c0d6081150b6411841c02000000c0c980700280746000c0400d0f610070500c0c0c1502ca070243c00420000c2003110080f20041992959a8035a01c464115803202d000d0900c1200c4401000282e41c2403078030b40201945d02e2060002100035007401041040c0d0740c0890807a800144034000302e00603d2a15050704a80141050080110060387e800001070201c16001003d5103d4210b84c20140992580340070748241c007000c4a000404003041c48411808021982c0c143d8000e43d980c100750341003542c0c0115160a40c4d8015008a4036202d49a40100450628110182c0800c009080c4420f251400b0990083d1030a010380070240000c0307585110051012240c1d048580d2945003102550380d035917920721a00045e5104400800491000003401300d200c01c007602c01d00d8001d281c04030250200300070f8408229680e400288050306c65001d10300d40000c82c0e40d140d1004000781315007900540600c20060034007408171401c1c1c40903d21001d141d840103903442a4448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 392883255 1250 392882005 392882011
    0x1020313090209040905150711070e010303110a20010e0603090303041e1a0402120106060806040207061e0c090902120c0a02011b090521060a0207050a050102070b041104090506 77
    0x1c00058880203420f0010307004d000c240d007010300745001e0204004140b030310040e1014411062912a240541404ca40e890f55605846c4100458550310000610019103d0402448030790109000c44030780001540355000c14035134140700d1351050b403c9900d0381c0e081560000740e05200964100ca200d811072414040c03c40d00e030300c0000c0005240c6042c040700c8001d0898140d00900036181c1250402c0d58240d298080b007110a0b0041c0c07804d900c61007a491546403100c0c01402a135040e01c6481c3e480885a072189420f01029401501c0c0c100c403103d4440d0035401d1450440488240c0030159a1404190f181c040900a8005800b0760003200e0200d0042004018400300c00140c00c2e0815405800155610a0031400702d004100122040b41d040440744144500182c2c020b03100b40a03a082114003a07050303021880e502d40511140c00000544e81c00010010b50f0b080001c3c0e000d003224030301980a4035041c04e490740da43e600b240c1c007104040b507a290220f000c2c0010f000f0201c56044040a040e6010441c010f0591613043c5c0d241401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 392884505 1250 392883255 392883269
    0x316021f230415240b0a09050f18070203040e15011128060902090a0b010e0a1208160503030109150b0306030309041d010603241b030f1d0f060601020313 67
    0x32209031000c1d001342d401015034124a4600d600e40c49456000d2005d82e6480541c0c1d013000564840700108441c94007100701034074110300403c400e00c0d1080c14040e2501d540170091001040d07000a02c00011807140e655004c81c4513400f00d0000708842da01180c000b45c820f64901f00b02c004998803140761540301a0811a041c9110340c000f4103400180385c1c80d890304502806203000000d40142c5008203003c0040900e8110101c2d007102601d0355202c0180c4c81086c8010280203101c2c3e803644800d0018610041a1000d005040307842e02400040c00d2610951031341441d55200b0303030205403095942c0c480150b01d02209500c0d0741c0900f144850051440c109540001d94a000d031048a41c481ca5403150100c4a501c088840c60500003001e1009003c6640d0f6800d0400c0940c4114200b0024941e110056842c12a141c0c403616145018003400c6a40340b0301d041000703c00030811000140540d076a212044011040700e21410620382140d10000c10f50b140400c612181004c0e40607015605540c070500c1300c240e151080c0000e41007a1012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 392885755 1250 392884505 392884511
    0x30414031b0114010630180615090e21070203030c060735131416120206070f0602090d0c03031d010e1e060301030c1a0703050316021f230415 62
    0x60404800104411f4100d00849500e40c9070319030800002d50800d00f1204008040c1c03581c9160388000b070b60107945e0b007a070501e209504a5501d91300c2249525400c009000342150950b0b041c62040c2e4007191840c1d10080007140039030302c43c40400401c00c1e4441403040c5900000d10b00300105044028055403010720f106a0f00c0000c103a2400094021a104280084002d40110070050001c89680c0417507102c4503084120300800c481c850b004907070703a90201d40c07100a00d540941194601101c5440c1e8003480f94030f4050031a1380b0b41d0204500d045a590f070016030f01c11035000d20701e644201482d5150180025090f02529030300c903900c500c4941c016a07001100745110007002c1e11013111101c0101e000e060120740c00d10909501c01804400031082c0540350840300c0548a2a0401d6207540c102c4400010041c010007800a00051040000035280141d84041482c14115801264440c8030707003d908440c00c44060b0784406100d03999001c02c2000c0c9806500003291480825510142802e00303844480c0006220b10b03401441a407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 392887005 1250 392885755 392885837
    0x60f021b011106040602030106020705064f052b020609040e1c0905030601030f0206250f021c0506040f1703010602010605040b15030414031b01140106 66
    0x40a06420418400c510041d00d0f141d1529240c140e0003504203005a90040c421108003140b5400d001c0200c030303a00c80c0c50030740c1030009884c0560000d800c081d10701c1f8108810032450401f002a420503404c500c9440000449803003406041400703003d5200c240c01c02207200c8601208070b0902c60152807542d500e0050f01a141d0300d503a510020089009440440d641c0c101d68030401c0040c41c0000102e4541f100950010764440406503038410030155200001e010107410074221400074401440e250000f0040403220140c10b00300300c030000702d051a07034200704074040d5402d9004400c0201189401c0040c8207640300034100e000c0d4a01103e0721125590341d0000d00040045042459110030300c140b5030005c120100c00303107205556035a19950028040c0805106032800381d8100110540d0764a414007001011060b907034a010708560f11a11210403092000c158001140070810907801c0240c41129040c29240209001260040000b020f0078007244c0168880003c02c03c0c00b05000000d0355202440c1d1102120000850b00c07110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 392888255 1250 392887005 392887007
    0x30203041e0212190b010608091b0a15030507030b04050c0a140403060c11010c050405060d0b0f060a200106060f082805070206131101051602040203010f0f060f021b01 73
    0x92800311071100288104d64a4a20000c8828000721a4900c1840784030034a9988039402e4542000958903c1130541040b0f000d0340b4802e580302e5108180050061015052507a2a460300040e05207407840b040c0066101d0f8100100720b1f806000344003803024141c03403c000520344403403c0c400e00d0040d42401d00c1080740c010401c1d1a084249401c0d03501468100d842044464080302014200d81455013a030011542032251041240b40034009690031602d01900b228545184c048035000144178405686a00541c103600749680e0fa01e03500d02808001a0742c5d112864210402c0d100070349010710f080f00e50b280300e0303041802c1400343d503503c103540107007207009800d00306960b496440701200d11031814401d01e52418003416500342e00d00c1c0c40350403503801241c0b5034003030f078501c0c2d1100c002c50138449a107050068460fa91141b188011948a0030007040d64169081480950f49071035400201070303900a03400b082c1c02e00000c94081c042d55115520040082038142018154030401100c0a9180c5a88000b03154500e002c10441d09216 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 392889505 1250 392888255 392888269
    0x50907210b0a170c03160305120a03020c0601090b0310060b0a03090c08030307050307080a0b010e01081005060d020705010605010c031b020d150f0b0f210c03030c070303020607030203041e02 83
    0x10786001e008412140855032a107560384c4007503031442c0d17100380b01d40106500141c50700c07185003080e250490040c05181d440600c00300c0c01030f40040242c104140e42000040d420789014030542e40a0448204040b540307590240070140f41010902d0851056898407004002c0307030b1210421600001c11506010446104a040844804a45504c010100d000010400080030392140003580f00c3d140070b8544884a841340c8801800b180c1003201c020340401c1c400075500e0303821f601400041c0d40c00340c0114030350b030790b003035111408030303250343c00c126201c040443d0046840010000e0a004160203480c0a10780700803140100d07280100701e4901d8500c0030301c2840c285007a200030354a030304030f03100800354012617109c0c0c86190140110006200c03105154808901d804070603822440d080002e0580759078001c043e02c82e031450f040c1c101003081051055616062007010300302c0c059600c00b8805060801c00c1d0341e0181207007524500b80a400e000008091404152042040100040040072503d8460001a100071485c03403a5102007111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 392890755 1250 392889505 392889509
    0x2150709030f1a0c0c1906021303081317071502120304080c0105160507140a1b06080f22030921200306040b0408041806050907210b0a 59
    0xc0c000e250880b1200b400355042e81000049288524060740d03998039120344080d80640e051240f42c68020006d4503005048210324110044e00039000145012400f000f42d424486080d40f0843d020540461174194040c010740105004000005010070312024807451103031501910702914049500e10744c01d40a0319482080f500201c81d4150705550350ba07080030304203200030760070600300321403903600f0100051030070841e03085003280e841c5140e1101c034203002d000d89d070341842c204400342c000d00c1510a01d911040490740540e41d068244400ea450540f8480c24088001c00e0104002e02114071402214240461107a9180302203c031003840d14003400340280ca030710b000c860b83c98107648070315a148030307031304a10000501113440300c48054803a54035541c6221050406c0100e2195404805515410210000c0e002c91804802c0b80d910a104030021860182c4508240c1200088081c5808001d652503034240074900340340002941020340da092a030000c0d02c207025043c1c007800c1c1103198a03180c81e0702d4412600d8141c80b030500001c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 392892005 1250 392890755 392890763
    0xc0e1309170702040c030c021b2205190b01020304091109030115090b1804060509150f10050f090103060f0f09060b150313030c02012615100215070903 66
    0x3900d0404003065a580782c02c4044140d119038542a400704020380248100f820080d21900940a207401c0c02501c04001342c0440001c03a04800400000a10f405429451902c0c3e45802c80d030000d1503041046107821001100104c903000541761488842c4c250ba00081076404170303900e050b40403031070b40c4044201c0842406285020342e01076080403141c450344d10740c131342c00c64044e108084000c001080100c8200602071444906486c001c02e14003002c074001c10031035040700e644407138440b0884007a40169106082d501404650f41e0901b54011000c3c00503c0c0d21000d0190000c101c110b5584210325000000100c0c2d0143c103200080045543c0d00d031008203810141c00c201481c0c414010108015038003401c2480c05417000c9050750340304100c51001424019101020f41e0301640c0001151400da401e25502600d00303403040f40e82070381805611038000c00c40317080d400e41e0545540c00c0f003020030f031041c04e00e0703030100c01c3c45401401060b01ca100c42142c1c84030400e81c0000c0d130310100004aa815400b940b03402c0c0d0190381e405102c2d00054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 392893255 1250 392892005 392892023
    0x604061d07120c0c110105130f031b0303020d0324080703230706120f020309010b0a06020613020d14060405061f0e040b04020a170d0e040c0e1309 64
    0x11850400d440d6440c4961915200c0400512084011104503680614528007054200781d0b5000456105405441c1c20541070404030701d084190200d00082e000710f6030103031401040580c014810040c60b180440051094100000461800c0d80e42c003035128500f08000508040e6036200124520400b428080d448980c0003100500b42c6403903040f640c1e1100241d00058900900500e249109030040034030201c441c061507809041d0072410300c0d0003111000300c1400f400ca5015182da10f0308116045a10085000d1084400006840c004560502c08044545e6100c582950000b0041042e0317164141d6003001c0300c0c0c2d4120703040c6015498a140416201040c11405030452107030000300810400c0010341ca41c00f942e9880035003420060920215406c01c00d650241c02c5840010070003042c0041c1c841c54041d40c005200415000e8a0742e05c4003040101544030031028180355125000c8071a056400001c0702c48c0303207071007645c00303000741883e0300c130094000c1c451000e10324014804100c1000044507540c1c41400026448901c0e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 392894505 1250 392893255 392893289
    0x10603120327030801151416061b120213081617060907090c02030904110918060603041e060606020601150309030207090c0c0b040b041721060406 64
    0x10020b010400c003500b41c9200000d00c50750002c918141e100348080d45a507484103141c2c01c201182110b079007012180c030b0038032075011800a10808500090401c009030710354100d50041903800e00005403000910a0304602c25a072010300400d941c0300820000c40a0002e0b4096030310145108039845500701c99205032060301408135820050800036005008445601012001c080702c0e0700d00b030a486a00684001043d41d100120030000b03444d254106074501c0034240184c90401500c14040b031709403849000c1c0c1000c620300000d920511441d14a081c401c0200607403004200c5490314170003080880c400a040602401000c2d00421184880280494407082e400442808500d030b4460000e581d8a90038081d0803100c0c580000d07203906c1d0034800e01c2864a07070b42c1c055005101240c030308001600244103024a5900700200c00184601040d41802d1080c081c501c0351040781050324090600103d26480703051007440c065000c101d203203e61042d002124408888103076103861b06840306800100140a26030100c9941e161103125 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 392895755 1250 392894505 392894507
    0x28060218031e030909070e030d020601030303050a0204030f140307080415080612030901030b01110f061501020c0108071b060504030519090f1403010e1f0605010203121801060312 78
    0x503006105505034102d03100300b2150b000c0d5104060210103450300d940d0052100442c1441c3c50500d4a421446601300540b001082401203410514400c01080142e400030f0010810143d040c450140d000707011a0307045040505640d00d080c05031b051020043c2c540c41048000c0d40b48080140304403504c41d58022500c03540c0b9903881d141840b2000b584080d4801040c64280061018101114003100750006030001d50700d410400e10064000740101c032842030411442400307460010302c041180c41d810100d0300000381520701e0f1841c0244020800f41117001d045402c02c800700320540e6041460300d030704100c0608086007030040d20050885020708144004d4150f908000a00050541000003002803404001140c2031201d420807054840a425118000711180040c070200856080d4082c208201d130300c003c0000c961051025001c61804032017103040a50030443c0240c0c040410110312402d401000e0a00255080010381c40c1c0c04c0c441c00c00000d1440c1c5a00810080242115500303502020186a01c20900c0b06800704400c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 392897005 1250 392895755 392895787
    0x150703171e04051938012106020c070504180507032406091a0a0e1b0903061509010909080306040e030903070803091905033f0306010f0809280602 64
    0x102d02105902e08802c0b920320401060301710052201d035542c1880581c0d2901c404110f038140d003000c10800c081d1903543d9034000a60113000800815110b80014100c86082c0000c0004440b409078510b06103d40c2120b04900242000c14000100c94011b03050015265400500305012800f980c01d480403146894800b040441c0541c2c4030706030000985182d2241e00000c01c00b84071140d4800c2c000c1480e5016a03400160800801c80c2e140f003284c040e4648000c1c10403810702c4c086441c4c1541542c5600c1540c5901172280d80301e050011b42140102080c80c070070720009070325440d0324255100107404a4001c1e034a03402d01010042c0708008442010710090200c0d06002c1c1d4900304a500c0350000c0300941d21451003c04000c0070707002d64808103002c0d02c000501414030b202c001c1ca29003411945600f08602030044c110121406d01c8030315140c48407214081c103a860384e203180079400140449030040c41c1c2c90501c880741c400d00001420028404170019590703980b1104601e00951984d18041c03d10714010102c07400020308842d2002024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 392898255 1250 392897005 392897033
    0x1d06030a1e1709030a0605060607150b030105160e10300f020c070b090111060a0e120a1d0103150b040504060902040303050307140702150703171e040519 67
    0x1600031100380d0b24210038641e0358440c0092090b8940c0c00303090351401140480e8069904654024100d42c54002ca03036580b404200c0701c4d42c02c0c40e10455070b00d6640038440e060a025450b808460301c050080901500c8002504200c070f9100300601402c0a62605640e00e40a0180c060001d03c100d4460354800c039291a800c040c02503442584c1003d64105140219040c400307009a07100d52000724040d08040c4d04043c00c0190300c1e0094070001d810001d41c0c80e500180d84030140100b038020801c030800465403224010b040c5d4a0803941000302203070048204049210b055001c0c10b0294584a010020710160749060012805007065014410503a161041c001508040e500e00034001c842041d101402001d5070390401100700d0080e803001030003003001000010900c41c490150320904c92032015082d810041c254020940d2a955a803003200c0c40180001c615080c15004031441e00c144a540d0341c0c0161520300451002d504082e03a5017264104401c40000c541042410702c001d41c030311090344c400840610301274280784031201c03115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 392899505 1250 392898255 392898263
    0xc02042c0c0a09020d0b0d05030301060906050403020f130b061602010e0a06080705070f050a0b010914010609050f010201060e07020a0b160e0d0609021306090c091d06030a1e 76
    0x101003074a00c00c100c001801001d58a14040e003040180d81325a0180c0210f56850103030140503074031142509109402980150b4130303981001809000200360760000d10078000309103c20801a43c0d01021414910310a5071892031444041300c0c1c030005043c40c1e81c0003552000000c04d03a4124800f000c110703030b00c010b8002d90381d0244061042042c440005450f0143c1c90006a100d0001500c103030050004200945c814a6011707081416501c1d810b040050301a0103c0b4031907407407001002500c140b4000c000d40c4800c101116191035161003800ba003100514440c2c54050011200c190219078001e500003c0140204160342e00c00d881e0200009441c0c01c0c0c00d007002c40b05e800c1040086208080004038540b45600140c885142c003030190000c00c01c542031400412504c82d42ca07078440c0030040e15041c9a80b1030100d50a00d001c00c00504282c0a00240d4000c801d0722402c00000410402208000e6030000010851104030710701c0d00e840f5040480e06041d0350f62005850124a40c8415003801125100003071180d000f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 392900755 1250 392899505 392899571
    0x702220c05120402040c022a1e0d15180f0204050c130620030a020607020708010903020a022e0503091501060203030412020106050a08030d0e010b0618010c0204 70
    0x980c5205a48900956070a1010340328000c00050041c28a940960000202c41c0101c5210b003401081c40349441500e440c1c1854084120f018032241e90400d452440043e0103171480614100900d000844c00c0303440c3e0040081c108110340300145140102d1588400f0345000018203104050905080540b04004d03072102c201d000340d241c140090080c840600544031040c0380420009844d81c517280701164403007510290110f1241e40070001100d030a5041000702101d000a4015180520780b0740c1000c4d0821010303612285840c8d0500401c28000b940c08214224410340c1103540880030b18410b094900040c651928100f440849550b030b007400c0310b030408040c61007240883c00311811312510300c903900454a000c0c841c100140c0e00a00c0400e0001d09402049011a41e0500c00000d22950750740c00100c0329a401e501c51001508005200d841c4031846001c0d4540c1440030344002e10164a5100100e0181d202e1100924200c155190318001282c1c403c50316464900d030018428018844520100003200c2c1d91a000c0c0cfc410960 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 392902005 1250 392900755 392900771
    0xa0b210609060312070215070f020a060f171e01030c170c130903020c0316061815050703020c030a03030212090c090601050d090c0602070e01080c0f0d08070222 70
    0x30380001e01e1440b407080075002d844003440e503900d1080fa030b404c6441c04a910030030011a81400c0d0380c680014100460060311500c8840c420b900601110400b035820040401892144128a10750070488446900c25404991002c1d41e50304200c03203d2107212500e054442d2100140000240b0040002d0001170754078414000425035000c40310155158100e081d45608074408900000c566600c80d804445100d00900503155217805c4140003034100b46116102489802c4401ca050109542c04080014100d0f070b07241541c40304504113101c01c001c500030401c500c4200b00c0005208000c0610900007022100805170444064214078980900650091a082009440c002c000036041e1040050100c008010140c00c41c1b90070b072106001195294410583e901d14651030f070740b5a2000a00b46000f141c000c1041d58090020310742003070711420210780113a100000d564411000c0d1805592182c03108401c03e4400c440440e6100c5180c5040202409030090195000b1410b03d0750641b614070311403103018825402c103000c1180c61 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 392903255 1250 392902005 392902009
    0x4060f0908070b07021206090d030e0102180d020d080c1b040b0a0b0c03070c030b15010c081207090b1c05061c0204090c0e0c07030912020603070e0a0b2106 68
    0x102092203081690b502104042003110030680040c40d829001422450004d01641d404616010054a100049912035031071800115454032030500321180000007946819103500615544191207d0342520500720000d0a90855840014500d440780d4481c00340d54032403603200401601ea80f00030040401c0104255242c0105117094802c20540241c02001c01d200581080410345030390b003040c0e5507140944400c0260b100414030510302c880040d07100c1c1003065824942181c0301d15001d03078000c40d4141400030003082400018014415252403410082c03000d032156661074003c4070304c175006078042c1c02c0310b04c4005a241003040c6080c003440f0035611000424010f42d00d40d002480380c1020191410b04000700c04c501000018601034005083c0a401421440049030300c8081128040600b5124402c01103000924801010b400a00140042032003940140302a0155008039005201c0242080200205440c004460b03540b80100600580219480540c0b204c0343c521080740301210f1400c200c400c000c60013000910324 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 392904505 1250 392903255 392903267
    0x1b08060f071e2607080a05070e1305100905040c0b160b0c07050f0c0d0303020d090605010e10060302161506031401020c070f0f061b0602030406050105180603030417100e0304060f 78
    0x5040e950ba40ca05c0d255100c0400381c0c000c02c000f602100401041c8070100c1c65a40c0c900715060126554800001414100561002010340140c3d004040040c01c0400700310114203040c0340c034011500501c511503030381c0141c0c040703424610700851001402104d2040c203200380305141c9806861700f60b215004482c826603074000b4030359459480c0b40c0029400000400c007000020321a030041c10707014403845000301e24080550364010948000340c00a0341c034240030404008025801311855402001681400c610303266002901180b0203040c3c020107406002c0c410aa51800600d9920900046403c200f02000e04068130b1002030203503003c6018040f0b98816442c2c0400e2030140044900c00b02c0d07035050b030b99040f89840c1c002c00359140b070720381040350a042819a0500c8046601130000f58406c612600380003a413503041404000540314003070202c61001d5554420041d0301d450000484080c2c45065941043c0c10a103100958a4003c65918100c0414200400c401e000070001028100380d401c5515600c03082c1c1e108000c2200e42c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 392905755 1250 392904505 392904511
    0x30504120c0609081603140301140103020702210d02210307030504050708100b0117240607050312010807060507030c1506080d020a1b08060f071e26 65
    0x44120042031200419008451451a0a02c54070002c200c00c1c0c0d06440700405504001c442c04424054508550209544a01a000644245401c0d40c0c2075504001507800d04001404a460505a00298031815075607141c040400c01d01d0180000e0300320708909410036440b4054a0110400f602c15804103803503641d20345400003600054101968159503441e001107003d40f8000d8030913a00d6001e0304501280010040c05420f41901030007a011842040c031400042c4002c1150000000201c0680c0900c00b0b00b094020258003034580c00d54a05d908001c2001c0002e0307051089080041941c400015017100300ca500110071412034400d04140e54415035038010035140c51181c0300b801270006504484520000c1e8010103201401210940001061b6860f0540d0354540204106004050707407245d901e0b45d041001c0a0504c00a0300c0ce0030b910b030084689406480341e0b80b414003600362166484144005143c241c4101c05005c42c07003031621901044403258081c0540314158002c100c510203001c5516003e0681c0317040d811350340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 392907005 1250 392905755 392905763
    0x21303060f060b03160c20030706030c050a0c0201021002120901060501030915020d06050604171605010e091506040b0c0114071205070905120304050112060e040f210c03020d030504 79
    0x491959072040f580d88940315105e803c01800405d81003140400e1040d1b05214102104140703e8107400e0002003018540211a0f0161f000c150806c035115800c80d901000356621000d403401c1c036501d6070020b880140d09048418200a411310310105d007008000c3d440840c0c0d540a100004020000702da00c86c0011001d654030440701804101022616840c0320916900412210300e50a20000d41d207620ba02c0003071ba50782d21035840b803a400c1d118000051000141170100742915000d080038110441d15040c00a888105000700306441a0f01500020321200300c260741d40d0351032400c01003030341d541c540d1034802d484859040364241c0301107903290903100c0d145020300c1040e00e0300840082c1c59030f0028410f1007075154042c080040000d010400038107400211038681c0c0404210710075a50000c0d645443c20600010031b2004030318255115141820703010001e041e60200c2e00f542003a04180e50700380c01d90039801c0004680e9020b001458111030002003040c0481d034082c0f04441c040d88654203494484005500440a407030301a14090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 392908255 1250 392907005 392907007
    0x3150403050c0a02060d020c0c040c080a0e03040b0a020f1005130b041103010c0305090c0306010b0403030e03071e0e070c0209160309050303090105070e010f090605070c09021303060f060b 82
    0x801080c0a003010b801c1004141d01150348000321a40851081c1e008035002c2d0013216000701d0f000808003c24070145641c80c00c150303030800c819160b03140000c0c40c41c3d102030108444280d4859074446603100030b004503400b5090218949603561510300c4029500d00c04008040b0b5a405074007024401c070f02c2580206400b039944038140e9104440c06449161224201410480c0c0f107082c40c625201c4030b130306c0a010380264144651000a410301c2e02000150501d4103080001e03109030485001031005003c06d000f0b88042c0d0340c00d40303003540c410f0185030003003440e043c040e822041c0c00d80c1c00302c4499606021504a1101911404100c3c8511500c81806c2602d4810504030002e42c440c000d04001101d050440c2e20f5030032100c2c104e02e00031031b203030f0416160300b41148c0c42a03e00c1c4c8000d946610400294941142000101c00000e180000c2c1c07143c0107800c01001c08a0b0741c00f0700c02c20001c0c0007440b14148080070805202074026a4411544c403d04006460b00c05641031108030307420b90411542d0015814240715020444103010030b49 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 392909505 1250 392908255 392908261
    0x30e150601110d121508060a15090902030312180f0f0d0905180604020d060f14030312010909050a0b16030f020f09010c02150415030b0a050a0e0a2403020a050315 71
    0x10308040c0c1740320b442e06464400c0e05000014040000c2110a00800705004005690790601d94490781e45000f0f03811180450341890041001620000221484984500300c0300c034080c3c07039403940d0707a101031f018003071481d403611175001a0000c076072003ca158042c0040c2d079802c64100401400303084c3d506402c68496287d0203808a81d070f034252301da102880c440c3d109400400041c504550802440110390203a00409605c0300d10020a02c0450608000d04a190004400550078242c103914200d442c82d0f814003031000c1a985071400c03c802c0050800030b038a003040e88410008428501410301c03802c09201c0c1e1184500081c204060140055464421140003043c84071040b031403c600305006603030024000e402241c10803104950300c203000411502a001420681817414488803d0900c0102584c07040c0203110321421044008102907519111454111203200c0016002c558518000900412885c814942d24010b0a1040d60018400c4000b0f0030903640b0031209520b0303442d20395007416610071895090051042c005804 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 392910755 1250 392909505 392909537
    0x2010c080d060b0c0a151503170405040212061009061e1815090614070b040311070303080613020f0d020f040909030807090e09061501030e150601110d 66
    0x14180310320480004079101d542c882e08a80c1a52003072000e413044ea002600d18004102d8804011035912040000500c5140092040045c00078200d200013094140d200780441d40c4002d0321800d0702e00401004004640310401c0043c0640186000c4800310700c15a04024801501c40c080c14200040e20441d5864008060b070300380140805110103441071342448142041d41074680300c044586006070000c100889610030300401c1c00343c03091000d50000000c0c80300300c1107082c109003e02e406440066803c14806d180a807560305095130300c08044007000c0801d0081050100c18140c1281129014040559020040809043c40713a012800b0705802806c0121003040900d03460009a0050200d080344c1e105280c4c87c01b56952031120444981c40d800710301080d030050422002d290040c02c4c0000a1012451982040c902038141c3c076210720000340300e20003503880504100d0499119a120182d9503007034504945011190003038107009054116070583c0011008100343e9070340d8601040d0001001c04546a0700c60015908203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 392912005 1250 392910755 392910757
    0x6030618090f020f01021e0d09050102030711150913060305100c0e040506030c03240c070f032d0206010915051804062703030606050f040501050d09170307080105090402010c08 77
    0x84040c0c110b104400f1070083d0701c2a21840d0001f606c4144004205041030080d0180c0340382c84a0384410705540003030240102041c8030070700204801404590541c14000090b1140c0c01d140200f141c80c80e004a84d03c00c42003002e1042e640024140d0f8010f208440c4407049040d91001550311a021650010b081600441100d040a030810b0b500b201c802030546000360920303000f180c98603012505500c4030045203408140c07800380701840c01e60000c4140c3e069529040854460190b04030010500038200144040000703015608011071070300415603000b41c11500340c042c0c040295288020302a00001c40d05d011030b9000c024400b010000b0481e0005001e0080c3c13941d4890101d4402e2100920680381244c95260100c0b9140341c000141501a01c0590054100c080b6410002c04490760794000c1010302c101044503040704000c00b000d03a01212000d00c0d0040c0c1e116052511000074024406c801020084581c000703c40002444000c0e5100b00c00c150b540c2100760380d07640200101c143d0241d4001c0c0c00706403803c0c41c1d1004181004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 392913255 1250 392912005 392912029
    0xb04150e0a05180408041205060a1404020604140102010b0a0605132301110102190f0e0a0f051e030303010609050112050106050d020a030912180602010e06150d0c06030618090f02 78
    0x26025007060b503294110304201d21f10b46400c0764582c10400030000c0002d041e1150788611601207868105a10703141d0f000c00c0082c822801841d04c012036091f2200b5217a8802d4119403484500a000302e90411303912100540a500312111412048011305070204498981220b06544410f118464011140f8074400540700102e4034544940b05540030050344040408a13228083c00d040280c1d141031055220781401400c62020494041c810f81041904000441800e40719505982c821140800700d00718880311a030100081040003600f5010200002410b01d810909034411100280c80c2d9240f000c040c58802001c4400900515020a109000c03da09114103940034100b07162460a000030701c80c91545694031803840403549030000a58228002140403401104034000b0321290000340044401240030a8680c2002040a40c1408018501028070f43d95640c100d22055080312458070110307152840203000e4002401030950300c240503210210700c000103215007a20f070340d005107030010300c45807650070049510780750 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 392914505 1250 392913255 392913263
    0x603060102162601050906041704050a0906151407061e0e060106030e0f1905071a091509061624150e0c030705030408040b04150e0a051804 61
    0x700451408460b04a180b103000303031104107064800007164414003603003880700107044000b41c0d0500c1c086c81041c4000041041d0883d80c0710051050500f40203102d0107290059600559000078004400600c0b2859039000c4000c1c1c44001014600f980360301c8030145e40c2041e003100c8510203c0e20822906012030120341c0042000000300c106d00420780003920030b61007501c512075000c0761950821704c010007605405114002840038004003800c1c1400d202c00519846141c1c0d82c0b03010320551491120441004030174801034010342030880e180300400b00c1e0f034504400141c01c01183c0c02d01500304a220010421105415102e10240c024900c5d89060180c0b01c4d03140e091980e0701d108581c800324202d190342148841c00b0700078500b000e020000081040b04140e01d041130f81740f2a0301141055908000340180d1200d040101ca0b0b100c0340a0520300e41c2c030386a0f4a04060303144607070340c8076043c2104045004074040c048141804000d58a81d0b4440c50342c60072130000c21003408114030400317622a030000841240c807040c00d00c107144d0160003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 392915755 1250 392914505 392914513
    0xa110d09020a3c0b180315090c01110c040c0233010510020f030309010f051b04032d0b01030317160c050a02030610240507060203091608060a0b0f030c0603060102 71
    0x24404102d00c4e035412000201d5000100000605400c0c10200144000328403003000c18440c03424040309158554001c142c0f150b04000f042010300f0f844d12810044203020400c09003080201030641d080094581d490540d4031082092070a91712008000b62412415440c4113840741c58180741d1a110400c24201c1c03801003000d080d0300941640754130f0310b94244040d41c031603104103002152400003803118000703e0304014550000340b804218a1000c201141041d1001d0f2544140e4080340512218030030300c209500e0261500c212152680018200311064a00d030b4101c0e03129883c3c04500380004a07500101110403656140c0352103002451480491084850300040c03805641aa11800b569230040303400c0040c2150050195034800208100d1203204d08045070f0071091014400300111340d049002400c03440b9844000d0300c05074001c00806d003800001d0016542d0450301c1110011b84681e1141180d850310300454041c0d0101c1c0c035040c60014075040c4030b00e503035015403001806007200045500c2000306a0300050070003411032207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 392917005 1250 392915755 392915759
    0x1e031802090106021e0f0604020f120a0c051329040207061104060f090326091c020102061518040c0e10030210030c170a110d09020a3c 59
    0x11060641806451144c2c050020040d00b0780745010a030224940d0200c83d5481400010361045c4013084858000358110b9070f4448001f40f403000903601c107a090210041600808031040f040044c0c42514a0480743c0c00e40d82c01200e1441949d81c4000c60b61883c801c40a00804030301e00804001001149240043c1d00400c01402d2100d00e4680d2001c4519100083c4e07103407180000c090010a4202c032001250f48010b14000350002e083d6030307414a0b01e54a10030140c03514010074040c44d100c041c40d441a42c0047c0301c05001c02c1c99006556154184000c0e94180590160240710081a48420213001800704001b01801100030f40456480d0344500300e0004000b6030701a81c3e001e40115020081005050180d03001c1d601000c052801d5004000010051900080915103000e412206c429003005c1d129908071045101040d01d59200342d8068050201d81000445002d0006581141d558640e030004194600070b031100d800c03190711110048844401e100301c48500320905400442c011100d0081d04140505281d07065084076 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 392918255 1250 392917005 392917009
    0x3060a1121041e2a090c08041a060d2405100305120a12021e0f0d110a0c0206030703060b030c0d0f110f0d090c080115061e031802 57
    0x4561242008a19040380180410300600c409900e0300b500710b0a003605440503681e95802e0221342120600010070100d200a0549a0666074107040200300080c000c1c0f050080001c002064008116001c90310030210f80c011107004030104c007c141c89a8005048014164100d843d82c00c01d1800b281c800c040001d01c210066a4000c00c2030046a00a8031441c1100c0459421460410300302030b00011014240c86051241d1300e07995a00c80072102406d030b415400160f980e0000f0344140c241c108141803c0b56089800902c030301c3d086001e44020200c01340700d41c20410010011003d00c0f031b400c3c0300d04440c00c00001c2000c6200005031030301c5801181c03c00030a040c0004e2a903903652100807960004c45201442d140003040788119900340e4000c41214022000b020404459000219001802000e5007006a241d010890302e94150704d5230302000e02e542d04000a410300b180d0b1000a030b0b0103003030342c00d9220301c1440540070009800e50007465810b500d07820f11003142110a985e900218014003400c0c03100c810740042c03c1d80f002c000d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 392919505 1250 392918255 392918287
    0xd0f091a09120601031401090f11031606110d0503060a14060417010b01090e06130c2001060303021203011a0703090306020a0c05300f07022112070203060a11 69
    0x11030440d4041c10456240d400d0401481080e0b09086d040c590400140000045484003101d610941c0f010210a0b02c9920030b0100703113012003d88032800490480980450403a8110344001d603095441d400b1035000300c051800458942c081921019084840c2000500807003070480e0081e10355800241c5003e091035a980704000c0750015600b580c1601e83d56540048100d568447c1032240604000b10384072090341401c00114103020b0040b0703102d107521582e44068441191191010800c121942c0c04a50017007078000307814034020403640c803088001d0300c1284a0f100c02c02c00b0090070b8be8100c030b0040200705038441c120400840203600006003101082503080740800050005e02c058400c440c0c00359107000702400c0c50301c1c080e2315200140c40e09039201c0c841110300e0881414540d000c0884200f13142085a296403a50741480014012580c00943c00800200707403407405071410080d10b41d01d0340030030103c81d10386800003011201489405c0307010713404da007040300015034900c11030b00240c00e004080f041c0b05d440c0ca603180175940b01b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 392920755 1250 392919505 392919529
    0x2090d120c0201030605060403020105030a05070513030305030a0c0f02060a0e0307080d020912071202040207060905030c0a0b06040c0507032f030918160c080c010603140d0f091a09 79
    0x100c1c103040d40703840039542d1500c603030307400b51a0650b819460035045800207006c40c04010101040240c40e14005030134503201d80c0688902d00340708440c2101181d128680a407031604100c0d03414a1492400c1d1419984911606a44072881c036a90081d29150b12010804070140031044601c0045200800c01c140026030120000c0203140040c100060b159030411003000300395204a002c201c00c40e800614207000c00c00d01142d2001c038071030341250016612a080c0ca010700280101140162482c0404210710841031340204040d12064401c0e240c2200da541c0d00800c000845c0c07900c0c2c40d150009072090007031000080c0503092460f020514400524a6a07400040c06040064441c41d036030705036000403e001f0340c00e00f4503d410540300c00101c80c20101e40c1c6840d80b242005540d6002c145801c211280b01c4c80800e020040342120680046240240b15054690a180c00e24280e01ca4a40c0030600c5100c0a20004510405948241d18000d950b41071405160503003410405c00d60f10050241200d04105484c1a030b5114250104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 392922005 1250 392920755 392920757
    0x30c0403211803020a061101061211030f0a030504050103020307110a060e1501030f0602030606071a0f060d05070e072606190e06060304140105040605090705040e070902090d12 77
    0x408028202000b08120000c2c0302d4401c40d000000c8081c00103079034070f91144058840c0c0386000240d07044401c41081c09000b00d603000340d10b20902081d44d0018410030341103011300300c401503003214031406860401c5a41c0754009030014002078028041030100d903209800454201e203080c80d049002c40707148880340e420141040400c541d03039a030355200360006034402d0001000502c40440c0c012025072440c5c443c100a003045420062203284e0000005070b180c0e4400007502c003070a40060049021113200000600b2465059444400c10b6904070b001900c1440d00303581c41501e456222000d045a14034141c140801c400c00981001700b0310298a05408034280ba0070000342d0f070810620848000b03810104207010039242c160390010400e800050080c001081c5201c541508600180c506943d03990b15818000c0d0786e03000804840c0429400c10701030200f030180300c2c2c10881c040d14100054499041d40c890821040f540800c400d0343d2590003807101003004034500d9014182040f40508100e06c91705644e654500014020b044280c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 392923255 1250 392922005 392922053
    0xb0903070b190615020703120908030d0903020f031b01140610030c111906050c031b0a090911030f06121009050c0402130602060c070c030f14010c05090102010506040507090605030c0403 81
    0xc180300520708210700c0d41a060510303807210ad00705031400c3c0e1079100d441c5000c80b0007902d0b4181981018800c01000e1004290001502d0315030f000b503690541400e02e07194810740e2560900c0c1a442c28982440340260103100b005008211041b13601c01c0c158098160705d0396503018030010000700305812609120252500c0c80e00103c5442108140c41c05030111900a045558400c00900c1004030f000705550900004094615500703455007050303141224110f45e00d80160032a02d0410020176802013004001c0d601981c4800c0400400d41d540100b40400b0442c1c0444020b01644480040140d03111103901c01041180034009076040840300d580890f040c1c5c0d001e20344200914652040c01c1121550500805420a00088500346000c0003030720344003200206800b01412050340012000100300405031964082c0c08258001d20030314420034000f400e5a041070700740318059400c2500141543c1703041d2040510031500e0713881e101007041c00e1540855454100a0515410310340c2000080045030f50280411100f0000243c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 392924505 1250 392923255 392923259
    0x15090402131e060f03020f0910050a0303050408010b030604111002010f1506080114010507060b01051e03060f061312020d060f091a040c140a170601030b0903070b1906150207 76
    0xc80120f44490784500340d02c0304454410320059542e81c050034914141140ca00841d5150380203804a048d00e83c0d40b002d0740c08400080000101500300d80035000720780c0070380c2c001c118a05090b0309143d1103901c201c0300240081d44149100c070780e601c1c2c4184501c50140007440002000300107030900c642100c0b84003051045903ca035080410803941e01c005940d01401c413250034403050161201c0044c00e940144000100a10346800c1c1014040e40305905503808030901400c440075540114480407126031050300c05034043e0440205071469400c0c400222119031842e014074051441c940440d14030141030000e01241e009490340c0ba140c002ca44507008140022140b8400015405128582060300c0780e000e444c41030014150704208004600d02182a800329020030304800e01e1100d4910000340c050510ba000810100a226480d90400d5000a09241641d12540c0701f03882c0745d254510714176940e004403e0000c046003411000680900120356030b406d01004080da000c600f094071a1580300005094840301d00c0140e0000c241 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 392925755 1250 392924505 392924561
    0x20c0307060b030106170c0603070e090f0708090a032012120610110d0305060a180203060f01230d110a0203070b0604150b091809030d060902031509040213 68
    0x1050020109030802c40e1b81c5a007040e508907142c610211006100d0383c00070001600140c007540c061104002c00824540701e03403900100c2408a844141d0b0301d040011144000221a04c10014040d05541c0d003540b00c4103184001030078889688107c411207030b103241c000c218880101c00442c202801e0300d201ca203030a03111a0301d8100d0038012044140300c210300c1040003281891798040c1002c41c80481e005406c0c03901081c19134420b0003080c202c44403540504280070a120510500c00126800355006040032610f071001c19140d20011110852040701410b044107040c010031107a10f02040c004d080c803803100c4070301164035070b500b5951500319000905018050b800018500d81008900c54029a00940c100c60412210759030581610450065000c1c01c02d15420005035084241d4440d0034800c001ca05180b03040c1c81c5881c10f00703151303602d0b5040a008003180d1402c011000c21a030700c0302d00a0780d10852a0458250104035204d08000310705030081c2c42aa0403002c0200000c000c42160300851401d0171884602150070601c0d40a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 392927005 1250 392925755 392925761
    0x31c0201110301050604090903140307030f05010b09061b1606090504050a2c192a03031d060c06010e100f0f09053102150a0c031101020c0307060b0301 66
    0x200402400400b000148078540d19a8103039070980301d1000e400621500b00f03150640303031200d10fa40600d803030640100402440b1a8190030142805140d030901780880c1e40c0c2c80140580034040e107580030b03920038001d1000d805448000280442000c2c0458101d034035569000804115485a941001c0c00180f02c0308002d002600305030040135005480d0782c4080207101c0800340c152648604c84e5172811001c800c0910b01e481108002c00a04191080340d003500c0d0720060091074084081265220301104000c402559100903032807511312078040740e805885020344540064015450322041485007a8880e90a102c01d82c0822030400c240d6018208201140c0c1c1c5505200c1007461f142e0441c0d612010516034102d00502416004d03820300400c0f554400f03030200b9142c43d800486044203e551942000030307130300c03c25071050784401f544488000c50b00907902100300c41c4904030001e410748501c4610b03c02003030b5000004000203115281c09065004c40c1030005003400e43c940a02401e42d0b020802c00d841d16512a10800b0407850284 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 392928255 1250 392927005 392927021
    0xc0f0f080303090a02090604200702030f151501050d02190e03010905120a0e060f190302030103020f0f13021c1401120f06020708030a050f0601110a150b031c0201 71
    0x1100a6041d4601191026500e140c41003001b80280488070110361161150381100c10040e6803510340ca140b186105d06201059048494181d100748100035403000d00e00070201d011403883c0c64030140924981d503100b0000c186129024280e6040000800002c00700c034800d840500b41120042018014085200c0300c01042035090101080c0300342d24002e07003400011400120350005080340b243c143d4403456908030640303642048650715904040005140e0007041103160041015162204030180081042d00081f022030000f4003000350480140c000c1aa81032a00344c0314007140307943c02481c0c200e0000600c0a900141e03009139195201c41d004010120034490702d07a0140b5111204d510441191035890190f50302024185004017620300204a0f800c1024030250342c0407191115040b480c543c0c1d4905102c8101c0005160444200d0b00603681100407543c1ca601c102081c0b044009108003c01102c0340c103445003d02c1c20100000285180c2d5a03580c0c4c48441e49081c03003480009041c50b84280041d50301d900004e400d440001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 392929505 1250 392928255 392928269
    0x307020f030f1e070f0803070909290d06060602010c320309070e070e0918030d0e0a06060f1701050105010f0309020301020d09060f0b0f0325030c0f0f 66
    0x80c8119980b42005000f40e9414a1440b00d0004244852221071a200e116203040981801003ca8a078424003051038025400b804480c0c0d00d482e5121340e6143c0d410200c920034110003148a10489204d9180c1d01c2d0340c81c1c00c2114ac0e0740207100c020076140070754451003101c59507485080503075150780c02140c4883e0080b07c0903c0c414010285450400740d4140103100402c0c045040c08a01d03e000f102141c610181005240050700000c6030070209420100c1016102211611483d441012001d00182501d0041d101c010001a4080015420244003580840141c103921614808500c1000c04440114699019a00c000c11030001c0d8008210f082803030310b0750044171061168006a042c200100081d9a02c001d410503980303110301c2c00090a11f0340d880082d000e40300d0320b503514032a603040100c2d44041c0b2166500c64076800c10b0103e42000310503980814403550000069110f030b07250300044001171110b24105841a04001c003620341981058603961a90515034503504900c591001c0540e0501c181824400703024003608031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 392930755 1250 392929505 392929507
    0x601080d0302161e080a0917010e061504091704050906120a0b04060207050d080a0605040b030709051012081309050610120b0604300f11130903050307020f03 69
    0x81e461010a4507100c07030b18001c0050001c0302113104400c81072003011414075440100507607101c0d16404000e0662040d80151007060030300810030001d49205105206c2428004400307445140d1300c4211903030400e007020381c0c0150440d8031003040600080050b182222a4103600d02c0244d01c550604080c88413120f0000d00c041d000301d01206100d11094400615491029402800000d0b6a03440d0b15081019010381c020041c0640f01d0000c401d499035810100c0984540381441d020801251354400701f0081c2d414000f03aa64054015503010f10130010203800266000300b00c08900f0b00301a50369203101c00300c01c944080070307601c1c1c24010039020030000d04800007000814801005010700c0c14510009142e50383d56640780014400160041180a0b03880d40044031001c4000701826110b80c1d445c00c10300c9509034110385800341a200c2040541552180140700c10b0240d411414141101600340e40c0c001c240c5002405071903000000102c0303014004d51501810300c5251180d0f486544900348480e001c0e18000307542d401d030341003504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 392932005 1250 392930755 392930767
    0x1104080123060f1f120e150709140d0c0f06021b04060501120f0e010c0c03030f050108070b0d0b03030a090905060102062202040605090103050303041a0601020d050d0b09090601080d0302 81
    0xb40e8940c0000406496103072144c1ca046200800f07030340c400407134000c1c0020942450440e1a5580c004501c1500c0d800043c1080fa003d56900c0c00216032910150082202ea038203210410ba05504021104641e010312981040014580741c00d41980c41040030703402940141d204c002d030000c1c081c006083c1d00c9034101c800e55041c0314aa0400c03001070302c426014004d090b9a04d0340c5a0000c0e200e1006a0046100c900340840200828074500d40014001c5409a00681c0844c1c20300700e0070700c42d40441340b00d0b41e4121101d04000c1c000440c02c046020007281d00c001c0d52003040540756412441e00340c0e0103000408420900d51140080c180c6480e10722000d0300e80c02040345065405c004100000d070f00c0d40700d014500102901c0c2901da6010b11610004004107a41d412440d00800c0c00c030008000c05c40000001c50156000390b600b030490b203210807000308001c3c00c00c83d0610b00503046850b039040300f40c1c021000307060010104000484d00c26a8417000c602c8000044400305401d42c0032030010003103180240125030800c0740c68035003949011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 392933255 1250 392932005 392932009
    0x51b0303180304080706050706140108030d0b06030f04031b150b0f1e04110d0603060902030c1c03300903030b03010603030c0b09071508040201090f080d031104080123060f 75
    0x1c03d1030701c91b1006101000030440100259903200d990b80c6030070122a21710301c0d6120400360782d50b40c100303d101c1604185490b24218040c501003060700d00c00c4c0e014600c00e01144da0340b981c003100c0c00c8103240e140482c50b45114044500041b9541e54541c01d40c511400c0009103075100500304564140c014040c2401508080180007920707040c00c2004161070400d540c0829481400b000c9241940310303100c0048000c51902d580441081425005281c40b030b030003201110300f01c4280004004d2081e140710310100c280d02d6012130311000a0f004a0411141005e140c405940c1000840b0308041424986070238200d14581d502100c90400d50144200c048010040d0003c014441c115503014003080781541c0043c21003000c41d00021141401009040003400d44410301c000170102c00440a81a0a420b0f40d080b40462074120001c50340b40600b8440c9821941e8140082a20024840090b401003010b00e400c550a02010003000c50342403802d0180500b8449018a010003103501954410300f0000041c164038400c03542006402802d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 392934505 1250 392933255 392933263
    0xc03051f0218040b060415051305030c0a0e040f0b040809040f020f0426070b1309020f030c0a022805070803030405120f070b011409070309020a120201051b030318030408 74
    0x50b1041d100040c66400712000520180074941c00403440c000451a0b2100065021029045503e070029403803011640f18420580c640e401c012704940c00030840c0f08100030709000401d0264009005031260310031403440e41c440c481c03500401c40c4c0c1900d0f401c0c0c2c001110400ca0030a803080c400101c442c011b045050584107100701c84544903500c203207202d0703456035045258806007548184844404010071070b00300303941c0c42d08c008046805c640c50400c202422031f640040e400b1000c0c0215038001114542052441c1d0320300c14030300705030f410180c1d01a0441c0305040d002500c01d443e01110071074081c500c9901072103007085441c0152616032a0f030080c0015070424020701002400001d8560450400c030801103444c0d0302d58083c0c81d0f415004060025104400c4c00c4000602403184c00c0d04c01105910580304401940c1d9030103000d03801d64000000087d0800b409081c00c0000f0820b00382001030261052600924140440d9002441d4981e000f0a420003501b0020170f1001100c0c4048920400c007044102850901d03103000c000c030781c907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 392935755 1250 392934505 392934547
    0xa0f020a1e05030f030702160909020109053f161a07031101110a0f020607090905071101110c010b03070b0f031005120f121204060b0105070c03051f02 66
    0x1c0580c03041060410109005071035400c103c0404045d1a40340c03400000303664500740040d240c810800c000002c00ca064082c000c0d21106074040e140e50398403c1c81d140600032445580407a1401e014894035981c010070300410000d0303281c01945408580d510f070342da07a03407a03081442c3c1001d41004542250400c00602070602000c10300100d03502e446549440c031b80d007001d81305101c00006071b100c83c0d4030300404511200110b40c00f602c0302150030348d04d42c04c5441107160140e0341e030b5001b43e0345000481c1e05000c08101080d800d810a0b43d00c507640749031450000b00f042ca441420745407803e0046030181e10105000341030030401d00c61282454000c40c02001400c1c9020400030303940c0b14114400c1505000000000c0705038020500403002800d000c1c1100c000d58007400d1200c1e031a004140250081c0f4058040c5500082c46010140c0d0341115402c07424010725100d03039130b51400a0007034000c2103040c0314082c40400c02080711081100000c50048002d40b5000800901d10481d11203140340e44400a84103000c121440000080300c4a6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 392937005 1250 392935755 392935793
    0xa0902030a0605030609060106091401021009080d0606030906050603010c1706010c021206040b060a0b0d091a0c07030e010318110d020a080c0111150402060307030906060b0a0f020a 79
    0x3aa03500d45441410240c003181e0091a0144210410711030b443c20005200781c12141280c0c1ca100006441d2a0580302c000512403020340140d0007403804103400000e5a0142d040144202029464411214814000d4403850350045011a030341c0e04208050001a01503203178051000c40081000b90301e120740180a012020282003d83e550703500c0012210b9000d1a40e5a40140d0000c043c039410841801c8a82c0d92044100d43c11644d04103401c0101b40e4501b0001d5906003500c100515143c207100d0980b420000500848405840001062a1014041c11520310083c007903111800f0265542c00c01d401d0285c180f040c4820034a040615240039104640c00c4a0710880c00f0540c8158400000b4510b20001180c542018a02035817140fa000000075440500090b00d0b9040882030b201d440d000d070402075150340c40e01048207280e011217a072000040c0061030316400860f4040d11504000403900002d4403408100e038030a400c0340c5000b2800117544d9048a8020314004200c1a080c4020452100d207556503208159420843e68 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 392938255 1250 392937005 392937007
    0xb03010806070513030804030f02040f110d230c0703090e060604090b120d03050a0e0a05070902030c0705100902091f14010318061a100e0f0109090c0309110f0a0902 72
    0x2e142841034242c071300010b640081c901c0e03440341c3d142d0070030b10030b81040c86008903c520321348064030b620b0b188280203003040781050a01c200d083c24030004851003e040c0d03072031650842c0c01d180380107100c84284669000c0c0c01854200700c503070748440e05032501030a20780c0c858020701c0d25042c2c00d0302041751565404088070280c440c8a0307804108406410003150030381a0560030141d142c0540c0c425090020b0340740d0300c0386200c0e5203400414405426400c00a071348881c08102c010340f640d00421340620040c0e60640056410044c101d120074036060042d01c83c2410b10710384685401e06c0a1300e8011010940c5030150303025400401c03040801a0080b42018000400c0d84c6600c17804c070300744600422030801caa01036070044843c0c65443c4096264845145030840c003c0a512b00d20180d07044000241c186030303040002c42880c50490544555100d201e11000300010ba0810a815504100d8a01404118046d007401110400e40c00c81d10041540e8103189002c008000c2e00380001405811564112860342e0ba03400281001c035040c0300001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 392939505 1250 392938255 392938267
    0x30903221e1a1c0218090a1418070509010605030103060c08130b04020307050d060209120c030a0b042303031626040206120c0304051009020f100c200a0b030108060705 73
    0x182c50103181406440c5680740c0301050003850b0328031038410b000703000170308494180d52540c2d07800201c0122104141d00102d017003071641c0000c665403540308400305e800c2c003c04101d501c915030700e800090410000742c0122002a1000c00100104011801341f1b151420150034420311510700354032290f282404a8001900c4007010402050a544043c041d1002070040501125030311084e504041003c3c1d030002860382e014481c510b441c68401310700030850034610440100074040d9000191940b200c88400940142d0b00c01290302880c84000b00804a0340c6040d01c0c0d054051034030f034901484160b0440300041810320074080c1540354044091300c40e07040c454011440410010280d00c3e240041a200d0080c3c001c403068401d101c1d410301020784040e4018520651140044500032941c80781c00c4001c2e541b6044009400c41702c00c0711202d03003a2505584103d1400c4c50741c60440e899981d5a180c0203800d182c460005900c00a81c0c2081d1f100a09209015001038540c94044c249154941600349079610380091010f01041808542 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 392940755 1250 392939505 392939527
    0xc0108060618030628151205010b0409200f030d050a0c17030f0c13030305030a0b0a061e020627070315050a0b030a0f08030903221e1a 59
    0x5a003401030115680d80c030b4000140c40300b900d00c0114000280d04174100048030079455005080d00b1141c1b42211460302ca01d401500d41c40000075400855442d5200c10407070806480d0781c814901e229000b2010740c2041c00442c00c0340d1a09182a50f401c038018401e03011040007681b000600a00003844078501650b480d1040310048901f840c40740d0f0020070030700c0404120f00c81d03004600e02035401000d40100c4000541c5800c2a40051881365032143c00d021910140200040b0340984080c40c0d02041e42040800c032500f22360300041920442c0d422107404a0001c00009100a000c030132954400c207014001003003039003802074034a40090711455401c202e0200042030440d04038814020100116071005014044540080414001d0f20049504482c1107291620804843c0740004000f8445600704c00452920482e90300c1b40b03507107944014140e50041c4002c100c03513000241d419a8881c0050700f1030340c0c516101414140076021240303040300384840300c101d8003005100002c0b80b00d140c40964080564070990325002112 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 392942005 1250 392940755 392940787
    0x304020108160912050a170304110d060617010f0f11270a060908061b1c0608100e1e060708090a140f0106080706090905150a260c01080606 61
    0x1c004084c4210408040070824000b80da100e582c1e00c1801845003141c1c072280000003e0008490182035109100310045541c100200c44044990090078007144864490344c00c668542d45002092141c0c3c0e41d550541c00950485201d544084601c034402840348810107003850840e4010307401068010b00020b24810140d005a21460780d01c408054003c1004036078948028115141c68450310185000341000110003919000c2c82c165000444030b041801c00c003401d481313040d41c0280b0094260340e05070364940c04640450104041301e980016088045403000307020003000d0521030b00110481d50308100c2520790080800200700d02e03a0024840c0740c112145d644440b615840c2010b012409404418070111920105901203242d44060311010000d00640b540c0300c0304c0315650b5116101b01d00024480180c14482d91119410032900301e190f003800800282030340f1001405150141d40122444440d120455480c086009040f4480844d180c004d010414031000c00603049030130040556118046c00103656014008801c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 392943255 1250 392942005 392942009
    0x9060f0f03152401021606031808221e03021309020405070305150108240117070e0108090c03030f09031603050309040e010522150c0815040203040201081609 69
    0x111040d08141020606001100d1a503440510140740f000b8241049500008440f007442e80680200f4548620341001140204410562030004410340440080414400000343c0304500a05410200300c4101c0d030303c80c0200c4011507100c4860b046900c00059090240d00a0700d0040360340544018110118510b6600300a1401c09002580b10f46450180142c096044d44614032503102c0f07010003001504100b005481d41c11045a102c01d00014041902d448106031003415100e852041c1021702c410300004208901c841c108a4803680068120b03541080d0302d40c0c0c0405069040f08042000e040d4801c2e40c10042520b80c440c07890744404040002410030321680f0308101420034451181c094444c4c8549a1504c1912507026590f4184079909000550707400714010f01c1024020181c2d0700315003110046141d910b00c5280341c040c030152003000d201c0401c0742e00e0350118001d000c44c0000540c2c482c2c1007481c0203081942c0c070941114015020314814010000183d800c014041e400001c441041400024501c038110f800910755 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 392944505 1250 392943255 392943283
    0xc040e0a060b1516110105030610270306050a0506011d010309080c0102030a060302041a011d030a0b010602101401030b0612010e0304030f1505070f030e03040f03050d080609060f0f03 80
    0x25013003000c40c000c4060491620710501d840f43c0564007880044a240c007044d201c2503488a60480400300f214000c0e600a03015509400110084000448100004503401d0344161a455190700c10080341d14041e1103450b52000090800c0b00355182d007a004c660071442441102410715a4960410f010702141c013090b0b48803080604002c0d5540c0c079002d0310500c0078264520089006504080714404d01466014101c40c08100613500d801d4032121480b02c6002900000c0f04068150140050480100d96011606c078041c003c10780050440a500710101d10445074012601100e00703c400380144000b50789095540e0700018120b035401744000c3c0907441c45005100c61003d0410510000600004000c40c1c201c01c1691a401032000c0401e0320f00490b0710703a0965404480d40300c00070f007030b10b50340b80d00b424002d80c01988001d12440c00c880c2425255144204134080980081e6840d9000810824580b03611280c1580d04c40d500b66800f002c81d05002000c1030052028000983c4200100f03040703c03d054400b0014602b800c852 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 392945755 1250 392944505 392944507
    0x41209050a0305240c0f18060a0f020d020102030c1902010b090a09030908010204060503070f181716050915010e04090606180203010302060306010c050c03120c0c040e0a060b15 77
    0xb403407800030359418482d500042000360041104410781d0f09251001e215450035008185866100010400c042d40010705000342c18196618041083d240c19000e4640500c4a858200105041201c06481d00c8a0425210216801001081400240d0354162080043c0054001415030348000090740907107444c41429810221138010029000c0c800c0d0800000d150017a100e44104645a554482c00c0c3e01c20ba000d410003161040011440c40c3d4855100707012400000e11b81400d040446809420b0904400d502c181008650345c038188039419014095900c4200d1400700d0746d8456072811001c0781c04000d000301114810ad12021224903164000c2c16001405400240100522074140c40e1078001003005000e844c50828400c00040c00c03c0901d4800c80e41600d070028425401d5603202c3c1b0044039000e996403021182402001d46c002c0150b181000b1004000040d55159a01c901c0107203552807034000780e40301d0244203609000040d0700a1101086e00d010707654216030f02281d800780600200718071320ba101401621180b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 392947005 1250 392945755 392945759
    0x4050a12020106060323060105160f06020a0f050c0c010f02031e0304030f020604080f030421171509010e0a021912050106050f160c0b2706030f041209050a 68
    0x40d0643c000b00c207075152034400b0000c01c99030901400001c04800c031000030407504040810004e42c002d00c05054114403510703801562620b140c0e00c1e00d0510b02070f02d1040361200c0c0c010400c000680e82010a103000c1241c0d0b403415900300b40700c00905640da2038005c481c40d4184551141200300c0070f4801d008444180589051040c80000c103000384000326802280c00b41c0c0045d039003817111002c440c404980280500c5d080f8840d142484500c3e40c040c407081d400604100d03403000703420090f1f5288802000d00445200116203641000e06040e04000458440040c01ea081d01080c03a0703d0000305543e1101c8160559801c10044500755540070302e000000c0c85018602c1d82c000c400003000401050b4480c0f01c410f420078079480188034a903650b01c0c040c0d51030700a100b1803000c3d4103418060f074516426115040d80744180600d20741031005a82d200f2045040d881b8028400e040340013400180040554007200c02d011a50582e00b45145140900f100074142ea00900000d0540b91a800007070001780c440c800310005044000c207040d040c55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 392948255 1250 392947005 392947007
    0x307060c021606020c122103060301020909010801141501050d09050c191d07051602150f04090509070321020a05070e010603150b040b0c0a06020706200c07090504050a12 74
    0x45c2c601c44580344070340c8840100460803603002c50111060043c0f4010752500301134844840c120781c1c00040c43c84d9050740d800c1c4518105035503602e118500a0000f40700001e441c1440300040102060024050060324500322004102c80c0d0b442003c960795541c00100001c0d080f201c2d07162143c10402d480340500d501c0880c500c42a0051212a4200c4045585540c00390f41c5100c503114140c0e002c02001c0b02d003040418001e100801142c003140800202092006000803c4050401c0041c60540c003e54290802e00c200030a0034805000680709060b0401201001061414955034403100709070880002003844011541340c00144034003c01220b5a03c640c030000382d0b800d8030f890f0000e010840c2c00911859000030b003802c100040710b4540c02c0351107007610401e0403034034949030a1020f4481c255105980e25101482000390a9000c44c03500d00c09401d60521a41c0081140d85c82e07640f524060440d03604182c0c01d500b00402021111170000a425800c0320603140d408a560340d29401c1180c1040349915028110f58000303100c0e840c0d22 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 392949505 1250 392948255 392948263
    0x6110301031406070206040c12020111060a0501081b10260106050304060522020402031e090a0b0f0106091a040305010507090f1205030318030715060608070507050307060c02160602 79
    0x10340b403a608441540d50340d00f108a955017801e079006030180f00103000500c05c06060301c485110300f034011304000c11622090318a0501d460000c8401d5014035507a200180440002800b0138a401c102d440c010102d00740c61140059034258203405220244005c80300c120358004140d122816a50401d41442151982c0d2003101803c9640115011034415241400041801020001940300c9001010100701c42c202c41d40d09109c002c0d0f001401c0350010b00c5140320f07a184107401b900c24040c8260111409000400c1c441c0c070704601c1a9402810700c0c01e031000c0c00001803040b1070307214003100103c690041881c28854001340d01440c03a4403450304003038401c1d401c0804000c101a001690b4100b1a012010013081c1c8941e24a03c481d4072186840d4001d01030b81040000c202c50303440401c0003c100400d804141c80c078201695446148941042c90201e0010391a1102041503603042900c150b8800e00c141805490001150342e840d84912a22000400080c6d035070b404141410710820003c1194480b1443c0b480e49140c1751a4080d40d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 392950755 1250 392949505 392949533
    0x120a08040c050604030f022b0f02150313080d021e09030c040c0f0503100e070c0b09010c0504120c0506030901021206040b01050724090804051c0803130611030103 71
    0x1107450000310008a80c100b120031641140e0700718a045440c1c4641d54200420051100030030842e815030391402c502c0d401c405007140b0b010103129043c00040c54510788188071101076114041c1007a80c2050013040414402c442e011501e03941d0001c0c601d9030700c070503400ba0b0702c00a01480d10030080d01d800303807104103000746907280c010408000120102c43e090440f0b901008140c8075440c10707a07400103000d00390580d80507019502440d040318008482c0d6603110b4403203078410710700ea0b0b0464040c0f00003104654040c1c00d02a8010034190080304d82c034024001039224040191587c0700f6440307802d03000c80210350700c1810b105201c075113000500700043c140d40d80c070b080c05070005001c0d400c440c1e40c1402141e0310798085841031420340304074100d549041c0c40c2c0600344107694403030180074144261200311408440506c20910007541c441c010721a80305880503501c0b1800c00041c0300c40c00705104210b4032045074848848011807a20400c0d42d5110f201d05011040c07030103040c40e003800585902c100e50b0140e00b0004c000403003081003454030220 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 392952005 1250 392950755 392950763
    0x204051e030c01050702030703061b0915081305150103111e0d0b070504030602160b0702030a020703140f150403020d0914101413050a0503030406140705120a0804 71
    0x4002010400303800403580d4811040c0ea4158460701c4400301d554090000750800c4c50000341524038895581c1c65107819241c0360303100f5142c100d2081407910b4429410049030005000070400b0b0750b000c05088a80074100040240051701508098800b070810401d04104040340186103405505007560740c2e103030281d00040c4100c00030b0300c100c6507050314034103a0400c0003c0918a980c010030b000d60720401741d00c0d1a040300e03001810140c1000310400011003c20090f0000f0000048540840c0009003418105141001030152501086401c10018000319940c00644d08054a03048041c9034050445c16003003138035040c00749003100c5490281c00200c2142d180c1c1108281d00c200d002c0d40a0f83c14400320400116007540c40da02030141740ca481021229581c2c1411100102048030605100a103081440150021500201081e10b0b080c030744085e0070321882c105040000300414041d0011810241060f4003d44124818428405000408610f86003407080030070140c1160301c3c0c1081c04550314036603007400a001c03e030212826a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 392953255 1250 392952005 392952019
    0x1a03010e0d0207170f1902030607050702063a1a06030c0d050c070c27020307051e090406080607080105060a090306180b1008010b0909070e041410020405 67
    0x10194010550907001030300707540a054641d061441140525140c1200c04000784122640d1307048406007040103211446040c0d444014580c503a03c10035192840051a110400109004580050b01e4100680380c54001e030743c4c80c40103074a506140411005809003100c442c459401c40c40184210801c0c0e001c101384100c2c42030303100c40d174550341014041d803484140c5894400d010200400441f281660780300076040745040040c1860041d403a160105002c40c20f40000300c0e400416038010780800000088086607050b00a400c5d070540c03400301c5020f001400b6502109070f0745000610504150f010120032240c52040040042100545408500d680c0300001c03240800400d40000001c1540c0c0340800035107003040b00030740e21403403d9819a61b62101a0000e2450f000120327060700e0510f80060b039803040041c441c80181484460b41890502242c1c299200d0050f094003c80d10310f001c1c01158080070495409440e1103800c0c2c041c954a4520f1b0040740c1401c1c0012101960203a42e0500c42102c040d50010411640125902 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 392954505 1250 392953255 392953271
    0xc07050301060f17010b060708090108060109180903170a0c020d02061006030b061603030203090106050a05060d020c0f010e0105011401030c091514030910110403120806040f1a0301 79
    0x81800c80d0a81c0c02644201035141604002490380b44d03400e149a6a0302d1800405c03d1000480410600d8000c9132089407500000300701181a0b580c00020700e60310840901e8030707061440c80d18501c07101000c0344a40118000d51902e15440605006420110f141d684980c0c0e8600640b902a0040c0002c10300303c03032420018002d4950400302c062002542502075030100c0e01c50f410462910701d0035001420074440d00d80c0c02020030302101ca01c07188280c00440f1003502a840140e642d2500c2941242100d00702d812076886881c02040c14001906c1e06000e580d68030380755580069603214002ca840e8580702c4c84403201003441d824007a031060b0f00141900020b04840105008602d036410f81001036007a03510030076400c400180320040c00c10606811405d800034065090030051601711076058541003035030041b00c00501c00d41c01702103110301102d280d02c10110543c100390035030b43c100760450b9100200f40c019090102d040003070a002107a007640d03d69122610000070381c0c0c410040760300c405698046030f52049909034400d51030f01140b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 392955755 1250 392954505 392954509
    0x705120d0522170f0d060f12110f0f03031308060702030711040e0a0807121722030908070e0114150a030504020105090604030308090c0a06020a0b092d0d0f0e01030209030a0501020307050c0705 84
    0x2e40403483d0303407013031507618901270300ca0a00844607400b004243c1d0013881c1c6005182944c80a10040200d14060941c4400c40c50400482510b04803014082d0030441d8070400841d03002c0f0748025000420b0302e00403540443c00300ba52103800d51404007110300140c5005800145901001900c00740c168509080c0c0e1510340501444105502600c0d404032030303042845ea8400070380c68145400214005502d0b01c2402c05007100d80d02c07069480d280011035001102800701d8407006200d1010440e801a8846ea421a22580c000d04084482d011900030011404203040d12030b00400c00b160702138400d480007070902402940d11180e07241002000100c1c1038485a9041c0554013002c640d500740300020f44240d81840c0c0050000e0072941c1d07240080706000400440542c0104008107407080c10600701e20034012101482e003125143e00e09582418803035403401c910240800070134214407064200310800200304d001d00f0b0050f10313001e240000c2820007110910061480d44004100954180c200010b001582601d2088840e580c0d06c61007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 392957005 1250 392955755 392955779
    0xd230a02040311060313120e09010f08150a0f09030c03030b0103110328050a0501060f08070e10020a1b0906050f0607060b060705120d0522170f0d060f 66
    0x1001d085083d160f001d0008506180f001035401417010302c22941d0f2050039480340001c61468480d1180046d403110381c0d2108901c0c0101e009070160000d00c40000e02ca9241c8607d06c0c0e51000d00c01c180c0c0c07484d50410303400100460041c5c4d008100c40034a240c0207028180c480c1c80d004080d6000d00000701e011900c0c0c00c0600316654401d216808000807286030051950b11039080040403103a10f402859207010811095040b5610103000f054007038010b034603000c00d440d41004000740032500c0d10300c03455041000790710800c078200b81c0c0b20a00e80c50340003041d5480004103c108008a0600001c1400038041e0070075292000001410b07900c1c8882214103004040151549410810040b06140c000c000c2d4040800e003e00d03408910b1552000d0700303500d00101350301e1a02c0c00270b41e605414910741da014860800c2c004100711411060500415510140720713100c503c005000c86465440c042e0b510700000c0c145c10101e56160306603c5034a0115128102c0400880e51070300385102840c1e0242c0160702424083c210341c00d90010348070201d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 392958255 1250 392957005 392957009
    0x13060801171002092403070314040309090504080f07050607090503190227070921051f0609020c030304051e12030a1d010b01081006230d230a0204 64
    0xc040e01042000d50000e00194121050045d0f0140c5a0744800c0d21071000c00316005511140349142a4a920340040040c04a80032003c50000b8514034100300400242d016005406540c04000b0004441d1164280310240f030003070301c401c0b0134840000501e502c188000040c202d4482e140c981d030b42c000c0c3c06840300113251311051103501625030368030304025840c014501850034558400cad2500000d400b06000310201c884802054802e10003080001e0014040d800768080c000b003d0034030301c0210b294260200d9440aa4403040540503112280d0703030816841c06050640c100d40001c241d904020764641e040e0091032912540180d6040b80c240c441c0401c04041e5000c02041000a000540041c102070020002100c1c01c0307030300042900818540d2090240c04500340c4034240e80c881101c00c3c0000a1201e1305d01d0000d03208c84000782001620745403401041101941c0406144403004030304040c6c1c20030282840500c0c00c0ca000d04e40c504000c0600f8084405000301c1c00010400c801801a01e40d244541c481c3c803a400200d02c694 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 392959505 1250 392958255 392958299
    0x2040c0519050d0e0d08160c0b01090518100c09080a1a150306010906140306010e0a0b0109030f0b0609070e0904111306030c050f09060d060902120313060801 69
    0x801d07125624034055005003500501040b8085501100b01c01641d00344841555120003043d42c010601880075142c200800c428411400c00032507070942c0ba2145581d2840501c940782e0301940f070340b00107442c1e2041d80001c02400c0100008460303105001e06203d90180040d2000c0000282c45d00d00d00207502d900000307080f480d9a40040740340702001c00c1c61700301100e8204028041070090044a6803d5004d072000c00c4000d000780840d28002a0003410188484800c0c1c080c0c51044e4880d42c0107a006015041d04141036507004141c101000555010000059a900f905a44090411a000030881e4180a0f5118400344a42c1044032089030550303607900140d540c94100076030150040154000100095000319040b0314918008204600c41c0b14814404803d868482e0001c07a00e0088030881085607041c81d171429501c1240481c0c05c0c150600c1e1a0300401c044114050b4041c00756520740031071506648401c810320000c1902602929918042c20011040030304d0f1034400c070341c0050b416400000c1c9100380f2405a201070901 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 392960755 1250 392959505 392959537
    0x20d020c060a080903120405010f0513200118150809030a0c0305070314190306090b090a0f0b060301080a111e01120b0607030905040b091b0c21030402040c05 69
    0x54408840f00780c03000381401344610003040751240d003403071744010340c1d110b988a14008182598841d500710190b6501034400340600100070450000a02c034641150b540c82c0c01071964050403241440104c844800203076500d140c0d40801400441c543d500810440c0700341c10036072606542e035240c00c5480c0d81d5074415103007050005001800c146d000680301c0e2000b00704c0d56010780f50140c141c1c1e171001c03407800c00ca51151000e08126128501c901c481582c03d07015403c01000e541d42c041199102a101083e10590001c0900e10300c69030b02c0345440341c4019580e2004a03503d4014013040e4172980c550700070903500d0000c023f01b62108e900482c0c03042403a26003580041180c0105100268902424400648101317070311a484c14502e42d142d242c4c804141d2688409025000d00039030f1911002442c00c011b100407075050390401e0340204011002c01040e96020401d00b0400f000d0210349554804c18981c400303041c041200c0030303100c81420300440003603200d00c4e40005d54059402200c0c1000190801803041e03840703128400c03d54001d030301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 392962005 1250 392960755 392960767
    0x6070804171608160807080709020705120a08040b010b0f0706020d09051c030f0204080a02060f0706090804150309030f030207020a030f061b09050a050402160b0406020a020d020c06 79
    0x103040c481c585181c4204480aa03403840048005110454006840c0c075400380802e60500426000300500800c10500500421403c00c4013081d1141145d0054804080d0001081000c00108200b0081442d620003c1e0743e031074a1007450001d00703459041c0c44c141c508100000000c2140011f1a013111400c0d21011103d80c5000140c3d07803002c010707402603281079001a540384840380c0803482c14000042080c98039090441c0c10341c0c0c0d03481c0c00740489a00002a444040c81803100f03100000001405181c02a0120780035500c6680d00120b419043c17041040c01410300e400c14a0403070400c20008060000d64140900346254804218030031422203a0004000d0001580d9029946c080b90003a802842618006049184000d4580e2640c00b08581c40510454840c2d6480c0d40340309a040b03000341c40c8214000d40b4604180e0807131400b8009254504540a01c61003550300241c044250001081c1184031345610072030038402c500e42424608000e40021a0340d101502403066080000303880032aa011400d0401044103080c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 392963255 1250 392962005 392962019
    0x503070806070f030b030d030902130e031b0a0b040305070819121b090e10081203040b01050114070201031515020f0c01031104031b0803190306050108070c152003010302040b06070804 80
    0x40394076090341c001c801c1c42f800210120141c090040e002ca030340001555100c1600d00703100c003c20050000030074590031400035140050400c45010790815050300e0045e8850f08030341000d00c050b104d904800021714081d80c1001d00c0031500142d1004566444100c204064a00b103051403510240740c0c000f02d40020f00b5514144034204000030351541109101010002c000d4541194514150600c005000c20310b41c0401088100816141d03c14050502885c210146010302c0c0d180c400e81c1e00a00c0402414117455203284506c5032041d85188000300b10001440d02044c800c418040d480e0405201e0804550003106140c080130350181c0203501d007031100c1580192600d45952a0f0403030740c400402d41039101c0d0011020010351a20104040c1c4100000610000d460103406035028003100d0003580f106d4180300880003040002a001a001c10513541c0010981007040d00394030394000145020550320b8195002c0b515101607038541800030314103817442600c3c10480c00011b0f0302008030501034800b004080003402c101c2031200d9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 392964505 1250 392963255 392963261
    0x20106060e12100c021609050f01120b04060e1908031b180d0501060801050f0907060212120403021c110609010203042414010e04051c1e02070503070806070f030b030d03 74
    0x130711304030b2051303400d0720420380146650b06482d07070704c040350b010781320740034171222291003152580105000308a408a0030210340e030702c102c003200080026043d10358444e030032581003800340b09000000c0d0a200c01c80d100140249045c94107a082580d100803100b8102d03910a00c01801e400483d1880101b00c3c1680c0564500c030020817480c0001c003202110705540314440000c880000b400b425004240d081200c0c0c000d0300d04030058074a08100c9500130411588502142c2030703030042d00ca04075441301718a003181500ca545c1e04c0c00c0683c5000c0601c041a01d41041c645180d651196005c3c4407510a8001242900c88540340c2c22845820303400280d602a040481d04800b111220b621340011408000a5242c0030580410f0001c001d80000000d078420700c400f0768900b04000c00c00c5001d001c074500615000801680d880b00844004001026608800d44540410040c100b40300d4020414a0f00034000242100e42682e01c450003a034840c481511102c0100b1850440405014003038001c1c07500800c4040c0043c50300c624610403c03409 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 392965755 1250 392964505 392964521
    0x203240f0708161403070507020117060a0608061f020c0a0806040c0b0a121506030e0d090e060409060f0213051c110d0f050a050c0a050a05060702041803020106060e1210 74
    0x3444010001002100650800f17140702c2d00b425110075403101120700015100040c1c120150900c034103044200001c550f61048594141c0d03150f03141692041c1c0c3c40750f0118000c042e8100825490000c0035000d40340c0c46500051070f805844090300c3d100b0186550700101030741c9080030390340100030754a07400c2c050102d12010710141c01d1800c10391a01600d202412600d500440740c40100c07003010001100c101740700c2c0f60703054051800c000c0001030090064142c1030300010420340d5107005503c24807685401280c15030ba200c3d000484900e412941c03c200a02c0c0844070750b00254000d2000c1c1400034103100d40065180391900541c05030102c0f5841200c0214140e03a0341901da03560380740145620182c02e40711000441c425071303040c8a27140c0c400c80042c4002d44450030020720307241d6000f903074a00c1101c01d290305000e50788403440410b04541c41945c2003a15a0401d100040c050482240302c800050304188080c028190305407c071404880c2681c48541c400d640340e1040c0200d05201108812403035101281301c507030402065115440c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 392967005 1250 392965755 392965757
    0xe040c0905090114010201110901080612330106090608070e01021c0206040302070b160204090809180a0c180e1807140a0b090d03080705070203240f070816 68
    0x105481d034001406169082e00021120300c0221240c01c199602441505c0d450788212640500300f002450000b848904001c203802d02a02c3d00c10f0340011104401c00a440c020720502208240e10b01c5080d4008030b0080c0c4090742c16461841c40c80000800d180501ea243d0162070781c5544002c10350b51031800c00d454030001002098110700c03440d50074603096010883c482c08001d44c00e9010f02210706107410300030703d4810283c1241010450801041400b0315800050414441c1d0591b8040781014a0f418458868002d8103c0c00350007100f0100004184410500d0246c0b18112001c01044014040c0038104e51528100d241c0100001d6050810701416070f0785080d95500a44080042200b140d00610407420300300c003a031010210344030b813046111240c0b5141990030068000990383c5814212800000f071569007141c00701605200d030540102e00020304c650101d6034865009000c45000c041e003504810b00502d822101c0d00358884840e0045442413045d541301d02d000c0c1b0260350b141040c940310745600080240190030410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 392968255 1250 392967005 392967017
    0x30c07020604090f0e070803030106032a110601060e13112b2406050a050403050d0503100608100302120a0506090c0f090c031603060803030405010501091104060e040c 73
    0x840140e441d0401000079020b00300c4045214a0490b41c0e010543d109090a10056041004184625000007041e281102c140303150101d80c0d03542c01000107c64140c0a2030171034009072103031582140e1580008007141c01c00307940d20840c0c0040c1e0ba04d2508841008414800307075445680c0291082c020b2100d07420449001d4031010345030727240c040b441450f40b051107a24981c3c00005002c0301a01e8030303983c11a11608407507035011628407106800700300d001114034810f40141c00c24002d000c030b0460201c40c032482c1968059540001101c110384084080640580c10850300200090950400403036118440c056282c0641024015400f00c107085034200184040003918884072881940c0c22000412800c01545004074075500c050504054003409111220001890f0203000340308410600c18482c80710001c507a4040110901c2d510b2443c801c92045000d080381c0c1d03004000900c800b100780414400706521250403141c002d04204908865543c0000c0385001d548500008502d200d00c0001c030f142010340004a20070310b0343c6085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 392969505 1250 392968255 392968267
    0x7080415020927090d02060a240b030103060501060309150c2303040c080a0f0b1f15080105030c01050a081801020a020f0f03031311011205010909061b090b030c 70
    0x1c0f4a40c145501d00b40042d4404208002c411584680d8080d50010101400350520344803905001e5581c03a4003424686003d942c800c1c0110864020000c0101e454483d00190b01442d81c1d20001c000c00d0381c0003800705581d041d00d021300008000d0f00900c29200b510f5440200081da620074581400d00402d071a803215010701c8229500d0111078840103082c0d0b50902c072082e02c06a201e061500708002c05000e5500223007401d52100c2e001c41d02084140b50354144156001d00b002e190b564507445004460325014004014401907940302094011806101e1810340a9559801075603a0303070b172010550380c1c4d013070107210b203010a0041101401c00d078801c10040b6880024210070b218050351034007031103007260700c2200c00c0750051704904805081d4000a010340b02c11034282c40c0003141542442d8205541da549100030040081c81d0b45091009039900440300441410482241080550303520ba08510203040c89450132130f14607107052140320b000380048010340790ba03240f9a601d2590305400d0641d40783c216440a04042c42c42e900078014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 392970755 1250 392969505 392969509
    0x115030b031c021002090a2601150509060d24180501020301050112140a09110a0608012d12080409090302070e011205060703020d020c0601030507030203060f070804150209 75
    0xc080e50940e050040068011082c2c1c20003401c1000e50407034100890300410130070a55655040c0741c0000c2c0c40c0041c0103041564249880100d20900c000c0c0c2032000d031750820083d102c68890903411042114002d80d4003060a60f82c50081160f0000c03000d030000d0401104550342054810041c0d009103003080d210324005103a5030003400c801ca0200c54ac202c121a541e400000500486d43c0c4000540102100120180300c030200d17081d014030030a2401040320500c0c8da5500041402e0003480c0b80324078481c1801038106200c40380c940034000c007442000d0040748800030724800c1c00c0c41c06c3d00b005012402c007a0100082403540c1420400d030044400b40b81c6d0300545244805000106900032984142600329104c0c1d0002c054803441d107034440241000503404036403984c89080f03540020520105203654407503010302d03005980c0c0320090307601002400b8041c1c40891034400c3d40300100800400050010940380200c04031482035075620002e0803840c4040f0b4600c0002503201c00802c00244132440b0003401c140030050094202058100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 392972005 1250 392970755 392970763
    0x2e08061212040602010c1d0108060d080714010506010c030801030b070212040915050a030809010f030f020d09061a031e12030a230106140309010b120d11070e0115030b03 74
    0x40070300040401880d038091144952000c200c1c20f00600509840f540d100042007600082418003441c4800100e43d139a03215010b080150740310300c40f29254102e03070414000b00b44103462044c4a540c82c00010585640c0500c0b2500c000691658400308668216035036070600040c09421801544280e000c1c40e4818110500940003815a542c000078407140303042036001c0b004019600285c0180c00030740c0c052010900100813030340c244000307007404030900356103000c01c400801010406402d01803021410f03000d0002907401c401d2019001d25401c0c010703081c2400440c2c040004105140e54181c2c403800340080b84150710301008002c48452011b0715003102200400c6c14a80d402201c02001c0d550352070300c08004040e080700740d41040206542144030a98100f000140182c501031703800000d00d0300b010000540307080c001d4216508411001c3c200800391002d482c0c1150380c41c009140c00340003049110140032900600010000304540e074200649010380d20340305d861144c003000b010303060041588400c4400b110f40c81c100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 392973255 1250 392972005 392972023
    0xd02130617100c05270f0a080d03060e0622090210030504020102150705180303041e030c08060f070f1107031101120204150f210603022e080612 63
    0x24050a4100c01682d480011143c22a402d8800d00c8401d0001095034440744012082800c20910100b030914030900c0003035a0700d40408a80c81e480492500d0109041002040c6468200502e840c18081d65444a035405461041191840d070000100f00d0f0700e001c82802903821400b003084441000400991075008664540c996401d0000403035240d006000031940d04000410b041c10402024103118103110400422a2040c151005441a0588030b0185240d905000303c03002488183d14000d140780005200f0520514580320955100301c041c0b100044840010806501c01e4003090a061001d99404c207080d42c1050b0040c0800080103a10b03c000d042400c2d04100d048040c0d402480c0d1403807410012030005018258464015030b24500612013005400000380c41400400d015040c0301c222500450f03000c441d003000c00c010703000210748000d00740e41c40c004140d130121003901d0095a400d0940d1040000c08248088040000842401004200c4001c94441d03034500341c0141e0010410942c14004088451504d0098 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 392974505 1250 392973255 392973299
    0xc030b0f07080601020a0b011a0c070f090e0a12031a04150509070306051507080f0d0902040b040c0203090d02030102041d0f010501020a03210609020703021501090b0d021306 76
    0x820306104045400c00201a84000c1c00d2005201d02d400703d07942c00b5690b490601c100565503c08a0140203200d0340390080e503406440c60400c03559032640c2c5420000380d401c6035110b801152741c600a0461030641c00411a00c3c0d0343c94009030703078180d01030308910200c0040405840e900d0800061045602041c1d4441c0103ca08601c444100c80d02c0c2c95003082c00f04601004052304810905283c560104820b850304114681030f8600b0808041e03d900c01c6d070821246501c40c452003c40101c0c00012160600c0005502c240000c42c02941e040150103240f105200c03c40310150602c5005d0b07030041c008110325151204201340514030140c009420241e50b000340004250301500030401d4400040100024203008004407401003000348020b0844050544014008020410440500c401845a45036500319240c000c40c0003850031040840d030720843c0d810001c1d250b0034008050103c05c4950000028032150700d00a0401d4200e0040020382d03003030619420010904641c03101c00100c0d0340c0b561000900b090a0074420f440800076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 392975755 1250 392974505 392974531
    0xf28090f020d050a0e1207081b0f0c060406120b13020310050906040c0507120c1205040312020705010e04020912070f0f063e06160f1b020108040c030b 66
    0x611110103050b284002c1844010901d4501412015400040ca1000202403107080c55600c1e03c0a023070200080c8107124607180c070481881d40d03926181e4800a403c041c07441445068680301c8000c801000018800c0e442403200203008036a44414042590340000701d0705600400401d0384403450b01d003c0059800403203100b5286401a902000b2130308005800c907a2080046404114201140c500540140506000a04010910364804c160240660740b204800d6420001c061501d529449005113958814003080340c11034428481c6c0788a4034000038148083d604142c55801a9555520a100c025080a84030a52001c2201151007840e0b2080c8801801f03000e80704059461181400d06800b26160107602c16002c1005040e0790800445003403922190303512500c0c0072000001d4a01c0d01c98202c0c402585480700c01d40c002d140c02d00240640303214021b511007095448007420082c41040c1074075071904c0c501c2000b440380b203842c900d00d00542c80b4641c000d9000303110300c1c4c1080c410b9807a82c80744c1090300d03002c813a03814170004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 392977005 1250 392975755 392975767
    0xf030e0a02030618190b1303050d0204030821070c030e0a0e10050f061305010c170d0b010914030307060f1d0a060b091314010b130b0f0f28090f02 64
    0x304c20721510112820651090b049011a6940d036075020300028102d5007811160501002018400c80c115916203560020954407151a4244400c5036800764504201840729001d500c81003048041c2d4403481885580c5810508280d16241078503015201080a0ba0056108070040390840f1001056400344003580c074807096080c1044148603031541650003031803148106010380f01000f404d050143d825a10203103014114942c45103454102e00c07900e00d2020b0030481000c501242034a11541c402030354031400360384d101030b0503a0703404e6007034440e18141041eaa0903070000c0004001080b629088100010030100002801c00807480c404078411000781d040b1011a040a41c415040c0180c0780910400800c0854102226042c03161440300d001c800e01c0c0d070060120140001a1044007400c1d031102c2140031024009510364006014400014518400c140b80318400f031100e8114a401d0108084079869000f429031840d0a2490800342c00c55500d00c0362400e40c0004208003c254864035004410105402c0740c0d0141c0c40e45 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 392978255 1250 392977005 392977051
    0x41401080d0c0c14040605130c0311030714090f0901062003030f06190509130b01090c020c01300518011109060702010c0204020f07030809010c0f030e0a020306 70
    0x1801462814108508220040c020034018040340f0700310b481c000400358000350901c1c0410058541039010320381c44059003031002080c48054101c0e40f5003800300c2e03608200b24444510741d04410301040d200038001800c101d1000b1400045ca20041c0414840101064a80e07965000003e400c035000360011000220340395940c440c480460b640382400c51801c500514154601142c003a40c0e4482c00410552007400c4013140340000005403419103010303010103030100c81d40b441c282c000c80607a01c09602007216524541000010220000d02c41c154206480d60b014000305405c00740111565541c00012003810740c800b11a075204031350703c2100038800c4080440040b41514144426079903081460707158103400c0e41092101c0011442c05c6040341c0700d00340100d640f540c48594a0004840c404170039040203401c28400a0141000410607000e402924031943d1000307516076506a68500b82e0310460001030109640d0401030b01c51500942044101e250680c0132101e01902c0b0303800091800c3c4041c0c842c046e5202110340e90a03420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 392979505 1250 392978255 392978263
    0x4020f0d2a05090d05062d04020d020105030a020c0115061103040e010b0306120601090933050903040b0409020c070510080a0507030912080f1005150a030e070810050106030501030816050c04140108 86
    0x505c503442d4500210382307007980114038402500d80e4001e040240000c0003440700c482590544a40440080003044468002d400c0350148403443c0c0107500c0824000d021304200b80038000304171819603003031441ca1401b0b80d20303005000c0c00a400180c86554880b141003074481420108102c1c40e4000c000400c1c000c10501402d0904030208602c200d140d0031a2648010026505556009011202031501c0d5000620b55200840607081d03000b2030300901300300c5e400084c002400c02c0c00d940107000b02c030500400b5101355030f07503841c10440d41c000ca01c5035200100780d01000282d01c80740349074130050f40324506090226652045544958400065807414402320f100c03041400b9420790101492a8410a000f005050302420400004c009240300c01000301044400150691468442d4000320306000c5d42c2c00444200b151110a5252142c0500d1030004805150000000d82688280500c80c100d80c3c028541e00d02d000b00e40d01d1019010600c42d5002e4509100d411207020342500c1790700c0ba40080035103a010007001941405a02418 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 392980755 1250 392979505 392979571
    0x307030e04060302031911030f0c030607020106081c02010902060708070b07020d0225031208010303020c0108060a0e04300e030a0201051b0c04020f0d2a05090d0506 72
    0x18920b881424001600c002602c0801002c6200703160b5180541840d043d42009005c032820354140c0510801022003100006404240740c4003203003130321400e0f903601800302c1c00c0304c585103d0020240d201d11407060351180d80d800c8412001805100208030510780c1d401042e40c070f50207540100c0d400c100c001442414440000112a009103062000d000c0c41658000020754409110880601c41113130240483e250101c1c00a8072070085074044003281c00100504000703040304209210540243c01582c241d00060b600c00d918141c490b41c0c0041031101c03400d003404240c4440d041c00030021101c0c0d100c0c042509114461f13810000c00300348460049130326130b0510b9503002015100003405480c0258054a80180140c2e00003054600d140941540300400d051b441700110303c0c000d03200354240d4001707100081328004903120348001c00da084040303401813083d0240400c280401088002c4001c071201d03204680d00510501c2400204096200200214489540c586805080600594a10514580c0700c03900031300d00400e15450a00d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 392982005 1250 392980755 392980759
    0x806030c18180316080a09090b060a0c031101051609081902100c080307080403090e191d01061503150803030a0b180f0f0a060b0d0209060c030a020307030e 68
    0x10040481150410702410702802d001000111640b2800182c842042074039900d910304242d20510045a0030001615032064503040c0001d00050401310702e0a540380a280c00e2490058041b61420300b0351030b0104c0e030700e10101c2021403c1000d480380308051007409019407409000c40180000150740800d5001c1d00b032a40540c02200c2e00d402c005001542c1000108002c5002d0f034060714a5000c5e00444441118045211100182000b034080244807520394003603001031207140b00b503c7d80000a9203488841c0c0ca407907070850b200818240078942c0d400c1050082d070841c1c80c0071709041503185900344a5000c1f140c203403600e40e00702d207403039407003408014640070f51500480d100d1101d0300d0989031229040c50381e001d0f00d91000410f9010389c561602d42c041c01036143c0941c000300d17940d1050802055030924102801c4504000d81e1042c0f818280d02c4086007180c0420b03c94034084805c90082e031403400340d00203144c00c060f4003c0c1c007001d940f0035006e000044140350103000038840c03003140e43d01071035491807149000340999444180c054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 392983255 1250 392982005 392982019
    0x9040504120305091f0e150c07050115030f020f0f03030a0305100b0f0a0e0109030b0a1a0405060d0b06180903040f121106030615041d090d090b03070c120806030c 71
    0x5940b80c0300300b640d480c00810517150100b6008002c4072464603200c0082c10901c040f03081c0004111246401c18003402440d4410340081c446007240c5d16030610101d030140005440608a032044000600c2e010410100b003401c06004c54181c200c0ca040000c0c01c68225150100209860f04c0c100030800780780581c014090440ba034210790070b120020141500b503010b6100050f050000020241c42140c7c0030b0101c600046912101c451070314500b240d4a03002a1031500c0311841c05d000d07071200c03540e00c81c68030b03010f254072501000d041000011280c3d2a040345840c6c001e40280d8020740701c8819074510904078110700c1d11800e50032000b036070b407145000030703010b83c1c1c3c0c005074010180c030040812404c2c00146803d40140c5030142c00c903481903c9845040024140c1031400c0c0c81c6012070b401c000f80000d189201ea801c3c4160306a16103139070b002c540c2e4030040c100388c4548080711001300289200809000300f00c0b03040081c40c2c101000d0701e04901a02859030740d01500c06030220714036003c44c810004002051404212002c40701000340d81e01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 392984505 1250 392983255 392983273
    0x20d240308091e06040f0e0603010b060913020702100305010303091707030822090c020d080c070f051e06041403070302071a0c03120402040b0901030302120f0904050412030509 77
    0x105814041c14a281d4803401c0003206500829200344100384907043e0040c00107903520b503510400480c2c01241d201b2202d404028000040d07032440c2c18443c0d0545c1c050007038011840d003201201000010704040c02050000e036401d226280168076038100001400300d0a03103001400354154100585400256400002c5103080200c400c604c0d020080b450303c044a50003100c040d02d0304a8105030340038036081205540500c401c0c00100003642c44094001518640107602610300100c49058200c5210004480b03030320002c68100314800010300010010080b06008a054402201036011f040321090b07019984c030f038020b901030002d100c14040d00c810241d5000c45000015403502460780d0b0043d48410b42c0384111300d070019410301802d4003180200c040710350150047e0240d039522981040d41c4403020340161020303070103240f426407211600d06000d40503c2c140c0342c05400604031668102c2ea008080e91001c107180400c680c06001c668126200c41c00f40302e0041344600e003c5101e280c410000203080301c03002064850560301820340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 392985611 1106 392984505 392984513
    0x122a040e15041203020c0705090c0f0408010f05180c011805061c0506010329010c02090c0a030c0201151e0803030f10050a0605090909070306020d2403 66
    0x2403d41c00b0a020034084049004060005186d980320410500ca585031616290703500402c6c2000072460983d020304c429810f50020b5200c02003e030344900000c2c414404c2402a194440510300d10340901500038111255135090150b40141030045d09401e00301d0716840c5000ca00702526020748600e6403450300814500c510015030030025030f240e03d00000b042c00c5600c68021a0b1180300e201560801c903610050403084007000e6002d105040c401c0c0c002440340140ca440020620901c104514540c45608040d4081c041d0b4686008980c00c40e407500020364010101410280160348026074101560205c081000601c2400343e041058607120200070041070308281c04416100720035606804803403aa8500600c003002e001c9000e40d2000c20f40c02c0c002080c003424a80441a0700180000840b8511503407500c03824121380c4061000a4142e0b21107000c44c04805041844e14102c0c5d8080c02441681441d5440e = true := by decide +kernel

theorem cover : BRFrame.Cov 392805755 392985611 := by
  have h0 := BRFrame.cov_init 392805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 392805755 ≤ n) (h2 : n < 392985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
