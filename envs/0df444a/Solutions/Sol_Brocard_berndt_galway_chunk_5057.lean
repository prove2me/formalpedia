-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:36:17.753015+00:00
-- url     : https://prove2.me/submissions/16d688e0-5db2-4ac5-8b79-f769c186bd6e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 909352517 ≤ n < 909532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 909353767 1250 909352517 909352523
    0x1050405031606030c02210d06030206160213020423012109120807200703020d030c110103230a0f060b0703090e0c03010b070c0512160518070813050307030804 70
    0x10311140c000100da0b510447d400c04d424043c0050415074200100c4c10091404250310040400c40c00d030389602003651a40300400c039a04120550f40340c0011444c04400103d03076010390540960905045c030004290080841d4070046e060100182008100d9001e03058070000921411004004102d0040119001c2d00c02000100e8052a566541203410f074050b0040324054030a0b030b40c4c1c02c0034242441c22102d100600084068a09109231400000140d5440d07070121941403180c1d0f1100100c3c0c0c40c521b00009280751001100e41418102048141c032071403640304c20642c4a0240f114082c064444801c403400400510154184d2241058000306040c9042801007a006109583e103c401d96590704050041102c02d480b052020321040004112498400e4003a080ca1401101044195a60392002980103100c4514400c110f4000030501c03014003810380c4d01d42004040a44010304080e85c0d018401d0040140201580c0500a01c000400d030045c00900000031403070f03807007030884c1d685420a0034060189181140c0032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 909355017 1250 909353767 909353771
    0x1215131505030f07030c150302130b09040506040501030809100903050f0609060f06130b1810180207150c020f0f1f0b1003020315060f0403020f060304081204020105040503160603 78
    0x500c4841200281e8402126080351141d07503107d00302141c500d100a0107900300710400d6024000b484203043d20b480745c040203103400c3d00f0403680c880e8800284000d035031004112500c524034004c010000308446004451340284111102800020445019140c0640a40010b04984a402180d80d45084009070190046559008907031003940e80959030f41080d60202c600b80d4015a9280c81e02c944ca1846d83c010b00a500e000074445c5003441c500c00d183ca030140400704e5025041d540500f0b0100b0010719032001c21801c200000b10250700d071000980702d00840a484003400c10b2207507520440d01e5800c902c203001c900c200c1016070003a100150040104550b9880c0840003540100c042e00c0c80b5045084a203104906413000b0162903100703c52180e103c00e50007900b00801410404600e401c1900b06942c4060040407042d4110240c1526135046006208d441500080b0281c01810100b0600010900d548140c40709401c5452210b649036840b440101c42500a03031748901d8044c41907803a081190042c165030034069856a80e41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 909356267 1250 909355017 909355033
    0x40b040e071403040f0b07052215020c1810050d03050702010f030b090a090c050a170f12040306020c0102122d060d030e040e1f11121513150503 63
    0x1440ea1540b0051350000c0c0001400e000000004070072410b015408041070400d507041200c00780500500c16040c0103542d00c4c1c0c0070781c06818041464210f00440700d10102c2d100400c0407900fa0008994071801c5100d02c2c1c28240344603000508185e0070b407180301c8040c04001d400b42c03031200c00920380600345810618080703000c1000c0c04011082c0328424822690384603001842c240f52500c41d500150000c2c5500c40054690300110b18000c01e1a80314540d489004088844010f4a0303140444034441c1030072000100e100072504a9010400da03c406403041e82e00356604000300580da004040802e6009100d081c0a400c091350162040084884074554084001a19000c068801c6081d5100d40f18110707400320707041940044e06500301c0380482d1180390b401815442c0580001400e448801217a40b4243d4a000b54a00c0d07800e40c081d030904080c581d03004401c40050001036003070601020041c00700c40090000c0042034000c84081c0d81d01007540d1500000c0aa030b040b02e02d0200000103800d440c9099244450141c503002e480340103c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 909357517 1250 909356267 909356297
    0xc0b0a180e07170a09050106180e0606010f050a020a0b04030305040506060d021f14040b130b0a02071701091a06210604030c0218190507050c0d1202040b040e07 70
    0x290035481480b00e903031900740031150000e00040c01c01000c3d00c41a0a1652100c10300d000034001d10800c4081c010091001d80c140c2118000070083d900380c228484004e8000005109241c0d8000c1b401c2515030100f030500c00e4413942514422440d040c851a4081e2441407080b05020034550168030442c042c5020301c0c04d0350301965a040a00642d9000860000d40005016000f4012130025000c45038210507580350000304150001c01500c1150095048440e180d0b41c00a00d03040348060310241503004002c4c60165034200051f00340041d49910580c070030846041c00080310031141c0d800030f500c0b180706180d00022102800803024000c03c1480320440d0020300805040f000b221a08200b482d2640203650014014807503a0303640d940071183d441c0e010704101c0e0044c00c0c01c100a20718a01560042344500000d040740b0070102c0c000702c1504243c4001426082c203100c0300b040600340c4290081000e44440150f030401e80c15440aa02d140c0d00207102d0f9510190710f40070080b8020075130303e03a0000c3c0071707005d2401c4d95038aa9150b40860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 909358767 1250 909357517 909357539
    0x213050c0a030c020a2d0f06020c0c0d030e010302181003060e0603072102120607050711300c0607050136060506130204080a14011b0c0c0b0a18 63
    0x40307805840086e101038103a0020b0700c000d64400ca510300e413600c0d9040b11b007025a01c1940d0090441021625030307030080b482e200c5e024410040300c0030b0600704489481650f081510081c0010702d003207080a04044e00014070115900d40344490112030003000c0c000b103842c104503400c01001880d07180a00300f4804000000309a461034001042c00945120441c5070615142140c041e4007102964007040f6040a0030001c0381c2001501803160910480164403080e0b5038000b00c0c40e0204500142044403889045000360f410300ca4202c00300510b000080031042c07070490410183c080e44c034150741c01010039884140092000e0801c1019006559510009110041c244405860408104a00401d040791030701500300c1c12400709403550080d1740c0000c005003000307081c3c841007802003040e644590000d0b40301d90f104140010800130788989040c24004050002c0041d0344c18220642c0e03044440e0540c2100700141001e503d004e02c035014016030000d21141c0a080c0e65142d070000050b040030454125884444614400040d03c0c640300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 909360017 1250 909358767 909358783
    0xa060f060225030c1d0c0301030f0308060f06031305070504020c030901262403012a1b060c080106020f060115030e0604080d0c09031106070213050c0a030c02 69
    0xc1d00a0b10340c12044049415003945014851000000c0c240d4000000c990925480c0010b08040400541c52203d5040c0140648501074108034140b5010401013000c01c0d8424000600554145030400700380d11424005412020644445a0700050000901c020100c8100401148600c1070083d9800c4d5030b41c600400c0224003600c6803141d05a00100202451580301d40d084036000800c0003c0e0710301100001c944118106400c4480260022100150701c0c2d0000083c000c1680c1200d00318001c0c090400503809001f2084910500380c04103608085151400c2e5003e802080c51302c0e0840301e0807481755181410a00042d017010303124080400c07103c10010807160310106408040c0d042c0c0f030000340210791901070110f030702480411800c02056591041c1d4034590340180480e40c0194010040c054441c801968040b04803262103d507681803041c0c0982c2040000c13404000f949292a0881d0000d403181c07202d0001c6210071440f504112140d501d00020402100d80820107480485400d40d81005009441d200590780c81102c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 909361267 1250 909360017 909360029
    0xf010905060708250620030601090311030c03030f040f0602060c040b030a0f18030f1106060f120f0703051006140907021006060801090f0b180a02071a0a060f 69
    0x401c010200214001c0001808400e21008884c1c00c00b841125141005100c001c80446100b5110005045003110318041c0015208407600c07207030b00d1800c01ca00060300704035403403000820100c00c01c6013800081c0d07418400103c0c0441c01806990352101c4004000c18940e2140c05140d1810312003440102e4524030000c1c610303208504103000b00385041e06088d51030105410082c02c2088180e00e4a00080443d003040c0100d00543c0200500294032510310f140c0502040141100d400420421400c0b1500545d000034240303800000c19100c10301c4e5880c00700042103036040703508425885482512401d145007040041c80c102180d004406032214062a201c50300191801c3c2d200e20402d43c0388a00030b000051505110b8260045502e004441c1e030014980b9290f001d960750b9500141c0444c003160010000c10117603004500100d00c15010401c150080d481c002010014000000903500162400149184401354100c2d640190018250a40e110b00b90044003c884012944c9900c0142010320015450054618000540e08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909362517 1250 909361267 909361279
    0x40b07060e100618020c07050a0803280c0f05101404060b060a08060103051f08011d01110a260c1b0a02030c0d0203100e0102031b180111030706060b090f010905 70
    0x40001c4c1c001e90424525546107025a0000103441c0c0c2ea014031f030707800030301c44d60026545030000015014046d03401a00f00c4000f036060424070901c1c3c2503000d41800121a23000340c41e85400d14080c2803a924000103440b40041da2450f051041071704000742c90006100c1d51050500340812400314091040b580140940d40e404954003801050071903020390481d6600517210042c0042d12204900040c0c40b01406d82d10901c101e942d200d00710b10000503000d088059540040000f030000d41a1402e040b107040c4589103002040103130400c65910481d8900b00080382050818004810a007800d500030340c41603002e607032018041c6401c403181c440005000701c3e100b002950010080d00c454034501007800707174014000070100d0381802100e25400c080f24180c811412040380401c00181c03a0701d00b00441c01e01d0841c00d00d80310072444030280200102c4089003445000080000c0c60000d50012850200601d1030040000040c0315904040000c240c1c480341031302910304214100d4aa10b0422152001599003030311900819400079 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 909363767 1250 909362517 909362549
    0x3040f020a12080324190f0b070506180708030d1401120c05040c0c0209100f0b0309030f090f040e011505040c02071406090a080a0b010603050609150105040b07060e1006 74
    0x141042d40c0d82400c403001c80380d40c510702d0f10303c5d500000c0b1403100a040118450010100c20f0102c40d00480e00400900150a01245444d000d500c5851703860b54010641800c0342d880b03010b803255a002c284a14001420706604490b100d001e050740741c4019015001c1003404d49010000002044a0f2030242230410b650480115042c090400c01400064a98941c4030010712110412190043e02d0300b00c9614418950007192818031420000c1c207082e1700099500c80381c0051014800c0c02241000481140e203410504044c15503122502c001051800c00144560b030f521500d000c900d28000a4190005444030104e03494070305489490b042040101c2e0003186455005174407200060200003940d0304d41800d030740c030020302e6141403000f4040014412642030700214480e410610b000c0e020080900c0d0518050145d5060502284c40c4c84c0c004618480c2000b86600b411680b1100b00e00c010740d001ba0100e5000e0512442e01c10b68444050501d0700290248035243c0905118129070000c060a9512032281600c2c0e00490b00d007100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 909365017 1250 909363767 909363781
    0x40b070308060a0b040e0f0105012a05070b030106030f0c030218010e1302071202010507092411061503070801050f0402152107110d121a0603040f020a120803 69
    0x24400091800b43c101d6262200410141100c502404c001c04469005074001d2a062040380107411060f4011410b000601461401c284020b480c202e41080840365260501407643c20058a031180130360105c0b50741e0100100214405501d45c124081d100030400c024401025084011412881903c611800c0000201051040707507214014451004000601000c55114100c409030100d9110700001c032540d030f8000c0104000307941c081c011154419450305048403a03921304070341c641480040c8510500010950a0b5000200d0f011310502140403d00004443c1d251921404190f0240a15801288281310300344001071104d00c14092944500007804c1c003264141c40d50790a210750203202a07030041500701d05000c41c1161000c010070f50340450b4000c0fa40c0500a051484025001721190a10306951360000228000b6198000340710405509010400060350582c0780600031080708100b40640d031200d80082030105002404400c610554022120400400c1d5680512014041401c4004001d4402800080d84c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 909366267 1250 909365017 909365027
    0x1c0819020910030212010f0302061603020118060c0219110108040f050102030c0414180c31090e0d08060d030c0b0708090c010e03030f0d0b06070302010504050d05040b0703 75
    0x54160049025003003105500004031100019491440001e5000c181c0400a902e20804036004007440404c03101c0312801c680100d181c0d841a1030027400c40c0800c401c03021b4201071003584980d2010300c0450003895002076600c0c3c00006003d10461403401803054164501c5601c0c540c21102ca041b03030307114100304444010340c0c00545030458020000c1e1400c100728003c40012900c01c1c0000c621505528100d1980d65040a226890500030b50540d180240c44031a00002e12100f078600450b04400c80090300740c2c0794191000c0c1e42501c2140c000d1064034084500300c00303c9111700c00300c10035011f4901c80707501403103101007030b00106039510440d5074030000144014000c5400c6040907283d0030202406458604d1201c0c80390b450354400d0040595102001454810400c128100c003032000c2c07000318009182011281c1c0d0554006603036406903000000c0c03040800685c60100d40c0030381e4804801d8641c0580383c1912010305003800b074000c000854041d03038507010f034080c034180861140007200e0076a4a414159801e1101c16242110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 909367517 1250 909366267 909366301
    0x1050d05030f1809011406310305060a0c0e090403121d031b072603041d0a06050901030b0406090302010e0601090e0f062205010b0d0c0302031c08 64
    0x61030380010081c0600301071082c001000b101c000441600000c050b03200601c040100160f001e001440551206c5954540d120340803a5030146404608c014000304051854041103403040029005d5100d504001040083c085080c52261900e017200b0041842016000d82d1451884116603601161400c00200028050020303050100c020701c01c0003846101c0b0414500c58000003a884451650021074812544800521904401344040d005400454541454000488560050620680303d031002c0050040c80c100282c1d00100141c003d80d00024401c1c07804030340082c5040e644440050308218000c05d013828a804554100c0754803104002e01507a4940b145030041c5013455046045540341d01a10006a81c10080b0501030010384034001144080594aa4940a0140f22110454001100b0480c141200031108521b0b19200c0800c210440c02601c0c0c09030041480c00c40c450362049007803030801c0901050f007900400381e0b4800da048901c0d910490541054845a411001300082c07048000112490b410b00c244c06 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 909368767 1250 909367517 909367523
    0x6060304200901030308090d140301090221040b010f1203080c0306120708070801140606030103020f01050708220b18012003070f030305071b330b03010e01020c030301050d 75
    0x2410300031a0000085402c0d000382c0c001d41c001130b00701080c0000382000b8408150f07034051500300301c01e442c81c03d00010300031404140304400d5559808140304020400d00c0402a001d960a850000340c0d0b45054034051901840c280213600b0303c038075141c1001c038116003000a64051280c040d110169240c0d1f458000d110b140e40010714858024040308014550700c141004a5800713864210007904420781004502c1e0308480104228511201c4e000c010b02c0000c1d11040112419250165850007a4181072401a1018030403107500a00c0d40c9000542d2106079546009c0c0d034003014602c50080c9580c035644503c0b142c62405401c65005000705070a20f5100340e50300880c0b00e110340b8401e2403141452220808216800c6412901c010b403a494030071010f02041580c07500c1010742c03001880c1407100c0b6040013491404888405050014260307101910b10304076400c41c03030f480510780c455070072001d840c2c0d0804c0c40c00c101d002e0503007601900c0c020340c2866414900e080060007510351040f455002181182c3c684010000038400c980419 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 909370017 1250 909368767 909368813
    0xc03040b0304060905030d0506120a020d080f07081206041401050f090603010b0a031437110907020a060f0b2409181807060c081c06062606060304 64
    0x750000d102440604402000c4010000d550309c3c0c0708050000e07909000c0150403454000d1060140140d5414105400513500040c14545075100040307041c0b21481040d82c041c21018010400c41046171000c0202417044200366002e10400c00caa0b407060315401d20078003806a0103039410000101904042c041c0319808003008001007005c24044000c0307480340103190025901c1c4103403d8200032440b00c007000351a50000c2c005c100d01c0c00035440309004a03005a142c05c586000390482030f41050910a400321040400d100081410300356080c04500a5503540a1000843c3c42030300f0800341890782c1940b88640403e9280140134230f10304031942010305a05124242d00d446201d1820b001414040d00c5044079480f02e1762455404a03140d00b801c200320080c44114540c4000c4560007000c0034000703154005410352070b880d0310001c020f03281e0141da40c920100802e69524441d00600e00341c0e0000b035990388822080380c8045040e4400104d040800305100b02c07031030110b9109404c642c04001041c0060424030401c1e52044c0b81445ca = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 909371267 1250 909370017 909370031
    0x9161d0a0915060f05040e031305190504060b0a11010c0206070c0201120f05180a030c030f020c03060a060614090303090d020307030f11120c03070e13080705011409030c03040b030406 80
    0x42c408031041d581020701c00f414803141c180014101403041c0410a20004021800c0001e07905061907070701958003407540900d090041400c16108040d0700780000c0c2c00014410f0014545641a45c41c1e59000b0514880004003080c100c0f540004061041c0103400c0d2040c1e0180c040c036903d80344103503a0034104407022410411003901c100c0011a20748101070141c06907040101e01c50511008041440107400d640c8003158100030304000000b03410019102100d6803504104020301520a016400c101d00500c0081e014060041000908080e0f5445a0260303482d9854600c6d507241d00d03615111040c09002d610b190940d10400400c940307403501d0b8501c0c0c42d0480c070003400c44582a03205d41d1000c02c000025641250141903071400c1c0030082c9880050340b09450400350080c00000d1034800020369843c8a03204014568502078045411000c000343c0b00ca51181d00070105e15990780f80342c54a0740c0200618a800d108509a10b40400c0882c84d01008a4007041401070065051905107102c1800c19070001d401140c00300da031041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 909372517 1250 909371267 909371303
    0x21c031b051620151207080a0204121a09160e0a061e0e07170a11160b0406140c0a030209011b030e0a1410051e0309161d0a09 55
    0xc1c212285803654a11021441c400f681400212004006010740245081c403100d07401d002d5041159900000b1440c20400c5500c030264514000e200c0d035002036445010b10103660702400101141c010b440710800380a0781080d07035040f03c4c06445044140c11074180c010150340400000c45441e0915400003540d2350006a26075071450b0900b141c4105107420703507285000610820000b080303c018940c0c041181d040c1258404032206102d000304000a10b039100180d030b5280000305a015450035110600c0d81d80201000610342030a2030280034200300c0b012500c090a140b00c007940c40c040c11916500603020080c03181d0404d810b00005401a41112079501c0c10428400580001c8800c040e208410741030083d10340d00742c400d20381010b10020034402e400c06c18121785184003011045d01d0780c0380f601c02c84903031625149481b40c0cc0320b421240240901c5034004030f86880401030100801000c40d40341660581c20f40007007225603845050003414219107040c001c00045010000e0705441580d04a00c20061040c0103400403500ba0345 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 909373767 1250 909372517 909372533
    0x30a140c0705060708131e140603040303090611040603061a0f0306120120041401020d050a231b061e0703180c060201150807050a15140a021c031b0516 66
    0x6400511b0000b441d2046250b460b1020700b640d006860003c0b2301880b4000018045041d9200107031005080650312240702c000e00c4101d0380842c400c2e580c00c84280d0780d16652600002c003e02982e004500c608803000400c400ca021010040700d0100407014022400d6135586001c0040c24111130240f10025521107180700c101180005440f2080d8039a0a002c40d111828031041111840b04010510305541c04800300a650700e80007801d407858000f4525200b141c103194500103291041920324058188540810542d0003000360f0a034030820f205807081215542d9072841d450081d500b11307021070f05c00d00c4d51160b004a2038403440790700800c4968005d660051007003900e0755201000c410aa50010005035034910706966881e08100000005204410051140601f0036001801e41640b903c101080010354090320380041d4007995030b026070b41c0c64071414a40c07104000100a5101e020000c8004005c0d081480701d01d14050080c0314540c030121455402c0c2881805c0780c442a0340341d82c42960154500d0f6014200c0400040e200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 909375017 1250 909373767 909373769
    0x31101200a150b120606130204050904051c080415050c04031e020901080307020120160f060306051507021e040e01140108070b032412030a140c070506070813 69
    0x351524482205090724102d04491200f80c1651040340442002ca25120340054429000801100c1d142001001501c079030000344a075611494120403c04200002d000003c9030104a031300c41c0082030b1140e60200781080350040340440c0d00a0500309906200712440c1030310341c4140d500281110300f4501c0c1985035151400700d5a0324a014030a140c40070417500702181444000c0c01d0041c4540801541818015400a00007210707000044030b020311844040c540090081054904505519400f0080161101000010403119004a50209091500000c0e0904010b23182110010315169280c0c18607455508112000030800a181d09110003d800c6004070303604d40c442c6585c00701841c2c0000444c06440c411300031040c0c0e0141d102000a070000078080000b081514200c0c3d0340b00030010700419816038143c5602c040701c0d200192042c0c100c010580400c2d1b12040000040855503403e4580c03072200c244402d03040c4414402c00000c0f05842d000720408000c5c5042c05000b52001d02d100308965401c0807030704012100002c4c4c00b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 909376267 1250 909375017 909375023
    0x903080c19080c010b0102030408030d0203091905063111030a08040f1410020d1103070c06050414030a050709020a050405030316150b01020601030f0609150c031104031101200a 77
    0x521100c410f8024459401c2c000000c0c000f8500b001d10b041103081d101d003d0701c90300184050700000041d003201c03030901807004400c890384402e82d401c030381c0741c10300c1a81e440d400c99500d4528080d08607029070101c8001815404520002000c5460700c599035a100b00c2c1800a4003041d8261046120310400a1803101c060b0001e0032048611803005031800d07940070b0000c000704880e14051260320305521100c0d81d020447c00c2403500e131802d050310b005200c159018507510601070060800101000041405a800801401201c5649040d034518900b420201901c680394101d0003072095100b00c0c410400007130940c001e0134280d012402d1050034256900702190030759001c1c0c1d180707501000c44010084200891100c000d64494590901001100c3d4044000303580c66106001c00340480517516840700400800750800068151f209550744c0002c4200740100000c0c0c50f41100110102c0d00b400840090364100034196021030360810000c1041001d03410055507040c080360301000e02c041200345880500c980400008a140b48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 909377517 1250 909376267 909376283
    0x12070f03051603260f01150203070b07030603170306011e110f37150b030102070b01060915050906070503040e01060e1e01020a02040f2007020306010f060903080c19 72
    0x103c0000c640d03009501900104e1095003101400a10505c200f000c1e41940d8008806240782805001c00307a01d18042d00b48003c0ca48000e881c1040f50145d4940c1100302180c0c420f510400c55a80050030a8180e400120f51450002c0c041f40a02100c50b42100c04420880515083c1010210100082641495500b400200080d03000c3c0b0301e805241c00682da401d40f43e03500c0c02c0f0440c140c0c1000c1030080ca040c0c10704000d006070024179040d16075100512507502035880098024000c5640d01c030b091400c0f001f805024820341e03002c902c0c540d02c0005c40801800300c0c041032007e036555007450001301408003c41500624401e42e480d2006200c0480c166940a512a010700f1060300c0f00207105030084100411208a19858000ac0c1644000110580d0300000d00201c03a550450f00490802c5003030011000400341d9400c0c50031042c1c00307040080352002c182001485072500a40c1503812681c5c8a0645a02b480414800c1100060588604101142e200806000c400c402c0740c1c00e80b202c042070150000750500b01c3c0c1200340d070020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 909378767 1250 909377517 909377537
    0xa050a032d1d070f031b0e01091407020d0c0f08071221020406170a0f050c1e0412080a02070810050a150f090b0a090606020a0b0912070f03051603 64
    0x80b000c000c80b000c21000031005003181c07820504c45040c1c003111303880003c10040080902d41d40314420612040040c11882d14880307810340c4c0da02c04e01c1d001350007403030140b01501100d4400720740e8a80c03010031f1004e92117115440d800a440c001c1e03503900d20034180e00c0341d0036903461000348814000202c0e4204aa03120f01255070390699108070b500741680c00345480020030f0705c400d881003008101c581d8212401011007000c2040005180e076a2403182805024490300c049803952409041082181085003e006010181c01c01420324480e0f40000d007007148201d000300b91019107400c6e00b0f98002062040200300c0c8650303620580e40400e555800a41c5810000700180001a44800401501c0c036003d1144c2c068816400b104908968a41048503148894a010b00b255503900d5204a06c10354507001d003842c0040c20702c0102000719643d40c0e0002074803410340d0041228500703203071008900000030010b0625600c10300441040d00d80f112550354010060440d160880c14080244a60559901c07000d512014207406a1981c020803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 909380017 1250 909378767 909378791
    0x1109030609030a090603020c010b030a0803100f0e043c110d0c141801030501020a141903020d0e0610080706020f0303040f03170a1b050a050a032d 64
    0x9800401e07a6800764400e0243e949180c1c1d0103081d6408a4041d41001071307450542c54041ca01407c0400062078040c8103c0509034100304a007002544120040c4180c41034560f100d805e440501b6032540305521100c1040750214010800340d404040301d403000342d01c15511000b80d01c20049001d1070301c0c00c204690346060030f00c160700b445100312036403e030010103d03100c0c54407a01960302ea044c1d000c804d000380000350501c00100c51480c0c50f49120181c400000032070503411581c0d43c0c80c1c00c0c0c0c043e610242c81000000c804000e85051036065030181d450300c0c01040d18100903102c1070a4100c0080d0046021003408944410150009030380c2404641e011301800601c3c101d40350704010281e854040d040d0311203011580300898100b610180030058941241d44a2910316002c5200d0130100e66614814142c201404c825100780558032860f90b10480500d000140020b140004030030301628507016221000300445e104002004603248258001d496400780e000300b80c2d00e581d1001c8442004c0640c40c0307003440d2046680d50f0401142c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 909381267 1250 909380017 909380023
    0x1113060e090a0c090516030b1507050601210206040902070f1502180901060f05031e070f02010c0302030c0708070609051f0501050405010b090d0303020c062707060e060c0c04110903 79
    0x144c00b034003005002a083c001c403110201c4d4942803400c001c055540138109515070781c0b0300380f5012200d0103281054850080303051454441d8030a104212628030382c94002d4248411072400b0718503640d0010181c905240c50700310000043e5001100071501c0100b14100c810000f4170420f101811880e03113200043e180c120b0b600403002880f0a05450038492141c101c010888568810b03052810000c80346003954490b22103080c1b400345e44a01d0001941c02802d81000c0000e05e603804201d08582030320541c002e0050390750040d401c0e01280300c19156a00c651a0400201001c658200014401d10f8032039100010348440e55101c203805c044000001c1040a41d4408004040c2500b90188601504040318200f05039450300d00c0c5001c052050340c0c42d1720701840d10115640c0a0501a90556880c5003011702507910f2441c1c1003002030350704c0c29031014180301d0343c101d41007000460b080017800005480c0c0b540c0b103107805043c0400803c51150001f415080051207158100d1a0a8032540200038000a20b0a6404d49507042ea40401d41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 909382517 1250 909381267 909381269
    0x111c060803090f030f030309210304030915110607121512170c071404060e1618030204141006080403080703020d11070f0605010902071113060e090a0c 66
    0x50600406000804000c030031120300c00c10466030001c2603046030f00860700b0074150508081c0745000100400908820108071884205d09034103030084c45801c00c40c0c00d103410380010307900030300062007c20701030203441101c122901001c22203040607ca034054501d9014a02017040742c001d400607800480192700080180150740090703030810b1401c000582041d1004010314005400034140320210180142170031000c90448071161480d80030303100040d850300c204840c0f00107c2003810340514034000c0b002803524010000c0b80d005407001c0d42c5415a2804101e0b007111002d80c580010b001c030b40741c2e1000c0040181e465104e041d4a07450150107520a41c5442758030302c807480c1d5007513205109020f041010000042d9020540341c0c0e2005007400d0040e160038a0b1000c00b401400b1190405140100000d002d00c248400e0041c1ea165a41c81018280300d1aa20741c00f0034010f900400000a01c1d83c1000d0122001518215100c0c8403042d040b0040041d8a40d520782060b000c4031740c00e64403c1103903003101606000b0304c404841c5040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 909383767 1250 909382517 909382567
    0x806070e1c1707081e0702090a05061c08040b0a021609090b070503040c031a04051c170912040b0d0506240c0a0b0718050f0a030b071211 60
    0x20310041e51910b428507003160070200da005045001491408114444d42650303040d11300d40c140c031690510841110000d82e408401e00340e114140a0001a203405901d0150031310406010f000c40000003a200d02c0d0304008401c81d2000c030744500d810b000100b01c80480c24050b10904201368020407a401e80ca008846045400e508013a0b401d504100610000c1224900c0d1540c00600c0e42c6000c60340c0350b0703d07403c2c0940a00b6090300000c1422044540030042101040d6426000d140203101783d03181e55250440d051100d036100c00b039101c040f83d1600a503664032107659509503400b0420303d09403040c03020325a80c091041c0d442508420965000442c461611002a100d1140e001074251801c61710200c80070204540903100c11981c880706640041c4a83e0159002e00000000d1680107042541c60700b04004080c1540400c585140d0b8005c0b02800c000806281188000465190281c07001181c50b085856056001c80c00a065400340540783d0350040c4401c15900c1b84043c100181c180c1591100a8450383e1020281584201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 909385017 1250 909383767 909383809
    0x60608090601061b030203091309060b0a0503190201020a05010507050a0f0503061c060b130609112a0a0c0f09050106081e070c02060f0d0606020f0c040b01090806070e 73
    0x14001c181c1c00114400ba8420a40c000701c004c640341d0301d0100d15510408000c5904105409120070300074032103801030116144118420b0000d102074900744621500d4500c03460361b06a020035046000e04000c924810360072401841918484001030700c3e2a425104d003a1058000070303100040c03054506600c80200c00d0b090410340b82c0203245040000006130032014140d4613a5001000703800040400c00ca6501502500b9400f40104201880b02d2810348018041807054030081414600c40c03829070524403085800d420020b00ca07500600021a000c0200c00b90700038590ba4081c4581455034000c182c09a00b044014540301001c83c16540c04d1911050603900180c0c080030a0084000600002c42e6100000345c4150080c807024014540d0784038030840701d031002c400d0065048000001e445228030100e0004080100000030180941c50340c5400803a82c07080c46120701c5c800c03600180c643c03000901e02a040102c031414140740c039140c05501c4441641c01c050090311030102040540101f1285414503000c1d4000005e90183c003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 909386267 1250 909385017 909385019
    0x5010206071d10051210051005070503121f03080c010f0b030a032706022b0c0809010903061a01020111030c0406120e071217042301020c0310060608090601 68
    0xc01004030101c2042c0601c00c111040750312807924494001d4a018041c410b041401e1410025140b140420842c05000d000e555250740c0c0c1000607004000b140e0010394010000c500e0114425801001d241c0080e020350503148011040c2e07150503c00325520070195005051840da103946011000d821500c800c012143c0c1f044c01d06000407010395020564607915038141c181801000110401703c1d89005050780c80140a0205400129400f94001031162518207016190803046451a900d001d070b041990442c44001500d03209103d0014000602421155406052880d002070f100c0c0d440034140e0f00c0034684030070b000000500400c019030b424000e6401c1d8038046041c40e45181007002100d14144a43e00615080c000c5141c0c0303d840c41b00d8642d0004950b0544181510f05580c1c44079032564030016425800c7d038116000c904010302404180d001c07075040f5081346141c0d050300001c00e08040320402090301014194013178200800c000352803e000c1c4c120140360184000400a007010000791001d00c010b0304141d5142e2207800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 909387517 1250 909386267 909386297
    0x12010e01090c140c0f0f030a0201060b031b0d0209060304081c052205070302030f01140117030a0e0f04050a1d011a010c0c0b070804151706010810030c0b040501020607 73
    0x43c6102e0b51403050580342e8410003040101d1900b10030408180d0a403003661a513441e652404030281c080f1b81d220303600a121035680c409000744607000030f99464000503000c160b030020505a81b0010203004c65002c1c0d0141c18440d00100183c541d40080b2816034a9090006002d4514010f6152500d442480684c0c2000700f410400c0d2280213400d10405404294120404410300b8000c040100100440c0e0050860790b01164400b4558060203010741e804482c510340c080040341201800c0071712454101e064004506011030740000329000c07031000070f8554006501c025041406c0d00d0b140619403054141001c0815000c28811801d00102d113940c203808810b915003844900110603902a41c00140024a001c1020b001142440b810900b0903034003c107580030001484104001c845005001191240711203a0020000d2341d0003074801c40d40f002d1003850400601c0001680560199800a0700302c14142c3c2c01c0d100d45502ca6032404480c83d80c40d00070702822200443e0401c055a810880c0390381c000454030b0610b00034400d0103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 909388767 1250 909387517 909387527
    0x11407030b120a0803060307030501180c0503121603030b040f06030b070e0109030b0a38090c120a1121010b120703090215040e06090a0507120902030c040212010e01090c 74
    0x164004c000143c0000800c205a50800418001d1a0480020001e09c4020b00400e940c050084104452130f543c03500340001c2c1482c0100d0f00020590f0014403840c81e0907030200000c40c1030b0000074800c40902d0b40e20720f0168030075203c9109856461050540010700309095080c12003646000820203000c10000016400c0e20303036806444034080766400031560000e91110481c2c0c40c05824140c040c582c108d0100440d0300018406400b1650449881200707001c090b0400c1400d01440c202c08442161009100300006003550300b40f507000c84c4c0d0084500100003020b122811400c3c039a5030001d202803801281020208282c18075060055006001c50070300c80d868034880c0094140042801000f0205044d40c0e94400015501c0304460488180f424034000b540d541e0711411034803281030080d1803060149484000090003181c0c103100d000d001e4803c985421060ad00f00c0c036444400f40c80c607a00100c2e0180075958201e082030300c4500240409203118401b440296051030140044ca030016405603400a0500400840d00341d000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 909390017 1250 909388767 909388783
    0x1020901141312030815090f0613090c0801090c05120c060309010b090f01080f1203130201020c040c0e030d0c03050904050c130314100203091914011407030b12 70
    0x205403550b107881c6007070b0465841400b07a901166082c030724040d44204150313000081314415030b0441c0580c01e4810315001441035030002140d005103012502004a44589041d101e0090791145100000c2050407a81d1380e100f007040e02681c841d010584d12100402e0402440c00428000303014207641d441c2d222087c7c0014565a4083c603084640a80000004102c1c82d000a410070026140040c0075403a8900700003e00d445141001d108010190140c2e00e001c0b06215408680c0348000750254803400c0c1980c88181c3c0c16582e2034002c850480c198412030409a80d59211401440d111f00610f8035010000340d030f044e0525041040107058401040403000d488000032303801206a44620300b00703580005256070307070300c45403c1207110f002090109015048000010003002d0b00b546040c510140068891007042046d60000303030b01040c0e900082c0d40e080001000040300c00c0d400c0446130180181c90011560103c10003560031a030001180031840c1c000314040080302c070340502134000c0e907681c1a075100c9003a081084595880b00c00c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 909391267 1250 909390017 909390047
    0x6020604050c06132c0a0c09090b010e091510090303080f13150f06050a03022b0c1716061727030d0b04180b0a090b040b04021201020901 60
    0x8100c030f081c80001302c0781e400050310104244004400014031341002e03a050060110b0719002510f400100b000707103030780036140f14204c5030b441c3c18a00c036091000f02009403002c0c8500740e0400c41c0d044a03404a5903100c050341d03409840a041d03d10480340085091048030888a0426000d00c261600100002079126801a41c028400b40d5480d40d15150b1000083c0c0d51203904101810201209480b0301003480607030302c04880c2d1000e40004002c26660b442c02d001c60f2101038840a544400706009400e44007031180301002919010482c5242d06404075618102d070221680c001060302c5c4003180480e00503090800c855520182042c04402c0c0680c036103140102035124001c00f0288001043d00410b01d44a4140519100000c20302494070400a40b20340d034503581d4202d801c8040c103040c100280300360030b410640b080e04c1040b00c40d1458112045503540b0394010500c00a07142c011841c0e41c4e0003a000209840d0b060450081744100b00c0304480e410503004014074407a043c05001c5541c3d10403c52001c0d640c0c3c000d1448010780d14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 909392517 1250 909391267 909391279
    0xf030c02010b06030f090d0e011b05070b0c030304060e03090906120f0d051314091b0403080a0302030106021006080601260105070c200a0303030905010e0a03081006020604050c 77
    0x101604a01410140010700c0e0007080100c00c1c001c0c04c0c280820280e100b81041422646000c010b800119004c0720b1481110f808070f82004019004064400b682e14480c501480807181e0444e500d802d22a03007680281089580d9803c08020312007009200d0080b402c61903041c5000758103101450000036200c01c07000e800148145107015a20b6148042400fa8010300b5034400165030380c400006202174150780c010244400072808110020071040e980b0a0403609040b170241801805035903420b4034815920f41e010303a90f0719000003808001b0008054000403c504010740d40c026889515051000e0320340748030603140b4810340e403e10405101116000440038111000080382d84500742480020f464544030413400d001455090208010f06c0980181140a40a10542c506102c0e1034201c0d0600b003030500103140c0c0f154400e1401a0801c0401c0c03007504201d0308a80520700010300c403100c83d010f041c45c12074000011030120300c2c4041007040616806045400a10a07070010b401540b80c00c2d07403544c0e2915441c1d074034184030721 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 909393767 1250 909392517 909392531
    0x70201140118091209050103230a0209060d09080703090e090604150b0307032001050712051804020c06011e063501030302060a0507050c060a201201180c0f03 69
    0x4400c80d00050405a000303c80081024500c0100a000c01c03806c1c0a100e0209013403c0513000d03142e01043d03001101d03030400070940541e40c6031000c11202030b6100c04e9145507c04c40500108100b10405d109500704140b052a0042d40e42003107180207090040c1030350014504903034001c00c01c0209d50740400d50750b52140d817000110b0082c82d180e10140b001000c140c1b030b40540503c11410044108081c1c41000450700880e0007000d10300180031001120680316001e8002e001107140c10001a6203800b550207450089020100c0041320340c4400c1c081030491304840c0880c50b4640c010300042010408001c0400d01200d0300c104205061801c040700074164041210f0440552414000718010001c140840000103108120440c4082c0d692828000d40d6030b034007540c000301410315040c00300d02414041c0b400c9903980714246d4050013040c4e84440b4034000034002850019440802000010041d4096200400f1341043e450720b0701c21154106415005021994500c82000c01d1401c441c0602c2c564215110040c8001c00780b4000c6084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 909395017 1250 909393767 909393809
    0x80a1106040b0414090c0c07090e03070609060c0905061e091305090a0506060901050a121b080d090e0103032c0303040e390c0309130902090702011401 66
    0x3901c101d52107036480c10800701c2c011a41e07001c0384201c4000c131002100d8000e00e54035800c2d41c131751841c850040300c080264003900080000c100c0c260002052412500c0c1503c2c10711619440e0402901c00b21071044482542e00c4c2c110346241508406440c026010950b0014100400707800610f80312480d81001081c2810041024000f036070702d02e0400010710311003441c244454204004021340c1c034502902c0464850043e840020180e090104055040324001465500d8807490040401c01449044005891483d40040d215041d12030107020b0000504504004044500c86080010549134a50f0085005032403108010000b095000d070104081d84602d80c181e140f802440c000040c81c14400580c074940501010a00003440c1e003281a801e842216184420103080400b0b80e5440642848000700d4040c000944180b0700c17407030300300d6070241048000303810032a840d120506c0005211502c03050b58603403503142c40342003072011800c200c2155900011140024030402c411603103040320014050151000c50f2151300078274200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 909396267 1250 909395017 909395029
    0x305030a02090a0b0f030103021806030c0d0f0c080606030c0103051501051309090615091401061409150a020f0d0804060b0a26120702090609040c05060408030403060507030501080a11 80
    0x14040d0114145c0e944a008003202c10541091005901c201c10615a03403002c95a401e00355882090020094000e510503d0200281a1000d82084d1810400341e96401c0c0040c800c10350007005842400000c200e640b0b008001c0501c3c1100002a4904050400f0207100c6070382e41000038640b0005003401d0039034a8040014455481e0345131603000303104040c20040d035402444039030350000d40c0e40c0c0e54902000d152551107002c1d0740140d400301c42c1c200b06ca03000c0100c0100900c500c14440301c051030303080c2d048141c078186031307400000c5550060010fa6562404001001d800182d01040071007061a00310010740403c56034090043c108500041000d010207807101840300d4240c1d1a06515030107441100f0a441c0c502110961900104100d90303286015403040101d00000fa0304400144c5411710b034002c12103095960b070102400f9a905015200b19006000101e000c0f0303a035900e917000303070000d041c011700219103992071400d0090548002804000078585070400505c019100441c4020b40345401140000e540c14056012540c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 909397517 1250 909396267 909396269
    0x50c0907020a1205120a020408060f060a05042a0e0109172b0e0f030d0c080d09031115130206130e01090f060b160b04031103031608130305030a02090a 66
    0x20b18074041510700740310391308000078051500c280b000e0b0031041d660b800843d01c124801c50140200d96070042000842000100301c01c250b1259010348200c42c002d94400104080d01c20103404003100d0301b80700000d00030b2582d007004101040707046441e0401158040c403001070a900000d0240b480e450603142c1d00091241c0080101140c00c44880354000c10072003d011840400182c94040840040d0304040090507a03c0c028a001340c24684c001c020b08010161500d041c2c074080d1144d0400c81784480140600c080b100406e21440d0072881c0030361202c1d09440380509002e07050940c40302d5074408003c607040a100307400d25140001030007260b043d281c0e90740e00c00403910459600102940502c1100c243d103000072820803010f4010509140040400307000681c0c881250070002c3c003034404078a040203048030007180800d55502d04543c100d03004e4141102c810072009240b604550040f6081e00c50300c0141b425407111194031010341382d4801504518803040c40c0030303513070002c1140c4005040030f04102c0c1c0124100b00161340e10b2103100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 909398767 1250 909397517 909397523
    0x30e090103030e0112060e15030106050a06020a0218040c0b0730020f0105013812060a080f0d050c16030c0806100b070303021c0e0a050118050c0907020a 67
    0x505030369591070020400c3c90004001400507600ca00d40c0310300134010340180e07030a40d41e0101014626640320300c0d40d82d24002c481004d00f941907495540005444d2102100140504490f90250070610814014040c8402c00300781103101c91402c4204000104100440000644d00481046586c40085003090001d41207410031041c0d04140e64010009195002c200500c854226502611206c5583d561802d08a4070709102da00341080110f9018100c442c10007042011000c4480e0418070100b02400743c806e41a04094041040768049100703004440c50b05da91a60001c1400704000c21821a01102c5661141140300041080c08404204070700d001d0400e000c0300b00c000544c1520001d1442d52410010202d08103403055441c6800341d00b000c180c50041d992800f10540311007110f250720702842c5580131030003548481003031003030030782111103c000403181760280b0189100d120700140403c1044c0d04019084591f00401006000b424005080010b8004070345e0600b16801226010120790b0742010a03400c102c8214130007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 909400017 1250 909398767 909398779
    0xc17030a0c0f0f12030b130902031216050312070e10050d1109030f1f09030c030f02210d061e0302060d0f02130602070e010b1206010e130209030c042007030e 69
    0x1441245e8141d029a51100080b10010300941f40e5170040c100710b901ca0f1a0194054201a0001c011400c80c9001029281c41d403d60507900004c054803214115004813070f40c0c0034000f03120000d1100761517000100c144104000c4a8501e141080840050164402e038090440700703c0d211a44d841c25071400c81c083d0703042ca032070150039218000a00039844e5100c00d044880401c1c042c00903141c004c01101584508454154181c13a010381c0d002c0302e500c080d01c880c03c0c21001c0000f117105803410100703e001144c0f900000f01100c0301e0041d0702c038030b0070b225581d080d07868070b03009514902c0340c3e000840d1007140a00d41c014216a0141c51069403080c01c246034074041d2002e079554000d010700000e07000f03555003640580e8604a074101d40c03c0c1c440316034480103240c50020b001c2c0f01390a96000d00703001100302ca0820480c0c0907007140050425840403c5201c010a540004038480411003617808100c1000d24201801140c00c4110100d90400003030000b8840500708030050700311018410780101d4140100343c0104810b00c01a0001020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 909401267 1250 909400017 909400043
    0x30603051212130302070515040f0f0509181b0616030c0c080c0d06050901140103030815011407110d060504050307020a090506030d1112070c17030a0c0f0f 68
    0x40d090950344040c000c51030705040c10000816803490000f41001e19039041c0e002d071103540e103840c0800906400314140e04440329420400041c0c1f052a8142540061540c44680211545858208070380500d0041020700528010f07043c880524030003164045e080140d08200310700070030a81012420364010b402e94080c10700101c04040d0240b40d0400380c0703e030845d8814085400010b8480c40c6254030b800d100e02e1a560440c56180c00e01e40012000d812543c1c1c8200c41c40c000050041075400006030800080c2d00542c0401e40b03100c1440510041c107020b504503034000b03080030301e2a00010003c986281c80742040240050074a20840c00300c0b41e40740030086c2c02c000d03004101442103080c5410519101d40c84588105d11078000020f001804229500034144900002400380c190984c215a0a0310703841c10020f10b44149002d499051685a0500c4015200d61030044a100080d40d0614401a4036803807000d07800b0b18183e000b800400c44d484e602a0b201e0217020b5026074641c0003024149000c4170340c0da0030741d6801044407662801c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 909402517 1250 909401267 909401293
    0x6090212090c0a030b010b07240b011d060318030c030c1506040911090411060703030f0b010c020a150315060e010801050901080d03020c030d05041a061f08040303060305 74
    0x9103500800c00c290680e4140c1078190104480000b1511000305050105401000040d1816014140c01d40c0190a0901c130703c1c1100d1101e640001c82c2e00c0e240113041d5600c0341c0c00e000302d507480210100500c00c43c240d900040d9043c080054290300004200d00d07165642c2e19000030000e03005000b540e4400b0b00d2081225201c0c0303200c3e010281c6840256000c500d038505c02100084540c9400c0c0a0300d00c00540203c44085401d04400500c00c12450007031040d0350a030b80d01c00e0309880301d031100f03001042914080e5400045070141c0c9200301040c0c42029550904100e142444030000d40d42c1c02c483c090884010f00c40000303411681c0a4242c1c05004003003001750700c220100e440002c0b10358000d1440382003113400341c0e12041e0903030301c8400b04601000207003d0003825520004110f441c0a0007a40103001844090b000c0345e052031100280c18054603004c803012540910084119201035070b0388002150491400c0b540d4a840c00f4003412840ca011881d01c0960040190100215061501aa0061000c0c6030410162454548c0e152 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 909403767 1250 909402517 909402547
    0x302101106150d12170c12060a0b2205060307050a02010c08091c0c060204142b06050c1c0204360b0105120a200304021012060902 57
    0x225020440d405140002030110030407040203051150010721000007054252203059850106442c820103024002041240d440c9400020178812552581c2003a50380403248040110352001404047c01003c200c4428441040c03108140c448040c0641056a80d000746003240039001d0042e64081d03508200000140034074654000020180c20030a500203000c01d01110340e0444400740e080300d000310315030440c1d191050300650700041c0d05808d40c46e5160030046002c003611803204990055100700780109186501f00501e04020307212102c0017040010201c00c54000315000c02c07681d409428001d202d1070f41c0d80000398840d0307580b030700f5100d50092121400c01450a100d1000e070007507219000c0d1558840c0b942d441400308008118520358a0f00c0583c0d01c8400400720340034903001a1040407289818048103100000c55020700c0f22035180300d400b1076040800c42c965600c089100300c0caa0700440c3f090340d0f5401c00820025031685621010003d000e840e00c0d44070045a0854000148401d40050b0300403400081c820500101364 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 909405017 1250 909403767 909403787
    0x911070602040e040303230a15180212071701051912061d030f040b0c0a1506030303050a060806060112020c0d0e0306070c031403060a05060d0f0b06040f0b090a030210 73
    0x6620200000419511040e12550000c00c16041004020b00040d02501050308048a06941c070700e0300801464071201d440140b004003160009099a02180c0c40e1241307330404036242c0e00700840d400d102e916091041c00c43c0080b603805024090050700540320391a10040d600d20b054004000300241440351000602e04100034046031511610a2050305003203864507080401120050b0102142481c40c00e85000302c64503d581000f00c100a450042c0c075260b50100f02800c0c0100858401704100241450451038041c0c111100945250b025900d0000c0510000c040094004e4001c002404c00f664801c12600c000c0d00a48030b4801c0001060003025410030056800c102500180501102520300303030342d100c0904998071090800094009001ca0a0610018003680c0065800200c040d01c05183d00e0340368400f00b41181d210036008111a69511517081015141d481504000f200458036070f85801e04e008000350018070035000300c11418600140c000944d90300c50804100659001d4406e80b10501c0085015104041c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 909406267 1250 909405017 909405023
    0x14011b021828020406050702130b030a0c03150b060406230c0c0f03010e0d0c08040308040f0e330406120b01030203100c1d01110f03030117070f0911070602040e04 71
    0xc4202c100d0039501caa80242d40a0b00c2c5160748441c1418440c0e000c208414041c440d03c007030a184e6a0380703000d8141d2818850744000300e005402c0c05c00100e10b10300d0304092000c00c3c0d10890000c0d61401d01407116036504c9100315000c80b85107103000036070018480d003820784038111904000c0e03160703e0000304550501000f05402c400002d08807007040842e0007400916080e0b40c194075004c0301c10342203090a42070080c0600a000401ca000e90819818282c60790740e2490b182c2c1c0990090f01200803111402c101c07440a43c02c2c001e5101c00c0300040f0018504084103000c6030703e400706400c0125000c1c0345010001645460780141c00038211303200d400a00d41304e24149103140d5002030200380d0003405201140c5085c8181030191080820b0140d5511951440740d800c40e20040301000041030402c00c040460b800c2003031042001940402c00705014550300c1d45000d2040d4840000d03440d684100e50007002d402c02c1380b03003540b0703400008a456594003c00e88900a0b251a80740b4400c0b075400908081c8040343c0841c00c240750000003803203544 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 909407517 1250 909406267 909406321
    0x100f0b0f0a030803040611041715010b0702010c2406090b030111031302090403030f0e0106080f1b040c030e07080d140306060d09080d2414011b0218 65
    0x36400d800d20400540d00d000152009030b0400100d00001e04c15030040c0340c2c100f40c10300c1076824183c0761400d4061408001d408058035501c52100c0c440741c058403030711883c01040c3c090581d914100040e80040e0441e03860600181c041f119007040784003c5143c0f071202103004030039100c0802c240d1361507000c0c0400400c0e410501c103000e58a00303030302c030a682d000020449010703e02d0044004014640c5034200021010b000780f00f00c0801d61947c4885c2c6103034525020f0901c181900c01c00100e4110b0070102c81d146881d465603114442d42e440050014079074107a503070a2849040090300d01007019000c400c002c0c1e001d0304007007201c01c07010320030b800d000600c40c100801c1c00706140f0415595820b103003103117582c0c107a00341c0400c0d03401c0d0703910041c00c029085148100d50b1140070550b00c210044c50801c484103038000f08035100020782c483c1c000200148440c00c0d109003031103c0080c00f10500c41111000110300000d26610070100d18034810482400c6c41010355655046c05119000e105201454034506244984006200b40400e003610701c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 909408767 1250 909407517 909407539
    0x1211130807120c2c01090c0210020f0414030a051e0c010507080a2006150f0607051504052109032e180510020702130c0c030809100f0b 59
    0x20721003044001840d40060303010a10138102000000b802904013000090504420701c202c002050720b42131180209221100002e500341140c50107400c01031181c500c0403880d03204105000710418a40b040d201503ca0701c12407900c0882860000c0317840d21340c06050242191090302244030f03803081c180181d603110213541c100b81d501e2410160f00540d0f1500814000618944080c0180340c98544100c0c43c0c020042d14800c0c1d040da908070032540c51401d01800b59440d4906c003107042142480c5040c40904c541441009a444a203400c950383c41e580d46a0350381442040118283d440441c0520404001741400300007851b02d1440b0381c006210f9029555030085946d18003c4c014070003e01011079840f6101c981075138280f41d241c1e00700224004400014440003420800129000d204880458010003c5451414004000680c1d4800500400c000c03c2c0c0d00044d041c04e0035051150028880d680030902c0350b007960f07040c10711342501c1c0c4605910606110f040d681c0e02d01d40920f0140d01003401e10554101c10007500042c0c035105425 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 909410017 1250 909408767 909408779
    0x60e0105040c0f0602060c0a021c020105160815091b0307080f092a01050706050903070317010b071104141005100509031c18172a011211130807 63
    0x14000c0f4800c0d4000b50708003c001170100d190700b40080408c5c00561060b00d044540e01998501c00041000310030713005130340d203504101c051030302d01c0d003049140b4100341000c2d600c80c5011540d0480e220300c02c40f000ca002e40308000100d0520550403012110720030000003281c0c1c5a25042d03030000c1056000b25058001c0064000204103c40400700d0302c0340004140c40364041071000c5160106030030f0408a008503041100800c21103021403268801c190048007400301070b59490b076150a0083c40074540c810f0142503020030000404ca41c0e1011400c841003254801d0040c5c00d40c1402100050050502c5125982c40000c04410042e03945e0040442c1c0040d03034021658200c030409900c10895041c010060003035090717400350201d00c0780d80b103c0240380503211025142c00c80603810010400c00c452203c60f400081d41c44010f010041a170380f010300c6019078108241000c8100c1e44004150014a442c0c1c090b400c0341800b1001101c441d5025283d00181c80404a40c100741d56954042110340700e408895104111480c0691103010400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 909411267 1250 909410017 909410039
    0x2070323070b0c04050a0303050306031e0607080408090d05030307030509010e0706110106080d050304170f040915050604080c0a0f0308120c0c0109120201050901090201050d09020d060e0105040c 85
    0x29054919409410300340d20b591010071400307000d411031900c01024000025a50b8495803988007461003030303030740075240d00f0030405161a00b40990210291400c80ba40045000000020540c0d408009854078462030344460500360300b5803007500a50391304040c030080c0340c00c00c2c0103002005500404a50350700704155a01c405e030141c01c0790080d845480711608604020007010b0700c02c08114501015007400081c00c01d603a00c0440b0710741401c402c1c1e800f010030030100030081800040d202081c1c0094040045501e00011480a48100e04c21170040c61240c030350b2101420b01207000d40074180050400a416240d075161214602c559404000d03114510520400001040e1311918621400440e54880e11050030940d805c9858100328100038180203003c038040c445445000d80c03d018203240715008001e4032601d6180700000070b095483c01403441d207c503030608180d400182da002c002c6482110741c07104001050b5a0b2403000a82001d000800505030508040c03640002c2d030b04c19841280114851400241d4242da28901810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 909412517 1250 909411267 909411317
    0x2040501022e0209010e0d0c210506071101090c030c17150a090f0c0b040914070801270609020d0b0109120b04020a03120207030c050604140f01170a020703 68
    0x19820b00c0c2c0007940145802a00607020000050401e4481c01142d00701259003825242403d84034030035401c00411146000322680d018500c80d8000d641107c1c4103540f0380300c1e80c0c0c100207007001e402c00108030350201704247c00307600002c5010390010040c5c0001d580c030f0070b0244410a4501426244440810b00701110010000d100c1840940e58108405182da81125800c000d091420003070720410003400e503190000712056265005004010f181648550806107000129510b036908510003552010038054040d4100807a91304440140718007040009e002c0c0e6041e14080e02c080f8030441c907507040c034002040e8007043c0d4002d441189241c1d101007122404d82e80045400e1941da10880500c000e100d500705000c02c8400d4680c80c0d10500207071a441220340d40c1e54409240400501300080142c00c150741c180b00300700d80b4036281c800500d0201c885c42d003800e082000b10510122900303000781c4200020119100c0f141d014085900c540981e4540b9080a0b01e0300032070200203903012540440000d081e82c41c210b0128503100e86200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 909413767 1250 909412517 909412573
    0x2071e080a020f040204050916030c0e0d02131b020106140603071d0a1206051008010e0705040510122009070915031e090b0906090a0b19020403060204050102 69
    0x320072881103409104500501084507604a41c00700400304064030303201130340c600034500c103580000030001103140101100c03607206883c2c0070062052610701d01c1365a0905480c10540c1c04403000e40301c80443da0414001403d50340f811494407181c0042d00e03603126030103600010440302150740b04940d448840040000b58441254500042a0310b28140118003100d040c4084683e0006009200c82a464203421485075003c604112b0b61641c8443c10841c4c4031a80501c910010407c801c02402000b0621102c030341c41e0304182c02414041d5503504005a0120b00030380d543c1000706500b00820520040f02d0801ea100054403007040300134190790050301c0890307040802040f0f01c1000c540c3d46804106003001480c80c05480c926405008041d00e6900104946092030041c00365130068020015881c0054030f031500d00c1d6100201044000d400000402614a0b000310b96060310552040852106a03969041d840c3c04020f6503101070801031000c603021040010301d81c02041900e800741c0844551604d101e04021090303100302e0645c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 909415017 1250 909413767 909413773
    0x90f0327121e0b01060513030501380105030c07020301181a010b040605180f03062715150a03080408010f050609250c1a0105040b0303070804061b0206070302071e08 72
    0x4201140c0300c2d601400c0c0100980c82c40b445039235529102d550a5034a9101d0480118401c2c15030451303807580700740708100c60a02ea0102c00d00003c40800018002d40001401c87d0075164000907014115507080d8000d4000307080310581d03511031400a0504100c0000e003201240100c00d403180000c02ca02d80e1640655044680960b174941c500044078010782040c3d4440c449098010030391a071032b1000384c3c0e0306104d61072140610030030000c4017186a15100c10301c400445a40403c40d00444030310f100380041c00c2d4a80d54010b0b00c6e0381c401e210525000c004120382000c994401b42078081d0100313000c00c1c0e004d419000a006421815018032440d01c4010400c4133400c0243c51081040c42800c3e160708162481e8203540c2403600007800c040b0907281690300c03508140d489040c8031043c11a0404014403591610748288448000164015800e004161380c03040700c54401c0380036200500003558100110382c4038a1000c017045e50760143c0501d48070f514502d0060b594080601404140328215000e402c04080c04440e80c400310f565510007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 909416267 1250 909415017 909415019
    0xa0c021e0a1104090618150204050a0e042306060a05090603060402041e020406090314010203010f0e04020d02130903020f030a050f180d03050a020d03090f0327121e0b01 74
    0x8480050700140481604544c0b1016480041107051103071120902c011043c4803440021860400800301d00039043c4000c682c818402030000d915003108210548001c02122600d41c1c841c0c3c01d00010007444004518038005084244585140e404a031840c0264000d484495006444600b0401d002c1e40444a403505640403000050261905400c51140c42111404122400c14180007200c1a039200340c01610208400e030b01d0070020019600041403080c04803100850865041c00b026031160850752207180f03011418072002c24103550700c041c02d05804960003052290510038030003850f0050200ba01e425405402100e201d4501c0100100407a0f40c00f016583c3c0e980d15154a410100119802505940c0328140c00401e503200c403038450f40c6414117a103010f5241c42d074944022850003460140001602820181070201d04800116881402100d00c0d1740b604001d42d1607040112000800d441088078885003507904403001541c1602c400c0200007043c01403490482c0d000000c801e80c200d111303005000a11007958400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 909417517 1250 909416267 909416273
    0xf0601030f060e2e15051804060905061903050309040c03060510020106030b07030606020715050d0f05010f14090703050415020c0327130507170a0c021e0a 68
    0x44046240039924900192094981c1c002c00e44071078080b101c07410f59000e50003e01c0d00c0c0030b0f0804418040c01000c04659400281031109000f5144e00c6817200340284800401d0b04214088009200c2a200801800402141e581c41d89800e006c1d0406030f0f1258060b11020030300c00441013400d05a4000e5039040002149001100340038170001b06401984042055981c11001c5019a180c8128156800c0340c3d90010540d2411824180507000d0081d201c14107041c50444208101d94000c1b80e00400c84400031100e9904000c03035582078445118100304480c226203403103917030f112a4110340d0009040c1c17a10301c0400e802e001d8135a4121401403407400300d11507000c0c03030302c44c0062005da00c00e400040d4440d22800000400150016581c400d0fa0004840e00320b0b10382000c5514814140100d000c906150b8903050030705201d2152001150142d0300c2040340803151f540742c60002c1e190500403188015201202403001e490303480e100c241c0c5801404c5550000006000d00000319000d410050814080300691340050301032070860f65 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 909418767 1250 909417517 909417521
    0x15040f0c0212030a14010b030709120c180e0d09140a06090e0405010e030318060606040b0a031109031006091103040b0123060304240e07050d08040801181a0f060103 72
    0x404607840b954135203c000199600e9100352600a0110510380c7c1e40301e04010074003070700703507405500000400001c814043d40803c551101da074040f10302c2e4400310710642c0010700020018058032209140d1030304c81d450b01020000d9000305d019049600e4030181d0309100364000300b0042e00020500c20700b00040d0301c100e030a010340144540306e02c0e001880f80000140c40b80c80c1d000d41c103065400c1201d40d1070000700706002000d00c003c814001e01c2da0040003110300f545050b007400d40c425502c0c001c0e134401d03004050740c0342000702c10410fa0204980c00400c004040300c000426140040024000f54020f080115050881700c0b0850f40b00300c030a81e4007841d071017402040240c2c2001002c00e0f141c2c1020704a000d00005c40e1210b120182c8a020085000c4c50141030403564001c004803a1081480b08039203807403610f0f480e1a9440c452440082100d83c1071300d004540150710040c0600341200607004035045507056528204641e0424828001c46100c100d2061b410248007030048201c000040c482103401d1409511071100242c2558407907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 909420017 1250 909418767 909418771
    0x10209150c161814130813031e0c0801020a1b03092c161b02030f01060905100902070f08071e030f031d0712050304030b15040f0c021203 60
    0x900494120020030a1011420741c0c02c0d600c81580300401201c00f10401c0c02d1802248031001c0d8854940300c0a00385000a90051510301c40041c0040c040807540b025075100c0d41e50300d900255009000a00041c04c0c003120316480b010100301c2250910b1100d4000a80c1c0c14040c0282e80b0094829100c0c150798510b0110401c820b9560702000310f00f00b2240c84808144045c203040d22610441c0107104801d90103003400c6030091314a00c0a0500c0c0c0c812000300d05c20340f4000c1d5108031444500e00158004004030322540c40442e14211012a03960783e41e50a00760301081045060344141d100b84004101d40d000244c1e03403440c0340100c2c41082c0b005071203140d08a44c1d45011480e840c00810083d44280518207881c0d003030410154a850f1000e000f2000502c1e001c0343d40002d1540742c0200700c2c0101051000c1d00f05444200c2d00c50307690701258410030900300d550341e285800f4000144280c9005580100f50b83c0e042e460983d840503d81c2620f509000c0c0f1a030b280c0031f00c0b00c000c00c60300d01c21031005c227030a80c009002104003100e84103041c2e040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 909421267 1250 909420017 909420037
    0x2012009150d05100f05010309021f05040306020c0c01080c030403082829010e03030706090f14010e150c4f092702031c050a08070201020915 62
    0x2c2000320300c07000080c40b03118441c40041c1d140555190801c0c10400c0709001c0c42d4480d50425003006e00100250303036440c81d03420812520602a884803980403c05807400e0091f64400f038081c030b00c049a0300311290000700e1f03156408102641c0314a00740d0303105900006d85002c16103019002130b8000c0000f4046548042025100c4804040044101c24200d03080f001501c4102880380356805440d044c02c104025080c4800c3e002c0002400c1007400e0041d4040483e0783c0c0e000b10040607017015160f0000c0c905100100c00c0ca10304040d00032001c0080700e0b101c2c40045018080c0010121118469108101f1584440d402000c1c060602c4108840c41c10416080c00006000c84442035001907580019070281841d602d141c241c049002d20690824460a54555410400e020360060600c03504002010400c1c5140c040d450f0000b030482d002501d20000039001003880c2c4115100020403100039100b01c070910b0307a000400b6114201c0b40307507100c2d13401d9512190100e090340241d800c0c058104250302c01320074800030110064003100c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 909422517 1250 909421267 909421309
    0xf04061a1c05061006051611040204080d02070902070b010603051906082a0a0521030f03150a0e0c0702040f1a03101103040b1509040302010c02012009 66
    0x1100344009000c0e005041e0340e11884444090780c49080200c14070402d0751000034480002901841c0c81c038080d00c5441904888003150080c3d0840c5c00401540a05045070000c001e001151143e4072485801c2ea1451258140f41c054400d0354000075240b13840e8001c461400307a02580700103d0740d18021050740682000f400da00108984880700e0303200c1e900580300395001012818024440800203084468140e0200031030f50480400c1003c0d80c200340d445480380802100c50507100002c2066500004150341c040200d580107844c04002240b080c1106070300c02960003406131511000404e0142c4e010030041c4940d92091121030800c0c000060214426840580f4080e4005440401c1003024031a8500466000014941843c0905031584819060030007a29024000802007080100b003481c41c001f000d4080240010b14000013600083c9903400c1602240c101060701805055650403c0d01d0081c0c081c10404500000640c030303003404e42810203061102101000c0d251281540390000840503c504c490300c0418014001c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 909423767 1250 909422517 909422561
    0x21c051e060102030904051f05010e03061b0c0f10060902070b04080a0201020d0501030605071103030408090f120303090a03110703030806040f090f111e010807030903110114060310050f0406 83
    0x11b02d46000e104d01c14050000b86138002550107018a42c440000d40040b810000041c40801d119200010b0b6507800c4000c0d0302d10001c40086031071846100e8842d455a28880d03014400492106140000307180408101c180703028802c0a0300c8400c0c2d00c00b207002c0c5070070181650f0410404603010a0034803004207604c4540344009464030004134180c000b0f407882030b801110140e079944100704006900c0700c02c10f80200e0348c0d18041c0d0300c1d5050648580b145806032101c000d10400c20b8013070514160b650312480b0500940e01c0410b0b642c803840c00c01c0c40c058403120040410740204003a1507281c214520042140015264541c0318001161280c07802d010003031600400d100307401c076541e100701000b155102c80c62103185442040a0f000001d01c0350140070104c80349002d003082e1107101c2d0310a101e107030b078002034419480403040c0b50014042800307080c01c548606015038221107c0d440c0c00c01144144004d420345a1040300180c1c00c968222210500710021130300e0072526828101d5178040498005503440e00300c0c8900c1d8081c006105148 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 909425017 1250 909423767 909423769
    0x309010c0806034b06130c030b06010509041b020d0e0117100f0e04140d0e0909100e0d1d0906060c07091b02010c080705041701060810021c051e0601020309 68
    0x2c04400d0040984013a010f10444801d010f0801155a102c00000c4500d41c20211955a0b241a070036107000060130002c03079100265013070b446541542d00540c8000d00030710000c0b4050042010080c1c55520600040c058002d0b42d4401c540030340c9901511100681d030700246078007094244080c140ac0070306802c0c41c04050a000203408020a0341800c040d00d61484c510065040501e0040ea0800304441c07079841681040c411118107a802000817045907106451600c45581d030040161700341001c0e0a8110345280c0381101d0110102c1000500384140481a12149044e494021401c86140c044041c440d9005102e00b000814508201c0041d21501182e0000c43c0c00c5543c0340c5180340305031100c6001010078403140740180b0802c190309000d4850b5242d41418501d1040c240280000c0c4a03103d140284c0f20600e0300700c01854a4207100750f002100503c140e009441211a4045034107019600000784504400700c0d6180108803030000340b141c80d028900780c8068800900c4134043c030b000e240e84006c080c0341c15408207200048003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 909426267 1250 909425017 909425113
    0x12210c020114010608040803040f0f020306040b01050118080712170307020a031d031209030a0501142a031b07080a12060b2a071a0309010c080603 64
    0x458505400110b55481d86501c1c0c040703081c0059000d54200712680041c0008111040100c1e074201d60091208041c20b000c074100100080d02e80c00d0025014810182000148a22588203906030340e400d07a280e0540581071080905c1803007150243c0803158020900400064249800040303000c2d220b5101e8283c4034200d8000b4a1058008540c0100542c000700780d98002c02d0350045103804e00f50102c140c00300c4c00c0c40250012030740e51480d101082c1d61420000031003a442c2e641c10003040e8411030b4040020300c840da41141009244000079180c07245d64412149500e2002c12845083c040b119808128240c219a15207141c900c03210350035545050801c104020510102c2c4144000b000c411185840e004642100803c08030104c8440e50700050400c0b40c00d00c01107681c0784240c41002e8501031450300000d0300c40d19001c05141490341a500c90404c40c1c0340500f0795180c102c0b0b08806036210b041301c04020800e03101d40c4881500e15000c01c6401c640e060b0002010303100c010582c3c00c140c1d080303d045001c0303e03140050710f84d1410358 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 909427517 1250 909426267 909426281
    0x421080a050c01060512030307120e10020405040e010b0102060c280c02030715210e0a0b090106230405040606181a100c0b07031b0e09090a1221 63
    0x100064000404282c2401c0074003520004140c151043c1d1040c40000301b01d5a10381c0406010101089031610440f41d04040503040307580e1001c0c540054805900c0100c07807a000179806441241e010320304085089000000603c5154010101038002c0c1000340d0b10380107030356225401181c040080090f41c4c1c02180484000e02e032501c10020844e114283c0d03641140c01014505100e0343e00c600f0001e0012250b8480141d032059500ca01500c6240340b200a01e03461440c05c4e0090480b500040d01e851044101c4101440341d10501e040c0950041d170001c00106450b980d1001511a02041c0586043c000130424078841c10305030301643d4003601441d00000c8140d2240055082e82440340520400d0300d0f1202600c0744800e0309000030f5601c9840468108140381640031004d0300b08000c0c000c001d0002010180005c5109001c0d400c5201054100d81c66400d541c40c1038030001d401000700001c4103000301d00010009040440009121944035004103410300400b400003030440b13407450040040300c041035102d4440e17442200b007402800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 909428767 1250 909427517 909427537
    0x3090a0b0406141b0405010f03140408091305070203040b07060e1c021203090607030c090806130605060904050606060c19060218012a020105090603100f1202010203042108 75
    0x42190382c221101415400c00c09401050210354245040c054013001d08201c2d8101d0b902030078480c2c88041d03286070640c0208200d0510340c01c2c144030f420400042155031001801d61403000c0340c0c000c200e420f24103d020101c6008031055005030b80100014006680c007640546032082c07166102245600804079441d0a2103142c0c20503440706240c0c007070001d5034141c06101c802050615640c1141c20b5107420741c50b5580e00d81010304082d007459526181c01e250a88600703c03034000f900080d0100d8040c0d003040504d0740410441c440301078032681c0c07410021461614164460901440d0040d00a1101d0307114241003151030342c0100c00002c031760b100b4440c0c018102001c80c05081da40d240079940c0161030791032041d200000421402121410000e00b5100d10740e1090303a000122884005101d015040c0c00c0e041d200581c0d244c42283e03000e5500030300c0401000000708042803000140c0724009070140c00c1964440b07003001c10640070f20000f405038200b0b000c1841306802c40b01441a08130f5507800740611403120707622481d0760b66206442e10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 909430017 1250 909428767 909428771
    0x61e06064f090b28050103050c090d0b0a021b0307030905010512270706051810050307180504090f0507081b0f1c201c1103010b10030b03120301030b04030503090a0b0406 74
    0x704160742e058802d095100c1c0d41540112b18007058140040e1409694550041500b54000c0200750148a9541540e082c0ca101e07030101c031600d0f9880c80f6919600d400c49401140000c600300004101544140161035030f500107892200c00030744031000d65855211013101101200c5180300010b6010740b5003003241400810b80c0d500c030b141e40e41078080401c0f20800851701080d40190180700104200540c00000c03258446418546a09000718542100d04045455400701d50f100b803c02001006220700c40b2141d42c1458400d80458490541d107642d0581c80d0190105541500000003148040c6420404111400b00308001d0402e100e8504c00c840000a0f802d044005843c00c04c01400758090325003580f40300e4001094200e6600708106580303030f604092301500f480d004002c40d034030200d0034400e5203094201c03070038040e40280340b41894a40014020020540201d1480c440d00c42d003028031098550600440c0d05a0342c2150406201e07542d50785040d03031039030310103080911940305140482d404115140c1003140181c3c0f282c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 909431267 1250 909430017 909430019
    0x4231b0f13022704020a050304020907110607120c0201060b04090c020a0203060c040305070602011b0f03091a0a2012060d060609021209061e06064f090b28 68
    0xc10003041030340c10883d40034520420020700d4203a004825207600c10380c111803408440c0e5543d1021141442d0000d02c075040b074032842040c000c00d0754000d10302300503500e440b80c420030901c038a8080490980340d883c170a52040c5901080280030004241d08002242e1540c0e0045070341009940d404249000400c40d0100c440764008035092080001c144507002c0140301520003840712a5080340407007031075000c11a40c107041c002c6030750400000324000c2c1c0150385e140da0054800000354254403004645e41d03004481c0e25100741d00d082a9209518908030441c0c0100c0c142e0701900741486500b0998440814019240035441240c0b01c0e00d14001172004d000d03480252820050142e2150840720210081c002c029260100c00d03001303442001113900305956282e144400c0c0d07441241407a103424001c541507104d80c01184111141350300c076003045071040c00300c4c101c802041d04014042203131040340781e9100d0b40130340c1c001c06600da03641c3c00e8100800c4104d500041100756000380144120b00380703804200714003000d5010b0400301c0368031018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 909432517 1250 909431267 909431317
    0x601031413021011063601050f0133030e03040b0d050f01050117270c0a06020304050108180106090612150506060f160b04231b0f1302 59
    0x116284403040e0741400b5031540301d1010802d8175044024030000d0350201400c0400400b0f5104050440031080407034140011180e1361b617416003c0c20b421104103840c81907a00000032080d005811441d076001d018036408420146d03524440f19464046d21480c0b08040d110708480c0d00080c400d000510080c41081800d90391072032040c10b54026074038003c1481990454410041003d81d07041190b4100040484100c05110f030b440744203400140351400c203106814940000d0310a031100c1c4c0010350856000f002c0701e102c5905a0344140481c0d1302c0c17242d401a01c8c0002c010744081001c10184d884001c2265035800c001181c00354441103028110b8043c0c0d800078040d03070300301d02c03980051003400350b58041d11340d900300400c1c0a00d03e404004100184603c18a070b0b048074034001003507075841c40d07058002c05040340c2c002001003607810203040036020403680100d400c003040780600c1804c51075040012281c00c0004039107d9030081303110100c200803120f410301c841c00e80c10461440c4903990003000c510051030034003085401a140101505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 909433767 1250 909432517 909432529
    0x150f030c06051305060705010905011a190b0a0c0c030215070308070c0c05191d040218070c111c030801150207030f080f0f0304050d260f060103141302 66
    0x352011007440707810408840c080f40c1c2060b240c81a10419101995101440e10b0014014189824050055441c2400010712645d14070165254001c1c03c0340d01e120300d00040c130305030301981078240b2401200030800c110010003180660000400c0a02550307201403240d540e5004140c0b0103003408107275840e1400c001022010907412104441d08101d05181900103006030343e0f104d010718601401640d2042001038040300f03c01107008180d90103088440302e06104107581d4120784d580000c0c2a03500f28818410b80071000c00a0762150b114610a015070303620103510fa80980c6441155243c440102a00a845003041c80c0a9030b90074010210702d10b100c0da4071070080f98986500968a04000700c1a00c045401c018420030102d10044415031180b9005100c1550343c030501007000003a4402c501c0f400c0e2640c5004070800090050100c1c0351700c1010400e4031255840c00303001e5001401a5a0301902c0000f0002000105031403980303c80c40264002c0d0103040000380c40c409c2560a07010300c1c07811a54280740500100a860850800d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 909435017 1250 909433767 909433769
    0x5100602010b10140f0d022805040504090206041d06010305010803070b010e0a02090a060c02010f090b1209010b030708010b0a0b0a020607030b010509090123031903030e01150f030c 79
    0x144000c02c10955160300082da0484003894a0040181c407004803c000c40001040310500f80101a0361950b4802c1c044000000c1e40104210324140b02c19811400208440c04601d010b044089684440c071b0b29050004000040c24084004e9030000002c1c8401301c1c3e00031a0310f03003010000c010712400e803800b840c1a80004040d543e0580020800c2e8006010920000d40780b6041c4a056030840c40c4a500b0590350107234100c0003406041c444a03444510341000141b50f6411919800701d2034000c1e0b03602c050f4214802001d0322250058460f5048a035010440450f06c01030101501e900715040e8000460021200070000e0302d81080c1b40c00000140e5034a109001440c40d0880116008000700030000e405d01c1a82100a903e84000a000c0030a050b100d510074007681e8800c10440d45141d400601d01c00d07841d6101c85441d0349250056001402071900076081401034940003c0c200e000880201d0080c07075800c15958100c020f4080785410b0300080d0748403540d2095080261802e0406031110b040c00410701455402e0440d0910b0b01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 909436267 1250 909435017 909435029
    0x15210207210c0f1b031a060a03020a0506090102070b3708040f0f02030a030f030b0a1a09010912063e0a120509070807091a01081008100510 61
    0x1c04800440d520b40000e401c402c00e5801509128000c0440d041480c2018202d541c040301503049a02c0200402c10407141145808521011194045e034598060101c0600b0600000e540954940010051460100024800c0345010f00c140c4030100da442c03610084941184800c900341c1c0c3c00ca012140850040c0322010078440360040041d125080c100c050250a00001a202034040c80981410401f032010310300d4083c001d140d000c0d00300c0d142ea0340389050043c00c1d00440c0003c040001d003401342482461614141220646000342840c10813001c0d800615205035000950487c1404000c95000604101d508040c03124a4003501e004100000b0a0040c42c10340704c2850b601682d0700c416140b0940240c00900c2c03846810f00c44420700a40d846001000030f6500030404503000e0005800c2a082020501011409104a8003075500326841c00351141190410b0b0b030b0114070f00720f506407561054a030381b541c440c86903da08080c2010b040e07902142c03103803a09420100310700b0085400300e4440c001c2c030140001607980c641c02011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 909437517 1250 909436267 909436313
    0x152d0114030c030105040816020622090507020f070b0a0e030a0c05090619180902040905010c08090a050c0405180f2107030e0d050102040914041b0f15210207 69
    0xd400c1d50342071004c6c001e00501182c00d80e00d42c1080c00464841a00701e038074030340d1004501a616410bd11710400019101d00440c20542e00b008045002c2d00c5c0000f9807002442c07480e20280c012242040c80c0820786801c80994042008241c3e11400a00e0700c0500004122501454019803098100401d10403108406000d050050000b0802a501e61201038404015100364060b55800c42d6007041d40403024180e4500080c0d48145480c0c1c0d00f50800c001544100050091034640204030394911102980784d410039040904076412a0b021010185045c3e800113900440100040160301c80c1e10f088640f8000d40e200289069038000014400402c14a0b40a001c0c5201580c02e00351410f09960780c0105024071040c2c001c1d0180d001501118100802034040d00c0c040c200c00b4008003c07500d100401c3c0420760b54255402c3c0c2d44040c492400c3c0d55080d965110301d200362150662480f003142e1916040464035a020801c0108120600500040301c0b40c9400c43ca00c1c020348600805a10341e0480d041080e018000e6590b4080146 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 909438767 1250 909437517 909437521
    0x9010b300a02130c030b0a0905060108220321020f0a18051003090c03060213060e0603011d04060213060c02131506050705010204030c0608070f02152d0114030c030105 73
    0x1c1d807a43d540003480b01c003142c40842c00c010360302e00c00d4000d050001c0382643d01072004e26002c2603080403580002d10070903007680d60b601c1036194006601f250016501e100d2020022640c00c00011a026090740360b00e50b84039400141417109240500d008a07004403000141803000000d9100342160b2040c501220312a08002e078540312486d00e0001558040c00d0000103003419150050070091200c0c0c1c200d0940155000b03441507641e28112400d20b441c58441d0b02035200490b048003005861810b040c81528165070044091424103000254071151004004004686179030f000c0050030700000c07941c1c6800008000ca500c0d503103030340c094a00c1080b441055004011a03154908013608020f100c5416042c411140241006030f40c030903040c186030b806449550405404007000501c000307030141c1d008618500c40e08140e92400e100b001010401c03a112840a881a480401e0080105540c0f128491441d10408000b045400c1d100c040c0f0711888800e04402d038080da41034445045001003d04042c001e003041410110000c00540c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 909440017 1250 909438767 909438769
    0x20a0807080714042301060f030501030c03030c0512071b09020c07170f0601030506100b07030f05090109170d031a01141e0d1b03020304021809010b300a02 68
    0xa0510b600c01d42c94050014000011503880c2c80d842941100c807400445c12901c207040c00c80b41c0456400384144070005008002e1002c84a1003441350b00c1c183c03131744024848105443e5840031225484800e605035514068000b2012050b0503c10050101c20301c00d18121040d07000c444086820001d070340c1d0214541c1801000803087d41000419200150748051005404000d00415101c0c6024021002c080c9640b0070f02c0000300a0100004515108000e4140910b003e0358507660000458081d000d001400705843d40c181c02c1c41c141c01480540906403042c507101071007980d500108607050001695a1210350032140c0e001003416818090000035550780c4508000d050b0030640001c210364250350300e03200b03c1c5d880411144595045004404005201c0e03200c21520b524410b550040200000c0810713000751b000030032103c10420b00034002d4903c5141c004000d000c02c0d1307040b6003203003800c10300c0100003003070655803894031031365542e1031017918004540c04211308100d40d2501002e0796072400400c001104558031402d058001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 909441267 1250 909440017 909440023
    0x3020108060402160f15020f180301061a0f0d0906050406050f011202060714010c0906020f0606010807120f0e0c0a051e190e0403030209040c090608060409171303020a080708 76
    0x2642c8038006481c100914104144030a038086d124511650000500d08034140580d40684034040c00081003005040568007090708a03278540c4189104220200344040c00d050100b00030f00706034180b40d22121319100403007040380111407049908840c8985c2e140d00b403005010f40d40c401c950b0b0104c0c603044251015414400040040000e0b90002841000005035036000c000c080c0347d0b080ba890200a009124004441a01421030300d407501500005214003142c030a0b04440c0002c400d8094501a110b03a8000e80340c9900441c1c01414080781e0904042d01c4070001d4503031104e148280402d40c0c072200003030410701407100d0402540750000d0b88054803071840c2e0725006018020507000034103440000c650a503038400d81d0039020501403010354170103480706503024104400d0540540082054030011582003200304040f840503500400680140350005050700001034542c141079000d03411090151440900604404413100301c660700401e0040c80c02d000c00710f070030011410000c00d0344e00945128405441c2180c00c10344541d139 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 909442517 1250 909441267 909441307
    0x30f18110409031101021303020114120c0c0a050a0503090111030309100903020a1406071412060112020f0d15050603041104020a031e091b380d050103020108060402 72
    0x22007580d5410000302018000c0d0705404d454141d500080d9200c4d18201821041d1406a2106901003881d900c0400d10007501ea004444480105000350052034550a44451058005441038085813007070305450000304008020300e1000030703c02d0000b5651244003030001010400c0180352100a90320501c280030640171701050291107250101e400080c141344c241012450150214000341032949040c9010305034940204d02e5a2041207240c07100300e181100d00d00000018460b01144a10800c00b450100ba510340c410610290401c01d0710201505080c02002109150391004e0340c902c000710742d244460740040c5210303682d03a40100001c0700c0700c5003189030644842c03820000d00300d422441240d001a000a0150190f44201d1604680040108590f403060340e0050003040300705819108100291801030044005c0400c40c0300f6100c90b00c42e05490003550301c15106104640d0a80344a03030385440d0300041300d80602d00c006050403070220900429154510300014204d00f5024000038041d174010401d0001c5c07813001410140e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 909443767 1250 909442517 909442519
    0xa0e03120420060d050106030b0117040b07210608070f05030604030302130e0708040b1602030405040207150e0d0305010e07090e040204060302060c1e03040501091e05030d030f1811 79
    0x2550802000a0820b501c200702581c0700d070300a0300880c01c40c03038021803036000354180c0301c0549081100400090054407413201c403140c12504075480d0800034000404085003a60000b000e0300385045c45600d800c1d07803001244249500c842d581b640e0b842c0200135150080211100916101d01e10088040c140404284c542c0c100400c0501070640010b21000c2001c0c04891900081000e186046002d00700303140c2c01044180251001d854031010b840c0803480d64606044400d0b1040b429400662802d86010148030103500014010396100010308920707002e074022406020544000c0501610302c4442d01c0c200070b802c842e070603001090141d6541e010814241c0d0024000300c141d4070f0602c03040f400740c0d640707100040c0603000030b4200030340001021410310801403000503c6640c1e0445c07174158060b50a000c1454594a028500c41c1e00e00145130940c080113544900c82c0b4690089910010758109680c039007000c44d28006100b00c092001a68440d809800342903180704020150080f18020b0003040304603161030741c1042c566405a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 909445017 1250 909443767 909443783
    0x10e3f07170a1a0106120510051903020a33020d0c240218120604020603090a120503150f0d0204110438280c05010f050a0e031204 57
    0xc001c00c40100800b03101c0aa100d40c4881c15096007100440c01c0d00800e1080f000464031354031505034280c2c024000d861052101910b50f0b42000d18240400000f41a03005207419000b202c0700b0003002503142e00036200c2c007504c584540300c06032440842619884a80039130500d4103404a0122051610f42e0100302c51481c0100342c9040b01042c040f03820002600000400510141801881002d550b05e0490300508055200801c07a24074116046043c8441d00701801d240401c240c000c43c00107001407500001543e0454940411100d05115036529205844e46a07091500030401c0031040040c0c82401c80b010311003071041942c1003241d01e2107100c041405061a544000d100701d0b1103454085180d2921780c00d42e001080c014a4000202c0000368140b8184030080c465000d114941c2e5048414134003240303044507050b0038a603600340c1c0070399080315402d6540ca9990303080400b008610320154011402c00d01402c3c4412001e18000550760800856032400c0b07072130720101d1007003a420501c00d40066142010750140d021b80c2240c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 909446267 1250 909445017 909445049
    0xe10020604170d0e1b06180d050a080a080406051302130509011104090b090c070f060f0204030b1608070816180314062208030114010e3f07 61
    0x103145018014003d0102440c2e00c2d01c42c18034140702c400244001c1149200c001a040c5541e01c500b884843d1080040c4e003104403004007043c1c4c06605025010702241c9006205490302492165103001c810352154040b03000262120040c4001d121252142d103401140e107801b90070702c0f000a907000c68200c030b9403d001103d10603038a5000581c149020340020072045089801c042c2c2e11038940552200805204004034019242440000c0000c11201e084035906608a699080b0001d05503403041c0140105840e40c1174180c0c1c0078000040000c003c1080306001e00c10407107800300380703c454510081c400c04008142c4000c000c056800d02011410324180444590058908003210f842c2003904490304085503030004010040190000c0d00a0001040fa180114800c4d0100d050f078140402410031640310982c006001e00c201000104440c1d892012400040201814184884615800094103010790602d445a00410420390780640c1b031244001440e1441c60340d20307100c82002c0580c0b07025a0b10040ca019a0010302c4282d42 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 909447517 1250 909446267 909446303
    0x41206090f02040c0c0b0a020c060613200301030b1302010519030617010632060703020c0a08010e010b01030908090904140703080909161403070903080f09010e10020604 74
    0x4200401142c0281081c0011200e43c07800034182c0941c2e4005496014081c2d0105080034018000c03a880e0078030000040603075448070410000c0f800ba1083e84c9a407450750304d04c207000448000000b0348850301080000c0795100d42c91401e101c80c08881c01000902010104001400142e810200340e40c0c106000c03155005030b10901d00c9084d0020807039034200391455030340d0010501d4a41c1054008600fa10050b1a15203105148011000300e008080340a0290220040c0050622414214060244940248110360390b800300c00000c221400119009400165107651413142128400d008030003552a082c40c08021550094070340c0134487c0258a0000d00c1071120710041402e00500945e42400e5034003c0313094904a5a6030710302100203601a4440e103006045040025070003120880c80e003143c0c00d403a40c65401c03110401484518185d40014501030601191307100202c04182001c01034100100d0111000740d8503507540b0700140c811006070702d00900c2106544110f181041c0c3c041001f941155020101c4210305103c84 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 909448767 1250 909447517 909447533
    0x2404030204050103050a110316120c0506030411040b0612040204230708010303020c014107030221160609060b060a03051e1e06040b1f0e03010204120609 67
    0xa88003950060402002100b8058040b480e01003041c0714064021101511384249520703a4070798000c0c20446240504100890382c0d51108401866100b004000c844035120b4002841036081a6030a030307154101c01030320a095040c00e202e09011070034120743c2141090b060321400040c3c004018170090140d43c8990071405181100305503400004001c1441c006145840302000300040000d12094006226041c03144095500881e2518600460014001c583d40103a907200b9020105000a181c06007030780d08040c075415416000034150403032095026203a0441299100002074800801d00c05801c101081190800ba13140103d0703586080e40103801103005d80c10303428100e004000100f80c0c50740062001500d144600d80c50340c0540e11902040041e01e54100c510032114040e40801c0b01d0404850320b141e10480300c040c0082011551107000101b0202d031102401000c0b8180002000c0310080011414002025203a000704d40740b000b40c1c10580c0210b06240c50214a100c1e0007440400c0981100c1d99042d0034028442d0403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 909450017 1250 909448767 909448769
    0x604051c0204092105160803070903020307090e100b03070e0403020709110702040e0c03032d121b07030f201641030f100b010e030102092404 62
    0x40081280c3c1d0210b0420711054441c801030450075012500303040040718040c801303554664040380d074400000b504a6488002ca40e0014107003401f48040100000300581d41003100a01030314004002044040105402c0d03031404414040e8410058148035032101942c500141c840c007200c040c949060007944903802c0c264104103e98001c0040306042c05640354440e500c0000402c003c0c0d1080d01d04102841405405a85aa142040c5180c2c190402c100d0f05902207955442d1081000f108203a00d81c140110030514180e50317100402000540c3d100104001c09884811508405250b00c03c02d60392502c0000e581c0286445501c1743e0b4042800030028007415846d00c4580305103540c0c0c04c0c0314103c80114510500b132141010312881000c000800032041909118080a0308005460710f5604182c4808a09496a95200040c08a060b018419562110260300b41003010814900c0b01240000b080f030740e89400180b8401c1e1142c0c0080c06680108070160540c2c071085070308041144a05d010440030007588114a541d0711031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 909451267 1250 909450017 909450019
    0xe0c18041b0b0d060f0503190209150d050106150807080c0315040f0501090f0603020604051c0b04030c1209240201020c030a08150d050a030c020a091a1009050604051c02 74
    0x40490324004880403544030744c0940b01c01c01d42000c0a0b961b0b900416a0303e189032401911101c036242d490900505144001c0c3c1e8000d0110002010f88200880101da409074000506a0b400d81d142ea50422000d0b4001d0426000049036182502084c94480d402500c080f802820585102000100281d03403044076103052002c1c502c00038014407040791000e140c440900000e020b5103072030354a00754100d1501107261082d141102e034050002e42c2054501410090075010a0f60b2190410960100e8a000039140700b06503031050340302e91906c100340041c0d81009001e10740b00c80c0e20700051203041d40c01442a411f9282540c00130b441e0032500c14501e1441507a080307000e400740400380c1400c0d11001c01c2d010031580d08104d815100d032241c082003041248a4104110000d01c0d070100242541c0c00595042020074070414804c090140042c1c60890280c1d83c030300304a070441e501340b005241c070f941c10343c4403411203490040410354030704a00e807601800b000e0902000500e00c1c40350303100e441d01c24002401034080a030400d00e807400c992a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 909452517 1250 909451267 909451289
    0x30c031b080304030c0507050a08071404060512030c01050705030c030f100806072a03050301050d03030b0d12020f0703021c021207090b100f0c06020f0c01050a0e0c18041b 75
    0x5141c5130181c031118414801715101d002d44100410a0b04103410110304450030b180042520038505042c222140d02000d15070350b080740d00c540f0f01050070b4a070503020440010041c1d00842c0d481810072503c5003100d002a24400c20414108244414460f00006036038210428008003801516407088a41000f400741d8001c4c64140100001c00000581000322211507202c402c2c0421043c1c18400103200884c8030b908002000b0070014030052241e818103048202d6024401e050000c0c401d101140010600c030003240c2c04442c003000ca030660b40c440941c18028601c410010074010008142142c1c0001c90700c84000d07601c104c900b0312601da00c2041d56180d012030498003415206a8661984501611b8041c0c85801da60034054040046807030710091040140b01d452000300c1d070701c064a001c0300ea5215800380d0302c081d1442c2e088200178407005a114800f03100d881c2c00b40100442c005080c03581266818140214101034074030a51000500c1c840c0342000458507588603600003c03510110700c0f43c82c0301c2c11500070107400c80340c0210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 909453767 1250 909452517 909452521
    0x403021c0b0903031626070c200f010e030c1e0910030203071a0406050d09080c1006090b030312062b02011205160e010504080102131401020a030c031b0803 68
    0x1c0303000f200460182100015078000000c00082c156000c611003d524021807103260b00344250541c48560380c43e0494510b00e003d1000d400503403900a900c200185041090458102d0346803203900e0061800441d40c42c003800c1c03001050014200281c1c80300c0300d81000c24000c206800c5944c8045015a42007040d184000780102114100322241c2c000c80039090100301c0c0a032080728000314405800005400a4210300343c00c05c2d24081c2407060485041e00411500384c5200c0d25040c407400042c0601c0e01514a092070000184030801c0b04d0000c20701a281181e0214208518221001311a600d022040300e800c0c1a9010b11441741d0340751078020070078285ca41c00f42003201c881d18042081140c12440c0e2050700c0c1c175000341e03528601c03081404241401c5920aa9031a690b841003500717422204ca004408101c5a00c60505189040c940c0d206295800c0e6401300303182801003500100309005450b60076a105d03000001c288000c000c04079159501500d202000400a4284a4408000d08a81c0840010f601c8155800f4055076224 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 909455017 1250 909453767 909453781
    0x180a110c070e01140a030611070c090515122a03070b0a0f050a091701140c22030f17160f0203100e0606040f020c030705030415140403021c0b 62
    0x140400d000b140c2e007021000c000001c07035501c11201c440b013030300d40103004286040c9161f40341001003030204c1080030414030900480f400f01d001e031101e0f80c0040007049000b05040c83c114030b54448150404080611503010428955540d41c4c000070b070880c03801c3c0d40840c8110076504416401850b04250a41b9070350611400b08003089802a85002d0141e4082c40d84a18440745c10711401580d1900690600380c0c001170b051700d41001800250120305a080640303000011f000d480074810f482082004a800101550001500b1403080032134601016002c0482e81c0b528401d80d0469440e09030000705450081c01b00e9040103640a10400c80d04211402d141c20041c0d0800004035616081590784245501a4070900900515441c81c510600440c82c0d6000e01001a0501d03584034810040200301703000c2060702d01d070b509110240c094581080200038407401000155140c520700380d03c601c8d1031501118110104482c0340380b564407000005c81510f0940c0e6045803003086501d543da04942140140b480040d0001008a05200c84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 909456267 1250 909455017 909455023
    0x10f0c0201020a120e030319020d05070206090f06040b16091e0501030e03031911071b0503071e061d04090b0117030702010e0409170d050a1a180a110c 66
    0xb2000c1c0546403000500d0f003140d441d908950603c01d80c0e105a1b0010030004207100480320940000d200c82000060038105100700c00022541c00b2140080035900070004c2c031210200c00c0180c050031940e154010220b0303203481e0f070719101c03404005000100d8a08030200455403140c024a030407000b030030245211140109142e2100412482ca074400c060100340b0b0903e00d040050000300441c1e1003505007440301c1d4603001d0021001e9008141d01d021341541d0b00c206004038000500c1a0452000b251042030712101d64a0400003010305040f502d0348501d090468094a100c54001c1065080342200d000f411b01050360b070240707501000059084844141e00600c2c020017001040460b00c902c0781625800c0c07000c0001d00c1ca002000b680e030380c800c481000e40400c0c000141c000d40c1c0c0c85c10342c02c0b05880c184070340c00718420400c0c13423400100d50380c00c0410002c202584400130400400203900c52101160038112000e2168443ca0000c20001110b00340707440459001c28000600f40280f9400c00c840b00740490010903622100c2000c0b45072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 909457517 1250 909456267 909456277
    0x109031416090603020102060f0a0f0e0106171c05031003080a1d19180603052a0405060a060c0c261b09060915090a06030221030301060f02010f0c020102 67
    0x74140040408299041c1c00d10076201580d6068008081035180c0c900c04482c02440204000a0309480d550024206840303409a200541820000800d6050038208483c0c18490041680442684454103401181d034008022035081003960410344d07039a845407880c003204162541c201402c0704e080090740481c4a58410b10b60075041001001d40309019000b03c08005110b1100040500013400b4294180462603600c0b0134440d000180000016400703540c0c2e61128200300d049124403a241c22410a01c04250480c00d06041c07000d90215404c01a40c501400055654031141c082c180401400701405400c000f20760b4140e80190118180c00035503081c0080b043e01c05124401c400311400c1c0034901c02c00400346210140311140d00c6009098030229911181030100071840103004a038100d660550340c10a50300c580c000640521480c0c4004140203081d401405040d1003001c00c0209510800003d461008030f020080e0f03815102103213401c1c811500b00b03000881c00340500400d0340e0b509030301d04490145072a8056000f04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 909458767 1250 909457517 909457543
    0x20f16050f0d020606040b01030b03060108030306090f0f070e0402090414060a06050c03031b040f0b1917071b021314060111030a05030a0212041208180c090601090314 73
    0x148280d200c4035402a190382c041c0200b180541d00000101e40c0a03c2d20b40c000b240030034418500041c038545884006131400001703031b01074101a0000410310040d82010928070f80d01244220303081e0300030305003200e542c0940301d8018001e01c108201418100c0d040d03942c070b404448a200001784103100c80741c56003004111492040c4d4500e80b00d203095030b400150141c041c500307458241815101850031035a5170f8400110a00301440c0801c43c9523800c00c40440d0404e1300042c00030151141f82c1045854954845c404055050040c400c20300740400411440d850841c0c180d80183d0100440c03030b02c00000c8500e2558044480b075000c0c9c00940c000e1401100341c1e100002a407250642040c400c0c0c400e80291608001910b4400e2859444a00754001f00802c1104c0da0185000f142c1004100c440185003078019007040050b0f807416038045445026a0040700a0320fa440482c2907001f80c1c800d2210202145607000250340e0340d511140850242c0c001100141e15030707000d190020b0055030018600c1c00344420703040c8000d4984800d40605 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 909460017 1250 909458767 909458773
    0xd051b010c330b0108010302060d090c06091d011521090305030604150506070308100905070203070c050f0d110301061d010e071404090b1513030c120f03050d020f1605 73
    0x2421a1002c00d003c2c201540720182c45084080c0d01f19020311043e40d01900f05014195101d004020018454041d02d20041c4207656030100e0803030030180d0030b400c0010500010480f9040d048014065030802c1011800c17040c0ca03030704046150181c107a43d14035450110030501180700f450036111070203054000e00254030440702150104921207420071004080c0e00d09001e25500414140311040000b030054603410340000b840d40081403e907a5840e8600e00b036400450700040140c102060003803c00088103200c0e0080c200c100c2d0104489440d07400804d900b51006100070f0200d280c82c405030b4545880030350251000d02669060100c0c603440012020039210000e2003100d00c119000c01c00110110f00c103429401606181442d481e142138602400500540001c1c2c08180d80487c4501e003c0c40141c3c0e140d0014160300c0302403041c0c0210207165040c0400500181d80c0314801c5034100d1000b90000034000c88440d4040f81e0316081158884400c004454020b000d05e03418200c6116000410101c0c00004441c01e0403070300e00c2403040f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 909461267 1250 909460017 909460103
    0x4080d0e0a0f0302060d090b070903021e01120f060b030a051608040305090907020f0601060807090b0c10022d04090f0b030705091302150c010b0d051b010c 68
    0x2440080d046078802e400191280c144107100514098000780000741e803800001c0f0b8000b42a0712000c508420940d1a0008244a01410000c50400750304443c2182d0250240114440904d03001a18841418500201d071682c1c0301507107590007078264400005410002134990b00ca10341504840010601035401411a1421500390001607204400c114442c1d80d0584e44e1505002d00701d410300c031580c2009028001580242c1e40900c003100c2e000c120f04c60003000d03aa6204441c40c1400c0f60058490100d940182c800c00d40100700c0e2908407140041d900d01c2070380c0e60700001030341c2e040032827031180c050b40c801301841c0c040414078002a010506040050816518100c80c2001510005c0da41c0b10300f100c50700f5012a4054002c0d00c0c00700110720b0b0807404c0c1581310230a41c00c00c1091640c542d0004100782d4070b400100390b440501003103050000b81700b4421425040801c0d64214445001b5442e25956041c0440121548100081440b202c03039220300305116085502446880d4140d49024103a5602654003c2e5041c2400381806 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 909462517 1250 909461267 909461269
    0x30e011a0f03070b0720100e0a06021501050d050c09090304060816080f040503090415090b030f03030c13120b0f22081e0a211a090601031104080d0e 65
    0x1142c00403a0784c80011207207011942e80ea900e11304003041101a04400f04038000601c651540034920001000340e654100010751a00100910044070303030001011903000300038000d29606403002c0d25054980450790301c0043d07403007458000e1038819542a542d4111904e8024001003510010207802600c0c400e4a41c160035540725008034a10303480ca500c032000020342c608041141c1c0c507003511460b500b16003d00b06492800c3c10101c0030405442682c09030b159400070b04101004020075600c0b542c0d481c20804c502520703458504200752640c90001800d50076a25100084004082003600c0000d8010003110407850003002050800380884101241d8020944841d400068140c030036600c4080b140002000005140061a8680544039042611020740f100245015580c010840c0000b9000d500125130341c06101d2500f048040203041c41c0850100c09290030301c02c500c4548100c182c00b1110540301654104010340d12600121f0140040683e02c0694a10004001c611660081641c05100d200350711117aa030055000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 909463767 1250 909462517 909462523
    0xf05030a0f03020909131502030112060509030a02122b020a020105100302100f05040b03041407060804050c09190c030c0f051905090a0b030901050612030c1507030e011a0f03 76
    0x41044c030751010788540029091070565143c1a2014000d507040032880200c0c0d0102022a88280c100c1014503194003818010407046000d19a804003103800034504004012130301a40e54402c4041c10080312001052600c1a90f40c821a10301b007154820f0034540e01d100c07011298100a5000c051b2040040d400d00002911030580c2c8540002240da020303161190382da42103907084405040c1e21000c40d0030090704220002d1000d40d4680510701882c010f1510104080180410394941911b55001d2418400040f040001181c1c02045040c45124140d40d119843d5a4844a103045540000d0b00301d00303150300e04244100c88a0b07040d07100c4001d4071010784440d0788840000320709a9680c0510301840d80d0a8045242d1120728a00c520050400d07580043d1040e40040e46403c00241c003034100b26030102480c1e541d00d04104c0c4900c0c0020912000a0450003c0e500c1c04900030081c94803a041c10315240f420055580118045510035440b8000c0192164020800c2a0780b480d10504102120360805200c0c07104441c031000546804 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 909465017 1250 909463767 909463777
    0x2709030210020a02120408010b0f0a030b0f0a0608031c1503020901031b030206121603020309061303020c032a01080c0301090b1926010606120908070f05030a0f0302 72
    0x680080c40d4080c0d850300004040c0d40f007504000b0443c000c080c0c1c2407696121510181000d05034450001c40e00a4409040c0720780b180d0303442e054074071500071000100040707100d588030203400482501c80410070707940381c81c1806c000d844650b21501c2c861000141401e9101c0d404a05206110783d09001030001c1c4d90340c08030210104440d4000690700910041c0100300040708002c1c4a46207014881002d069981d407030700020030a0700040158500e211390302c402c112880441c244403040f0300f10141411400d6041803c00550345450040c500303160f20003484510000c3c14000c1141000c41480201150070700080e0788260420b9550b100c00c0d130328541d81e00c206a035020798016640c40d80704036955005103055130b10742a68a8090442c00525940284400a440060f151070720a050058544209035a0406000b0355400030122010710030381c503460745408014041c66903c102500d007c0c0c49040804207840d24982441240b03441034400c000c0c200020704004908100012000d02060706560319090000315140d50f003034003a0b11407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 909466267 1250 909465017 909465023
    0x1314150f191b08060a0e070504080606030304152102031911070209070818030a090e060a2111030709050f100312050a051308010e010e03070c0b0c1203012709 69
    0x400c8400780e400d1441421000d520134401040c030100280d540d10003404109040d1008000104002824000014104805500076000383e00031842d00d442c000b41000c1451000754000100220a06104200c0ca103102100b00401604407046649042070a25030010401d01b1a1100b8440e007840b603002c0f02d01c15050b084e10246a0060b0040c6a0740e9141c4408881e4020020212078039140e03003146d44540100100301030840840b40303031105140f1070305240859203840d20042a251003242243d80512545404103c03d0124900302c02e43c245c40481d46142100b200181402400e4040c401c010740040c40f1451600603030b02641d881c80c00704410f9213036100d507401050014040682301e51040580b400d0b0851140c0010581c90010340b8159003000386e082403006009500d540715034202d0f0b444480401c5401420321480b50003209980043d8500b4249954481300404c41e8400c248811401080310701c10114240b206c0c0d110a03c0d0015001e540350303115181d405403240b04402c1284c42c000a0b040102c20020940705061045030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 909467517 1250 909466267 909466301
    0xa06090b010309080f0c031e0403020414160f02030c0f01050403080106110706050706020705010c09032a0e09010209060c0109030801140906040b060c0d020f10051314150f19 76
    0x1782e01d0084001c59400840450014402002044c9078111210713000c6c011071401c1d8200b0350740c1381e10b9401000150b07180c00701900e030a825144180309400284c00c0b00309801e42a10b040c443d150584c1c0c0d12060341140182841d0006501440c2040e400d10702040d40305520491190700c680401340d80b29102240c0c200107000c1c0040c007560081c2400c1c0710701409003011b00009441001d026103014201c0c1c1c2c801c0d09586540a00b00c010540d20401441003100300480c6540c0c1e940d20000e40d414000c503551340c00360211300d28411010362680b040c0229004040030740481e204940050541540e0341c2c6803418050080030a00c8080d00000d00b40b8001141c0301c0201002050039402c010005495502c50804010040c111010640c0e0b100404112801c030381d10051201c8248005541c016000300e40c0c55000340380c1031400e0304060007034440c038200c1080209a443c1180f5688241c0001d016081c01c000700741800d2038004a03c0c0f221404030501c600b045007481d1103034403a502c15020b641d41c15640300b400416900582d1071f0242c3c0d40c040d102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 909468767 1250 909467517 909467527
    0x30e0f1f02031003080c0f0d020c01050405042301060818121207090306050705090306160801030b04261c090b1306061a19021f020706140a06090b01030908 68
    0x407a000746070040c02c3c1805003d12160b480d601c0e41c1c0345074480720f250301c4140c000d060030040101080c0085040034403d030014012030720750400002d001c0d01c15401914403690f52140c086410181c51500b41d8001d1014515031011395854480c017a0100a040350032003c0b141c8501d0007160700039000f103079010880340b10035400340c140600e1903100d40f68007000928090400ca017001000020961a01906025002c40e84889540b2030781101807605280c0300070200b10903540c400e0100c040c00c135400b480c07140c110380d080388500616884500d03001d0301c07400380081c8502580c45008480f5075201c401100500c030100d500040da50b0f05680800d040401d5840c15000a0300c1070b06558002511500725901540e4142c0c841e201c0040c01c151101d8070190000c4042e00d000050900c00320b25011603104044c42601c42c452030380002d0074031805488036174590708a00040922160b0b0089038078000c0108030b40104100440c501954000341c070340f43d400000108a14481c0e41d01031408c003051144194000c2c4a012200c80d00828124940 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 909470017 1250 909468767 909468823
    0x10203040e130f03031e0207021014070b01090506090619170f070b040e010e090d0e0105121305011b05040311060c16030512030c121f06030e0f 63
    0x188000601504030101007091150015444181140754144a17840004542c140f00c02e2980c2c5024103100080c904510404c1542d001d85c0d1103d06450a034076051910640c20a01100119182d004030034000b880000841c001017064042034210f54420201074812200554451081240c20819215102424210712006000c1c2001c04545403065030180d5084400301103204890a241840603801601119004101032100c48000303010140140f0790780c20b02c2c4001d0708110309039540301d01501c28950244a0742c80555038860340900160b410030344241d41584000d103003078040000f41d0914441c040b00c045d481d080550540000304065112070755003580d038588c1041d0940ea03401c503401d024102115407150b01881003924900b010040c801004400244199a082c40c515025280c407011010002d00300805104100120301100d05449030203e8010134926280c458428820400501c0d03031005116241c01e800102d402d40d09904240307810b800410072120124400070801d0f84503102198600e1407031001a00203014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 909471267 1250 909470017 909470039
    0x10c060902060408070e0105040f0b01050a03020d0612050c0414011202120a05190c153507021e1b120c041a0f0d110d0807020316032001020304 63
    0x800e07480900b9030b80c50035440e010780f103242c4445a407120a80c404118014801400d050084204400c540c1c14140035600841c0c0c0080c1c4a4080c0c3c3c5484020941d000c50501008041604000018075408840100c41d41060600c981c461a203c080c0364051401c0c0207405000c1040c11210781d0480384825518003000c821a420050b403052110b1850340d0318400c01e002e03c40440d01c03c2c01000700701042c1c040500e07154407852905076440d0321154020200e1140105507281074a410422040102c1961610210740340d0221614440f94008286111a0400407008000400350000f80b40210404902d5a500b8015410907810b0b076260646802d0b4203400210707505030b08444c00c01ea003409901c1c3e0f0468080d980883c195102060803038290350310100d0b180203034503001034807401c0c090848091b608050703c2c228050021901c03001d41540030034101c10300502400440320240800c07501503070025070f4014107948064107500e00306441d0406038041511f0121748103a0341141e8048501140645940603006181080d00d01120844 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 909472517 1250 909471267 909471281
    0x1e040905101809230d0210060b0307030905010914030a030b0a18020f120f0601082208160804030c150906080f0403090b0a03140a020a0c0f17161e02010c06 68
    0x2098420f1100040740a83e5000800d52005031300c030001c042085101e000246082c00907008802401d140c02d009004034120751045a505c03012504011031207455a241550051503110001740c01c000304460b2214801c4008801030000f4401079405202a151440802c907452400c0e103c0c1509041401d400b01e000407445402800c0c414070010080b60800c2c1440c11400080d207030484803041d004100c030042001a6820030fa189801403e124095161030b820300c4151030051003807a50140c4641c2000c20b0604032480020703101c415031035200c200951215900c1c501076a10312514040c2021190b03050304002400c43c032480e140c00440d84030f40c1d140f201c1034031042c60b0300c500504d000d8416020041c6001d00400d000e0304540c02030104811590f800551458001e0010520044c05052501c00302d0040049800d500e5224118590a980001244001c96413900d0682c1841491281d141e10281e00454043c0c090388032074404040490280c1c1d0340360454158104c070311402130312885d0300901141a030300a01012a142ea03000701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 909473767 1250 909472517 909472523
    0x60e0102031819080a050c0301050c2502060c030a020c040b010e060313060b0904080315030d05041a090d030c06050f0709090b040f051006020c0906060318031e040905101809 76
    0xf4481529002c0c0682409108141030310250b00841109825080903c0f800e0b81c860000ca64407424682144070700c0e4110340341d401180c90242c005400c00d2040d07550f4001200c0003e03403c1341c1201c0c7d0350403004a0194232001c0304040d6030f1145140410035500795002d010500b42030300340104607900c1c0d42e4540203003880d1041402c3c0b0644940d99150f584141c141c0303810700040d0003203014071a466240c0c90480c25104100300907500c2c0502076044441c000d810550000c050305c054504440312044e24dd91085084d80043c0a07240740d030b0703600046100e61402815040440c1c00141801100300303014030b9443c3c2007106100041076a010f00050200b5204110000440c0e00c507032801e10b40184003080703448215440b0010340c1d00646511482d501c20400400103980c0401085041c2c01701034480d01c1540c0780c0310000072210f000c001c00362018100900c015047d04901401114611309030040c0c0c4081840c0c482c25104a030350002d004a250046c80d19021820107403580d80680112900348000381011031042e140340c0080c1124007000c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 909475017 1250 909473767 909473809
    0x230901050c0f0a09090c270b030a1a0d0c080708010b01021c05130b090a08010b130905070e090a030e030f0d05161509060b06030f1b071b060e01020318 66
    0x20178402001d001d142828141d56854a80e580d000e401c1e03201c0e2044008044081c00b040780340742000b01c0781140c0305032030f88185100000941c45a860020b02c0320440c1c945c450582c0110003a40702c000700604055154255010f03a0125100c498965840d80e0072182c0400c0d0301405a44a14150115414144c020a40c070b01018074001d414030600315100b0921101c142c001042000380450582241c2c200300b141480142074443c000e2056002d224041412002c0c40c038040a05143c803a04281c0900c801040310000234042c1c00d004100618000b102d20b41c4030362580030700320001280c800f81184136140004008a12030104406401c401c0000002600d242d400b41d90f4940105003001070740e1000c112040c0449003030030350170300c4003240901d205d1900d0012036000100d4076224203410301c1809034100c40b581c00b555111200e26180d40b588410068582514090800300500c00e000c22880e112000801c3c00c580011074840d500c6246a1581c05070059859014511007501036005144000ba0f40340b9004172071184c0030b4984540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 909476267 1250 909475017 909475019
    0xf050d140313031205130506090616080901170717102309010f18020306030a062a0807050d110f0703020601080c04060311010e13230901050c0f0a09 65
    0x105a0860704000c2019000342c1e0304040030010700c054828060360b0f1654604c1c099162144a4018001c03402e00d50145a0103500c01103043c942c2c3e5200d0380100ca0b00041004c0704143d1001c1c0c50725028245d98455908980040c0000008800b404240701099000c4c82c0d55858050740c2c05888880420031190017448500b027030741489400503c05040c44140859140040011807140b00c1074403d000714000306900400901081407410000f030030444140425460b5044000b42e030365101c01c800280f030081c65003005032132685840c00480701d00d210300b0400c48650f05400302c6040802240c820075903061904441d40000b01e0400c0003202081540d0340c2c00f1301d0030158503444050500c0c3c0302080c0180c0b245c10036a0224003586c0510010700218808200d003a5100400321010b005160940d0b6032804119080c0c504103050016035807a40840380c1d19425090500301107440d08105100388044042503481d9041001414420f0740e8010410b201810301802c0c2c4142401c0c03440600c0c107039001c1040b080359030100b2011010000c401e54 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 909477517 1250 909476267 909476303
    0x2090411041d0705030105151f091a0c061602030a0f0c1b0305060109050601090e09013b0307110907210212010b1e0d020d060801051f0f050d 62
    0x8410340e140c600307a00410301c0f5401d04080c5421030380043c0c0003a000c0c0d070940800c40400d640d4407040c510680440362a02c80c0618a6203400d580751401034008070a501c80000380e84260420003005414480c43d079000f191580d8680003024600c104001c401c3d82d006800030021604002d000e420546265062494449402d4003261039510001c11213101809041120a9040046c41401c0110501400f583e600c00c0219050590010b490740c0b500307103c1c8902a441840000d400b00f0820362020041c211441034058070480c1c074200740200021054080c1c00d41c03040c604001c0898000000c140c940d001e50094500c902003c1034001c001004e48010702c1c41c0100201028042141d81d403442c10743c452403019600150f16141000944145194140c1001c40c0950040c0090020301903107801a180b89902106400d9440340820303008000713441041d0002c0e00300e5050140001d403aa83c150f00851080b03100a01151041c00408000c1410081130301c00c1d0110740707580440c10f00c01c2d890104440b034000e0384541701d103070000b84011f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 909478767 1250 909477517 909477551
    0x60f090c06180b120a15060207182c061b0f0904270515040206030a0509190c030b060a0b0307030527010b0109050a08030d0905010608150712090209041104 68
    0x3034030303d007900002141400303080105ca000c0c1545010b0034a140103070081c1020030081d9594070522a844031003200150801002501c1d40c064181651000038281d080840e0213411041d4040340c80d5058118840d02c0c00203881c01141d4501303400d4400700e401c07000346801142034110726141c219010040e4042d039101200091030358030034114510100f100c841000c520009040c1141400100801424030504c510208401642c4c5c4000701da6000b00800c900040c3d81e1a90311003a45007201e116007240c201c0d40002c404a0a003d5030321000700c00c49104410108840e910f20040c000c500d4428800d80125120a1021505450080c0c10803a44074103030400008090000300d0b23000400000507041c04c03150b42d540d0300500006590001a00025000948031912007074540000103a5a110302c850300d00c3c044d0342c4c801d440b404014080d084000204145000c0300c0164544600034004484162174000c0850300034820780310346034114010044041d80084c0028415942c0740c886401250301105140c0e84642c1c0e43e88020b0f5004012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 909480017 1250 909478767 909478777
    0x9100516060f020d060e04060b0405061c0512040f080f03040303090303051c050c19020c1c0c0e040302030a0909060b070201141e18030c031b010c06020f07060f090c06180b 75
    0x20791001d05c40380c03d060070708c58102c5106070007450266007400d04000c2c0544400419100b201d400030704901d021030341d40c01c000381440484511907840300800140000c062542005030421b444000d0240c6d030052040540440d034910581c400100400c800a81c100003081c0602c0240446100608030541c844005000f000c003200e00172542d0703a04a540201b100810f0812100182d01701e0344807400140586100310000500301003020100601c3d8014505100d020001d5804d6144000c205a00c1c8400107400c1925020351641c115003081e8001408000c0c0028240085029041c00c40e0240d185440c034244a98004451407801d5000d00807401d241007050800b100c0498001c0003808000c080507070b440d0711284484d100c49012a1b01464865400641c012220790340104040e40507404103454403100f80c1d40c1030010386011102450241000d803010480d602d00d85c4403c0010402140715190400441c00404007840499100c0d003005001e4a14142c030500c4441e018509500c1c2101c0301d80242d958042c1e850032000c0b025801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 909481267 1250 909480017 909480029
    0x4090608011b03021305152a120f04031b12031d120715020f032d0c030901110f0a3203180f090c09100516060f020d06 52
    0x922101c50002d00b8901100700103012207450b0035032800f2943d1111500340f503a1401113500c02c101003885c0d85c02c00d0400e0000c03180300b410140600c520f03040340501000944642501c1040c030710301800c1d014000d190246000c0341d2000f150010300a04060964031362201e00c1c541043d10790307248082d0048c00304061000030505080a0302c659180b2140350f039401380d40c9090f1004c0314100d074000c06001e01d03041c0d44008042103803401d880b1102d010889003a004ea40486c90600103c8013000e09000000e40000e0081545d002002560b806010307415801800100301140ca1180301441d60f050382051100800940c4100b0840300c10940c1e9004842d8070002d52115541403520203101182c4072404500081c00011801c1e809047c0705000003500c14a00c40000d500035100c0c030414800d01c1ca0041180ca00e0051036a40c030444401004020b004c40d169031070700c207070b000d08582c2c010740b1220f105202100301d2401c40c41c03084003121590a0107482450310382126540e41005031004030884c181d11902400300d00d0b104203032441000d0050207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 909482517 1250 909481267 909481271
    0x70315020d061d150f06040501050313060204080d0f0206040c120c03020a08100b04020405061213060507030603031206061b1403030c03010f14090705030415050f06011205060f01030207080409060801 87
    0x1807022113440e4140c5000255030054204030450740c8a580c075103041d101210400e0030314680d65924081c165030b101280c1000104800c0c07002c1001f05d1012000501c3c40c180d440a0f896004040322088030983e81c84504440040040b00c1100c000d11140d01d1030010055000d129411503000d007a1a07030300042140703105030060246d0307911054224100c00814010071800c000140e404501c1c0c5820540804c109224029140c01006142d2022801d40c2c070030185070254031a040394080146040240c0014041d0103107100030f030002266025191001c009a1003900100d07182c40e141e54035499012665656664068942034030000c40340c3e00d15085070b4a0a100031445041c003401001d03501c2d81010382558030602281c000d1007641c200b140a9034581c1e100c0d54887c942140d0141801600caa64916001440f803142014142c20f4600340824010949142d03410207001d076000b601c441ca480f00d90320a07035004444040300c0c2c10f035020f0f9882c000905154001d90007810700c9801014482d01c0d154442c0d45030400c0e5003942d48009140d079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 909483767 1250 909482517 909482521
    0x509060d1a040912090522270f0b0a14070f020c0303071a0c04060206010915120b15030d0e0d020406050a03030207060201050106110a14032712070315020d061d 70
    0x45e0788031041901a05007101c3c25500c400503484280050740c0000c803062050390769840c11350002031b040003410000e0780e40c180d03800403c4c0e0900e14001e1880c2510701d0080760440e40500201d82c2d420214084c3c5001c0000c001c4c900c59841e59001e070211041854425144190302844503420b01e01e882c18002805e105020b4044070b07404203d060000c1004030002409003509090034413081c0311442c1d02085850454030b5100e404900c41607100f10031000881551721828040080880240400c0144c580d11449040519848100b01d01200c0a26450b458070308a1040060f000580500d400e1801d140f0382c01e05140041c100040c80b5844002040c1d02c0380841d00140d01580c454142003141d20303824011540034150510300b0030280703001000e403a590b50440160003010b22181c881443c00d6801c0c10415a0f0800400740f90b540790b20009410545001502010410f00682c08083c0029003044001460001c0307035441240c1e40783c501c1c03190305400020340000442d80841d83d200d4800286204041034102c082d00307444210304001e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 909485017 1250 909483767 909483803
    0x516051509060702071a0d0c02010507110d210b06030405060a0b0a03020d030c060e030d060305010e0c090708100302031b0f01140a0f110102030709050109060509060d1a0409 76
    0x51003009040180d254041020404000d0b8045600030072502009440c3c4007810410320840300d180103104a003040310f880d0121540070143d05401140c043c440d00d8031960501080c102e503540d269440171044001007041c0c5440010501d078a02404a0444244100010070b0045d06000034450b902c1918152030540c802001e0000048240c0f1030003074254800c81d0044062481d690109807038404a131406020700031106221402e200003030300242100d00441c4140d90b075409141810100408490005903040c1d0320b405076410105400180f0301c81e41860050165942d95520783e4100c89080c0014904c10041c112044000b0050314200030700c051040b00b8101403100c003040102030048514128442c2d0b4100540c4800510305001c0f12022150300c114075150212525954a03001e540861003003800850f0366200008105131141c0c80144182600c03026624100c0e655910502115039002d0702010703a074840750820950721040340650010039040d910620b40c9018002250005044031f107940d40c1a180c005030031000303444d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 909486267 1250 909485017 909485053
    0x180109081005040c0905060a03080304060e010c02012309100e030f0a0302030708091b090702070e040f02040608070b0f07170a0804020415060813060b0907020d090e0c090f01051605 79
    0x1170682100308115510300300001075141c03040351001801701140000800c0600140e41c0106071020409030091080e180e030128024020003980010258641d44104101000440312400c40e004050040041600f4180c0081c03003001442800040031092104200d80e450b9412442c0160050704882e4034010381340d00d013910020700f54190041c844402e0b0340010989240602010882c1a00c2a00984042c101070b0380e000c0d004d03450701001d50007220310302101c1020401044240b030100c80c6040d00c01d45040c800c2558811211f40c2c0c0d09070301e0041a0075490140001042d2035086000740141d24000e0b81b0b440c404a110f640306000990001c101d40300060a103000308425400e150188036086001003220b01112440c00b03000404089001d070407542ca211008031044184511900711100b01400103001250904102001135500c02c0100c100300013083e4107420000301c20300e0724020b0340d10984883c42c00d00d142581e0a004c0005005100b1015410f0020034402a40f00061402045140900c00c070018041c6184d48100310072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 909487517 1250 909486267 909486269
    0x3120408030105040b0a0b180109050402070606080c030a2310060602010c1d130f02070218040506090604030c0f030210111b03040f1a070b0a05040605061005180109081005040c 77
    0x405146020020021030840004840b002c0c48c0f202d00b404507400039000102e618403c1540041c0e0700c0350000c07a010301400802d84c0041e0494481400b104e5000d02d60b201407580700d091000002d00402900001c6030080300f00040c02c40c000181034000e82d02500354000c50f800442c4c0482c0c001000603135454501c1c01c0c0d030541110125488132074005110001d030040d030001071113403c415405080d03502e469407000e80310140190169920107074018820000c01c8914801a030441c01d0488082d40e46128050110f0642c400220f415805503400d503448100c1c1a50030b0302c4210402d01c4070402201184200382640f80007440c64452495103102c0396900a0f61605d44101051403006074840c4500c070364004000c104161034115000c1c00c200e0b42400411070b2107900c0c2c0c01356040340e400f840c1c1c0c010f40b902d0341c8a410416220400c0d440039100302d204030820425600c1d098188034413400620425408a402000ba1404481c1000421044e17000149845aa200d4640c5041810140d181c0031400d0203680f207900340010042403070394042c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 909488767 1250 909487517 909487519
    0xa05061c0c0804120914061303021203120c07170a1707050d0c08100504181a040c171b04110c030705010b0306070212070c030f0b010501020d050c070504050903120408030105040b 78
    0x4100300d003410450450801211b0700c6030710600000400c122404400f000341402150014903d5040e102c070400051b40301d92140030884041c1c0321a80004512160711029610481c4d0002ca070000030458540340c1d96165404498440c06104046807800020b1104a00301d910481440c1d5030583c403000205010cc0070355806000110922401e8810003c00c400c02801a004888040358042220880000c400200680040000c0c0c010b8a011552003028810748850034042c41c8600081001c281c2e484001d4000301d01e0281c01e4170703080d80100703240b0881064442d825164070800240009820300e050a11902c565101c100c82d00074a4001280706800e001d002c0c490b440d03020070140d0140ca59480d044000a40b28640540307541550035000c0b80130f42c24032400795100350281d44e11610a42400b01941070041ca0700c0424400c59005114850030701d014144038000707503180700c1214070042411906250400003d010001c00030070481c401885a40c1000540d0740502c4e00640c060b5200b142d5a50424081c0f100b070700c41d490516 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 909490017 1250 909488767 909488777
    0x225020906010e22090510020403110d0b040318050607060e01050708060303030a0f06050a0b1b21090d08070f03090f1d070c1407080106140a05061c0c080412 69
    0x783c0c000c1c1c45094101d11a04001204451904600240350000b00300704030001e0280e00c00d903010342c80c0b541010340c020003c0c2c1e4090716050148410100400c585020861002840c440c4440301240000303016007510b6840c1003804ca4960999a121404540b80d80c10214060315069141c0010280d0f2110038411980c00c0011450100ca0740e02e80000482d90320700c4090510401c00343d44440191400010381d00040c040c0c07400800c803501040e42d5514510721a00000b410318480304c0c50070b10050710783c1d000040c0c100040b42e0301c0702c809103207001c2100c000131250888090180c21048944400000890101c002c169481c1324402c404a81100b03420020702040701a00b0100e9074104c0310340c050003c0d1140c0c18068045000c0007512484c150782d0a402221061040e507402010316059031303012000e0002c04501c1000b80d52000d4001c020040d5216590161110a003140e503810018040c001c0c8004e040c2403004180c810800085060b07400b0310048640c080b130703000a0a000028502100340004c009564500101b46180c620f00307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 909491267 1250 909490017 909490037
    0xc0c09010e0f01150201060515030a1409100b041103040b0906011202090621120c0c04020405060405010e031908190215010501081005090a1b020f0d080604022502090601 74
    0x469a1240b01800f42c2c01094078055070300d1020510075042000542030250119200003504104201181c1050750b800c80c6803030500701101c405402c4092500d2281e140351004000c60b108519030f0380000c05801d2419900241c98005904c2004840070046008a1150300d50600754035009113418107008042c1c0110301942000c0020b040076940d040744254220104480810104102c400c2e511101b090702001010030b0f00a40700c0c9014aa0802405080c00c1604d040a075406c04046508010803485039010b050b41c018070902080c8200e522502403401240f202500300c80c002031140d071925441005156003121074101c0010b124170024200c02c94100b003100c1c01d00003040340440204c204500203005004450400c0444000a030380c400d1442da540d401408098112040ca090140700f0002412000c0c81c400070300b10103400041415880042c501d40c18921002c00b0f1320000205a20403546500041c1107290710a40030301c00358000006c0c00002c500b8007184c1062090089d440e80c4113110140f03c000304618140040302c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 909492517 1250 909491267 909491281
    0x31009060803070c0506181008060307151205041e05010b19051f090b0a110f120d0e1f0c030b0103150905040f08042303120d021308030c0c09010e 64
    0x780e40b4117407202141c40c10b46541d403907280000300688124200e1380c030140c1c9045d00100a40c2100c2224020344096081d070f9400d170740b03d85a2102e0090404415000202044d401d199100401d50003c1c0c2c029120791851038000d05407038032002c1c0110348440180d071165500c68807581075140c014001035500c1d8126a0f180c0c001c0d45040005079161088070b000d078144081e60041e509042d0303c9882c5080140c01c04000d00340d191511403100408801c102c0c0c01a540324070034441407205080740080d20300380010f80000e1062901145150340d802500d010b54030201603126640c00450a1b0f0f404015032600c2c03850300d010005540443d480c0c01000d65a54842c0a41410b01d49101d246456500343e1341c2005171001000b0211f491b49170340c40d11a108160b0340401826100700400e000c40c00411401c01c001c140c0d00c109400703101742e0b0007031810180c03620790821107108a440108403070740071030082d0b401420000c0c119140c00018103076a03040ca80c3c1503500214003802150442d4400080a1829907262030250010b40110011458000307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 909493767 1250 909492517 909492533
    0xb010f06111501031e12030605130605060a050d14280605010212070812041b090e0601030b1504050903030105100e0303122205010515040b1f0c0803100906080307 71
    0x300015040740c05171414110f024400000c03107203466500c40e0690250340c080c101e0040080c0701d540541c034861561024088a28140c83c005c02c030075108010100d52400310383e4002650113600c0040400c1500351a005107500c40c801060f0303110f100d800c004d42403104910302840a002c02c03d2440d00c0c40103110340b030404240090303640068401c8500b1402c19a503541e4820310704000c002da02943c40e440580c001c50008020411101703111061441c210b100303803150600d1f1268041801d40b04a500084003541c8440c0040020036140140a03800c00d01260fa001d0a140c486000710f4282d403800c07185000540e00000c010412070030402207864500c00e003498007001400c00c42c40080d45900c034160805a0fa000071201003000c84905003104240319600030700d001d00c0b4058038640540070385000c885000c0010104c002c05411070405004d0a842c40000410381c136403100c2403854200030100070000d1745040200e844d17075100006540600440c01120441c08065502c0e14141d81e180075544c4640003000a50070034004240011016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 909495017 1250 909493767 909493769
    0x47090f0a11090307090603022b110d0206030a050403081305070b09060c0d020d09051804151811090a0c0f0c0602090604090f0b0306011811070b010f06111501 69
    0x2036001144a405004100381180116014550f00d40203440c0002000c0c8840d45c41035080300e100351404802542c403001003a44014a00c148000c4c03d4401c0003c03d400543c003102c404001c02402030800c2141071268000c5803007a0022900e5400f031503903440501003030640006509a1201580c0c401d2100303e50b05959880c2c44144d0342c494600490000b003418042d50341c070501603c8440320410f0842c0e0040c2100c400c000e6a81401c100c01d080451380d0b102d00455503041c8040e0b100d0501c0301c050b0303081d4890345456a44148803084003094001182d0b0700c08103501200c0e400c1d070351040c030140141d22a03200800f1440400c444414080c19618900f807415019401070354006201c4950f024190800c640900310505140c0040e03c22010400d81c07081c0c001601103641007060f03200c0307002c410313207030504200040581c0c0070325030ba642080c014080c500403001248030700c5000da0703002904018081d6803da805c00d02c060b83d030341e0790001080c1c004101120203850107000f03140e4815a11a65008071000403d00882c150036069100a41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 909496267 1250 909495017 909495031
    0x503010b0f0f2107150e06040501230c0d11061e041104110301210c05132012090a021c030507050f01020309010f02040f0947090f 57
    0xc0110b505995607511024000c99140415000800494500d10b86880e00d0381402451780c01c2c2c00da80d0301a00322911881801b0403035000a44010f1400b4201001510581da600c400100b900c6802008460343d1402040941019111500100303004c102c6060003400107a40c810840380603900c01010012031074207403804503001400040f040300068403141010010241d680441c95003090070810005010345040b00118100d50405a41000b504e0148000e408000031013080900148422300042c8924604a0001d07a082201410002140c0500b41c1050080b40c4942d220000c0c1c0b4580400d1f20100105002c003110782c000a03001c090300c0c0080d181c2c5c0c0050000c01007103d02072286070300e8008020070540100300716200729800000b01c42d080d120502209010f03501c11621008254285440c04081d16a0381c001e840a0b02c0b0742c041020865403e1410745c10041009812200d0050700c06016191003151400200c0080c00654420010303c548041c082d40c2201c0c50035050364010603401042080d0720240012960300000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 909497517 1250 909496267 909496279
    0x11030f0f040c090e062502100b030c040e010b010305070507120e06360109032f0604030507090b18060f030f0708060a0c080f0411130204120c0503010b0f 67
    0x72107041202100116410500e020b41c6000156011028001111889840c01c141c1c454a00080d5049040310202071810981c00b59101281c40d90407402c02e07420641c086080034044030381c14810540010103441c1c2040001516964070341c480344181d41d050003215801400c130b041c071a07d803c104d603481040400c21400020200002540ca000482c3c1c0d503103003103411100b00c941c087c6005801a100000150710111000005041c641c0c1082d00d25501a901d81030450303800c0800d1042d01c032281c42c07241d1002d041e103481c0f000f05c40b455201c440c1115a40e5402902c0514002d000070700c019800c085004044488403404217109161207003070300c018918181c6115a01c44d10a490038070b200c41c0031002084c94001e40b81000d1015015500000c42d5401380000c0c502d118480c401807e014103404040155219030b8140d40341880d00501900080115883d000840580c240184c40b8000c800d524101c1001241c0058001401c4030300074041c1c2c0300c10b100e08810628040c2c0340850003040400c20300800940411054420280100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 909498767 1250 909497517 909497521
    0xa0b060f0304080d0e010209040507030b1305040c05030a210201090c120611030a0b0f09072f0102040f2d17030f0a02030a120b0f0d050c10050d11030f0f 67
    0x4050f41007950000090041c080c020002100402c0e4080e40101c8a580d000b246408002510303030384240540705088001070a1211504017186464000e854020003c1e0760810644200056a40f01040240b84060050030100340144000c030f0348103c48a00100783c9811a81003001c0c03040494609140c9030110740c900b500012856845243c25005401142ca4906c03800b000402005030070f01840c2c00007040c1d95812a400e1a0611608081100244007540c5040c00240c0b010f6414516854072221850800101441d802c403a40110035280e0a80c0c1c0316130094041e0031802c110070081e4502c45240c0c8020429042400943c00040146400a4400c507100b00c2e0a0320030650440c003181c09051080710560304c1c0c658281540c8640a01c4040d42e283e029540c0003000541c0c00030380d601d400c400d0780b240301a40035004210100f11a0341300204004000180803c2d602030140da050380c10740c0d58600c100112141d030280c4685490b0b203800b0282030110b0f54045500304200e10704000700079440c001e804145510028441c0820416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 909500017 1250 909498767 909498773
    0x41a09100f0e0103051c0309050d0806010e06032401110109051c05030403080a3204020114030405060f0c0919030b011a0d0f14071e1b020405060f0d030c05060a0b060f0304 75
    0x8e4940715a020b841c42c020002d401c0702c0b256002c40014820002070300c6001780440d072602840319030301c001c44418045440c40030303041c60100e81c40c007104020700b0030514211102c2d030008072400d03086488950b412180c44d0301c03450a051400c04841c0d000042101541821410740c0707400e403130261030718000610407134915030b4515001003540c0204051840c00303407407032020007074040c0c54016504480006850580c00300c0c0c4450a240b1600c0100c90480344a6603210740602119203489941115005014001c1070007450107000f8500e82d500c4000440914291550700f1070542e80c40d6080100f44614103070040c0b0654041e4a940c6c1c040034140c0c3c42129162540c5600c000789200c0c0700c15400e401000e685d0140b0712004020824480c0c101d5004280070114059219a41c41d10446030209403800c01c0004100b0040076120031000000d13150903405198031050203080c003165000c200c40051038040d0790035401c5020030a1a4284014001c0c00c0040650000c00e29408004085418001950030300480e0310401d03c03424000000f40030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 909501267 1250 909500017 909500021
    0x1d07080a09150204080105060f0a03031409060403020d03020a12031b050c010f06270b13050603010e0d11070e0c120405031926010b0405041a09100f0e0103051c03 71
    0x8800d2040d50b04640b605d44819015020307200a44015210f2041c0d40c0c2804007601e8500c1da424100c13641525440700c1e031500d43e2001e4500e600468031040c0d03c20010300002015807a08030700e420120344a5030107042c1c00f00c22883d10b43c1007050b00420304410540360103502c82c02c2c240400300410214420341803a030f44448045106902620345818042190350800c4400200103020003203000c105482d610b0032191031036034205c1d06401c07500381300c0d2142c1d84048407001e01200703c00d16a000c00d0700910041d0001c15121034901d0350780c0c58940e11925000000d0079040c0d4094000b0024841400a031141d82c0e0214450304004074100001d008020140200b40061004102040010000c4401682801c5001e4184441d1850b015000300c500e0440d0400803c90000a0140c90716604400350680d03202d0b248003402c0c50b06100c2440001c00b9503140704e40c0102ca420028000e1944c40c40c4400d4812041d07010101481401c140148161940d06d0784520302e02415000107200041c030104103500b14102c44105845022030350003007100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 909502517 1250 909501267 909501293
    0x5060a110d1407020609120a05070203031905040f1d1b0705070807051005090a170f060415060b0307050708070606050913050106051c080c0109080409061d07080a09 72
    0x141c0c2c07420900140c0602240c40380c1d88900e00395025546169649141c0b142c442c10b40c00b2940d00d0440e8204032004c2041d0203403020f88080d034000707012a030603c0d00e2120030407a03043c40c02200e100800c0000c2000c004001c00e405020001e000c84940b145a01e0030301d550020b40e1100f001d091010105844690702810b06816010380300d0039908002101c5081c0d0b40c1c2d804c015141c02140c000e00f4000c1c03444034810303001d040c00340b0100d03003500b5006071403400c1c910b15011070000101c1303080420301400c0c040c501000c0c030907260803ca0340d0700643c01242d83c202111140500301017100c410b81d0108010300020301c00c001b441504502907814181e002105c1a55583c800d1801800800742034205550140026040c400d204d1040c900f6041c105218030000c201058480c1d041000100072019070504d0040c0316180000001c2d1340300c018050407041d050001c5880360680c0c0d81d8805c5600117400c1922000d0b44c030001080328401501079120031040301900c4140134101310340018900c00004000d561140c0c3c80303980d00002c115503803240030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 909503767 1250 909502517 909502537
    0x51b040326040303090905150f120f1e07090c12200403050105060406140310020c0102090a120b0105010e01171e09030d0516020604120c050312160c05060a11 69
    0x9690b850726860041c060385800d00039034445600c1d1000058910030420214282c2c00001006000d480d6800c804001d144d81c48002c081c0094068150400c1e04007000300514400e03039415903071142c80c045508404503d0030031160b00c4218a1410611501660754110181c0c0f031501040d8403001c0b8a00940102e55000c07001d0451915200b1348001600200740300d8103610a5000340390499080c00f44580d1100d0078030301c9644d00e0032102d81c07603008a0351640300204076500508000181300e0025050107040c0300068108921380c0d01c031005019105010504000455020078007401303090801c49012090f000001745894102141c9151911020012808080d00505052181544002060010f181180c801038494000f185004040d07030400c4007145041100f10b800901c145050b80c020420f9656540b150128402120100b1f014040d0881e00718002c41c13005e01c001c1003403049110382d030700c018240000b00200014950002c1010803130340c3e910b07070400684003048082c2c21071a100d2001c0f0300c02d140c81d0149034091291035496 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 909505017 1250 909503767 909503843
    0x705030703080604050a0c0e0f120a0b0103031205090a020402090d02030a0819090b0904022d0301061e0207030b1b1201052107030b100e090c04051b0403 67
    0x11604041e8002030740c2d03100300015241400207445445490050b18036050392403003c540e41e48501e4800381481d072500d0300b110000900211025644d0f0074518241807540c14107503221668040140149500624030648442115000300118a08850015183e46030020300030310a40d0001007448003541d0f880b03031a408030390300142680d007034100d07502e0300e0801c13548000706021514404e511911182c50103201c0480c00c803104040001c0c60002d680040100a40c001c1510455110001c82c51881e5101002c0710580014400300025580354103001014165110340380310844144105504071030415400b15094046907807111100070b89886088150644840c0e00f904909035003008506021804e83c51b4030500d048076030079202d00b450a5801000031045001e4003032400c0c1c0ca07a02c104c004200207034082100c4c542c8804010004103000f1f4a5a1501550000c1641e005540307611a038002e106078a41031083c02d13004203c0d4071b44250b1083c0081c90059041c081d42c070000c0c2005070110802d000c20603030303c00784d800403103c02815 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 909506267 1250 909505017 909505027
    0x111011010c200a0305031b07080a0f1b050c12280c060f0c17070f061b0216140a0b0415080703110f0319050a0603050c0a03110607030302070503 63
    0x4001d268102407070007407050403052041402c407003101044500d11a9055a80d0500d56550400e8041044945a050001c840307401c00c01240882da1103006451401403030b86e603d41106007201402400d201c1d908952444000111070031200003000002c28100094050b184038101200d900455414400b9070b51540ca0401d000030074203808240c01801003804203110701c00d803aa001c1d4a030003040300c40c50031202000000c21074011040011840c24a5922105080610840c0c41e0120725950304001040c081c03411178034036444d1103002c001201180c22440103103a8a10007009039a0b8003d029091110341403140e20103281040d20081507644543e40c101011302004400d06c1d50b01da6031140b68800d558a030002e07482c0080d00290105150300d00ca4000d540b07c150000c49000d051500c5030125008941c809040201c2183d035990614210100d0340c016075100e40c03803980740048c113145107003095801c00310342603015885031610117024400120542240046003c6c107581150303c4100d1803134103400a124040340940036101c00b01d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 909507517 1250 909506267 909506291
    0x311040b10111203010b2205031005010815061c03180324021602130f0f02031602013b010905100f1e0f1805030304020f0a0311101101 59
    0x2c0b2840e4452180c2049810340f0340441c4440f00b140c002030140d481403074001c103e40c02c3c8540b84003002c41c150695220b8201082a0b80342d001a01d880014521071070425107a0004206852091004040755900942038039001d14050001407a0224104081c0d800c9018219003c1c050611078050249521103c810842145880782445220840c008686c181494200c0c0d60b40c901c282268000c1d140d01000119500c0004c8806900708001e603081d1a00c1945a035680e0034413401002080e028040003101c510900507502c1c100040c0e030342000781c150540e00f819a130500401d240000d90b80039400e40c5a04960001c00010144800744444404068000000035824040d207101405400314102041d000e0718030040007817514034009103054681d07115400100d800c3c0218a0400c0304410341040e4440003144500203031603020480c01c3c28041c603080030240d03066031001c170800086080c116004110000104c1d040d000191541c5d0b501c0e8407100170085131a025032280c1042d0708000703002c1c0c90680c246080141c001c0c455105408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 909508767 1250 909507517 909507527
    0xc1908010204240207290d0c03060608060d02060304020f01091205010c23190905120105040b07080c0d0b031219020d05040b0922140f0901150311040b10 67
    0x1103c1c0303030014440740409030100da0001410200f25007805030911500d0b0303070405400410502c4801b4110403407000700001002020380b803082c8d106500c42c0d030700c00092403030810310010302c041c000509550042040782c1c4800c02584e00c1000b500c1d4040e078100c400d01c05010000004a4400205520000e11000520041001c03c001900504400386d041d0703a0301d0b80560046880307420041105c24036812007020401203000d03001040f6182d003c00042506101840c02d0303440e170100301003416005c01c034020760359140180420049013a41d4640c020b401490303c24024280309020910b24801c03242000441a6910f9084015450902c0000c0d264180c0c3d00c0b807140ca44245c9504030011450f14404080180516071750203c6d2035000d80e040d41c06982c010710000d801d10321010140301c5007503810408200c0400300719050403070385c603410702404680c0c03402410460703040d00b00f00c03a603070307644c08409000d11010b0307410321b40e50100b003a181c600c04400312030308802480140b25030900864001d100b4080300c19000002d56081c00710f0b0507000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 909510017 1250 909508767 909508799
    0x112060b04020c160e130b16030902091006030608010e1f2d05061e0f01090801061d01080d05031b07020d20030312070c030212120103150207050c1908010204 69
    0x84021455140c0d80c5548240224135041b0000b88a4401800418248078042c0c0c180000c0510500b00000c4240c0e4503000103001c1e40044484040300a034002c81480f0a80d03042c06143d000340683d100a2011303010358075250761500c0411000d45010341e901e642d41d88136044284c03c5004080051403034555401c2a04100707046002010f00c1c079484103428032001c0703082d9040c8000948030043c00d6481036021a2204400c0100320072010024030704001589a020946102c00c2c45240d008080044075418049420030700c14000e42c405a20042c0c154101c00c51100c10b080c3c2007401c6980c080b14440d0b0a0070740380c00350658000c02e03025004019400c0180c0b0b0200004118500c003007014007602115082088001c8081010f50364414010013841009115010445140c021b05d001100544a030065888440c199140c030201d80e0090140081c001060705e004100b4050304204181c2d001a4964041d07203010480d4544507075800041541d103004140d100e11000546811607640809480c0000007596210b960340c031030308907030045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 909511267 1250 909510017 909510029
    0xe0d0f1b08130819260c0328020a0303020a2c010320090f0d0206180906180f0403110a03021b0405100909030e040629030112060b04020c16 61
    0x110307080c04034402000007103160300034411880900c405040da40d034911001d8401400705d81d06029096461950400c40c4015000031101c00e0025612284000c555503400364503803a0010a62001005041c1c55641c0422140000d07501414050382d6501d01c00001c448400301440358040e03400390079501d06410f03101e2074082d0350f603204240d078140f00710072071171000e00c1c03250440703c071242c0c0144000c0044000604003141503540284004002a150002580102e800303603102c424665100d0707101820f003504c2850040324407900320405841c15004461221852026030a0260003808101c08420004041500c161244a141107143d011f680155117a80350296841007a4000e0b400c401c2520020140a82001c0c0700d0a4807480c084030300400d8440c541500d0368001d114030341080d8100040c0400c440d0b030a450b40d00444000b03101c089031609820101803001060311103d04400b041290080004200d41902c090000d6803030b50700603000080640d41d20300050001d11503c0245822809000420349a031074507010084103c401e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 909512517 1250 909511267 909511297
    0x20a050918010b09070f080c040b03040c03030306080c09071d0316060801120b0105060304031e0504060e09091e1608010b1302090904030c111e0a05040e0d0f1b08 71
    0x2a420081013071605080300c800c0d0000c0ea00d408550a103502c0344d64803d400c0000452810b1a0503142d440000c5030f6481100c0a031086440c0040404c10580d0500c154401808600c0151070707015141c5001030740041c405005e41c1b080001041d00000018040080704070404001001c403001030120746e0520300c3e10712592142c0c03808140641c00000350489211039460544d680817071015041e81c24641003248580000d0b205400300002229a91052011540000000c03103058460030784840c60004d005001d0030b0b003403c0d81400b40c0184c0d0705204009a000529400200c03040c4022305000c0c00920203185083d845a25600c5c0d000c000403800500e2100646c801403083d802640c140c102c12120b0f51f001c5040e442614144e40c1c000d2200300002d008030b03216010482d030356072103a08001101d03800c640008207800281031490703608011641e45081c0a00d030500f2284c0050005440a00c1320000720316640d07460710840b8803042c00f40a0340720503407070156204140300c0c141485841040e40100d825820038004c95000f400c00c4400d030407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 909513767 1250 909512517 909512531
    0x306040e01021612182603040f030f231e25060801050d0b06040903030f050405011a040e03030c0a052a0106060509060d200d090501110a0c03050304020a05091801 71
    0x950303001917000351502541c00241d1021100070721a0618503840c0210000c1c00103000115544141c42950002140241d80301010700781541022030401c501890340d40003101c0091089060010040342100fa03e54405070000005010308900da410441d8130a0000c2643d03004404041924211b4580081a9111030b0b840301e5642e030300c031014020000803000001c1c004c066507200203a054a4a900200b44041c401e1801081c0d40300e0483e403100540728151002c4506035104c40444114840300043d0140c1070800703c506000381c2105201c025240c0c4400303455044c01501c00100324079030358042c0007121001d01484420509444c20080085003160b81d460301401154200680050450b00c540191021000000e00461030240c051034100018a2513500325aa001082040303044900045006800b45010403900810302c1c0b00a403416500310342041e00e414084071010302100c15807075800101700c40321a40c181401c075601c0d2140e000250b0f05400d00d51045502c68000020004001e41c6040503060100f04180240300300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 909515017 1250 909513767 909513797
    0x90f04111b10180b1501180e0f07090617060d02090108030c010f06051005070c080601090b0315010e010501110f0a1101120603030806040207060e0a0c030201020d0806060306040e01021612 82
    0x9461110f40a44130040c1d000202c1da5170b000400c030415890f901414540745d12058480316244110703080d8400103150280004002c0b44a06039020715510100514255404038104400900b0383d002502e06407e50680040024021b134580c510501d40140d0024100c0701c0075a55580040e03a6a071001c2d40041441d402c111204440748414040e58040e24030061001c0c040c803000785021201030700300c50000e943c022602180010301284c00c0c400709002e41402d11010070304400280034903181c6119241e2903415214144c00400c03860880c1148141951000d02e4903000d03210140504130f01d0691406587c0750103000b051441e0080001e910303503061000c030b401c1c1ca94044004541d000b850031170b86035100c003502055415000802a1400e60700a100c200d110b52800617070380080004803854103c40180880d01c06104041c140306561b010811145418400c1c50800c0e010f21f82a00420318030700010705690f00442c1c0310501030b00c41050171340648100c03900401122131403c603642042d11240703882c503500c0340105440d00503075a10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 909516267 1250 909515017 909515051
    0x71a13240e03030a0302251101200d0804050304080714012a14012409050f160c060605030d17180a1e0203060f04060b06090f04111b10 59
    0x2070301c440100910304100c0c0580d4158007070f6004a001d4503455501703078140f5100c0c103103160081c5104e0380202c040758060300f01e540025000c210f40801c02c040d8850164204e94200038001690507290340c080c5802c55071921140b81603841c44c003c40d08003d0307030390042140114600c241d016071740078201404d9840310f440054a94400d0484031040030141100100b903849100402c0d581f1641201804903900001390144a003101449100c801c00d4900c0d4080c041071004004c910818001d154000c071903946511528103180017040c00c1c2a00c1d0300195000d00441d00143c005100b402d5010310014400942640d01c900c204000040207610302c81c41501001e2011400f0600c0607002c06540320342018000002d002000c41522140aa2103100704030055041d03076041c0f9000143c90501c0303d203004450a04144c01641410724100e020b451842550b940505424000c040b495510080350f950442c2e015200040c041500c0810329240d80b140580c0154144108550001c15181c002001d60038005196810044107441030100740b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 909517517 1250 909516267 909516287
    0x109030203030910051b0c030f010509060f060103110d0b1306060f0c02041508060412081905071e091a040509010b0a0c120306150908071a1324 63
    0x905a8003d100f02525030a001c80854903000075410054280380d0744c10030915050502c0760b00382c0f855030400220164241010800c0707041c07422210000384054940254059500c1d0700003402c02c06010501d41c0407840590281e072250080156280c0d500d07540e044800e4400c030150400341000760141ca10880076509101c040e11070001a07458a40c2c502954200b504012503800c0007144043c0c1c0d01a40d01c01c04005118990140c04008224150141c03000e031800d42421342c0743c03030820700303048040c030602104005003109911401400e100c68131340000f0781525142d40c01c5400c5201644c41100784011171841070110ba4101710040104c1d944d06190321080e41e01841000e0b024000c0f84245c8da0040d201e00014410780c000b80028040c1201c0500d000c4480c49065151046141d01c00b002c9000031950315042407001000c071803082c082a410904154650a1a01050658401a031310455040d640c0c07000c019200030361040c04071200e10f640032000740074207500e039002c003805200b00c00301c40001c0c4011062002450b60190159030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 909518767 1250 909517517 909517519
    0x6170f06040503091201020d060807061d09010b2d031914010311130c05091302030f0f2223060403050a08062b0308090109020a051005070c17070501090302 68
    0x11300308502d0105000c4005d840109488840d50240b00081401041e8820140141284001401401d03d0320401400080004040e401d00d14132a1040c3e01850311980141e504482a14010541e41c101103524010110b419402002181c03c8560a40041800c0200650701514403071f01e03031001d001c411000300d90880e10114002084402034000401c04034070f081c20003c032440c0018100002c441549071180b003c0741c01e02d4040360f02250000c2410030f41800e0490135844d008520007801c5146040203020b002d40c2180084c10104100700100000706450000c0b0444001412000c80c05a40c1c2e03410780c600000070b00354220985c605000c03920450400b0f19400128240903a4040e15039520b82034011104689080d00202025000b51900c02400000f00450061007900c4e90100002d2121446502c3c0081900d140904150002c2e070414450701c001d65201c4448008403102140c0782c840d01c03c00d070350003964540a200303809440401c1c6500000b813400c4008030f0f0801d00800040c161900503854100540d051401f6000c06 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 909520017 1250 909518767 909518773
    0x5090c03011d061506130f080c10050d0e10061d060f0d151404030c050d05030712050603120a0207170a03140c07170a030e06030408030402010c080c0106170f060405 72
    0x894285070802081d0005100007402152406c4480d103040340c100c1a0325441030034800411007041041c180140206400c0707583c100c0c0c00e00d034080249600104540600c920300c14240e55104580c15442504116180030b02c02c050405000c41380d03991292820108121005922100741c2c0303400100301d8a0120032210789140000c1807030000c012143c031100510315001c0203074400c107940d44014002c58003001c03603807502c514841d035101c220b1040c035407038401c0c00d16444481500c00e124052080c011142d41100e8401f04401d103030400010075a45400000c1d240086181a030b49582ca00062089405035001c11520301340d0304881e906608001c0340c10760b07255403a034101c580a400100a81c031103800c6901c6200090a0022203070080341c1c0743c0398543c8050807420940c403400c00d80710b60160000c10704043d006203045580c43c0c0116100c81c01c600e01900d400c12a480024002030410080c0f0000400704909041500c0041458000070041142c480c040c4140f24039110306070101c0c510601c0c0001e100000c4c00208030f486180c2c80406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 909521267 1250 909520017 909520021
    0xa14010e09070c1209030c0f0323030a0f03060902040b12151008130c0e01140405010810020a18080307030e0904030e1e0414100b040e070c0c0905090c03011d06 70
    0xa02400004c42c0c00240200000b10f040003022415040e0940d020700f0340c0040c100307601031035440d1180549016150010f10f40310f8940070501401004000d4400c22036150070056200700c8402c83c120014602500300c41e00051000c5004a81c039041304006d03000264805802c0ba04607100d0782c000000c88051681840d0340032480350a0700e00007900c42c2695a4001084079030b110300581c0265989840c0b124160800002c1903030202c01084010524201060f200c0390540d8108015410040142d8491180c0d07200e42c810b4903000030307511001c80d01c10701890b420020780d400b1a002542c0c40c0e06840c2e8aa500ca160190f0018013600c00341583c600d4046000ea01903540741d2034090080140c82c1c140440201080c00740b208150b1049051009034941c1c0c012f0115001c5404890800d0746440d4412250703041c130036000044c17920743c2840140b10031002d0b06106500302c8500d05042404501f41d01d0f00103082089600225001c60411040c400751100000c2c000201c641d0440c001d200003c4503000c151700d060440d0b51002601d501c6400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 909522517 1250 909521267 909521273
    0x10b0a08070618050405070201050601030f1107020603151309050709140a153b04021e22090c06110705090405030c060106021c020a080406120b0a14010e09070c 70
    0x30f64102c03a1000382c50b18500503540c500150032580100d5540000d44d44480800c20250ba051107031101c0d401403400b082107051b030141c0c5c8803e102e000b502c40003402804008040303174100424201d01c0b91f143c840103020f5481d070982c281c5008058051800b04030703554410610017080c1040315002c1d40a0800d0304c4640d003030b03c41c1c2c0c0c1e000042014100400c0055020320401e100803c60120f04554485c0380c03c101c9040e1045a040007184060b010b0354101001d60020400080c0801a681c03d07190283e0354000702c10720021018410f000400c50389110340340c0b10581070a04044001c00c8030540242c1c415502411079400643d5841d14284c50103200305060800c65001140103008603c1d0500a46070058058001c50b41003c3c6029480352400100382c00c01ea000da8800c0c104850303011080090754540300b26501c05402030014035031f140303604ca000d580540414840740301501441195a5400080c40c64001043c0b040000c0d07881401d030306400040b40080c5d000544d40c00030070090f070401e039520b2400380c01513558030b2940356403c0e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 909523767 1250 909522517 909522527
    0x20703061a0906101206060306051203033d030b0106110c06430506280c020c100806010f110606010f05130f0e0f07140c031e040305010b0a080706 64
    0x1140c80c6007400035030806503217004a60f21038140908500e40780001d405041108019503205060303400b200340d80c000c008110b46d5550719003154075001c1000042c1e8803000040d0322801c80d44008111481c41c0c00440c50f10000610142c020322904032020b5803540000320744803039051a2600c150040ea81c1d00003008100b0180484050112804c01000d1010504100788221802c000f401c8520a05400d100740c1c00308a08040c80780c2801015000564038811445109190407512860178440983e03c1c40f040c0c1d2640d40000c91030083c041d0205d800703c02440c1903009540602d025005400a407511800108069540400280244060103400b0034036401052240d480c1c03001100e54110307150011040100904c610b800b03010155803084003402841c012040c201d410003030488c111500c01480ba4046420083c14842541d80001a4044015004502c150b45044411003d4914403600381c142045c0a624102401c4550103180603105803440f400003482004518010803076000420b0042d2009030304624020080b440c020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 909525017 1250 909523767 909523789
    0x80d0b0a06031b120e0708030909060319060c03060e0a06150c03140d0b0a030b070e180a0c0e0a0801051f080304120501090b0a020a0e090702030a0315030b07020703061a0906 76
    0x580340841d003060704903090b0b401e0180c941d07c4409a54030219141c1c4403403408400041c1e01140c144e00400650306120aa40c41c07400d0003400203021240d03035500d042e00d081e110f60800c002422903205a400a401d214500303070000d101e18880c02d04003021800c2002a0b05101c0c922480d1120381550f40e49a004420301c1841500c0d501c12464803910a80d5407003a000e141e1500d51362840194001d00002380c1ca46010368014003c0202c00c0111485000e114081c02c5104c0a042c810300e401803210072340000c0d81140c00c14191049c0000c0700300d00e0390222200324001213000054000c81d10404000c040201d25041c00c54601460241500a10080360002c4c40140001c07440c2c20f005a8500d03000320000300f45a0481c0c0c40c2c090518500342c2c2c010309081d4000481502d03154000303007001c0c44550705540c68030b054034003100e0080d124000e0601d1326040540340e0100c0b00009500a19000203540c1113440d0450f03038204000003030350301c1446100485041e0f04000066082c15100010400d00c0d400140020145950b48003c00c00c6104030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 909526267 1250 909525017 909525047
    0x607020112090507080313061e03020903070e09072408060d150f06061b08041e1a030108061e0106081801050c181e01030506030307080d0b0a06031b 65
    0x240b46094404280100302a40044c0715803c041c69036800c51402c02828040c4a8001e07206014403250b4440110140d00400303040c20303c45240060700d8032460030010341001c0f0301d82d0000b0100e600c80c10a0003012000450074104a8500790401440303010425000341108142c0b200260115216a0001c1d00c0345c140701e41e0b0b10707031887d201c3d282c600002c0c0500d80c3c0500131600001d2202c0744450343d640c1e00740566034000300c036201d05582c2c00900c1025442c079036803650980c0c07241c0d0195904030070442000c018411124a040d0020304200c0c1c521034028201a001540d2640091080790214803495000c110306000781c40d0300d00c0e0070b8910034140285581c00d00900b6100c84002420036121500814001c04140b038083c42050b000301f000450a0b80d9407014a017030542c4103044155044d225040f1407060700040c00700f440580f500f1030001e0030003090903a00c103030011b0b0650080f05e40c090141ca81c00a0301d0310301c52031164030209441c3e5085449104582e2211030031021034450015260030490361032005199680a04212a45041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 909527517 1250 909526267 909526271
    0x60203040801600306050108150c0a02030405041d160e071d1915020d0206240306130201120c0509040f02040801110702042a110a0b01120c0e01050607020112 69
    0x1c900703d02401601000c40e02002140410081072040100b076010300c90060400350020f2614281e151110600d41b10081c1507800d8541c800540d2000281c020700c01e8500800d0000c008010a00c56403100c00980e200700198100d15000d1815083c1c44030040095080a0341d585882155055580703250641d070407803009003103041400070b00350801c6149d41c440145022000c0e00c403101e8003d05160416009200f81d4030151b4a06541080c1c0c8256650380d80010700a030300c5203094030810200005010840c640391000741c1000c1d014020b510030400720407030341e18246401e54402c0e65103800042150b141641210303e042c500f0400508104a150140e14042e0060000784149403001860705070b960740301d5401c50b501c1c41c0455400c0000810a1030951816100301c3c5029001c40480902000340184c081d5480c0d03408614100a020030b4080c14494504200b218502e01c5504c004040c0711540c5401c4884580c46600600316070040c210742010600d00078019030a8120340d00034003010b04020b0103a005413076007400081c00355100b80d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 909528767 1250 909527517 909527651
    0x50c0714060706020d0e010f11090f0f10050a020607021b042d0c031b0206010b03070c300306060e120a0503031e071103030105040e16060203040801 65
    0xe150348020310100885d0440094483c0400b10184c0c00e4440c16040e11400c503190103a06000d4003054011201400c108891a4507071541d1140003078154001d50a6058012141882c0c03d21450380080c0140340b0721030a0b4007180d03040c2c1d44210040742e50342008034002d203598804140035105410030fa0000810308a511021070201001000ca10800c2981d508811022548801c010180f80c0d4052007064039007400800c3e580b100c1c08081034080d681e000184200d0b60002e0001000500c0c440c400c0c9101c170b00b0640c3c8011041e641c090211504400024640d001b00400c50f00544010491030080c401c010407141c0d035032640e18410b4842001c005d4940e4460040c80128044d0004040010b0000c1c8011440f91210411150b0a10704030b14200f0801200107080400b809450a85030300789800000907039044500498000c074800320480b00060500d0008010350702508201c400100d042c94011028005540d04240200000044c1d1b028005000c852078407401c01102d50401d44811480c03442805440b00200034903503030220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 909530017 1250 909528767 909528773
    0x110610230d030323010b07020111030d0603050714030f120318060108030a08060901030506010902070c0e150405090d0507140a080d0b09070f020624060406030912050c07140607 77
    0xd100c1c159030880c0020750303d044a4002800701c4080c48003464086220300039560501e05095818460178102905110301403809441c2c0301030800855020360148941880840d40ea46801c84ea41c646a000d4241e8604072100010607034180003c0e615a41e0002c80028150300948205081c05684050000301008a110028481d0703040c040061900800d0300000450340c400540000070001d89002d0010341c8a00c0307880c401003010640c001101d07419100040030050381c4035840d00e0003401c0b0520700e5010003844803002d81004100c116007100c44e4584001a14240102e680700741c1d81e2612002100d04440205a09001070340c0030641300b0b2540312a03d1800800c5030381d10040c80d02c40c54000e0700000140506141c40304640c41039818400c1226400c4905030a04101e040309004000c0d4403800c0c02040101085400344840940100e150722002c0e801e01c018003010307516610303800d000740681000103068481603191200c0c010324620482c01c0726170300014800900701d9103003007c0d01d020403403c00045496002070107003c90004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 909531267 1250 909530017 909530029
    0xf0f02060c030408060108060901061211010318030509120609070e061206131208070c0b060d080c1005061f0f02030408120d0c0207060504090f020d110a11061023 71
    0x1900054004004662610540514001d03004001d1015070741407410411040324018041116035503c0dc401c2031030810303c0070041300180700c403100c40540480720400d00303030034103401c078008001c958016103913900e5001e460701800e6134440044d51240343e294400c01c020003030300d07240304180c1d900144001d185515213100c0b0a04580790213410b80d011046030128500750340c200700103204018440d104904180131246803003107020b8501c000000780a429a200c8000181641d942c044400b09401d80c03140f0310b191201002400c10341c1d1029403024101c449480c0001042c0280307050448a111030111405c4004100d034488822134081e68001281400d6200a1102245044d41801080221081030b000ba503201c50b0640e01401c240c074400140c06042d504603002c1800b01681c801c007205d007602d1011b240820001d252482d044028070481c0b10f40c3e1103c83c030b0724059001c901854801032074541041d5881c6041c00340b510500340d4440105584110103424580e50030480c18654075005221248030284da81c0c0b100244a012643d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 909532374 1107 909531267 909531269
    0x708060d0503120109060617010e01270e0a0308010b092421011d090c130912120c020a0201170912160b010b070f0f02060c0304 56
    0x100307001d010012a00350500800e0502103e40e51050400014000350040400281d039494041501180160066050b5003900071050b110703910302007442400940070581da408545001403001c02c100b14520400c0d5481c21108068480410a441c00a25200c0140c02414054006108404090310780020f182009946000414401f43c000321001400707000e902010b4042c4006000003040203801e50742c000741241c4205020000e820b5a180404010b44000c0714032268992105400d079000d80f0788445105503400010000042046558513482421400c000d004404602003501c844040c583c2072150002140003032001d00400781c1190300083c13540a402000e00c03080080c44010461605083c440103250800200b001a070b1005942945011141c2910041c3c401034480400000e000e04002d0454102a510420502020311155500311620135221026170b0000401c1c000001380070400c0000340 = true := by decide +kernel

theorem cover : BRFrame.Cov 909352517 909532374 := by
  have h0 := BRFrame.cov_init 909352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 909352517 ≤ n) (h2 : n < 909532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
