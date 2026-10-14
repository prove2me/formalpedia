-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2695
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:28:16.053202+00:00
-- url     : https://prove2.me/submissions/a54d7ea9-8def-4688-ac3f-7d03948dd238

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 484532374 ≤ n < 484712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 484533624 1250 484532374 484532401
    0x306020d060f050d03020a060e0106081203040c05060c0c2407060605030d030902032113081b040e0307060f0e07030c0510030b150a022a010e040c1706030f060f 70
    0x43c08119440f8102e04203a5901030f5403182e120b84001c3c001901e640001d16139805c01e5101c8801420340a041d00e0004403940e1480c00c60364401c803000c41c0e85405603000890344c0d01f03010041d1095400100010f0009080700c00c10041645890312544004812003104003c2483c4a0307400380c42440d10a180c08a003442c10101054103014160320520101490008040c0141c3d40c009a00844050b11b40017581c0713504440c03240506113200b1103640c6548990b404100064111000880e0302c0c2200808074864290790082c0100004d0b1200031a07a0041d0b54030500040c00490308942c80312214002c40c1c0c030b00107008000d5079080703400c100d5243d20036030f03003201c4080c0200b04509182c50350f1955a61540307030412516030007400152168046018035880c2100100e11031030761600811500d20242d41c202c0c14014040c1d2042d18060110729124181800943c009026004604140c05140d50500503610741c07600b1452040b4014480038002008503034548a01060004000c005200141c001d0203072101c515201c0c500703039030128400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 484534874 1250 484533624 484533629
    0x504033309120e06040e0a0b0d08031b04032109170d02070f0b12131e02030c0307080c0f01051c290f09071107170115050d030e06040306020d060f 64
    0x34080f1915083c1c0316580c0daa001c46081d50402d24080c0800d03100ca043c0b11000780000310721250801154080c41c2c00740440407010718480c0e8000c12095903010241c0310703000140c3c05188801070602040c013038040484c2e829078000080f840034525002c0c40c4d007039503413184044c199001d02210031690055602c0c00d00c0c2d039506020050113000c002c4a9400e60f5860070151303d82c58801c40340b240c1141103103040852141d081ea0500c10000641100d40079400d12001c02a0001c072040d608400c038407030700c0381040301e038541e040c00701b081c500b210f4000001c3c000c403c0101c014084100030690b0318504222040241100d02c0c48040c0c60400c008201100001d03904055440244001800c5405003100400c01340c2e0b8164a59184c00004028400c02e079546104d0381c5030210290ba142c0313210080088035020f000070100382c100c000002a051100103000910154000e40705600304a070182c041c1a4000c1708074090180420300454080b49a503c0160056141580e00c3d1265000c070382005000c403607007540710340042103005200b0019101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 484536124 1250 484534874 484534877
    0x315010305060609010f05040b0315102c0f040e0105100803071104020f070f0b0603010507030c0e09040503040f09050105031011030a2007030e0907020c01050403330912 74
    0x1d181032020004110f13000c0c1040160400c0703541c0504070925441001602c0003130001c0c030041500c034108880003456a507a08002c090181119070039004215114500b951040c80100d1450099860507403140b2018841c440782c200c2c1c108560341e510116a84446c840c503541c42900038000500c81c100b4440f034841d03090142c2c2c880b446030390051012102049543c29085c1081000700c60059844407000400903041c00f8450006d40f00c54254174981b030501080400385881140202c00030030445d6a12001074080710500c1c01e611002410501040e0000d06002161a401c1809030040b41d041c0380d038483c94945c0c0032110380c020008072500d540040019040410040300d41c0c2101c1c8d403040c0a0048680031598031404020200da02c0c041c0c8816120f0542d424800300394090322054507805583c6d401e1340c100904040030942040340200503c03800110201d01c042440000c4010507540c141c40c02d0b1641d203c11205030b404c10048801c00c1c5400c0ca24441140c80b10810024000b66200041080d00080c28078044d84250301c80c0613030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 484537374 1250 484536124 484536131
    0x31101020606060307080a1d06060103060609080c0105163c15150513060f0506090d02010804051006180c110601120515042607080a050c010e060c03150103 68
    0x24190740303440c02d5a500482c146010340242e47ca007404000a4914118000075007003a00c003811508550208085120f5a02030300c091240b04ea40e018100c1d0f48a0f110720801240e0780001138082c03038540c4504020b100e0303901a400a019840040c0d140c804400c40c00f915100b503c000040c0003084101058080c29204010b41d9041138000d01454881210b80d40050040442c41c85c1e5865180409203030000194001c0c20002d0301e010600d19030f02480e000205218000c3c016101401e05000903207283c1942110700140703001d00040a0104540d0040da0800c0e40900100c40c180103d42480480742907911680005104e102c51440d0842d040c0c140c0b0900326030f1804140c00400107121090810b12000003069070455500001e10b41781e640c3d41c4e08055007441c0796515208144a000010300085c0080c852600200104558100728805440c0340e0300c070303c988101d140040200b4001d00c01e803103080b40604081c02640c8800301c0080f03055120100490f007416011290004261008001d201c204102c540d00c030075001e0400e09042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 484538624 1250 484537374 484537381
    0x121006050705060403212c070302030a030e2706040b040507021f060801060b03090f0d090e0a060e0f24030c0607030e120109030e1005030f0c041e0311010206 69
    0x2030319000001c1c000b07414002d048000c0ba601d00130315501010311b1a13035000d08004041c0f0046460850304180003025401000c00c03540d00329400008030702442203a500070001c0c005d03032015540c1510b04008103014244c0c000c6102c45040342d07a100c4c1c238440c0d10090003115242105498071104020494034154030301c5020741d291000304031416800040444000c0150040b8030808480040d0328030141049070824141542080750000c1e081140c0c0d07001e1030150f9610016a1300f44c0d0700c0e8240007a51200000340c2c0500060b1424000c00c050701000d00e1203600030449410209081d5225400c094000c0c00545075031129821103020030110782c1540a042445410045010303500f80050320009a880340c480d416075204000000c0d003102003501030b0fa203c0300030f607a014042100c00781140d83c086009059081040d0045201043c0812040c42d2003d01602086103680360541151502c12424408150040814034100320403c0701184007081d2080340031440109103032001d441030a500e001c11441c000359600301d06642c03140e01803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 484539874 1250 484538624 484538633
    0x1083106060521060403031a041505030705040e070b030c0d0926160b0a0b0406080a0311010c0507030e03011116060b0402040b0304020111280b0601080405030405010c171210060507 79
    0x13281c00c00d405207004901c000b0b010030003501d00e1703002040c40d1f5406403a0890b81600c808001e0281d0084807411800e44150300c2e40c42c8184000c0e04c417040c0c40c800254001150a010325040b00307000e1500150b50a031070b1404c180b8522241c1c0200e500482080c0c80c0b510340c0c3c010500e000001120390f8005180f852054a003032040d0080707642c00344003003070100605c1012010b001404040460f40845800b0340002d1042c440796a4602c0c0950301c0e0070031071a0940015480c102c000c640b00005018102c1000e4050b078415140002944044401d04511400c00d50701d0354031440d01305a80901c070400780a015206040702c0c0300f84034842c0382c00d40440340351241090150b8010f11041080d011400190390f0b0054080c2840c0d12441c007814805030030845000340b40303a5003070300d0b968009941d820b00352070f034248003071190700360001c40e4403483e0040d690900102c070b0013003080d0301c00c20042c00729510421b52407625610400404245080000382c660305500a060345412601c4024100080745003152a440c008044604000e071030102c07244c0340c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 484541124 1250 484539874 484539883
    0x3090302060c0a0c06050124020c15090d060f1508070e04030e060d050a02030f01060e030706030c020c120a020a0e100302101b0507050f060901083106060521 69
    0x404060482c0104011002600490354403010030781c0103d08015541c0c4420840e00b034004c40000942642e003c0b2100d600509000280512460314001d142a403403440d2134400d1050761340508042c0d03400c6840c0d200d20340006070700b9000d840d01810750fa14020461041407a418485240703036a0010f4025401044100410803ca41e80d05802540610300803d40f0000d010101e40c1c5031180070111040b044c030300010858450126405103000300300d12640d826a50366941c034104c505105041c036081d07250b040104100b03c002d003340d0010280e05551b00581d040c100d40a80003078200340040308507060f40d8000c3c240003000c5181c0025401c010309904100a1031904041c482500648a5408024000ea00c18201d07101c50a00440782e0070610355005844c4d000a0b0542c3c5441c81d10307985035124803806480c080b400810146404030035904105c4c0180c1d00d40005a81741c0000d0301d120030b07009107804812006a2044204081c00220700440c0d24014540442c070341c1d01e04018080307206213401c80d84010305801030901c0c40c0c0000220703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 484542374 1250 484541124 484541131
    0x60709360f0902090a0b13020403050303070e0a090603080909090d091401051306111c1d0a03050604050303010e100b09010509031e1b030609280203120301150309030206 74
    0x450004038101c904a54100928402201950100e202c0080040809040c0c025000c0b4000c1902d8052032191031707620190503401103005c0108a504140001840980305803d41c0c01070104c001c2100548951b40e40c6a00d044514a800c2690358540010b40004941850701c1102e030801c0340070008084032150b0f071030000d0080f1020b0081c50f0286070100a560b50b140c2c4584140c4101e04081041301c540b0035075522020f4190000780286c280113005031880c0d85900c0d240c04503281c1d5081901c1d103680b0b440000302c0041c0c5459401000b480c2c1c5d03208681c0180480401d10400045d07124500c40e0008650701d5050482401c2c650400070103804260034900c10a0040340b20520036130310300072028242103844076000d80009003001080781100e0b8500361081040510207000042020980e007040401e055003841346014151903110445010b0b46941c041410010890051001c010021203594060707500c075000b83d80024100f5541d44203010b494070002c00180489010758142845508030740c24100510000d90354081e4031480c2c002c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 484543624 1250 484542374 484542479
    0x503011d0d050708250201030b01020a11010e041107032a0201020c01120e06090705103e0102070c05010809030a080f0907081609050601050f030f0c0c060709 69
    0x1103000010040c042c002d4074090346681c8400040c00b18030344407440c0b03080c441d05e00590000f41004045001d030b50003c61030701c0420342c01c4805541728a1214005440f104094800c50741c100c0d0b551600c070419070102c000584041c078826501c0d2608950f6420100c09184003249013180b500d1400810f0b840140c1c1c002501004181023030800d06c80d0004000005001403420658041d4107014041c00c00c41e6480703010854100f42c80080361600401801054110341c60481880c00014914041080c07111962100c05040c680344280d00c042d88030f8185910140b03003640c002030401c039201004c0020500c602d40c1c0081c02c0d11ba01c0101040114204003411000030001c0c10050a00501ca03020340e00402d0000c6070500c5210080e2102e4012101480302da8010b21014072450b2042c03845e114a0000454895882901250200030024a402c1e0454503040b002298000002e085054170798010051052440418402e45114655507115140c1d44d80c80c0c52446646824444c3d020b20341c201c0068140c80504008452080100800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 484544874 1250 484543624 484543627
    0xf03060b0d02100210060f060e06160203032115091602070503190618051f020421060f0b180c0c010e06070f0e0f0609040917040503011d0d05 62
    0x10400070600d000307280507000c0d401480710140e080210340c00160201c2004a102000c012443d50b610f003502d10313112240204000070b038503c180e1484a28000c3c0c0503000c03001400862402d29001c541c00245035a015a58401540d03440b61008504800c43c034508640c461003030510310500280b203000180d92400010001c1114481c0c40c00001c0700e0510030072283c8041d10001c1c08a030841020f400c00502c001c401c01c0f504407521410000a61150307189250707590048c9922170024032403a00181c4817848079946151990051540c28400007620706c40029902041c44003030002400340803844c4c14140b094402402079510b0003410200a4070390303510740d94082c622840004107422403684500d452040640b244401d00b05543d0700f888d0320071002041c0410414000d85258460b8540b5a102c544151022001d4000c1168099298049280c0c5410400c0040030141801000020400302e42c5d03a03032016a4074050151841c402c0c02150911603400c0034441d0080d000c2c44002c10486952500d65400c0e603455000d141c61041040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 484546124 1250 484544874 484544891
    0x140106140f0403200a06030b1905010c0b0a020d020a201b1009090c020f15010b04030b06040e07061116080622120f091d070807120915150f0306 63
    0x10b11450351302d15503c00034115445160342d0b58004000d42941da80562041e4100040550b15840302c3d12403d00311101a112800031020640780d549400710021300204d01c00c0c1d003c0000040c803030752310f1008103507903e010344841e0001c01e0b0080c3e03504041c0c814000342c1103043e80052181200203d00003521042d0403011104035150303803661001250301e03044550041c1e03820760600200d06001500803554282c1641c0b4882101c1202c00e00340ea00b040c20040a10900c522620204401e101041c0512415684124090310129808a0001c4070310700d4441c80390f00820026041c60341c0d82d01d000b60244664462484001c0d41c0702002800e100b50681c841c00c0203820806001c00d00740708640451441915040d001c1e42010130040303c03031070134000504421540307224440000c211610109591606101e420301c04241c1c14581802599170100030381c1d540030050410300a0180312054400d403005603005d48010184200b0701c025121055100d103c0079622180424184a900080240240c124001d035001c100c0e0342042001c00c0f90310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 484547374 1250 484546124 484546163
    0x6170103060e2d06060604060807121d070602070b1c0e010b13151a091002120a020102040807050604050d030309060212090c090609150d15140106140f0403 68
    0x4440700ca040c05802100d26400f07501020031014442804070701000da544590300e850422141e407103180180f40204400d0f001040c2d941e4410b0b003050b5080b5441410010304580300c8265000c07208803101034011182d1240e803043c414141e060040a009120401e009404d0080b03d000789074040150070340003d0020b030340f03020124140030300350060031a1032400791960310490407a0161902914414041c94030550040d9000aa10314101000d218449415090603091142090400400c0040c507000300b01144a090b41e0880b88088a00090901070b6164000680d96854100802c0c01c206190380310034440c1500b40420011070321101c41c143c00d4654545400200585603150030f000900480c0c0b544031011030300d10b0070024000b8001404040b15042250000180d659180401605a40450b40d0800c08003043c080030485082440a2450395803284201c5514131998280c00411a084a042081c0b0013404800410449804c030080b008039001070f282c2c4c189001b8246a030392517180b0a5110040079070001000c00410742c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 484548624 1250 484547374 484547383
    0x2120114010308070605010e0c032206110a0e0a0620190807050613020f010e0105090306130201080a090c12080d060b1b0f0d0c080c010e1606170103060e 67
    0x420088110201541c59042040158119980440d42170385410008119402000101403040c0c41501b000c62a60745c0d9200040c0920b1202350b0348400000c0313043d00700c40001382180076000322030a40d100b030280c440c80170150040c451200158010300521074804d05100c250b9101503041e12000c003034813265100c440f4a9803114504401803001c41428039204940c14200200c0ca0014100e0304d010784101c66460f150f5180c2e50707c0c0e00b90711050096100c241540c0e01c0b100d03540101c41c5440344200504105042940340b8010034103110003200c3c44c004c006a4806540219a04113508640190000c8420028501c95545510b800c041074016110508440b0386c0060400406100322812458111824060581d94501048090b04400d52400500d0311000200400040c00140b19007422240303401030041c191446019542400c1c0705009a8840008010040c0840024010380700c1c215000802051344c0e060000401046a10325044201001101002d4501c3d9991484500c1e054a40000c0000341e40d066140c111840c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 484549874 1250 484548624 484548641
    0xb1e131e080a120e2b020a0b040501090b1e04020d0c03060f05101509090221040b07080f041110020708160801180203060c07060b0406080d021005010f03021201 70
    0x4007000a0340e2641030b9445080348034000030328407041c4180b0001c07010700f6444010b210a6403401300c10140e13041010080452011000f9101c41c016900306180646500780202c604450940d041c2c2c0d100c1d49000d0801c000800100d501a10403001d66910754444545480750010140020b8410074103900a8800d0014509104c0000d55002c030007005036164142c040e0001d44000c580d10700e4003039051000002d03c0ca180b0b200700c1c17800b4020345e5641060241003400c0c04009400020b50140d0243c46c0003006240c1040700e00c0041d0069000c2c442800a42c2341c004d0008242c3d03040180300218582c184824040000c0446402c00340c0400e0454860301000f400d040101e140c08080d90080505220303500310351100c40d045a064038181c64185000b8011481c1c50024001e1801450703800a400d43c1c01040000c250900c1d0801030036200303204072004a0000d25020000b02910143c3d0017181940d0072841135101290b804104003e004035008030240301e1907240c4a03010000130201c1c48046e0181d50404052008000c003076000418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 484551124 1250 484549874 484549883
    0x150a0e0c060c0a03031d0a14010e0d050d05060a05060d09030201110301090902030c090f0f250e120d120e070906150f0203030114060a050706090b1e131e 67
    0x442c0d00a00412035900c1060640070340102e4038040901c810049007003151a210301d0759000030701c2c008000d680d0305111018424008e40b025580d035a003a1014203002d001940700d249081d600c10f81c50b17024000c942d204030b50b4080c090521035031071140200480d0b221181a1641500307a59000503021038941026405410b01400c0740384500b10010000c145a1010350140034074500a5048500000840c0203003c04450103654404241e04828001000d00b80d140820756405034400c0c0003c01c503840c611070a16031b01ea00b51010301e000310791410650f55050034840a42030084540d40024010449080400b420848034100031004454484102142d142020400c2d10020b00300700c1001c000450344c480c01c081c01190001c107000b002500849502609910000603241620030803184413114100c1340c4100035a5510010610091000500c044804142203218000280d40600e01c80d080700c0ca0140c00744801515603811000400e00c03c18148601d002d00c11b40a2403101d41c3c8508035184080803034000703218003e0003400080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 484552374 1250 484551124 484551127
    0x6070806101d1306090e0309091f080307050d140913050703020f0d020306030f0303150d0609140a060b01020106060806040f0b03060a090c2120120114060102150a0e0c06 74
    0x1c403c0070301a4014411038070034060401400d01c603100d250f9201d100f050f40f0243c0c42070202c4085410491402c0c00d61744840541c11540501c0c82d5280001410745d044880305440c640c010360809800f85404c1503202e03146400c07440700e03a4545901040000c0c241c4142a4600400964480004a200d4080d0f41160550b85000c541c15441740c1100440001a47c011907010b0b000c0e01421020030000400001a240125551800045005010002c0c8485070b150507a0a60701039071110384c048046141003200710402d0302050050198108035003480800e032200040c0c0141160314010041000550011070380313801c1001203d000ca0481113600c07603c0301601c83c1850450341030285000348030410040740c0c00032030000c2c450f22900078502d42d42c0480c01613448464840c800c18518100030040003900c00d800701000c254042c1070310000d010440001c10001d200e9298030540d141c0d5604000004145005404c07a0702420910043c0100c0e09208c0b0b110f2036030705001c0c0c042c0c055552143d004040c1840d0511114600d008040d1105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 484553624 1250 484552374 484552399
    0x80703020d060b0726030f0601020a06020a110d0203250f061404030314040206040306050a060e0702070305011b091710020a0801150e100e040b1003020c06070806101d 73
    0x340d640881c1c0210b51302c14410301c8220048000e9280000c59003250605d20f4103540c0c1c4c080c034002007071a0082820b030460160821090010740148050528111255075100d6170b030030498642c92403c00300b8400d036400d40d88240030507410225041c2c000014400c0904414020910600c1d200341d14505211008218070f040000c0c40760100c60944866104901982c0c0c140543c1c41b44882c1824501c1c4c065034080d400544c20001400460380a80000d9000034841000042d142e5440f0450844104107440c01c0005800c111000c0003449002d015201218204203070002013004032070000f40c00380085104020310031a040d40020081e440602c22a01c9034010403400390359507500c407000100014024000d980c1704220142424440500c44d105c04605042c0207002e40107100d07655001513400e16444a00d8030340c415181c40200045844000c109a45807041e40c074096114128000a9418004001d1621041094482c100425039440000e181c601072460b00700340d400302e12510b1002c0c1550070390400440d000310340320310034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 484554874 1250 484553624 484553639
    0x2111130b0a09090603021305070c020306070807110c0d021507060e030a031406030a080c010204050a031202010605030a0b160908060403090509010f05180915151504030210080703020d06 81
    0x510a8141c0c0ba07440b11292615000c05104031000790202940041c8420542c3d45440f0250f4800e03a084800c03400e03d040c0d43e00300c0b030380020f05d045022a1418000340200041c050b0b40ca4100d002c00c000303980303400040d04109a800340400c80d0092180f070080c0c07191007251a070241905180b4125800311350000818044100c8401007665294010752110001031701d03140f823040180d04061012806190010054186040740341c03100d24042d000b64044000319542040001342698800c140d08000390b120f090f0010840400400190854550b50b220718001c3d01714070042c0303001a56078080c1e02d52040c943c50b00c0c1801503035041c004460402d4546c11a440920407a410300c014150010001000c4440c200c40c1d140300303a0380711520070075454040c5c825160030089d60321a0481a020304c64446078481002c0301141c0c854041940c0540c00300c8000d48501602c4007801d1920b0550342030820020b900500c0b211417240c0707050f00d55804030f000d680011030f1010403c112800828801840f07601241c40d400040c05051084a484210 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 484556124 1250 484554874 484554877
    0x30302070e0601050703051603030219090f090e0d08042d0c09150506180301090b0a0b0f0609060d0b09010b1b0f0307150f090f0308072111130b 63
    0x55140d00c015210004a0944c42001180e0940354140e5078107080c500c0390000f0561100a4410842c00e05d5004c1c880010010010074000540c00500e81d030b0701103418500006901854015000383c0806404c0c40d480550f424000145103085507243d28103038501d50340ba41800340f56051010b001d0061003241052000d14882500541ca060500075070906040f01c1d0b482a81008403031031805680d540d046650010000c51401001404849904042d84100d6404a00c0001d00315080310100303ca90f20000810f00506100a200b4201222415a0007010400003580003c0803806410741c0540b0400c800281e01c041d038813040d000341040c00c5015010a006507180c00e0300032129007213035095940010fa0151050502d0200044480c05445128065440e18040d51200004c2c01405c0441c41f40094032440c4491140c212131080244490041609059072210f0707240007407940380040c04800811844012000e244d1501c4104949010303164003000942200402e0700002c03d0160410211010068100c00030f1034200800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 484557374 1250 484556124 484556129
    0x90f0b01030b0a080c061b150702280b0901090c060e01020d09120f140706050901030b01020105040b0a0e0703060f0b0907050c0a0803180d03150504140a0b040b0a03030207 75
    0xc074240254901d00c02480030040c214401c90f00b036584100c5540c41c060034500300825980c00c41401030b07916250f122208914200304400d100c0417245612003000041075050049204600c41d106a142209265102c3c01c003010084890141082005402154010a00b54811104580d10500fa50303440c07551a400900841d101035112801740c0038540c640d016007481410300c01d069944200440c0e000e20300c02d03210004501d5401e07a04942d0800020001a918601001048014011640c0d0706a589030818001000e84801c008001c0c1903a0600c000c2c4070015409403038041e8442c500e000700140781c280c00030201d4544840d660000c0d02440c0707030070303900722220105401441c4801d000340c0311200c45444814003141e0313920400d90700102036001a5428400102201c00458004c0d28a06030050b0030803c16400a042075468900f074004030755141800b2420b52011b0071901c00421040707401300b100d85070405d41da20103c00010039510b496991054061000e984039442003001000161900303580301d840340381c0179603030300e8160 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 484558624 1250 484557374 484557377
    0x12010603030801090608030313030504030c0b0408010627090c0515090a05030703050a0b09070e0702100b100f03020f0708121b190e01090503060a0f0510050303040b070804090f0b01 79
    0x110003ca0b0340328050044d24100c5610380c000310300d90750b909c5a0324003080d21a0b403400c07410404200800000700340b99202000190068005841d40d1310701e4483c149013112443d6005841034290325040420001c14541010502c04030050042488030300c84c0340103104070040360041c0b9401701a02031052030f01080440a800c940c1d8040d00e02c0d4010988030410569160220303c00141964019446800060348508001e42c1042e070782e104540c0450740301c41c00c0c1401280c08403600001640019000901040140914050140b06592203203c5940b01e41c801403e14a00342c4500c003c0c140c0000d004001003079500102c0340c2c0160416805a158000d18400c440b80766001d603143d1104100003100000b500e500e0b581140d002400e04003500c0508410034500b51481108007840b24188001101d002815840c24440c8500c0b540c4600700003c1c02d80503610b41081143c40161610510028403030061141c0d440003c1281d00341c0d2203c60219071070b4102c40c40e00d101d20b40315503005401c07103908104141a050106420132000300d01c09 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 484559874 1250 484558624 484558637
    0x31305100204170714061804051905070e1507140a060209100305010e040b0618070302030628031b08030a02011b0309210215130c05010804111005091201060303 70
    0xe00f245944840074000d01a0a5035040700501c2646020700c0284520100942c104c008070560b00000340031140c0c12508681e05414105140d08141458807502e0340c041051308006a24034802c3d404a091a0b0083d012030203c2600000c006092069808501400b6500c80040381c1d405146441c21a0181d0000c0107000e0054030402040248a4080c0c010281604c11103842c02e9916038aa071140d03220740902515054108250b603503c800900701180a0078890074040e1009662814440e091140002c4028000404540e07203040e101418401902c00c0ca040b40e400c5400c00703e074465600318034100042540d11803046071000160268100390190407201d40340c0080394400201020104c4241d05843c20303681b000780f80c0242d036100b1041303508041401151000b400d00c11500c042c42d420004440082090b07540840010001d0a0841003103c40c3d40b6840c040d05007840d00003080c3c1082d560b8002811080e001082c0b00d21052084038400d58841d6055a03d0790304003d2451400c1548146081d00170070f00c501094000904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 484561124 1250 484559874 484559909
    0x40c0806070819020a050f07030801031e030e0603060316091a09070c02090c040b070605011a0a020a140a02090c030906060303090102070501030b060f0a020618010b01080c031305100204 81
    0x20400607120344030040000e0040d007580d06110f0000d40c0200b10000c00d00005100c01c0b41802240400380052912035210080a541142000c0a05c0302c4a03040e40b030710b081500da0800c030001c1d9000d280a00040710503100e143e16511080001303410310104050145040030360301030024415020b40c2114024410911458006084031000d100c03407000100c0d2403602199071220041c0060416001083d44551500b41c040c2c03c00340c40d11450031481c1d02c0381d04d054600948a034014004183d010160078810b44481d03024034501600544041d41310111510040c180e80c000c034010003102c0c10140010115154002e2560380d01c1d00e8407a2226071540c10998000f0307800c1c854100081c0d46420f00004885171044140c0060140311700d44001140600030400000e5042601031003224480c0748898090304003511141c0281919190a100d5030f001c034502071560b003107a42e04000e100601c3d6608200c045130881800044150f80342e40b1120206110318003007100803c41e118900e580c0500c69983d0740034100307480e003043c804a11032a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 484562374 1250 484561124 484561127
    0x70e04051b0304050c04021303030e0303070f021002010204050312030109150b0d0c0306170601230607080d090507150212030f0f1b0d0501140405070206180106030b040c080607 77
    0x81046519109810100703560011591001010390380c0315210b03804544a010300c40001c6020381c1c00200010a41295880c818010150080004681218181e00450610b0f101e51210800210070801c082d004442c149504040c00781300307404640181034082c0881f840d41039204030602050b4824031412a0070784c40d1545002c8060101d45000b001c8031040c000c07803420404084608002000403455400506079541d000042007550a082c040e000340410000d040035624104480010714001e030804550364100f80d0344a4072a0740c420041e1803840e90412106501c4405603c1541c0003010b10b102c0103016442018000a0300000e44144982001400d5003502e161040600f40324056010540d00d01103c0c1e84072500007050036994403006030b40403008480c00520100038880348107056101c059000703801c540742e00c010300a40b1500407138080c0800e0305980400c40e82c0b41c9008020740f40c1c0c1001d041069903400422910200c1c1400f50014400b640e041b400b0f044031402e26141002c1448030a10038440203005501c0002d4032607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 484563624 1250 484562374 484562381
    0x1030b0a0501060c03170a1509020711270a0b040212090d0f170c0723070605070b060d060b030d1e020304080a08032a0912030408031c0204031a070e04 66
    0xca6042d25404c4407100058903540c82d07528010b00c1d1078800741e07691818240c0c002400b03002400400d40e049d0f0050b50355009080080607401d416201300e01880788650290a00d502412480e0104d81c41c01d90b51800e55241e0510410182c1000c042e40c680c802d0011440e10050041f12072014005c1c2c514070304580000340c50400554400480c562121301144508102207003940114401c240e01ca42c3c4048003601e0510260744600d245520300310a400c42030300803200191400410455803005d40715034146942452003542e50180c0300071004003514090102d2140480410500e508070703051440c0010103543e10320005540c014001030401c4c920304854000710000c03d21541c00403080340e0540c0c072000080e1803036400300d03199200c80e9070014007601007010702c0300c450240c01c610002580c800c2c04020210300f41c1d9003041500700320890040c2c590100320f40d0000c0100304906c58002044441000e104c152000c41c007503090800d60028040d030751003e000200101007516114007a0703c0078034412007840d107409900c181c658040c441107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 484564874 1250 484563624 484563647
    0x1701080c0616061107030f0f0e0a090e070503011109040605240307140301031212050c0a030e01060906090c08010b1204020628020309040c050f03070e0d0b01030b0a050106 75
    0xd071007001503018051440b0042c2c0c14507800b424002c6407104400d185210158800301091780090805020203101c5903000040d001d40010500d40202041005800107551a01c0c6201e1340c0c0c90b280d40c840507201c1d01c400a00c284401044010000c000001e582082c0c204180d2000700241d224610740b01000c5428588010103104104800c0050240d95000500380400307944088c0116052140700600700c81c0101212004502852150310709010b205400840980681e55100407103c007030b0700307100c200412030981e03000342c0d0101075a51a002c58074511400c0442e00414503504017140341410b201c00402c1c1d016154011184840841d510702d400c585c0d80700c429000c140503130003450800050000c00306000d403030504040c200a14182d1003200c2d107036444100388080b00841d00c01c5035015030000b0900189515180c4582000790b061400e00910b0170601c1c001c0b40d6054440104814180b10341030000d158107407101c8817152803c0360b0022010340a541c49080c4060015001c4844d242d41605040010607041d100b006240768 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 484566124 1250 484564874 484564879
    0xf013f02090901051806220510150e0702010207050a061e020301030c15090b030402010e1203190813050601050907110609070f060509060a030e121b01200d0e07151701080c 75
    0x800100c900c1240000d0000090940751440b0b001250b2703c1c050b00c00e00c0b074501c0c405000044600703840d01e081070034810400c0007881d21043d0391045c807881c004a0700100c1d4136100b40b80d2200c00001c5515107210088036240002c00c43d1a84a0b20102c0040208050b0389c0b8140262402440e12411b82d03691007a048901c140c03a4001c1d24929002800070400550007503201c4503940740010804120885c2e5490b1070f0b40f03181c0110505c41c40d140b040c40c0d10104581d80000141703811407204128070444c001e2507100c40750740d840103200e502e02031100140064500c61041a00c01811082d880584d591810b2038100300d03a94200b54015024030300c0350b01d100050f0305070180d812101d100502500007420309181c501300b54000d04004900241900484501082c1584050001c02c0c4003e000c645460703205400c01421800c50350642141d540f0554441070700c0003840440425101900401d00d004940c13035401d080c14509201c0580d0061130000c104421601d030558001604200d00c004084422000740c2c2d88d00c0c01d040d540c0444000940c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 484567374 1250 484566124 484566151
    0x92d06051f170106051302070309061e120f0203010303020706180f050111120a02071e0f03120c020d0b07122a03060f0e0f013f02090901051806 63
    0x802d840c19a0746002c1c0005014000140d0a541c607804980d04d100c2c1c1800c0381c0c4880740d001540b4000c00d500890301d60050400ca151100030918401c031201407400005403034105000440e0780240004000e43c10904509e000d60340c0c01d64803965245006503845d1964011b0f0f4021422801135112840001d0128004480e151411079560303a14203c015203414405503c44a1a0701400500c560228a010020641182246d0040c81201d2030210500d400210044052283c5d61481000f0014185250681c4080c1e80c0c208041d01880a00c0b201c0940d0038105080d0f0094011480030048020b01c041e0110592217141991110440800704098107403c5074400d600d012402c0c2450b01c4a400986000c40303207100711036401d040000706c10740c0303d41c1000c3e06000c01e94060306000d00070b0020440d40d8400c040c21340d40103040310402c41c210b540501141101e80180c00408900c0315400f540d0008081c0080c40e8885095a00548403c20604144500d940600070880d0f1040a07204610900c005010740094802d01c2400e2400580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 484568624 1250 484567374 484567379
    0x4080f190f0311060718050117010608060105070c06080103030e091003030e030f0102030c03041211071211061204201809030405130603032c04092d06051f 68
    0x14028070360645080d02042890030301c4103614102000080c3c00743c041c1da155114169200d20424001e0246900b00c0350401c5440c24100741c20a041281c0281918002d0074207015aa892400489590003496005004240030321400034140740c202e08041d0590303009659040f02e48580c0403d000088400303a403a8103e207442e0308801c0010910038800f40c0c036150130003400e44544100080780c0c07600baa001643d60403000c040010038070040003030b4400e04401c80111814604542c0c400402c0441e02c0d82110b1145048590703178252500100900d4034004141020010300340e640700c0c40d42411940c04c200c41250100c40c48031048d440c2041008150312140d0040d0300c0107040c3c488001c0a040c000c04d000c40050f0540100d44030900c0702003a595502c2242c4510f25096010004100b07203541001040c2882441e40d1104503000c0c12010403414042d184031032411101a1000b06581c4d01d00e02e003a41c40703244480001c421000744181040040a6610503c5108134041c24081c0015214421102c2c00511008484032480c0810a000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 484569874 1250 484568624 484568633
    0x20306241c02160c05030c03120412061515080f06030a0201030e010e15160f0801060513030b07230a050a080703060312080108010c0207140d0f021504080f19 69
    0x1495440e0074014409400c000081c0341e1604588003000d011a00c106941000b8002030804201061201004074000c4c840141c0c600140d032a01d01c100d0040f10107036088c4003003100502c01190814414000c00c411a040e103140e50304521514190f40c9003c1500060102c0049401070490b00a05801841d004000e00300459096005400a0030300e0f03100c1c1502552100ba051034101d006103c101c1c1302c880a1201354070760f03251030404d58480c0c403850719950f01803114580d2544140c0e5440058a8103490890070320b42da031107024041c042d020008507070004000502d02c100300a07280380d200007540c080350b00b50441103c54410031902c0e0b0907503000d080b001d000020414401c54007040d22801d00517070400e5650030000b900c503450351034030b00300c0380310300c401190101d4407260041012800921841480300350500c0508041070600b00d200ca0500c511204080c4190030002e03074103043c410409000e00308268010000c40119190b00291001c680041c8515045809041500b0803a2030000c1143c080070005004060b80e0080702d9903c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 484571124 1250 484569874 484569907
    0x5040b04270903021b0f1203040501020f0703030f0e03010207060e030a0f0518091806011d07030506090103060515061309050610050706020d06050d05010f1112010b030604110d02030624 81
    0x140182d006c40e6254241001c0d49803400c0300c82019500101a5a0302c50804002902d0450200d0b06000300364041c2c80c040000c40d41c041103c40801c4400c0c40c112038200704240001e4064010310740080c1603075150200300310051800200034241500c054403004500d24460000307543c5402a0380041d8411000c0e4050b03100645081485103074423440b100032040000701c0750310040d0700d820785c01d80010403e04040d0140c14a081100700c1d03100e5001b01d00c0e2605000e00d01c0c1000200d00a001e040c40024000c0f5214808175840044010110003900d10280c0075940340d0f5445c00384a0342404061007000c141a182c00045409030421024841c86018203458052a15205070746500003507118000030016a950390402003415500c900801c561180100c001154100c520309281040312811040d43c80c0041d0100801120081d403d2005411641803c1c8119113a55403040400d0240000b10741c1c4100d00308001420385500101030740614003803001a01c150072450745c3c131a42d0354203111001c4138810031100188000e2007610401c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 484572374 1250 484571124 484571173
    0xf090b0c150c1201030602070b06062809051c0c0605090a03030e1302040306021207030c0f0509041d1b032a13050a02090f0303030f061005040b0427090302 68
    0x300b2a0386070807140107040707200400a03081140e0454002035840248690356440a40180c81102c02a01e40072450112221090480e20517030a089101d5121403000750082d2640c60040201030559034000642c510580140e80703090500311642b0144a6000c0350203072041043d01c000b00c901401c05401c0d82c1c00d603103099511a81404006a100b0ac6031044590502228005030004600ca804e01503210211420740200114008040d017082504d000d0340c11070b00c10b40c084501c035807040c05420420307603038106030b00858040c0ca054900040130118851042d0b1050000240c284800303a00ca1203900c8190070304c002016160403043c0016041d84c41c0c4140070511582e1404d02044c1c1d2000001e104642c0079405106190640d07000321030b0821801d80c0811041100c0c100401c0504810b82c044010354034510309003039403035820800644032900611107295003801319400b600886010b80005440291519650200b1801009041101d2440140e004648440104103270103883e4642d03074182c0181c14070496564a030400c071004070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 484573624 1250 484572374 484572391
    0x6090510170708120721050723061302040e1203090715080c0315090405070f0501050715020c070306020705070906060e0a0b0a090513050702010c091401080c0c0105070f090b0c15 78
    0x1c101081c80403208103808213036281d0544807c2d031100c115080000d40d080c00c2c1105103131080c0008858902d51400400e105510507907412209001d030096001082c000c0462000c420081e1144100e41c080d054007040180d44030784200000c6910540d15017074241034001840000b034020030360000c041180c21740d07200044c56014101c90926841c40081100281200704262000d40700740d0040c2c40144140c0c0320031000000680400e0a040b40303018901d070b48804040d6185c02d445981c059000c10840f0400c0b1041c04240c0095800850554450803d0304086445840d90300c900d4404915080c030000e0385c1c50003074840f0078400c10002c0001030b4681c50300d205222a0303030150100c0300400410303440125072640d540c07c11401c00850702070700103180c2c42c0c09540682100c5d071018800e018407030000e908001e40b0207140d00401481d202031a1104d1603440b085400e511038001d612007410a5420300081241c215440441c0d240404250b0351001070003a42e5206104003032092494a0216170019a1180c031140c2134581d000c0d0b04140305 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 484574874 1250 484573624 484573643
    0xd05130c140d0f1109090102250503120a14060109150806150c030c0d0c020d1e151401050108160e030a02060c06010e07030b060418060905101707081207 67
    0xd030390f5030b510104180007044401a045140c2e00c2e503282012070a05071b000704004000c61500c0d00a58039401c11100400e4200c003418112101d40042150900603980c603d01008135408450910004200c09803d0291502d10501203000000c0e42961150320541c04036140c080304180384917802d06040314068801803042d81c108055002101e24528850024041504000003440c1c84410141903681000c20a041c0f03401048844600c0750f016948241e0011034103540200240441504040142505070130550301410100d030f40e4120041161098000481c2180d00713601d001d682d41c0c1c80b0b40042d284842d068400140381500041611074107070081e00c902c845100c00504980028403964000396069029164030a215001341004003c803455145a558209490341418881e802125000c2183c034011840780703a07100c404000c0d0035210381030703141c0c4a08007400550710140894645034601415041492181c2d54025804880a044640012034480180d4000c00003420102048038007602d07154000b40001e460b46060b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 484576124 1250 484574874 484574899
    0x403031209141c110105091917040f0501021005071b031b11011d030325120503150f0604091d0a0317070c0506071103120c0d05130c14 59
    0x6042040c1072201150b441002c00842540303500410040345041030140f160705000c1800b110107c0410840120700d280040e0104100c0141009195044202c1c0710364200b4400180114690300320300060415250280c00306d5400104014045040302c40488814002400041c0040380c2d481c2d50070b07481854a4028503045000809400000123207800301d0004a0f00242e200303c0c03550017560000541102120500394100385200c680d408a40c07644603104609981c0600c0b80c0c1c2d160b120454000c40c4c100c096030440340c141303d911001d020207031032a80165a2034a0300b8001050040381858010b000809035100504580d0415291802c02d001030803454410040c521008250900c41c1c0303408100d0f002106000c1d6483c0c4801104001525100e440080c00403020481c00115480100f0400540980c10030140d20300303005810500070181d800d40c001c0300802d004031000f200500ca044407489004c0c0034810700d140c2041086031503401100d1030303002003000001c15900280e881044800d400ca60b104022400181103203908a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 484577374 1250 484576124 484576163
    0x18050102042402030f0708090d08031e1308070605130803040804260c090408040f06020705190608070302030403050405060403081209010b031921020708120403031209 73
    0x1c000c2d401908402450b9541d0040c01d0741aa80306400034040d034000b0b0340c078040780340720912401c0c4580c007070113861250700090700c8160741c03240c04001c3e00203604200c00540307a09200c2d210540942d000c0304240e0030b81c101440480c080c01a40d10151095031b81c0070a481c0d01d4114131342d072543e0180c140108500c1c44d09040d08403000106124000641c0318038880c1c0307121030f0f603103040c210001c000c0c0c486c880000030045040c140c00303410001c000401c041301c0c0d1411282c5031311325991843d001c3d0042c41690444c501141e04c1900010703001303400080e035405450341140c104075038484403031100110b03000c1445401c000039031000200d05024026401590081d010707280191400e52a42c2c0450b200d60b00540c800c581500d000203604000201080340b081d00b25041100921820b0281c3c0000307603445945a420300100d100c0c4d00f00080c10440c4007544400205080101020381448131000651941c009100b1040940640081640c5200840c000c44080d130303506444404211200f0050790300288209042203540d007200951564111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 484578624 1250 484577374 484577377
    0x60f110f0d050714010203010b03010302040e010f0c020c010813211b0b0405190b010501111609090b070c031205070507060e06060f030a050d0c021306080304030605070f090918050102 80
    0x340c0301d645405541d0040b81c500354004030140d02071860540d01c1031005001c00390441c0100ca044a0301200e0110302442c40c0034410f401081201942d020380e610f0022608038868021070346400c3d50200340c0712091560b0302c02c40718111071403401000030b000e0050880c034801509810320015403116020302e007040104400001000510909c01030542da441404010842005800c0012071490312111903100d00f10016566060a9020180035160500114103020406094208440340d100742342c5090325401181e0b108a45e800070002030700141c1d450203d0000040c2c442c0e009074075442045a060790b92007006c07030030b506441c0f004080290001d01040020030000c40425000d019202c130740310403040586803d09040040000e03240e900074a003400703900180c41482c00b0070340200d04421410101d080c24881091548005201050160030f2404094038280010810b01c2d030000c050010baa104400c00c2045452340b003800d442d5000440c103e0000508107a40510022025802060002e2203501c2c0f00e0b418000710f0355446099 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 484579874 1250 484578624 484578643
    0x20f030c1b06011217070203070905220c1401050c250e04050c0a0f0e0c0d06080604031713050a1b18021804053d03110103060f060f110f 60
    0x913040c0c60400d01c020700c0000c2075801c6205500c000039518120440d4040f0b511203170240700c2d01140581d02c2000036000c076150061441c0c003092656240c00007191078903142c1c3c0c40000c1c50103149920440d0710003200c1d955002e10304460760703803031b0040061400e11007010b0310801e610200d43c02c480003158072487c0041c2d200c50b1002060300440c0301308090000c840a900a100840c00b49a00c001c4101c4401141003003035054407590700e80c02010911b449552900042c0d0306101404803540a400648503a10405c010b16034000542060340680c2041e024090b2214541211202082d60018185400c28031100000440d20350800c0180d80c0d4003440108003e5844800401024a41c00d0030034000d0340004400301ca8443c2070003180007643e42140d00300120300380440c10b40319912003903200074480000070175441c1c0e16010602c8242024458a00418180e0740c60b450400d84070040c2c82c1e1400c0c0440d0420030b011461b00310b89a410340c1610000e6803442c5400704407000494100e40c401c1d0380300149020781d0702e851444c007500740405800e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 484581124 1250 484579874 484579889
    0x4020a0905071d010e01170c041d010f090603021e01030f02180910290702090106091403010b03120703120911010221030c09010201021c050118020f030c1b0601 70
    0x9000640f181c190202060950352810004180707902c242d6a03070010b600b42450308040411f0301e0640d40d1680700181512807900a0355800ca9580b1099603403d546221003410b0f0742410401c4070540c2e5503026903406a485034003000b980460103001c03080043c4640903c0f404c400d4014980403407000b4112108400f280e1160100900c1d00500000b030040d6401e04900003a00103111302450704c0b030039107400c001c0c007440c90349e46000740e10011401c2c6000000c0313402d100c02d03280465002451035086580d11503026111500601ca5040b82d0b0030074403500812854103100d2581074481c058041e010f050391015104413203074003a11044050050484205500604070b10880d05014490044400300d58126000603141c002508800b9080780318040f40700080d0031040c015260080c0c1d0101c1002c0e124440140141c1c0a8002c82200184102c40ca003071175909000641c00850413903030132007015124000780302ca1040680c41101d40c10402c0000420101301c1e910000c5008010f58928119041f160b00c003c00c0225003403040a030b00202 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 484582374 1250 484581124 484581137
    0x105130b0301080f1506040509030708030702010b1f1707090b13031703100e0717070305070e06090307030b0903130b0307020105010f050904021003020d0c0c050705010306050604090504020a090507 86
    0x44404001c10010700c582407020300804012022407171740c018081004103503600498541000c109030032001c00a96199540c080e440035241d1408010081c0280b1416501c03920030007070700c040c00d02c0000c04444500154480c035900d02a80c42c81e01d40c0054040080541351004111101400094031041d9201402c41d404855105d008868514284111400f8a01c412510144810001e001c4146903160704c500c116040c6407170040d420b50700c0e204265107501c1c0c02072860700c030061040c041140c02503041d405644903030110f40302c1c0040c81440c2c00900c107041c06451803590f010303480790030240040703182c2d074125541c0714040100322860400c4421040034900500d0380b080248520200034004036a40a0103194050000c4c0c0000e003184603d07100010715180c00141c00030740201031985031040101d109070102c61700c0c0c48042d0018481711001c400000c2c42552060010380d41d03405019804142c82d8032a0003020101c2c1c03401480350303051a051140b010000c200140c0f00303d034002c0710f5aa001138a0f000b94040c051203100ca070348504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 484583624 1250 484582374 484582379
    0x7140c040e0c04380f12060f1b0a030f0209030115181a09060d050d0c05060a140403110c0a06090e07030903020d030c0e030304090e0f0708030d02090105130b0301 71
    0xc401c2c0c900c0000e0143c001c0390361007800d01c2c4a805103044160a03d410616040780c44e2072000102c0c2c0e215941c0041241c10910450b6051000391002900b03902800c4c681c120f141603942ca04800c480141c200305840070404000b00100c0c406a80b003a0043d907036400360508010302d840410300020f421141d0002d8903840c104c103002010050b4080010000c4042c07604c40d80c040c071004480c060803c01c100d11352665280720b1021100800c01b25100c1c00c4040c42d4580e404000c807580d2507455080644802801081106d6a00c10f9000140c50080c40f070003021180003117654070300d00c0c5480e5507800b5948800d64581014891043c46c8415101d66078250540004188940759074800c2820203003903581010008003100d0a0500740b00c28600080d90014580d410072460740b80c00206807241e0101200c07002902c1103070307a90500c000311b40403030040c481d81c0c00941c03082985030440300080c5491140a443e00464881c0103040c0d0006c2c4480106005150018082d62030b051601a207480f80030030440c0302c1d064998002d400103280c0400103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 484584874 1250 484583624 484583629
    0x212070c02030d031d0703050c010f0c03020303060402280518010c0507170a06050c1908042d140607110d020601031b050603040c0f0504111e21060102012007140c040e0c 74
    0xc0c2c1c840c070740103860564100408dd4070041e54a11001d88610f014a90008108461002440d04003500b02000b00d00b10780455180d610041c00303a0440d038050b8074003018005038240d5560140c0c060200007640400900705080c81c001e03d4408410b40c1c544015200d000d41c401c15000100940300c1d10384100f1200e404180c4400b44001c4d4501070004030031010050115200c14000070907401d504600d9000980c41c09000301402085840740ba2061a9200402c03500c0c002c0800003130b0420104106204900560b10b07050112050b14000c0e40c0da490680a08015070010001400450034007200c040940c807103010290417440e5640081002a441254241c2d00f010501c5800d01440c0f080c01d0041004007011034060155008504a003072461107507005885804c040010701c50583c00c43c2409880c6a200448200c000042550707550409030708044419a005510300101d00c07038000d849100d2095422030703810340780781840102d644200440062544040c424400c900545040c2da680e0700440100c0c0d00740c640607129145284c4107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 484586124 1250 484584874 484584887
    0x2030c0a0f0e010b180904051006030305030a15030c090c0c20130c0504050607050715120509150a020c07030b24090930030a0212070c02030d031d0703050c01 69
    0x3041c40414010040c0805c0783d0a03011218160f50011100c0401c43e40315480c1c018a48481540503141e202d0620030000141600400594070444610100b4010300621411007148240d05010051501c409100203200364181c80d80004445501810030200c0d89a00d501d40103c0d50300040030050071101300c909403002a0074101e03402255520f81c0c0c582803010403101c0e030000c1c4c07407030145014080c003c000100341e02d0103001e42044100010641c940c104110b00048c854000c000c0e40800099900050400c0701003013014030b00160030b808107d2081403041d0640c442d4915640030354400d0310200400d100310000440410718409a0901841c0303020380c044240d1502171900030038070011a03025442280c2010800c4030031080411402d0900300450302212919480a00503480183c406104c203401d50004010060762000f26402071422000c08026081a6030b90340b40200d92002000327000030f4054104992040d462406600022000802204109581002210700b0f0349003c0003940706840d03035407151a1303e103a2560405c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 484587374 1250 484586124 484586129
    0x3060801050f09101b1b140604021509060a20010c030c0905090603060402121509010c0306140d0602370806030715080a06051f0305060d0b06090402030c0a0f0e01 71
    0x20f20070300040030030510a042500410341030301d0a01c201030345000b0806d0001400010310f29880000b1803803400c0b01015140c0d440008460490251740c00042c0c043e41c4102280030765150610041c9038502d422031054046030141603e082440e144030080000001c09042800b92a050038500c1e80c2c009102080d05000500759400388d07101034000c0a801040c4009502c011514650054041c0c031020307294004800e549207000c450058200442d8541c0381482080c1c4010341100d22813414555041c80320720345075201c1c241c0380c00301000700c0c1d0392040c680f540b41c10001c0c041d80c001d04400700585480341c4030350451100040d501240c031050b814170074800c1d40e1802c80351074000241c190415000d6006016440c100610810788101d079540329014000510001000d0307108075080540580740c041d14500d0034550030380c1800c0c4243d4400c4a401c01003420300001a481e4107080045400154200c0b1144010340c40d02014070480c24070190042e038140c00b0f02d0200e0040c41e221160810024241840812016450b06500f04014001038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 484588624 1250 484587374 484587403
    0x50606040302130209062709070806060a030b06041e030510110307030b032d0f03030c04030807020a0f1805010b070c03021011060c0c0c030102070203061603060801050f09 75
    0x103000610250700c0f00518410800c3c6400b800503034902500000030f24074015900780b0071915101c244c0c49005805225415140c1d50819143c0b84440e480d14402510059030450714140c00500a1081148181c400d4101200514025240340c0c980350311000300f004441d203c0c10f00a41903101200d8100104202000281d0308607a00304400c00004c21540040402484044e1450042588411503404941d5042c4404800f03c00d8001000c00c5080c1c22040020501e80140d00e00141d03401041180381006001200f140c0c400d441c6400c400d85040d0450b99954016001910309030380160751801c02185c0b00302d0410402018003501d04140144000b080300040554030305070040d6a00c480148605400600d60700f61090039a9411154000c014100c01300441d403a45001d110300d0f005204000c10300100318011002091040b0f1442e003544d4000701c2d40c0c03051600381d2254a600a4040c3c1c86100010041a00b00500c100d07020403038034003c10010782d5030024600b55141608c0e83c240c5500030005014801504000c00074045001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 484589874 1250 484588624 484588627
    0x4060c14010c02070b0310120b15030c0109090f0204090e0a1403070b040b070519030e0c0306010f0611120c1f050411010f110a11010e030601140d0231050606 69
    0x80c8000d41395180c510918024100120101b02d46510792030110000e800b128a07510380c10041420042002d078001d5440d0010314460040e21600f40c140403c020300e1404040c1c5804041701d1030b26001d003004080c203a403c04841d0303609110100790400c0b1030103007080e21b902c1c40c0c004040705d6046041101200c1c00312050021180c1c010801200040d90218070b040c1d2054000403910300690b103903801a58240704540d074070709079030754901c054100040d00b5511034020354031404100c07201050f090081c542d88240c05e00940b03d4000c04020100b011030710071074030340310540c13685019601d41800700511702c08240c210820000890704100c08486c440241300004401d40b000112091000341095210811180c030f4003510541001016060005141d0003a0f40a04112169030308450a4050504208500c0700080c503110340080e68001c13404000e0300e40014683d058801da00c01111501c0604820406041c14284c1c0891b008a4100039142480c4100806a2101c54281d40000e07681504e112856040b203000616440c49843d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 484591124 1250 484589874 484589891
    0x2060d090605160f0512060103021b0613050c03010603020609040b120316060507032c010209130204080f0c10080912210901060b0d051e010b0d11040e151504060c1401 73
    0x140d06c20115004002820010303070799400706000c2c400081d082c2800e601c89100c7e4000348840d106400700d501c143e9600440a07185400048000c05d4282d80161101941c00701092200380d04074500380c3c1c0002401c0781c00605004000c55080c2050b4110341028a510710464425040c1c203040c4070b40c60081c513502c0b85152070100030b0303200300c1002030400c100303074404d209100700000c22403441800c0e01b5812129446002006200550342e02550000a540300b40100c111602403080420340141e80001e100c0300d0810b0041484003d45015001100c038140000d2909000d44a07103012078050440714402814840b072007418051a1008400481c1d101031000380030a1410381c035009040120102040c00e03034002c080d0554012603103459030b00450000c910003044c82210010a80000600070034050028464030035504828004441d11103ca030905000390320989041c0f100d443c000074a4007911a8465541e618001d00c11502a00c510101c10016005030b04a20b000c602d045960109201081400403102d00c41c0710001e001510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 484592374 1250 484591124 484591147
    0x813080706092609190f0519150e030f0a0b15040906020d05040203061302030a02060703030f06030506100b041d040218070f090905040b0402060d090605160f05 70
    0xc5080c4000d440c05503211030801c1080082c41541102e80380c40808103d034821540041e414981c002c02486101e84003400461036054105000c4204484201c0301960142c2e250205100040c1150811a254400d1104011030303040c0100501c03100d8030b542a51414030240b407201c103041ca401d004515642040e0300021000001501c0c1c5440990b008150422003696140b5403401f14000d400422001440359001048440e0b01d04115804144114002c504690083d151501c19503030180e08440c0194154221007544805401c16200a0420714440d2034005200c5030480c40780421148241c2084802e03801140a218405c20a0100c000182a45090181c9414036200200035409445000002c40456034000942559550070302c3e00c00c9032040d980d9080d04d0b80740c0150001d104100c125420b05c041441c41202184e4410306204052080303030301010103003882c0c50b60b808009140e04004850075203d40c032100804000780031401100d010b484807104c25a40002c195202420800d1101c10200030014140148203c01c3e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 484593624 1250 484592374 484592377
    0x30b130b090a0e0a020307030b1015020a030507030c020916120b300604080306041d0c090a020c01060b030f06191203031b02030a1701080703060b0a05040908030403081308 75
    0x802c1128006050022001101d00b40040400701035414040d109000052114007240f1510031180b51101e07002550b159091070381c00701a10b048100050f4003070329964001a00407001081828041c8c02e0402826000e42c0c0019003144084418441007940c040c5060121138000407000035410859606203e881145400304041201c040040000c11203400c5140b1110058141c40c4104808a4015140c2c0c41c83d01d070512015039401590030500981c5013104500200700c3d0030746400c00105803e806072100440c414104292801d01030f040989043e0308000707a40200d8024414a0010200c580780e864603850142e100010f0f03043c0042145000310780044046442c032455000c140140d03001040b4100407807605090032001060010842455841100740350644c180c1c000001d00a00000c41e0b50f580e40b200522484403000100a00c40c2002c02ea1102409000046950304031004210003d00075000e01a5113100081c10394544813001d80d1003901c008244001d150b44408990340c0300c044c00b4403200c24070141c0ea4a1301940d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 484594874 1250 484593624 484593631
    0xe0102060613050c090409080304030e09060a0b0c01111b0c090103050613080702090a05041b0b0a050f090402040608070908070303020604020d030201022703010c0810062001050106030b130b09 84
    0xb80e5403000001c403410302c020169001940701800800a4900c80c0c50311543c6507009641c26004102c808401c1195403030074404040c45800c000d040c00d015203180601242080c2c101c080c10132030a540b240d0000f00505859400f5280c0c0034100c00d00c00001c0030b200b007126410620a658a1400b4100107001800031800001b8070b41e07041304411100102d900d44034140f801c107074019100005d41c003243d8a0288031071108070740c000b070340900d001d00c0201d020074840303c3c03922158082500c1b842d0801c1707509200d02ca000e60300920150200c03034000140545060847e00024040b40d00582052001c60409018840c02c140d2000d9424040d1084400a107420b03811910080e580700b40c02040241728205032200c0b4000c051003074066a0b048500e07410003e034804000c55081d80d03c4145c81c3c9206010798a4048001101d9205920103400f81546410450010f41004401c541c0200140c02c0311040c0c0c64481c4a0b9641080244210b030300030402540c0c001030f02005081088903182041c1041600d00f070403c00c4405850340c031703084010340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 484596124 1250 484594874 484594909
    0x1051e10060e03190605010e09010e06071d041b09060c050303040209180a0606030210260606070506011205010c08010e0a0b03120a21090305160507050904120e01020606 74
    0x40b50440900040d240c942d1092500180400e10551202041040c1c0c120300d042c2c400c403c00e108060b50300d103004d0302e088031070001d00718046521000114412500550006440003644111008103018901c00f040a035145c190501000c00b62034503110318100c0c0c1c894401006050980f1700280c458400ba1540c9a49000251019106445801c080740341f034034100c1c140702e0810161100783d510001440c04c11a0060410780b005074003d086007046134070040d204108030007494601403646102c030204044e24208050000f070036030340c20541c204618404034108000c00c034020300150341840440d20340c2d881e0075030030351b40325603941e209100e0400010300801d8100d1110541c04145682c5c005890110340d0b0020385484084041080481c3c40054004456030f030080e980d12401c210810a001e8440d00c4a640c1411228260780c0980055001c0c01140350422102d8034410480b8065011964a06c0c0c0703d40000311604003d480450798100002d00300e200f50307900120102030b14407090010300403d1400501181e440300ba4100d0005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 484597374 1250 484596124 484596137
    0x80a0308070504053c0a0611010b091609061d0d0611040b1206060403050a1b0f0b03070816091205010905011107020a090c0c062c01051e1006 62
    0x5035114425010340e0300509008040d061242c26448a100104420700e0040c4195510910f101d19034141c0740b20703030a0405e900504503141c11031416108032440c8510750309003507a954131503002038001d42e00e00200b14042c0c50009044100444441000381192038076901070001d000092a205c600400000c034480b14401c0b00f6210303003001d003007189010710061000341c03148212607101040c0442c070220000d02400304001c50880c83c3c285a201c00003009558040d03448010b1091340411070a00000b00403035400014413070544400401039460300c440c41d01103e0241c02c0441c11480120410526941c02603103980c002d02e80d030845240254047d40008d02402181c0152142150461011010070500354412900c1c5500240208003600e08400c0c142c54a520920b0b09074440c4090440118807040d80f44104600c20319280c8900c1c460010302c0ea03031a07001c0c05040582c85042102040394011480c1d40124103640103406030000180c1d49040600c20714403c1c0380703a0484180c21083c504008041c50380320202c2054408a04004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 484598624 1250 484597374 484597381
    0xc050907110604141e030403060b06120a1a010309050d050f070602030114031203070206060f0604080a060b090106020a0f14120c0109060f02071a100b120103050601060801080a0308 79
    0x207840040d200c8030041101d115501c10071083c04118803e000d424040581590ba112150800702c000d0001d59031040000e9400800042000501325480010820f030090311050408015205c074109540c8200c03000c4031000c0e01c800c00540002503c42000d0101003090030200042c56154031100c0d0341700c0c1080c580030103111f80011040420301081c01994009135000c042550780750f031543c004030000031005084500900c540080c15040300390510a40e486540c041d40200700664407142001400402050801d40090040001140e105010701411403a40c1c012100403585100b0300040c01007c080503840f0900f1074010200607000110f210360103801407a003280040c444440c80c41c1d076035428008214001d11a801c2c0c0044c0b2050800c0c01074014a0785140601c07000c100801680e01340c4010b0b8460110000c240040f025103648510b2405c28025402c04c464a1315003000c16201c0303840c012240d2185030648016001d83c0010810003900b045031a000d0441d0b4a401c500075454084000c0e40c8401c03401005040c0002107002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 484599874 1250 484598624 484598627
    0x111c060504080c010207051e0a1502090a0906080d110714090a060e0126010209061b070306020d09020a05030705090f040f0b07172503090f0b040602250c050907 70
    0x90b141c20f001580000c650724009440d1169503040c40c03c0005502010389484d103080c0340c030f021440300030803034104c105881c48a080c0d0464400943c040a04107a018124107030204018030f043c07285002510b59407000f02085802c02c0406031204020443c403c0003580480810300540286400d51012040c0c250f46140305501c49807406405481250040e940000340e582c00001c0244400c030b10748000c001080141110140081c1d01d6509038803035050600d030820000c001e298591800300350700e40d811080c4201a2106662070342d80d20f205a901c195580d00201d500d600c002001d500c1c1000c4d03032000a0a0407801050300c1450800824140f04000304032185d0408c4107000101800045a501b02403154010b00c07000340c0b4903040b9800f86c0324001d11503545d506014010002480c548043c0f4a200130207101d180c0302d240d00030081e0011005060f110200b210081d0171000301c480000da048101500540c0b003a1000760f295103080110101c042a10f0184400764004c60410001245402d40310758242c2d0000d6170606243d58a24a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 484601124 1250 484599874 484599877
    0x5030c04090f12080412080f011421030405120c0a09090f0804060f0905091302120f100e0f0d0c060507090e0a1505030a0c0b0a1e03050103111c06050408 67
    0x5800302e4104002043c52643c454000b03403007103200d004079030b0348001016411a40c070700c0b00b10b8400340401a004018005082011503440301810000c1c8400c04480e001240d414016120007006000ca41c0081003d04c12850034841c01e0310b02c0f1300c4000003060f56400301400034131300441c18842c8503030b19a9030350009000d00c0580010240c14a0700701c24000d5403265910300040541a10100e02d80005501e950040f401c4e190400d00d480c0220000d19119048180680070002544a00d003008601889038401144428509000c001a800700d5070100050070640e0b190100d051501c0050344420310b80080e9141c1c0302c0746030000e540468040c1c000500044c07554544005a0f0103c0c03c4d60002452000088108001c48003a900502034040c001500711510b50ba64034241940c4000c54000107040000300b8106000b2180788401400842e00d0b80e242c4811041a600d28403500c071010304901800180e00d03880140140100507070009029481902e1002149445822000c82c0b16007116000700501d4480c0080f405000d0b5940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 484602374 1250 484601124 484601153
    0x10140306100e060a0e040f0501060e100905120604021504060903110414040b040218330901260714060904060504020f120606070803060d05030c0d050a030b040605030c0409 75
    0x40c4011303640c0291240c050503490307409202d01d20442c10240203114400031401064100c0d5016141c07000961904000c210018090351302800030450303146000602513443c03a005030000c0e0361000181040341814014001d450000300b1441c0c0080408020401007140d2000200080342c3c0c01003112506810381000083c00790801d4040b510003c08103806000501c54418031690085100301d90050bc42084030508000d1210215000b02040c01d05c035603000c00c040c8030104100000c200b540e04440352202401c00180a0718401e0b0000e00954164000c8280180741c02e995034002d00c4120700c0101070052400e591000815210642e09000d01008034100c10a0380302ea8005201401005100350740f5001c0301010f4103800d812201010403030321005c0f00411401d051100031920307025000080d0f5841c56594070140304d640603082c42c003200c0c50711080040d0041c0f11002d00590b0701064040c3c1c1e610342c0ea040201c200074180e07003400340d4030380c85185451003c0100303607030026892528841c166008941e4400d182060b160104c0b145 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 484603624 1250 484602374 484602379
    0x151b1a091011030108010b0f0109181b08040c08120304080a170108010c021501030803060d051207050714060c0706030b030a050102281701091109120a0210140306100e 73
    0x10410034402e681401450607a940c1d1402001091900410001c038800500c10391801300c0d020103014084100241d4481075404050b0368003192040c40c0c541610ba140103580350346000101301c14144010082d014a024000f803102900400c41391081143c0c1801c10b00c0701800c01040310303a000540ca10118001e441c00381407802c03c950781500a40c0d4682186028080c80c1c408039006008120002d03400c8000020164184c81d00502c071a401c5564800c00c2c8200c3c00c50141d819281e074031404883e550503022714401090064440c002070b0030303030750318200000280001900c1d1040c03041c071003030202c0c010981c1c000603032404585040c0703008640c0c1600c44020a040c1494440d01402c0342d40009021242403850013550480b800e0041103248050582c244101d0f0319040c9400300151401143e001040600300503003000c00700e540d44550007450896603000003600a24000381c583d03410340108440d02e0a5103030500e07000c0e038000454107104410514400540b00340d4030005103124461301d8005a1400641e200d01522a50740801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 484604874 1250 484603624 484603631
    0x303060f0a150206010303020d111c0c0203030711090f04200f0a1e0e1006030504111305100b0f161a0403050301290414011206151b1a0910 61
    0x100701d0000c4d02ca9409000a50140c840c042c0446c0d00705115200d40e0a0110215003c5c201c440003070706080c90801a114407441c06c0201c201c40541c00344e40c040c0700034688144202040410220202c0034000c00d000000c00070040d8034401c400300804915500ca600c00c1c0703458540b0f0441083d2940c800040c1310079903060412034108a00640214410341c0c091074000d40020fa00168025031a66002411000e00c0102e403c10b0905c121781c0c00c20010035003c0c0e00980d80181c07080704030341d00602c80b0602041d8402c000324410081c0303d407a0000c0c400914101c0000c44090400e103c20b05291440d5402c0d40c03d828411210500c07140c04149501d0410f002d00c040c083d50520783c0807140c4a00504003400c0c02019030700207010301070411400100504088503d00c0f91000050604d440381c1307040ca8507201301e001182816580c403074140f040c40700c01c00b12400c4c003920402c00502601c11641d06034205280004110071046000c0d1407000e201d080c00180801c40000d000f40400d1640000c1c1d0350aa521088000e08200c0f8200e80202000c1c01c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 484606124 1250 484604874 484604909
    0x1b030c0321051e0105040e0d0513090c035a1a0108070203040612020a030e070602071a18060c03070b0f01050f04021c05060103061205060402040b060a020303060f0a 72
    0x141c0306003140d46400640c0e9849044e0b42c0390b004000407512107241c000e03440d900c000e00080c40d56019401900003407100d900350380342c0d450b07441ca50070007910b070801010b1002941d100e0300b0001d4402c1040a0540d001a51040c1070a2000c40784001030b0280c131080782603039010b00c031019a144102c240b01c1c00400f0075400003406000300c6140140302480c03e030f0718420a5021841d5000000c40c0c5610010682d03046810942c0c40744501035412031090b0081d80110382c003208242e2204d034030b904400010848000100030a500614002d450708814030b605407101909400103441c02c006040f03903084907401452070108104c69042e0707141814510300b0702d9841001c20080c0800b03000c0c0104410812103616542c121403054a400b60120058020002240325440542c00808032124603c0d00354100f56000700c0c1c1c8204107043c005078458a80e445c00c040c2d8004050129440e41c450760400c001c504050040b204207a10623140e071804c007c000710000c1d44a000050100703008100001c0c92262391340d42c480d0307041c000b0401c42c65071000030320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 484607374 1250 484606124 484606141
    0xc0c0d050f1309140105011b080d0b3d0c0204050c090a0801020a12050403021c1115010519030b04080313020607030309140712150608030301080604031b030c032105 72
    0x200c4c88031001101c40c00036000041950007035000b1005107400900d40400c24856603181521030b0400b4a0042c82c0070754407d6182450f0b02c1c1c002e400b04042c1001951090f41450b020440350900114800ea072441c03010f80e05805816030f401540c9982d460394100d6020900d562031100307001c0e6600602e900503a0004481e0030001716520107600510b03080602d5a6031100111001030b00c04180c1c3e400365002001a440800d0369003140d010450708266492080c0742401c1084c001192103480d01c4803600e089806446a0070040003180340c90303407107031a80c0d01c3c200c1c3d1510000c610303640700c100d040000100040c0c81d0910001c001241030000c10300903102c050340203180741e4640b5030b203081c01402030010b039608448480c2d00c40342d0a1100c3c6000100507003114452503e05420003900da841400100300341034580314843c3c46a00200381c045003440594040c04ca41c0000304083c0c41e05050041941c0032464500100140c038000d241e001c00c1d07001c4214442d0030b0b01802c04040180e03d40c40242103928249040d592200e28100c280108e00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 484608624 1250 484607374 484607381
    0x7060e04020c3f0304020108040807061b09090b030a0b0106080709031211100908031311060c01090c06050a020d0e0607020d0501200f070210121e050c0c0d050f1309 72
    0x308540011050140c1c0000f0340c1c980034801a60040c1c0819100c1001800140325800105501481400081040360b030ba131300561000c09203c094000410407044007440701c02400d02c035031040120101c004203c090070940301c04a4048060040c40c1c100201c0c14000381442e030107091100300540d0701860794041c5181c8020000e10f1b41c0c0104000400703900403201c3d242c400c25017074040d500c0606e4010702141e245071101c22066110203c104411100001000404011940c07590064150300300d0250020800c80d044d03240010031400d55403c1402844400d000841e05c550740003e0fa0300a0507183e0a003003ca505100000032880d0103210f000079070201d83c2c0e5000000b00001074100b110301803140000d4164800544030800c0e62400707100d0201044120500440e03001d8500014100d1041021741401c0c040041c10402c0001aa20142c2145d07a0700c400940c80002009141d200b036a5004132038800c054200b61140381d45075285c0303040213001e0003000408500030501d150000200c1e00311001a05502c010603568284a0015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 484609874 1250 484608624 484608703
    0x4212015040b0301260706080603010902041a030d140414010c06050406060609170a080a090e09010504020328021003060810090204110c1e10050c1b07060e04020c 71
    0xb10308540b682c01701000036621600082c0d4580c2c01c0903042c100d003400c90450302c3c2c0307000a00d1a9807541d2126107040140e00c8500c031380401c4030a400c01201c4010780300d2003803500d003c5d04c03054124100800281c0915800000105403025200d1a0210000c203040200040720781e85194500500628981001e1104005081d03100710100c60080c0c4850050540d6006207003400080b11803d242e164010344001d4001a00e0f0400030800e0342c0850800d0703880e1130388031001a0982407044030101040da5544081c00194903081001c03250124002a00440701103c03a0513400b4072600d4800000d0003480e003910711041080c001e4100801402c250011207041020044220015282a080503030040d803030505426202d10143d02120040d405402c024200500440900740c02205111401500d50054014618000b00d2038003515020b1403003084c003e512051001070a1041d0003421040d0b004941c072104080000d290400540224503404075401030701c6000b9031107080d013030000710b1010908102107400710000603410610248a03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 484611124 1250 484609874 484609889
    0x190f02070b0306101110020a0224041e0203340801050c220f030c031a1605090604030506010b04060216053105040804212015040b0301 59
    0x80c010355822204840e48003c2e14000c0e0030404208454412038060100001c00303150702400c0342c05c0c07481c084049070102d82044482c1c000581146800c024038485042c9250341c403040c035004621060038260383d20381032070179040e09200441003022403103000d554051050f03810110002024405041c0c42071401d032144153307818844030f03000002c84040b03007100323051140d10311804410038102d1a0003100103c0005011350021103a10342e00d0050000b141982c05403a0343c2000b1032046488850040c15441e00c85140948103100712103501c034070010882c1503031003040700f41d01c441450304041c0c0d03035a10b0441c0894502c3c4213a40002e403540c0b00314400001d0040d1144001c00480700b07154240e4030b212100c841c3c000c13540e640c244100380e032151741e545100b00340f100c0d903164010b603141844241d940c2500000000c4030070364038119000c5d00c180f00046800c02025203000700c034a82c2000e0100845010720481e50360006051804a940311290300c040007500480e0715a0601111007c00b036209860326183e4652140030141e000340030f92003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 484612374 1250 484611124 484611133
    0x30c05030f030f031f0b04090227280b0c03070506060306071d12060a0c09090204030506040f0602090d06020a091d070c3207060c020109030b0c190f02 66
    0x1901d2000402034819600e10108011300d140c443c0c105a00c4850703100207202401d400359800009410139140014070003001000c9001d0b807034000d0220940304924100c0081607801a625040d41c90300d964994100b007202944240c0c0740540065100d41600045013a005044031110005401200d0a0700001412510740b0600854010350743e40428151035140c19a442404076681d00700300f2501a00003204d04442290180031090301008202da850300d058425103507114401d0341c41c030226040561088011004d000307140d10a614180c0b1316660190380340c038002d00151550b07a00c040740c44100946601200c1c0d107100010405019100141010002988644142804070300400e00000740c001900b0b01e0088058042007002a8643d03401c1c6090303404040c038200071160b02d902283e901041c000301c1c442c0d2401d40c540d0701480c40d403000b40044c4a41d103411160341204080c84811074000300143c3e030005000c415079600140d4000301c0c1d00d0f82190411140038580503460b002200c000990305d0280c0c00146044034500590845 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 484613624 1250 484612374 484612393
    0x906040b0907140d050109141b18040b030604290709151101150501080a05101809061a0f0f010203030610140a11070b0a021005040609020a030c0503 65
    0x44502501030180c110404100298507140561101640e02030718800e07051410801d0054641190401d80102c9191a9101c0c82c0fa1240c609128030303513a014008004012001030241d028911500810116090700700700381981c180ca03074450360040321500c44041d0480301181800c0c0f402d0440f030150795504681034801c00031038411701c45003414454025200da468941d0568107285104600d5045c80308601c1c10b004540f007080001203070074440d12000020007000d401a05040c080010899000602038648a50405060025117450030341224203c46c0402688102c0c82c452040d030b034002c2c110380d2030050b00561404e800e0034000001d4144444041a00303c03181003e00481030308020000046241031401a803060002a046003000e40d000000341055040020b4240e010a468409540c04125110300048031000301c1170248108001c210b0281c0f00090049050003c4c0da9002581d42c00ea040100e00e0b40d54032000403070144079040d03115942694004c2d00d8100301c584c5900b0601c0c1440300600c19107020303100e86c4080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 484614874 1250 484613624 484613629
    0x2070501022e0c17010b0306150403050d050714060109020304020a0501080405060f09010207020616060e07030b0604050a0f0f09020907022803090e040309052e0809100e0c0906 77
    0x1000032107420a6508800c007034540491030001c02c51210140c0602150200140500f1303044880503009001498440341d407440c0c060184035802d00707606014030301c1d00e8041c4420b000041001c559207801c1821460002c3e11052142450003010a01642c8001c3d240500800400c11202ca0740065220780c0c02504c442103010359600046072101b00c200c0d40500260031090129081d2450544141d4020255400141c10888103800040881c0d011403018040700c4e1840c194030f4100582d90251442c1000c01c9000781c10540d03e03684559000d140c0c0200503034405d42d0390300c0005698880680c80201000700b0154100820041e180d4044014146807078140e22540742d00b000100c443e840000c07d0001100b0010400c0c1181c0d040c0220103910302c1030b02d0003c9060000c0c2102c041400303001d1200403441070f402640e41200c024035103024068000c0e40030325146180c00c21020a00c2d034060300c080d21201e520342585021002551044050b81c10840b41788281074200b81024114100780c2d80008080d00c20140c22503042100d80c035141d04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 484616124 1250 484614874 484614913
    0x30c0303200606101e02030d05060409020d0803130b130c0e090a08070204061a0304171809060102010608100e01060902090f090403020102070f0f480f060207050102 72
    0x5418035840b000000d0f0441c100950b406220300618140340c0101c02c034580b20726951804803162100140e0011490f640012402c0c0145034019005403810800c0d15040d4000ca045032200241c00f07045000c0010110360068000441c1050058021404840ba81840180c1d00340710f102d40c543c2580c001656050109440700001d01c90360044888900a10790711469503202c10090f00450030070380e0b00c1540e4100001e100001c3d031703c4522052032010030385a03480c40c2c00d141036070014082d20103e0540c0704041c404106d00500c2c041d140440c11100b01c4100c000713540c42100407805440a504510f01501a18201a044403c0c03a003000390840342c444000e101c2e81d81c07940303202e80c106e0141020b00d560145804030703904411f00304250013a03046402071001500e000c20035100e07504035882038241180c11100801020080c0722031f400c40380f1005d07030144080301003032003600004165012000076681c2c040000d82d41c020041400028006005040c0e681e80e03c0b00d49540c424002c1d481c0c01507031060f64094090308040b503c01d040c9054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 484617374 1250 484616124 484616177
    0x9091e0c07110910170709050106030204180b0a0501030f0e010e011a0405061005031b041d06100903230f010b1005030405070b0915121005011112160c030c0303 70
    0x40343e0000705454445004e105d404030f1515001c05000d02d19000c12101a64060b2501a0000303840140c2e403545051030071003e111803042c6112041d460900c4200042e942d103040602150b0003440c0c0032490211070b0f2102c400401c80d4021002040d864803281400402064105512056682000c02000340c0e020b4140400c1d5039040324407550110105801c4e000c0540207030003940c0c000014002d40c1c1b2032103140d0703800c5a0456001d40c02c06929071002e10070300c120708040d4888841d03000360300b03540414aa01100304e02034083c100c640002001c0300c2e201e0007452214401040402c000c9405030084940d03070060031046500034a2100d038002c1c0501c04140e2f41c0c8941030701540c1100c0c00380d68048000d104242c90401c111a00c0c4e041007603003550019030300f4a065907e000400c01b1b40280c070008040001641004800f201011800341c0c0824140b210700c07003c48644000c040f60107103899407035101d4542c0d214007140c0c081c400464a24401407000341007001c0442400101c07203005080c1c03486521000309114086a08440461262 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 484618624 1250 484617374 484617391
    0x130b030a1b03120c15020c1b01031b0801050f0102070b0d02030a0605060d0e15090c06070206070c0b120c07080405211e01050c04030809091e0c071109 66
    0x102a52000031a514040ca11607039001228100c00782c0c4035650800e43c1d4402d070100c03000003000400c0007014010703403807000c0d00c15403030000d82180307030a03e120601070301d40070388182ea1901c01c400100510100d0b4003a400050108400068084403030b540c001000c0c0c0710040078000c0038000e803840030141d05a035000140900580d26080b603960304058101c0b420901940c001400c810486407503840000e025159130001e01802c4a0000010a40c6042d01c8042450014200c940c61030000c400f80500c500d0010110301c0306a1260700382e507410340d21105800070030b01510030007400800141c00002e0001d003026034440a01204c0b101c0c1642400c1c0b44d1151440c0b0645030207454400340002030300304005c11251800c0c100c18608002c4100640c0d000320403401d6418100000700b200e169141c4007840030490440801c4c440c06070b1200c0c14542160074242540c40c2c184c0310380070f20780200d8050300800d40440c0003141401810782d0355120010a44485181c0845a010070340c018102c00c4a49010250140d001483d02026030361149942c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 484619874 1250 484618624 484618633
    0x908030f130803011701150302100f02030f030112150606080606030402040b1513050105030c0304030318082205091311040b0301052403030c07060c020f04020315130b03 74
    0x88500c05981004054041c000079201440d41034000303100344000d07500910342540c0034050701c41c00e25200c60940c0d41e01004103450000c0c4002c103200503503810301c0783d411144491031306002100401000340e06d940f06080301802c44034008000001c2102440804000d40c81c821000780080003035003e040d0041d02daa5015840105001400086c05400e184000e0742c0d00600041c004540000d1000101d18100614070841d400024005150080d40c500c01036140b00520080ca4046d2440c580b040030300450b07000141004080588981d045c44900c201180040949d41c1c1001d0385c141d6414181866040385188071600e01c0030745800c80c3c00041d46240c03d0304400e1158168581c2200e140c14140e0701c58211941c2c81d10b10a600c641e442180000e60345092081314411100100032010a066070100d801c90401d542413010701c80c1e03004000022620030080741c0d043c01c0b00c2041c14181400042440042d46010844021581162001c0108001010480ca21103185081907030851001ca070281c3d211001d0f101da240d40940c05622 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 484621124 1250 484619874 484619881
    0x70311100504240c020d060608060705040612020723071a2802071806050306060f1f21050604060603060506040e06180924040c032a12050709090803 65
    0x141c083c0d0166800c001403034000303840b444030703800202c80c1310b501c28040e1007090b510340c4c00340300c2c051003002050381044450514030305141ca4480c0003401090050030b000c010a030042000401c2004501b5448030100040190f0322110554182440d40d801d018414825100d202c050307040c4008200d04d007210480020301d04485000841c11442e0300c0d0806400175a942107100381d40e400208608425180e184095030001d0114800c3e19090415190100c0074104512030b0116007202005559038403c0d200f0110003aa0325240300080211003981c2881d50700b80d040c90702242c9500c050074402a81c3d8420380c8904801c80d010030090b52500000c030b0440f005070103600d0308490100f00910040114010556008100030300c180880854000f801c9071600c401d40d803c003072170703448440741c0709603d204895025081001341410707080da4500b0380c465040b0b5510034840513000910307042040101441d9604814030004646000c0b1034115038030400003000219181c0c050340c017406180b10100d00c00030213000e1000c0c0b040d04000107505584 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 484622374 1250 484621124 484621169
    0x1501030203090705100917011404120504050d03091d0f180a0503070b0f0117030409050a02160b090c01080103052d10060303080c0304120503070e03070311100504 71
    0x1480540072034114400d0f09000100c50340c8518001d14084881d540c0c241c01ca0f45050044040580091b40442c0d01d80d04209040c0c41e45925000c0199003e0380050028040050902d02902d0500c81c54121681150107a13551030140343e00560b401003200c800e81d90802800d403031403400495154050b03822008190b880300c0032a00c440c907411071600c0007501e0641654020840c65982910310740c410b80c030449d40344400e0810014200c040e03500190040070150fa250b801c0410345010740d80c491003a4002c001d1300350b60f16004a014500c2c940d05072504a0200111121090810f041c2000c00c86003c50300407001b80710301c103c541c3c500e5104106160480c0e6210300241a01404003030400d0001072620031400c0c0518030f003102c4800c00c1604200c002183c40a51500141d92400d6040080500c0c01c0100310140c800020814000020440a6404250109494425200d071603880080350241d00314a942a414414001d01006110030103401d84001038040300e902000d00c1100d4403e8a150051380315140c50300781c0c034410080f90350 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 484623624 1250 484622374 484622377
    0x604030e01170a0e06070c15021c090b1b25030c050a0b01140a0302060a03050c1308010f0c0903050615031c02061b040b07171b0a060501090515010302 66
    0x305050411008841c0c80901c01104407004884240c9040d4850341014500501801082d821060a140a0f0107040d440e07120178540340740c0c854290b000c0560004070103030508040400040c150000780d00510009000e803d00c0100104280c40c0d402600103800d0584101000c0b0100311005030b06486020310300c820136551000400036124005500b449145001304001810900129545510542c071261103541424000c0b1110508145842d019444154043c000b42e9a00c0c0140c40c1100180c0c82c01141c40d03560110314181a0141341900d5403040700b5850302180944040d01b01c040c00b480c0c03d8004000000d4400b5040700d0100c001d22024120750010f102003000c0100d891900c030580d81000d01221580543c940310b0700c1d2141000360310900160400d4041c0901c03091b4403454075a4005482d01006e08241c1400c0e01540280708111004040500031200030220702e03002da00351246402c1c0040c48410400400346c1d42a240c00c011030003101c049142600210b000265841214000d13078001108100e00c00e130800c0150001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 484624874 1250 484623624 484623647
    0x70506131214120c1203040807060c0e0a1811041202060304050111030403031b03140c25061d0f03090d03050904090503130b0c030304060c09180204050a06050a02060403 74
    0x4103145400410003560b4100b00601402c3c103600301d90fa41c2d401c004150320741044101c8588041100e420003d01020800503000e64405a411410001d90620000c0064480140c900c0859800140e200000070705030540d600344010b0048981c034240019000d00c02d900324131340b06038080c40c2c12080602e03808801505240021b50b83c018881e100001d07152841019260281e04115411070000751100c1c1524506a40105010369090345420144044180c0144a00800100a151216130f0b031020500030070800304d00714010421007a40f1044465500103041c608c02a100030b003010030144803801e40401d204000007554400b000c2005001c0c41c182801f0904002055071000303029000c0100c103209443c403550701c0d44075012403c1c0c8542d0003559105c64945103124604a00c0d44110300c1c1400610aa1407600c0d40803045a5125500440000e003040081d0010349207031079650002c0b5019110291007011100c81d90f40200305840c002c43c0d81140c0d25503514021074030303841100f203c000103801c0907000c40c0000303014400c034080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 484626124 1250 484624874 484624883
    0x120f030309020a0b030405030d1404050606010e03100204140a1a07030807110d0c060c0f0206010b070503040f0e010f0506040501020c0d020a0b0d150f150f02010b04050c09030705061312 81
    0xf0b00e40e0740e0079140e24103802c2628180c40a410008000000c0d084078811a811803206151047c420b190948441d9100c40700200b07114144840303c03100500f41c1da001d001525850040f07030400c41d101d64603200484002014150894062120031074041540004075801c1558820540c3d011860710745956400c030384210000d80b042c2c041c848414440f000100c0705100c0e01e8402600c90303455003241c05060606106a46141030140d0034031145801d061b440c0f550102c0e50324107407100d080c41c9684d00c05061424525501c1150300110244003200710128070b8100c102d0805040741c007000408604640c6031420000f092240717103c1c40307000d03a201c42c09240031400c01a10040601d4001044178004980c5c40120703c010f0f620a22a28040c16940d9982200c15259440e08002030406844800d01c024104140c1011101050900c1d8051180041100c0d4800e0703c03d401420344218040d0080c805820280001600d540106142e28800e01900d140032946081420a80319010305240001d11031914003d01040a006040310a91307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 484627374 1250 484626124 484626139
    0x60c1c020a0c0905070f030203150919090b0f010503070f050915030f030a030e0a03091a0c011a040e2d010b1c170306060d0209010c0b09070f120f03030902 68
    0x802062640400c0c0005000d50f15000c1014600044010a03034800309441d4024588180300740001c11054002c40300540742c0aa0b0416016142d17100c1100440790810101116281040d002c0380c108412a03006038000d2103010440b042c2a600e44040640712a102e00640c0a8842142020000d902d0000015a000b00e210b80c078a000d081c2d18a404642004940000515154000070340740020301c0c0c1c07500c50814954000700c0909140c0c0010340d40100303e405c80d481102e2090108120281041c50700c4403c4a0741801001c0081044030f05400341e00e02c80c648201d181503c298640a004a004440402c000440c0021140b40e242001c5010460b0034420300808080c00c01c40d0360303070446810a61501500311448440c0c510100200003843d01c3d0001c030781d096000e100801c0342c2051040c0305807a04e41c1f0040e80c80c1c120718030b0409a03c03900c7c04801203c00c0c18440b400a450000080184074500c8008075101055030580d0720f44440300381c0c4600383c90340140444100108100314a904c801c021a22076072142c0d050910081440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 484628624 1250 484627374 484627393
    0xf0904020d02031c020c0604030b070503041b090f180b04170706050901020d0e1b010e2d03060717271219031e0b0a0503010f0e0c060c1c02 61
    0x84c41d1002d011099120b6010301c0080640254042118031010501111a140b402e41907075100c00800f50060720800c00c0c0711010010408124904490541081300410303440b4450f596071500c1d0024180c40500080c0c00d52400000f2103400b0f0041c0b5600d03098031f800c0581e0060548460355005640e00c4460300c007001e169024044640001c00b9806542d0261724041e0000da1250880f42070701d41100c2200c1404041680810041c8220100d800f000e0781d40c480c0c4c2401d200702e5481c800d402050034050001c032000680305c0300c000c190000d40070445c50104142010341c01c44030683d0342c2d94416142200f4a141403e6910803240008451005071030940307032004042901440064001d203e0580303005c1d2400b035000084280450700c500500311f607a100b509240b0291605000007c80c01c1410000101c0a03541c1c1d0700110340701d000c1240c098541d01024002060003400800070351654901c801c0003006074008200660003a01100c2ca61340c41c008050f94441081c0c0c82c0549503a0700da249403103900145080c140e109502480190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 484629874 1250 484628624 484628629
    0xa110a140f041e082d030d18030305090115090b03030705010501180e070f150c0803011205100b030c060a021f0c030b150f0d0212090c01080112020f0904020d02 70
    0x207007000b00964201140507100c8001001c01e800707201d8001d4411684408104905c1c010019420440c0c0410040b980e55040c02100040e4110701c6603010040103e030929400307850394491716800030b51160081e50100708a84940d46140d00340d41425000d103450f01883c0740c042c00168516400b880086100404681c504603441d600c07142942e009034448501c0380c0f181040c820300b299050042c420781c2c2900501501c1114200980c070186040300e1301481c1ca0002038040c01110709400740740040c088503004202c803a100d6075a2030b1082155003001c2c2d401c40d141d0080004040301e0700b40f98010000c990030700a024000400da41c1d020b00245801c80a444030440c4203404406042ca20f5030307a1401c940c0c04a80e0300200710707001880d4001e02510515003096029000410460111400501c2907500c0c81c1c08100e6902d5440c072541d1903d0010340a0010100c00302e555010900107414800541c080b80c401080e02c03001440d03aa51040d00304041709413840690450f1805585005e40c0c940054010350140c402003100c18003140729000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 484631124 1250 484629874 484629877
    0x1140f09011d1806010b030612010f0b04060b03060f2404030302010c0908150c030703060512010606020d17010513091a060108090a0512090303040b0d050f0a110a140f 73
    0x1141c03124880282ca05402e19042e10343c1d40118410000c00d901c0c80c62540b01d581d520380510617401d40e01c1012000c07034955038403c9001d08845450b030000b8170402d00610001d01c010b000d1114818419860700070001500b1403e0000e49101d460001c00c42c65031192801e00740310814504a0000501002110070a00c03119800e0001e0310265010364000200c2d00d04982c0081c210607041e400c00ca003154058000a001c0c451003889060303008183d40225601c1c2d845000d03042e00034001c9070704100d603c068082c200c42c00381c180540c415400c8804c0d59084546044040409aa000e0310f01209800000a44001404903083c00800000720311038503400020741c0300e01500c03640e02810031404c40c20020201d0b00280507003580c0c405000e40e000002c01014061540c244d6036425030328801d60440c50403901c008518490349540a0041d01c2c014036032840066951004060034100602d02114410501c0c0076400200d84041c155100c4c3c0003a452601a0b07403440d03d84122800d49808441c0551029001030402c520f00c45d19a000c0c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 484632374 1250 484631124 484631129
    0x1b030103031d0f0d1103030c0a0b0402090a050c0d091502041706160203072907050c0d02010203070f0e030703150f06090207020f1012110a080603010606050301140f0901 74
    0x141e600303992a040302080c1c2c00c4031403100240d92080c0c0740542c07203643c250b40d88452460641da05c000c501400b01051000300303040d402601d01142e51401218484428000403402d441d22507171080341d05d40695074461000c80d0803504203560382e800c1e21170107216040c003100c216401158503a009440b0b141900c24151290000d0364095000f03203001c40714071458603040000c10410b40d83c0003501030009842c20040d500c0000e50300d010300380010b802d40c95812000d10894048000d6646881c00d076101100552a1a0f030f03020308103030303c0050702c5e00b49841a100300c0100648180f0130f4a0094240356501c8200410014044545040740300341c2c9541802014400800900402c140480e19001000c01042d60510040e0102c22540660b208503020b900422240005a4405108104400c0d0480d1101900301c80550210340604003044050030302840c02203900700c1d210790b50019000c150003035540c50842d550303140145420395000e4450355010420030301c01800800d18691240036072500140964035207034449000125220000c1c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 484633624 1250 484632374 484632377
    0x50705070f0320030d12090c091b0807020307060e010216030f0905030313030b090f0f0106090606180920040f03050114040b161b0c0806060a0311091b03010303 70
    0x3410410406854070b03003d21410224042080102d41c2e2011079100c0390002101d004004120707410707055800c81a0700461030250041d0b20907481544600745032000700b81b2080d05500c0380911040d2500400c0c46070002a01c00e0000e940990706242c0c0315959000501030f039440001c0c480d5002d01c0180311a1a078aa400c01b41d150103560f40b409011404d07200070301900125003110307000c0d410030000c159550512038810000c0380d901c03450003607160b91110b205504011801c0110122030164980d080d0b0346010540080d8107494215200b040603a40d544001c0d100d1802040e078508800c0085a010069032220344e00010301030101c00040c600c03550218515402c1a80a604006540e4031800700500c00e1200c24030654000b0040c050a080e51802d2a442e25140d414000f80650010150303180d0080c41d25104102d40d06412411000c414903409041c07511903c420014090f50781940f2850300000e4442c44c002800c0011a5000502034101c1d0000ca0244408110020100300d2181c001f038184901400c44070000790b000f180039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 484634874 1250 484633624 484633649
    0x6020714181509070f09030f06020705030301030602091804120804050f100e0601092009010228050105070e0d020405062809060501031a0603040609140718020c0d080705070507 77
    0x310b010004044409000407041003280e003c280740d02c41c0c005086009903a0042280c0c00380c10602d01d0325502a00c10100010120b000120001040103450340182c060b0f030808803043c0380d1070001180044001ca008640142c6100641d03000041b110b405100c059420900510681e5190108103014914105103442144074090b5503420211b03d480c014004d19014280072131060100c10300260b509500715400340000c0401210005201c0c055a008000320105c0b1102e030950248040b00d1041c1c042503007201c4210a89055013407200240f10207110740b082c0000b0102c0103240c0002c10301030390244801408020001a0001e00c503201c0c0c01c07820000c44410003242c11080c001100c00d40c1c00c0c150300f10240c80203680004d060506003000450700380c07940b4040e60200041520995180d82d10b5040c024081c081d03212005d880c2e24444d609a40a8803004608c590554501101e8800640b04da110068101d01c121103241d41e0981144a0800c0380038031582d051034010301a07140490400d0115220607040000079802078044224 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 484636124 1250 484634874 484634911
    0xf071b02041e050108010603230c100e01021921051204080a170708010e2701020d0b150a08091006080c1f0e01110709060305070501180602071418 64
    0xa00380030b40c07400743c44c5240080c03110a00e156950703164590300340c4518446810709e08009014090800480f0300307a041c01086c1031142001544003928160b2641541d41c010300a0010f040c2e4280144a5070504031544850901c10300e070b0400d62840301d048410100c0c0380c10071800300000b02040c014941d84a01560084031700c00d607682c2e031001c00601100704c006072a000c03140c024801c1090b0b143c2c00c81d031a5411602c0b2070588220702ea80d00001b003c861462003001c0fa0709080c00c11200c0c0d4402005502601c0e0341d0600072020040c010100003006890061450034808080e001c002c1350079018420341c140c2d074015104904441d98906e4210803070081e51400c0c2c0100540b6072286100a2103458000441c142101c140c018805804080c1c0400400440c405003041c2d060001041400c08507000410260005015501042014646910f405500d440052041034001407020035a23000c06c040581048003110015002041d4031403910390180c0402c0308004195a02c41102900401071a0011100d2786c400d80040300d0960581c172 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 484637374 1250 484636124 484636181
    0x5100e130302120304110306040b0a0b01020c0604090c02070e1303090b07051005060102070b120603060105042f0f0f1e030108070b070c0b04120303060803030f071b0204 74
    0x1000411000300c2890040151001c240c02244455181005010032581d07680e8a00b032080604040300710365500b5203d0340d42000705000000e40c10a0080c58222401e00c0201d001000490355880808021544880c040004001d40b0210782e00480d0b1400b400d0042d94105540c480d004400c10904964000c0c284860069400405a01c550100054a080404036007480072645505980711443d0316200c0b00b90740e803070f00030502980c0200600402070142c07081c420380d076814110580d49491400d03120203009100703003000825103140c180241d15010100180c1c4082c590b29820300010b500c001d2128024403614200a0107010248a000910922040340c541d142d44007032000b42038104802c540c010610352001031005200200010a000302100c040341c3e00c2a880c1c401c1c80c2402c80f00610203510076400e648001400080781103a001801480c1c501903142089620307a01c581d12500c0e44411100ca2200700e01ea00700242103113000c0c2401c10104030151300c407100070100647c003040440e40008103680201959022803035204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 484638624 1250 484637374 484637399
    0x20a06060504060e0402040e0f030c030901090e06090735010e1b030a020913020a02011b021518011404030e04060504020405030a0602210106080a0c0f210209040510 72
    0x1031500b65402c0240d1483c02119014074000a00000c1c46580c880105061400082102080305201c0c0401c0c1c6c0c0e5109801ca4405079039a200c0030b850340c0403403111a8001414101c000e002881a400074201c2000381d56a0316003110940300c0c4a81c0880c0c09004d224000c030305440101182e820802a407074075107005505081540d440c0c0b4a00502d2880d01283c070ae07660200b046401015260040710700980581c64241c4100040e4809525040146c0c1c2584041403110420340d054104031118000d010306030716101030340441280c40f100650090808520082d001c1b403025841d583d288404c200e480c200015040d00c07520070300130380a0010398046d0000390b00404010300e0b51415100b03083c000c00d0120b5003140f40900d40340c0842c0e103405540c2409489a83d0100702441c103c001d02620000c40c801040c03080402d503840741c4018000e110b0942c0c0358409946401110300c080d0380a181001c805041c2602c8050090404045110500308050182d50059030280000038458866000742401010b046002c1c018150801c401c0c00c045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 484639874 1250 484638624 484638629
    0x2091c15050c0306030c040c0512190606020d021504080c03031e0105030f070e1e04050303150d03081302150c071503150b071e060b010f08073c020a0606 67
    0x200804109004d0103030750001e0700012803c419240800c59803040c600c10344260152156107610b1944010401402c101c109100301880c90300b43d0b81c1002640d40310744040740c2d11000c41541c82c0c09a4800040310310049601010140e0180c4100740f601e00c0c00c41e055102908503042031b110541e00d00c0b4040d00070a0000e083c00c202070301401095000302094082180220b076100d040e441006130401c0003d0100300001d003041010040381001c0384082c0c0140c20980380c0a90b0300c1c0d104807600300d15015400c1803100e1500d4021003204045425694680c0561220b40c2482d108600c0f1810417688003640303050188201d50542c020342640d004460142c04824500100d251114140b1303860f500c10540b40402d8a416030700d0040e07020041d954503d4225807101031515007209481406a06110002207954821042010541100350a080c081e40d41c07d1082a40780f0040d0388040042d94070b507000c9800b04280c0300c603034023144000c866903550202c01d00501028484081d12600b0300301a20800603044a282081405450300a0500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 484641124 1250 484639874 484639891
    0x61205030a1d01021e0106050312070c05040902090c090d050f0a1e05031603030905010204090618090b070c03170408031008060f1b070b0106110c120d0302091c1505 72
    0x118002d4000000b511901020441401c014820400049510096200340080e1001804032800d4040c07401896810760000e100450340801e4030440410107041031300070074502a5000d03102074140e8071903d03800702c4a03407c100b0766039810070f414028080224508025290a1141c0c8102410101c0c401d4202284580c0d0003404150220000242d01f41c00200c0000490b045200340741d0014107103024502d000c4024180c44a0064403541c004a030120b14400103031b201c00d0032500b43c510201d110f003266a44000503038140c0040901812141000a12510700810440e80c1c0715200e0b00c0c045140c0307220000100c2e1254015101900c00f01004400c10502003640c01c3c00c80040c2202c3e4000f0640351508000c8100c92600c0103080640603580d01250f102001c5100c000e503040f15510281c000f800b50303120040242017500300c0d5100c10f5240704107080007041d0306102d0200404100d40801418502035141401c0c0d020358041e04246070003040041046014003124080e92054070b21540800014a540c076805500342d0303102401080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 484642374 1250 484641124 484641167
    0x40e030306030303010611030d02180a060c02010228150c0f08130201051e1605012d020c03040b04060e03150115230f0d0e0c22061205030a 61
    0x41c42d80c0c0002c140d904480c524a03100e107100038002041c1d41180510070070705890303e00110309114a960004110409003600303680000740c542d0340b11400c851074040000c2c0a40585c0001144203c06907440c900800b600b091244001103100c50380e5aa845403004100803c060181d8611506408a40c0a41d1020020486141640311030404085080f0a4501280f0003418001c0c000b41410603854821f8468419401860340992106280e43d448440c80c403990303500711143c2d440c01c00569417150014220030b0f601c580c03221020a4649032500c046009501c40090340803d88070034040010350f641c1c400000c00140007240d07902408228003505041c600b069803003c41c10350b00f04120041c81100c648a85454451200d46440031600c0c428540304164071403a459039180503200055416890800a0010240c901c2280340030000d8485110005456a0851064603071240c429640c0010311116110700f51842a10044e000403030998980d40d000d00700c0710f440021140b0b0380006c80c0e1000d415802095210081c1e6540c60100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 484643624 1250 484642374 484642381
    0x8192f060c0408030f0a0c080c0c0a0b0a021005040f0b01150305131205030a06090c09030512041202130e06040c030209060a050603071209151509090807080c03090904060209040e0303 80
    0x59128081d07003450170010750000c24112032903071098008a13030880d0460203003a9118410104940c031542000e040f03030300411080341e00141d4048041c044421030455540500b040002d0030305690044c01010f00140c5142c804040200041214607510b40c0c005e0410f00c000700f61030b900d01d140140998200900801610346140141000311b011400080070a034068130346182c1e656203143c2d25000902043d000070740d580d4507040c4105081604982014260790080044641c41420300c0d85400f80c5105078020342c02c80d403000f1003d801c01800d1800ea01800c6628010006c03030b86d0201d0b0304171b591500e0b101b21000d82d1a1b0780141020415801d0194859801000a45082d580d040c2040089010351002910080801c401c0d0201300003004002d902c907842d9182c0c00304050f00e442003030541e08005040c81c925201301036910b03100005681320080c4510080035900c5111681030103220340380c902c550340120350081102d01040000d00c400f40c0d16183d81030720641c800c60340140c8420030b0700140004c4491050211042d5401042130 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 484644874 1250 484643624 484643639
    0xa030b0108011e0e191103092505060c0703080a05190804260c062401020d020a0305070c0503012301080703031b0212030c0c040b060708192f060c04 65
    0x240f094885410000e02c0c81d440d01900b942c0300301c40c00b80f260003d031440e001510794406843c100460251a946049031f0784601d10301d0a8001402999550140c019010141040b9504152025003500c3d1862404e803103400e030382d03038440700007651040801000081000818004d039810031808560000c40074a0980c88030f16151703444009041c11001008251502e0391210b480300c10540084174085003a4400b0380c5c42c14106002c40104c007082c0540041803000307011240346200d503c00105801503100a9000349080ca1003a101565a64446070007a640c401d03110b003002c00c2d03541b42409004200c6610b03522203807080b803004450040c0b101c410303000740703a0980296008201180d03000b40404111181c030020403c00004a200040f10441134881c468454000411a182c80240100e17920101d0141680d051001025600030820180300c3c444c0c009000000c10300040d5041c0785242844085243d007820031840070114480b116a014004140101000c5001d00038944004024800da540203403581c140c10741480d090064 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 484646124 1250 484644874 484644929
    0x32a150c1803071e171204030b0c09040c08190b130b030f07061e14071103010603080d020c1204140d15050c1b0d020d0e01020c03030a030b010801 64
    0x90180d105110401c00000359001d002c1c00000304442c42c04070507024041c0180d0b45001d030040c8900c0c4540000040c2c030b218001404507100c0798082440020300d00c1c1c1401c69907100000d01001c2c4c20322260084c18003000c0080c0d200c030b00c6840b601c004562900c8819180c203280d50b281c0048a078009082c410b042030800d0b900d5444401c95080102e00e4800085110078001d404607190011b001d0f0b03483c46901ca0000300040c00e07070301710400e0f65089103a82c8800d00300407031080b4259081000d03200c000c00c424134100f181038089150a40304010860004001050032a501e0b00c2c3c02169400c414445000c207030340003840e0b032081d1408009250240300c440c0c03a99810b16241c903411500c100d03584040940103d4841078604e040112460070850b0513920b0f49003c1003642840400002c0c150011840501c4111004c0b40c00320800900081c11414904140e009220742100b491040341c8010a00c22854194450a6109107035554107101600600520360740004060000d00c00041c03201c18180d00c01419080c02e0800d100c50103c082c403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 484647374 1250 484646124 484646137
    0x10207081908070512310303050c0f06010303030b0112090b0106050f130f03030f02010203150f0f0603040b15060a0c1e020d06090201090506040f030b040302032a150c 73
    0x50580307128415810500c2541c400c40ca0020214060b010f0514940283c003406060804d0b009140051000d09110300d800050b144d5200341c8175050024003003000081c0c8118002c08155005400740c44018640c0302c03046180c04000e030000c40c0882d40b6005841d4007542d200692059505110106010314941521070340b20104041c0141c07410800002050030741380b000e101c1102d00e00310300c64003034403070840d5036035024495071a2901084000404039110101518414000c1d030b030140c0207a00000440c60b0300802008014000740442070340052030943c10350744070f83c0ca48000d18407a50046401501501c1c0c40580946403e02d6100300c24407502003480b0801c00254040074031a4510751094601c2148041454001352072885d00384002d52001c9120509400c00030142c2041055034401c3e00d40403200c5071150200309040c0100d02130710201d901c40748010001704d02d050086c4e64101c1d002e40107481c0f82110162130450300c07d1000d00e03106280c4c2c00f03242c1840403540d0100078290f5405d10030405040c0908001c00108114070900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 484648624 1250 484647374 484647403
    0xa0212060d050c100e04140708061e030d0e040b0d1e0c0506071203050a0e030904020f040e010e1e07081f08030c010e060a1406011209050312041101020708 68
    0x2030000d102000800c100103003e042d0010700c014a051001e0764010b05040c00c4031915030042e410420082c5154103086ca40c1401040b00b9100d00b0794607641c4100740300300d40d00591004200064043ca042240d074806010245089400c0e0740e5880640000000f0b010a84912014050085a00e880108046410300885108201d00c840340d42d41803540c00c0c1014540340c0303066004a54002000140319003045100f40c150b210701030081e01d0a0100796541d1090720300b111601c12102030180c004110200c44c514082d402001f0403104225242d041607111045c81850714001d070420000004440d050014064a10301c600c1801101c80084110300c2c500800c0003071007000b02900b00c803030a800c080510254903d11041b00030241640c0c40403244c40d0800014100d001e00611f01c82c402c007501030740000c50400c01d101d00440b14121002080b000958a0f00c03001158100c00c4000300030200d80e5690140400a070041c40240480345c40b6910140031800d090401001c20007443c1062810355001d200100b1601c0004a01786030020b06a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 484649874 1250 484648624 484648639
    0x81902150403050111090f090c0a03022802010603051c0504030602250803070e0627012304440c0306040c030b100308031b07060e0706080a021206 64
    0x240c04010041c007850700001c0043d424080000306103800b290140c0b0758010210745007007008000308148255500d040e0b49641046c0d204100f9400c149000e90024003105200d00c0d00b003d1106040010b203445d0044081e00c1d01c0050751246020401d000d4100204a0741c014404000301c0c08045c2020043d20921842c40010300883e00030480d05000380d51005901030345041e00f00003c20000350740c03406e1702d5560710440e1920042020428105524240041910b0404a20ba081700c240000110f24102098260301a168100309806011490064512034040b0040291140140e2918107100500c040b4901c580640c1c10b0849204008840280041080300300d5000322403207401c50108400b40d5203081440301111f55405100c1c000500c02088445124001100d0144420000381e440e00c215454942429202c050420103090010074401601ca070000d030744c480d0101240c280741800c40e5851406070f9200100304401c076000004100b1001d6004002c3c542d00010141045107010348043e502e6940350300181c01030780038050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 484651124 1250 484649874 484649899
    0x51819050303030703050906010807030b06130b0d0f1703160f140c0a02040506010809031b0c090408182d040b0301060e01030528020603071e030204060207081902 71
    0x95028100103410003030280c981d01d1410110107400b0301810b4404504501c1680d0000072401d0700401c8907400d981d48045203131515200e1104004c40c0c038003e40c0001104039a03c00c07410f40d0a541d07586508a150b03208068112400b082418010311200056180c104440790401c104008600420418540545d071428540c00707a00235240e084440c803400101d8008a2140000c40c60010320340042e016440740c1c4200c5c0c0902c41907440000454082c001030b55201c8ad294403d002e00044030041f00412424003c0100c12203100c02041e100141d44042c0680b002d44121100003040d2050203090503203020010015103880700381240101004425007288a40c9c50030100c1d142d02081101e0b80ca1f60840440400010020300586440d1000380400ba8020300c41228248180900310f0511403c1b814000c00b100001202e144041c5056000c5c428158030003020b58081203aa414194101c0003011100d5001e44080e6a0040e156400c02801070320b80740640d0000780c1954070003242402c050034480fe840b103178290f040c0c03400d81c100c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 484652374 1250 484651124 484651159
    0xa1805090f01020318010f020702060f031509070804053913020403030e0102070608090d031a0a0e011e080606040e0f01050901020a080a0c0801090b0a090501080a030207060518 77
    0x741001d0060500c0d4000030500c2902c03019130302c1641d01980da00340204012050070090404a1040b801c00a4121800348851650000c40801031940001c100c908000d52402400000301c807c0070450309040450780704000d00061140400001c4440c03203030a40340f00100ca00c050703124003000d6107803000d41c43e40d05c0114040030301d039441c0d070003840c03088642c445415502c0d540c492030301500380c3d142e084040d0300500c00c003d80010540c1c400c00300140500a43c0025225912180340220b016020005500410202c610030f041c03004c2d1580341036400284031880c0035800d107504003103200301d185030342046050305010418814840c10394041a40c83e000101241c000a1521000d011641040062006004154608800c005880d0419001004003404540c0c61150300d0350303032900100803a0840e140d007000064903080184420400e9a112100001004100039074040d55095910182e5030241c002d8410b64100240400805404026581c058001400c0c035034106260f42d0a10001800000c10f054414100c0c0c0f0550061007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 484653624 1250 484652374 484652383
    0x90317092b02060c0d2d05070609021305070e2713050d030c0e0604121b05130609150303083909010e100c170d020c1006050a180509 58
    0x6030302610f09500c844090b5881030f111045105080c0c00f04141030507803065a4445149240f810802e812106420030b440207080f50607030003284046594668600c81607025a403020b9025000c0200d08602103420720300b031a801003d0704030364580240030708080c50001e0106c2e0220020703c0001050204495000ea6902410b83c0d0000d0300e01130051b042d0301515508500b0300d45d02da00548140042520b8008203940307842c0078030115108522950109107070201140300081c0b100c091b8194020041c6031415100c50b103481c002424401c0000d103801e82c07150b444904208100c650702840a400b8000b0358041100c62458038040c0080700002c200b5a405502c40802101c842e0b1290614034404592007030003d00003002500001069002f01002c50205d41000010850f919001040c0d50880c143c640d03856040010075518a0740c041243c1d481c81c1d156900a00032440030325040c0c40501400920f02c002041907022612013030040710646d41042d400b0300c04ec403c09006010084812150410380c00d40c00141c0341e41c40d22032880c20f2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 484654874 1250 484653624 484653709
    0x120213061a16290106080c19020109050d020703110402030f010b2503030c020606030115122f01092102060a0c210216080a0821010609031709 62
    0x4966243c161090700c08000084030000d6048050251460362a041d041c3c4407448202d5034045007280401590580f0315104030649890081d90001080c0c0b01c2d02641c606041c503040b4039424005a100f24010410700c441010407044e4400e0903142103107141000394003885544414010240d1810001554031244103800c1c0030b0703010f04462000b88984c03041d0245001000340c080b20440c40c1c014490180440c0d42c3d40b5040c41500c003103d00c1c1c0c032001ca003550b2a0411b003440028001401380c0741f061800802070402d40107182c25000000d8881140c0303881055210001d445c0d5141a0081d2604035420320b0140948085480d4031000d654045a0b4a9180e0407032400841c1c01945400000b001c8454101095041c8100c1d01c03c2e840140c1040c1c3c09540d01542c40c21102d00124001c0d1041c0f482651202d024900450091802848041c55800d220340c0c01c40c00011070940440c0086c0c0c0640002004240f00b0018030111800461f0b452024100c05450312811400042d119001c5080340703142c1c404001903886419002c000903110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 484656124 1250 484654874 484654883
    0xc0d02090d08040306060302041d060402040b0f0301060815070f020d1209050307050a1e260705060c04050f040903050a120b1c021002010b1309050106050406120213061a16 75
    0xf0f499880c0e1600c81c0143c090381c8002c07030046003880c40c001034000440c00e60b00b0380c0d03404003401442e0740e55581e020480607204440036030360040080c00d030046454400703024050180c501a0002d25444048141c420060703100108090b04014584c0385409006c0d6000c81ea20303902c280b0a20308101c01c04550030480c80184441d20740281184800600b40c02040404980c2804a50242d00d00300402d801c0401203070701103920198010a44201032825124030905c885400c9203161140d080070781091082d582c1d1528295055406031840e450200f010000352400002604869109580501c0394400d141e402400b60b019561075003050006004004404005e29401010f040c0b400500c0d80700029551001c0c1d0310601c00c13841081c1c1c007420b1040000c09a003401400f9042d0500c0f005070084501c0c2e0b1a950240009080c5c00b07404465554940d84000780030707078070345c06850094140c00300c100344140094030410091040909107a845142448810000c050080201000800c41022030319959081c010003400602d400320070080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 484657374 1250 484656124 484656127
    0x1f140912010f05010e1e04080d0c020a05120f0306010c0f210905090c03060907020f0a0c060f170a0902040f09060b0922141c081e0c0d02090d08 63
    0x1403105410940308240b00380403c125070390700c841140d010070074101c03440c48126034a00d070112414150b55903000e90042c042c012040c10042034048090940f00421441001603000381c14510a0240900c00c101e13108007210b1100d45048900e00050b00d150000400c800d061121203815203040c070203525800260319501ca800e508100e210342d800c4108402c807850507100010020b801c08600c6042410aa5000340200110141540c0d2408104010300c8001014a030440c040c0200f1030100840070460250464890302c000c100146c100b4100a002100c0721400100b0802c0c3e41350b1440da060a103500d495048500283c01040312203880c00490060a051140a180c0c01e260070695030070b0214a034440d4841501c1118100c80540f40d401c10030404d2000c10341c00ca001260029115400102d252003040f40c18a402c1c825940400050070480000115600d88080441c480f0002c0100799141190610f40402c2403800c0c41c507a50600c184145418013550b1b02018202e1ba001682c050541d64111a061525900031a00d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 484658624 1250 484657374 484657399
    0x61306090515010b04090e010b0d0f0314040e010603180f0209070201140a050114120d05030a090f0609061b020307082809030c0506030411100e0d030309020306061f1409 74
    0x480071a80a4440d0a5146d440c11990300c524a506010340040910000c240805036512501c4183c020890400e0840901c0b65070780600c0200c409800150008050300d030401c50305903241420103000d54015259203a03400b1030300c1a9610000f0041e900840b101074058030400300980e02c90304180e004002500740b4415054101c8208103140c045c07030b04918183c07400b42491a20081d074403024041c0344a5418001c4483d50818001c90002500c03c0c0040c640c0702d805000082503165560b203614041d0410040151010f90301c1c1c4040109100442c02880c980030700ba00c11900066a500c03800945901070010010109040020500103004680400c121100e84050a8682e4407502c0c140107001d55403e407200700c8880d0b40c44200083d040c80c050054030b20550700151214000c41c0c581c420810740da40107049075000d009507030042c0030807905c2e49016214501c1c4261070000b40341002c0d00402d4a090310041200707101d540b5901098a4580485d25013480e40c0c01c20f802e000614451001c024499809400c2d150354000410705240b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 484659874 1250 484658624 484658639
    0x3c0c010501080d11031602010c2405150105070b19051006031b050412030201060f09020d0605090105010e13060b0a05190c080a2319020f06130609051501 67
    0x16040716042c50442d00c02d28100c00040e1510040e00c0b55902990b0014408912000304071040014102e205241a80001c5420350302c0740c0b08440320100b806005542c1542d00d469070842c611030a500f0806039842190100c1003c400209541f280c005c00400240c1c02202048101418549440320194040024031151409218101880340b00e03100d0b040001e41000c040300006041d48800c821210810b03903070300d450541411681032865464003011421596100000144c4c03d0103429050040d00704800e001d65250380060710107003990403a8120501c9104a08010446aa00056003844501007074840c00c09451500304103100804040e40000043c240000d0440030241d0301c48020700da407219a501c1502070500115040340c103c548840000c01c041810020b845545000341d030700c0c00910064018003d01d00e025801c201d4401d0b000b0001202e14100b01000103402c1d182c06008a0505c00c8010009200c1d61500065608084c980d0a6025015651719802801401000c0c4408414180d24421700d0146503540c007071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 484661124 1250 484659874 484659881
    0x40b0a1d06130b030a030e012c03070e0105030a061d24160909051b07060c020706020d140a050d090c150221090321040503010605063c0c01 61
    0x18402c1c49600424520b2156081c64840d03595003120140042c25602955501a1a0703005000d850506201e0303648441c0b1395450400d0812000e400c0c0440040050050384018107244c039015803c040c1c0c00840c0c040061155440000b01440d07080d4000802058209418441140c110140c140004030f902a6100107446101740c028051142001b485034524240c1c7d540e6858194014245912400584600070810404070640c21080d00440c06150350000000c11500342e0700654843d1108072102ca0b121810781500a80611040e4020041c82c00648560750a0180003000000084034244918002041030540244104103071589a4048007003000040700303600784411585920322032818200b2803041809030003840804c109a100850b040c007280b219041030301071807180d00a0074209406100d07401e5440c00c260310b003c005200100402e0440c0c2e59450620b0149400d46550350440d41c00340e4010004d400c81c3e00132441e035079039850364000800310b0070929007444100072020100705400e40712800304410203108410751 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 484662374 1250 484661124 484661131
    0x20612040c0f05091b09120a200303160501021c020309060a02180120030f0d0f05011d0a060f08011e0507080f090703080a030e0d0c05030405040b0a1d 66
    0x124007101850303031122940541c1c520b500900c0d0708182e91501040f0b1200c00614940d0380306a1101c0005d0802d00c0d120040343d6901e0092000c01d5103540840d01142c140001c9510300384c40e2400440341c4502501100d00403a60368412040202d0600040c14041d400f4030401394150f4070407000c50315817004420000031110000c0c0d081540c802c04980110001300d0f0307604400307100b12410042d60b40018180e01060100644d501c05408245101360010801c2010149805000070402214116141c40d00c5001c1c61000c0b1003150081d106181d0308511300801800000000281010f02ca881c0ca000055555181e050036001340290b98040c80c10083d94120104a692041d00007105152410441040f4140b902e420442900c0b415118000460240008902cac00c0380f086240c0341e4800005022210410342e2607449003150340c0601c000c0400a5030303030f0242100d41202406000100c0e18075140000f0464541d032039440d03ca1003107100c0c0c00d04c500e0752002d80c0152510b90a419400400000342c50340c4040c03e4503240d031000c000c8101e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 484663624 1250 484662374 484662383
    0x10905190b0d0c11070e0a180b01080a03080109090b010512030c0607020c1003090803060d03020f0a05011d1606050c07030609050307020109120c03230607200a03140706020702061204 80
    0x20480d4861082d8000b40c0da00c00c444100001d06c08544810020300020b00c440000308541500300c0004e64080352803058141c0c000d1655038002c10460219050007018021306030000e1107005d003044005004505c112015a066a100302c0c0c0703540c8a030b10b007a8440380c910f1003010306910244c025001008000c580204222441c070505840003d00120402d00c1101101c039903040040c21488140003065040c10102207002a2602ca8011503c120003040411032410011900031503550303469a1205011311807220005010900700401804034404001d20042102d9003405054100400404c3e0f129800b5030070040c2e44011500301004010745002e508106440383e0108105a0210b02e4111000503490001aa4544a6600883d408114030304590301d0340f2030403c03402d07011460661070200c2a60040b03802c0c4400342c000c403c107440321402d10484102e801d419452030800d00c51107810030001900070940109011104085c4008456965011482c02030000e0048900c0030f17410002c0820400d0041910701013250046005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 484664874 1250 484663624 484663637
    0x40302070f060e0303190203040f030f05010b010305062d1002060f060603070f03020306062107081617060a03050106080d0905041b030911040e0d120209010905190b0d0c 74
    0x7190000d8810f401c0c0d0088054065100b00f010030000001680c050310322049610690340b80594912041005003100c2c0c10558100881da800d4408000003481402d401060030b003001d002c240340980c005070b403880d0100c0000001c4907003248241040ca00502c200c81150a0080104200c0401108c000b5501c02084540400021200740840e90b24a4900c0a0345e201340c90300d0380d40c03002c000141882103010750809800141c0107031042c1310f00080031141e0100000081c03a040d0401030709d46401c2100a046240c0904400130341e104240c0320081d02030b0b01840703070000380039891010740d0540c0714003000c02e401000c42d601c0030b00154a40403000c640c008020880115072105070380d6598500d501e400801003103481004e08148030801d040c00000e0003a000e40c1200600c0fa0080c0d4429641050284c0482d00b0780726a00200c2249806c2521000b0200d50021810800300d81261401c43c2001d98003c00608080400d02509100d00350110b4a0028540c1c3c10300c0040190070415240b54640307001401e500050820b8110030408100b6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 484666124 1250 484664874 484664879
    0x30b040608071a0a02190f03030506151806090301090f170c07060e0d0533040b0112140d18060503190e0a0b16110d0909051e040302070f 60
    0xd000411030b065541d10000c90343c0742000b80c03000c8911903205003103840079400b80820401007203003500c0c442e02d856070044500c1e003030000d810301c3d00a0840324000d0109209000030030030004205140c109407810a1341c18200301076010708100004140d070081c40410f40d03056081c2004175080048245442107ea0710501070000b10540a4075006001d000343c1025080d182c0c82100c0402c441c920131000e098099070301500d404c41007061601e4244c18403008100c2c2c0c0310240c45014000703400c0d400c00280c003084c4041c0500d0b1a507040c101642c030400c10130010f200c3c042c40100d04036100c0050001807215030507015a110111041100401409400507079010000c543c40c098002d000034000d07004408603440390b44441c1d01c540200344903070443d40040c0403544840381c41c0c0c07141130740e490009210014414003500c403228030540b280c00403900c0281388400b201d440000a070801e03002d640502c5c4e0010220320684012039004500b07030351010003201769111150b58100414060300c0c103201c240364001c01d00c2001e13101c00c00440205140c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 484667374 1250 484666124 484666139
    0x4090606051906020d050304240c0221184504050604030818030c1b06040608070318080304030f03050c18010c140f03131211060304020a080d030b0406 66
    0x44036803080b880135030401c40c524003905204800035030340a4030a4500321703807003000c0244510b10b40c3d0342d101c40c14100079034a942002180d034040040240020150741844507180305a2801d810038043c030300c0326030074140a81412036002e50324050714209041c10006003040c001004114000e6030040c41803130b9409c0c40c10748025013488100c0071600910940d0030400900b0b441d281e0b40c2c2c0072108160001d0848140000300c60745048503c40504c001c10b008030340d400c02410740c10505c500441c06200320103c4548108010403007002129007040c907a9902003e503042c0001c10200360040e60b02c890b100100b000b08070001c00002c100405401c10b5404942c03a50950302000203540b07003543d180c183e102e1910800510030301030800c40f40649c86031541d400796505c207002920203141e00b00212458003c45507802c812681010a41058904440301500020301e00d0520795114550961500681d52000f2201c103405131500100003019501c0b0040d245004001d14403c80e1300307980e0001c40040062040c0300c691842241488000031340745 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 484668624 1250 484667374 484667419
    0x3060e06071e0e1012050c0a0c1401020c01020a0908150123030c030d0201050117071a0711032a03010902060406030b010c06141602031303200409060605 67
    0x39000c0380c03158407910614145480188807480c141a08021021800f01c800f41c4a001400d5034255864644000c0060010590415076030010080c3d20038080902031000c03000d903c400c0c0391102d140c00c0b01e1070340d41d10440740246601a200d08081c40e0825800040d01d00000d540c0b0a0031755040790024000c0c0d801400b01d00740a4400d0b940c0a12800340202454060600380c48039a00c1c00c0c00180c2c0d00201103922810428000c2030406c24807500d4900541d46d940010020707a2140b00c03a0524941c10000075110490500481c00300a00301401032071070348a80031403040d04200503003150032035600008048881e038603642030001d400200c00007442d03170084520400c0d0f00c1c05400c05000d03030044550f00420b0941441e0904d80120003c0000852640c108660100080c0100708113120301c0440d50251000c001807480d20000e01040703042880d054104540c0304206130b520118141c00c85e44107580c1d00c002c0c40e2440ea140070141c0a0003112465401354002d150000400801815a00c400200c030420350707828444414064081706030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 484669874 1250 484668624 484668631
    0x30a03050a091a0c04180e15071e11390d08070602040e04050706030b060c19080d151802040e04060f060b07030509041a031905030c0303070903060e06 66
    0x4070302c00c038240050b81c01e2280c2c0c5244c2e2000c803540700c090519070356592994250000c6140140c00540d40c0203003410303038031301440882071022424529010034201400002c0150405010a5501c10554040d64241d10710071449004a920709004994904610006c140c2414071901c0030b858203004c0c11015400000c010300343d020050100201000c00310505a2601c5103254040401100e0303c607030030000414440d0f042000107018500550007086070a003450380181c11a06200d1480788102c2c0180030000216000080782d1240300024503402c851001145000d03005401800c8184ac4a1130510a881c0d55110001d0035800031100300c0307807030141c914204450070005c0344224041c0b146078010440020b40464200e41041042000701000002c42c0740e61450140010b0300903890807800104000b440c0d90507841d003030040e4070140102d002e80742044e081e4000001c0c0d40e0240301c0c800c142c55214001c03140741840028810707500105903060980b60340e46424800100000f1450004a406501e0000400c1c005600050f05910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 484671124 1250 484669874 484669883
    0x7120e01090f0f14270f0f0c0f0d0b060417060a0218011b050d0806011d060a0c050109050607090e07030b0901170c0a1e090504080f0705070e09030a03050a09 69
    0x101c2c0d80c01d0400700f038100c000400085810000c5c1c1180c1042c2029130240c024015000810703922001d003041c103e109103c84018004404507140380c400e0161441c11002180d072004416226180d03505000c1078800098403021030902d0303100f00302280014420803003e15520783e1024110a859140c0d450b0f040380300c104e00030a8000940d02c010200094003950164448015010720f80800c494660b20301c0e61107514083e01080b01400158031030051000390350b0400e002501344140066030040c00318000011503903034010900ea85080000009400c02444029844007880b650440180c43c0315280110018010005a114403601c0d1624480085c060500c42d200714400408010300701c807100e900c1c0400031403030b203050a843d540a40c0264160100940d80359000c08008244011501c8860765030a003040c01c07800e01c1a400446098204001c0100180c61401143d000409059556850740312504245252000796080344109030754600900451070400005000707000d40d990350a20417551529903c07401d40b01107150041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 484672374 1250 484671124 484671149
    0x102070b070c0305070503030403031406041e021b03031e0603030a02211c050405010b060f0405060310080304120c170d08040602090a14270f09010207120e01090f 71
    0x10700e07a910074403440ca50140685001820400503450342815640199000c5011a07582d584444201c0040c05240350301442c01c943c2001204005030514190318040144d0700c1442d5400207009425900f100701e10500c403000101204d44a152103c81e13100725442031003c0740141440000081e0702c510340001194411040b603406030141e0940040441140d8a1200030420750034014003e500141c12180d003002e5441e010003001040a09143c02e1a50850306a100d44a000303900400200001c004a88126000c645081e10019507a98520152241c4c030f25840c0c2150b0854000001c0004e0b88284c02c1c0c02d0404d031203004462a46040342d0f50140000048200c0c044c44072a5001052684111400f40c51810b0380b150240002501d840840c100180e184ca586410400741e405114920b1141c50802c6803c0895091124104040c503110051107002110b4009140c0034510894000003000000290152004283d000070340c0c071501701d007c8401a040d040f0001146d40098851940054020000f4850320f088139a2a088e80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 484673624 1250 484672374 484672381
    0x905060a03030e03010b0904030e010e0901080c130b18070e180c032703040303110328020718051e010e0a09020a031707120c0c050405070201091b090b01020102070b 72
    0x29211549082003803581175507181d0320b061007030300e850101c24499031203940d600c031181159400260003d084e034100b83d4040c00c0c0070401400860000520804509012900d0f842c0c581a0500c3c1c55001e0304403480e0305900b080124016044010001002c14005c00450720341408421182c002e00909d181c00c200a00d60890001000c603040500d4200113580161a403a4060b4010000920221400000000310001c035840007904005040e8000811a94a010039000d1403034603641c031000c1269075164080001c0340365a443c2204c80c00c24001c01c00e070002000c1c081c1c54440000491618040104021100741440e914140715554490990400840c183d642d10b117450392294a07032511040081ca4011000c0f600f085c1440c0700071010070440344074942c907400b0078900c1661f12030480c84c1582e0303040c481184440c207020a40701038600084141c09000280e1340282c0d40040c0c9980c0e41070089014000b860000350440c03600d1000f0410211503001004150341502006200c045a940c3c0128200c0c46520707030203080e600544010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 484674874 1250 484673624 484673627
    0x7020609090c070c0b04090e0303010e01030b090a060c0507170306030a0303050c070209012d0e0402010f120e151006080a090f08030c040504110403030c12020f010f0b03070905060a0303 81
    0x4003600410b241c04090b041988569500700104d02c0ca4101c0a800c40d030220302041950180c2c01000000207900f8051419949031040320b4480f0310043c08000e01c0d01d22424001000f0240401c40307021003507000300080c0f00702c0105960181a640c42640203890507003121955148035003500040764001c1c07402034018030103e14142c40440c007d1601905140c0110000c2086401580d030318110140a483c0081030503017183c000c1680585451001541c6c283c81c01035182d4204603212204061a0b40590203082c0340403141035058007120300404c11002110410301e00b40215065400c0041c90102c042c01d040780d503100b65191080540714070305892050b10001280b04000800703d800301d0f00b200307061900c544042c0065942e41d5aa5103001c2d002154500d0011380045000c03c110300d81802080940613030400003520f002c1c215240103085030344070180907000003d100003042d070071442044400945c44082c00200901c030880c21a00d4042d0680045a9100c0c0c460780501040301c112900c28180035002c014110340c1203520f5940e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 484676124 1250 484674874 484674889
    0x3030909230c0903030c0c0901140303180604050a14010212340503070f05060a02070b0a230c040e0603010b01020712030201020418050601110c0a29040303020303071407020609 77
    0x40d10310b140b50502c402003454804001422030031101e00060030b0381880300020b002000505a0210040c0b0100100c240c0454a000c0201c6030707000005200d83d0015450a804924680700d5503000c9500305800c1440003d5110f80c1c4585034140304401d80c03d071500d00401d45a4519180038515038100302d00c801008400070304c03a800c0c40b0050003c03180100d0031048100f640f551411a001030100340c17008504e081d0072100f0400240000c0d0f90000350b03100c0c11414104541c071003c00003800108409565581e440c2801c00d50f42030300103500741901e4025242115840c101110849542151050500140400020814a2030103004102d06080c06900401c455440c0600c001c41c0020200c2c02642555402c10022500520038ac0701181d00c2502e082d070109090500000041c50144005060001074200024408403680c0e881807140803112890040455400e5041101c40460b4940d544810008000a0700108042e00400654405c6041d921000b0940601142d000001d00c03803030070020b510000401925100d171401c2c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 484677374 1250 484676124 484676131
    0xa0f240207170109060507020304060f050c06060607062903100e12070c09051003020a0b1e0a110f07031703041515030f0521070b0c1602060409060303090923 69
    0x10004030b11084682c69601c106d43c015103040006800c0082c09014482d0054055507468519107419460042c00c264041c2d00d5074806001203108020020b041d4043c070000350019134041300141090384210360a501c048900705400342c003090082c00743d100c013181400c03401e00c2400000707106000940240802c501c5580100d03404081c0032039018a21520100d80c8000074400c15201c0c0a1484035103d440703095004008007400640d00100c1c0340001008201618140c81da08a03050309040f11101c1c0d1a4800b4103010346028880c9008000140702d0303030f4000041d07400001101800c4a008021608100251401c01d541c2d03440112405041c070211800e02e0b00c0c03984040e9020361203e020070405040001d0320383c1d40d1038000114210040da05a0b101c032403906c0711b0300d0b1503007031010302070f1105918580750a10a9496007070805005054184200740403848556001a02500c901001d030300a0119a842e0349408844005003a203000c242c1c005a005070300440c1185a9100303050503103a8008882c0544501200d400c403800400a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 484678624 1250 484677374 484677419
    0x40609090905031b061009050c1603020f0313090c03020708162102011410150302210405070303020d0f1e0c0c321008150a0f240207 58
    0x4204050811040b0003202d548413541c0030241030300d41004040d00102c404079400150610f0315007824080d1900410003120071000b00d445980f043e4252505041c0d04044503413101c04001c1c003000900c0042c0398141038015050301c10055003007020b02e01001d0210100e0066403001000d4100c20031454400020b40b02410300d200d84681d40040301d15503419404007656100ea007185000d40e46400729490f040b0704001c061580aa24440303280412490720162100401e40384454005050703000070400041c1e14460b8811544100c02003001d1850301f0311b454040e41d00e0002d80b2058006004101007800600e03c154480800d070001541c80803844911120322005600081c0404000d104c8603803020300000b600001c20310010244081540ea9440036014002600c6000d8000442c4451030710100058a0f13580716994602902680341c9050b40c0c0d641c202c8070010f6a003600c2130340c660145803070a002a4080a1465030f0042d00c82c10500e60301d01c6601201d0320558030b603840002d0030150300480340a00c69540380c0c00c51a080441e12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 484679874 1250 484678624 484678627
    0x1101020c030a1d040c0909090c080a0f031106040b010b09030a0b0a062c0117071206051e130b28090c0b0f0a050702040b120c04060b04060909090503 65
    0xa0160325552003120b040b00401c071071000c2c0a19041c203940700340060300000d88090080002c003141c01040346229014819a045d0b480381c1603804d101720190140094031851088980b100c60a00308100f5814840100b03c00040d0742910320140d40c0170224003d4040c03980400090b41a034208400c080d080d4112010340e07030f098418540311f00c0104d5181955035000b102c011800140c107601708070420240380c14411994601c44a9144114402100070343d84078112084180c080e07001c2e400440010341000520b40c407400c03039820905103c0052007640c3c2d0159002e070070000c1b48404104051841200c4403d030407144114015000d8010401240c802260260300070520111898002800788020505080e9004612061961107001e10100152440d181c8040c01030b440b925820140f800030b501c080c40c80b540680c4030400c43d02140d43d00c2152115040080003c1d80206505090080761554664486040b01e2a601c11030500c03800060503052501100c080e54050f036100d90f00b20303003004a203801a1180803c1260907100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 484681124 1250 484679874 484679887
    0x40216020405040332030604050402280801152403110c5502061801120b03070504150e1006021501050d110d0c0803040f120b07110102 59
    0x4442c800c4911480c802c0d100c825903050340d008040352050508281c50031a6584420500f000d003111826658404406c40380400d0a682d03c0c8041069a440c41c0c48401200b0358110102d40e00c9c0c0c0b18500e84100365900301008022000074810f100e4414242e0b4801c0641441180f00c00003d4080300c0710184038590308505011418040c00040164251700001003091190890208050009501c406d00e0100303c2001c00007000aa0ae1810119580101c001902c0d00c0e881310300c070303000d042c81c104a0082115103800134000d6440341200030088561030301e00e114840c005091305420b00801000f5108406002c60068000e042c102d042006000c01080700100e036407100b045500000510000c0042c0c00e070b1050741051aa812610f141050203403500f1301c0703400500040700114006000d9520344041c08521150007228030300c4a6040f04000c603c0e0310301710100c05072201c0e040c0d400c081030178040000140121800b08881c128069655444480c0300c10600c08000d02050708000820700452041000305030721030081c0300042c079141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 484682374 1250 484681124 484681129
    0x6040305070b0a0605030d09050406122112050a022805031b0f040b04030209071713022805030d080408180303160308040201260601030203071206030803012c01030204021602 76
    0x40030014640015001c84824052750419000d00d000409000c9408000c1006564918140070b000d00e0030305450400d4603180402c114811100c031040034015080801960900d215030001039030000c254101d08110109403001204090000c1400e031850994800342182c0f9480303080000d00024450036010004c003800030880c4100203900500c01440300c0d007a06540e03186588180243e0410042c40602406611440e052103812007003d296402000b0301c21440b5800581d20010b5606520003100703002d03519007251843c2e401288401401c041d0b400c11070882d10b84a986140840700181c084800030300c040000d00150201f1140740d001e001c500000102502d00303000c111042c1c46840c40c80d9000543c0091464014801996001a84d055041c0a1000c1c0d20405c0000910082c0326070402901c1c040c1050790000025040c1c41c400c0030100da60f03e41220080c045680d8a043c215500d80003070050b00704407400c4292409a4880c60f034819040041c1081140126a10355002c100c001c2d0016000803188403a41060140182e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 484683624 1250 484682374 484682383
    0x6031b0e040f02131e0912020604200604031a04060509030f04151e050d0605010507120e0a090603030e13020309070308130b0c0d03060603050903071509020411070b0906040305070b0a060503 83
    0x1150009000070411502e0500d181c206080401140c10354008500340808140021400310703c0d419031030250b0410bc0000400304046100e10360000d007560320180c0030174020781410422035015a014400c103110300c3e29000c400913220f100c1c00740004034450301044100025a001a402886100303035003041407103141548055107452814503681d074006280010301280584d4544100030241c070003860310342d04101d0f46030746074515441e03842c1440003800501aa050642d59440e41004042d06a0745801d001daa03030b40c0e203000b5003078468584401d48144480b1084200040344d0b48296441054048014100b092954070317028000c0d0700680043c1810454600302080d000380c41340c02015003489040c0240170301c00040300010111186a0480c0c000c1500340400d0212011000095502c80c43d00101100c5001070140342c0b1100411015030001c1d0868102500c5040d0154840083c0800728010b0422001c56a01c503c1d0300c5450f40d00403140100403c0c2c061040390f01180d41c4030728580e4005960300c40082c0c034540301c3c000a80390 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 484684874 1250 484683624 484683671
    0xb0907030807050a21080403030209030f030a09030c050d020f060307050c0a0309051801030314090103090c092405181e010308040512010b0a091e06031b0e040f0213 72
    0x49621110484c003c0000261080c0382402d81221203200311030390703640028601c0c3c0c005000030b0304158000c1862403050750140114400c3c2c40600341140e60b14840d400000e40400828030082d00c03080001000000c1030300b04944240c1c20164020000645c001c51602001280d4002800000412009006416010904100c070f168014000c3d161a0001c529203000c20407001d195040780005924481c00400000381c010500d8280d04a00d414116264140c2500480003080502c10181c0404124507001904080b80d40c089050351000b002400086100380001c405000040d02c0b42c130b40c0008006125034a0003402034010764104000c0524401840c0c0c10f0101e50a000d02c003178100b59500040007504025604d0503e01e508112048030000b4820307000c800b40001c444008d24840c1000142c3c0722035041d84507070701e0520000304030795603440100f04591307c030b080071030021008000110820024800216800000030b0300d0310b110355480f100011101d0801d500340515135a032848500b4030701c3d03264190401440010529041c0c3e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 484686124 1250 484684874 484684883
    0x70c0b030a0f05090d0f0807120f020a110a0507060516080a09080c0f1e03030415020a05150f04110303090a062606030a06021305040203070c110f0d0b0907030807 71
    0x1d9101001003000c048402c0a41a04e4503603100310004450356800820840a503280c80c00c00300b4180d45e41c28002d491850080080c606c5852528500051104140c1d028110044c001d6079545142000ca0349120742e900d004d00e401422079400301408001d203500c154000e0403403000d008021044204c0503a9922000e4110400f036101090700154140415071040260039203030740040352002161844107003c2803410307220086034206889000d81c100f845440030411039008000c80ca140c0e08070f114a005000f520342155070f200721030740d001e041c401c402d51105c24511745016100750741c0020126140d030b5030b8484610301c2c0c801c0c400f9054002884411825600c030030203800100311a840d080319089100614481c0846c41c40d525801001d40c200c14028541c0700003800600c01c50b441100160b40300110595980e81003107030b5201c03560282c000010041680c0e03009494200d201c0c412040b4100e006205020048080d003001241c541009030140340783c000c9000c2c10401030b004518001a15115a1261035002155010610a68 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 484687374 1250 484686124 484686131
    0xf090f030f03020f0f07020f1c030806010206100b0703090504060915050307030305041703091e03011505030c0f01170705040302091509070f031509061401020f030708070c0b030a 78
    0x18180c1044070400c482409140071490300b03902c101130094030700480114660400b0007113003150454942d0001d002032508e005004c0180c9581080d03400030b0720794a8500c1100040d40c410b012a080794000141d0314003c0d641080d0f116601400e1a041080d60303004200185d0800c69029000200c42d1a035103e45005450b8070f035030100b0300c6548180481e840351b006074840f40c000c0c0d100400c01c1001c40c1d40203003640c05803251a414003841180d9000d03038500c0c0d0300410031190b500c07246141d00035440e84011000d00c002904150002c0c001c400b401d06103072030340750298419560181c000d0280340b485c0740744c003c1440d076004074141131428010f0344880c0c4004261800326000d00100720f00042c1403080d45030074040c0e0342c2c0c0410b950960021215590020420300d03400604603100b40300010701c49407030081c003d070440b146002c21200350000c0155501c440340c000c0c040351701ca886134080b00a07140010079480428401b00881315500110300e0103c86a0340c1c1e64247c2e2105109851903000c412010501104020045010b51900c2c0c5021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 484688624 1250 484687374 484687403
    0x3100905090a0f350d15030812071218150e12040801180507140d060911011107050607022407051501090504031d011101150f080c03030d02030a0f09 65
    0x380300c1c1540e03850189602c90400b056012000c444d900320b0319441141500401e08103460b5240041104840c0c0006010b02004034101c02e00c580554816482183d1950f100700191015147e03180480d40c2409401e201324010150031004100f0310b11810f0740881c500040001c40b8000302c14111f04003445280c0d10240040e002808005059090094120780c00e4001c034442886041552076503a980d405114000d00c0d00203601c00300c1da82d0351f02e41000755090358000301e00b803258021078944104d1400c0441c0c51f19001c210a075088021000e0002010426548060700c6d06241600507001c10000c0c41c402949100610100301c41d082010b00d19034042c044040c80b9100405a40003c24281f07400c1d0b1030140c20011034a40740408001c0801c0d8804241c95008a003540368201344803540c00100d40360190601d10045540c200b061b12414040c02690080444007a454001d40c8943c440c4003554a80c125052140c0c9e242e4414803003d1881c10700d40c0d00664010700018070011300081d6142c000002d580040c07406a4100c020f44018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 484689874 1250 484688624 484688663
    0x10050c0a0c24090c0602060f1801060513050a0e030a02070911220303020d0e0907050c01150609090509030315120a1704031101111b13090c15030203100905090a0f 71
    0x2600c05132817140081d0059103800c00b24520300441c003d00700d8414846542c0703038800040c82940480081c240140c0400d599026600c90701010701016901c004c000740c903202a84030403032000b00a55049100a074050140360786010000000341c0403001014440c801d0800880d9801000e01c4910841d01c0072003003c00100034510b060180c01d010004515900f440480e40307040190743c1d80c5461040c3e104005003400e03511490b00f110481c0c0100a886900d41058140a42c0468040e4010240801312071040105000942e01da28445440340825105003400c16030015409845213441000c1c0d807108022601126618061500c0341744156503220040070881c08005014000d20042c0f40d810404800d0030308040009040031070305d45076610034104940d10440a01c00b10030480355a94220542e1031050395400380a0884030303046c142c1e5140c05034802c1d001d0001420300c0400080b4060b00980b4490001c80d80000340e0140340284400140c030005000041c00c1c000d4504950008440c0308040f11100d0190107450069601d0707071304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 484691124 1250 484689874 484689893
    0x190e0a05040311060103020f09090a0507263c0a06090210021f0e1609020d05090703080304151e0501031b0b0301090e161202010210050c0a0c2409 64
    0xf0a007200350410401030003d0384070341e890582d0a0b803040d10814042c1e610f0302201404c0c80c0e0301e100000c005004180f4001100541203ca104400c442c01c89151518403000381803036a40d000c0b003800c0d12440c4401e100904018007900b05c400326a104545a400d0000b1200c00045081812150341103a80e5a581e010344000e504042c405032517403040500081c4140303034074110f11480201a01d14005021915249038400da104140f010032111504c0080b108841516103050802039084114501e490743d241c00006089180009110030840760000003052540d111602c45111742c0c0004d00009141c1510342d800c1c544000d011448540442090000c00292135045141c1111082c00c02640303c105027852000c20700c002602c010443e41103c0410700b001075204082c2c1e13901424400171038140300c8585607105c1d00040c03c4c618809c038821014400d07801c1d9000c00790101000c80c101c440580d0441d40e101c0042c00100141c0d03004008158200e801001c03007940b0b10002c2021102c01e01103524820b003400c0e44400e484c0d410010004c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 484692374 1250 484691124 484691147
    0xf03030a051005030a02090406020d0c090504050c2d070f032d1202130e09030d0609110d020304061e0c1709030304030f0909021215011805190e0a050403 67
    0x10910002e601d0b01000070707603030011503401910035190b0b007000c6130400146504580800054138024404104031400c0942038540d00d22509000c0c0b420600090a01c000d600c04444041400d00801581e06214210881c140ca40070030002022420420a240100d0041c1200702d40b014404c0d030382c020150031500c0c282d0700403070b6400f02c4140a07aa406810003400c03982058403541508144100180c590314410f208030041d1026520003480d840040c01440107001d0088000c10f40081402c605026982d603448500c0200d44c90001203201d107002c107010304050340c03c06400031604a401500c0c04190808410600103943c0c0d500841040016600e400d03a49045400c0010a2f400c40c4104a8544062030803c1c0c009440707110050004081000c0082c2c4111404e02989102c4054984400d0440d103a40c0e121180c00450101515200c1440caa030520340041da41c402d8071228000e9a458006d10100c03860003041c882000f0380e0400310001014030031004100040414001031140486c00d001180d01e04050401500000c3c10a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 484693624 1250 484692374 484692391
    0x3010c030b13020f040b0a0e0108090a0305030601120b0406180b010203130306050403021f0605040605060c1b030f010219091d0105010507080d020705070f06050a02060f0601110f03030a05 82
    0x2041d020716550741c0c0120a0b00c0110300d0030160ba1401406060700c1e44e4450350300172198a081c041200040c0da544522200300d84202a29200559110481a142d07100f40e0b00c8001000540c080001400d1940304441c1101e0003010441c02050354409030001506135580d50f0469094016031507a5143d042089000d00034500030700b030001c2c501d0700354480d0070040244d800c1e000140110362520301090426208102111203a03510702d0b076603842a440c0301d10340c4020741100e2259502c03d600300300010503545030200440d00f04401010082c1441c00c0b408032052000e03005010202d6140c000c0006001c1d00c140c00b0b00083c44035206407000745c0300380380395650060704112041d044044140010a407040520b4112003143d0f041d102c09003040e507140e00f006d1418100901c41c40c2442c0c0221030010440c0405c0040011300e15042e01c00502920001a4641204072100e01404205500503070005012070440d040c1501d40d940c1000040c0340824440820000b814030b40a1421210700300b6602c001304002c2101a9440380d9600214623 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 484694874 1250 484693624 484693631
    0x1a03070b0901020a170c030a090312050c0327030d0c0b010e0105030d051305180601090b0903210906030903030136050a0914010903180f060c17041403010c03 69
    0x70000002d64410840100600920f80b044031340746499030403001d40796402c05079400c8960321012500000d02118007031004031820860480380216150107a42602e250744003042c0110706000841081201c0e02c8400c41c4042d03108a143d00f41100741d61014030249002004caa1283c1503d1041440d0010740b400c030503403291200301140801880070b5035000c5162101c1c0706103032605a880344041100c20802c84000d52042d83c6c0b001c2005454404400c00705000ea100c1c0d6024bc83e03501000b40c0d103140012040c4035000540754190029801c240ba05e4107602d500f00d5141c000c201c0e02030b040010510204445910540b0440069072000c4010400f40e805003001d6000c034640f0103050700e1840c0101007200811056140310800d440e844070000303000c2104c1d681c8140c280c40d800c048050039a40c0503414044c000d0034011400c3e0000b41c00007048030b82c54000714154404907800f0780140c1d4001850004100c4001a040c00c0841e14046460050412101c0010251000c0c00d40301e2150401542c0c260201421070349881ca511051609 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 484696124 1250 484694874 484694887
    0x1201060b0a230f2b140a0603170706140c03101502210d110c070e100501050912030706140610080604021b01090510050f040f0206090d05011a03070b 65
    0x2850064038155001c4408582d04c42c4c10002c2c00c3c00c40011096880e08100c1105000680e203425250440f412042d10fa40c804045921640f14140c25100c10380030190070540c942d009100c010710711038002c18030340e07004000020f250042081c041c40c080c2d000340e8000107800c001205101d1801041c403021002040140f01c85200c0d10f0100001940b40c1c254040380c480c0c444c81380d09515401d00040300444203015143c003404c008100342c5c81c8142142da042003406401d40c0c4103104d4089403042c4000c0001e800b41701c00390441040b0301d2401004599580c0b10703007001a0081415034510b20707001000c00280400d5480b942000c40d000041c40c06a0600da1001009103205440c0015003408840d001140550420800c1e180981c1c0d410075150311107c1561079892281031907103001c001c0800d200000c54144024400450144030729100e8030313050740c00b0140c1690085d109032100748894006141110040001c100701a1583d840000c10740c94036421108a4001100c2212407a01e09403003c6c90103100200c050b20840c14800d040c01c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 484697374 1250 484696124 484696187
    0x604050d0c1a03040b2a03041b0506040f1a0412150b04140402370f060f0909020703180b0702040b030f2e1b0e04050f04020f1201060b0a 60
    0x1400f4050007203250700c03d030b034410342c5908140154424212025000d0303031f28201458602e640c90190004070540d240000004115440c1030741c12641106d00c403a400c829080d0400280035220215030030b1070118031100300030010303800700102d580a10280c0202e01a80701d91200440c1c100564040484251003689040002d10305681170441c1c260308150141e07015403c036001ba141130755150b00d100030b005084040c0040d50144102100745204262503862164015140c0d40c1c007010340306d0400030040e00001c01d8410105024100352503003d8152a802440c1900320021940e0302261441c078203070012007407450001150000d60a0901490726030702c01c2640241003102542c91281e1300e81d04440051854000303006800002d200b107403d4003454072004030744200804041e8004400300003080d50b1400b00400d80c001a0001d49240600c030390380c45400d440729102510f540329402c101401903454400c580c840076110b103036035540d8024407501010380042c050241d40d40d1310800002d441c443d08a000b4080c440304595240c103062 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 484698624 1250 484697374 484697393
    0x50106020c010518040e1002090a1514030a06050a030602090118260c03030c0f150108030a0c02010c0f050c191208091201051314010506010c110604050d0c1a0304 71
    0xe050030440401c580130550005020b0f0240c83e55901840c030441d00c4594015480303600074001300c1811521030310400d41c3c03006049816140e860a00020170380c1c600a0a26241e0400c00941d84501d00c40c0000034400e4549002a50814040c3c0007518007903400308130240556004402100050140c201400c200b038986810300c403081c0e03c81c02030307c6031148044001d4203c40780200001980381074010242d82d03c40d0301400b01c00d56281280400c02c03078544542d601181050840400880c180c44100d00030310300d0940d40300c4054036402c60b540300407810070860100b4a40412514800345007910300c81c001810202c8505010004104542c0082a0070380400b0700c8200040c0040c0510185910350050f42543c60b0066000011200c140078605100c55500b4101004240903500c460b00949500c6050461000c0640f00d201c1e038200c40048078042e001c929000c46502c08290119016000841c004046910382a01c590101d05013900107038040f2030f242960442840442d0b420240d4a40c2000740c541494114a0181c0712810301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 484699874 1250 484698624 484698637
    0x1180305150123060d020f0409050402040c0c0302070e060609031c021014061e0604180c09080606090a060f062607140309070e091c080105060906030a0b190603050106020c0105 77
    0x240400140840441722160162440369802142040d01c466540030352601904040303070201c3c400c501e0030081c01c0403940508003a010042c0c05a0041c02268104030407800d0490000c2c042a40c00f1000703003c80510b95408024241c4200f4100d14444904110300e200030f450182004100654282814111a045502c0c1c2c0c03c09640410100ca14403852030107402c40c00341165000305115009a00014080303102c00000402c54503020403480c0c200001103024408841150150050800a030003510104410f458110400c0e034000c0000c1c2000a0b071243e032060382c2101000c00e9440b101c00709003d00b4840721014209101a03081d8500d6102c450198074103490000c07c08000f00083d02021140800440c490103420440000a010341c2030724910303913061201c05117070303030f00700314002181c50440c8110403482551042049038100c0c3c42c003802c0a030910880c84204440d0740c20040425440c1551440160495a40c2a51075240d114001c40d110394200d062400050680307030160090300941d07100348041112641e0040441344d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 484701124 1250 484699874 484699879
    0xa020c0f030d0e0f060714240a0b010e0301020c010606081602031b031207120b0d030203180631170703110f0d080315010e091501180305150123 63
    0x700c401403180010a0000d18046003504420041265002c01100031030044400425501322100c415921409402090305c4441030344aa107808d4000c02d0f51084203420030030a0090504182c01e422a0040101342280c001d812400310980d110342e01000000d8200c0e0403a50465281ca1070f5051400c0c0006010399603100348040311846c4001505010140081402510741c0c004120125020a06000e90001c06065000300320b000c03500c0c5419100304441c40c0004500501551540265007800080240f41c42814141c00c459500668200507541107007a003031000703100701907400980001c80350340800c0031480000c2a41010400c50300d01c140086062500058400c11039501a1012a000301c880707012540403101b440110b41c000a040040d01e040000c0d07035014510451071105040000361501c8011240c0001c0309240079003001007503000c90301281000b070a048840c04181021034040501000c2d8603035600d159402600c403a007210f1440880c481402c08600d00420310f20038821200c807511411081a01c4140b465940b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 484702374 1250 484701124 484701137
    0x80408040b120a1d1f0605120109060b030d0e0607030c1401060302100504030c052701080a0203010f0507020d080a0608030c100507050f0409150b0a050a020c0f030d 72
    0x404001042040350040e1a100e1400c5899640224840040c02400d0320030b6000039040c09010002211804040c2d051220480000c0003081030782400c10b1090a1010100b01442ea103405010601d502c4581908501700441d000004a0024500b861000c54a00ca4a641d00c2a0020759201041c527500007040100070104542e1107030703114220728003942d07240004000281700c0d542c80410105041d50660000b4110f80c0291074640301d40441207009c41d228865030100401104118405201a04002c0c9480c0e90f2180d641010460310074061302c0300c3c542c0314000d900c841c10303540c414000c034401c5040a010384511b680e01003100388114208590301075250480924507800b042050000a0740b521084e4200d00d000304a80002d40b9900c0060f82c0c00591940d280e80480650130741403c020800181c031076011105640041c9050908042c10005148054000d041611512074811032010403d507640c4801804150526181c040c0c0d0782c20110703006401d2850798450070707102d420368640c3c102d50b80d103001c10141101c044919045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 484703624 1250 484702374 484702381
    0x5012606130c0201092a170106050a0b1309090b011202131a04050c0909010b1e0d020301030209060d050d05090307121b09090c050d050102120a0f060e060303040608 72
    0x500e062111071114203618100300d01c03801c5040c0c0661088000b00d00442001e040a0068080b101c40d4003860b449050100704465000c01c041c110500a0040b1100c4c008004580d032652000040c90381801500612003403000001e4502d4560006509100141310700d98090014861a80311001c010b1014400e0304070a40741e0101c880b00315030340c001d01900e00c0c0000b080c04100c021240060400d840700405c05c000d000710710740004600c8080f1100c00340c030a003020040c9000c0702607080c0340b1107a8168106803600d0b084010094606441014250044d001d0359250300c40c016140d41c51801004290940503111034080e0303403020141c5010031004200014900c070b02e030038259599116940864079100213170740a10089080303000c0240400c5441250680100c1800c40615045902c4031900c40403a049454010180e84005000300400d0500400c002c4034540110700050410b441d0040c03000b0311040485000c0c1070360380e83d240c0c039018040d9103100e90409000c100c46e0b0b0603a81d00d00407002c40c0c0e403489280548410f200700301001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 484704874 1250 484703624 484703629
    0xc030a03120905010e101a1e012d03060506070515101802090a2705150d1101020d0315170c1503010306110306060d0b04061502060402090105012606 65
    0xc0b15260f90710400030020b076122045240d46601071543ca15030900d00301000e00b0000c958600c8580445480100440c000c0c0d52058800e1526402c40202c0324180104030b03c4030b00c06904010b9901850440c080d000e404500c1419800504942ca179802491050b1414040800030480001c1c00c405406444000c500c01174030b0322010118006000d9020301d66035126550034042500340e0703401070010310070160b81044c0c0c055141c40000d10211100503001194450148078040800840e070000c5800c5210b28072441c3c000201100130031540055024151514800c4603003001c1a56410440c00d1103604c85440d0411882e50100076101031791803144070f00080800c2168035000c611505214914100100605001c2445040030030300c0301d160401d102c241c42c91071800308141d111a108208a0740301e07120040c00d40d45401030265440b0010180b1700c0011303400c02d55400300811580e00e8042c004482464a8008103045c0c0703400d00c100000150160410780c100140d203488d0542c90915041d09c1c6070380106504034000c903036960201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 484706124 1250 484704874 484704881
    0x306210c05031204090609140a05101d2e030f110a03150e0a1505070e03060106020a05010e120a2601030b0103050c01020616030c0908060906060a080c030a0312 70
    0x1041d854043c40d155000d08951820092003241c81016040c030a040c2d4904900e000c690140c907181c0030030700c5a000050840c0400350302c503030341c01500c00800d908501c1e00c9118003082c040b942e08904941c0568a8140243e112050f260015030303980d6024402e180401204400d400b8400c1444000e00341c0c200107007407200704005954028103c06000d4407d803130190752401c10318128040c02d40c18001c11440e106a605180d00c0205a5107070094110311000302c1b0541c015960402081c004081c181004180d194502c0c5580c0c042c49968002c000940c01451129004e081441c212040b031043c00006900c00d0304100c071111010030076100d00910509210084503144000d1506071044000a80303045001400003004020008190a0590b4050b40468800495900069989284c10303101c1918844c0041d80d401016486a0444003e040240c030f442e00f9000c2d0385a030040d25122040e1106006500700038108041070030306961b40c0d4028941d07180240005200f1401098803848040405030811114403461035019a0681 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 484707374 1250 484706124 484706129
    0x1201090c0b0a090b0c070302150c1207080702031b0a0e040b01030b07110d02011a01030203040b01031e02040e0c150f030f0a090f050105100b130510210510060306210c 73
    0x1c00c0c903074460001405c10384031038243c0012403241c40ca80205020400341081501d00000445000b4008103140d40d84280c001d0b04101b00c01c60325204100181c0c030040c1c40a0000b00e50903110b001e03440c80a03010382d00030090150503940041500030014001c120118200586960440f5040f9000d82126210280c04403640e568000d40312120b4030841700e065141c3c617030540c03000200721941032514060b50081001101644400e132006400419820b0052011403961110b9850701010051403181c84034595000c1010740d1544001010740c0e4110070001c842030b0030700c800c0e034910065402141c1c61802041d4003401c07a00d0300000d455920292100b4001440d0348509602c040c3e031440c1c001071000c08680507442e105000c1c2c002290007140e0385400540000700c00e200c6009403042c0f0034005000087c80e50610052004441820071580100482d100c000640c0030710f03000c081d540245a0600200341480c01c400c40c40008180c81c0e0242e0201450040c0403c4401034451141d1109049400c00c80c09000407410f0070b01d84000d054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 484708624 1250 484707374 484707389
    0xb1e0301090f08070201030522060f0204150503090d0e0112150b12090705040b03030d092a0303030509030a09260709150503010b01020c060d020f070605061201090c0b0a09 75
    0x1982c44000b406410380281084500c00d136818011139403031360200c41000c80780720142100150502d803014006482500010030101c0390150040c101a035420a2212503100c4401000220303030004280315403090b00b0f005010002001b130602c02c043c401c0076400288540007003804040c03041e030ba07140f441601d14020b9000d100104580794022741c40b00081410455a0301c01669445820b22a100001541c1d0525000b9018004402000765003400311900c1d428014004a2508942c8251135021580c0030700d040c10074840c0c4803050695003441c20390841c5400b80803980c016141c000d0640c4280a4503180b03e901810401c140e4001d505440303e8010074101102c0e40c1326203040c105505010300103010403045d50f0b96104807002d494074107182c8400c0e031b0344d00241400c03104440581c1d8016001a10750008909004c1d009141900002000518080e1540a100380c02c0e04007020440300c0e42c0d155010b10205243c12030f4013209450340741f4001c00040380c156a55500c5504c403031142003c00c3c1c1c008600402180d01464441009040d207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 484709874 1250 484708624 484708643
    0x14030a020f0307030c0806100503071d0904050c03060c04050a1809050f0d020d0e030318011b03030c0e0111071a0706092108010b030106050310030615180b1e030109 72
    0xd10f4025000e8809040301c50009161100010740a140c1079121962840244d2241846c6898800e0101d86a141c6000041d10040c42d00b40088519212060b01510442c010406000f41201b981d042600303081c030103010040c20540a0006111a03900c544492007141d51061a595090905884c0c50340500400c0704060700d10b0240c10324420300e481000c00d044c0b9501c1e00590949514071034400e03003078031000c200d00c08141c1c156100b4081300010b20309080c5800c15010050420302c5031030b05401c44104100746101c000300c00080c1c0340c84c0e40140142d0400869a2100e80c01d003046c40303040000f034208965541ca03e1184509078940704005455a02c09903003200d5107650086000d0200344a00d007000c000c41044900070000e000c2c083c41d0b0702403520780300c0d801c0141038920f8048400d20316482c1c20f13422a04c9030001303040501240c01304280000000c41e18851103145500c014407030204503140c40100d50310034080580f0103c60a040071050314265035140c1800c4040d1036811440b404015074000803d00401180d440100907240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 484711124 1250 484709874 484709881
    0xc120a0909140a051b0d050a110c010e1902010c1113150503060109050c03040f0318031203110a120914070b0408010f142d13110d020114030a020f03 65
    0x140110b10384202894202404507440d03c0840b94040040a407085540d04801d024a0041c0989038101c17507007107100028046409100555020b883d40e1105090002c02da41d5810b4280d2203840500082d020340c0d070910b648142c5080150006041004100c00c014960b003840c04265a1581e510440e131294481030140c02c02c07054001c031905003102c0302140a5148a4401d4100014000c400c0e03005061148500d41c0240f4216101c0e5518044d20040d486401c40500114204040035074540c00c022000440c003030712844440315074200d009000c87d2204112011f210030100501001da54001c2c4000e4010b00c0301002c00110003005080884007016243d0808015001b0000001b94528541010f801940d01e07410081103040e0765220001d0490b180701b000ea00e04600c0000c0003ca5107035002000014841000b00b6a403c0d43c56007450300170744114201c54407940101c40342c000340f05021101d4100d07849000280c0e1240d81071219500081d02041c046030508502410000c00500c10340b4854050340c241c015a1000140c6a04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 484712230 1106 484711124 484711151
    0x3020d0b100308031302041b091e080d050a02100b09010306110910110c01050f090904030909050705040e09030a080106080c04171005010b0c120a0909 66
    0x20507000004140076078002c501c202c050215400100046104000480e142c0302c00070032031210b59038028a000c580021481c801d4454811011000c110802406019014290050f1000d4010083da120149400c040030303000d0819140c0030303200c030000d20a0342181150051002503a0041080004001068440d841a0340304038241c12017134a0841d005022130b0394000351a0501c400200101c112900e0002c0511020000034001d1030900d00c2c00350ba6011803a0345001d0399189030b00c0761280d01c020504250103495040e00411103603106216620b800c8038003508503080b600c50000b04c00078100c00110740071808001c03900d00e21001d0301c2d01c0c45240d0801c903086585103c02001868490020440400c108950401c10841001c1d088028a1900450032484090303c406910103c154981440a140d00e0040030640c85441d0401c4101d0710780311a440c0d44221070f0141240e104190a510701441c070007000 = true := by decide +kernel

theorem cover : BRFrame.Cov 484532374 484712230 := by
  have h0 := BRFrame.cov_init 484532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 484532374 ≤ n) (h2 : n < 484712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
