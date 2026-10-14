-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:33.407256+00:00
-- url     : https://prove2.me/submissions/e0a63404-e6fb-44c5-9809-66493ddbd58f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 542086330 ≤ n < 542266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 542087580 1250 542086330 542086339
    0x130602090a03060b0a060507051c110d0203030a0f02031005090606040504020c0606030d0c0b04030e0a1203030e07060e180a090b0118150324150803040807060c02090f06 74
    0x103a10a84500031110010b43c81088046182c4a48108000800481da007100c1c0820a05100b641e010520004460039012203403070511281c400180c0040300c429003c0030040809200d010440500341368000300a6204030419001001061a1300c1025002d03807000b9030310307822541300b140c40500041c41d10b12403070f40c1c201030b00418a40ca0540d40c5c902060680e0403003544459160800c0082180e10705081c004041461501c1c0f50903016041e40b130742c80411130b0b44058400390411605280ba1134454a1b500d40701d101030054000c0003604280d2502d4000d01400d190250b04801d0b000340c4d0170001c0da080c054002d0389084a001003815038142101c24038032298800060140c41c890b40c4032400180450181c00000d4040c1009084482892a03c400c0f0070301540c1f03c508855800c40000202040840d040c8541100070317007020031544145400944000c0c01820104500c01c0c4003100c816000a0f02c0540040140b00f02c1e006a070a54483d80c0e0380d040203407040f8040c018083d41096009000a200044403181d165102c0c2c801030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542088830 1250 542087580 542087587
    0x63303050903030f19090c0f06030b0604140a03080d0b040606020f0d12060b04060903050111160303181217011a091315060906030b120c0402070f06110403021e09130602 74
    0x80b4010146c0e0b0a49100707983c40100103900340101000449800081d11450806128169007031000c181c180c4034070710500c00c00c3e840c036044801f8599030340c924001c021034001d0000d540710304040050034020004812110301c03c0380b50007c0018650b00110b090645050000043c100f40550804191800c03d461000c0c688c034250741c2c0201046071000c4e0409003002d40503940d11a0305050540c503101d070071a0940c0c28040d0203030106028081a004075401000d8a81c1d034540780120b91121700070480d50b000c24211000504c103034020500260850f0b444403407070030000c0740c0c0040c0c1c0d040c0c2e90361a4001c1004c0c5112000016220710104980b8003582400b03044544c000c180ca07076000074503007409610818890030940003100000d00300141007084580c1400742c010090300c00c4511075003049030f00100e00d47d00c290704002c09018507008506034051007416402c5c5c3e0307416504100144a480e80913201c2c01c640e5445404220300c50814886c10703820941101c0700e050500700000d840f10342d45488a00040c0614203034002c040b2100e40c0c082 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 542090080 1250 542088830 542088871
    0x100518010c0215040f21030c03020c041e0c03090503121b04030302010f0b0609032d01230c0415080a06080312040311030c120c01063303050903030f 65
    0x10080d00f0400180c0880403a03ca904080b88950a82c22580c0b000b005c500b100140343c015074070841002c07850350740d043c00d012028402e9850b080c0e0404c103800c4140c4d9401860802c40c001304403900440e08804018813902000b21044a0900b40c080364078030342e00581158020300c41c0c1d1600e0f10040911581200c10551280e82c02d20356504070603100d502540086006175100c0f81d9072074211060303001d4000c2e080802c880171410300641d41c001c296108168000c00c0c4c030089920300c03108811111855201e0700b03a40b140009010b41d0f00b503000400c00091008803e4428840b010700040c002c46084800d88080d60300030708448000c420558011100e8000180c0503000341a95000c0014085004100420029185c2d0141d42150b10f0242009004043c655410350416002040502c0b00d040001c24130702608003450b100181c4a01c128050780380101066040000400c61014408503420340c143c2c000402d205040140d00f445900300c0e0001c070140c81c1c01f039440c20025441803022503400403000c0c00b1654025a00ca0a000800080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 542091330 1250 542090080 542090089
    0x13050d02180c07061425030f0e01020408070603090b04240501060f02120310090f0f140a0605150f0a030e06011d0109110301150203070602031e06100518010c02 70
    0x25100b9003406100015840c0820130280a0b4811810b46050003500c0c3c1c0c82e10740c2e8108183c10100005001d0103201d82d554290300e070b0095100320f101e9192034070704000e0ba1080f116154000e40c498041c83c0d800b44a064800150280309008000c01141c4c0010088820349903503456030b100d46240f00b114056a09225001d10680c0c04034801c1500030701d9a940c0f64042002c6445010b070400340f48008651407240208100301814005883d0307201180d04010703000540451030690b6000404103600e02c00403050501c2004141081a82d42040c090400e0b02d80c1080741c5555102000600903105400c01400a410301001b5030340c8c00500042c00c90109103081c04100303060707400d1410317041c5407007600001c100101019a80d0060140b545900c0d02605110008001c85111504505040c1c0414401c0c501c4134070b203018141060502c01d10581c0c80071640b1078025501c90804142207a120001003804910450500000071414600008a40c3c10075007180c80e0580380c640721445800081009045607410b20400c0d40c41200103866 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 542092580 1250 542091330 542091379
    0x11010207020d1506240e0d02010f0e0a03050a060c02160f03060222090f0e010612081b0304080c0f030c01090306020f0f070602070b07020a03090b071703040510060b13050d02 76
    0x10b00105141c0c245c100c5000034108000211241d40283c0d0081c10540041c1d803c212184203c0c5440d04018074a01e0700e24002807624190390300028518000c520a20301001180e0700050000c490503000d8540308490003801c007900050750f106110008101240800200c7d81e00c0d030080401c0c400308005007414902c807001e00c05403185207512a0503507540d80c1c2d55149001420b03101c0d005052058500900c00107190000c10300168184400241c003d41000551001c003142c113441d01a954002c0f80141da407116a03441c641c60702e580900100f18061001d1f00d4034810740389408203c0c140304820503140c0781042c0303085481d00402904031401207030104808020030381c610280c400290a82c58030904000d40d484c0b40f2403402d2520039001821003000d540c05694001b00103900002c030402614801740305aa1125058101141540200100c4903505040003050000b40600481c51140c4162010f40500010f0750756030014895118070f0315007248901a2a10a0109243c92810812001e00080100510b02e4040c220410000c0c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 542093830 1250 542092580 542092619
    0xf0615040f090b06090c130506030604150303081b03070f181208180f0307090b0402070f0305030403020d09051302160209070503040605010f0e061003060e0c070311010207020d1506 79
    0x34003040002c03520304014420341c81b83e034000c201030900301c9984152400c041c81d40a4540b0134540440003488a8465610a007041500030000c10768040c2c2c0c0c0d050140945500761840c000c247c2c50024018059180741c01124000c20640d580e4181410000b5011075030040c070150303298010020410006082d0f0b60801c07020550301c0c0110203582d07541c8803150a204003841e405215034022801d01280700342e030781d9000c50890304482d0820380c085046034010740050002d10580100a051101c0321944606260f840800780d8440c0d03110b07400301d6000340030701d00b01500c0740106c5120b4190700c028520000b11048106030041c10400b846a807410f0480f11240e0300180f03140304c0c1240d1400001d10003108010522846000d12401002c21b41f082d000c0960500a1054100c40028080b600503071000c8541d0071114481e51000009100201404030142010084448103601c03503042030f00045c442280048030f1030307810b10172078403025401032511950104540da0040344035040c00d86d010f0702d595600c0c000144c82d600000c500e080304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 542095080 1250 542093830 542093843
    0x30a05130206090f0a05030f070609291c092a30050706020c011707050304020904050a0f1110090b1e0409060b070b01150c1506030f060b0906030f0615040f09 69
    0xd414004010410010f070b03844584100140b01a0360440c3c5010820302c01400c4100300203a946074407100b801000e140c00ca237481d000040c41c041840c41405206146007100079442d01c0b042a514400c1d801a006026080c0240300c011203907161401c1420040b80c80b0f0440d507451501c0c0c40d50300310249032945400c0c5400c076442742c0050707005620f041d283ca41e4841240701b1b031800c002481109904040c5c1004245004c014402401401c080c00440c0c10b010702001190102c50740100603004234819458441803a032145014180143c252400440e0101d0044110009030f5582c600c00d2414084d44644c040d60022040fa520071030a1400c00c804030300d0710315a00400c005400080d0074035030b441381c03a46040c9000d0300701640081004143e2850381524036520812200519800c44204907004000c850a03400070440c07a8070040420404002d40000c2000c640c000714440390701102c1c000c1095440c0c1c2d090585404a0380034400c61904910000380301e204410511f410501e00285c400910000c1c9004ea140441d20750a07403d8801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 542096330 1250 542095080 542095093
    0xa0602070c060f090f09110903010516031d0307060c110f0606013b010302090a0314060a020313060c0201110318101b0309020d020a0b030a05130206090f0a05030f 71
    0x785800c1092480308004520b41250030310f2a00c24011300302c074406c0c082d002034161a210403070303140b040907005e0350724603580100208500d0030015088858001a1a0b1481c042410800440062806266042180c88281e406585426800ea944500404078441c6500078000030296440ca240810000c01c0c1440203510300500d55420020001b61201c0c4030900c0c11a03038121901c41d03100d07205a051105c241042d20740c001d550740c6031a400005030040d0140c420902d0300401c901c0000402e004140010401c01c00c4044180c82c0c454480c81d9480d0203a1100701d030103424a8500081a4001403c1c0d5445042002e48601c0002007914418142840582c000d44100341c880070000003214070000c2c203100e00403021f05030820820090718100402c0314600c20000241c401d155a034801001952205407107001d6199004100080381611000001a5a0000d4403035200c1d49103404001500080c400c40d1403400d0300c4d00240000d040c41c0e003500400005150744400c45070414030070b4500040c0c0c1d840420003d2a00e0440b480074125 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 542097580 1250 542096330 542096339
    0xa030801030506060f0a0303110a05030324090106050f0726031f05030705010c050c0d0503120a090209040b06010302270f0f0a0b030c0717042c180a0602070c 69
    0x25120004d040e80d03224040050b0010203a07580d021661003100e515081002200080000329410101d24800160041c04004108851800701e840d500202c1d10002d000e00c07a80c48240302c14041010800d000308004618100000d89400d84140301070207140340300342c510090a0f04104012088051842e6480c2920800481030000c0101e040c859140d5008000d0b0050940c2c0b49400b0001e9520103a034411281440b800558042c148003007480501c54842024091100c0000e20b403402c1e5039203511400290202c00c08a00104d03403048014081d540c00160000c20900d800d840d1034076085e403607401c0070b8280c5040c07513800c000360307a41908202c0d0050340c004001070180d0780c018400c1c0d0074040394081c1070341c0c800c2c46100c060030740c4540e03903643c1c1d48003509503400a000306841c0d5907010b0006541d842040d9002d0102e0040520010071090000020400d5903500800510000707580310784403243d15005006181c0300991500000d0025047c110307400c0100e40400100d40c40c10040303450340c0049034880d9405a60001c0320103000c1c031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 542098830 1250 542097580 542097583
    0x6190308040f05090a0e0d031a040e0705010314164d0c0d060b03070302120109150504051005070e04060902090f18040308060a170c13021e090d050a0308010305 70
    0x358458000c0c1c40512607518551b40240c1c50381d4002451b00b0078507540d45500c110705245840d0712281d1010280007000020852503206649841d83c3c811507000030304001450500d510000d0b881d50182d10a01105034041d00184001c0c3d9030101042c8500d1030030340e800700c0340110020f0080d560190006480d00414084440346900c00c90807144c140c058002503026160ba0652911508039800328180c12480001349007961000182c1020843c1c0d0000c0c6d4081000840080c21850650014925502c24a045948803a02e030b0760030001d80e101254082c0151f0400c2e802d889103009030317810680d0f03c1445441d01401031002140002c0c2100c45941190b4507d41c2d0100f40242039091080300d03a052420304403524a1203401d1030340c45020860006000404128010020420944413002c201001c0c10744400c64400e100e81010105544d001a0700e50a845600d51840024000c40d161080f14100028040b04d006071130320320b20540446e540480345154100702c4011480002c2a0705200f10030b4a144259103c1280d9495403c3c6203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 542100080 1250 542098830 542098849
    0x1213020a0b0901020a0f020307090203010b03100e1026060702031b01020313021e06160b1023010c020a0303210b090112050307120801060215090606190308040f05 71
    0x2001040002c00084000c0d0b80c0010b260045035a0051030a0107105940c40881d040c44a95800004034074008000482c011034903001840c800c0049140c06400b2690701c00c003140c449042500d151140d2805024213001070010941c00010308841c840a20042400f00d10902c2d1400700d0488a9500581000c54005210425001c80b407440d141280025819400e015400c1c503661040880b00070b00c56812008940c0b0381031421703818200c00404c02401c071504d0340a140c510b0300c2c07546021074003100d400d035180c000500700200c27443d9030005603020070a040c050445c500952075202d400010768181403114852040006a503400c80322806903129594440128a0105084640c811441c26080d0150b00b071080340c8240c3e85418a1440c1102c2d02e00a0468500301d1b9410301c0740c20f40c80b804802420445245101400850f0081038a504951131031f4201c4030508640b83c9150066501914113000940008020039101c0c40c20880c64014013400340700c034460031a078030380e5000450782c82a07100c2c810000b05c0761320030000c070301d00310031031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 542101330 1250 542100080 542100089
    0xd03090b0f0f040602030c090a180e12030705090a08010207080702101e181a0d0b09011404110f031501020f0d05030f0615071a06010518091801090b010312030b241213020a 75
    0x1040c072460820308820cd10b020040c01c01081001c049158481951001401d4004080c4a4001c6598100d24140502a41d20270f0600b41d004085081a40c07200c5407081e851400c0c0301c0781200303da00040d100c0342011034072a850b4100d5070300d004468544c003141110081010070b05105210207404e50301c000400310001501d00e40e550b214416003640c40100410444188083c8800600b2100003d661030400c4180c000c42c05401030020545501004012015200c000031002c40c0b2800d8084802e14650941019a03503c45500d50000017030082c00402c1c40400040c42c851b4000100078004111085040d20075112a0008841643c400505d1941c141d00c14480940d802d800c00c00a203482842c100b280001c41341c107500500b89003401455071400191034800c000c800c94081c00100d10003484400540c1c140b0951000c028002a107902c410006d4120400e4003c0c812001080000343c01e26269490b031070f10f020381038101011001201541004905464403d0b90090340c130500300e401405500c1912070060008042e0642c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 542102580 1250 542101330 542101333
    0xa0e0d120614010203070f03170a020a03050108340503030c07030c1202010f08071215050316030c05061804092405100504020a0e030d03090b0f0f040602030c090a180e 73
    0x4400c2c4103030340e0110882d00e0b17081d0458850b0040340320341d18007180e03c828400c901411842c03008003800010141a001414003c2c8990340600c0242d80b294606500c60002c030010b06120b030308680300000c0c0600070360805401c0320b4501d840080e0310303503840740401d085600c0546040b59581109606100304070300400c203100609185040614690029400604007034041040c44081c444c036100045c00041c030400d01800c0d03401c1e0001040c0b001d05024210707803c45990f1400743ea0b1180c05003c2510440d0a000700041c01101d0b040b01e00828110300d0302c01070202c1580011100070b85082001100c2d80c060310349000b20301105106402061a0703100e40300700c00c0e0031040c8000c0130300c0b0014241014455111401411842662011100166108070103102551b00c40c081501ca16007501580d0321801006070164000d2815070301030b03c2c1108540c0d903485680d4025040480f1111a100c81c0100031030b000c80c0d07603940510743c80510710410914000182000505401456015200d1080d2025104103141c240303000d03c0c0c0c642e009070740 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 542103830 1250 542102580 542102609
    0x4031703060306060418020a0602030d0606051806090303130e1008011a01030e0f06011d0615030a09061d0706140421080721030b010f02060f0a0e0d1206 67
    0x40020f51a480060140c03445540c8601c50046001907001603044101e0b40100303400001c5a0b2800c02940700d4201c10071124000307240c00c40001d5510300580896124190006081e21f02d02240e0040040d19004540e4440e0103100512446110300a1500c1003c01340c249400350340b00d2032a1481c840c449040840d0482c0c14540d05003c00d1543c6e140214001c0c080c40c0c0d109083c0400d440c03460540162902e221780b5094040d9204042c00054400364840d0a100d02c20016001500b4550380c190038040340002c1c0c1030190b150b000c41080051500d0038141d1100003180c0c40f81c0070115070000c1501f41d50341d09000d0200120384580104034104101138002c9040d5541e9400ca2098605140c80c2494000d9490b2150307090318401c038144464842080740440c21a0b030b52503803000342080012014403070003044480f001200e1000c071345058180e42c0c113076005601d440c48046442d4010580c1c1e659130388004010800182c2420300030f585135200c03201c1c2104280020201c5e40c0241d81c400c6250148d408142c4107640569114400d50b001a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 542105080 1250 542103830 542103841
    0x7171b0a060804150f360803040305030702030403120f1701180b1207170d050723010603020301060b0d1808040b1803011404031206050901180b060f04031703 69
    0x800c10b40e44150400c2400340c160000c804002d014105c01c000240c00340345000c810225a403500d440f503034244000064403406012294504501c5005802030161020074248001800a8401d03401981e01000902c143d03810305a0b80d5403200145d0701c055804801148183c0d0404605503030140c8685240501448241460b5140510720381b000803d8426920400741c0707812580c0c9450321120b401744044d80c03103101107030102c5681c0d80011508140c07044100c1030703030b00031003540f09429803040040e03401c0e00b500005e2400b000048610400d40301c641164031002555299070700000540d80a201c0e43e001050708500141c1e4907105030b0240760072035541039400300c10714085403862001700d40c078501070320203940003540381c20799030b140d89404041c04103030820b81c0c150b066080c20b940d500703070130f001c80d044500442c4640c5501102c405842e10b048140d03150b5024094118041c0e00c010032600c80c0da460303180078400400000054050b9404041901030b80403a64140d1010340005c2c1c20410000c003201c43e888003003e091401c50850510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 542106330 1250 542105080 542105087
    0x703121401150302070609020604140913050c091f060302040f0803040b0f1c020a0302280c11060c010e01060321140d0e0d0206040b060109080a0f0507171b0a06 70
    0x3100400b82c10998082840384c00c10490390701c8a01c00340d8004220b070780c646a5074400d0720440000754003010300451895000c1807202c2800d244518615500a0103030400c3c1d0070600510107492001403030848028205500002c04d844441510f9000d08020341d0007690701c90910080310b40059a50b80141c0ca65032007004204451004034060300c1c114103209195030f0382c03060107070004000c5000060041416030300c00514403154640503402028441400148039802c1c1145400c13100204405402c000301203201542100c00180c1003000340c565070840140900d00340744200c1501c508650130403440e07450076135652509105102c61185007400c114405080390540500910004000c00e00d42141441c8221010a90300c0940c400c5400022043c00c1c144c1c100d82c20203841d088004d40d601020344080d54010110800700d000c5520500004081c0e03003295004112505103541c450b242e28840c400300703071014010704502050385107040c1807080304006514010954a280c1010030340a0030038141d0482d115600c182010800141c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 542107580 1250 542106330 542106359
    0xc0408070e0709031403070312090b06090703270c1a0d2f030f0109020c12160b070504090e031215040902030303101d0402030c190b0703121401 63
    0x2103820800050342c03207000060f902038510703800041c07140c4980c56901e8980c00c0004054580b06000f80d440f10000c01c018108031007100c403024006005400414005502400d00040903500542c9514000817024880400036040510b0320300c0200c034034003944112105014600084001504400c141080904404801c0c0581031060f0718000590b5601e540b030b910104003220082c0a0074000c3ea03002c40c82c03801409071846940d5841211401041d424400c000b0404041520a654400103000c0040c45c400b007007801000120380000032032400041e030300300030000081d40080c03606000d804036403202c0f61620304084081d4250b910050030315200754028400ca4030130308562588207800c034040d6986038504030702450102e000b400c07800328040e4141c4030010034801e03d403a144004100301e54100803049a4039600801c500400760095501940c55400034280010354074000f101c0884140341c658914007110b07680c0d400240c0d00d82080c40250044bc20a50252440c401e803401005400c50b00c0b0340003900301d98101509120200e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 542108830 1250 542107580 542107589
    0x220605091003030c1a070f1b02011211090406090203160e0108061201092109050a15110a0605130c05120a030f05090402040902042c01120c031e0b0c040807 68
    0x201101101440091001600d03801031181c4002c4040c90074506c00741c82031080307903929000500d0450a503907481c204010206400390741659426440c241c01c0024074064145112925004c050400c40c0c00c88654440c402ca100800c036030f1501584a16282c407807112015080e6400e01c05021042002e0011a07074800c0055501400c21612a210354101c82c80c03080c0100319082c00241465062060702c88400d0341d00d4941032040d806559501d660540340c10500c0f00c1900184605010040c050045101d4540a03510021440c03c03400100c0320780108640701c40060fa503065441d40002490900000288045c07031410724082c14042d42c4201c006000c02d189243e841403080c9000d41044070071903940350101d01c220304880d41520002c0041d500c458840440000940c07252240d0070b01c404803542400342d0500f0144c2c3e0b07512405080303c001c0c1709a83c642980c1c1940c91f20320120480d110686c030440070000030490310000c46610300c1011503c403074000d41c6c034241e4401d00c0c0c05842404201010720003003052801c00203104041c0d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 542110080 1250 542108830 542108837
    0x30f02090a0b060a0c0b06031216031809090b060d03050d1e1d061b0a0c02150307080901050708090a020f120703142107020603070e22060509100303 65
    0x35a9041d881c00001c0402c0102a0340c00308000500404e1650300540d21003086020720700800064a51100f0565030303c2240c1200c0c1c503410300601c00c500300c100c2c0500d5048100c2d07003c1d0900d000d403444d640518240810698004100b41580d0780c1e03041d42408565189581d0001059900c940000e2007a2005422401000b0031009855100e0807030009644554419450503040140b040c0500c19200c0003c0700801d400000c0b0880f148150000a1002c2c041d030909414034003041101c0f1480d000c1c0110040f43d0301e552194040e60407113409081520284080d4004611070801c6580781d40b05800e14543d0f45003519006001c0c101000315080900070100b1010a10105040c0d04440d00e941c4580b604000c00c0100080102803441c0303000d41c00000080c4004103003221501c1554000340c404503421500001507101c5034550b090121101841040c005060200013103401c50b0041c10048c8201d6800d400140e51000851480c2031741d01205401c0322950008d60140901802c0f0446400105140c00e8003000ca04040750321024040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 542111330 1250 542110080 542110099
    0x150903031b060b0a0603020c060903070317100b03010906050112090302060c07050f0303011214070602060f090120180102011e151d010f0e160e300610030f02 69
    0x400100390b21903000e2100151104c0c418a58903000503000390485401c40340d00d4020711001607004036000c0b084a41d407940c1516010801e246518075410001002032140558203014200850342001307943c0658003e005004c4041095405d050005101c0381328412001d010908041c44440029008501c0300d5001004c03414464940150341010340c50711006403449003250100100102e400517104100c05541802170030b0030560b07010b070349100580e00c00403071280d030740181c1003080401c42802104010300d4000c45128000b2820a4141c52004410800200360600c0003100080d03a03e410701c0818452106407009000030010007034003403084000a002c080c002c0a6031035659040c40e0140c610070700c079000034250030031030013818203c00c02e00303103800d22800c6c043d951041003c0000096940304802d240c81c410f81800010764442c050181c0c05039040c4001100503544074150600c0e80c407081e66042d107454043c1003181030f4950400c01c51051142400c2d4007800f10001401c0a42c02400460400407081d88130740d5043c0d494008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 542112580 1250 542111330 542111333
    0x118020a1409030a150204210302060411010c1e030f030209150705070e07080604200a0f020712060911040b0a060f0903061a03061501090504090f08030c04150903031b 73
    0x90041e10394009103038801c5c40501d0b11209501e940940300351410888092081c6010140c9405940407c450082c01644a0301c0003e0004004844148203c50103060110510301c641e5280600419600048030315a031001020354141a804090310205c0069030804501e460413244c0807598184007000c0082c90b084c00050350104211f0704100c02c0c0024030b0780c003071120031030b06006400414480055503130703d00c51420904000031203005001c00108554021040c203140011003030342a0b5075414803002c1e040540c0110080047c00c02c0706905828010380c494400082c1140c4a850243d444c243d1800300075024624003100403100e61074042c240401c0e940c075400d021141c0f4034450001c40b00004c2d29000107011034205080f00d5818030704020159481c010031000e652141d59440480b940345c0703c10a0b20b40d8002904120100000d05040d40500e08081c080c0c02410401c2c20103441c0c820266005031810090000006802c00034000300c1d42d4140c1c070303800c2e05144c032110076403450701d0081c019201141c0c25403440c0021680c0c0c90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 542113830 1250 542112580 542112583
    0x3130b0414030a090f06020303060a170c040c0c0510060b040605130f06030f1407090902090609061201031a01050105040e091009210521040212060f0118020a140903 72
    0x554554140c080300e0f42e41001640090500030b5038420040700d0902e000e804250070340040180e0744108009032100102e20b1a08152940c2041000c031038110314082c010881000303849601450508689580341c1081c106814581940b4040c142d04c4440082441c100303080c012a80c05008507401c03503c0720301c4e042d5180d20383d40341c00d43c02140281d88031400c0540341c000d00058490305130b0000104503480c16002c01070441c008c1c201e00e00c4c1d014225860070001e003022005120041c04e95000d801c01081c0a41402d00749800039006c1010303540312040010500c074a00e030040080000700c8440c00c01d90b0058042d684055450040040e00364060350084a02018840340000c0d041c0c070042209600f600c5080c03606112090300d505003600c00443c042501c3c07100351408a80d080100340503800301e0f1102c2c000c5100804101401200940c043e1001030012070380300160280304916014100a0240141c00080c01d50301c1c19403504c0d2006000c6280b801c4901201c50060082058068001c500c1101c224198600703d55101c1c00800040e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 542115080 1250 542113830 542113853
    0x610030c0207170c0a0602010b0306010605211905100b0315040e060f1b0903030904090611030906092b031a03030c0601050405060a030506070e13020d0507030b0603130b04 75
    0x255491040407803010141c4400a1104c06440d401c2c2da868032004d460b0b0008038261860940d6081e0036a00030401000494400c0d001402503012411850101c1c1c220060522202c0505a0342222483c40d8400c09000071000b0348560b98009062035a2140700a14000b98401c00f0f000050a0b4034920908040702c800948440d00720f18010a07055040d66820f1520700141500590240d4810110140003455400b0031982d542c22141441d82c002e000b107041c03103007400c00c20000c1d00300d04074200c4681c1d441c1c02003d4207120f02d4a001d0b40c050300d100e001a00c030307a19100910351b203081007450084900280b41101182c00501c82c1007051039800c0d180ca0081040b20700c09803803820000340444025090f11001441c2a07009001059450698404503000e00c440d0301d481c4100b008905e158000900b09800060120b10254003032018103184000c05070040c40e43c210f043c946141280c01151203002802c2c0c8580401030060703030600c01c01c40031050407104a415400c0c4030424500309540d1b030f03e0041044006001107400d105040f2440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 542116330 1250 542115080 542115089
    0x1b060b0402041710050709122a03290103020d0c1802070b0f040b07050d0f02040b221a0c01110c16080106080303060103180c06021b090610030c0207 65
    0x707560700c0340d960300c000701c85440e521000c000500604480d01d0144060380200c6000d80c1059454074401414010000502810507100300c0320100d51812124810321130090092071112402100b00740c141c0786042c086c00f91240c1c0d4003181d0080c500c5480040c1410360380310196044d242c05844248190550b40340c01c07408130b5a80d40005944492808508881d42c0ea50b40017007005a11420114440351182e10100c3c0b00b108058030020311400d2224005a07400744103002501400048010119201815481180480c0e0060300004001d40c400500c500443c00504081041080e0111800890620b0502050481c0c1e44140380d14001740310003d409500040d094011000740c40c41030000070354a00707440032000e6986007090410030088440c0309002401c40f60611680c800c544002c805545141e4842004400500246092040000507805a00003003030f410040d40f00030f854960018070103040214075400351104968240c0d44078600c00e6081040a4545100411a1400c1414080b450419030201a41000240d400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 542117580 1250 542116330 542116339
    0x30b010203130e150409020906040b420310150e120a032d0e01110636031935060402070f0f02060417101401061b060b 52
    0x90200d03118400c3c11070075000d401d9032840664400704410500c401e071141d060700690300903c1c940c0001d403541000d8000b280c0ea08401844414400c20320b000a4a4a041d202d10700c0034592903802149040000c003150450000e045100c805041d4500704850401915a60107400400c25038501c69001e8980619141c42171110f00804184a209080c0d205a03513881400c482a000182c01c9040d40020003043d51544204021031302d00103d0b181c0b600007003a0b0340003140450341c03410400b00f00303003d06010b9411f2005900480c01c13201200030350181d494000345040300f422040303401d00c3d2031480c12043d6003030000115209209401061050701d102000141c902c040c480c200420f007a4192841080c000e80304409000c1042c0300b8000210807a180c01052108a004032003000301010b04030043d1070041703216070780568121440140a80d02c1c1c0380d1284000704001901d00d1800003140e101c09c000301c060f0a43d5015540c9012003903200c0e80c000d0340c0b40c040700401c403d540c81d03a00702d039451400011a081c44880d401c210020b100142 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 542118830 1250 542117580 542117617
    0x40e03040f06270f09090807081206040507021c110c120a060c05070f020d022e11010c050a0503070504030c031a0a110f13051207050a0603050115030b010203 69
    0xc001804603041e03500501000743d0a000a401c05000f428501000c1e1441c407a40203610070b0074140b52a001340703003d00e0160380c1040300388041c100050018008010442010350840520300b0982d0511080c0c2d500a05130b81c0035034104034926074030310440c0000442400c0706842c1003003042c00300c60130442c140705521003443d40000d00c00e0911080d10313a00140000181c0d109070001c01184284540071a450b01507030400504000e1040e95680c05171400b800b01e0b006050000306040c0040e60140c5d5424034000040140c41d01d0781c80c000c0082c0070170b60313000441008000e2181000b40092784142030000c1c1248102c215074020b110010000c268060312650070743d80a10f6120218241840e03c0b400d1003c0c5410302503a03000c0c0a40c0054000403904a45405030341080118202d8090a108101c200005260404290008081c4810400003103d0740d40c006659603288001020b0008181404144000a07155070001002c0c941000c00422034491103405001c04100d207031030f0000b10100c80000407402c52048000041d942c40c13807070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 542120080 1250 542118830 542118839
    0x7020a17060403110304140607060212010f09060806040b04020d0305040914220b0a230a0c0e030a050d0c02060d1a040c030c0c060203060411040b07150b0f040e03040f 73
    0x1903854003940c001e460b200104003d13405075950704d00c10341c00740f048500f40c4071244146908020002d0600702d03204144c09030420303d50301174400e140c5200764841141000040410802090ba84c4660006802d817140981210702d05600e60144581010308020b002e03c403c041c002e000d00d4400c1041d54081c1c80d060100b8051642500041055150f003910700b4403400722261030707205180300c2c1c9519401c03060754400c224060a540d10301d20500103018110a076110f442c0b0790803d4080c0c40d41200103440c8138044420340040c0000d40c4540c014404108021198060b134060000a000f14000064401c1c0300d072514075086114103054808913071203014070800c40300344074202205c000520200e083c0b1450800b0055808004407880c0307880480c16202501c0c90302e40461141c0c070b81d0f400418416001507610990180001c154800040d4031980c09510550003800c079604080780c200d0800904800e195031411074240148110440030000450014070b0594107480340c0c0d595907816007410014015a0300500c401c1c80b1441046649 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 542121330 1250 542120080 542120083
    0x30703090f050d080609010e1f081002040911031e04031b05010b0310230903070b0403090608010b030105090c0d240602010e01050702071703040305030304113307020a17 74
    0x2107104070f0200700c48800149080c00c12201042c102e4652000c0660603480d1005e41e40895a0f21034016880c00d0110a030110750860108140085102540c4006a41c0c51a20080f0800c8800c0500d003900c8601e001c1003405040030042054404181c401d0072400311310f848900c0c00755031502c10182030510200001e5101c000707011041d03201c449050410b030107542c1c103a40d500131208115540000380c2d505210902c1c400b03800c40003500315429401383d80345048074501600798a640b20f6030b0404a8048002855061050202c154084001801080380c0e220050031941041c0005078441700040800c22044800f140c00c10320708607030390064a01c51a0306000c20798076441d11040b00c800078816014400140d802e01c403240001040500c02c841c81411203a002c0c1c284a0b00b01440d02100c1a032911160116100038040400407403001e05c01580258420300043c610003840700144511030325213070310310602030314944031008600e04541c3d454061803498144031642c44901c3c4c070003d400460719802c0740c0380303164466103050700b036000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 542122580 1250 542121330 542121343
    0x30109020a1526071b020901090e03041d06100c080702011b170301080f0703051e0a0804120221070b030a1103040501051e091507031d0d18030215030703090f05 70
    0x1316503440d040d8005180c00c1460a1030b9448000f9081031010004101900241d4003802640480d03409803860700c0d9548211aa050510644400c48601c0c0d01040c049149000d1003000031040072420061441d80203505c62000c0d034051450080d06200859000c8070071040c454100207042039022000554120070300b03103400d249030024020410300d44035020814051210001d00103044a90040080c800740110b95030303a04114243d102030900c00d204e00c4400c0b80015000801400c09041c00c0d0303040846c517081c82e0041000c02e0707000c8060b41c802c0c1900c10340e101280920100b443e600f03540c4503400c2c450303403902d9403021800240403086510540620100900003009019044640106d0006405628810550010200105045d2a044a60341c8035048060b42188100070036580810f0b40d04001401011840f040d281c0103000c0d500101b450740141c1c0c20880442c1e08200030041c40c101032032448680341d0440c7c2c08202c401c4a015401001c0440c04000038241e20b2007600310007061588a451500c0d407a00c146031803640c40c403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 542123830 1250 542122580 542122591
    0xf04090c15050c071203050f0316080106110606100e0303070605010e0105060a050307210908030708010e070f0e120d050711010c0f0311070e01080f0c030109020a1526 73
    0x101c91040702688a841202626841c204100c0640000c915044840800782030b001c400f10184171051090712a150324030f01c0654030681003104148504603034078600800700c2070140c000e1001d011425901c02400040001c829034044002d071407500141c44010019103c00e4521b01159915100c000380e070800300b1030719402c824120344036585070300b20598a5500300205402000407000c000344050001030720702d511403072004801c00b907110581c900424070f40c2c0000b0217a50039541c00781c60030b400000c01d01036060f03071019541d4010300b004034245209007400c50b001040101f4503050001007141d45206c08446546401d03110211601c003100b11040c51100590181c4940c00c0b006040c5c401c126100740040f1154040c1e40000f0f281a8040f026000502da195404c0d03e042481900160061048103000b05170a04030a0445020300294030080c918140710b02e011919081000140500036418000c4040040c5c54601405040c0c0f080e1411460002c01002401c440c5403409040d0007041990300c1c013038055aa00d00c80b81003030040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 542125080 1250 542123830 542123849
    0x3100b280c0b01061805030712020d06090f0b0f13020f0f031002040e07120c0c0605090c130213081b040509190321020a12050c070206070507050406120308150f04090c 73
    0x70f1b50b4800401d52a254644214058030001640e484014940303a05041e05092003800006280501034803600c640e030000c5030040356038403035003c188140c0c24461540d41da03001d0018078488103103611a5001c1242c0c2c48800003068041e405140500f00c0343d51301404500260f12070b12004544895642c42c44450242066440c01e012a14800401c500301d4124000c15031a940d180d1650100f42d886652064010540100f040364540560690101c107507650102c8602c01c02050b03200540c44026074003c084088410303030302400c481d80c020716920b800c00b001403d00044070a02164000341c607595202c2c0e07507400d01811500c1c0100a03c12000f2442c04c068100c120500c0100440c244000c003c00010740c00b00c00c81c8298000040407c4100310f007401e21042c181c0065521a66408081b400c21803558041911b582254000f1074130360704801414000d0741803a00c251802483c0004a01e0300c921550b84025101c5039001d051403c901c1d42c0c940c10159207480358880613604800c0a04100281c41280c1000c90011005001e41f030b221 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 542126330 1250 542125080 542125127
    0xd06050a02070816170c0c0f0d1217060a1206050a02040e0112050d080112230a150c05070f030f0c02060a12050703020301050112200f03100b280c0b0106 67
    0x4405c04403c0e241c0303803c41580200200b070b85c4141000490700c240d0f001960b1096002c1035403030000d840103200782500300b51921140009034000c00810002d1703030001d05071800780b403203c0e030100b0046804503000b00c0d2240c1c1101001030701c1c2e101c218140700070707101c0c1d504a04802b030182d07000040c00101d80174041c408030303000d842910a00d9806c180201c0b400a03082c42200e030018130004494002c1f94441d0300700101015140000680000800500303400c1180c40c4a05548208503803c100300450002c1c001c0d201e51071020724106103480f00540d291003046980500290803c91326642c6455154003404000124680042185031100c0e59200300404010326641103901560606c00030410403806030003500d0684905854200541742c01154500042c4583d070200380c2c0e00000ca240411010714071000a141030700e00780d1441562482d002d8500703a400c0c401588000514001008100303000003a88500407121a280c01c0840c1c058240618200e54100320314a02401c02e003c0c0d0000018015040a800c50000c4000400c0d00f54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 542127580 1250 542126330 542126363
    0x17060901050f0618070201140a02070507080a030203040b13050406030b04110a0e0610051204030e12060408030112110312040f05120319051903020406030b0d020d06050a02070816 78
    0x7070b280c0c016900350790001c0d9456400711048941d032140c0e961080c01032000256a41800c0300b050024402610121030599002070340ca0148401030080d103014221900081c10021404d54000b59a8412441b03002009800491334903c03092000d1000c0000b064020030a00c51151242010aa051405c1e40c04030340341802400070803801d040c881c8511048032000803003540140c0e184400e1003503e804003000201040f0382007103c0304400e0260301605008600940d10380807224110310a1241102d100405440a68000002c100005040c07108076070540700a04880502d154603407a100e014200105580c0c0e905005c0d6840e80001d08030940c5c050402c0b40d00303074100480c58694800038404112500591110a07401c100032210100a130744c11a000000041c3c9851444c081d0050414400d43c004000c0c1c2c4400660009800c102507685400b840d000d00304115039041109240340d00090789a404140001c200c1c641307550001d07120640301d60503101d01daa000780d1001d54890600481059000c030124045841c1e0201b00c85202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 542128830 1250 542127580 542127601
    0x60e030a0e0d0210110102040801090f170301140402070201030e3a0c02061308030a05070c090507120b0a090207050606180c0a0e0a090e030c0c0301020f0f070c1706090105 75
    0x19403031500030b000444914015a8126080d105c4221001d0315503400704070016035800700348200c000f01c83c01b0307801d20480c2c1192840c1c030000c14207512402d09400c600c14001071000a00b0452801100b80e030407280103a8a101b2031006a016040e0b41000c0c40c4d03c3d02036035a41402060383c4a01045a18814404a50445245007114058282003822400005580710711950050822000820b0f1050014003d001499520010145160301800305c075800100081145020000404207035005800402c50074004c0d4505241e00034040c2c103c40894003805901d400c80c0f846961108600ca8003e0880010103543d2408281841c913503501064034103038050b0404030000f11802e0000341c0c0c851f020b10035046602d494284080b00c103c4950805066407540440280ea000a0b03c500d10311642440d030003440d014544881c6410040e03420038102c1510035000740d00401078405a10010030455500c0c041c200d51141d1a030540d400c4c044141500c40d005844107450b42104a854008001945880344d09114001d00c4a540d80000380c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 542130080 1250 542128830 542128849
    0x20307020f0f0c042304081803150c0307090807062607090b030709050301091a070e01080705130504060608011a0412140c0406062006010f0e060d060e030a0e 69
    0x142426046000c4901c5203140c641c000044004011600010100c06170a204072025003e035000c07142d402000400002c2c0c00c48894107074501c41c90441c00b41010070300c1e1858141c00d802c001000946002d40010010341414010300112020700240070890f04035907207030000030b041d00c0364284592010300041d030040440100071a1225101d85000d0703440d211620b15103030456045030400b400041c03c0c041d81c4500031071141c0f02445a00105d038000d0325441d8501c961442081c00c0c00c034000e4921402c11001d60f801c600103980101d41c640c1c015400c1e10300266a5014152429025210385e0081c0e03500c00d00342000003406540c414040783c165040010704c001a009140041030462280e4031440301000700d2503aa4102113002120314121001c1d440c4142d0394191800800a4101c0300c0b1038103c00082034103200103090000c0ea04501c2603480c19444001c00503541001c0325110142c0d4075209440c14042d800e0005401500ea61146804c0702d58061401d01c130400c40d40301d50b90b0700d90b0000a10f03040000c001c6400100a460080c121 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 542131330 1250 542130080 542130103
    0xa050a0c290d0207050f100b1519121e060608161d0604050d060f0506030f0606040c180305010f0f0902010c03080c0415030b032b0e0d15020307020f 65
    0x8140742c4051409441d000c1d4105100c1540c5c0d6008522079504680414494140d02180744000081d032016a94204034030982011840c00c4c1d00b107020700401118070080301540c42c0303041c090304080d500825101305403809440705c12864608100f00040c2c3c106040241c2d0095000d5802030340740e8159954030302d1405020468000161320018482e1060740105403043c4d10311180c0490054100d503e01a212404940169045107003194132565401c40030306c00111a201e541d40140e811800790015400b40e400155a80300e020b002c086c851947d4650300c5a40d00e0103034a289049003020464280203599030304080f8002c01c6d200f01804001800d001c00e555240303085209190a40340d058480080544481c0c44c11116171200408042410342c0801c0003041c00c240d181811030070420159000f1904596817414907060880300e4103400c0781925440500354000d40b01c0000299035500b940341000403a4411000580103084400d00a0051150080043c1075800d880d00114892010340d000c9070032103500180c02e5982c900321340c0349 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 542132580 1250 542131330 542131409
    0xd020406080d081e070203120a02090402071506061d0909210c0c03070b0f030736231314130308070c110118030614040215040f06080402030a050a0c 65
    0x48068020807001c0044e0003185149e40141032803000d2001c01c0480c0d0280c5000e45c2d130901180c07880d0f15000440d0044002400080c50700c5018509a14542c12035150348201981c07141c0400c01c001041c1500c100043d14070030401c400c1081c11303240343c0210070800d03a212040400060041e83c41d05102414000b078014202e4880e481d81034030b4014802500200c50304050001c000308940e140302501081d8200c0e013014119175a001090803801100c0200303294100c0d540d0f1100042419000c9241640d20740031500301c010b040c080d1141200401085400700c014904808480c0c0c0e0011110140500d542e4000719040c1442e10a0f02c580c90303952a039000545d004005240b0017000e4040e01c104010703507540304816500c0700d580107007902d00c14140c80f0743e00c000540301681c6084039514030040c00c200c1946442d9603403041341e20301e00b44102e10702820010101c04210f00c90140609000440c40860119102041480591500601600c2c0b41b040c0364501202030000c140700301c800c0344440d2400040344581001708540c2061802c01d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 542133830 1250 542132580 542132587
    0x201060b1204050a050d050c0d03091101080606070c090c03050603011401170a0b0a02190f021903051902010b0f0a0807030b0601030e0f01050118060506090d020406080d081e070203 79
    0x30901d50451401801159240600b48070007000410410840640b600c0d0381d01c42c0307501c03400e07520804c0b0314014010008a04150800e81074501191b0041c1c0140300b156002e2030000b00e140d50320307808101a84a407000041c0b00340ea0011001580014030351090310448529030741889192146401c03d42a24062082400007100e40b0300104914406213412940c00d034894010384258000715128545203003000c90b80200010f4001409548004845510800014040c14114150410203400a688546800002006001844600e4181406801034807841405c506420f41190000f140c002d01a00eaa0707071409000d50344050142c030440c503141380400d00f50f40400005000c101c1c030355124a2200840600b04e80d050541c1c550711041280018404003105030311981c00403c040d4503048201c0c500c0c0c2102880090600c2c6024410b028a6550100300c41121400700d13500c1400e00386034000103005150741c1e07001e80c4040c41001c0c841030410340c00c02100e9108440d01345110301e08400d159807420150030201c41d5280142c0082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 542135080 1250 542133830 542133847
    0x9050d030b06090f030f030a021507090e0a18080c0f2b03051504060f030308011e05060304110604080a0b10030f03120b0414090f1c0c0302100c0c120201060b 69
    0x50b07010141c0d54005c0c1190440010014814110780c00061941c006803c445401d0440089480b29160004001d10700340030454641004180301f10000b4182c441001d0f2104000084090034040075180ca039040080c169032040d1401c14103999021090560307040e4020342002890001050000304008400104206a02600f8031811401018001d20702c2e000ba001041311001244c64520802028001e84925000b9040c00c5080c0504841d405034460480c051140f07130500e800c040f6802002040380c0c0242d68960712511540392034401c1103080003500790060401704001503255070000d0a02100c9001c2e85180c00340e074a40310442600e0101c10300010b0302c00d032061901040040c0c4501c03034186e40300005280000308610b94400140c1070712002c10f052110b080035074061054122080c800358500700103000c01030002000300f1017280c0d907006c20540c0c01d8050000200c900b005041c02800882d0a01100b0b54080000c4001c1c020007420f060841c507025500d00049550884040b03005105100c15120791040c07460410206 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 542136330 1250 542135080 542135089
    0x1e020a02030d180f0e040309080309010903201201020d0f2007030908030c030301090c08070f120204030b0c0307031103010608011418090d02010e0c0f19170109050d030b0609 76
    0x1d041e18019100100080060700044c00b103020b2010b4401d0a0350f19145080c1820000c0034500d050700501c24603081003055180f0f613a002944030003240e0f0b001e03d00004841030076003420590307005000915000321440c40000d080c12030640c020710259241c8103080200e43d580241c0601203410901c00d02c1642c210401da42c1081e4030040380940116172091a001d034000e500d81d03502c0740c2141c10551001c1aa5130012005002003022400b60800743d00741ca1500202614192000600e0122181c01070707010300001c2249400c00e10070340c0e01254091a00541d55101a041c8644407281c1c56004641d08c0340024a01031144204510a40440741210400d41d40d5001590a21800284110101c0c1d200e0f54401d0051094003100d0016604040c818095800075166030300c90300c60003a00b9100340c545400340540011140c41000c0c0e0301d41f49881c82d92a019a130500e0664011264040c0d03259490b0000d1039148613024600101c0c16054202c1c3c0c90365885001a5040b112001d94107806480501030100c1e4000402d001030f5001d03050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 542137580 1250 542136330 542136347
    0x15051b0d050c090d1202060c12040b07022d120310061d0a03030e0f06090d1b030614190b010504050118030816110a080c19050604061e020a02030d 64
    0x80b18662450304034000c0000c0d0300b075000600101c0741004044d0003807803030304d03014020158041500000e840c0b07414643c00d901028040c00500c02807a2400311008078035000d10800c025105201d281600380001e141d103000320701400c480307101c3e0700c4080c3c41200c0d01000e07a0b82e80c01007528050310402d1f0303480da0381c03a041c4403094038031040f8598841580d11100751001c0c040c0d40c4440c1c1c200003c1d40203441300c80307100d10054140221115500c828a01898041200c11029181e00809981d407540103820a80b04501000c2641c1da000c14661014251500300301170080c20f00b90006465016442404001418407085100b20b03007603901d041c440c1404240c1c01c0c0f008100c0703540204007a00c0440d0345001060b640d10388aa5901005030059054030441c0980d44200300100424580c1d8084888005c40d240c00d10a80b40c8a22181ea89910903000c034003a02c0800ca60042480c0a0642e4038080c1c0001010a81c0702c54032114014012f035500d801d0300300e0a00b030721200c4030015030010915021164015001d4042e000d8003c07404d60b0701c0403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 542138830 1250 542137580 542137591
    0x1107020108130506101509030b1b13060207180c202410060e030604021c0803070f03060909020d14072c070f080115050d0915051b0d05 59
    0x5011070300c14000801c00d1113680d00c5018010340c0b0707445040c1420255a02091000301c03100c02d10408110074400b1440c40015540d00088008951811040b4181a001d0714081c10031040d1000503401004911540c0201b070740380584e4404d18405110042032509407003910700c0090b44d40b0102d042200d1640381241d244070741405a051680031500790341104803100b41ca80540304607440032482d070344051280d45c62051b0324041c000c00c40b9140038081c0c1c0100c0b000094a400000d04004c0c0300301910b905014800300a04030004d0f0f0103401517003103a02c07860141c401509114190a14000092034120040b4518441d40702d8611540d030083c080101c03908460380c8490740c83d04c10424030619441207200010340070707400c0c00040c0140c0a9480d0261021002c10402151042015002c00c05000c41010101d25450344204101d0450f030000000740003201912105a440340b08090010070200d061059200511040d07070f8100794150a8040100803e0b65421100843c041124095042ca080c040041c000055450f070021600034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 542140080 1250 542138830 542138851
    0xb07031707090f120b06060904060509010803210702030910030e0a081b07050303030705160611130501020106050609010c110a081f050402011209030e28091107020108 73
    0x180d108842000041200d02800140740400d09214508440c280d00004240c8800810f103440c1c026543c0300600b15000f060140a00380100b01c082d1180e4803038016800600c2c01504005003035031a22480c9031a54000200040e030070208030f0348078049400c404030782c0d481100b81c0e9003d182000c0c541000c11411520124920040544480c0b913030000007404c1c04060905403203408915034408500c1000c20a0450f05007040050340c1120400304080c1d01d01104a9501c142a85040c56895003400c169404020700740070068400b030b20b0103200e210904582d100806c0b1408080c2c107400d00c40c0ea6504012070a0b101c0a00134150007000501440c070855006034000ca2601d0700c540e1149400c1d500c1d100c0400d000f151180c0c0a144503a2004008000d20301d403800b0781c100c56500000b018002450150001307095607a410f10141e001c10390780c1007008181880340b01142d12407000140f04c09004541d5a444e0446a042440302001041c0c2d9148009045041d43c410034060981514403e400d0104640064485602c024803403a07a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 542141330 1250 542140080 542140097
    0x141b0d021309050d110105060307050d0201120621152c0f0111071a0c040501053601020d0c020906091b0a021b0306091e07050301180b0705130b0703 65
    0xa000384000e5134075103025035030b5030310303211160b41c1490940c0c1020b0b00e80c6001f80c10110040c0555214501e074202203030380a081502c0601807000308403000707040652008204810711405104017628080a5284043c02400c3e140083c2c400104004222054038400c0050310b42101c020302d05004e1003c0e8110b94a100d00300c19a41e0340540c03603404070b00b56002a41400c10000d07000440e0700400803074a08003203a010000c50302a01c03524240500208030700c25400b40b20705009021590040c4040102890078040c2c41d00d07040c04070100c030a0f24068841c2200040624054010551580c5440388680306484031a6001404005079480e00024070601080c05040c01400da031002c82c0b03a1005461400040c01e103103d25900a280072804500e0342444a40903820480c4a60050b20a110f031030000091501e101c000105106405030300700014081c40d05601e80c3c001ca8055080455000c0c450942004120308140611808440b59030740174001c81e254459101e050b001e25016007000e00c9a0100d400c0580b11261090602e4040c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 542142580 1250 542141330 542141333
    0x8061801120b0105090f070e0609060d0c1403010f060305151f0809160b0706020702030d05040f05090609040b09070f030f060f151202010306090f02190201110a030e030f030103141b0d021309 83
    0x9542c0c043c2c040081071035220840c40185560003500c048050b11005110303821941480c0c03020704001092d1150004146e00c4030007040d900c001c40507440380c102d41d000708121240707840940f00710803804140c100000400c515a000900d920404a1414144015901039035665030905007005615040440282c8080c0e03400c6c0900780040e2400c00246080142549030991070310f01c1d00c0300b0350b80d803003c841d000980206492800c0c4030842c2c455001c090381041d03002191043c6580c2d52008130f031810728207521190640c003000400006100200c0401b442d01402040e0034810303260801406001d481c1c401000c140200f44c4140700f000360804d2040c981003031920502d000300b1107550341e0092200303581441507480000d52380000c0e102030700c2d05041080c249826860009100185840586040d14012a290740c0d09050300d82c4120b021034241032080341c600390b038030302400341c3c40e96100e09041104103186c200d02d5165106540d41420090300403032900d010700000424400036002c41d5030034803013a541209815101c007603c40e0741c1c400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 542143830 1250 542142580 542142589
    0x30a020607260d0f02070b0a0216020603161209030206040b1024030b0103270618060c0f08060619030209030d0f020c09060904020108061801120b0105090f070e0609 72
    0x88008000030421600c8444600c1c80400300e501d107101400200344104038110011f2000d5140581c0507c62100050304c81601c00d01c820854003846100940c410000010042d048000042d1461a0001d80e900d41c6020035484c0171303d000b1280d003040c000d005640000c0c0042d0021b603084c003100b41d02c8409815107620a554501040d510740700c04103c8000703440c011118400c003456240c03107070044a0409103000c0c0140001070b0082c00b4106a00e4065890f40c0701c00e10100c03c20305c00c40f81c00194050012804260700741c00075040c00c000410020b0060800160300b1030f90440d40c01c1c403600da028054580101400d01c1c10707000b5000480c0452141c19440107064003803003611407542d0b0501070400707078030316030b459484d1452504d10009051498400c501c074414410b40042c0712054443c0d2108035802036080c01c0120030b0b41c03208000118469542181d015080410400205182c418860640e0145100e030b0307844089a600c030810010079030f80460b4003c02c1030b0403a4002a1030740e4400da000c911002c4c40030388034919040d44800840d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 542145080 1250 542143830 542143883
    0x3041e0807060519050319020d0b19140604031101032c060a0c02030a020304050904020a1a0409050f0415090c050a060809060604060b0d0c170a0506031b030a020607 72
    0x800468000300d143c0c004030440045039003030080f40d445c10341d203103180960b100e81134203080c4211942003d9000c942001400101d621511040c0002410343c12268121490154a41410f0181c1e5443d0b1210180f40c80042c00c200742034406481e404030044060165040044008009051246402c014066414003e90780208441001c04a000000d01203c2c5441c000ca9001d030b0b040c51031200c04540c010010201c850368040b081e40c082d240b0860b860340300ca403603900005406480a8100e42510046480c00c500b4034001c00b00240100d0f0801041880f890b034410b8100c0ba01e01c24100d8014100c441580048018050b440c1d0018000900c01d1940790740007030b06e45021441c0b076540391304090301150341c01041c0900d83c04100000b507406102158140915414128558454001c1401c00b080c42c5071a81000c00700c03580551100b44103004031400325543e51820a10303010140100392002402401120702050030850403080702021100054010311040032641d0a121190344100b5041d0350a480301e0b0b0101c2e50700ba5441002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 542146330 1250 542145080 542145089
    0xa0801020901031d07050111010b0301051f091116062009180108030a050f07240f0b0a06120b09040506042102101805060a060614030903041e0807 64
    0x180c41d414690009030407568401c0152500f0302e00d1001501460b5000a645400e466082c40d28070400c00c903020030507015110800c540743c1d0650900d0104040d0301d035021250762280781c4800000207010380e251586412901910080c82030b420080000c1801030040b05062200c0c14410000001c0782d0508101c07004004c2c1301750440c21054000016008124500300d10f01c0c201300d070750f0461060019403600c40b00d41c0d5240320300303040001030107000302d800d0402d1000c0d40c0954202da6000360107440c510b60030710241c0d80013900492030200d503149800128030359a00030744108842c031540a04076849441c10540c051b61280300e0b0481402c01c1c00c0d1035408801581d00d45203c1180298480c0004040f1030070a03103080504400c0d20461031540f20170b124030a1181c554001882e007070000b00307040d0015035000c40c039024640b50088a5400b804a11809050115039507141d8883c104490495503081842485000308180f9444182c03131503103903035005001c1440420400c5401070b26024403050544422603075171907072608100041d4007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 542147580 1250 542146330 542146333
    0x1c0b011b030513270b150c0a3e0d170307080705030f04030e01090504090b060a0614031b1306020a030212040503191b08060a060e0c030a02180a08 64
    0x406411288840c08000d0140020002040000c4d2055001012450102c03510103c1e958890010540d5611050040c0c05050310342e074801640c40d0800074095039200c0441e002203442c03607040c00300a80c48400d480018016000d952415062001c0101d40039000426805101a80701107410482e80000f04aa0b080c1c6014444003d01d603500c81c94842005440e440d0004c00301001d02c07c082041101c03144040c568207030310650508202075240c1e004c4004850000e015004990000c0c40c00324203d06000d0b541c40d00c2441080d045420701000c5481e107104079110314110201c0d011500c0300b031021900624100d03486801c502c41014246050000d0400403802243e981c0d440319025800c5110f008081c1b684c18041401d8a400000140b49814604004242c0c1c3d25080c220b20076001802c030b4510310800540a0300300701c52412142118030050740b00e43c9800d40303990f410781d00b054a1034a007450000743d000403220094030503210900c80c0e0f400e6a681d4000c800203944945803e24481012409900b03c40e0744420010015012140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 542148830 1250 542147580 542147587
    0x11030a0306032a09050a140403021c020c1e06070c150e0d21020a060213050109080a121103190e041d07050f061209150c1c0b011b0305 59
    0x51201e001c03911421030b01c1c20007040010384007505081090f148100c5060ba80009055503610181000900010541c10b004040d0b60007480309040e80062844d0300c81c0869204003a08030420708040c0e0340e0f0306c3c0c0f41c02000c5e0008085400e940e0317200c0400100030140940505a1850404540d542e822045030300e4200610ba43c0d82c1e03482210b078250703100508104c0070b80151411443c010841e01c40d200003034505940f51201c0801085503144035032013400741e2204580d000b507040d500c0340180541c140d040c007190300501d03000800d114400142c03803100080203103c0d00c0d0402603001d81c494070b1081c200c44070780121002d42d2541c0300c10003048160503222000f000791551541d0314503801500d40c504000c19501600c0031800d0380304205200c2150f080c004110341c41295021074907048216010030108009004d855002c03000003241100300068603c01042e4229210000808640305580d802c9500741a070041c00c0000b41d5556100d220b40c0c141e02501d901c07130104044141012202070f591030360400120317451890110001003020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 542150080 1250 542148830 542148833
    0x31103120f09010908070609030528140f03070c050f03030709090c031505040b0a090212010602060702070f0308090414190c021908090f0a08010b0a05011110050711030a030603 77
    0x80003904222500024000c1d100c141e1a03003175480c000c1c0d560141415907940e40000c105800b6030101d40c0005804100f501c01820000d05040991f1303094100207000c245100310101211840b14101da80e0074a0080010f03055840d902c0307089a000700f110394100d036103109860301c41c6041c00b41000070f584a15040e59555122500340b555000070b03540382210203011315051140241d00c5281c0c0c1a0b41e10183c0d03000382c1d0300140304c0b580c0800290300581107502c4a0b0010f80300143e0089070705000d2041c60b060b40c12036002c99410b03485d480412603907450305228011154249000520016800c0002407124650082020030100504c8070300c0401140c013524404031030b00300042c0040075103c2500a071030020815002500b40c00c0360381c0820b050103114181005100c4100016400d0442d65009041c80d060702014000c6240301381c0341c0388050700070461400d4051003030a27010000a03042d881507541030100081c020240c80311703003007081c03120000d440d010b080602403001999000d401c030342080028190007206698013090ba00c2c50f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 542151330 1250 542150080 542150101
    0x1305060406122103060f0305160e06180c191e09061704021804120305011401050406081302042c070b0301050d1707030905031504020f0d03110312 64
    0x120b90000125240c41c40e002d50204a0701c07840720300d0041c600e50440310000c50303d0f0b00407030007403180d030f00036410501007410301006012000502d010f500982180d100d40c010b44604c460b0102220440e812a8003405032445241c90004024110b07802a00710103030582801701c40c00290700e5680e00c1c180c01750005031035880e4001520200e90000c1c081c1c020203040100031203007002c1c0000c1502e075000b12420030340007540c00860115103400d80d01c2103c10605484d80c6072681481e240c9180c82600354144400041d051400100320702d101161000072101c0c05844407480c05241c07600c2030f0392811009000002c1d01c0200c0401202680321801205109224060b8455840b400b14000d0742c0e0344020309003020880d0380540d405008621121089170b06560045034034113200003252030543c61101000410f520780010125542081681142004060722002c500340c03503d01a00540c0011a0882203401940c058046035185c901c50528410300c800040c020b1800310642d0750314040302807956200300413945004a2003002c11460142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 542152580 1250 542151330 542151341
    0x1403040f150f1409040c0c080a080610090501020703020405060402090406030804081e15060607080409020a030605030a030914030c030a050f011b020706050a110f010c02242413050604 80
    0x240d900f4048036403450242c0000341402034500603406aa500c00d16005080e00030041312003219802554150f880b25080313802480c0c01019a00c4a000b000450790a401a6000f00302a83c10340d40180d005042c02451502000b014090142c503482c2c1007682000078108039119801194061806171844a41d914900000c440c40c00349000f50141404a18004041000702c0c0401e001854040c0356442071029222040007031103500c540800200044400140000c012540d60090003510403152000c0080c1c076a00c00030f15803508298100103002580c508000d00452404000c800d03038800000c0e045401c0c600e5144040703490202c40c0d800070b45040c2d00c82c1d0110b55440c1c01c240610000d50210700f2080f20181070000d4043d640f03404600501d02400340c081140204148a2000780d56807200035421110085007855102e03000b458000c0c2c940005025940e184c0c82c907008a1000e044210410002080255803107400311a01d12401941c1460640710b0310340024910740c0e0350031514007001c4400780001040d05042c1c040004072076 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 542153830 1250 542152580 542152607
    0x110a08071418060a0201180c030b0709031109090309041a0913030f030902180117070e01052101060801020f03100801050115080403140f0a0e04020306030a1403040f15 73
    0x1040000c964190340c000350b40c030602002900e01d96100d0b51000c4040e40504005d4030220343c0f680d1400d0303044083c80740d41180ea50440f8011151a10152284281151741e070b8043d0002030300118654168900c0c0341002c807455503200b0426400c0c1c0b4200801e4100240c01d803003140c41c0e5034000c24505070400c03605142062119030801000042010103107601d960103841a24030002d048141aa00d0b113120b4299161440700041841c1c14031069800c0351b8440215a603140b100609511561090000110303580c0352000d0900d0503034800810205407075001018013441b034000d2000c12206035403035000000b0103c00900150010543d0b40d00701c0c1340c51386040740c0c11b22403260007a48094401d0b0b0510004100109410302440c0e0f40c00468070300801e180c0d4480c2020786842d96901c3d19403c0084c0c000401c503052807807072400381280c041d20b075440c0500c0040490411050b400141c0780541c2c1074001c1404d8000050344001b1900040f00620240c07810302d070340c0d05800354400585900500070104070302c440305c0306264030030440108003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 542155080 1250 542153830 542153867
    0xf0f12051e06040c0f2d031e0902010e130f02040b0913110a0c081303081c0e030901180807060203040509090303040f1b05090c12011d0a050703110a0807 67
    0x22410700e0402000315641c103100c94280000d0078080902000c030302ca05200b01b000320400c4414a1052000014010f1000030300c01c0304150031801d0a80b1090000c3d018412015405a640c000001d4100c42000791011410030f45981080e41c030000350b00b050403140080d200601d100c0c018076858200e0b140510500800c0d403030460203528508a0700262107030000080d222604840e2400040605251600c214103124020345c2003a020740000740002080005001401c1010300a1280074101c10503070350010568860344030000c07030b1f50018008080e1651140814500c803c000100c00300c045542d80550b00c4c184156900300000603003000a062040e0b05043d02781c15003200d1200010352642c94103884a13180340915500081c00020000040d83c1c01c04a00645480581801010310025040c0900c0081895001c5407524008521031400000c407480100000100341080302c1e0041c103e41d8130300c1100700007040000c2c04281490796841001c0b05020051004d405101c1103504e5000c0c039410945000380901100d1112003400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 542156330 1250 542155080 542155091
    0x60f05040807060c062307120b03070b090105160c050102070f050d0f05030c01110309060601020a0209040b07032d0608011503020105090a051c14030a0f0f12051e0604 73
    0x921070000303200700407641c00d0b00e031480c0400450300c1c100c2d0103450142c000c03c0d80402e01c41040c6c1050b10804800300e01409443d240c0c0c1e6036042d60100884180c2d581100303c50350680100c030040041c0031144000340022407051402c0c914240300b071600200c0e041c9144406072401012514140480d580411007500030b024080d04008000b40740c940016a1f00c5940340d4002c0451134641e0422040007002c10554400e010140003d006006d5105100b1a040e002260720380004d00c10003002c01c05650001c0ba01c1c0907407a801034480d5840e9501c51319000c10010010380fa040c1055982c8161b842c41103505d014035a20903c01359500d0001060b0900e281007079038544d8219800c103901d0004504402510080c2e15000c032942820910b031141c00c00030004045558075400684c21000b841100f202e4040003074000c0e201a4452007607041c14181041005607030b0b002c0c0480c13000108000050154205d07000b01c0017044031915a00c2c1030541002c8050080b0262a4244c440aa0454142002d4004002a550010340c02002038504010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 542157580 1250 542156330 542156339
    0x3080414061b091f03090201021902181b121e01060806120f030f090109060503010e04021e030f0d02010b06070c1403030409020a08040c0603090c050907050d15060f0504 74
    0x1c100265480c00d0902c400300140c8540103440f40c50018a10440b08001d20441d814420005005005101000c03130050286d1042ca1810282500516003025000388c503241030200c442c02d04048541000d4440c22800c003d114071012420000d00003020013041e40c0d001000281417102c4140942c01604821010186219005210b8940c1c8000c009a001c6022240000d0b0220542903407400e000c601d02c1491094000061407a0281740000c0c0202040703230082ea1a100c80f9541d9510031529800280034a4254075010408a00940f5244104450114801c60303440380c070180c1c500000303141006a90902070a60400403c1d00b1201ea02881a107003044002d4941c20f181184503a00e9000e5841c1134007840f450b14542e40c08000007905c0c100251784c06041207041c1150344050350b0601804040c0304480854041c19900004505a803082c043c14940e00d500645d1401e0050400c2c08101202d40000c04000801200307002030004701304140564110403078803030b1400149074103080e070003421114036003802c0040c400104070412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 542158830 1250 542157580 542157601
    0x6060311030a0506040204110c0a0503120f01060e360a0b0f011e030e1203040c1211040c180e09101404060b06090a1509060f0f080604090f0308041406 66
    0x6905c558100c50014164440080300d020b01e00807204603088500c607041d1200100040000100740900c08100c1c141c9e2103a03500c0a0810300090309025240001e9950041c5190504009210450902003002c058919940170003002000c0100000c1681100c3e000764180455034149200d10101d000b400d4914014240440d03002a010319050138002c000b000b01708070400c0e01c581c0700e5842082594012400e031051600c0c5188240203542081d5000e0310b860716241800030700312070320804400c80c0941c400d030b40461521420003001b004003100c1040300140600404007003e11940c2c110600e016140314111100903007000c0794401e00c0c0c03d81030f442c3d80c002c0500d414031462003403040c1d80d4040d034401d60082d00407030402c140c5404181140661a441ca4000001c0700700400e070884038858840ca024415641e46a2060785c81e442141e1104c50300f40c0035008520116940304016105150080c1d06c16009000844c8900e0241d6580f0b00e0a0800f220a40001e00e11005110800c40c1820488108400102c0200004d040001d20324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 542160080 1250 542158830 542158843
    0x1a280e1807060c0b010503010513140c100207030605060f0603061e03190501140c1902010b0a0f031e0c0b09030a05010f050601090f0b0906070302070801020706060311030a05 76
    0x4808040425000892a851040d50a80940354840c01d0740d1207103a0310140034000c4095590101c0b54285400000720f90f5040501c90648202c2c024040c3c010042200d0b100c402c84401080d1b20030805000f610520b151945030301817032816500d01c1c3c0c1c1c0142000c500d1400d103c0c0440310f015201d58031483d100e00c014241580c0700410b9a410080446a204a0403e40180b1844803402e0418094040c0a02d4008001c41e810082001501a00a00007070082800c064401c0c0c01401d0119011100c0703070f90070302640412000d0b001c80b2041a0000380000540070900030006500e0b8840c5a04c072038468140b0200c140300300940503556410960484400b044024030070340e600300d814021070290003a050030104034440c10350340c00c0001540c450380202c000c201d405a03518120014101c00c82d105404039848500004404200b10702003400c803520741043e1801c21041b0300400800e80d00582e010350852280c82000305003600d00384000d08499120781c000003000791039880c1481d5001400b5804a119030041002c00b40030070f1000c030b1403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 542161330 1250 542160080 542160089
    0x18090a03110a0b0705131706041101030908071203110a050904090c050607050615120c0409020d0b0c0310050d031e120e0312150109271a28 61
    0x704403541c9031020300328a0300c0c40c00400984101203080034440b03e0368105000f0102401440c001100075900d60041c284601c0b080317030901e8060b500c03030300000703011501820040d0b0010805140211b054070b0b29844200c0190410901076039034040c111000b00003c0e4061180403030840d56210000c0c00d188010001900c44d01401c803105000e5515281d9000c10800b1244550340508401072481e622842e00d81085070f60b03480b0490b80c003030b03035942e040d4818409458074800040030422460024000810f0000070f02001d0f016030142241c00040034001c40d400500803248141c440d0080e076901070b1300c03440c03d40e080e65150883e650140c0c2c084c6046902d01d8000c240d20220754810400c0c2c090700c03030340d08403801082211512407000340401400c0c903202100c1e0001801200400e40002d80780c04649075505c816500710f044d00d4200009a01103030320b9000030082038003d00d520a603001511540b5400c0d80620040420507600107101014604003144044480c034500b00600c0050b0b10f0702c040000c00e001700503a0700b81002c000513015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 542162580 1250 542161330 542161337
    0xd0b09040803070c051f0902310e0712030c030318020d110a0b04060c06150b070b0702150106080402011106011a07051f0203010302151305010e120f0c18090a03 70
    0x740f13003032100800c200030451180d0103120f1204401412480001c20b41044100d104004a0404202c0140380300c035041507106204c0048822810204546001014220700c240414010410001042941c8441e03c021081c000c3d242c2d030408000a1400504070b8a20f8282c0048030764038040c102025840d40d01d4082400d580c011100d140c0030070400c0004001c540241d0001ba030310440020041041a440329034040807500c6030000384038000c29440a0362040d907150203210580724081c48150003180703800012503000201ea0050302d40d26011340102d200643e909800a07004120507100340b00c1156804448004083d07001005402c007941030035001056401d880000b0064030102081e0941031210a00044410000d02815803174445d8181011001942003448268869050031804c1c2c010300c0441c0080300c0030000e65182e5101003600303001c015184210210120b03500800c0c1910242d140940c02c10580c1c40101d0200020501c1021304400c0100c1e40d40b065909a4007092882e0034801c6008000811400c0c4a62609 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 542163830 1250 542162580 542162597
    0x7030f0e041409010e0c060f07030302030c0708030406060e180604060b1207080c101e0c140105070804050f01021e0901022505030c0612061e060c01020d0b0904080307 73
    0x8005800740c9160524014001c1d516420f00014040c1503110346620300c2c40751305558071382081608212040c02440154100d0700c500b003103050000b034071940c011030f80084940140b5040603545c0e140c805103038004031002c5480641d00c1c3d80078003881344198140c0303900c0b511001034044580403903402c407502c0d8500600000c259640391182e6411580da15800c583d2144080d000b20f03100c1a60f0780150560700c0c0500000680281500c0007500c1006118011180d00d860710503044040c640b0760124200d40703002100300141c07001200c03007e044038110400c0c010180100f07800e42d24203c050500f4209181401403910b0682000c4e0303c100101c201c000da90410882024019084050310b078100b20300180d0420007201c00f040e00e01354822808090700c0642c0c4a504040d5102541201e81050081e014030540340714030800c031552203194034001034052504917031071030260300c202415a04003802200460556042105010300c565004140071126032418440c1504403042103840d25030034202600d800304c0e188400fa0a0070208084417 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 542165080 1250 542163830 542163857
    0x304030e040f1d0106150f020d0e010e0409030c021801050a0e1807150f05030712090302012405120319391209320301061d0a0207030f 59
    0x65001c4001d4103000f6810069000711034900c58000d141c540030b0740286113240301c44402924415128003a41c1031440d00100360541c40307c00160f50303016201200f28104900c0303900080c00713a1240c0c040c0e410440e20989036040d01c500341c3d01c100003416501c15000c1d1042e0460b60010419941e51940c0f00c07080b01c00d603005040340d070b48035410008010409007030305000a205640d40010b55407142c0f90040c00d50401a5034119209800c0c40b0111041e1109a540b98009030101103082c0610071a54441c03040d55109000001d0303004002100340d40b910908004d0003103100b02040f004c20090420038400381c0180d0000c00514600000d400d0032601d00311003940301400b080401d2a4052566808550400e5000382d00605080801c40400150580d06540c2d9011070b00030b680790030782c40007050240d1400d0040e038486800001108041b052080192030800212058941801504452540b028440c1c04043c102e00d850603803415074045524881c0440141240402610401110011035403090203101c035211180707490307420544070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 542166330 1250 542165080 542165111
    0x50c0102070c030c030203060a1103010302010e130e01020307030e07080607030b060403170403140604031403090a14030316050408030a120609020a0309110d0201051606200c01110304030e04 83
    0x81c0781d00107041025a440100034003201c10030201c11607100b1400c0302c04c5a551407a00800b5580c0701441d03100545d500384014001036010758400d01800d40d0250207640413000060300482074074141c4010f603400b658008140031310164180034000d00035075440000c0103d80e1400f802c83c0c1d502e281c000e000300c1c01c05a450030451484d40e80c00e0b080714020741d00040d10180540020188014660081c4001c64803c010001c1c0c41131008004101d243c0b00c1e68040c9c4913610000c6045074410150f50008102410030b0007000101d800003003003680001840b0070001d00864891921000200d0408150501c41050007001d10041040308000811141841c03550701c0c0c0300381e280758036000d08809801e0580020f2411400400c0703c0c0368040d8198042c4100500484a090390040c2007800c1c05001c1d001050081d000807010400300c80c2d4020002c3c50f07400d00701e10580000405940c0301c0120400c080c1c4220138100c1101c00043e074a1005c0f07109000d4150541d101d00718561460820740d5002d49105034003c000c50090b84ca803100d5100c072002c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 542167580 1250 542166330 542166337
    0x2003060406110f0a02060a1401080a02040c02030c01020d0b03060916061b020a08030a140a0c0305160b010e01030c0b0f090103090c091508010e01020a05070f050f07030602070b0f07090501050c0102 86
    0x240c1c403095445113482e54019481ea10211541c004d52480c0c41b090304140004034200758120b443c04400707491120300d0340c0c09000180036200b50810562100300a0501e40c450244007c120100d07107070b08001a050f44000400d41400c0c4042c2c40d0034504d5014900d0b07940f2151a660032881111024100550ba500c035410045150966500001e17620582030400020300c04030204c000e04010200e90369038107607103000345280321840c000c8101d1500020790280e080d10000b17018400400400c1e20030200000c0c1c42841d507070381c0085c40303400340c001c541403100c0a4010070400c200c441c502c0c005400314141035400e24003c0704c4070907024044d0b0b2144c64109a1901c1580d0188020118100040c011241c814401141144401c2900a00078070030108198079044420000800601c02d40b6a001401d81c5e94902d0302d105925042c211405c0840d00352091f00540308010001c40041003040c00551040383d025807103030303030740d0401120304040102819400e07507402c005c0081d40c5602007104020b513072090030540c3d1070b40c0110181900901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 542168830 1250 542167580 542167597
    0x103410c03060d0c1a030a0b040905060a09031b03020c0306070c0b04020f0d170c0c0105040807030f0206040b040e060109052e090f18051311040f020c0a0b04200306040611 75
    0x80d4207210045d40100c1c48003d42c41000f90b448240052112802030008642c0c540c04040c1c503e4200340d012072100e8045810104640c0d003e4a0084102c203171000100104103201c15040340580d21040b03525240303080c280040e80d8001e8090804034050441a1a009041d80c8000c000130720400d09030a030a00b00e5581c00200d911000d411040f074880c20000c41462944940c0080d146904074030a54441c04120345c0700d50201c0d000d44202d030000c2d10f103a0b461595031001900c2c4c0040101c3c2d1010701440042004010b8102a00c0200340e188aa0062402c210b000909002a40e07042030740a0090301803045101010084140440b100c1c400480d1303294071104408940400c09500282c0c11800f4500c40002c1c016002883c1c91580e000d466000c11890700c8810025100781003403c030050000e8100300c15a4501e19050b404415854500070016240c4084540c500d82418601e40003164000380381e0f01440240440042e003032800079007150070941c00700c00701d40c00a580c540300108010099078889100d840d8400552060360b69a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 542170080 1250 542168830 542168849
    0x20d091a1e03101e031e08090907020102030118020412030f0509031501050a080d020a060c020709050106030f0c020d020c040e070b0f030405010b01090b040b090103410c03060d0c 78
    0x2420700c08110110590b10b031003140307151602010b42c0071520a00240752000c0f81c0d40304110000f07244460590b003009201446d002e44e00300c2018406095644c941c82c11780c1340b01f6003550f03000681e00c2d0f061181c14007c500ea1032026000003441400144a00044084180304039038041c10b000d40c0d10b2865040c21600d511448a0171070300340c00f80d1688284200c4044a015050380c504a0319142e100d900c6d03c40141d40c0d0f41da0f060781d00e0f0040c0e001c1040e40c4c001c550150701050034104148182c0e41d8041e120040c21090f45c50a912950020b560ba120034070360203203180724030340381c0005074400f9100c1480e030a2002503507500769011062149940d840c20b11034060040003d0310003010ce5500d8651039910355003041c10103402c11a81035038103509001c1000515032144c1c03040c801343c0c0d041000b22070415080c10111a00c980080840d2410f15503150303500225007642c510854600c030070854100400c80c0c0320441040500c8545008858150000c20900c4070580c880c00c141c03980024282d0382c1214070303026410a50308420f100e80c4040700c803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 542171330 1250 542170080 542170087
    0x4050f0103091b0b120c070b0c0c010e12190201060b18031009030f08010e09070e09101a01022104090e121c051e0408030a020403050319020d091a1e 65
    0x8910442000d0000700c012603217506101d64a00001400e50f21811500401c400c100c0700c00a40010044030142c140442208000642c0910844010745822007a0483d8401098046100d5101ca1001c1c40008010002c0384000e000702842c00d070100c1070318003501c64000004008034051841ca500e040108080004143d54140310103056400d014010000110852001980d40000824041c81c000f00722801015030400504074113251033410040b806011b801d50742517001b50f00e0140c4010905005444018541c0303208603c401c64144000391030040403074900540c002d01c1c018146e074008004c02c15901100c0c051380d0b0200e01400c0191050342001c12045d0107000144011030440721210065284002c0440005c04c01c005544403000c4035960311050403594000003981c90006070006020b0409141c2140020750b025061035166a180c9066030850707031081090b44181d042c1c1f034607034940c10840003003c0d4605051202083c2c1c107188a28400300018000c102c00c00100194500c01100212981f003102d0306560742c480d44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 542172580 1250 542171330 542171339
    0x1a07050102040b040f05120604020d030516110406140a031202010e07090618020c0a1b0b04030b0f010b03010501120b0109050406030f030e060309070909170307020304061404050f0103091b 82
    0x83c07600503000321212104084070101d0301f410000050107a44800d02d00601c0141e0f980e40c04c11003104220001241049000d02c21801c6001440003080d880511030764000600d1440f041c1484104c1e1000e41c082d01e00201d9031440350f4078580358828a070059079004071104040100a41c0c1c1680505100c110320302c0d144c07040030030000320105290b00c42800d071004c0050340c9440342c191415480a900170341440e40780c00e4112404800c0010400d20200c03800d00d9092011030750071179840d90100103a4125502c00d40d41030002504016440240440301809058100e03815425541408002020400300a101c0c6254035554010559541e000b02242001000020800c1c42029140d203814540e1604c2000d044010500c00d400c8100985403600c20340c2d1084c44000004d08003d464520008058824070350b098942110b21320312001d041c6a00c80046200d81c6083e0011951580b070000000d1018100c00700d09a007400d0300b80401e002c171396143c80f01c208a0b00c40918021a000440c0c0c2020820405900c0c60102002c0401d600000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 542173830 1250 542172580 542172599
    0x30803010e0106020f010524030c0604081506101403070e09010603090203011a0f130b0d05030a0f0809070b090f0a030506070f050f0a0c170a0e0a0603151a0705010204 73
    0x30b050b6034180d401d540b101450785260a00f610300903151b4104403078000c0f008031610001956504144400102180c07100da04020100302954059003005000ea04104444040d0700e10482005030012801c1c1c80c02400d030756140c071000303000101d250f00c4854a00303000000308103200d104003403130307107004100402c480110759645002070018145140304038029400d1080c481c1200c14100214039131b004001c1c00f000c01d8a0b11107010040781034201ca0005d40c00c1d941d9159986100c0d02d03002034000c56203101d200250350741c0701d04400141c10f05182410000400440f04108284c03140c004c00c9500880c0c89029616440389410750015000302d02e003130000d81d04500c041c2000400d00c100003e800f802454035449070750000d21941c4003206c03075100d888408000e40000300121101d1510580003030342c00601601083c0000c040c200c810700115031000445000040100c85050103924140130170307000902c0c15040820408510202e10001c40b8103600c07545901c40c8a0094140040c08032004a50f08680d000c0002c41d9100e8840c00b011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 542175080 1250 542173830 542173859
    0x5070603020c0a21121b110114010b04031403071e06060503031c0b0103020403020f0d0203150c03040c092304030203040b0d0f0e2103040c0e0a050a0c230c030403080301 74
    0x50001038207170942c1c40c1102c0c1603100d54200000104813440d1000044c0c042600c19043c1a0702c440000e6585001c1140c0c81041840707410302804c900084240e48500e0b50800c0300ca486500781c0503001d18ac1080003140c000492080401e20291351613000600754404e2400c001d8000c2103960301854060000007100c1e001102441600c07111036220010820800d00c06100460032070095000007500f1100b6003003c5806481c00c1120542400e10040444520042c101640c0d8010320040e41c000c0d20144001c8244420082e4150740340f0080c0c5000541089000351000024104004483c15800745001210114041c180b092084902400008841030f60b102144004900209801036802403224508008801e982c0030201d90014880c2601c0380341004001c49100e40788440d48080d00440300f02ca4400000036004406500e0244201c9607801c2c00681071070307c4419030081ea141119040f08021044640300311004001002e402010040d000c40350319110308202c150728502c12030f0409010840b000c03000091180d00c89400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 542176330 1250 542175080 542175143
    0xa030507030e010b0d03050309120a11100b090c13030b070215010e09120d020405040c050a02150f1501030b030106030b07180f0e060117100614040305070603020c0a 72
    0x1000300025000b0314501302c40e16000c0c10f03a4000320022510f030109205030301568001440005070762003020b000500030407a50001402101050b2950802c060110381403041e00204060313500c0500020f9010b5000034040080141007901c00700d404078400700c4607070300c0321203010141d5440703140310009092200e80a980d0780d40c007900c68520101c0c00400070440d50603c0b41c481c0e004217100002044462881c50003044560000e0008072003080d824000000c4660710750140e00030800040e00c525541e040140c800030f0400042c800100f0702c003002442417102600140c1c04070f43d404909506081015890390b00120060a51100c10f294550300b42400803062049000390b05020b102c0c075032260041030311400343c10100b60340c103481011403500e0010401c204501110b5070850f40660305240c060200811991010f2000800340d80d5031b40009517140d400d10900342c000942800f0000c110030010300b02803941d90740c41c0d0303a41d030740c0d010f00c808058002c5081d2441c12010050140b02079800740800f081c42d15600501590705004040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 542177580 1250 542176330 542176337
    0x2f150907091a040b180f0a1103090a030509041401030c08010605030d02281b05040b060f030103062714010c05070b0402190812091009060804060504170a030507 70
    0x5103448492240070305000303550803202000d03207000b01000000d02c241d90440341c11013910b90350907042d0320010203510310400c100f003600e00d40341c1050f4040b0703404c0351030450700343ea003129041090200310000060315204032507040c1307082d88e500d042080100380900300c01c3c4404400700c0000c42c0048200b0142e8000c240c06d036185032000b0014a83e5500403d81d843c1071803905c0d000981c00006511580710b105003820075424601045803426a800c6554044240010f0b4a9020999150f0b44040c405882c040c0034910b10b050f8100c49042c02c00074000141c032810310061000130051075840000030400740007146403100a1500c05410100708590782400a11075840780034040f003d520f828840e1001e10302400a5444881d040340400181d540e5039030920400d1800007180d0210250451000180e1181c10800301d40348140c43c264940d101e015181c02c0c007517040d0044d0640c005014010341d05000503035022036004e620540240340800c0350749450420040801c0c00c800d00c0b0f03490302d000096050500e130705604001d00801060b81c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 542178830 1250 542177580 542177593
    0x15090705040909210e33071211030316031e09080301181a010318020307120b01080708061909170a080a0b0f040b011701061106162f1509 60
    0xa0484100d0301c0c50001a60181c21a2400e00c144031b858408005180441581001c2c80312180c11500b086800001d0102d904404c003480d00c84440d9403017505021030107600340c021425402c1a554401900c80485000c0b01015925002d00345078140444c00100c214001c82010016803109080c01c44441c4e100f4050b0300980c02818180c20184000c80c8641c6260303850003410013090900a5004401134510b0b24103401a04481c0c04050300565410f2250000034035400e565136030021070b90b00d0040411030059100c2e0b8095040030a00300030700c207400300300b180c2c0c03004024210070110012004030b60018104400082e04030880d20281c0c0c02402100c4000740303580310054803020102d80d12a1000d40c1515001031a040c0c0104000008410354101600841080c0105050034003030300e0610141025000d000341d2005001030408400a500b0318410722816070449110803021003806001c01000d04821000788000386c01000d80c4601e0040c0d6076140103e00301900b21442a1240422004018202440c085d00c60f11541d01608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 542180080 1250 542178830 542178893
    0xc18090507080f0402010203070b04050a0b100513020f030a0b1503070806090a0e0c0402032208071208010303020601030320061603060f030b010b09040e0601060f020d030515090705040909 82
    0x100f0b5038a00ca60350503801185441e0007681c54600300c11010b4030450302440381a240706d000408220900348189518856492003d160004000c0340030240c10222000794410010b031000c1d01040011241d01114098000c24040001400315207260181e2003002000d0700c0c080705101406078800601070260508a074454000e0b2104987c40045075100600304c0019400074004104c54142a009141d00c9540c44c0d104a201d880ba000c0e03e00c070b00350f05c01031080741c540000003100410401016142c119201152520011039815641c01950b5440c041c040602400884290800403510f00b642c898040f0381e552042e41c081c0d08251044050740651405110040783c00c2030750101d4140c0e200301c1001c0c01c40f90014224902039182c081c0301c007815807090042c603402070f4490b000300c3c20900301000385900074a141e40d22102103060303140000307040c810000511005c250604003400701062491401c0c2e0400203049800300d200d501c90240a44007131043c2da0003c215642490f80500900918000001e901d02e1018000300054255 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 542181330 1250 542180080 542180101
    0xa06051e01050a0e01030209030a0c080d08040f300f021516051c0c1d0901050f13090b0c0c10060b0f0d090c0e01090b030a030f030c1809050708 63
    0x4144640002c40a0103120200c3c1d11500110900e80e0040c1001890419170300c012a0824080d000b050300c3c4490a04020001c4040801120200360028a480801d504050f654030388203100d03150001e0148540300c904542002c2e00c5803455841914070010910708140c0307054002d030405286c4001c0c1d50140c01038820000c203a00e1500b00184c840c14000ba00c004813400c034808141c03155044048402e0a2100d07040810100041c0c61040040d5110a52a09064880c410300d4109100410990749401480040010449502c0e000006541104101c42c1c440303a12031300b00d50b0350005140203032001d0f0040390b0000a0203400340a03003005001c0c881e01d550a50f50a00c0c289040c04003603847d54801c1d404990410058a0502030841c800381003035140348071000c2540483c0fa02c0385200ea800a41141d2190a440d20041142200381e2007005449403003a0054140e1000544002c0c2042c240c1110b01c009050b03c1e9072030149450301c144980d02010200c080c201210503120200c1000610382101c005001c1140f03507004c00c041011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 542182580 1250 542181330 542181379
    0x60d0f0f0b09090a031e0507060501081c030b06030f070c0507150f020105060d080a090f091d0609060613060906080102030f010807030b0115030b030a060b0a05040207020a09230a0605 80
    0x4142d141e0a0079001d1410441c1e0012506030305240030024123001e100d000442c01d0040c1d0b40200301d040001e0103035420582c001106580c5907014041814600711004610340c45a2081c0d81e0b200c0740d0032050044581d18034200380e5000740380401c01001801038140c04295180380f00500e0222070305542c0c41c0c007031524507444c0c00d07800c0f260240da00075448910403141500280040004000300f81030362800709860b582c0d910700b42030340c248c25420150a041e124801180301d12445000300b40341305101c0c4010500307810021207490302c3c2c06003d4000c6000c0c40c072510403000011100d4200394024500514100090366507507490a0013500151082d85003000404c000061480c030015144041d25006030b03e8507026443e25001d00d0300c400b9200019018591500051035403a81c00348010050107002d9840401c43c180c2c0d00c000c02c03240031030b103410291081d40306001e07a1001d0380351000c01d034054034a1444d0004051500380300015203c140d96103004c0305100103c00308441a0303400e40000e0116a030944051000c0303070060142000320034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 542183830 1250 542182580 542182583
    0x18010e060a061205070302040e0c0a090c080a02120a0504061e050117010207020105030a0b010201150b0c0f0d302306010305010b090105070f0c08150c090a0302060d0f0f0b09090a 78
    0x500c05d080c2880035140c246d1090600071203550803281800d801c40e020039510b1000d0340c81404019a1401504c0d040d54110031010703809010102c0c111301e02072201a0b000075440303000d084006100c0d66240050100304142c1d004103264201000200d14440c2c00700704503805440240141100f58001c0d8032240141c02e814000e5446959058541d030741160703580849040103200a40c0e1a904664a9000036605c00f6140345101d030207014041041c95a990482c4102480c0a00360890411640d005034101904150300c4010032000e0740001000c140041061040c1e94210042118041c1c650b900e041c003e000d0008410044100a2147d500341e020943d590000540c02c4034000d124020340c4010401c2564465813148004042140c4120441d413032844181d214183e00401da6000402030364080e084250382d82d2015508994005558642141790103404008201960001e1000070702480340801d4000702a81e098001c1040c0141d800004c001c1001d980b400100904002941e43d4003880102c1c020581000000c5000180786 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 542185080 1250 542183830 542183833
    0x1908070b040e0f0703140103030e0f0108060916140a090f0e060a0e1909140c0415290d0c0912020f12011107080a0219170318010e060a061205 62
    0xe5461080c0c0d0502554010141d804165030b0310740c4070903d0101c006c21503001c0d5001c3c6d980c2c201d29142c101c00307002c0380c45003051105060041241c1003150700e5950344011035101c110091b408050300d141c00400c0d81c03008441041c040080801280241000303038003041807800c440041420305281580c80c0c0055680d241d0903100c0941111f0046001d001c6440d01604564000800c0300c07107601d280013000e400c101110064a400c5074004400d0707100314400c10040140c1010008200c41c00c000f81c514009044100d120280300d40040c2c0408080c00710008500124034081e16880303008416651320414004c10006c10f6641040400b0650121020800302c0c00c090382c0f480c0c141c0d40600300c3c2c480c40d0000780401041404031300d224000ca40d01e921034840f4040c100400341011f603104210064840240390350180c01d0042c5110008004c1c0b030079003c200040b402102081007600700454885580743c503210140c449000070021a540690309000f40d81401210004d030310382c41160b040701304215440d00e6011808403100c11030344c050304c0f6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 542186330 1250 542185080 542185109
    0x1110c1f14182713020405060a05031504020105040f060203070201021e1f0b06070f021807020a030e0301090c08060a060f0503070302010e3c0108070516050c1908070b04 74
    0x41e410300040c42c0c11000d80c0fa02101e488960441100503441604903030800c9030091650200007181054014507030041821600e0380c008608050104c0c0d5145012500740a20b090350501080659000300f0489025004000030021441c2e21894081c0d40c9906c2458103c0c01407150201c01490342e1401a208100c0302c4207030000c2c0812400c1c0b040d41e1030601d01d20180f0141c08540e42c2012003016130300c0500400c9540c1c81194860300302d0310725004200078003800c03107180d111400060041010a0341e02050a101d0650301d802c00241d08213010300400e00400c44e10100a1240d00d01000c0854019000210701d841034441070302c14040f40743c55080c0500c0d00710040c0308264050b40603103c05e000540c0940c1c4800312854010700050641c0000380d00d1485100c102480c188a41b0749e40708003041e01c8000140c0703500c100380401c4c20198220300b86850010158414490303401901c112403e0030204022060014126155008101c0c0150764031541d0318422184c0507129031140761042c2400000d8428001d07042d501203030f0003034081214 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 542187580 1250 542186330 542186377
    0x4031a0a05070f05072a0807080a030512150a0909110d05030324150703080c160b070210050f0601110c0a031e0609060b090a021801110c1f14 62
    0x181a00301744000c5588402101500880e9100d034002e10036a4070846089800341c0345044401428540150482ca0958101e5a61000800c0e0050b00f2a10220b1a409491605030f842402401c480c41405003038030782c440c0902c100090030031703100c2d04030701540d0303000e00c2e0095154246441008044203000c00000c006030018800212034407100e016000c9400015070400c4e20b1448003d000580580031214660080309010504505240d84010080e9100841b650131514111100700300031440e62060100034060308141000404a91080c05480143c00940a0610413130810303019240607180c0c12180e9038002180c980f0503001004d000120010112b0b40580103104183c00c6444e0b44880d81a00000715410400e60340091001034000d1082c1d0310721130700407540041c0c2d40c0c031890200040ca0401600c40201c00c0e00510035500f502d03c015004100102007400c1c03550500d440710903094240504c0121490303010350701404134100e4003580c0b44604000003c55031a012403400124019000c1d0040142d1200b883e6244403803c82c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 542188830 1250 542187580 542187587
    0x3100e070c0515040b0c0310091d0105070c02030c01050901080a050601020115060306060f03091101030509010b15071703040f060b060405060406050a02011505130207060b0604031a0a05070f 83
    0x150403003a14941056009441d8480e686000d4201c140804601c000d681000140181800041d4124a16a80c0149141407017a109203801440d40134441d0000c0e510040768005c1591440701300f00c940381c580000d014519003c4000b41070346543c040c0c141d00074060104000025031240303040b02c2c10998140c41c3c581c0343e9110714204070b00901c0d00030200d44c159980e03440c03042c942c00b1703d02c4810790092900c0e03503021030204c2c01c0c5080117001c040c0d4884160281802c00060100181c1c11549100350104280b034001215135075110124050980a0105500042034a00002240c030841004026040c010b21131550042c401100e800d00600c411103000e07002040c0300c0311001c005409a08041606200102000d040035200c0000401e650302070f5011101040e000140740c481540c080c011410f11203a60501d10102720300d0100401c000c206403040c0043c0595001510000300300c1079a100c0420301c40081c00440c0c4481e101d251050000e54070070900900300f54101c001a02481ca140565032194103141d80d0f5000c8000350800c1036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 542190080 1250 542188830 542188859
    0x61905030a150b0319050f190b0a06030b0a0f0303081f09050f0103020316080d03020a11030406020a0203161802090d1a0106091e05010c051e0a06110310 67
    0x80308095100d61140e07100450303100b81080508201e41c0c0303460307582c00d06055440070600344ea06980c00a80c18041001005484005100d03480740d0f00102008410440c4000c80340101860f941055000c0b480c54808210f050b8035030f01c0650420b0042d00c02103803103a19a15a21038940b410f210040c0051310490008020010385c0340d40c2c0d05a09441c0120b0310090703841381d0014041c1ca0040f1190300c01c401c5e500004100398a0100410303103507913a0072910750710907505211481e5101c0d1010310148092640018101c00040c2c40b07096400c10704000d0100344d80e2030300e40b80e0341c2c0251903050003442a8800d00c1420080300202e290020700c0811074418036903030304580e01034088460180d081410002d0b070150380401c40801207400f95400d08142c0c030343c0040b019015810300102428003103194200c00c400b110010340180740010b44401007000c0d20000d00308110042c41e286019403416101101c911b4502078000b041594000c030000741d101c01c079480323003034180074011003030468044a010840f00c4000140a0080c1084141c89c40e0010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 542191330 1250 542190080 542190091
    0x12031305060f12040b0f0c0712110c1c05011b0504030201030c0c0605090105010302100c050c0f0f100f1e080f07140c070312020c0a060f020a1401091106190503 70
    0x219414030f0034a411001c0c0790700e0212000e950f191018810002c034510000020b607404002c8424440c100032058641e4184011f081450b4800c0c06807070200200c001004104e800a1014010401044103040c5000d5111850014004581c1c6601f0150304505207182c2c120181c00041007942d03200c0c107051440d001100034052816a881c1072100011900010032000e00441e071240902e0310021413a94594418001e005020310390750340030007084030b810100007900419880f490481c12101580184c0240d80002d5141502e00b00895201d04030101c500401034020201c0404d02c2c0035a25418542500720100380d05102108066400058101700002c050010701d258a0340c001c221460940c2d02c650203008014201c0e40300c1c3d0b240d0320701a4401c280400030010790241c000c00c42c001a10140030301e041c0c20004281840600d0140d4014002844c45121900c1c0c400c00a61510a4002c0d480c2c045511b0b041320030358002c001040003518030443c0d00300c9941441c1040c804403410350407a041e000a01412402c0210303002d403c05000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 542192580 1250 542191330 542191357
    0xb060a0305120f040f08031309020a1211041d0a1134150204030c0f1214030c0610080c040c09050f0307080106060905120a020d0803040317010f051203130506 69
    0x4500b034a100c1d00d400000c0d0050304007e541d5800c00c45241c032003c582d10340c06503000301e0040216289055004941c44030f00e05440c034002c1034107080c030156070f5083d000c3e640203140604460710640b809194a121014014508c81004111180f4000840f0b05d051184007460251052801d8980c550300c404212003611604941a4103040340c6600d41d280e184400303403001400c05c541d4000c41c080c401e0140c0300d152a0010300d840000740401070714214282c07a51100c05400a059959034203032500190700d0030300454551186001c15100d10385001240705262080600034030001d48202481d0340d030035003808d200d08494001d680c2c6034811a503180030104084034400c1c0013120342500a028000810680034010f00c0c001d401c0b0f5072a0041c00508060610542e0f001900d0f0107043d6038031640003803016855541c1089900b0341c0180c1c01650b2580c031070805a035508000030141280c5600304000040c0c0039401100e5600360384048402400a0202c00030456482c040d0301a030840c0300d1040801003080d880c05400600d00ca1040c0e10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 542193830 1250 542192580 542192587
    0x2060c0a031b020102040f091b050702010210051030020906150309010506030613170f07150c11071d100312020705210c01110f030f070b060a0305120f 66
    0x1c00d10788110b8501041140540e4002c2014072128009950080291031581e80c10041846a55030085850290165003800d0003800921401036920030b0251040c000e03003d0600340410309001d030b03c80001020398495a284882801000c0b1002021803030100820003d003145c403000c1d140300780c080062041c40648059480381500d424000c40c0c21525025504c070b450010000109450a4420301d800c0440081140403010b4418084100185042c0d01c1ca48081e81784c0107040f52110b24201c49a000e9105441c8094591481c040128000c1c00381a08042c001d0656a40c801d500500b5042c1c0c07a80d5680007a014080034100c2040501814080e5010b826604c1400b18100191203556921008840c1803040c4003800142c10011043c020b42c00e02803c984203680903821000c0c000146440c1281d00c0707520100c3c040c0e041184403014200c801204024104003030000c0070a41b40e4810012800e1083c03544403903412280d05511900040852074039290100442c1d410002610840301025030060031648900c200040c6a403050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 542195080 1250 542193830 542193851
    0x60c0702063a150509040b0a11091e1503100302010c060b0a060c0302071e050409020112050c0417030403020607080c01150e0103141209060901090b220801060602060c0a03 75
    0x200714041d02c400c0c0380341c00007900e031051800790150039065000705001d40e101d40c0600c000104e0002da0141d018241d01c400103001c4003020100540d034400c074600c41c0d501c24018000800e000a0142c1c1d0030400f980c0445076110f0604c0d505003503c0032800110303514030300d40015a4040000d5409408081100b6105080020340c8011040003d5042c40b056002000011480900c01042580411100c005000401000d4103d0f120341115412182c0d103901815009030384440b003080469000c2c00140d14000c034042c00511486c03400640050386600540303d103200c201c0788241000d417603100110440b803c0c0c9401a100600d00384171038444407029803004845014541da140c06004c01c1445100c4031101038524048038040951450038211070f403445130312600c0070640100400405035040c0350100c49010000359121501e0b030303021000590348402d1903400001c441030b001a64058001c02d00b003016015001340250900701d07a4841405c0d9080701c05602034200540d00c400702140300703844290302515010300c2615021035851441e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 542196330 1250 542195080 542195167
    0x1801020c0d0605010608131e0f020310150b0403021f050f070c05010e1c020f04020f03150123040603050c09030a03020c120f0705060a051303080a02060c070206 70
    0x10000c00da4040c0d076030f440113100302507020003141e42225441c03164010704007140d11980ca503c002542d40e40d03c100d02111010b82046814225003800c680c0080c1505c0304200e400c0d0048010705407188090708590f864420210b0700c1c405400c1500d081e240c0141c1052000c6440041d00420720070024504810700400f40200f41c9280c1004004107200c511850040815030319040c009460707500e6141c0340707900c10031031301c081910b80403d02c810b18242c95404442c140102c50064002c60024482c021801a0720702c00001008485a91400401d004078000ea840e0302c801c01c070b448805640102c3e01006494115810001004050b1207a00015080b0415241c0b003890443c165000030710304511030400700c01582003920102c41d20b1808030902c040c80200180030b001220300342e00129413111200e00916114101c0452511891803003a01a1008400c80c1288481d41680383e00f00f00740c454114414900040c816080014001806441507400c2264003421007410a607031074002e01d900d0b5280b00500d0b40c03036607841901071800400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 542197580 1250 542196330 542196349
    0x8040b0702011b020a021c050d0338090a11040608090111030703140f060f06070f05070303051e1309090303380609010e010804060603050a0309140409081801020c 71
    0x203141c00802d000512441806402c4200c1941401c004200c007e00002041c800301c0c0c41714040d6942e1500051b2002004002105290f4900491940101c100798052000c030094240c100100800c40d0000c40c07542d500b4008000703a81c0c45003414512400c0602040140034000c0d071056401400c5980041504480e104c0300310b203e900b0403074800c80082c3c7c560b60f92154401e00000701b41c0e048a40d4095502451801801089040f40c12044040c024000052020f091084a100448005522106a410740c42d030f642002010358110f910101a08510b0380e5008003a13100003802c48149104841c1440505450004280c00429184a041d02850786800d100c2c50945040780b0340800c50094048404908103240c1e00324200780c81c9240c4502c2c020740b401c001540f5141e03041940c52400e9038003403800c6207541d0b482d803a040020301070a0348000c03d00d2064480c81d10415821012240a4603e10844440c0b0081613900b04015101c0024001d4001001001505211042200c1d924071152040c012201d40000c01000b003402d261 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 542198830 1250 542197580 542197631
    0x8090607030314060409080f0706021209030406020f0304121e05070603150b03060906040e0708100c030b0306102c010f142b02180f01080c03070608040b070201 70
    0xc3d550b20700340c0c02000300e440101e0b412000c2514201715400e9243c0d65843c243c425203a480100b1036020550364100500340d01100c1500c2036444e9144d00d541000c01c0c150781d50350864010380001d40507071102002100c10000136601200c140d0b443c0076a89a155440b6015583d4140791180d00c1c2c0b240c41000c3d080445e10800c042c00080c031580d9000902c4441025400300481c915400161101d202082884607a54400401640002c4119000258590701255041c942a041e89c040c104074014420300224210702940071511502481d2000e22550707900c2030402d501c0d000c0498003401d041c1d21a000c144561392103081003850000d0900c8000041e480e0041c0c4814404100342d00095081040c3c0b0400d204450260151080d0382c80180c40010384a1410708000a00c80300565200b448180352141000c1950340d019009041ca1041801c8014541820702c0d10204099003400380c0c11461142550548043c207000911004858042e503a120540e01da0756a094203c0d10302a0044046640b242d00711003030403e0301400561b408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 542200080 1250 542198830 542198837
    0xa0b0618010309060f1d0c0a08120f09120601090506040204060f0c051024060302091309020a03060f0f36060605060c030703020f032a1501080d020105090303130f0809060703 76
    0x44064480081c5800c0070b11f035000d4090f0600f400100816400002c900741c90341100302c5203544a812504542d40300303020385a200350b400809401c8041003000302064081c1a0b4080c1d000500c1159254424803050748a41e1003401c00261450a28924140c41508a01303801032140082d510032407000c0e2960420380d0700b17942c588400459006068021150f0f86a600c2008100c141010350402221600081251541c08078040c001500d680062085603a14504140910b90000d001c100b03004092a18900415044029483e42c1d89044003d45040300f404050000312081c180f0f0410049181c6e039034180d0145820b0000b01c44041d1500000324030359480c107000d482408001e0f0011900c5000078180245072550f1484e000c0700e00c0d082006100760038144444241010414000c9100186a11142a92500002408423a008004a4004988840c0100703004c140724203198028046600d0b42c1000302c2d02e0380b2080d5190b816204043e600800054080340a1521142c02010141d0405280d880443c1140d07100040440c0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 542201330 1250 542200080 542200121
    0xd0210090e0610090620060a0515011701140a05060301141003050108030f0714060a0608010f05130b040201171905010611070b0904020c0a0602030a0b0618010309060f 73
    0x2440d4070000507400307a000c9a0810b01400c0c00036000d440198640507900802402219410703050210307100b0182001114000c4506a107082100600100815a140200c1525403441c5032160b42c4500740702c1911040300c902c00701c540c1e441c0035a414040d8058000041e0443c00e494400240e42c1c0d2142c02440c02010701d45030403945001c1903401c001003242111800340500d49450014000300500005856625a0320f0701416680d44c4941458a0548501d041d2500c0503c11903040003024885a0401012540c00200078025030420422410554004685071240503545416074004940d6030740b038140d08a401810071001c0b4000128600012450440d00c0c0f0780c102440708410207084c0040d04c207060040c5400e1418036540c0d46070300d2080307840c0c00151003042044200419960901c2e5a20b604444000030031200b154400c0c00e031840c0a0020b074000f2240c00c0b0003145000403441e02814200d00721550b00f0740d800c1c0040082228100154001c4c00d00210540f881ca031b681c0005107649680d07102d20396080014503010440f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 542202580 1250 542201330 542201339
    0xf04150b0c01110409060f0503060f0613020c0a0f0201140c2d1207300305042102010603050601050a03030f0503040303090609080c010c030e030a080910050408030f06060906180d021009 81
    0x102c0982e00849c06603001c40200840c0c0c00e0100016a0860300843d0741c0f41d50001c0d482c2400010740200182e26090b4081c440359581041000c0508070102071003038031190261001c07149543d4042c00303100794518243d0840c24042034520b6418849507480c000180340d0000303020100c0009468084c4220070700180d11800107216040c0901c0724900c400039440c03d442400701c80c68404104c1000c503106000c07002899224804507003000b05c0da641e1811140c40c400400c0400f0000404000d000e4201ca00c01a50b842c00740f10004203040c02c0c005680ca0513285c05803514030540c040c000c0c2c02c0754aa80024000d9041503920740069001414900a0f5000d86018001407a200d08006085508441d444400e030810f051800484404641e004021344000c0c107c50b0070940c4e00342d03403101200e40c289603004036104810391421003008100001c00004d18000d03400c2c0512906103a5070f0f5403e111041c400c51249a0f880307001401031a0082d18000201148041c010304410b24824681e804917449141080000b0041010000c0a10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 542203830 1250 542202580 542202599
    0x203030103030e040b0a05010302340317070c150b0402030c1c050402130f06080105090109050607020a020102060a0e030c100b03010c0503010f0b09120601140f04150b0c0111040906 79
    0x1580c20300104c40030810803080d040061114aa40c2c4a858141500420380c045a118400b901840c0700703c50710500990400d0b8000d40d00c401110302d0200f100031652803907200806000581c0765a00c80e08442c0c9407024041c041d03449034200c3e04002c002903600c0e6502c40da0035241c65225400594083c800150740a900d0f02020301c07180081302a21085112074501d03020400c4090303030b00c1c0281d0281d0300e0340500300041c00d003244402d094003418098002c05000d40c200800d000300e2980540c010401140602e064400d01d4881100498549907082c074064016031290002ca020301019600052400c42220112460601600c2006040c03460818683c421503544905030103142c10207009401001c802e41c0360052456040880300784030a03c0b140240541a0400b090608040c0c40d01c4c11941e1190401074101c3e02c1c1c1c0d607900e846071400700314440340c903900904034041e201c461340c20f09020324005030a4520300070240314107041407014503820032008849250f4840c071409d009160800010b00141c00c05080200303010b4188002e14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 542205080 1250 542203830 542203847
    0x60903020d031d100e01062312030c030708031e040605160e0112050606070c0e0a0b010804080d0b0a0f081005010602150403120b0a230108013012020303010303 70
    0x49010b00c01840a0401d440000ca01e4050001130b40400080180c0901011801418281c0201d86400b032030940c032090a00b0081c0c20745814110880e540c0210302040e044d0070b5120700400300340c0764a55205003e104e0014000c0c1c00030303507402800260340020340040d044c00c601c0c1420303058505071401d135a94014000d66103c1c0500340c41070709a503030502410381941c15000a00884000c0000081c0c69036803c0032508540e1102c1c01c4445503900062003003101c1da00c5801002c1c80e1030041e21505103061408a25000c40e50040420030310a58100c040c2d0b5050100c00c08002e00030340711a40c0b40383d82c0320504100201c0c800c6e155070004005000614018040c805900c0460300482e441031b000541954000c054200b004821540850f42c820340c03600d000341c03040025107108400781c442c0f41e6149510001c3c40c43c1c0420fa406030b9503191402c03000040c0040003040c4504006607040d00080c0144603150200013840c803e1020401015441118000746082401120380c80b60030b10307806182c045100503080000104280740d80300320030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 542206330 1250 542205080 542205101
    0x50a11010e0712110a031202070801111801121d06060d3507060902040c080411120c06040e10090c09050909100c031e090506070516060903020d03 64
    0x80199000785501c4a40d2144548561251003052640103410000010810000400d029109025107a200e141045011103040541401407145000c0090b0b03081d81405045c400382e810910551400d4030380b000701011030382114040c43c180300c000444c885107004144680325041607000c5000c40400d03020b003000b80c00c04001421943c840c8600306800f070f0108494070745055241001c20314100c40b590b245615114041d400c01d80040442c2e00201e840c034180b10341600102d0355648210780811543c2460031050784c007418181d0f005040b64624020703a80f0305042a0710a001d174804000100d510884012002a402c1d42c89900903c000d07240300d2062100c40c410584444000d04034181040c0410050380b00000d0280b0309500c1000c2c031544888012a9003194280203441804d021100305001040c51150081c4c0500414100034443c60001c000600103a0031078481e0101d0b032036015002c2c06464a802d9404c5aa54102d030000310880200c1c0407600c800140180300760b100c0b0300d1094000d0714200e2001034024040b01c05000340c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 542207580 1250 542206330 542206333
    0x4080a02151812120a0203040c17011b0f14160b090c010905012c3c030111030c0a05120a09110105070f141c0c06060911030103030c0203011b050a11 65
    0x91940c0404e50703409036a110520800040c4c5036aaa41410034210b029a0321069132441b048a40d400d0b80c41040d00000141a050036020138480c441120484d100d0302940941d100194000c619419924820001001d1100ea2a40c000c1d00d080d00544641c00d030740000f038030300f015581e10090b4419103030f50300111544000c0409090078285d0360075a800c44c42c0c112011140049121380c1e455003800b45a40c3c0c18400d200c2540000342000307510303991007600380304104d0104040c9000d540488008861741c070341400769034890075404000342e0031070311072804c04846604440c08003800d20105100c0ca06200c000a014544034108070034001c01c410300641860382c6001c045800d143d04102c02000700c8400300e080d10718403062803540f0000c1c40c8441300451880906003100030300e00e81c01c00305507d4403104c25554041882c1810030f00030746003080015504c1e0400c904940640a101c0d0031614107000403c0442d000d12002c0c2d10340c0e40040c0003c01c6210000c1c6403030084108583c0e0884c01f04801140422007581e214841c402c6d140100300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 542208830 1250 542207580 542207587
    0x140f0714180a05040c030f0609030201110c0d120207140601231509031e151e0f040602040810061d0403050d0209060409090b01180b060304080a02151812 67
    0x1005001100042481d01c1d65503d60b4045002c11401031070343e41c02075411000200103013141d0b00c7c1000c05801e4014050300190f00b880802e01e43c078120081151003010000c4020f0076011440d0209031403183d900b040c00e164540d801c0c400740c0003084180103000f240f4001c240c040c0c82c00c0d41c1424410406804000da0101c0d65910006014500b51580c90402d802c509102e40d0103616240300c40002850b081c80c2c0514842c00148413441480f08a10014114144809020361182a90385100f1f040d080d003d500313a00c42c040c0401450106149140c03400f62580c0040c06040050318144c1c46d401a0f5160052040380707005030715925001009542c0031110840503448038108492740f603007815100141a8041c590642c80040d0b80095080859601d41d8100d4006151500d4240711412450924017030702c0000b44100d00c10890b03078000c200003030003030741c4a2050002030003480709003541c50710b4484046070b4000d00d64100a6114101c200540c9180200c0c000340702d0000400c520b0b01c084001301a15081566508494803501000d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 542210080 1250 542208830 542208859
    0x109050304030605090a14100e01140708070504030b10170102070b010302092a0702030d0f090b0307110f1c0c05070512011409010c181202010c140f0714 67
    0x100440303040b26001000803400e40c80d82d82815041225504000b040b090b03050941c1141d604010403400740c0e0080a5108124040034121164282c41406e400c940105840c64009200580902900c1e03400403490f1030210700b03040d10b1b035442d180c60050a8402800701e21a45c0410480344862907804001008120300960a0807000d55800350b01c0e00e8180802445110000300107500e010784500280c820b210350308080c4201e50040c1d5001030140c1e1204405901902581c85040080350140350901a00305090303954503001444c1442c000c000d5000500040d04200d080c4000303070005082040007240002420018044140d403070410f405605468030441003c1c08030046449011a0004c565101221000c0d90305648001c00b201c1010f0052549094440da65a0000c0c00d004210505501003440b1286540701e1f0f00640c1481a89071342108034900c6108240d181103070180c0e006520503900030035a43e200d40ea01d09684084240f20904050310684509081c0d88948004c018100031090304c80c1c0c1c922015182241c54a008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 542211330 1250 542210080 542210083
    0x5070c020607150b04020d0207060506190b070204180b060a060f090b03130b070225050906010309151e060f060504050d051507030f0507021b10090e040c17010905 71
    0x110200030b426030f40071032403c0010000703a0f00201c0407400020720441d5510500304502000390003c100681c1c103585464000f0315181001402d00c01d00c2c00c0f00c040d00000e298a00841d0048503031010a080380c101ea03e404098003076280020200500d58840e08a11031589000c6040c4200100aa80582e0130490387d0000355003003e40207910407042d1401c03154401e540c0c0c0c0e568004c815000b1402c0380c1c01071094a5410030003000c581d020840140e00c06001c4041099a200001c41650302482c07801050b030300001880114443e0b600a61140503a10301c52994100040010342c182d200319400e07084c0d09200000d5114080e55a01024410f58024058542c0c4221f01203083c4640280b06000f14050307140500314150800c0700340b200811084140c9109040b91942601d05060000c028140740b00015400e0790500c80401c4080c5d002145841507080d80d0b010048001090604005192003070100352014810141c0010400f500e1044410740f01c5d40c05541d42c2c3c40b400f4030f0410900308160201c0c0f00e0403c5a49411a2000050070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 542212580 1250 542211330 542211337
    0xa0219020616140a05030a0909060b0d09030e100906020c0415060806061e0a120c080c032d041a071e2a02040507050a05031603020f0a020c0405070c0206 67
    0x240201d441c4078440440c81c048001c402c8441003c0a507116200b4000c08220002005054a4009680714010681e5414001d425290203008040c43d50105114000025402d0341c44400308501a1a020b000401c0400c0480d80072400281c60000240c951001031000d43d0b01002400c10b9220166020040ca03580701a07640e4902c01c160082600300000075021482d10ba071404240c1c0c08416585034000211802d43c110121a43e00072038804011520181c15903084140910a81c81281c4042e1200c8095030380c1c840762005560f100802c180c00c6003500801c1c200c945171030f400c07800d004426941c03400c81e03181c240742c144250040c803e11350110790340031900c0c10040100e0f8424062000c0142601005e504080100030503100d805500d801d030180504034006104950b100c00c1d44402e82140213490030007068603110780441d618424032a91502145040000c01c210035000c103c0c4030602c07907151900600309002409103000c140d103c0548480180e1010360811501d00d4103104003500022541024803c0c3d40c000c0e40031890601 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 542213830 1250 542212580 542212597
    0xf0e060709051e1512060a0902030f060108040302161d01090501060c0b0702190b040218070507020d0206090405010f0801110301060f0806030f0303090706092115090b0a020a02190206 80
    0x12020320f20207400c1e8643c02c0c072000c40103002903c00e5454070200c02d103d03403c1420032102c091080b0520640000d0f0040c0d18800c40b4000c000c1090316118596881c001034540b00c60291080b400c40c450000e00d02c040307002e21790a010240006a80b01c00c1a00000d00c010b05040394181c20104200303180100401c4005c3d04840300c6410a60301005851030307940c80c0d1105074140000e2200c4400c0d09c1030344103007e0080288002c0154401c91080302c41084c0e00072102100b8552483c12114100490f400300244005403601481450181d8402010103150801040224080e1002070303201d2030850802c0322084c00150420f0085541c2030707881d40103030703400d48d0300d0030100a050600e01221039040c811400b000c228541c4081c00010000803c1000300c9a89007000545546d490005d840745100160f480900442e25a05061154200945115000c043e0464546914803803000130030082d00341d82d59420415000881d00d1081314841d15149100503200c0170b0b0400c1c080d0404400c0701148401c1303040200c410700141d48150a0301c8072003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 542215080 1250 542213830 542213869
    0x50301060b091810050907050307030c0c022206033201090b06060f090904030e100206040203030d1d24060306040b16020a0203030d1b0c15020d0605040f0e06070905 72
    0x107403142c004152084005400046c0c104458804004d0102d4000c00118001c070803540e01080b8046030043c3c1106d02d203221420081d4002d0280c41e404802c03005c809207a9000017907414001507559039030350780c480d40361155076004490900501e200301c200281403801840316003801070090204250a0780e42c0904580300501d11403080b800410746004144280781a1190080047c0902030b5a040504015040f40b21020025204104100190b01c03002c1c40800c140780100e5000d0000c500b401071925045016001222064000c410699000000d8400030824090540b400d2421038052203c2c0078245001e80000404a0340a17612440c24840080e400c03001550740311320700200b42904000c60000c00c0b403c10a03802006541844003040000c0c0a90391584020b000440000100c0c0d4003c4540c2819070f084110407002030088400c1d502c0c00070008000350000d0440081420000907902d4450b00018101d603580b1000052443c0e545051030703816007040103080d410102606101000b58942000508592680503901005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 542216330 1250 542215080 542215129
    0x1121209080c04020d0e0a060f05060a030c0306110c0703030c0b161b0201020c03071d100b0706020706180f062a05090a360b0d02010f0c021504050301060b09 69
    0x1000e8145d004006c000c03401015141000518107010014081c0a1103c001207854800420940d181c0114000704403540822120f16003803075900c0c3c2c50001c080b801412040303180c0401c80068010424450a406144251140140e490b8a81403c00c4a248002d0a060030b4100e0172310383d0845250041100e0300e40325107800125520100c03500c0100c0c240200c1c41d2941340c06214118000c60154150442443c0d1402d0f188008000d0f0307900d80030020f4801005200d22020300303000700203041c00305401e81c000306030030390152401080d101640c642e0191210303c1c61b9802d0700c8000c40f4195200c20060540144000c0ba401041011a41d20000c60074080c4840e02e00e05503c240134001403166426107403400110010000c00040f1030710968606081c01145840c0000141044000c42013544105601e205520250b000a0200403001505a005613541d0044000240c1409400d07441400180c0e902003c144240f100c000009403280d00e40300a05080d941d40360418401c1e41400d010001054841c01c001414500e191002e0951 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 542217580 1250 542216330 542216347
    0x20a0b0408090d06050c1806070c05130e0a0b0702061b090d03020f10020c0607050a051c09021f1706030d230a03141302030a0b18030301121209080c0402 67
    0x110303c0301420010710150518007000780c40d407042c0010345040e02910b00c000040722541d0041006a1085410092680141090038413440c2403098141601d10042100005c02090b210036045c6400f61040e400c40e80c40c03020b45d0030020403590501050350841c0c840f00c10032060071500650714849001c0e00ca007060054082e10484002e16108000f42100c0c4140103040e45d29142808607408080c3d441611404030921030b00700414a1710340310f85c088a0a9400c82e40d41e440c203048100022150b50355001d40110702180d1900e030864056510030480c04007820210440781140094030300c001c0e04000d0303281000760242e0071a00c04c00c030560300c001c0b810061011651429007488142010720040b040d82e0400074000c020008034190243c0d51705540b220300c000c0c840100c48031207a074445101780c001d400d0141c0001c0d0103030401040c0a0002e100110102c0c0c00030f045400e8900b080c1403559600340b458009a0080001134802400e110600048140d885d081040c01d203854180681030081d000d039100e0003905030300c2c0150342c005900603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 542218830 1250 542217580 542217589
    0x6070e040e250302090f1b0f120a0b030d02010207030e1c0b010801200304021f051c020405040c02030705031923270d060b0d06021c0c020a0b040809 65
    0x244007200031420201050718101c501c024004060101301e0042c0360040205008102020303410f0711172800003210782c60900c4030440840d400d0300100c51906620b8000e001e50143c0d000309850312031160b140c0308070014009455200b05881c008038403a0503019a44100030840200b80c4c40b860708d410351181512004142c124401c8141020300030f85401070120900304001287c01031043d00034560102861091004d52013070a04141c0d001d02c400c0e1002548130140420502c45101c03c001c00c15006102400c00a041c4010764000b09800340c403001a2129060f80010280454a001d100b40c00100c0e04520046040103541d0340d60650307030f200386a800700078904c0b11284050028406d6981582e00e04104030289400c2d0b190805118280c0c011814151139080082c09810848001c00c80c0b1920031071000b00307040091951501c6a00c010054a54000d80000c5902c41c95008945140001c1a1070140300100c031004459044030f50040314003030201002150020002c98011851601c0100d4101d07810401c46544d030b01141c0b0004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 542220080 1250 542218830 542218843
    0x90306020f0c06041a070e0d03030e1615180509190f09120e12030a180321170103050606010302030c070605100f060207081b0d0611180306070e040e 65
    0x5802d9124040030003080100c0c0900c4021141d40c1941c158119843ea8a029596160203120850300418250320660101e88a03401c42c0130a0101441aa861000d04080d0b8a5144240c3e82120100f030b0000120800d078141c2c00484903001011004842c481c036030410002504c2e42402400307445400074509500c91610a41e40d10405080410103001c0201c08450b181103100000300c140e601000c078892651400090809400d2720340e20a200002071450440184025601c104000c041c111000d00242c00200008400c0150320900c581540950200e09a5200c4010140b01501c2005949840c11500400010340001451600100d0900700542c49907100c4000200c00d000b0705901401d40c5007043c09004403078034130440c0b240c01c1c1c800c0c40c0401d0b4000d036150f18081c1d0b681e071f960784030380d007042d9000b8109540e000e902c58030481c014010050444d040403009c0c0e1a09416a40e01341607000034004000b41c0d10811036101d86032500f40390303025070180083d850040801780c150150340301c40c0e900580d00c58a0760000e040003170128 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 542221330 1250 542220080 542220097
    0x108120c0c190803070c0317030f04081303050313030507270504030509090a09031d060909090f0a031707030b0d12051308060a0c02010b09150a03060609150506040501090306020f 78
    0x200d0340c40b070301c5c6810680e400d24900c1c401540e02856040c0fa0098043c81d0751b003140c4c8180701c80c0c501558940c580b941d500d021741d4401e00320403800c2c4100c80408800200140010182c004154200030002802d505056080c00300a500000801910b4070b203070510054408929107001022540c0000c0070340d1281016a85481074114950b8800400010008030070b0301d543c04207100030300030364981c04620601507841010300840740040b0f41c0804180118466841e2104074a42c0c040b200200f69805840e803c0300146ca4498081d504070041030f110544460303c1800d144c400ca503c0203240c1740502454641e00c011070b4080303c44d00b4000d45a6082d40b03690000140c080e90417500c00f1080000c0149420380d468014980390b02e4166980c0350300c1c50802e11005501c51050092100c090802401d1a103d0303116003841104a01c50000c1c0150041000345001006c01c040d07104140c01429070342004140c80b218554188928001034200c0b9106600a02051100e664480134400c107481c0d21800060f52101c907041b180380b580c01480403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 542222580 1250 542221330 542221333
    0x201080a11041a0c060a110d0905190803010e0705041a1e040b0a09090504020306010506031b0a030c12140c090402042411070806070804060f050702060108120c0c1908 73
    0xa030040000540c000810b90700c80c600e4241c45a9494140404091f5144c21064000c100401d120f0020541d60035802003038064401c40c2280c0503014500603c0e101b4848040090710140008801041403090b01919179a120340c65192403442c00b800c11301d2800b420245206104450341c4040703140d000340d101840e0f4030300c4030402462240e51540e80da5484907500c0d0f484560118002070400d50001030b60701c12809441d00840d401005404240c1c200300901103150001003190060f10b03c8980c0100da2500c01d07000600212403540d07008a00b00b103014901a26514010655554461410080803807100c409121603810404d05141241d64009000015019000780e8000c40c0c0300340a0904000e00e01c4854086581110745c1940320b00700900f00741d42c0340c05d4952000d40300340081600500c000079800b070b1064074842c0d803081c4a071309c001440007046890f040469404640800151b0b000b000140304100e02006603003000b40000c0251072800f0080d080c4662900001100785006101800e0400c2d109041401940b015040010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 542223830 1250 542222580 542222609
    0x702100f2706020c0909071e0b0c0c10050702030706080c0c01021c05090d08010501050a03060b0c060403140406090515071202060403140a0507032a0b150301090201080a1104 76
    0x300040301c80c0c026407203804094810420014818201802c0300c905c00c40450010304404d0b454103851120002c51408140e45100da54000480d204440501074180c0030307030030070081040d1003c1405020384501150201c00601c00c003480400c005a0780010300809071790711442c1500741510307490340c2d020142c014103814030300b10b50011030f4420034410040758034220000c07001e80c10300c01a1640e48a69844480300d64010340011980d138010b021550203440142149042440c00040d81541c81d10260260382210300c2c40e02913600002d0502c002c0c140d0054124550f5612441c02da1310341460583d0151201000e80725090040002e54400f0f00c3c20554001591400e54000c0400122410740d658001d41f0707658111012800300d50341102c078001e115260320943e00000786507103800346803400c81e03181075074100fa1801c2d1140041a072540d0103041c100c1d1030000091040d21030380c5100c0301824502c07a440c00108403100302d02e0090f07160100030005030b0303030100c0d80316002a18000b00041c0f02c1030000004c4e1b000d101d9508059900b0f01c614 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 542225080 1250 542223830 542223887
    0x1401030b34081b0304030203031503160b1314030a1104090209070c050616080f1003050111040306050a02090603011206020d0606050415020607021e0a1203050415020702100f 76
    0xb00c50203114201d6541c8524a6075070011900e4000d0005642c0580180e00500c00140006800c501400552100600b01c3d416105084c1c005000c0c0b6000e0b40014003028000300d141c0070801c5001003e000070703219588801281030a2075002c00e41d1b0f40304a400140c14402c0080010b2855160755010f4a010303500a00011402c2c50a068080c100c41c4002d6000c81d402e106450020345000c000e61440d100200725603882c50000d441c0c03000f98481190300508013521052802c0d02c000700180c003d12552112000580016888034070707509116045079030007000084c449004000b030f00e90700da075000c044a0558891075402034035406a810514000e0107081d401440380d51908002203075864008000c4c0048030203140c0010022003004000f01c3c1c032154155500d0015030710600c801001019114010452a0140c00c00c0f00d030a000242c0b2174003d080daa560000c4042550345060100b407025107061203071050700010702545030050f80d5010480e40451104141c042011140d800320145102c0c4c113083c02090128030301820400c001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 542226330 1250 542225080 542225087
    0xc080d0f0204171c0836100e070b0f0c030d05150f01080402010807031104260a080909130803091614030a061a0603191401030b34 57
    0x2d00400d5034030f0f8001051040c182030001518504c03559103020070550080c68440603218050043c2100c0300152005040b42803080406040300e010001e55181070000c000c610441e07a041c40c0300f210301940714134100380506803010400101e502c00c0310028008981e40f014003401001c0c00d4000c1080c008064000041c40000500440d0001c034041c1441208146c0f0340c07103003403040005d91040403d106011a0700c120004001d903000e600030075440f20042c1008254211040200c1c030056009030840412142503002c210001191048071402e905c1d040c400503c112801d0340c80b14032181c0030b0800d9061007502c580e800220b520a4810150810551001c25561030781010900540c07034000255004060300f1107a02c0c00a0900e000d000122409000540604a1072590f0b441e1540500102c601c03040140284c0748899070262660801544540b0030040c00c0017030195001c07441c0055031200c0c1c0d42240d508071048014804503050082a41d04091421030341009002045954130403809070302040c00984400e91121f0408640 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 542227580 1250 542226330 542226337
    0x40b07030809011103090a110402160f0c080d02190302070504020301080a020906100e010309060e0f061e0609011e03050d1709010c142101090e0d02011109010c080d0f02 74
    0x2d900d8001c2c0440c0c80c18a5526286003c11078003004242c0c80404000c01140310080011110003014201500e01107480e80948001d00710754108660f88a120b500b46420704c0244010480a015010050207200d41556402565a58907141d0f200303a9600824200c000c00d1700070070001004010242c0103640781d60b036a05100d9102c3e81110b40603401202c00c10005003003803070890a50104101542c80703071141400310f400110003e00c00600100c94495550071641403004081000d03080112a0600500d8185000c5030103a00d200c4041030810f01502203801032062990300d10030a80d055400c0341080f14100c0e070028a0100c800c4103107501c003402901030785040c00321040d8400c01a00c640001221011130030b4a500000d0b0f07080700c02d45d90000700051100103c047c13a4080c10001000c0001e16102d4603440c00c144100704100c0ca80082e4000c2e000310b9528901c7c0004070000707000f03d9180d05011300007084007501d003010500d61071240c0600c3c00e04004140100304100440070069450324070701c3c060104000100003c03404000c0d032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 542228830 1250 542227580 542227591
    0x616021009090606120b010e01080a090309030506090303073209032a0f0306010320060403050f0318010e0907080903160c090b0901030816020d020306130b090f070b0a020102040b070308 81
    0x1800c1041b485c5055005070b503031a040c2401a550214035a480d1180100248500c9108a041080c000c0001012910800c1014010880340000c2c40c1d60f400c3c03210b4041d0a403446580c40c07426826550001025000134080c11030002d0f0aa41c0355650f4a407440780000c0e041c003d80d014800d084c034882c01c2c5031040340f01180110340410081038074403000171006070040642e00e02091000400301500001040c643d4410000314081c0e01001600841c24a0b48030358031142088400342c1480626400410500b20030075200d80301304860142828a0890104c888000c100e83c400018662020b12038179001180310040c0c10005c40d08442e070604d08500d2240000e19003443c4220b580d1103030b40c0d034040c02c0ca0301102182c42c1c4405203504032a0301480031441d1a0542e00d91110100101c07000782e03070003241711841c0005a1011f2144500c01d144000c0c0030200c0c611245400540315001400445a40e4003803410304400e0f41000494a081d00c0d50f0641d050340310031840d08103e01901c036581120881c1a40460580101500140d200c0e0107032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 542230080 1250 542228830 542228867
    0x90601140411182b0201090f0b12220302060108060108011401150909020d05190c0c0605270f010f090201090e0402030a02040e0307060b0616021009090606 68
    0x44150801c000a960080c5001003540000300322031440c451100c0072100c14540007422407a15007100b035000340c8640e420060b400a003d81094900703021903900c01744500241c20b0451640d100c40c3d00303100c444031603401440158040003540c5030114500300c2502900c00c1b0342d003481c10708414001141f85002515004c0a1084e10407901c02e60300085a4400180070718008050741c0440350300a80c0ca008041001c51011582403024000701d60310200b28a080c0e40001c00c425403840c1004505414000550312003038091404210070140303840390300300c3c200e5407000c0524244c0307030860070100b5952100280c00d03ca403c1c01c0690540c0c030032840f40301110016004125203180582d071030002c00030645070300c0c88142500c1d52024000d0001d445210140000d06175100d5094001f80007604990001e1403581c0400c040f24400c6641c601242d0011403884100203040c05040c030400d01c15502103080600400559000b0b02d241c540c000d00c6075a10704500c0d80580d10403d804002003000e034005000450742c42001030300400d07070409541c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 542231330 1250 542230080 542230109
    0x10e241b1c0f02210c070510060302030d0e0a0512030c060114091506070303020705010b130b10020307020a0506090d0807060204090501050609010c150e03070809100c0b041712090601 80
    0x44045842514400405040078550001080300440131500f00200200c0321002e040c03001002180d0100a4243c1d01448641700150031411801054903254021900c801040494440b03001a0780311904d144d0200c600956114040e02c91032010315055010b4580880c0c854880c40c800015290b408014500e40d8100039a004005074a41101c0c40c5c24100f0000f6410360040010006240045d12a50003805910700940001840201e17140c00210251801c810024201c1d441742030255a501d005c05410b1940c0109000651a102da2680411111000351044910440003c0380413103003030300c2e4541e011060340d40c04080c1513030343d1503d4508000250440d01840c51107d10305030010400e4280b10003103c0d0003820503180d034585070001c3d07640c0c00e5040c40680e4000c0200380d181c01c0c18026101c800c1001d48a207030300c01c00140d51034452800c18406180d1000d83c40d5400c10003c8404500860103410306107420a030050f5215800c0c82103544014110b21900942d1200c200800f010401d15075400300e100c03810f940826081007003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 542232580 1250 542231330 542231351
    0x1b0501050901050a1104080c090612010e07050a09060e130c2d0909030e211f0b0402041a1e0c03030906061012330602010e241b1c 57
    0x62501030790099004661129904048c0d0b032916103d40c07648200020208140510500d40150940c2d0140401c100b240d40901c0302801145016100c010180c0031000e030800600b440c040720001172040151180e0f1110200380c2401050100f5034042c10054070760340340d02da42411106240300030444100c4016807044041010302042c0d140c0c050181880140e0565200d0040402fa401042420362010200a9001c504400382c040c405d0310a2000307024440000800094a031000400b07441079a4180c14054403652040109210b500e8140705c007a2402100243d00710b444058502018042c0c04c1c0c2c400b9620300c6040007003a030000c000350000045205100707440c10303141d840d11610280b100c02c0260041200208113152041c40001046034010209110320000e5002030103042001c1c150100360061f582c054890240c0e80c00e001030f0307809002d0506407007002001807500010800300051b45110020441c000381d202038001c194000411442100101c1c40f0301482980e41040311502030351044540c1090800d642049030044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 542233830 1250 542232580 542232611
    0x9030c011415030d200c04180201020114070c081c020d0902040b01032c12030412021603020d0303110d0c050301080c0a05090103030e191401110303161b0501050901050a 74
    0x100920722611248055460030b2050301141c172681c0c104c1200381c400c4100c1403100340c0d150f0241054441111881c0705e0211160300009094a11461031441c820358000705200596a0140c410f03070059403c490398a880f11903d042d000e071602c8555044440c0c4600104900d10403a01c00c2c0d01c4030010501c21a001c000415164006505949d0010264a250203d502c020b581c0c080481003160865100c4100b41d86a021803504801029001500c06480301242900c00080c2c03207404210142d0111200c20546406615550000d0500340030a54010300701500c030461080c0c1040c00c20117079080e044100300300788002910010000c2041d04240310700c480d14447e40c0b001c00c0550400b014444117540014003001310503801c5480683d03401001404d200d40001c0e1402d44100e00240090505010740a00034001603200481341c001809201d904c030b990a00c80d00308109020643c14540000d140c41041401c000d035580d0300c07002c160203012066a030003030015400c01041040429040d402180b10300d0302d45c1c0c2c041001018015007003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 542235080 1250 542233830 542233843
    0x801060e0901150207030506150a06020316062c161a04030611160807110108060102101d010e0102030f0106020f06131b120b092409030c01141503 64
    0x3280c00c2051140140420f503041c4001030000c03040c0d401110191541e0355602490800119800e07509803c14007069049882d001d2203c80081105100031130411800b20071208191054802c004c1c00c8640e83c010b0740b20007100038258000c08107100607090100b1844241f8070754a43d07081290081051270085004108035809a034046034032a00da00805080c28110f0362050700074071f410102480d40c20400c0c4000350b508510340480001c001e2040b400740340c0714001854115140c81d032426540e818001d900040001c41e99000a090500740e40b0010003044450502c0c100040c25842d541010380700303508194010782ea015054002f580200880d00c00c0b000f15030390380c0004036256905402607903c00c4d04104007040750102c0d040484180f03030f07004d40304864000429041800400302030b5441080d000a451000e803090100401c000c40e441038108024001c240799000b060400c003c4482082c10500038603001085082c64104192181c0c0d880c20340080020b610310030001d0380b292602b2170b88241e9015510714112070904010500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 542236330 1250 542235080 542235107
    0x60a0e0601060e09190207030216080712020f01030f050a0603021503040203031b0705061602041815020c0f0f0a020909011b1d0306070f2d03050712140106080106 71
    0x118403040e04040100304c150b5202505030307141c4402804112035800c145100500201e840380c0c00070074030744880d880c1d41103400100b0b600c50119038120a1041154840c0303c0c05440074564103d41c0030700d4881e0240c0040e0b0060043c0705591400c0c910b0081040517800b1a0781c00752081d01d00895007000c1c0c03456500640101c2d84030884000350141c005020982e150300e60080781e01444000e030803c0e10000340e180d0f008a11f035034018983c00040c3d80c140711502c00079800e2502c5401d001d9003901c0180081d4042c40e071034003101c040ca030380c402e5200c42b5400520501455020702964890f0b0740b030802515024083c1166003541e81d901d07004140d00c034402c01004505000014403d41c0036041c004e540c544d03105003906109031920003102540300441c1c8a0450722000d1983d00740201441100d15490300d14071510b00040c002d18100081c1e0105201c0160f00329445a9850f440380c25401a0380c540c90701241c1e9a40d0b81e10221511800580d21090560808086141c030691089840c1c1c10390b1800e55602155a9950000300c0301107a02403903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 542237580 1250 542236330 542236337
    0x10f0f0209030f1b010e0d080c030d0f0203090c060a09090e0a050d020f0c0114120421020a08090603060a0f0824070c02130608030d06030c0b07080417120705060a0e060106 75
    0x4c015255406039103600881ca400030b185c5104071a00d5199010a94001005a242c540000a038050340318150b10450106008032030045083d441c0c04040c80d6a20000d0310686841001e010030340e0b0724410b1085c0d040f0300261400c06c00a000c00a030740d80049135100b41003002207800d4000c000c180c004040c40010b01c01c1500c10454000c1800d041900015200b81100c01c80512a01004004400e1007410700c0c400d40380035a105a2005241c0c8089404400104000300005021900304103e0000484d02d00c206903120307080104ea40721ba0b207450f0340c030000e480880141d100051010351251f00142c090070120701901748100d000006801e101d070840c06c2032000042114054003041105c8240c034094188203903d0744c040b4400c88000134060361185c00766031841d0054403803628101c0c0c440030240308111035076000c180200800702c03a05081c0b400984d2011198081d80c0580d454541e107030301c0301d13125408040220814024180c2d041070303a282e9503030030700d65165078089aa00350341c0707400c0042114110000081042c101c554995 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 542238830 1250 542237580 542237623
    0xc010b1503150604051810060806060703031a150c0d030203010e0412020109330515010c0302031c0203180a080a03020906190f1701140111010f0f0209030f 68
    0x102e050000d2042080c075660405014040458140c5030342d0583c4040c05d1090300c14042614150b0646001800650404000c200f050424003526407140c1c41511041507041c1004141c5a9000e001c8488040388040d00075484150304240c40c480034003800c0188070322080c800941c1c081c60a07000302602640300070b20540e52000c2a090000d001f065803001105080a09032001241c1c41c0b98a8841880c50b45080c0300707807411020300ca040c0c0c8180b0f00c05d00b850100761109000b414007980c50586c1501060341104840a41403000840030b09080520074001c580c08001420048001d17602c40c94400002500102c41031a00302d41b100d040725001d003000050940ca4240c3c89840b06180c0b814001c822006504800c03e0190000e0040c0000107903844540da914440d0a01d941d2440401c00f47c80f40001e00550b614030300c1507a00c0072030f1001400500460040403062200a007010140d4240321600b160040c000da040101030039217410503500d801807445e0010003404c181101100c1c2905030000c00c0b1621040d501400310a1400444c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 542240080 1250 542238830 542238841
    0x51306031b110a06061509140306070c050a121d0303120105062104050f0c090f072015010602070609052d0604030f03030f06050127051003020c010b1503 67
    0x41c106181c0e15141c2e1001d4405141c220303503610068688a8002d00381d2800c0020080e825a5409240c40004103105c42c800005d490244000c2a100c40003c2c00440400c2070a030b4142051200c10070241e03408c0b03507019400101c003910000c00107007a03036085c0d10b0103045000c05403074110640c80c0002c140e13a806080541e441480fa464101000301035484103048220003036101d001d04490300c2d404045144200d0142000e400ca07041004500c5042415103412584542401c009100002440c0c480c2c030356000d2910701b400b41c601002160009007800710510100d0851140707104600c1145806640941210340d10b03022180c002c0d483d0300045d20981c002d8064030350428204501c1d103860030700554441104d82801440586040c0f00c900208005a0264001307550003980c1d001044101030b898400e10b50300014521040040b01e04201c002094640c03800c5003da2110981400080e042e586600880300400e0020400341008465401c080d010b0340020035180d00c65440c003c02c00d40282441840300340e201c0c0b10304000c64515900d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 542241330 1250 542240080 542240087
    0x60a06021e0c03190213200901020c0409060e07051210090f120c150501050904030c05281b15050c0a06050f0103020906040e032a0706051306031b 64
    0x1e000d585441442500550200c80d20b00344031210405000050364600c0351002d0041c488011201540900caa80c038000480500d880001c40301070f100c4400c50700c826941d480d03110040b464602450581580103140034800410000c165201d240c6d01442e80007560640c030768510412000940603a4403e000d6040f042006c640200c0e6980b00484031407050b1440b501c0d0203500d8640381c1e64500d47e00d5100012602a00c1602c061210a40680888000741c0000703004544c18040468202c00001d0b00080605c00704090440401009100e51025a0310400800e5075008149030b08500b2002102400e840c440210725503041d07041040f018039000d4405682c01b04100f807603181320842e0703640d1003001c1010040c0aa40030381d10016241b0f0107071b2405444020300d814004e5045004020080e03202401f000d12481c90142420484000841560034290341790322160358403071489400600825420342d4815050040000c0400c15035042005402016402400610419250385d803d808860903041640000b0702d04803411080c0620 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 542242580 1250 542241330 542241373
    0x5090f09060a110403080a090e0a1b0e06160308060f01090f0303050304230703020f0906090c090301060308031e0601080405120d060521060703060b0f03060a05060f070b060a0602 78
    0x40b1000d0607103005ea4948030643c1c42d40066036520001104914100043c1540c030031351035040034600d83c081112502e00a032003519201c141c41403409100c41042810300d60781d07620003582d400400d403498403008185c06140040c40e05104a03034841c418084698100c100f54890f0380e1100549021201d860b04c95800d54405640a4000410440710707014034141c3d440104041002e0b800d03030f0315450303801003403814114410400150711000c03080c0d0068032090100555540d49041d60b40d0081003500800c1d99a1920f50003084c0540b070203800280000f903001003030203c880f081d08030700d80e1a003580c1d900d01070080c1c8684d4011104041c064030050410351002e0700c030a118984a50090150144524001034450341c0d800100b1701110010098820090b004010100c06050500146d40d1007849071400b0400681170442d006050301a50042032401c160110001d0107549600303001c00041c090090035280c6800c2c0e0503141032510303403018604552868284010801c00c1c10a20300c0541902d40e9a00504901d14103284900c05060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 542243830 1250 542242580 542242601
    0x190e0a090e03070602161202010b150703020c010c0309090e060604062c07032309010507030e0327030303102301050d0207030314010b0c07050306040f170d021305090f09060a 76
    0x12001d006c0e150010742c10300b80100c0c0d40180c9800114030b141945040010200484c180340003008410000070000923401720300c0f81070348482424022100001802d00703c49014140c0c01c000441840d01d804035a03035500c0040c0f020300c20042282c0a0110a0315000d82d007094801e000300751601141125040811803100b26845d66000e001d600d40000c0840864804c4200c0380b554001d1017684602c1d040601c01c0d604000c0c040d03030760f20022a0800f0310002003d40d204527078910540085012940300c00c0b20800265000b40031061700d40c00000d04aa44034100b00c0206401444107110303010802c1200716032080d0354400303915840c5a07010161a840c1c200b05014040d1000780d80b002500301c1c1050b50741c0ca0000c1c1c40c1a54a80710f81d01801105821540700d1560010051801809030803991081d8400400c0200040e6000b1030040c1240c1d0044900202e00d9101d280103c06025a185900109001060000c0760030081c11001048860480c2d1200d102d0b150300aa280c000312065070003070301310340007030000070040e1070740d03400520320314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 542245080 1250 542243830 542243857
    0x211b07020907140d05040b090d02120d23010f1401090504050a0f091b0e01030f080c070f121a040f02090c160b0105011416030e06190e0a090e03070602 66
    0x9083d001003440c0300ba40664014107003269524180002c0c045001ca90329884002c51008195200705020041c4d40c4080c14414180182c01c0025030075500241078000085c4a01d400d9500c0d4800b2540e5480c40c40208401d028110700710701c0f0040002003404290344048013915040e15117625490400051102805000301b004144640700c00300640144106c0c8075049020b4010b901e11202a40028110003109034258803400342a61200010f101044411040d05603803680300309003070b9444010402c00c40c01e102050380003520020105800240204000d42c00351501ca10864106c40040200c2c0982d1345201d40945004c0c1002c4a006084801411b011459030f030440d030700100c02c41c140000301084020040703c000d011111a808a0010009940c0004003001440c50164440341403407039080807291032a0380c8000241c01c1106490b607503088c54440c0c808840d0b807094a80308000605800c07043c05008450030a017124065401118005a419460712a40c0406d03401175000e18a02100d030f40b01d820285d0480e480c4083c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 542246330 1250 542245080 542245097
    0xf031214120a0e0a050a02010909093809030a02010c0809030d090804091811010804080a030c090510050705060a1814010605060c061509040807120c08211b07020907 72
    0x30b83d2410403060201d00c0c42030b00107145030104d600c0010101042c50f4000043c1c0d50900f0302d21400107580e08850040248582a040c201e00201460b100c1c03108101400100628040e10030f21400c07880200c010400005a41c00170302900c12401d038100d50f418012034403009140c20922003001580102d4008840710390080c030355075051540302c180301012a078481c20700d02000f070220000001000242c040899402c042401d14064916258a4840c0300d0302c030701c581200c06c050f5207444060390705000c0c12101018000203803440c01c85a403685000f8000d82d200c810140c2c0d40e0700c10302c000207280f40b00700d00800c1025400000b10751040394580c1d9905407a55803000c848542c2d03540f50034002c1110785840f8040d1881c504000b0007440142403450011002c110341c0c11103e401003904100700300114030b0807800c88403a5a0300c41d08a5400c000303142d1040782c4000007000b00034203840303000a03002c9110303c4103109058040c19850101c4404e13203540420f01c408000b207481406440303100703202143c00f514242212943c416100c0c14038041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 542247580 1250 542246330 542246351
    0x207080111180127080a2109050108220605040b15031c1205100608010605042303010e100e010e03030609010b030601050403050d03021e0c100f150f031214120a 70
    0x4804d03e0ba5040898654081d2200d08140701c40c0b20900040320000007403034590030814040044c00c2302d05500826040c400302c507000c10b060101c00c50700d41d070b02d203c5504000c0340b203103507035280082c09800c0c19601695000006804140c1c484011160401a00c07001030042035111451620300e807042ea0345601600c14001c408030340d40e0b22103031240103040c4510f041c0100100c00ca4103000015010703503c1038004004100040c08184034100c40c0522059504040c5401c1400e00302c0c8610000b400751002d401b0101050142595008903c1010f0b000840ca904260000384040d1000e180b5099480c002110956840702d581c000401214a4400003190403d1040c9802441c00b0388903144c4918142003114030741c0000c5c0d4000750040d45211748025801c0c1e62140c03400741514040c482583c82c2d07502c28000f83d0f1241c056507100c0d1846409102a0311070007501c60a21781c000c10160f5655071200f407107000d82c481518154440040707100c2181c85003c03101040114506424181a204084a82c0400004200c0390307075150743d4171500e43c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 542248830 1250 542247580 542247647
    0x6010e060c01180203011409030d0f0b0402130801050606071104020a0309120206091b13111303051e03030f150604120809010f031b03020715020a02070801111801 71
    0x4022410f1649071802e00c3c91a0b04c107040c211600100d101c021302d4064418058103110100460700f5030120044081030700503407403c9442c01008200c0303116a01c03920001da00ca00404142007500111060403008102079aa4041402864890001c1c003d06040740e110820003d8607040d80076002000c04c92030006010000c0340c0d15036403003c41240742140540d01510410409040c1000117122880c10000e40000a00810003c00e160421700c402290030b99855004080c80c4900100640b004904540c200c4c40d440703690b03410702c943c95008000d08410b1004494403208500c00c030000899004040d600b130759020f41e9032000310001401110307000315680729808000001c0c0038510103d120160341d025250b0070369254248000505080700d24072a0304181802c000340582412101c0e005611422403509016a80e10705601c0d04e4820102290900c0712283c3c4007007811951590300103490300c19110220001c201d012141c402184043c01011411180e10916043e41002e95100f455503c0c2d0040c2041c8000c9480c840150410303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 542250080 1250 542248830 542248841
    0xc030a050c06091c08151c060614090612100c090e06100207171c08060a0f0b0f091306150215010e130302030c060115031b0806010e060c01 61
    0x5000180010440e245040e81c288032550300024501c00502c500d42c070300307142401410005030071542805100300015403038202c030304144089500c005000c448032445921400d140c8100b500d00c10364030545012000b05a103018180326882e9981c0c01007040b0401c1d03035210104103103100e01484402c02402111481a505d100d9406404412a00e40e12061521405d00151203501480100407a1066100318540c000c2d068000c10702e0f41c1079a41150741c612440d402044020700e0311391814840145905102000384036298400c424a000790b0080f81c00d80080742c0e44104400c0c1c4140c5501558903030280401404c1d40da902192b00901c10305c2005010740120803c20800501207600661101444200400e20007112940c140600180d285a0418901d59035040030f41141409000030284040c00d10b40f0603501003414001c0041c0c5048a040d07008899841d07844601c3c030701122556051500200b41082c40d087c0000f640304050740c2203c0c3e0070356030300b213940e6031800011180441710b800b00581000c010817403450005400c4c01607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 542251330 1250 542250080 542250097
    0xe0303070807241b02010b0f060915040306092f0915091302030c0402160b070207030512090a060903030c020108060a050a1d07020c01021506040f05070810090b010210110c03 76
    0xc5440d2031084131383d50207104c2615401103915003c0034203210b9444054500d40305905460035074440c0c15074000728020580800c160304000764041400030800480341c100f0340c3c50381e1003505c0420007044190122011524204a240d1200c51429841502030a0443c0026800030518005d5045825446c0c00f1078074004003664650208980000c1010070350800700320b001d94000054504528000204220707088684101c1c0c0000e0048100c440414056842000b41002546e0081e007503410340c222102c0704860036404452903502845200400107002c502688589086a4140c0c0b5451a440c1c5140d004603031406000307100c5a440f019003840860240c4421000703c0c0680107051603204181035070b6541c0c60340702e00001c21482c11540300011015840e40d0100e03500300c142481300501029900c8444c0007a001d4022100f148480310b2800c81040b140b55404000203024401d207000c2a81c2041c2c58984280a46245000c03003405640000c811400f03036401039021481c41100103050500b0504c00e00085819548070134203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 542252580 1250 542251330 542251403
    0x111012380306280207051507090906081f020c0f010c030605011d0a0e0406020705060a09021c2001090308070803010f080a0302060c1c0903050307020d0e0303070807 72
    0x40c0200503090400071550045000c51584101c1011000c0d42c040c4412000c034a503101680100d00e00003040001c2000710f1391514109848a0b5a03e8070140c014844081ea208503030741036007001c000044c0864045510807600380605851000d403d0202d152001135030000401c0045886403410091071030f4822b200b102070f04900c1e0755000c68540e18140c0010180342c0160950240301501d041e5620141c1c1e103410102d030468005810780c08184e55070b820164002e0046010180490041004120f403807000d0703600580125100b151a030f0311900d1681c003042c00010304400014441107000b180f50301284142c080811807040141740c159846500e966810f0643e420608084a0710304010005001d020f081003040000742100340e0003000d00c0090380d1002981c401000e410307400780690011304591144510314030a2507402c16181c0178000901071380317002401948119010001409030404201d8a548203c185121715031009000f5410051a501e99103401d07406074804864807810014680e800703140c0d001440310700c084c2c0a40e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 542253830 1250 542252580 542252681
    0x5060c03041103070e0a0c030b060d05100308030f16110606090c16050105180a050705060f2506050a02090f120102120f0901060b0c030d0e070f030609111012 69
    0x4400687e85084200d509250910714564030701d454101c00e03624203a26000d00401d443e120100301a5105850341c0002d4010700000040244c9074052041d110b02504112030310703107106400c0c0726007242c003444041400746450700000c02050342480c240c2e24a03500401d20360700c0703689410b40f50b421640c0011040c40086800f07035100c1080040d40c0d070394040d407202542c81c45405416007069a40e210703920744100d8000d00d40308000c00704030100301e07400d240240c600f03202c10200395070b04401d5000301301000b14402c54011245541490006070b4080647e0007a220300e6000980b0541d41e5480440c108100c149030303d00560900e41d401d002c50218508180364541c09080140080c2d0110305007c01d50600351350071038004a04001c8104011611110000704032aa071404465001031102c00c3c0300d07035503410074140741c0c4200b01c80c0740d9480021051013110341c40801c80b02c0c415200b245806039040180500d0f07005071a12130011aa04040844102e201c541009420f4255a041100b00d020300000402d07181c00111142400c80403070a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 542255080 1250 542253830 542253841
    0x8010e010501030209130c0b0f0d140f06040615050c0a08040f15020610090b032a1306030c1503020d051006030c090f1221050702090106050705060c03041103070e 71
    0x28a44a0300864900d240b040c8598198131801c00b141e00d03502c110944401d0006080c0389e805215400e0300c507000034100c0d00b881003118220700101c50110558001340d440b807a8101203001c0d4540b61250008540c0d86100701c108820600405403002e8101e904c00300030500034526800700090002004002074404820020409400c01001854954070104500c040d98081c0c0280a1051b41003003e1108890400d000480c9000e254400300c3d0a003890012000c00002190212803a0003500541d001e10022059407407840d01c10b03c02940009440305844041c00c00c00c01640c0034015045095070b200001d51035418098904065030701500d00700c40c001c071a0010781c41e0078400d06000480d418051541d0703402140c07034012040c9003010010782c440400d9210320100c0456800d1000200104000480d1705182d01e0b1051048000d83c400f8081c1aa5002d610220b11074075502c00007090f0305019a042d14a0300d0381280041c00c0c3c0c0c2d42c841022090300c0d0320140090b100441101c00c00211030380c082010704080c20008032420346d5401d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 542256330 1250 542255080 542255089
    0x3110409080d091b08060c1206031f0c0e0316090b0d050d080414210306012303220c030f080912151b03040206031503031908070503010b030402040e030408010e0105010302 75
    0x36001004e80b0740146c4240310080300010160342d0041c054501400c00c0e51103030340c006464100d1078000724480c40191240911001e020717a002c0301240342070392564580305914900b015120501400703103000010051070203103c41d100c0b6601101c00c50700c1c050305c001480241030300c9082c030309401090018009541001040f0070030004002580c8002142e000401c003050b405600c0304c0c120074003440000303141e01c80400081c2c4640c0c8207894035800000510205441c60110030442c02c42c40d80200c80704044042042030600d202c0c0794075408a500d0741c2c1c200c00343d9020b090a40d59441c060714070008082d40c43c0340092060344520340d505496600c91210300001000301c80380105490410305070040c004038550341ca0f00240607004542c10106e940c8142d040380c0d856a00d41e0784480650304d8290840d4096058800441d030728881c40000c90106101e0441500c07414102c0c0c0c1e0340c1804039403c0c44240030302c40011300c062011400504054200342c2004900d0003c1d21704060f2a94882801c403000b16040d4400e680d1070344010803e5041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 542257580 1250 542256330 542256383
    0x70506090705150306240a03050907050910060f020109020406231002030f070206040306110703031b0905010e0a3b06060304030f0309050a0c1e03110409080d09 70
    0x4054039400210800d2541080f0b0741e02000700420301030000112506024450202c0d01243e800003c180f598444e01d5024004004240c2141c2500c840e1050040105452410308006071140b020350070b909941c24104a0101c40520740d1042103000d640d05ca101d1400180daa90003541d0203010108010384203080300300f04142c07680111030324050140303150034500144c1075030100849282c00b210100065803030f034080c0301140d11486240d101a04035450f007000d00044141c100300610046003c0d41c1c3c02e00042c8000d0419422911900fa000d0000c01c1c2d00070010410b6501079180c80507031440c001c00340c1d1a401d540340c418031091036202030ba51010070361180744040c0f0003403014506061803030001c80b8200c40f4038003030000c1015880082d00140a1080780340901071010710030340002c07008991042c00d07507401c03401c54900116814a00d0040303144038010300003d940c11f8441021030f5001c030394101c4507900f400c17003107041804010030012500b170310b50400070405081c4000c4c4a004100a00d840360042c0c0740307106110b1007603521444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 542258830 1250 542257580 542257589
    0xa12090305090f0a03020a06090303020d1106070804050a1209210c06030b0d0804060c021806090105190803040f090606140d020d090b18060115080f060103110705060907 74
    0x2490900044082680075042c0caa25010540d202100f00c82c00c0d60001e401060744d03502c0298850a80800810f945520038130b03600441e031194007103901d242c00846096902080f000076889280d0b1002000540c5188100011a00305000303409035a240c542035101e4101e0b02096501c03410108280820030080c026240349900451956680c1030074080580e550360003510582c5104000c10142c41c0c9260340d07500d6480513204c2807915407140d10a42c0d205e03501d0320040c00350582040260b1048100310302d101060800098aa0701c0b0342c500038501e00f81c0740e00307003030800021403404070001c00c50542621010a019008100030006056413140c0503030420316042c101e0081da915a088082000700d5204401044012003040e5000c0745040345015855407101603c0000070b00c8600d40141108203050140007018140c031900b030ba071400381c860075112561303210b5500b0f036400302ca030b054404001801c40c00010040714210503107070b801c0b0005140220b00b4203005041400035400501007a2450740141040c040c1c250310801c4100000d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 542260080 1250 542258830 542258867
    0xf0f0b0f0d0b06100215070e2412090f1506040e120d0e0c04020f07020a0911180f061201060318020117190e010b0906030c1f0e1003020a 60
    0x300c070603035210310245601808550040050715941342c1c4050003030181d003008003005100445c01f803038030700001003001c2c1d04650504e00402010b500c500d11002401c14020b60070464450f03c0e403924510010600160800608554803401044803941f13504c181840300220800e2035190682503410402c04010440d0681101e00c206503121070150043d49855605885440303490080006091285411142c00c01000c4840580d115100040c0a0002c642034005032520a00984680d025181c40f209100c040f02d000c0c1034261110300381032202120003019580010345495000d005001400356607070214407a0342082400c04103c0300c102005100300c59040c4251001d00301040354180503043c21b900080c156060319213200c222401001c0c0061454403088103028851018030004000250000503014020010684a94402c42141000c28414900007622075200d841c020032825000f42200a2030b10001031044200c02403042d40b80d4518103a079900303001e240484020761400341c1c4d10600002e0040501d03081c8111003240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 542261330 1250 542260080 542260099
    0x215090c0a06080702150112031e05160809030d03050915060a060f02010e06070e030c0114090607020102100510030204060518070e120118050c010c0b06090403030f0f0b0f 75
    0x125074400c4100e600701c0d851401c007001e542c0c490f81d20407402d0036525071010b5118552480000381c0c1d5144003e4400b0800d00075600c40c1400703460040d4280242e10700c1c60b441800100300380489422041400c00c1c4415861280918510300707901070300441c2c1001304080040000c40c1c0e40d881000b002e00d4080c0a512410203101c102c00c4100c0c41c0c6440000d4400d60140140003c10503d40750140381e45000358000b100c18a2040c084446034603101c00700a00d4000b50b000114041d008440108005501482071000c0c0211035500b032f2420b109940c002e00c4141e41001e40c059046205401c01900c40325480d04c40c1e64050030070318a540d01e100742035005200030f80384541d0026016006040303031800c8802494034159000340c0c191801d9042c1c811b070b8500052049007406800c54040d407038040301d41e4a100031a00c0c4a40c1c150b128109a0700500710030070055403815411080a0301c3e0005400000729540740c84041113500c42e11905001541d008a40c4900049501c0342040103822541d0703000030710052408100c5860134a5089884406 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 542262580 1250 542261330 542261353
    0x304020114032802160c060f030e06180316060b04051501020c0d0501060b0409020d110705030a0807140409051e1909050709020f0d0b100806090703090501020307021509 74
    0x40041100a00382d007008001c110303500049249070110f45d102c440c1815561401c450030306051500c1c01e00b5100c0c9001003155140007511040c001e000303400300d5507185005007280d50340390300781c146001c140d8102e20442400104244082c0312911140000082d024000009441300040c081c8002c0300c01c040c090481a03c180f12180103280c0e40010102e0140b0030984074006152150300e00140540740d2030300180082d040100380810b0795034695029002d00c41c1c601200307000f1580b46240e40703102849048070290054000f00b00320b05c28507016041e115004a51441c003800303441c80504c92a1306c0754010303400160032980c03500309021610410340340d21040c00003075146e031903020b080180714030030040005603000080c0b50b250800c95050040c00d0211400408050070259500d5a8864031220389030310807140301d080035203031140c011442d00b8000740c090311101c001d4a032020161202e60400021000007840c54040503103485440000a00030f0001c0c0d802040701d5001040110010020b41e5180b000c0189031625a2340030f01900807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 542263830 1250 542262580 542262601
    0x507080405010c2a11040203070c02040501090b091b0c01020703171f090b1503040c050907050702030607030f09150e0c0d0c0905041401090308040210051908060103020d0e03030402011403 82
    0x400c030048984c408055610751809281000459416a030b20500c003104118a01e50045130f241c40c43d43c82110200490707a22225400d045644243c5a2a0040c9502c0c1c0020901c0d081070860507510b10580503080e04205045041c40e003039070300040b0102c0026154201000e48560a03901c0740b80c202012a801c06105141024000040c58030b500c0349450654846400c2c5205c2d441e2003001256030740c60b010880303940740340500f442c0782d4840e40c41c41003d01994402002920b998031400a880455500030041c2c541038460502c00c40c040c22000f50552039055841079010001740d488a01da2000b1503a030400070400044002ea01810700350081803681c081c1c0c000002510000300700c0c4d00c0740420743d010140c0008a6071514100610324031202d101d1000a50301c0e11861800341508604600d20032482102c0a050b00d0300220070855560244910f401114414940c0340724806009650b12540701e0010702d4014181001d00044500340c1e04000300c00b2a054000005000965070300c40441c2ea000c1c20301c03440c114a1810a2440c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 542265080 1250 542263830 542263877
    0x20912072c06010c15151706090723010e10110d0e0a23060d021e0901050306150c030f1209010605150703090b120f07020615060f0c010507080405010c 66
    0x40844417125100c0c0e110521a070310154840c0180c42c45040305984582031010340c1c5580a065010718410034001904800001410500783c030605c0f401d40c550b40d02d00e080007220b01c2410696450500405154580240e213490106142c1c0c41a641d4070206401d0035804058202420344000e10104030326019001002e48441e00c00f101220050790903180d5019010301042b0281031802d0280c2d610040006a4401d140502d4010303204180804032800d1031804180840040307446a100c609000c030ba8140006040381c0791050201c58244949002c00f440c1032450b0035090308552050300c0f11009584041442010004816142d0f94000c207580020043e131414680014030804034ac003102c40580c44001013141c00c03d8420380d80c40c0c0c0100000ea070321940b246140c0b2161161030000b01c4110f01001403a400095800d0300c0040c8160280f000301e100c00d05c84075604014848554490b04803d103449104002e8505d10600901c21944104000e503031720345003810700346881c6007520b203645440000c014003290032140c0c065600014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 542266187 1107 542265080 542265083
    0x316080d0e0c1f020c10030c093f020a0e06090714030703180f0f03200d050306030f0105040809120601030f0204020912072c06010c 58
    0x12481d5a03180d252141980094a005a58040305a5202d10b10f07001805105680810010602241c2420840041100041e0395041031120080e88040c00c20701400c852094548041d4001803442d504506520b1202d00b40703050150f10408441c1c0c6039005c0000d03a980030708103032696540d5440fa145e020f44100c03042806070f4102000540198880c6940070074003c40c001c282c50640d11510811001081004c10032040030100203030450206400b2550403150328440d1840d81608181450010020111030040c0c2c40c840e04500c0003c11050004a18400c4051961034059266900c000001c0d1500000c80960070555107000c060005010f4400d0040030108000d070303803d005108040110956880c02403102401d40100791249000520341600117000b01c1400500d03030000401d0f080b408504000342c40d4003100040714400d44140c01ca0030748815001c04506207d02c041c00c54a440000600202c010060 = true := by decide +kernel

theorem cover : BRFrame.Cov 542086330 542266187 := by
  have h0 := BRFrame.cov_init 542086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 542086330 ≤ n) (h2 : n < 542266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
