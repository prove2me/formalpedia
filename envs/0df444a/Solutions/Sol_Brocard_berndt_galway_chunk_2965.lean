-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2965
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:57.921991+00:00
-- url     : https://prove2.me/submissions/d0545f1e-ab24-4071-8e3a-e57528cb4c18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 533093525 ≤ n < 533273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 533094775 1250 533093525 533093537
    0x12030c02190f080705031b040e1603050102030106080a020c072903040510150317091201090b040b060d050c060304020102032b0f0605090402090402040f020f19020c01080403 76
    0x100440d00c1d00340c420881c06092281844100c1c2c0c49032268200c0c1e60151150704a1407003440c00000742428046a0030030801c00300c103100d8006a5620007800040c010000160003d8420001461240400c0c42c2134900954450700000d0307070f80c0d450300c0070041400034090101c1105501c100080808110700280d48802c440b5045040345030b240d207036110440610b1640c80341242d01500001044200708012032446207d100802041242d20744400308030003861070780d0000510046410401003801d1000c5000b03400444402002c4080103411000c98a080d00c1024500f100c0e040c1d4a0300c24081040441802c079548010180d900d218044619180c0e5580c1d440c3c07086c0024010040003000c2000c1d0b902c20300c02c40c0c001110140003103c48080c0b070418170003900300407000c0402c0c45190590007442d024030b078000c14003240c000400d821015140c503001c1116030f00010380120780c800c0c5d175036100705085034507800a406010b0b05850b10b151603911118858202152240c00304003103402400400c15140c0e04080340e0754001d42c041c5002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 533096025 1250 533094775 533094797
    0x18050405031e070b0f04020d03030b1c031806050c0703060902040902120d02061b040605030603010f0c0e040e060705120705040503011d010c020708061504091208010806010b041203 79
    0x5400c611076280c0c40440304a40c0b0b8060010341561000510400348580480c00071950380c290741105203401030310002d6200038124041008644207400c406410307140241545d515140c05608c9400c0c03049004411404162011840e0119001040c0d44000800c2c66052036803400310700f50041e503203c071201d010080c032003030307682d04094207546450b4440da029950291146800208440303800e03581d103682c0c1c078100e00188034506c0010414140548160040107800c0001402d01381030460507240b50304000e01854041d981c810b003121812003c2d003d44168643c3d551255084251850288420b48007099141e00c40ba600c007200b407120341d82c0c0c064101c61886106508000340e503180c501c01240c10340314076401503a0560031329102e5004041b419104640c650f507088002c006c0c801010303070180d072501c14900c03d842c0d094000320002100b00d10342d0722580081c00d200400c000b501402d1662441180e4024002181c009159440103105001301046100d000d09066a1600e003840d1500c2c0008241c02010f400c01410005420300c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 533097275 1250 533096025 533096033
    0xc0504090c02010b060c0c0a06050a020d2706030203060a0909050a170408030a020c1206091e01061a180105041427150a351510080d09180504 62
    0x86140018000c01155442c182c0396a01981c8075011f0150078414201c009001030014011000c0341c00542841e00503124076a01d0304c405640714001d0540828041180500b14000f5114003d25080070300020f07140103859003820400e00c481e44000c2d8000d040401d2a009072140420030018240d480310713900c6140c030845440c1c0e07552003a003103000310750210f100b40c400440d0035034082d030b004900e001c91a2000d498a141004003652a01e03980d402c244ca41d000660042c44e4a114004031f41d10702020740c860324500210701c0300e684460301c48007012420f06a03400e00b10003084a03041108201030441244400b483d0903810320b410709001c01340d42130f002015240305116045040d426440c18080c0d120f01030300501c142d68207601d054030030140c15540c01e11003d40704403600100800c2d4488160759102c40199880a80700001c800060180c00c101c80600c2800801e105c0c041900714004406451944251141c04600e11100e01e0204000c0c13070b05000342007a00034800c083c4414003d01700581590b4045501e21600482c040e191070070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 533098525 1250 533097275 533097281
    0x110d02090c0903190b0a29042c0c03070f0303080109240305030304170c030f09040204030204061d0c0909190e030f130503150609042a08100c0504090c0201 68
    0x2e1404442e164071304a0010701840040082c441c0340c446800748000398031505000e120750b40420307820815000b6240700c58010b081075407003183c1501e000c0750f41030045810903030482c18105410305000c00e140c0c08001107080509017449400000c0040461044249040d5a005000391005020310b08100d551141004414881a0072845d0001c000d52103c448035512414515245d0b0300490f000d55440f082e520040102204000c121200c0b548000d020354207000c1450850f41c03e80c0e010304072603684550203100200169655100e90001010f001c0321018144010102c0e05c4140180109858554503042c0700702c49254a80304610f40d8000e40781c562201c40321500f10000c0700109942c08001103507100102e8182c110f10400d100801002d41d05880142c4400d540ea01007503910308100c001c0d0f04200ca03501011038404e061690760f064116105024210000f030014002c0301903504201140a801c005c400020804c0800074030140d0000001c1280900205005400c091300d01c1c4a54440e81d4103060340c0d85550b00718503100394 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 533099775 1250 533098525 533098543
    0xe03070c15051306110c03070f150e040c1e08090c0603091005360a06021614010c0e0f03060606180d0c0e01080a03090e151c110d02090c0903 62
    0x81d00f5107035000d4584400420200000d645000544207000070b4603114580003844004480e000c02c205c1180d1814601903082480c881200c00090004a010710300d419916401003000f03481403a5a19002c0b5142051540c640d220101a80c2c0103002d00503041c8581c8507408512203500c10002e0700c0f07990307994480d1002103103403062000d00344070380700c1c54542800000d040c540c2c0610a40c8c090840d00c42082d004180041408800300c80d280e01c0c441c0e1000f240d000c0090300c1900501141118180500d00001d0261a42c1f0501c1e40300302669000c0d6503450440c0840c03150003102c800382651007900c228855400440110b551080003428030351203400c002c6140f100f241d40702b10a00e03400c3c00b40a81980c0e08108549805006400b25000c0c20481d141142c0000c0341101e80004c0c0751000542660b20f10700c40c03600c3d001e51702180d80405080600402e178004901e03080764813420100c3d10210018036010f0340c803a01d0350824030141202c9403403981c41aa41c03030200d107002d41c0e50700e2080794201c042c1c1e0724050f0365a08000002841c2103508 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 533101025 1250 533099775 533099797
    0x1b050d0516050a0309050a06031a0d05010b09010b0307091d040f0c050a030b041211030301031704030b01060c02030d030c0f120923010e010b010f0503150405010909060e03070c1505 79
    0x2201c902010b6004605e1802ca9006441180c0c20740d8454006034150b41c802d06c00000300c487c0b90300c60210340b480c0c17110007800c2190080000140c1d8084420100b068803800742c00c4520703560b0000041c0551036070310801e800c004186200060b8142962000a003001c40801b420181c6141040c01c615000d005d5055841c1c0018080105050403482e0b480c40c01031461181250180c0300d0001c0714042400d95402280100301610140e40a14916801d5a442154818990850500c03900050101000082042c0d000724082c002d070340c9517440304202c60301c100b500c0c2211002a0070f00301410441c4000700190444000019502a401c1501c410341450105100524032031030003a10801c0c0c00c020a2686851100400381c0021981c4000e0048500e4151810709030f80c109a00a80021400002d10383d900b449007002e1a0411141d000200d5501c20b00d80014003901c1d803c0e04191455982c40444404000d8103100342114003002c0400fa50403e07203e5203400c40c94404501c80d130080340700450801d81d100c40c030410840d80200c1c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 533102275 1250 533101025 533101033
    0x1b01021c0911060301350c100507051002250b06210d0f0206011a040302010804081209030a12050f040605090304030f060f11120a0e0109211b050d051605 67
    0x34405501880321444520b501200e524031183c030100300c0802c01c001d01c1c184003410050917100f40702c50900423942c1841c1240301c2040340501030140080e906101241019544080260300d413812141c10850032032183c20b248842c0c0704a00c1d0b07010005080b107490168003042c200c4002da0782c2c01100c04012101120b10b40c1c0410180100402c442646402c240e0440300a425903086520907030b00c1e00040d8005064105035260010780c00d006c100019881820050740c4103100f024030350304008052240c0314090741c0030380c2c0390031294001240360510b00381c0c048202d10300354110500912a03400c0008026070a40c03000b900203405a5150000079a04510800441d00210b512004144e1103d4003801c05100500c7d00c240801009800c002441000c40404400e423806090743e141070704d01989401140500510201240c01c541e07540b41c100d030310046040c02e0040394505c40d010321110fa000702a040e0040c9460b509810803000200300401d150701040000803c80c040880c0d5040c521768038180c80490541ea0703420a60014050300c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 533103525 1250 533102275 533102279
    0x20a0e01032007081e1c15031b1502010213090f23010e0705091c020f0a0303051b2406031f0e01051b07061a06040b1b01021c0911060301 60
    0x50900804a80d51910b050742904040035010034840d04c91500b1103800c00c1d0a002184980c95040d6000c100e865119010300d18045a40f27540703070146d801d090310407844001000c5004000074140c01540d855520203034402180350500209203111485501e000fa00c1c1610b45c2e654000740d18200980c001d074100c00e4004d50544426880b102c01c020154024000d251059494a002c25081c9000340284d4980c01c4000f4003d041d0203441000322400c1508811090b0b0f8400d61090014500392660342c28607001d14000d6960030b07510f0280b000780c0030801002c88001c0f05246e00500400f0341e21b00c0c080e002c1e59000c0c5880719102400782ca54000007460083c80b02002440009001560180b07241d490340840755140e5035400901c1581c2d030380f4103802d200c0b80c04240c410020410801c502c10014000703a0025006105403020b182082200314049401fa40064000741424800010130000e90051048107045082a85000f035244c8040c0f051400c050b111040480c3c0251038131102103404220105d0040b000f00d4401030103550300c0390303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 533104775 1250 533103525 533103533
    0x30309060403020715140903340e13030c17040b041518170f1027020d060b0d02030a0302010c030606170c0309030d1401140103020a0e01032007 63
    0x280c0291400c6000d440b854900045212080301201442d14041c1c0b42c0b203007242a201008006a441020743d5035040c05440b45103e02c00c082c05440482c05015200d03056184100d00c0c02488200c1e169802c100c08001d1501c00300001c03042c2200601d902d842c0d041c54480324900451034054424010340c07002d201c050740041008160011501c0140c4100d0b4010043e05c851104208004c0d101c1c82c284904212070700d200f440c2d051100c940c02d00c5140c3c2a82c811501101c119a06904100d03040c02041c0582000454445243e99189a10494000d00d11050602540880c050641c001740c4900406500104201d40740c11155085554040d0b040307402c180c01506540005100d482c0c001c1c024104912030001092030500b01094991144640003c9001e50101c00d0500b911098017140b0207400007490503845210811aa00490103540140000d040d408170700380b411941080070980442c0c003408440fa0401d40b05010900c0e816612100c0e40144100a0030000340d5808105210070080c40e022044509030341740003c04030108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 533106025 1250 533104775 533104783
    0x2011b0b070801060f360b070c060516030309030e060c0a14010b0a17070b070f03022416180605031f05010807030203130b0f0f07030b03072105030309 66
    0x1614682e6a2000980c0c84000aa602c0c0705a50103500004005c291004c0c04420040c1c62400860031400c01640404c450640000e0012003e80140b0810440440c1c0300082040c04c4c96040f010742290304040381000c18950014500c0c81100d04007030100340d243c588000901d230103a03046888030311026000d40c4d5248000003480d6030318481c0160031a841c5920106865074050180300d4410b4810000300a84e007090b00d00726401854044800481c666405000000545860441e0040c0701c1c180c41107401c842144150704029082c2030010864200800040502c00240d65a90040070781c0551401d5036000c05a9246100700d6000b02809804003158000400c0800c51a401c040510b03c01c408402c0311a80402142c8502e00c0201c101c0d118050116003024013080a06009802440d402100d5540c420241c28898880a0035000c080c0d40c454140c0c5458410f11034400c1ca24a01140e015107542400d0083c18182c0010960341c40062203660540003d20b4801440d440d4072104040480d0381080c1165164100b0b0f044850311 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 533107275 1250 533106025 533106031
    0x10030b1305072c10120c14010c021507240603060b03030c0303010e15060a0302030f1b0f0a030b0a060e01120c05030f0a02070b0403230f1602011b0b 65
    0x75403103a07040002e0440241c41c160b1200540c10700c3c0209024003070440c5808000400b5245503000f2807081008034040386003641c0640c446008042408282e482c0c8180c81d5801503041d9000303030400c600d010801000d40c507040025401078040340140c03550f822460900002c03154200c144840e005070400c01042d04140607400030340541e8002c01c03007003003142c001c0000c040e40c0c1e2048902c010741c0d5800510040110445081040c0d500c01014541c1c149882c0c0a8030009026500c02d00343e105c00310b503001c8180403540c20102a03080c0d0149484d0b924201600542c06490703410f0044210329403040e000003d000c1540d9110750007010790050060010200b0f039445440240600c003000a0140c000307980b003d000e0100c40d8060180c2c12031a81140c86940c030f903031590700c4015040320000301b1703504009408210071000101200ca140c2c1c8154041c3d0346501a0f1660041c40c10100f090000300100d4074501403108003100d040882c100c80940100116071008680540f0050350400d0035200d020740d00000e047c2440e0b0074004ae00900d01d00c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 533108525 1250 533107275 533107283
    0xc160b1804020408060c03130b0a271502030c0d0911040b0d080403020f2e030501140f1309050a0305030a0f0e0a2613050a0902040510050310030b13 65
    0x180c50a4000500089004030711880c0b4407540301001040b03106d200f000046412011502c0640d20541c0c030303521500740310305040d50141031781c55171180d01d8038422140000ba00c1110001c1c210902842405494210462481500c0d5011079940000810702c03641101341140e080c405804814041e807441d50034207903d091080d44055000d0350602d01000b80d1441c0c501c0019080030761041420741030600b50303002e0103005000300044a402402d140c88800181034000c0700089170210721007900e851444003400c014103445c6c041c1c0c0400607001000001103ea9038a6036a042d4007450141c03082c01610a04840f014003070411644054254040c013401201416403140c0194400c15200c2d04c18000b82c584c6005510481d030b1440410b98090300040c1606e40000c01c0d04c202074605a107031000040b51310301011a064443da004044441400c84c0489c3c2c00c01c0a0f041c10346049009050b44181141802d20341408940c02e001c8000c41402080780000000c0d4000710030280c683c000d150010751079040c91904202e440503004001d20151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 533109775 1250 533108525 533108557
    0x730060801050708011a0405060d05070e0a05010f121d28120305150301020a020a020a080307080301050d061e0222030c06110a020907090e07020706050f0c160b 70
    0x814040014040d40f4003540710380d0f903003064603032900506222075103a488080c4501982040000f0300743e074404000c3e240b00340701000d0008450503c1c4901038540004050290f000d00e41041080110380c2e08000302824224003400e115142c462208514001007078072442521200040b910306034004580007883e9244006500001103000104080c03003c0703111a03090340141000b40c186071001d0035074030a42006801200b009420030480000000190982e00540030220041c0d2203142c01c0b50961501070100f00c0184090310203149081980d07194101e4502c41401154000c18403104018100140c03981b02140c0020074241c0102c2d5450310242100107580811b00100c25001d1f441100045034912400200c100c0398080200680745142540540c0c42544185c0b143c2400d0054091120141c1c5a2496152081d40c2507541c80001c103041517035003c440340d40a4409000c56002c0c02d0207001507600041114500010448045e0700c4040c04c0381410315042c03000410b0700c8d00740044803000840307400b0f060140c48200f4a45e4020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 533111025 1250 533109775 533109779
    0x1509120a0b1828150516030c03090519030908010501080105061315050121050c07051e0a03080604020403060c02010f0e03070b06240708090907030c0f08073006 70
    0x10b01d0340c450114407881c038140c100724800c503220149070304040411849000004410390524480104480341214841800400c00c07011518040c0c1c10311806502c0c9000d03003420440010b864442ca55540a0164170006160001761840d0034180120341c07a070000d0501a000b401a50303103410f840c0e4060002600e9a9000381a0340c410341d02c0012040c0242140b84d020300c0b8800e50064a04401106d845003c1581500422014800b541560b0034500565204001010700c1ca0354401321454000c1c60040c0c56214149481410355015810101c04101803481a40501d400c40480d150800014002c6c451039100505061400401c1c40101e90190800c00381007042a404100c060310361640349031070b88241007004004429500020b17155140c0760312100c0704120240308490700542d0410200e2050360001100792012407000c02e20300481d01d045002c050780700c4050700d420700ca404410b10002c0c0200202c580c48000340124040001c5a0b070784650080d036684445c141164450302c1a400d0402010303030000c800400900e0502c400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 533112275 1250 533111025 533111071
    0xf010608011508030a0327060603020f01090503060a0e011b02060f09060903040e0c070c0305072306040306020901111606021014071206082e050103021509120a0b 71
    0x4400d08036006040994681141040106c000780b40320403038a42090300f1030070010b280d4003982c2d81410402e403080c07200048407811070040006a03488004402e04010a5070003e0040d501c02040c182d8100c5001e05011511102071144240541103d8072928030107001d000070750b0302081c0d00180ca2801000c950510761115100d0f400d41a480d10070403180c1c07250583c0f08010402c0216068109a41d0102c1070000703da04008440c0e030341c000c0d6000b1a50094445901400060103440072200c191100f0416041101e06c051a0003000701c0d00a01403440041c0403a40d01013910522a4050445d911080c1605019541d418004400440d10074205002d208010310558034500001c0546124150110b901058071380965034505d40304680d40600041c0c107018444d160100041c02c91010400301c00a10080d41218520700c1101c82030144183c179980d20215441d05050042002d42c90f04030714401d80c05419201036a075142c0301000301300383d00c402d6150110580302d07098002c014000c0410415003e83c0c0c40d007418090340c0d405606c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 533113525 1250 533112275 533112311
    0x312020f210709060e0f09070f0f0e010813060e0109032003031005190b03010f0302010f0509090a110c06090c0118150c11060703030b040501050a0303050f0a050c0f01060801 76
    0x9042c40400d103591414811507000720843d010056008003115101c0c8180f801052004006a031741c4030108422180c0201a40e421030310748108040545004403002c1101000205644000781600c02c000302d51392003000a02060340c21003040519694000c0c42504401d2400412905440309110301c40784846a000480b440f0110440340582d8000e140284081d06050070800d0f5009440c0d800c040036182c10f580000c80300700540c0603500a06030003440c942c445203140009410800ca4181c020204441008071100b03a07583c034101e65403c6200d8100000c0d41030301c40394040406101c0c610200c042c910580080000a900010328a142c22900ba071701e250801d018003800f80d40c00803284c0100c2d142c0c0c1c0310306271740010083d100c0c46010704498052445440d85501d80c4020139540e5100e1642940081e481d00c400c0d00c100c1c1018003541d0300402d8140c0d0088803283c9984c4008190380144d03401e1550400000582420703151080c0d040c0c580480c43c100907602000030480c031040c001c0c0030b18803481006500f0700c40480e000551400e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 533114775 1250 533113525 533113531
    0x19090b07081e1b12150a050901060522050a0f030c0e16030506040207020901150f0207141207081e0c0d080d0506220c02011107020d0f0312020f21 64
    0x3003009142a02c41030700201c15030110024540f96080244000d90080d009403003010700881e42c001c03420100154001c1401500e888542003280604c444000401001c0d50081c2140c004084036061a40b00900f49055504081284e5114070340c0305800800200350b0301c6009103100120307441104140300555a4600340030507031408848228004410b4103182d440280130750010307640414010001031070520a42d0006101d00c00a03040591407684000c2d444000319004100c04075000d00364001440e509207011b86422850b04880c1140740124010120644544010030100c3d0241c042d80c2d0954151030200300c180d045d921940300e0715018034450b900941c1c940b424401c4120b019650041c0300c07186440900185500546000381c0415007090b07109004ca050b602d4000d0383c1401c4a00c07850000310741c86401c4c800003829245440f4005120354010070076040182d88010b02c0c0c40702664000310401ca08039040c101940d0f40e0300c100c01d182d402c150000500e80e20324a005002485000042c0c9042031150580b04180310442c8411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 533116025 1250 533114775 533114821
    0xb0d0b011107063006150f020a020307060e06040902402612031905131209090216020907030c2c030a06050603011b020607050319090b0708 61
    0x103c80c41e03134080c0300c41512114184800380c50490101648010b06003c03101280d10103450500003803412000c0b260700a141408103849172008000103665900000d86901d41ca201c1c19003802100c074200320140d107540b81942c00a08444030301311b4441200b00c0c0400c05141c1054510700304c0744421062540d0585000d9802803000103a40c0152002c2c0b8100005811001034640f9011307401c10044015808240342003100d100f181d6440d0480d02d8490a05400c05044280300c179000c00000750038032081100320004ca410805101790861009000e4429080c420f840d820700a80080c421603000003505111364016070741c000d004510136142d0710740555540000304c0c11900d50825040014201a9100c00800541c072442d20141819242e50341014403034400291800303100c0081107607460344420810005180a200780b00002d03184601080c440050034400030b464001c01403100c002e1000c003101282410403884c507110021040c89030100070307400c90784c10003100e819001c480440000700880009802c554031011042101c1c510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 533117275 1250 533116025 533116037
    0xc01080604141e060d1e02040207120e120111030f04030302040806100305101118060408010f0501030218010302010c0f03260f010f1401051e07080309151303180b0d0b01110706 77
    0x31b11020300d40905031003d01a40c0c015000d00080000c20300640c100f10303141c4100d4651015002c0c0410070b00103640c0c14602d00c40d0403645049603002c1040703d050101c03580700401034040003140e580c51806800038010364015040c0b6105080800007c02501c600040c2078074090790031168603e42c4a00c11100f500c94800d4280c0703241c44203005416041441c28903a9421030030060802e400e050b1140802c41c2121042c00100b0340c220340b01d0340100b05500340055020046d05000d16070040c19811a000600540c85c1540003c2c1562103401e0308806140c41103c8200c1c400c0740c0b0042e100c1c260300c02c94406d400300c900191520502120700342c0000400542035070404013203c0582d4480c50440200c00c0055440b9005500005601582c0307442c102e4440280d0b41c014040d4610400e881c0d5203904110821900c3c08490301008206810000184001180b94446001c05a90f151405a4513031401e0003084085c80b0b4103500140e100003000c110380074680041e03006289544c0302a80c038a026112035880035591014a803094002183c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 533118525 1250 533117275 533117303
    0xd030e010605211c02010c09090c0c020915040f0e0d08040221070f1502070801140a09020d0b040b150a0b0f09032b0806120c01080604141e060d 63
    0x302c0ba034143d815012403061328003a40740c0f048010844000c80d4403060060f5528000c0041441d0490060740241c81489005c001d1241c2c5203c001d0005c02500f00e020b40b15081d4400051481c844403000181ca000c3e02030401d103c09403604410b40d001c1c14404440d19810301402d200d00917007d200d04070940c031907500101032809810261210041801c101108075030f0f0741c090010040340340e11448401000030140603103040c424140c0031000a090404a810240040c0d0412046144164a810f04030744c02c500201000110800e0920000319445410040100418060420001842072070a8400d11031094040520407081446042103110045400340b426100814440d50007450240406000c4644000d0111507041f074150310300003920a84054170300101584000076007240f030340c07207220203401c040c05031000844000140c1d0700303036162501101c280d03040006040019807031380d40303540100c031062010092141c150708158101400342c03080d00e4200c0190440060202c0c0b100d003086880b41180ea03401c514400c501c1c0e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 533119775 1250 533118525 533118559
    0x306020d020c0106030b06191406090a052e0504030302060a0f06030f1b0605070206070230160806040507030b0702070504060902030912090102030a032301080d030e010605 75
    0x1400c114000480c480d801c0c081551401024480c90307002e075006140b0706030103240000801400b101e507255010801818504104000ca400c01c240700b13204c40045034460b13194101c5e80007040d6055078960100e80c1c0640742407800300355075541122142e4800c5481d5040e4080d480e0340d4034103403031500ca58400200140d00c003200207548012290301c400e45620500402080c556900c2d102c0c20300385540e04a00360340f1080502904e030b410aa0348107400c80209024100a03041c918070b0f1300001c41500440e40040d000710a050017034481c0e00c0c0380c1d180c180105805080d03e06050861002040d584170300a070b00d8403503007104030030010400f090001a680c2c8910703070103001000c2c15030541c0d44415035010046d001d40c09511403080c0200f01a81d603402802c016000030000103840b4988808028981040f895940320302c21810003410f59035907030100845404802a042c08149080e00c7c410180c03000b0350407031010200107100e0002180e60315010401c0d0803008000d680a00004102581c2d5500f201d00301d1007034540c003900d02c140b41c0840f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 533121025 1250 533119775 533119777
    0x1a0d1815051023030312070e1816020709020a020c27130515130201021c0203270a120b220b06060d050a230f0106030b061909030b0606070b01030602 65
    0x18141104411a0f1984a000481c0c619000b00c2d26414001c14907200b08201c0b541e020746843c181e107800f1144c0d20503140910041c10b940400c00381902d18208030304030440881034000c004044c010203141c4800c40d82e500c4200c100079211b403d00401d051180c42101601000301c0c0c03818000842c1240c030481c0340c841e241c0ba1070b1080300d203100400004503000c0c05070a1040e00c030b4244a502c001c2c400e291514484514407020b10009041c49080c0aa80140791443c020401e5080c6e03001003030b102c006c1d0940d4504cc420700407071103012003000c0e45000220ba20920313151022409412806200d12000d02c10300080f1081c1d200c1c0d1681c24016068040d50f610012300c031010f00c8003c50340224105802c0342c0c024110034a070051100656003601e070111003414900d5219107843e41c1451041c13451a0000980c0740200c3c0007410003110210b000e10f018072480003010348a882460316655454101c03551030300004804060f4444010018165115512003038842010120004149040440444414a80c001800c205980c2903581d40402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 533122275 1250 533121025 533121059
    0x80f01091509020a0509040f020309060c0904060b07060c0f11031909030f060507020705060901080109090804170c010f0c020d0609170705010f0f020705071a0d18150510 74
    0x10807000c036500001c040e80741d403000f042008103a5070380c999600ca044052005072080b20002e1700c00d540c4100100500c0c0302021528640090343c28180b01d50341c01944000501034400f41d0040c4441e80000038407281005480d9000c4002c8801944485a0114500300d0035180d008541101c40002d4104010800c26020200140c204c03203281805c0040007903881c0e880d02c0d1411000b105c02112210341d10414020102d1301000400001c01c012920071f8504280000000c1403210113100b04020603486000400811001d075050760050020b03102c140b4560703041d044c46999a105070501d0135011412088580500034031a51140011540150000300d404080d59562401403010090075180745000441072038030780e0040f80003840703147e00a00000c40d5040c030b8166941c1c1210412038269180500c1040b80d0b0000401c089104011a083e058007003000703d070070b140c0120a5104e0490a040014600451700840d180b04440b84c00d002405500107030701c2010010384440440e03c0944504c4c900c401e0b43c01081001e443c0001c00021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 533123525 1250 533122275 533122301
    0x603160f03152a080105060f1803031b0a060c020604031d0a03150b13150621140403080603010606270305010510031e08090f060c0d020715080f0109 65
    0x40c600002c4401440c45904050928550b0341c0010b14605142d502210850140c1b03c1111160300d80400d50080c034001d0700c030b1102c411380240c0b15845030381c0951b078082c01598060300c203c41e8041801304403001c040d619810040401c0351314a103005841001a03200103151407246501d42c9800c1120030700703450607030003001400c0a00707179000800b0180403000841100c6117201c0720000030f0011030000100da040001c000001c20b003440200b0301d000f10340c1040407401c0e680201111014241800d262860100c0280c03902032038031103107500300e08015039444032040f0b40403550b1040e8000d03900c14541d03488950802d400d8076403511a2900042407002e00f0804a2021803408074104008011007003038503036a42d0b60078203440049400412000304c0c0a000c10030b001441c0708200d142455103102400348040365803003003503a01661001d00d015000318619003020b615030404852640c039640d0112458000750340700081d41c034549802400315a114183e410f0144038000d407176050150380d44a007030416680c240f41c0d00c04014652018204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 533124775 1250 533123525 533123531
    0x2041a090f1201021c09050d0c0c031a040210020a0b0115170c04050a0b0f04030b180609010f0b03010c020601050f0402040f06050c0c060304020120011509050603160f0315 75
    0x710540e440d42100c2080461000c00581c440074648001c2000c03a60354010944000d0501505800180f00802c1c0700d5140d031000e00f03246100e64001c7c10621440000b940000f403440c00c40401201c445e1310358180d064802c92003124841c6040010130012603d410000d0402400e074400784005100101c26005420503c00c200d1801c5050b0031468905084001002e071103076030058500140501c170900b0301c00701c8040540401c403c142d14042180345070001c01e210300d20010f80b10462a001181c107606103001090b03155400581101e40d0b03418800b020350700174000e040304041018a840c1da51041400c3c1070141c0010b42c16160003900207070b0301c1d00040c48400c5003c0c0f011164026820400807580e400750141d20406042c1d0f6070384260303d80b14001d040b00e1400496000062242a0034010440140c0c1d00c126441d41e924050701116002c00c0782c07980c166014051520300b50402c1c041000d03010862101e035a02c964070510080f4211042d07500014003001041d07055003c1c80310015600c580c14400700d4000540c069049812042c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 533126025 1250 533124775 533124799
    0x18101415060739030b13230a020d11090a2003060d020301020c0d0e0d080f07020d050f010b1e030d1d191e08100f02040b03041b080102041a09 62
    0xb800d054002038070076140d0380f014052050101c0c0c070500c41da100110000711030754080d041d19411a2440c50091010845c0840c0303000c181c2d500700c14000305003903c0d400341010780208800e00d40b98040344600f06416000e80840c1d40040c0d118845400b80440c1210807499903081520b203006503a43c650b03c0200495006101180e4200041c0c4003480102071040d6000040c201080414200610745001111414803030b00b00510320201246a2404a5003200d81d1301c00000d035103130000c0c030100d101e40c006058060014010742c01c0d070a83d03403c0c041d0403081210204440180c440d04c81c4140f40d120a0511030981c82d0940d0200e0a084826401a8080f0070300174401251046030403001c40002d401c030018109205403040300a0310402140400c034410301d403160985000140c0240c10407401c0340e9600d4155841c0808541c40b000c00784068001d80e8110b90141c4040c489041d96032900781408a407503040211010300801b40c0103000162104107109603804c0d64101c803030a500714800c2c601c02c941c0c3e6801481c41e050b4810011084 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 533127275 1250 533126025 533126093
    0x4020a0501050d06170304030c080a030801050405130210030c021912080709030615140d2012100c110303011a0d0b040f0b0907020a0812181014150607 66
    0x1005d15a0301040000c40e600e90031403610700707810506c82d400001c1607480404a180001d070000ca07001d05454003594001081e40d541070f081f0f507540300304080c007030340101c0301c2e0b03174104030a0390b06401c241c91041c4d030380d000ca0f000303510791310b420940142818401505285940d404030500c64071070380c1410340100c12850580708454036611030a04071018818032a41e8a6446501044008200019072490342000c540d5040000c000f5141c0180d0403c41a245140c580421441d101059517a40c5618500003010000c41e0980c003104400b170001001c9410162020075404c852400208500004481c140c0392494000801e00354000030307188217904483d410820742511307486000070684442c82403ca02e5405000086020300f40ca406110a0000203400c40d0b045401c0b036100000821039520407100b0340cbc030001d0000d15003540c0d1600055010396000c545401107000340d04100c00140525007002402200ca8116440d4648070542e40811130b40500050540107001840440081545450080c0b914a4484400403031a101e80c1d070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 533128525 1250 533127275 533127299
    0x4150b0a0b041404060e0411041d1f09030f030506010903061415090105061b0102070c0f1e05100f02071e031a06060f0a0e1302040303031404020a0501050d06 69
    0x41149540003082c1002102c00c8030030301200750349081d201040480d0030048110300c8000300400107004008001d001018503101e9603c09501100109801a1000d250510040e01d074442c0d081140c02819129180704003421141c880d4603840369041d00c1d8420b45404403102907014000080c0723034505100600700c00102044480c042ca0305891100180c0203614503101d440107007220300281c0d4990007901040014425500d4800440e4010070b42810041c070000c2201c000c1c14060300c150303040248104001034001480c22010400042502d01c2c02c500b0418a0504ca004100001a00d1050941c002d1021154610081c042d41940c409a40b00f0310545100340c0d00c4808241c600c2610032012942040b8a05003082880b0020039a0f901107007130501e540c42c543c05c0c072a000a0f982e0054603403d41406000090a04009000c0e50b65140003000150040f140c80141c1d40a900080d0042e11095001c00d0130030103001c0359902c0804407580300e142d0003460380c14242c3c1041c0c011030700c0390071035060340d444580d48410200d20311440075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 533129775 1250 533128525 533128529
    0x40509180d0305090d020a0201050a05161406010527011214010509030a031118011b060e0a021e0102070b181c03020c01050301030c0902160b1602010c0e0904150b0a 72
    0xc0c07004125810006070041c54105e04c0300c0f1007821900080641c0c1c2c0140c0e4000100e0750007815600d0010703200c1d40404100d0528110f40a0b000b820400620300c00c008404001c20030714105c40741150200558038112141ca10005040440e280146a101c001407084010300b080200416000d0a031242c0200840140035007100d4003503070401c000b5070010403803940044d85800380d203100004894000d0f04104d0010304201d032000f0038015040c10b004207041030342500c40310b0340d07103d80303c20381c10140501141504880c030035110550290700740d0048041400703d0420080c0c0b0b400f160b0007270806900a04d02e140c90404205030540003a0000740d5420107610a145880d540d4120202512559488006008015150182c504810740d090641800803e200410218070220780710422120401c1c00942c0c0d4030315440c1a0303503d942c42400700800301d1500805000a0303603d01d10400b941186c0c40c0e002001151400f0606840300b040101140340d109100c500003a0003d00e02c0e06800d43c00b0081500f000c22111001d0300012403459042d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 533131025 1250 533129775 533129777
    0x204020304170714070f0305190203031204030804020f120a030c03020c03070303080105091f0b130b07080d0501051e06070c080d0503071e090b030603070e0a0617030c03040509180d 79
    0x1900031301120080030304c4440f0080404c032462107621031950b80ca55440707080b2428999032141c80c29a40500355142070042ba0710450b14180300b5082840c2c10301d0007901204040da41a4001c00e8840b00041ca9410200d000e001c2441402c4000c1c4a0b046035590201d4000488040071011809030000c17041c1962820452500514840d888800d015030402040c003030724000050120110199600c8054484038110800c40150390444464075512403208411103540725031507116820f034080010b0403405000101c000740480e07000006080c045645e0750802c000031824030081820007000092207141e01d51404000400d85144642c24044209a032958107606085070192000d000c10000420421182e07845010613003c0d41c100e40c8801d50704e40c2d02c00801010050309026040842c42c0004c046100c0e5603040045a0040000484012061170582254805000c13030b40b04605201c80710b0b035070180c0201404000c0e200c28041140045007403034a000c08000200c0000b0b802c605580fa003041c24902c00c00414803a009074400300e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 533132275 1250 533131025 533131043
    0x150e0a170105061c080a0903080d05010315051605090d0c0b22181d060c090a05091308130e07020a1a0f011a04210b06060304050a02040203041707 64
    0x26128080d420740c2c100030041c41c0b0400e40c101c0301034060341203400e01140c12034003c900b0940f100310505c4144d17103521403070704081c001e004045004520003180303810060580e0320a6402001d1303229026550001e0f1503007580c040004842c5042e00d103152a01c00ca02038a940400103115a405081c6500d80000c500c00d04c0c0c001801c10500004c0404442c08138040649544025000d068038840c500f01041c52165a02c500e0990301c1521810104c90407514000c0700c1c900ca052603000d540c0c0310b0070000304e4080503a12182140780540d0241c4000250ba140402c8220b1040c0d0f410342c00c8500110865488002c1e642c0080b032140609500150082034054884c154a031182407a40c005120004060601d040082c1d40c1d000c0403242400440c003008030111480503014119004035084920080740071076081010b0250381c0009084d83c0301c880c141851900c0490840440d42d004944448207501c2e1101400a00d1000700c401408541c0620000c00c010704155008680c01401b40040c0381c002c81c0d410492501c1d5600c090800e030741d0211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 533133525 1250 533132275 533132309
    0x4020c12030903090909030c030d0b040603060c02150108151302040e03040f21050c01030f0b1203031608090318030a080c0102280c020d08280e030d0801150e0a 70
    0x203264000b644c101b941c0318011418441280100c50792440740c0d4820560440e00c0d000c080700d0075216a0451005168044424400d02c6c145050003592050480d01c1802462200320002504003000300d400d1260100301304020b011603840c10340a4050b4410a082280c000f503449620400e901c4041c8081d2001c0d043d4403501c041100d291010305046d032016100c041d040c84a6810b043c1000450000e00416660070030b00b404119940c4201c0c401001300024130690790004600c2e82401010100440214821802031010090105043c0011204038104458460702a4801c000a040320240c01da86402c0044004048441400750742c0d4911001d50080426070020b03179008510100380c503040c4402160411900d0008110104005000400b80780301c484000e40038030718030365810051011400c01c949605c050032081c0003000c41c000c4241c01d140100d546000000030303041da107000c0161a01040c58022400507503038000d526400c0103804054949000e40d01d00c01c0c40010114400c0c07035150071001d4401468a6843c440c0b2003c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 533134775 1250 533133525 533133529
    0x41e06030b0103020a050d0504050f2d0705101101020f04060302270f100e041505030609030712030c020c03121909030c0608040f0b04061b180504020c1203090309 71
    0x400010728541454014482c11842662040944441e10316400c0c0c00300d095122420b105040000070041041540111200315500c65071900364a03070340569a203008a80200e2014143e41c0700d007168050326500044200021243c0c510688000044481c1d610006207804000b1000800591080e4000c0020a4001c12003c0f80c20000c001c032034402003201040d03042042c01880c0000c0a9071a40f046d000e10455501d0240250a48555502d0501c0034000e8410041040c1c0d1014440a0b02424441d06101c1c1c41582c0000781091404015240780c0390740100989486041600164080c0240000900c118415514140b00a540801003100c480302c1c0c01a00b180d0380c811003148074003520b4160822030103004500c41c2c1000080d20b11401c40080b100c00b03180a400701d45480c60101a04101910f000c0c0c038841c0d20509000601c00140e1020b1107040d804070313004003e10842ca5083e50032a90007006400414000e80040210f8180f54005011a0220009a8044494188004c002ca030070680341540540e01c0854514054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 533136025 1250 533134775 533134781
    0x3040f0e06063711210d330b030402010e0d1a041407080c040917030901020a020c040b030d0f0221030901061a07060c090f1508061c0314041e0603 64
    0x121505242c000c184c5501c00e581c40e0750b120700340c101c1c41c0b00300482d844e4441c40c0110711710113403890104210701c1417000d85490b44051b10003814a48820050300e000e00c2581f0000c19070004004112030607000e10b541156a540c0043d11800d62811345103410450400213203002401c1d80d00d07451004140c496411009003020b0400c1d8001480445c0e104a0707991003e40300f448105000101401480000c1b100480c0d20161441e2100c4d5110941d80000e200d4035003c42401364039441034002c2d000c00c054942c00c6036a030400300c0341003005450600b00042e1301500507000000c1c0b103611502d941c110341010b83c0126441c90092a2000d41c81400728140c2544201010040c020391041c203010311002003070354204908151044250341c108920403503800400c4c0c1ea40d04c2400480030342c040c2081c3ca004041d07094a2402c4540c1e50780202011240c0e03403c81c680094102d000040d0685030140c0b0340500c901c1c20461141440f10300340e4040c1d440008615903054900340a20000070420301ca0b821026000f25411001c0d01c07000c1ca06500a001c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 533137275 1250 533136025 533136127
    0x906053a0f05060f0915060f250f020616050d02030703091415030a0f02040b0301030203010b04050c0313050a020604090b090f0c09130e0f0c0f0303040f0e0606 70
    0x41d28102030900005564601e1084d0b1050b20882da41440e9031142440c0743c80e021032408919401c40d201003545050100e140025107c6001a0000c1c0740d40d0071945012086140c595680040c02001030b00740810241c00d14201620b260b60040146e0300c50000e50b500c07054584450041c0b00f00c0181d10000300d080400d035000030000000e0010b043d104255107900c40000e11002e6528040080d4400048002032112849822403900044d031140210f5a964681202ca08250f000340000e0f4020360078084000c28504044c40340b580b081ca043c407035490440d12003c600f850328140e0814182c510b407055122250169a801e00100014a04288001102040c210511000f2600105100c1c2074101e050300704100b0146000889881d1070741107c00741840d100350205a001040b02c44490381c000d1151182000b41c4503000142048c0d1444100e45150305540c80f202013640e24842ca000d0154070311402101000149881c01d04143c115100403c0c050405001214108581080b0130120040e40ca0340c0030104001016407230b4081e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 533138525 1250 533137275 533137301
    0xe0105090d060e16050d03030b19031209060c1110050d0f0501170321040309080a050f0c031605040203041a2a0304022817060105130504030906053a 65
    0x144e51301c1d040000d400d142c40e510020703003415240d20341204169602d019981c0820b502e005c025081948a09080003690400c407110301c0401d02e88070300414002d000c0e104081503641d1041d0000d184c48a09030500c00342088148143c0140301d0240040e00e01c4400318041e410095002010004803503140014040080300c4d0850703800041d4004104c2c40b0081d12500b081250030741515811081144c9071441c0446000c959580518a180034180d41003040003000320304007100084140842d003008000100300340d16180c6965522540a60007201000a402c154000d158094081c4c0c0c8021140c4500200d4510b03094000c556580c41208040d0345180103800005041602e55a0307080070609500c1c0aa0100300d10166000711a46008424150000910440402480906103440761002c6a0502c403007400e40d41c98007802500e208001000342d080200c0c505c1d100719840350340c25547d070410f5149007040c00d40b1150b218410001c00c0e41c50703e544007072800d89001924401c85d0040e80b80620081394070543e0f07104803900020503039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 533139775 1250 533138525 533138563
    0x2041205240c070c150806010e030c010f030515190e0f040b040f0f080c0d08060603040519050309040606051812060a11040503010507090602100216030e0105090d060e 73
    0x940028040c505581c0c400c0b0084101643c5040905102d000c0401560001c1255003640c5c400d24017840c0e1068890380242c0003030320b504400c0d0102c80109920f0310243c018250004540820100346948213800c050b0304400891482c403c403d4403640840c098080340c5002103040007914404001000000498603484520440e60800d02e0402d50b42d0032a0290380904094a002c0c2c01c4502d21090180340c5800d10840c55000103800d50f5152042c00c404d0300d410391140c20034081034414001440900700001260b200715807040c090003041a440044042d03024608030300740c1d110310080c441200e580d141c61240ca40980210b44455468101600301700d2b041e2052103405901a07001554002d030800400201a500941e00490104030300e0500b1125030618055039000a90545c02c060034821041c0e000783c0c010081d95881c3d405c1d00d150080c4540303082d040c1e2260faa40c00b013180751001c0d42040445c1c03140c260042940b00525201c2c1ca402140400200303400c030030032820b03030300c15644020528550900700b00030444d01342092010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 533141025 1250 533139775 533139823
    0xb0d0b1f060906030507052701020c0402031905041b0b040f0501030e0a030f05070f060b0f240901030f1a0a060c02060d0f02040803030411100815210102041205 70
    0x509103115403048000313141c2c442c404500315078050010388140110300802071b80c101343c82c400304905140403000b030a030140c000c2600d0204241820b0084900c140c8071800c1d91300d44200441c03403c10040c140240140c80142c1d0103222910a1040d000c0c0e201c00500035150710a4603581800394410800c030060b80018180b44c80d112048203c0f41c07010452f54a41901420f01c2400d103803c0b4201650785210758417000f03150f47c000442d55010055242d2041c61100015103140306440e40600c1803025194079400200280405070150381c40d1f20013541e006155009043c5404a94009589840d0060351000c5452070070300740001d2015540c0f41450b1006400420303032450400807010007500070510f41e100d1020f03018440c586031170b008180c3e2607143d0100d50080103110b088070b540e0300e000d0401600c1400d000000301d100d00d501c0721603081c58034820900580564034944131291200c0301041001000481501e400c0c41c1c40344400c0c1146003008080c80544002e10800514281440c094a803131070611190002c2d0114105911104d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 533142275 1250 533141025 533141027
    0x30201050f060d0b100f09020c0d09080304150323090c1f03020c190f03110d0905090402030c04060b090a0e0106020613050c03030301030c08010f0c1b060b0d0b1f06 72
    0x21100d006070b0450304c0450749844020b00ca0224038000d03001b40c1013200c05040001982600e982c010880c192980059400c420b0301c03503004684035200b0344203030a203a82c002d000c03d1240d5660503d0709080c080702400d0002c0e00c8000411200c080da4628080c03400032207044d20400c8400802444807003c1602c00b250780340400c6410041d0780e04031004207040c0e401010303400320f4000710398082044540030941c904040320b85004918a0045005011410120000303010f809889610550000300c2c200d10700034039100c41000318105828072140000040c010380c1d142c41840300d44c03480341c0c85a01c5017002414001000640ea00035600c140900c500850f8400c00b5401980f50040040590108800c0e810002004400c00e40c00080c3c14900e2514450300011681070000000000c10000c414217002c0c00c40e00410028010b8003403100b004000c940c003440319803010a02c50b603005900c0e01142d0381800c024603c540c9000030f000010202081012100c0710007201c80410b04d00500c4100c668501d00340c0f220071501c2c00915525400c0041c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 533143525 1250 533142275 533142289
    0x31103070c02130504051c051e16060903050309010c05041d09100e030a091d0705090a0e150f0d08040303140c06340e0d0303020c06070507030201050f06 67
    0x3140c5420401c604108004640d600da00d0000c040b48040c500740800d0500303041c45038942e03c07110503000030a08182c0b084d0403024004c106413005c0180c0c3c4410000c41a1903600c03005407581c1305088040d800100f1b00018400604d092141104550013543c031243c0305d00d000040e990860380745401050070f010051204010405d80100803402403200200d1340c004644400d00b03450b203804400c1d41c154100c10304090890b900c9000010241840080d203a0f00e00321a150384040c5036400b00c2c0c80441010500d25002c0016507000c3c0240e00401e180000034100c070050a5403032041141200c1c05549440190209469000c15450020241c582e40202250b42e500e015850740e0304e0103035911841c40000e06102d0a840402c0401c240b207030941e1000004442524003038546440f031100d000342000c2d04072503c549007003070b0200c0240080c40324245421141c0c40c0c11320715581180401c824048040011801c164081003180c4544c134080c00542d0061240f525015110485071a0107829107000400e050900701c04441041540e5403601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 533144775 1250 533143525 533143531
    0x31812030501033e030c03030a0f1e0203090f01270e060402210a0f09050303091e0a140f071d0f07050901051e0a1d0901030c0302101b0605090d031103 66
    0x480c821507418074007404217045c500800c00e46d0b40d16000100d403a03880983c20030450440b940c6940e8843e01654088900d42003010f00070401000184d20500140383d16081c00b0180c801c1c40041410300266610a00c09086c006103c840c0b07090b13822203509407041201700c100c00071264100358100c80542c06e2290505010202d080d55a940c04401d40c0c4800105a60340302d2640166000c0e891040c0a005c8021a801c00b00c0c4d1325801070364208007070320844036201c1016403802e401c41281101d03840900010840394480c0c054940300c1c0707142e025950080890805808408000e000010a141d103421040d404a041e106040180300620300035070480b030001040304d4554448116003c004007402d05544821803903050150560b075005801020b40350010300c3d44071142e000780015100c803000c4064911075446000500c9881242888000c0850001c85004e0005161001400b8044030080c82d01c0b81100510040b088030030320b10507000b40c4240d640c072410b00042175014805000340700483d0070b0900c44044170400380c0180340300007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 533146025 1250 533144775 533144873
    0x1b0305010609060812040b070f0f0b040c0e09070509130503190c1a07050d020327010e0f0c0a12170a030f18020f040e030c010f020d0605030a0b040303181203050103 72
    0x1800389c0004002000c0300a0482941090004110345042c0c502002d442d401401450380c40c440420006c1c4283c84c0c00100d03081034078409000d2074015140c01542803101d919810049403140014040c1c203645840460040002e040070f56a00707a1940700a060044110381d580d142509003c030708408005d1411703045000c807050410110740050fa01c0c2e07500d000d04a8000d014175601c12500c2e1501c121020901d0054001c1a07c2c10301850640701c0704081d02d6004c0342c3e103034064410b5640184401c8000c00403007000c0464249201d015040c4001011038052040c0c406900116110001c0ba51368110082521305a00c03030a0f044d4060660010f090780120740009190080603041035210f192540b48034061080c0c2442a03d846d0b61032140240108082c00243c1c40203900110501c110741447c00e840042e442c9400035907200700ca40c00c1500619192540d450031070190100f028400c56080c00b10103890300051069a2001d41402c00d954000f03610350451070304640080c401d41102051603000000600d40444910702100d558020b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 533147275 1250 533146025 533146043
    0x1240501110d140408030705061f05010c02060901021c050c0d050301050f0d03090f0b0c100b06031f030b09030a080a0b010e01110c0612010f0617041b0305010609060812040b07 77
    0x85003802003e51146400c4141c40d800042698002c00c0742c0003030390600600d004035043c44154403c1c1c0d00740301c040900c0c4c45981c0c0003d0440f40d50b0405030412030010010104103106a85800c1c501203d403166041d8880550000120f0024120790170130010f00c83c008a804413032078414a5940340c01c0015207003800030b840013449403205001ca0b8040500500145005008045099032034a40d19010712019810000e87c0783c419010300c180e8440250810b110741078030068010074590454440c1c0360400060b00750305100010141c19454040045010641e400c1c0c801c1d400765000b5551000c046030300804115000c0c0510b12194107002c036081c1c0f96a003060007442c441c1420b11704010300c1e186e040c4440d4940000a10b642e80c10032400a0041d2030302098502143c180c445e20b8108003240d5980c0d20045411484480b21240d20301061408100040c040030340c074100b2451008040902240c41e070b1607007800c5403aaa0f0000b80b4960b5100c50410501ca824407200000143c107019950509240207034980107442002001003200607 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 533148525 1250 533147275 533147297
    0xf0c020907021509070503010b030d080f15060d020c010c020d020c10050d0905280201050405040e0114160306050307030c0b0c03071e230d110f01240501110d 69
    0x4400c00c202e0f0b40541003110408001e0500e00751072904c42d9200d0090900030750a0001d80c130500e00740021851807500c0d80d0381d071307844003503903500410214003c000c1c1201350301c04c988040044140c0d884d000544500907c4540069a41380c250840c0c6086a0301418001c00b55040050f06070845600030404180105080d503403095500798600f0125054400c40d04c41c03905c100d00e001e501c80240038001640c40c003102c2290440c40305c00f803003000214084080d2024020b0000d14204800d02c01800c00d07400c91042d0000850003c03035035000348205462862406c031210318401040301d0304481ca095050181800400e020307009801820304544a40d40003082d64002d40011b11000105130001d81e00410845030f1040d0800038050000b50860281c00603c0301c03001064424540412102c00b48011010505000c1c0c82040003c00c65100032040640d00305c100805103035580c0c042e07208030845110080c020701d040072818030000c00341110383d0007ca010b44490780d0401030402c40e0706001921821400070b08050381c0261800c09081c800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 533149775 1250 533148525 533148527
    0xa0b09010302070c080a0302120f031b0706020706090507092003100f0902040303020106090e100902010513080109060f02130303180b1803010e011505010c02150313060c0f0c020907 79
    0xc843d480d0700400d140420b0400060415004c15440e075440d01c65400c0d9030091032565003c3d82e5074021301c0100050080e04001290a03a00c81810000780b00c50b40c005d18504007203241c0ca071281280c01260050b10b109072102c50300d41c01c0100500158010f0001d2910802140c101e2522400c0e0480c00c84500441c1080c000001c941d001d1029003030310000b0310f9000848415a07442e200e10704040c3d00030307100c1200590300380a408910a4640e000d001c0b104002e010081c00700071150700c0080050012044d00f030341880820821507090b0240040382d44c000d0b014080020544480a00d0500211003502c0d8200031400d1052005900b1680605507220480750180342544d645501c10f80d401080c44600d40c40300c0d6000200040713080290300500386003104c0c0002100200b1400030404403003403e03100740640d803183d000c0d0540e100b80300e298002c1c2145400640064003c580c0607010420205103903109480b40c0c01c00c0034a04088000700016400b071009160030070b10317200148405024010f070511646510003445000c0e0680011411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 533151025 1250 533149775 533149777
    0x80d09091e0c0203120f0115030f0f0c050a0801080d0507081c050a09030305090708060c0d06051e1c05030a03090602090d0c1d01080c01110a051005240a0b09010302 72
    0x207000c03211000c001440d00d901c0081d50f0ba511007980f450682c0d201c040001e41ca403a0175480503049405049002500c10301c0306508a0007059503070701c0e040c0c0c42036451030f0480b40049107116801050505403165680c440034a2000b500d0441d0591180320359501c030798840704425a014080e12101d40e4061100b0f904ea00c0c0c1250280c9120402080284c00c041c03070042080301c0307101a5002080071600030380303081100307456280400340c58613072500a8141c03940c4200c02141c7d8103562900100320b2403103103440014007941c580780012a0311505540c00100c40c0300c00740001460b0702d44004400e1a24240c00500c007100c0311544d85e481e4907401070280290500d940c444010090140700e07012a09103080081100309901c0c51480c0411040002c0d01480310f011214500360b03100c0001c42d060a0341a6403001d001016141004401100d20200b061040c0303040e4004d101841001480400c002080c0600480b008185881c00301d80c0040141d4030700d004407152002041c000035581e104c81c0185010f48403c01c410a60b034504000041e000303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 533152275 1250 533151025 533151071
    0xf1b121207060b0907020a20030a0b0f01030615061b0204061d0f06010c030504090903050c0a050705030c0114030f04022103030a110c0607050d060b0a0810080d0909 72
    0x20080000e00404101e5aa4070084003104100c40d080c0c80345e155100300302e81d2014200e00041c6403880386040c4441d804442e141c00209408020b048800e411256610100300c8075081d1502c0b544800351200500030440203000300a4400c040750403450b4010728000e00200b90303a2414080003490703a00d14a0210a5407501c0e00118084d00c09000ca031460401060241c003106001161850400d280840c040b888540c440c1488140340b58040ea10141001c0c10001d07004001d0803030300012424484108445190080e003804104040307405503010741a6545480285070800040702001810403001061101d14520500c054030b811820710264005555070301c2c404a03545180074044140401240190400e0000f8000000e620441c0e0b070b07220074009020402e02000090181101099a03500580000341000303104102030403124428040c0441c00c3c3c1d030740d4258040c69511101150b00080ca036034080000f500240d501080c000c211040041c0341220303451100a025a1583c0918040240c0714140030085000003048000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 533153525 1250 533152275 533152303
    0x2030906040803070c080d091a09040e0a0314040303080103060e0a051207060f1401170114131a0c1e0906040e010e0f060d0f0203010f110c0f1b12 64
    0x26455072514807032030343c036001140121002482184e0124008a02068100b40d030152034136252a8282402c03c2460450814450010205000d00582c031251b40c41c0d000d20074a1003c500050804030705c440c21f00410791040303401d1a0301170348010042000025408001c407411603400150020798401f0a003a1503050450180d400390082c461560008001107560005085580c4590000c00c800070340700d800401a10081240381c00c9201590004200661001160b003100c0c5889400001d140c800b0508044001e10301a90302c42c410000c025181070810a4a1070801c5050641600e0440030b458440c1406219200e0201400004051544101d032052003203016a108004002e10803601d42303031120ba0307602003420300b4460034205902c00c802050020010741c8840d03001d902d000d05645070a07000340c1c8039a440241e002e58203e03003540d0380324a441c54080240c40307581034040001c1e24031541c641d90031000d40e28086c00610051169006520f500c0c40e5401640d8100403151002d40d62000000c0c441c0240311300702151024860 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 533154775 1250 533153525 533153527
    0x111224090606090d0b040825080706090305040f0305060103061a101d090103110405070c05120a0e0301020a080603010e010e3408010510060c110d140a0f121707030203040302030906 79
    0x30020388001034440d90b50a030b042140c40d40780717a00700003040380c0311048c028086030020068500481c4042d042038810601074180b00d0301c0c0c10303512240103204021a50003550142c200c01c0051041100c6030182c4103000d64252942c0b11007105420028181d440303410041004e05c2981076800f0200f1084440c1c6034110368008094003400d69580c1000008250741000c001e10a03031500c40040e071031a00440480d87e2803034108000740400f0320b0b07112065880c0d43c0003510385814030030b07070303060060b55aa000d0000300718a545e81e0303030f5101031818000c05050070340f1807612a9a030580d04007500b04080c07250002d0034881c5040ba4045900c010044460401449024401c440203544400300d00490300c0141500400e005000d0017160a00da90790b00c0c07408403000204c0500041c800b04000c2c0000b54103150550400380c50500602c10000d1038030400d43ca030361901d020128100e4020042c00400d1040c0701044444605c910b407031b41000e21414842440b050340f00100101454249a8007001080a15100300280d8000d0b1201074180c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 533156025 1250 533154775 533154781
    0x15050429040b031902120a03051b030405120a0614090c2808071406130b0a09050301020c0c0906040501060c2d0b06031b01140904111224090606090d0b 66
    0x75480c0301c0300e1a07070117034010303280084c481c0b80f0600002001203071643c255450318100100d10f45200c140c640b4a60f90440d4510080c40301060319075554036003a03900d6009500a1103807400d42e140240640c3c00030041e8140d000300340d40800a110f1804560f2049410b801c40795071154490241e41e0000c400c040014030042c500360424003244d078100001d8054142c41c500c001501140d20810200300701c42c400e00f4420055545003000c00c100411036480503110a46190804030ba049440c2c2000c0390880c0c00c01126070640354811178450421f401e10110003074100c0010b8805000d59070520401500d000c0f85280c1c001c10145d4808003409148c2e80072005901c4040e54414460f402036400e0401d000903200907036540f40300303008903400c00c20006081300c415641481c041e1209995108541c481c01825001940440d40168640001c4400c20203400f0081c03082c5a101407903000e00781416160058030361441c4081c1d91824115115050302036440b03459441c1d110b02c08454440c1c1d580794000208a101c820910000c10a003e08414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 533157275 1250 533156025 533156053
    0xc01020f0f041805040305070b19050c0310230d03050c12040303030b04090506010302090c120c0301080c01020a0503032404020c0f060a140c0c010e07030615050429040b03 75
    0x100200d400c6030307160fa200c0c048006810022903406580060105000300443c50000d00e180003001c1d4018030805894182291041c4400305480f01140c000f5812a0008204603d4480b0aa0050080d014140480c0003010414240c3c59503480300010861048560b003030070b4420544950201d4510000000c1901c00b1980c925604100325005408101c001c00d050120317001c102e09045c450352403d150000010941030f46960244082a000034040e1036440b001003020503664010704210500880e00710300074560320340c94000418207044281c981d440c1150080c540381c401080d000010b0369049426020706006491960b8101c010003150b81c60300c00d401900108410342c888102042d440d002000d044144c0e40c4a5441410130303402c03614144141c0003903032210408034948503086c00c0501340c10b02c0c401000007400700341407035450316114895004032101610340540d4562000200d00f4103000341800d64080c082400790340d9504407600c0d400c940c800c080000c0200911215a0340c0d82150b0f4001c080a03081e0750308018842c3d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 533158525 1250 533157275 533157277
    0xa060b0d14030c120c100b0411120402090f0f0a0c090905130b0f060310090206120103080c07060207051005090f0a120b090c06030420030607092310050c01020f0f 71
    0x340f1821401442c0c2c203050f500f0050710407a03c507042640003400c0e140048031181c00007004840e6000307030081d03592610140b0300944800106102c6000c001c203c0d40510b0103204011050200800300041d0110b05024811200c0c90040c206403c80118100070903112100e410840c0c1080d0260f1051064030b00341070034040703004a4a00c2c0e25800754002d2034100320650f0758002c05104113038107a4850b501a03001c050701c1c40d0020042c3d0b00214486200030b001c07515028403460800e0f0404000c0c1c2065a450900040d07684a1003403c0010900514040c0081c2c600c5d070340b6282c00144060b01840c82c0c0320510900040b10019a42c40307010f180000c0c0c1b00140222a099112442009013140140d0115482d10000d4042045114001022003926600900b80c6240d952240e6480d450b03e0310347c10850407001b400e95030410003a90180807032841195541d545c403102a1501ca01c42c0039420341d655189140030200055a101600c80f10819109000390b4100320b9910400d944134240288642c0300225003840c030225400b207410344600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 533159775 1250 533158525 533158537
    0xc070905010905090a021c0c03211106060f0105071415100506040302030606042406080703061e03020402030c13170705060310090507090e190c050702030a060b0d1403 73
    0x202d4200500d546058030b45607540000b070704c080e5100c960302c08a034a009100c80014507250b0b11403054031140c0341c0c0e00d643d040081d144c0d582041d03c028034452002c02c42c2c69844040440c0c40d0211600401076403c1410101f01144402202181002800036403081417118402c582e845400e0640103c91903140c10703154042c0b16000c00c3d11505620f00d144c00d400501c0307143c5601920305494000b4054030142d12182c007048000c0800c0246000ba03002c00c0c0070030000d03480014072854000c06154554000919019a000742110349603001683c4d511a460442640d28190903901b0b003d6a80c103840069a070b48032500354903002d01070360081c095840f10700f130303004a183c1c5070445021000b0205ca00882c1d81d0036842d4410880036010803143c0c0700c00720282c090308000300c4000d5041113030405494105000b01588800f0700f032180c940c0840c1c000c1020300f90742d441440e4a03031081c414030500b80141e18013141010360030750020b92900250040604007030b80782d25121006503a807281c40301e195580088034681c4540424556501ea40241c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 533161025 1250 533159775 533159789
    0x51b0706090309092310030803040c090b1c0b07201c030b0913020604050402030c1b030a0f08090c0918060123040507090b03011202280303140c07090501 67
    0x1c0500241d0701c0c1084c000c1d540150500041103091007104505c2c100312460080c030100c4210003d40001020440c903100641c0514042c1c1240c5080ca0b0030030000c2030aa1705001170040c001c54401000c2d4201c08041444541420752002c43d075000382c0c9582c50125010010582c401c801e0305104a410342181d50006101c45410700710707100d050106100190185d00301c6041451494014000702d0000b06184550074107600c0b002c0c801032620b0300f015251400f044c02c80e003003182e116110000000341a28408400001e002000d41c4210042d8a0440c0d41c660043c0b03003041b4000001c00303104800010078060315090110040c0c40e003024005002074504402031036200c1c0c100c1500d1540c1409035030000719085840c0380344000f144c02c800c0c1d1644140c41c038181c1488002e040c010000010084409004181c200d4001d004600900004141c04030400c0355004028045480480c3c10a10203c0e150075194801d0500d4000310480c0d4050800d0300400d00d041d0070780b01403842034180342503090040c0400400d134004254400c41c181c03407007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 533162275 1250 533161025 533161037
    0x4060206060402090904020d080403060f0b030f010e0c0f040204171f060e010501121407031a06070c050d080706050708071b24060302031b0102010c0c080409051b07060903 75
    0x41c101c01d00c8103d00c10314240703c1d0041c00340c0e0300003070243c02c0295440c2591840f800f90303903103080da803a1501e408030b80028615061107070703d44031001c0d41c0340f500700010000309100304020008116200d250300c0d5a12980d0040c68020094503048503020f950301d6065a0040c8580c060b4a034425100364905e0380c0710850011306038a502038a4842102e400902d100d5101a40ca045903450307120303401d040040d0381a83d0300c4559040103540701c2004855224400401c0c078000c2e2140d440100300c0d40e605c800c1300701c215101e10741c1b140d0207880180054404150280c0318201251400c0d60808516181130408120600c101e00c0c01908003410030f42400340690340000c2d4a44503600561300d80c0c03e08466180d56040c03c0d0003004028001c0e000c44070924002005c65400c44180c100c00d201c0010b5050303584d60210742440c075030f00d580301146c1e0943c400540b00c0b2b58080c01f41c40c914400c0740c9000618000b2990707030301040d80603034028401c1d100e0b130325000201c56219924145840440c0070140326103612091a02e81c0180031407203021000109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 533163525 1250 533162275 533162281
    0x31f0c031404050a1b060923030f07151106010308131a0315010c050a02120f1e0105060105041a09010201020904050109231009050c0919170a03090603091b06030204060206 75
    0x207017000010f000c0c0c0b8075555038070f41c041e0715000505605092100610410050200c0b072150140e80800c4050030759483c032805040d10f00e1130a101c022034204802450403d02c503a001e404100d4002c0410b4042c15651301c00d5195486040b109500c41c8007030b03c00e401c0303040084010b54003540100e00d15409148a5200000820b05072041d1000444824030a004010b1450380b1140d2684014030380500c5030242e00b0003141c2250380e0f1780c0e07801e02050b01d49010300203240b10a0391180080a10032200707006195101c202828091718080c42c0014051086d6043c01c031021022034007241d201e030070303038400c1d01142d010142c0240188810350319424500024862a9180360b0424019001160307a15080c4444034401c400c03090010080b5442c20050174082c110080040303026600030403020f0280d54810410200500740d01e07040ca03000302d0a00001d0b0b4806d00004001403040d40c803c221010000758001107903016260203244c0851655064501040f1110380080000d40c81c2d10382800100f1981d501d54003030401c0b103000c1e600301d400c191 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 533164775 1250 533163525 533163563
    0x90a050322060521041b060c03020709110a0809011107080c0f060c03180a0501051015081303050f09040e010c03140f01030b0c36031f0c031404050a 65
    0x40310768002401d501d840e88103803a40c0c1002c4e00c032a07180c0c41801524a1668813407542680c103c903988a8004602090100c0011002c0c9541000500050040d0310010008034520b114200172501814442004120100c070000d91b282100f90014003070103600303008968940405141410441d08201481507a070f20480581000111000410301c2c0145803000c1c00600e1340d00c6082c030b10549030044000340c1007075129012884d0b00090092244500c18800040d42d040100d0506180401c3d500280c04180c082003560400d02070b0508107000c200e10125410b00300565070705548a2480c10600a120206600030314040da85070b9000b0041d003080105005035a01044400b01d02854480d0002e02556000c81c00c4a041300180000380da04418150001e020444c42414282c40740c071441c40c000044c94208088851010861800407507105080d441803070220041e205240c0c10301c0080c41812640480c508600e0744956014410500940c090300c4000d041e2640d03c00203103000d0905070340d1b40c102c0c204102d0368610305145240b1301c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 533166025 1250 533164775 533164777
    0x7031115180a020306041a070c151a09070c060b06272404080d0c1509080408030a0e0907050c0303010e07140c1005070f0215090a0503220605 62
    0xd4604150a500c0d80d1150741003244411200c0005803141e02c035400c0100056039080103054803891154440d140d44400002c5003005404000d020001804001403d150003d062120000118400d07003c000900d1420494a41c080004068440d60403804035024001803c0e4002d2302040241d01400040c040544042c0a203e80c903c25400d0761009074140a5000303001c00c04100b007084828400a000340c903003140d20550344548030910b02c0c5240c81403400241c10480c3c2041801928802c1c0030a043c109058400d984585a00800307826003141140c0d03032048031b1801c1008005c241c601a299400071030780c44180245c005004001c035480c54034855040f40b40050f542038483c00440e8442244c05001e11300b50713482c0506c402401c44014003501d05000385c005105003080c03036400290111419001c010f040800d1011038003c12500060400d208000568104800780c03074000841100c441c25002c0428500ea0320024600d0801d484220014403900000401c0c20390702d0241c01100c1c2908103445170005040f542c40b00700341d0719 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 533167275 1250 533166025 533166043
    0x906182301030b0f1c05010609020c0d08090105010608040605101503290121090f08090f0405010f15140d0506150a020c01030e03090a08010501060306050409020d1e050a030203070311 80
    0x48000c4049140046a142198030b105c1d861054001103595030725001c200c001c0c0e0308040781e1150603030b2000c20034111966100e1815a04050b44100030805035051850043c0f00e500010b1024211a844101203410b524400c0c66038801407113603007441149251001c0f4004e001d8000348666580010040d40300c2d05800026142038900180140c41e06090408034440d941010106034124810f80ca03620700d0700401040000c0c0c060300e08180b040a03c6903a40c41802c0410400340507581d00140500e24080c010302200c55180c1002040e1035010b8060700440381c80880413140da00046032180c3c60740f640803550784100001398010720701800d82240c884810500080410050f40504410f400c0103900c542429807565010b135020001c0030082c00c050340e18100501003c2904c8840030f0b4440c104c1c0741e540304010031010782d1507c00c140250504840920459906400044130254410405002404440100f180c00b40702803441c0d4007250391100a07120f240c070040c00c0c043d442c0c2c0c201e201d06a002c5055030151451501c400700715000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 533168525 1250 533167275 533167279
    0x2a0b0c071706070f0903080406021501080a11090c040b0c030408010b0d0804090507140a020d020d02010207051f0b1804061d1c0302040b040807030606080303070906182301030b0f 78
    0x451036841c3c1804840c2c3d02c0d1011145020f0115072007001c0003150012000b440075201a4004100072104100800010401640720381d200380c0000182c2d00005504542226441c01c007210f03070000f02c0c3c6600c0300d03941c42441b41d54410300349542e0000d440036507060044081d004a415960080080065034000d000f1480c6801c0e400a00c1e9038400c00c010300003a005640150381140082ca000b40d42a000c00b0036440c0994840902c55025070701a01a0b034007969030400040301052407a100940c20104503903101d0b90343d001d001424248001884455211082d501d51050322a81002442c0252681c10640d1402018000355030030317100241043c22500743c020b210701c2c540b0f60040e0440010011900700e02440401c800000340e5150805030208030002c5c84030707003140291000d0100800a850030a1a45c13401c48101d822550040e0b070580c006004104409400c815824215031007400e004c0f044942035107100100d01450741019441141d50740420001074070029480c03400c00000e03241040340344003220030800e01448c410540c503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 533169775 1250 533168525 533168533
    0xc1507020a0e070219060b1f090b0f0c1614060304081b0a1b170708030a11010e0706030b0f0904050303130317070e031e03072a0b0c0717 60
    0x5801040c9601d00c0c2d00030620b00c15616129030710303940c0883d100e4170390000751402a15030082c03040901d40382d1030a4400c48000e403010500c4500c02c02c40509080503610481000e8400450403804a00c400b100f1104071203c9102a94920f802d02e111607400b601c0d460150703091041d458003040c5150308204003140d000d0798102001e00d00f0000021079509410403c404a00d1003805441000d5001a0081e804c9030480942c40515a49841c00c050145501070b2071540084402d9101041c200070141000c4110b910f0514140740c90440006040d182c1809032006906140b180e2060030320005000d5416031003640032583c100c4030b08148181040400030030440540b4041c003079800c1040852109400301ca0410300c042c0c800d00346000c0020760119000b0404e001268510f012a801d2800d4000301d02d410b10008000c0400c84001c803111001c81044c0d81d50360300030000010701c1051080340b214016201c042124058040221241104a482c1c1c0c0c24801560403a2160035032501c076041c004206080c0f02c0942040310314802c4010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 533171025 1250 533169775 533169779
    0x8090601080a151e0c2a03030504020a0803031e090d0f0f090e0112030822080d0609022b0c0e040207020a15030506032e0f0b03030c0c1507020a 63
    0x241030560554001c0300e034641e55868180115042e041030f046160b5101090001d00e040101a02600f0b1b002c95405240900c80a660603004560a18034602c2010b5014a0002016610381c400300d40070459a810500291002000300309080d4195207035601d030405c5901d80c43c9555201d148030541d44051141c0440c010035404542226010300c11070141d00c00384650b01e040d0090750f41e0307800061021a0b00303030003101c501080d000f051010701d0307084000680c10900c1caa0300c41d905030303101000e48403500c080c80704c000f0000d8500052500c02c401182d01b094004e000d2480d000c550350920411075103070001c030189580b402c980b855001e207210390300280300e011006e00c181c0d110204900c01d0481001700070740c800c2000b01c0c3e2088003100007080b03c08103254407540d40c4c01c80351800526030501c00100351505640d644190084540031a4490080c002104c55a480e96032108000c1802c501302c41114010f0010841195094800441c0102c803c0ea0002440c40790440b0503a540300303102c1d0712080c9400c5944204400650011488003003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 533172275 1250 533171025 533171033
    0x718020c0724120204051012181a0a090b0112050d0207060207090b0a0902030408030417030403091707030506090a2d0f0f052b0306050f060702030a1a040308090601080a 74
    0xd403c4a803070503520300600d4681c5910000320700c00424500c03540040c03805184040c03001d200d44a0907014040d1200c01340701aa4803550f50400e14001031140c1500c6011413800f041c0424107540003901840d40c00880500150f85407031403c02d10b034840040995080c0300300c0752a034580c140042524015211164083d1111904003504000a00801c0c0000e5030420b07a80e2000041c254210f202640c02144625400790b0380341450300341074240301c01264070205107100030014000042e411100a004450051680441d50400d194000d03050815562000d800d601400c41003155160002c90745040541c402d11116092041880100700c1d12501044500036003010300c403030000860112a59240c10ba071084240703100b02209641d07003500b00441c2c0d0140e51800054100c000c2070320760b0320381292640242c0601c0c0c10441035140ca000203603070041c070710110342c01007200140c1142507407030a02c021a025900581c0f000c0b624800314408070b010220443d010303000a0f40b420041022403d0100b01e041c100c0d02d07040018080181c45460f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 533173525 1250 533172275 533172287
    0x1180b07030902030307080c15010803040506070605040f0510020c0f0105100614070c0608010617060a0b0c0106031e0c050312040506030a0f0c02010902011229030718020c0724 77
    0x1500f66410b00c014040d600000302044001c20310600008040c0242c0510b00030850301040381030f082018a40c01c144010300464447c1c0055850782e0360441d0011813561503509001b0b1280c18001000f4129004842803084107941d603400030280c5884860841d1110001ca1150314200d0f4410f0360381c481c007520701d10001c00c4803610a11000f0144121490410302c1c0c08401e40c0c5003603c543c1a544040b02003035031800100220b90300100d944641c0c02045040d000d8500e84000003d024040d140100035643c507020034004044e44007503200001039a4051500072910018031814100d036410413404403819030140e50041400e04010850441c402c3c00421142c1c10b00e0f0031300c000c100c50382d040107124031811661000b164584150b0780c080c084100c0d265400010340f4401e036000050202050071400d600c0342c2d0503e140121480120200c0f4040e0442c81d41d840203d40b10010700090030840c0d213a1181031a041c0b80009a0170711201355000b05240141101100c80c84c5503030320103404048004141c2c02e811405200d44c0098070314000d107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 533174775 1250 533173525 533173541
    0x2040305061b1201060309380c091504090b030114152d01090b0f0f09060705061f09110a0e150310080705120304050105130f030605040501180b0703 65
    0x40b040da06018260992000030314090b48020006600c8500384802c0c00309a494050a050201000c41c5100528469a0414042441c80341c0390301c1c10800001040840361106440340f030340c0018100741400440780b004043c250400c0c01794440c1c0a14184c65128145014415030300b181c8101442d0511036924440024503141e13042c900340350807991814034072120070301c849180c9614882c0070389141100340704c8100040615002d50031100400c5010072030050f00200100503034524407c13607590729030f44a401e0804904076005010000b8940d204250622030b20841c1c91a000c1c03e84001c81c000c0c1c0f07580517070381c4140d8015901201c142c101000010400f0680140c4643c003404174200d07014090381045002c17000f01241d0381e070084444c0c0d80d26403000e05c000c2c040c0c420b00388500c50081c84d00302d0320444e141010794292a1a40302d00d10615050140c000355088032090303031080001c028004442c2c110412982d03414610080c21089808030b03810b52906140700304980c2161040e800854011040a40d50f59502006900900c481 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 533176025 1250 533174775 533174821
    0x8011e1503021e030a150f05010302010e101419020f0a030c0308091f020c0c01022418251d060913061119020a03020a06050a0207021206060a06030204030506 69
    0x4600440f01e80d031802c000d4035002c0c61040304440b40c103085401c41c010440b100500fa1070301503070900c4010400b5070703801400c00194001c1207908002c2507003c590103841c4c0b080380d0030301011926808580f030007070f40c002003501100c596550703000e6914642c0300e00051600c4401c0c11000a022440c90030303035580800c1c03040c45400c1d84007400004858051044503c07080c007020000d40c0b0107103510740001c1e1700c0c2c3e5410780611295036282802e000070290540c4582c04403210341da80b9455a8031f002d040c0c0d0000b83d0702c2d1070780400070360600513942c0c117a03540840c800b1850142c0801c0460450213184008100050b0700b4036450041000b01000d05c03244003da10390b4410130000310409060740d2910140c603519040816a18420000389814415016a0b141d407580c2d4141c2078610045034210554101e020300002194010035400095548094002056524103001c81300078007400c03a02941064240c105540038150010b5664000c4604030395070f80400e0707980c2e207044081e0f03c43c50000030610381050001c210341c501940c07180d4041c0c80503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 533177275 1250 533176025 533176069
    0x11240d0906020c06160e19030204050c070c080a21050304060c0e061611060304081902070f080a0302150105010f050c0703020411040303030f110406080711010608011e150302 76
    0xc0e0000145041d80917501c020105200d00155200540c01c10180300650304142c0c0c0c0034007140100b610100081c00e0034440a40125211800109401c40380c4089442c0141d01101120701e4548a810036030f0b5034007034900c00b100c510a2031315140f40d115015030181d2100411a41d90b6a00c1d550b1a40e60304001781c9007a0798680e050120028a241080d03503500094403410401480100442805041460804030104030841c082c80381082400081070411f811a43c00949140c008118000c40220485c6802c105911489260030321090100b0484070104000c0d20490003039003110070345081d104d59052000820710885011540030549881000c5c01200507140a000c10300c140c4404969031b030045806d44403d000c1910004000107028000c260b01449107a81a0342d400d070040001c0e0101c02455080d521450113040d090101120001d50308602c145200c0000c01c00c401d0003400150b64404086001e48800c1607180c0000c814010942e41c07600440c41451b00d290354010420040300e14603028400d40c4051032920300c8104d00f0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 533178525 1250 533177275 533177287
    0x3082203110a050f03090a050405070207031b0503030307050a0806030d0912080904020a0e01020d0206010302130e0a2420030c09030a0f030e010305060d02240d0911240d090602 77
    0x401802044c44c10341500c0040c40c0d13282c1d060820001000825004140302d207103800140007620707900040d0b07a030940380e1084100b0301112041001c01c250b205640e000395030600c400000c101c0c0144d40301020302030320105603c0c0d01d4450f450300410141c440118484000019901c000104030250300001c003802e60300e000d85102807400407610085002e030b81c0005542408180c50104511071945e0400054034510f00350b1001c0d0140b54110790008001c0062100c00010315501ca1500c0124403500740220340e102e503880480d07504007040307100c520040e9428201c00882680d03c3d0420511031082c400680040c01d07000a030103a4555030364000800303405e4001c0301c149600f41c03140180070341c001105412145a082c2c001c0e12030701100c1c4881d000040503620000d144600030000c80c400360006072640440d42d5405001c5c4c2d541c0c4016600d00d60f480b0000303809543c0c03680324010308103016002481204405200c0e44001500c80d010114803203103200003022400c0b0003440b040482042030500c82e4121b68058003c5601c9400050f203003203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 533179775 1250 533178525 533178533
    0x207050105090a0c060801060801050d1e030809070f0e040b0a0b18190b010516051009080c100228120207050615040b0a05040906060e07080403082203110a 68
    0x362044a00e08040da0054403c3c3c0240180781038008000d01d510b00d0584030540c10000020021081845160700450042e0030780c0e810000d9a003080001000a59030488410803503080040c00e011f401c2d141e9200074000c400b4041040c0311051003100c10b8403000080034135035803115599441014401131010044954492007441d0701c3e6580060400c81034a0310148001d14101603205008502c4002d1418030ba80d840c054609240b641c020054900803040c0500702888800f660520034100400320080600042c0340c000303501c0030403103803030042d0810203800300803a403441c10242c0c5a032007244140901341c2808590495041c004940c519020048030183e031a04801d50109000408141c2e00f14101c100c4254010208100c1d5080d01d03002c0b0354801c60021542400803e80040102c0c0d90241c46000d218000c94486400c0021702000d030700550010801e141c2108154036100e0300041c114242600c1c02c800182038000030407005079000b07564101401c058a142242075429139015100906000c42d004114060703018504003003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 533181025 1250 533179775 533179781
    0x2502040f0603031701081c0f030e030a030207030305010807030209130501110f0d0e070605031f030210030905070b0301080705060901020f070e1f0f06050903031216080c1207050d02070501 82
    0x158425101d484c00c0c06035103020380c9007425050b0031812595014140c10302462000c3e82040500c50583c1c00e1151400956000840140012003071542840c800050750803070042d45540103221550181e54204210703601e882106482d02d07400e10002c1c0d40201c004c0040344d801c500900520700b180c0d21030000095005a583c845903050b40201c00404200080401c0c0000704000070b0081c0740d008041140502404c5042100c0640140006088019861038030f2030703603801c0c01c80c0c8244007070080c5d50000c000f03420390b101c4d41d88001d003d0003000c42d0840340d90080f80c000048003040503040d40e041c1c0d00544040c2131102e00349014044150860007080e07045205140c49900c1c0000c0030b1120030080c00351151803800070b00d40003030311102c0524007420f030003100c0070340030030810208200c0c0100c40c06641380751a00c65134405202d070005c3e295014100782c01004804040610a24055440700c0002400c6c10b0b07210360300f080e038540c1c03001a600c0c09440300e14074211040b2000a00703000d03c504001c0039030300d101c0d01d030040c2440c099888150071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 533182275 1250 533181025 533181029
    0x9120b0103020a0504020a08150d080c071508241813031b03020309040509031903050603010c210b040f11070b0a02031611120a1d062502040f06 63
    0x100426100051065050040030304002d000c0590701036142c10160440203184140040980f8141d00d044090180c2555440c4d011890980e0041009603d410b0303035100e1642c03203003110310801c0d802c1c0c6915029089801d02502c2050310400c215a0440000b03940b03018001046407204400d030b0781c00155514200303500040310031468042c2c4240c43d00c24612090038a07001d0311100c1c101e0f80000396035803041849400654000103c0741414825940401c46442d0f0750710b201d142d03015040c0d8602038201c00c800c13014145540755104e1880b03035400310f0081c0f10074800300000303039060040c1094a0131a843c40341401d04c04501a40c00c01e54204802820000d551041800310104a44042c002e400c5200340018000c030078031004201e071f6504980114003c51443c200b03440d080a8001c403904001e02440700e0014801007040051110404e1140034000040e66010b8500000f0000080501031030320400001c4450f10386403c0c00c5c02901c9080f00703c442c000311151003110425550303400e0038400320ba10a48400c21b41d00015403034041c03100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 533183525 1250 533182275 533182283
    0xe04030305220f020102010f110414031011070b0112082505030406020a0204110313020d140102180910060801120501060911120921073002011103060609100912 70
    0x42144552000900f500c000b40640303010f890270b00e44000364695000d0300b00d50850b00c60b9001c1900801ca20008039013801034001801a40d18600101707900081c420714000c0c55000d1280c0304440640c4e8a4584401e0ba910b06c3c1d22023300b081d0f105101c88618004400054248481c0c400480b542e007000c035640346031956001781c000c14016004105071008504050150b08440001d0102c041c0c00c62070609030b5440000951240a403040769190001340500c080a00c050120f09040c000a654600040e1206044400501580c6005200b2a80020754010a21395240140c800c19a96140940d10740743c00402042c04000301a1025585c8100c00502c015061181c0d00810303108900c11a100d4601c01c0c507041ea804030091000d02e4913000791221114000508580a2601d40d40307190703a5450301c055050ac141640c055050300c181ca030010280450210f003012410150340d44040d0700a110301030340000107080f83d0000351030450300940c00f445000c0803840e1402c0f20429001291401201c0a55038045020740700c82c10300c1f0700381c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 533184775 1250 533183525 533183543
    0xa02150a0f0e0606061207090b030109020405011101090213050603120408160816031e02090a0b1e1503090a08040905011a0304050d030b1201060810150e0403030522 72
    0x915100d500b40500001c2c0d184034000381000d4502000410010320500380703c00d00c007250880004d85041d0044c40c990001d071841052054903507849a0021b4000c0d030040c0101408540c100081c02c4418030140a0711000990241660315030101e4030440101038440582215414090600080381c030410b4000071304002d1001e0801004507a03c0c149140f51400c04c0798024000796007100021403101c070303200b0420008607135008101020809080800c4500420032000c029031243c8641c042c441405211742140040c0b003001c942c8008803102d85100180710104086649410081020307500032107500e0341e0701071680064040c090f281c0c5000300b40d0301c0c40015030154001d004825561401884810f542d600c519104204030420f081c44e5080c40c0d15040e07506ea6411070414201625000500b18a8a8401c06084500c40300b4000384a215110022070380c40b050f041c2c8104102500c0c010640303010803418112541112a043e481140315120390b10201c0c003621005200010700c0084072003109039055441c80c84445140684050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 533186025 1250 533184775 533184791
    0x4020f0d02011e03091403120c0c01061706190605030c0103090510090f110a0f05040c0207080102040923011214071e06030c020f071202030a150209090901140406020a02150a 76
    0x1102c06d00c031b56900341c080079a0090200024024075105c60300c3e08051240200c47c3c8515101004502505030307030300482180c00340d804080079104c40000301c1c90b005242c2440312007130040f0700c4103013081151a140f0400f5496404060741c40c009500035440203050501503030a03603402403403d00044054030040c0004854921129100c4014004c000e44650740000085071050a260701d0015600c450843c98007a00b84603d50303443d00c00b0080c0d40204607c40c018000c1100a5484035580e00d0310400a0090040075800c500b00010039240c0071001c90700c050b05843e4040f0081c021600f0a446105000000390303601c0303007203104c1d101002c2600c0c88000900c0075841500d01000c0341403402e005c002019198950526015940043d600309040c2c500401c1490070b482103484036000f003000b50b0000038681a2110f802400340800043c511501481030b030001c0481c100300740d6480300350b40c4803000035a08841400340c3e4444c0341d4820001080008140350010101c040451040766048a1504c000d2800c2c40800e840a1319655034ad0044c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 533187275 1250 533186025 533186033
    0xc091302010215040305090f06130b030106120608031801050f0c0d110f06011403011e02040801141306050c0c01050708060a120b060d050708060a1a0904020f0d02011e0309 75
    0x6140440d0712a200042d0f242d0405a801a01324003442c4841c92080041003804030302929404103031a00e60040600081d1140c0da907134000d0040c0d520278040d150001d61900e28800b01d0041c2c0340221411181d502009525280410036010f5000c4841820341d410400e08100130740d0158a4600601000c945000250808048030366000c3c1420f8580070510310217800410240e4400c1e40085049411075020140880d4550100ca0000b0b0041003d88401103242140300c1403002c10783c28960103001a24405402000003030035107080907204140860701c1c0c000b00c48103921000000760304c1c0d40186810900d96042d09051103416100c0760b00703580c3e086840f40f00103140c610803c0080d10b001840b040c001c003100a15001c4a42d0140c5402c0c80340c2800600190043c0c03081d10080d0304015080141130000c01002003614464201080140040c0032005201400e05401111039206445c103101c185002e2a03004110a14008000c400d201d06042a508241c0c1801034480304c0c01a1340d8800c02050724040b44903500050000c40c40d140c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 533188525 1250 533187275 533187283
    0x41a0a0207060e031f020f0a02011b020f07060507020a09111e040b09060306180f0103120207141c0c090204031716080d15150f08270c0913020102 64
    0x445001000110120403846482c08602c0701200b0316408082000283e0482034035011f88179854180d92155000107800b042d0a41c190320000e00c881c80a402d1095020000000f21307950a202c0f12100b03204e40007041d080168a008000400840384050030103c200c681d50540502160407140d45c0c14186d01c0005a5075000c00307080c4da24411800503041c0d10600700707030500000c0410340c0901c030040f40c0030b103e000000c20b42d41d90b500603c504001c1550140340e01686000025034682e682c00f81b000303c1d4a01c0a0301c082651740d80c008a0304100b6100c40e107414011044281c000c2206100920302c1c400601c0c3e102ca1450b40220f40403400100c00b402d1392803c0940d455180d450400c1a4810031142d030110140c0034000e031154080846030b0f220602e134000281588a80780480c0300d41c0180b20101040180404090b0001201758080c0030101d03040d46603848410007103c10201c150b40d03020044504260484004484d9084005407000c150000d4061400f1104c112044001140c0001400e82d81c48003408043d5000d08115a4108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 533189775 1250 533188525 533188529
    0x6021801020d020c130905070b09010f0e10140d0e060907050607020d230106240206070e041a03010203091b01090e04020d0807021f180302090109020a0302041a0a0207 73
    0x200c001c154100110b40000d44607401000700e14440e0880d07810480541c07001c0d40190340340640000c2518000d903900e4111400d640e100010013404120100c0000980d640660b00f01041030710091b145100c52140480c0071123040c00320b940c910815520030722044c6100384480c81014844101c500081801d41004001d1501e015440d0b405988200300403c162001a15403002001e039047e4841c03810100c5800000c100350f000280400300e56250340c6016000113084403014554100d01a400c403100f516003400d10812030311440704076010381c00305c0e22214503d105810325501200d5100b00c80ca040d1034061507400c0000b1309a0340143c51025860b4000b0344003114200400c412005010002d0820a22140c0751401402c40150b0040029105401c42420700c828492100d00b21020f090340201880c00c6205600c2030004400882c0440b1000185030207a400f6000788010580c00540382c0040007074803183e190010b50006540100303002c404042d000e0000240d45040c014000034040000400381b92200380544c0c00034580b245503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 533191025 1250 533189775 533189777
    0xc060c0818010e070b0901020a02030a0309050112230907051801050405013f0803010b181e040b040b0306010821091f35011208040524030406021801 65
    0x1c00e5600d21403c20001c0c0310011034074920003850300c401003100180d00f03050001001940501584c0002400c0503405140c040070780f142601c0e40c070840c203d04c95800c0c027211f42c81e5031448a1040048400c42401d00d105100642c40300c406400c44102075211800729012140c0d1880d40c140071143c2500500880c60a806200e0140c408400c01a102800d52301038a640c821240340021180d01081407a007456060304d40990710000c0e000510b01c0c4d0b0306e503501c103d131031642d0307000c07841c1e1b00c5c10710b4505050800c3c14074004881480c1441c40c10150300310415108204001000140b01c0c070b44e440383d5038540420b056107040c42164002d143c01b101501d00400c0d061200000045500741840c000002006640b0a40c1d640208481491071120407110101520420965103550301245140c2000380340002841540c58a428030005684511440c1c039040e41c0e1440e5a03c00300320788880041048000f80428042410040211212350381004807007107400310380c010b108810b0f83c4252021ba82003a00003e00c02000e210140d89800e00b9403003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 533192275 1250 533191025 533191031
    0x3060302100e2b020102330403030906060f150e0a18140103060e100506060703030509191b0803041802030603030412050d030b01080f0103080a110111070525030f030c060c081801 78
    0x5038034074045a00902031012803209420f403005c2360a0511a900180c1c040d0b0780004200910b41d21005102c0114920784155a960b9100f8903180907428811104645189000350100005500309283c0700c03240d04034490320010b140d43d0788101515a03034040c07603101e0003903004640c00100990090380c860300f024040054075046a0906040c0f1031203480702c1e4102d07162550589000203654445448103802c011001e0350b809100b15030b41c2240c400307020101c0d0304411002003032528561141d590720340c8903450740034601c42c400c1d09441040c24904909a250021640a580101070300c1c94940c80d07202c070302500d405045003a01c0c0703680812152a0b400d42c2500c1810314802003400e100c4007902c2d02c00150000c0030740501002303114010100d54507891900034600c14808000d14002807214000c454036883c20740e0000b00c026500d5201e42e032035801f803144085403076072801c800a402c0e0020660039612010b400310203010b030032010400c41c0d0040d14089139003441400401980e41d030340c00c1d1890800510204101307080114a0885900d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 533193525 1250 533192275 533192323
    0x90b15150f030c030414010c020c12010605060301050402250606090c050301031e3306150f030207081215120c060426030f0d060603060302100e2b020102 67
    0x10221054a034043c1d0f516904555941e01e91506141d2010101000b8a0642c00c1c881140b007495000300d40381030a4042580d1403c1c1c803c9148081c24261a610b100c3d05800100402c014000d40c18150001c0c4244050f0384055a10100da0f2415039000f03942c410340581d12075650314010f01207514a40120703030310402c8a1038a90706550564541d0040035100c0d1110414150210510400b041052a0380c02101c1002e440c410711441c008152000b05088541c800c65a07540c500300010640b0b440025080c0b440154940c0c03030744d1803806203035429002580034010990b03048205005007400d40783d2403070b152032003900a181e206540164110511002d8040700301c06810b1a00107500d89241606c4140a403000c41d00c800003982403400c10340e41c0190b550050300b01c0c0b40680340000942c4941c0c0343c840000501b0903c0013604108905075648a0403005c4466502000f0360105091000703003d80e51064a2102000c040241070340c052004e0f030860b004005855003118841c694040c4030380c809549c0c040c80034a000070001c02c1003655401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 533194775 1250 533193525 533193547
    0x50103020a06050c01090501110c010f050705160804050301050c090f04060315150512030306030613030906030506011b030905010f0e0a06050a2601050916091503090b1515 75
    0x41c0c62809048200980400c2401070070600350000c4007000d0b04080208007100030040041041d60045002c06a10744c00c101100c112580544181c0e8070031122513a0345d60400c11b002480d2207444400440544640c0001e000c0851560340a21074513014008488100307588001441c18400c0e050080c40c01c40c1c0c8914980b4500304003103216a1402c0344603c0e90200b0008041c29000c0002e03200204a0f0080b0390040001640d0b440b0040c00000110b0241d20b04074111400b40d940c0c01043c1803401c580340c2c1c00500050142d00e007084240c0c0241c015a80040050400251920100406981c034210f440c4040d8001460480c08011035604000e81034100001454440c030580341e0000130512004040c810101004000201c000500348550004003000804e0b80c440e40e030444100c00d91606191080c016544501c2a00000c80c2500b01071790400c4032102000d450303c004040c030b80901d003188811090651010300d6160307491400003031180c40e00c041c485c4002081208219060000740060503800c0c25510b0703a8100d0404c0b09441c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 533196025 1250 533194775 533194789
    0xd0c0b09060709060e0406030803100e0f04171305061326030412050703020a0909050709020c15090705100503010806060a06020a080a050f0403030c060506032d030c030f0c1005010302 80
    0x130781d056040c42c2e1041c1d12480c010500030402684082d00d2100e012091103041d0202c8a41c800440b0616011030596071501c1640c1c20f01d1280030b9500800b45003408070f610380d00450b84006080401180355080c501c103a617400114440c0e52000032035006003d6004400d11003458140071188808400c1e00407802c6561450102c6552440703a80200c221901c800c001220070820308000100155601510304000070b075581c10464040d20031702e070089803107000d0500e0100d003507031041c401e558420254000403d96018110958203030305a028000d040c06008030f0b400407616480c0c10038002c1c046151690765503929031420300c03101d041c443c015007032521805401004000e0b4a6000502140090700a070400f540c0e041502d078107503407034400c00418803120000442d00009268002404000b102e010791030074490355460000b00368941c6104105200f242603402050f00d40703e140c5081841140c17168400312890181022002442d41e000b2040e40c814612000034040700d071711024404a070503541504410300c295411640000d486c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 533197275 1250 533196025 533196029
    0x2030405151308071403040b130608221106182b080d0204030210030903020d1806050a031112071701150509060d05100f170705010c02010207080d0c0b09060709 70
    0x1c1400b0602c030302404800070514400b4942001187e50f981c1d542c0540c007600d50070030320a106404000032800100700340102c600c0ca10a80e03044040d00002004104c0c0d040b11101d034007009443c09007450384041e0042c0c9540005003654200008140d040c030b51714000301710038440120310525207010500b02e80c07414103500e0201c0028980c2e1020705070b0380380c01e04284110000d0003180e00c081e41c001180c1503080b01040d05079008070700c00c901950a950220100700c000740c80000701e1000c045200d000c00c103400c100301480354018010000c16440d0111780c002c8802109170740c0d900700f4103d428503107100c03005200324290441d503001b0400f29643e00c40c400c00d41c1360440c00d030b5030707a4402c081c084144030000030300c03125955070720044802201c0c4002c4100941e0408030340e4042801c425024010781030115200104007059030100007a40d8400c120003d001040c20702004403030f054010b4408a06503c40c145001c030f03040d0000c1c0265140381103160380b0304901d104541040c11170080064800c2c0f2180d00701c00103001042c0e0b482000001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 533198525 1250 533197275 533197283
    0x115080c0619030921080f15101d1e010201140c370e04050a02040f0b07020d02060409050412050c0d0806012025060512090304050406030303020304051513 68
    0xc00340c1160400c050400d01706032000750001c4070043c201a02a410481c424041c0c6d4251381003071015980c000030310501d00444007413260f01840c0200401a40ca22910520301c2a0403006500e903d41c010b40c10104120009a66000302c0401b9110b175450200c0d41c1c2403141e50041408461081d64904181c625005075110f03144500c03040070080110501d00f04001201c151075889681c28825816280c040000c1001d000c18603240e10482c24200814411501402500d0681d000d0b170203900d202d245058001041a0f21500d82260401504d4200d40b0260b65240c0203000100310303000002c58545854075205003107000f030500490600c40c00f03100c1d01c10920380000b8408803074039240c14413610940300c10780103903521881902c040120b64a0b42d003510304980000714590070204403000142103056800c500c140c055900d140107034000100140b10815140041030340b0182c002c01c0035420340c0d141c552200d0209043d111160002e501103500013003403008005041018550501420700c0056050030450544138242540d00c101030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 533199775 1250 533198525 533198531
    0x60504240b07030e121507140d05060d02040c02030c07050a1503020a0c02130b0108100608130812072a05190c080d09060906030b01020d03021b0115080c061903 70
    0x501051300818003003607140c00042078603000203980e13440d140c0d845034100b04071660000b04102040c806409101d4500292030044919030400210207101c41c01881300400c9240c3c4006140b00c584056180d512440060f1605ca50295945144044040d4688102d50740224000d03074207400204075070300c02c000300a44040b403107240140c3c1d19409004120340c54241d500c4043c1d449108101070003076016030342e40074840340042a07c418146584900f54000f07602210310070341c4c000c5040e440c00140312050814041c4080e0b44100926410441c0d02c0c40b40350201c0d4001c440c100c000c10361310300c400b0080a12051001140c28070211020190002c50395405031a00d615129015000ca0200003a03410000783d807260340007511422007140c0f141d420010340204142c01c90300c51a8003103003030941e0200f04507201e4041c04c0640d06c1d068004101c540895030040f0000d40c0000035641080e9402c41c0720b90303007864003030180154044924400c60112030601d0f01980c1003509031089140f00700004c0080082402d01c201d10b401d00380119003000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 533201025 1250 533199775 533199787
    0xe0402011b060b151305090402060a0c0f0c03061401211101030b060f1809010305150604090602121b04260a08071b15021f0605040609060504240b 64
    0x40c002030101c9240743c1c0d0b88030107501510041811103502601102039114104501a5a100107025956100f0b17a800781d0030280401503910600c1c000c00001ca000c5120b4100600513038240d464100d0340c1c80c0543c1040301e44030785036040c0c00380d164581c00080b030140c21941b4203030b2441c850340d0f406d80c5203080706d10000503d004000c00d900320440c0e000e607005c5094407001808080e81c900c1862111b00340e5501a0314180410352070b007005072065007400c2c4c081c1c40c141ea034054014480c000380101e940351607000080c4400c0d03011340c5a80700100001d00340e001a10038501c1c0c0140450950402008010f40454521a4002c640b1424402040b40700d03802c01561541e60448126403042021188065003081c01d0100054140303c00014842c040140707440d1039604484140a03804c0c0c007242c072104903009000802c40c1d04801640202c0215040340801d4004106140c02d40500103400780d41d0343c0215003554004e500130360415548640c104010305040c0104099a0b009110302000718076018402c021044250042d007521103004101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 533202275 1250 533201025 533201033
    0xa051f021002070503030f0f1b070609060606170c130501080402040f0207050d0e040c05030619030501061511030a0927050103060207050d0f080a150f0603060f0e0402011b 75
    0x903030440000c29400940d43c501c1c40e420038942d0381e4030035074003c1078280305030300010310b454082d0620600449007100030144460420300001c00b190007642c400d0703440c0359540c604080000c3c0144100001800c0c00d8880d05010002980343c1e62540b4001800310b4420501044035424080c50b0704c440c5000d0380c00908141c0510341302c50004c2001017110034600059503100048150512030005050600d244259403541d484140c15418403041d2822100c2d24004242c05001285c400e1810782c1c0c03901c05e5106021a401c00b841da0701d807109825120305602460881141005d000380007503101048814100b4400e00861401d0b050074001400945944101c11120240c117540e031b46c8074280d000001c01c001c031004000f8822542c584c1450300095000440c22a6a803003071413401c807545400740300101e441e04007035102c6550550f241c8a1420281c07030010791149442d00080d401041188803542d00c80040c080b10b68000a280341401d04802c00c4a45903000400c440386402c08210050707a022000741c00342d00030807801281683c2c007458 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 533203525 1250 533202275 533202283
    0x180105070c1515120819030608030906071a101e210f05060702030d0b030a150506040617010e0c030f122b0f0c0f23040b0a0302180a051f02 61
    0x250004d54512164a01401205409032880c54a0344017118030502c0004000e07812a13040b0300c200c40d600d400602c002000c4c0c0c07410401405415004000003c520685040400c0440608844000340b42c00040c03001c1c00000b040c00341090400a020909401c464101111180001207d400394080c101d83c0c50304070020041c4035405c0890300c5500070b00300d07459403d1110000c0c0d2290000084200510f203000301041e2149400501c007040c03981c0045c1070004015070700400030080e01c4000e21946d000f03a110840007485800c2e542081116845c08800000c41d4503910f90714509203841491401e02ca603010a8034103800c00342c0030907904114128801d21641d44d2250704240f80005035200c251101d81548800341c187d07184010f81202c0d60000d0031030f00c200060003003547c003a6504041d10868000190144501000c91040480a001c40b920318920650401e5981e09000d4480d034000e04000780080c0d00818075942c00100e144900540e5002103805016090411300450107042000906c2c2c2001d4019032096120b0f0740c001c1c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 533204775 1250 533203525 533203529
    0x90302030709051e0703060311180a050403030209130902090604110f07020a030b0124441305060f07141b060106030c0e040c09050105071a180105070c1515 68
    0x214500644d03151041001d0001d1449101c281e8a08001842c003980901c0c200070910700311011205140800c2e125401680010100107004405055080002042a0303940c0364100204045418005c51101114414815130380c1c40504030354066400d10100301d9500101c5002d64162058000450703848202c2800000c7d190381e0325a00207450b0301d00c480000700d030762501003105803a0101c815000c0c0e02d0440c0782d0038041307400710200c4608404401102016a80c00800448400341c0000d9100c0c1894500981c600d00c482054025514084070b82603466a400401c131041c010254403c200407e126428613203030002510f0380301c0540e5000c00c41e080000d5108401a400350448042001c0002210b813036686600c00940201a000711400c0403506510401340107140901800801e040c0710390b41c4100a61501c80155100d8001e10300413141c0c6210540e0800141c0001c1410030320420045001201e40d0030011921801c54101400c010304002f410303401040030500d60010604a0714201c240022129440d5010007143c040e1a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 533206025 1250 533204775 533204821
    0x204030b04030801152a03111903110a0302120f12073b0d0507090c02010c090b160206180306040507030302010e03030f0114130f1401050109030203070905 68
    0x110103000074103030f200c0301e214141d600000074a55203182d5044169903812821201c070840100c00c808000b918040d400340d1a290303611900300200340903040c1c00024109282c80200380d070700b83d000c00c0c0000181503110b0f00384c40000101902801402902c1d460094644030f00f00119005c01c000050070300003410440044803900403030280088050f007403005008141242d059050210303441102c0385403072003da2613000d10f812078103841000920901568240100e007801c070301c8203031400e0158280006503a0960b008203a410000ba0b4000100c01580c200302404181643d0800c05818005006007010784012850655803e80c0460308241c84942078411840303901d01a140c580e4140c00791209000070001c00140d01c205a074402c0c0c0003032210340103403401c280e0b80c1d0204449001c581c0303580300c0040002c1480501c015200300400b074128680b48141c109004180d0305401d0384000906e03a540c07507000e00e042800911031301602007481c11030305240c80d54000a81d24003c0e03000b0315000d585d0311404140703400c0d580302a0004807901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 533207275 1250 533206025 533206043
    0x30501050412121a1c0b04050604020112020405090a0e0c0303210114130b0a050603040305030703050f1003083702010f020306011b02030c190918030906050d020403 72
    0x2441c2848045445a500d000030503e2150070302401007090090302c6000c0c19034101e00c604403011a04010580d04900d008158448200052502040d0907224503071150780100001c00c12420702d40b00041c03c0f0070907105441a068414803050082c0e035103806d00160408607541c0b0204a03a00040016420b11600d140c2d0396a05120019082c5a00540c080840070300c00c42c103030032502040c0e1b43c0e031100407420205101c0c1c2e954011b210380e80c16410348030654084848008050491b0444075203a40203d0525441910103401207800441003010003603150240580c8031303610800c802034504190006040d41301160100514010300410070110b00c0302a04443c010001468441d5518410410f103010310300381d01d8508400c015400c060b10420469400d0085901a600603543d510343c4942c01892810a46070071141260b240c0141101480030340c0d91001c468012070350300e20311210400d2401e00c0220032207104488000d400301e90300f08018040386d00000d03804112555814038035550b106134a403500c001d1165800040c58802 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 533208525 1250 533207275 533207281
    0x9010e0c09300106050a05060307180f033503060d05011806020415530108161a160501090501020d0c1112090f0915030d171f03050105 59
    0x940519480b00410b07840c0c0200140c40d119002d00c00d071106180a52600003108001042e041441825030740f90f80640492822102a1100790b40620351400e9070041da50481c0c50010880300342c1290607003980c2040d89030300ba41d138161031007100a4201e000c002c0c86c8038821500f450480003440420342001c80482640c14aa080c030656501d4400000e400502400e5105c80300c40111660076030045004290340d0301140303900c6400704540029880c031641e03038500c41d4941d40d040c0b007003c5400c28000c402d130944a000c1002e0308541c56050035001854045520420006404018810041b071031020080d690203024003c032265036820f515030008804940ca000007010780d0318040d619401d01806502030310b4202903840c81031044100e034010854802c5104040000c85811000d80012002507180c014124000c01400ca41030320300079040000c0540c1c0c000c0320504a0480b0138441d00055140074001c1e140800030038107040b901e01003144101c0c16003040003002106500581c3d11711244060f80644a00d00641e4400d00900040c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 533209775 1250 533208525 533208589
    0x5030715022109100c15050a0f0902130504020102070e0f09060106110d03052211040b040c0903031b02060705011a031f020304080915031509010e0c09 66
    0x610816025001030044020028411010340000c0940410424800f41030440031801c00200340d60640159080c098440c0f94640001c02c501908020159402400102c901d0a880000291100515260f03d001d1404519400507038410800c4c0d00c0314803044800048030782d110310050b803500c0c00310b400c00e40c2e0614461040003414540071040503c15140c1c50143e806599039007206840b0b24428424000540c0c002400103014103109a21441d4480c2d001c407a02c900c3e0704c580d982010303d500891903041d00ca51b071205401c0541400c3c036005a01c83c110042d1420811421240801410344003540802800c00403a28040d07525018001d0800000540090040d0350340c0d00c1c2c900d40701d070003000d640042c50294000705000a04516021501200d01c0c0d0701e06c1b07401c100c0845149034000c0203520060040707070248402e0020b1501c0b5190403d500c0c1c58409080009035507030800d4040c2c03072010a60500407a200e0001607006001c0000901102a041400c000000342c83c1c084410004000c1c202440319500c90340400c0f80441016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 533211025 1250 533209775 533209799
    0xf0e0601180f090c05040218040e030901020f03071e060f140105010f0206040309151e0f17060f040c050d05090106151103040b07030908030408010227030a1407050307 73
    0x38455a030340401c80400a0400b400996031000343c05000c05240c00ca0412107424203800030580c2d81421800900080000d00000f0100d038900d00c000b24170b650022921440c3ea5804207c03042d0500540e2000f14280175841e40ea064100402420100c0484e41d200b04490401405030401c2c640010031210511407600c07011107216041d803091207041e002030789444c200b240481c004a000f60050b03030142c1d10300041320f00b40081c4045030301550b00610108182941361848410060b002860040c030705a81e901da010600e0340c40200800480452116072807269400c1c0607069560807040b2146010644002c2082000307003005551900500a00318140c50900081214400040d0711440c00c0d2249000304e01d41c50100441c040301c04207440034a4030f11310340c01008107010f50245100548140b82c441c0c9807400780c4d00e8545001078110703001940a003080760b4010a80c1c43e142e0061660152085880000340b400344a07000c0d0000b6550080050041c1809080b652113071103002c02880010041d00b4043d080350300096881c0710100503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 533212275 1250 533211025 533211059
    0x1b032d0209040c110a02190b0301180e2e020f0d05010e070309020303040e040f05030c2805030a0e12070303050c10020c0601031217070806010306140307090f0e0601 72
    0x801c0d450454a40005030044014204840c4c0d880001c1104002503824810b03480d000d00a040d0290025030310028a01c502e44004501070400d02498406003203040031404292040030075460030310340000130805102d144280c036114144c01f40c0e24419001e4030070845454001c1c8640e0748642c0030424002800c462881d40e90b00078a040780c0c00c402034503000f6a6215400c17411690b038044025450b420820007040b44440708011071ba0824042d81e030050700081560703921883c51b070040030b5910064000001d100d00c0e1110b00641c0340c0032400098403002c7c0c54411980e9003a00c2c0d01c905150101880700903c610000e68464a80c1e07140384a500c0412152003e40303d040280c41c2d41c000e0101d4542034442c10a00c46130034583d6009650814040400610950b400c60740c035078044140001d4034104114603c6580034001e00e01c5000c81c3e000e41943d07180c400130750074401c00060a494003604020380c030900f14050181c0f503480c0010340030704076113202c0000103068182c45524009000e01010004540c4140b20012911102240306458 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 533213525 1250 533212275 533212279
    0xc090a03050c09010f0b18150307021c08041a28090209100b070b07030b2e110705130b1002030909150d060209010c060c20011b032d0209 60
    0x1485a0383c50101001600c600c0c000e02c0e101c42c1d0203100e4410112000003169000c0700c40180f0740c0412811103801907523650422038010005038841c664800586181070f0707115108004603d0401014a45529a401e04458449503161450154400a00c0718140c5660000e02c804403141086101c0c202112020080c0503d080268400d4402e00042201110903141d1a82164110344c4e1a0342404455259051b4000d002040d09040c0342d22072183d40540d40e034500103c40442c10003100c20b00d41c203c81d0780200000801400119003400703e0000c21203d500300008860003221030440d0b05400006441c4d50f20006808404185034101410322010741e1207980100c050040030300195445000390790b0f8026500b4499040b400242e42026403c0100004201e00e0b40080401c00c4040c1082c85200c1030780c1d550403088070002d91b104000508200003000342001080000440f0804200003800f00b0381d6044400d0303041c04040400b01c0305166071b40300b0b26401161b030310303480ca20740303401802c250103442c0134091048000c2d5200e0030781d0314 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 533214775 1250 533213525 533213539
    0x50a081308011a04051b0f04060e30070801050f060102061e070c03110a0b06090601030905190c150f030f050c030a05060f12100614060a05030c090a03050c 68
    0x7040805052065190580084110ba55914010b105000003008007400d03c3c08480c0e181e031003100c4c0d203080010003020788642d4148001e54030303881c000c00180070341e241c0c1000c01c0c0710ba0300300308000c0b030001b00c00310501d8114105006504c046d03500000c5030328545a019031080c655075090004012400002c04001c0e44034500a8098450a543d207001c45c80d10a403100300c80500c5520407201007074449100380c04125655200303051400440f000e1040eaa4500000d0040459404a8440421815061180560740c000030203003401d200c81d500958401c0d8503031b000c605020401c001280d11003001e000e06200414020140710024446800b40940020182802c00318071902003420010003200210356403040c1403149030040340c0141191a600b0115029140251a403980b18604107500070407580c0300c04e14118484100002840c0112080b0840d0b000c0e070b103107079100d0311a00f07080c60b40d035440ca91038000c22200f001c101460300c540e4030790310104051264050416a42d800640610001c400c1045c001801030724404c08417080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 533216025 1250 533214775 533214779
    0x1d031c0806190303140a0e0d0f030e0105211b0a08071107060e040f0906050a0c110f0706050703020106120c030620091c1b050a06030e030f07030c050a0813 68
    0x100042900b5448010000740c081c1d0741c1c003a501a0704c00c01603d03241e0010300e02403c00190003400140d80f241e81c076206580009080422100b01600840c2c0e451a600d0b00b801c00500740f00c0302c001c50340c00e41016452504410310006000a00e0420311b1501c402040c4250404151103034081c800043c81a0700c02c41e43c2c4000315004d1501850903031000205081142c82d41d6441e500032002607030a1002501d8104403447c0700988400d80b06000482038040c5c1446108445000100340d07103140801026881903409006554109182031115001d010820070b0607250b19090142c1c4c2e45644d81760890041c0881c1e40001040e540240003441041404038411040364010b50f828070803000e00207032100c0640c48415034185d224100704201080390602c1d2034242c50740303201e041b4480c15041c100d481e0f415907070208081401e81c1c00043c4405016a160010383c8102401d107900e01006588154000d580e5203110385920a10203007804188001054400e2010300303d45c0742d00c40c0c00d41e090164507140c0385000b6001104424502040c0d0240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 533217275 1250 533216025 533216059
    0x3040503250f110609091501021b060304060506061b0703061a0a05102601060320040b0f0d020c01090c05030a0b0402041a0d0c0305011104061d031c0806 67
    0x2180034800d03040101000c0381c0420390340f01008800048400b9400c50402e00214103559583c180c00b5205407103a0740707040c8601c001c0c1c100081c10704041001180d0f444540560406403030b1110b005495015500200000f1540c03030b40e90000d00c0c1400b9008062001c0b90000c0c9159403c003401188940c01c89120300c41c180030701442081e01d0951030498200058206011130402c2000b813404100540000249041503a8051094102038600703203001d11341e032002140e6240040100c40d43c0351294001903546402e90105031403003982003075154801c6224101d041c280c01f15414180607a13070401c444905002d460215035541c8444051400b0700440036060f070303894040c100000703100d00700400c07000046580015007803032585d515800c0100414802c8278140c445070380e4030420416601c0d94641074400d5400344552003080c5196180003800e4030f800b03003a07110070400c092004225464010103121036601e08041802c0e004440c40010034900510000c940018510628071401c3c0f00e82c0020405029400964a0305604024030385 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 533218525 1250 533217275 533217337
    0xc0d090f0909050604230d020606120f061303090512010510081b300a0501150b03061c050102030c07060b10050306060c010605091608071416030309060203040503 71
    0xd00946644c10481c009000680700030841c040105a80340403c1d0700781070303001380e140c0341000168200001d03a0000f820b202d85803134030342030011396410050000c014094001400c191102406441c17404c030514015040d001f09401044228090400607005180040c146058103010b00780a8079800d00300c81c281ca8000c00d240c1030109230340080c4030134980829600e503c00c00034092002d50038208200c1c0d003818080080d003810005808411030100b1540140710300240c80c101142180c110703003162607240c04404410040d9015250580c0da002200b140c405540304039110074250714188160b80208030354400020409648a07080181000e0380c0248820481c1202000070302034130300c15442c0e84802003041400003c6440c5800c3c4018041d07940c00e8800030485c01d5840c00030482c0b188041e100b1718044010700c480044007560102444c1c0d4000014135140c1000d40c4e104503074086a200302c0d80d14030300c0d40c82e11400560a01d40240c0203407003400d80c404011550391901d801c10070f03143c2e045110401c0c140c00c556202443d640d48662 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 533219775 1250 533218525 533218541
    0x403032901080105100c0204090308041205030108190312060920040506122203020c100f0c0209100b030103050f0706140301050d0c0b1c06050109060c12050c0d090f09 73
    0xb848015299081600b0440000c090080c8a410440260340c03c0d0010b03100c40c0a081c1000303209881c0d4001d01c0c2400e180841310315043d0040902041018001003090603800511303c0e4819180c180d64414282942c1070448403041c5a404541059041490014020115520071640c0c0c155103c07940404c0c550002d40102c09101d98410076078044402d001800c000c02c03040f403c4070703004200c0150401d018581d2310b40c61054451005c13015000750b04144044001d070305240c0ca518540d481186010607001d5044240a0901d280d0940702274000c41c0310100003909142c009010750080c01e204015035031213603036038502150740307840070202d02c5c2a5003d14140081c140d40121201c1000d10000300095003947e00700300512a8014a24074151502c4241040015503440740300024000007a0500b0a50422034503035041606a400c0c0b41c1c06a8100084c0703050800c0b001e5072001440100039400400c001e6800010141100c00303005a0b940c1c64a5801120180403500340c00c01c20f014101c0c0c40e104404401c1640d154282c00c04c6400e02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 533221025 1250 533219775 533219777
    0x70909030207210f0506040201090506040302060d0e01060f1e06030e030a0c020f06040e09011a030a030c05010912200a0c05090a380916080c0904050403032901 70
    0x280c1824824400c10034001c0c3c04005040350745425003021920796042c030103074900c1c040c0c1e07403a0090000d00c015564000d14510180c0815607040e4500b51442c2e0200c3d8007072055003008060203540300100c0310718010a4110000612141207000b407420f4884a6090341c030103036100c51210288001000240d82ea0180c05001d0044046402443c105451108165082d8159401c08c0b41d0020710044103031450796602002e40081c1140980010f0545400e800680c2100c600569008050180e03449411056900084210030a41d041c0340094803c440c030b141c12030241107003001c020300100d1203544c40b0f80501e900c441245001c3c00c1124011208150b260009511001440d0007d046c0304c0385070405001c142850000b045c0c11180c4000d000074814000c2018451101d603d05804145c03d040c0c42d0b101c03444601d1040401280101140c41c0c60280c1003c0301d4035620007030303202d05940900200d40002000b210a450a1361080725002e801030281e8601450010300420241048400890254140c80e4000c1d0346501030340240541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 533222275 1250 533221025 533221033
    0x402010903080a0915030507121103070507060608030a030902010f08040305030a1e05150109050315012c0f0604270312060302060c010c2007030201030207080705011d0709090302 78
    0x110b4650a80340d0b0f2001c6250002d014190030001405411401007600d004450b5800250318242001d00500041d62224480500d60900580d41000b007902800c5980084c46400d1269495000f860702601500c559840702c07405010114030000c80c180c03d6004407401e00e00c01d984d807c01468028070181d0b410702e0190b4000d00041d40a00000e201606a0340c02407505c0c1040504d079200480485030b8840503542f08071110004400c10410b030307500558021056030040c00088000d42213120048801d000000700521510000d4a006421142d605103006a80c1070b40c0034030701c41b0303022003031410f2180010551820b695090040349000c2c3c407000221241e44840d0a9244040c211404810403900c04076442071800b003007101e00c259144d00010060341c64400504050852900120342041d8a91000d03080344018101d0182c02907081e800c07070003030400200e041e01c1501c2e03090070016110302d464100014032f4040d850000303200d507203024040c541110a08a02c0c0c601041150700321000d0944807050441500e039000d00090140e80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 533223525 1250 533222275 533222279
    0x60e0907020d2a03021608011e020714030d060510030e03031302031c02060a0c030b01140d0209040603051605030309030703031103072a120b070f0c0b07020304051804020109 76
    0xf2158036000115040e5880a0850090a0b106090f0988120700210050390081c00400c2d4000c400e00c1c2c40300c00405900c0c0080041d9210900001180503028141580e0180c7c0001d80ca801c11007181100c503900242d4001712615550144c40c03450041140d800364a104000340018240e03102d20a008500e40680c1c26006542942c68190392081d01a040302802c992500450100b03183e01003140440010704041d5500070695070600420710000c88240b0305605c010141891414039850360085c803003002054848200075900c51180d08442e000340102186168024205030000052020000d4803001c07040002c02c6070003803139030340c0c1c41056540c0c89071403030150301500a0801003001c00d0290080105445e8007000b600d19210f55a40c403070308030568981d02c101c844908400c40728400c004089500307024003048129150740011076103c0e0032110400800120070000c6503964054490701c65202803a00303c1d03000011b02c0b05400c000c4006502c03034000e40550740c0200c0400c900c1800d0280a114000d0180380c041e181e42143d28 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 533224775 1250 533223525 533223527
    0x3010b060901121e090320060f1b130303172703070b07050c06070206010b030f1f180f150504050702190f0209090a150b0a09050a06060e0907020d 64
    0x40f0700d41d5003195140d6601c059000c400ea1265228100000c03c1c0e40003c040c0c04900d409000c00071025000250311152412a000350600000c046402c116041e803510742950391440b000107005a1171460402082d80402d00c6e210102c81d001d0740f201034030300c2510342d031403081300510b2081c013900412110f0240602d000260340d04030f541c1c00074494006001900950785005030310380310403903070312030958081000507400070b0810074491051204a4220795103102900311549444841c501c5400041d20740007104000b0303404503403844504549030b000c0c0c0c3d0002d0100c030403440d622a0b882010302a0905840d20242c14405140e103101c2141c4101c00c0440d8900d106035141c1810842404001c100c018189010742c495901e40101c400000200000b069201d0704601050b1074041c81400360720000076064114540c044415000055060b900c29400c040c00385800080018107640091391040f425806030707401a2904042c0100d02081e60041c6090700d42c181c03500d1b116500141c060082d001802c960580041e000303080c0404d022 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 533226025 1250 533224775 533224787
    0x601050618061605010c09140108071b05010606080702010b1e0307030b091b040216061e020d0204290a052a0f0105090102040501020a020f030f07080a03090503010b060901 75
    0x42201c000e020303039074184010003160700c2c1d038840c004000506550284031030400400f4051111121810b1605160f100c0c1783c0740840700400b003111011410f0121070300008010510803085024541141004840c0c02c1c0c80b1824054001c3c40203005100c000f941590009020b02c0c014050f01d003d80c0c0c0302400e501c0c28442e20240381c1e41c002d6101c000713599040c0581c00700000410480c10798540100c544a002d880ca0b0181d506160000c0303842c1e04045406180140101410440d18880c004d80c580d0300b1030000309441040e8811080910681c131450300c801c0b40301240c215980c80d0380364050307c03d913282d0503030032860302c00340c1500c031039411514001c45d0384020f408204250880c1c0c80b82025042c909005803107403111026281c0c88540d40b8016141d848016800361070380103006d41090080541010040000310714260420380001d440d90080d00c80640510710101c0408002d8508201000c003164200040d0b0301d4094503000000d1300c8520b115019400a2030324800440d8038038040c880e080c90407900400841c54205104019622 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 533227275 1250 533226025 533226037
    0x7090902071401050c04080615010c0b0a090b09030d0605090f190908040b030a0b01032007050a1b24021e3d0905100e03040906240e0306010506 63
    0x6420b60420401c40c60090040c0f90041d40152425500d443c02e0281180c9000d074010001058035007441c0c41e070820350740c001d014040e000340c204410040c1399503840d001601a0085020080110b15580300304541202c01002803d8141c2100905105e196a13420800c240d40c1c1042e80c0d0b004011000d04003080d500e04040403200186090090701080340980e545403000f00d40c2007503000385e0740c84100008000300460710307118602c000030f400d00b4104103045c01110b0000c0c12000da89180707480250002100420300508006040720036610213082c0380c41c0300721424500005009486590f5030350118501c5415100300310310032141c1481d40350f401818885040d05450500f035000c60030065041c00703104000300405c0404d17103104801403151030380154501441c80c240c402c08811540440701c0340745003900e0080000c4011078041e40d08482c81101158500c0c04070f103214154440da0b8065015203140c16400508c41904221404044400505610285008072001d0721042002c0e00d01d20707410341050300180010700c0c14002903c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 533228525 1250 533227275 533227283
    0x10501080c190314060403030605010c0510020c01060b04120611070807020904020609060d0515060f04030b0606040b0d0902010e0105160b0406021902010e0705030d020a0305090301090c03080318060709090207 91
    0x1c0641c0d601d460313444141d004114a199260011401c00041c1900b60040e40002e010038070b0844a1a03c150322401d8a800c403031544d8030340903600010507404801003500100082d00c880d05845aa03150b03550403076200001000c2d01140d42d0f0342414110f102080340c100c15143c2990f00404414904001da0b42000058000144100d91202c001e00c0441100c1e00d800d005400d82c0d84078034000250500301030001e1000001301140b02d6208410400c05c0c02c48440c4a1020f5400f1654004407201c2143c0716840062458010364000c4444a0808034440e5044140b5400c02a410360007030303c3c1d00c5000140100111928410600c503821700c082ca51201400180d4107e40342175202c0d00940005041c12503001c1c03440d00e6040c801018000503910b40200140ca8081803001c24001e0204400518203c18000d10103034880d01c420101078240100030420014548003034021000c1c0e6540315400895164a91420650039001554008c000400152510502510004059014042c3c03911107443c20380c90a8030410281d030003984112 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 533229775 1250 533228525 533228569
    0x50a03081312050d08010503070501051c0924110708030f0601020a080a0f08100608013008071a04030228021234051201090f0308090106050102010501080c 68
    0x44102d214212200503601c1079010b407080100c154801030406006800040c402d41003840100856a001402c40b903040301c01c41408641115248404002000000ca010b0605003c8503000c001c6418860044601e54002340400c010204140340300210718000c40b00c0c01098050100f0105060a50403980d5984c440170502c122407002015a441c11082d030055010240071032010b9094004003038021409a5000c0300f165a00c020740c82c60202e00412161040c400d407100d0102c014a410442050581c41414204199004003500000b62900251aa00904c0c069a610200084142d100e503540310034580074581590040c501c19aa081051400e21584a001880c001b480b070490801602e460b001c0004640382600901a0700e405141d403460070000400c102071601624900742c025002c02d80c080c20040d2401640c000c00c3e40240e8485903130061044c100054800c00d09181d0b03502c00c15a20500007441582d001e4000c1c4106030f55880168280c83c03080c0a40e51940d04011101c510074100203201c400f80d401140650 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 533231025 1250 533229775 533229779
    0x325090905031c0f060b1c050907120305160c05040e0a050607051b060406020a112107170c0609010b04090803040f21050c062d0a020f1606050c04050a030813 69
    0xf000720b90b0150300203006c2c0c64012517950081c3e144c3e03684141041742958028802480c0c86881a6100ca44e50b00481c054003c0030110796040c107100d0307400d458075034100e00c0080040110710300f0030100700c2c5681e100301803099042c8480060350034001f1071100380711580500140201d40b6482d00c1542c035600143c5004820105803c07500800b481e00300116030049004000c016590b910000005100c080c813030b1030055180d40030316050000f0040f02e1a4800c421108282d0f1581c030340c0d03064030301815001c0c0c1440c0f041003000404141c030002c0b0140070034000d026007034001c000c0182d55030010902c404e035a80c100000c2c10444003480040c000c54030301a8280015403092034200c0c10003840f03c0c40f01702a40c034080d01c1ca8002660229000d0032260703042100700c0d004000204c44104803604000308905800500441c0b074000564440031a90322070f869010382d174003a00e481d004251101500403645030a1480903205455090070038020034440000315044400303a410180c05503040c1070442d11048215408809610380701c100402c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 533232275 1250 533231025 533231051
    0x1005091002070305120c040e040305070302030715050f07020d022a0402030f0f0a110a120e060903370f050409050127060501120b0d020325090905031c 66
    0x916105120744ca4580d20340b070546061404854004040c2030404008100a00001c0d0802c00a5036010741e05180256480e0400d182c120b0850251010040c402410604040043d6003207401492086400a011280655400408980da16112401c520140c2c010b050b0303141100700485003803400200718440344100113411f40c021508a030301c11102ca282c14880d050a000c501c10004000f02d4000c2d0300c41b007003402800241150320307105208a503a030300c05101c000d10a000c0c17254950340042811030135601c1560350302c0c5400a501d545a0380810105609001c0d0f00c1412103400d55280d0b044d80714540e10360303c03d050100000c8402d9030b044c40c40da40c60409014041c80001100e858070b0003942c0c06000a407000c1c500340140740d00f098848400e5014858180ca040901c2445a40da0200442503040c51540700802c80b09c03520350120700045201c0c0c070080d425002d00003005108100d00c50301c00081304a075a684001660b81c4490800858600c1030340100160010000440d511000401c83d41c000c5440c05000070b800405a00c2e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 533233525 1250 533232275 533232277
    0xf1b0312182c0c0a0f02011a13090b04060203070f0810030828020c04110702130f0906050a051e040305270907020109031101020f0f070602040e0f06211005091002 71
    0x41d40003d0a03000080100701168040e110720718070801400248400c139030503a8610042c2408012260103800c1c1040e20020004c1349421400c80c1039000710303442181d0b08140c02c003400a540b0442d03031440401c1240f03c0154055100d06180d6200d0011483e5003402c003419a61070038002e0340a07050f04006419002c1130105100c029a00030b03000d042c0e00340c0091561403115001e01040e40d280c207159030b04c1481c0511640340940ca400c68850890020000300240c425140c01501d00281400700000d03120514143c20007606a443e03511050041c004490701e200d405c000c0d02d800b00c075048411240100021b805120740d01314811144d07000c1c10000c080320120a040340c04c0b4804510b039003008890020060b0346401c0390340281364029600d0f0741039200900003503192455454040490303200d000f50710003801100140100038400e207a070585000d02851403580080f801c02c1800d54003603500988255203e403080d8000f5003c0086032910990040135030070041c081c4071468882c51402044000c102d9685030003040758018034800b03a84 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 533234775 1250 533233525 533233531
    0x150311040f1517061203040801110904050c0f0a141204260c070302010e040f020a12050c03040f03030c2109030801080307080906070f1b0312182c 64
    0x300d400720075291180030800300110440a0042c0000f084910301d080b40c0510b40c41d40c3c40901640c404140d601d00c11115403a42c0300b0383c3d102d030364294a003a504600c12200c00380140040c0c0811101131200b03071141c0c0790000151048a96030f1004641c1006070512107405000407088015140702041d052801044100030980f0040b1011564650680301c420004414019070707074a04240c88400c2400c0c55100204541d403040540806814840c180702060030ba65203d822070361402142030300541d10f90340480d17006881c500c1d4008281240074103240c0000c10302514001940e1145800101281d40446152016002450702c1d0925400704101c80410380c0880c0189111521480d495400000d03920304182801448007006821034001343d00200406008130346103030b0555003440402c4070020360320300032413a000020302c1500500400101405c0d480801d28598400780c00d00300c90240e0202d548200340d035601180c101c1d401a4500280c08490302c0e09020080d81020028140b500b828404088000d2102e0b2084000d0310403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 533236025 1250 533234775 533234789
    0x15120f020c010c020c010f11010f1b020d0318080d020d112505030f0a090f06050a0e04020a200a1a0601030b19090b0a090903120b01140415031104 64
    0x108007900d20000d104250708040c0b0352000e42041c1003444002032040006207008020403562440a4245807001c0d4090800514000010401030541604d0800d5a81959500c1c0015014181550120134002e002c3e189140105950b5114011070b00c1d07440c80544d0f003202902d400d8031a8280545442a8071a200f0040711400c2000c80940340c11140940381c03010441320320f031825044c0c490740140c00066800019610081045030086444003e4003800302c40c55122a404001d101000b02c1000030081c1c1c00c20024091410b4a940300000c0d00054001e00042c2d20500102c1c1001031090303042030102000b4451010101001c003400d0782c40009280d15080705181d034603032603040580e4020050200c150b0b054454429041010f1b200340640700e48401c0fa000304000c580c4a000341d42c03605c844514100d95900c520140c007510340110704100c80b20032810010000c00b507075a0102c1c00c1c0380c81c10129140d1580951004e010881d05605964505800d01da880c00c011243c00b400c41041c5510b0341e4903410b40d03002e80000b920150003c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 533237275 1250 533236025 533236027
    0x190e0105160c081219230907030c0306020d0b0904031e0e030a170f0a0e12060103020102030307080901140a050f0705031605070c0e090f070e041e0516180b0a0602030415120f02 77
    0x484010306c6441c00000e000f102c11544040406c0000420a030321407405c990b0841d00050300c5501d0402441c01030444e000324582d000b840300c420441011f400c041c2c03e084005002401030950301070700038180e5a0030740550829078958854034038a40041c42e400000001c0e00520500c49003888041000b094003600242c02d0080407995a1040401a0500c1903460014080400007001c0710352441d00044d40340c0c4030207400401000344c00c40004c1c00d64042504071441c0706c00c80e090400403901c1c1c2042500018030b419100c8102c0200d115010440561185059030701805002000a0b480c103c1413206640c0c9500200088803500c1a81c03100161943c090b014040c41000400c0142030400c00004040c1c1c2003070400e0f0895034509403900140000b2403220080071004a07a00181c8203c2519075040072890513031090300401420641c0e0f2004500603100700000c030700c504480302c801e000b1038001604214410111b8068000164002d00081102903880510f1f24901c43c818103140d0b01020509070300b9026a04100e80341d00440360 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 533238525 1250 533237275 533237321
    0x10903081b10060608040b090a0209130201080a0903022d0a14060f19020d020903011506140403052805010204080c09060402130e190e0105160c081219 66
    0x1040c007030400719542c104401c000365801e00a0180c40000c01030000741c0600c0c01580000c04010b0104240c0300f1540d002400c12040e4900101d85203103024108404074001342c4450042803040da09801200c07046989074024040d6510200764920311205480d2400e009110b85014061305440b00b0302c84000e645e4020b402c0310b0902d512441c01e541c5000c0d400713880848018024420071071894281540c5600c9144150405692194140c641d080607000d00454035616500c1d00031038901988104022504982d0b2540714100d1047c40c80c6000760442c01640300150045d0041541c1074440b1000c00583c14800501926900d907134a010388440d401c907005a044041b595101000c01080c03898000c520560041c0c00326002e500c0c180e100c116141e502000c034403d0300d40c03c41d00a4040303984a00408168000044109405c01c1008400e44030740d80139180c1a2407448502d5089440709408512842801c02c0c01034110711a145041c003480303103118550b4401441514031155a04201c0250403150080051104445481d650040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 533239775 1250 533238525 533238577
    0x2100e0c04140c0403170d02030f0115050c120c07080304060503010f0e0105030a06050402030106120b01050405060d020d0f052b0909060f18020405060f0406080a151401090308 77
    0x21080220b000e1005a900d0812040c03401840454095991085401d2456000910041c495001d070200070b81d900d40c004002c03c14000b1182090718100c885000c200c083c000c01e08803040d1030034802e240718909260880c0b880070030300855010080010014880803200c40c0703691200000d003581c005402c41d100141001004102d03514104842c40d0150071760015205e040d51501700081e6403849071000041805803190001001d55400f90306c140f004240440c48a000700c60185450f0448800034054240710f40c1c40d241c04940300b81001d40306034040c03545c0982114000240b5881e656641c0c042c0d018111010300c100111341d001c1d4200700c204002401c3c039a100209600d01c3c095405425000301c1d0300f00030250b601c3c1c1441046006070002da41e8040b86c4100c54120a110817a01c0400b000e4403858018503040b1100041c00c0703007040b030040e0060044449503611840540c5960382968250f804a500410042815010500c04454102281c0d05c07000070505084000c03e50341c0e070780c2c011541c2201c00c20b0b0f84581842c800125840e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 533241025 1250 533239775 533239781
    0x601060801060507020915040f0207060f11041e0510030c02010c172214060402030d030b1f02150403020105060f010c0c060c02060f0f0405040e16031202100e0c04 71
    0x50101400d10380415810400001d1080c0201380d8040d10595281000c94201c3c0c414030b003101c0c400b40c0040d02c1800b1594450207a40040c2d4080642280d5651030300e0a1310100d066988513540c504141c403440c051500d0715180b07105001400380400c0d811907050f41d0400241c1a95071003c1034000d414140c4000c903003040c003060081c3c00c4818900d200024400f01d50910000000800031040e40a4203a083c07411007122076001c8411500c804980040c10702202a00060b546c020008040d44030f24402c40844d00700580e101d000301c060f04e1200b602a60000c2111810107000c0c80f5100cac5031980414584100c1c0d07030580381d1803400014a00c0a031804da0141c0d540e070b0280a01410400040740244000307080401c0602603943d01c01c02250582d01c509002c104a0500e03c0d02155508012544a000030500a80c1c0790802e8030440309465105124541c4101c0c40c181703020000d042c003c81c40c1c2103880c8400503400740452858590f0310001340501c44410443c06030003499481c6a402c0d01c551344107401707454010501c24200700c2c140011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 533242275 1250 533241025 533241029
    0xf0c3908100b22060531200d0207170a020304090203040303022203121b020409020f2116051e0a05130212060a030f12031b020105040302070509160c020a081e0601 71
    0x5500514200c00d20042184440790029440840004a00758440c04107180c180c0c5100103507d0680d0005a80c3c0c80703100080d005002da5600440740c1d11901440950017a01a2090303500c9000542c2003400b003000140720990107507900c03d001c0c0c2030142c41c0c91482c517103120743d0a400003502ca1800c1e031107140503c240081004610315664980c1090141c4043c0300070303c0c010400800030b00a00c01d07600c3e6200001113440d850a2a070302c0d10809005894070700c0c401c8000e589201c0000c500070f65140316020210b581440440451411a40c01070040310700c012000f1001c00828040590198000d031250380001110348403001c17a02c000f44451200144c40302c4803082c0302900000e0141c20306105a0240c0024800300741040d580e420354030781c04040d041310a41440c100358054040003e188085071308207602c0604490301034001c136100b5403080c1e0a5841c903d131540b0421080740e4041d2411040304080071900005180169540203040d40010001d0783c016070b441c0d02007881c00e00000c18107001045115000c03100e0060401407140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 533243525 1250 533242275 533242309
    0x25110706020d0e0d020d0803190e06010b0409201b100e0303010e09010e01090f0b0906010e0c180310021201080a02010804030f0c3908100b220605 64
    0xa40e08542503000b0003c016021481c0e108101d48020380c811035032444500032071950700c107041036140d1518441d0940100540082d804070300342080803000314441c000c2101c6042e5014880018101350903c4803110051104440311b01d010103d10780394568481d10343d0098540c180c1c07124105035042c040c50395501d040450242c1501c00440c107241c000748802001006030307419151401300701d500c550784048449014044180d9150740d5075203060002c03420f10440e0186075241c94000c00b2107030800d071501280b20340e80d54802d00c00c580041e05801c010034612520080103040b04101e0000741413086618200007400d01d00c0032044040303003e9000030002d07144543c021410340182101000b0f4641d007402034002a2111500910007000c114010041c2e02c4114014801c0c5c8040c00e2b00300a804000303140741d01c2c0c140040200c0031503655400040c10200f010f40305000314160243c0d1031940260812071500916240502040034240f81d0100e004240d0304400ca5004c001c8114004269402080c40c518000c10f01c0341069103902158 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 533244775 1250 533243525 533243533
    0x6030f05060604030228120201082202040513050f06150d0506040303021c0c0306090b101409210115050d2006040503070e061908060a052511070602 65
    0x80705550340d0805540840781c0686200260b85032031042502030010038080020045604c0d04040741c1e090113001441450f40c400c0e01d801d407440d1102012004104402000c810000c00c1031032010b801814035400a81d0802e0808030580b8001402d0741e01c05081c0090007116003119400f0341c0070000f507409840c091601104007074a50310204042503c40d6601c2c2d04000340068241500000c010040b040c5072401c02c50038425403101004030180504004009c1e04061141d061040d05022441d002e07850090201d00c0001040c4d19100d00706540507140e006590031658215500503c440134208070100d2074401480c0d0420030000010b031b80d01c0d0740380e00d895221a86401041c05510040741860001c1c0303000c50030b000301a00f4041c12081034030000c40025505e1103141c1120303415003e8503e0016980091006c00f9000322070444840040c000d02091880b041402ca1040300c28941c805004a80e0998a42d4007440d0407000d042180142d00c080582d10340406628181600b0001d0b401507008010704c1000e01460020340ba00b84050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 533246025 1250 533244775 533244781
    0x50a020303010905060d060c08040c092306030109060e071a040609060c061b0c021810030f050c0a0608010509091209011107050405072303040210110c0a0b030106030f05 74
    0x350399001c1400f484800076504c0340841c42507a51a2020300703005501c410103010640440800802003076041e02d08562600d0110400314145e6032501615652903a4078203944030441d02d1205000e03124102400254065588270703100790120783c482c054400d407215801c0041a1041c03415500300d99612111707003080c0c900a800d01052001d00d80c0080d2071021240a0300d46210501d1407424180010440026003002200c100800702107220b40044c50b542d402d43c0200c8120444100c81e00d55011040c03401c0304c000c0c0382414880030030b20000340d0301c46c01c254034580210300719540c00c031481004c80d09903583c03078200300040381d15000100b029203001000c031503126044d4409481c0c40b42d1482d01d068803a014001185060190b599001780e400340041081000800c8001c0003445541403105015060440000300750b0828079005295440c01908101240d02491b0301511094098120301c104541910003498849030500034141b004c5403035503031540e090010b810500001642c0b0b5242490260407241d0900811841605000c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 533247275 1250 533246025 533246027
    0x30507050403141504121407020609090403140c061801090f12030207170417070614030c040e0f070906030605090a09030e0901090204050f0a0b18030309060f19050a 72
    0x41e00c04599010a0759610350920b0210b481c102400d80603000c0c19a05081c0c20403050049800c002c0790300742d101380c9807500b1044148045030124400c2e11000b82d001081002203a5503420003150495000b80a440d002c0040c00c1c0f018142c0034554082410b55205520a40501640034043c96090440f09803400080104003a66039032036030000d0206c100904045054001c841019002e50121070303425a2151000c9090f142c0a01150242c0c0c04c14050f0032041050b4080c50595104005500f0042d1070329900e6010041e6901c10001034540e1008024106200043c00005080b04080c1c6201c2d002d43c4a02214008034608854010150b43c05507004100300350410f60f04101c2c1d0740b2001d200765002001d142010510030700c42c0c01d007503900c900c03072168040e00100400000101121298050401d50b00122206a03e8100b013501f0091140118040c4401d180340410014540d5040305120700c428a0014003076074200100300001034030640041208090882000035541c8000b000c0282d011403c2c005c80c2031050074070701e550760 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 533248525 1250 533247275 533247277
    0x60f060302030912032203021f0e0f0a17160204090515060901140f06070b18060903040605090402181e09090106030b0c280f0e0d020114160b0a06051003050705 70
    0xc00d2000d1b5500ca6140c4003458400d001050402d440300100014401c5440c0340500241017a040030003a5000b00080d501b540c45010841c20861030308005480708040052031241d0b2154403072200c2c070804a00220140005854a0190b4032a89000ea00642200c0d202c16880548020000384a6407150340071341c1c0140822007403005108040756054841c1075444000703a0216045116551020304940781901c00c01103124850401ca19103000c810050710100d4481d1118503650340202c0c010300c00455418005c1041e1401c0aa02521102c80d444800c0d0321003c207d04007041e11003505800c0c442146450941c0c0b0500e42c02e0009000360801807190003001000d14607250710f048484090800c3c02c0c030315800142070403896501d980d480c44885444001c54405800200003030f0450401c0c1c40e480300030a80d503140d060071900e060a110103010350183c44000280d031500311040c4440d4422121030000110704010203000c030701d80440d010711803001514001080303030030107041010442038110300004060801c0100b210480d4024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 533249775 1250 533248525 533248561
    0x403211e08070e0103090203030c030403120c1a0924090d0e0d0204050405030f030a1e0b01140c2a010e1c020f0f0d12030b0307050307030b0a060f06030203091203 71
    0x8641500c1c2c3d038842c000120701504d1034000107540b5104c08652404289000700c02001164482c01c107690030504050300c01d50f00c0d1404581c2c09400b51448903050151074411103000b90340103401c07205561001d607100070241c1e0684182c9219921143d2084100902000c0030410012028180d013000c091101c041000075191148450b0020b0250b600c90b80130404001080040c0c840300a8035030002d640340d00d04139a0f070700c0040c414a903e100105820000703416403090148200e443d2094103954580c440540f41c01108a554001700038440c040c441d03499902200800702880c80301d0213500510072130300302401c000014516851035807100c0c072491000b40c0384080210000f140480560b410317122090802c00c9080014219014154000c0e0016480300d882406c204285010126860301e9880410040a0306400e050345c80c1010f0064580540c403020f001c1c004142c10307164165100307007103000200c1e61030b45400d03e082c110050756002c440401d40220070702984100c00c0c480c40c0c049107002291282035141c030743d0400da0201904 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 533251025 1250 533249775 533249777
    0x3050d1106060f010c051515040c0c0f0c080706020609070902030108060114032409010f0204080a08090a120308040c0b1309020d0b04360b06150403211e0807 69
    0x31002900c03d603400340e100301e0307002030300507068500303940e4041c0d04114600c000700d65440c4030003c954041d03c1075250500c5505245420740c3e0751010188030a03070728840c501030100810b0310030003a12040041c40700700400808014100c0741d8050301450802d284918546822500301c1b4240b20300600c0140303c83c85000408a0445800340c09001440c6c0b0f425000c20b04210740c0b04980e5a50745038100c4612501c203c88c0a429000f45415002000f000c562003421508074011400340032141d400900440010618030006016503ca0040103c0643e640d03400c290001c00038804000ca0100304000c0070002404071500c0048000e2503107500c050300c2d00c0c02000ca440d00025040c010490000c1d4046000303a00390350b95500c100030a09000d4020003804403400d5401e80980e9641c05581204600c0d60351b40c2011032202440d141000742c3c4101101a103032600b40030002c001444500000d0b107074000b4480007000c03400e1070503682003141c0349010440941003000e40040450326485000592010024045001c107a8070401e103983c01006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 533252275 1250 533251025 533251039
    0x1302120a0f12050d05010902040311030f071206020f0c010504020901090c050910030f06030c0810020f0409020f0d1b081303020a2604030602090a051507020108060d0807030903050d110606 82
    0x880605481c24018400b50b410121719001c004241c2180e1503005105503400b80460b407000c030040a080554422192072040d081350410002049811040c42c2000040b500c00c0c003025080c06601c105411380d90f000300711001500c1c1c0d1a04140001c1d400d01203119809820065014046542100c00141a0780b06118105004150084440941902c0b0b68000b0300c5a50880b1402c1c042c1d03680e01d003802d4444004600455035240160480c507808201c3e68401c0f140040e04081c03207a401c0a00d00441c0d41c0094010080ca8040c03a14108801c5030400e800d031040b58100c0c1c0340540494a0b228500c00003c00f41800100941d120004105a60000c17070b400107814044280d114458802c0504180c20605d4211005d04189401c1e500200d00841041403540280c052a601510710300001e941d90810001c00e07c503000080040364000300240c3c00076501c90350003990701080c0a0400c00940509030b0b10030381a640300010070750020700d00d40300620411030700380020403510f819480c1980a420315003559941b10000a031903d403090f44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 533253525 1250 533252275 533252303
    0x80f0306010e090f0a0c09210204020c150405072c040c051005040806090c10030e01090c2402010209100309110a08060f06010215060f181302120a0f 65
    0x720852084036a8480502400001c4c201a002c030020140282c0b0802505410400d40b809840e100d840541c080700c070302c4110f210076400b20100302d500014691500b40d070042e8081080d191001420007000c088810480d107204854035090800758202851500405101c1c0600024038506610717800030110b4054401c0d44082d419155458503260b031b04150340c08103411030f0f50003901c101c4143e04040504101d82d609807d8070f00903541c510003191179500b02c640e00b5512440f81c10305e580d0494400d40c4403c510700d40b80e00c00028202d215885245403004680c3c88500c101802107540c15943c41c45118401d6025141c0c002036041444200000344034003220400c040402d652080c001d030030f00c042a0715846500d4000f52181e003015441d000100e456a00c04c80e825855201103d000c2802d41d4400641d540c40309041000300d821903120001000400034011000380c1d0b000340f11100d002028000c2c0052039010f00300d000e8a610210314148140980001d12100b1500d1942024030030b000803a03e211101009154081a101e41c411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 533254775 1250 533253525 533253527
    0x30e0f060d02090409120302181f050a0e13020c0c04060609120512030406021209070b04270606050903010b09090a0209070507080d090312021326010203090d0306050d080f030601 78
    0x101c05c0c480042d011039502c046002c10607070954014a2121a00c07441001901900e80078040304100303010040325101040c90010590501c03034005050703480080c0c03034028000c08030380d400940c94140c0c403042d802483e5400500301600c11020400e01800007400d8900b80806460401c02070300c200b07002c2c850702c102840d000134200204882486104208040c4028260b228185410040000c2d041600260001c0081f1000b01c0c0c409080010701800311141c2c400020304d003d0034840e82200c1c0c12550003200c0c5042201e4485010030604034044c0402824040e50b500303440d01908400c150940d0320941c00c45d8019134000e010f03c5000800410b03240d2542d41c050303030003003016100c2e080c0480b03240c810b41c80043c05015002c525001e503032040340c000c2c0140c5400f070784d210400b00710800100780c201c0c4260380d03d0010070541c40e01d041018001c0e84c10035459845106c0d024900020148011a003a6841124140a613400c400d684120443c4c140c41130201400e0143d40900808803a0703680c030f1265200b2031413201920a270110002e150361f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 533256025 1250 533254775 533254781
    0x1201140714070c09140105090c071b05060a0c0506100501090909031b050d02070b16020d050316050715050a0503070806131b030f05060d02090405100e0a030e0f060d020904 75
    0x106521840ca81095503451302040c0007080501960b2000e0883d000000900d407030710404240c0154071000c1c0342031810031b05691713040c4100a40c0c034444100744410400000d81d07070350310005022034144548415410054a140450030248005c1c60f110491111010602841c0d9000300c9490644031010400266103405003419125480403130041c00c44502d8503601c000c00c12201244016514640b40c003200d44003600c070ba050340c8a60203008480c6180d003188840310700c05032418283c4012035500690549180884103290752014007064a070070749550340134042c20042c01c00165400120343e5210f241c128240114044000d14a20000d001c0b04100a400720118000b55100c002104099080c420100b002c0710402c41c9654000e1361280407000880e1600009590f00361080c00b640d0710860008041d089004601d5080201d81200030b03206075070600c28022501e800b0025445256581d000d0b00000786842c1c1000e2a00134181e15070f488c1400c0c0140c2c0440d500d8041602d81000341c4a03024441ca5000da103a2181e60701060007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 533257275 1250 533256025 533256037
    0x1b0e011202090a0f030506070807080613140c1b0303060307150e06120f060d050c0d05010e1510120803070804080d060915091112072601051201140714 66
    0x40260f080a000484950704e552103000c492040007a2605580c500c01c0c04c0c1d40120048440c100840d62103000a02d0904d02000ba00d504441488000150401c07565038024101030102d031103540d1000c0000700d0700f40300344100e40200e142c10b1000d4015482c40c030f0a0707400300391250000c0c420120083d03071682091a4080c001c7c046416202c01c040c0080341c0300c2101e912501002d8a09550f80d40520307071401d0200703441d41010910000a80d401000400c0440c9a150a101c0f1160b05200240c84a55a540c1c00c0c1b03107954001d10401444605281c2510303424103140036942c0c480707510360b07011143c1e9201d42c0d0b48400c0001d804506684e80b05415003002012580d41c1c0c00e081c911485241c0710958064508400420302900c0d590000381c009040c19010b440c11521001114101c40784204020311141c401e200d915212010090500e07031001c4540b80041e030115516a00d105802c030005a1200302c01010001804141400c50440f4001c40d005030003800342803801d28a071565150301620034410458100340007044607a0344bc0c00c0b580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 533258525 1250 533257275 533257279
    0xb1503190b1b1c0b030120030c13030f030813053a030e010506010f050306060a230c060c090d0b0402040e030f07110a081b041b0f031b0e01120209 64
    0x9550320f405412128403008144030004900c0c5001d40079a41030405100d1280600a026030855141341c05500072030480d08002c00d0403200d1041000400c00380c0110034618402544248a04080c5084a187c040d0a06c2c0000f0403081c1c412540f540003501103080000d108201d18903645d450303c1c0c50088144034003003002c426642200040c6680c410008055415403200c2c00e03508585c40204141e441e540e0044905084110816001179024004101245040c1303000300420741490400500c00098040c43c0b4000c4401e4040903001020003103903520b00501c051041c99400021251042c0c941040d5000051010406541c090041d0340c04400007002c644540d44040000c0403480100c948036070300d02103e1205980408800c862080b8bc448035401d8a040004e039a80603980d103040075054045200221203c82c0e0210f8845076401600d075000e08044015900c410712400710a9941c00c0400506110090185c07680ca0f01c902140c01c51214980c0c9a0035481744003c1055542482e07c0c076013030543c1e100725078061700031010040c0e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 533259775 1250 533258525 533258527
    0x1e03120318140615030d120e011529120613061e0b03012403090f03030902041a0901060f18080c190b0412050a0507030b1503190b1b 58
    0x100c14041000d58101c4031a1002040300c200c4e54070301d0440188041c2c00c078180c0350540d00c224018412a40101a52041044403020000d043c0c5519030b4843e09548007141c02e16000d804060303043c401c06c149410109003072110507050713001c000152410000280300c0d20309040c0c006251070010541c02d555250001d4048815040c052000d613860742405c0c3c1085451a00f1405a203031001c100080e4116460144d0381280c4000d44404145074951710b03030000300b02c00c45c1ea00004050303880480e8000100201c0204910500903a40020786107131a2040c04100c40640c0c1c05161991407442e40c6a0055480410580c19205649002520319881000945190a2050543c2e030542050b55001c25100b40001d460b410f0369000712981c90010300c200c0c08a00054607180204003411604000c00d1061002070106038141034890002c072028000030b81c48282c00c100680d08102d41e081c00700e01c180711049403004910035080714118080c04140b0b40c01e404140000f0000000145181d0b803d0b40080c0441032849200c00081d000c1c10b040c0e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 533261025 1250 533259775 533259821
    0x9110405090d02010c0c08030a0507050f03010602160602031801180305101a120a0320030a09090c03060b07060b040615050d060e09030a120204050a0315061e031203 72
    0x6161a48850b41c8090019071030001080c01140c0b08655080b0300c0c0741c001d00c0c4a851515618808000b4200c01824001070040c01c01c80070108041e0703007000714020146a800340924180070403030154540190340c4080115032043c00740000303d24800710b102d00e101d60242006011a140038a403940c4042569002130018010101d086513008165040807d10101003005654911655810085903410604120b2840c0d4441c4052078002402590700301400802e4441e110011140000002d25680c0150080c000150f4920801c1045e03892a016080d158400fa04050113400c1c14541140d1160144038809000c83d40c0321210000162202e5000c1d01c06050301054160241c000c9000203041580001401106035140000c001803041e45c000c0300074010900c43c0023940ca008401c0004507207203001c43d01c0d0541816401c1100054540d1220140b2005600c25400e81e11910b4540e00e00808445080c5c0c441c0d29440300158101d0001c48400304041d040da0f038008210120b44a1a0900f180280403003000080056103032030744 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 533262275 1250 533261025 533261041
    0xb16120c02072c040f050102090a03050a14010c020c090c0f0304081c060e06062a0c0306011703040b0705030405130509060702010623040902030307030305090f06011809110405 77
    0x60100b9160701001c3e4000320655061283c00000c07052160607200e0029602240008200b40410454603004000260034032800074001054000c0780da204540344da0100b02d4031020003040c56080c00c0d007075035668000c0040324110403002c0d44580c102410648581c02e01c0b00024086140304094030940000000030548a280c145465000f0b980f20b40001080d40034042c2d8502c2c811072040c0140c50a403070780484146803070386846c802d100740c9401004100c900e10b21000e0840880c107045409102245174a8001461403140070000d2605204068220304984c5061040c4071020700c60000407141150801605070340d0356012070818038154010f07030304103641c004200c0d48032242201103900000d0160310304006030388603501c44a00c10390803a18140b0441c101c900d03078030090b1141d0480303c4817101c0d407202c80540041109002e076070000341103921078002200400d58540500c0003540d020845844a0030410000b0009541400e05c2e1031408018500450102920380841c1c2040006850a4021050002c0d20500140c241814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 533263525 1250 533262275 533262283
    0x1060201061a0c03070b06042a0e030c0315071e09090c03021602040209040e010e060a05070206100e07030209060c0c1c020d0b06040902220b010801030b16120c02 71
    0x442c48840d5040600749a500409920448607030302c940000840c42c0c101c1e1980c03200c1204100624150740590f49044036000f020028031030341e0071000a0201c0d2140110f1030900544000c7c216540b250081c1c1c841100c2c01c00c01d4a00003400e0000860240310429181e0b140d5034100c0d0215076a82c109070000070264500ca981a410091000943d50b24036030034800b0034041501103003280920b200350046003540354040d4015080c241c1c001d040880c8003034008118a8078810701503082d5443c401c8104004d81c0440304119501c0818426150031003164401b4210700e00b40a003841380349212500230301061017191000300d204140282c0c101d54031400082d0a5941310645101003c1d10b0781141a5514091290b1003014680f203060f00d0039086000781c0c000c08240081d441c5494800b0070a0008042640080e90f650885003da0f40c1c0c4081039401c8520414001166040d038107a840c02d030742e061140e85040c80407400042c400280ca8054040d8482203181141074819280c1c1c2080b1400030214240010b0a0301c1e00200041696001c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 533264775 1250 533263525 533263529
    0xd110d050a0b1303080610091a090406090501180c05311a07060f02211b250f080c100e0a030509010f0201060504020d05070f020606030c010e0312030106020106 70
    0x410403140b0741d1442422582e1100c00f460040005101000040380c0d803503d13403009280c0c480b4601d081810951540403826088030074141e14041c035107020914100920b070038060200941f2010205000c02d525001c450554892142080801030f030325a00056002849501512404414003d019405020136204060381c01039210210302400789007500030481c2440116006100c5941903440d030305e4410075441e150010882d6106000007107401700401401320f0300c106c076120094050404400c50303d0901d1820000049010b41019180381000e22104110710194004882c444407140b4102c4400070582c5001401e1a00f6000c0040c002840401c4035800c407180000d118030f6034400e1a00030080c008012920603a1100f90a8000780042c00c1041843c40d903500c500000c1c40c0c04a01c1d40008038446454200180030380e00302e0f01d2205903041e62034082240c6250302c0381c00c02201880c90700182505041c20000b20781c80740c100e40070322411702415800840c000d8900b00401e8010391403c0755415100d58498030003d010302418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 533266025 1250 533264775 533264783
    0x209010801050630180f0d0c0807120e18010302060403020105251202010c020c03030f0c07080109031809150b1809090c0a0b1201030b0c09031c080c040803030103020d110d050a 77
    0x18144900700c43c5d90000d0b4500d0803441d054002c0808000318403003100c1283c0b0107102150241424031043c0002a8010880c0a61004903241d613607070300d07182d501401070b4840e1010080241034208001000542c03660170881e4280c0380c080ca0711a98a10f11a140305040b140c00060b03140c81084e070844840280101c0104c07a00500340b1f240d00078040442c07140000c81c2d8078004051900d905420170001404002403c900401940c261102070b6001590b859810074212544580c050700840c1c100700103503605902e1090081d000d040064010400c1ea0118812090070311803a00a0410007880003602c80400c0c0c255124460f403100d0002d1640740b003442c1044c1c141d500c829003c44080e005862045020a080b0b140109407000c811200c03400142e06c1c0e11b1a1a0100b902e01b0141c07240300b0f0344204000c1000b25807414040150500014000414900b1103003100030b1031000020021150300b4000d1100b888a1007020080b01d0440341c0403035115450800c0741c1018242c41150b250015070217000400d45038100007010419000711030003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533267275 1250 533266025 533266051
    0x1110d020703110402131202210307020406061403180111130e0601050322031404090e0c01020102180108040512031303090503031c051e01270209010801050630 70
    0x2119042c00217a0048410121000200b40c40a010503102c11200743c2c80701e0b00003080c2038000c0b5514540c49003603030444030452619800002e4042c00350b04150041100038105460704c04400210b102946182d0b000141855031004171405503900d14000c25000340c050107208900441c0d0b1a42e82c01880020200d85108810070303c8600c030006103031580184140d9103d101c1001c81c841c203840c01f18601c03000e03100b46540105c0c14450242503504100c00300e6800362016040c801000201c102d4222034140c035200c80051130703e04580c010454014400c1948040141400081c28402603070784951500ca801d2440e58180059850f0f40442001f00000c13140425080b80703400382d243c07405c40a03201d00a15440f8807031500c0007880450b06903580c403824106c81d070086d540003080500360300c1c0603034441d1303101d00702460280c1c441c400c900540c404d038400d4074402c5c5046c400380c0d201f250001c5240c840c820703001030200e40052140c02e114640100e003203480303e0100c403049070a040b082146080d0308d05503840080350300d040a0300e0483d19200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 533268525 1250 533267275 533267303
    0x30804180e0f060622020a0503070e0f010e0d030e10021e0109110d1a091b06070f03031d0a0b01090f0209030a12031e0603030f02060c120601110d020703 67
    0x1501040544682020001400091307a404062140341311900910204940800401c400d030f0500510241c0701b91400c43c2c0e2026560f081c000c030003d107800d9002c0080f51140100d0b200600060381c02c680481030000c429104224215400e0a040d02c4074080b02260980160200440c3c0110765030203d04103102c0e2444030120001c840e1110502400c0b50300245e0000d0842842201d44c0c1d4852030940008090303148907006818604124140c0c007106604155131070b001551001d000041e00c0f00c040c0095540c2500d0507541c0d030f8144045621000c200c0603030100040c1c140b40d0f803022843d044846c4c0131044e61001099008030351480c001c1d0300e44091598070034800c9480c82407920003660740c1c8400a00840d11822402801003500c0d00e80782d103c03901c801c01035a60b00820325980f00b2015080030004118200c0002c0c2881c000502c6519604000d0012030620814100710b401c44d804102e15061554140c1748180000061071045603629001660060443c542c10307a21849041d4107000007ea0028040060764410001c4410142c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 533269775 1250 533268525 533268551
    0x7090b0f0301050c12160f1b1e0204050912090603090c090405030703020c090c090405062205060906040c08012d14010905010f09060c0f060203070207030b060a0e0408030a0603080418 80
    0x140031081c182e00050506600c01e84501e1042c00c80e01c00100c1c1521039841c680c401591098031302d05481070003615074509c04581800350300d01440f8007948100d80602a04c40040c0e04038007001d003845442d07015440f40c1008400304602e43c42c02c111807698840043d110700b11a092078100141e9a80125104900500c180c18000100d410031042c924007a241e1190f81c1810a0740c40c1c0e04003c080c0c01c00800f210380108071000121000b90711404a401020a083c800103000e09294003401481e010003428280100c5c209201104859072006c001d50440ba03910003410250b8505001100e03100031000c101400421000f40003207007000744118540002e480c241c850211055031030f030041d148105c10030000004038440791030802605014010a400c061311820350243d804010741e46e054103c1e041580c2c1d4100680c0305281c00d00410449240c02a00030004480100c2c06501d0000c6400102d0402040106504004800705041c00400c0d048140510b5000304410b031180d80780c004440d0a0b082e014407400c905410801540c44203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 533271025 1250 533269775 533269801
    0xf08121504153f26091003020c0d0905040c0206090d050a0207030507120c0b09030703060e030c0109120e060f0a0e120a031d1207090b0f0301050c12 65
    0x82e1042103801d1410501d00500c0076908500280d0301400e00788a035404101c1004001e4140750080380079240810784004605004a02c850950020300d0030540c10550300e0f4044609005450110b8800c0703c06904d20291004120003078054541e0284040c4500c0f8403c04c2500c1c0c01c202610181e0300b00f40d43c208190150000d080340d0f98041540c2c14411504401b01100165100d04003c01c5c2035030841c0100e95020359a0795409142070302d6a80714107081d0080e940f500b010406a0101d0400030824182d40340d0810240170000390b00c40d5814030004000c41d50300e1030300c0480c40c0307411300036201c1021803d0000c021202c154102a0001c410700511400001d242c404580a580303010b006031800e015010403d80e090281e10079066460503540c031a802e90140d8243e0556a60407010841d80000354403c2d5905160549201841d190310f071400700859110340b000c46812400440c0c00604c41048032031040300801c0c03010849000c06da235100700070ad9040d010750918003004800e55000d0b0003031422403909603040c540c03680d400950a500d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 533272275 1250 533271025 533271041
    0x131505060d06020a18080706020712050d120b270703092a320402070308130c09020403140c06031e190608060412080105030304030602070f08121504 65
    0x40640c0e40780c66070011a1980e8090110441503003020b400c00c0c45203110f21042e80304a540004d1a951108405001c102d03818005040200f9441c00000e25407072003a500e250700e4030315400c14030040118000c0306400b403120681044030032000240417010781807003410300300980b80c1d842031403001015504400704141511a201c0c0d14501a0441d00151808140803e0003103403103005002d003c401001d00341d01140014401220110055118040f000040e042c00c0783c034a0041c4495a89a00c643e105000181c00300e5004000907900000100c0f416000308070f545041070103020190070802c100d61001c5000700402103003001d50380c4007420390707401c8400700400340081010f40e01c0f0032a000c1d517407403c000030408401d003460582240c2281e100703020000c0d403a45002c1100304032411039019081c9079000c04207000134403151041c0f54000e601075107040300c910340c10200460ba60340f1403480b0041030756500146032000d02600410021031264060503940c0c0c0c1c0d144005405003207a40544440f1690b485d039101c1074113507152911070520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 533273381 1106 533272275 533272279
    0x909160e090c090301180c0f120b1906080c01090e0919050f010504031d1002192306010e0a02130603240b1b060609040609021813150506 60
    0x1c00c1111944040234035130300060284414055015140c24190b089040580580c0310300e03c1071403111820540d41a0641e29200012980000101e604100c48001341d8a84500c0350b100c18001e445240199410360481d0301030711a0fa40040702040f15400c8480c024415140c01000d54500903080d15030485003240040c2e010059102d000051100ca2091140150340f070088501d81140c0c06951100501d90030b48410700c141d9890402c110680c19240081c91085141c100c07107401c5184000d990712400c0c090680e5001c0c2580000c6d8030300c482c40c429513000780c024041000b0075031b103030010135402828a0b6020038460b000c40b101090791410a95030314002002c4810310782d41d607004610301198400d0400b144c2490700303800807030070700400f0b80d2007039100c0350400d802030341c0000e000d500c6100203886401c14192054503403042c1d40070400400300d07890881c0410b41c0113800088028514203050300440310308694560b = true := by decide +kernel

theorem cover : BRFrame.Cov 533093525 533273381 := by
  have h0 := BRFrame.cov_init 533093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 533093525 ≤ n) (h2 : n < 533273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
