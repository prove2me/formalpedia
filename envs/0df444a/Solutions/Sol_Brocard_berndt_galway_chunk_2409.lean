-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2409
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:37:32.885716+00:00
-- url     : https://prove2.me/submissions/d36a251d-acfd-49d0-ab12-c0334fa5309c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 433093525 ≤ n < 433273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 433094775 1250 433093525 433093541
    0x601080601080f0c0307050105130f1d070507030806150903010e0c0a1d06010e130207030309030e0a050a0308030709150e1005030c121017060f0610020d0c0501061206 73
    0xb030304807080c045014078a191620303140501d0a03810f40080303c040141d54050402030800d0089035500011460711200300d2440c28809400900c0440c0c11401c010840005010744d841c0c0190392070803c941018460381e0014082d00005000c1c2d03004400c0000c1d6448500000c00030340f205010020020b0045826441f41260b4403d01b50402c0d91103142a140c1c002110320207110500c054998210700c0350081e603070380c50064441207041c105103600301138000c10005240c2414400390070303404d03c02c1d940841c6c01d90342410014929015500420310a5034048000c010560b6a076251100b207039070052500e038595441c1c00d0156402820b03030b40b240c08a80c01340c06801b008241d104210101c03400e030482e41100d682a0000003180c40740011115400521010801c480840504201c2c0b25406980300380f00b5100f05446401940f00c40b10003119601159200c9424444040c0044900b2a03112170107031040c4400790b40341a8000c0d580c00480090344180542c0003145800d20400307400001c0a00400ca42200322f600091a000c00181850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 433096025 1250 433094775 433094789
    0x30d1101141014130603050102090406050a051c080c150f090115050904060603060e03040303080a111918180c0807020718181a0703090203030d050702010e0601080601 73
    0x1003440d00103240c10044006000c1c91421a200e082241800e008803d800c115502080d808941d0303400e40100c440140c01840040c5110360005a110902c400501c0300351029500130034415003107031206000545400d0414160007001801010110f41d40d410168028070694030300130454081c014203003c0c1d264407910081e0103514414551400383e914043d4013403c868886052511401300307100100043d240681459400c0380c000c0c03900254555995540c402166940f410072900307500049401c10526400c104902d600145008040c8515414142c140510384030702d030942c005042d170a00d00d0034200e600c0340e030703080082c00e50704a0007030812615034400d0351051000d2108140a9070902c1c1612410074454000e20f070048071140c0040500b5820b2001c200030152109a140d80500d55501d0300d43e107030b100b10403040f01040d030081100e56441e17403881c40e110340800d0008007298181401e003001680140c4002044982d00407500c1d60004840e01c0b9603200b2400342850702c14005e214070460b0004a62400d000c80c405040b1015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 433097275 1250 433096025 433096031
    0x6250204110a090e0603190305091f090b090f061606020a03020316020f0601030b0c0706021306091a0307120204080609010c02010b01031e05220501090c06050702060304021e030d1101 80
    0x5a403d44d050081000c440440d0582c10141d207030001c030300341e0310401030075a440303414490300b0400c0444c08a0700c14004e800003450a049004054180b440d000320b40c3c0b102401d20410740d10300e00f6000c1004605001c0034032504034040e1074005203403507440e050780c00c0403000e0a03840311080d5a52144a907000700a0b420550b403c2c100300348241d428116803800003840b9018000100050305950307107103480b1541e001e0030041001100c49005c010503800603060384000c02c17401c40300d0340558540e03a00700b45009120100380d400581c1a0071078030481c000840704c4501aa5440350862500030b2840254059200c0a8000c0e03500a00c5076100f000140148524190409a04101d695008100700c002220044041d176100e103000d0300e40c048030207018030504980707600b1140c1c0c841d1540314240c015844010303507624800390f25001682e540e50b4500714001040104c207110802404d044c5009800c00310581c000416620000d00b00030302c60380801c2d142a001030202c0300000c0c9114030003001e56243d41030040c00034180c0c0d480405c011040c1d5107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 433098525 1250 433097275 433097279
    0x30108060c12060f031015080706090e0c0d0f020a02150c04050a0e0916060207080609070b030c1303020301060b1c060305060f0417190e010c0206250204110a09 70
    0x4210001d42d402a8030800405082d5280c520511503441c0c800580c00360036000f990100021541540110900d0202c0481c105840c0f40c40c0070a00c03400c0c8180c940000e001c004184208010007600d94801e12741010001c00300d251746040c940c000200030b021644100c207400780042400d41b1403607004918082e458a2040d02002c66135035080d80b00380d140c45503004181d80414100c60502440e901c0b400c01580c00b0b804142224201a406000d50401000781d40c05000180e200d85010300c0200410310002c2e130400000002014071508100340b202180c000140540c100100c082084200c54403507490900003160003034020445a602c407030048503a40d10130a00010300314020041460030302141d01c0b6140440790800054011611040490211240050400c1c2c4503401004114110302010100500c40c1d100e40640810040b0b0804102405030101d0881281c10301008010200250300c0d050308603818640031007000340c50788116030a010840d034480d050294225280c4a094207680703c1e40341c000d025a4942d5214111501c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 433099775 1250 433098525 433098541
    0x9090c05121503100f0b04151503060506030a0207020325140105390705090a020903120c06040c09090f151104030501060302030616050415111c0e15030411060f0a0503010806 76
    0x9070381c1840f035050508030108d0422901c0280c010343c60540c540e81c9004a0841d60fa2800a000c0c2d4206586178010301e680051110b08618040012785001d8480300c1c6600c80c0c1071080c90054035030522034819082c2c602c0540417441c0440c1c0c442d4003110000d0001e210f40c000707815040c01d4440e1036000070281c80345c0305041c02135008883c400c00150850448038010f00c0848290360b005a110f019400030001140c00d07100d1b07000218201e83c00040a0034030440303480000c042c1c0b450141000310201d80294003100c035107480d10b040d07100846c030303035010551607140c0100018400c007044041240040c042c105041c41e100c1c0021501208011040d00300c030084070b008508648090321101c2002c00480b800ea040300c8040f0700100001c00c5425588001c0d08100300c0c46c1d06181e14032400044c4558200020510328202074a2840300603c83c03960400b01c81040090161180b42a9844564080c004d034440a000a0b2410200c04060318050f5140c2c0101d410b41742820300850384410010f40050300a0300b00380181c3c0658013072280081c1010f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 433101025 1250 433099775 433099781
    0x3100902030c01210c0e120c010813020f040c0e04090c1502010e060703090303060317120c0405010e0409060e0d0804050c0301051504050a09021e0109090c05121503100f0b04 76
    0x44400000392043d02c0e1804c150420080c80081c030400180208240c4003c4240d403002c4061031038001220103401039400380400140404402000803418040c001c61090158a8510450803492400e0382e0005226103e00c0081c1da40c000060388055209007032010100420681038030103021035840b5018030484c611170460607800d030750b0045000d0015034030403c00180d00600c00e400c00340e9158003a041c001525030300c94480c01a407002d8048507021503103002600302980b01445400340c0c4d02c0211507160608103405e140000700a4103203c40130a10030703030300e4907030001c11f000c4694492040428503038200c0b00e82442c1d00c50050605203084600b80c9460091007042c803003604040c003c0b1071160240f400c0c2d05403d207001c0001c00c0300070407003e040c5190055996034584e00580b50040f160b5441c0e00700a1080540a1301d400005020700b030b9036003002e62810305003601080320b650004c0c140c031441d1500041410103982c814007a62010b540e1018000d5041c032604038600000c0c00280e100d10ba0000b0300050a1207100342000900044e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 433102275 1250 433101025 433101047
    0x5040e01050f2d011223042109050112060522020c030406020a050d030e030702060304140714031204050f1002030d090b0106090e04030804080c160924081f0b03100902030c01 76
    0x1b141500840c0c50021880140740ca54454490b2400e03150f2248411100c0301c0041c0000090008901000d2041c8860741c0c00440f596202200f071a0240700c1c9904040c045905e83c0460700c09154030070036004e29001800e007903170180c8000c841c501c82201e840342ea42e410300a5562a26010959050091005543e0120700c07074050a940c612030031005500d003100b2a0b0a01c02c0c16480144141c6070101013440000f5401011302c03a400080804800040000700c40b0400c15040c101c07148070040186408000070400e54844800b40950514100c416100742c95458406a0451141900344115107141124075020000d8074010141a00c100341d4401d54090344504040b042c00c0300c242e4000e80400c2000000800041807030004003a072070300138815640001e04030071100182d03002c3c503046a00c0ca2a00c9e080280d010780740c0d03506071070340c1707211215240408185070403c1d0a44904400c44090840100504002101c0185030072281e44500081c1c203d800c0030000c0c0703040c1c8006082d02002281f281c01b86900708001c0e9842400c03d401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 433103525 1250 433102275 433102301
    0x1205071806030b04150b180f0a1407020703060c0f0e1c0b0106090801060b21070e100201020304061427010902090a09170f0d0509070b0f030f010605040e01050f2d0112 73
    0x3400e423680000c0045035000201a036031841e0f100c3d03030401861a180c00b125070041c0469002400d40074154a0300100b6603a0140c00e0104220100307480540969218090b4002d4038070603600d81d070980c03070244403080000b000302602a0166869600008002d5400720081c012150b035074000708025512048140071500c80ca860500b103208000ca04075119440e0742c0301c0d140d0030a40a0030440304500014002c5140c050510001c10301503540402044284070141c01005220300c88100c00d020186045114040554480e03a02ca040e4560105031401013034409501c26124250000c0079012545031858400001d8a0740107006c45461079455550710041007010107880d4132004129150382048480c0c0c014500415004020008500c59101d00080450003a0020809840103150181c0e0300d2402000018109006030700540c00c104041104102465140c16418199503048480c48042c0e0440000103545442d140807407504a00d00c5d012804140810040c03050143e20700ba220a203e100640040d50100c1e070b07031604c000d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 433104775 1250 433103525 433103569
    0x61201022a06060d060b040f050c18031618020c1c02191e0f0b04080901080c04030f1e02150414010525020d0605150a1205071806030b04150b 62
    0xb00011400c6e08a4040c0f51000303440080c101c010b00030400191181580c0c2400d26880014241c5507480307481ca50108500d4080d4000c1503034070440000d10242041074400c410171100c504c006906288103e40403500e640303400c030342203a03900147c0850364004400c000d10b2078005072042e10210495600b0000b0307000040c540000721800c12108020401404c02c1412600300e5960405c04241d0000805d00e0a0700c900807030085d0506600d03011018005000c0d070401400350024001e080c0000c0002607130b2003400b5228a07900c2928060042e00b41003120b529a004008000d6000042c003403807885096a0b00b000d00b00b100c41800300f00010724100c070010358180c414090b440300144041c0e62040d42d0580c85054050380c452018000036242c00d2183c0b120800c8410940760356540b1000d014002c505880c0c0410307264003802c8900351442c0e49502c0c959405170364168174442c032081121540408000f40c88a41e20102c01160000404507041c030f05403600e2880010700d1903000310b040303182012007900ca04040c2c0c4400382c40d03c0c50201074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 433106025 1250 433104775 433104799
    0x1090608190209030a0c033c021903120305070f0c03360e010305101404030c0203072c0c04060503040323040305060f07020303070c02010503061201022a0606 69
    0x6007002c0d5000d08940c503018410600d0140000e90344005c02001907000302e0040c81070000d030480d00342e00401c3c4a1042c00584100e26140070f42000d000005003002941210400e10759650002d15000701e015940c0003502c0c25803c0b103004007030982c258100c0391092155a035013040c684085042030710b1350b20003240054002500114005401120310728821240c04141c201601d07950449603820844680d55081440e0440380d02c4010020000104810120502c409005010f450704207191303103102c0d000081000c1c04000c0d2101e051030954900b400b2483c003030301c0e84c05d8010341078070341c1c558040c01005031072088484100344c244000760307070154482c0a1302c0c143c0d050383e92082c0c031315103841d20200c4625561048514030266416a0f51651110481c0240001e52240003c2e103070a1134165216000500000c0100095420800401a20315030201100100650900707010303440f0340b111030219010f2121642100031a6200003814070b10b20410500e11429980300e044c9031985440514029601c0c0e100c1903e2054002040f0310fa2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 433107275 1250 433106025 433106071
    0x60b0a0c020a06031b0c0510110703030b0303033c10030203070503030306010c080a09120b0105100806030c060a0216080a0b070f120c020c04050712060f0f090203060a081b01090608 79
    0x18003481ba40101e049440d030804180c40c90301180c2810f8141c0d0044580050541c0800d41c141c015030381b01e2074040f40510b08602c1c0480c0c001b90408981d058200c0c1d1304882d103000000803118030050383c92140e60700c1d9540c885072400404003484561507003c140d120b440307288400a454900001241d104450683d40c0412a0b68686c1d10f000640c0c100e4503d403c01d000045101140c160040040d401ca020b02540081e00154541410300c0000440c0041100c2080000002c11000785c0b00090039500c00602914015a02c00110804900b019600780f4003203440011270000003800d140004450030180e00444503139004c0e0300d9151003550301422000706039002c03e0950360409007041c07659002c0702d401c45050040c2c85581451000040480b131741160b080000ca64140c00280410180e4410792020740554803d100d001428040e4004031000c01d031103980907268001000071602e4484d620180000d1944074102d0360701200007050105407400c036003159800074119082c0010210300c01c011450150900c41c814003203030700c19500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 433108525 1250 433107275 433107287
    0xf0e120f07020a03050a030c110d0201090b090a0509010e010501020d020604050c09180a140c150304111c15050a09120c0303110406120c030e03031306060b0a0c020a06031b 75
    0x41c2641c1c00328658000001007481404017a0030b0a00c02e9803117150201c1945840c1c2c841040144c000e90144012012060050b600190300c0c1c81603032a156000c1d61500c140c0c500040039844280c03c25500312070f0b40070000840685813071815069520913005d0300c8508804040480e59030300101c44c01b070100c0c0d1060f440c0902a06159409640240a01c10201072184414038044e03d002e00c21a012030701d40702030683d81c107030080c803c3c400071152020071211050900840452a600e07400054805400642d907546100f801d070b510401403002c981255400200f002409040015424641900c1030703081500b0200050242800c5208615009a02c41082007001c001c0d01021190a818910100c2c01d05640c0d01c0c9641c440c04070700300030704001d0800b0b0765690b00105d0b40d03050407030a80c4e4000381c1c10024103052081e080d00c000b0780441941c0d4000c4210707601c41d483c0d411900708800507006c0e55208440440e400551440c015074400080c0d2aa03074020f4620402d20742da250380443c11030b40c0304c1e00b000031b02108880c172405400344102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 433109775 1250 433108525 433108537
    0xf0602030613141f080d030b06070203150103031704080403060e0c060c070602070801020a02210d0203102115150302030d050301030b010e1006030c031404060f0e120f 73
    0xba141d031001d400010301020895640e0995401d0301240b043c100440e4484404e90b01d032051104641e4007070700710314001c10240c2d030381d010818160500da00d5450701c403101d441d21010b030f611040e00141241c64050191044000f81c0400b0300059002603000c1c514035038000c8003075002a010725803001d48240303080e14645800000b02851140071586004200300b00300a69151006483c0b001ca0b46006032015501c3c100c1c0c082d160403050b40c42074807a43d0040c010011406d030046010940300010110320303200c82c411141707902d6040c4209134a41480d10300c0030060285151900000001345c3d0000d0b9a041c4500d480d5020412070f10b04007007001004108500c0c151001c0705050341100b030910b0f6002c0e03403554001d0385a6002a0030408092007200025001000400610049041180c0100302d03281c00391019090120901c0154030160081d4402e043d1509000074107207200340c1c8002031091103084102090b081903d408800b520384400b110319600d0604840404030380c8089062032004211894862030031a014940141542001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 433111025 1250 433109775 433109779
    0x60f060e01030b120610080a0c06140412060f0f020c1209040b1f170907050d020111060a1d0d02031602030705090403020105100f030b0f0a0f060303021006120f06020306 74
    0x30710f052580c40d40b10b050320005444c20900c050091031406102c80301c0706100a1f44134503c66070003200c4c0764010170368540028054807402d00d40b40c614445071340c2001181c0e110700d500100031149124440300620645034807038407011914000a114110310f0441c2c4100768000c101180c0600d411061101505454010017801d10410140011490300000c02c001080541502c01441c180c200c090f5103444010761046d9501a007190312101e070f82860801d0700c6015607800c254002c05018445c04804c03a000c1d60701900c00c1c00c43c2c07a05030b01c0458503685003030034103800606807003007190b0152000906441d0855502180c4481814542e600540c18030b40c8045400b011071001c0350061b605802005030100ba207444401c4040d218034043d400125060500c62451a171812030b6501010036080c81420500000e00d03090b030580c0d00204103010f084142c2c1c0319805500010400205a080e1440c60035100200301a000b05028005a04040003040866580c03194140761468845006120103112216900002c2255001e1a001000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 433112275 1250 433111025 433111031
    0x180207060513032012040905060307170316020315041a0702060903250203160609080c01050409150f0f05120303060f010f0e03010515120a050c010507060902270109060f060e0103 78
    0xc40ba516154402d8104841f110b4548007000b00509040012100504000813001d01701042441030544134007698034070094416829000005660f800c00c520b19001161109102540c101454170842c4a0620125151601401000a14468000314056200311001001f035480c040140d004401c1c14030101d0a00705103502c0c2800c0b5074015031000c0011501c0c05c51041c000d007040c103007800b00140c13100c0159032122020b64070038a071000317403640d1000940e01180c0442c8008034525041d5031680902e0141d40c1c002c0312440c640303501c0011b01d148210040b081201c03c291b942844d44c80301030303641640383d10084580d00d42002c0c030280e010301c40d07510400c0c5d00390114000c1d20b070205030104200006400e4074401c1c1c0308c0000c02c11481d400340510713240c0591010140d00021004083e449400c0d6200c0380c9a50484010714148240420230406111280d0401212141d0050086a545118400e001140503280365070740321040c20000085140d41081c4514000d40701203c0d481e15507540b40a00842d080d5540e83c0442c1e0415403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 433113525 1250 433112275 433112293
    0x15070503030a0209011d010909020f19030f0b0315070c0201020f01050106020d120c0f030b0409060501181b02151e1e0601091a0309071802070605130320 67
    0x2005001450180c10b02e500302603a160f040344001403203007403400c5100b8016606d650b40741c0c1031603070850788080407580700700d10260311200d1041c403e0341903018281240f40d02c501414a5058203650560040d140c11035054010440c00e8110f100741540c0e2416000300d140d07818115008151400d00a00ca44403d140c8144101c4c0c41070603001d02110709558081c1d00900241c1d02280109202642083e03001030942003101081046041c0c014004040c120324840b0b03101407598030064440c5c151116045800c605410040074405940d50341c004a44103a580503800c0040c5203489504041340d942c1014109500d852a40240310036168801c0c86014441d000c1c2c2807a01d108081142c05030f10828100005100b0f03e014510b900313185110803540200e100000702400e0411a4a0500780440c6074101d082c20f090400c1d0032340c4180c03030756103022030303285041c4464010140d840e20024103801300c01001c2d00101091413140b40280507640f03d0804a40030600c04400040204200240c00e81402c142c21301c1c050707134080c01c90044a000c92 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 433114775 1250 433113525 433113533
    0x140418020a080d022e0c0302040b070f1703010f03080a0504030209070c050706180b160b0f010f060302180405250c030813021804050115151b111507 65
    0xc1c00551081e50a03403c2060b240401603014403550a43c28111004140308014100c40078058180016540d02140c0c0d8480c4d60103030184c800e60648001d0040c103903000c2d03510382841c00c1070350007140500000c503600400807034441020300000e426a8101d400441040c80070500b1070f59850b003160002c283c1c0f001086024000000542c5d518607400380a01c025413107070303100781502c2c0c2013003801c265054002500740141c0341d4000031050304510284084516418840c3d03281c514049840020748107810001e04180d51031424410340350404800c040c100c1e2044100b08400c0c0e541c61500390140d015040c22403050448421200030141003139085143d2040450341e003503000e0803020084c03880a42000105100003008a101a0105500055520f8208070b801e40c0c502039081c440c1d40080d0b0f403420050241c1c0040002140410f00b048000d4100303404039824092600155600d407000c043d5040b1740c400c1003c00054816a0325802668044041402541c0150b5074200e182c02c0802070069070170342403040000c4140708000e40f2000c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 433116025 1250 433114775 433114789
    0x8041a0d0603080c06151e03010906020a02061e070906111903030506011d030a080f13080c010e040c0818030f07050705030105010b0f1207090b0721030614041802 71
    0x1451141c0b20f2203440d072010412540c505940100321007034025005020040554440b00030340c61604030070078042d00703402d8681c003c2405080c01400c01814140040342030040c09401050b114400c074028104000c00110790f00d6000c0010205540c0d1002050a42500340301c460b108610021442c00000c04580d9403200100382000d010384107801c00d40000b5a55014081035680c0031100d4004140d00605001c2981c1d000ca000a0712084244001800c1410000c0c3d41ca50304598141a104407a00e034001e02d5030242d0307a40d81d0b40b070f407202180c401190005d0b80c400c1d01070380180f86c81d1186100040d02d03a51048110340d14400054111241e0345106183c1e88010320448429546040007000320f144240003a140d01c1d0f1038101031600755081a008545100d2040c00121100581c0e0015952918001d07500706903a038680740400d80b40d06400d6005401c840c28001150340600c049000120450039451440301c0c0701180302c107000c808844603400707003019908036031744c6060482c07070680c12406003200c100810000c006259400181c207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 433117275 1250 433116025 433116029
    0xc0c030d060905010b0a141803060f01030323180a08010f0603020310021c09030e150c060601050a09121a1e01060507030804031b0c0b04170a08041a0d06 67
    0x8040d4076800248461031950064a006100c080e8180d8100010024040c0503803040f84031308826500007158000b200c1808208010072039501500f500e0071410015442c0d04a501c0900054001c2290155460356402a40340d140554031426581c1d42ccc10105e91080034038488805c0c01134142e01241074400030504040070300c1000e40c4412020400540c0a103184145070800c003d81c480f41400d5071050007540305081683c0c011f12029200a00c0004d014030303403031505548100381c120110b86c20901c078072110950f40c005200104906c0070389100b00c5082c1d41c0d86600440d03451041c580c42c0d5001404122007040540001074241500d50b11500c161003100c844019402910f4900720b441911180c60f080d21017840450b800120b6024100524217185004495200505100d4006d04028200818514002280f81e180706500041543c804c0c16010032070b17550040c00030342d07401c28064551040d4101d0358032101c1c001e0008028501303a900c41243d40c04c0a02e0281c80803010090080e00a17a4220b003005140d0a824140c4601c42c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 433118525 1250 433117275 433117297
    0x904090c180e03030601050913020f0a080a0b220f060909060204050108010605070206030114120a032007120809031e100f09020d0b1504060f05030606010212120c0c03 73
    0x1540264540075201950307640505044540c004000340501d59038400d003203c1e02c00500381c86085002120a00040c0244110410052101408181c000c0c0c0240c4c0084514000c072030005060100103101c001f0400032090703d0f4440c0e10803403503070030141c400c10380190000d09070005c410000042c0342e552003030282d060b0781c14a82c08641543e80003a00707200c2580c010b81c1d15409848640342a0b4101180f507808508207200600829004000c90a00d4250982d200145004a0b1082c0d0054509104080c60082d204131800340b14481000c3c8400801650395000050200444030340e01c40b086004050340c0c962598582c8000368294245c000c00300502c01c1c401400904d0040500442c004104c0954801040001c4038061040781c070501d801d041e10302001da0390711194600e00325000020104181c486034105407960440311401c40e0000d061103c005603c0da100700d48082221001d500f078030a82d43e2450700480c1c40c2c59010005502e450070a00c5250b031b521110910700780e8000310029006280000c9020b2140c070350b401000c400d031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 433119775 1250 433118525 433118549
    0x3061b0f20190b0108060709090f02160b060a170a060e0c09010608010906090c0f0e040f0f0e0c012a020d06090516080c01020c01120209090906010312080115050904090c 74
    0x1100304800c3c030040c1401419910301070103071814a080c00924903100c922039060016242d01c400c0c992180d0075030455954402c202c071030741c624202c00d140020180d041180e060b0700c5100012000070391142c0b0001d9002c1011404800b42880b040c2c076a030392000500000c01509454855505d901c9100d0700c1d0354a085003e84016120f450496250000b40b60546503140c02c0340d4000c80c2040445079000d6004651510030003030314200101e41c908043c01180c020406241d20111044c10098020780c2a03815a2204042c0c1d40c10000380c0b039401c2940401540c000304440307800d413a40b152080d45422140302c0800707a00d9030780c0e00c02010006040074030b0301c42c4826101e0380c8d0740030b8a0680290603044072001251003040000e1020300701a050282c01d0b00c0010391a44040300034641230100424614502c444a41c0c1254400c8500030310038407403400c0c0800b21699070740007400100c841002d0b101c08000924050501c1034100d5440c21242401280400c1085403280c03c07810302107030025114150388000038002180b000181425020781 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 433121025 1250 433119775 433119823
    0x80604080309010605010e060702010305070e0907051e090904021002010e1605030f07051f090f062703080301050609011101050405010e12031005041e050109020403061b0f20 76
    0x40c215074569000350705101d947c042000041d2295019101c183da02403c0000305662768a000743c925903a5040f407260300525000801c101603400c04007800101801c020307d0321640348006034008140c820458051f9004ac13072803001800501d4401802028031405c0d10010400c40c02d0044418503082041c4451020714070944018020b41c02d082107002004a100001040001c0c503140c0030508188240307a200c11107504000300440103034000d0003001300811001d0080c00207960307510002040202c03490140707107030354000300c400c50300380f2081c20701032816a42c0003941c0a2440e403904081291a600c00100c10707043c484940201800c9481c28401c4500c900d020718000b00300400c010701801e08082080c582000400001d00501c56131003002c40304c89081e9034040e41c0000301c607660041c0035014003000704107c0301c406040030004604031200381c002e0021240b01e03000030f00c5404044905042c02e4444c401c8490000b880ba81201080303241310781002c140b00220300b0300760000c0ac81c1c80b84190b400c210324442803204501c580d11070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 433122275 1250 433121025 433121041
    0x6050408120703053a02030f060915090c0301030317010b0409180803190c02010e060406050702030c03181005041805060f031902031209030a0311150a0507020c0f0a120602040806040803 81
    0x43c11317401482c640030861541c0380c4076070504090140606076a01420702280002c0403002068032001041400901c522407619218049504592003400f04034002812811405500000520014141d6640200d03c1d4289810700086000410300d18406801201d410031061022940c0b0760021402501000c860030001c5108017490429140c40c1c0382d811046a1504a1a41c9a4030012621681050b40000f012030700b5214070008a140d8020020f5140f9540000240042e1843e101c00c01c003405100281c40100a40d09000d8081d2664019407180c680780440803000105020441e5020940c411801007000c0c18290162000c01c0c43c0c9504002000c00009002c1d81d120705510b41000f01e009030000c00c81341107150506550100e521441032030002000d100c042d100307452814100303115a00441072155203601240c500803608002410b0309989490241c000c0c03d40302462400c0c480514100b81d20094510078440b4904409100c00180c1060180c80c410b900344400b24181009010503801140030382907054607402c140e21 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 433123525 1250 433122275 433122367
    0x13120303060506090a0b09040608120406080f1303080a0912022401081504030c1203060e070c03020c0f120f0a02090c210406020705010905030a03060605040812070305 73
    0x10310701c81c0700d013032086054558a800000b42aa8408641152035482c1c0c03e010502134102e40c0c00c05402c074090188540001048039000c1c0085403166622002644c4031041042c0c4400b205449244c000202c0100001c0800e004012541e0041500b401c009842051520f5140d040068070091030016003010b510003035100f403269580c200003503104000c05442e5140c4003461313039a10ba440343c00102e00d8902200080505025001c10310b40755410454094100403003140080080c441401000c200c200784101142c0c15900c56100c0342080b13581a00240150408202007040411000c08003560101080c500440050406c2c880c5154441c030b0b4100800b90b03503000d84100003914070010190580d481c0207102c2e902009003002910a132440c0f11540e084010340b690b003080c0c0040c1c8070f41400640650b0801d100c2d0000c01c00c0001c000c064407030969604000c483c0c2c54080444140c4107900c03500595a003d2081a002c1841c0b8000400005219080191610540708603d082800300d207444c4140c2140240c25820424200403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 433124775 1250 433123525 433123529
    0x20f0106091e150b072301020901090e19060e071407030815041803080106020c030309091807080706030b0a0504090b0a11160803061c0b0106080c1312030306 69
    0x16800b400300c0290290b103a481000090155580c40c0d403101d5503140c00039103461880d40035212101c1020fa440da09402d1001400300700c04844001c50000d022108006c001c18030a50b20058070503500c10005925205960000c03c1010f0300303503000e1003600320010004803a54803400700108914070b00e83c411441c0103000a03000e00000e6021300c650380c400308944070020b9400400f00b43e000c420382a04091908140b000304e801011008109081e100e0382104650615400c28407807030407030301aa0300302d50b000c2c550071090686074080c400c03d503138000103402c010130a40d4000b00030008449075010121644182d03201c0c056894101564440ea02081e600c02c921421030a10000c501c0240c04161014018031000e66901c0181240013013590039200e0341c4840d8554006100704c100d9040401015203c0d60001180c2007001d1258001e603010703449082c064004450100140104c543c01c980c1002c50395038280e18080342540c1d1600d008045d40c80700d000030021721044030b1400c0401d5000c0c120000709200c1d0807030b41d46030140c22a0800d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 433126025 1250 433124775 433124789
    0x40b100206160c1211070b04080606030c0111120c12190909021309020705070306050a060f090504020307120c05040908030702150c03060607080c061e0c250f12020f0106 74
    0x43d10030040810240b16078141000540d203007041911391051780e01800d0524079008030104c0d03080001c001846840025407035000c0c120480036203007403941010056409402410361461070742c1204441c0e186c150043d00285c030030401948240c0c2c402d8144c4003940c800581c03080680c4100c1d640f012440310b01d0640d010030a18041d02e01c8100c210300e403505c000b0b6212050200d500c1200d0641e40c00251071010081c0c1840280c1c01103500c00000d02190908481c0d0101600d030b80d000700c2c0580500a40000343d10419405120701950300a0003500b991420700701c0400c0e1002c2462806c2e10101d18050000a0941f200d12179080c41c00d002d04c1704a500e905180400900308603e860b0070050b542e40000500c241054203404903500850103c0d10113079103019514125842d4016031341041c295005800411587c00b50340143c854040505d805003001540c1e40346003165460051a0505148802c0c80b4009044201d83e007040c0e03588503004403481c0c10b5501c8923030340d103813010100c0885840050708242c0441210a509005a10107842c0c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 433127275 1250 433126025 433126037
    0x200105160c02030a140c04060e010801240506030c04030519150b0f010e010c050f06041e050c0f06070803071e09050303090607060e0a080703020706080c03060f040b10020616 76
    0x2440c0c0000761395080324030002d004450552002a00c0110402400462500291051081a5440702c0c1800d190b242446840119428550b1080620f00c1c8484800c059052400d4140c0e8402d0825041c04200d401c010b180d02e40d0f4503030810000c80454000c00031091a240c0d4a030540418602c18a4101d000001596002c034410381440e11210099881c0c05240601d200c003860445009130301c0800494880d111030380b0103031182c01205510b901c4882e000c1a0180b040d03014000418204c04a5280d420849803580c0000e40f03a1f41000b94558414079250094840701c800c010040307401d240450b103c48800d6882a60031b0340106e6521400081c00c080030341900301010116003444410700340742a0209450b44142050343d0310450300021441c00b0000c0540c410aa480e21040444a00080070b192000b480d17806241c0035000340c03050300d00010382a842025203038401d1584c03200c0ca50464031070000b408a89501254130b03541c4242ca60140e21004c2e1a455405088003141c0e40c002e00032802e00c5400c1c4004a418010300d01c04000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 433128525 1250 433127275 433127297
    0x90a02031005070e031e07350313030b041a07050d0c0e040c0804020901050a061202091c230c0109050409031202130f140105030601080a150e071b0c060f20010516 71
    0xa07441440d406030300101a001e1013070852100c2e410342140f00700340741842d0ac82603d40c2c000c0207102c840c402880c4114410514030303011440206031405403400460f501350000b40c04000b15010b0f0032054002c85129085410494824040400054140c0c0c01e01030281c80040e0241c010003003035242c501040e84c010310054501d510300747e08140c0018801e0a28071882861540c00144000300e0703071200304031100f0340c81c010005000141641d141620b40003214281d44052400b0100c1c80313400c290004035004c40c0204050711000b40741850941840f02030b00010109805001c40e0010f986403e02ea98001005803600d0b003c55513941c94100744014000d0410341e0041201004640e030720b1940b41c2d80110460350082e600742131070f1049030b8816440300080e006103e40122106100e510000700e5900d4200c1007400b81c0815100c40c07190b50101c5190340c4680f01038050203003450100000401c40d40d401541c00e54005641485c201d40c2c040710400821039150142c0d11400b4442e03542d0000c00006814406a00c000e8403102e180400d0414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 433129775 1250 433128525 433128569
    0x302011107360903022104120302070501120c02150c0c01151508160305040f17180d0309091a040510030b070f17060402090907020105060306090a02031005070e031e07 73
    0x140c0074200c0f441181b0140d5001d001946003080030b441c010320907030108a0840d0401e1031700079168a040d00c5158049009108600f000c00603a002e6890050f900c0d40c000c04141e585e5407000c940858000c1c1110003030340000c100c0007400e0b1400b801075900d0301b400c051008482c1c0d131404180d201c20ba000c400c01e6204220036002480205a4014030069151741c5034a0b0101d01900c0c2c40c1028580c0c40c035041c0b0010443c81c40d1000b89800c444402002d00307480c0d260182030b0010b042e056030030300400c26100032008000410303044041c030140a195010360807039504405c05000f0819000003003400c07940d0a0b5202c10000e01050700c20000c121005403402c0c0d00041518000c0c0f09062000f80c090605c8109140094864a54000041c40e0f0340b9280c1c107480740404014400c0c0000e0404c1c09002c1c0c0204401d41d04079000f4000c0d0000603000c2403000410600d800c0e40a0010104e050b4010000f10041c0301c043c0c880c3d41040b031041d100d40c00c2603404100344400e00c0020400c1c5c0d02040c1680900c240f5010140e0301c42c0360480803100f503a680107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 433131025 1250 433129775 433129783
    0x302070b180f070e040b0a0b010e1302390705091b0d02070308150901081b030f0d0203030115030b0d020d020f0402030c040e130c030201110736090302 66
    0x1014150300d01c6480500d00c48002401e010041095100ca8421600c1c0003400d2124480c855020301d010344018542c03034036003401071001d0325080720f1f00c60b0118458a80c16400c900f05107101d80d0000c07901d880c006007043c8004071000310300342229245440c6400848000c0311502020002501842d03245801050654501408200591002051a03c0c182002c1680c481c0118000382200d80c80e047e800411582d4841c1440d02410441e0181c51458003e0052141c0060700c3c14440400ba050741d82c2080106040d402c20300591074020f4843e88240d402d4013900c04100d1b00c44030200281404000030340c01031500ea40c103103d413071483c100d0306070019000c040c20010314845031341350002c04135895601035880784940440307130002c20645143cbe402840d400c90b10000410031620450005001564580714450945480b102407040004201e00b0f4040c02c0d05d203001108000540c003d00c0503800e80b000d11015500e02a41d02c2c001d104a441c40c0302c05010300e10750814130b01900454440f10b44001080010000c1110a6840d14000c2da5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 433132275 1250 433131025 433131031
    0x1333050a02090a1e03120302041404050105060409090f020a080d0f03090f02040504061b26011a031b0d02040e0601021f020c010917070506130b1605070609030c02030c010302070b 78
    0x28140f59804c1d814003450b400721840c0186070007102240700150038080050096100340b140162101c00442150341d58030b401e019407412120020249800e2a08101c81c2100810358003030101c8441c501c02400c040103071104d14040c8014490340b4054503040c8410a800b4103040034040e03080313040620b8003029800050b00700c08a0051a5010b490006403644d0b03524024004180c450404421103081045411101ea48840009040c03000c1000000c81086684810b0119100a00032044002c100040060042218002540e4000c4d05055600e407001c0f00c0101c0020550301140c0c414a16940002d01401500007220b011604560284010300b245c0c03030600100d0158018110819100b590006440e4004102c01d4204050b00e603007001c400304810002d901ea0011951200302c00702c0f02e9014080000e1120484598880041600701000840a030b4900c070900540340c0850b40d4040030300c0011321842000c00c0e01413080c0700895100b51140e8240d0036640c0101440c106403a28101d04040c010411100020f04401d82550 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 433133525 1250 433132275 433132289
    0x100e030a0212030406090b19060f0b0f0a0504050604060c06060b03160f0908030a0c060b030a1e1a0901021b010c0504120503090612070905030a02091333050a02090a 72
    0x103140d494628280717010700562103010300309091039014040824494a101b0700c0034203150008118507980c4404031a1048958802c210000c1d4007800488002c0c2d43c1200244007200541c03411503d040d8807800014100c2e045500210001400d00c030304c62081120318841e440182003546003050551070a502c401142e030203d030440e1010451520036403105d20b8001c40d42da178003612058054035150348400600811004041c40d098843c181840e482640c0d600300400c0c41074a80e0780102034060600d0314260141c034035564003801158a4655445403104440203080041e0207598010000750b034a00f4507800201341c1c0b0021521094403649400401a015500101228100c0788414010000c0b0200c5092090030744c014018019040301c80014040080102e0041451051a0580b20080295220410706a50300000040290083d51700c0700415640f08488000c114154807460f42c4056180300910000711944003014042a1032081c0c0708888040340b01d5000e10795010010901c21400c2c4420000000c68034440780c800c00b6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 433134775 1250 433133525 433133527
    0x801092009040f0b030123061c120509030709020c0f070605090f0409020909030307090b09031e190605150108090607140f12040c0e0702120313050708100e030a0212 72
    0x940b440013900800c140000017030081081c20100304004424980700041031140384080000580d03289040701400c100c050440d201d00204003955540c00ca5203031440100070081c41014003003a48039035020403000015080507800540c0381d1030141e070450710f00240a604d4000b00d0308201414004164040203882120504441603c042d01c0d40c1030100d002451150000794000c020401004284030700000110b02920f007d40c0c9507000c542d42e50700c00350000c1c02040c0b600c3d135254220001e44007098040c1603201629140e2038040c1c17000f02c1a00d1454901c008110079003200d20030384800c00c004030441c0c143d20740e40074060282400660342c40c19450050722040014807100c02e00040c0fa2002032106401d13402d40e100d528440b6912640c0d01084001300501130022502261400c51460010680003901492039000d002c4540042c820380003009481405030304020200e101800c1d100d664a800b1920401c0664010302200018260035a038460185003a54602030300d01c49954003c10075912560ba0002e040000238540350f58007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 433136025 1250 433134775 433134791
    0x9060112060306020f091203160b0601110a03020a140c0d060504061104080c13021c09141f0606020a0203030a0f050f0301081e060112020607061407080109200904 71
    0x2150003001c980e04040c02c002e03c00b02c2c041c00381203080c10041c11395510846100d03035100f0451014542d01d200e40b00343d90500c0401c08054800007402c0c420751503040303081410881803601c99a24000c0c43c2c800082002d40059000654550601c100c40b110640300d04460009002c0f6440c82c4804510b02c004c0d1080c00510099550000805010032a4000d40359221103c80c0380d990340d55502d20807550b4071040210300c0c0c8941d10b08032900003000030520031a485040210749520b94040000c2417800100000c003001e80f503a0060040004500c403062101c004845180e091a43c14079a01484450850340c02d034001d01d0565022070403500c00741c0d50000c01d86046196920b000019001c401d00102c0d00f80c05048011001c0d8403012001040340d92000c20300d201040143e4441c2c51200e8a0108115a900001e10440a0820f1112000d00244c1402002001030034095a0f01098081000d0084010103104540c09000503030100d0061004060380d010700c002c545090b0321004481c100c0c01d60860254407602032039900c07469a407004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 433137275 1250 433136025 433136057
    0xc030c0516051207050d031107020a050d1a130302120304080403080f091f18150516050a140f07030809040b1305161b0c05040c0203070615170c090601 66
    0xf01001c1d0009115901c5640c1454260354900d10303a1900400300f03041451198060a281065441641c1c00401c0f009280c3d2801040c441c021a1440303050305d200b0348508004090490895005008400400010f4005005030500074102028070f0103081075407a0030424080410a04029507050306c0e0071a8840c1d80d240d41c0000d15031072030b106200b0020b80155881c0e4014070340c000d00345489005c2c41850b4444040b2100c01229080380001140141480355080d014410300c1d00b886a40946024103070b582200503400415100c061804002c030340308841c495082c0f0f4211521400a018141541507048010603948c3d055076140c520f240201c40d0f04034052a0364a515510942c1e0707400011031900c590401c20080b90601d154442038450380820031b8404074141071000c0020340140300711280c020740c1140c24011010304007404c02002d000d01c60461401c42c03000744039002c0030544034451400c079041d25040c010482464802c1c14540219000c100c0350160b00403180340062620ad600c0700d507038050000d03c1c01075969941c0b030761 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 433138525 1250 433137275 433137283
    0xf06031302100c140601062a0303020c1006030b04120206150d020d150f1a0a05060d14010e06090c040e040b061909051005190e15040f09060c030c051605 67
    0x40d21981d0b8481d44c200128002081c2d41c0c1c143c2d201691850b43e039006031611800c1e480c00c2c0c0e903c003103849a0f10203d07520100c1d00c20b43c0940014a0202e007580d000e03189010301c86094032065001a11021031002c14002003000d0821541a080303040c1c005040d00c1d1900500100d01c001031046210300400d25003080c0f80456450791031000100781d03c040b0200400c103140c03445600030000742c240211610301e050007460740c8000c0002038000322800202400c0c8030f14240418070969401c42002501e07800c0e15820750759581241250304034042c080c80a82000b6a29080081182c0d2a80c05803480d00c401d5010001070204440a0079030076482600040952910f850b43d40102c1c80c14001d01400c0b0000f01108400422080c910350050f0703010710b030000d9507071552940b034004004440866050100e243d50b9981d00802814618201c46984291b010f003034081201001d1010906403109219090b100d241d98000b410200040e42c410900c00e080b40d80740401c030b10f444400c4054060b2281503a20403405005421007010044200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 433139775 1250 433138525 433138547
    0x504021e0d0206031e091926070b0708100b0307050721030606171e04030203070f0303090213090803070e0316060806091b0409020f0903011a0f0603130210 68
    0x2c0c060742c2c0d43e89800c68005081c602d0f170309952407030658010041440083c00244d60810000c0744100301c0072504856031a01007000c440c40c40b02c07902402105d402c106141101d40604081c43c02400c0e101620301d40020001c02c0e45000a045038441e604124082c400100c0403000ea80e840900c07420103d0341c881a42c24054041c01c1d10f409181f020719103c4010749001a07040e0418001c80d982c2d512161a20030a000580c010f4001c11504001c0010707203007800821890420130707091307040740c000d0045e00d02e8018103807680c1448c01b5000000382d012a840d10541401c60501200c04103a044160070100f02c0803c040c0c3c0c42003107601c4058180010040001c502c0b07200c031740c3c0c14000c64400002008942440300da44401c082c0100c00c1c00c0703a429100d00c0c400000142c1c1104166084120120084071103813819040002040c0250820000a1503528041c000e02d201601d00740304107020502c18022114181501a040040c10307480a0f4246002d0101402800164400418604201581103c1c17922110245201c00c941604c07502d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 433141025 1250 433139775 433139779
    0x5030f0703052205040c030209030a030e060f03040606150201090506190e0a060b01021204060806060f2703010b030a0c09092f010206010f05030a0201031d010f020910030504021e0d02 80
    0x1c0b08004a144006000c60f802c5500c281c4007480214004001a0708a0165801541c0c15030020155000040d2080c5614160400010075140c1072041003440c28002d0340044600303e6005035034582c1404071400501030410148400d03c000c4c00103507142e40d25240c64050240c29814802407180d58415201000d400031030100282c40200c0300b4111a070f00b02540038108048106025000300400c400c401843d6004030340990307000341c4078000252941801d10402c4c0d4031400c0c0d101c49001c81849400d002c0030056401c003041c2008490440780395004e01040508544100041c280300398040000b18002604040340d640450741222000620614681001d280c811454613012130200d4100320f0714a0142e101e030420f440b50407130a0f800c58409030b0300c0e000d03c40414074042c0109a4543e0008440d0380040d071091f040040d2200e0040d62104110785c402c003180f07081d07450000d0211205500403400c14114203201540d50002001441c0c00e008506003030b0013042d241013090012071145500210400c100d41c5444580244560380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 433142275 1250 433141025 433141057
    0xa120b03120301030c0b03010f12030c150507080a1505060903010f020a051824030601120c0504240c1b030209010b030a1d3307080f0108060405030f070305 68
    0x216540036a55030b4000d020440b081d10585002103a400c4a44058038160b8070385903e40307030015040c0f803091100c1612001d03084003080a01c50401000035003c40242c0d020b03a801160204a504005138043d114031001442e0991261804c3c41c8103001140700c80c0c2c240d04999045c1c81c8190344030034400102e405018489143c9102c94000184c00c940254040c005001d6524010b156004442250f010004d01c40221000d0944a4840403559000700c0f080394015074000381c0504041100c1d60304500304805603800811702801284011904108034140c08454024002c407a8003020400c168003d00502054014035001e031000010301651000014044102d001441c0c006000043c1d641e500d680da514145d01c21614400090b041c000d141002010f100c480c8000011200050151801541c0201d06481901c08103240021214402c400301d4410440501d40900144d030f4072000c85180107d109c1c1481708044c0d0000c00907a000c8001c000c007045010003600c071041000200203603110940c1c1021203080c098a544480a448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 433143525 1250 433142275 433142293
    0xc0306010b130b07080a051c0608070602010f09050a030807020a1b0501030b1f1101060e011e050102061b18030d0c030f0302090105030c03131205130e0108030a120b03 73
    0x4504015010b04241000081c42035519150041064090504014034903001030051400407030041c0080c0120002a890285899004c4c007030980a0300d065500c801c1554011a41c01e001503035080c01030903416007800031306100344122542c42e20b42d5000d01e110060100311b150004600750620901007007144540010070b05204024640818400702211b20460b40031915290702c05807103007010403002e1031000d592130301c81500c9803103032030207881101410920820556070341c007002c200f490003010701c1800703058410100304403146a49040300300640d154000c075055501407810061a03444c442c800d01d107103513030403000c890b2a001500407000c5101c88807142ca581c9801454044440d2540c0103c502005034065600c0c111900b0820800758100c0c8140e418044c0064800c1001810701e00c000d1380110b400c07600c8100c440f05600c1c82910350148601d02000c8002c00a1b40000b440342c1d1342c82c404140c03440030300304000e69405254588503071240d4920400c031110042c48001a40482240c141e0b038040c410300702020b0240c404000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 433144775 1250 433143525 433143539
    0xa090b1504090606450906030501091511030a020c01020d090b070201050c0901050a0c021302040b03041406070e0d020d0215040f09050705092209080901120507020309040e0c030601 79
    0x303d28010840007074040c1c51041d00c101d001d9a910800c1d00481001343c00100200c200711385107140c0440f070021004000721400204101e50b442407400550140c400000c3d185418601003441c1c2444451030848a410045902240c1d20b0510440b6005507074204010b03a01d944204615019019050840707020078a803100007030911a0700d4050a120710701c15402000140e603000546421801641c0c6424001113003400410f840b14003614600303050600052041200000c12101030b001d99100d5008009003136804002d100030051003c04041c01c6074940000b422441c80d110740000c000354030b00101c5520804002d51003c0940d280c07610f56111103a0040c0c245110714000b0b0780c400841d030b0300512442840c106042c3c0300003551030703031481154005c09041d90341500e0001c2c80030401144400b80c1802c0c144020034107649529510147c8a8814058460364085486040301400500414002c040c480e80766400c003000c010280b6804001c0300e2081c2002c5500080210030360040ca85440c1507000710301e070540704607070000c903d0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 433146025 1250 433144775 433144781
    0x1051c051321020c0f0109080712051204031703040f061a01111902010302130b1602040506030105190e07080604232a060918060109140a090b150409 65
    0x8140103030380101800c503561088208102c401c041d03080058100342441041841c0000300d00107140e105151402400381c0b15a4228200001c13640700d0244102c6000c852010000700340800040f00c8078800e50b5606080c5191220a04603d50761252074200400000041c1040b90003000d81d844160824070400c0804482414144500c103070b10382c030381e011900103c40242801c0c00000d0300f0f910310402c0013624505928650040d0069000030040c5406484c0c00720000c5504014503025003c9a12030114100c01540e190041c00704440b0040c1c03125010741d0415080003005224506000480649417030300181703080c0301e0812182030400e2a040304150b40690003e2200340400c680c500783d09440250a220214140781540d01e50f0748016214565680011030b4140501c915480a11569440c0281c0038900d042c0c2142c0000d84515600401c404103d5800c1090107000e5a2000d5440c1c00b4140e2072070440d90896007113000903961130040c402e0b02446900c60040313a01c1500d41c0b4030705000c0340c10b0320000ca5445a4507005d400c005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 433147275 1250 433146025 433146061
    0xb031815010f1a09090c1b0d08100819030327060e0109020d0605060102070e07080a150b0409050402060f0304051e0d0503070309240606110f070501051c05 68
    0x4011903040407500e4014402e40c1c41d9514200c50302c0f1480d04118000717000c058071000304031412021091248910035580b00310030380010341c0110090081403141071006020024050a807580900c085001481482000121040c0f600c00200d15009064550302c0c0c11400792140c0003400d0340041c0781410308000c103803511041d0501223100e040240101c00c01d40b00740705e080307541140780a54041321040c04c05021481503484160003600c1031040d65121a180c855046403500c081d00c0c16000104218200301000c40944115000c8081406150003410318056000c1154020b078091410321507a1000444c0465aa81d803c0b5800620210351540e16413030f10782410fa443c1c3c100304840407070030350b81010084200b04020030750030301d80034064a405046848840d0220001d06203500102c0b8000034100e4171034000408120710310410040204046121400c04000070074401d982105614154010a40707840040004203540b0240c0b01d0a00c0c00720748501820007916028404031010880d01c41ca0030060018805102e11b001c21 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 433148525 1250 433147275 433147289
    0x3011509020a020c300102160b04020f040c050f130e090c090f060a090207150504061d06010807270f050f01170606131104080d020c06130b03181501 65
    0xc000d1804d1044c030210200001403200d01d0b41e07001c040d001c030148082c01c0c0b410414925800050038110b8401159205102c40e48043e00c40c0d000c400c0410045240010404004240a66040c0301d401c0180304042e0250146444442d020f0700f01144c1b403244c80d14100b074000f0080c03003c50b080310b0302420000b18054495150400b00c1d8064411640024080c1c861608014010040079000003040b901d0440244025001400202c030a010b00d60146048900f245c09040d0082c3d01807100011002c100503c031150261481d480f0707000c2608407400400c0074840100e00c084c1120002c124240c040a84c04000340004120a10048102880c2500100e0400801e60260b8400d040e8080c50000c1030b601da103400103c86a09034400351581c3d210f00000f03070386030805444862800d000c0e0300002c1400b02d036803144c1810715009500000810790228243c3c0c01201d0303040100820444003602c0c0c0328903203c40456070104079010740c0283e02200c2c800201150009400d000d100c0604030b07454050311921140c4180c2c91407141c40c00e1044034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 433149775 1250 433148525 433148533
    0x3130c0f0f0618180b0d031d030c1f02150103060c030c111009030e06040b09030616090306090203120d020d0f0c0e1905040518010507030b0f010c0203011509020a02 72
    0x2048a41c0240d44082034286400b0394018803502d00780c1813440c099910468500c056032511030f00c40366030f210b428040c1c03075540c40380e100c82ca421600c5864801501c40608112482075001900b503021b60740310350702d60401051a0050760142075040c803205030701d000702524031402c503411742100020522170640d221426121075035800348020740304650210745049044a090301540c1095450403031100169102290080c403c0c1402c040c107052403400201c958010340e012200d25071000841c01c0c0940f50070310946500183ca0311400803031050249006013894028003008044c1c6903540d0944081d95410818481084140801c180c0d0f1505c2a400c44006900b010003a01d21070b608040e28a000701e01346004814032050b060340c030384101c2e922000801c0380c460600b400c400e0904002c0030b00816191160700070544151065140c003071b0340416001d40503013100d000030701c0001094505540c44903d590b038401c405403075240074a02645418400e000290050800516a885030060310b4030021300016190050002c1030710940982e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 433151025 1250 433149775 433149779
    0x90a0317030a0e16060c11041104081908191b0f020907020c01020d20070608040314031003030309052505030c03060f060907140705011e14010b03130c0f0f 68
    0x4680c1e148462074040640c20301300c40090000510403108480c41d24000c4003010000c00070040031038222014483d4589141200040074460f1020811421007014900081400b0700344081e04c440b41c50b1700500d038240d00c0c00c1078042c00d000d0403103229880302071132000c00c0c1ca505c01820344a840c2280e1541620f4030100d0281c403040300020a03107400824000c00003103041e0090304031841401000c0703414650452000361a4910764508030002102048600d01414254071916201d0815043c090200e500d00c68486000807000c004001c201d0a10382c0b81841100c2e410306011900d80702d18030b4407900b80340030803803000c0a0800038810101c1c07410040750448216601903054a46159110042c1034030307208212410329a10030fa0b103010a009060184c01c155000c461468507018582034aa291721095101d10820f8403d60b46422000b001d02442401c194143c4040c0340e000c10904013500103244100b4014410003148601c044001803210608a0100071942d0703000ca854200d05403205c000a9000300c8034041c06555a140300c3c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 433152275 1250 433151025 433151051
    0x22115041b0804060e0703170304111e190308161211060412020a0206120118090213090311030a030f0c02010b1c0c090608010219140f090a0317030a 65
    0x54001850740c0365118041039440e5100c078800750000340c20200492103030b100004080b4245184031002040f440d01c2c180d40d03905150900d4075002c0e00c07849001e8403030301d1604949480100d114030300d09642d0310b00344c80844441094240b100b0060443e82d0010706441d50004010002081001307034100c046100388408d0440350700d402030489004000d0449291140d00c000c003c1000b182080e20b1601c80c01c2140d104031001602c3c680d02045030364020900d0f088403815414010300c20307156424840454110301c00800c000c3d10607550009006420785124044105644a19650600d4854082d03940314a580004485d038900038000004c0041401a0315010000d20f485a2890143d20601528889140c000c2c840810200c0280e05401d1111465004403000c081d099000910101c40340100e1004100b03003400143c640c884031461001002141103520f04012941ca180c03442080058152000700401c82541c5d51203410b02c0d4003245801c0e406401c0130b014503604041510280140b14001c41c071828a2003400e20407a070782004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 433153525 1250 433152275 433152311
    0x70605040609210812101e06081003020402160b011403030a110114160e1f140c01060902030106091d06010e06091806030f0304080d0302211504 63
    0xc64002502d8800d040001104900c1c104601449102540c02e0000c3c4940d500d6005501c020000314120510700e040180518a03041d1040c0148003d041403884031070000030400449845015000c14071032245c011610440200c2d0103100074680c0507000f15502c941d0001202c40c074520704541165410010800400e661480302242e01d02042c002e0002e504107141c644040d680810b00c2c0c00c06500035941e42c98500c0303407246040d51701400381c2c150407011002c90740c2610b402807451045800542c064041103034120240d0000b88200d9400030b00c0c40c980081100e1040e003001c1120300c80c2d0030b1001490b60806030081500201035000718100e1f11103896071500c0503555180142c0e1240305040c0641b04103548400108203502902040301e816000414461400051000051080300316842c980741c50001030b8104003d03400e00304521420701c40f42c440218101031620701103c1d95003116800700810150040b518202c01c4211190010001c0c044410101003403030070820b007a10b038000022900c0e09c02d5041a10a003c0303080018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 433154775 1250 433153525 433153529
    0xc010b0a03020f1c0c030b01051302071a090703060207050d080702120d110706020d062303060412140a0203070302010b01050301030203150405030d1e051803070b070306121407060504 80
    0x7a04034002c0a60b02410070507049001d04c04021203440031801c0400050600360380c1d5025510035140301410354100828001218800c0340200c0b9000c4c810441c410114441c51400107020b1b00d041c00c0884d4981d01d0001d101d04214841d4001010030f03001180300400c0000200d441d0060403565964841c055441150480e502c0e4a92091840100d40800030345407109115000010704000410129180c041c140d0354000c12a0720811002184958540e014059a0803000c1003150b01d001c110340030302200d0301c0d50700020748606000d040280301341184407055540c0d40c0110340c021b000110102586407a1301940c2c80107510307030744054000c41c0103520f0084000403540c09401542e0580790060014504055a042140e550640c003030019552840144a030719503c0b0740b00d010740e451003c11902c0b40e4a00b400c401c06c00400303994002e00011200e42a910008850180000984d110290810111001030b191001d0035801071561380c101c80400d01e06c100d00710f8244000401c082c1c030184a5042100c032500c0e9122802c6a0300d001d24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 433156025 1250 433154775 433154779
    0x110f0604120b130f0f02011403060a05010e0f1c0308161e0311030903071a0105100f0e040507090509070f020606040e1203011d0c280201090b010b0c010b0a0302 70
    0x9149401c0480e145490340c5a12140d0b0280184034403060f9219143c4000401c0d4040b5200b4135034580d61421968003ca00e041c0c039041c0001285c0c01e501b0104000f810700303c07407801481e0400c4200c2880e560b040c0d44289128030340b401d01034204a550481c2130141c40e41c2d007007002815408901d031000810342000001075100340b50301441c5e41d8070b40b2144400e800482d41c0b48008804004154850060b460010041d10040d401111000019a6201c0b100e161001484c905a15003011502d0300000401c9180c40310b507a44144c0d1289441c00b042c00280d1303003400352002d10307600e0312907500280303044c0030451140d4100340d418082c0c4604480440c0d41e90b568040c00c581000704e60303000380016003086010640506080c0c0100c840c41e8908000d8440c8405201c20005154000742d10250315000311014502c100c400f9180b8080c0c220072155111403800301408000c100e47c102e40014941c840340d1400c0c0e03201c070080c402e500c2a890503078482d0501044d960340e50360310302458100f45d1454010754603025038241c1c02d24000ca80e600440340c4c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 433157275 1250 433156025 433156049
    0x20706020f031b070f1e1b05030c040e0d180f060819090233132603070f080408010203190b030a050c09091c030225030e150405030a110f0604 62
    0xd030740741000d00101c5c6c80c180c40c0105649400600083c5100c40302d2004a200404920446140030101803403c0440320034103010f02c0c0380c000282d000e20004540680322506a00b000240c0c50510120a00c92606030340c00886800306003200460801d5204440500690381c0e40d200388a00100f000410040703944a220084d400f411300c0000300482c00048503550038201a86a06541042841403504201d0f40540780e08404141d408209001380081d03500d0900204604c01d202d07a402152460425039244251a4003a1554446003050420006440c2c2100c0290042c04025505c1e810a9464071654031500c41e404402c450919902d0852410005046240c035a000070092151182c61340c04d00c2840c0d000600115801d0251004490f4a000e850030810711075215a5401a640c0d0503107451030720540002500568160311a26020010a500110f5140c5030403003140c03400b850300c0449100c20168400e0764000c5406000d072980c4034003031040d2600c5160a45106617000c2c0c01e942d101c00d040080c06e100781e000300110700340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 433158525 1250 433157275 433157303
    0x31e030a080711032101080303010e01140a05061204030306080d05040509130f120314060d02100c0618150b09041e0203120a020d08190f020706020f031b07 68
    0x301c00c50300d59420030140e040c022003c080540724241160310502c802c240710200e884120340c201003004001030040c5000d101843c20340d41031000248400780180320b541829004000c1060480d070f41c40c00704200030400145010341e02d4810104041c080c201c221400d5010a00c0c0a8000840000c040b0303002aa1001d035544591409062104002080002602040501e40007074428400156030100304101980106140300d64040001d4005083d5540c2c41d4441064400c14814007281c0e03200c0d62040c0c1d003480c1c1d0469a80d2091790005100702e4010380c0c1103601400e01c5080c00714040401c06034488c59440f840c060780074000522b240d4a4010145c401c1755500681150400c40050017060500c0342000c00c0010368201110005120340000b40342694042c0301c1a00ca140010700700e00c1d00c03a01004003441040e035506000449182100c00150607842007000c0c01e1b51103860300d01c2d04142010ba03504580110b0f0348480700b151154088c1d4050207141e042128a60f00c0c80d250a0702c4c1801055140c402d407038005130f0080c0c810002c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 433159775 1250 433158525 433158527
    0x2010e07030b0a09060912020304031211060f04050a1a010503010b15030601030908070c06030c11010b03120c1603110306010518060d020d0609030c060b0613090b0f0d0b06031e030a 79
    0x20444130950781e9a9030f03440808000b40c42e40e1001100c1000990003161914103500b0100204000ca02030b54041c0101d0322041003a03083c2c04034025038840c00c0c0c00d407080784680c1d40d030800d1070500c910720300c00034000f01c907486000a072495240007040c1603d0081e4002c000700b03411007041c811640322015454904070014000296658401d400170320702c8500c224812824455560f41e0040069400d40044c808652030701c5008a110f030348141c4950182201c0360083c881a102d0b200442e1321a050350f200da01500100107440c0e4412101006248101481607001040d43c607528203014585e040c42d843d485101c0d015032400040d051424070701e903d20008000700c0e610401d0721014200103108034a10001c1b0380008250910a0114013030340305500c0d00074081d8403030b20011841480d081c0e08590142c0c000c00d10580b000d20440b80c10007441461310090760400c660028000710b013240091112044240b5850f0300030341050204003040000c2100c2402075000f90200c0d06817000304000501c480e8201108904203910070b00c00b0202035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 433161025 1250 433159775 433159781
    0x608070f03051b0402250209060d0b04030e0f030f0a0b0a06080304090e0705270603012003091603151104030f0807240207020909160303081b070c0602010e07030b0a 72
    0x44000c0c00149041d45014084001e400128803251000681c030746c9810641c14003400d0950302410856405200900310b41d240c411250380900003600300000c6003484c0155443d040180c41400e440142103a44503000d05282aa50b00c2c109403003111107040358804102d40e5022802000c040c0c40ca403034013841c2031605042c0d449008000340001c210340707881040b40000d0342e41c665140f2205811600c00030410b950040d00758101415401802c1300d4026071501c000602541c100c4610f841d0021910f400c82a9640c940e008540d02c2c0115420314003d0a002c810b50000030840040070301c08200603040000c1c031002c05605003400c101e00443c4405041c0c3c1c000c0084060010324000006e2804610071906000303800000701d56080000440c141d0445103d500050174419440d00c05141a40491903400500306000102c455200c01085440001e06018000021441d84072800c24010107114840020310f40b02e07030843c200071498200724171450f0055440d000800d03024100101d24901a240c0002010005840300900c41b401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 433162275 1250 433161025 433161073
    0x60111100f0b1f050c0111040902031f06020c0105091302121009050910050a02130311031005040206160503071703060f030303070f05090f0a0308030601140403050615060c01050a0608070f0305 84
    0x855561012039517407c0400701e01900242038108001030300ca01d4034250610403030707424032101503604501000400c8659800580481d2200b4286003450b01c400aa4001c1a0755242c0c5401c2501c0701400410100000200301c10054421108a46504061a0750f4521035045078401c6d5100c0051750049550891918404c1c0c10598001e102e45c0d10062400c1c03408404c000d001d42d102d410441d07000003a008980c40d10f207003c004002624050500801a90805600090841c410700542900d403440f41888082408418070949409503001507038a48840f01548685189500031203c0718810a00304800b0700c03a604000003601d110780d4558854000c0b07402120300989151b04055412a03222a9031141100507413650b00c070040c001d51080c941d240e100d01700000090000c402c008018440007800740010001b1038000681e40741c01c0270003558140e0b41c9150b46000306515129400c0c0388000b41d800c100c284080d100140d8000d800b11840300b01a10150307600c981613280c0307040003840060300d00e0380100405141041da120388202 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 433163525 1250 433162275 433162297
    0xc0c0c01201504060609021201170307021801090507110303040303050916090501080d02033a050103140c06090102150606070605011d1506070803060111100f0b1f05 72
    0x181222488240c1842e26600500d614500080a4188803c029150264402600d40d0280960412800751124503c2d00414800d20b1142c40843d6000d0744404402d00460b911180c014040141c440189050400c01800071b11541c0e654501d06000103940920904071420300c039001c50003071851a02c41d901c2c110060180130740860b405008003020080c03000c400c542100f0090298000100b072a40c503165110707085c0f05103600a2800d54000b0000c01000304c064041c104042110b0081d041ea420034441c1c2802e0030503040d0807003242d040b482c0c0380000c024800404440d180b640303440e0003140c203200e1410f01880b80ba40521101c00340544c2c000690f07a03501407510780e020350f407140c0c015096600340452a155441603a4080c0d00108403d072010011030440e110a002c0540d2010b407000100108900003030100e1030521568002410303400e00400880c00d603a100f103441c00100e03030080085544400818401e180102403080044188501c0c0650711034890902d0202100007c030a80700020100b600004181c44d29405050044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 433164775 1250 433163525 433163567
    0x170609040813081e0f0d050403030c080d050406060e1e130206091309020a0b0405010c030f020115090507091a0403030507020631080102030411101704060506090c0c0c01 74
    0xc5a400000c00011588421440c0841007148108004c0ca0070314005029401c4540c100b801919107140e000b40441b4100e0f81e051415482021300b030300304000a030085c41070070b80d0074038104420300090000540207070003652101c410620084d111100c52814030741c0c0703c03d0040c0c980c0202000060741505020050415030b07001804181c41c00500c440090040d4040f410b00f802201e0b070f120b09020a504090000201900f44012224640f600b4100080d100c41d0000800604001d50405c504c9100791003900302000107200f14940314003283d201c000800c06008101c580070b0008244400000d00c21800280d070a20703110310b58032068a0705066840c03c98840d03000d0b0300e06030b030000020030620050b50000242020709204c0c1d05030112180d6108800903442c8181139001850300c0e8018801d0002194000c02003066911084a00d180603000d1050203550700742e11000c41030465446901004240300450700514490001142c000b121b0365074650720b1004901800e014507070158010b40b02d80200c0d5009500480da9102e07c11707050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 433166025 1250 433164775 433164779
    0x90406030f0807210203090f01090305061806100506040b130302060d020d060b0c0c190f0f0807060207060503070c030c060c0e0f100e130f110703170609040813 70
    0x280c0300203560000c84a09000003003a0f001d00c0340c00740c10580300d900045413030501c0001c4000000d5607030185502062042da9543d4440d81c03680c1c0aa03140700021a4820291800d9140440d184400103e1f041040d84140c0542c0002440b100e10304000d501c03e8a0380102094206418000251000e0700410a1060f41240d28000440542c3e900409003210031025003000d81e5a0152034600710540f40e2661195405590070b20040c0034005000c64506115001540c103c000021180c401d048800301950141848408a1201041074441e90036000c05840b5110125820300d80d8a4a0482c8c0d00d204611680c80052014030101d040c8602c2041140800c6000c0d02d003842059070a9100d55049a200c11b010402013070650044e0f00950400503041d16440b4022128a0b400d003481b401c02030200c04c1000b80c103d100321850303811030b20000e81070f9001000c0740311440c41c01c02c500d84440d11310b02c0c403a40c401c100540204a521160103180c0600950b0b4601c50134000d00480080c0d142c0780da0348001500041c0311400d0066100f000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 433167275 1250 433166025 433166033
    0x25110106090615020d02070e0412031b03091a010b121008011d010b09151c06060305210a09090908090d05030a2c0f030f060408091e0d060209040603 65
    0x1d840143ca0403004400402e0702d40c0c100030f46800000002e000564014040c01c0000406004443d68490b41021800c1c200c541502001c400512540c0351800701d00540b50103c032a926031590000b41c0c410b100b02805e440f0340c110394110b0450008240b09500c451102080941c03c540021801c00b03403c808034140c2501a42c1d00c0f24102030a40309041140640300d01c04c640da0f014440b90900031410f1504003038503010581e04103121104070a2290603903a50207101c1545039202c48942c1256407070581504030f0000c100303072900c030b240090700c0c0d001c2c0407141d00004a00c452520003d550210440e2078030841034480302035052502020300c01500f0f0352041910350800a001091013030b00d03054000d050145c8150701860b9600d203007640240507142c4260031030031604030440740450078490000b915654258111540d00740c445028001070b00c4c002c100b00000322240581414042040540c102404810304111482500b110100080320310305980d03042c07041c1d8401941c50031500454040d60080c181c0c2c100240010a048d502c94031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 433168525 1250 433167275 433167281
    0x90305030d09110d0507060302220e07081e061c02130b01080702010e03040506030c0c1b040c030b2101110c060a0609050415052505030f2511010609 65
    0x2510800040d02c0b42e5248007000b01c80c000d0030840480494448160810648881d99200c00500403d4107156002850f80011000c1809201215110101ca155180d8490705654503814054500c43c0105210350003241038054040441749002e050a45030b001f0a0b550001040b51112a10892001000c0100141e40150720f0701d18a0002164120b03c01092046481000405a4600030080000c59140040041441202000f107904459041350000c1d22622580710704050361160080400180c07158940b200321030450024482c4402c0b1040381c0401009569140030350075104107070b101e80d80c401d04100381d8000f8600e1000d41170051010354000080c80c04a4504c200312280d12454540d9119885441005075a031401c0c05620060428840c05021504056a44146e6500b01800544020ba100c0c40020001c40804400b01a84000000e501991464254000c0c182e540182c4203e983c1c9032091000a4541413000d10300d012180a4003100408030000a9045900360303041c03c001c40c415502c0f030b5800581e405041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 433169775 1250 433168525 433168537
    0x30c21090d0f08100b090a050301021b06010906030b2403071e0909120507030c020301290a0f0911040905070f0f0f0806040207110a0303120c0804110f0109030503 71
    0x146607082024801516519860b8050801c2144203403c1100c0c13501c10669041c203c0daa01e58140d13446051100000b5500000b0750440d98040d8130128842d80120643c1d240c0003046103c4a042d194640d8891040c442a42da046c08090300611700d10002c5034051402082c411803841d000712949918001004c0001e0500b1819400021a40b50000c00d040d0005d4802e0031100041055480410a020b026655000c06040c40140c3c00e09100300030403000305050003040403d00540e0700600070131048101040640444003503010700360003c1000718180c0254208018a203064503401905124414940518500603111b0b12000c01e1142605010010300c110040c001c480c01054941c9031026852240e030b01c001c0c10645110130420400054210407203059810001540d000307081640e01603504e050310f060001e0f40010000c03141c0c2d00303c0b009090000c1456400b114211400c820b412045c4100110204200c0c0d04020540300076080245915a0b0308061130711307900c000ba5034001030514448041e41d9441e11425a08a1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 433171025 1250 433169775 433169791
    0x70f080c0909010e34080403090905040302030301140f01021b010309060e060f0c03150105070c0b16050c10081f05100305070e0901122409050102070203010b0114030c21 74
    0x80144035480d1101500100e04107018020f401d074040ea0b01720214020038081221805020071a400b24041c0751085080b6000b82546900c240039038100380ca4000d40e2984244940311250900710654079491030184042100c100d41640104403900c82022962111000c0009090506680d2000040061000c0c02440e801c00b58100181089203061405042210001481100c01c10401c001304101545288803c8a4114087c68101d441c0c4034103140074040031045400440c07960344040340c030404001c841e407000700308584103500343c46a505076202800315035505640c80401107410080002d182180c003c0d1249138480d5040c200c0a081c3c2d5484020a405903150480c07000065100c03810429007030741200c102e1030f825406903540a0658035180c0501c00392030340700c40024840d900c1c001c042d1916080c80c1003814030740110060b00308002d0b4401d10b072a034001c0d80104400c078029400d021740d2452541c042c0007a0034a004181403541d10f0b65540c103c6641c0250b204035102580c4240c00b4612244807022042501e10507191 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 433172275 1250 433171025 433171049
    0xd0c021005010603020f0a0305060409020a0909030e060406020d050931051003020d060504060b090c120921070303111813050c0d0f14090d110105070f080c090901 71
    0xc40c91141074074416040841454010090155618881800c841040049140004032500c4440004026001c0d000000c0c0d4451a10030b00440c0800c129031105000601c652103031100c00542d1f500340720050047e0b104060243e008a1980000c6501810080c510504003c1486086802c078840c0c408040d80592500c04000305820010444403100d03114061700300784161840322041c0d1441e80000c1600c1a6514000e01c0a0b844002142c100020341e040400701c4900100891040e29085100003001c1d04449812900aa070703c10120f0845000820000012265130318001c94400c1007070000c02c002e50045404408042d5a1308002400d0741483c006001e10320320849420314450700143c20091220821400114114503103018443d68500910882d024440c8040300800d0095502a07404000c10100704604007540203201044522213010038244121000c1d5200c0c01c1e0071451800029088450444940d0007050b00040710480c182e00440049500801078a01c1600d0000c3c418041104810b080e030000042c2c440d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 433173525 1250 433172275 433172293
    0x1210020c07080d0309050d2706030203070e01090518090f010f060311040b01021e01063b0907030b0a0f020c0a02011e080402060304020109030503181f080a110d0c02 72
    0x20303040c00f0340107114800d031406000310b0041e5181e454803101d0000c0107009108100e4016511030300d40c05110905d103134051f450703001c2450742c502e00580a50f0044034440001100d001070150740358003c40301c52003610f00140c907000852240d41c0e2051100c203000340c8240041d00c50414000e55005003405041c4111400e1b10000ca2010328502e0500c072520201c0003098030680c20301020700003699002440420880b01160400d84214a80d25407a00615507a04548900c80c0410162500100b40000d00560304264a190443d088003540309500000000e40d1800000d40000008001140814044c20f8224090040018500c161138003064100c0e4032051621075240c0240d41d8400642d83c0141a181855441041e801001110000c000f001424011b10092284002102040070369224040c0c442c06540d1010403a5541c8800300051500c2da1741d1410741900c00c0250701e003101c018410710204040c50603165240c104581d203d805141c4081c1039448426005400300344180c10700303040705000f0a0042c01090700030b889001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 433174775 1250 433173525 433173539
    0x307050702090426180103050a020c0a0c03140601060507030c08160308040614010f0501120e011103010f0b120612120d09060513050703033f051302010e1210020c07 72
    0x1070844115441844e40074051501032a1204281a925003000d20f8001381130340d03601040303800a028190201c040d43c454100382104000c1c5924080c01500c0c0030348070060140b05003104070b580d06c030400d01413500020780500c04040000d00495605c0c500d40c1c801c1c014a42012101043d00400d0000a4030640c00100c248007030006000c0d05110302c440724002c16003088084e6041180c520140e11403841901c0c100a2001c03950411703c0c5459216440440c0f10600070300c4580003184039285180c00c00e004004141c0c011500c0000c102c86d16400720755258000380100f00d2507540f510200f01c00300a1950b0341000600510100742e807060b10306801028a02034602c0f0010340400e46041000c100d070001843e180c003101c9410441c9000c01c0d4001114400c683d894030300000940d040e10340c4001c814110650410a51a0088510b010741405140c02e02026842d8202040143d031000002668015100c82c0a40490303140d42c2c03440340341d0805003d03601451484c00c040f501e0420900200d04126403224007409099000500244030300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 433176025 1250 433174775 433174823
    0x120a05150901030c060c15020c0a05100e0a020f04020705060a0c090504090f080708040b040f0e0a021c0c0207080616080609040512030a1b020a0203071d0c03070507020904 75
    0x3184099404214560640c1d44010303059140d03014842c00d00004407524020010500103400c0e1180d41600e0641d00e40e034511340d20603540d803082c01048589004041584005160f80e1140c1c240b10301108e8010182d4884e035800340100040102d10940d0401c0d020400880824405c10009026080c0e8070780000e548001704d000240450651b40045102c1d0781400d030110b02080d504030904640d9034201c01d40c0e0355151128901891144039076400307410703000e802160006843c000382803150112800c4440c540100e80e12070310781d817040f4400c8144103600d1a208442d0140300030b006501031002c03440c4600454006da5140c9199519103802122100000e40c1c10f0301d600020194020580303a00300e007007591400c002d410555501038030349400e0390034541500d40100010b1501503075a000841d00d856401440303c540d0a4440c40292a000002d905900a10074003600290302c47c800b81c400b52000c0d0a02c00120050384405094014036400a0701c030394100300040c4940000759403400e007614000c611070300ba202c0d60548002c1d0440e0310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 433177275 1250 433176025 433176061
    0xa03120b0d0b0f1012030806093301050c0106091a0d030c08070f0c060201051b0306100c060b12070f060c08030106110703050f1e0c0609060f120a05 65
    0x52036a8145100011405112036401c043d0500c11084a50b840b60380c4134803011440c2d0301c140c003210080c0144005041c2c018805501882e0b00b1b0b2658440380e690548001c007400c40040c5032030760402d039050f10980307144041d5a5440a00301c0500d441450070b07090000480c02e44004e504410400c1c2d0303582200e124012800301000f40c0614064440041e4600c0580740a00100700e00200909603100c001010810045009100000281d0002d0403200c52a101c09000f802407000b101c8410070300c0c280101303520307945c200341041ea489050021302200403107680c2481100d1407401918100d504c00d85a241d100c05980c1c64014210381d0404410007801e0480c60503a01d2408000c41f5800b0b0740c2801503020410f0007143e40101182e054940c0d40c201542029407040c42030349446206da001030903e01500c0c0d183d442002010581cce81e1101e121805204001c0c03408010161690004500f45030310090030030039100c8900f0148090281034890b0603105042444298808842c18401c03541c413020f60343d95400b0040001108010020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 433178525 1250 433177275 433177279
    0x100810350c030d0c0809090708090c01020a020f060a02120f09031005250e1f030b09010f090e160e06040f1404110d080409060e0603060702071203110a03120b 69
    0x1100059181c08640ca500c2c940c1c0c4030804000003050301c0c0c400e0004140880341039005c050410350403440c280c58001d01008096403e52080d018101c1e0076222903200180010303840d074005003504001c01c2c0950030410145c2c403944210f42035014000d140c440c50784081019098003807110407030b50741c1d800c0990304260508080140145181c0d18020034807104101d02003940d40d12000446c0350700000301004809881c0300f0803245c20980e000308040a1400044000300c0142070000954a0a12034440c1e450200701817482c2c01d010f0005e03120040c0b078007002004481d030031005080d101700059840c0b949001110080c0c030f802c80d420000918221000344890f9007418420007558090041c0300f002029290814903d0b0000042c101400700202c0380100d400965a58400420303031036010f801503a4961351081c18a014040e64810b0700381c00e41240d00015203174140412458400c0039a0b0780507003141c81c18007102c1880d4420043c000e03402c0082a08004d03444940802005a11034000c0c0c46c4d0426450712426032200355081c83c92054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 433179775 1250 433178525 433178533
    0x50705060d0f39080103060903140310030204060609080c1e181b0403050a03080604020409020c0601090f0902132301081b01020106062a060507050705100204030210081035 75
    0x3e5915803016506055070b82c04400400c4940080c02d0842e09190b04010340c0d04030701000000d01503123441ca41c030114210b030b00c240c3c2c0c00e100303403a80c0b4102582c580306503201701c0d11160007444021420345499600a810004205000c00d02c804c0304c1000f08200422040e48150352107515000d0011030200342c207044181c103806561f0186441d007550740b403070348560301141c00a091110a00104001d582c070b60b019500501014902191590164500f03039503144030070b101c1c5071145813500003a1200306049000350300300150041c1464400c04c80c2515244010b1001549a0424210b00340702152100580c0c011107008100c880c00038000d00c17040caa040c0c0d4500420030441419603141910410155405c0540494030001c030300702611080d006c000e4040f40480c03044100030f101900c0c0030300304002181c10402901c10a40a002121000030030031803d20100d10913804003951000c41d425103040d0140c458802c07076a1144001c014940516565007100d15640317102e00381c100310500940083d101c1c5011203043d419a200d07180c0014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 433181025 1250 433179775 433179881
    0x80c010b09070f210c050a080901020304080f0f07170306030d0e090c0901030908040806011811040b0304020d0506090f12190804050a170405090c07050705060d0f 71
    0x15100c1440b11034001d043c0300550b1821200d66503d0104e01c18504808032040c400020324140081481d40211643e42c081100d000116145050510035680304541c0101e184d440c2003100c4603c04102d820500e0300b980040401c008800000f01c0040800c0c144160081c400ca460781420420181080300d00002801081701c60f06054095548020b951b07604402a0240c41d80e42d1078803500100c014101e0f1450190010b0340005d80003501d600c0009406040760000240070b451031f2455040f090a035542c4100e0713141088024001400f114200c6802190000c0c80207180410042060781d03002e00340300085900c40502c0e00820352010440500b4003282401c01140c5809c0c1e403800554147d5151048042688ea104200c002c9000070104002000342d9400b20380c1000d14025110031544040d01c00b0380c4540185402000c1120125490380142810740341c146901170041c10040d403c0000703000c070b0b540000521050301516000c1155801030103208901802e4507041081d234202ca9a40321680903c4010b81e03105107036802c101c1e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 433182275 1250 433181025 433181027
    0xc051807050a09032a050a0f0b0d0603021e090a090206040306090c030f110312070809042703030f05150a060c080d020315012304090b03070909080c010b0907 69
    0x1519a200340c16040c034030380ba0050503030221140c0c5041d030001801810b00c80c041355038180441840c50614003040c4004154582c46405105a021140c41215006000150280000402000640314000d808100042c2640e41c940004840781000942110a009241003141e11030400840700f2742e100c0e2840b54107014222040c0d012030075602c21440702415180e030b01c0c09010704204255403100000d54015034005030690320b0b81030841051050864680c401d01c2510410340f1070840500030b84da1f505420403501c604019081d02884041c10450030250b00c540c5d4900c0c042000f5a04460b1541880c070701a0754000f8400d00e0044054080303e0001e4050801e0b00030041c1c0030134041da9040e00060a803003a174500050b41d100301c0d140c9660a030150b00340c00071880e400841082500e0f1025005203c2c4030109036110f4903600000100c82070b03024a034002e00710301c42d00100014082088250002c415601000c0c044a0060369207000b880100c403202401244c120b400043d40c812410002d000d0381d4400e4404440620803030500d031070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 433183525 1250 433182275 433182319
    0x130603050709050d06090203060c300a020d0615090807170c130b0406060c150608030a0c050f0111280207150e040c081602010e07060e031207030305040c05 68
    0x100302849881981e84904c1004500e811440c04203502804481d150b090071100c0c07440310b41220441c2c46440001c1101610005414242e1503005902c00040c03242940b283e00e2104069030200d103965244a44400b00045c4d000b010780c403040c501070380355070380d2500207420710790190306001c100c0c1e2246c0080800211800301981c80854409960901142c0440310b06d0400306207200904200c890450748070303140240c00144035030098030204085104403803510280244445d450304960040c002d82d40198000e201922025015000c03a03c2c00c58016400c03107446c5050a000b9500790350b258081046417520105862545101d96000404000c00c41d08285880041202d8025070b507003000c3c032402d010000c0b050301031071060b40161150800340c20041d0003800f0b0341c880e024019103404415035070b00c011680c90440d4502c0c243d00c1032245c1008050b040300544490307450824100c440344201b50141d40d250040c040180e01038901c050090801c01d1003924003240c0c034601800d1418900031f0a500a40c000d00680540c005140300d505 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 433184775 1250 433183525 433183529
    0x4090615081605060913051f08210307080612070905010b04151e030b04060504180201020c010309020d02191d10120506071d060a0203070501150617040303020d0c05130603050709 78
    0x14000103415940d102d1110a110710303545030200a68241302009c81c0010011850391101d88160880c0010070788203403400c020138402140e902000a070a040422498900944000c8025225800315800561a500b6020882e88281d10140000c14001001c002880c140c181c2c000c00e841c0d03641006810261061807500c0740701c8610305072000b01903032046814000d80d541d900ca8806010064803c016000c20b058a00c940305015030002d90140c803a0703000032507440d0303c00d024028a827075026003032284c0072021f40d0074400e01c0c0034040a4621000081480402c007000fa906115403241c50382c4240c041d02e03081402260306902d07519001001e0340b0320b07001120b1000c580c0c005101c0c0e030000100e18101d100c03665840c90100c606032116800e02e902440c006004081d095001019280c6940250002c00c03404c81c8500d0b2075098000b01b48100d00c00f0400c18410f621450042c0841d03903034400d0103810090b1501040780310710070407940c040a03c0da010030408030790880295400591480038010501b01005142030000d00035102d03400da4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 433186025 1250 433184775 433184809
    0x306060d0e010915020909180a060b04091209060e0a061b030309080406020106060e180613090c06080702011508120702060c070905061203040302010e040906150816050609 75
    0x1d584100084a00750b110344151500555400707000d51402c81c040c0060741c40700301c0c003e2052101e03401140d88604c031006c0790b19280c0480700c02000c0000701a990307140902904640b16a006d540c405c1e0341c0c1e02050520300c084e0b60640c119075909100318149035000c1c11080b80b8490181c0580d82e80c41080c004180c11540c40c27190110215014525001c40d0316040703000d04002c2400406040c800310b000521513070150480010785c0c0c142c0d01d40903125040c0303005108030380c0e0030100c0042001c1ca0f404045451810030032562504001e1900d004591690645c0381d940d0145015480040000c00100804c400d0039420b200d60080c0d440302440388400c2d1480c1210f000c0c0c3c2c036a420b5414400d11040000d07600f0440da102030864941103000c0056a40d01c0e0307a01c0c942000245000c69160f4000c00c5075a04654511002008a0302038950503151810341301102000e000080800e40310490302c0659032460904244c2584514200520303445d402852001d41045101d00f07800321035401103004202c2070024003969038170901e84441c00307280 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 433187275 1250 433186025 433186031
    0x3050d14033d06020d030e120702013506010302070c0b0901030e0714030115032604051804060b030a05060c03100b03040c060816081902041e0f06050306060d 69
    0xc454260a002c0c414050204020201121148014580c03205202c02c031940ca8081c0c0d1015000d10b0740540c01d8032180d4610712034681000004005007181c400113002c245006260007400031444860749204c03400308100701e521502002507501608000740c8501039000c5428602542003000350340d500d0b4020605409549504800800c603600f40364401d40c801e0001c1c00c1075808031980c5035515400c46c0c01811f510316501e4003070750030a13100701b411f020440307204d0084a43c00641c08600007925218051011100754246403d000300b04000500d60f650303104156200c0c210901200d123103042c10b15241d411100102e090501940114080c40c02195000c02c480fa03108964000b1159070765120901200381c000c1c1c40d08003608044022086c0428040c0f02250f04054034460b4541000d1525100b0841c0344903030781c0c001448e00046602000640c01920700c185d0014141c4140005814562140240d40003d0b580c0c1062101000002c40104000c0d00f40752140c10091116060003803550402c81c0105040d0700c10901480d5030261 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 433188525 1250 433187275 433187311
    0x60c0e09060904051906060e010b0a140a0e040606030b010305010e0c090405041401151514030103020d0c2d1a1209160e010e060f01020d0c031809020403050d1403 71
    0x20601c24155906010b800345d01580f029480c001c0020481c601449408040d00c0300040364030418072048400711002f6480714061018160100c0b01c850380b0220a040405c00c9070540200540c07101c1c080d0030007508031503c010030a00c50320300005040b00e80503441104291542d41c24850040001021150308000036500420140d840d800e045845001000c20482150700c0c10704203840e84c04808245070b06850070741d501441d1598401004440104007201d864130b0303a44080004100500d0070110100345c1a20851044480d6541d80500c16a81c2002104c00b032a01c240c0e10351010071403c04680001e0140003100d60204a148025004400e140912b4042600205090001c01c4a1100411441c03000004040c00c02d03003103903103880c1c1204520400703114005403032946501240180c50710400d421140301041e402030032495000d20048424040700340d0142e0a01c512006001d140406111080300a0010000c0c0940e4443c03640c40c10900d444250048002005285040c280740c8014000841c3d4001207003400c3c50110013 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 433189775 1250 433188525 433188533
    0x60607030504030c0b030118020403052d0d02070911120402041503050d030b010e042f0c0708010e12030c030c0d110a030c020c010c020303040312030204050d03050304060c0e09060904 80
    0x110031500050030380680f8003000269205c2400c01141603448812103504000341d50b00b03020050f8040c03404014a90b4010717a884034260600c2d41d07030441000240782d440c1000f0340f03a0400c00a0400c1e600003d07010041e04480001d018000c0140076100d5002948800310307281400c025100d0034a414040e03c003e11882d00d030b030035480100c151000800061900081034503070010180a000d03008000c20041c60740030880100d664001440c0c90310460505036148203031046256541d61078012001254030001aa8003818045840c080710100001c1001d00882800007403e00f01860f1031625091400c0c0d0803082400c0204108070b0800311150549030400d00b446d40060321625001a460090000b901084030320140101e080802c40350302d50071007580f8a01580a03200d11110440044500c9002648042e4040e80200320820000b2502610b0072410343d400d140c014100b0f51120002076000d5040d1400b0b400161000c8140000c0c003107140300d46512015581040c041c406100d0010840011004019501c1030a2100c0010184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 433191025 1250 433189775 433189777
    0xe0a0e0a080409050f060a0b0a08061311030604052211010e2d0108060105070b04060902150d1103011a03070905060c030c0f06070203070f05071802032d0606070305 72
    0x200c1d41c007429a540351a107030b00c20f83d4001c00c01151954501031071240466002e0800c2541401a2500710440302d00c0c0c050a40e1044d190284050445c0f60000b1400c0d030030a885e24081c0c491103182208104a1945e80d003451805c0009480000d8021116074018075102e03c1c0280410803040d003525030041c2e120b1403500c031100c0140d5100c3c860508254005203051603541408040a4010400148a841c11881019440011120790004440f0180416003c0141001180d2960502c03980644620404540752241d039001c1100c45480b040030311000400403035800c60001460040340365245070203e406003950b150012001d01703046081c0141600210000218108038030a080040c040c01c00074043c555501080c003809640c17a40a42d00c500d126004640800400a202081c030380d0094000c1d1f4010350801d56291a18842041902c0c0c2c1107480d44070b0035000148003a55084006503228147c8030040e03c0c0d1414200c1003961a2203c40c0407282540191039294000050444445e00414160342c0c190300c1d480300d0b1a00341c0d12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 433192275 1250 433191025 433191043
    0x120a1202090a1e150503071b030801060302091f05070b01080a0b0a050c09041b17010f21050d050406030b010503100612020714010b0301111602010f03110d09050c0a0e0a0e 75
    0x140e10003414a004e031060308480118094183c0f665610000114020034940400c8030f0132001307001a28840040224600ca50081e0052079001082160482c1402c0d1903042c02d91104800600402e0011400340b05106015441e40e00501440d4043c11901c0c0b020b0740e4040315000c000f0101d5940d15a11303c00b041040f0780190556601c0240a00100015044402c411006400800200c000110306a000f8490a95900b081504a52110031540b451a0503c0d006003455044c00801455000007012600b02051302004540d50070601511015030b03076414508001c0c00d8400003400d56062100420511084001d411803407001c5818510300f00d804485103010520281c4114072028064414071080350304807000640c44440b07400f108030000c224641c44140052054056181d14600380308980f141c0304050750044800040f0fa181c0c40c0390009200f058032079003107000d801c00b20205480c0755031101a0001c0103070030015034544010460703051010034034041c0b00411840e0000c06030f118494850310012040c100422a40c65 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 433193525 1250 433192275 433192289
    0x40203040c0320120304060c0204090302151008060601030209030303041407080a030914042d060b030406020a0905090606160807050f100f0903050a030518120a1202090a1e 75
    0x84038502501d035080e03d2904000b401d4030603860342c2d401e420103200020469085449a883e581c040c41d8003038003040000c2c5044001a8190b00a8071410303100310920354211441054180e5400801c02c1c01c111500f890000c0c000c060078180b600c1000381c264280e0700002943e9002d80d0003e940c580400300d200910b41810b0301ea41c4202101c8c07081c0c100034800c01d608414050103452001d9020310403225448100b200390307050024022288844200c4580300380d070300803041c114400c02990020400640d1134070305280b56441180c080e0368450f80440c01103169035024014100174413089440c520702d0f0a1940000303040d4400d0706030340358803907560500103010440c140094a2145030803500fa190111003a0807032540381c0c2080701c0d43c84c80c414540002c0e4070400b0300344c1c0700300c1c045a501341e40d800741899080003080e4000e04000e0801420180c07003680d00d444003030b01040b045900d01c00016400c0d0700c424101e103000d0070b490b1100300c2c1030b000e140c010300221182d5110324080200311600002601348081036a4032283d040c201c1a003000c0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 433194775 1250 433193525 433193543
    0xd11030f1c060b0a1d040507092606040609200603160c06050f0f0906010b190216080313090216020d300e0d0308010b1e04030b070311030403020a02040203040c03 71
    0x1200709400611208000c0380100610803407002d000c5c10041102c10454440300456015901404401001c15545000a8880364504c444030341c0404040d241c20340803202104c0700c548601d050400c03c08100c404c0c501203086164600301c2e441c1c0101c0000c909001c01015038054444800c01401618411484004945d030082820030090070040e081111400089654454003049040420700d070a0700086d1150481d10702c17030086810040a4025504841113a1012004600c260b80700e5034194200071002e0b03030080c040321005680d50302032070440b0700c3d0802855002d5003c040c0f0500c01c0c00c00121100c4c1c89076811030390413130f0000043d11952078100c00601e0004a1880c03082c0d0008140754501080000703004440380107856040c1c07a039502c81e04008080c4141074000300000c86e2200100810400381c0068018113421700c420094020900703100101c107410035407082e140081d102d000e00c0485d5416100390b04d10300c46400b081034554070340750710060340c0d440506000034001ca0740080000c00703201540b1210000b43d07501045070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 433196025 1250 433194775 433194787
    0x50a030b0402030f040203120313110f0310060608010b04080a02040f02120a06050103060504020a0e041505120c0405100305061501090f06030e01050f07021216140d11030f1c060b 78
    0x14030380031300040310103d0180c0709540c00b85100e880d07600b095a12821b101c071503010700f0400c59950002100c400b00c06403604403108240c1c004ad580e03414800e44600d0a418000001e01c140340c80e10060a04006901941c00000e040200b4131060b4030106208034815010b86d8003003100d00280300400001d2185040d91ba40744e90045c810f001c1c8841490f00400c0c211402640c09110094450081004900c80d0b20322090204185507003840c1c150400e0303000400b0004921400c2a03d965807000400c00000c0c49414500c074a070020040a107480c64107102e159005440c1c4008011100c1c155550b443c3d8034040542914000c120314a40040a680f040207000040e210b09241b1001c3d01c0d0b95810042c014141c0321120740340365402c3c41c0010f0318001d00c0e10240da03c64116680181140305041d800d1500c5a8000300e1000c40424001d400700b000b08603008068100d228003600240306000b00940d0003807034440d07125000c8110350000c102001007003002c14117403414201042d60710a441403000340988010400d40d44800003140e004604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 433197275 1250 433196025 433196041
    0x9010215010510050705030f16141f0e07051e0117040209011a090a090e190209070c0303020904020a08090706031104061d0d05070f05030304080d08060109030f2108100303050a030b040203 82
    0x2251106224a0ac00b0003020b04803d44191140001c145241e900c1010048000c00c58240f174000d8040c40403008140d03000030b6200e001084440003a1281482502c088030080c2d2210b50b400315510441c802c1003461149a0704199001645240d010301c201d00c012802402d450030364403000d408640011000802c54200280d0700c00d00000a4010f40d004030010b8003c14018500e00d0909880500005d54010302e90803081d5104041039603c103a2140003601050350901035002c41e42c0b500c0c8014800e90100791034080251030829580e030715140c403603080328003010300f000c01000710815003a0a40d07040c0c81c440d0030b044010900070780c07010b5039003004402c03069072020425064070117000d00800c07080e01760b41058008a20081c1c9403c14156030340b04500c181d4515512480082081510428130305400482c149466011545d403500c844060009030343c0c05595000d400308003285d0010500c08080400c1441e4103003002c0f5850807488100b0008510320010b4288480041d050104a03c654000801000c000b4411501c81c10107440c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 433198525 1250 433197275 433197307
    0x5091501060f1e0f1202040e0f090d020a0b01140607050102030708091204060813060605030609060f0709060804030c02120d1808060103020306010b0f1c0209010215010510050705030f 80
    0x1c03800b40424032402c808401440d00c031031143c10080040d15000e0700401c0d11541180c48420786602d40a003180e0a20020481844031312030540034a900035101140307420468815824511080c2e007040035580480c40e850006000c8245060454040343c0f000e964000320080810304611685200070401e5100004000f801600b1070015405410a5411a040700038214061266403146000c5e12012070140e000141d0f410440110424840f4810000450815954000300340f0303040d17042c2c1e400c150b140c004004200c0101d1515034240d600c60390b1464510030551810901405859010700090208040c1200010654450f1080b485400f141b1008036146284020002082e498409111000c00c02d200880091000000190075041e241c00a001d085aa4680750078a203041d80b00790221910040203000720300403800c0c5039002003007a00d00000b0143e915440b9400080c01c02c80d0f0781e642d0a4404055000600c8551120303c10a540b00340e03030b42002075031303103149092042c5540a004440c20083c1000034100070303a01c012007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 433199775 1250 433198525 433198547
    0x1121e051c08060a03200a0312080703020403110603091e0c0306010815011701092112050705090d06021306020c01020709060608070e0105090306010e15040b130509150106 75
    0x303070141c8400088007800c40d0512400d840c3c0c3c550000854500740081071701070040ea000c0b2000c28844050480254020641d20041340d401918805080078400142c65000607580342e0044803807a0441c901421030307603001d01815039080c1d120700a031408400121031000400454555030462906950b80d11245500c0c20754a11280e53307510f010740144e50000620090006107d440c01e60b080403205420703803d04d020f0f03640486c82510300760541d64841080d0b00100d035048509224074500e00302502e203000702280000c0d040301c6a13003c200a034070349482c0030405030380d41c400103075000c0040c12103002521880e01d0914030060701410000040b540010319001906a400290a0118503403e800303036101250380701e001100703c41240c41000c011030782c1d410000c0c1100d4400c0400615001c0141801ca09040140c000700340703050b509070081001100b0324014482c43c1442c01f50500c0751090f0444040c052000039502150009a01212503111a51104081941c4160510041303940f070b006410410304035a580c45c2c0040000300c1074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 433201025 1250 433199775 433199803
    0x603080315060319090317040b061e011e0e03030309060703140403090b0928060306050d020f130b03060a0903030609060311130b0604080a0c0801020405010801121e05 73
    0x280c60804107080c180b0075680f14850101da550607a410609043d005410b01280440c00c00000589510500380c1c610711940c042c6005940000c0c0c103141c2801444001c60011184900441c0d40000200e500d030307440b1105c178254020002c10080c40c01000c0d02c0603135001040900343d5030301d404003004004580800051051140020703540a00c8040075000c040710020744180c5000e80014610f2509001d0388494400a05441e400075040000c11a05e44ca100441038101015442d41c0d440715400c10800a0f134540605005408100c81c11288440c09500041c5040d002c55680d600030003000400a5100382180d105495908000e41a00c1c801d00e0203800c1701c001080e01c00e00842c0800d1500001089030a8148a1041500c1d8071950004c40030358010b007040164038200c02d1703a00c04c0a45490002200c0d456020240c0014003201d0000c1c1075062641c504121050510703044648260b1062000308030681e40721560504545401c9915080ba440c00e08140f220051624400c000c01404d103580b4800b000800140d05c0f1141a0b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 433202275 1250 433201025 433201051
    0xb15072310091a0c2b060303020c0f040218010e0a08060c210f010e090a05010c020c0a0902090a0b1602040603030923090610210212090a020312090d0606030803 70
    0x1568441a03607003911080b000f100d06101e59a44840300c544030385d80c014601c80008a03603031082c0c0078000c15102950401c50041e0030494941c016410820b0409100c0306003110190300700350300380340402c0d0302812001e0201c1c10003515008070149920b035000c0e54000b0f811000150340c46880c0c0000402d0b42d80e4024012551b848806044129a40d603400401e10301800c0d2100f8181c42c941d10b400800c002500d0301404c0401710b40a520211400640244100440041141c01230718010612030704001c401e41456119501d240d00402000c0c00560341e65601c10191a900e124960316000d10400004c281024004029003052810300044145500f054040b411a072620402d10f0890f12a00c0801c1107542d9100d50340c5400c6402840810a00d01e030003a0941c02d40c10861400381040401005d000a0341d4440c03218204802da80000c1801102c202410016481450b0340020401150b440c3d0200b0b0b40c0b032000c000c5000803c0008611803c080d5101d002001c0d0064110b5400d22101e900c2c0e0800c1032040d40152200c18a000d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 433203525 1250 433202275 433202303
    0x203011d090106080303190219090914041e030c060f02130503011a040203090c15070203010e0f150c1909050f040612080306040b1003050106030b1507231009 69
    0x441402403e0035a04043d010b182151240705032450461b041d038096038502c82d002d2081014240e211244403e0b802855621014840d1400032044105c07410b804800f40c1c50342c40c8004200c01710350071109001b0341c0d404601a902c41c0c1c100c1400c044407800c280340e5004000768240840d120898205401405003014241050203c80340e450381090700b01c0703006008454465180c481c1c407080c1407405902459003ea14842074602442100b400161480c2441d0380302002d05038081103202c1542001d20400d4014110000100034106c40198200ea841d0200608445080c6000c00017800c1d8481010594030000809540c0380d0340400d2291025003903031518041d2600801c22001003c0070342c64240986011114494840881c035103054071100519400104115081a2201300305003482c0c5850070007004200b25136070005511350512a0040540b04815411485000000011080c0f40304c001c2c02c41d10015441900b601070b400c40d003101104650440441043e650142c11105660300703001c2e0f082a090588a1800490411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 433204775 1250 433203525 433203541
    0xc180e060f10060c051b0a080709020d0e0708060a18061d0609030901051b01020c0712060e011b030c020c06030c040e060d08070b2e030308060d15110705010203011d 72
    0x4c180f2000103001070b809641003214040c100c0e040008001409020382000944030441280f0b00041c91744407150290340000c0d00981c034011440b944110245000144c9440d03031400c0c201035a1280044c1004050564808030b040d04860002164409168014018041c961500c1000003400044a41c0342c80c8130700a8400040b030132200407007103541240c4140c4915040440b108800003a1f511180510283d665003080081251a13040001c3e000800d44140c41d044800c0b02850014107551000314030009581c10800100c082e0f0310650007a4482140c14500010b940252181c220b117080d40c2c0d080480c0e082100081845143d1006400400613070303c8011900c9001d444940600c0100300d04c108020706800c07400d00401d030000d501100c0054221612a910300720b449816161801c8043c140c2d081808410300d40c400c2041010742100c44181e002d1800c54010411919036124013081e02d041c88014500c0c00e680d00d190074032100c2d4800c01c1d42c4032745030008002c41d12503854005800110307081604002c1c0ba840350b0f1001440203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 433206025 1250 433204775 433204787
    0x50d0c080a0b03280f06050a020322030807030207082a010b1c02240406030b0f100905040c170c04030611040807140f120105070305130c180e060f1006 66
    0x1100040706005490112140c4031006040e804c90300f203446100b400f40e60800301d492405180d01884000b540140d032410718a119076010b480035040ca4030030311400305600c1c0220b5002841d2640c01191810302503038805562600b1880351290100200020540d00551000342428110420380010035500802606140304100040e014600b8030480715080030140582c018203041500000c030780000074607031904015451520344079401c65003044001958800e001e851516080a40449141c0705440911005696940045c00d0399454020315003eaa00c0d1581000c00744d01c642c00201d8420030102c019152410081403408c1907501610094413114100a0060403c040f100105c074100e5504400a004803480c1c8031104d0000315800c00c2095100500300712a9585072150841da00e50981004000201ea2a00e080d02400316075000d008408a451705a44060000380e59003041010354201d1003010030816034880c4400060318016000400500618041c0622402c100c49014007507040c00941c06040c60320780c2d408443c0c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 433207275 1250 433206025 433206043
    0x1c1409100c150e0a171308030c06010e07050d090215070c03060b01020f0a29010611011505060418060b040f0e060316050904050a061e060b120402010807050d0c080a0b03 74
    0x1990071120112000038a003100051002d41c01020385c03410300113030380c8214500042d40d41c00720000c5e8100203401001c80c1020700541b0b001d000f00020f001100d0500071001011402114820b5503010350780d1000d0015540e030b650440c0c80d00b0550082190340c1d016103113810a10027107144001c0701c840d410981200900e40c00890584400c4500a008000c3d0161540b81c0c01e010900f03503081c0f55490316030411040580e03a8141460340c080c200c240c44a01c401d94940050303a08540c050610580d6455108000b40410340e038620841d0103d40144501152448000344020003d005d10f0f032121100280005000522821070502a01101c800d0841d07586141e03200e0083c152102d1502000001c1c03461980340910080c580600140d0300140140c007110401074256446d141212812144a460074002c1d00304003203140781c24001d02c80078080b0303515000e0824507203042e1102142000742000381071150545c00204c86512030800d1b20041c0c0039a05c810300620261002c003400007030040e41c55546040c1047c00300400c0c0d00340080d9080f4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 433208525 1250 433207275 433207301
    0xb07180b13050123090d06090f080a0f09060203030c0d0213091b02010606051603050706241703030c0313290a020304240e0f011d1c1409100c15 63
    0xca0320300756400308804903592846c22140f4170760310b15030440030030101c2c041c46c4a01442070202507580c122a00024219003280d8035000c080240103001402400e5000c01625002450b4001d4184c68104010303d201c042d01030072041d0f2001c0440d0034000200c900d401d800655104118402c0840403041c0795100701e080e26958014200441d10030072202040b03840789200c406840d8000d1800c1e07414407031180e5a0340280e94440d84a030841c0c0c035540300034010f03454480401d10700408a00740c920f04d0108680c109280c40b800001c0509100301800f00000c0c2c0030715040c0a5110300954402d80780d82e66154844902040513002d0354016900f1a00e020010705101540c0c404c80f4015030f007001203c1d5400740c030016680400c4900803000c070f0f0040d0300c81d07001101c007000400c01d03803560107201c00010031681c11081d2200130030315102450078100c1c0e00001404d610350b02e9102040e000a81589000c031505101c400b044603d07446013411140d04041329401100307140d42d10103494a16544a2080d0a04080d03010a03004156661820b6102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 433209775 1250 433208525 433208527
    0x31d06100b0412261209010e0706360609140d0f020d05070b07080304140a0c090e071805060a0f05010f0315050414041a040b07180b13050123 62
    0x100c0030401150319540841070f03082520f80e84c007104802c0d910b61500318000c62a44510000240100140b00303015807900750342c809008101007454410300501056401e699a0150b03c20040b51100c0300305507100f406115000c0804d0342610316503524001b0103042c0a0300c1111004074150701030525500c3e000e40110a06900b0000000c8120207030f40030025185050701d0112050300c202900000c246081c43c024012103400748507019181e1802c0d0604c030b26010404e100c40f0302c81c2d40000c5684000104400481800d940b900320340094090024540c0728034000e5190011602c0301d900c07600d000f448482d2504680e1040c030040d10402c2c40143e40c0c3c5844162a6010700503070b80800c240505415040d4441c0c0d001c1400d241040e507000c0b0b4078907036501c007003000ca13040488210340000e2070700100000d11aa100c07006186444005080e4031624250b11050340d5801d002d465038040064406400108100d070743d030b40ca405450f40181d030580da007542c0e00c910200c0b9509849808e020850001c1d20368211800401000348002d000b011103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 433211025 1250 433209775 433209809
    0x206011203120b0907020102040302040608190b15030102030a0e010b030616231204020114030c030411010e0405070305330607020117090d0905121c031d06100b04 71
    0xa6601d0b420120001c031160ba41c4009000569841c944060b02139032854000507522402d5006000070f072400b80c1c01c049000c1d4820380e545c032500f2020308100c0d8601500204605a1502c03020007020958000031022681907001100b40070740f0010302d911405211012100030010041c445003403540321103088418111216105d4100c4500b20300501040c2c01c031041d02d400d01030018500c0910360502d0f812840c6018505d40540c2c04210440d45c01c0035845c103c554049882d1401c0d450800d004003082d110061004003c0301408103540030b41d90080035548005800180144020f00c3c01030310040041c00100c0e0f840c0b0321245411441000212107540e41c0300030060100d050704000c901442800403540c0440e00803410000440d240500140317540c400305010702940c002809000481800003080b07001c031a0800361242d5500044020000c40001d0b0b420b48501d504903203050b100302e482c2c3c0103600070908140c07050400720411b05403040101c0045140780c0f040e4900301103000c0c420b8880c00301c0003507030155008125480003802c0407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 433212275 1250 433211025 433211027
    0x307150b041b110a050a140d1d0d020d0b04060903020709020901090e040c0521071a090d060f02040b030a0c030209010219050a32010b030a02040209040b0402041d070206011203 77
    0x143c6a140d42e2071104850070502540d90f82c925200380c00c2001d9402040d000c2c2c1004602400344090280c5100300d20b0400c1d0443c1d0403503c9610b07582201c020040c40795103210740c840d0440d00c0e0611045030712900000c0b80742d03c0785418201038001d040c0103c8103c0c018050100041074000b01d0303100b920140761701070f0354074842c107414510012165903003c0d10580342505d50707040019aa039030f040011070400d0001034580c03840c82c0441107032500d018030075000917a0f80005030982a80c203100040641c0c5000b81c0c111075100040106003065801011080006010180002004154001110000c0d0b00920308000c04000505a20000300c089005960000b801a00000c00c0100b81c01c00c000800d108550052054564040c107681d00c100c8a10398074031410281428481040c20804459108988800300c0c00c0000c0c0142c0e104040041e48030170380d091000740308030b60200300c1d00c40796160b40d881a0f450500140045503540c0e00d4031400034040b03500614a0701484a0718000411081c800b007822812500c5580c12182d0b5045c0740d0340c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 433213525 1250 433212275 433212287
    0x11e05060d02070512040f080604020117060103150b0405010210200a12050a060302011e02060c07110904050a0c0812120604181128090e0a050307150b041b 68
    0x41c40580c031076000e200700404144c0c140119840c940321181c4443d40c40d4600103503a002451580e1008200390000f50030800583d030841c0011066220b0f041c0444410303681c1c0700c0140d0092103031348040302a500580e500451101c200788010300550344241c08a40801003c46803103410344041108551926034104603914213000d0f4000a010003584900309200090420303000c00d000c44004440004040d40c84403010019960008401160b82000380290001c50070840c2c0045e5490b10050124006814002080c105000c2101c5142108030001001d244040c1842c1c03c1095a4020fa680d00352001c5840c0d0740001200840019261216100e140800d81841c290034420403010314001e100c0740e00603403151a80304010a40c070b40c240b003013248600b49602e83d20030040c044c00301c00544000c0c0300c0301c1551800ba011b08070350940140401100c0d20040c0c04a11805801052420304a0030310b00101b0600c8080307000b01c108805c3c1c0500402c0411107410070044690548c040005944034040400001a40b018058509520440e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 433214775 1250 433213525 433213537
    0x31609050a0b091b090d1401060306050c03070f08072c01030506010c170906070b100801051e041707050312040203100b0d03030b120a03050d0f1b0c230312011e0506 72
    0x249084807106c29516500900c44d1101c030101d0311a559050305000308603107407069940009008483c0ba0541c5480003000d801004100c031040c050100301000210928030442544400161581240c480c2c40c0d5840441c0e0755168040d903c15021900f0800018825481400f5001c606074010b092140c0a80f603049421045601c09040305810501c20810017020503112800f660003080b030882c40080340e510f000c03450b070b0843d44007030400907850840303210781ca42c1640941039603500301b0b40090350030020765003500c0b21005038070030640004c20304c1c0404591003941c03081241215101e64001d500780c0b0b64131030340020050200c80d50802490b900800100d141804a4030991011110391406401c040b12003900c040d00615102001a00b280041d078000b4001807800603034029900e203016000010b1141d0000c81d40b11082054591107900c041100e144c40303550a02180114052a600c41054480625602e1000403030300ca50202c103c1741c11020300d0500010b22091005c0d0010050312903030040070701c07850411040201c250304c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 433216025 1250 433214775 433214779
    0x170603120a0215060402030105060703110a0605040302070f0e010b1801120218040e01020a091503180803061e1003020c01060506030c041503060b070809031609050a0b091b09 76
    0x110100c64a640c41008001014080d00200040030208038020b000308402483d8500403401440104200d4490301c0942c0e100c0c55043c204001c3c801007010b4810719261941d403003c4c204034103050a0100f4150040f0355802941d121403843c904042d2101d8402e2240d140030312910480c0340b0104503610a9000c540040d4480100516040f41850304140030041640c04c549411040400764551048203450710703200b004012803035a0005d5050040d4060081c05444641c4100c40500d00150040c06030b09210341d015403008140d0703c8400c0c0341c3e00000c0c06c0c810559001190700c1400760075108004401c01148111051136804c00521040c0c0c23803000000c2c1200030f9000040c50f94020342d2101c40124042e56414061840360010280c91921039141103458066815241c1079042814a05a01032180541c0503040b10361003900501800d5803a4203d0000c00c0c50300c5007035003450280b49411038010901c1e055070740015004003203c00d400d000400400782080a54a01031342d420180700c24065049150a10000c0617000389900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 433217275 1250 433216025 433216033
    0xf0610030c050d05181b030a08031e0c03040b060306043203040b090a120b0c030c040909061b020c031f14040c0635090f0a140c0907170603 61
    0x1000700302402da034816102c150b4080c0c200641c050045c102081600f0300e8040c000a075086007000c2ca00481c0d210310013118042d1a400b000000220403101c262078840c84214140c1000d034003864205260805a00261412a03080d1030050208001d868000350082c0a1600b0a0302868041d4440d121400040c08813801c0f03021044105903101c5030104140043c00041102c0400c01d03641c1c0c0002c10070042400c0243d00030180001181c05c459002c9180400c0240d8003020700050150b80f41c440010a072031074007903680722907416801c05142c84104540341d00031240e00103101d008403000300004001a61207884500320150140c0c8440b84003580c4070040341c096401d581c0604070000f0f400034064000c81c00604103c50680c6c001074112401c0051640c002d11050182d40c1c42041d003a494100d511052540c400b91281c981030282c46240800e0b19410148070403103650212208991030498a03150504078284c09644520290003080074111050402501c00c61103082182d803210080d0780c061850700c9180340003800303141c1c1500c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 433218525 1250 433217275 433217287
    0xc031104030501061403010c090b0901090e0106050a1e050703081306090c03051002040f05010c11062106060c060c03040606080604030c0501051602190204090c03060608060f0610030c05 81
    0x40088020405140194008101181060030540118103008030844c06a0700d005518200c15910100791400e0300d078501449a9580303502d00c0100c41c80541ca8100b039221601c554000940141c004005003030354003072600c038641c1c0031041120001134018001c07003010209070100300d4500000c3c8500302c0039501c41690300398042c1c80200c0782c131860708031015140c0403070b400c8103052810f0043c81400c22580701c1c0c480040409500c2d007420988501c040300c00324410745042c000c01089820402c0282c0110302c004441c0a403e03141c448074105002c803119046110700451100640c00031501c10b05000045504003901000244000d480f403100312085580001c1c010348d00c1c240e0360000407440c1402400300714001c501030307501c408202145007081421503074041d0140f04103022003000b050403a5000718100001910310003113488a07000c9400450054036290100800c11814440701004011322680070509407000350701110305070307540d43c804410000d005554441c1e00c16071a0021140ca140300350041c054459207440c003541404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 433219775 1250 433218525 433218551
    0x906040807060e131a0d022206090f05010b030106051303140c0108010603050610050d0e10020a1e05030406050c070b07110f03121801110f0c011a0f040c03 68
    0x1159801142c0040e420300c2c168400c41c6002500c8a6824032030f24010403c468181820702441014801c505018911003a040030a558540100400450030039401c005407803d6565900010103c0c3e00a100170300746041c2c4403d4000b103c0c0d03c580b50580300805004c41c1b941c0d003454001d4038940c2046048200c004001800400090310040049214550b00d07001060300682d200c1c005040c65005801013400c141c90b1a0030800244c0d2519810b42d030398280340c2021a540c050b8080030302c0c06804402c041c5000c6100300385010313000741c600381d0040c00c040b641d69445c40000d64035540300000d21108005181c0005130144042008101c0c103900c0550010185003002c1d1801006640d809001c110032213007003000c100030681d0901110f00500000b0360a00010b0090340c9420881004072061f200c0c040d081d180d101c84807102d41c07021144250b00110075110549986512140f02040300c0156034400c00a509041d402c1401c458503c440140c0c418079540030061211105c1910441800010108803a60400301922a42c0307413400303d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 433221025 1250 433219775 433219783
    0x30f0906040b0f120105060903030a11030405040c020a02210706030b040f050408030a060f06050f03040c0506121b2703070f1203020f06060a0509090a0213140601030b030606010509060408 82
    0x8507010706184c0c42d0307102c0354201c14800c08141e10041c01220308000038031450380c01104985903966941045007520403180e0049145014a400850b0010b20300040000c12640011712502c00c2c0b8800ca030340319000ca600c500c0300c0c182c158a88058610543c405201804000e00035001501c0388900600b0024148030940c15035000d580060320161007441d400018080c51340043d006010103043e100011001251034070300010440c0c810380300c2d510003201b4044040303400c02040000c01c60046c000100344945818640c601c040240c0425515005510501e4207034500050814003a50a0101400c03c04000ba1140c54255107464007904502a810300640e08045541450410000e01902100c10141c038071b94081c0c50064a8005c20503540802d550100d410030500f0b55a51200c00181d501c00c0e11110b80303546810355818949848050029406110480c1c45000c81d00d00f0380c0150180384801c1c0d590f110f2601c8500041d07040f03440050086405402072300c00950360f0350182004204c47c0a0242202c1d10b0700da5160040741c10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 433222275 1250 433221025 433221037
    0x150c0602040e04030e010903031202070f020301020309031b06060105030117011b02010c0207060302040b0306040914030703020c01030605221e06150206060105030f0f070516230a05030f0906040b 85
    0xb680000184070903d6070000e8445421442820b081c9202800c54a000e408a103002a0010b94907800007800800c0102409001920741c1c1c1c0076009544a040c44140291650010030100449081705505a0041500012002d004107010384419140d64200511800c005c40f0000045440b07640b83c00b060100268a45000c1c0803001c86070703000003804d100b002c1e00203041c000c80d517000e2010540144011710560080d40203e94100804850004800582e8a000c0c2100300e400d9200350b9a0b4040800c0348000d00d60040780c00354140d0000d9804001c4c040c3c03100d0403c0224402d07400c404240c03088500141d40c1880e601e0748903041844005451407440020700030060103642c40da410071042208800744d52404c030f0b9010054150410401d003056820f601e000d10841050040081040c02c2100c41c1d8004900e02a014008440459400440c0d10310a1012403c00a081d00ba000345c010620482c1c840d40343d0210500400c0f4008034036409005180f801c8600c07036107100b070343e0408014a60b102c04200000136280c0218401002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 433223525 1250 433222275 433222289
    0x180b04021b0c040c020309010917011e060305071d06010309031e0c0c0501030513030e0406050405160207060206090d1d03030301030302060f070311091e030102040602010b13060f150c060204 83
    0x250311494061106940f006030000303003954407d10a003811680c1028004c0300340c3e03141d17540e5050303030300310442405014113001c0441c2c0090a00380e818000c40a003480d004441034034001c00c2251a644d07583c6241e505904108000038040d030000002003981d541c402d030081102c00d40645040044581805100110b1030405001c0b0303004203468500100400140c001c0c420020402400c007040300d480c0826462410704004d84000b801c000a003080800c0650b242e0740701e000504800b4000b0401d503e4a000004007403140c1820120243c4154000050214400150148203060752009040703410003004003a40c84c840d40b02400c052550342890140c00685003040614002c60082d0300030030290500780305500352120003a00b4842050304000303642010301f00b0760080b180c0301c860940b1010509484501e101407414440b0840d40c0e4194000034001442c6541500303c541d41e180119003c0d120191b0625288044030b80f030348140702e8410b070080802c01070004100101c013a005182c0c2051a6aa15030b6603c45080b640103410100c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 433224775 1250 433223525 433223533
    0xa0314120a0c2a0302151c140f010b0904020702040e03160318031a09030c011406010e0910030f1b03060c0807050a08010902160506190b0a180b04021b 66
    0x10b014030150b003105111107081c0c802c01003086500b00c1d070303862400710507404042e00801c50702003442128403c10003141c1174500c0080013071900f4035410a01401820389190312000700101034010030300d207601c118400c5049070020806207251580b503105101c00b94009860690703009036969199211031030182700804480407044a000c2c2d9a1040f407030064018140b844019440711044003040c00050301d40303503000c00a11070240034501659228080246941302d41c030540a0b0319400d080303100c1000a40c4a40321802401c00b62642029141c0340403e201c08100219480400c0070b11500c0b00b0000305c2c00c0250612407190050712008800a8005e40d04840c05100e41d1040710345a64901e901020240d11803162900712800e0b141c2180b8002c02c1c44c500414954040c098000800d60016400b0070484481c00043c554540c008141c81c1b240c64600d82e0f02500030b44008140d54002c0c02d2040311200c03071600007004000d0700e82d001ea401550b07060040619004011034044541c1059081100307210030800e0741803107440c89144900070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 433226025 1250 433224775 433224797
    0xf15090912110c01050d1b1e030b010507020607080714060703051501020307061a030d02071404090302070e071205190e01150303050702031e16050f0a0314120a 70
    0x207071a28038146184038204500451041000e84000c034101880c82c409207407507a1150509420302000b0f0601c0c02d0746044039108041030b061520307000244216003099640b015001410301d23034026002e0790019841030780010005c00c20b03100140340420150240c41d028901050806100c0e56503030056101c201240c0741154440010800b0165050141c2a8002540000c055102c0300c5400080e669002d070503401000030303895125414000c4c9845580302141100101101d5009000c200042c0d11081240035450b14020404200e030100d05060060381c1100c1c1c4c2c541d000740000703032a0407122158810007134142e84c1000544441c05a005030a8014903004c1d810415003103c055441000400840300400c03a4148113074140440c00d5903070503402010b4012243c00d818072964800c402c1c1b0001342810072085400148a8030743d10302484101303001030140200c483e00c0d140030340c48076203c0e0100030000d1555061103504c61810765041c40007400c01d40b50b10781c070050140d0484a80034045180b100094104001c4000007902d41c001c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 433227275 1250 433226025 433226033
    0x2031806040c08010c0201090804030b1b030a0204031e080a14071a0f1803030136060503060705130510030f05040302062e0509061f021c0503090c040f150909 69
    0x180040c0d0204134002046100c0032949c1d140e11074040ca2002514583d0190001031160001d1139485003500d03011141c0580da403801d40381010080d0014001035400801c0e80b58203401c3c45440358440ca03072190b00249201e0a08204160440e0b42c00c600030134032580d00030103006072400103540c42c03101b401143d02040d4a12461400c0403064010100041c0b4075602140c0c0c0f50f50002e1410400f1040768155480740c840100d82100001c103c09401c1d01d135041a0841b82007d0034004d4841e40c1e40d03400301007601c10850a03500c658840000494040c00740482c180081ea2404004200318503103e501110b42035450300b004500448240b8141d012654101d03019000751b040582004103580407010b0032b01c41e2400e24065640c0c104106403204c1100301c0b02c1c0c01698060303865100840d425035208030002118940d6201429071030780a00704000c2d1030703031503034a0068107203d945400940654040d4040e40e200309038903402401c1c650400b40800000d0b104459070041d240c5c3d540e08030b40c42510028080200900a00c160205c3d41c002c0d1494 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 433228525 1250 433227275 433227281
    0xd1407090c03020a140904140f0109050615180109050d0b090712080706020d150303030614011e12020c102003010605041206180f020f04150902031806040c0801 70
    0x40001d040520410800c428107070403c107019460720580c04201e8a6240340404078000349160b9400f60300451a15040288030403910210f1416640588018021a2261801e0000302040c00501c20007000d42409030700d0303070910f00800884181e2414540544201d9803540440c6110308454400d54000d034189007048001d2030100610745c01445d400260000b01802c64440d18103034040c0c200c2c010245070300010003400140d01600048010f0440341c008071556542c80c50702034018881e070310403400c5842202ca03640105602071055002d01250301444c0d0341e400c1070f46440446000301442d110040f005d50038042490143c1c0d0400c2481c5c1e05005800c40083c02c0218100d6400070b1a1119000c5003540508000520034160b20030305580c1181c02c65802c0300600350f501d02e403c0c03000e00100042c2c00741080350f59401d002408210203603120314034001d481e008a402d211038148800d075503500c0001d911150110000f04103034101c43c0d00850740a101c0104031365810605c1c030106400d01c0f4065400361404140f030082408040c03002c0c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 433229775 1250 433228525 433228541
    0x61206180703020904110f071707080a11150c090907030912110c09090d0503070c0f0b0601120e06010b0903070e07020601080f0d02060105040905210c0c060304200d140709 75
    0x82c0420b0709007d65505141150722401c0c000521000801d04070008002040d8162010b542d40641e40c00d44607940c007400280312100900444007540300707a0200e400082960311500c1d004501c0c0c0c0b65960301d410081801d204003003101500c024201340d40e4600768008203210034082e06041c1003540d100d820036204020300c94500740c6503106c403034071880154040c00703400d00b800515074400a25506246890380c0d921142503c0c070170a0300c20040c1c03460900750110020411000441885000d09032502a2a0170361344290604030340350609190b40650020380144040700d070031030185c407013400020201e501407a100c030b40d40e115000c01030b58141c3c003503406000140444007041c48200b2464540f4030040c8941c0c100410000c0d42c1c0d620603c9014082d644d1401d17001c1c203204c0306020200d440c05c2c4080a81500c40030140400510707500808003040d040c0124490b9016070703c1d08800b104e000781d400441c808080f50243c20080340d21401043d00301da0250400040c40001105000300f0742007080740750044c0203101c5c50303d0340010643c3c04007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 433231025 1250 433229775 433229801
    0x10b0a0603050c0909071704060507081806010308031b04030f11120a030e012c01020d020706090b0904020c060406020d061a0a0315051e04060e06061206180703020904 73
    0x60b082196600d110070a5544071070044035840d8858840840c1542d18802842d28459860072980030007040c03090f03580001c1e010f15000e50303c131001c070f0340c4104c0c516100c50004040880150402c0004101141c0c0c1040516004038003048400681020444002c10540c4180d0003210440c500074410000d01c000300d01940116002a00e04942e402d007803410081d154910b44000a0a0081180d80030303810b40d12645012040380d042ca8968582c10b00314000640401000d850401e00610603801d8101a140c40459400201c0b40d154132544c01c03290418046030004d4000c6090baa030051360a1000403134141d404c10500d4015401a080103a50f0052003d4440c00c0d548150032031442c078110380000c0784c01421100121031003041030f0b1600180c4501d2608000120410551040e036010810342c0c00d018181074420401642d41200301c4e003c001032903842404104100044590b2070340500c0601a140d42c2211a60b46598044002403e016040281500c0c80105120540c0c07074800196020640c00700c1414948141086641c2e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 433232275 1250 433231025 433231031
    0x20a110406082e0b0a090207030c141509011506030b0303190f260103030302070606082e0501050105070f050c0a06170702210a021c180f03080712051308010b0a0603 72
    0x12130404907060085034800c000d1450340c001003c80c14548511030740d21035190f024403900183d0143c3d40c40349584070380c44807000101d0740d04c01c40801c544400510070529400c031148400100146001d905030700904250008513050f00040007031000c035000380c14490200b0782842e00d8203003c4c480c100038000c148140c0b49a1000054038030460169805034000f098904499040c0360150355000140340440c09460700341d012210600c03400104801c80d000005404607071251503050040e00b032003a068a141901e0b420702c11030340860b40030465200818600c90405140a024404445401c24414040380500030641e10117000100c8040d184e01082511900032034100207144020400c240e0044040c2c00000c0d111032202d80c4010000401e580700c1e134002d1180906922101c4804542806220009030009400d0a0520701d000404503001c164440500c40400c2525002a074450600c840c542c1c3d00142c8a00349150b130000d01100b4803d0159901030360702140080e000d00c20000c16035800c03c80601142c510a60082d00c00d00d41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 433233525 1250 433232275 433232291
    0xf0f0303050f0d0f0905061f0e1611030f180306091522110103060806091f063302030906090d02012a120f020a110406082e 54
    0xd4064182c0c0c44540005030115940c0380d412001c44001c00c2c602c0c041003d10380c200b2004a0500c070300868590311496040842681e0000711598800c901400b600400300081801800f0854070740010000510710a80d0382055130310f49092201291441d000324211142070f003000140036046040300341101e1000e0905a005107018182200d10a80780c030904c0a401100032500f0000440e030714040154441c1070f007003c0c08841480511800d200071101e40c101042c41c0800c1c14003200040b0303a0700001d4243d2080600c0300141000100d0320120044020480da5117500c500d0f21083e0124101c001c882407031003140064034010708001000f25040d2800b040720380000040d90414000d00c0ba0b1900c40008569034a2011a00c0c42c4400e1903510040c3c8a0300313504e07000240b51605500020b50450708000c0c800031085d000c3c0d01b001d125040c3e6664100c501003400108040160050f40072000024021a2340c0d69071800018408581141c607600740c1443c01041c051002ca0000f0b851405d00000020175485030305044010345d050062030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 433234775 1250 433233525 433233527
    0x7050306010c05160906030209010b130e1302040501060c1a07020c060c1c08040b160c020f01020106170714030d020a0f03020106030b0406060302040b180703090201020312040b010f0f0303 82
    0x1020051100d4140240e000401082020038404010f0b41048400480303800e54035020900d00405480c007089001e0404000081807054084003a00e5151071441004a559820400001c00b0004040c1207012189440208031005030358a01400340649071968811001d8100c1e418801e031540e2aa01c0e9a5100001000c03c0c090119804102080890400d40d0800c0e40c999454003660318100c1c145016203902d075400d06140b001154403e00c3c19005034081e41e031502042d1a50010301113081c0384601100045843d0344103200040c2008102e145502105000018216544d40c1c220f841182c0600307440859034001d40000e100345c6031403e260000d400c20075002400311011840740a5902d2800c0b9101134030240307040f8420410180700f500510043c50384500d2240351402d01d07103400c5000e04800d00080b44a02c1c2456003161700f504040c0c28000600d0200402c00b0310076100e00d44103074010040f014059045000c00c220015110811801d1030340207501c01e00200c042c6600d04594041303503540ca500003034010395254000708042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 433236025 1250 433234775 433234777
    0x90114060a12081e07050d0503060d020d0609050109230f07090e120c01060608090c2202250308060904051b041b0314010623090105070206300705 64
    0x640e20b150103003001d007107080c24407240e28000c4a543c0444032280d0b442c03c00c02441d2002c00340094900c5441241e8000c41e401c442039946000848030990041440107000d40545040c2030301c524014003c0d00c00283c86080c50f15001e0075224040019030740c2c0b5000f110f4202c4406110014000070041f50005400201400c0a2007038543c0c2c160f103d81c0914a0f107603c50050486018400b145080b102c44640c03694888051401501a0540d0b204400125100000242e140107000c83e4410f00480010000440c032003a58130312a01e144178100813038a00641c00e00040302103000b410009801000c40120700c41003a40c075803074000e14545008000070b00885140c020310000900010311504901400025104808a0040490014aa0041d46403915414400300f190025010b03070022444c02ca00b0720703407601030380e80320306007910004441110380748800310907000e45844d0342c103500c05451440d10500d000c1d490300c0016000038585070061a414200208811000b04c41c401034040c0c44140014049060701d00c1e45080d07480a455 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 433237275 1250 433236025 433236029
    0x403020f0609060c071e150c2a030305071b0e0408070303151707080c0f090406090c0e192304020102070509090102040603110721050d0f0203090114060a 67
    0x1980080381c55909542c40000340c4015401d400222170705595a40d1314040388040c4940e8004481c0c694030004690582c4a01c84821140d02d50740300c900c07044e2501c0d500c4245544802d0103001020074a0010103015441250901c80210b0095440603100c218a041503490302c41070200e2100c03080c903800002c00180c500786d443c46500ca900400d400707441d0511410164003810050b82220048481202c0100361441140d4920450841010486da141d41d182c820b060396901301705440a900ca00c18a04a0940e032038031044e01030f400740c4110b00120f0342c481c4566840e028100940c208203110003411040260841000601079252450f088081c40001c0b003002c0b04d00b6501583c0c05071856249072031800101564003c0000600610000e032440c6c2c12031621000e158001e400c6409400c0000c1e00b8070900748600d004c800c01380c1d050650026090514640360310041e9003144915100e0805000f8244100030020004d84a04034890700f15060241e0ba0b8a80040e10500711135801d480a092410341e5410300c00a52290014007003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 433238525 1250 433237275 433237279
    0x5030c0a12150f0507030c02150c0313051f0225210203070b0c0901020d18060315120803060f0409050709020a02030f03010f0609060c03171b0c011a04020403020f 71
    0x644102d01d104090321400400010441c01d1900307108195505600600318111a42d0907500d16100d05842500742107000c0c0e4100c0f00e21101407000c0b8820040d0b84000501c03207841642101c1d40075110040341000091140c4c0c00c1c03d242079002c04c40c058100100020354181104403220f441903043d4940e10340041c03038200140ca40400d40022a02d0348030500800454405940010701080c903031506001c1c1d11400c0d80400140350041c003030710841c00c4815001e1854919038454140c0119403203410000110020b002c194540e800300116200d001a4100c41785000c5010540540751861b503d1a2000c10f10020070b0f00d03180740a000c0c85c507080c285000b203079002c0340802c244d070644c0b030000d40d0307400d48050304a01e54003544012070301ca81e800000028007101d035402c29104450701030300d0381d1501c0c683c1c440d4180c42500c40b803100900030490201815562001d0740c00456480189a8082d9001840c0030114501517000150082d2090795602541030904130041046414004203c80940ca0035003140d010501d05410090414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 433239775 1250 433238525 433238543
    0x604030f050f0a030b0f19080d02010b1305060d0209040c0306140618091f061d0f04060c1e030b010914010203090d11190303080c04060f0513090f020405030c0a12 71
    0x80704546d0b4074240401c1045009012005881d80d40064001000061054000781e101c2c01c017000b02501d0040c011101d00c400c000788084605000c009031a006031400a1066074801c0d17440c1072000c0142d44848165000704d004500680c0a0380c11841d024045070b6140845c555201d00180800200b5901e881c000211110030080190081c1c4031482030340e2402c0c59045134158180b079400006460712000d90b001d2021207180307010100180c0110032000041c40d00544041c079a105100c0001070115a080e040300baa80d2030a0325040344111502a004c03010480007101d140c002035102d24465606680c055601c0e800f0b8881480041d64600c16100080e6070380c0310301241d090140300101381c100180088468460080c02c0082c1082c2c2d02110004403000b24000d49010890100301020089032001d900d60045c0c0c2c050300d44544468003032102c021415201508642854034051b01140b102045462190041000d40c40c541040961220704000c101030600f000c0c0e0500c58000d00f1005400c001500305004003209054203d03030b42c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 433241025 1250 433239775 433239791
    0x601092d0b04120530071106030a0204081b010207061805060c030c0d0e09060d0807020a0905190e030307080c0d06140f090609040b100302030f0604030f050f0a03 71
    0x800c61004807640031a60140001c10001030200e0740c0011030f40d01e030344124145c03074040d94566901c00380510250b01c01c1e10118001e4030071a0904505200506416024204a1101050305000500b9070b034000c94102039640d40100d4108100b403002c10001c00c1025003003404101415000c80001e5451105125540411954260702015040c01c0802a409810064580c1c0d0741da1500219843e942d6120003905070362441a000b1800001d1321525414144560041c407070140d80d180c0d41d040100c06c51001034140d950034020000788005a030b9a01c200320040c040384c60040744a1900089031042c102d0101c00d138461240c02c220340019500008001c9a500140702d0401c41700b143c603060020045070040d5070980c0c2d1000e29090000c07990800c010400c1c0a80c1008641d41180e1140303e40a222201c0020f89000740c0140080c03000c0303000560000d200d550b02007011034442804035940e40021f03141450b030541c800600e400c00c0050000385980b2034181001c00010303080c07580c42c000411a07103120511621031390781704142d43d403481 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 433242275 1250 433241025 433241099
    0x61802100525061d06011a03071704050a050f160306050405120c0601081204060c03201605040509060103020d1b0b0a0503150103180201051c23060109 66
    0x840b0400000032822000e401c8602e03e003610042581c0038400f9070035a222107958224000005031941a00d070945003a0800169800981e001608090410000d1145007a023000201e01d0143e8080e10840c0560000c2c1422081420860309000381810b03446625007181e08a88060b508003540c6900312030b408007002841c0c0e584d0b42041d41c24a5440e00062861070800a04086030120010300c15050725880415641080c400c14203081052003070344500307800324910301d0b0504d0101380221f0b5220000c500c4482c1c10460b01c500b91014030304180c8050300384050801290024405414144284c80e8040d164500403c6c555045070000b07039038907400c100002d2000040c2151101c00b80e002041c1304004ac03840c4042241c40c2d60880300003034103d0300201c0304400d040d503070001071504640c403c0c0039400e001c002c243c43c90801380d401500110346503802131101809902c0345101c1c44d855091248605500051411024030305032a10301a0300c115088040c10007810481c0d0003609119441c600f4030700204214034850410b1050300070840c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 433243525 1250 433242275 433242307
    0x405030702031f0c0c0c150e060c150f040b040b0703020d02030f0403080a060b0a050a0504050901030515100609060503130c14041d0703021c0807030c0618021005 71
    0x80c0080d014081c10004002910545426540d00c408055061004542c041c0c401ca40c20260410050210504e460003088a50000703003103401c88980d03910300120b01d10203443c04a1b1040d0b02080c0342d0b82c01d95201505410840c081d04da40d50340c01000403121007050341020f45504649220281000c0c0c030741506c180100306004d0080d03048071801c411962003952a890640c00d2461660021a019004100d1010014491103014803c80c001e58010900c5035040035246001151140c000030448030600404000c045050b5446449180c002d5200304020402c0c40b07600e4243e545240b10180210b008529416818820f0302e4001c01c2c1130050318014548240c89a0b41c071a00c0d4200786444030030203490101c101d203000c20880340010418400400a4900b403148100c16840e030402800c4105c15280b554100890a000510380200035007015090481804464146525041c505a0203502d04402268000e0f200c8020031103203000e4052101d0b214440c4c9020501643c010074a02d815810001d010800c000420341002c5130009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 433244775 1250 433243525 433243537
    0x70503090103241d01060f020a17090303030108030316050a12390807020d090506090a0e01080307031706090604091502070813050a030c180204050d0809100521040503 73
    0x78104080c503aa60300020500580d10341052111140710004103146d0301441e2800808809940100007a6032141ca882400c201c60a44880800804001244d51a681000958080c205c950051a40c80c1040711201d54001180e2000e0000d0050070321044140d550041d07107202da000142140403414420900e048400414099100884801303d010b000445245000d04040241800d0f111002ca80e01c40d18030580c1c0d5240d07142d142400080481809101508120002c0c20540c1005032040c0303140c80c0c44806440c105003098100400381e910108a800070b069000803000091100301c504008642809030109151180c02030005003e05d440e003000d50100021000000c2c50b01540050454581708d062400e500250300c0000404010b884504010480340741c034180300e0080301d43c088059040c25141034040d051a1084248615800b0340c28080040d054446445c030190f100e00c5080141d80d28580e40040050401c4010700840401106220a010848088100181140d40c080040c1c05c07550b6240b420a155206407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 433246025 1250 433244775 433244831
    0x10020c0a1203050402040c080c04090e0f030c060412390b1915061b050106080d0e03060901060608060f0f03011a1503070807050304110d08040812070503090103 70
    0x12078007900049515502060181d4402c903020301070151980002c0790303041c10a682210f49210208010020040b0961280c0b1081c1585029110b607030304019186410754000305105011500410204810001c3c0710440c241c0010b02070412100382920800001e00d420780903004401c0d060248003515880c05480044444042c5d80100c04158038030300761032104604109002900c00f041c0c2403140c0344824a010354900b0341a03032a0b507524942c071084100b110240c0c030f0f0b01c074400641d195580c8e0f440104200400b0702036091000c000ba15a06900e0351200241445c2c00c00c0200502903c2c0d240c030005100207544101010f070058811200d600c00c45021138002242024103200c0c1ca5415803a006019010690364810082448401c4030582d481d80e0007501d120800f0311044aa0400103480500055442406840510342250088500f080811003020100d64800380401c0d065800742c02c0801c0c03c100c120800c001d10308041442038200781c14100c450b582d040d134900170104140d05141e21808032038506800b94100c1b40c04030400b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 433247275 1250 433246025 433246043
    0x1b1603030e03070504290109080f01092906010f0210050906010602010b0105180910030501050f040203010c0c1113020c030415030b09250905061209060105100210020c0a 74
    0x24034030300588421810302501d802802141800181d61910388564542ca41446a002c010800764241185020384034468040c14040c000c040440d4858040204440343c1e08008000030f4102100d062903404101c038400c0d8038203500075402e1120b9070000c100703006a41140003824110724005003600e09070308040045464410151510007000201c3c50000380f100d040303504a80081001d0758081004490b9403240e082c80c1d02d081c00404c6a81000e60411840c00c90b4401d0810400c400f8142d26561541e0940b2000c2d24034000340c0c0030302402c4c00258503081c80390400c02e01c250304050701d003100284e540584024401c1401d512a41c1942d100c1000300c1566012a10f184d9502e0054a83d02c5440c2c0480007010a000200c5000080c0341c40305036070a40c14000c07243d50040c400c0460448105aa00c140d4a01207054801a40c040000e858000102616940064030505502186891207480c12000360780c0707040d0051344440d02c100394034a00480a03503004510043d80c801c0441c00565108400c50b070309864480400002800142 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 433248525 1250 433247275 433247279
    0x807022d2223010f03050304060f02071206020306120706140c01061a1c02030c030103080a02071511100209180405070b0412060b0909190609020909071511031b16 71
    0x549030442072007460503070b0150019641c98202c000d492030700500005000303501c10001440030318051030504007486c120744100c40005484000c8484511012081110700c1e5030080140013003450411060b0030080320420085c408149850001442c010700080024448500020814114082900305c84060003000d04060003d021403c291400d1b54818220100b070048140d40451040d9030398000c0342d01401d0b140d08401e06590841c0c84a03146035024240c000c0641c4641100040c10051030f1000c92180c02c150b441e00c281d01044003c1c0c9038106001355060711540c92040020f0034403952408510542c006030010198401e0790765241051400b13002d908180c03038818003c900010300048002001d0145403050406001900d08202484281082914500c000b034000d9103000c4803040451200c5142607001d480f010480c160076130042109e029050382c508400b45c004150034007031122003e02c00d860f10305452502039100321010809940728040c240340702d000741401500d03a0b50700800070001607130050000c07009000107903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 433249775 1250 433248525 433248551
    0x9020a0c020d120f0509010e0925200c060403080306120f16060c0308011a0d02070614010e01030b0c13030614060f0a03051e16030807022d22 62
    0x215440c3c101400040032290405203051042d001d0780c2c49280c1c11785038607092852102c10400000c0c0f0003444203000000794004070547d481c03200b84d200e00c8080e0035100e440703541d510135103030446108035078442d000180c0c01440c80030742d540c840c8030440341101d0704400c00360340300d4883d00c00040414082840c801c0007032080f000c805200c540c0209006049102251024a80eaa90303104c042d91010350f00d1501501040e9040300400c40019410805008980041d00062800628042c8041241c2203030806131219030781e51007035003060b20b01c134070000b4054900c050800b0b9480d8550390790810f034020000c0c401103079801c0c08107010791f1004050300346402031a4400018005140c1001c50428042000c0f1003841c0304030041c41c1540014104101c8190640c6e40050103802c0303000411007000c282c182180c084560a10901411020b4042080d108c640558402c12066540303c0c282c1c010031a070207910340c0d00e400d10040641c00c0000348110310501e00035401010b44410318051b0003c0d14540b003118590391001030311410513096074052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 433251025 1250 433249775 433249793
    0x31510030213050a050108160509150306040609290607020901140a0f05030318120616030b0a050d06050406140a02040603052d0c0d090c06110d080109020a0c020d 71
    0x10825682d05249060398900410000b01c0c403d01c40e59012841c00004102a094010b18900105010781040c0e498421004045841c8400c0040c4d11a00f07228044207020f0145842d004810042c14840801e000381e002502880c0c1a00748810342650308052404000d515a46550096805158004008048940c1d4074040c1a801510004c5400d100e04504940800c68514009690080c1d400140c011414100b0400c40840b0f001d04a44880703502c03240610450756889410000240b05410b281491787c106042c090307015092700d460003001882580314840a2050361206a40c4004152f004407021505d920350b814281c00601a00b50b0014100e030035a400c2000d50880c5800400884000780d0b4100f00c60780d80c450002c80c800711744118407038801c0b035544176800841c009840280d07000546085041d2904840d5401c51003100d100600403500b00302200c004210581c2c01814218280160741c0c090328882d041103030001c207034072014000d280c0c02d030b9800704100c14000d00c14984a9501603000c0e205040002d00b03800c001903a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 433252275 1250 433251025 433251037
    0xf140c1c0617010f060825090c03020a110c1311120103050c010f0206061503040c0b07050109021e010f140f131505070f020913020d0609350315100302 66
    0x10540c04c1c0290704445080d00c2c421281200d440c00060f007104800002144d80804440c61302049102100740049410100c41c891540c01017100e48005940d481c2105000c1c2c00d429070791400c070035240c202c15180d00c520b07111894030940451065000060084c620700b500c02003401100046000c0c091800c00110400034001001c00c5034180c240c0310040c2001c982078003241d44220850392143c0089044403a28003642c1590003841d009031041010203a4240c03200c500880f0303608000001e894607910b5031140425070602c1400c001d20042102c0385444c5629560f00068a007100c007400580411890b035060820446045050341c9100549c1e05a1581e540100225809a81c00350702549004c83c40094000100e140100115050541e011680d46444500c5800708520500020520400c554003c06007800599805000d5080d241c425800094003400c01c0c140303004600700074641c99102d030682e0042a090302c22031100c04c134500400c100d0ba03c2d81d01e50392508030030000d5003c03000190f0000e56030317940b540c02c443d0140c0182078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 433253525 1250 433252275 433252319
    0xd12030c300e030a2106080a0303050123011d03070810060f05030606011e0e0612090105010b0a020c040e0c0901060f121e0207060905190302010f140c1c06 68
    0x102c2c14000c00401c0e268401c8044003800720b4680e25220b20301e2039040803040c82c0003e03198030004600ea95a0121418401030450440c0041d50318001440703a4403042401070100603450b90000c0e4900e44010028100b245002c3c0d22011010000d030550b01c0315602001580f0290041c83e0035144180d50108030b15014001900404050044424002c183c070b0600051407031040c18140d5030500341d240906410340740883d890690030200b0841c8201090f8944800c8018000303640714240741c000383c1c41d00c420b0032401c40780d06030408121107034204000c01341c66030300050916010b80f08840000d520408600700c03500d01445010f41641142a01c0b000203510b503040030000c840082e09441e002c2042510242c14000c9a1000c6c040e83c40744020703200c4203815000c0a5000c0c042081c426040002c110640d40c603140e02e04580c05116040c40b0500c1d0041204165080c001d401612110b10024840035104c100200c4103403100500302c40451601240e0110383c680120b500b0800c034100c90760100010b68840f4210f454109036100d60507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 433254775 1250 433253525 433253531
    0xf0c060201022a031603140304080403020f0102070612020f221a0304080706050604020d06090c031409030901051e0a0207061716180503010203090c0a050d12030c30 72
    0x140401840128120f04030b4240005146044040400d00041c601a040150304105040c08000c00d504103210045020318002d1142c01e031141c0c40c6104110510030b072001d915045400502041060b10341103e404c00140c12084005078952446c40702c0e0102500443d40f510500354400319a843c804c1c19110021400c7c0c03114801e4600354000ea2030765111441c07005450042140340108508404070703400d07078010b0342c20002c000c1c000341c07414040c00e400760203882d5550800809070f41e071184000300c1581c140c03041045001000d203103440c4614000c805507803a0300070001c440307041c410700003000401075002c0803965181841c064003440c0c0f10710308808000c0d682c840c9402484042031114681082d8049504003170fa03c030307980c6400503c080d031403055011100f05030191240e04001d0310b100c201240a036401e0001d075104000d401c00409988000e01c04200704407055034811401098031030303610000700b040c000714680d0050503410003217441811883d0441c0c41307989094100050315000300ca01c0c4001c00301e10400000c00f00c1c201c00e085c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 433256025 1250 433254775 433254817
    0x80601030b01230c0f07180c0c0b040b07020d09050607021905060c01090606120f1212020403061a01090e040b0408040302060307020a05010b010302041217040801060b0a020f0c0f0d0f0c06020102 85
    0x105607249814064401f0b2004031036070301d9885c40c4043c0c00c501c1305000c1c01d2900314000d40c4175948242146406039012a42c01400c601080000b41d030420240b00c049100e450813007401490040851031307074840c004010380200d0b00d849280804480100d1a0001001c001d80741aa84460741d49813a4002c11941c0700c00c4030343c141403050016072442c4102003a4040b54000001503d40011617903000c442a54240003002817046040001c500425144080c00c001c601610012806143c050000b91488071024145414042150f07020310800140c9010254090340c8410f80e42c420f900c4508041166005a0340002e42c040000020410a241c0c04108401030600c0341000f070048010490040d801e074040d6000c0c108800c03000c0c00154000c16035444880207503451610696180a44070354446003520015042000c5034100081d4903401c05a04100c045a5951294090a82003284e400058081c1c1e4844c46018402c0700c40040c81e1041c002d5084109000582c801c0850b900c03151f036448040e000c1e4128004220891040c4908 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 433257275 1250 433256025 433256053
    0x12081c02040e010e0a060810090209162003040506070606030614090c011d06030a051e041a0a021207030605120316060e0a2a09020901080601030b01230c 67
    0x351816101c031a85149442d82c20484d10401c0d24200511039004140c0b00d03e00021001810700051340a0078010601040702000d6006124041c003024001e10802a154042c0b0401254040100e000e460640503041c3c0350b400704410b185240d4003940e001140e0043c000900c2c41c0401c40d19034004012a4030030301e4180261b191201c00405c2c003580c2103400342ca003900070719080001036200700c40340d0443d41041108424904d54000c04100c4035002115000442a52002841100b0222440180c0c08050b4050981c99519060b601c0071880761b4060040850b1807101c0c07000c18842c603c10340683e00324810003c03400c15545485a0010b0240042e03101d550700441d03c000000d0003c00010040fa500d19590510a0450800990381c0034010300c08a024072031540a4480b100001901c4080006c004181c64480c400b00c61042c2d00612030f40f4501e5030b02943c2520301c1084200143c0c0d800c00f80250b4040800d00340000c1c00040c2100503108130180c0840c40d00d244020460814110000e00040c04000002070200d505041c140c40c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 433258525 1250 433257275 433257277
    0x70902031b131413180209090d0203090906060408010c0f1d0916051306020c190518090f010e0307061503030210090c0e25031a12030412081c02 63
    0x92a9495400c0c00b12080c8642c10405941d80340384900540013200d10351581da5030b1011030b0055000035070b501200e0319010703082d0f2905001c115000300305840500904030b000c89010b17540380b094240e040d001d03510b41400203100f991080c0550b801881028006d00020303020200040012800764009800306501148040e54100300300383c04504050050980c0c0d90b0340e150045a40000000c5042110400c601000b40c00c80a003a913008060007445150018030000101000700841588421040041d0b003002c80410007140d510108800d81156040790180e002d525001401414806484d004a4556007490060100c1441c00401080443e0280c141005050010018008210068840640142d00a1006150b01d4200e80d101c00c502500c2000c0440c003060b03484412003404241155021074825155100f0091868400e840088c0f43c0b000e841c04120281c50703040005103c1910321b1849025010116078110340b00000c108a90140a42081c040d00e045400d140c44503030f039404000500c0814018200449a41c84580 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 433259775 1250 433258525 433258537
    0x203130e070c1502070f050a0c09050408160f12090e1f1e0f0906030b0615180316080a020a06020f0c01030b01180303270317030711070902031b 63
    0xb030344081101c101910781d040c0c00c0c210000b80700c4455908200f010000b56000c00401c5202d4820400b518203d010340c00c1c12070319114aa405010050f08100800001544486c11a059a24840d25407801c03181035060590b170141000f0310041c5000c01e1038900f0600c558200a0041c01c4403080d0700e54201503510700302406542c003603c4480e07011803003144005000003907100031411207207901411501841c03035480d00c03464070251850b071002e4480c5540e440d082c000c2c442c001101d203601500580c1c4d003805030310010300f00d0710480c410700700410060308018601208603602131001c4408443c21001850705552035403041911008034403400c034400c0748004000222640049007500310043d81c5c40c080e01d007039090700c3c0041d000b8001400c0c08074104000200392000a0b8a03808810010394081d55842c0010b03809802007045940601d80c00d0034040b40d420350200001041a4254442a203030044800e443c4c0d1110303801690001000a11000c0c1801043e40105100d040b59026500c510464940c0610800e802c40d8610741c648605 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 433261025 1250 433259775 433259777
    0x509011a030d030903170403200307020f0103110d110d05091908070f2004061a16080c03030f0a0b1e0d0312060602010f0b0139080a0203130e07 63
    0x20041c00c150050084d4000301c1600c1c040e040c580c40322022114420580c0d0b000300d4007103020985020901c60014121046da120030280c810046152400301c0d0001407584219411681c101030710740302080d0007100080c05a805c0908003203801e014010344078824a10300c1d0408003158840d0351400d40010112000041d02c81c2c030342da00300200070048070410f44503034007250b20219003501c02010301d4455600040300c17800e4544800e100c894200c00c2c100074050070803098030b1281c0c0c05070790300c51103206c030380c00c10006842d080b86c42c8401400d02030084000c1c2480c00051a0244862001c854000801048010350880c5d200601c5071403d40400c01c18840004200041084403500c0f550201d0b900581da800141800001e0402e1b240c042d040001049071000000d00950f0f50311341103100140d44441c6c0e810441c405a00440f107803050309013410806040c0f01002c81c192620a01801c40303522001f004041e900d1054292450501900040d80c0c540d05e40b5140343c080d603030350f1000e000143e502d0141c510020383c07200800a154010481 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 433262275 1250 433261025 433261033
    0x15070807060203041703010303030c020f070602070e0a0603050d12060f060804060b0d0501110c1203060f0d031404061d1806240403050601060810080c01030c0e0901090509011a03 78
    0x349844510003508010f00440381100c03a005c10301d6040b002c65025500840c030958000c0f504514103d0024240714000e0f0090348182d004103414032400e40c0120359181580c81450340780c98140c0e11403490f480074003015031019140380900007039080760030b5002000c41481c10070410144010380d92035040c046c02c01214410500040c210801203000148585c200c40d04050700240f600620076003584035642107610801e104480d90a001074152a0aa414410440a0485d005415080d450000c0c0422004030102501505c01e5130541e580e441014051466070022903040c0060320740311515040d0180c01c0d6942402c100381c5e910611b080a075000d2410361002d000c0640507170104511750b115402030020b40e1901c014120041e8510303c1c813803020000d400014000942c011740c0100103e500d0507201901083d0f01030305014800080c2d80091048490000b01c1910030307002840d001405100485080f6202c02050017030f183e1040000c0000242742c54260004e034020b1141500810492003c1c146106440ca008080242c160300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 433263525 1250 433262275 433262287
    0xe06130201090501030c110129180720030d050103020f030303191a0315040209161403100b03180105010b0a080105060a0c1403040e01060e0d060b01031506020c150708 73
    0x101c00d420121a0341b0250900d003503001c010a80450948085283c200c00c206180b41c002c030000c0444682000d0b458201351258000000f0000004040311401403548080c48607a224500d00d034891900412028034049007504d484122242e040400b400080c03206070b00c20070005980d882c091901204503070054115064000e0b01b440c0034041200504010800c803450740710301c400108410b0320300340803110f420003610f400c2c515145440d104120ba40200504200c50344260040c0c030700403154010740781e4001031854040170303622507407441d090001d10601900036058400c00407050000d0070344c8a080250749800c56100a010366a21000c0313142560185044803000246030b41c004000c035080040013442454070324a003229034141c49465810941b680070808a003150301c000350802c400c0152841c0c0790302524a600e801401e0600c02400209505c414900245c0110b90f1071004c502e8980c029409500c84000000c96614595900c4070302a40314204400200d008042465140116200d5607048404140c0e1020032941011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 433264775 1250 433263525 433263527
    0xa0b0307120c0e1503040b0f0721091709130e0a022218050706020102190f021f1d19080c0a020a170f01110406110c040207060e06130201090501 63
    0x90000040c14043d501c3c1546006481d0004140100010246010796908240c5801400608002d003c98004103500301801045988581d0301c181c80c52101202c40c400b419090442c030014200504000e01201411001346110300ea403030040e010100003180c1c810325944a0b80c2003d001d6424007022409507130007100d154401454000b404000c92511a41200d031010701c1c0400350307030413503c0c0340601442540404c8090743c00c006040005e0030183c4030780d00c0251b040441d182800e682008040c02c1140038405c0854131110b100b407003000260f007480c1c080500f100000c154281480001e204c8140c1e10f0320a144a104048840000000d403401c1905100c0703820042c220081d1200300e07094004100344403c0c3d020f0002014096039604400202800e01c5070501ca41d03250340350740e41a02e0300c09030184000169041c16850402c5014900035074044580e50b0528024034950030207400d04119803401441c0c0c0c01403010030344a040c043c4030313030140402c01600c00465409880d100403240c0ea0a103062002800070f064280c1c240100c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 433266025 1250 433264775 433264781
    0x8030403140d0914130207080a0e100306060f08040218160906090b0405090414060903130504050f0621010207120f020a15020a030204090207031d0103020418020c190b060a0b030712 79
    0x404001780c001410000d06640d00a456440083c20000151003040c081c6a149400f40303030081628041e01303041001a14040025200300c1c804541030b020b0146000018040d5281c000d540a0440f9034040c03600c2051070304606a45428864103100070004245900c0070505a009288050955103052400d5040c0f500d40350400c2030181c3c00410490700000d004180e0881e07071104002c82c2e8014078a010246031a0000b03c1c03040010f01415901c502e21542c103000030700c801e801c0707441c150941042003503c15075005001d8a140710300e260302e854203c000545c8006103580503c20101c1030107081440e41d03032f207510489001107012a65072a04480281840c0090400b4026035550341c1d000b05003c07291420050b040c50b40c0d80144100f01d030805107055000c10300d0605110014002d401c0141028142402d0860406040000b44d030700c01c01054203203095450780041d8080010310f082241c034142c10b044078410401ca030032501e0400e8056409640090051024000128003040f0705410350b842150107a45000c4400c072881811005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 433267275 1250 433266025 433266049
    0x302060f07110d080d0507050423040b0a0608040c0518070f02160b1206011103121906030804080d080601171003060c0908160503060606031008030403140d0914 70
    0x2005840102c08101c50316040c1c1800300351402812055210341800310180107850005080c0e01c20064100000c2c400c40e5048884248800c0d200d0a4001c0b442c3c61301008240100104804103600034400c8400240e41603010700e0080c40f4502c2020100c81c00756441c02402480d41e5929044004114400700140d145886183c200c0300f106d1380c510481e40b941312031040144110140741c00511a00c800080c0700400c000c49440002d402460a20b406001e2101e01c00fa00c5489000d5600343c1100c0a00f100d0100e12601103405040003411945402008110ba0f03d1904540c48d900c50f03c5001c1c0103001b016183c05095001c1c5100f1740c0302d50010385070021101c0d14003d40b10321302c44008025000c000e050080c0480071846502c0340d0300f00344078a6250032580034100200340b4508100c80c0e00300c66030b03680c480d50f003407200e610302064017904000e050b206903489480780360351450402c40342e0300080030030f120214000042c80702e81c00344150f9002c42d150aa036400c81148400300d450b083c440c010b01c440100900315482e1181408030031980 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 433268525 1250 433267275 433267283
    0x10504030206190b0a0b0702120c360903040807080111040e0a140c1e03250c120315050619080a11040f0807050108071e120c080a05010902040302060f07 67
    0x500c1130442c40020fa0980ca064002e0346002102040130403c50420781c92150204000100810810204ca000540b090840310060100001c44100c070a0001d41208015004600c500340c0714001c0b0714204240315a250020b00c204a42d0b4459400c0000303a113941882174014540c6120051881c260920302108190180a02030320b40369661512540010715a90b41c003075000d014490700d42940c4102800d1980300901e04442100020102081400307003000e0180e9a22000ea400301e4030050650720308000a80d0107010043c0d000d4042480c4600c44074485078590700007040d860145248150a980b55428810280030f03103003030340c4000c0e20100414541c0038041c0c6001e50b4004000003010490071305d0381c1008000c80c0c100e070744140d44402d001201444003074024070140f400b400d82860040dc0600c4c00070001015402140640301280e010ba00500000300d101e0b5190a2040c170281d441804800200c0c1070080134100c00311400695903180900115900485000301d4044030f80040196007402818446038406a003d040101e07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 433269775 1250 433268525 433268531
    0xf1608060406200304060b0a140d120207030c0e0a060f0501021911060708030f090d1d010c060203010b0904060801061d060d02030d09080c180112052802030c0301050403020619 77
    0x80b401c1c40e1140010351003140302d40c0003c103000210000b4400300342321541000e030791980a4040084103407507184400710250340081040309284400c901c26800d01006420107400021a41c0001c0f58a8941c00749141c001c0d010f0540c1000203d0365001c500c0b420114a0140a00582280f11140d070310818034515803440c64055044060381500750000541c1c1d55200f01c00c00c0740c4000c2c010041254822501007055800303007004016145c11003540d00002d00b44400c0300e40c1e4079804a00c0f511405543d9220b950001c032510350000045689503180c4445041513004120510312850400d50042040741042c05048115241c034404111014100084c420303600400030503080e003010300605540003580c0c6c20464000400c07995100c1040d10782c1443c0c0841d043c18194208540518080c60100340c080c0c029200c40740c11664401c0c07848007845464900745007406c444a6200c00f1055030381c0300600004070484148500544220101d44401e68107600781401d13100104e03000340168000100041201032541c02059811144000c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 433271025 1250 433269775 433269821
    0xe04030e061b06010905060d0f08040e251814060c0d05040f0905160509040209180711011e0b03070f0e071403061e030c040603050f1608060406 63
    0x840d0440c0c100c1d940c40b1110400850101c145001c1c14441e103405409030590a006619000020850000704010020b1040341d409081d03905015004083d94081c152107001e858103070800c07003404404001070516800c1e0150b4105459001140241c0e01d40388408001b85e0042c0501d841c10480040001075008020b400000c100210740f580d003030a122203e520740b0151523244d265802e01741024101c0c40e80c0d8000a1241e803402061101d0f0074402030317210044a60520301140d0315501341d408074020780200140d494001e10f020082c9214011000f42d80ca105651550760707000d8803102d8404450903580d10700551101e5005650401c12140003903040540e0b406000740407920644c0e03484001100085107584000700b01030b00f000a012600707600c1040010308443d118111030443c140200000c0700300c0c02901c070103011050070340101d2815440c140058641510000d01c100700c10742d0340c0e051203929455401510805806550351103a00346c104d50301c07110f003a1004103004050940d565038442e002002c0b50034410310300c00180300c49 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 433272275 1250 433271025 433271029
    0x14090d200a0b1503030a050f0a0302120f06040b0d0305220b0c1501060f05031302040b030f0c1206040c21080c0a060e0309011b0618050a03110a0c0e04030e 68
    0x11009503510610a00ca0607182446000315650101440c0034801d810821000e00c49940c864188c410b95103040d18541e90311064403001b50024030681c2e1410010049080420520100444072a0b2107004141c0c1c0030301160a0b40300401c00400d18130703075000380420024850b03203003080c0045101c884072241a82e03812825540b80d01d010b4480da00103001c0e9203982c1d444041c2202101c401e41d207a4600604060074040c6550441c0172002d040d9000041400618010702d0708e280c4250768030754200c0070b1950700c06400e45400b00d18801820361201c0b04102520700400741c90f00c6030041d10388000799591140360010380515242e401c040584107a8542c1a505100094220100b000492890b02c014282d00c241040107020324029403800c2030030b507260240d81c42072a80081c000340c8101d98200c0700221841c40004d84000c80ca414610700503000702000b45104600e8115120101c0801800050107541107009445000b00e80c0e0b101c14065076036445802c0300409400c2c0c44181002203041c5080c803035400c90701c85d05005024040d2440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 433273381 1106 433272275 433272283
    0x3070e0609090c0d090c080c1801120b1e0114030d0f080a020a120c2607050a20120d0c050924160f020414090d20 50
    0x10f204442d20136543e12030f801c1a50712038050000d03151203060103561140b4400559024201d000e4448400d0010000010304986c4041d5650114910b256940c04072940b01904100d5001404945880e1800408142034040c002c640400c1d81b01180903410580b07010500280c4406018402a040b604140d100e80c0c01c50784581000000340c2d4602809404880c5504504290392015150005c0b110340141e002442c414011070203a40c040002d12800c00ea10020481074855001080040210211043c0035281280e1100d9820101c0d01d00486100c5903181880c814040302e02100e540043c62558041040c41800d40e503051615041d8180f920f08800309070610003064040ea031803200107408444841c10b900444101d912488840b040c3d0310840c1c5400b551003a14050100e10541c20076007412078000701c500300944540e54080c001d2a40c8501400151400034649506100c030640485808844080800c = true := by decide +kernel

theorem cover : BRFrame.Cov 433093525 433273381 := by
  have h0 := BRFrame.cov_init 433093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 433093525 ≤ n) (h2 : n < 433273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
