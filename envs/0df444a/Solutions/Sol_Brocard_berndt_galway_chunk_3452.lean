-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3452
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:11.819988+00:00
-- url     : https://prove2.me/submissions/c0a8a2fc-ca05-4784-909b-24682170732e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 620683453 ≤ n < 620863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 620684703 1250 620683453 620683493
    0x4030312020d0e03070f0204050a020a050405090405190305040e0c0c1e010f09030809120c0a1509170c06100609050111030d051003150207110d05070f14010207090603030903 76
    0x10610040f0200810240410764040c002101c00110390b030041c0021504094030161510740100121132490340c1003c1110115401641c2020044d581c50070418104940340361030700c010b20948410001450b6204e0098000d039654a200d03502c0c180c0f5000100d94092048151048036a000030001c40c0f9290200340074504c134042c041e0008218030141021802c11502d00341c50880110ba40340d4284171030714404208101d104184900b0f620310341104c0f28003403981c1e4200481c000344103000041300344c1e18032082c41d0003101085500240140c0b5440c0440480303007040d0400140c20195101e9200002c040b5400d84400e041107880a03285c10b500c007400e24004681190b4042c01140c0c091004222a490a0307109100d8248140b90b040081c1b04441e045161030a24640d000b0310f0207007510300501c59507000c10315403846040e0966089811506100079031800d5810481564440160000c1d4418009444144010f508603400c80981c00d039080c0648071040b4000b20340c0c26000250005245200910014a417810603180800c0301c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 620685953 1250 620684703 620684711
    0x60a0521011503030e04020711091515090f0907092d120b0c07230c090f180601150324030302010f06060c0b04030f14030907050f0604030312020d 64
    0x4030580d80c2074402c141800010702d5080e00c010002d05030b00001c441d80c460b404031000d51400070240c885c034820380b44a0ba00c4500c078180c0740001c900c0700e20080240504182014082c00d40d540007175030f101102c5070400f95500e070213600c00800c14400c4e032070a991003510074402c80e20b6030018141407140408404150b481c141c01c0f010510a8460715841840c846980101802507010051442c01c0c0fa080901003400380c2150070466091103460001104440c0d0381e180d01c52001001072804090341165031812016445460b0461000c0d000c0c86030704c8218a80345486100441c0c80a4601502040050f948500902c206138028603500c2c500c0710554030030380098112403280100112125148003050941040303550048015070364507003042140304141d01400b0000c0c1a10b0501d9110000944c446042217113004000804000c00d007d04c401800e40105608042d4000d03010429449190400415a44031840d004071131090120607101c80392403500304100c0d0103503a031580c1c0707181501c803c0400b142d002c0d4012140f00c0081c00d0311 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 620687203 1250 620685953 620686009
    0xf130204150503010e0f06060607030923030105060f0d02060306010c021201090501060b04081009060609020f070b0109020a02030d050c12190b1516080d05101508060a05 74
    0x50380140e0301e11501e0015035100c014601010035003150503281000c591a04000340200b00c402001c2100c5504c0380094071180e640b10702d90701e001c588055064000800d13641204070b40f88204102038019008085081d8000c2099444e0f40041028409c41c000801d58010f4240300752400504104000d15004076060416410107001a40020b810f8403c10a00b915260341da031581c0002e2001c240500402001c10310784c5140b50a0920007241d0300da0341840700741901c180d00c2d0b103000300401c00d01ea88000010641c06000710340300c82c80142000101e9102c3e041c25102410100c00101e41d280c041e03c21940e041100390000d501e49240c0d03201d40005410b00515240200c2c1040c07190400340300341100010704c070740406a110006c0000348a0030030b04481d0003411740c80c010258502c13003050340c1c99440b0480745032081c248015580004c442c50011030f0f5204454115100d6800c040600044504940841c000d07560b02100c0b80c9025960720104842262040328096072209410104200600342003102403000c0c541400c411100384a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 620688453 1250 620687203 620687209
    0xd030905031b031201051005030406051f080a1406010609031b09092907050406270e0105010206010b0c03031503030d0920120601060305070207030b040c140609090f1302 74
    0xc840c0e580e080403908002514400c1c0d1505003001303070151000f101c1100701480340c01c0d002802400010b000400d000d543d2000b0400325601101591a5100150340414506480c1d2726950707103c0103130000842d032141c00b81c00410b00b05d25010801c02d040e00d00341d0340d0380040280b40da201d840d645244041c5042e15030481020224018685014049001340a04010191914074000220034070481058420350b2160b487e051010700c80e4400d088404070744241c030300318100d211403071030122790820360f10b68030b4080340b2284c440040d6440c0166912030480f0400d03002e075aa03d81e80c9140381c4540e40700d0402040f0854104000264402410000c40110050080c00322410703c0320203003008044554a01c402d44a9036590300340c000c1580284416420100010340b0b6994007240c484548075501c45040c098070040c5910b42c40000c008610801c402d00003135800075030090385030a2500700400c440301c0500403040010440c00000b0003a0400f4001c031420960003a20300b6150307594841c203403109001d000e0082c10b41c04e040a08003001580e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 620689703 1250 620688453 620688487
    0xf3f0503131d04030206181203091506030a12050703030b060d0e010f0c050712170103060b03071a16020a0b040f08060708010f031719020a11010504080d03090503 71
    0x1d0207090401100c1428019081108010007540351402d19944041100007580071402e40c0d005540c10b86040d101d040c6030001142010800c1e030402c0009100030003000140e910005010a50b481d408900900303070340b9000d09040e10754100150141507242c5840e900a1070078400e070300416065000c0c2c500090103e20303100c000382d80ea40c040c02d496a0015220b4908140c2081d00788110003070207401c95402c20912015100c041d24502070550702400b28801585003903c03a600641000c2d101401b840c1e091030240da1a45000b00082242c0c004440c046e10855002241d1405444140019030b00042c002900b00745502804000c501da01d414102d82206138190000781e07070f0b00c075400640041c00c510b0241107405404c14a9451415070f00a014804001e221070040216a035081110303c2520381002d6048180704250b03041d03013024800c0c2d0700800e80b502c041c07071500303185a9070126071000c01e1441002100040424500110740c54011405008440d4200b10500850750f03000e0340c00009030a1248050380e0814000761030700b00f000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 620690953 1250 620689703 620689717
    0x801061103120a0902090105041e050402040b09090601080d081003081e040803120c1e0a1b030c02010e0a0e16030605030f06040b0f0705070f140a0c0f3f0503 69
    0xb0f0381301c88801e0214030b8400441d501500302502c04014007660640c10305594420b24886103495030780c64010a09644454101c2410100301501501e5942480c3c1055130383d40e0380910a1820500642640e562881c2c4154003d83c01003d40d81d003015a040d0075a1180c145c1036001951848022030303150341c00412001a04054001044a94040c58079040035285050b20b1150080a10811810410440300c4d0402c2608a80d180c44c1c0a00003100e40301d501e100c6090300da841c148501231108080240c5100c04150f4010045401c0368400ea0b102008482c040d800d1001c940390030f0080e40380a0914100180c64200260000c116400c3d281c82d012610582d030b1004a42400002d400e001c40941142c8200400d00101214043c0c00021002c494109480c0082d0010a24002c86d50300a02c0c602051100ca018042020b401e02c004d40000010340f031990465190500174840d451081e60b04044100302c00040c6507003800301d0742d14440b4250406000050285e4400442c40c414021b413600299640340c04413011680402c050800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 620692203 1250 620690953 620690971
    0xb07030e062e0807030b070c0b0a021c0b10030c0203040b070c0f0f12120e1801150207030b04020f0406150e04110f0a140c0d03090b010e0601080106110312 68
    0x92000e0401100250601d02d440e0210a00000a020005039800152a41c100d0b43c00610f0030603a51a08103044403000121a8040c00950510040c000c40c550186d00801d1034200811161340d00304069a0001c00362060000c4285d4004031541e102c140040c000e0304140307182003441c81504d14060300e0b4080100c50390420041940d07041c5a0390400d20041c02c18980c4680a00b41400e5024036481c1350a0f01d04002500c10700000300400c14250ba20082180238000b0100550f03402000c0c04c0c01c001d400c0c0400c080c008001d1003191384042030b10102c0180b007400422914250390300701c4540300c4250f549401303101c41000700307500c0036801507560140002c032550744001032245c0c01f2041d541c40a08100c0d40c0d007004141c0e8801d0910a03480d074410840910b204850350100c40f0380a9203400d0088250f10100d86c094180d00901c0c4001c82c203802108442c1c5030041c2d01d544814103162180c548c0e890940d0700c6002c80010107004030b0361203010071100d400601005008140010b4100802e034220307481c0c401007065545a500080d00d5072a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 620693453 1250 620692203 620692231
    0x120105041205041215060302120a1209050d022e080f060105190c02030c1203120901020918090a050a03090806070e0a0501140c1501030c0e010b070b07030e06 69
    0x1040081441a4103240762440c608642420304280c00a42204a499801008150f071480844500c8249801100045400804404a0103801c41d4090388030702e100c070001c580790781207100a48210350040e00d075841914405400b10110849541c2440301c0311000d001600581c4000d08845462001c4100d540c0307018103416034484e421418641c442c0e44148101411007410305c4000c0c06500202480b900000804011a00c0c0c081c072450f45a00209042034814040b10350001408203140d042d011000005210300442c0c002c13180c249648102c0b189080340146840c19502120f50716018184000441c0395030342000004082d03c170700143c181d40329480c0440c0e9880c1180072030f400e201e00304a2000140b10940c1d202072241040300c3e16201c50b1001499041060084506009200420241710794a00042d6602240907900311440415284441d40540400b44400c9501c8140d0100200d90441c2400f103050491791010344142c10580d803607441c0c40a07614010720700c1307040503604d03c4009800c0c0e1040103030310300820400701118 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 620694703 1250 620693453 620693461
    0x20d03020901050708030c13092306060c060907140103090203060c031009060303030f0c0302030f010509070306031e1103150c091503070e0103150e01050409060b030f0d03061a0912010b120105 84
    0x80c230001d06540c007040d036070351030706450407405c40e100d80b40b150f0100d405d08580f4200740c0d20300f400500316010b0110380c14401c1c4140010420000c0d00043c009080d00c66134881804e08035880401141643c01c100402074040e00000c01282501581602450b084103100d00400141c0b504d075003600081300c141d80e00c00c1e40025103c0710705250540035403040314101c5030385150552540c40c182c800c2001400303041c0319a5000e11010000651300703074400e61099018551125100b070b038800240c2580300c0c18503910380040c2ca2440042d0964009460000350100c0044551041e01c10150748601140b44640c10103103599400109801420319040103410045200700360544a0040740ca200d9000181104d24cc02d0103000e08048107002480364080084070941110001c550204440d4224a81900a401c05408558051186014840742180d0105001c0e24201c582d580801006690303003c41595034106d0190748141440411200341542080648004030b410083c0000c200c80100b00040355000034109024003032030f550b9600744 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 620695953 1250 620694703 620694727
    0xc08010504050c1602011404030c03021009180209011e1805060a0c02040216050a03110607050313030309030915031a062a010b06040b0304060b01030c020d03020901050708030c 77
    0x6405010166420800c6107043c092074605441020103001c85100140140421a8842c89894500c000c805c240c0c03a49a682d41d01e480407010300907020403407054400e500c003203080c0781c40341c1210022180c81d910301442403200030300303208029840700321858104601035005401000f42076819106400c0d1079a80d00703100070b003000801c549103003054000920521081215000c0039500003045086190121001680e4030003822030b0096001800038000d0142c01030703154481c107050b00304002c1c8001c5842841035940300d654841c0111a140300c00c80300c00389068600c034502801310b48030fa400000c03414440d060402c80c441d01e41182342c10040000c50b09400003034560081c10b81d4505442c802c6034109506840c0c050030300807040c080a0001808410300d15103940760110f80c001d014001d40151891003006403071726540d01c0c1c8510884080343e01c22142621a9810a1a0110554440d215002c6155140c2d4084c100414081004070060752001c0b80150400809103c1d82e004142c103200114014054402082d0b69401507441c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 620697203 1250 620695953 620695967
    0x2041406010e100e012601030501020301030209070f0f0f3b04050c0406210207031e020a0c03140c0405190b24070201050c0a0c0515211312030c 63
    0x428000d200700300c0c000c07800580013181201c0c0d850090134a1030240000895800c2000c171001c0e07000f41030000400c0000103114041d40214140e900a07100d0400c0e5588034801565184812107916000564185a81c009244030742c41303015011500e480c0044001e4058001000000021120b81210450a55580c46002c003048544100e910050790244000d182607070301c100311313409144039981c14007407048003005a1a003a991070524250b98900215151a99424002d04050b61000b0220302d1460b0346200c904c81c24000a0381355001c590020000c580203003569103080d0100d1030070900d05854410a8242c85240d6204d00800e0b03c40c405807018041c100b030741406280152000350500c98020444000c0502450242c000351200000c81c032104641e50b40388074801254680304d00a09100d060044601070010016584800421654205c070755410355002a03035003031070f9440758440303200244058001c41a00340b4041c0808a50020074030040114036066915002890000c646071100040c2ea1180c100c4c0e070381500422 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 620698453 1250 620697203 620697227
    0x30a14010504060609090209041e0207021e0f010e1c030e030d030605030717030708030711010c0f0e010c0f02030a081b070f0302090a09021e030c06070503040519030204140601 77
    0xe0b06225281c5401400307031452903140200340d000c0d900001c41130016266600103410b03480c0c06402c903440c0711524a006400a40008000324400c2c440c448010b02110055205586840030081190354513803800b40c01950000b080e0204a038024080c21a00c10030515203140c94000d1034002d444800312244101c0400d81000d11030800001032600d03190003400a038400003180011b480e002011440c200d0b4042d50030b41d05d18000c03110010122a800010440015400300c1000da103c1c4202d00240550644002c00b40d90071001c01350800c0c0028103050523248030390300c030300382c0360403000d0081ca18901030135001c1d000710b820003201c00d006071088900011034a228078404180981c01c4500040a0601c45042c607248204183e124800a8031810402000c18100345540d8002040d0a07401000100d04d9800062100d0040008040c40e612a0190014072007046c10604c003202d242c10f03840b40185103050305045c10000c03540346913460034010003e61000840140c46900c102400303034960408216541c0740540004109a01400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 620699703 1250 620698453 620698459
    0xd091703070f0f0c15030617011a0d080405090c030f070908060408030702030903010f0c09290c0f011e0518101802041a010201200d09021302030a140105 67
    0x40003501268040c28042e040c00d500c00040c1500c000b281c188400481d42c1500110701806884c18001e01c1c0a406030f102e88211541464850003143c1c6601c00d5a0807144140c030b079182d9185c3c080b000208103140468000146600c5103940714209034072000891700b03014084842d010524000000e10200141d000701302540700c1d11a10b0301d0000b2904040e031803510394002a10040940c0404000320342e00500a000f40d940e07020024000b0400441000103440140590038403580101f554202d020885040f55240000446c1034107840c00c8050441d044980c00584c04a054450303203004680101440c48020300403414a607411200901d030b61180c90001034101d400107810035854030000c048040c5d00030000304919a980000f40e000041c0810703115101c0f107039021461030080d0700c60b01d0300340f4403042019000c000d10926942130740204086495007a12049100f091819403a070944140a5103c0019050f0841075030548060400d10401c0f24081d8101c0998000b0b0300d078821101d403103050105400317007d0112180149011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 620700953 1250 620699703 620699707
    0x1902030a02071b14010f030f051905150d080904271703010303020a14010b030f0f0601050102030906071e08030411120105130f050a080a020d08151e01110d091703 71
    0x403003580e80f290b07008001c150602c07803803046c14a090390095001340c0c00c44402c1c00c000e001074076100000c5401081305000c04290240f60038081a00300440c00010002640c0103030003603d6094658440644035045507204d1917101c0c3e154003c103c40c3d0604d41901c1c00423400c119003a21a010307828038100c00014012002414216002e1004001007a0b000680c10001138221042009002e05141c2d0a4050116440304079014414440408140080000c8041001800e074080e035050342d80f900b004903241c0c0301c0e00b080a68028000e2051801003a41d5000d0590280c6841c0c1340114144569070366020580c100311001e0b00e0f1444200c0071050f903802c0c0750808420440f5880020005894080d400c180354011041010342030320750695042c01002000c000c694680d0340c000c0c07156511b41981d000000d5590b43c41216440002d000c0c1e2001c58404070602c0d41e5041d40300300042c0507004021006d80501c20100441507800e0400c88249649543c085003403150300381411840c1d550102503800c2001c0c030403a0791704008411a5030742c42 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 620702203 1250 620700953 620700959
    0xc0421170316080a060e07180f0b0405210604080a08070207050616030210020c0a120503010503030406050f130b030109061e030b19020c0637051902030a02071b 70
    0x7031146a8034022443c140b4020a445030a5508000e007142c6d0031525041c0e10b01c03001d111040340c000e81c00d070301c580e20502c413503142c4151103410720b00a1403040c0c030035a114400d003440240020302d81b150541040c0c006120170b1b0b4008540c1c80c101249000c20545e800d4415610000364145920b5120a01551000090000300030381840d010100b4868070505030a403681403030220400042520038084503d000090201c1992503410b0034142e680c40740184042290518480031b0300107242c03405041500c0c1200e000070701071803c00d460031200343d40640c4540c00c180240c0380104604650042001c0c03419000e482060b182a03100d41c10024140e0443c0d21640081d07045558a8908030b550b00500614001625031080706640c01c0e0325800c031038104124500d40000506800820000d10000e80020202c3c82540042800044101e40600e5003d1401c070082c6550042005c0e01610943c880302d036001103030090503110303544803a11604515034049800a680110f41150001010420310102c89030341140546c134443c80f120401e103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 620703453 1250 620702203 620702221
    0xd0507060509130c12110403051506030c0d0f0f110d2d050c0d05160e1b18090402011407030908100b09040627060e010518150c04211703 60
    0xc0807141036003119489044488561b9441d800b6076000750303844411200c1c0d486007652140c004400407104140244a00d0315002d2103031802000c04c003110350300002c0641e01801644c0344c01c071001400d044107452804940d0b2084c0303841c1e2611108070328030398010120000307024115552840038101d034581c494800b8030400624004a500402c40056240c0215a02c07181842c0c20f01e17007113041201420501282c1d0380303440c000055010070424181d108110505031841035201c10245c544450141850440c91007200c11103007405c2d2305049581076007081c01414105940089030340484c2e11a4041141100002d0030768008010058081040d98500c1880902c06d00c00103400304007045200308010405010242c46408443c08010340010804030007121041d80002c1d0000ca0034040c01501e10340002089a42c43d24001540cdc00846813681c5051101040180070f030301840f00e0f0742c008140030180c081d0284840c104000a000d40040080712000c10b0300c3d8003002081132060a011b00900100600207035907000410030048150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 620704703 1250 620703453 620703467
    0x114030c09040b100501094e15091713031b0305150601020d12060801060e160e130209011e0c03090905010e0f040f1205031008011802040b0d0507060509130c 69
    0x800c081020300d14640442125030380c08014000149800344a1588480003103220075400623049000f1121035000c901c000304000122078100c4409489481c166110494012120000b04207a0ba20b034010b20b180c0319101e413102c401210070b050b6690700d8020001003c104120b030038090040e0424910842c12041d00e41400040d4403800751804480802c11080102d17924900954800409029210b00030807015071034010061880e1303001e40c2d000105800d000d000f8616680304a4a500102c03401400c0703a80051314180326175000c0c0d00302c03d031118144070608a00c0070403c061500035060031b51281d502c40320000d00c582000f820103410f5410400640b42003a0043c00200194103100e6000030250182d02c7c19913644c0d0402d0003012090b00710040c000d41c1f900140c83c01103030f4080d01960140d9003103c10048442d54a1501600300e40d503d00c800700c0841c03174840c0c0e078902501d0b280d44800c500c05006481484c15a5540d40c805041820030f070814008520041520401401c11403071900078845406d8041000407025500070300b00c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 620705953 1250 620704703 620704739
    0xc0a0605031806040809191503020a030e06060307030212011e0603030f050a08220b070f090f0e06041508030301060c1e0b061002120c030c010f090b0114030c09040b10050109 76
    0x561034045006003c0c83c2c40501f03a80081100304040d48007010048401000703980302d010702100281c10240080b414400218070903000b16030060081449924650a00003401c615480540c119541d80d44542c4800e4042a428950308013100c1d8000740c01e80c20741c5030180c4140d440790491401c0000a0103074542d0940c01a843c150401d819203a46802003038030b4919621018854400100042410700502003919004501d080c030104043d240c5001c890f8a03074000001e45103503071141e1846c001c2500041007042c10141d0203041c1c80c99002c000112184d840326501840d642c400c1e07008600280060410704140183c00985a82d5040a074190440c0840652111481d00f0700150903d4451903810403402601e600030042c484c8003070492080c0c142c03500301651000381c99402800300301c000b550800c8120000f0f0103141c07042110003940100360381d2359039081541c038140b440b5024108507054071440c0d4080c9e030b03507966045490f88103521031034280b040f070319041c01409081021a0320503418089210000c0c4110003404a0300e17070b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 620707203 1250 620705953 620705959
    0xb0304080903031b01200c030d0e0106150801080709050606030412030f0f0e15010305120a02070503060f0402010e1206061003230906090304050d11030c0a0605031806040809 76
    0x35071550000190440c80f940009845500814000d642c00d03000640240d00300440800c10054000145100189140728400b144034140d0802c024426440361158044054003106000000e280c58651000c2408030940e02e40d00c0c0080b501d408010850600d04002c00c001510024400740258102000031034614000540010502e42c650380e60070788030903c04e0303001d46889032288909201203a4180e4900d8024540c030b56408099004a2515000c0392509080481c100c0c0d0340240100342d9401c41c00208802d43c0c002c108410110f000761000000d1560782040040d0140b80740600000c4c15090610002d046084000d01d00c0307000b1118590050307008a0003148060707001d901600c0409030340104210441c0140012028003001d40032041040d964030049112a601c00d030703005001c4401d00e46aa00d2603607624041c3d4401c55034800f5044604400140b80c1601600314800701174116540c1c4458900010a102e6803500850700040002c0100a20001d07641550301d007141b0001d001d485075041c01d071510041445010000d40c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 620708453 1250 620707203 620707207
    0xe0c0702100f0c02150309120702180c07080c07050109150e040c0c080310030302011401030f03050a03060815190e03090f030703080d1e06080c10121812020303010b030408 75
    0x220b400d01a804804103c1d03401410034030703103000d400a000f030103030426500600f4038401c0800381d01406200d0801c1b00c6c18aa002030800380080902d10740840b6920780140038005042e001c0c480440002c041c2c03c00380c80c00d59640740282111300d050000040c5000c14903400302e03000710000640304240c19048040030340300a0041d200801c181031000b000350350081d00304200504819002040000713140655503400c050701d2091b4000e03c10300e41c041030500342102007804054102c12024807030900090180005200190f07041c2000300321140d030782c45110709011a607800c0803e0300c40c9460070490751407a030f568030010000c00f1441c10042d2400480d881503490150f180d20342c0c0503160000c5a00301c4c2c1da40402030f07880110750210500d90b40b00030300c210480180a0004001d9060710310a501d020302e50101c0d0090301c040c0c2d4401d000030700340c10611408101c01d103030201401009120750503001008414442c0510185040e07600300d47c00074003206160050f60a10348010321401c640090005019407001b0408480e0095000440b20f5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 620709703 1250 620708453 620708477
    0x51905060307030e0c0d0308010315060e07110a0209010e16031a1201091707060b030a03080c1c05011517130212070503100501030605150f1002071d010e0c070210 71
    0x2803400c030701c85c604103901c0a403207005081015400282c840c148c0307124034045c2c00c00d40250b8881106842d003901602e0310384164040011220b9101da4070112103414003408603445c5d0101a00481e40c5401c0c00c4e005040d60228010402074101d05128032400810060700e070030401000008032544c80480c28140145c42030030000c3c03912204080940004612a401000c09501c4088442c03a0f00f0341348c1d00481c400c030707019400c2c03003241c2d00d0300d25011522244150301911820515560541c0c0071696500c1000e11401b400400d00e01411642024400c00d17003c0c0c00071000101202884070b50181621009135440304240c801d0000700f00101d491b1583d0148002c0e410b603580701040100c090b46034104225500025014030810b60501d40b45c110b507070801812070f8050201044281ca8982950007a032200900c00c54000c9118001c001d0282007001034440050003e1040c0e0365295105d0b825030105000002c40003400441010041c460041201085a0882e05000015103007404681c0401c08503403001c5808800c0c015180700318 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 620710953 1250 620709703 620709731
    0x30c0105030a090809030f0c0a090e0604110105070b010b09011d15070f0b0a0f0b030d0206010608060414150f0316060804031116060e0a050919021e0405190506030703 73
    0x641e40480e0014240c61f09001c041c1c1e44103540c1c2004441c8103100b03080d00c2c2d50014801c082e600c601f1038040201005004a0754554031940c5000102c10703002070401108001c0940031401500e450750103800344e0725026a94496407030005100031804000010b810b444060522140d6803900160107044041081c41c9441d6406802c24440b240c03c100c00141805024208000449038240d000303018400b00d4a01c10080c80c8031034401d159482c83d8281034100542d01c11001400703100d024489440d17111100030404200460380b250791002c070f52819a4007a0000c0710140024030145080800c9400700d40d01a0f004110700042801d003001034241c2d5104a2003405600404070303003410b20540381d0000c1c05860380b04603004400c030302480002140d0f942c0304d010005407610000e950186400c00d200c0088440040a521403901e800e05070034201d4a403802100b801c65403c03c00c1e003115001840c0c24002d440000d401541d01caa02d00000d00c203040300e10074203008129010080500c40b6030b69907001d417600200305290002c1d04000d05494 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 620712203 1250 620710953 620710957
    0xf03100b030f1c0215090c09090106051003020d060e0903071113060303080412111216020a06110c04020405130906090c1e0b0307090308070c031718030c0105030a0908 73
    0xb281c0d080c081c02156624940084011003403c02213a8200e031407110412000c800500c030241e034001800e41014541c50418a01000c0c0c254004090200004602d40e4842c005005120001c800d00701203074001c41d40ca000480d680c81a01e00400c1c02070213103c0780703103010f2440076200d101e84180242801551400c0d0341c01d0307860380b10403a0100c109158042000341c0c1c0743e040242500004503801c40c0c640c0c1c0362201e150315403071040150207105160b1800800e940700701103c0c00e0960340c1145550040b009a5002524007590300e070b42801300101080c0d10740301d074a400800681402d0001c0c0d4601e840c02180100420800782e10383c0d031036002862044500000303034070751245070040c05080218806000c1c01c4140c0d00210300d04d8680c000d43c0218041540410034101da643c503080086000c11142e440120b042d80c0c80030000300d802c40b4014421386118030822482c50351680e03140070400703180d62200f0b00c5900c80030460380c010801e4154402b0400e03c04a000380341071505031000034418071004000200654495030600e041000e4481 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 620713453 1250 620712203 620712223
    0x3090209040602040e090a0c06050c120f09030f1515180703020d0b01080103050606060f1204050318040213030210020a150c0f110304060f09032405060f03100b03 71
    0x805850340c01c0a040240281d08140145081700c400c4502203920201d0000704035140d01e51041828400516041d4162511781241607001130600500042101e00c03039990700207007181740c0603040b2152034100d454180b501c0c04e68544924420bc0e03004501c3d03d8804c91700c4403503c7c4e500a07584c03002c44645c45c4001000c1100441045914001a001c0700e0030311071a590190042d041d28048010200300c104000c900445032180c0a20000c1c20340c0e040316020494609088000b0048118002c601501e4200160510351102108072815526074001203019950040c00310301d00030700c07030404460070350911854103628480c14190b8071000b0700c90303d9a40501da203410700a02c504031440317030410003010f90b898400103444040d0401903010381c0020501580f5a40c9580a4030108840c064294003c500b40b60400700300f07580201c03a070f0007414107110340b111002000170310900c86044414000c0801003503000702a8803180680d60081c021510400300303034500300700f50b48002909610030210a03601051564001000c03038288101d9034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 620714703 1250 620713453 620713459
    0x108150f04051b0d02060a02010c0315120b09030912060603060a020f0a0f210902090106030501061706030a0b09010c09081b01030b280f0506090d0b071103040f052815030902 76
    0x402c180d0301f0390350107502c2520345c0750140d01d0a10028840001100c0c0e8000c981c026001071510510004010601d205800c0350300010080442c1d19144a02c00011610744c4809414141a40b0410400c07450f401d00340701c0e40b0740102c2c00c10020f504200045090442c0c40c05800e05c4842044032803035100889621417800d401d060402504034240100c40c0c0d020060207000b6003c030581c09412484000200300d8800e12070103040f28842d9841d440c10910145da0b071440700f10301501456062182d40c0200000c50141c00c80e003401100e801c0c0c000610041031102c0074055010301e5105000c2c982102035004e03a40510300100c3c4488a07401d10300014174001640014107294105400c0103590390440d1615055880543c000d507060b02e0490060070300c80d1f07940d0010464148a000205c0b43c100301465075120014448204840d0070400c142031040c0500d1640d46040d143d81c2040c0c0c0488001e081c145c104000300e08292001035154030414070748400800c200300c0c0c0016044184c2c400c0690f5500f5843c809680b0f94401e0f44201e5500d0740c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 620715953 1250 620714703 620714707
    0x6030a0603120203070614090304210501021b1605030606060703120c030e07140a03060b010e030d0305061c0b0c0c0708030f0301030b01050d150f140108150f04051b0d0206 75
    0x903074002580e035001750700304851441c03525140d20120020710f00c81c1c0d80309002200046140034105185e040701c403200c90310031100103000003080100107030f402e0000e00040c220a2407658030046001ca002031170880710003104850603038519002e020030740700826010b40c460010b80d0550f070b5400c1e803854212034009402c405040c1c440e207409480101145d040e0460010402c0c480115010761b07448100f5049102e240d1440e656102e982c0b6035017000003501c507400121040a050401c202e080140c0d002090624045084590002c0e030313141c2c1049400c0c0b602e03078641c90807900304143c000c06030045a40c0e0680c180c07001800f0400c400030042250b41d40e1034410040341002d0130150081c3c0e500e84030000e80450254000307020403607401e0300d4000046410700303002c0741032001c258114600f1400c0c9201a00d8400c0140382d070a00101d0403030740340d04e8800c880300c00360f0072245e00038081032000300302c98000400300c1c14840c035000d4040000d6400207010700000c150001810f00f000c0300494610302040e40b403540024099100c15100070f40180d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 620717203 1250 620715953 620715983
    0xd11030f0613020306010f0602060402013b040f1109120a020d0803011401030504030e091012211704030e0a0e07021c0e010507060b0a0b070b04050c040c0e06030a0603 73
    0xa401400340b903880c4240d08a40b05640c0301e203000203100381c480c0100c0005a101c07000103800340d0302c10310b0103403003185910014078040c02d030a03070060403030038081182c005513802d0708580d00c0b1060070140310b0440144a180f00400c011198400134192074441d42c45000e11640c540300140440701028881c4440040e4018100100c4032030914114005400904c1503024170181c245026103294003034016a41704940c140d60b0b600c400d1b0b040e0f00404c04148809402c0101d5250005008110300c42c80c51120403095014064a030300d043d191590000344680251f1600d020045000e90150020744e00c1c1301442d4101c0c0d03150402006a14480c030100b00a40c02541c00400c0241c2507074140451035802040754000d040500c01070368481217008034242e8504654894142c0081c078100003800200d00254012149004002c191035030003959401958081d802c0300c1c030705503801e800c1c08083c801044030400c144c4120b201e0503a400d00034502c100802624100c01d100280d80a03040010008800c144075038015406598040714441e01100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 620718453 1250 620717203 620717221
    0x504080909090d030510030b01060f0e0907030e0c0f01050301180f0524010905060d0209030a0c081c1b030f0203160605070e0108090706030c090b0f0310090b0d11030f06 74
    0xc03041d45103404a40785c440414000c9400c40400342c01d407a040304680b4810b0b443c1c11f070200c80c0c0002041d01c0c00c041045520148240e681c90304039045c052000359034041000c42001d02a981401444800d03035128000d140712000281c3d030403109031303811603580b4050b1255026080f16003c014002000503518898500804c010400d032034901c80290783d050305c413079540200e040b071001910408460f025442d40648140304c594000121034000f84054100901a03c18003210b564803400100c50035045412990000e1019010a01070001801d41d19031181c0350040740001020502003150300008000f070108050340c1d05030032842d4004c0049500b0031401e40340e0306844c440a1300f40003008040a61740f407400240c003d0008500340d03200b0789445024507200000741c19214a8002d05030010407690071603600384110040000707610b040707040181ca40244070034905075480c40c200254a00c00d1845800540b4041d00c2e04c101585942c60342280c5a901319403105040180c080e4020000740350a02e00b4242c2a298031a40040280e070003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 620719703 1250 620718453 620718463
    0x318030602130e010909050c06090411120a0c08070e0402090103090807140607020d051614121804020a050d090201030e01090c03060c021c210501060e01170613050408090909 76
    0x80c0707443c582040607601e031001c030003c0d51a061000752090b0f00c10f07003040a542c81c0890007880c52050050000842803622a90b60302640c0002c1e519a00c41c4a849040003103c018038081d0545000c01454001c80c180b030b10070b05c09440aa00152018081c603404079100603240d0195009040150300140b54540b40d00651a181700303010040c82103400d00740689404a0030060002400405d01c104d079885e4141800d40d00080001c1226409209032a000703140d4442110a80003030107030b01000740205190540d250701d18001104809001c3d0368081c000c0b4410098407004a03407210070790b008070100e424007103840841800101c001d801c1c55081c07041103510f8101b850341000501c039018421280302e03410900c40c041060030160384070b8044508801c4c5124591444210141c4901340c03540e98004004c80070440c0c040013001000440e45e0980149010900360060342d030303031582c01c400c51950210843c02d00f01d840e40390110114600f040d40204892809482e1300104040110355020b403207040310042e00342c09c5285809182117980b9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 620720953 1250 620719703 620719709
    0xe04022209060f03110f0904050a050d08011a03090c0a0909061404020d0b0c0c1c17070f0c0c0306141806010509010b0d1b0f020706090f03031803060213 67
    0xe80308201002408a045019241c1141c0098000a00c01441c54585040c4489642e100b2584034071445880c44051781d4a000a0f40254007400042c0500c039014a046807802c102001100c06024901004021000030168054038402240d00e6281e200c0c0c685003640780c503292802c1101075200160500103e015841c4c1c1d400780c002e903805820f05218841e44880c500790020400d40d4040d4209000380d41460119000c8081690001c41c6d0050846c0750203540954035041031089402000548280d02c01d02c2d02180d4820341040c1c1141050310140f2883c1805c0c180544554001180c45d0107200d5140317820010701604144800c011a080700d0140007960110407414490701080300d4a802d00480030305010551140001c60700e05071200a04000b40300e900f02460406590401800400c895865490050100721884a08030000015454002103c241450080d0502d00d407500803200708040b1501c1007003494101e00100c411241c00d82002c0c2030348440c1000c0400114810380001c1e1825000103005a858000d0009210032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 620722203 1250 620720953 620721007
    0xa18031506121a06190311010801150f0e03070302120f0105010b040f060c020d050f0105040b0a09020f1003090c08100b04140a050903040503190c14030a03030c0e0402 73
    0x1800c0c0c94492040c8650980c010141c542c18482d008580114401d0f50544e4000000401414a040480000702c0541d196601308449054140414031a02d50300680340602400312510307140c1044507a0380000300b00154103610038042204091800394940c03400e02c00d180c06903030050200202a1100d41100c1e6840914100542c1742e5840d11000040540310503081c2c1c2c0940b515545056a00c51400104a503140b464003c140d9009169410b00000188104650f40d00440044000b0581d454a403d0000442c88010240f0a0040c180506d0400690f1038184090074210100c5c1d402000d02c00d0600f044000b09281c5e04010000821408041000c0f40000b440080d0001c402a0500c1040d482c203041c070040c1e40000d04a1840700740414007040102c1e410307400c0203a000550104503030415a840d80040d00e09100038071401b81061703081c0503000038420080b0110300a0700e202078203c9415a03482c40032035030303c0031600006010182c0d81c400004105104010307000299000500c10364803003140c108202682c01d2071003034601c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 620723453 1250 620722203 620722211
    0xf1805030c1605130e030f1801020c0f03101e0905160f030c0b091f2f03030c030718150201051807051e04090c0305101b050a180315 58
    0xb0b11003508000c0c0030243c4801070110601d03152840e403c0310103080c80200407106400244440c03038100300c1c0e680240c107003142d40c042d1069669001000180c100725007100401e004180202c01801107450000d92030516039030303001000400402205041c9a40c005504081000e40e040c141d4080a110001607038507101c43d200b0926085d0541d446207400003100f01c52100401d10240e00c0130411403401d1840140400b130001502400786151a550428144550810083e02068048010088204003c45a000083d015098050031007200c420002d0b0b4902000f041014601c2002000920061007500100c110f41890038070002a0754a41610b0b103038000c0301c0004c2100541c41c4c240020112140e09240010320080c40c000342181604100a000f1100c941c1d14034141e4200040b40b010249440b01d00c5643c1401b8056403003400c21a0852508600300501010800d54550a2001d140c070644004090303113004214074200344d0345e6480c1a441c1940d01600080c20208424100302001090024284040d04c1c1700b400c05000708 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 620724703 1250 620723453 620723473
    0xf09030213050f161d061909080f0a0c090507050f190e06030f0402060903030f030a020a17010e060f0f060a0206090712230312090304030b06220f1805030c 68
    0x81031814413982c000010755081d10340302d0782d040e13508004440001c00b4020780d161a001030100760460981c903000d0400a02d4480c0c003041000424004100f000c0f8560018203405003458542407090320003400f40140c800d40c0c541c0840c1e01203000d48103d50340301c2000e22095850f1107640e040b00e0201c02aa0b44140c01061880311022a40d01e000001c603403140c0c4143d894002152555020310049800041c0a541c00d84010481241c4100344403010314804c4115540150760303000f9540c0b0051940103440150442440000e006105541d070501c3d00b0f5601050a6507043c0da815846000600d05071f004c01c81c2c190304400300090719600d4a501044103480740751501c0c22501d80316513170101c0b04500c5055174405003642c400a00e20442009100c50f03500046038204007100c2c202031544000c8643c4503c19681490789510000d41002005002c1d0768096000d1070448108aa04217005048491160b68141c0c4105203542d83c0d04034403031020290f0016800d4104131201a42c821024601030742d50b070b8040100c0742c2e81c0c1d00c40c4010071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 620725953 1250 620724703 620724721
    0x1218010c050d1202091903110301060b03070807031512060b06030610050d0603050601060207030c0948030609050603060121050a021012050609160f09030213050f 71
    0xa00010350001c01400848641d8108480f030b05110120030394680d40800c4090600da842540a800c5050b0101021905a02e54909400d01010044009000741d0510303c081000c004c611054952004050038a01c0b0300d503544144c102d004125111201144004c4188081501d80503180000c5990307209000c1001034841c95820041c1c507000c100d80040d4005407030200500c0c602d2040703001d0820314901042c0407039025140c0d035819081c40c100760071010041c1d108980130800c0c0100031103004d000b0510010108040308125014040c20440d200d91404240e80d003016201101d00003c03d00c84031410035408040c0c000841c00e0b8010060130a41c42203c155906147c08104503140c00f107040c50403a2890380f00c81c00b00707852589007040064007a00c000e58050240018000158440c0c80070aa4000882c0c5c0d1510180c0345508401d000320750001e00780d10301407211a400c12070500b0394043c0720000359045041000407080880c0044400f140305801c0250801507180da80241070304070340c000c1c500840c640c81134200b45981e10581 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 620727203 1250 620725953 620725967
    0x1e0a030c09150e0a0b0a0b0f07031409091506121821030f0c07060f050f15010f030e07080a05010b0109122103091a06040c0e06030a150503121801 64
    0x12074910403031a00c0130805203141907100581060b070280001a4180d82c0b014010850703088078a81203042140020440c04240d0306c403070010080410b0b404a1401e00a42101003100c084004102460070744e004a1201c0f403950310341c015034080d0000050001024540a80c00015070420010044650b2092a0400c84591446104c0c00060030012508034159a500c081400d4442805040c04060080400090006c00e00c1400340c1c0a06406501020400f81480d054110590000800002c1205000e030368401441c1c3e88020b901c1844400e526011400b003800701d51f4542040d245134411201c6105032040241040303019088492400e10988030000701e03070740e9081c03000c00845d6001c80080c00040302010300465002402103002442545140c009007068195450103043c400e14194041d40d803282004011403454140100151214940380140c1c2c50b002d5040031910b1404050039443c42161605684038281c402c1c12203a2005060050403115140c1d80c0d0300f8400c0103a40814440d00d03000c0f41e80306100c00e41d54041c40c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 620728453 1250 620727203 620727209
    0xd020706200a0516020a050d0c0e01050f01050904091b06080610020c0105161e08030402152104050109050d08071704021e0f0a090204090509011404021e0a030c0915 72
    0x68061070710441440e04d0240711000082207901218400c004101d5032101d00f441c0d04403510601611804a081100755060100c05a110b584100c03000a10020305036880000e0358081c0303000b500e010a440c1c50303030b103449201c40c050300000080020b1807010001c3c20310350041144c0d006a10507202030304500ca890108136100c80f81105000d0102e0020084a02c2264030501640401401501e00d004c51a580944000307580445900950784042d021082c0015880e0182c9010841540d00110a250203880860b601c0300a12448410300c500d000c0340002400d20100303421200e0f50503030001c25280c6d01d007490300c4080d02c411004d507155800030f100e401250419214070001180030716002031020307900c0c0300d5285146640d81c0c42c1c0c145180d00f01240d20b400c41c010703407200c10541d000b410044601584403810300c203000701200d0000340f400025a040455107440c541458400d1a009a01a600e6503d8072800200f0014160045241341d5080000e0981c00030610000038450419034103d490280708841d42c402d4044040311080c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 620729703 1250 620728453 620728457
    0xa020c0910270f021206040e0705030607110309060a080f09210705010e101b02060c0904094403071e030f29090c0906030a020d020706200a 61
    0xc400e03414000e100c4000c1c032103090982d440450a02d00600207034090ba04812000060a102c5109014091038203001c4d00011310140001041454a4000005d0341c0b02400b03850741c0b060001d0310410340101231307040c401c44074080c40c040c0010307a40311242c841c0144111011541042e1654903031000c43d4841d140810304d84070360402072008a00111240c155098140d009120455007990303540242449001d00744002c05960314002d40008a02c0b20152040c401c007039109001e002103411500800c01c03804007900c26606004815240041e2008262822070f807030484804c20420350a0a8054140455101c0c0681907d511400c010765045080d41880300d0340e250005850441c0031840d1010b0f11044112120b2040010308100d01d0b010400c0c0101c5440745080b0740c002d0072100d945c0c80913450000f1805174500c48106007502c054424408600d401c100b0b086407400380003100d1b40306031000004030f280242c0580580c0c40840c181c01c0c0c00c40d95000285045802000401460b54150080304a00b080d1030304048180c41c060302881e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 620730953 1250 620729703 620729729
    0x806070801230301090b0702010f02091507170d020405030714010215071b061d0c100f0e0411031009021606180501050108150901021608130b0a020c0910 67
    0xc0b0801c0511a82c401d40b07941d02842c40100c1041541e41e00340520891a4018a03041040342440e14000b401e407480090081f000e01d004100b4821369031100d041c040702d1642d941d1b040c141c5a0f100e91600d405150300b40741c1241100d01d0003081c1c180c02c41800d07a00400451b04202d013141e40d0b150791000b98040d03c090307038a200d0380076070400b0320025640c80300c0c0b0440c598000100e00e0805040081c4104c41003c034019800c0c1624960380e51000701c07100f2084024428244003010000740848195140000c01d41c01c010480c800c00c0040f041c14210046028659050314807100a0090245004607041c420aa400480d0000405107988000280400042c4203d1b840c601c411462507040200d191a105c01510710b5103681014020000c4c5a440440e00c01c1c030607a4060070484016009459181c449484103c80142201000c1c1c0d20401041c40d8103041c14a074940c0b4150b10030744103510b83c00ca528103550746102e1139000c0c00340d10400190311581a940450140e2440004a40070101a121b40390701904002c103a0007446441011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 620732203 1250 620730953 620730959
    0x12030702210a320702040f0e120a021c030f0b0d08030a0207140607080708010e010501050d050901020d1103010801140906010302120a20011403040b0f1b0c10060806070801 75
    0x400d4682d00580354448881800a41080b140b1440081c00c50207015003800010440c4d004601d024011500c08406c11003081c85484002d007100c40d22584400202c0e00e04900005030124064000e0006e80c0c0410b40070500541880d55801c00a0061b1191400c01d9411a241c62030200d241d15081d090007075142d4003c0310349800d640c0c804140000952080c0c0301620074984c8825030104010040080920070b0b80b540d40c1c1c1d40c2c421f080120025040700410f80014565102d51401800030b40d90000644205000020010446440d401c2c08030340280310314150044400d0409090241c440052001181250400e00013040318208544000c0012207060b40c00c1001508540c004101628101691418180c880c005a8411001c1c0742ea801c01c1d4071521503800c03000300303105450320b5950703603001505901c0c00744c4854240d600e1458166101000804001c1141c5448050a00414060b0b454050b652001c14000c01809039500c00d0080282d545941c840001190305007810b034086000b0b000420003602403e11a11107152a0342 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 620733453 1250 620732203 620732207
    0xb0103030f111605060c070e13110901080a11040605031009030e0102010905030f031b070510060e07050a20010f05010504060f0b04090f020f030f0702060a2904090512030702210a 78
    0x7000e06031b0f4041501c80d280010030400d03046528036000d0365000240305103004d0329241400340b59500c2d407446c0d44900303802001017007011400329500f40c149a01001d05900801c2407000a00180556007042c1d40501c18500c1d6000140242ea011003101da02076101d1000c2c074010b0368012402d8075006440202250014040e00b4100c01410740555046202c030440d025540d00307210349008143d00000400c2e142d42d0b000980700420400c251062402030a4486090a83d51a01400141c0a4800c2c10940d000300102110850048500c49403031200804401000380701d0106402d0400010300001c0c01014481c0c3d19044000544001c280111411100c045a100e81024502003000c1c00400c2c002d8a010116502002a83c0c1c62242c1da10045100c0c1c01084c0d1445000d0804400c02442d01030010040003d0a207130032586080b03010007020001d580104a12001002c2104c1008180074082803c0000e01c50310404c04281c0700c940e45d0101030340c49800c29078211450303001c414100640240c181e072030368000038600f0080f03420214 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 620734703 1250 620733453 620733457
    0x31b010903260a02070e07050f0711012706030510060207230a030b0403120b13020903030c01090b0618070f050322030302091c051c0c0b0103030f11160506 68
    0xe04122400714603404901c2902c00c031540b00329481d000503004000c0c148000c211324041c1a400002c87e1a00e1f038104124003440c400180324160010340440032040c55400b440c3e124a16412103c014002d8800344200c5000a10ba00c02000340100008a800c00e000901203c81c089000400c450095004100c000d1410420150f10303103030038907504c280340380c0e181e9050707a1901c50701d80b41c50040d03200d2403003030140789407a0800030280e041400c240082c407801c08440e044180d50791101080ca003045210300594034000c0000191551003181504082942010008014807072800c0c80144540010348000301c1c044c00c5450030301c0342e841c0100e507000081080141c0c0340322591721401c00b071640060490141c1d05800c0f0155000740000c1c000c0c900c200c0c006a000904055541050500740b50700e0580742a40082e180700a070b44082c2c4900f03010540143c5941c0c25100420303141e22503505c20741c1c21904413072010741c1c0d56100d00f0014110b00810b0710341c0000c240191402ea55050000031401c00482e900d40e0b24908940c248401c02c1015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 620735953 1250 620734703 620734733
    0x2702190f021e1507081509090717100e030c070909020d0f1b090b010c0f08040b0a050403030806062104051612050114040f06110d0c02060402031b010903 67
    0x500c100710803102d054030190306000580b0707a82402051041504100b94600c40e80082c0142d082180300710a20040440340601550300c101d00b01e6689007503603140c6010920340b514a52244004406808904800c824081110310003901d040701c5c2030104035000940d103070303591240c0d02048076a40d0141e14100401003241d801081c1043c0300600004202d10282c6940054251120003a1508419400c44182c4018001401c0004241c044c00074000c802c032a10000e0503c00c14540302620f210302c101e540100308010f41c3c040342c000e429148165502c1d880e400600800c160400d0204402040500000c42c405240800a84030894940f4860b40f2524410420b48a07900703030098011101c4d84103030316001000100c40c91551010b03111920b420b045207606c609000c4d0955400044040c2d000c01b0050078003000c9600303103e0181c0c1c00c3e5040400840c079811003c1c88240c0b01e200b210f110340421860b005001022581c0890142c2c020340c000c804031813101c007246900c1416010b984144074045065142c00304000748110300f00c0300903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 620737203 1250 620735953 620735957
    0x1204030e040c200708030f09030c04060605070302070e010e04110d020901171c020d14041d0106080a140610120e070620071403162702190f 61
    0x98001400204050754942e80314800440e018032000310620004980c43e1961140c800010040c0720f01d0031808a44910510f031000e2040c007400603400108c0c0c3c0702040a00411900644104012681c0d080d006000d80c110040403801401503030000101100300440b66816101e1a2013440c2003500c45548040501a414064a4000e001e103252140582e07100f02501e4000c041000081000a000a07031301c60800702c0303020b02005001842e6402011aa600280c481e6003c0541d061a40c0ba2100e42070100d402c40c000ea90002418071004003030b5501300d25000701c4150480f400e80e11a50300903244c01054000351003080314104ac0765010f81d000168146002c80218041a200341403102c401e405480703c40d0166030440500303120343e60100004203c010b0707000400042d604052042400f105080e52481c0c1e0f02d44c0e84d103101d80090088540c0108007156410702c00c0440c00e01034041030803015035440100c4c10401d000300741c08160086450094550b07002c011700840e0703544440c100c0d841900c10300b58030302503810b00040ca00e0842 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 620738453 1250 620737203 620737217
    0x20a060f020a0212070602120712110723010e1804030513030c030c030506060307081b041d0c010306060c03020a140a0b0a090c09140720030a030f0f05040206120403 72
    0xb50304c41e80384505882d00c148014100540c1491030180c907210341d40a0811100d01c04100d80d00100703103001032104554074223140200d1504015032016103044000d400c488a0840130715009003800349503040c0105820000e032103481401c1c40403003c00040080800310302c01840042030000d170019101d6802440750b03110074281038000325100d07101c038482d40010341c02c100c034100324030706041c8140102040380c95480b5200b10006e2440a0030046c81540b01c0b461880c401c00766541549032140b4640d20b035000403000071150310a00008200c40b41c03c9030343d9159400045e50104c0d14002c004035205211310803200401782c060700100446511a6901210b240140340043d100780a0b0381d141e01e001442995900b0b01480d8403d002188010160501e40030313490700d680c00041180c0c0750000360300041914070300203a800b10403401c10816205501383c0030468800c00c80c070580524040055440d82507a0154049814a080420b080081c88035a1540c6000c544d8140c401a5100a040c8443c91924248414090303109209141c842 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 620739703 1250 620738453 620738473
    0xd0f1202160828050a6b0607050f0109081201140a03031803050616200a12140a03020d05090a0201050d09060b090c041505030103020a060f02 62
    0x12500d40e409800482d0307540c001c2900555500888400c407104609034654400101e2001e9440c503580e90700c2d1000060080c00320200c0654520300e25088118002140081006c03030f907201001180c03800c0841142c0c2ca0b00d0340001103442a640044161409080b240c50203a201c0f015400002c00885422101d0202d6081c414119204090b42c0d083c081d8000e41481038002680710042c000d90319095500c140c2241c24100450105040f0607903900c01000216078050624810280641142c1001440c05400140c61071003001d040c002d01910181c0c8080d8000c40c90740c2c0f00745103243d41049504040c201c0d00c031002480d42c4100440310100c0d2038072000074144011814070041c84d9461030350554841e00803032a2140030950115905070020341d64042c0a510a00320000b800000d640d50340040d0442c0070360f4058a920030795541341181080b0301903008801c1c041004100784007914011401546a071720501071000083c400c41d054810315800781f01070364141c0398000c1c00c0140c094140213045800103c024200d00c11845100a80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 620740953 1250 620739703 620739733
    0xc0f04170d03050f0604110d0212060a150206070e0d140717060405070303050307112a0108060a09020d0b03060c07060c091404020f0f031306060506180402030a0902060c0c0f0d0f1202 80
    0x401002c1400055402b440c5030801c10442240303c0e0394441e51101440021058141307601041d115230160300e9041c100c1c02141c0d6600490380b4080780d01ca0040070b4580c0004410f0400c0300006014044403030351142c1c1c090302c5013a40e01e540d80303c80c01550002c05603807081c0014400a03000d0405940e2248180c0740680c3c0e52001441031529000840314000d20540d80442c0356940307290716050842a108080c204046503040000108840300b62620a2408160f4041445452000d40e6003080110b944000c088074414104020902c045900c84503080380e0562030460a60070742d601031450030088131b05500a881500c2030010510001c0d6002c1540002c10b0740042200e48420703503900e400f5601900d28580300c5641400d03d407038003100300d4050b40c104078443c980600c50406042c03140346c10384c403a84000307840158603a200c1c0315215028004110000703501c0040032908507403030000040c501007501001c40c3d08504840050040c46024042214098402c00f00c26081c0000700c3e141105140034191240704590320038001c00c0f0b013 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 620742203 1250 620740953 620740957
    0xa0201150603050f01050901140d0501020d06030b010509010509010506040b34060c020f0309040902030a0f032a0807020d0f0b070306030b010503010e0a03080c0f04170d03050f0604110d02 82
    0x403600c0400c1c0d0700c00604c0703000080680d29038090001a510b03068594103020403942405103c1040602c0b903544071003031804210081d0152803200364500c0041c422251649811901d0501c240195401030343e031000006114070302005868100c400143c0150b241c1810b0607001c85050340a00580c85611a0303024000c08100381540309005400320b21860243c000d0300360f1418906603407890412030304543c001c00c42029103403004000c40b10b50701c00803640020300e080603102103030600d8003010740900145a018615130506030800313010b84c400e00b081c0e150140c51600c4100d014100c000d14400142500800f880b0740700060034485560704080c3d004880c50b0603800150f681f15006080b044500100180e100d000800c00c000c103102585001d04000c800030b1040000040c8015030740c560425000e000c000f80e51022440988000b001c50780500c1039945066500c5480740c05030f0426030030f10401c00d01544110013800103510320920800307002d0080180200c000f40c0354541007002500c1e242e03101c0d041d800c1080180c00c00140080c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 620743453 1250 620742203 620742209
    0x60305030f030a1d060c1c0213080f030415030902211b090c03060628090e0108010203100306380a060206040c03080a03060302190302040c09080705060a020115 70
    0x2180c1c56981c6400b810700e40c16204035400e20808524114103829007100f000c95066809541002015120f402007010080040c104181c00d100c0548002101c0070400c401021a005a80340034080f100c089421401503a500c1c41940b00380c0400c0c418902c0d103d80840d1007a0060940240001c0c6540821030110820144600240c00d8044031580070346907013590100001028507904a04443d0b200302d615204500303d070700f807000921f00c0e071050400241c1511f031450008001003425480d0750200443d0400400e01500d04607990107154142d040f0070000083d80f20050007201d00c505481c0031132400d42442c40d550f00c0060314040310f400000f0810318403103130010741e101e10544100520075604a88546501805e000d070105036034101c0c0003150003100811000c240300f00d15800480390303c901013507502c100b11101107008003229007000750b00500e00c10116140c45054200d0005682c001c4404000c202d40c41241a5550b604512032500d036030304503100401a03485c14034017030082c1980b04d00010400840d00f040c00d143d44d0030190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 620744703 1250 620743453 620743477
    0x903080a09230109050405131b180e030d0905010b0d0326010b03040b06011412040302010f0204050109030b040c030f0f1110080f04030c0c1d09210d06030503 69
    0x92801c0011880700072051a85070640010180445903000000304103080178007600c2d00481d140d0000c0741070302d402d511001481603000040000d100d10080e50301100c0500500c1504802510640c10f08521203551141e40c020b40d815000030342c500901c070500d0801902aa450695955684107a448143d0300c400380a900d2061281d0f82e03559504240302107009088000c0500c070703441c0c02ca40c0c00040c0325000030482125081600b010300d543e603079912900102c40d0840900156084908046507003400303030180c01400b44c0100c0c401c0e00207004502c0451245812402140700d107a0015480340340c10001700d0340c0b0300300032078009018000705401c2c9502c80d00c0f1007018020120084500d0120710800c07030b045c041461207401158000300d5010705145840d8100401040026168100349601100440c0405000b141040002580038100c40034243d9142078400014444203c081034550b000700000d643c00c500811918403d001896a203c0381400c003010094036a00708070040c288003640c40301e0110101d0002c10203400c8802c001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 620745953 1250 620744703 620744717
    0x30204060f2a052a01091712370e1e030a080c0118020102060a09060b090103030504030c0f05090103080307031e0c03150b030c160c080a02040b040b2b0c0801050708100b09100903080a 80
    0x149d00c0c010100c0e60b0101f049084200200070310001c203500c60102e600c1842d0403a8845112781e4400c000785a0003110241280e030501c9502c1480041040c0207002e0a80404000001c000f0b00c406000303900703400c030951540240140c0107940000c280d004c1c0350b486065003a00540e000682c040c502030201300100c000ba0800c8c1c0102c1e4000c1001c00800c0760001480d805410801c0310400301915202c042a035140303060000805801c0042b0011b10414030940c04203c0028440c80d80340300381902603441d00d00810b403038a40700300060304091000030030705440070711082141e69040c4124503580c0c0e42c0c2032140d12a00581d540181c40c846094003000030501500510003e008d0301d2021b043e9507665031041200f1220100c0c11a802981005c01e03c003140c0e074401031031014104501404420001e65842000d160310311a0030010b110000449003c550f9010540c4154852060383d1242000c54445c91410b0251007420300c210030342c4501c104900c4445090040900641d07840ba801c0841240d51a56901d40c2d540c2c01403610000041c1b40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 620747203 1250 620745953 620745997
    0x405091c092303060c0423120102181f0c080a0207180e1903120906110711091b0a0c11090a1506030204060f2a052a01091712 55
    0x14010650415030000c404d0b85051f01e091580d1003111007480200781d15019502c01c0040e15180c0b58502c036440b00120008569820b00403220040e1040a1035000d8018503803032030800b0940703100b81e2401d06c1d00d410944542c0074041301541c13003101c580e05c03078080321045021302e00000905a145c404602078a500030310000c554118854082864170321a0b444401c1900314070185138020030b03003001003950a0309a8540100c1c8016144c1000006840c25051401954070001150001c4c05040d6889140c805d1080396980344640300d6141c0407881d00802003c4a034152000c12030340810a000700b0290368110b20620310480d59184000c001000b1500c2115a814440d8482c07a0711440c4180c0115240c02800c69070600b103003050300f4084000c116002e1544d000702840740d109110700301c00b0383d20f04c0c5da202400e26a40c3e248041c8400e6251544d212000400f040251503c2c4090068a03880340c0070308030850703000c1030351204205481c11170070141b0b401424210480034000c50a0703614001d001d500051081002c0003003a00c4808031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 620748453 1250 620747203 620747209
    0x12603041203081911120a0608030c0d1803020a0b160818270c16060903030b100c1707060f0504050f0708070e01090908040f03110a050405091c0923 65
    0x1401c07207484e588091800c0d00c40c208500b042c40655142041c0030143c41610758450521000030881500480c50340c0c40042419481601c00042c0701030003a605035114542604642210310b0450654000258030402070f2409005400a440c041c1440314103141010541c0541ca0322509181d5012116442d6012140d00c0781c2140760074205020300b42560b03808001b6100911180b60300d85400d001400c0800d401c540007419280145c1c092084000305500010204400081460702800410100d2403282c0100300115501c40c04900451140c8845500420241580742065032202d00a41c0200c03011144aa5203521102401c14a4400c443c0f01d140b2500c020000c01c56040d40b004e01d07290303807036210501a03440103c0c240000c0d01c003110140c0c11111000c00128040d5020310307000f10b05001d1904075003840701007414000f00b401611103085501c0301096589400d00c07030b00c80c0d06100c01c2d50360881c0e20780d00b030360720030341a05085072104801c4212400541c9400400c50340c0380c0a1502496039144c010486229400040340058a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 620749703 1250 620748453 620748481
    0x70812150a0501051602040c030b1302040311030f0c0409082502120c0f09090c0306070201140114060304260d02032203092c0108010e010b0901260304120308 69
    0xb42400c0ca64102656900310350034100100b940207000f580c0fa801e0130f8880e0b500941206e15010001006881c0896102000b48000d4000c0d1105443c1340380300a44820403070a01040b8224030705451000781030720941c15018400540305100003100d451000b00310900312000504544108040000c80309401101180100102400b0100114a0382d408c80c0380078142503034507010700c802c1040f810340d00710000e5514800541c0c10620b14040c4103415001d207000304400c503903040d80554400d11142400351038a0340ca40011085845913074003200d4001c4020400706000c20b2052040d00041070381603040c01d00000c08040280c032aa003204031303501c002580210074010084006010340804030046a00c62103184803544000703025102e1441a10700c83d0583c45544090481a255600800c04507407107a6001c030b5941d82001c900800c02e40355215025403030041c40703100914010b0440ca040b10a20b0801f2680fa100351240304a01751002d0304203d14074070040000140c141520000110041e000b0b03101c0d400740d0702e040840c2407004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 620750953 1250 620749703 620749709
    0x102070507050a0b040909050f01020c160b07030f081321031103100b0a050f0423010903080a0f02030d0903020a022803030f020a051c0215010b030408070812150a 71
    0x60f00f64800b0901c00c1d00070300e1081ea0202c883d034503000f007204c200b981411420b0030240514400503500000d01d0740c054480c0001c010101c03080d1007409901e2a6030341d100c07612a034003400e44010000b03035110304c2c00d44109100700540303900020030303400c0000701401a07540c2c44920070302110750741c03140d04c03105200c0c400300d03074061140c544604078030407802e80746160000c4c1041c1c0103012070217803284101d00841d03109900c52050302640c410114210841e0740d2141c85070480804102c0154100d1107880450061400c80d5208031026405c0700e038000e11590030105c10a0042d140c00140240c25411403006001e6051f6a058501034103100714000d07009402140e00d2030040c07040303250450600031030749c00034074100400011690b0002c00c120ba80610b46001c2e01501c11038200d0070a800041d02502520900c184480c002e5503008448001403401d40032540f8a20001c01c1c600c80d402070911070000c90030f80505c001400b0070402402000d0041c4074589040c41c00f900c402101c0c40014050f5001c12481400201c04461403d04004071030103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 620752203 1250 620750953 620750959
    0xd020f0c030c060304170301030605010f05011e0e01121a0316080c1c05010c020f010c0c0b0f090a080d0f0f1a131b0309260d020307120c02010207050705 67
    0x1240e0300c00404250b0b10801030750610b000f034100000003800d10070305286000c10400f0070000159a0b581d80e08141004e40002e0042d01c3e41081d80da01c00103243d6001e400c101c910510082c0d2030b12801c007a8298240c510140405900741800241904200f02001324400c601e0314090b001200020140e200d000d042c80c00d0449191540d0030741d9a0b00003404821000140008085001ca032232600344402d8202a980495071400010915801c0481071500517402203011501505103000810605100201c100d5035010103030000780c10000d40304089851040c44525055110319254200c45000c4a1a61100c00ba98090020320183c60303a240720782282e02040b030044811140c010303c0d00384020f13a40d280ca10000f030080034204510541c10038070b1103181c0c0c01058003c558100c02103070710003a250700107843c050301070070892200b111400101c3c940920300780030481141040160020803070782442c0d600c50303948000307600150880c01402040b180e120035a1195020f020b800503150741c0050b031550030a10b005841c0030b1440d049544 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 620753453 1250 620752203 620752213
    0x70b06030c03101505060a030903120203060f06090612240a1a070317010f0302011b05190312090c030b09010506130f0204030c06031b050a082e080d020f 67
    0x5564000a42d2010311025280c0020342c4d0054004034000b010302544455040000400e1090a8035017541c05030110502070344843d82c0762502034444000b24401140d007998485400c2a991005042c40c401510441c0c5000d407030f4500e411007640131007622941c11203182041e40301c800c0c1c0e50400c815481d15030504c64282540c2040a0f9800c100c1c0200000c00444061070018401051150505100d00a0510a5001e001c04400c0c0c0c0c0d43c5a0010240d01805030000b139012402d40740d0700c03007641f04c1d40402c5164003503003000241c00302103203d011041147c960200c0690030040843c1007010031011600c203040300f444c801c0c1c49c0550101e2071441c160395a0000101041d01592500c001c02107562948480340440c0400b95400058050020301c40030000c3c003980c1c0020300501400c04012641350b4141c1e221584088000300380d00110760070540c040396170f4481c100710000003803240720100350700c0f14807603212403c01c40e0410403901034600c0000500c42d8502055008012990103490303d64078a540500508465804007400f0380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 620754703 1250 620753453 620753473
    0xe090c030f0a0b0a0903120509010605031b10270f0608060123030901060317180303070c0605070c0302091f1a03061905060703020307031206051c02040f0e03070b0603 73
    0xb01203110f00030601d921017500d4035114800c140c032500d107045030801c400008019074100108404d0080209000c0e0b135029109803084030340300031130184070a07164410081c550b02c1248000101292010344206141d041083d0b11407503440e901081c0142e910141110141a0a400e0f2800c40300500c1d4220241034181800320340c00e44034480e406925008000c51461042d0540d80341c907a61600f9004120036031000d800740c00056551ba4001d8440700044c20070003c915000702100030300300d04054503880303200d07002440600e64280422107240502c5c0a0801e46000380c81c50342803a90341c4c0c0c010504419040b00c1c215049800c13501050011407051a5541c080d005c4d00080d021310b104113104180c4584005004248248540ca294403004070204025a01402001d016240c0754419813030042e56079000801c2c110302160003800f41c0740301800306206440444000500c400c1000305c002e48014044e2801c1c00d400e1760402c0e1229000c0c07040700742034010b06070b80c207440b00c0081d82d403020241001024100d0180c0001d10031b0708407810314 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 620755953 1250 620754703 620754713
    0x311040e040f02010e0d03030902091602060712090605090a230c0609030f160e09150105100306050405010b0913181b08060c120f01080712020301060e090c030f0a 71
    0x3460740142e1180e481c00031541c243c00141c540001580405602001c50012001010b5141c0c2101044910968250350b0f0754131403286074825164014000001a8072060002ea0094802d2401601c030110b0f40f0070000c0c0c80d2056490b01800c1c0c0d00c08607000a1954003c0041c041040008040846400550b800441c0000c80144201c0d8681c20454950f030f215103070206480446507000d100c044120ba08136412100a845a800103030005080d5110700b5150803000030000d10074034000b1900366040081000c55160680c00e000030010900361016100d41016030f1a0740110301c0f520340e445100c2c003a040d541310064403044802d00300410418141c410240381d07402c00c00c07044c5030140b8444c403600c00300b980105606190910700480d40da2411741680031010600c00c000a00a55003250801810a030301000c00d50480307a41c441c0c043e01080c000178401c03812168400304c070410880c40d0b000981025584005c001180007a51a540c01c8c40d00407007942c1000054004142444640c9803c218402000482c04090600385902e0340321 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 620757203 1250 620755953 620755979
    0xc1e190c12050702060c030d06051e21150106020106080f01090b01050609060d0906020d0c020604030f030c090506040f21031706060d0e010c020106050303041212030e0307080a031104 80
    0x40c0d10103201000c20f52904656441d02070790070201110085903104c2c00b00ba816080a042c6506c1414012004210030804001c00c0c404410310800f001b91480203e859991a044080d40540e405103159003c2c044244060800350401d56000784226400400c20508040c1910b040082d0b2840c2c0c509541c0c50b100080e000650091030060446070b0849d80e140e291180d80c00420300074440c440d40c0034905480d042c1c00300d0400c41c00342d001d0011701c042801c00b040340001d10501a60740c1e03002620b000d000710340c0010160120511a410059604038586000300b151a590b0000c100b85800c00e0700100320352429982c1c180310b0305021040d04c800f44010a00392000010564034042d0003460f21021703c44149241600182030780d00da440496002090702402004540d0503080324600030102d40040304015401c00c9030000701850004150360549401103480c2044143c26950210380b030f400c100f511014141c6603403002e0800102440940326440c0201a0150b440c00300110050460305114030b400c00319101484240b03d69041d0f090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 620758453 1250 620757203 620757233
    0xc0c060f070f031a0f1c0b0712060b0d09020a150806150a08180c06030c03041725020301090b04081305100504171e150901020306090f0c1e190c 63
    0x203041708101603ca00403440074040990840c00c01443ca42101007084504407800344103401d951340d0654101200349001d42a10440d104081844400b48180b404c80707003c9910980030b035031000305000c0d810f80d550702007900000d040398809404100d810042289908000c040711042e1040366480c680761004205000e07110103000b4000c031003c001211342000201000300702e4001030400040c4856228909461400350682c4100c804403100c0145e100c0008200c00040d050756600c1171841c0c40c400134001c005a201c12890b4000368240c5e419900d52144a0204e010380d030b8103d00940c050b842c21644c5a0049103119548203242c0d21443c01a00c00200351900683c1c082d09540a998200103ca036252000c0345505241c04d040c101e03031780c40c64004aa0400d040b00000a0540140a0340c88944100c03a5510b40586080380412030345aa0400c1f4000c00040d0390a8140e10758550261158861504008502b03010200d003602004002d07000c0c100010b11000c0c041e850b440c10f08010101841d0480c02641c00b90350382a00d0203650300c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 620759703 1250 620758453 620758459
    0xb01080c0d020708121906030503031f0f0608060909190803092104050f04110403060e0708010e031213030f0311041701021306080405030702090c0c060f070f031a 71
    0x104555481921a03011100c1403a00807600c55105c55001e1031105e0780d0390081e5103c0140d122100c8072400452906d020380c0c81102d401c13402460440da2480e9410300d03100c000740d040c594551002d40002c10b44081000d4000040c040e6030baa91401403510300c0c148425408098461510741d03022810b10b810342c185600041c036020340d00c44020758480c0ca4000c58180b07032008003000403881e14604607004401c075000c0e0b00504120f0f03000326100100084140c00b4071084130107280048010070410030051010031195000300764a030b0000011034410b1a82c81010360700719003000054903070070b4000040c00c1c007200c11012100c03904601c02008203070712401103503405031046040d5103600003450340b180072086040480304c00b510014050185019080010706401d94000c0d4003e500101000c92480c2c1d01280c014406c42d445445130703038098004c5240403441c0d000c02c041e0100041c00c5c0c0e00302c440108403409a4220034020b45014440c00c0c4001d80c66070414078006000407140441e4101010724100803441e1240c50600d640c90041015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 620760953 1250 620759703 620759707
    0x231306090303060909050c0a17060105061308061005030c01140a0315050d03081605070f0f0204020d0908340b09030903070b0a02120a080601030b22140a0b01080c 71
    0xe803030240c0c09007019600c0303c0182ea107400d180c0414000007103402060201c04543c600316030707500c500240340d9424035400301c1e8000343c5c4100b00600040c1008801400309050050f80c051982d5070f14042130b4681841150b46008205081d0010070440c10200304100782c200003402d000c109081c1e40a0382650300d010b05000c1108040e118540701c4d8490980c41440000f03060082d00503400143d05081c040c04c59281654229841d0140c04101d035213680c07190064480f4283d00400200f0040441e8030740e80c00e040703070b0782e1030581e4490740c02c00038044000b44520801609134400d01070030f51500748130441c6401e004800840d200040400321400c0312202c3d95150500180c6501c10754800141c0c40d0019010303d075004406949826100e48600410007040180c003520403247c00d5070881f05800b03100d140c0030f840380c0507110f4050b0100300401c0220f0117a40c000d81205982c4040030300404804401402007007110b440407042c8180060b0341d00300c810051415424007540c480b010031001c2c0006104240001d200318401010504e51000c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 620762203 1250 620760953 620760971
    0x109140103020315151b16050d1401020703200105072f030a11070b0a081803090a2705040203030a110f0a05010c091e05040b01110709231306 62
    0x10301c00c800c01c00007002030005c0d0855510340707940b50304652000e445d660701a554840d000894020000e01403008041c0400b04813091450a014801712101f41c00c07046400c0700c00032420350109a002d1020b4050203010b569488a2203c003030640110300346003250943d0190341084100030b130258000303121490030000f00c615210000d1440898414024620140f5407a90100189035102030b80c0c800920b200c0038002ea41903a1500c0d90300c40c00e00c50b030380c41920840800305103244000362042441e0100140c0f488600003c0e00d1411000c5d40001d4100c12094001d1481c141c4041101145020341140c03003c80580c0801003000941080d4000076502e0140b034003040c0400c0107000140c1c001890501c22401020750040890b0700101a27803500c42d01030320900510600250650030009000410b01c0d0a1200303003000004c0d840d4802d0700b003800780006049022081410300c041503481441e2140e0400c217005c0148603012001035480d80010790103040380188007001c0d00700003540f4207115041082d9141c5a1710309a0080c0c0000320060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 620763453 1250 620762203 620762221
    0x114090d0203070b09030708060f04020f0a03050307060c0305070c150b1c05070515030601120e0304050d0c080601060f051210120b04020111010630060e070f0501091401030203 77
    0x10003418000e4141c0111180000c9a0142c031014002e000811070548a019455039609582c0f40012558a45441d5001010034054144148041c414403c050708140c4095100c0d03c4031491540804412106035550b489816031291b0300d4801c254010011f0700c1c058140d0009a104c4070700c802c5805c0b2180030100e5a400b10100d60f507031640c0038900c0c5102c01c0b001d6042c88500605010f519a262482818005e82003580a0480070701e24004503072040078142c44070b2144480000800c4020a69400c00340700610080001248643d034410a00c00c18a101d00344d0b110741107007040d004505004069200009018503200400081c1c2d4000302074900490329440201880c1d515901003100300b04056224202c0840d41400400038404a8401103104600070388a9203401c98400d481c581c201c402500c101c900d1004103080014004601e40ea00c0440700307441014182030048141c5900701203656030350711071030154044401001000c0c8011880c80c010002420720b401d060785480a00c1e2001340a24006c2c0741003560000000b65018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620764703 1250 620763453 620763469
    0x41802010521010b13080102071a06040b040509010906180222150b0723060c09030102070b1609060201020a0f050307032d0b0607080a030b03240a0e0c011409 69
    0x803002c040c0706500c03541d40700d5000710154040341e410704403c007200801003076003d414000c61381c4c000d034080114403000c005880d2031407003400c010300041d500c1a2540c8468a495941d0301031786006181c00800000c81c0b80b500d00e230040c00c944c40c01c0700c4a200f44609a46410150303540510f4401c101805000101c02c00018280100c0105901c1080f2a202100010302107801e010140140801510404a1014a403010390740b0101415002c07508654961120f00081c003c03d4818001e0301300700d000600003605020155441040b40c0c00e0480341003000c103c8689403c80925030000d00b66000345644e0000314900110003000802c4826019541014080b0000109004610a500480d821031014a4880d6030441324410f21900301a200140b035880d500f0030358490601e1500800300c03224560302000141c645540b045054000e00740021000b076150003904840281c080500d0703081c4444840711a84070581e8900800600112000da028025055100c2c90980b50750343d80181d01d050078111301010300e6403a800703002c000a4080c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 620765953 1250 620764703 620764747
    0x150306190b03091b0105130303050d09020406170d0c0b040221010207031d0406060203030604090606031403030106030f14060d1b080f0d0804030f051806040308180418020105 76
    0x3000000104041e465010a013480c0340c01e810380d51204803020f92001101c0b02c0c058821f43c1030002d004520b04100281c0900010104102c0101000c54000d501e500060110340040e40019103541008c8605800404103111060810f55241410b117100d08c41610342182040e00184020b00170110500d45407040c03c071011605c40c400c050b620081d9500c0b5210b140051804080d41d45070407200c001900070103007500c0c003402000c1c10f98036103900840c11990740d078003004040c20444d20180c445941c2d1350004800f103503984068200b0850790a0055550b545403100c01421944014681d5107514903105901c061500c0507102c013600034100326a09600080ca50801064030b074142010340060004042c800104840d020a80010522840b0161a022210468140c0f9040300c11100180008c42007945c01c0c14040c0aa0050807441c03400081d07170003520310305401243c0c03254803d40040d958280082121540003840d43d00000d1100f00c107803000c0c0144190302182589c1c07031400c07090080c1030000c013146500444113080c07011042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 620767203 1250 620765953 620765969
    0x70c03121e0c020405250516080a110c0d0c06030921031a040e070b0f0c07060806040e01151403012301050307140901051002150c130515030619 63
    0x320399201d02038034440401e4000c03400307a81080b00050203030701d450581c00032001d0b00801c2c0c111a002d510208444a0b0f006121100c041d40800f0b0407407012400200203050300000319107408108800140030716140200c581a5248200c42c61244c5030009144155010211380c16410081000c40316850048501c014076210fa4602192084481d2490f070b5045d0042d002c505542080039210b00b0254042c40140c031107400d5060061f500104003042294801c800400c41c5d009a00305440c00c21203505503541c1004960b5000100058103d820300996141500c245031600c1c0b10000200010708407648000b10241540c49500701c02e0001c5094403e850301c0a40180c2c841a00c0342c03444c4040c11581c1a61001210820300984d03000b4440c00101150103804c040705d8622800c3c00901c4850340d603180004103c0307415480c401407801c6000da07a0540d62104030740550701d401445030510301511a24038a440b44900c0c513581d4800c2c0e1241c006640303004449540d00b0105d83d00034900792041c1801016001c02440072280c25480822 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 620768453 1250 620767203 620767247
    0x91509042a0309050319020f0d020d0e01020f060a050c0408100f0c050313080a110105090106032006031b07050601060c050105070804020f090702070f14040b01020102070c0312 77
    0x20503031044041036503030741407090001d25900200030080b811100c200c24004d00d9680100001801c400c42025038030707070318041441262400200000c41c6030601d81d0b80504540540d01c410310300342c0500c0d080703c80103480560030b10050458600a0203c290f90741e42c0540000d909540e11008120580090021100548001c1080741e03c404c00860610004000e052580c0d92028a419501440141f044081300d0240d282d0424858907030b0783c103031a1101c0643c414000b007400c0c03040c0301021250720711080c02810b1203406401c00000e9514910306004144800300389a540c002940350100f2501c0340d403283d0540f50007005200d15880102c0344894800d59500c504880a041e40c800c0b00e00006d050b581c894a6481110310401c02070109890704841960031880a0303c000358040c0f48803880c0361090900302e0340aa031200d8288105c0e09455540d900c4080315058032b4201c4e030f0b031880c2d1110144215041c1401549034201d001c0c8000c42c9410240d45940ca1425480c1c04010403044004101e180404e00ca03400d80c42290710700b000c0b100c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 620769703 1250 620768453 620768471
    0x10030e160602031201090e060103030e060d0608010b0a060503091e010902090115110313031103070510050703110705090c0d110d0b1206010b09010c1a130b0108010209030309150904 79
    0xa9503e800100e13500700750f400d510340003248042841c040e400402400400801181e401c5641c2a00c0803000004401c3e0046428011700b1804017403409000010301a003000041e031244013005000c60383d4003c0c0c00401c14403004005000c01d5040006211140b41640e40d100d1028907401c01a4070302403d00c1c1c20b00a075201c40100004240300046090300c50700340d9007689510400304000c000090f26170040030300854200282e048100042013621000c0303a419039009081d00c11458507440000c4c5000c03101c0e02c0c2e0400044001c2019010950044440117140b01640c0061016174504000181400c600070030705242044003080d4528044095000b00c44840c603c1140c550300d40d541c900c080d81c02041c005c2c907124895841030421100c0902d0214140e8140d802c44000540341602600041d2800104213404850b440d00440c0407500401c0100e40e80c0e4080e09800500396181e4200b810320b41c82c940d03010303084240203034810045e04080d41d50000c120b40960704240d030030a451543c00300056016000760313404280c0144c140800c035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 620770953 1250 620769703 620769707
    0x11090d0303020a1218060908090d111c022b0c06080601091401080c0913020c010509010605011119111309061802010c0f08090d1406060f10030e1606 65
    0x20300702480340340d5641032400311440c4c90703c01070340c02d107038900c0c03841109509604e03010400ca90003030f604050089001c186803400c404042039003c0c54540301580c02440c5100503840d20302d0080d402d100b4504070181d001c2003035207850f0002544040341001e003091000c81c180500c2642c0709001d0300c2c8a400c5404c038004c841c0b12a5142d60107040c5800441340d140c00605c00c0000400d161003001c02001103076806a541011a94610b00c8080d11948400605540304a5043d000548940d050004014512590001080301d0800819175400e41d043c0e45c002505100740e4000810700044002071150070810754401c100124a82402d00d06040402400d40b1030300f10b10341d0403030b012070151150800d09184e48100c40800282c04d00410308081400b9010009002030210790f10031001c00c00000c0203100182c042c1d002186010380c81400a94032941d01307001203803905204442103500a00034400039a0080d002da41443e01250300000090400f051150000c040c16500e00c06420100c0f8100021a04424412480c4034510b860f40c0c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 620772203 1250 620770953 620770957
    0x130e0a0b0604120b0f010308090d0305090406090b0f030f12160204180309060503010501020c0d05030c1504060b061204020904170a020304140a0f1208071a04051c0504060311090d030302 81
    0xb003904c030a81c0c003201007032410b80c02c2c6207030604981e005000c0c1030420716054104000f1240903402034003085024014880259070300d00c116801003450355000030761002a54144440030380994440703840798004100d020304009010a0344010800d012040d07075910340c00b180000799500d102000181d000741c9406441c040d80c58006002c0300019020340c603951020b5540d0358003126148400d000365070058121344d114401a0a28407030b8105054071034410369017400c110740c0001d407801111401e85001030304c52000b840180800c5110320100c900042c0c51080c80d20302e00d00990050310001900007401910341100103820b01440030881341d02071a00140c407542d1740011001c003e641e83c110f03004800c00c1d00c2082141c0700e9103184c002060b02c21034194030303403070401a494411a2601d00121900640345000c0c10402400019a1400c3c0301d001052a188443d0403401d150801514000d15902c2d12908506180c000120f000e07081400c1e9000c68015140104421110350003407585802403515082e002001c1c80e00d40c90400d605600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 620773453 1250 620772203 620772239
    0x504120822031b03020f100309051203060a090603020607080309100c03020c0c01030501080616090e160311030f0f07020a02031515060a05071209050607050d02010f02130e0a0b0604 79
    0x1400b1000d4034141c004010f190b46041c070000354802000a0720384242d0a00a10b05850140141000584100c13103489050411040718004400c0d014000100803061030101880e0010302031900c01045620300310350128030390740300300300c006011070501000244a25400704520113004008500a22030000b141d4000340194110282400d280e000c6c0ca0815134803544684076481c100c85148008002548410800044031007407608042e0400845d158041aa1541d100c4041e001d094030800d004010368010300001d085549019842c60000d4040046c040411009152141c0200f0030070000c48030703070311000c0c016440d0038039006000b501402503640c13000089442d01442c81c03107a04109090710408410900300001482684a003c0200b07030306014006c0400c50410740498289481d0800b26802600c0e4070004100b900080c0044400e54000030440f01220350a019050101d03008480560401e4402d00a5034240c682c2d5000304503800c0e038600d0020340c100505802500c0c80036000780c0305a5407130741c4030480690129400d203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 620774703 1250 620773453 620773463
    0xf24030307030c060513080d0f150f0501020d051612121401050f1807080702010b0a0909140111090913061b02070b030c040303080414100e120703050412082203 70
    0x10004e001c1b40140040d00c0582e60740090803506d820715280c0c84000170300d05102d0004000d56036030b01040d0559924890f00c4050310140407141c24140c5450002450508500d80a10030000705200703c404000302401030f0010f040d4024405003d51040a10803102884100c0111185909042000040d05081d10145050f07c50070346940314400b4400c8140f03c0c48904c40900c0006800e2600005002c19201d071400c0303900711449100219454102c280040c0300181940c0002010a6032450004d04100c0700d04503c1c0e5007600e03500002e0100398a5498030f4143c5001d101c0f08140a401010005180820310b5580a02e4055102c242006182e90144a004400d10340001d81c0c00940b085010114032480e081c81942d104820402d1100d28241c02d5039003c444d29040504200c610000c1c03007400860072442446528512408120005141c4a0360301c08203180c442492440519141c1c1003054201003a4003900721030586803120707009901d02c0c9481c0b410072524410390080882050710407500b24080408500981d0440e8054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 620775953 1250 620774703 620774711
    0x20603060d1b06180503060612010b060f0307020c01030b010e060c10020408161208030411030309100302130f12030806010c0501090b061509131109130b1203030f24030307030c06 78
    0x4102804544c6072140a016419480100090800d18101e40e420070140c17500700011807a04060400714210350032041d1240e030801d401004000b40385904001070000c02c8002d10f0244880d81c552000640004032440005015600c002403481041d54100714628021100b94001c650791690384030207039102c00070b518407203d0400f4100000502c03207102d20a204580d9400c4600c2901d940c4032543da4400004107645032580600003031120604035598400d02ca007600f4125200966201c6426810703030b00da04083e8000417400b800c041818440003207521f1029010b81d92600304054152101c60050300e48001e00c2e44000c00542c2440c1c0c0080412000c41000c40c0150310070344400208414003c9440103502490350400c0d04109485109560380550790415070300b11501c00d0200d0319250641c3e0102c1e91400b0752905848500762a80e0300c0089a003040c01d100309101500303c1c041d50460811941e010300c80c9601402d203402c12020240c0019600ea0101070600c104100101280e03500c444502d80500515014003040e6082450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 620777203 1250 620775953 620775977
    0xf0711210405012d05070c05090f0a0b121c020a151e0501080a030e0a0504060e01050901060f050d1119111011040302010c0c030206030903071b12020603060d1b06 71
    0x21144d845031141d076011040d020548240842205c0d2030704201c0302542c0101340208006010b446040ca02800b83d41c40c14070503100c900e4001c0b41c240940711000d48a60154100811704c03d003200307010880098041c1980000c40941c0d20200c41203281000b6010058880713181a4000c5d02405807503480803c42d14404d008949844106280320001c0761005d124548070303038000403041c1000030f2141038031031480c0b2802000c0d804115180e00221b802c48461345c004080a1801100511441c9440150340d401072074645000d071000807d14200402500880c501d00f844d040c1c07504481c8280c11454810341d091142740704d42c0e02030003031580c04c001403070a4841c0f00030034104d010345406200340400300e01030103c02c559166030325407819141d80e00440310100c07031050a503140e04920310080f005994440055008103403000003140c40f2039075402c0c10283c440c603041d882c1da8904c1054401700800710040f0b507a14110703501180c10715100d54558000c200413200d09100200841c600b901140b002c00d101c100b0200a07104999260020181 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 620778453 1250 620777203 620777237
    0xf06021f0b0a06080a111b06130314070303140703090209060d12121107050705010216050901030602160b010303110f010920011e03050f0f0f071121040501 68
    0x1292007489030050302c80303001030099500559480c0d030820000180000c03a40340d00d13009410240c0150b40f0b801e160b1886a003201d09101c1040000c0d5411403071074984000141401d98003e170103201c1130043c50041030404034902d800e240c001d03407081d00c0801e4920407441700c0b850178180003401041c162208070711486050000c9051802c20280e040c0740039510481c00305100c403800c20259009514500d124440a8845610b050321040c00c80140200340e10a07401842d0042c2444006820b0841805108050718801c0d40204600d548a113030540c11130340c01c07410059441c41040c09444255152070005003580c54032000000806520400220381004010142c901c900107038901c40c1d0981e01030000180039103402006c0100c0405000c4506196031505040c1505008180340000c41c206101006d80c1c1302207691002001440d00d08510810741c003407500700482c00350346000003a0103983c080103806a0300700810840029003041d81005070050003c0c04405070795081c2c501c41c4504460385c4c00750281e00d00064112103c800104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 620779703 1250 620778453 620778461
    0x50a050a1a0a0504170d0905150106031b051e071407080118050a1e0b0f0a06060f1b08040504020d06031e0f0f02030106170a1a090c0d08040f06021f 65
    0x1640450f0b0b005c9100026030300c61605800021069400f03e0341c030f80c1303c034001420412020100c0825034001c04501c1d03141c000003030100c030700822012160500841d8086005030303001003290800d00c01d140d13070840d2184440282d41c005025a040040c050080c42d41d8900000000191500464241780001e2080d810000b080903000c1c0385410009019620151240f00001c200301080803d03802444e808050150107902d0360f815409094588040f2040300380f080c450b400d0704902440010f80468100050035101c045001000e1490b0150103103420071044207102c042048040c1100e00800c002441507448404401c8036600038201840704556811414000342050090a868486020342000e21480c02c000f0361b444e40b41e050303004290103da16558401b0003041030400b00c0c1c1c4600920304281d00030400031031035150134180c13001401d0300f0100d40700c0e8070401c000740c401c00065441070221003a00d490040629520300300205001342d80000c1c0c15180309041c08a64598002041c455a840c004a11240d603a511090380c0704917 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 620780953 1250 620779703 620779711
    0x270307050106350309090c0a02010507050f12060d060f0b092a0313080307030b011b23010f0204092301080d0c08070203060115110114040f050a050a1a0a05 68
    0x20407007400640d001d0f420060f100d030708044500019685015107400c006000030f40c0c00c417846045040c01185150481e9030905c43c45520403982d0130050720746400341c52213a420380140c1d25400d040071414000a149501e85000b08240a135210320144a0304180240280140110b140b019014050000011328074040e022015140041030440c1d062060348240100911580005d08100d001c1251003004000100d45c07070b00851051050b030b6030009442c00c01d20001080000d4501c01c4c00d160340904004440861a0078281c118145998a541c84d1820984040c544c00342100c407035040701032403010030300064145858101d0407032148a0a40c081c0a002c10031000080c0d018203002c0d400b0164007101f000e0142c54040c554200b02e1501030301e01103050103000d60000340b8181d0241c000d184000d0b924400c10002c90303003180107a44403043d541e0090040510801e06820400340040004d0403407003000c86641d0902c54140203d03000c040e044000d42e900c000c00740c100300c46c04040c04042405084400d10000c0c007011800d109007802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 620782203 1250 620780953 620780999
    0x90b040c062d0e06250201090b091e01140301091b020a0807020112090b04031205070509220212070e100504030b18122703070b0403030503270307050106 67
    0x2d074119404100c5422442c1603072150000420041c2038090341c095424544070620940f0250514000c0d4400182810220f510400805405001c0c6099a584050840c3c18407081d180c000760034404a00c0c0100c843c038282013101d04e5240d02c000b00208100b841a0049905101a1010745500d604488070480c0c1c0c0781591000504010070500c04000150320a42055a00c5019072102080c0d0000230f44a00340c0c2c100040e10700314041a5402d004603d01d020b18011250303c0a054180242007801d0800400c0d03181c0d520903015406a900703210b98005030241941031b107100b0040300c50311170031900e0a44400b4080103076903000c4c1442500305100d0301041a00c00c0d001c0302c0550340d00c607281d200c503500c0340000d034440b0400014080702d07603000d00401c40310b031010140c016021540c25007e03100611010840c0140010001c0200c2034042d4120300d609000240c14442180c00301e0394145440e580e65a40e210a414140207895035214140050b280c0503485640c0000107000c150340032702c00030056103554886c072541c80280300d05001c1c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 620783453 1250 620782203 620782277
    0x1e0f0f03040e1603110d0c02010c0503010f0b030604090618050c030631020306071d040b0d0206071a15010f1701140f04050c040f06020c060904090303090b040c06 71
    0x2100c00740100c10360740c8070065050104040b140d0345006250703034221b81d0282d042190307101d82d100c081c0d03542401500252650b5082551955041000e6014085600c0c040c00b80b0242002011880c10348135948500318032a08100200121011a141c6190700c65041c0070503200c0340324281540d049d5250120b40503000c0e44051848002c0080e40c400208200d008031607400104001c003e16410140e1402d100461144640d503603a081d80c860300b9a0980104050000040e02651410643c04640e4640720341d10008180c04030f4906032030f4a09450040318808038210203e12042900040c80136003000c00c20302400707a80c42602c2e0807418000c03101049030440c88503e000d50004000000401c801c0710b1188015610481c00362040c105841c002d80070800741c0d4010303580600050300001d01001490140350002010f820f0b207101400849614900017882d5000e003414041c401c0c1d50365003001c406c160103a4440e042d0941c0c00b041014540c5001d003420307802c001c0c9601c6840081780300501a01d072091041500308100d04c440800e040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 620784703 1250 620783453 620783461
    0x13110301030b1f03060b03010e011a01140c0106240201020705070b0f0f1204110a060801141210240b040b0304031704060209180106081501021e0f0f03040e 68
    0x442c2c4000a00070586601d4154106000807604905120156004150110f1403e0b103540626007180d5501e4010046645450290000000e4401e401402c141c03003440e003410100c140401245003071007465860f05d5191320380003001464014001c0d003401f0750181d41c586864010904041a400d0b4858020f008040e078002e00001e00001405001a100030700c0d107200c125007401c880c40c500060680c042c2048a030300c00031483c104400c2114008450014060641c1c0007480145401ea020b0701c4400c06018250641081c650000030f6030300d80c0740c041d88030b05803600e040b502c100c414254440300038030880c0c000c03009100c8110b461492010550700400110340c01405068542403a005440c41c142d04064422810084462000100e456900318114047d500446005076501c004004101c116103107082c685c1d102d101002c0042085e142c10a2900d9403040d04e565078443e0390031810004070b09203503c40185402d600042c80908007108000610302d10440440c1089400200710b00b000a03540f400f543c800e550355665014001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 620785953 1250 620784703 620784713
    0xf0d031a0d150b060a180909080d020c150103080702281a0702030d0906090e06220b031e0606030102031303050a020f2a0a08120a05070209040609021311030103 70
    0xb0956800c01c0d80d42c00550305411100144032540002e0340840014821980800301d82009a02c240040015600c1003290321020f59035034000d0f001d151404a400c541c00b00d404000c181c401d01901d4901180c1c1d400b40c084540e1285000d441c00d40240800743e0080075400046100a604107000c2c0c00307040543d034a81840640b0701012858070b02c0c00c4042000c0500710038054000161020021303500c003e9500d8640c40e6a070342c1007401c01403919010754810110454a2010311015403078049241030200700c00741001c1905019504144003810121105541500c00e0000952602142081d07c40c110292075007510440d03100e810405080c0c0c002941c2d1a07401003038800c40c01d000640107000811941c12280190307010700100d04522410201e1121180c070000c0740003095406c103074104103650004100212442d04240d402d20701480d5030b41d144600310762848000000c0410ba4103000302c05499840764020111041c0b0b01c0c1c18644603014046a04040380134404601021180000900170324801c041e80301e001900b141c0c0303540c403a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 620787203 1250 620785953 620785973
    0x10b0901050c01060902040e0a050f010311120f03030919050c040b0a0f06120e1f02030a06080102070807021203040608040213060b030a050628090c020309030f0d031a0d 74
    0x9800d040c81810001d0071030000003801854003d203842d000c0144c64030714190420400c100c004241c41e041c0351522040040300d000c40c00c00c10341500d0f006880f00048443c40d902280000c0d51445a05840f071040442c2c45010340720002c01144540348146c25038a402012031455101c00c541c42c3c0c40204203420500800c021420b2660010070341c00d20007400080525038808101081400503001800040c08001c1d8054001215025290300022a100181468092009030580f03c0000d0701d03109600c035070008003103082c014450700a080238041c42c3c00210365560061501102365440f00da0100d00441014200001d01c00d0084203543c100d070006e8490980907582c0d5801c2090101e83e84452180c41640c3d03110101d012a05500038601c100140440000c2c9400d143c410040800d42886800c40e030704241007000d1050368054070f800001c50383c01c8800864240c02c041c00030703410340c096050215010701c01c100d0f04900000001a52000b50007403130f10704004014203400c0800510780c1303012a09401c00e80d24403c0c02d00141c05d54030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 620788453 1250 620787203 620787217
    0x50a0b0c0705041112100e0c0313020d050c0a060504090501060807080403051c0504080d20120604180b010e160c0b090a1b05010905191203050708040e011503060e010b 73
    0x19607610748408480484445c1005840340c03100354446100c203204100403001602d070001041c1c002182185407031491f80d280349000f481e00034002e0310340c54225010004100b004048000c4010103c82032030ba00c560004285401c203208014005007000000910a809448128080c175032551b9500c86075075864600340c5031076010b600442c0708550900c1c00181502d61034851240140d100d100440d41e981104800c20081c0d0314441130310910002c4c038146060100304600c044400101401801300755958455000a00815940c40503108609110b1103640c10800a00f200d181a41d01d4190004000d840d0340e2070302c08054104543c814081b400422102e0042000246455800001401103d080020568030807a00e0580840301d1005c9400c414070a00042d80c0005440c4043c040907034940c0d40702c0200c42c0026144103018802d400c0360f1140c1050140900d44510211284d182c0c00a065555403980c4d003034000c640107000d204183c0c0c0c182e034003000003400c6813081c000d01049035841c9a01d2a150303420001c840f5001c4d4425a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 620789703 1250 620788453 620788481
    0xa1103042309310c0b19090e190902030f0303191e021b100f0c02061009090218070c0618030f03150f030b010801050708010b0406120b090a06050a0b0c070504 69
    0x660704000421360085540a4202c2c0f42c0542d45604290b032001c52000802e110080601c018411f040c032407400303429644c0d540090000c003200d1281e0913010201d0018405c4040c041d40501034220302e500b601000200950081e09810030315444480c1c0c0c1000c1a0480300b2003001c01d60070b003907091403020704c109044c5c000d00440440b440f180d080107140404024030709154410a848420703102d464000980a1074420f4541307071201800600100d140030358040a5010850045071841aa5481050190b40340c5c0142200702c6a00b03000b01400320708004401500340b0801d0f40c001c469050074101f145082001d500e11941056625469400307180440840070b801802d0082483c07a100b03c000c16000854040443c8650000c0d4002c0e24028a5941000d00c03080c01c2d500001c0605003800740280042104410103422203003182c0306441e10030301c2e8032001041000501040900c5a900000c0710050045200d00743c0c3c17155040700c5044807c1840640d4038019a5018003842800740103541240c038081050b0b00b0321f5000b90000600071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 620790953 1250 620789703 620789791
    0x706050f04080a03020609100b01020703080c010b06070803010905010b072118060302030a052206020a050702130c020f120423030a0302030c0f0a0b07050a1103042309 73
    0xd02400e0f031800b82044019001680440c0612a9401c028400e01040009202050041c0c00f40782c00044d5458486210052000390000b51403407488a00390302488102c2e40061450b81c0c0d605007410100b0b0180c10a0083c1e031400e1345070100001e01501540115201c6580c042e003a034001820b04000d00c9482d419612102051060725495961543e00d071642c02800740049840068a80c10150a031400702c400c010709812103824981e070081c84062030f445180c50682d03072008026a6441c403c0c00e084441e8040c60354001d401100d00c1c84100840360054100d5108428141c1c200c45040c034200b110580e650115081403101d000c0104028000307510303820703485030615616544401c80e070040000401e01d08109000213a005130404607144010210501541c52001c1051000740b200074405e44070b0b404807510117041c00c0300380080018250380c89400781c1520803481401c107007a00e40302da0ba581c1c143d06040c00c84402c0c0e07900486501004090340d00c1c040322002c1c05445860030780c130748180381d40750046c940e10080c2c1062000e80c155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 620792203 1250 620790953 620790959
    0x120b040e030f07030e0a26030d020a1d0a140d2603060108070804152c0718020313060e10020d06050a060c0b06040b0a030b0406020304230706050f04 65
    0x8100700514810341d421401d1656030741c01d41001000e400844000b180701c0e105003082000b080f84403221103244800c0400e08500c0720140c115109285206071600d0700f08541c00810360500060f08a90380c4505941003e840c08841c0d0f911508000500416005503283c1300c0f0610000205824840c8030b403202c583c405c8030700b0075000310301f441903042214022008142c210702c0041000b16a59000c000c540d0000498180040c4034140380d60380e0110300c100c21042042041d85c81c440c410780300d101070b50654060161406031441c454049821980c40e07001741d0042c85003408541001c980c00403080d1007100d01c01d40700048080c50311902c95845030098001005c000245203e2000070811007491880140802ea512241c0000d08d186010140803031190b10758000800d014410342c20b44081185069403e030f012400322800200b040d050400a4502c0c2442d400c06048a0300c0b910800c0200030403640154000c84c080d811119007004001d0708250842c1d50b141005c40642c0000408201a50041020380104c200c522142410143c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 620793453 1250 620792203 620792231
    0x1c02010902041104050a0509010b03060415031415130503120402040b091006020607030902030a0308090313260304150c02040b060a0c230a0311070306021b010e030a120b04 75
    0x480b4000c03c405150001020011880c0c45042c031402050203032000d51296151203503e164034040100000c2c0100d0b11444001395219102d1a0070b000345600c44032800850340b02801c09583c45800c91202060008800f0100c2d07201d04003a091105400c0d40324004516012a0107415001d02d2000f60080b41c2013a11134103140c0c01a59042c000c1841803c0e5101440c01203440c11b00024500341c8044e00c400181880e00840c2c40241e140401d001148070b4040c01e001e51140c503401c544615502c04d091020040e20302c00d01020564847c01c180904000701d0452011407018451482c842c1c80c0e00c41ca10990750036885820300e8803c464020031510401074001040050700b210100d0100e0303420744c009a4040300142d012568003040092030168020354480032104034070040440b60899544894800000c0c0a10144080c140e5103480704100820145038402000c0d92503038009204081071100d040303032041140d42010301a8001443c000260341f54414559100b070440a000201c0307030700401260004079081a220006004190 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 620794703 1250 620793453 620793461
    0x15080706050c060105040c080103020d020a030501020a090f1d07080901020904141f080706050c0c030a0b0f160e060a180b0921120309100e1e0f1c0201090204 69
    0x440394032003941d964004410941002c405170440b034840c2d443d00090b5080c095021880d40d0650358107a5243c00008598000102c41640760f0303000609941c000540c0c160090349c450403400c1180c02030501c66100c581c0341d0398080418034199649201107800600062501489000700c1a08610200001490032540101150983c0c184260001d02c140c00c1070240851845020340c6095460750a101c209400c0c4e081108054541c45144075890801034049441c5250070410701070f44801100007400c079025020a46010001600c04440d400d0301e14282c0e40020b24101580740c80c060421155645503980041ca44041140ea5040300c204075041210546981c40030a0840d001600500402c4a0054492960504001010710243d41c0070a4001814006d80c8a41300000785011000e20b0214041d41c03a5900c915102d450007680364802a415400c01c4403c16002c078011038800651060181e11150003441c800300596101180410078016a000d455481002101c2125085052584d4800030802e240150005001c0d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 620795953 1250 620794703 620794709
    0xf1d0c18010c151a19140a0b0c0f011d060406050c0d0504051f020412020607080f04090506010e09070f11210405040b0405090d110a080409050609060a0b0a03150807 72
    0xd03a501e071410312480e0505074000b8414801100c05001c41d450761320b070600c0401c0541c881d040041b07880314841c1b1455030700c4001d8131014088440f09907450740c84c0e04800c0d5684100c2c0519040c0700b540781a00c01c0103110348040456400280c21801401c0c183c03604d540f00d00c0184001040c0c0d1441e52000c0c040c0d908070000c5030080e14002c60089c80100300348181100c01140042001c03e1200141d031040004002c1d03441d2410103800080d0701181c005444030050308003074805110344040d81c1d000500015001c1000c0201c1d500036800340d0003e0741c070741443e407070030409010001d90180c4034500460450202841820300c0742d450103145240c6c48040c1c903800000400d22a028400c60207501040741000316050000303080a22812011000442e01840242072400c0b1040c0c48101030703500d11040080921a0030b1241d14200404810b0f15440070a841d030796603031451820010641601c0c05817250482c54049607181c0f83c028020410340d80100082c9142028110083d4004c18031002004c09500002400280d120310a01041c0e0003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 620797203 1250 620795953 620795993
    0x60e04110f010207081209270a150e150102011407090e060d0b010501080c04080a0305030a050f15010e01020c0a060c051e120c15010f1d0c18010c 64
    0x440121200708201c1e4000716503081e04540c4030420401c10244005107120080860030345d07150780c4003a42c0002c112402615030381c010301141c03901103000109105864547c800c1c0920b02c01000a407c10380000010145944200c4111580d13010101d640c140c52074510b40350303606050000040390407080010f01d6000c20300315821000f2030100d2904000c2c201580001c20b601c20411130f141c0d486100d4558950702c000006001d481d04002030b10f40002e0521514400319809881c094045800f954803503e0000c20716401146c02d8540981000c0c040303036118614003d200c0c084c030324801440e8014074124004640c186054052941144a90a007505c0c0c0c5031a008400400303081d990752440509006820041d24144050b070b01d1005503014542e01d11940c500200380d00081e520101c05d803d80d01c01401f49580d14281d811300e4000c800362100380000504c1c22081450310226110509098010f0112030850100c0c51402c46d18178091010800905007403429802e0450183e000c141800880345d10f850702c0d40c000d150300b0710b844081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 620798453 1250 620797203 620797223
    0x50904021812010618090f03080c040306060b04053606010309020a08100c05032a07201315031e050a03020a150e1c050f2206090324060e04 61
    0x821a9841d4a400060300342c17a80382400070001d19030303550307030340116190020302000240c1d004514201c00d054201c40003540c203c0000d000154480f054088a80c2c41031090910564008107401c0001c80e20b002508014428401c000e035042c2d402201000b40c00900626040c105030f6943da410bc01079a0b00d040050140006c08020310005041d9040a001c0314515041c00707003400010300400442c0700c1041c05105454076161444058404c0111080d603032030152960041010946809007055401650500600b46104032880105581d02582ca0411104001000340f040740303003450248041102c090311400409070300c1000c000000e010751541d40c01e100d604038084006030004584001841001503603c1000c490000e810002110344800555581c030f83e61490f07644080101c1c0c1d40030602400340081c6c0d001940500a01a65600350240350705c040082a40844901ca810040102c0e10303504c186590015a41d10010000568049009203c0c0342c1c60301c07540c0550290b444040102c2c03500580201640500c2c85405884 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 620799703 1250 620798453 620798459
    0xc010603060c05030606041401050d06060807090b03010b120c090a0305030d2d0504140d050c1236040903051209010c020c1912050d0f0f0509040218120106 68
    0x8070540d0707030001010003000b00034020710804d80c1e00c0300f003182c044900f10004114140c02c00401a04c040c062100c05030281d5251480019006400c40001c91045525640b81910b00d6110070782c13501540428011405419024442c46a2205003210040c0e00071086411460415020a00080c4d4803200c2da00110340c1c640000c01c3c030256006403402256104d042c0320400b00310000c03003074a500d61400c03a100e40c50210551180081014850000da03040b1640c140d10040c1d6280c4018072002402c16070100e0613503407083c42500b5910b5117261038a0150b540c0e010359034000703502d030101d20001c140c5241010303c0910345c5441d03403010b2291141e503980305214a09119441d41500c95000c04200c034080000100400800c0c0d0503c0c00d9009542e82c0410301e00080c4200300c411040005a4592003400032015801c4640c1c05c9906242c000c050110021b0240703840c00540d42d4010f50784e030010b00b04541c200c83d80400e4001080b818444d00003145095005010103600300b4010500f10240741c400500e040d81898103d40c0181d64800040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 620800953 1250 620799703 620799713
    0x4090f0503030c1306090305030a08041b0303050306030d170c0c1005090105101e03030518090f040b060d030504061202090607030306061d090c0d0e030705031801090501050d0e01060b0c010603 84
    0x10100178103445c241445118610740741c2a403240b24901003a400c00c018040003504004403400c100d007410802c40314130640561a0f140281141c0d100b07981a074171a1107600d0094900f81c2c031a04240ca0403094201c019800e0b42c941959600054114120074103103806001c47c5136100f071009228062240450000114071820610004188150b49030404002c1c108800184030521200d0840394048aa244c030b04280e03541c1081c12682c02007031441c0d01c030a41c050a200b00307002103244001c4c015801a4001c51840046898010412040401d40d20307000300801d07014003003008030380d0286004400c0c0c0320340d011740545012944000506180d02c58a81140480e5451000780329042d4841180c011a4030b0b00740b000101c04c00801c00180d55610018440840c0030300000f02c03040501c0c41c1d504030016540c0d20400300c070f0300c928a500d8215142c0d00304028204400b81c0020001c0c00a40c42102100f00b02c903c1a1a039a1504c01000c0e008000341c0350807289000e16640340c402c0001c0c0100d0700b4004240d1880c2e0705000062440c00c500e05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 620802203 1250 620800953 620800987
    0xb04120b2706071e0509091015031a03010c21021201060f081005030717070806070c0501050c09010e0f0102120d0c090f080717070b0d0906050901090b0604090f0503030c 74
    0x14040500403a04013248115088030403510841c4003101d10501668800030814000380c056002402c0101c0c010715901900c079050b0304584030080b2072111550400250005060881d05a409010000741c5590581201e42d21445c900c0d80b0f105101c0c19025151020b80c03085106100001e80c0203800050751100100001680903481582000b044991026134a2801c80005d548410a0254400c0001030b00310610100c801003025400406002056400303e29001601a00c0703181000c209071065405c000002e80c5d80300c802c1088030301c941c10503100c05070310b2980042803112510310911005d0641c0700302c00030418803030886805003411112145000c12002060b0f04024204c400c240d12a20004000010a208818011030b00105880300901c01c3c180200700032131035a00d4010b0561104100010000e40380e42c820005421400c10075005440603c9a9144d41403c1d41c202c0e112448050054094540070420034071b056008100098002c400c4000d1184440e00e41da030965105a5584c1c60200c0c0000f48034201c8068450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 620803453 1250 620802203 620802227
    0x3010303090806090c03120f07051005180a12110f0105010e0702070608010305071203021905150105030a11061b01020d06290f1308010903110105010b04120b270607 72
    0x20245c010340c0074010100c1c1c0d84401000c440710510402190b5020030f242000181c6440c160804202c55030301314420021402840195081020482141c0c815120310b0b1700003a015013116480301d031040d11102e42007011120741d81110700d4410750340203a090b1268080300901410b0b000e000c401090043c1c0d41880300d8040d2500c0c01d1903005000780b00c03e42c00100080b03080841c2e00c904480325809510320745038052030201c1c105251075941d01d001700e0321517a010b0305110000540c0d01c0103440a581c0d520180e40c030340c2c00301541c0d40034038030004202200c041c0c1c00314102e08100c0007030240e441040140c5440e1410102100e801e80e0002d8000042e0b05907204010003500c4100302255a0b5926943c00c1c0e001d600c1c01e644429496441281181d0003031680000740082c145810034403510017806080001c06c110706043c60020410018000180c4a03036081c14000300d0010700360021203040301e005180c14007244081c3d036501c010300c2c00010301d02503004000c903100d086031308010110b180014000c1d00103041d041c9040c540140840034a02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 620804703 1250 620803453 620803471
    0x3030b1c030801030b04030e0306070503060a0e01080309100203132304090b04060507020a0b090a0b100612110403060501180606170f1005040c030b01030f0e030421050303010303090806 81
    0x1584040703500082180e064035082441c0c0d02c4155117504064034160001210310b501807003460200248241e2040113540505403c0300c0d094641503444030010b2030908280202c115030b801c2007000040c0c518205048008503c0280152800c0940300580321161321007a80c0040300000f801d2181342c13110105220701c005602000c9034108100321068403400c180000092004040035603034000300d00241e008008a00183c0d901603c190880c1c5469903120341c46d052401c2044030140384460106100b2441c9045810075504540da0b812040b241c1f05a0040142c68140c48241d8210340400010011906030300946000c5c00c0403c19100303549000c501c1c000100c420544c0404100a2140c400c0e5a00161803821341e50404416134080c901a250306464001c21500c030307070001c0d9016281000f000006074241d041000390240988040003242e0030444224181d030301c15400c20020750020403060000c4240000c0b070554103c042c5015040c01003040d40c80911b550f0003a00260080b65210804104480c0300300302050f4085004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 620805953 1250 620804703 620804749
    0x30c17070e040b060913060c030209030d21090614090703050d03060b070b0a021b060618040b0414030f04060201050613020c100c0507061b1115070c020f0d03030b 71
    0x761903d01c07a405014148520940168012444003602d0b0400d007030500d500721104000400381840060021340c02000090f000b805880680c021940c020510000440800407490100b503040d40541e40040c0900c1104a4103550340d425441c9040c803401c500940308040a038010440f0310300f1030510524000310040b1020416081000030b2000c08958400d40c0c0c100303039201100b00125259406003401030b0040790904012003c40201e40c80c40719000055260140b00c066451800c00003605000751b02091040750003410f1068500f001c2800181c00710356416441180b4002d40341030404099613440d40b64030035801080140e441c0d4048c0082d600d411401243c13840d00d001011840c094a00010544a0b82c1e105000940c0315a145072805c0d141c1e001c0c2044801455001104000c088405003414507052000d00e0510001141a403014030301040010b00100f9034941002c8041a55503106d07c11500004a00340c102e8020301d4030b482110103600c030300032407842c940d2003500c02040120700710003030085950750303102410302020319 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 620807203 1250 620805953 620805961
    0x108010807080a060b0d020603040c091b080c09010c080a020706020709090f0609020a0f0909050601081906051b0301081c0e010c1e0b010e0103170909010b0a09030c17070e 75
    0x2c0028145074065100c1c1021960303100020000d40383c0c0d852820080c0d00300030000100803c00c2400d101c50070540e03034501d204001c4800541301e182e9034890f65803001400304103000f001c00d281019000103809103110514180c00340310915a1141e080303800211450b00581e103c00402d1001a0b018072164002d010880810400c00030540c17907101c0e032103001c83c00140025644100010540d114980c845000e00401403036180000d13552012000140f01d80c400940d40c1d406200000324a50002203440320410709118070740d5050404d940c65180007058042c219215807540458442d40940414015600070048400600b072241c0c40010004c041003082440c16040196483c40d403140c40e0b0f0003d000ea01c0e00b5030090034440110070f0003090413070001e044220251103024040700000c0e0707802c4000c03005d5050b603104602030356440504c2c0d4007070030090042c401080c1c0c1c00300500c4014131150a1413001340540038010302e054009a40d0b40e03110260308a10503002401800e520700d00c40c07401c00303a0030060780008000402c0e06502a1030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 620808453 1250 620807203 620807219
    0xf03040e16020a230106080105091e120304080f0403020904030c14060105060301090e0102070602040803030403120605060904090624151e030902010507050f0703030914031f020c0f0304050108010807 87
    0x4d41000d504070210342110f503040b0006025440b030005458024001c100e5810200d1a1a55900002ca4040310a000c1c800300400080c030080313040450350764600c0e81142143c65070b42d280d0400360060002c3c0305050b80b0034040040540c1d50613032464000c9010f07417140345c84d1020310b080c03000e0a01c0c02c03d40c1c0b100b0343c0c2e070042004000e10f40b0342c00126411201010000245241c3d45c8039024007a200d030400c0034243c0c03400440d02041c1e041c4080300850190307200c0e03200d214442c0f0480d050300040d41c0780751240c60342c0300700705002100302c0c1e040540100060b1845680d000a804000c1c00c4d20f42001d5590704011940c0f1a01d03071109002c0043c0d4141038400203109420901d010300a8510030f2250825041400e404040c0c44139900d03c11a4040c509465650703a0041c282e4115410456a0130b5442070309100c01e8000071b5407200005440b03001806191940000035019207a680c00440d8020000c1000c1454091607582c01c004030585000c080c07011619001c4050040c4d0f82e142c0c030301400140780b818103030822100b50b0490f130030400c140a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 620809703 1250 620808453 620808473
    0x30804030809010e1204080705100e0103091118060f150706090f12020c1003060e070e060d022701170708040807060c0206040213060f170f03040e16020a 67
    0xa60600d0103010740c0e0b440802282c09040e082c9001052803003503c1c011108008004d02031b000741d076800070840e242107980e50300700540c4a03003401c100d5000c07501d20f81c40007000b13503c641c2180107598000d10b483c051080460b0042481404c0c54003410311580c1c03000050168a150240c500000d20a08407400b412080b030714064001d540c842c194000702815030310300e00714081111900c400c3c14881c0d0488104403000c0c45c2104040d440c0c200c03c0369410f1003400132040741c0715094041c1c4550010340d1a100b03166075050750384010569051a41c402903d920810030f22400104460328002440400284c68a401a2085036803003110b401d0030903100306050100c086800c1404950860380c007603101410b803500f002252620f0814003a10301c00c00c40050022400c140d0b0003c8520740000b2041e010307900c2a208400e242007641110340407a0050301517048880d05030f080c20007000072900b11842c0203017800404d95915070180c02c2d20600e9a4000d03032020f01c0e410068000c1000c00d20644890043d411040e0010f05030116450355507202c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 620810953 1250 620809703 620809711
    0x206061c050a0203010510090b0603010f2d060e0405011d13081314130e07052404030606060809030403080405090a020904090813060912170f0a080615070308 69
    0x30400109000910004001038402079401030000c212506000300035003100b82060003001c5003141030030a0749002c0d003810011607040b0382e050a030a910060600507414041144041000c40c4202070f000d1030003040010300c0c0f04400038040d40d1510850b881c180c000340b0080e5401603112800c25080040040c400d501015411a4070040030090182c1c40d402c60700c0c2500d032600a170503620702c0b142c0040c6008a40c01e104a412071881c40001c80c1e03c004c03000f01a00340007003618011341200d0215009484104418104003203401686040c801703801c003078204070044095050b0410782c4180c40b6aa242c5004000142c2c004d461140c1182c51070010790b2805066840e020028421480348078010141e01c0000b4980300048ea05440825030300800510010380582810b01c015008620b40faa90700d0001c4000044590094400c603084450f405201e4030300c14400e071203006a00f82094240149000c04020360600d01803103600402c802240380c2c1b2504800d0a0050030b203c1e0418000408000c6044100540c40210750840d08050b48 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 620812203 1250 620810953 620810989
    0x5030d030e19080301060908060603152a0904060602030406050301030f110603150f010e0a0b0d020c1f0f0207050309090a0204050d06021c14040f06060b0406050c010c020606 76
    0x4808500990300e00c1d040045004020980b070062140b000c00401c000114100c1d100b80c2c0d180103a841e00d4003a120303211141542d0300c542c15800040b00080c0c0441e806207095100007440c124403666443e500090702102d040d500030b00310407400025140c48500c0c2c20712640c000360103148021802c180c1441d0001c2c0c01c0b0f00c0b041c000030b401e010a8184400811809101c042e00da0310010340595100d007400751200c48962120015244582d044841441d550351141840000d00e400c01040080791a192800d044216801004242e20712a000c012207081c07140e04100032040c0c050787c11005808080c1052030802101c080d540d02007401401044081c01041001055444203001203844640540b29a402c0000901c59680311640118050b10518140005603014140240340401c00c202201c081015510481e40528500600c3c420701201140105c0d01c00c0c141081341c2c0740309240000d840c42c2c50308580511500607a2040303002401c00641d51250311000e0082e503080039458002060541480307400240b00e81c040b1912440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 620813453 1250 620812203 620812211
    0xb100617060d080a051c2c0307050f24040b010e0702160609031a040302060c0d02120c040302460b2113021e01030b0306090609100605030d03 62
    0x25901c1c80c1c0b00c10451944031040d41c1e5115070446025169410072103001040c12046080c02415911030f00034444c900260842141061b0400c02c41d0001809002012040310700c0248075100000d2000c203d0850043c6044005040700c026112000d600000701610110342ea222080038000011010005241035407100003801d1034607940c03008224607050305105441c0f81c0105224000440076044075008054a02030254140480f441c1206504192001d4400600580c08080010400301c241c4000d0500403a403288050320340302c06201c00c0c0c9d582680a0f00c1c42040104001420001c40c40c00840942810340c0003028044000b03030304000002401c00c0600407540030003040301303550f10304800300b0a0350000e02501240280c80301a4000c4401251074405080c405241280000c00c49608410700400d1205074000d00c3c0f07200b9802c19012680d10720074401e6616041c5034541116900c01d0354280300b4036124a0141004200070300d020b443e01c03071405d4101590a09468031703040e03043c401c9880100d04040d082c032407402c01003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 620814703 1250 620813453 620813461
    0x20c01030b0f0429031212040f080c06012c0105310605010906090e0a021b0619050601030c05090607050715030605011403071b02130e010204030b100617 67
    0x1c0d0503104240d60840e40145000b003402e02c0304004441600240001e284013020241080007411b90342e00941c56444071076007081c840b0145841081c0509030b40144203000d55042d80c03c1a0740e810145d90040207000700142c0200c4014031001a40c20b02c180002042071400048020030340c0748a000048060207824020600008580420750340803401110310720301a0b00c1d030f440403400d80c4040d0000300aa03000d010f0004045050000380c1a1048035544140d50035040107440302e840e400308420096000101001c0280d81c500c0d0b518030b0b8454240041489000f40750a0b40705c0e071000b6400c003a0200c5000a05080c10703d864100740c2c40e0015440b0041d03801c10103003aa422552920741c1e040c05880c00040d50700c55107031112000c200c0f52071140c0c03582022003118400e0300d131350b240d94034809001d0f4003e000807a00040054a80c01c1e15001d0541000d258202c050700150000c2141d00b001c0d10707a501a60324440030903040b03070740000d010130400c01452607155007e11030954040d42c9501349040141180c04000c002034440103414013003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 620815953 1250 620814703 620814709
    0x914040b01030b0a0330090b030709051e091b070305090301062402010c030513020616062c07051c0c0b030103030c060b01031b030e0c090907031401020901020c01030b 73
    0xa02c8203c0020015034a0b5075a0345484681c070035107451203060108035601e4040d080700e10709540c21050525500c400c10001e084c6019050380e500000d1448040050000380019207884135920f03800c041c02000d00c14402e03188541d0602154081c041e000000d420341c0381041c540c03540d0340141900d90711941481c10581c0d811140c0e0029002d854182c2000700c0414528016000c40b03e501c3d4080100103849800a02195505c0c1a094003200e208440550018900d03d15610061801000900000241c56000070020501e9210ba2003201c051442d80c0c0b141140031641c10000c80004085050b4484101008100803810940403030f100f1000c681000d0034550041075403804222035160204040d0444d02552500d80d84c0d00c0c18010856007a0f4131003a608580750071468445075200e40510083c1031400d42481c0c11043c4a008128002c10080f00c0c404420701441e001d0000c0c90350b9034102e09002e45020001804031900f035080a40d10f2040c0f0000403d00c5071b01c1046921450f9802003461052102c0900340010038001031404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 620817203 1250 620815953 620815961
    0x409060b030708060601022406010f121409071202060a0e0a0909081b0a030807111e0f0105070c0c0302042304120e0307030213020a0c150212070914040b0103 69
    0x100740e06010382d0001085646002443c42e1003204241c1c200d50300c0321904451042c1d154403a10807580e5a22507580002c046500031042c0020584413460100c42071400080c0100450350010a09000e0307a80c07010602050400c1001000061b000f5110380c620a61190b50014810348920760720107051000c40800c12890799070310b80340c8200801c1e494100f80601c4149103054643c5a010310303194400c0ea103040b07841d85900c91001a41b074010582c55151601561034450090340c1400d00c200b440320013885950f0410300c5204601c4010360190464400030320491a0f8148000e007501d0700141803408000b800c6210340d001c10301060381c50048a40580b400203501003400300482080c0502945440849160130601c401c1120b01d0300450320400f03c0e5529608443c007440201520f448482c48040e501010203800c83c1e0012085131b006108444a0f424007106032101513a0304040d40c004113094580c040c0c1d01280d64100130001003107595001d491807820604003030802c48540040f0a41001c2c45004540d40c12011480d6406588 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 620818453 1250 620817203 620817221
    0x20c04020f090f0d080c0109170906031503030d0e1c050a0210090807061a1905210a140a1101030204060c0803040203010b0603090106090e010b0d0201110309040501151d03030405040906 81
    0x2a2590303503801501c1040340139184100c4100c0e080b01049c0b100549a4600c41d00740c0d103030038000a000c2840e58454661060030540402402c80c0e050208015140c8200c0742840340758034000e80c110240c008803011403c8503154120310817001061140070400d2041150f40801c5161018441e00c4001805032030302d052000d1140035214000706103a00c0d12940e42c0c0640440201040803200031103a402c402d02400000f0501c0c0f051500c2002e40003036134640818005030031840d072800c808911008640c2955101d80b640003440b51038640b180d201d83c00c0046044284100c402c041c0003180c0c001e0806620f0546020303801000005070b054007914215010000c18110340d001e402c00544920001c02240e04c1e428016000f600030070f000d200700e546803450800951354044041c003030140d00500c0181003210000d00f40c0c0041d51031000c9100540c0482c04204a40402990344d071041070302921043c401560b0302c480109025290b550000c1c4911185120700403210302c2c4c0e035800000c03a01510320030b54003c229005180b90120207091095 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 620819703 1250 620818453 620818463
    0xb040e0c1813063902030f09030a05060103110913050a02092203030b040c021b060703171608010b0304050a061d0a080c01150f05010c03140c060601020c04020f090f0d 73
    0xa0842c590442403c084c0400c6490441000c4103403511284000c420700c0c00c1d0203038000360300140005004a62207001628203150b000d016a141004140d450300e041c003400742c00c11180344c1010b007134421450800e641050b503c541141102c45404071141c07251940c540766030760001d2203000d0350340006002d90207040711180090300c0c80c0d031250091091132501502611140754004e010b2894100f018802501c0040e070024840300401c64840c1da40c100405201c940c0e80148019000d0040040d11000580c414440c518410103440c50900c0c0c02c882c2c0f0100c000d02c40001070f4000c5403441002e0042c40b000c124081213009100b0350080e0b00141e42c461407003140c10f003e0f40d210091420350051881440a10100700001c04942c41030744020000d1320b00c4805e484805091340d0050100548503001d092105502503504054268060b09103000125000038140300c4981c4000c02c0c0c2243d503004141800f000c0e58041002000010003200c056040c601d12400101e26401040000c502c01d844243c00350300706868120421103000e801c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 620820953 1250 620819703 620819711
    0xa17120a0507091d010503060a0b010509270106030b030d05280e03120d0f050408120c04051c020f120a110d141b180c0304060f050a0b040e0c181306 65
    0x10310343d0000f24a00903c1b545010b40284c0001520b110f21070312810340c51110585503a03040001240a01c400500d01542d81807002e40900c18403160060080301c640d00030105a81c010540d900181c00f8181042a211307911b800f840b1061140c0803500f1110542c074084d0250b100202c0e034004800070f004503600340c00c044140381c0500031101c20701c070b180c24140010a03000811503c1031042000c0c208400045500807100a0041102842000c603100d840d2087c01d0b80140314280200e040913140d000241c1011116010081c42d00a03084d1100b003182040800d00304980c80c00c031507000701d041c90030300c0c40c41d1900070798040248210103150441e0030070740c4e40c41c64541c10030390800030340305448402000c0c10b0f039104008094640080c850030760341c03a894500006018810b140c25041541c6a444113603880b215504081c10440300d09444155070300c02d1344d184d4450075206255081d80030030302c0f01e400c4043c0401c03038060140110094011080f810440d480d5014021050303042840c102006589250b14446c802e10b84c410010403941c14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 620822203 1250 620820953 620820989
    0x923090307050f071a0f04050301060b0a081b0f0f040e0906010806100302010504030b0c0d0c051e040b09090408070c091505010302131a040302060c0a17120a050709 72
    0x1d0524907100c2d40448a415008000301596901d01e4400da03007140071100c244240b4441d810307003d402e042031034039805414540c6480009080d2005900b0005d00203101081c0b608034140c0c04100c3e00e030824400300880f03486404402c4005114403800070400781d2070f1800144482c465148808550050201c100282440d04024a0444e191002032180d0f1181f4400d00001ca07600300d8070911820101c0b44d05031121854170f890f40d5554039840318000c11081c4150810f012583c040202405105080c0c1032942d59a0340d41c10102245144980b100c20300303001d881500340000d120120151088403500308045460703801c1691545884042841030200041900071210400a203400150f00064003c110128608810b180c86400440485c01160110340c0e40b10a5a501040f2190181222600000720700001038502a260740108140f54041d101e0320301c081d84480030f03240034019111310007400208441101c501c0c0115000007c9a0007001400725a805541ca40c04203100c4e50141c0d21070300007007810741c60540c07450365 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 620823453 1250 620822203 620822221
    0x13090b040c23040b0a08030a0206071b1e02030106030f0c0801060b0f16020f0a180e0a030c030f090e01080303060108060301050601170c251a0c040923 66
    0x50251401c8840001c1d001e4089140d40d10001e11200041600702e0300755500c03081c0c0c410807010744074038140181c01c000420404160508244001e0200f8400c40d00100401d0820000090810112081a44510950640141c00640404000c0755404c07076011b140d0405540f40d000090040007280d2000b00780510304400002007003404001d85084480090003040041c0c0c1e6031a500c00144100304102184000411010034000a1100c40b0f50a50340040c20f4144103070008400319081c08100e0300040001481d11090052035003160050000300c81da9180a400820a1a81e0141c04c40e04469002414004426a6014018800c046c0304009000000d0071801950b901c180407512684181d5140d4001900b050000344142414007686002e0724060b0745003c1d5481c1654850200600f0181c19125650b008003c00035454006d80700380512102c000158009426a03841c0424003403c500c2c1448124640c0d00c8200803041c50b0307020070791701144c04d025404034002200c8901000c10820940800e0708804400b014025062 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 620824703 1250 620823453 620823473
    0xc1d0a05073e07060311070b010b0a0e190305010501050a060c0b07120c0c061802090c1e030405070807270f020d06090204050f0612040609050a1406040308070e010e010e1309 76
    0x2200760700d040104d0944135a21b968184110030b40030f4981d1000307a004106052900c40101940c00303141c46c210b0341501200c2d00041301400080c001c01e8003200342607018002e02034280b00d01c500605003260700f51002c1d8904540904161000c030b40182080300d103000060b41a80c00b40f0b01a00d107041417117204000f80c44050001608151541c0800c0c0c400524000032200c1007042c1e8803915640603002080203509a584036020501d50740900d01d0b05140720001c26425622000a50244d401030b80b040000c0d260315030801e2052813038281264041c00e1444c60800202640405851040040e110b009601144030010152200040e1103a5001074003214a4681c0005824100340e001d00305942c01120003464982502c03003081494010103840100101c181c402041c0048e01a60203420000d00c603109a4000740c019858452004030618407041054104104000c10160b0010740349030b00c44003d00300007102e008130354002041040c0c0d03074001c1340c1031001c0c1048840d003035a541440e0710702090301c007281400240394516000c0d00d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 620825953 1250 620824703 620824709
    0xc0d0c0305063111040509190807020f030a15200c0c010e0d082d0f03040308060607051f020c120d11030c030415090c1d0a05073e07 58
    0xf01184500e4000142450080c2c0484641c1291900c2c402d140d143d03040000820000e0301c0003100748200f0350f40c0f0340300d43c00c4402201e0840d409016640e484071841c0c0144202c07500000c190300c2c0311360005013005002800840340c400d0a41c0d51b00000250a00e0769034003510260710002560105414040340c24044002c0008229011800c2a40c480010b8500c10f0180240301c2481d000003001280d050180c0380c3c0000000c2068046c1c0c2e140c05041055030b0390b104035007908941c0320240504071030f60300004000525800030011500241d041d04e20030303c1c01009840e416100c0b0000380c0284e000341c4400ea2089203801050301034445100d9040191103690b4400c901c1208181e0002d2400303201c0c0790a1980c00d44490080a00796440340b1855507000340341d6950b50362200007442c0308a120710500c40c0c3c1c0c3d0810002290080d802c200c0500301610301a040d9040d0318001030b41c1c03d8001040d0f03201c190f04007410000b44030341c030044010005014500640c00840125901c1894403141c0643d907011420500311042114000520b800071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 620827203 1250 620825953 620826001
    0x2010c06090b0a2406030e010f020a050703091a0f09150301080c0a1a040b0d0204182f040b070804030506250906020601051003090b040809030d020c030c0d0c030506 72
    0x5500c580130303a0640d141012a0035110aa200000c1008a00c2c025080401d02c920040000107420300c191030030348100e8000715404c1d0001240443c4020801d600542d151003e010b03032807103c0b00c01160036041c0c144a885002001084107002141064043d25035040641c0400400340d00583c40707603191001d0303030b60f40d44104189070700c92040d07110005102c0004120b41c04021040b030440c5442c03d41417602c0d81806030b2001e441c10000950800001401421071481458004a81440810100e51544040d03a82c14a20810f00301501c0c841c0c403010130840c0d59042103504885030110313031b1600c4c0c2c20a0b06007280359004070f610103000c40c040c0c2c03000c000d9001040c0d40300d000700054003100007a01c1d166050040303a0707990150141c2e10150f4401d000510051070401c0d246000c400c124a800300b00d901c1159280d206180c016601181e8074000494003c3d043d02e0f0138400125112150701c01400451032200003c0d582d050042c0002d401040403103504c03030502c040c114050024540001c100d03252801d00b03182d80c0140241004c01484 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 620828453 1250 620827203 620827211
    0x2011415040c082412070311040c0f0c0b07030609050109022503141315020714030d02060a0b150f090f0f0d12030609090f0b0606030106081302010c06090b0a 69
    0xc500400e84030340a6481000c0d600709070140001c0e07400104c007160594a602c100c0c2c420b40c80c0d500907030422144000c2c41c400e90050036055206410302c000c1d514030603401014448410410030507152700900400c00c10b038100d164080103844106c42034005049a81001350210305240000c511000b00e80c0003400c2c1070380d40600c0c5580c000c40d9103c0300d050840000400900050200b0070310750380a00303054040c0020f41180c0315840c040e560760b4580190000b0a17a9045805600311030420407001283c110700d004480025405426050140307400252108801088441b50303550707814040c0c029854003040b00c1200d589020040d076580314840d0100556811040e03011b4810781c0d04044032400c9084c01040000742c1c01d000f41001e01070511507580c121828003640c2d40d6104060f501d82c0e00103021200c500400074402d00a680794101c0e840c4030304255141c0c0700010411802a01c0410042111582c00564168840189100320202403058401201e000b001a080908110304111400c0103001e10060340314010300d44990108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 620829703 1250 620828453 620828471
    0x3030d0e1005060a0e15060403200301021c1806180c0506074b0209010b040b090105070302030705010203010b0d0b01020105042001090e0c03010f0602010510150201141504 75
    0x41d007034980803544581c010303400001c2005a03d0240444a40049840350b42c201007065090101d4440d810940c41620301c0e04582c008160392000481320b20341d040c10160025840c0c44400074079041100b0074845080c07401551140111203c580e948034030703118035a00030360a120b42d0022810450300842c2c500c0701554410b1300840c00052078680102190b1145501410061405004003251550002c03110307040c094a80d94128440408132101a0740c503e0070842e60000007603001c1600500c1540e010581044400c070004001c00d0240988020a88008000034600b05070364140501c0d0403401c40c000d440c3c4c001e15960011002044c480809006030160104107039040042406100c0124241c070f8058401030700d9860711a0202070143d0690090a000441c103060400c170340c41d0b071403402c180c80380412541c584680b84044010b00044c080200c0c55402400c2c244020300041c144114000c0561515110700303220041d2182d40300c03040034000c2d00022100da0110309038500c10319080c1c0d03030b082c00a0b15210300144250b281020407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 620830953 1250 620829703 620829733
    0x6081807060f200109051b040209031209061306030501060e040b0d150e03040e1e0403020606040504031403040c03110105040e01140a0e0403030b010f050f0307080703060503030d0e 79
    0x1000c01c0365100c0d40c441150030751030081500c0341c0812800c2070380d0700610140443e206076070901030000201e204800a04034800c809100402e10428041e100d449180100030103080c50b40d00298075070714203451700c0c0060381d2094800d0000f1414450520f15202808030207400081c0150182e011034100c03001d036150503020700d14040400c000c031602110306035406880076180502003194445600c1d03a2498208000400180b00d100301d901d90340055200c04948001d01c41040801d0282c0c1c07689090ba50400d850012160800b940c01035107a400c004d088a0040e96100005401d162140d054a400070500c0c503c1144da90400d8201501c90501900094820420b010070707030001548284100c1d0300312038030428521556420800123506c0220703003a41c0030b40d2004071014082241102c1c1001385025500c00d0b00c0000751100c4450000d4035400781f0650000030b001c82071044160444502e011658031821031f02c0e151800c0e42d02c500040d0014544c1d6042a038241c031011400039840459507200f03895103008407040302c3d0b118001e0a1a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 620832203 1250 620830953 620830963
    0x180b01080c090f07120e16171606120b0a060e01021510060507061b08040b01090b010c060209150f0a110c031216150c1d010f210204060818 61
    0x7444128650000460310761141702c00460025403418003250200302078284c5454400c0301702d20300307032243d603d10b0080080ca014010b400f041c1d00ca01c20040c0828032401081079040300303218465030303050040d00200650041c02640c444084900014611039070f09498050080861a48003141c60143c810840b9050310406618100c034462104401c5840300c2505003442291150440101210071a40750f060b000c0c407241440034a20f030b886032151f5074120b0614090420000b140d4040c0e10005032240742040c0310348640d03803000c2c154a0b0903401c00c0c8056030355411400840c0001100940c0d050004002003070580c82d00114400604140d61141e80c1d121841b440d1046a07502da03a9840029a4168080078103141c1e01e690010181c01c1003084a058480d0f10030a540342c9803009040e11900d203105550360002c00304400e07009589602000c0c40242c1000e01076145a0019014244d40d110301428000c0c200200001d40c480c001c2044014001c030441552110f40c2e0302c4020703100e010107a4042410021000042405241c0010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 620833453 1250 620832203 620832211
    0xf0c08070c051902210303071b080409050c120103031101061715071205090d030f09031205132010020a0c03080f04081905060a0207050703060f180b01080c09 69
    0x41c1c075003040c4080003d004140b400b1000ca03040307a501801001e030075000d0849140d00202501c040c5540c0c1c907140038020421640c20010303000942044490002043c07050301502c0c03c0d2100500c0c00503041e203409108000700c0c007500c03500c80d10409618001004040c0d10203aa011118101402480f80755183c5500d61202404040c1c8001c80d50301141c4c00d100320012180c1c003540c03c94807138180030442400302441c48090385c1d01250309080960003a840c2ca180c00358107210b45408201c03c803000b0095040b4a613001800003148800c003034030158032400480e03a95061000881e4540303500180c0019250268006888145201c0349114821529000880032043c0003003901d0030142e0b4000708401c41c803070a5503500e140c10381044100c031008031414040880c0e0700310b0400403200f46000f003462180820840b40760072480c0040042800d80e400d80107106d40d00000c0e4000070b0407801c1c1ca501100104104041d20369443c01050121641d00020441070081803d108800500074140ca00314402d64558100f842c2c144880c03c2d50030340d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 620834703 1250 620833453 620833463
    0x140d0305030a0b0616050a020a090e03032404060e01090e010606080c25200a0510080606121608070309120f09052821031b02040f0c08070c 61
    0x1c00a08411899408030100d12001050f0504103131410f00500384000c10044100d500da8000c1c00040c042d4508010a803000b8440d000c01402684400d15200d9100d010140000b50340001401002440ca201c9008204c40c005000d0403c012050703a9150004080070284124a0768603d0000c00841300c01041c020740c0c0558400752512405030f217520a0341c002da0f611509000e420802008410300c0000041038481501e5070082c5607046c0c40000ba080c641000440f00c801d414401c1007141c07410480d0351210038052200d0301c0300b030070002c12543e914030108002c0e10803d2952880721a0030b60030414405040040c0980c3c04000b640d0364041540c075010140c2c200c17181000068849040c80040c51007440c400e03034003101082058030f040c2041a40e500d0104039074403000b2600c41c417840d0b250319240000300b0055210900502110f084011000d00c0c610805001c1d5402200140c2009000615034500103084692503100b1907014104101c1c07640960914030050900000d200e0006020401140d4101c0c400d29541410039001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 620835953 1250 620834703 620834707
    0x15030603051917040e1b0f1801023703020705092e06050403080a020a120e040e03130312020a1b091d0d0f02010b03030d0e060108060709270510140d0305 67
    0xf1b00c00e03c079480103120f0000d64003c81c1002985420005030001d44a94407c0904000108100d4400a42032690050481204c2907080f1030400c031850501d2041d14481c1036440b0703031000c034a00d181012800d1000d40e8110f03540014600051041244c468401c00b0b0341c4140d290915101e500300c00f2000a950143c501c01c92000030420310040c0003113122040109000509401160256207142e505d1003d248102c000d040003060100300307034454a00f010300444060240000c007441c5032000205002e02440304c04d0002810103211600004a218000c00a11008e140c02c010910040480644500c0d0511100c0c0542c244131420590914010084070504100300c0820030060260048070800c01c23a02040c80c0c900c080308540d280c0d0107030040364405200800e104140340340701082d028031043c00146044c90603844030700542d221100b00289994000055800c0d200700c407444030401d9410420106801c61341050200030b0502d00b0091003000f452102800c0210395013040d1404000e0340c11810085150010030000c0c0c042842 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 620837203 1250 620835953 620835961
    0x803070b0f07050d110702031b030106061b080d090209010e0a0b0406050d060f24080c1020120f0306031c0c0201120204030519141615030603051917040e 67
    0x945c02108190741e1030391a0302c0c1800714640029140c140828500d5642c0d1904c80502c1e40c0c0d5041c01e00030b8101414460500002003a0759220144540c0b240301c802402442c00070541c0c00a01c5c070240c000402044e00107080c04410350b10781d041007001082c143d80c441034543ca40341d00d540040c22706000d251704a9400802c84d50102445440e0f82d030190096a9214232960350350611002d0300200c0c00200b044091812000c4102e06003001c2c9068507010b0103104d100e100d440000045600541c0c0912105225a4411404801c1500020301d0078a0f045c4030b619a01208040230036001ca17205a0b030b101540c401d6030f00310100d400c040103080340d5194a00c1c440c01c610000034100418030000d54000d400410001100301030040c546540d0303440b1a8202140741090000e001c0c0340c00080414081c10340c5881032810b100030094443d80c4118101c4a00c40c01c114403654085075015081902c0b210300a9100c50011030704401510381120348840c000000c00e542c007004071442c8815050b20680406408180c17426140080100c41240e25 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 620838453 1250 620837203 620837227
    0x1050d03110105010803090411040f030f0302010b030316021c03020d0302090111010c0819050f06090915161101020711010e0a03050f0d0801080604030f080910060803070b0f0705 78
    0x408240e050126000318148000c1003441018003d00016001e152641c18100c03c101c1641c51810f162011110103100510040b40400025421250300c8002c0041c2c80855240590141c1a1031141a038540408200c0e21848245a04403c00300c510803103500400c07c6118508003214511400c0c0540180e10100e00b0b01c0802d806607000740b00061050400703000c1064008901c0e829549a0888540010400b406114141162540e9803503001045d6100b84002d01d4031b007040e0b0b140aa80100140d12498851000c60314105050008400c154181c0c51403100da8508840100c81c10350f0301300c1c0060001022070010115481040c0700f5145855846a6540802482c0c84011980480e900784402d174001c0e00d1450010000390100241401c030180c20002c4e295820a600025160240582c00540650070000c10800029440307580740c8282001401d0100c0c2ca0b4481d040c09620f4600503081c0365419910742040800c0306000003000e400034622904110b003a941d201058070520040035680103010400904c070050001c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 620839703 1250 620838453 620838469
    0x27080d1415010e0a081f0c050414090604091b051311030a05040305040f06030605010e0f221503150506060a0903084b0415050906090a0e09010b010e090105 68
    0x260f4003c020881c01a1140005030820304288041e6440d01010302c81460340c20003900a0588100322402c1032402d251402a410000018020744107215191007c0096583c0d80d803540480c515640020300601801c00d45244656900c0845c0100ca01c00c421503040f1810406050248450011200201d24190307210381501da00138100140c4101e062110030300010412090300c42d504070082905903404110036103828000b50140da0000c221500a04081500c01215103800002a001380c805804205020604814141c0200200c00b01c10360b403260752074800800c0c0220311084040b03010903524100321544592040101c10320805100301e02007081076008001184064000d45003440086846509a401da410000d107080c029000c403c0c00b40d042c81d0b40c25000301a8410303000b40c40d01c0361004100c2c82c0505050941030414500006181080000203c0741160345500b010b0b02c128960160a08040d03503119651101c1c950b1046a200c03600b50b18084c0e10111035032141c45442c00b403800207440e0103030507402c05040c04050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 620840953 1250 620839703 620839727
    0x1a09060702030102070803192307050c010f020f090301050a0207210e0a0603050412021b041d0f0a1502070209010603180209090d0906020303010b030a27080d141501 72
    0x40d5824021040846c03102c500952207030004544c00346842c06d00c80b04010071200c2060310000380c04034224508018001241d80c0e01c0d007001c4103040c05521002e0f1443e606002d8101074480b184090300200c1e110104261580103400e00c12021002031015981e02d540c0c540803400740d91405407815a00b0100c0b800e400301c1900c0300400e040a24981002e50321162000302d5200300060344100b0009603640208000d021100038080351030780580c40078107607a00380c42442000f510103c80d240d074032035030f582c0c03041c505040040d0f003450001010200540c0e040f500b0f16041a9140c0c1c80180007907130b0348002d80800460b0304c6002d10031254042e038000c08985190b401c18400310001c28908048444d6010003c484101503550303201144d00c12607901008080c00d0200034402800c2005c240e001d401903500520040c0104000c007801d40e82c0c42010702031f0020304000c01340e80024280391903e04100c4034100300d0400f0300074005d2000080c07440d44983d190a000c581c425600006045100f00d0380314042048a00351398550f0742c412103031302504d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 620842203 1250 620840953 620840959
    0x804021f1701120b070f120c050702031c082a09040608010e010c0f0c3909020706140103230c040e0303040615060807112d071a09060702 60
    0x4503040a410440101c0c0c801e8122103054001e00780c040c4100414410241d070b11240518001016107101800039000c40200d4116030304503034403404500f04007481007007628000b0342c0040868a902d00b40b003500c401d2409800d00580300141e03e400001e08901e1014909008070780303054040c80380750f007000508000660000c0448992080d2159000280d2800c03d0183c92001103682000143d410030700c41001e0030f03544541100c041484010841d4001042103140390680241c0103003211019140701190900205000c0001c5118042d1031250224203074446a01130214140708a0003009030400d8050703500c06074082444028441c42400e407400c4000d803142c03029000e04008002c12610780d41005000281034600a42c001d034010b40c0040304000501c0a54011710000c09802c0703144801c040e052640080450400800001c2402851414140e9a070001c200181e20b0341c590b41600210100c440241c06d42011045885000742d109000020613005182c840d882491512026401e1a10142100340038840c0c00114042c0e034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 620843453 1250 620842203 620842217
    0x910020c1e060618060d060902041d1e01021207030c020c0913030306120804030b130c1508100b180a05060d06080706020102070f03030207020f0a0603020d0c0804021f 73
    0x1100159440001401403150280c8460725120040c00040303051940c180c4807484e0300308140602519403840503666a60459404101407038103002040103440481180c1180829103200325981c21800700ea01d0b6400400c05035020b1010301482078582c241c1c0214075840c0007441e05003010402c181d0203688514002030382ca00546501d000088001184880100d408441001c1076850b08010558035114250217080000414240c1c40d1241d01c07140494010703808010917903865000401c024500300c10076a80302641c05011851030030389494109a09100484400303010440700740200740c11180e41c038180000e4503019000e15042c800f150440e140120140b2005030382024524401040b1502d580006001600c803001d40401c0d4036191038030692030142250301543c21648180a4500020aa604030200090b058940941c4642c40d900001d15000500d0703214550205840c840000c406070150082d0450700007404080100700d002400541c0d044001316002944146d00c4181e5240751400500f0020381400305150141c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 620844703 1250 620843453 620843473
    0xd1d0310060311030c010309380702030706050f090a080a050c07080606011107060522080d120b0a03020105040e0a0219050d0c1d0409060f021b01060b030910020c 71
    0x3404480103908160f0744659950070000740c5003420840c42c00c11003820700e41001a0509902e0329401c0d403184180341d10400b000c07000c10031100c55104d840381c0603070300014420102074101898042d60f1799010070004c41e1403c1c141f400141800e002d46070340038443c0d1600e00140003140356a555007604c1d680800480d005000702842400c5200700c0402c1603038050500103009081714204070001401240d400300300c0b80082e901c564030610007240d101003a42c0c0e00b45201a0324010818000c0240a080c42ca80d800c1120241304120341d260f17400e40d200c0780000700f03519465010001d0014900074000c1031090742c08042c2c0440c0c030400c42089003000e1a520207074440300c0074400504040120f003020b0784e05010103105800042c0041450b100e281d0340c038881c11408201a05000d070b03100b070409600b14103801d0071a000c140302d140e40c5e281da10180150f0b900906d1b03100840c40030855495020100d40b030180d0250301140d140c00e41c44d04001003a0030607888116409204281e005007101605100c410020707601c81c105009090050340394503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 620845953 1250 620844703 620844733
    0x6090a020c101e0207081803010f050a09020a080c010e060d0f110a0206150d1e06060b0d0f1a06031003050a23010605060406030908130806060109080d1d03 68
    0xa0004114800d401081442d40f10200f085003211500389000303d14410045180040c5204003100c5682c0c03c50310f01c994a50700c00b00006030041010607aa030b012170b03040170204100c56100307a20400d101e40c403c903100442c4a031070b818102c0d07803001060110350101d03100c0c0030803040351b00d4a90b001e0300c9114811880880c10505140c060f40688030010051000c04501040d03010400781c041c04003503403048010341c1c16003958076040005014070701e44d064041c0180c0000c101d01c41c8000b0690780d40078103054010000b440190368815448c0386a51103d0364600a503480e06061550b82c4406001d1041800c5000000400700c0300c21008014660307002805c14000310031a203000100007030044c00f20600b281c0c0903a040a0005c0100f091618001303007107a0118241340d141000922180d9a00c600740c0341520700d28a000a200861480c04003e28440d41c001c40590b01c030004000241c183d000200c05100d103800782e86003640150346690b100e554201e001444808100c0f020305400212400840c80040900014216403201548800b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 620847203 1250 620845953 620845963
    0xd0c1103370509150c0a0807080d060e071202072d0606060c06180203060a0c0318050d020705090f010b030a0b0603090703020102070b0f180d02030304080c01081e06090a020c 76
    0x41c10000ca8408190190b191911056002200400c002800c0c6003105002c0780b15200d0010400c010400700c4049901020720002405a072440100c00604010341c5403101d8500321042d41c200d640000207040181d2641c0755407820f0007550f46c0035500290a40700d00300070b20348050b040301c000300c84890020003051312140410194082e641c002c098a449440b0400f0440c2410707010380b201418500d20454030f640f034281c016100094120352003040150700040190440508801a1041600200c00810640a24420703c5070100700c078050000315400b25075180341e940041c40f0640004075119503e0f104540010000314009100843d40700c1000140010405400d100084080c1c0041d603e604d41c9621000c424008c55804010600241403002070803400c019000544107030360f120b000e000492a04028290003002d4494114402c100f980c01016a03464548410342590740d40e60480e10540090440c00106800b03505841c61803103800201030010714a59900c41c2800300c220405042806415420000f004001c481442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 620848453 1250 620847203 620847307
    0x30e12030a1503030810050406050612060a23030d02060609160207120b09011104050d030c0c08120a1211090616081603020c18060d030c0c0b0d0c1103 66
    0x403905d2450800000a020b10000da40009018604e803040501442d80c0340c8007550350180e151480c2001503901c07030300460a41307580c9a011000c24514403d10f11041d2500950f800d0b58944103a0807686d507003012400482c0ea0344400d6403070a42003550ba10108407840082e0300040280d9045004079410300d99500c08941c40780d00c61900546800c0d040409104010201780100c0780f00001c000d0601d41014100000201c3c05102070341c008003400001c2412104003c9601452002000c10b43d083d00d8003080449a0040c082d80410148000585c000c3d02d0026024294800c8040301990040d94504094018090100d02d0303110814103402d020314450140c0000f0220002040b00304204c4440d161280700503c1c0c0a841c010050724824414020362500d15240c0206a000d070354440c1c0220303145080000340e820107442d039400507080507102c0d00da011000328008030300a008100d000d0625504200581d44110201c4100400820000c5190020003e4610403420744800007a40c000c6c3c000c018641c031812001807041d40c1c50f692 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 620849703 1250 620848453 620848457
    0x10303051303120f020d020a02010e0d0204090f0609140f03070f030e0901030303020a0914151b030f1312120302030604020c0118061d030909070c0f0c05030d030e12030a150303 77
    0x5018441d0285d0503c84400d0b921018001080f00081c980d001911034001840388500179100c9910002c01e5642d00e4000c5142640c01500040000e07181d81003410141c424410107403030b16144e0001d00243e104000138084800840440a1800c2114550712201c1031b604250702601084200d00f0010043c1d504c07490954000c500c26140140c1c1d50802200280c08641203a01900c00502c0b1501025840e440e500701205151090701515070b655440c0d0030242140c9a0302c0c400000403031001003000121a104503008000101e004120041241e940b2105400e80103c0c0f80000bd00030f22210368070004c800e0080d0082c40e00100d0003000036050649207079103642140c03201c00502e9001c0342c0110707010040c44640e200d0840c00b07160081032480b1400020104035964800d500d0120300400d5550009a4803900c200520102d45511829403540c10545041c1540c141040340a1540309008901c5c0603102c2074003900c0b030440c0c400c0110340a49440d049600c2040203a4100502003002e440e2900d45010080c502c251001c0d024501c00d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 620850953 1250 620849703 620849717
    0x40905130507080c01021c170c030f1005010c0210031d10140c070332120702010b0a1a04030f1b060e130203040c05090c1e1201030305130312 62
    0x9070034200c1c9420300c0340e481200d89070849103484045990101e49030360b021450385120f00d20340e4043c880884008071550000c1840d1410700c000e0002c50110440218010200d0390f502c011240c4a08600704001407403441918042140c400000300142407401442c20030b407a00781000074409001d859103c00541d0540340102e801d070440341421000543c0e80c8144041c2000c40c0014010601e41144024840c0c410468050284403060300208400c2c0c140300c2c80b0038183c507800c6250300140c5124845004003504010250b0060219a4000580080c41440b60100c000340003405114114501800c0c8002c09500c554a04004201000040041416138010041c02441460701240040356004003011025140d04142e0400121261031801c0380c2e23944040c08440101e00c20010b0b60b0791250f1904078840c1049a000d81e420402c040d003041850308c0000003600384021381c82c0a100f94204500206141c5e441026502e9655140640051001c83d106402a1000107115845180d5542d269220300056403400c1220500140c60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 620852203 1250 620850953 620850991
    0xc0615030b01171b01020607080a0f0f06060318020a1401030e0d08061806010206010b0a0e0d0803010503071413200304120f0503281e05100807030302060a0f02040905 73
    0x41004489082c0d00790013200f0320450b20030340000b5141c5002811010070000e80b00045440da1303101e0760200901c8407040008110000c074140303000d00030f81094422400403034035040050101001e400408070050741d0041408034803e0070100701d03071408050507a4403030416698440710b122500003000190484032040d11080341c245840001c01542c115940d00d6600d80b00111804d02c0320071b0b60006403060541c0c1880e40e81a8480a03c04001c44c1c90600311012947c0c070109c04d02e24001403043e0103008605070390054007036030b80241c4c580c00b030b0f00000e030301721408130b42c0003d0b0901d82c801480c00c05500c00b050900303a161600c1065041e80d030b26209540c20a80d002e449041a802c14126041d4000c11554100c0ea043d0034a20708516040d01503404010410f900003070100c5c010403007a00c0310038560b8041304402070400410307a021131140c610715005000072a010000d01000c030a0105003a54000f5044e13007207a07030541c02840940d0740d81145102070101201150400341d024072012480e0345041c09581d07c06e071020b03030b5500c4c07646807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 620853453 1250 620852203 620852249
    0xe010f061202121216111003050a060b0c0c130b061b0c010309050d0f02030d060603020909091513020f0a0e0f0c13030b0402210a06060b04060c0615030b01 68
    0x410f1201d46046a02c480210b00110000703c0643d0020580003001404201c503d00b00341001c1d0740c0c01003613540e01c4180d000b0080301071500366000134000c0e4010182081003030788501440d034142c0b054981c110650742c0005021142490180490000e0800007440030480c01d581401080701c44d00501015202d080c0d050003101e814540801800444150900e000d100c0d50255440d0140c40d00f4102d500502000017400341d00030418001c00c1206c82138404280704110f210780c2c1c1c9400074001c0d0480c0008c28812140740d80401c41c481300001e800c10a040900e06000216103d40614640074080b4000890f0484541c1e4807003141503071501c421100800c29010041c01c1441e1040b010130840300b005100c400442401c0c8807840d0011148000c040c00e0344c1d400b030f204500c19101c500001d078861603110002d005804101c03c0b0f40c603001c0404034400540510030102401240e4984881130880c2c01580920b000141030100c0b9080820100c0c1c00c80942c1240032100070007a41d84944601e0219070090f00302c40f2182c20980320840241c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 620854703 1250 620853453 620853469
    0x31602210c2e050c04050904110f03030a020714180f10150e18010b0901030b0d0209041b0902041401030911150a140301050604050904051c020c0a080f0c040e010f061202 74
    0xa85626685d141908180000e0400400944098107030001814071000c5522102011089400b004085a40351181541c00941e503803a140901040300c00281d05c0309215040030100d40417200d4108c0c6048035186d40d640607840c0340d0380340140320020b111034001d0001800490040041c007100c0d11541d56090040d100700a200c2d010724560b80f20800441c2e41c100411007040c14805803035202100740790100704990a00c00199010310400710195000380507800780300c108010401c0307080111100c440b4440c0c1341c1342d403000701c40101c4c000d62058090408070b929040e0b011358426071040024910a49041044070300c00e10200d41c0b44203810740c0f0018444800543c040010b074102d0140d2480d003481184152856041c840403c0c6140603d1185c140202042400b0604000c801d002081554079203007840140c510160000039030310b00381d804417907010305208103001c01d0389072010030440c0e0f04d00c0940004002c0300c48610103010042c081d80c80000100c3d562a8140c1000040b14011200144110068008050b540303004000a00b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 620855953 1250 620854703 620854711
    0x150f0506030d020709151d07032412021c06140604020c0c04020a0306031e031e0c020f040f0c080a060506040e13020a1505031602210c2e05 61
    0x30780e1022a803110b4403940000c480b000d50720403000c0031810b0a10003291008103541a0003e5150500c0c0480b1441c90041c0d40c0c114030320481c0c49660078844c4003200c220074018a14221000070000241c180140a0024070398800d0440d18400b5040a0019900c0c0011008040f030120003103810781c3e111607105422040d2280d9154004000f10340441c941003410b00038950380c00400780300902070744d0080303088171400d0300981c4480000e6410140c00b907401c845030344419026000e1041d0403000b040f41051034100c2e000d0125000489240140c0350b140c03c0e125203400f000700b203904440d88070703501544a28103952030b00028020361600b14100e40340d583c1c180c100a010720041d2010798000c18041c460610007006401c11954110307401408481a038200c8210f1400490080086604510700b00348451040804036688080198851144800b1701c0d59850440d03981244caa03100d50342000c144420150345018600349090080c140302040303e0880e40d0b01080c03030751a1696002d080c510780c3d2002507004004400302000d40902a84 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 620857203 1250 620855953 620855959
    0x19030302070c08190b100302060403140706030501050a0b03041403040f050906100512040516030c05040f05010b0a27120210050a230c16080c0409020d120c150f0506 72
    0x401005141000320100120b02d01805c080200380100701400701d20484a4003954020744420342c2c3d16213a0400c1440c60100d41a5030b203141c4907004002034410300ca88545416a00003d01401080c2e05d4800a22402d8001900070344401103006401040e081003000204001c2401d100c0d1940c000c4c1c90082001048000200325501591000100c138200c01e901104440e02d10000b1440200380c0c0d12282819440d1500e48100394003c1039402001206100c520031603001204c9040754140140c050042010050390380030b03c01c0350780503a81400107020681c090700a52406412041002120342d4440e001e100d041007080d4820800140c03000d05110541c10012004151081d0b2400c2403807030f22210030701c0140501d00c8005503407688081c3c3c41da07142e248242c50b01214803250701a802c4518441200d034501500c0700d61032144808c1c5204405c1e40c088603081a008000e0345903002841c0107101284d5032100c0700c140c0c60000300c900070080030758284000941c03d020700d40080c03100504009000310f60724002500b152800742c00360748 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 620858453 1250 620857203 620857213
    0xb18010f1a030f1905070201020d0606020d090306020904020702031b03010c0f020c01120608011b020c031b0f0301020f0706020703080f0411040e030d0230060a120519030302070c08 79
    0x300480004040301e8200200c040201007070782d04c0c401d8414416201203000b480241c100300c14442050f9054010700352000c50003404101c820f9a520099958101b080800404079410305c0003000440c0a07a1b01800c1c0500024001614007900790713002074201002400105c0c0d18141c01100240701341424030488007144958181803201d03404080c4065514aa807100050400462030081070501106802101c000c1241000a100e0700c0541307041400320100c000c03413080c01031203481e4100c0150300d80007424892350314003141c0c1900742c5603446081c051000886d000058056400700480020020940d004020039805100d00580390409031400515100000e091006003000400c240008501513402c01782e4030810888001945110142030715003580584144205c205101281e150111601c0a24040701e40f041182a00d01c201c2192032400c111217402c5c1c030511f40240044205000045040038000c90090240040b40c1c070101c207100300d40b4400402e1070350487c0000d0300403601c51304210421604102a1407040042c2c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 620859703 1250 620858453 620858489
    0x30301181413050109060e0d02060609100605030c130807031b0b0d151a120a023a09030c050c03060906070c020a0806040503041811090d02040b18010f 66
    0x8a001c03501401c0202540300703180040040100950120329007035408603043c884009420034142d2100745018211015004241c002000c131301d001c60140380b080061603801000c903402c080342207a054000070048035243d0020000d40c0a6408044072030301c014075500b4010709031a130861801c03044010b428802c2c40250141400103000d42c2d8203803010b0701c0300d0115101c1c00151f034803500710810710101c1d2554000145444507491100c821109030008140401d05c0c24203801054076007201c40402ca22a261411205152152501c42d00382911840c105c400b00303103104280c4030003560041d031404035021040f0840105210700d1602d400c1000c14006203035006012000f801203458a21308060700e07940b0041c1150b08000c1c40d0754201c000c541d200340366074000c0c0088500712401071a282c034000d40d40741e01501841e00c15115070b03103208840c0c12550240c0d60103080020001810151120f042c081d000c1d20829089901c80e445059440c2c042d1503080c40079040c0460300300510b00652401e0801520654603400038400c01944070051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 620860953 1250 620859703 620859731
    0xc2b050f0403031b060f0c11071d13060608010207150e1b0a030b010e092a040c050c0a060902120a02150c0102040509131703040201020d0807021e03030118 68
    0x9503085903014203045031507043c4412603003c034101c85079004010030702c6d01c0032081c810301483d40325500313200031034031000b426609481304a980c5050510960019600d0b00f440308507502801607801ba08a003024440318015946d81d6140015600250030034812a036010440200340100701c1c2c1401001034581c9010031003c40740812042e1a0060070401c18078409405c000782d4030740d03118000391100030754000b20710680c10758680e500c44186100c2607440c1c000510490425203005c940041c80c02e01241e0325811083c58041e00003040c8000303400307042d0b0000107000701809145a500c0051010018040c0703e0342000640320511720402405069489a00f402a0301400c1c01d81c00688a82c00c0110080d40b00031501511140390307088090183c0b056801c45900300b5801d03002e0051600c8803510100c1c02a105030800d08019001e070110918600084070080c0c0164840544504042d0080301ca1a4101c400c6106541744012084048114580b9826000314203078400030040090842c100c400c604906661030003444007051444003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 620862203 1250 620860953 620860957
    0x5040b100e0609040206041205251d06040906061203020708030a050d0b0402090a0605030907050102033105090108030703030e1c0809030d05010e0114040902030712080c2b050f 77
    0x2c60b03402502c81c0f0300880d05554403c1c043d05c004014440040c2170b81c641ea0720f01141c484000c0500d0388014540090090034007040c1c102a04160381c1055030104c443d40c0920000c00d06610b02a001582040d43c99050300c02061182c000c41c009045181b440e0000b010052170300a1402c00f02d070b4004092034000703200c8401c075541e20100300e81141c504004040360303600180002600078481c0645a079806404410002203154014003c0c41c0325004d2041070312607007542e440069840e842901002d05000560340d2501203454000410b00e948818084074a86055842d10041103450f00c00782c1080006030310101c0d0950400d42d00d805501c4801d41d58401515502d8a00e40702e02c294260030a00308000e001391400000c48201040041c2e843d07101515906121550b5148006000b030030085c05510920884010750fa07200d0f081500410f803107290f0241c0184421403920204680380420707040101e5505004200803c0047e00402140c5c1025846925030b0f000034801741c9290307804014540481e02401014001d030f01c1e2103500002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 620863309 1106 620862203 620862211
    0x2210415060605040e0408090409050c1207030c0b31060e09040c0e0606160503040602071e0b0f0f0d0c0e040b060f091c0605040b100e 59
    0x4400d001e4031054000c103004a2400c02c01000300780e00b10b02d0056401400390020711b05003111440001c040d52110103065801d54011101000d061801d20194034503445600000c1034068510340e0b801400c5d045511070a1050103001c64141c10128082030348080d030f00ca080300800c0391448401c6601140403100e0003460006030900461450350f0a15407d03190260350003001ca00a000d20305644e0b00700c46040149020380090061125200f1a5000c1007000700c3d03207100d0005141c0301c03802c1c031000a182c043d5980c480e038100840400120400e542400c241c5d030513070784035420555440080c04440009071080300680d00000ca0005407113001d1214590024044486d0b80d030724400f5018030300301080180e0391003690155020340704100b9030721103411071801084154000303412180440903552456421031015042034599648440400c010880d5101015520540041c614804941030600d85101240010 = true := by decide +kernel

theorem cover : BRFrame.Cov 620683453 620863309 := by
  have h0 := BRFrame.cov_init 620683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 620683453 ≤ n) (h2 : n < 620863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
