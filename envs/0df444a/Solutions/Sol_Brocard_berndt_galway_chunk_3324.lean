-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3324
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:26.991768+00:00
-- url     : https://prove2.me/submissions/6e85ed35-f490-4961-a4d0-edc077e41dc7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 597661870 ≤ n < 597841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 597663120 1250 597661870 597661901
    0x40b0c07031e15050a020c031210050d0f0b0718092309031206010219150b06030702030901030203101e090c0f090302040902190f0e01080606010807051b150901 70
    0x4085640c0c1d2154a043c44966090b5080d40c0e10007182105403c0d9058130050100380084a555401d004555400020101d030000505c818010740460507007410496a5071441d0310152540701c0c4030300c96aa091507940c0041c40802004451105002c002d15083c980074020101030400141104480c4d00c07081c0703080d0160900c03c02418001003440041007000089418034000d050070000341c2d072035a500403810907412840d0300086003024005c038001d010050040c07440200880320300300000e03600c2d182805840d0104036541800745e04240031f58111387d4066002958440c408080e40401107448803441710103070340982c9080540310015042404035650600c90300c1c41c80300c1da40c202071448408d820030003050240741e400000d010b69154030a240c215104c08100710015450403070314013042516416216281030b028402c495009081c2d500026034840041012408cc20f01a5589501e0360365201041d11594005c000d003e02e00485da0b12b001b4100182446000c0c2003580d860b8002c1e840f4140181c1282c2910f0002d003551001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 597664370 1250 597663120 597663173
    0x90f0b040528050c03071d0306010e07030e070e010b0d090c03081c2f070b010b0319020f040e0907080a0302030910030b0d061a03030c0d110a1104090602040b0c0703 72
    0x16004c4010b0f00d500001c2440c00800412860204042814030135030501e030140319060011031170300a1503d94a100f21a5039804200d402008111142d481c40144540e81d10705c2c094100501180e40c5103c010007010312141804225001103035507601c0504100e0f88140d8035840c003c94403010344e5480b040b8801c003481007244148841d186051529540750019000c0d4903c500305110b800300d0403030380c0c4c030306480b501030300580c1e20710140d07a403583c408003280c1c011070380c1d01c01c52007665070004054402c502c00d460110050340d4082e8241410a50440c0d0400b10241c030010715441010340024505400f0001c2e00d4043d4481d90180d07071a240c181041c001d500b0084100d003400d260070f001d05200c20303803901080f0aa0311030b0021000300c4e0003420945c207a40080d4401344501d03014000000c864208490001d100300780030003559115004a400c1d550030703940301c40320300500a00700b405c0003040821924003070304801140c0340180e5005141c03e503104c035584d10652001522000540000b03c080040c080d04600c0b280c54210705600003042c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 597665620 1250 597664370 597664381
    0x1b12080901030c21020a0c050105070804020a0914180102070f05030406180e060922030e1503060108010603020c070b030f04051b010e01180b03040c08060109090c090f0b04052805 78
    0x7640d5000390048221136901150142c940c41c0302e115203080481e0004020416400d00d210010034464088a040e40140070b60580051003508600c180b202a04d0140900c0b00741c1c2d02c540612604c4042d10418510481d0340034030070000441d200821034080700340320f4801555100e14200c40641041d181080d400310481001c1e030200070303e007071803c029603018101301c41104159a81011240c00154044410000c10200078121000c00d42c100100d10504071040340c1514001560038059000c910080394003d000420b86001009182d01980103000c0d00d42c486010350b2030441e00d07403580c100183c00072141003440c0c0312220300f80420704c4014003401001c40280c00a40030356203083e0001a01c030b500c01824450400456012022003008807540b22400751004001c0150749040c141808000d84209000f40c05488c0034050000918440d184103680c01141d01c03049001c0042d2600c45900000d18022036074086541c0c480c1442002a80c841c8640c5109520341d031010290b00e0b06180d141001a0042c0c1460f0315007901c1d140c03e101c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 597666870 1250 597665620 597665657
    0x10050601020c1012110f0d0b0909150a1e05041103010b0a1a0d0501080a12030605210c130608010b15041202060d0207080304060b010f0c1b12080901030c 67
    0x1103e00d01c20705051450720540c400c140300400d07034181240c1042c440800c0d1401074103001402072072240481c801c248258081c210400c03a521500b0340b8000c8255000440300c2c16000412045c1e0f643c4440700320000212040107030705000e04204041e0b00a003007260341c3d00400007003180c001c01130346140805400030040da02c0b040010810790b0509005241c03400c143c40d46076040320b003460011070b0f0038100d0802051041e541d41d5011642c2e1035a4400084480c0c03082034218a90a80c4644103d004450b001400c8600ba00901d124003900d4920800401e0101e0103a40202c5440b0785405401d141040070045000461614201c4d00e10708550340c0e4106144900c00000132032894100907410f807025034020901e520250861071000545910450720704807071030343c0003040e20300074009007030007552003513000d20800d10581c0546401120604203242c000c83c04911080ca141001ca95014600c0e88400c000b4001105526201d040304a0115040c803002c4500c000002092585940d060203424501d0406044c415031840c10801c000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 597668120 1250 597666870 597666889
    0x1309091e17090303040f08010b04060b030f190902090423010c0c080904060503120c0706030b0108040b0a0e0f03030a060807180e07050a081011091e030307021210050601020c 76
    0x40012440100390307241c4a40c3d052045400400552001c907040c2652075514038060051110110f02c6146400340c0090807294038800c0340d12504620310302e2407455556109452600e07440c841180100b960faa40d003940143c44501c601030241d03004060190310bd1140000310018002955186842641400420182e1541000c2032a125551150000382c9450341140400c00401080d40035551510524040b155a40c1c4240c2c0103000d049854001c0d00c8486441d01400d8054607007010781980060f9150001801041010043c260031071242240895644c850308403661a0400d1f0f0221102035070000418018040c000d0300c038000c0148010806001c0903480c105440345101000c80f1060406d648800592481010a124078805001c0083c000110703143c95607015640d43d01990400f000303451821400c520640c02203015a011044010485d00b04204004032164000818241a6415200c10b1001c4001648d41031940c0300c00300311480040c002283c003c54544181c2c1d00c080c00c1203055401200440c507031600c0d2034000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 597669370 1250 597668120 597668153
    0x80a0903241b0e0d02061315020f0606010903140a062909060d030f02121b060906100b0f121312050304050604061a121f02090f0f061309091e 62
    0x91310010070382800070070100e204911080682440d8004041610305e02c0c05e030000c2400c40c03107900b00d13410032600d46042640e9040030b403805408105500380c1040003a0406514686200c40e030400d54000800c155201025030b49000c000c28441200e000c41060501c0340241c840b11910811a0341c003642d42000400b0911111098102030100301c80d102482c0303070a6008000d280140070710300c00c6044d9030350740142c8007085c90034024000351024011240803c0d01c442c00001c1c0203018004402c0e20111040c50803001c01156480a40356240405051004101c03035100b22441c90310030008440c8101e5020038274a03040341500d07040c000354000c2c080103000340408a8400100350b0307030042d0312200000381c00d00c2200d1116900e0403609603842c2e005109200c00040294040b03210600f1100d09201c0c1c3e15081c54014880c426809000724131604040c50041c01109480e110244074600c1d90086d0201e840e201c030f2400b6000801c81e0755000f00408940b00c0848104000c28000c540507400c20715510300c0b0011800359107860483c0c01900c032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 597670620 1250 597669370 597669379
    0x120501120f050304120503070209070f21061806081218040c0309080a02070602011a06070f02060f0d090515070807030914030d06050906010c080304080a0903241b0e 72
    0x55400400c00104116005815040e1a09000705e16a20b07025540741d1280c48100d0044100f100824111401101c601c00c04900d15280c40000130319010403085410020380744070700d07145c0c0c880c2800100c912068000c004254188500440c8860038a80840d18020743c400044426071030402908450940144202c3d40d507031001c031404030b130300c0784101c80840103041c101e030000d000b900001490b04441600018200215011034000340005006a5440c11005070010b0b2141e42107001080b1800004d0a6904503000c814801440c41d420300d500d809601c0c065401000c0d0540c4550355a107200b9040c03000400141000f0400010f800c400c0e4a845030f4010019500a4008018075072074101d040108081c40c007220800c14840c3c4100d170b448040d039800c5040a451148100fa0054400c50040380c020352088081205030368018407454070b10313129652444440e43c0150324090030402c8404010000480b201d91204904200c400480e941c0c81004200d107084401800d10348080400340d001c00c0703003415000303016107a101d002183c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 597671870 1250 597670620 597670643
    0xb030102040e011502160b0406080a0204080106030311060a060b1602012106330513030203030708030a0f060e060607111305090f0a0512071b06050a12050112 69
    0x11901901903074022100300340c00d100000c607200911401039040b681056088401144900243c410342c41a640035511001c801080709100190103101445c0d00000f040f01c0c014940b0380d0301c8082e42d003115020382040340081c822108100256200700030306900302040481c10000c0d0341c03a0020221b031610660a00504061441d800142568090400800400c40407000e220011900401c164000c2a082c0100600382d01d2982000c07403e42c0c24140a182d40712000940303030b815400105401d81d000e4001008030781c0803050000c000700043e1400c0c409040600c1c0304168494aa0800382c2d00c200c00d50703d00e00c500054261a0013030800030383c8441d50740f4030703040300c019aa416503a00b0542055100700c0e045041c119080803a003103500f2400040c90313109502c65624070b020380304500a10721180341c80b4000a0000b400075400f09510107091602c14005010b054400d28010341c5500741d80413208085891548400049500401c00e000a42d4016858135441c803500d01041280d0360421080105140b1011406071000c22001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 597673120 1250 597671870 597671891
    0xf053d090b0d1a1806101224021314060a0c0c08250b090a05010e04110408030702040e0a080a211b020d140d0209060c07030807020f0d051b041e0e1c12 66
    0x1540c03040200c08000d50100d890040302802c8d00650310440050000702d0718802c0000d5480f00500070951250f8004018a150002034074048400c0829003000703641840412400007032102c410001500420003001c0d4142c0090003801901104041d954401000000304001510883d91482c4441c802e840c4c0908010100741d04250200e402080311006034241e00708001804980307140004050700d096803080f01c2c18480d03003029601c41604c8114000004011813005d00602002130701512000c0610070300e900b01200c0c0f035903070702c9041d0b410f90301d560401c04000303080900e42031080e0b03034184a43e80c145c000394109182c818040800102481c07140350b000a10f010b40c080b410342c1e400d80e01c2c40102c441800c02e00c2e040311511a22420701b0011030344103110480c41409808103a920600342840070300d18640c0c200000e0070311806c1e035111600e00c0301103030500c099005aa0302c00c034018464151000d0b28024955580c000b42e4241c007680e02d42e1030414031440500c00d050030b9101c4008030541c000300000c10710074081008a8060800c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 597674370 1250 597673120 597673133
    0x170d030c211104080703020411160b04080915071a01050a06030f0207060e30030a1814070e0105180601120f053d090b0d1a18061012 58
    0x400c03007201e10700070b80002d0014441c940050000166030003190100b205a5140d0305000780c501c6085229803034600040b446070301181da18035525030b1040c00703519010710340b4080c0800568103202d00ca003801118900850454180903040a06441d02900c181000b01103504080c001181340c0c03035611848040548404080401110903016103020380ea20010030b001840c0f000007599150380d401001d010051141d50901a60b66208240a03d80c0c1102e146a40b1300d50380b502c6190101400fa107100b6200400c0040340007000141c588000c0032020324400010348a0b5500b0f10f850004100010b91007a40b2400580b074080c81c0500a8030034441c0c100f5824240068116840603548014000d06003d00000501d00000c1200302030314528100c0c4140841d0210b8042d0468980c0300b844c0b040ca90384241d000c1070440c6070040c0000e03602607020744810303200142150050f01d600c1d03480c07000700000710341040d20940d51344050050500e14180c04001c6020000040c10042c6030070906100401202e101e40010700039544480401e00c480d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 597675620 1250 597674370 597674381
    0x10051e030a0c030501060810020711040b03151611010b0307210c03030302040e070314010e060f04230f01080d081015020c030c0301060b03060d020f0a170d030c21 71
    0x14002e40e4200d030701c0c2d82ca081542c003d10040c881c0c00c065005800c80040300305090700c00c0b149025070020341d80e40080c82c0d14003440b0061200c1c15400d074151140c0401c804029400002c26440703219240c030b000e498845086401801c12441d100c6d845041d0381000c840c03030100ea40101d1440c06540c0f03404110701c484480200340b02c0d44070b0b1405001402c2d800c240440482855815001401a00c0316404000e43c0e603210890308074200c4038040e03601500d05607285e005110500724030125039000800101407401da08029400103003118151100700d51030340003440c8080c00307050000c516130b54400c10f404c282c46020341c074000310a925006002101c10402c4800400100141c043c014881d0240440001ca0141e80b040b004001e0f40e5400c00e05800342c4203100b04030442185140c14001c0708180d0346220700040c10350711040b05004c404903980d441240e10400354600085207885000ba0400100b02580d104014512100308050a1141e40342400f0100341c10b20250072801ca42203480c0c42d6210180103900100007449895010007000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 597676870 1250 597675620 597675623
    0xc07030516030906030b0d02030d110f0d1812050307030507150203040b04031103130b03090a0602160b090c010e09250f0201050f0709170307120503040b10051e030a 72
    0x10300c14081ca0a1543c05500d0b10252005920b0401c0a403158808100c0c20030a80c070340003941a4440f03989189403e209049205032030002d0421620b101c3c0b1954600780c10700c0310113129100020000c19900d8984500c1058000013000312042c18001500c0701e48a49131244036180026080c04000500c0d5030800c6003074005140f03500304c84242192642482d1a11030403440003036406400080c0044440240050040100c0d202001409025000745103080d15241c2c1a401c020000010b60054810000110304c060000340b044104d0107210764125200b514241c50010405070071803100c0d500c0008420403690b04004001f6941e04100c1d4031510179500c102d00d000340381c101550001d00728140910014020340e00604000c0c56131f12180c0080c00390740e64a201c109040f060480d401c000040303100000f0000b50400408892000400c0002d6a10b050219203948110020f8500c8032000110004204020300c000c5030210303030300f00e0a42c492070ba40c8a450500081c811400c0c514401204000d01452140c56950030031602e41d11a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 597678120 1250 597676870 597676897
    0xc0207120f0b0f01060e0f011b05030d05090304150203390a06020d1d0d0c03020a170a03060b0903060105040e010605041d0c0d0b0a0f0b1e010f0509090c070305 70
    0x901d40608000003c0000380708200218492070710985d024900410780502850381a9a08881c02e4410301000119100003102507485000c01c02114105040b00d002e05407103440c1c900c1c02181c2d01c520700004c600340c01154254150840d00140044020311542c00f000c8004424100010070381c00c044401d00e088411020080102c0300c1c480d10211208000484e006030000c9500d03000c00700244111660314581030030b00d1040d0b00d001608140380b681078540c05020803c00160080c811282143c000d03a40308245042e061213000c0d061400800c801c200039905019800241040000407030a0407a41740200b40e030b503030f81030007582d02c150340f591402843c40c1400d610400c024407008200b84940f95018a81d0074003c406001c020f000c50140142c0c56506d07080411829010650002d010740e9982d4580441070000d180e49415841560388900301505150303102c1e019030042644c901038a68a0450800c0090070828101d549181404001d000303420055a505140ca40d2120403542095500c04080c9400c580501c600d10b03403035011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 597679370 1250 597678120 597678143
    0xc150b0619030b040513020616061506030b0319081903020d02130e090106031709060d050c090405180a030c0212010203010b0d0c0801120305090a0b03070c0b06040c0207120f 76
    0x7031a5068020680c205810342c0c0400041d111005d01040034040104c000e5084502003080b07601031900c03603146004844c0200d00c0040d0040484000c05418401c0342e0100300003a0700d5506407da10728003800341000100c07040c00c2505c3c0d951786c107543b600c02c240100900405000c401d200d28801031400780e01103d960552502085660340010110510403100501400402441c0d8400086480b10f0511500c01900c1e00000306c1c80140c501a07410124135405540c0c01c58002100380200c10f2030400d00e01985016140c2c3c112801c0e16145103d00b0b010895000910b50310302c1720700b24010211a04400700d4500c030995003500d02000040420300204059095029403054158030010001622420500c080c01100e04058024826412514001c6070f401e0030a00482154019410b40c01c000a805a40200654240540f00c0410260354619545e19030b00211205000b10340d440810070708000c1c120007400d500040484081106100c1544000cad5a00390f9070103062152204400d8031020b1010345a45106a15400074002c04c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 597680620 1250 597679370 597679417
    0x420010215011d061207150c0209010311100c1205090d050601141e060d09060f0606050c0106080a170a022b090e0403141303020d0f02010f0c150b06 65
    0x5000b40058140c440200340f4020401900d804100940310200e14402010500e0900d02c0001d6041c5c04d170501e05062103a22102c0c1c40040c1c0b0740048050003940500140c1e5401092001840411006041050100615401040b0010751551a0041d0204452614542b00d40c07a100c085004001c6a1001030300911501000248001030459182d4a04c981650406408140b200c4105043c00102d964940d1060050208484403c1e036588041d0350380d0f000750800310f00500c01e88141001c540c00c40e001070700098000600b00341680e0090041d00d0080503440b00030b00b904c2441e0b48400b00d4590450411382901d2000140505200b44200480115900e40f400d000d5450300c5840000300f4240e00141c801720105903000e8001400c40c1d00b000e0b030709200e45e81507110540c1d074900d0304084120a81c01442090550110303020040096140e11268502c824840c104000c20b200781400094040489041404c041213900e40002d070000d840641c2142421a495001241010001c070029905003d8142440803500b0009041d15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 597681870 1250 597680620 597680639
    0x31104080105100609060801140103062426010e04050f0f0706020d0906081f080a06050a0e0a021005090409022e0206010503071e170a14010203042001021501 69
    0x140a03041030500c0508882e031300c4105940c6505507106d02d5010403035180040180020304440301414200500d0001426038480d01c40c1e45401c510780390092408d01900b0aa1460b041c1c000408000e030400401894540c0c8102d0350b5034800b203000c14059089030002160105040110400840314500b20b0784041e22404004a00580d50b550381d14030403140144694130044001c0e5000c0e40d4100107130f60440da600b4040ba51462004c07078800713040b4141d5201124480d2000158980c0602c80c80e003c9900c03440c1c000c503d43c1010f44084007540c0036160000059048040d9140c0140c0c0c1d5569146481ea505091464440c80e403840002e0044c03108603030294102c410303021f11030081d00510701b2084c074815860b09514002a6106030480e81d6402c01d00585400d50300c05201401600924ac4510300b18860940804003006e440f0314007004a0000c0c0d01c0c030100d150303104d140c0314410400448544d05045119000031403c51605031100c401804c81c00243e003d0740c102c00e001001c05a4828000d1242c01402c6c60071800b06941d41d803e0a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 597683120 1250 597681870 597681881
    0xd0204050a0b07050d081501111c0207051e0d0b0c120c0c101104330c05060112020607020907020c1806040b01210e0f01060303020d092c06010311040801 67
    0x304c541d401154840310079140a8159103000d064035402c0d02400401d400019201503800032030f074002d01d11403203084134030502c1c58411038100c407003465024000680c40d210078891902c60284000c82c1c4103551503203500158071142e0750011b40c69040030220859840e00110099940300b2500d103900a110f201040103c00003041000342003070f07501003007180d0150301e03c40040c0013150990004895401c030204000c0018100c441103032900a040610715078001c0d8003110040e401c844250125030003190f0811492400d10030103210040c01804880c1151a000205900240840c401d0850007403240000c00e01080c00c051080014100d1040040e001100d8402681c0c8c030302002150440d038003441030b8181100750505511a962034036180b94001403000d214901490050080d0030b81e074010a8051003034200e103400b441000d0003900000c40c0660060190706104040060001c805500404020040103040c0500e0080c01458108113805041010585486820048010381840007000281200106022440c5081980701 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 597684370 1250 597683120 597683123
    0xc0706150f0e040c090b01110f0a0308100e0a020d060e04060b09061e09061203070c1e03080a08090c120723100c0203030904051f091a04020d0204050a0b07 68
    0x52268841d42e405a00203002c00448008108071006082002218020f030800c02c8500701c1410b1807900140c0d8100700742e2078141c212641c488280e01c12554881410b800043e1507800108041c0a125035504190030090001406001a810181d0004048500540c0b5510500143c414054500020304290400b20701410b0000304c8280f26446120208003a86408840a0081411260443c0084511004120441800410a41c0c01c110201e0032042c41c2841071005102c000c5c0318456601c0310b1401c0c039114840c80c010044500c0c1071413003890781c2480881c030500d058885451292a0060150341c40ca58950f00f003245114056410810701400c2212083c408900c1d24261060806201d12074052445082c15200c0514011a040304101820b04410351150b0300b40c04e4490300140440380f6080c2c10b50045000c840c82104c81040300360722000b88000c0201040003072401000c907103e051004008aa88804c040074001d048644034a5000a5541070501507405035802803c0c02001e5254140e9160342022041d401900b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 597685620 1250 597684370 597684389
    0x20a05030a0f18030e03240709060e060f0a09091b020c0406052b02030a0b01050f0d0209070e0d08070b3301030b010512010609080f061504050c070615 66
    0x8807064400100d01c15114140f546014800090500751070640e02c1104c1d80c1842038050090703041c0d0584148106500e40d422030071400342011186000ca9005001e200150441020404c01907a0400c9175910f00c020f480005d07440c5c002d140d9690b4800442603400714840e900c0f05000d6801e0603241810b11031110a9a10324040903000d680c11008603c0070082190348900460798840001800f560309100c1203514016004c8a2100041010801e50000ba1800700e000c002200e030910810018061030900005402c01c0106c162460307001481194001100d01400411140403c60080340e10201a03035030200000289412020131aa90101400d04145203402218101c440d100007810351031309851090b01c0b8004108000200c4003498200100440280054400c0f0724100720090001c401d59844180819000b84195110051041d2812008505041c01c914000e41650441e40400200700c03200c5041121000d011240000c45580b02c00040e07606024005c4003800407480e28040b0407441c2c1c0c01031007110940c4c00c400d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 597686870 1250 597685620 597685631
    0x203040f210f0206040b0409050412110606121e0307050d110c04050c12130b13030e15040e040302010e16081507110f0c040f0204230102010f020a05030a 67
    0x21000d00803440700904a042600d0504040c0700407506002481001d03070300c0101070300e19041d80d03040c01c81c406d40c000d0307003040c2c40b100c1c0e43d401800704220030480c0c15144020302d400c11042d11140f100b4195213804000b010940912190404100d429505000003a59001c80701c0d09803203a280a04c115a0341c90300403050884451107403064800007103010302c0ea1400d1303a906c07900051200710401802c0c04054900a03203161185a424000241111304050009104030f0711070030300e40c0c0610780e1400d203003900040c060a0741080b5050700d00ba840120f42c0c0414413850040060b07036002e172054400741e103011142c86582d001d00b411048142c1400308041d07041d0850f02078500d41c1030856421288543e001e1202c00b4492140e0883c0c5e034800002c0e40381107005614069805201400c05010180c0c660501c10b04040c02102090140d40001c000b20000c1d290a214480420026800c00c40c02d0508000301d41c5044e2840070005c82d2200d41003040554a40c7c401d4103c0e042407400c8240564580300e0841014010390025100740c2101820304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 597688120 1250 597686870 597686879
    0x190803130503070302090117030d05160e09130b061c050a2603070e0f0310141b03012105011401050f090c0417150f1f0807171006060203040f 62
    0x101c840136260024140380300790b4a0f00f42111928040303803048210350702003072000103070040452003034a1007500d41c200a103180c0d1911400c008c18030310781c000c0c03210703c038410680600c40c00000340a42c81080c2c0c0e5000c0a84c40aa441d1a000100005602c0b06420f0090910041903020804003003032a2620f6841102c0c001c600c03030500c051408641079014401c406154050001509880c4a804400d507040c0d0042c00703991202c000f9201282c1094401c1c503008202613110301b041044941751109051f440b22207090030030800213130742030001898401031280140d1400822400c0080011490004440c154004001c001021800c40d45103035035182480360a1180030454003006480c10000744252040c07603840a00f0b443d250420244180503d0106004002c602c200f658100c0200c48a008882c0990200c2c40140c21900d000c0a80c4201104d608e01c0750140383c0e80c1280e04000c1d5038000100c0c80e040c2c40c1286c0381a10300580b030f00306943c50040c014030440c01d21801c1010000f0125000b00040040d05da10320841010962a07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 597689370 1250 597688120 597688123
    0x50405150301050108150415030c0f0803030402030c0f150414010314040b280504080d290607171306020d0c05060c030709081221040b060f190803130503 67
    0x9100700c13400b1504030707000111014645403000050180c000d00001c0d001c03100b41d94070102c401203a0811a650389101c0402d10120f808034503d41e004200080041d032071441c1c6907010035161922490a54060040c400c50218035a0311403c0503c00718010300e40803522035541d03492000d003590000c032081e80441d151240540c0c0050000c894244503070f81181d40139900391505c400c1280d10b040104101107180802101140c0540c50740e028860065004140094403030304569400130407550001d850300407400040342c0790305001001c0556040c46d4a0100e84240c0c4074003240c01e04184071071000e4078010900701300140304885c00308445a44001c0d1409c40d404c5500715480e0708400e9030f848542c043e000e892a40901c0016001c022084000d5070300c40380d0741c47c00990f003503581c0403502d10f800e490400381680000040f420b0343c00d58100c2003001d440d040907170710302a142d810240c840800304400a082140241420350041b00c41e911044040d11000e000085124407550b902d90455803079802000740540e58500c40440081c0343e150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 597690620 1250 597689370 597689377
    0xd03050a0314070e0f060906120604060806101403120a081605040b04030807050a05010905060106020c0d08091311040807030c0f061707020708190201080f2a0f030705040515 76
    0x1d151507446001d640384e001c00001c1943e00004640c8408104034008254a98001910b01000343c81c017003030500d0812030b04201c2500e180781c018805aa009a040240c400c1c10350312840c048480f00d1404460400b2200007180c10a84106070300c542c01c1c40c00040130187c45a204580903ca0202c00020b0200c0404520301100c0903c5540b0031003100c02d00521050002c40c40f0301005019640c4100300f25074203898030795292400d607910500151348a40010300108a520340500101101403003c40b550041c0704c9880d41c50b14050b002d590940c5c1e010308071442c503034101c00500758400b070f10007041d2080031511542ea440840c0c0c3d0310401404200d0b4030900355840007480210b031620030801c1c1c91081c3c17a050013039100b82d0780c8040000802024582148110980025a01c20502088440b01d555006511080043e03000240c14048050460340f5400c800b44100803400035004003180c403040768400c448422007080c0c44403400350301941800b000b10610001c2030103083d5402c14010021503038250344025414800901e4801c40e0b02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 597691870 1250 597690620 597690631
    0x603020a2304090221100e072408010918051c0e0607080a081306090501140f061503070212040e040620031306110a0f02160311040e0c0d03050a0314 65
    0x40704d03040046240340450141704114490304101c0d080e4030310074204181510304152040d00c1d07607082001c06005204085165160803001d580002140c010b045c0790041084805228200c00703503a0300c80c0168400203d003e122840c040c0c000c0101d40c07115009080b4418a002010300c00c90126262001303807030940c04d0040a03645490f4001303100c541043c00c40c12007522200c20040115807081120700569000503103600c01c80c00458010700001405000c40741d0040030088014010303450f200e18a1f420400076a0b89c15440c030040780c640c89200e0303481e030300c1c2c0c03103801e030321b80002100030303c0c1132a00c040750104503c1500381c21244250b0155406024101207040603505d20b40280c000c0450709501000001c0000b410024090807542c410b40c40021b001605c00040c1d4059000b059201d80003031110f8030b008403e60307410020344140e010309007000e03500c1904e55a55040d0400103110190701840d103403984810310030740070b1020608240001d45500b54002c003070b141c02040390b8024201c0d0008a45082c103904854a41c84110501c100d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 597693120 1250 597691870 597691879
    0x20d050f011215020d0b0d031805060309030712120c081015050a0c0510090807020a05040506060403061e060608040311030414040218030115030611070203061303030603020a23040902 80
    0x3c4000c03024483c003a40c0400b0140c040d103919005200080e40f240385441c80e04c640a5501c6041408282c201c11012503060390105100300424014814a510080100c2d050160b00058141458114980664004450010340d0100a1402034080301198000c560644661324646100c408075842d0b8404030030f000c1e41c81200ea80020024040090918095074803007110038091022685590703824040c030000c0d0740f4070050484d420344000c2019001c50409841a40c0580b804071014006440c01001240c450300079448003505240d19014a40c4e04052200c185010700020840240081500e40c2c90280400c8030030b440440c00a110b0f011118900e200202c25034045d21140c1d2225559881d9503403c000194000c5036110092040d030071600750b00703a40d0034451401e04901c010380038460a0310f1030a060084810310003501c0107150040101e0030042e580480e01c0c0c3c3c4e00c0101e24a442d8410b60b040d0604400511445c2c0000390001c0311060080340101110f0000201200c0c0c2c04102240c000403001880700b80c0700c0b6403400030b400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 597694370 1250 597693120 597693143
    0x9090c0510020307022419020607021c030b010c020303040e09250501080a0213080f010e01050c0904091a0702010b0405060d030f080901020d1a120a0c031203060801020d050f0112 78
    0x40c54500100310a460350444803c0c010140d100307a22046d0303401510103110110070369000415494041c041030768840c0c0503001030010301c0306540003140380100d000da901e0101035452401202c203a004410783d0030665000b5040743d840310b4644002000c220700650f000800c40c030540c540501640b54818900500e0070203512007086440c9407100554040f080600064001d81d02401001260140001441d00074201b010041c012408025451401c50342d00c0d01e0440340c40c1e4189030802c080303ca0140f048490050003501c00007003520403030070400320504cbc01098120382e20700360400744401c40340c1c150040c18010200301e8007002141c41c2c503001c001102207000c5009000c25100000f01c05c600e405180c90070f60008814002514060141100e070040725201e1300c0ca041052100042c8072403600b004d00d120410782600000070088804180c86d1081c0d0320589100042041c404242c02c981c00c54480d4011070b0040014500a644500c1220b00d00c9010380b80c100c4004403a00031600000a104406598559219401c6040c8542 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 597695620 1250 597694370 597694373
    0x307030305180303100f0b04081c050f030108010603060f0507020c1519020a120503060a09180602030114090a0612150b06190f03020a171003020402030109090c0510020307 75
    0x9000002d00403050552580700030401c1c0d650900c0254481c5520941c1400c00d5410201000e0384215a60003064500d5800d010134032200f90000358a5003c04841002c4101102801c1c9040300c03148141072502c1a00c0002000001d1040415000700c001c0da48150310610001080c044c0d90012035208031607020040e840880d42010303900701000c441c002c502124840303c1c074002590075580c0810300c0002d010801a44005113400a00c220351600405078031040c40d003603140d400c101e40000c101c034400d40981c4074010f03655a60502800d400c500400c003095440b4406640b650703550034045800101c1021a2401401d54000140305210302d8410038040c0d41c48260720f045088502e07180c044801d8086402c03040b00a64500c16040c80d47e848402070041030482c10100b01010040403001004520410002070606005020b142d03c1070b6006400304140100000c01e104035aa41c42d0b1004100da0101c1c1d0019400034030000c008640d10310a900704058083c0510054005107079540705110910302031f80c0b203032030050302305210860 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 597696870 1250 597695620 597695627
    0x215030612010e030705060a05090a141006090605043e0c030f1c1b0c051f0209040c051e07080705010507030207030e01180612061a09090612030703 65
    0x103030044800360141c41401d414104107400c55024a071441840d6001007580350070070a04001c3c0713651080e100e0009205608100d074546580c0c100c1c0382d0000f040700c44e000c040d204000d081000340614030010104284540c503540c400403002001c5030f00405005d203003810003048810800c0308031407403080c241c0900000001590840d1480e40100e02c185804609401c000040441000304040c09500c107904032143d95480ca91402c2200c0410000d10700a00d0b28180b10001b84043ca035200128040e506038100b000750242540742c21070520f103901c0c0c00700ca2003106805105540c84200d9010f400201401d0341d08000301003130302e40183c0d50b600545141500203803400c588045050380350400350894920620220742050059510b550a4540c00c0700d00c0000260302040c52400d040c0c2c08034422000c148203003820021454420101a80041d06003c0c0c00c0a00180886101d01408660301c02c100070131100c1103100124090302c04034216540810b0003544102e80450106e0003c0c07030701455861400c02c40d18001c43c9415066901503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 597698120 1250 597696870 597696877
    0x309030209060d05060a0c021203040c0f1505070303090206090904030903020307060e030703080a020a02030a110f0a0608070c0c1502031b12070f030c0c1401080708091b0a1a0a12090215 81
    0x42c01103010b100c000703510511271036006e140140e1081600204440c100706413400f1081807584002c68414510440240858100c0c0445840b04d0b090320700490f0000f40d50010664500c0b8402580303811064400401c01410350120740201920710031000c0d1b600300741e600c901c1180c14034180000a80e054024040410002e00350f54010312642402c0d00540f84240701580009007040c00200042e14040707074840c400d04071031400340f00f0380302e030408229003a018880c00c0100c002d046420081224060081c1c100760701c424040140c060100030700413001809100c0130040b03002503ca4101e41071010720704044800010002e600401d401020b5420881450304083c0b41d511007460103110f80f90180c040c014500d0b0903030080350780c4400b44000b8201000303580c914051000001091250011b00400c100207400f001d11604810120b045004031044052054288400c3c80000b5a400015802101c26080d2804990030072000703240604420701030354071400c50700c0b0103100b42c00382540c3c0c801000950007000001070014040200d40603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 597699370 1250 597698120 597698141
    0x1005010c05100510060e0901030f02060315030709140a05010305030a0507060b060f07050f010b010816121803080903130608130501060609090606031e020a17040309030209060d05060a 80
    0x2c5032040c40e10003038648112072040c0d54041c0b034041114020b008054200c5a03080d0409826100c040245d89907482e4810408024030b8000d00c5039100001080c60b0f11040540701003041c10080584000a55442c101c50080021400740304400312510300141c5d005105215060480c0e820001451501150300c50450341c46d07000d031004a8603103940307415030410741e10f8039005070101500b01821180d0312409828540c0c5400402180c50001d40c0c1421004d4034079980c4411420b40054484005294583c9224001d0350313055401000f18810614124812130316143e060500c0010501a44904c3c450340c0382e202e1131544900c981c41108000001c8280200080c511032041135612001a4080c152122341c650340d85801c4d29040c0c1d02c41c1c80019940182446038082920038000280400e0030300300030101d00c821219500c4102c5e0800c01c0d0303038280e0118105580c1405a5607540d90740603041c0000240d0b10f49403901401940c402d0100b40c6c024020300e170004420b42003062980007025041001416195502c1c1e9041c030180c0342001e40c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 597700620 1250 597699370 597699373
    0x40e070e031005070e1f0c08130810090c0e01030b04030e0109030f06050f0c040501271a2503081f0906060201021b0c0603010b07062d0b06031005010c05 67
    0x580180040c50310566024404c0c5070388411803009a00204612000d448900312464684003034580045a000400c10810550085455440e20420480070703c80318480c0e0302000e014018000e010b014107200d070380006002c41c80740c401581c6180d102c1800259005003408004c01c4650a040800c0100303019201a4800c400c05244c1041d80030707165920070aa08100c800101c0d0f03c961100140081607000041c00c61f40200398020540c1401d1422000902143c0031080c0400c44010f01c2002400c401c686034070341760140840e800325499040401804060035401032000542c1c0f0707096403150108003454800840c0046070035a42c2c170a1243ca030940405007a04008504003200a0301081c0010b420b0071034000c1780700400d8281c000507190050281c81800181c4c0c2d40d14441801c0c2c0105442c0102e5940781c40c10340e410f5600d0b07400c2d8036403112242d1501c0001072525a0180681003200f0501601c42c44201e804e401f100d00381030a003404100d0310941880b0650100390703540f00303c036910083c0500c0305520a649441e076550280b030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 597701870 1250 597700620 597700633
    0x609060a02010b0a0608070e01030921110c04060b1c1d03040303080c1218100f0209180f1506130321090b040608070519020d1202040e070e03 62
    0x1000941a40e21500003240075035101c110382c000618144c580000104014101b00880340b80101c1c006222400350080c0606241d6594800c03801d0001507415a90781c2e00103d410840300444c7c40b0000303031007541c107190301000314070840041ca5141d05042c0264421503070a03d001500f80084650100200155020103070010365448006090304e00e0284000a820140750740550f903501c3c00c40c1002084d0500050801c800804200301d1281c414502e001c210740d000000f41e002c024001c9641c0110b07410010050590781e1418202103003203041c02a03550040c940d80c001210404103110381d01d2020000c01004494200d114030114000035001c1e0312a407104600d0010040003a0b107000700d4804000c2d1516059001980c07403428071760313554030700b40b4240400a08942a50525008651034812808641d1141d40100810041c041010411031405102503c100c8c0b401034903081614800084000e540e90040c9840c07000290b0705030201724000d134880c42200d0036900c488054002c84c2c0d9884405551400003421090340511419 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 597703120 1250 597701870 597701887
    0x20910081f0e1f110721090f060203040e0105030606030c1005040905040f0b01080610030f020111010c1701060504050f10050408030d06032003150406020415020a1a010f0e0606 77
    0x288030b01e540c0703420030343d912090342c045102c1410101d403a00722038800c0030b02d0304104510110f0300d60990404e030030042c04610804510380e441c0c101c9405082e54041d00c007850b41d6000c04a031040d0040050000c0e52500110b444035070303a8900406a41d200160f80c0c1d44c1e0160040b030b440800c00d0a001d4400050300c1014140703607141031307960300794001110302c1100c0903070f04450f034420701c00c1c1080b8000050078010543c43c4002c024905001e024888a0040d138803004bc400b6990510340f104690064441e4018940d0750303002040403100500000d801b12005010307004800c100c40001150313160281c41902d0503030300080c000780510b020b003a0903c1b15220302001441c051180034003001a0a45d801c000400600700c0003034020803460b1840c984001a850305080d0024440000c14240c41251000550300102010782e40901c074154441c0d0400400038415a00004140c1c14480c40d40070425400040346100540308041206520411000c60340d007140080c0510b82c05040329800410009200c0c0030a1500120010107030352070301000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 597704370 1250 597703120 597703123
    0x2107120509130603020312130b03040f080c0d0905030304180f02070f03021c0c020625140a05070b040311120c0d1a1803090d050114090307020910081f0e 67
    0x72094200041502c8090038400c60a0502405000b035003903034012402c09010242c0e0b640c07005849d0041c0b0b0741118010001805028401001c103840c00c3c2c022035850365540c51091000c0d180c12074a1002004070380d00000000707482c18000202c90032280320b4104080403c00034110400948006558014215024891900131541003070003c01c0e1030340b00e80c005000055001400729201105500740c54180b00440e500340740982c540104a8014040c100032a40a524030700d161202c004000741405440d95181c5407061000d07904c00500300c215940910f04556089559421800036031207640002014000000703000541400c1124042c503214603d40184c4101a01c0c05010410380c055a00c420380c0d103640c0c13042083d004503000e1400c550300501160021318070311035846441a5203100b4019070a006000c00100c500c1400341c20b50182c414142c0c060705041c450700340300360005d54940050300140e01c03030b00301d10000c120390300150481082143c860401510012441c542541440030110030070150301c6490f07000070605040e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 597705620 1250 597704370 597704389
    0x302040b0102211810090e0106030c1202070201020a0f0506060301060e06032808131502031908060103140c0702040c05160308040206070b13060e01060b1804061a0c2107120509 77
    0x1540d0300006c031817400700c4207200303524182e2040c4185490300702c028090561013004203401031065400541d071030701c8510040f0724040c04400041c0c800c1d00440001070800c240406c84901411045009100050300d46016407490034058504a5256001c081d43c4e030194054034088060140c6004400e408900c1030780c07941e05841d40240c2031030308805c488442c148003c100110042d007181503103100850030b1508100d104280b0103800d11b50740060050400010b00b0b581c0c401d400900307100c0340f0008042c01031300300250103120540003804c040303200764244840c040500f4440e1068902c0c140c80360390f80c81b610403182e842c1580c4a08018100780d800c02c108014020200341e56807110f600800a01440c441ba540745402d210f07041b103000d05003042d1181d0500200304034204560050b00c4c0e0b0300c91141c40692a019100001030000e0180e0360100d1741d482c940040d5000c904900c0801b40091000b010180e9840c604207002455011508a001410810702885020041400c1140305440f0622509002d4078004051000826044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 597706870 1250 597705620 597705649
    0x18150902131b0c0503031f1a210f19021303051e0111091210091a0f24030106091b090e090d0c030207090f060302040b01022118 56
    0x5884500c0075003000049110b1440319800ca20744241114226560b103a2248405040c0d039003001c0c848400400664080d049046c0200490f6540022200c418107450420360030140790f50340e030f00c5003200f0002036880c620311815200380c0303901c400d4603c00d58402111f002081001d01416140715401d0110320103800d080011000558094001000210b5154030640c110050005003032003039904088180b207064044401703580c19080d00b1503651414141d02031403030741303083c0595500055a41c21301c0e20b880248000b01c0e0310310812503d0101290303119656a42031542114055842028020011003410b4050055140711030b500c00009002069090f6601303098825580d00c190300fa5001a107001509107a29040100c1400410360ba0016071564600898441d8072500310060003428040490308a00c02c00d4428442d500107882c0d10036040000001d07003004040202403c0c08100c3c043c0d4030300540790480d980002928900c1030260000941c519203504a490100c0d0801842d00400d500e00f29a0403a2980c0c03101d81049801c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 597708120 1250 597706870 597706909
    0x21f051006081b0d0614010c0503092707030b15040501080f13060f2405151e04080d0e040b0d030e0f060403060912080708010306052710050a18150902 66
    0x117a080450b01c6240340c01c01c01080d4180010040c43d10006040401900d02e4407170b040720500310218041940d00d00404c01c0c820315100072441013080144958141e400b604941000b52440c00042c203a42061107240d20a030301410f40414005000074000f0b05402c4000703a8484684452038600207080e50300c0005072050603101c0030301c00b030b1105400030720844e41169071401d810340101076a403a14500300104410082c204c0d82c440c101c00000442e1682e54444204c038140c151090469190b03100d54030b21501d9180c0c4100d454400000310124055006454240201d45100314001c22a460a40d00b55a003510f110300301c211282e802c0403901714030f41840d40d51080640000c0d8001c04000c00c2d9040c4500c1c04100c500c2e1076401c9142032200c07260502c21150303444200c080c15640d105000103100e880342c181c66001034081ca42c035502081d100d0006003502000101c2c2fa58582c4095010510498448480410a0b10621507800042404103080b40c0042003041e1881c1d0303200c01200390300090707980c0944c0120300000306403c07083c0b468 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 597709370 1250 597708120 597708131
    0x10302040507180504020711060c0f10140708040512070b0a0f0905061605132904080a0f060f06030f1202190b041110021f051006081b0d 60
    0x560805004590b0b00c80003e2400c0b2881c18a10303142e00b00c4108aa004103400f4540c0480c000e000c01c0420084840301590041c40b0b25122a04160100d55403408860111540d0141840b407480c0d041c2680941031040c55180f030110603554451100701c8800000400035a15480361b011047d01c000441170040251600440110105180c202552400e981743c4402c0100c10601e8084d201001c0342c0045031094000240c40035424030400804d004480c1402464182101407003030300d000003400b82d840c41021201030203a0400c24004624915411005d0165100318402a00214420400076492900350b0048600c1441c0c0094034003080c3c1c50650884540b03420484440f40d1031207058052060003075104c0d440c140d80c1d20050405400d2550400c00505031920300518000342c1d4408035040000f10f40c461540184050000c14119217a000020356407504800540d1411240c90b00d40c1d580c0034024000e40744510b090420f000181860304a0481d01204c0040c2003500c0100f0522002d411030090030010551a2100c00740801d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 597710620 1250 597709370 597709373
    0x219091a06190233090708030415030b18091b0114090411030106080601170405031b0a05061f080c09070503041a160e1020070e0a09030306050130020c0d080103 70
    0xc002c1406480717045550b11001d03041006d05000030407201038400c070b60810704001802001c01c0d009820310003080799021101c001d1240300c03001d03190300c0c151144031207034210303a4074500e101388030783e15072450f006001d00050608459440290034000184646c0c1805000014011581800007080380c100b0703008000000e0341e04051185a40c1d00840c4040030001281052443c1e080c1551066620300c6240320703d01d030000d41c50f000180c0c0700c2c0f0284030003034402c0d40207003e855092030290003d0303000c0401c1010010404c0c0c003c074004503a9440009070408500f10103041c1d40e506444002040c2c2d01508018012602030004082060296503884a603c4c001c0e48120418113501c42e42c000098210844800b1190046036003400c40901540d001c000401d42c07580c000388440c0340b0b400d4805c44c9070420083c0e03001031100742c000781c0502180c0c840c0790303206950b0580260740c2085100d85940044422280e10952000311409504002c00140321038004c219144090700720051900c42052052810202c100c20f1610125149000410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 597711870 1250 597710620 597710713
    0x40f0201020705060307080619150201060501080a0c02070b09030715020706022103151c030518010f021e07030b0a150501022a04090219091a061902 65
    0x1028003c1250f1181c10b51800400c0104907500c010001c038440d0201e0300c0b41a940d900c0c900000030180c001109201d0724503044400c0a4060101846003a00081e4814000b8550b010700f8030803e0b5841c03d040d40070742a0249003116444c043c0d00825209545401036202c00a0450380303003820041c42c06529005820828680040a800c08502c0c0402c0384100c3d4500320b1210401640c40200c0b030b0320001601c42030001c48007400208071912502c01400000081a215100c1819049406031002414003000c4400e1101e10000468440003035808000150707101e0998801042a80800e2801440b126030031200460b5a9454548003000e095890014444e079885507882c807a48909981c101600080c001021201c1c032003c06120301c000d0507401e05120034031111004a031030361907802107001d0a800404602c0801c504501040042607507110f0041202d1401c00300281c4010035414100ca0240014482d40c20700340c0c1c2c4591200018a403400550840c02455040d00a44c1c6024000703404048040803c5e00e82c94200c0f0a880c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 597713120 1250 597711870 597711883
    0x30f021207081f18030f1707030f06080c0a061b02040c11010506040b150a02010204080307030228020603040b0c091f11061003060b2101090611070203101e05040f020102 74
    0x244403035090078074a50108a4800808440980c94130300006ca805060504550403c0442c1080c0021403c0e6814440500d43c16005413440d8000040e00b049265920504255903141e50000e454004030204010040e0500425100010090428080581c52090b40c0007508881d141d41c0316902050080c0c800411503482446801d510904c02c0d2402c105103000140040c06c200f143c4505212041400a94014428400c0d015600100310804c1242d0303c9801616010352500341e49111360241d00c0b1190010380d40c2d80a210484000c10350068007451441d1100d884046403084000c00c00c403030320f0a0401503600551160103d030100900c902440311004010311034020019040d8a95501d8942c0c4030205015009212304c025400704d0f9031040000a001d00040c001c250941ca02c9804184c40c1c0c2441401482c5001d019005800550310807941041401c030f01044401c0f05004442c406501944802080111201240d10400074031040c1002085208083d81d80c500035213400f00e0f0202c9050301145810411542c040215 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 597714370 1250 597713120 597713173
    0x1d01090f02030417030601020709061410020d0e011206030206120f010812120a06180905010b0405161107052e080f1b0d0203240303040f030f02120708 66
    0x79440c0d8100b580790039500c03001c0c10104080d0740c0c1002000c16840d03802081010003e01170303e0320a201890b5107229800749a600f00b101c05010b0191b00414251051000c50b10360242c4242d5110b40343d0f08105000110b44000502d0300100d506c039038411000c00075035030381c9002d811100d000e003c9140d0780d45403130b5481042e050786c181d00900d825030002040d600100c100390309a524141500310104c6403552400e903080c020308120f500c94031860b00d0030100320700007141e40c0c0c20100c2010f001d14028018103140b0800c2c0400c80d007080b03c00382c55000105202c1c00b80544107280720601d50b06100d0032140d0031600c620000340b040e10a0411050001c02c0030703d541000d041c2e801e2078002141c1085c10601c0389840c00101801c5050740081441d120002c5042c08900d030182d001055400060036210115100c1c50103625a121481d20002c00d110000c41c240f000702c840b403900004440139075130b03a0030507010384d1742c0740d940c40d1150b4100580e800c80c0d000c80c8118510107903120400058009040070300c0140b40741e42003080e0018414000241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 597715620 1250 597714370 597714401
    0x3090f0c031f1e060602030a08090c060403021012020f1206060a050f130e100302040b03120d0b2d0907110309060c1609060f05011d100203041d0109 65
    0x203200c01c07003041124004028944000040350310281d21891a40146140303c211076070a01c3c1480106885a00002a1001d405981c951181c1d54507400280b960720000403024642c02a0200814001820642c41e05044500ba90a1850724801c22120360f02c01e0780c002c0c140c0d0b200c02c1500491000c040070084603500c0e401040c00d13100280b50482920340208a4400c690a403003482c04001940960b040c11040350700014411b0940281060500e0134000d01640070031701c8284e200790b0904584e03004a20340810b0003032022283c01d164a140007030006401c07020f0b245041a850f4441c61000003108030301c490000d8031340340042c86800300844110345020480302e0b0602404523410045070074891905507400004560140404658158460b030140c21203618004441090407600008003900280a10994006c03800340c80740c0d00740c1d1030680741d10380d4011902c1c1850411b40131502458002c1685060508990754a5080c1c59417069034a00740d00c503487c0d0404a811808614003c07501d640c010080c1d1401c0748a5800800040702 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 597716870 1250 597715620 597715633
    0x90f110a1d0a020a09091e05010503030c1c1b05030c011817030c090607050f0706030c020303012306030f15040b0102060f0c04090603030c0b07030203010312080c0f03090f0c03 77
    0x850308400d80380040c24070380c103241d0000300d0004d400d00610600f0020b080090b000e000d03802456460500740301d00140400b865908101c0045110b1401000391007c8090000040c0510f89402281040310b0820f0310080c0184060303000182880c10044d0341c40d4000d180034200550740c0d4030004401d00d003100d152100b40d4010382c01002c2c2e5200024944402d81c1c0611a00045aa840c1d40f200416940e49200d080940741d4000000280e01003003180100341c034148640020181d8000540c0c9403030a030b0a03120700ca8a00300041c1c000300014003072039010001000c101451801400700c9060104080798265005407500b00543c0704032010049081ca0002480c103c04405540c140110101d41e00040d5840002412802041c0311030800550103164400c151801840606820701c1260798070304000c0d10b161103450054900e4440e17507000039681c0c2d01900880e812264440080b6490781002c1100329144007020b480f1242022080010b00910421600510b00540c6500060400080103008840c608400c00e24403d01030340046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 597718120 1250 597716870 597716909
    0xd020d23010b1605010f0203090120090d02061b0313081c0f110c060d151d06090414010501030b15030d080c0a0504090204060806120c0906010e0301090f110a 69
    0x141950a0700031a00101c3c40008103500d861405040800e000a074220300c00b00401c40e050710305400012442c3c0c0034000903256411054540f00c1d1a10400c9440c5800544006c051001810aa0014440801201c2032020345840c071403446030540d0700500700700300c01003880072081c000380c1014803801c01c1318180b022128450300030b0744001501015965080d1824000e07540500b0480e95030501c03150b650010010001544c81d410003482400822851040c3c0c510301d03541c80b001141c0800c6ca0380c00c00654441e20401410560781d0f440400c03aa0450044c4215007178a8145400001000240105406103100300a11005450101c2c0d11420005030641e1151185d400f551200301015041203180d0303005040c070300c0201e40e5442c1280b03007610309208035030013003000900c00200010060351120000c0e0144504071103540141c0701e98103035079680d00d20013080795a00104c0780e80412101d6001e40070b4a84641e4000c0c00102d03040c0c1064413040748114a1000c00c0c0e413183c16900e082c3e005458004000303005010030008085614814 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 597719370 1250 597718120 597718139
    0x9090309101d0d0c06170103110d170f0d05150a1a0403080d1d120a050a0e0d230f060114040204031e11010906050a03110d020d2301 58
    0x301803200040c0003902c499001d9003010b50595100141d0081d100d02e0510140e07160a40c02c000307980c858038001489201c0100d1403d0b0360040e805040b03d410446e40c1d042214081c0401600e008007400845410103a01141e1604144410150803d60003140d1550b4541c000c4802c1141510001044103c41c00422005144142e8446c08501e090b03459003002c501444d0025807415565101d10b400140c030180000c91445800041e40d08031400e40c1c90744d0b6900f00100301000c00080e07a5030300800746076408680240215019284a40b01902c0e240d000ca00d000d61000c13078040042843c0d02c8400c907054404410400d0070680c0300f04100035034180d000e81d11009001c65840003414035103030300f018069a1040421110022005c5e5601e40540b0081d41d0000d032032024030810140c52024010314460121742e002c10300c041203480d660144c584c8100701c4516480c0c143c503044c24440c048008102141489800600522500b40740551a102504081d00f05080001c0d210f803c8641e40c0c1002ea10405021045850300001841044034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 597720620 1250 597719370 597719389
    0x30109020a090f0f1d130609150e2b0c03050f040306020c0319141c020705032803020f03060108090703050613142b090e10050111010c020712080903060a02040509090309 74
    0x81105000901800a14212780651204035440480d40c1c1849000c444030300c00481c2c10325416070b40c101c0b034407068030800c07040c0360b040e40e00f40d1030860100d0400b03607900c03012900810080c1400781c5000106403406071244d44a004981110b80384524a07400400c5002d1070200241d03070010a02000d0a00211031440c50f10390f00c540d44140304402d003111429081303140703d100e82c0b901580c40140e40071044d01c0c0c445103145012400c401000c10a42210740c04829801070150191089400c007001202805103980e403007000545440102900c404403512a00707200001288040c0328080c01444181d02c801c0e2441500d04019002d410702192007040c942220071050b1b403002d5009a000100e04015209085203100004103440b050040d50004540031000020049503048500c8501c1c1a00d0098031040588804c10344141d08076005030000300c015070f11480d03047c0228100403407101e1049100b801d03124136083c54040800c1c00c00000391950900c4039000309040c0101e14000a1440e030022101d4002c500304a680c900144081e00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 597721870 1250 597720620 597720623
    0x809070302100e010909060305010b130b060301150c02040c021609060e1b040f08030901030f0c0c141204090b12240c0702030105041b0909020303030109020a090f0f1d13 74
    0x14800880002d9001d545d200c0000e104252082101503920300f40140a05a400000d51082070030241c09142104144550080080d000e80f0340d900f5a0f00744002c04402802506c940400d000350500f0480c0182e9650282811400e4a0b902030200d41d54603d500001c00314a5070022414603040940910440d40c0c40c0d6a043d6010050f41000886a040d40503e45003030310541c0c0182c02c5005004501140c107040001c010484041c0aa07020070031941e4509816003196440100c000000b81000310381800b080c0c1100102155128403021b80d036520402c3d0080e0354895106034401d4003419101c3d002d41040d403409610254100e404540949504a00861030860060745c4901e142010780d401030104001005401c166a051940500200030070306160411a0070341d0080c4440d200d6010803908085001c900301c0c040c82e031806902900542c2180d08000d803e80194100082d41c004000d40c400c03000421800c0814414010890507924046090a1404400c041e1009a000d03030201240c08003800320010b24541b128a04e036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 597723120 1250 597721870 597721877
    0x20c041a060f1b030f130e040206070f020f040f06050a06020609060f040609120509090c040b0708070203010f090309091401061d010c1b291b07030b16080907030210 72
    0x2d07200f0f0201d841c80c06580801614541c403000c41d1462108904400030110b0305149001e036401c4030341e01d5407219060302080318000c2d00b05100b409480000b035000e82c108410039200800c42054600d8180108013250000130950944981f2075004021504240048101804003880504074901d0011140d60780c681020300341240000840001509008841c1c1c80f20221640c04280e048081c20182e0008160340c100749500c900c02c24408000c43e1b000c0f41030344219402c86480360000d9017024003d0325000100c1d00203642c166003654841d100c1410306506441a480c0b803920a07121484003a0400074180111840d41c003889620f207020500500c01c40c0d4010f00300107002e44010000308174020852004070340c0040652401005560050100c4201c0303098900d0030025148904156034428489480c19405950800a00c4100400030841046101003800b1100249920313a03040750740e529525640c5014094040b66034202101c0d055400c6603610341c0c000d10035904003091030300800c901410743d0009031b1554121072410050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 597724370 1250 597723120 597723127
    0x150b0906010f0c0b0103080904050a0905100c0509090a2406020c060a110f0f0c010e13051003050d18120b0a02031512030403050d0503010b03190b030d020c041a060f 72
    0x3144150f2080f002e66501810780c19507542e480c90140303c1500b01a0070644101d050500141001c1441c0c481c0d592031f183c0080007045019818211078004140f440881001c04c074040101240e2616000801d6000e80c00e03410000607140704007070701443c4172401c001d0b242c4000c4130401d0080281642c0091b28181040007210840d50b6007090350015200078440301207101d1680501100381c80c20400228a00745021006e2042c0d403020700341d40d00119802d01c102000d440d40091001c0c8991400e811552140303510180402442098a4484e1a001d01c4d2000a43d07d10700001e40302d00100c030b0780c801d011040200400c80b000444842800641d50034001c45001011060801c1e030100010344a170004150782003d000024003100110f0100070319a0f07480f54010b0005a17203030300c10f03000700540e0148910100c9040b12603000c252403c589884211041a2005490003c800b5445e8211650241c0c0c0a01485d9800c04854000700002001281403100fa9040c0c0e50900e8134842a40004910503200c4200312411f40c0507610450f5039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 597725620 1250 597724370 597724397
    0x405010e121b0d02090a271515031b050a05180402090a1b0206090106060e09040303020f1e0309010c09050102030a0c05120c060708010e01030305072418150b090601 72
    0x121400c14800130794003002e61014400c01c0c0d070895110601c0d0000c10045600c000c13441460240820229060080c00d031030354103540f10351071101644501e111901e0f0210320200700c1e5490300c0304401c4885015030b07d213600c100d1203001c0042d840c115904400402c4190749281312603511b070804421400c0c1c000d00182c080c1c0301c0000041c1c080d078031075030044652140c0c80000104c407820001002307660b400100c0d04540d1640c60880c022400c6402a00945206900100b00c159250754a50342180a90010150400303112414801c544140039008086416011070044503a12440c0884800d825100c540f03c13800280400034005000c140d074040122402980700d4103003803000c101103240c402d10300310348482203050b041e5000c81c444080500100d4400d0144400d959004180d9880350502c01da042c03000e2000402107a020462880002c1c044415490042058246441c043c2034000e06030341a521540d208100c041400350b052010800034601d88069242d04110400826045d080400e00c040c8014001318103100c0348801260 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 597726870 1250 597725620 597725629
    0x31e020c131805101a1c02120a0c090e0c01030e070b070c050301230709080703170c0d02011d010203040b0a0506060d15090509030a140c070512030405010e121b 70
    0x2030319564000103ca0020030313140900c40c01008000c64142840352039802e14466454107420111030b12182100b800c0b0000701d40d0b400c020510350f0285000505009602080c0b02203148040f01000030032070500049002d6942c480503070704019960794040e0515240a405c040d041d140040c0240503205c45048185d60b9911a0820907485445a4045681903003030000052014070103c60039440c2c042040c00080b5103480d1041c00780c8810406010300450360740b00f40810004503200c002180c0ca10702504070aa40392590200b10b007801c1c00021000c00025039110644000101d0901c500506405074501c021400e604080d92580d003d0440074100207401c940f1030b0041582c1e41d41c0c40080f01d58007800704d0010840c4841c00140007094000e14031405010601e02400600c01810120032240c160700f80d03581c2c142403074200403202c40d91a0880c550f080004d11a140c2c0215250b12012410b03403a280039003008503140d5107080300050248102d00341240c001d80700c0740700e24480000e000031104001e0302c030620a5010028000f000c038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 597728120 1250 597726870 597726911
    0xc0c090227120106080d0e06070b0601080408040914040506090c220b09041a01060309022206151106010b0403150c0219080a0306050103020906120c16031e020c13 71
    0x690b06510700b102c00296074400103524121b00c0aa901e90382c8110010404100c0c0c4c40c010400c02501c00308400300062517a40c0300d01105030f40a48212112030400d40c450000d80f044403104141048446079150500080c0601080790380c2c0c2c0700161100404240c01100045040031800340741e1254401c140c00307202c004845841c0c20203142e0280252400c1038a107000d0900e10110700c0000e05c900304540e6044004120107100e03005400e182c2d074000e0088212801600142d08440b1280019056003503500c09021400002060b103070488190ba0782e80315030400340c08514507414000107034806003808400700020000195500000010710040040000e003490024500340d0030456081c02a40410f1a1180322000b0801c46002030240d8420700c0c0d074200541a22840190100e118810350b683d84128180400c0700c10103240003905030b0000c2d1105015080c0062482641254140240c2c1240401c9604030048603d5810450016130b80b215440181481c0c54036202041410803154100400d071a00e5603400450b070481e00001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 597729370 1250 597728120 597728149
    0x90c121c0503160807140702030a0206180108060d0308040308091c030e0607080103020616030e0301050c270d0312020c07030606050a0b0c0c0d031403070c0c090227 72
    0x1601448088100040195004403089900b0b142081000c01d000e44c82001d46510130120b40c0c80348642110303905050425a0814102242e1612075540c0d284016100c910181c0100085d0140e045c2c0c28207185400500600001040540144880c50a64002c079510941140d00240c2604281d8125210001540d040001c0c0d110070b0840e1040c40700061b803200d40d143e800083e8075000c600944e074158603002c0e03040320700c4002032101039400441440382a0f05820a21020500c20344213040030040700c0786200100303094407070850310340c003070b150300860b00000c80c0020460b900c50850340c0304c60180b800e002c0e000004818103160803002d0104082e05a241c0d24903415a41201c4121400d00202c1e014242d581ca400400390405028543c0140140e0f88001206251203080d150103140d4040075103c802c56400a2201c4149104026010031064001d09042042000001c5000d4019a43d80841003086401c09408410703156100c0e00e421441000b41405040401325001d02841c8294050303440c00100340000f40781000711015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 597730620 1250 597729370 597729403
    0x210090e0103380c0d02070b010f0338180a060501090b060a21200304120c050c04050711010608010203010519210c03060e1f05090c12 59
    0x80140031035044401c807100c000703810410481034900b1080c08200a4980681c0040f40400003040824000c04e019003c001d1481d9001400c000c0c540c1c0361100d8240c420703400f1000c0080819014001d07c4240c40704024606030100098070b560305d00b07140004110f17100c0c2e00130366060b0380030001042111003620003a100208407030301110121b441d00c0c245600101400c0c800d108800b450701018207007904200054886900f095203e8a05410030b604548040c206030000009203580c4c2c40c1c42810512040007c01e40e81d101c0b21112094480c986440e084080c15070560880042c01030182101000507030000e0180800f07641039070046072a48130b0000507a01c4401503080ba132015401d050010416200c1580558122241140e18a800301c8001400c4c0b000b10056001c2c0c114042d8000014401c0c000d41c0314030f134444651046181043e400c1c0c1d20b03100d8a040703802510b0000300750341006600581005036004008070100300c1400820090415410135660f402900d40058000d00c50302c0d0010340048010311013004845202c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 597731870 1250 597730620 597730649
    0x240816300b010608090606010813150b09041202070503030306090105130e1c08010b09010215130c1815260c10080906090601181a10180e060d021009 65
    0x403c080c202d184e0484980c00207126420024100350301c51190309006103104140102030500c15210f124401d480740981e91845529020258034035200d00c1e41c014803641c059505014980815a0002e05040107540224130950050090008550310200c4c25411108200c071007a1040590421035030241061526056103405a81d11551164101072801c1403005116541d03c91180e8862040f001300f401a4046140144d00080c010302d1030f100c0c2e0f0080e040d0042c11814421840d00d42d956600ea0914145800a091803490980c8840c01e4030842d0141c0100b2041c0c0c002199000e60504400c40c02d034020b1510121003210218503401e651840501c807000c41418081d005070001c1d03c4a0001a08508061310204582c1c03243c04005280b9010128505050f10f858000c4d007200440c412844801512821a442c80f0040b03541c4440f0006584080e24490030301110b494a0b01c50700628007081e5880b040d20307440382c50502e103d20304012031a0b503612100380c070040c1e0407600e0704003600301140100d0f00402c20b90072184c20081c003070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 597733120 1250 597731870 597731879
    0xb1b0d020c100c050c010612050c0613181406040b1014041802030402121b0f150a030b01090603090f201002060115050702010206060d06240816300b01 66
    0x101c014541710004100038003496680b915040d5280c000b03a080075189411411200180d45014402005024002c51064120580f503200c5050044510b40811008503075641d0645603200307880080710781c0208100c40810604550b1000b040310300d400b0a0300b80c000c0084400c5040d4040010006443c042d1080b24550700200068101d8900250f00550382648901c90101b0364a040c01e02c00140f540c0040c0c40907e0342d000ca11490300900c80000c011610850340b218004501c02010300b0701d400a0300489105607030120f10000c0341c00001d000c11003990404002c0506010b008000f0500c0e400300e124101e548020020710140440760f4104020502d24005a4400d25070032074001c034154000750007030588062034200700b00342c0d0704040d007a10103205a541c000e015800ca90002a4141703409040c0c451000d010354804503164140c20010082c00c800050008803144489106010f01d00c020802c608098000702800c0002c01c0c00c0841d042c1d131242c40800400c1000801100e48000143d1202610328102d6110880030f5a5503100c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 597734370 1250 597733120 597733127
    0x70f0309170c04060801200a0203070f0f12050309030403150207020d050604050d1d0907110d03230108120304061107120e0a060801090b01020a050a0c030b1b0d020c100c 74
    0x40c03205183c811070520f00d020800c0003040c800d0b54200041600c901030321400140e070840007038004a4150301540000c1c421100481c0c9030b0b84800000d01d00c43c00410403001514a03040110905003440d1504104090080020f0418000112400c0da0380027801081d4074084d08407120080c3c032410350000e400c9440b4012400810070001040c50080d48103509440541211250460740140e001060001c404056100c4440c1400d140b0589070300300d800c51900c0c10240f101003181c60300c3e00c400c6c0d00c080000039a5418040d203607170645c1e100801401441800002c025454209807a694021644090340b4404001010408219881d400b00101405000c00c0c00d45544c3c0710704000500c44080507074040440c80402d030301a0300b46070a5901038299803054540300b08036402e0410940c01000880d104c2410b6204514000c0c022480422080d00482d100300464003100741103190100311100041d08003115661168500380d11040200151141c01d001c0940042e22140140303540c3c0d01d004982c8110010081c64495804411a030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 597735620 1250 597734370 597734383
    0x1d0d0c2c1602031602180c2104020a092a0906030e0c01020718020c06310b04030503060d060e07050a050f011218020604230d0305070f030917 62
    0x415461450590301c184205201611002000c00183c01c10040703001030b40d0241c030a603c003003400540005030380c84103e0414048404c003641d2401c0005004a03986403105c5c0c460716180b00d0b201c00500700b0800e03800c10b580880c41702422401148031164132200000c2c501d411144543e0704006c28644c03105102c28100c0d402400c283d202e030240a0005c3d04120f0f8030021004001a0032107406d0701a401030003010710341314010031500400800544026020030074104139100821105000d6003c0c404520310340c5001140641c0386040035a42e150b920402084c910b00401c4907290110ba003c2c0d05030500744da5a55944000518400070228000d01152814610b400200c40001d8017200356801512080002c0d501c5008010355042d1680309240062100064035441500780d4020441710551041c49901602c41d60b8000303242d0b50460340100d8880c007161844800b07070481c00c04441e000700f04161001180d1070159100100ba030b124602018040340340001c070b05000c05100b054100c0c0180744d5078030510303d13050091814544500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 597736870 1250 597735620 597735689
    0x30b01031a06030403030507121113050a030c06300504050607020609030a1206050a0303020312252f0309030f0c0102030a0c150603110306071d0d0c 65
    0xa18020030300030408208000c40d9410750005106504582c0c1c0c56030228007400d40100400e04103e41491802c100240500403140c5080814120603140c0382d40c001e403007031308803101d5000911034121000d0030008201c0d0501038006960041c504010750310120203103580240a00c00c000410501d0004e402640d1100e1035102e40d000754030400a0301c5164a81c401b00b20780e5508280c42c1c43c0902e4100b000600100f50150720301d424110030141002c07603907954035030004000b590243d01c05da0268100103003581c3c4c0c0059020300c1c5c691111801c1c10304c41c401e80101402120040d205c801e60400d00510100282d60b0300030a840d102c044091030a5041040703003070503000384d80325013214101c0f60003482100c4107941e0015001c1403190603000107034000d606110052100300c40d07101840200b0f0f00e400c07154801031040c00f071440c0244c0c0b010758021252000740303040700d006051a2010041c109400c00180310441d0885000f5060b1100329090111040081c0701c0050030984980c0700683e02c40e0003c06040c403521600405511340c0c400410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 597738120 1250 597736870 597736877
    0xe12070f09270b060f010c0501020316260403030207030c060f1d0f0a0f0f120e011205070801141c12090501080114191223190209060102030c0d030b01 66
    0x8031880700400040319485002800c100c0f03481c2c0002c0307050412041201101c84c05140501003a94070b078507071508983c000c0c2e5490102040c40e601e044142c0d0340005200910801800c8040b010f5204400c01ea02d2458015000070201500011841c0c03c2c1482218203c48040e04200d08104d014880c1074590002c0c201c00b2500090b02c0455100d48190210104540401003182d10151060958035030b2440c11264100340101c0d42c621101e00d044d00401d00c0013131100340955143e11032129500c2e4840005d0700e100110003504100904140410103a143c0c8100038504640700485c03101041d001d08400620308854854102c0c241119011740d00342440f40c030b1172401a0702034175030f110703484016100c400446500c6001d00400ca400c1c91411040e410030b0404000070340140385198400d590094440a6101495604540c10748810416005030200c0312071700790307038800002010710040c00c4001500c010400384020981002e44a03000c840c1c0004c0c8980d000b4400c0b0307001d29074100f09590046c02007400c0500145010702100303000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 597739370 1250 597738120 597738161
    0x8030c0106091a0a050d0807050304090605090c07110d0302070b07030215090102090325091d1b010210090501020702060426070e06100306030203100906110a0e12070f09 74
    0xc0d801c0e80465103610f8800030f42001d26a40c02c00d014004012141d0750b0480b6001010000d880101e5802e1010b0009050030690214407980391030700308205828050510991600100100000103000505a20401c8400d60b1501c070070420900301641015041d6000d100c8944c0b00080300002c042d4082044139a104039243c00c600962902d00c84d4908070b00580500a404d940154025201c0000c01d82410900300060400700c8c065945601083c03081d100140c200c01030180328444032140741d80042c403000108200045090210701c1c51880002e655041c080380b4001d525964201400078040c0a40440300e009070050609640c0f965501440c029030880801100304901c43d44841ba4810940451090102c0e001c500000d20700740c84980c100840d00020f94030400515a941c80d00100603102809001c00241d5a4070001880b0405800e0800954282010354441050100a0301c00106d4004040d950140c3c4d082e0340760950409001c0c0403a05d01003e0360031480c581c41303000d40001001030072a0003200d086520600c81c400c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 597740620 1250 597739370 597739391
    0x1204080309210c060d0b0607030503010602010f050609152e0f08070804080c0c12010e21160c09060308092b020919050c091207030b010e0a0608030c010609 68
    0x1210914100d05250765004540c0f43c184501d00200a808800d0014400042c003c4d24200047c409901200084010030400300042051540a200700141c004240740c0500003442c00d480002c44d0490002c0c0780403034080c6821081412501c8440001107400164003c5442032404814603050b0040603450700c000150000400181151062100368020712450f1a401c0d02a00c1f641d0322184143c0001c003102d180e503c107071400c9000da580c0b406101c807a103140503400001c400500110140c109a4221071942c040c62400e0300c2c80c3c60007079046080320102084040c0402d00c019861500042d010019409090810b081c210084140b058090042265907000c94000c0c1200c40306000c0c0501035814064142d811948c840388100250503c281c18650142d1071002420007280c5180a0b18112913040c1d600465004001c5000d45035070074020003da008000702c10040205078990350307880d041078105010b5840802892000315000c0350064005030058180d080275251107600c1c5090b414001e0100d0300c100c0c402c407404d0031074005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 597741870 1250 597740620 597740659
    0xa0614130b18250b12070e12030d091514060405180f030301050102100b0319032304140402030f1f12030f020105010b1602150d02070b04060b04111204051204080309 72
    0x480b040c14170035030b4041a40d82c3e49001d4031216851202c45030403003122000e8505400050000f412034800d0400d000940346160b06100c03075158011299208410700c0c00060749001210a921950700c0300b02221301040035503a60490001008040d03c48015074407a00040502d01240400514182d9a003a421110380004040c2c0d0701084c0c6081d06600c80d0183c00031014002d15108111250b0401400f80c109050700030900c41d400b510301d54404400404152010074184084010690006004c2000b203d0641c11410040e210809503540600503c220124881c00d55100301040394142000707000018200342031580b6820301038680c050060401005520b484008601c0070200f0302560880d0742c1d0500a030903214001d82c00c0c400800b4401e0391800196009001e144074407051030000740301c0d180c851070408055003040d2511000f40d403020040c0341c0c4128200031200c0c00c0c00c1d40000c01d4071101c0502c0d82c2003032001c0d240d80c20810300f0f2180141340295001d000040c041a0380c20700000429001c042901c00700a90b4a4003c03022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 597743120 1250 597741870 597741877
    0x1914040b09061509072a02030c060c060712060e01060302030619060e0618060711100207140607080921070803030405030a1103040f080a0614130b18250b 67
    0xf00b21454000e10150164100500c001d5407200c1c060401025104240160b901121021042c01d8a803941a10b141c0381142803d104642d204c0105640303a509001e14049120f89441d0000c1629080081c0c200720b44030741c1a8039130014002002c200710415080d586801000b0003940c03045501c01e018112903081c284283d9000003542048070015a180030040f40904200300a41d40711045040341070911712036071a05070740d0390402482118402c1601801000c1070505110000d5200e01d814130942d04011010015100707028502c0c0380d11344045030700ba0751f110b03103a00d4191424040d070000035800201c150191189401640303881e00e8103130b06541c100c40c0c1c01555002d60030703900e10044070014115001801100380c030034002d00e10706604e110b20105032801c1a0b118460480c1c0b04000b0340c400022a404031000e00140001c41c402c040c1d9008007807601c0c02c807030714003025045400010241d0003080c2c403140b0400a420b59402480c0c4440103980d801c103486a45c40c01c001d10410319500c50861414007040c0c24000a47c104418086 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 597744370 1250 597743120 597743131
    0x1c11010e0906180a270b01060207150c02060f0d05040c09110d0e0f1009060c030504110d020105091e0f010e01080406090c0909051506060405010210051914040b0906 72
    0x40004008440c04420003e0310080d0003507064603158030340e085011003c1e0043e80c0250142e090108890303401428103641a12040c1d00000540d007001a040c007100004441d500400300c09c1d13040c2020050071034030201e01544520311042c1240030000c81c400a240ca440c0d04414007031801005294105912040e01004a803060303c0202c41940040011211020f000e40062702400c4d4100c0c2503c0f070000440c81e495007001806800800f20598400805081165a104100d00d4001c41e1504006614141d5204001340b0f08611b1030030b114400704411202160b02c10f0080302c11101c000381c0340e500d0303126a26130104082c0110300940c5114803c06a041c1c9003951040070b50308001c1805968562640d01c854035110300812a00c4002ea620000b034000106605045025a200444c400c500601d039100f01d032005011000c1001d40024860349042204200c82d80c0c0c0000c00a008150784840001e4944400303c1007205440300d80441d502c140d0900e9001500c11a07100206441107000700721500031517a80d1651641c941400b00c50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 597745620 1250 597744370 597744379
    0x6110a0e1c05061f060c0804120c0b040b1c09020604120618080307030c09082d07030305191103040e090c0904231612021c11010e0906 59
    0x16850035928020090032009034031a214840e891115440d6281080001c0701c0e150003c052000c02c604030290013400c00c500400441c6400a00d503c0c440d40d81070702c0e61007035108403801611f0380c03851141482504460240100351050001b541e6550b92100e402080e0080b50700f40d8041109001080344d00d090a0240c0788450398018401840c4c01c0c00c0c010f09400a180c000e2042e10f0640e914012141c0340780b5044c10000d000f03401a0326a68891610440041c203444048150741c08221621804200ba03050001d030200c4c0200322071380003004040f02e140c0740034485102d031903522609204041c070004c00d054103c802442c500c088040c204400070310201040d2011006101fa02071103a004010400c175900706600c019070048c0394a0300b40c80c02c0016010014003048416502600c03081d207091010310301407070603699200d2000369550192559010302c071117410710660584640b50350f5031000401c00d01159180425112950180c209420000c007aa06141000021404c812070200b596000d94500524100d084584521300090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 597746870 1250 597745620 597745637
    0x91612060e0a0213030804060518010f12020d0908120406060509010b040b03070504030f0b091b010207290406021510050f040f020f1b0c0603250215070c06110a 70
    0x82c25400250300075101c01c00e0505031440e01100058426000303000410003980c410352101c2541c0100040041600f03141414040b40b92190b40201e41c02801c0c2084080c518500140c583c5400383c04030b400f03000e260034000c01d85c0c41c0014500703078090500c821306402140110003c1158684500520003584c10a0161600205003403004100c103030100c0c0000c5a002d50285080f505040c0d030f80e95a0405c551880000711207894401040244440003081508212543c038a008901d260f68140080d46496860207500b946904114080c1510455441c1900840790b100c014540e540d81e0b43d0030020340f20110b078840c07195496074030030124860711003019118007500c000905040500e07030894100401070035640384820f22140c00307011200084104001404030004420701440390280002e001c0382c01c00f00c41071442c0d44200ac0038018001501080001440c2006541c2c0d25041c0020003040240c2c03070314a003001d150340340c01c80f104104114164062500c899680c8500800d005002d240011003680d03015010780c141c002241d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 597748120 1250 597746870 597746881
    0x1306110a170f100306090303060e0c0703020f071809020303041a030a05010b0304030906030f09060213080c0603010e0708040501090f11010206101404180b040503031902090105041a09091612060e 85
    0x44c2c1c1b0030b0450078880d080002e9101c3e6600e09291102c2e20403101840e040d600483c14806168041c400150170702c3c007200c05810704605104071020001400c05060324102d0766041900c046450800840f070103400e0b40d01200b040582c19a05410048e401240d0013240c841c18003000141352a03030441940d004a6250719003604481c1032042c21802070107041c0c0c1c510f000c0c5494100718030120340280300a00841802401209040c0d05240c00f840c5048445082c607405044100010004248081000340e000541c078503259009842e6414150701400200f24007030105020203214400b0490145001c0200300d0007a02601c00035540d1504103140c1607680e102e0300c40030200080c510100e9150680c884680400190103040c420095521542010f4508880032100c07940000144901c9100600460190000c400415442e00c2e14000c0020110301892040080301030b0380d200309500c000701110550b58140406009078035180341204507007020401c03d04036040400d0108802070444041d07070007400140c3d0450070000c292034840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 597749370 1250 597748120 597748133
    0x18020405031e0a12050a030e0328050403170d050609040506011a0c01060936030c150f0b0405100806150a1a09010909020a081306110a170f1003 63
    0x22004000540244031244001954000134100c140501c0c4c0c3d42c107602c0d2044903401908070780d000f1080c080c0c0c962042c840c0075040c1030b100f95083c0d1b840007803160302d05c98003841e42e10039515801181c000030601c8101c00822028a8420800341000894540040c0300d07a450310402d0221020040d100548140c00100042c09881e44420310700881148600d440c034504005804040d003120b0840e000215a20f032102600084424008528035140a070086400d01d4500c100003142914030705460010140f24624000a05001e6420001400039901d60414803441003107100707807002040c482c02e40600c15442c00300450401d0b1002000d001c155618000200b005445c6c4015100c1d442c0044241141c0c071903101c440c080b502f400703002c280c801020031600d01e140e01c90101c40c00161441c02190001e0102520622061080c2580002c03450341040104109410500e540d0800c10042c0c000f8400e0b002c0d1070000081e102d0b034199801031455013071082141041026890315200b5500901e4241c54215100243d041d091020694 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 597750620 1250 597749370 597749413
    0x9010302132f190f090311150a05030f0709052b02060a21020f090d0f0b100e010b1809071817010f050f010b0703030605060d05011802040503 62
    0x5044510060a14054000160b018110004905140d0010942d909000c910f000220f61100c95400c1011020080c844003c01e0080a0321002d00070403132880000d41180c81d0800404890014a11000d40d54001c00700040e01540c07090703d15003152803003540020320092103a02510309849000b821000d120011052051014106041d65a40b19088035980001a034840300100380086540c0c4030401c8480c0300ca00c040c5028900240050b01c0d040c010805c022045151108445800c0b10450340e00d003241441d414200c900074140d5400a000410000c00e02440c0c2211390b180e00f08a804481e107503002070b170700d45120015501078944801e4040d0003000200110b49441c051130fa501c031019142200603001881c0c0c96141c41000b6510220344203990b90f108c1d8101040a001d154444500707002c041c012802d011a5590b11180144628400035001240e01d404051103904540f000b09401007005440d4075140a44c200204000e00c030f01d0034100b411002814028580d8001c0d5002c40d00006c1c0a05603040143d40b10402e41c60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 597751870 1250 597750620 597750641
    0x1d10050a1401090e01091b020d05030f09100507110c060c030928030c051f1d01030207060608010b180709030201031a1c060b03190f0503040810020702010e0901030213 73
    0x20f1600004076100c079150240703a00806e1840c00100d907843c1e40c034074490502c1509490300803c6411003005051a0f0790000c040384c0e08402086050811691000380c1030381006024143c5000d403030304003400d215600d0b60100d03100540040c00000e40e00240c20401c1000241d11807002080401e400a01c03515913903281c02d940305e080303d0050702204400d07a00307028600202c9a410f0340003200c94186201c01032045041c6081208074503080645003032031019034440302808120245004203054401d0281060103a4461340607142c03400d41c4802c0512016441d4100f050103032900c40502c41c004c028104d143c0c0400f0580c04461400780c0e190b51a8925018119001103014191150003583c8281c5104240b070200d45130303402040005240b0800780d166010310751030b085055550f04000148281d100c11005000020401c4000c1d10003a803100069403200903600d001400d50185900c0782d40d4502640001a0061000f500107280c01c038401d83e254480c205020301000f0b9020b0081c00040c2d04400700803c0300c41c00603d00d5003c0717400032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 597753120 1250 597751870 597751877
    0x31201090203061906121d100c050c0d090e0601140f0307210209120303010f0506072a0e070216060c02041e0213170a0206030a14011d10050a1401 64
    0x605041412460101a98401d00020306c140c805008129864451007410000d1421803000315440b41c0201d5603248404031004120958070001c4610b02d85c00341003250409484002500e25140c090b50000d00010320380c1c402c07050b42030b20401c0020b80c2584038400420742c2d081c2c030701800c13800c2c28001030341144250001000784081c816001c8901d0304c880c0c0905c0301c0c4001c0e1280c6550240e41c039080304083c0100c00c04070181c940507691040c40103101c101e502c603400c4816220b0943e40b143c0ca5114506090958045020464240f03ca40da40349202e50180180701c0c03400d4031040060301105849801c02240d132a642042d01c0c903006910500c0c01d001c103600c1a6001481103000800100303448000034865050541400140036040b903000846004410300313000c21400078020411007187c441e049183c8944c6920011380024840c080000c00600b91480940c4020000003003185c07074110568407100aa00031340c50071000100c5240b9150005101d14002c01c460300c080d540050809884903141281010b140410b040c0c546051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 597754370 1250 597753120 597753139
    0xf030f041229250504051306090501030b07021902090402010e0414090105151c0803041401020c06060f1c03050d0b040504080d360303090609111203120109020306 71
    0x719001c1d054542d80c0d8507038420381c02909050107005020b600003c41440c0e40c0320355448102061140c2c006041c0d90850b44251854003074402c002c007a03c4010241d9411007420b141c076000020090004000e08140715650035000c8070282080c030702d455610703403445950081d4080300901c0003c0065101e042d00b021214406800403c9602e00c0c0d101c0c8030407810003128581c6e46603558504104543c200d030108910b00c031105a8582000040d000052007090310002000380c83d0392000030200c0d04001c0c44448a084440280d0004c40d29142e2213200d968903200103a03234079881201000c03041d40c200e1402050008180160071258940c03081155020345441d00310014014449580f44482c00391512140607052240f132240c030ba1181d0300c09500130110200e50b0700c02c1031004100c141e0144083d10b15000380341c8180d05d041101802c40c0000d01c900d0201c000d03107650300300280060309001c503c4080082c480861035603000115181c001c641c984072000c0da50381c00703841c58000f0014905001040081b1459000b0741c0c2241d0040d2400f0203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 597755620 1250 597754370 597754403
    0x10110607030903020c0604061d030304080601090f0605040c08040f060e12090a0e0105010504060c0c051e181603090203010908210109050408092808010603050f030f0412 74
    0x200041229414082912140080101603040c0101000540700b207480c142028200300008010480d482c0e03806407a107406c900030001d566000c2003594001c010b441d086421940e10342000401602100420300003190400002040030b140030300581e1058010b5503521001c0d03a44a84072410070b0407800c00705403103960b0f9035110410120800d0084080f0031b0f10b41c405455a405148040c00282c021a5002a0401c114040144800e81c0e02000315402c0307502600c0c2903640300d040d508152140b0140f1b540860780c41a407415500a10704030b683e0049283d054215083e01e842c1c40060500840c5030401c86005001035418404603501d83d00950000400b5400540002811500c9549820507a40f1404c40c1640345200050100702e0200d41c28030310b50140119139000d02c21070500369111005800740c000410700c41c07101c0c41124013101141c03910584100e0700540e14041e21942c1c80000038000c0030140001d850780e02481a518103110000004c407400b000c0000f20341841c0600d00503c505290300e10003402c440c40c0800c451480d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 597756870 1250 597755620 597755623
    0x40302010f0e120318011215030803180303010909061505060a030e01020405090103030e090714030a0f0b040501090f0f02090a03110a09050c0a11160e06010306051e0108241011 77
    0x210300c0007052180d80c0d80d450660001d00584a00b4429001d21360030408d135a60203160b0007035002e045036805600b203516515070b4a01516540c600724260201c521020000049010b965008aa4403074081c0b0010448000c054440c0c581c105a6802802c2d000441000103138280d600c698002511801400300060810b0b459200298410f80280d1007030300045c00d0401c0280f010324141c004a0340140d19404e00a0828a07021100381d054000288401c0c20507a444d45032560b041e8081c0c0201d540304100034400c00c44c0c2e42e1120102c2c0020310988091103507051900c0755034602d101c210710031540740d41001041303507813464a10754031040301480c0e04000941210361503800080d00c8446000b003d001d9072610be0415100e40030b02c10b004100450b559001c500b5a48009240c0340c1101c22111108250b031268a8200307600c3d6146c41c010790141c01c00c0c1d4405a0011a00385030080d0b003403e00508a807010100340d80313591460f01d42e0016007865408003400d4208904401c2c4240c074807490020340c4810345407010308041c1a2500c4801400d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 597758120 1250 597756870 597756877
    0xd02040e180304030506340c05011b050304020409020424150516111c0303090507050f18040201031d0c03010b27040c030210020d080a02040302010f0e1203 68
    0x202824429882842406070950340700201c60754801004508040c696251a41e1341c41e0046c0070891a038000454512851a1441017048030110342d0400070310182c1d44440061000390711460507604c1c1e5107070020b2042000399000c0c00780c0403146540c4e1140d0a54485070200002081100230482c0c1c419a41c1e8131400b215103440e102c0e100b420184c40c225299480c94200c4080902070b401049500f006010001045500c03100745545042c0da8004140c031701034440c5031000c0b48285c41c00310301590b08850320118003000c00d0b525422202d441b40c400c03020f59035200e90b1601482074001c102c001103540310072114110054018000b4000d40c0c8580140f40100780c1900f41805000014052403002c00790b9049203003600f0380382c1400d02549915005c140c801c0c45407600d4846400d006500006a8488081ca520000c039007840840d80000000e1074004281961032300924402964607002d92030002d002c0750f115070004039010321900c00c1d201240d0301a10783c6d8424102c0940222810200c4c40241c81d40500408516104040204040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 597759370 1250 597758120 597758129
    0x30e03010f0e0d0e0414010306090215190909050105010203031303050426010b03150105060d1b0804020307060206011505030702100f39050f071506031a0411060a03020d0204 76
    0x5003552010520006000204044e00710340502c0c100302100812000d0464243d04494000800180300740040c4000f03502c640501482c49030b482000700d04c4072100c00000d048c2e40a400340703688030300100c41d540d1080c1c0c40c2514400d200e0315015800a0000074100303680030001c1107a1620030700c0c1803482d003900c40c03d110b0040030032040203800c04407402c0d04142064109210780e62885408400a01d003c608501c0c2074500c08905002e00c5001f43c4c4003040081014001d5000703540c42c0d00307040d00b40041513100104014201501103130180c0c403912401c48002241400468902c2c1a180200110703000d540702c4580c00c0d0f4041e48040c0c0a0021032141000c0b030103c1e1189481821107003d84c40c038003c180150952011409503d0156020171400440740b82c1580c010b5034403070013801441c000d040c004d45450404904142c0f41c00740440140c80340c2d04000e054041d444299201e101030b07a110300c0c60440c50360b9114a103449480c2003168000c00580a9241800c120b14041c809811400902e01d030241c43d0103003a0203400180d030450f500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 597760620 1250 597759370 597759373
    0x90111011e1406030d0f030b0d1a070c03020307020907140a09034b0c120b072c0f03011e0608010b010c060b010e040507110c01020d0c030e03010f0e 65
    0x1d07507154068807401400a03000030090302034814142240041e4642a4410b2128180400341c280c070150075009800ca02c0060400615031126440503042140007a00c502d032840a400c000340000401050003070000812864140d0700460401d0000d0382800500030004d880311050009170f0300300400e045e014a00030458800940d50301480c09256207020101081300c3c09500d801000126041e074190044c020040da40c1c400000c0e0000c590211101c50b1000402c0030754009003030000b0000010800c42d044907411011b4503c182c62903003080c1d0794100102c5002c100d40b07006c59440403d1001e20b05604620501c0b9101e00d0700002c01c2217201c5d01d6403800007404c4401030150486001c260b9145400c0b5012184101d500a155420091040b0008040001c0c024a182d0750700a011f180e0781d2100b03c0303041e4819104c090384000b01a02c2048242450200580700d02c890809400c024800d01c90700b02030a52000c26070608841d00354548580d050711566094500c5d940d06403003140c25640e103d8000007030326524015410903401010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 597761870 1250 597760620 597760661
    0x14060d05010335121801090c030c050402131e170f0c06040305030f1e040b041412030306101209060e070f0317030601030207051b040612051209011101 66
    0x200c4400c4440d81c081c44280c0110440040052071203580302220f007071411a503019043e9a940381d40201401080c002c1286446d880c00300b9038010013500810200039070f8040c90260030340a03580c03000c110603032044040002c480304001c81c0401007800c0450814813090410b02090807038544484142080c0d2604694030400c951140c0542d0014583c00c2c0040c00740c522007910402e19085c1182c607070b5581c900c503100821248010026802680034040e0780c2101120340c41884039587c5542e41d4550300c8040d013190091401d40b140503810b03d001c601d40343c0b488510419840c8042c60450390303884100700d0000001d6406100b480031078940f0041c03455162084040c00b6201d10307000901102a03c0b9002c6c9842c08a800c00420145035001c00d00c0410403501391081001600d283c1c141e565602c2ca40100d020740650311004000344240390700c883c0c1e044003a50b0b000c190300c981924200400c0c1c0e950311401c18211000390f406400e54210f04a0382c0b2000118200610b00404181001b400055080c3e00da2400c46580d200b07507c800341c0001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 597763120 1250 597761870 597761903
    0xf0204140a0e0a050c190e0703020d1a0a03030e010e0a080102040e1b070b100b07030206011401170c03070309080d0603020f012f120a030f0e070303020714060d050103 73
    0x52180302085100c10b0018222829103690b82d50b640d003864a01c1c180308070080d203a00d4455001c2219104003920041c40c0360003613810000030103800b0307410803511103004509000c0207140f1651064688143e00d6001491b03101d015266803016140111440c691038100050700102e20169143d000e070407401881c0c09800180d595203050380d6800c4007040648003d202040011010444403105001c0d0b900e000d4210b8481034143d220f016020040304019805921022004200340052640104005040341c2c4640c00f540000841140112034280a40303020442186403c1d010038a03c1c100c0b08061a403211007828001030010071138030340401e00d4000402c40d0321110b488800a00c11820a440480640b403800e08090110907801a001c004d1b0711841440124900803600c0c800b800a40c081001c015000b0b0200e29069072840412001000f9002038400d9032a00c0303062001000941000042d50022240c02d070740502072507410414101c20f0740d0042e180741c681c4000d0a000540b440f16140c4601402144190020100320000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 597764370 1250 597763120 597763141
    0xe090327191a070215180d030e012703031d0d140c0607150c120c031a0901030b0f041407120311060f0a09050708060c1c05010807120f020414 62
    0x30b20400703040c05041802490016100c482100c615405c00d16516070300c0710b000140300040c0e40304504c841580404044056001d06170810084513201c40f00f030341c3e00820b00300d442181d00010076100841003905e8016240070004240304140c0c45001d4611041070ac3e600141c844c00045400c1d28a180507142c0c030074840c42c0719020700d10410003907407040c0c0c1c1624402e042002311f0700c1c1d2500700c4039242c6902c07648a80350440e915069214008007044403400b00b104114101e030146004000700b803080b071a10900900f40b40d000c0450300d0480e00c0503040725448105958075a8900d0421008041d0152084590f400e1f17014510303460003024800e440140c0302d040749051031005d42d41802011240c84001666181d041381051103100d16500e408a544526510004158098285856443c3c00c441c0d5000c4c010304c1c0255814081081c1c191801003081081c52502245003001d100154812660f083c07250091560015604001d2000f1501d400c56061340182c40c0302860b08200d80114007a41d900094540d1492a42010002040d80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 597765620 1250 597764370 597764399
    0xc1e09060215060a0603051e04080c190f02010e0a0b07080d05180709020306010e1201020a02010510210c03060213150201020a05040e0c0403050a1b0e09032719 70
    0x80402c1c080024100640030030400442400380340101621440001c02c295500c2030088065400c207001c014080c901401c200035140c000010082e024003485001e0900001619094074041d17800801301f042e0002968019100702d150f2903c0aa0803080c050300005605444e84040c142180c09080b010fa59501600740030000ca68009010720f0b0040442504504007103000148002a00c141c00340c0142c0d682c50301c80060b103801c1420000c80c0c0c1c0c040640403c01040704019005030a80c41e1640c0c00030b000e603460703034640e80204400901803e60314400c1070408000e040c0700541210b50b40e5002d03601c1c00c800a034691b01c514003a0ba010001103c512495070008200e801c0c03c441a0f440101c40d01d1000b1030030f2055400b4010b2503882180b0a5552141010012800c15501c0340221801150f0000032a1418101403070550255012940d19099a518800001a07c40b1802181ca4410b0a1142c00345181c034042038511002c60343d010000c205400b001d001d0385211502d41205120800404041001c072079464000440c80717004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 597766870 1250 597765620 597765643
    0x90a0206070c05010314040f03030f020d06180506040605090a0b0f1008160302040b0f07050f030327030a09060315050316080609011103010605160503040605030103230c040c1e090602 80
    0x3c610504000219140d045140b108c10ba151801080d88840848000082d0080c240c000d00740924142001a815000000200a4030b11521083c440c640d501801c00c01110510320465400100782000510f070317242d0301d0340102008000105080c521a51400204d603941800b84001e8001c1050181841820708040c085441c8004030f0703180961419042958245007809038484000d400c01000c10f9140c2001400d00c00d5004254892048980b645441d501821101e00040c00e038202c60001c420f04c1c0d1052000101c21201102010f0301d40451140c0380103c114002c1c150030310300b00041c3c1042c00700402c40f690140011911004510150481d15084c03080c2241030802c09024001568906451180c2c405108000d4030b0443c1c1d0581000d50302c802006040303105202007140010703e10b0000050200b0140c1d0440701840c1640c1c041e1039400c018049281d107500060018211005081e0700038800581c4901c0c0c1030300440d041c0d220303510380215585801c080e40103000030b42e490280081407004000b848819030402c088103800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 597768120 1250 597766870 597766901
    0xf020136081504120c02010c0f080405131104050d080d0e012003160e0d1a10080d020a080f0403050703081801080c03060d112706030304030305030a05090a0206070c050103 75
    0x905007581e43c2d200c408184c03454001400100780307101c01568040c00b41c00b0100b9402a0682e00018602d2400440f250b0140c000d8502c40c41c414030703045001d0344062207030600320707010b0040c0d5900d450309040c100030300b0080041d000c54108604028100c80c2141c28040ca6087e00c03901e02c00402c905240007081d00c03c00072109281010f4080604c104150406240a0b103180d000413420302d50040f80c00c040104481448540d80545030024a03c0d01810106a961010b40300382c030b214500c0101141c681c8206d0751900d0f1440c2914005a201c130302c031031020425410003440035019800000345016680e0780c8043c00d0000c1d0354800c0d211301c140400d10052409071601c20034603070b40302403905118619040407101014000542040e018111041c40030042040e006003000301c0c4e800052048221001804403c44400000040ca104c015420008522681400401c0e18103507a450f482e407a086540d28a0300303134003c227002132180b00c10b4480d6142c19030241e1609001440d21a0003900c515040900303200001d03050303401e000f640d00e000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 597769370 1250 597768120 597768163
    0xa0b010e060403080a1403010e0105090c07030e040506012105060906090103030c08031003020a15030e0105090a11030a0209040309030515040b070c020a0b03100e01080a0f02013608 79
    0x90380c0e4000c1102c040c1c030391200305152200c6605900b00c4030a0b0503061040a030f103c00100102d10805a80e8140e4101c403011544000d0b1641c4000da0b070540ea0040307040c000e011604155640c01245055000264015410301d002c50340403041e0621001c0c0a00803565106049035540140038240c104403440d07aa000c001a180d100b200d52560fa401400055001400303440b0071f00c00310200e100584203100390720085030010041d01d00c00b5110421015580c5104c541c040219142011603000d510041c0074561041c0c51a8000d0503015103a901d40e0880f00600c0014240d140c06075036100b000507034823200709901980c080d036034405045003140b618506d0040780034200d5007185042d00c1004002408049015444402c900d020038681c1c0380703840818490fa040c1d07004080014800301c20001d5503810303c104042102e260300e0404042c1e0b40e0358400580c031410380c483c0280c40c0e0702a941d00c140c05540918200d1b0403850001e09240050340303840f41203032403030803540510000c4008040000c2280e1b03802013010002d08a046000402c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 597770620 1250 597769370 597769397
    0x206090a03050a120908030118050f0f0c0c010e06070305040c0603020f0403030e06120f0603010b01030902090103123b091905060f030618070602030c30120a0b01 71
    0x140c002c164610301000304003030300c002d84213082d90442c6402a40c006070075a204d5031102d1415640c1651001e400e080b20b403501d000540702040b000c3c9071600610145420b0350a50f03c0300d80400d4190b074099120484659210300c8030303440b41d0380708002c40c91050420340d40004860820345050380454149511030000c040c0144003175881294503c0c01c6504987d0300d801c108113226a01e4000c5802d0b0300400c1c80350001d0400c00002c02459800c0b04002e144a01c10440c020885040d08900550484131440c1e0046d41240e0b469005100240103600340900100c2203090000e402c0c15510404000d1403c09108601d0f941c445c492003205a000402d081c0c104401c0854040f10719144c80348403040a0035400406100c1c10381c6071008130300300f41c891702180000104050191505450000c42c01030610b0745044070703c5a030380302d04d200000351644040243c9150300b002101400c50161078032554071000000b50300051184010044000c60128900014035103400031341e0544001d803506520581c121480000703128144002e01c0610007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 597771870 1250 597770620 597770627
    0x10908070807060e011b05150a2702030c03070303051903020f090d02060405131409010c1b02030c1807080106021906020f04031a090c1e0d030c210206090a03 69
    0x14240c0e4250b24004540d00e400713500403070384083c094080d103869242402918040c010003143e01007010502c0300c9a2002d9440742130401c01105c410403000604c580d80c643c9140720050040c0401d800e1107000804a801d80c2a83c0c100003410b10042e03610480120310700051414054021041550728001c09090450415411070511b40c070724400d0644c0c051180060400b040e045583d07040a45002d8500500b840715440a141d04243c000c0034503a02603400e0303448140000c1c40340300c01400b505002d05195507a84214141903058074250440300c1e041241d040c050800d01c840152a441e40e4400310f00c4c1051031060b428207001601a003140c0c41a0403010440d00450ba40b80c6213400e5101c0c0340d41c1c4c90b5a21004c0142c0d181d003940c0c55000540070381c0c0c1008100c4940f9400070f10001d44041e10740390040500c03005448000351000c1c2081161a4504110959000d00b01501e801e00c0c80c002c03003c00d1509000342061307440c1034219074600118550b101c0302644040c210030645c1d03203015810401039512000d10001844c6006461702c002d0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 597773120 1250 597771870 597771883
    0xc0d11061308090d1b0915030201090b0f040e0a050414060105090115050d18050609030a0912050f0a0302071401170a02091c03020102091302130e1f0f050109080708 72
    0xd408101d000614220f59142e0190161031182c204039a01032044203420700c00d07120714051140403103a030b040c414a0001e030108100007d044a50584800404610702820705500c2c0c1c11000a180780d0090510000800903900850b1900c900c1618900050302c1c82e0130314000681c24a40e0001c951180d11060042c011501e41c01c00746410340b035104040602c103024045048a40744a025541e401690610500001c202040e0006010700c600c02c1066401c0ca50303d402c0360a543e4007490394581d002610701c3c0410420918008003036407686001e04162286c80005402452a1900c1d0710b00071401640113490400004440c044000c4480a003481e00b01001c0130341c3c030360403482c45502401c030050050340080c80c100c1071361b12940849010700401d094900c442c4403030300303000c3c2c003d4000e40071040c01940034038600c40c0c03410014402c55200956201440304d440341010755444803444010540e4685a008580c3e03103603400e1115589034004d1540130f01c0103400e213007004001004242c003035101104a5103e40c400340900719010810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 597774370 1250 597773120 597773123
    0x3050717191b0f05070306050f15040b060d14040b060a050102030d020a180605030430030c03020d0e06011401022406131109010e0f01120b150c0d110613 67
    0x90054400c4125540d10b100e1200000106142032a22003001081400309801081300e000703120820566690035940d030045034040307407007150314150380740040072500e000c2d407011a000d4005003c1d00d0a100580d903248045440303840511045841d80b0007001308110b491207465a220000f5140340d00c445180c400040c2d96401802d5420840d5500410008202445440e10184035001f0240c1000641d42c0c4100140455209039016101e507000b850030f184003412101450810301c0e1f0040d8101a1180940204400030800802c0040c10035808111500b41120a40500500405420007404041d4500149540700c809080b41c400c3c1950001d080c0b21040c03c0404403031a0700c551100001c0c20107583c45500141c1c1e400010b0301c40c00031075480c1c03100d13141d200d4100c1b03070142010030400c0c1c8844c0d0315186148200305000311624482da0001c0c0b1002000c0651048a400083c105100074107c515028000f0512164903004550403504540c4a141c4800a8a6000c0100d9030060049405000a0b042c2340c3d003200755100e10800c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 597775620 1250 597774370 597774377
    0x406090302040f14180c040c09180e1c080f040f1e02040c0c020f0d05060703110c0d030b011205011401051b061602071715061306030305071719 63
    0x600707205840c898001303080c020b404400c0d05000b450040c440140017a294031903035105200f081000c5000e0304003842000f181c11000c0d00c945011034a0400c09012030340d48151141c400755240c4006100075141008045d40d409103442000220032100180148a101c000340381003820241d9500f4040410740681c0f020710000c1e04185520100100d45801d00c03c0c0800e00c0070000c1d00702c0e240102d00c20311650300100c1a05040e00c216452068217194208000a1018220780a031050300a0740110300018001c0d4402808040b915452074101450030841340d05254028441d540440d449400072001903911260056010041e02003c1100354103026503421502944180e00e4103020000030f0006030300f04200b06090602040c0e004480c0145002c06034400003031202d0b10104054443c900000c10b00f05405014141204001c2d002841720403421002118001d001420b0240c005c011204210410040c60191401071800b0b0380715a035840c402446c1000159031940e5007088060414015051341141d00b240c002c5000704a0b28 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 597776870 1250 597775620 597775631
    0x120f0203240303121018020702030d0509010212030109020309010e07030f122a02010207081f0c0c080304060203070909060e0403080a020c0106030605011e1d1306050f1803040609030204 81
    0xa0100789540304a85203100441120005c014000c0c10b00012281940e01c01000c15502d8540c400541b82030340148a4000d46c1f40c0c00048c494042c0034032401c0980842d500510407a085e200c04044444c0da268800e81060308503039000010072185400900810600d0241e00d0b008103e22413130340d1a00e00c05982c0126008041c1c2c118800c980c110180318542c0203084410807900c003426030404207043c815254000354120b000d07008944002500d9900801c804003103107240842241b4040c01b4030022401090071030102020f00c00607480000105050002a501c224464400140d0302c2c103140f240501045040d510005c05d441c14500c05120900ca00c12405400c030390b00d41440e42c143e8a803410311801a000e0715544100b1586807040000500c01c45821060485500c1c412008440344031002a801c03061f400d0150202c035140039510441d0604141100740e030712010340c00d60280e04a03c250303200d034151102a1131f04020b900040060280180c0c40c4181c0440d240d0300365008519192404001806a031468800603102c0c07951354 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 597778120 1250 597776870 597776941
    0x127050a0b0405010602011a04020f2d0309030705150610031503050f010603061d0703030c1502030a1a0a0324060909030f2a020f0d060903120f0203 65
    0xd400c400c1c0d40c000c00401c14071003507840d4200280202055008540408611860201c26040510845a06010400c3c405181c41c6003401822403e881c030480d841140441107503180c0136a0404400b0714090074600c0c0244d1364802580c04c049142c402c0c1c0f507440100d803541c0c100600985030b0b9084042c0300421003508003c01c1d000b4038590a400d9541c0d16a2000d4221300500504003444481036000e80300366442034000300702c0440461009200020101d044111170743c0807c0c1c0520100740034032001e420a500c00c406541c0c0380d0112034680d0003660070541c1ca030070041e501c9a800f1401c54201820400070700c582074a010075254034580760980c0c8004c2100304078003c816051003c7c1460045c035080f8601409886070140854034091400a00b0300010050040020b0400d81602d44078092a400380c10540030214100c9907000b0954017001428002e91310100d074841c0850a48400048160240800703041c000d451700386e103498440114800380c442c800400c0000d07901c10010004c205e0035400b103041d01c1c28400800c4a502040d01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 597779370 1250 597778120 597778141
    0x5041103160614031009111309060512030921031e09030607090e0103080d020408010f0f05071106190908131a0301060e0f03010b120312012705 63
    0x5580603400d401524220701e1040e5601214408484181d0748402d4a440c064a10410742e000659001e4000c500100c0e04101401c03058114801c4000108011460160001609000c020317082d0301c00c9500c151112403c120074540304100380300130b88018028611b4001c1c8100010088056070384403d1f0941c25001a01e042004104141c8152504016242101c0401c05108072001d03000700c00f0252091040710000b031040c512036400c0c04200d40081e0b0391031354543d0855443d00e002d50040004801c80985c203004c0066220310034010014405091400012023903880160402501d50040040c0c0c20b10a07200544262681c0c0007810a91101000381082c1e0300e541d030000000c0c0600703000031020b01525808140c0321281014030100004866846280300728100c070b0b4000e2a080e500091080740f000c0f43e82148804694142100c241c210a1030082c0001040c48240e17000411103051130318400030592010415014407054801304a001d80401c240c0b8003100c0c100a90340d0620850388044010042e51200d000c500721061 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 597780620 1250 597779370 597779393
    0x2070503030c030c010b03030f041a1903090203060123012303010611061f050108150a0803040303030b030a0c050616050106030809090f1605090604050607030903050d02011406040504 80
    0x1001400d40382d03078448040350300b0f41d203401224813101294039003c0b40340283d01c0d0000440d0344a02880801c83d00302884c2c0450404000c09500c02d410000c1c00411849022100d00e50364110b00740100d8400188146490042c10b2900405800041503103041c002d241c081001400a801c1141c10246001440445007034004650010040180307417224a0200011800507008007600203800e00c210300301e0700c03140d4a1001700f510140300c0d030410783d4130032680000a008a52051100d6540901100c0400c2c01942210002c2080f801550340012840c3d04081010f1040607858001c4c01c4d02c2000071401800354559544445020403114442c1c01e100724400680704009004d90200c190800390000002c00096949040004240d400042140d109200c103500260ba2002c0c0c2d50892402102e042803206036040340900d090303a17554416008140d00c0364043c44001031503079a50000300841c600c20354800b68140c4c55450803615040b14102d1040c2964184441c06180b11440d0340c8080d44004100c0300840e543d100e50521401c040f2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 597781870 1250 597780620 597780629
    0xf0601060203180312120906090d08062106040b0108120c060a15081207110907230c0105250c030c080f0712031505040b0a03020d060b2d2b030207 64
    0x60085191003ca01100f440c21f40324101c0d00058075299a550350140d80c90b540a00380c6171000c2000140403a80500b0300d543d807005070021f011005401010b491078864603100c4101c90031a000d040c440700500c09500d050150019501d041d001042c01d00001d42019902c4000c010030541c0310540d0f480840440c0764440c0090b40051072018259011804d404072140d0007944140000d5444900764041c03240641131041d1507034400d1585036a01c1d00031600c0b0745c0099601016007500d141082c8810b02440c101c00e1428425907004007410340c080444980158554030000d4003d1031000140034010040c280407a4010410140969101c5403242d5181c200e68800c1080d070240c5180a019045622030b40c2c0c3c003141d055131104803091000082c10941d02d60b240108410340e04a851501e4000003a48803c10040c00c21400580d00544580f4022550007525004511320f201d0060704c0c80210041120451039441254040c16400302060761000640500644204004100b000903a81010504861001454420712081c005407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 597783120 1250 597781870 597781903
    0x906050f061926070f0504031a15120a120212031f03120e190b090405090322030c0609060c08070c0e01090f05010b2a0a02060a09080f06010602031803 66
    0x10f41c0c4540b035081801d80031110600030403210900b58103640d0080c402e450849501100312101800c2220070b034414000081e0030060504005a01c0095075a03480714450701540807003004140b581190300700005204031100f0308000707640010300c0071180005040c0481c2e0f03100c005903454048004111070001e01941c01c59202415507420400900c50345940084050396a110407503002d010044000c1c94104100f40318440c052181004004294107802e050304055840001581905e00349001d99090101103d440c02c0101005028100c0a00821003800d41a10181440b860140c00c00740c00e1150240c4043c803680006014948082a030700200107010b00781c8030161030000510852035a4664a41c8050004601c0c0420420f00740000806c10b507003400165924000182e185072000002d0603481505100070b40141d03182da004001e005030141c2c03200c10040007551240e03039408407043c0c034080c10b070b42c146200c0000440035600450010456140c0c00005d80380c07a020351041c00312031028000b000074a0700b1040b805000e881c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 597784370 1250 597783120 597783167
    0xf0312051503010c020f061501050409060b1b0f06040b0c0c0715030c0c08030a1e0c0e0109060c0c06031a13090309120c09051902130906050f0619 64
    0x325007405040c100c0c40401600240034884400c2c005a88503210305406511603881440005c1e03403616520000b500000d01030410a28080e141d80ea5803055540941003080a104002003501c1298040444d0040c100e82d29400740c4400b100910900d51902c41c044c001901d002001d9010036a801d64010446d8200419101118255541c0340f0749490007040004103080480e14140c0010071a5000300c05900c07400342c0c01040c05145a40f580140c40080c08030105803000f01c0035030800c0802c4c00b41c03280b040624103081600c44d0796041c0c042d04001001c0c100c4603080081040440c1d06c2620014044820b414103542c0242004100c2100349900c0805140c0500d0485a011881041c0003141503040d52202841d64007a0340d6074804d0070780340e52030f20b1100c0503420b100600c0130071141c8040100211981c000344d00039880000b0500c004280b1036261050303800c202d0b120500c0c85a850410407004d9000c0c0b04d40704c0102810f603041d103c95a103600000f01d00e4040c000710091310705081c545901300103110703c40385008000070500074603c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 597785620 1250 597784370 597784381
    0x904060f020a0801060212040e060d03020c1002030322020108040f0305160b0a060b0301050a090e011523040e1207050708070b070b06030304180b0a030606120c14010503040f031205 79
    0x10850078800c0305d000d809080c6c0b5803104030b5504d2040b035040c0e0317030003000c81121501c0d44018485580b8059400b60114010200e00c00d64a5407003003e0000c0090f001da000319100e00f054440c081e00b80265000c0021014641820600141d0b0015041c60f070090304034841d08200c0c0030508040d643c6200300501d5910000284081e1001c200a40b407071240910006038003004010303210740a400c480c0c807080c06131a5000c540c0308010010458a41c001c040b01c0c4003110008911000410968018001603411a000c5807183c0c59030701410905504050f0720700c0400310750502605214001150b00c840401c10a10104040001c0c81014880108201001481110219070b51695110310740c2c019074200f910304841e022240400702e1443c1c0b40000c1a1420340e90f00030b1600c080d0944461080000700781e80880300d031b0040042c0600102040da130b032044000900c0e0f281700132a4a0582d070301e4480d044d80041e81220041100c4481503800a9902c101580d502541c8020110843c0c0c406040955921424114a103c0103090404000c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 597786870 1250 597785620 597785627
    0x60603041a0106091706011a03070915200a0803071407020909030c15040c1715040c05030d0518040507090b03100e0f04021302033c01050105030112020904060f020a 72
    0x42154004a40c0141c150001805603071104000e104052016236210290b6100c802058001c5820805505101c0b502580e904a441404050a0f9012000c95818aa141c0011026240140003c10040083c00503c600c940c0c4900c00c0340005004101000140ca00c2e00f803441c10a441103421564000b4403c244c00c1c509401d5580c4d8035440307292035640d10f0060507041c0b010041d070480614015079000c211020300c5800c1500c800b98080da010850403540c030420320902c489001e844a503a00071070080d108080c80710300f40702c1411702c0c00300f4903000f5600700201040b1001180300c03000c0302e60000c00402c881c0403580b91529801150008071a07000b100340e940c00042400002228018244100c07201502c078490503070703508000243c0d00769003110082c0d000311008001804190060780199403020640d002403c0720b40c06000c00c40c080c0c03500320080c03c0824500c2403004895805281103d4010f050134a001c0f45158104500010000001e080090003041d0100100d0b080001ca5085400406004c41c821903c6404080c0e004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 597788120 1250 597786870 597786887
    0x3013303050f0115080601030c03031d041506200c0402070804180b09010f1203120e0f0f060a0e1b0411030c0a03050f07020c010c14070e01060810030209060603041a0106 74
    0x203c003804c0b102c0d803001508080c0414070702c0c122500b08071038095691a548013035071450280c00c8049902c1725a034040b00282c0d629031140100d40c4550300c7d00c140e0f09506003000944460b0092580108401040c00000207100300010711f0440c10a00b80c5026032030f40c1c81898400c00a0040c0e4210070002049048000e0780050301c0d502c54400032808540d005590f9a032868241440d2a036401840581030388080c105000c40e018020782001d03100c1603080010740300300f03c05840b420020000d0316070419400030047d00c08000d80820005400c04c074000300070808100c180074080e036148407000d40c210081440d00806940c0e40c0d00c0c0da001509910312100095038034502801c0d10350340c690085240602181c0303040d002c201d80842d501961803064006400404000000c0001562910342e26001101d01c113080304503a00400c48284070140c010300e040302014880d13504040016210100c01418071001c084600810030244e640c0f003d030320350004025503032103503243c030703641410760300120516203162440607582c2c00049c0c40c1c1e600211f039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 597789370 1250 597788120 597788141
    0x15090a090e101401050a090203060d051b010201060807080c10030609020403120f020c1c02060f070606030c120b0106080c16030801140d02060702102c09010503013303050f01 76
    0x30044001c60b40340f610b0010b1000e018598011040420030b208032142503008580140000f841010680351980d038040ca41801c0c80103442d54404030400f07045035941c09010f0301c006402d42c140600308043c00c00c1100c035a6844004480352041c16125119086980a030340454041d0101e81c2096640310740b03a0038004042c80c0302d0580a400a10340c010141c842c18408601c3c807041c0040241420001e00c1c0440c0803000c0d50188210903a800041080450888100080180030b0316205410101c0e40511b5424115541d9015500c13085001c007078480f041001440042d001070544c0c01c94244410360303444a54911f801405402002820624203407a03503414980c020303030342c1030403203a4080b440580007a042d82072203c00707601c2d030308004e40040c8184455001072030215001b6101d911180b40c00200a0100d103490784032041615045003400700c2030090847c241c11701071001400740000750000d00010310b1050900012040c3c91150980c41860448111030021030340601c2401150040e0481d81180d420400380c90081c10740d00311 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 597790620 1250 597789370 597789403
    0xa0503041a13200919140a05010905060a06080c130302030f0a050c01030204030309090c1704110f0108040506040609080921010605030706020307060b01090b04060f12060515090a090e 80
    0x48103501983c110355003000c540e000d840001982c56140d400c141c078204880001c00650b4882141020382d10401000d03074810303540e0140c0403489501d40004c000807594080c0195020310034604040c081c050300049403d40052080054503034a042000a11801c2059504025414010000d000083c2440022503086450143d401d550400e80000015000c911484c44000c011406440c2d04104100c001e900100c00f000450401c229804400c8034110000c003022071b001c039050455102d0000181c01c001200c1440078000313003006000390406403207440d03a429008000400c02902c1c2d244100402402800f5a402500040c01d140e0f22401070207001078828009070400000c82d0320302100056140b0f4001481c808031480354018504c0d1803010f85405018001d020903481c1400b400e4100002c04188950051000b811540d03101c11229001b0400103080311a641c4e40400442d08008040c8544da864070711251140100342032a65a0340b604801280c0d05420360341c000801d41c1d25000d41e018a500021030b514810060080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 597791870 1250 597790620 597790643
    0x50604030f0e01140d0e01110d0e01051e07020f030f04030317010506031b0405150405010f03050610200703050d12090302030f0d09050703030e040608060c0a0503041a13 74
    0x310225030304070402c02d202d400609580e05543e007403216072008100002c043c1ca004260b40c00b0b249465401d542c890384502007101c10019508190224a108038420007004034001d101c1801c00c0842804580c4c03070920056080703911540810940ca0007084140d4810500000b0703071351034201008002c45c00e900180700940204d03d65046e4401c40d0401c1e4075010f03058680003404141540c8400d0081c2a0750341d4189000130002804200c046003594500d1003000c03100d04400c4210f6511424000010043c4607132030040400c1c141800c091100799920325428914910061900d4070788500b600625246580500030006110702421130b0120a012001c0340103141045c5985424220b0303428004544e0440341d440d03034050010b800911040102c1c1441c680101401c510042000c5820303082034403118240245070b80100e0229200d08550f50b100e0602e805006c000b01480d0003d4599460320300b803043c50f80e11400a4400030040004000340030042d4402c032150001c11114816403941c03500c1c200c44c1002407070490f0b00799203400d0401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 597793120 1250 597791870 597791897
    0x50306040503071e050a0501020d0b090402010f050903031c06060306061107061d03100b04240b071a0106050702150a0e10030204080d0915020303010302010215060f04020705060403 79
    0x14900d024551100045203000c5040d1550184100c00704003104140c3c0a2410390030116030700b0481e99003800c5c050742c00181e58011100b8100300b22001e1860090054100100300030140c2c1c0c008a480304510b0321800c1c071035602c10050001034258032804603101c0c0c89480c180700e0341c1d0124190364484000c1d80d0850714104081c80d1034071020b503800301c801414076581c0e52007800140000c03403058803120460714102030000113206c40f50000074201940c0040c0101c41c6990f0b040000400e1030b0a01452002e0b07550001c1c2801000b50301d940e1000300090f075003d4007a1250300003030f186007003007150700c0300c0c1030041c1d40408140d030b4958503084020b106510041007a841107400c01c0c10140c419500500300c400406803521180040651007007401217400243ea400020305a00344400242c2a0040c402c000d041c0c1c03815660920b129041000140398800d14070321280031540240011300050740c0004920b1160003c208210205542e91000034a522005942c03880c2c0080c00072501000f008000a0410701461098030390382d900f550310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 597794370 1250 597793120 597793123
    0x150c1b0b07150e12040b0d110706140601080105030d270e011a030c120619080d08090d1b0f0507060302090f041e09050a0f2a0e0412030e07030803060a0503 68
    0x1044c0c1c01c2e07000d400c00c4104951041100100039055400401044560509002c40080d8000920548490f612061401902d03110100c03030300d42c40f0809007000c00c101c4d4140340110b540c4041c2484807005020000040d80c2003070703545860260104503214140c2810030b44840e58403014141c20310800c41c81200c980f941130348980320f1704140d034031500c4004441c0d4100107145040e118205009004a608802420306800c140300c1c0030305612001d008503000405060702c1c0c00714010b01c01030000b04503811581002482c2c5c1c03210380d480040c803152415510104100c0b223085060803c50103030b0443c001401f910034048001541901500039001d40c6030202d076201100710708803042c4000d803408500d04419140d1034604004484885501440303031140030700200c0c0c40c551131554500c41d4480c2005c00c02e4590396405510f2844081000300c011107030412050b0141c1182d4a00198080041000390000301041c0203007404014245c2b0941c030a0a0030b40700b02d003c64442c55501d042245c0d20303600955006020b541d400c40041401d040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 597795620 1250 597794370 597794383
    0x3080a0921030f17010b042324040b0a030f0b0616170d02120f0601021908031e13060c020309090a09060204080607030b0a150c1b0b07150e 61
    0x1550303981190301d03a01e40d400c0343c002c5111010401130241d101045800b004011106901070451000300755620303810448000700b882010069440c0e15a40141091400e8454141d50690307100c0c102017542000c60402940350407405903800c0a05e0154000c0359043d02c1070381c103802800d207401103500c04004000d007001c00d0003001d20491015044180300d44c040d42001440c6200c1c401040100340c40d0150400c010305d00b584c13040ea8018811000d0036112942441090025451031b6070708a00309000600a48a0b02c0034040c80d00c0307202c1a00070300803070000b00c0060020280c0100070017200c03140f613800e101c40c2c2c60428910451900f0100e4291240c0c0d00e0400d41466503800001110b4400d10004d2100040c0d503a442ea041000d400f00c204103d80c9030b6004d020009503114204040707802404c072078038040388050204017440300e58242640903403021000408550300c0c1d6a00200040001790300031411038208030303000044042d548684d52020800c44c8000602070144298480f1140341140c40701d500f404000b1140b0305503680c030704 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 597796870 1250 597795620 597795659
    0x5070f02060f060a12030c0b01140306070309050a080304060e060f090c0402090609120d030509010c1409010309051f060b180616050106090f0b01022b0908060103080a09 74
    0x240720030003081038040008001a031040008112041c600e40b075a06201c0c00000d102000c9010444030701e000e000f0050010a01400340c4141c90580e41e00b2003a410001ba55804090700c0607040c19502c80303590b0f0a002c81441187c03c203640012001d640c0c2e062078504200101200d5000c04041d0094801245056003400c22450140b40560000d00c06800c041c8104002503212400c01035204008104481d165119041900b00d880c80e0207000d0000740c4541d03c0068155103006203032145903458a195030600541051003914110102c122840c2c0b01d4000500507030050044c040054140c1c400d00c0880780142e110714010041c20200c0b200280070090790b89020340c085002e800400c25290020b464140d106040510141c40000020801d1610407586505c0c0e0500b11a03294002000840d1200d100310400d0400b8090007151140078401441c06003005225034108140540324441c00390f1400203401c010030300c0380d0000c0001d03010031000e503161540c2d81e2902c64040c0d800350050002140c4281c02c00034202c28207400801c01c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 597798120 1250 597796870 597796873
    0x41e03022707031e0e07091a1302040501020a150e060c180a0806220b010806010f080312010306020c0703081602210303010b0f0c06090a050f01381801050405070f02 72
    0x3450344441c0d41000e440f201c1d00405d00361049500014142905000e0b80d04502d15903d44014480900c0c1b00b800940e4082c0f521885049004120070003d60b42d002416804150f049000780c10001c400040d0800505003085660b48e41d841200188681c0d0a607510003404000c0da91884150b0742200c0400703201c1042400d10401c1e000b5003100d000a043c01c02003440340c90800e580060b05100d902c07000d5031043c0f00008280c015100b1503100b40018007a242c11a441c480203820004002d43c00c10810041d5808940700c1400000c1c002034012881d0307074480c4820001c2d40c019503401744c43c094985001c05000c0c0211102c0d00001d82c030031841401a5000c030450070442c0d05050001102452a507070800b0304252036580850442d405d0305408000b0409002d005005050107000610050243e04000c1e0034800c2c582013100307440e140030f03924041c0ba03913603010b094040b40989068801c400107000184982006210340c1c1c005022508954121044e00c012403c081d80203041e907508940802c01074a41c0c40003107480e2000c001036803015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 597799370 1250 597798120 597798161
    0x1090302040e07140126090c0907170a0603050c0f030c0301020412150b061608070b011215020f09120a0b0717091c0c0c0f0609030b0606030c041e0302270703 69
    0x420b46d0144459200620808485403030038214007185511004503a4000065404020151401000000140c1050340c803202486002d04646503192901d400d50411807045000080b00e11250700d06200780ba1948600400840d1120f550f174907803110031801e050088603100044201251003402c03622071980341d608050050b40c2400080e603002c5c9440d088086050b11030320410302c0000001100754001c0c0b80a0034142c0e0400c1e804401c0e51508100d480d40c400a8524002c1c014424451031441034825201000012900d00414559030401641048820800900040c0b00b04d81040f80103034003e43c00b4011460880301c80500e179a22808003649441080c0f90041207070011105144085205600000c8454040c90940105568a03108034128a041e503100c000840d14641d010000e000d8000c11b000c0c1c0c0700500351603172851071508440400c4a0301c22030082c20700001203144500504400c00649101031940a8400d040318110030003ca00360500700442042d18000440004044600c00c1c0204400301c20950b101100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 597800620 1250 597799370 597799427
    0x810080a031b02040504030e01120e0d05090a0f0b040501020f060601050901031e0603380604020309030d0f021b011514042009180709031101090302040e071401 70
    0x14481d003840360440240000c202c03024050b136074500c40c603402180f103603c07014003242c001c90000d40a4042c03011510071052804040f810f00c0280403511042017819840c00e10360b90340300440083e00203081c40c0c00c000002c008280d004140e000807a00240240c030401d0302100c550318507981000340d441500701c0713000e80003800c24000c1d4900e5500903000344103402c0079a501d40d080820440340700400c07191503a10a9800000104450b04000001000d09005042c08a21200e046045906409c00381c040030b0486401642e0010001d410000140180e41140c0c1e0009814004820600701c102c2c040c0d0040c900f00f1603200e15041c8904c810010510401491029040f11240b51a00d05400504980d10180c4019001925000c8030811840d81400400c240240307401c40e6601c074100c10041c811004000d03c111242d007005a0b01388442c0e035400440c03400807603a00811440207400c0e03100c01200e010031554070081d00070b8105030b0180d54001000c03c502c0280d070003d45c506202c041c140741c01101c00400b080e0b0b50340043c00010311000d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 597801870 1250 597800620 597800627
    0x90d05040b1308030a020106090b06090102061305010b1008011e180b0349023007030c050f0303010b0412050c060c0303100509040b06041e0c0504060810080a03 70
    0x60040c52031110b0308240743d5181801429a030000b601c03203005035500c17a0140074604103482015403603031041d5643c42c140841503001035030321000640700b0f15496803030900180811100350003a81d07014070f0103000c004524852140c0980541e20a00400c11440c1d015050b807500120501d10020449046048601c0700381c2c042035400c802030000800007600f601402d40321000000350a0807644000c2060f0504010314100d0030300222440b0486070904004615840080c0788a940c001010000900c285a4145d02203411021100c5004541b0000321210800814200700389604003041d09001030042c0140c8011080e40d400f820307204d11090041e580704000901c03042c0050784c001520070b50071034490320844004056150000c0e0702a0007056810305c040d88004200803005152000c084000c11081c1c0e1188400e003070554070748000440061829000380d03074911000c841c0345910a1040c0002d15012810003441d01301c03040082c49a40b10b4001d400105000c5000702c0c20791150105004211200380c0040c04401c00143e034104d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 597803120 1250 597801870 597801877
    0x1030209060d06110d060801050c0306120f0615100804051c020717010915090b0402040c0224070314010b0403110105191d041e0e01020706050a060806090d05040b 71
    0x240c00c1011400002c00052062040280d1031103c1301c1c1d11900c5601a103c0c00082d2800c81e040719030140d040609015031144281d0903250420701c22100700000f18220b1003607500d0554420300300b60180c410b90f010321400c401101040320504809031b80044a0300b11328101510507120955005101e0361010309070103c0030005a803c014480310ba03205868591386d454070389001000806000019036551150310b5420801c800d0064844440b44080600070f8105540340c403100b103070f0008d102078000c3d500c5460113803041d442404402d000a6810314a01c3c0e0300d85656003080c0482e4811103070f4a01191518001250800701072404604840440d0841c43c503080c1141d40304a0090030360781a00b0f05001050000c22028001c0c06010070080c1d01d10340e00c40b101c0d038542d2881419000a4012100d004da45071000000307101c4000803000003500c4180c0000b00301100d0b2451540e0080c4901e00028102911340010720052580c141c100b14129240304044618a8035001c00841d1100c100f0010030300450b1040004210604025024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 597804370 1250 597803120 597803131
    0xd0b060c0d0539011d12160602030a0e0106060207030b0c0c0a0503040e04030914030d03110d090f050d05031e090304030b0f060307060e03070618240e0409020901030209 74
    0x14560143c07400c01c0c0c41460350825001281c052001c1e8524201c104024801c00404070802007031a0b4400608008003911180300b4060940300714400102c1d500b03040600d14104c21001d40c0103600315900e10b040c400141c01085000004030240d4208000000c1c860310000c3c81c02c0c29030380c00107544807907a21015400350319a4030616098400f4021000f801e00469018800703807000b0081400d070003900e4645458018292440da800c07000e2902001003020f2202d80300050070100c0c0b018141400600e4805d82200300029000c1d0328018000310742402e130000704020035185003403c02482031084400154603080b040c2c50302c0c00304580000ca10301e5004240c0440405056a558010807040196850310752640c031040070390307002124074100e1340c0f4a0f002405464201040a6001803225140221a82c0803200000c2d0b02e4203030922454041114408240005242000303200340208001c02c1c3c80848000c14054510080040c1240c0c600403400c0400c2c5a41242464001d601e002503005104c0106a82103500300440308401500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 597805620 1250 597804370 597804397
    0x705040213050a03030f110706050d0203070306050907020703060b0f09040803180d08070f0e1e040e07060e0315040b040807050c090103030306140d0b070f020f120d0b060c0d05 77
    0x1c0000c0c141c590074412006103000390f40b5072003400f40c030480280c60071281c841001042c0e44031850400c0300307903408409d8031501d070410704025031360b525402d2084000c0c1c841504076a9004000b40c2c28801c0343c6400144000490340300d01c200b0301c1543d12400c1080b04c60400f4003500b5801c216008005800520b40c2002154000b07161210800100d851803070803031805a00d01d6440d0080b5509a081c170071610303080f1000c45134101c0d803171504541c2c0403202000f1403180c401036a40c402e040d0071352200421640d03413181c00c10301107030084000721410a56070300e03002014003500c0070300030340a4050006644032100d10760310100d1107150032114940345608d0f55030310360240d070340720003415641400b84a041074005d40c2d60440c3c581c000d500a640100b010fa040000c2d44403042444503255100d4074404841800040c6200810b0f90310500500b8800389034261b642099040800c51340c40401b0070b00440342d1400301502044041e1100c0c89040c081003003003007050002e1100341e20030401d20b09603d07407043c14030001c91807054005042102c126036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 597806870 1250 597805620 597805657
    0x2070614031605130b070f17091302030601210f0c090602120703090324050106050c060411010c1704210231060612050c130e09030f1b150907050402 65
    0xb006038046e4022076800c030f600282901043e001d005501241d900103038980c4801918200c1110001030001400c000124201d9070040000381c0c084c0e00640d070340c243c0ca545006c01d400e0f8800110380510010541131060f450540d28020412961501c54820300e03064820395001000001603800c0b100362680c000500c22000c11021040110005034112840710344070180000b000b550041417001041540e0050b0440800c00c02e0a0000d40703031680c0b00241e116002074211000b4141002c080d40102c56000d585c0301e02070007086000e13620820a041d01c0004000f00c0300002c004120504a46c02d540480800d0010082d6000e40440e00e100307207410903542c0c143d8010545442d00c4240c506151b64240c00d440d81507000e580420603d450740e080c880210b0003a1580300941520303052504811901d605c0031542c480c054080c00d50740d1800090b00c660360800440d9442c10910401c262030304840a81c200502c08406052402c0740a00c007003054a0b86000c5503200c2c003d07032803e0050a5291300303007010f1000035007006000010224164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 597808120 1250 597806870 597806879
    0x115051204150606020a0b011e0e04020a210b1e07110c1518040b0a03081b060a1b090b040504090615030507030219081b0105070606060207061403160513 67
    0xb48920f40050055070050100202d00e414800d983d41016800ba00c2211035040b40b035100000c0382400780c41a5181e0703c2c0340e00015191800450803500302a00711000c0030030325000c80d160005941020b070403080e00c00c62300740d401d90b5035101354070b0007080c0258030520440061602049001d0301034064014800882c01c05c03102d03624000000550314140c03100000c61280c0e000500c12101070800208001c01003c10b58040c4940c0f106100403815000c52844050910080461482042d002a40c09a600020701c00d045510341d041031076000c40101a0007070301513179010005000d040c4039400f404e842e008840d80d4600b59810985003900303010191050440841d0340303039907480c1c074042d03c5c0541c501410041c40c042c00c000c0840c1070452040c003c1c0c1c4824004d243e604840010030811a0490009080d03041c0c03142c3c1c85000c0038004605006a83c41e02820703600400507405c10340d002c14026400034108003110305940d5070194000d1025004860780c8400e40d02c0700560214000b50500c0f26000710002c0c01041c0045125042c086e40d00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 597809370 1250 597808120 597808163
    0x41110050301150804020a0909080f0c070f090b0d1e020607061d1b150d09140115030f0f050f1603060b121911060705010b090115051204 60
    0x25a000861004401404101c00e41d80c901008400303241854819410f091300000c100b080103101d01e2550f10f403540048c1082040c2075003921003154041d04503540f02d170b21490580d5210b0383d0f071f405842e625420740708000a140f0761074081e01c081044d0203024941100180e48500421126500059050480a00d50040140c079003400820300d6a0058070300180039100f450a100361400712000c130ba0f01d240d000c0016051145040614840b14034011100f50b4049040707841610064011841000c5140e0320305000301041c800d403429400c1484429800802003416207440030303035503018140406000c080c410f044080005040000400d00c40c5d00a400300d45540c40c01a004234508030b40d402d8001c603599800c0104008000d0b00d070144500302401150140100c4908081c60307540e0700d081e2030b5122000000c0c9080d840900141440384034003c0c81c0500503940c0d94100c0d00385a07019041026500d4083d8110500000c0c00000c5411100440c03541641c41c0380c078101d4000f4240c208294040e0055600d01404a2000307443d400303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 597810620 1250 597809370 597809389
    0x10e0f030408070f080607180b0a0f0e090c0f03060d050a0507141e01030c030921110d0819060e0f04031d0105090402070515010b032502150411 63
    0x400000d60303960341010140350030140c2c84d6000400004400b20240305140000c0364141e0f00881d5480c201c01040341400464001e54255449070034940000104154420303841030303503c80350506540b5901c400c0c0c03801205100c4005030032643c4983ca40340900c203258100030700d40019038126100420185e210b190a8582c80c1c1480b01521040303401d03034403007501080380d0342c01000c10080e00441105c0910b0901a001142d9000c600007440c0c4a040560711103000310740c2c60107948a80300c1590003022aa07241c1e042d00074258020080b024a40d0081052801c1d4021040800a041d00018070240e03581e4519841f1021103c4282c030580c0411400c241d180c0b400410318100c040c04a034801c0b0b51150341c10a160a007070602030110f4441d240403020880560401d0407059804c281201c080110685d80140d8400203820a503061132002e42d844c40c1190900800014035a4050020b54002c485401282100070710300c6190380d00641d1071101440158000f04a400c0102010300a4294807131701444200b0300041c010400a02100b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 597811870 1250 597810620 597810643
    0xa05070213020304150207020109050f01050712120b0a0f0501141903061503020a090e1906080304060201060b0a020d140c0316030f1701090e03040b0c0102040509060108190e010e 78
    0x10750100c104414414000385c0848446a049021842c003003640d0000ad042c4c041d280101409800703821040d050a920a604031030256070080c425410305180c803400144480c407621100c10383c150524402002c21714144a115003200c2440214400301d80c5040010f5600e001c02175050940303d0000d0008500070101d4180d9840704074217540d80010920b0500780f00b90350205426204000305441070107480701e420707000f03a003000c01d44035081c04d0214241c0c0d844185950700e2440031a24102a818442c000540610000281080d80d2803900203110ba552160005e82541c001e80180c000140d104130b4454902a0281003a0346070030580641c0705140141803040d491440c3e01070281000b035800c9210036402810350001c4c0f4503010814500c1d0212140883c00304d00708001d40c060081181c82c80c4e4902c400e510540d4100f08403070003003d4600e00941c569a4040b1401c0c000e41041c45140d00560f031440008403070398458008684618103c002c80741c101910b009014008140c2c441010840d507583c0ca503401301d507c808121015100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 597813120 1250 597811870 597811909
    0xf060403110105040b0406110111040e1810090606080c04150b0702010c0b0403120608030405031023070207030c0b0a12091406101a0705300a1e09050310020a050702 72
    0x81102c2c14232406c407030100a222100c880248014030564040e50b0441d500007403030180c969030101c00000041c0c240b0f060301d010b0740c88182c504610207041001da500050111114001501d0400d4100340500003a540c0c0e0a440d04400c441010003840b21a00a5001e03020540c010701d000518180303d40c0e1a202d08140644082d0007085400c0d92140c61207a4a00035800034024031300c081c600709854400429070310041842c0101030f0f1629050210900386151070b8030a80002c0118182489080103c0081e441d48a0b0740025941a2070b01000490707515200c00441d00b07240081e98070801241c40c425400d1000300003c10302111124154100040c400344100040c0d4001c001032030042004a240003000240501e00280c41030160005000e26404100c011031302c17042c2c1440801e0000e00040411101500c540000c1c9800311100700c1c0402c003402c005600c0b00040222841a240c0e41280000454040c1c0c0c1c0c0f80068412141c0c154042860340c142c458103900500b031206440d0074031606007051075001500382070501c0b2080048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 597814370 1250 597813120 597813137
    0xf140c060319051803040510030f0f0501150816120f1a03010b0a03080414120102030108010c17044e0320090d020a090e0d09050f060403110105040b0406 67
    0x10300010311600750040c44d50312091440601d22005103440e030040e1310030548540ba0404600060b030740039810008134a907003090104108d0440c1c1361050001c007000c3c040d55000f151651028601240100d5845004d9480100c5c40c5102681c0c00904803211401d0304c03444a03481d81c40d40c2c0c100f14084e009010302c003640e61903620015652301c00781041c1400c54204a1455108000520040005c00d81020032542035072050403050000c08940c0001c510120a03185180c00070303620000c0005080380065000640349507045c4c0c1c890076402505c5e004802000c000791406002c40440b000c40d00d0300e800c0558142000847c10080700c6d003264000415112003250b0903905075040107101d4034a500100d40c18450590003031010100080040419a00301540d4007034100385c540602880003005080d590b4031014032005082c400341c148a045202d09001392940c883d1048000412401d9402080781c3c5440030240d101c0c8040039081a09040c6503403030300a800741d08844214180b18041001140c09001e801c01031002d0103440c4c45035240e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 597815620 1250 597814370 597814411
    0x90b0412020304240203090607060207150504022d040e0309190e13050a0c030609121b08180604080303010f0503120901260108011a030a0f140c0603 65
    0x814240501a20342107400801042c070441d40070000b0150f0f482810b12283d203501203001d00680c51845940c0140d5803008000c01c1a000300038080d001030807000d10400164070703800911010141522400d4800950007029a01811903a4035150030030100d0380907440929886580c3c0d880450110740340424544025000007030b800300c250810000003100d0203108e4101200d10b40c5000101440c2500c040e003c0c5401d25103698500061000400101181036000382c080c00310b180d40c07860010020200c48a00710b0303501d00b07148180302806018150300700380d0b4403820150008590203692040c1e503d901c514482e501c078400002110240c2e4841c000900302500d1264001d6540c1e5051001c22035000007142d00c030520a038820700c1f052020b03103000030a8170000d4800b802d00c5401d00d40e4100300c21307140c03c40080341e246c2c940c01c00c0c4000054441d0150886c01840000c1000310401c010504240b68590074032100142c1907840741040303640051300c040b030701480c2070b018141500c034404203150014009034030613034502012442180e207440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 597816870 1250 597815620 597815633
    0x8090f12010c081305070510020a23150103020a09201207080906010f090c0e090a0605040c0311071b030506162715020703021906020705011412041104090b04 69
    0x40d005007444c8000c01c0821401d0782d466a0b038403202c0c00b034280914180c28207a4010f034002c200e04c01c0d040340d0003041c2056000494410726000d807a005060350941c407035904071080c09a054040281665000340c800c00c5014201a600b40241880001c094011400300c0030801ca00d10504024203900303040c0300d2041b010350900101c0208083c2001d450f418040c2c001c0d1004000043c84140c0003001c641c550781001c01c6210000a040e14008210525560080c5a01041000036030f034503800f101c2960307822a010400481411012021100120310300340c01da11041054501064680302441e00201e00c503203182c40919242e83d540da08010381a503606900d0300b81564680d41c0e01d0340080d010f400101c85650444140f0544440081e041da24501c61410b2104201041c1903403540709001c01d0b0017454028101340d41419000601c3c1082403418400c0318014003035040040f500358400c40b51809500c0e038800c0098201001c8180d0003800640240080710640c04080d0a064640c54070300462a1890003031420401ca403800e0f05000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 597818120 1250 597816870 597816887
    0xb03040b0f010f0f0302010e010e120a050120040b0d0b0d0803011508090c240f031b0307123c0b01030c270f1701060503010902010c08090f12010c 64
    0x8078066500030f2024032001182c140303200226502403a008207d0040c00f0f00503a07520705041f0015070020240602121065800104e01d14a90b01c0380c0d008000c0b610502103000310242d0401c5920a440b0810042044039090707100103881040400d4400240381034006002586948500c80c04540640707010004000c21000030713140503c190300c00d007401c100a00d0300111080d00e41030805401841130f010111107850700041c2c81d4640c1400001214150f507141990902c010481c0c0040360004840c089001404001c82900e00540f40507841d91b442d1002e10508101c2d10b00060075440b502d0001e04031020303406043c8403142c0341c043c050200202c4001501ca46112071130301c1c1564a02c0c44071a0505050075030740300c03a265005001210000e0f0ba402c070300f82c9584100c0302e140b084260702c1e40704520340d41101e44049001034440c0b0351142e0b8501200d0003000a50b0340d440a05090302e0721814080d0101d0500d0449401003100708009040060000744449100c5410703500040e401c01101070310042d00e0395501d1044500315000602e2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 597819370 1250 597818120 597818129
    0x315010e04140f092b0c1106030705090405090a02091314060109020a18031e0303290102071a07080306030c120c032e09020303070803010603050f0109020a140c070b03040b0f01 77
    0x101700070b43c40300b11003171059a102010401e0800a00221720f1003485503050900c83c1c5880002c2c4155607030f0800307420040c0a600559440f921540c54500440c2201c44001a2500d0084d40504080300700d40c0e030500c0e00c155a40415806035084044240314842e241000d014560107880c07102030040e120542984000c1c1031130000c40e10140c0500640906001003a05040e0200781e054075040e10080c01d80709031a00318090042e02d100412032407200700300c00210710b84049440040100070303030854403103c2d03480030340002c209040e660404111030208580340104024a0046070f100001a0448600c10310042c0420301c0190101510049500b00301c0f20b50910f4034051003580c1040800e403100300038480305242c0000e000100710100c141050703615070300f000454a017401074541060b0840c0c5610b8980d80d61f80d50103005000225180e2441040c00c9002050240c9203209480c1515020390b03500c10080020490004a0391052550b5101842034060010b0040b01c010300030b51255200e91009038160501031016007031808103070071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 597820620 1250 597819370 597819403
    0x30b13030306080c0904080c03091306090b09070807180e1303030b012a0614040b040215280e03100b040b01030e030d02070c0e0412140315010e04140f09 67
    0xe18182c940c5d40072082d6410036042400b895981c08045011440c2d03105410826800035054502c9820a4007690701020458000b5502032140c0c000300d42c20051550411508100441c19140c04203000300c2c842c0c400b0741c500c166000340b16000691604070003450f0340001c980820f6a0036413082d48030100340d45130141504c1a5003c6c2809078648205c411000014403500740040d52068420b138140c420300c0780d240c0020042805200300d441c490704060404d00c4800c08111410703400390300404540e00d42c0c01000e00440740821281c00039550107080e51190f88100d040354240d682e04020b003000c6540e07000d640c02d000285e0741000c2c0c0031000a55000082c00c1c04196034000e103080d4140b51610100c1045050003000715620b4a80d1005c0069442c1c10700c0c40e1400d036498454100300301e50b80e0342008201c104403192070390050403060f40c0c0321000106130500c03480001c2e110843d14070b03603840382c0710240e4250342d4080d814090015600500c0443d199031100b400c0300400200329103103904428440b041c840824418884001d000ca070441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 597821870 1250 597820620 597820633
    0x403060e10060b0a12021303050304030507150e04090302011b0315050a0506030115110d050a0833040f020a0c17040e22020d03050414040504110d03020304030b1303030608 75
    0x7007543d6002d03001d0307024240f064804285680c9101581141c1c0850744641c01d0040d070380d0f100c5c24916940c4c0c03c10f0004440390310800138003007a16103000c0c5106060101c207560741503503c2e110000b0300c0b001e0301c4104005c070250340d01c809802da81c00403180000041c000003035500140714440e280e40d0708110001c651210740501c040200030f004684480e03003100d054490070030300711504843c102000c2b5089107880e03662000134000e040d40c001c0c14030303481002440000010755811055407070b140e0b04c98404150650a4800c4692620074400a00e03114018405800b100200005046441c010030002668000e82c0f09900107019552850100480354040650502c480c0c5a21421f040c10188100d10082e406420015031182d9207040f84e0603010ba0400540b28240e01804d4420000142c0c0b030068000d402c107004400124000182007030450070b1522a85106a800c40c501c2034951a084c02404840030045409404500042102001091502d2140f82c02012a0001380802c42c640c3d040050440722150000b0302c03150004d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 597823120 1250 597821870 597821879
    0x3020702030a0f02031c080f01080c01171e010803030406270308060f03030c06070207050d0201080a111b06071209031d01271404060b0d0e120403060e1006 68
    0x510500e0b0658080c3c1c0241c444030160001903e4000d00b265032011940e805090824a0707a0700c40e00d040d0052000c17401243c480c0c2d888031030310754880c0d0105280d107001951480f900c80622440c0c1e034866410900c0143c11000d01c405d800c440c070040f040b00740c005199a40c000020f0000f0803246200d89403900c00c441801c0d511000009202801c100d401c0c901c050100030911002c5500366440c4807601844481c01000c59030b4580b06540303016140e45080742c0c01c2016014a100005150414181c403034426641691090065501c0242d02c0e8010465141c109411440034008031250350343d500c1903080321242d2507005100c0391a003800024100e00280a283c00769a040c09850740000e17800c100e00041011076101c801034806504401201c3d4880c401550400e0132491010045401d01040c2024050713400c80c1300b03906203904242c814002034440340d21070380e400c540080003060000c6c0959880241000001b00c2525651080001580d9040d005508281ca0103a9100b600450340d05042000203070300e0501c10018400c09161 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 597824370 1250 597823120 597823123
    0x303090604092703020d0908210f040b041d0703020f073c0b01080d09120c05130f18080313060212090d14030c0307050903030c07061e0302070203 64
    0x5a100c0e0800c02c5450304005421039543d1107803a002003100d140400005401410700966400d00c8441002c0410404040494840c00124007031148079283d01341d03003110f4240319038083e840340c0c00480c03003500221041c000400c042602d00c0082c0018080000c542c4544148441000141e01000d0511014144104090400010020309440340a074001c40309000414141c42944940316141d00000f1110080443c00c03414035003003410324140540550781c3d011190f0388130404684d6030080e140746000800d103000b0b0b0801c90120344295140302c2d68412030001e01c0c0b20703607604085007608000d480c0701101c4648032030303240304000410300c15a5190b00411324a00000025603d6246407448003800c0c8a801014042100c1c0620120f9011607441c1d401001d02e07a0040d1400b420384584814804410f00b000411442000d880c1d0314124080da4024250451000d14540710302d44181c4003a40600d9113103800d0f02040c4002200c0381c2040c0301e0f00c0c0080c21141c1ba0b21402c0741d1034a1030700403e070502000035010f052040c440f60700940c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 597825620 1250 597824370 597824377
    0xd021e0a020d0308060402121609080c06251a012d060327050c0306072d0c05010e1006080d08040f060908031305150105010203070b0c0f0412020f03030906 68
    0x20113080280c2d1984404000c00e029203d01111000440d003400e051091500c0701200c0144801082c0c0c0e203481c281d035180c5e14902c1e12240b82d0b03001e00c2c4d0300140c18000d0380c00e158a40455000001d0303500614810300c8a81e0394550000c802201801c03900010780b0300040060348007078050f544146110207015807208514140407012040384c1d004140401d81d488031008044130a500200c644420024103020500360140b80c556a00c42491107a14041d00800001c5030019001c1e40442c40b0950240c650041d200101441425086203880c9040081018400109001c202d082c840c2c5107410303924034050003650281b04844401d8230003070790002c40d45900a401440e410381d8011109500284e212210000340401c505190002e00822400a00245000810b00160151171802e070350500340702e907040e0f5000d02034144180c5171440092103000d000d60401c000c1c12001411100e12280e20084582489050080705556642260000c0e04400c800d05901380d000c07015071030121083c418070075040780298070300901500420030070300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 597826870 1250 597825620 597825623
    0x13050603010b1b010204051e04110f0316020102090616050d02070b0a1d040e030d0b0607030c0807230309040e060105010f0f030222090c031a061b0d021e0a020d 70
    0x10320f45076641d4451a401c3d0100e60090200611a030204507140c208028090f409070303145841207107003551550507480c00100f62000607110064590459840b500000b02c0c00000000e050119542007040460540d01c50000e400d03060500c001000d40c4280390710b40f640c0392800c4503c1000545d0b001c00710030060350910300210b039164460f9103442554506000c10b00c5040500c04a06142d20904002a955046100001505907142408418041c2c04000f9003481400c0c441c81c507001c2e001403594000d850100381c00c00010403c162154100110b000400d03010300325800002170075100c4581000907509000d160600071030002d24820030103400d40d54500300000e0000c0419400c80414882082c1c0405000360183d0706039101c680f40b5016100c0c2c186548000200402c00c1c0717010b000d03811807034000000381840c400c3c40b5a100c8444012a1142c1c408095001c010301900001c41048442c220b42c6076900d000401404040c11080141c3c00401880c100301c400e1004281481c0b1040388a94001c482a03405030b038480c0005542075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 597828120 1250 597826870 597826897
    0x506040c1d0409030909020403120f170c16020a0e010611031206010e061c0912020316020616140303070e09072c030a0c0f0807050604140301140a0213050603010b 71
    0x440d58602a00d110003641e021206c0c03144046800420710264940c0100d00070a550740c0d080581c245800150b650750313109614104055140000200300e590303810014004c4004c043c0480300400304a500080c0000300c03a4101c02ca40c130b02c40f000104103450300803c024044e0b50065028505001d4084207034694803400600c1e540c10416584074014882e00c0d2481200e403c4403e42055002000c1240c00000c0600004401241c40c0b0072850b491108451011043c4c44c1402c02c40c02d126610b41c3c80d66020050283c0020183c1c5000c400c1103d64040060003140c5000c0040d000100555106c0c60005005803c4565585a41d8080d610703820821040c40c0c0c1c4103141d1500b400c2c01c688480c0c200507036149041c0080b00701c0840140c0611840c1d00e041e05000c0c4126070001140c141c075280d484440d45500420303403280824070807280c01840510041c0210b040d6400c0c480424040503000044849100111400300641501c003400000c3e40012192240b05140101601801080d01c005103154500048078045100304d00c2d11102071f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 597829370 1250 597828120 597828131
    0x10c050c1b18070c030f140d111b0a0b0c070b04080d02040f14190807030623010f0311010804020904110a0e07030e07080a0f020d060b090a0506040c1d04 67
    0x1580c03403281c2c1d81c400164800781d655051030b00b01c0c0050051641854103602240c1408041494540710b060756041c1d80f000c0741c10142c184400f1015070300240500181500f01814240701ca1010144040b03d2401c69544420003085512610306140f4602c100190408588800070041407002c40c4242c00b00581065000e0070440d42c80d207404010350002e01490308501c0c40005c065000041c4c0402000755081600303012203d1100861488100d8900c6c45421b01c83d4070710700d41156030f0400200f0829400704550f901140e13150480c120a40b00301c050200400d13049149904142d00061043c0f2141d120b888542e0b0700282040c0380c0f10b04003a0001208040000c1000b422000b0032142c0300b01c0da44601100d80010001c0c8000296903040c048030240162010300780d05c0800d0310400c4c80005e5401c20000d0103a82d0207400c654000e90780005038091000c4490005021303114261200051440754070782d018464800c4980c40c8001a06080c01b20401c41500c0110403800704010a4a1001001000607043d00381d50140441b8001134 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 597830620 1250 597829370 597829423
    0x106061103161e170d0b0406301202010c021507080606030c070210030b040f090c15140705010c0305090c1e0d050609060103061515030b06070210030e010c050c 70
    0x50a00c800f20f4000d2040720042d100a40c0001800003400240011030424000c003070424040c042104e86a101f03182c02c0700e48000e1503180e000c54112000c801d007004502c001c0519070382c54031440c02c00901a610f240043c3c0d503035075541f07803860f41c14401088503481c144012885400c10a900900401010780384610514000004c81c21024440c022140c03071650203080350011040044000e0020641d40e101c07a07010314200303141d0400f213a900d0b01c210452564455451241e55003804001c07902140c1c0010001c06011010342d40618519003038024201e01c41c807800c0013043c141c0041000809490002c0e007180b4203548004400c419590300c0021100d040c03245e000100400082c1580007030b0494484c00000b510900410060007000003005c2001030503a80200c80500001c00c4032031550003040414440c4644081e802c6421a4203117104e5084000b51510007812070341440130640005480507813403c10980407a80d50a9940c00c1000c0038018010031940b03d040160903c0c0301c1c102c025895061504845d00d410010245141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 597831870 1250 597830620 597830663
    0x1170312060d050105040f110a0305120f0c07080a0c0e07271208041d01031a040507050616060c030608031c1d060712020901050405040c020c0303030702010606110316 73
    0x100868018001748424101411700070822010180181c03400c5501044100f964244003000c44200c03070b8418010224104a05540c01c0035030056078080f1140b00303013004203c03851401004a18003030074699002c1c2c24400501c1c81d020010701103d070f100041c81c490180401505a0b007001501598500c07070502e24022024007070010141c1c412a40011103164680c000e1001804422000390003940d01801c80b000d0b025020760318810121509100080498001c400f031100702d440107210300c40d0000d100310100c07000691a203000a095410100c5400950004000c04409019840c000c001e0b2101281c2803c21155060101182c2c50744900700c40381134107075a02c0c1c000b1018200300b036000d0400300320070040100803990310240c0f003078881400f86d440c0c00000f5a400103c40c12030606100b101c08000b41611568546031400c001d02001e8604200048194060030a10300080e4405000039445041903a000103892130800102904409000c012441640e20603c54101d070303803000324800c2c1c40c403903001042000040450f80750300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 597833120 1250 597831870 597831889
    0x109050f150f18091b070510061d06100206010909050c060d0209190f0e0c070605070203210603060406021e0f041805160f05090301090b07080117031206 67
    0x114440c07400082a424030409003000c1d00700d24482034400c20001540804004a07684180d50a01c0c0c006042480c0f0840c04000000a0031a035110320196102c00d000e1002c071300304440d2143d00900e0a0320183d001019203503000c151040c0c0c0040103c542142004041c1c000a40d00c1e8014042c1a0495641d410000e080c420100040507039200001d100c2c55a42e100d1030303034010294102002ca07a000b00320391300103040c0000c07100c0d03014800d8610a01010308400d141075078204110760302504d42c12585004000e07241c0440c1990140c40c0c032580320b40e00210b541c3c028a00c50f080c0403d00036900c25000d40c4040c0148031080d42d0114282d40c2258003c8401360303d5039464802d68814800d8114103441c5000d000520f511b80d110424080c100711412a4641800030704000031040c107441d012164030302c0340d41101c140a00601c0c011000e112412051340b41c0281442c2a820100b42107503403017001030741d030029241c0801c1003007070b0300000c3c0e1742c0541152080d00414051662030b5070354a024040011185d8000140020700544403c400c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 597834370 1250 597833120 597833149
    0x80601030b0d020d080714070b03060f04020702100903051c0c1b0e04050106030303050a0b0d1203060911040801050603030a020307060b010e100f02071502070b09041d030d0b0a050109050f 82
    0x1a04c0c2102d042e1503d10340c0343c0c4c001c44085407003a0348070b144007038400700120301e4034103d4114020381342c5107603a9041000010340c4040503440c0c0c42607080c0180c2016071940015002d03003081981b40c0c0700d0a2030550502602d414009403602c1d1400d90103502403103405a01c0303103102d40381d15031000400c0310b80042504d035420800c000c0c0e0001081580e40004200030721005400c241c04890003a101008680c65007000d0805407031103141c5081e0440c40780e1070344d240009c005801c424420001481e0008001da151148070050301c0c030304a48280295808102400140e070284680c40d00124100c4c01149000c111143c00ba483e80100800500401d669410b03500c0a640a03508000507044028050113903403160710700c003030003068956001000600c140c59004c02c103101001c54003540070b507a94000f012080d01e07040305d0141130780c4802011508240c50b800c14105021403402009407512a00000d0b60b290030250003504100c400d012012446a9800710302088580d81002201c0243e44003550242504070505000c1000c04c8440e615 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 597835620 1250 597834370 597834379
    0x10503090309030d080f13080417120f0901080c070b0c0f070206070c150903032309031c0f031e0c0c050601031212090503180109090e150115080601030b0d02 69
    0x4201d6851544134400d180318900c01c42c02c3c2030700c80d03d03941d01c99287e008916000802c2210104001e1100401070b1044090401c40c5408030f0b00d070015084424000b0f5001509010740d0f6134000b02da0a1203642c1c0000540340e01005c030303c60103414169261030f00744103440082c0440307034000400a58140070314810803c0750845600039124035501c40c514074007a1004402c0f48181540c0c0000d2404a54440348682c681c4800c40e501a03664050721a100b2001c00310000800301c040e00d410b1402c0100703403160388040c08035120312468028a0b10b136046a10201511030412840c1e0318040600d0034104840080214042700400c8107440000103400300b02c045c0944078401400c6010f0070f2403050000020400050040f44405040203982300001910502242c0741944c1100a00400c5a041403000c1c04060710058143c4004420515024541c02d41e82d548400807903d03100c10140c2590081b548188a0800c0c44072002d0048c5040e44203071020002d0950020145078028188a0405444247e02d1240743c0c0c0e50504011a0303030b0000c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 597836870 1250 597835620 597835633
    0x609020d080f04090e0105070c12090317031b04081504020d06050a1a100e0f15030a0c0806060918060105130909050f060403170703090b0a0b1e060901050309030903 72
    0xb680b9020316002032060400c07844c10003d160844d03110600400c1d0044510749c48582421001b9603441c1008181004002c2c1007101da0040000400c404010310011502d071045541c5d079034182183c1c04919100f01c1c80500380d10344404c1204004901d400104600d4041007184880020b854520014540ca0300d03c2d40d0181c41c0d07a00349000c2c00b102c800d084d030019150a0080112a06064004c0b040c44242d0a40407014808100408c0e41c03501701e400d040340c20502c0e100005040c142e1134101401c02c440507402c1542d280e108290341743c0d05003d03520380101d0320a800a104a900c1d6051120140004040d00d43c00684294850450004034134039134058010303500f40d50180014109600d0300c40c010a00102120a0251034078403e0010306d02048001150b118040c80d01551011110203440000050441010300f11104142c1c1c0c0d01c00001c082541c20003c2030042d00d4510004c10341d10406801c0103001715115201c6c4602c0d64580303400304255911141142e00080c400c3c2800c507200d540715080a41035001e0140740540500400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 597838120 1250 597836870 597836887
    0x1507080c01022a060a0501060c260304031e0507080307050a030e010e0109030905120703030507170a09140103141602190c06120c05042d141203160609020d08 69
    0x41043c01148501c1d04480860b681c01540800341c450a100d050045190b0001c02c80204501c4000700c00386041c00f00e480c9400ca0740402880c80a940121400e074000780b442c0e0b03440200c0001da8a10300039004070501c0e00c241054942d0b211511a807101070403080c01d03c8800501500154003036002040c00040c240001c001c10014598075901805110200300c00003006064003181e9403502911b10040e5002c4103004001450959600707403556800090706560307031441640400103200c040d00040040e07018541d201e10145203424401c9030050240d050780b03814103042800c00b40003400c01c00d03502944200042e500d03403d00c1c4002c1ea000d80c1000041e089042e00445040303403410a11043d00308101c1160900d546aa0300e140801c108401240c4200c8402e1002503001c02c410000042c030600c500011981d0301d0140400d001d47c110340740c0600c04107584501d02204410b800902c0034074112840041c80c4207100c015502c3c0110440b000300d41c00440701c0000380480c1d5a103c20b08190b46034404003881d21035001c1e1581c0d80d030707e030304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 597839370 1250 597838120 597838177
    0x3050703150f0f1a07060905070b0408071502010c0e0f130f0b100207060210050a0e0607090302030d18150513140a171005062704020406051507080c0102 67
    0x65020f1a43c004040c640002005464070078800c1d89895510303003041c00c040301d5545000103402c0b0818265101d104241c03022900b450070310010300042c015240100f4410346042c0414880f45803111211080da494064009081500b0203820fa950041c221403004e10315480c1400204540260041400b0040c42d00007401d40d039200941c017004c800c2c0012940040b8403c482c000032a900d00303580c0580d00050300b000c0212510309a440d00134a400100c80e4102065104400c0f0829103043d400b2900c66000030480c0004006605080c07122030761045a40c030704001400c04559a001651409106500d400a0803c07180c2405910034010340700040c03031054111900a644018040380500640d02c224469001401d0000700910300c0280003200d6000701c0080e00c1ea80103130b00d586030010000200400e4100c1c5010460040740500f080c40404400c4904002d40802c4c10a4010b01007240c0301030300240d01903031a0002c2c1403084000c400586441540c0801c13601d80c0c8400c0503030f045029002c1c0d04000c3c51a60300111003400154803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 597840620 1250 597839370 597839399
    0x22202250209010506160308090c15130e0610140c0a0b040c050402030f07030510090f0204060305101202060c0c04090b0604051005010801060509010302040312051308070311010305070315 82
    0x2225030b008281d80b1007040000512606500458035040807403202c002900421089500c071144c8000d035082d43c209070010420301d00d40d40c0c10712441c0c124009040e40303c0c810340b0308c481c0c8060f0000396081103ca10b40800410003003202008101d0510016004001c1000c0b841e800300c40c000c8040b141076910200c014074083d000100192001c5a1404c0c228801180c10b04140c4296441040303600c042100d01c0d1a00c41d000c3d00201009440f40b0600446614041414407980c0a0184075600d06000107a0fa0f929081d0010111040941080340001c4406d40420110b0343c081410281c0d581c04444090340d0b0108255040d00c4c00e4000c0084070f40050421101005100d451804544680c074241da040c049a038904c1d114980702d0071720b0b003d518040b1f2640380040c042184248081d1195100604005203056225201e5106070f1150075101703400203071f001601d4580d904a90030254004c080c07000061078090308550700c050101015101d03281c101503130740000404080c4a500300100303c20001e008102c0c920745030403200c01c0e00035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 597841726 1106 597840620 597840623
    0x2030c030706020607030e03040e151c0305181c1b0e090c03010c090602060a02070f2004241703090a1502011802220225 53
    0x8804110701405054107070014111407400e024020255061700700b41550b5a00103120400000740031541181c0c005d1035140109000404038404260000b201c21000701503082a0540d11040c150410002c0000c0e05051414901c4900c4c170106021412000e6041c00002c2c24100c6104c0c4041080f03c000001502c034082d26040103540d4641d81180c8281d019201041c180d0490000e946e15441c092242c010303104898240001d0f210326106000e901e850004002c10000307a00011200c0070444040c58001305190710082400d00700400c62040291f0f81c500d2071046000740d180c403d03001301e0460ba0000078440c40d843c515447c0d460a040c500e034110303136410003900968944814003508600b80c1c2d07449100700181003c405078901c81c4c0b40b6170030005c2c00c2d21048185031900b814440c07201ea015848000c0042d0032840803840c1c1e842c0100c241d49428000340b1901401040501f024031040480400814114156070b = true := by decide +kernel

theorem cover : BRFrame.Cov 597661870 597841726 := by
  have h0 := BRFrame.cov_init 597661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 597661870 ≤ n) (h2 : n < 597841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
