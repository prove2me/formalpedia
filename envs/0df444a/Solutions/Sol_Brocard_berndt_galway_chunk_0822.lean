-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0822
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:59:39.334465+00:00
-- url     : https://prove2.me/submissions/99ec2a31-e7d1-4bbe-8c4b-cf7275453b29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 147661870 ≤ n < 147841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 147663120 1250 147661870 147661873
    0x30c17070b070503130909231203041104050c03180c1003020a140d0213050405040b040f0609020303030c0705010c1e1107030609050705150f0301060f021606020d1b0203 74
    0x600c0c020072025140c102600070f8625000802121907881c0480e040032020b4442007400060202c554201506c80100c104070301000711810409108090b007001030104d082d100300310781965481c1c3c0d561400d00b0030407040002d4240c210703080400b405020a8094060351050341c20f56080c0c5a40e1010458890b500c0b00000c01240c7c10104440b100d0022a01c01e4008200c134070000c2c10460550f50310f0510a0050743e010114042034140d010411844131a484542600185012501400b4504241c1c4411800000c00f51000f80040d00702c0140328100f21854000040c0380350006d09407078403441d002c0c03d03408450b446020221055442c0c01031103101c00d030144e40c00d01c5403400c0c0c00980e8000c50300301501c155a80540c0007030502c400d10414000100045c41070103803480303042c440d80207801c00c6031600d01840116020107042440054060080b00c1050b2a20025a4115100d500e400c0d5010325410310107905010304580780c002e15080c00318001c9001500090b6004035603060381c3d41d01b580c00ca519054408060350005000750306 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 147664370 1250 147663120 147663133
    0x7020a11010f030e0d020c0a080309030d050318030c0105102304020f1303060209040501051e0d06060b0a021b01090f1802090d05010c030b0901140909030d0e0601030c17 74
    0x3203511500b10007142240c00e060014580c1072881c61949403034000c600c2c010060780250038040d280d080c9469000002d0034110001e500700300c4405c00282d10303612002d0800041010100c001503d0041980d01c500800344818240c9542d00a5076140c85c3c0603190849521420000c1000c0004406291040d401400c010090a2a1095001004000c080e500020390036019120034440340194450011450000f10b1140000507910010001448265481644818031501919000b180884148561546012400c6904800400da50f18259009108640121510078000710304100043e4000480c5d40d0b0f10600c040010350540305120046036540202d01079851003090580041014240f44121082001040c0d103000d0305150400000c01d11401c0813540c195400c1c0c6d100d080079100d17250184a01d501c20901030302c40d40103030f60500d20040c048068200c41c950203809404001108070200744241c880c3d00c15201f0050000701035404500c0da940f10280000e40c1d40e90350003400060301d02006400b0101c00e005180c041d090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 147665620 1250 147664370 147664403
    0x3060f05010f080a0e0f03090a1e03240606052a030f032a0307090b1608030603010f051306050f10210605070908060603010905100f0f020c1507020a 65
    0x411030009410744135155241d020f64401040180000601910080000c5440d00c070207604011102ea1151700c440208050002d18038000241034501070140c80c4c00180c814005001d001207054011002e1017840b240c50714111012628941c4a0b0040c01c5003804d0402c05a00328a001c0300103059401503035000c0340d00d40c2c420000d401c08010100701541d409403140c1d080740c030104190109000f0300e0807126000c56154000100b0080307965001691140036148419820307060007084440403a01c14040d040141c462034003c40020010358007508000c008009481044c0301606222001281d040d80000382100c80c0c0d42810000350000005050711441002410592800c20340303001c01010824100703204c14030f8403030841c00035540070980d0f0b0701850b0301801c0ea41da241a02c180c9050140d500b04880034141707078400d90410180b24085403001a4942c8020a021000a61041560000c0c4010903035880c0240009001050a90040c48080780b012200100704640f031140d03a680d108220303140c85800c4d00040801102050088 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 147666870 1250 147665620 147665627
    0xe0115060c08040302031519060803030f150415051c0f08160b07050702040b220c051b0a0209131a0601110303310816031e020d03060f05010f 62
    0x4001d501480359140f43c181c9030303004241000b94042503840c1c0c00ca020740c280a4904940d0410070f01821586004000450a05101c551a4800079149042c51824034000c10314010800d402c200302100b006204000c640740c0307404c1812218402d4898684100c0720040f41e00e0408400560415210742e0144104014400c2566075001c613030800390003030b1814401d004050000400d074000c081d020f1561501d80b907488400714410002a10240d403600307030042007100d511040d00508540d107a03034501e04042c008502884001001c8816000e0300a070422514800c0300340c03a510100100d584441c1c0c9000396140080303903a074081d458440c002d11040050100c0f000c040c94001e00800b0000300c0740c10034030514280a81d02d01da100c20900d103030015107490103c0d541d800d03058440b02c1005103608500500c86041f0308607042c0c83d5202c02120b40a18200f0344144055042880d042510a0b01310145040c003002d111849411041c1c4000c1d512120804410003091801802150910100300102e0494105950b01840301007003047c1113 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 147668120 1250 147666870 147666887
    0x9100305010c051c0f0905060f1006050405090a0e1f02120609011203030c1404090507020601060e031e070306060b18010e060405041a04020c0a0201031404030f0c1403030f06040e011506 81
    0x481c417181e44141c90400110140049030140100908844107030070306544565122a0036401f007010300804220812141e00c1d0700d01410790040c82000006a44100b4480300b07401c2444113044401003116000380e0000f8001a98060201895441b0802445ea070303404e024814002402c1c0100e8110000710616840000c0c8650000c400d14070542c90001c03942c003010130002599070080d41017007035903644610410074551f5040050b5801001c40c0c0ca0b11011145006021a40f5411310810441c1901c400c01c425002000040004400450344244100f000551390b0440007900e1b0803600d941c0c60070708c0d08916000040e40c0f2941d00c8541c0048028111887c00340b50108000c0109031000d182d8880241c0b0812805041d030b1076102030802006100f0261069000500c00103044034089002074501d002c40009000c0801d9020014910301e00041c01c040075440f005041c5000c1a1203a070b03041d08520f12001040000314404612078074001c0800b03aa0034045014421f075401e0988480c80502e00c84a10341d80b00400402e031148201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 147669370 1250 147668120 147668141
    0xc0d0c05060d06090603030908100504110d02040e0a0303150b070b0a0b040b0a0906061206081504050a0b090a02090901051623030412080609190b060909100305010c051c 74
    0x24615a1244c00c001070300c3d5135a10603070208400302e6017000607800030f001202905075401010011450305a441600407840c06a01a008007403088417070b0215100e507844580850b580c5811512100158900140540407940d4080030320a10190001160381041054864040d48080b111600e5039580b50080018509000b50300d60003500ca03504600c2a0f2154008a400340042d13010100c0c0c50b509250303001d00320707401c13004941c028286491030822400c00040344010807411188841a0161a13509005280454041d400340959140f0300502c11450000128200054030a541411090780c07a00300b118200d03003048450520400010f00280200d0340705401106005406e454004d01c80481d8000707145031500202e404541c1302441500252200750403110965000c0411504d1104600d40b90700003c050405070745140100035250820f0f114039075194030a550000c5809403c00c1082c2c07a25000542804d2003502c4151002d51134001c421000920a404464200c182d00340454170b50889004070b40000d1885d40e58 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 147670620 1250 147669370 147669397
    0x13080601030f06021e0c070305010510030f0f03050405150304060b06160308070912050606040e010204124d12071802070804080304060905010305061e0f04020a110c0d0c0506 76
    0x1000176405039001905407102204010060720b8110b16041e4211034000c2d100300900d10b183c0508000084012084006050740480b0310080f101151400b9a0640101e030031144e888070404024183c1d000d1780401646c8590301a2005005008060040c071513a84039035541e14804004c1072a0b010080383c028484160099000d284c140380650391910520030511070907404445c1c5820800600040d49050300640d1030050b0814000c524080c41e10542c15214408028020210a080c1071903444190401d03401c0005081e1900c20b0101201c00c020000310091a8003225107081d01c0c3d8405800030604264102001510620004200340c03820640b50b014100026141c14103069000c004810002e0b2550700503100a2000c5c40003180c0f25410050046e050011707a030825410945004204401c0e9030310030b00151000302120844200d449001404601c0100424a80ba5002800011640c03416a440309140c043c00c1000c10a840707409844a080007821040c4d00401342c40200710034024007031450080700a1811580242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 147671870 1250 147670620 147670657
    0xc102910170a0c0e06040f03150e0a080309100905030409110c0f07060816080a0504060b030604032001090b010e2e05090702010203061e061201090213080601030f0602 73
    0x541e6092805011100035203010340302c8001d45101900030489940030002241c800d070406083c40f2001c00143c8451201512001030105807400340c11141d480040c01605843c01c0d13412161030760078418415801921036052511400074ad000342d8050b244a00140c2c90340c40805185054540b900050143c0008145401024010041c0350b00002c01008003102c44040507000d003004034030307002018008010050030010010300c008074841617254040c4141c0e030b02c07c2e54154001081d03265410003034000c051850724250944200e01c203104c1030682040c14482c20103c0e02c40301e0150040c0010a0500360345a07070340d009003282d0a5000600010a000340c403194400441030000500c40b4090442d400d01081450301d489400364042810310050a100e242d503a4407500b240000c0d451410200041842d20030344030070391201c44000e582c8600c01c84c2d60310707000c40c0c1012034004455440c558450388240000d40c00f05d1800c85144218210004080801040060403641c03c5843e00721080380c141c4038030029600081515141c0c1c680322 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 147673120 1250 147671870 147671897
    0xa0b09011104180b0118050120100b0901090902010c0b04020d08040303050711090f13080c0706021006060c0302030d0203041b0b090109060206010b0d1109060c102910 73
    0x4401070401043c2c000300380e20020090400141c21204000241410801903440c200e98150b100e0251501b06d0f10b00b80781455020f8200106205582010001d84885004841c030709044a4944e40082060741c400b21004049a42d031141c0703850031192080c6000b4007003505800c5903000b00e201c2044180d4002e00243c51110280400e6580c05460f5000d504118085030020030038600784000d41c47d402140820030350305070200b401c0039100c2c64115031004040a20107406007400c0e60400c00c5083c1501c0391842000100c80d20b0703d4031440c000c2c2d298414000c40201c41c030b1600400040b5140328850720641d84c0d8054014614080000004034040c0d40014415110b550a0491a2a401c00c0d144029401420a04003954a07240048001032101519500020456026000600200e0344d00822926691f41d480340025040b01e2000001885000d00d051041d480070011030458452070010070b00101c1e84013200410003104008543d0212203c250280c8000d008031085540596400c141030720441c0c034a070b0350a025042e4240e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 147674370 1250 147673120 147673151
    0xe030f07080f0601050604051e01030906020301170c06031005011803080f07030e0d0503090f030f0d02030417030c1902041808180a030b0604181a071205090a0b0901 72
    0x40350300c1000c4a40c807500900400ca0b0080c46454050030b0100d998602d403e161000003142e11104c12500345264031080c0441615a0003a800b0600e0180e2182c0b083d0741b40e41c0e417000c0a612441100d88490355a0250b068401180e1a000c012248694180e010b4131181d1400d1600440b51400d4061a2a030340310001440400800e660f00058580084090481903440384d42e40790007000202c62180b00f5000e602d03041c000500060703000c4150b40d01c200040d1003401040c4c8480c0700003440c2009443d4035003158002c0c000740c0c1e0844c5034040010020f44002c1d0a60540500749910460781d28031903a4043d400c5c0340c101c412058400e0240d0280d41605600040021034070340550700121100240c13160003243c0145000908404e01c40c2a010514401030048a0340c01009145440754200b0745801882e4038892560352071664082c0811020010f08039412030411040300c68004055a00e0b003d043d83e10801003000e89a00500022090080074802d480100150803a5002503594001c051005080c0340000c0d5212201da1040038072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 147675620 1250 147674370 147674383
    0x207090f0209120f0c01030b0409020402030c04060305060a2102060712020109110105070c0e090307080c0109061a060d09060605061305040605030c06190903080a080a0506010801060f0e030f 83
    0xd440d200680c0c0340e840d8020001140020114442070342c1001390248860000072601d40c4045d402800c000c10004829400078008142c4000e009601501c0030041c00703519503281c006071060700c1c07150305c0810041d110301c000c0200c07000c40c6e48202c828002100c24014000210f1401c907580403031001d0f080c00d081050503a0ba80010015800341140141e40d113000b18414020941d01c000b440300800e082c200d1411005440b080c01c000e101d402004801480e400c0440c0c4400400c0045441550b08400e01070f480b240300007081030103400061000d841140c20074000368040c0000d0100303042100c4000b0040d82c5030201005c404d0001d0000b03080191406651464001040c2d250f103801480c03180da5000080201605010030030080361443e8009600070361204c0c81405c156203c036000c0380c03201d806500490080100960b030445603250f480d0030052080401040384400d450300030000174080c0b00c0a01051003280e5a0000458100700c01348078101c00982034203141d00d1881d005007900c114a00014054030103e800e40c7c0382c85480e041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 147676870 1250 147675620 147675641
    0xf021203011d010501080910020c03090405041b0504140a090c08060c090405010803090102070605071b3015230112050d091422110a020d0203030f0406050601020709 72
    0x340b5409862046881c09100707015002c01d00b4070121a060039440c99917210110705041000c1c560014407132202050800030b813030311094010b10034000d9103007902d44203294145000701d40711042902900030801c1e1525024070081103160f00e6041c1d54a0f645d100c04040a4a4166001c1e180b60204e500301055004c02444090311900b80c0d64030140e03886c41c0b0750b01480700b02ca030140c7c4a4031140e081030140c01000c0e070380450005c00b1207005103001034407a05181030000d02651a074003484c4000011403000216842e8161089104180b6000d204480b0362002c0d0301d01c0060381d52190020280821015180c1c6007940990101c2c031032f00c181c08141c0e807002c034012b420900c00c0c00013a00841e41b4003081c1c16401c0c0400c00c040100c82d14072442407030680310691411010741c1c10000301c072a84a225291600409030a203d8043d0f0500c2607000b01641405101d08008107203400d940301c600300c0360042c0698034100c0c4489000008590180d1204c515903140c2d65520789a4200420700078000504600840d900020744245034018103070f081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 147678120 1250 147676870 147676889
    0xf0a03060606110105040c05060703051c0507090e040209010302061b03030a0e16060c0807060b030d0906180f0504090f140607020115030201170907090f0608011505030703030f02120301 81
    0x240c01d221000d4010f0001004600160307040900f000b0000300da1809113030031284241c600b141c0302c91041c80c1c2591709000d001120005038141e40b2541d031001320203402c00f5000e0f00f06519a114180d84403003400310042d0707040758081d400c068a0401000182408001450300c1c401000b00b0000c500c01041c0000e00310f520a03070754522091344500d0381d40e035035450603c00e0741544982d00c41c00340a610303c0c04d640503010b65400000503003410030202e0034200307004032900111007000d40142500c407040c6200e20003422000c1c0a008140010300c00b101580c58100c0c80305e0f0302d04103507001c41d0348911000d4507140812010300380c0700f0030450744e54103182004000075a9000e28940c04521002c094032071440c0c4240000d0071176203140d01c0d80622014a50042000d83d030081685001c0c4160480030066030742c2c81000c11440e260702076100c070906524080c05003122600542c020003d03141004028004d441070200000369600c118000d460b03054000c09000c10000303005a213402144030040c01990241d24003040d4815054009a0001109 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 147679370 1250 147678120 147678131
    0x9090c170c031506040f0624031104090905030c070b03150315040210031b02030a03060e090c1212131805070f0f0e0907030e0d030b030307020f0f0a0306 67
    0x140c0c442482080302042803000741801051000000da541e507140101d243e8a4400d44040341144d25160030620000340811028040c16a40d0880c00c90582e2034001800c28540d01441e172141c44030301c640501141c01c00d040040340d0809041403065001800c040c1c80440741c510040103034540e158404d004c084005c00c103484111b600d0345808041c1940300d40f0719000c42882034010070140620320001008140d00543c050b242140d00041030801a802840120407070700c0911004802c0b1810270341d0000040c01030b008196002c1c0b00507945c6100c0842041400c0d01d00840542040c1da2455041c00d10b4071015036010040000c5440650a00c25090f5041d441110151060480d2420034000c2804807000c40c1c00c5c00f115104204402d181c4510000d111200c060308020801000107290810280b2504042d080e8901c0100004030f2401d00c0d89004d4000c2044846442c068000c0c000c00c4002c1d18083c0c4142203030003501501851070002c00c0c1d42041120700101c000c06078400f09050503400389885020768035014521a1000145 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 147680620 1250 147679370 147679379
    0xe03150f0612010b09070342090e06040f080f07050304150c02150a03060902180a0b12070516050a110a09110712170a06050a0e070509010804080409090c 67
    0x11404100c01103502c9a03042442118050716035074030a90b8044510b01c2d002495104480122007012090a10075014921983c142c00210801c0100b170780801d00c10022001ea89540c0b2031001701074034105038818045410074070015010030020300754029060320842440c2c1c13030400325001c1da030555040507030181c8507607201050501c183c01062842c21710040b40390400350481403207a0300043c109420382160f09422400415002450340c0aa00624007406581c5000e43d1556500855007150b40007a4440c648503144403d0009460140c003003c5421a4081200c450040c1d600c0000980c1c09902c544080089020b640d138404003c5002400003002191080c008100c1103e44501040704074100b94110f42c0f4090b1400b0320641241c5503020842d038441c0d030b000040000045c41c0c450b084d940549005003041c0481313494420001c01070fa041c3e2011050319401c60f403c3d0074442d110844540c1950f01101c0070008104100042d280e03e41c040e5090503880b92080740d18030300c3c050721400f03031406581c19428112510f0700320820501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 147681870 1250 147680620 147680629
    0x81b010302132c060d1203020910050702030c1f0807020715050c0106060807020d03050901140f0a360c03120906030b03010218010507031205010f050102010b10020d0e03150f06 77
    0x79071010003080003e10f142014800250b0410403038400410100c0f603045094980c50190b0181c0d407141e40010468880c150740e1680c090030560060804a10078080c960072800389240802107400e00e000c00d001396040451001c10291a0084003a0122013588140e0310b000820400c80603060100c0b00441d9611510f612a0003c80c609480040d0000340034894100c0c201f06e9655800940203449050526001c16580c440c3c10304c06004002a00000c00d400320504200214003942d04600c501609000404100682174225065500400d003009021000c1d50100500940320305003030700c0e80003507000c0c40c841035020740c0c0c83e907940c0d405081003100740d000b0071000b140c204602e542610605c1e03d002020340082d03203007029240100389102841000141030160200d5160241485142c0e46171700300310030840c100580d5850321034600001c0e44602c500f40c0190f00b488018030181c00d12124803241c40c1e82d160001d08004040d000280c40c00350102d142190036100390071a0404180b00845042e004e0402d1143d04031070f508141c014130 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 147683120 1250 147681870 147681929
    0x21060207120f030615050708090d0804050111030f120711010509061005030c0d120c06020d090b130b01060806010302120f041b0b0415110319030b0a081b01030213 71
    0x11400e0601e4031604000700300f148400800f1810705c514050f030759100d4610701195107000d03030400c403908104101c0f844420041c4d010014001d40310700362a50a44503400c001442d549102d00c51003002415000d00641403d6010001011382194260810a00d04145040c910f0b085900840d400271043c0e200805001d413401c160030001e801341000740e010708819401c28002c101c0400440100800e164141080c0c154400d01c035105184a039070740300106640c0c4d11940e5030204050800100c0aa643c40c409801181f10810200f0851080d0f0f0750102e001660f0345c0c0707000006c0d50140030050000c0c2c1459020418600d042800030f407041e101d0344c400485100030781040c5c00c22a0701031052110490640c502c0d80c0e003d000c6a02990180d038102e4200c048a200c0788084000c048a1000b01c0221181580c803020a0000c0f0754900281c0d0381d0790f0906555010040c6880f907508020500d82540f1400368035400c030081c41001d2605c42e401c0500170b480181009490004100d61075510301721140e1022226a0582003c59014006036800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 147684370 1250 147683120 147683147
    0x1b010507120c03020a0c5d0c110310140412020109021e060d05010b09130b0114130b040e011802030f0118090b1513152106020712 57
    0x45041001c041400741c2003217400c2001412242103843d80c1f0f014424030090b040d10ba000c00300f441a54504c14000725000c0000f8100281c081701c01103464100c2c800540009252241c1c0141c1d681c810859925100c0c5810a001401c81c0e42c1c15004109517052510713460b01590a201c00070000045240c90542405285800c0101c82c0c81f0440e418580c0701009a5900d4810b00c03100a0b0b41e015407280480c070000020000c0c4920310042401908010000510251402c041e0002101c19500200c07442c44a908040c1240d01200c00580480d54100b072000c0d400c440d074400b5054000243e0000e031070041d00c03041e02050701d400551000c5906c004110050140980d43c1c04c60791380040709042c0542c1941024581010003401c1402050003202207010303180d040c0f03503598102c508410341100c80480700f41006403490b43c0010310007e590b4001d1640f5000800107842c5072140141c9403601c0d00c845c0344a00c0c1480b011105013070000408480c1030028054410104800e48003d1404500ca0071000a00b0700d00008042e011008441e032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 147685620 1250 147684370 147684377
    0xc06030c1c02161217250809060a20040b03041b0f03060507020313030b06010f02071809030c0c0e0703140609010308090102030d090507030b0f01060c02061b010507120c 74
    0x114003c40403101031940e4465512109001c50655411404c46080d5103003030b4140380246021080c48a503000c0710a880100541e041000c6954048884003524042c1c03040d600c120311a0321141c0044c803201d8403070780320703520541541341240002c0210420300c203140e4029030002c1c000390200005120070041242c1388842c50030b0f02540201601071610140b030030101580d21000c3e00c0c00e81c0340d00002e00644c2c42031088a616030380c51485030302c4513501e9041c0450741d00b0003101c529001c2925040258511307400010f10038215800d41240e06c6484a480d0174100c050440c410085040c015110480c40025048180403130251111460404107441d00400090959101a841081c4811400b0510140e03440d429002810f4036000001a591103104000407451885071400d4806440d182544200403c000172885808803409981401007907100c451082c91190028031420000c034406462400041c00c0c180003910000002c4210a070025a010050509480e021200c810000ea00d42209501c0e0b4002c5124003450b56001d0b24 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 147686870 1250 147685620 147685627
    0x30c020d08090c120d022802220e01050105030d030b090a0c050f0a0807020118050309090417040b070b06040209010c03141207020a03180b1b0307020607080703030e060408070609050c06030c1c02 85
    0x7603405003240281d1380d010b070248281030041196000522041e1031111420002008600442b030226070080c0400c0c000c0354440d0042c1503040400d98420701480304100c0d40200b03416031580b01c5a070f41c0c000402440c1c1d110024807400f48080121140c1040103002111800d03162800b4170f180c400f00081c211900c155181c41c515015805c0c40c004030780c0010a445103032600f034074503442c20740b0f560030b00c420301810340310321b0085806000170041003901038500606292440b9580d640050b480315802c00c81070b401080d10701d0340000c0c070820f800c6020130300c591001c0c1025405030034a18038201088001996a54007180c005c00582d001030300740010154000548070494128001380c1440c40d0502051102c0c0384160300c01440000c1c0e0444101c404400140200c4590942c020301d107645c1da000e545003020b155082682c081e004245460401c03c0a1940450a60f03ca254061026454400d07a651040c0090403040410f0300e1034800c403030300d002a0352921001103000e180c40070209501d030740490811920124020003400d56060051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 147688120 1250 147686870 147686923
    0xd0813030606081f02090d0c0803121e07081e01090c020d032f040801021602011106010b0703050c03120103051006091506032a081006030c020d08090c120d02 69
    0x443d4554841302291026940c1c0c3c82d8074000400c900c9005038050582c1000d440006080c0380004002c00035001c0d0700d400d41c4c8143d034400e01096151415900109000540c01c0002204a4030441c2000d17072000a51035520410584c40c0c44909038910700341c0264100729035031042105000d404202c806100d480074902800b2075080c6903c5840b800c60914510010050500003110250142c002074602422108001315101e00388114600d041c0c940c0a88146d0200703010000b282c41401000c604181138680030000c0c58540502540d04481c154008500601a400f050015455003503401c0754107402140218000d0900700d03803420500c2c0460f070440d403210241c245013014440788400320395030640803205603040002d000400c80c40008505a82e140c880940b10180c80040302565400c465a10b018410550200028a4582c10250115207014805c4005680b03c02d03a1102030510a00b03650b940050a030080d40ca02400440c04034552280c0768480c0c5040703401031a00b06a040e9410402001d20024030384581c0d4004810 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 147689370 1250 147688120 147688153
    0x409052208031e06031c1709071412030f071e0303060603110909180a05150108070e010302031b03120711120d0906030f0b0913020109080d090b090d081303060608 71
    0x1081b02420403d24482a84003070242c0d42c0301c0c590300420000311102e8a824404140c54205600030b1000c05000c44984101c01d003000c0c0e0a040b5403105090003503203444807005080d4603039040a4011a1f014294280308045a038020036258056482601c1c0866201e050150283c1628041c442440e1803410a0040519030340c4d8110740d440c0c210749481030000070443e410752407504151443d54060306a1040e0003c01c204140e800320024122542c240c2920260350700c17030505c084054030070700c0040c0d8551700075810f40003a081d80000d4901110340060841d1614503410011034800e400a86054608002040c103040300b605000f041c071400c42c0d010300082c3c180b01211503c06411740c44076015100070503075030b01c45094028031240e01661200c000100000454500300000d4a68044005000c0740001d000c1e41000035103210004200b0b0b1a07000c1508d07080140741c00c0594038030341a00a01c411075408440d007604400822070b03400041900302d0f000003500a142c0d0440c1000010343e4442d9000c0351a69004e8400c0341c0c40c0300b01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 147690620 1250 147689370 147689383
    0x20d140714070b040609290c0324190b040f080708030f03070306030606030b1611030a03090c0e0a02130b070201080406021b0d0203030910060503030409052208031e0603 74
    0x1d00204041c00c84d215801c150005140400c4001d0401401c0c0502c80c00c0202c403402100515804081107e00e2030f07480110454041c00b0a1758401e14205003503600d400f00c031a403124618103d040c0540807031940f2400c41c80c1c1100104403980011803111001600f441451030201140c0060880080142b00701c525022026559106042480301500030102c04a00c04d98880c0c1c014800854020360140300e050f86a08000e040c001c030664910048000031301ca203661003800b940c11000526070100c00b0750f0a000f403000e0203401a0030400d104440c0c81019041c0800c0124400d00b0903402020a28401a120303403403c010307070000a0094108910441e4107110f0f81c0010703a40154016400b039800080561a5001c0c0029840d2801c4030040c03040440c010603024000e51540000654800c0290310100c1d0402401d554440d070448403031780220794154008010902c0240700f2608850380101910b4640d44910550300d82d40403c181300c010b0f0850301c0c1c84000081c880c01c503040c000c0c0c54901e054050701442913810040300083e40d450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 147691870 1250 147690620 147690623
    0x60f03011a100903060e0c100f0f0e0a030506010b0301061701180207080f0d1401090c05042d03060b1906080402090901060812040504051f0b030603030904020d14071407 74
    0x20b80d040851592a4400c550520045902030010700035128960100c40d20b499108554170700901c61400c0c50f611551144035020303961002910fa440401c0300c9154221400c58aa04040f6000080c031080000007030b00410105000745619015640c6030350401500402d03082c0c0ea1025003004002002c010f2100c008562140d210342d041006006a031034860303160041d6580240f0900c40a0040c02058000000b840c2e074000565014405040f080c0360382e211491802101c250007000c0000500520041c0600d03402d0015020b1903c48005800161801c0c00c24241d00b0004180c0044070126202c05191381c85080c10504410400c1481c1200e040c0107007030800040c100c503001032010340715038800300229200070801c0d40040007074a4040c0544018039018400c0ca105030340944600c1e400b45282c04c00280004254012120560302e5030b182110041c1d00d0b10821b4005504050511036041c0400c0002c4001569548000c22100c520b001d808282846905e85902403407000800f110180200b9100c0f050003144210222034995 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 147693120 1250 147691870 147691879
    0xa020a0815130c0206061201290303190504060f030605010f0e0109030c1706010b0304020303030c0a11030301061e030504031413050909060f070509090402040506180f060f03011a 78
    0x2006640d001881104200b11640205071030401c2141000303078046000e40c8510400d0340e62034840416194484c1c22a200c0400c500660040d00d94124400e16600c0c202c00710b14071005040b2410880d8582564040e00349085140c0d02203132000504115041d00040000c845030503030304040203400d00c1c1000287c074509940c0c00380400c00c03881914000030f40e0301440700d0f1006960002187c0c94604e881d1007454060110100103030b03c15205400c0005041081e010449104070ba000d0091800e64071009043c058079080203c10100344102240c0302641240f04102850090101d0383d079030011025004c61142c400c0320800d00c4601090f052004010200e900231000c0340c600158000381070b503101c6034001c00d401c0001413600300607440030000c1d05104000c140064040e00074940c101c2d00d106561640c0318156801d100c0c5400d0640c100030b400d40020058a003a034005a8051005010080a40d00a00c84a0520001114510488030104083c00440e082401501045400541c000c21410070f003001119103c150002c002c5209 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 147694370 1250 147693120 147693151
    0x609060c03110601060302031807030f020918030703120f0e0a08030a020d0504121b170706060306090f0c050114030c0c0a140709050a050606162108010e0a020a08 71
    0x815100d20302030a916807940065a0982d61a00c5d0001c0c043d510585020036290140c0200300c40c0c554020400c8000c40e64002c0c2000b8051090768280408400000d2042e5185645540310155012083c0020031031144241d95400c0383e008109008070071512403422000c10300e071030101c20390500f41c40091151100c0360014601030700c80c1d035140e10701806480703241342d0500d4240c104020b010420480200c01c4d2120401b94840e500ca00d800302c4403e80307039a0520940035004000e060320040809006c040109001801a80c022a241e5202e0b01c5d20000d441c4010710071516107213034902000612003035002c0c4202900091802a460a17100e41d84013105000142100c144901c0c006400070304214100070840c1140d070301c40f481d4910030980d0481c042e00e45105219800606d0700340000a101c040c69403190310710500b001880c4a0400c000070b0b8407184442c51184040b141241003100040e1920b0601083c4800b046441c0c0e034008140d0b0401c1000750b00850301502409070540180301000440e0303040040a6072000d900b00c1c451a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 147695620 1250 147694370 147694373
    0x7150f0b03011805070e0f01060e030c0406120203010507020303160e0d0c0b120601050306130e011103010b04092004170a32120906090d08031509100609060c 69
    0x81940c4080c40e0740c5503280064480c10500c00007441c10800b0301400503940c0c49075031100310300d00940702201d15a80d1800820014405640036400307000d00110701800b21082c0424000110b02113a05a8100400b050f021410490841c6030074080e07a41c0c0814148003550942c104441c0012a943c3c1c42c1c0740301c10611021641d214040c1d120000204005d81d04080010141c591302c80b524845544640510441c071110f000c0000c44c05e50044045234020b80d00908070360b95040690004000404494104142c0c40d521089100c1c8800103081c080c1d806441e0040d4055036a6113000304400440e130310100d002d0084201480903441440801080d1012900414050400c9204600e4200d040a0704102d0041106400c10b0018081ca02100e81c81c1d810b143ca255010300042090111156803141c6942400000500800110016041a2000d8140408003034854055000796658510860700100c40f200310101030103a000100746049080a90000641e0b90040c85450500a0061004006016543c20700050144510 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 147696870 1250 147695620 147695651
    0xc0102060604181502030f0709121709040510140a030804090b03280308071107061d030a060e010518060406051902070f0b06060c070905220302010c03110715 69
    0x3d00071680400a981900c144144850003074105030f400325401143d080014084a01940049060350540080d500b4000c0071a034480c901d4140401c55200480740a11440e110340d1154001c4038000d540902c0071210013800c002252110301303504500140302344248081013001c602c42c1c00403182958540d140c0464400304e0b050100c1d2400c85a40c0c58045140300c1c4000345010700180c401081580c506c80da4454680d5244c10808071440400e92000110380c0d0002d010811040780940315801900740f180005212901200c00020709140a941c1d0944549481d820441c00c101c00a105882d804040d00c611070100288034040ca40d40e840e002080203011940d07c03004102e0b80420024010030309004000290341e515110300d060304c860881140b08480ea101000701084c0d5501d0000e05860500c00680000c200007454141040c02801c0080c1600d5800d01c5a1031844410703150380401144806c1c0646c00202d20310bc00c2c40002000c4605903112140c0c0c44009020140c001042c2d00350721080d94401103404550160b49210300d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 147698120 1250 147696870 147696911
    0x605091203070f0b0115090305030d0f1d07080609060103030f0807030f0f0e010c020309060d1a03032d0a0503010504091b0611060604140408070524010510020c0102060604 75
    0x1d00f1122041c2040010070548509680c141c3c0e01d01c0000128040016505031040c1d00a030200402540003413209050b1624a0750040d0110034803903d0101711000d2200d030786181c00303030712441340b01043d00090030600641c5801c02c030064120350702c030005100b250314540f0300408110510160f28200035030007021030465807180e00156020b1170b80440c2040100031a03c3c04400910041c001c40e2455400c22070075011841c0040107440e004440649228a40040c0e00c820b03000600e0f08140d1201d080c85c0d00d180300400d40d20100040d0040440040080c03c0400d2143c80018600240480c4090011000c02080346241d6002040e00d044a10955000c02c040c0310514140001c4591045400490a075400f00021003940c003203000c2c00030312101030507982244c40b19010b1009489007240e689031052040c1c80424000741205008003081801202a290740c1c3c2c881c13411020a24600554815403485143c005004a281c9071031180f200501c40d000520080d4900c90010f903c60200500c0140b1607607440091000038001a001e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 147699370 1250 147698120 147698123
    0x1a0705071b0f120317070e0d0303090f060501030308011203120c031b05090f01110a02090601020f0607020a1e150b030a0b0405010207060e0a0b16050c0d02060402100207060509120307 80
    0x101d0100c0e6110322882c580741d0f4640d1410707070004100016440c40d50384c0415606016820aa8813010303507a03081c40a000001124007800c408050741c61820324003094280029426480c440d8030045519450340c00d004090600680180490b05103400300f2000180d00880c00401ca030181c24404642005200b00a40040000000b0014141212924400465400402050041c0d03080310f26084401100004440c0000032012001095004007081ca0261030f010561650003801441240c00e501e502400301030608030155281c0c00507034049400c88007007000285810005041a02c0449030881c419154803414510520055007040d0f6948902215502c2c248125420180c10804030015820709103402c034006e510101c419a01a072034001c0e00c003040140842d8059120341c00c01e0358110140c0760340600e144440039294070362003032010400c41c60400c0603007807107458509103294006e03050504c0c15006004040420044c0c0030219081204140010b64005d8252001a5000d4404e0104829440e14551030340c8030b800d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 147700620 1250 147699370 147699389
    0x1501170906040b0907060e061818040b1509040b041e080301181104090f06032003060603070501090b09032e0c17040303020d060b030109091a0705071b 66
    0x30080390200000e0281e008500c950000241651040d0165032190320a01038003001400b0790600007040d1601c040584081d40728040211075503855440050300c403005090501140103004d0081005000ca50004a544046924000261801104c001880104008000600c3c0b0000080464140010902880141c102c4a200300408011509103841c0302d07002441081c040080000000840240754015102c4420b000700d059800c10381400600d102404070190519a035540e10403000002c5003c07001d41050f080c03100d0251148000f0305c00145424000004c1445000341d114982c1003010b40d900c01d042c80101c1c0c520039000c50300c803a680c200080c1404044401144400420010f860fa054240051143e0751020070000304504c4000003020307180000148084420141c10800003000b00c0d000790010010075000d0000080c01a45400100129400c207820030089240c2c0e07215500b08106105a910b5560b80d14142030110900d040440200948100e41c00209041540e800300050020b003206c8083c054500042d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 147701870 1250 147700620 147700667
    0x3080c0f07060c17360706080a0f020a0c061a030607030c0201090203030309010b0a06090303020706050703020a0b151804020a1215110d0f05060108010519030501090809030c06040b031501 82
    0x2c04058a0203200340c031003581001c10545d014549070f080c150125400d00b40b0020b07004462826a069408400040203e4202500d9540101d0310304001e1006112a60803030f05c81c004948100e003080ca00711501c1c1c140d10310340d071013504640313007050394000420a901418034a00851100c8035072404034007400241a00a406110200900c0380d000010341111300150b0040d01c000500d00d82d280800c80d4540c1c1584409005600500010302441d48143c00514806000e17004640c05034440380d40c1d80d2000b4104403460352074181c90752050001e9160401052a40b0900b0f0100c03c0b106041c1034000641603440c42c40382000c41144046e0100c00c000d0504e20741c80101d00c0c411010404003401c128082520783c0b0000c903d60000b85048400c80c0c1008841c81018056141a51012182c1c0c4c00e0000303104040c41d02a10301001005080b1002001481c00d00699085611407500903842e041d02c00c09240c40c0c00c0c4140d299034032840c0180021301c004180c0200b40d0b13521220b15400058620760350001614855418000300c00e0340001403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 147703120 1250 147701870 147701881
    0x203060a090f2004050907020303070e09070e0607111504030515060103230702161d04061b021b06030f2202090a020c0d030501050d0206030c1303030c03080c0f07060c17 74
    0x4000fa0040b5617090b200040345646901049031a48001c64407407001c15840c94040980d0300f03110703141c41c0c0d0084c1d11741018043c03100c0b0f880000c2c141c0d400c15982143c0c0b24180a051030842e0030060000c45010a80c0c184c420708280c11035640c107071a0010150080c0b901d54218001801d281e2180e045010032412582e410641000603000041c11000100c8141000d40b26201c1001000c41c0c036001e0400803146402c004503070322050540300000514010b0030a80b041900d68001c4010078000661108207046240c00030141c503103030002e10303103000080c001400d48914420300170081c1b030301c01c9500c0312075011801410041d0780d46822403c2c01e02c0740c0c00c5904080e4100b540b801c10400d001e001c0d03a0040c86841002011182503c107407060442c00d0b60024003421750004055443c200050a108000c1c581000c000395405042502c14581c09a0072226580180c2c00101c102da030080605400641c00e6030041004c00780245090740403900c000b03642c8540c42c2e000302460b90350072032040322a100d034049108910791020201240d0502 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 147704370 1250 147703120 147703181
    0xc0a0e0a0501050d0206030c09041113051809030322080310170109031e02070504240605030610050f090d0804080f03120f04140a03030c03050108010203060a090f 71
    0x4940345580c4514103000410305203040001080442d5005042a06d135030f581000300c8150f0f802100e0096042912a4120984241c1075005003680707218005445007030500d020f0400101c1d02c280c80d004076200407248240701a040020042380c1e0b00910502018550041c80421101844000640030300b4849004c0240540321400ca00010300700c0d103003100b601e460360201d0740e1904e080740c0c0c210600074013150840c010402010708607480810302d40083d005442e2050f58940100d03040c3c4607454428103400d21070b94004000342c820510250043c10007868402e042d45003203408114102c00d100c2805043c001c010460b0804000705008036070f44404060920000d80c40545400c40c0650400e0146602034002d41007171014019001003a11b0348201d00f410901d09684031500f48420803440603209883c150542072800c000d40382c1c10440e00c940548203a40000da6a915160000c0886030306800205c640d0740108244011583d90381980340546000010000c0c00f030040f0f8019030001c205e21424109111107101c41900d03000107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 147705620 1250 147704370 147704399
    0x8010606120e070501032c030c060f220c03051510050105091e0409081b0601090c02060f07090f031b052b0201050412051605300c0a 58
    0x51039100c40c00c1c1e64035501c0c8024151a8055407822082e4041c440c00c02541d80300340c01000d08207541c403020050001484006900c0c807030001090340203d0748002801ca60420041140310307407284c412400d8666a050940705140c401a45d00903201c4814240d0564106101506a140c80210fa10204403030f02c00c6040f00320050042c008551010705403c0025000806500032401c6a02030703a0001c15160112801c1001902c1a100c0f11200e1038120350349a0031200060f40200080a60b10000030803e101e40c0008011240341003070581000c1025420043d10b04200c0360001101c03504881d04021101956450140841e030038a565070000b80c2403011000008203020407100d41136242c80d801c015a50f84c550300c0d10f0074000325a0b0340c0e2000180250301c5079540c3c3c5150109045200300d1600c1454100d2400c4d580e002248044074200b801681c1756045050841500044140c0c050002e0609903851045d20f00c0d1759240e5801158090700c139440412a00d01c0c2e00b400024248455180d400c0000c14919165456443c2031041c480d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 147706870 1250 147705620 147705629
    0x7120e1f080108031306030e010204030204051311030c010c020f1f0909060b04060e0d031101020f03191a040b040e0709050108100504051b0d02090f09150603070303111501080106 78
    0x1000d50001181103e004001c981e6a22a54014846140e01c1c00004800901d114400807000d55030074030000c00140d840b40101402a1400400358a055401e4242544294003003c0c61a100764070120300d50803180d800c0a0700b4103e554044404500001d01c207400719440c1400030007c54044480c1c40018040c0c542c1111503403080d14060981000300d1502c480486040340b01754000d00d40800c004401d8040c3c549030403d80400c04034864904090b107010340d81c04003400d90b0401c01c40e00311029408010801d01c0300c0c188164181030300700400c00b0302c0b070100304401ca9041c0d000f03d03440003030207581c0700e002c00c0c011505d0725001554801d0300141280c1300c260b0740c1c8092500a080a0164a080c0d001d01c252000c8401d03070500469010740e0304400030342188502e481c500d19007424901c20407600040480f0085000d0ba0703880718154400c0c21400c00480d0185044100e50703040044043d215a840d090034024001207480026840b01629403500784000031300d40044460340b4220488514203000302c0804004928400107400103400c65 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 147708120 1250 147706870 147706877
    0x609050706081806010503061602032205040b03150c0f0c100b01030c090b04121104020c01090308010503011a0d020d0209040c14180727030302010b0a0501110307120e1f 74
    0x7401010b00701a1648021b102c2c480d0302d0b9201c5008034444800d026840e00c1441d07036900480307241c01c1e004140c552036008100c124410859640307504010900f0a40a41010800704034050031404514281d1300020350701c041c1c81512550b00102e01211038400c4101120041c818582c22103203102c01d050448005000807032209400a414107162001040c0140c0211003070714400c05031242058145103411078440700c108004d84000051403003200603611144001e0502c0c2500d40c00202d81440705090140c0852810ba201500a038513013a004130040040350005a0340c54412244003410208600000c0e00d80c0d0401c4401030340c07000e062001d10007040010700084049411500c3d00e8440c41c2c050000300061040e0304854294100104000a080c0c24801d10031501518403410046c0400506c85a2200b2035010682048026030764800b81641d941c03030401c031804000c10342440d080b440c41e1000c41500d510ba029442000388440008907519100c1070254240b440c48200c040d1080ca2115100d00300d20219050100c90314011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 147709370 1250 147708120 147708151
    0x50303042102070603090606091b1d0f061c020f0301080705030109030e01030e070308030106030614060c030a0f02030f1801110c060412020f090c091507150207060905070608 76
    0x140100c0718080311100340c0c1900038041143c60150154003511000c041194000d0b07544034041440f0306d1510407032a1001f0890300f500e541088488000d009019229065247c043d01603109a003107035140c1750103040e1500140c0c1c180e074480079014099100c400c100d8104520b0503001240d03410030a4041000b66048546100844841c01e641e001807508031307100010060002000e00d0003003607042d4082d030443e1202182ca5021541495903035140c58189400a0304907000194642d8000c0000001200304150540c2c0100c1d00c00303282c0385059080d20754070311504280c0000e2140040b00031841a0090055403520311006a40a0707481200d10000703035000c5541070700036011806900c1306552100e000910401d61100c040c02e84c9140c14140181040c0c1c1d0103a0001c22a84103408500f5a6603640b161784030705004e01030085495031189011400c00045d1149070700071001c050f4080c00a200462a08456600b030082c80d8180160fa0310040d0801c1000341224070001780081c814103500160f650360110007144039801780218100b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 147710620 1250 147709370 147709403
    0x306110703020729031314010f061d06010c0c09050a09060507031a041a0301090501060509061c110103020c030c060a05010f050a0504020c1e0601080706050309031605071205030304 79
    0x4c8012800c1140d6006050360780b2441c00c80903100066421400c004000c188000103a1307603a0f058500c0055a0f040780d030351102d400c001615418011840580030904600028103242c451201d071010005200f141001111440542030112103d100d00c05000240341c01d100c0d0745005060140988900c0d03030116502c034900b90006000c00e20900c6a09e02b0001c00050410b011510719042001820045890078103442400010350343c03542d4244114103403a48200e00210f0b000b40381104100288600600071405102c02d0180c165642d4840038800c413001340e2203442c400b803c10b94000120024043c840814180b80710014100d48079020001d405486004200c2040c4926a201d020681401900d4031a8a0304816400f02c10310076480d09401410b0400d104074121580c0b1441000c41e080107000300198503015800c64070040c00b41030400e115101c09000c0d14200540f540c101040060350f284180014591422044a440720801000348460002014555450f0301d82c0c02d030505000381c0300d9000b49c40464041d60000c1d010300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 147711870 1250 147710620 147710639
    0x20d1103030604091407090504060f0506130203130f03051b03040b0d050c160f1106090901170a06050717150102150711030f0304020906010305060901060e060403061107030207 77
    0xa01182052019608580350070341404098115804101d032105803810312003403072620410001d0300600a24002141c2801d040c203102c0b080300c00801c0f002441030f00304403c0007255203814010708446100f4036001070792681e51105500108581e06801880c040d1642c15440900d42c1c07140184c51844007009906140010b02e085440d45da2142d84240c15100c003081c0848210030013994082070b4003030302c0100103c1c903140d00d10b2881c80d8070315403400c01100e1103c0d51b10400414010082d018002808054032150318000f8100005101c9410520034860380c0b1204550151036043c00707100c048141c90b030200083c002c0e402d00708406004809555208061803110b003002880f03604032465504490141030f006010920324040e800c00f00d081005050000f48004992224500d40080000788188155403070f582d6101d040c14410015501000340040741018140014800d00341c4d94090f8080c119181030a14520f4075a82802150050080b0f078005001203103040480344425010f0f0004022051080c1c2c2a2840e17a40c80d0200e80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 147713120 1250 147711870 147711887
    0xe040f061b0e030615041a030f030a1d0a05062503050c0f120403060b010207081006140429031204120215030f01260d0909050a020f07230a12020d 64
    0x20b1451503400c5c842504180d4805078104045200b4a610403180002003440c4c80601500090b1b0f0f94000921840030651001d440304c00e50503440e0900c00d03d1001380c5c0c0050028251406400e00c02e1100040888540e0303144840301460000c21041e943c005205c609002e44290424070b21101c0902603240801c10385c00010921102020455803850b04090031501d44c2d1004203095a552815441003201c0810b400d84100015040070310b501c203001c90036a040040b490448144904070310f020743d041880341d408800d8800700303042d00006e8050001451400c903c0020380340154138000e2000c00303d800100410119001c482c2100d400707009440c2c030704100d80300800183c0c8500c030842d500707104800c0c40001800991200b031880060000e0403502021040100c0c5840350500f210226010b0108035244801c01036900c00b400340d50307409400d26908509142e581480484c0520540100810383d0503040403080c2121034018103414a5441d590449500700c1c02031038201d0703039058a43d01a40140c45130b4001c03510072502c103100c0d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 147714370 1250 147713120 147713131
    0x1080c0d0b0c090a0803030a0e01060509010b18060f04081b0f010807140702101d0303041202150c0105040c080c19060507171903060b0906040e040f061b0e0306 70
    0x1103107025030342d0140c105a0ba030418103149600420520700002c800d00100043c0d0b008040c15240020200d602c96503041c00c40718241d014501031000c0e6801000204c1c0840140c0f440f090036030000000c000c1c614800603041d0b20a02d0b0201401038800b01300450408000520040c0001d42c120040e01401d440d0300412803042445540580003508180c00100b14a00c2000009952901c0d0410350b0f050106903400250f001c04c00684d240001010f940c80e440d54210368400401100b0000d034042c44c5031608000300c000da15201004080e000d00880004066101004000c0301c0500c00320704000c102c24246841c10f0b1441d9500fa1058462030300c41d0414500642c548101d00c19600e080d5011801c6100d407401c0010b4031140c106440c02c3e034a281243c0c03c619003d00080005104541c40c00030100307901e400180002d01180c0ca1178015030785e8500203100045d03154542c8801c550540b0302c0756415465941e290b2a00402400d0f026030001c24413400c10800511040b4248070030400710303102c2e03210003a50307004100c103166807601c08440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 147715620 1250 147714370 147714383
    0xf03080403021903020d20090c0d0218040e010603050d0908060f0702030903010501030c0f06020a08090d050f10020a12020304020306010302060d090c120605090d08040321050f01080c0d 81
    0x7000103103003656201c0b2202080c202020308550762a00001c040318010403003a2003004d079052201d400f52444c0c0b040f140c1548412100c80000307003800001c1020b17034007800282c620301a030700142c007008104410403c8401034500410a1005a040c0c500b9540a002c4078072080321648603041086501500a1310440e0940d8050002418141c1d2004292000413202400540030b601003003101d04420385080c042c545c042c41c0542d040046461400c8508203d0600c84d5012408640000c1c45e0800010000800c49200c0c1d482200d00b1201117006003402030400c110122540c0e445e21909951900007680d0740c000c0c2c4510b03c103586603210311003601c111803001e0317100442e4029855048a00140010320700350028008440701d4a90000c4c042226642c1c4d508404125081401c08001c010110405c11844d805003592111548024000e44005d915001d031080e40084c0c0010140148848a40d0141050b50079100c50703c41e02040501c1503007810406240c40d00828011190f06014488505156080184c2c2d1280c0c80d69102d41c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 147716870 1250 147715620 147715627
    0x12070507320907030603060213080f010c021e1f060503010b04020702010819110414030606010203090901150c0602120414010606050702042408150a090c09020a030e010606020d02070f0308 82
    0x1000b8000341c000781a4014182e5030074001c80400c2c83e0b4805031030780182d10402600d501e4208100c051614031140d0810169a0601d44d910181c168045400601550001c091080d917007600c0342d1041c1040c924680d850f100989014145405103d250405c600f2950258002c02c00e0b001d130701040c801a0310550001a001c00c007010003007000409055030020703101160300c2000612900f81d102c0718202d58882d90140016880c40d58180342140b40500110781c0214090000f5458043e02c0b90104411107414414445010281c041010032031b4002c800070b20307034907a01120442d901e18101c050b00741e5003a81600d0903203860302c0b980044121100144120815261603856a0303050212030b03400c00010f00140b00b180340d41013482010840c6a404001080c001030506480501420381008891042c140c20080a04c05024103044080012441458000e410740e103900130003598404440303209030302a10346511054819032a181000888a40c0072070008070309102c0c0c1e82507950300341d9200c0f081d14666202c2d0001401080081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 147718120 1250 147716870 147716969
    0x803120a0c0906300c020c091f120602071e031701081911030a0501050601120b010905040c030e0607090f0b0c0c060c0f0a080d050127020c12070507 65
    0x140b000140074015000d03528003070b400e540c10007174552564141015912041e0840c070300b4501001007a50080031070800410915100100c42d506003982e22070040280b800c07040c0c54080c02a6501298a2942c200700104e00b4000c844109000d441403040781a000100341740300160740c201001d240315040350743c0d1000520017148251421000c408070006e00700c07a413414156034a5102d480521103460030030b0003240001036625000c00050500c62041440c0494903141c2040342d103c81c0e030032101d482e05559095800044d04454203506800070075104040e58010b01c00c0000b003244240d44105038105a0b01402c2e4040041542d811075550300303008080418150303412004081d82c4a040c103e001d030101104110403a462005080c00303843c10b28103102026a00d007000013618900c54030042c05118014440f03108044038041e808002d84c0700d007050120700602296000240815030b40410400c810f0060f0301c1401c015500d00c151310b002a42d481c00f81c13180a00c8101000144001c20b041c0f1104014042d1641400800d0707607404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 147719370 1250 147718120 147718157
    0x10e040b0417041703040e0705040b03130213020c0a03030c030c08040b040812070e03010b0901080d080916060503041a0c0f0703050d090f020a230607020a0803120a0c0906 75
    0x1030201548040005210000740c548402d041c068130080305001442c0d0792800c210088480302001810740c814408c00300020400358030400b040ba9884400f800582c1503080003440022183c40d4250344402c1c5203800425403402110001c1145207110b0b2003501c01b00048881500d00360141c581c40b030700f42e40c00b042e182c500050200d041c035141c0c1d65000d4800c0c240540b07410140c0203608004034051390302c0c0b00041e4059958070042d040920a20701c01c5e02e01180c40c44403961415902c00d0307031000e078030070071100b0420300c0d00100d41c000c201000041c00c03004601d030401002c40d4950b01c00501d182c00032502545d0140c969a030ba40440d40d600100540034603040ca0051f481c00000703900b03040c025840550101c0800074100300880d4840507038861409814800c003602002c04110780100008800c842d0484d03400408140c82440000300716551081c50488199050741d2035110f5400005c42c17240301035000c20480c0c0030004603000c44254800c402031060100c0a002c200e01882e200701115051018082c00d008126a4900606103416 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 147720620 1250 147719370 147719393
    0x60a090506060c0601080a03080f0408041401030f020406030207021305310605040c0e0a050601080612070504090803100801060602100b0418032a0f0b3309010e040b04 73
    0x42c00c55890011030790000c92030284240d00ca848107400101c400c90400da404804950410b43d0341c4400f200908140e10f034100c0611443c03240240440d6605503401e8540d0081c0c11a280c5442075030001c40d01e8035680c2038050007075480703030b44200d10940d48030303010f0b21203048284500c03030003003000010961402945415044010750a4200f41da540740c4601c00400000381280201c1d8822403140484038100d51500940084545010300030101407810041000000c0e44e104401c0c940c4104100c988450341c410703115480e8200006504241d4100d8184444070f41030043d5200214015400480d40c0a4920707030304c648050807034819001d4400103811003848403084500c290090b102112005000285090b014048901d83c41c1c0c041c00c0c12404259988000115007010445120259003568190001c03d141952041104244050000d058800c03079408500d0703442242110210700d04103109141001e000d058140c00a40400403482d901c25203d10002103280032408510034015036010040f0302d0303281c40303641d2980030811 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 147721870 1250 147720620 147720631
    0x40c02070b2208010c0f11060f040209060409080d0e0c090c040b070c05040504060b0108011508132d050106060c080912031909080f0d12050901020d1a18060a0905 71
    0x71252030003c10810020311a44000034803a4440b100310880300380340a4202d074007079141c04140341c02c40303030420110104000450b580700790304031aa82c3c0160740740c00c0080e00815030710902904409010520304140c00d0f00740d108081c413805200c12180050f43c500f04002514904850300043c0c1c1c64240700c10415011004017500190f885154424802a200d00c00328040311811a0155521519011034080c00e50700040c2d11030241c18001c01003e014540310a010f442c1c10720145c504e161100e030222454007400310244540382c1c4d20748500607e070380a001d56a502899117058030307400c0d1215480c022000071100d01076101d6620169001c50128200120171081018480c41110a807225000803c103800d000200300502031040c01c529200c0c1b541032070030040b10b2071900f00c400f10b40c41d90581c0062100c00c42d0503045000200c03120411040420f85603182c81c5520f0290184c03840d1030f9440c508202140031600100d0180c0507003840192407114407501d0440075090411020350344190441c802030340910001d6925042941e009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 147723120 1250 147721870 147721927
    0x90b0612100e010b04092f150304050309090106020303070f170606160501021c06050d02030c0d030e0d0305040314070f0614041a04180c0e010806010c020909060105040c02070b 77
    0x5040a011405840b24180212a0811984403024400d0687c44a01840003ea0460602441500004688240d40d031110024500d0804400141081304c10400c41c0c1d080c08014008030300559444801a5407030700305955a0000c6641d0301c1142c0c088a11481c2003100745013481c5000009511004148100c941c04202c404840b818068900400300f0001d00050441480d480420010031889400c0c400c112240354111600c1a001c0842c0e40015175000900d444c4030000480d02c4040d2803900f484c0c150344060100550070f400503190b9038a40240354200d40680103ca00a1200c10421004016000c0c1c03180a5070180d003a07042c0007070300c0a100d8140728115600e040440d03035030403e18140d00e1b000005070b24549502040d120308400181408110301d5010101c1024901c0fa500307010740c44040d480685400410300605042290100000c0c001341c0c42103041d03001d26a000703000014503040665950f17480341d0090148030300035810940002c80d40f038400148001100c20000f16607007400d8030301030b004518801c905d5080c0c0c0c00c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 147724370 1250 147723120 147723131
    0x30f1101112104120311070507030b06120105070c060e01150306020702010e15040e0c07140a140a0305040e06030705100203030411120a23070801090b0612100e01 71
    0x800340315511071000100d0085440e604080d1201624004244a940e18a008041880005505400b24400030015420003158000302113001224601413540c0c06400d6215180c0300109222040521602500095503140101e44840e80e295003070315826150712000802c0c401d1302d203000c511140d105988550380e0b5800460000900b41d5030020781c1d402c54000303880c151b500181a904542c0c00040e8000c0c2c41e04140d54601c3e000304e00004030300d001d000300d1280d01c04d500b444800003a101c50000c0221180d55034031081103660000c070680f0080e076071400e1a9046500203590294180e118200144807001f07154544e551503d03142c03c00150b00b03803020b0040c1c00d0b103415110790390000c1a41c0e61000c2c0711844c0c0805550007503031203140c1410552901c0606d003c04070701800074401d020020310750205000c0d04030360f000311038170004242143d601940100741c00060290713800f4070754020070074190640282103414021040341d98152035030b604000c0c1c08811b290066089a01c16481302c6079846003a0014450803650200000e203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 147725620 1250 147724370 147724397
    0xb0604030b0415150e01050a081513050106270522031101090b070804030801060c0809041a04020f0a02060c0a20070810050105130b0105040902130b0a030207050f030307020703030f 79
    0x1285d08010081091000180641d0602c402031000800390040100440c4034244286200e107100a82031742c044074080072442c01402400d4211000420b42010600c40d4120b2480000880ca000600d0141d030550615011882c1c2c0c5992150700700c407014401c2643d200d05a0030f41d4003a100602c400c0c4100d00b10395201c3c03050074041402c42440c50f2140d100360f100c040561906250090000005030448400e011170300c94440081000d43d029101000b100399400210110360782c010b6040c08650880c0d803540180001741c000041c05100000d8880d410303054084601940310701000510341d000d01108000082c455031444080c143c8410810800750700d5134019620708a4076448000e041c40e926014401d5020385410040005090042d071024031080070040800603a40503c000800d244540c0c810038020300e030040340e9200b00584440c2d010008284900403542c0d10390344000c0103400307500308000c203490034000c01030495440d550104c1100d20440c039941c041c02c901400c40c2e509549a80c0c5100c10101042070740080c030803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 147726870 1250 147725620 147725651
    0xf0601030302010c090f08030304080705010e0106080f010606090e0c21040506010608010b030403090b130521150124030e010207050f0c041509020706020c160303030b0604030b0415 79
    0xa018500907400070a08200c100405040284c1c26071000f10f84104600702005203142c040162908958098051607450800c2e05241c3d025043c541e19440955190240004513440d00054045407007522400070302c52655140c50554107a00340e8424840103d4031840000c07a003049a00041448881c5130100c42005141a44e01c02e181000c210f9048805520560041c4003054028004d01d00420120300070920f50b00e0540c1e00105000c240d441a038450510100da031804800003120b440016040160039105040c0741301850100b030f090306050680c014000d10004d4410f08203119412416200d07200c401d00c240c40112049121000400c00e41d032400c04d6901c0082d98146402070000344001c80c0524020040310304007050080c20720350003051941c490740c80c100441d070080c4c250441946c11503102d440016255031050a040d8080e204a010316034060060504005041e00031247d00010f0b0ba0080c0e4003004125408014415240f145010141c110040744000900003102d18128003071000c2c140c070010030080c0909104c3c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 147728120 1250 147726870 147726883
    0x60b0402161104050c0f0d0c110a060912020a02150306030a0f080703020601050906010c0605040c08031216170a0504020a15050d14040309050d051203010902041404110406110f 77
    0x1142c0c2003196614450180c642401140e8014210500c1c4500d4440c0ca010319040910a500e002031a450720b4400b41c02e402c5010b403c0c2d0811105010082c4c03001d440705450481c0080c40101011140800640344a035034030751000980000c0241e020f801c04e4289010030100d4a00e6810051482b0b6041c80b600d00e51000089c0e1030b0049066241c89042c0d5161115074600d8040e08028050700420300035482101081180d03030b4000441200d00b80c12540015068880b2304100043c4a0030350440380603803100040f11602c0044040e03542e8421070b6501c03900c0d01002020841180c03000a805684800c0507000380110342d820b078055102c5a0401e2006200d00b07281c0b5030740e2a42100088d00e0070350308030224801007103410700c0c2109805009541030300c501328801c00f0310700341e500584120384500030310f401520a0301d041c04c00c20104100e0180503c0056040b50340b20760b910b040c0700003e51310034040c4800c01e8002c000300882c642007070f00072540441402101c243c201420141d040303402100121680c0024800d20021103a94001030008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 147729370 1250 147728120 147728123
    0x130f0207030905090703052203050c0307050c010801060804020109090c02010e0708070f091416050c01020d0501060f110d18091802090c0a08070c030e1002060405060a0209090103060b040216 83
    0x80c1c44842c0d01e040204040400018800760500d4241030400c80c002d081c42c400e4000c48000c11880040130400307803c044895000e22004038449200008030007052000000c1c0302041c00c08240c0c3c42002c1d582c0c923200c0072903100c6025a0000d020450b22501401000203580040c0d204401a07c000a20201c1d00e015032480d000711580807100d01e8211400c140140c040070b12081003c1d00030380030148091200f8811907030181c60002d062481000d244103030189110b1250040300c4418480070000e5403648001c0e400c203001400c00b0304c9101d0100e01c6480428680b613005842089001e002c00014111118034104142c0718842114800e07480f244118a0202e0116054413a4050602912507000c1080800d403044c090010b801038015403001c5000c0c004400380690040d030481e80311805140039040f2014501e02942c10510300c2c0c103101d921004281404240170390005119116070301810850b54140c80d5404068200e2051510150308021444011b102243d95500521001d00f00035000510b07080c400404086404283c200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 147730620 1250 147729370 147729377
    0x70609061113032102031801020a0f050309030d03090515060316030c090515060d180b0108010f0f1a0609030a050304060807030c022a0d051b13140105130f020703 71
    0x2801071140000e401d55546415410503542c203035035508003951b41e0245070881410200030f403c0c00c038540c1c0d2082c0106111254003c83c440200d40c0240b414079201c1e000b04403564007034401e03101c0808242e0310a00408250310707041005048903015000069000c3c0d54000d01c00c40c1c06100e100307400d41c2c50310340c603080400c000e6002e0012a018281082038560680741c020700314442041200c800804181d03905c0c821180094088040003c642e140d01c0b850340a40740c00c1980c0903102102c004000900041d064200b6a14103c100b03c0c1040704408101c0030100304c030000074000041c0c064120b02c01c016401d0003001840e11400050880b0403850742c5a8500c0d10b503500a8002e103001500c0d5105010149416005844001045002034251048441c03040314102142e84d111004241c10880c400c840c9840310b00d0042d1040350130030207668a0b0500018a101a20701075104180110104449201484018850b00884001c6811584110703441c140c00c02101d020f052110a070055030301c81101c00c800c0303400e200400380135200c0d48 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 147731870 1250 147730620 147730657
    0xd060501091401021c030f060603090515010b0f0703020c030307032006090615061207020309012a030f050c1f0609140601031107050717060c07080706090611 69
    0x600320100303a4001c2d142c0340c0000c40380c8540caa801207100e0b90311400d54980b481d42441c80c04402c8016060403840305540a1612801140e1968950803068015000b8400c0b9501d55003401080c002c80c0e4801d03c600201100140089161488448003c001103802481181d881c1d01c26000000c0c11503005200880200e5400c54805942c3c13588000d842020342c1c0c3d03a50280916182100400d516000000e010081140b94507041e25045e5840805541c1c071080b0039940c031122840c240760b000c0d681c0c1e0701081141740803e62409000c2c42d054000f040030140442c800c00e0310f000104c42a43d0544d860b0712180c602d0001d220052000d0740315440104141080022103161448991590030510400c03602680c03c42ca20302c47c241f400081c0c0101074140404e810103028640003641000001d00000c250046450040607030080b01800603010660b800c803a4985401c64080e24090b07140c030b2081d80881c1c42020ba004007a50030038000ca0000c40c65a0740605c90050003071901084d0062021076280340c07075105003100c064002c0b120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 147733120 1250 147731870 147731879
    0x110f0a0e010f050f012a1403130f0f05030c0d080717030403080604050708150a1a070606150207060c0510050403020d0e0f030c0607061803020706170106090b031b0d06 73
    0x31040404008400c3c00c01c1c0002e050815140780c840c81500f040d030803046c1150a115401c020b8040f561600d00705907041940e46034001c03c15902d405003444c3c4110301d581c0c0204500403074164a015252400c0300c000400400b210000e050600c01203001441e02a03500d10703014851f11010131465501d0b441c0000210841958070714182c68007604040c805041140214035147c1013080960300000721640014004a000b070424072010000342c42d4041680100241e1200c2900400c08405080301a0000d140704401c180101502d5210b4100110039520551005a024410800a0501902583d58001d004009880d40324843e804100107680382501c0860041e4804181359080340e6000180b442c64a80c01c480404801501100180c0c2e529410204180310b00000118038017000841e070301400340e52848100303c031084a074905000e5100d0945106800206010200848440300502c0c10541030b10341e5922244456070815901307401e19007006250f24140c0441d0706005c046491144054802454075000c0032a0745810b2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 147734370 1250 147733120 147733129
    0x7090603050d140f0405010503060d06020c0c0a1203140a03020c0d080712050108030a050f160b01030b28020c1f0203010f06022107020a03080c030d06060507110f0a0e010f05 76
    0x4250f03412404003800303030358982d5811400700c0b01100c0091030003580720340f101070000c0e426004111008013180d100280c18141054040b0310500604421a00500103540e80c481c48080d0052000300200022141403d501c0b0719941c010140031901c056260042c10070303070b0140d40c951504001c4540480415524010440100c4c0d0090300101c00910f186010702c0154504000c3c15528001d80401d03c081c4600429012610303201a0156014139001e19004040321406040401c4030200c00c2c0400e48071101300500003400c0c0ba41076003030922506e00e483c04a054001d142000c0000a40100b103a01e03646015170030511107410203440c010079221219000040e0343e0352600e44003544115a41d030101c0f0554000800ea50040344031200000008400d030a0915541c0d481840042c0405075940c0009000300030200e90000c12800c00030107000003044421007000965200d10060740e042c010320200810344045c0c0410403046042990100d010074102030070045255454268000b2080000d802864031190b480e00100007500c5c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 147735620 1250 147734370 147734387
    0x605010b0d1a10030b010314011d0702030a080601080a24060207050109030c0e041103100f05060d11040e010b0d080d0b0a12060207020d0206190206090706020d03050907090603050d 79
    0xc40c004990569001d100801d240c4800f0454020030f25545825240599000360451300c000d007288482101c0940c1c403030480160381146d8140c00740303030180d102c0005800305d40000111040519076032186142030360b80c10011504004000c2110000580b100d04800c0c0740048501d90704940b0842a00007078541c1d0600100a240031001d910050400c22404020030100e0820320400f001d50704690100320383c940c0c031800c09807080c3c5100c006543e050300c40c0c032040c3d065100b1103a1241c07a000090704d90034080c030b403602c0b0100a002240d448020b007240402100b0407400b454560b021b80126094032001103584c589003c00940810070b17080b0203031511a0b0006500715012518880c401450710704403500101c60b03041681c464903030a54130340c00800c11390340082c080043d50740d19a102c4000640c02030101e99030750002540d4494440b0a125510050310521000c00c0a10348007140074803d80d405540141200e054519003200500301c00781c0060001c2c0102c01d00416921800d0065502650088000308903e00a1000003001c1d501c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 147736870 1250 147735620 147735641
    0x6030606102712030903031103131e05360c1c0b0306190b010e0906010c060b0307090903080c03060d02040902031009060b0f01031103060d0804030605010b0d 69
    0x40c0455465031040303800020708003801640e02107140707024402c1140000c0c4440b03140c02c88508038002110790404c05a01418440589100790740d502c03040d4a108103559624081d01100c0c658040b0850424400b040b140c085041c40311038444c6d50343c000c0550350804a0129100b03c0c01c0302c5100980200c10809042c4202000d141020100143c090b041c034282c0a8008203000c0d103521464505122a03407012103401d035400c601502d8400a0036034046d404d06c40c1c4140314000d000c1207012110345c00c180e8103118a6000d600c400c0001c10011b000300007195241001112840607018041300c217503556054080c081d49013080014041c01410380000344d505000c0c103015052040003050031021141c10001c01065481d524114072081d6415039002c500c240342880001d0902814051569000340380041700402d01005401c1081e1110003955800b0240003441300450a55841d0300f501e00002c1c5042020aa550409514928101740141340c21424242c5035541c04094544c2a40100320220011405a1921038107200d01c00400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 147738120 1250 147736870 147736879
    0x90f06091914030a0525030615230a0501050f040b071a090708100c1407030306031101021501030f031704050a0501050c040302010c03030b03010e030f130905010b18010c06020d0506030606 82
    0x1003065914646c1e521000c042110305041c0c403030b240300c5006e0b000101d000040c50340324101b401203a0380c4a20210074020700d481f60b80c8566060040c280540d01800d0000c0c040044080c0c44d041711607061800644442d0302913103801c0c030320300410400080e001e207842e40030b80803003882400c2d003204550800d402d03078a284401070f100040c035401c44c210800451600040e4542d504842810101d03201407401001d48040e182c0800145010754000380c010100356141d40704a06691050301d90107014000c02004a07035640c29001a80c10158002006101007001c0044d03060340f0620900d880c02c80c20f000e44203070403107107a410b42c1c04441a41c4103c2d06402046000c0c0241c60f4800c804072501c0f42014510b03000200011000300e4007030285541c0cac5440e140c4075102074100c000d81400703407400c49669446181c03040701c40b07038485401101d4a040c800800314080e82c007801268101c0b6a02105a07042c40106080c1c146030b0714883c070009040c00b1340364142d040014028009050030072800003000650b403401c401858144440202141d109 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 147739370 1250 147738120 147738133
    0x4270f1419030e030309100e0102060a0605060412172209020a05070f0302071e06020709020306150a05091801090b030a2f060c031c06030305090f0609191403 69
    0x1e510310804001d85141c06251884038120802c02280c111303c134046007581c1240e45901050704064129404c0204003800713a084400c10740e202400307442180e5180c01100c0d8030110820080111191341e01510040358000d100940c400703e1004401849540150030100340c40740b1441120041001d00381039400100001c4d1025450044201001001d512800400078a102c2c4110408800d040c805c0082102510406d50340002c0890841c00030455240369105010040c03098a002180d064040d000782c0b80543c102a03d0310000c00011804010381c1d80040b4070a0301042800c1c0148441035903010522040a00022420712840d414000102c050f545040b50283c02540000820310018070030b80c12044c03941400c8458250511020410000f1001545090661009001c038440c401404080000c2900c0f83c0303500d1b408080080d079180000d0980d521031101602007941400300036a41e00b42071032600f4802d400208032a2070140c103400002c4902180c0542409207641c0c420007800808011460090b2151003180280030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 147740620 1250 147739370 147739393
    0xe0d0c0f060e12010605060426010f0e10090b0c1c050a021e03061302031503030f0c0105070801030302060708070309020414060a060c05122b0903140a0e04270f14 71
    0x147c600c52849003610b503d00d80091009906550034030780820000f54002400714600400d5000081c0070b0103410b071009405807001c680d5000ca038600c900d1000950000c440f10300c1d6a514038403c0c600c1e40080c880c01d841a0490011200c442c074891050310720596480c1001a140e0025030030702d048501c48900b21075080c0c5810814060700d0ba03248941e01c41940b0703011001607626a19100101e0100c0c540700350141e09444042409454141a50301415501c2d8405008000c26940c020044a4440081c400600541c0054011901203440780c1001544904170382070100d900f03105a8042012074035020113452480190320103015492900c05500700080ca428a00f007400e04903140c85141e00e070044502c2c0040c2c0c0003400180c151107642a5429030304444644e040d40340c8400d01030640745015100300c2c0002c600066040162661450b05c0380d098842128981d540c030781017000d16400740300040c4a2b43d40d004202c0e183c401c0c0080c040d1b948841170450854850454a540241513241028442c4907480d003880c070300d410441c0d4024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 147741870 1250 147740620 147740629
    0x506130611180d05120708030a181205070309050a03080316020f0c011b060905061501050f0703030e070e1806090a050c09150d141504030e0d0c0f060e12010605 70
    0x5141c440c02ca43c03d865060b99842c3c514901100c0121340076241001003a00e1052002403400b81d40f24900303000301840050780035140e07a2202c2e10046c030000d140c400c4941c6250030052044e00a401c0061103410403890103500d800001d98032680a03801143c0e0803038004104007500f0700c52486812855201d00050648503070046110780c03956a008811810071040d5503190301500c00760851284d5164000300c082109030f0640c01c15581781e031400c907421050a04e07a15070702006548030380c0403541c6200702c0004290418003156412005400c800215560510540c8404500400b103504050700a61004510260072014a904241008801020110346070001c40b0304002080000c104a211102c1c1210320981c55590100540d1901c40054840d0f5002130043c44800304102d5100e003001070840031201110b00b800d150424032000030b601110010f00181003001a01e4041c01c00140200e052031054070101480e5480c0c00403243c03541c585030321201c005801d40740c151840e41003503205070304155800c00081c011181401c0104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 147743120 1250 147741870 147741907
    0x160209012c07120c0516030905011106040c0302060c15070306060306061803061503080406021f0504050c040507030207062909010b09271306050108031e0904090506130611 75
    0x203050380c0d51580d4001c1c214031700c03403411150200e0f221070803180160030508006192040d28054180420b00458442004a070000749e407a1256910100c250007050071542404416006484404e4a5100f0b91203d55a95a500003485100701c4c8160380014625140480c0101a07070380980c003840a01050654494070b641540f00703072400b82e0381c020002294200141341e061305480c0e0f26500c041d1525502117000b20706283d004c07074000071501c410320f403102551101c455903908480c407e540041441d8022412008241025000141c0c0720b102420014200b0140b9103c4034256031116614400450661070b1000310030f62201842c49032401d080c0c503803640319810044020310340e200f0850b80d5442001017400d0040300c4600d14060088400a846034010b20342440700c0d48240910010104542c402c0c2410000b08000c20004159180c4c080d403402000d24800308010b0300e003555401a032605130095101d01c0500081041008a01d008100451080043c8100ca0921004403000e8547e0700e0103c410401448040702c1c01c03840702 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 147744370 1250 147743120 147743147
    0x312090d0f050717030309010c03051509040204060914100603021312020a0b0c0303070e030102090307050112060801050405061905011203051b1009150b01090308160209012c07 77
    0x8000d40001d40c180720349000340b140c0c00f072a50802c00601141280001001842c041c0c2c1c40240280f001c03214140056056a4088a4605040464000819141c580820525086800680001801a240e1f4030403400c1d10200107900c8a0002c1030000c3c007400c6903ca54100008054030300e011400c22581c0385c564440d0f0315240c420300c54854038076282c04056555186031100102000310481c6c1e900c0c942d00c8440c0d52079401c216180404241031038800b40c010308041c001c039200d85000030041c00d03446090900540da031400e10f84844104581c1d40c40085171007282449098002e038001c00c02400503141450142d400c51345400cbe0f051280ca03060000401507800d0760015809821b0345810142d13161025101c1075815241c041e0791a1249101e410150030175070606034041c504990184001c0d55051391800c585a0a44180d0fa4a01c0d00064159400b00040344030a406012240782050f25201100307510b0300003500e03d4400b03811024200005001c0c03c1c217000e010300350f5030940c115481180210382ca00004090701c000240d040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 147745620 1250 147744370 147744383
    0x60f070e060705012304060b030607081f051203090307060c0803060607020102030d090c1e03110402090d12020106091b0e06090a031a0414210702010c02030d030b0312090d 75
    0x810b001080341c2904500d4101a040031101d114480403683c2070354455003502c040c1d600c241341c02ca0030388142c00d0104126100d003040e80ca9984294548a0606c04032105c00c00d080c5203200301115010401c4d564600740c495045950300011920381000c0d03400c00d030500d14503034043c0c401c2c0402c40300f00c07100003100c0d641501c1d8081c60864541d078540031180010707400c1d44181115a4110b03858402d001c020440b5040750b00c02954603080d0742c9409540041039070050014580000f502501000b03207844000d00d0560003c3c550200080d140ca1580300250f03651040700c124040036440981d45800c81400a45030070721811040c0ca840701c1000c0240c2c88000710203003070111819a2039003e5000010140c8507038840004140086d030344120005000090145050114041620125581c00f050300b10705000f40c0001524118074030003928203001c105038802d0b1500099101031012414480c031001e10001680c1c0501000c0913100c010303200440d0400340ca00c10075040c10f40181c00c40900403001c0c0585021078440d10128120280d2005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 147746870 1250 147745620 147745627
    0xa030302120f04031a0405010b010e0a0504090507031b05010806040b130f02130b0702130203010e0f25031a040219050c120a2615130f05090a05060f070e06 68
    0x70341181d030034031482d00064810170a00040d031018540a00b012442240544020080d80540b440110f1f004200003401c075a01128556082c082803601c1d41c850004c8621074000c8030365099032661524001000204062640c5200a00c10422540c001440d86d600c2241268108640a503a00c005a001c40d20003010f60b048640c0d03040000300c80d203110303030440b02c41800100005000f160340c0e4840000e03d91141c030381280a20380690034809258814029a07041ea410210760f070703940e40d0302c0c001e00324000a00108900c00005a5100200b05910341c080703e403114072000d40d004901c40c0030402e000e20900c034804118074040c41c410000d80e03102001080840d0600c2c2200d1402c156500c0d9200d44951074910640f8500700c0c01d107800141409065002250a400c0e410300d14008024070b200b042c082001280120380300c80907060041030514a91922403500040052964400580794164034684000c1b02d40c00c441500550b404013103011b040c020100282c59000c17407180540c50041c9004540244030310001b124440c020030380070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 147748120 1250 147746870 147746887
    0x30f060b040b0c1002030405070506070f1505180a050303070507030903020405010e1b03070801120311150702100b030309010c0515270f06070e030c0a0e0a06050a03030212 75
    0x1500100014030602021580355034031031003012003503030248950594900c1940e4034040d00140600a03607208a4100c0080e2061519082c103001440e8020f00089449240c13207190f1100050074440d050700380c1d4400c5103000a440c54440c4c00303c03428508403420021683e100012000014900104807540541e5518007181c0702c4205180903540420641c00c02944942044000701e00c50f29031700181032044e1382101613003240c001082c00b0400d10748800d4400c0b00028646400500c110740104040c5d60741c81c2d2082c50541c03070454030f40b01d4442c2010001e181c007110304020201445003841d4108180710b6a41081501004007110401c0080e40d00e1003203840407414002c214022401f030100070b020181c2d5841d04c0c003c00c0c040e80c0c641304403d51403c600401c1d03101c1c0701900012051500c01c01c00110520b0040420b402440e082e00c80c00000d13129042030b9003900b98144159010240f094072070b070b048040200b40c3d01071041c2030307420500a0038050780c105407c09805040e0901d010004a540094a541c3c4104c56042c946c2d50340319034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 147749370 1250 147748120 147748151
    0xc0e34030b030709020c010507020106050d030f030506120114071101140619150f140316210609090203060a0903170c0f030103050a03030501050a05010e040b121510150f03 75
    0x5134041400580b001c01e00d941e0a00064110500c40c44480c0e00070051651124104400d80c0c07050036001d00001c070303a658865030407402544416001a002441121012800c0e0307451425180542098040c0e44007a105020718241c02c1014008aa00c00c1d20091126640081c1d440d0382e2a0340c02001a440780056200e11030410122002d103a0203003000e20480201401c50304405014841007141300400034060350705003015442044c4c01d6a0065000c00300c000119104500c04540c410101929000c0ca8140d9510200c182d4036144252030042107030301c001085489541c0105424150000c1000b840c1505001d0000f0010703500c8461025801c812803114107443e01c9400d0714210b1030141008207001e03150000008814000009803059035640310380e406004a1b80c81e0390912000304803070b100300740c0450640c400da94014505a046904000805001c200440300302d10049403030310801c4e210700c604c0c1c003d2400910889400c4880c200025120f80d210131803465000380ca0082040b110702c0c40580405944084d4405031400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 147750620 1250 147749370 147749383
    0x4020411040f0f0504200901030605220b030609060601110307021c0b100503030405060d0b060403060902030f01050903030f0a090b0103140706020a020a0b03070c0c0e34030b03 77
    0x4461a00988680c0c0700c01c002e92200d140c0340149903c00310f4007640060b0034a854011403100b03c80c10081049642c1c4c070310214a043d03400c018000743c1490307111500451240c84005088104801e4030319007101d400404a0104200c2d004800c0041c0030307401c50740030004075120006415030032a10030b20f810a2500949034016043d8014910300950044180d000103118209a892413000d0901541c100806030f1180413a03074034650703000e2140d41c0c0c242e00300344410004c034a04038000c2d08030125400000f03e138400c1c0e4100090580c0d440343c1c004030b0b940b983d20b61030b100035030808001030207124201c10000c00c024206511690758900004000d1244451040d00242d0100340e02c0d04102032503a8058295404d5507107030b00e03280020300303203034550708016118500c80010007510000c0d08036244c5401801d14100725052000b02a990b40c0010440d00c24010000c0080c0006100c0b03005000040100b009403030035509055001c0c40d6040f19401520865080e5070700186501021010718810300d81c02418005218040180030070704001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 147751870 1250 147750620 147750641
    0xa0e0a0b0c0601170a0c06050f0c0708030309150403080604050c070602030a0509060a0b090103020d170a0c020f040902090a05040303200d0605030303040503030c0315101107051c0308040204 83
    0x2808030707001c4241d4030001040c078180c599045042c144d40c80000c00e002e540b8114220081c10181b0011010400f85001c0c030010102c08643d02c114074a4130b0f04a942e054541b159951140f070266000104011341801305020b079031a503c036820500440c0e4205510001e101d86006800184541c1d41d980200c0c9481c007181007160006584001c080d52241303020415140208011210f204480c0210307000280d003400300b442009000310004107224166425502030101c0c100850300c0031908034035401d45c4035802028a10142240155581d03d017030454165106020800110360440c60217182404a04401030341d4503210705900030703c01400010030b60340300c0c10120f01a18521401200c04009907045418a8000e14024402184141c038240b05413076441c0706055482c4001c0720040d141d80c0040c4003040e13003d04c40800035a000b0301d0001042315442e450400181e07654040e051090040384080040c42c01c4002e0a108000080100700c1c2c4609092040749019441c0380002417000b020004242d00060840d030316a480102140c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 147753120 1250 147751870 147751889
    0xb031905010e0601030b030d14090a0f03120207060503060904030c030201140c07020f0a151805030304151808030417150109060e0c030603070608060d02120319090b0a0e0a 75
    0x15603540d000d0344002c15041d103100380000d00b015800045820009440c82d21040325541e49070180c294920410f11540001031403030f038030203c4200c00062601c102030040010f0350194000301d80c04944980080d1a004c00b81d80b01000740b0505204000e001d580340d803142d590054050800c8102e085003442d0032401000401d402e4004c1d0b5807804140055a40d104020300f205500c00ea80c0305d804402d000c02008076003240c620071f980619280d01026202c5501c90f03804206d03085504400d031501a0340303460000c1c1c00c2d0381050b0040441401d00130241d0058540c441c02001010300020f10911169080644044c1c03644070b94060341640340d0300100d4504036404d04000f012078558845c05003401ca075071036006400c0584103a114803600c4030f0050010800c0c0f0307007110080f207001306802001090503d14000040d10520002043e640d03220150041110142e02c1c1c0031a04c23140002c0302000f540d510300004101341d814038107405050301000081c0c0c40c1403080302c94000c00c844618016041c00f0307443c40900700004030803169540000000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 147754370 1250 147753120 147753131
    0x2060f09161e05010801080d0509060d02030103080310051905040e0c19150206070e04110c01020a020a03020706050702030a060e0703170403050d14180312070f1203090b010b0319 78
    0x42c0ca0040720b4503103810348003a0711240c41680e41ea00440d414842070041d80c0b015080000c4c1c00840c180200010b0107100405400c06081416084e41e5100700c0c1c10990040e5104100042084052030001d0240e01c05014100e840c00d080103030142d0b1400d0b15038001c1c001c013805159205c16906003003c042003036039800c00001748144c00d50711800546681c00c07103203889503045600d4444006800701c0c2c00425011b00c10006a039810011040600410000d84007a205402c0800020450b1482c2c8181c03e000a0030200f8498009000081c0107140003450910036510401c1042400d100c00d00043e0b1b800720f640d048560708000c001c2010b2404030349160600400d5440140003118100280b441000c001010700216400f52081e0341203c00046c5c01a94141c07452031407290f00342c0c4100505601e5001501d489040b40c4c0c4081c08407944000d04400d40201d651100710150b070304a8604000c0810400303000e040c00206031044c070301400452681d070388e0740c01d8014040c0903000322b80f100480004d61000307462180100b0014045000c3c0321 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 147755620 1250 147754370 147754379
    0x3150909050c13020910030b0d0602040b090315010501050f030414030714070603060b0912011e060504270308090f070603050711070b040909020d0209010e01060f0801050102060f0916 80
    0x26221054481d0b40d0194502e5070294604410034800d0301c0f071024002d00b0700201280d254104a00804411070420360003000850200041229440944054421600125030b2402e02c641014505001240c8101e0354400080060040ea64403c00b40c640c00e0072103484071502c0f0789a0b4904800c81491580100700c240c0b0011840505110710303528001d5603140e170359094805194035184c0c00c0b020389034a8002d407854001c00700002002e86c2040e00e4100310070980c0d040000780c0b1103581d1080b80c03090310641000a10054072500c0a10440c901885000504140750307800c052500400e07100302c0001000480041c060004c5e5500180c04118140304894901060300c040e07034034454603a00003400600c0c0c2070b94500002090a0000d080700320300001c00100307941d41d882480d07003414941402e4102400c00c1c6c41e0100d801c903c010071002d00588908031624060412034900c504950304000e0000c10007020613500b8400c10000100404c996600454025040f12444a98552981c0c42d08103082c40c0c089001412403800288000018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 147756870 1250 147755620 147755623
    0x5150d1d0d080f100312020f06010b04060e0303160f0203100f0f0612020d140c06180306131e0602160c15050705120703020708070306090209061f0315090905 69
    0x14011280c6407101e0750360b500c0b03004084042c1582103070301c11100000c01304180041041880601e4550305a0f204503032804d0703030b00c1c0301ca0b0303040040aa10182c80c070a0040303401d001e91038010703544520780c0c0029001142021540d004907021040c45c9407010380000f1000f4845429920144241000020010b600f482580030400324100201100c03c000035041e13140c070001090450603403079000038103034004003050100052501c803c1050300308554640200d03c154a4a51810b841d40409014100400101d1484200e64041070504101c1d0040100840c040d40d5400d072000512a09840010030000100c070914400c0c541c40c08600038854500c3c4100300c4800b030185a0f08105c04c00304014180d8070441500b14248044000542d51402034220081c03481e0008000c01c006c9140110141c04450f000748119a08281e0b68010301e402c05405d40c105950480d190f000f090150b05050301e10300d42140b8151a4070345005580f084040c03545a04074031140405883d00301c5042026003298030003001d402c0003a020003c0a550f4035125 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 147758120 1250 147756870 147756883
    0x120d110a090315050c0a030f0b030a0c1e030512090d0605040f11010f050a1107030204110c0f0309010813030e06030c070201021009020307180e12090f0a05150d1d 71
    0x715a00caa001c85810304400a44c02001e0140c1c220043e110308280b04000207901425213600c421062503903800c0b404600d40d800f04020381440e4054030350b034494039080a02002c14103441c1011100000c11901c0104000f940c001144a41508500710060701c0310034110003e03403600d000c2d80014101a00300424001840044217181c3c0c1000d01c141c0410720100c00c2c0780010b4a03100340440720f03d800b055060090030f642c1070042ca601070710b460f1460300b84c0c1d900c90f480368001800c0b10903199200314081d0001c1040700849200304a413000d50000e100c015420240706d03074002050307c2d00041a840781404e484824104143c01108194088140141856120310340400c0c330303101c660005102a401485021000c3d140e0b07980718070034019500c2d00174000c1d242d0142132904014800300c512103a0f001582c1d58040c0840c0304d96090164901d0111510721013940c40c0569420400805404403c0314420308240104010720754418400540c2c00d500d02c44100d4590004616210041690703181c0ca00000d0310705c1960240382c0201140f0b9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 147759370 1250 147758120 147758123
    0x1140d0f1b0201050126010902040c111b031b0301021e13090603080a030c05070f05010b181005091b0c0303060108090d0518040605041d010501080f120d110a0903 71
    0x4421406001c1802c074280c40c02840750035040c40c00030f5200403954801550034a03602c0130720300000c00d1030390030740e40071900b100c0850000c5800500c003100c1d0b80010003024064801e01c18416040c2030ba2400c0400700103526500d824441500224078403102e0342c89a1002c0d01559040401c0003031075544141011000c503035990180851181c0381d0420100400d44220501c61001070b01d800122250030844220015001002c0140101c020310606110b420300280c0b0982c8001c84040c416400412074842620130b00250fa21340340d03070881001072403a0800015808200030304080701c038100d85100e516240c001104440c3c514040c080c650507100020404103040e000030065001d900c080c0d0b1707a980d1940d02c1c03001d116110301007050060001803041024510010368100d0b4122122070080002800940e5640042c00b11054003d01c0560040072480140c1130200c00c1c4a803600611112019046c0c1b4100d5401d07040d25000b0725401184140c2001c10508040c018a07800044007515101a0350356881c0b11104c0540f0441c0c0d640700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 147760620 1250 147759370 147759401
    0xa080a0f030e0a060c0807020105070209042d020321090607060b0a0b0705030406030f0b040608010c110c010c031101020c010513051002040609050609030c21010b04060e040201140d0f 80
    0xc80c00903c1c1003046000c812140513030385080e0162000d582d1080c40b5803182170280d042000a0100e84003594441c198240541d1141a420020b030080030584900c0b09070b1903401401c0740003c1c0807407a001d618046481d01e004403081000b05c030301391245200000b07580114101c41d0b400180200d083c40402001da407083c5108c21040300c44c032602d513985098025a911035100300030308940050000300b086600036040901100051103010410740c96400c04107084983c268040d20043c1c0d1180c0000c04034580103480ca6004201c41c5002d451200e6403140003800030081000c0007810080c2c010b0900c45156001e43c1507270b10440f6240024801030400d100e410403c8499400159003600454910b0604501030307108890803a1000d4a5905071140780808001c880c1c1c1002c07544541600030201a601c40303640d154800304c0c00950b440340510400101340b00d110b003180c0502000ba0f0045140103030600404091586156010f5424603003109000d00780480d1062900446400000341d070300b00001803542e0b860030b8100111945036100d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 147761870 1250 147760620 147760637
    0x210b0114090d080a0903050102070b0a0b0d02060a140c0304030309030201021e0c1c0f121202090f0f03030714030409052410020703080f0d0b0603011802090a080a0f03 73
    0x301818064421580310355400700000341c2007000503405030f000c0c1164840740d04003141d185542ea115a42640d1041c10122141010b181c10040c40068610036100c0c161801c0d51107042407909075001c03c0b072a204050102052005c8078115181d81d9984004031426080040c05172274490fa07892a000c0c100c202c2c0c0c0e010403800b50107031308130926004040701a20449408108000c0c02d01881090911030380ca400e40b4030f00c2160740084510b01010440c001c10810b81036210300e0402d6106d00020400034800d420400301348080e180108441c42c10382c3c1d00d49280f81181d540480710391408460b0800001d01c1c5100750300d001010300c40d0b231805c9642600340110203881207818510040c0507035540c0c0ca040d1000c80000d84081e004500341c42440203050b0420840b040c258080c24011110714545940752192250802c40805c1c10051000131650040c81040c02200c00d07540041d14414190b5040000b420324640d1405801c007010340c1d01080c005003a03900c2d000c05c40c00511071542034070765032099418041c410700d545005c194040750840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 147763120 1250 147761870 147761897
    0x13060e1c1d01030902061b06060906040e06010308030a1506020d0206070c0f11040204170303040c0509040f030c080d0903020a0b011e0501080405070b2b060f0b0a210b01 74
    0x141c0709540d88561a40300519008200c03001500180010f000581c0c002c10207200500c401c0c411402d00505005450006106601d0440100321207900e00030006070181c1d060032841001c01000003040f5040d241d104603010344035030780c0d5540b41c0002d20046011043c60040301c4000200c0d25008581c02e581e00c01c0c540e0a440742c56a96900c00e6030304400b203540040c880320341ca0701c148002c1132101026500c1c1010041000d89065645c1003240780002191148290503000001800200410b1809200c000c1c08191103111686c9410344408189025902024043c006c1d00380724541000708000c00ca48030f5000002c4d080001d030f501428002d5035031507034040c1140c00282030000400d40081d5407082e6180c12000c06412008242044011240181c2c090030485042c481c3d11404201803061030b025000d081501781042040e899400b111400b60054046028491854641c3c20b100800440b0000707410f60b203094402c2640d400022000f200c42220102007400700ca112403d6114a41e0403640040340c0d151400d036541203100707140c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 147764370 1250 147763120 147763127
    0x1c0504140607020901050f150408010b0a1a0f070c030206070f06051b18030c1507051606050904091a01090f060f0e04030f180b0a11010203160813060e1c 67
    0x4404000c0d50185581300104802d1070f100c65aa000f12401416000c1c8075510900070f1b45458205800009440e5101c1d0380009050a00880c010700070401c821080c04000907160131144140b06071401d041c0c2c80790001424005110b82801c0000095130b01500c2d842e0798902c030b820176030041c99408004a80d1a030404d0007040c0c826000d450b0000b64840848c04462910104124031445160500800e68050040760044a80c0d0b030b5520042e02c400613051201c2c41ea844e1060710785030381051a01d085188141e0304180c820702c0025030000c107680c0000c4003a540060100c0c0306040ca00310300b51001302a00000c000c2403001042d04400341e042400d50341a02c0710140401900d03200e42d01900c102502800500520240c0080d0201e841155040b0744540241480a1800220103080d4480c140a410681804400246280519034059a401c0314204050021401c50420350050368144000031200380400000c1004103c0008961201c84440c5600800401541b0b11080e071691701c85103880d1040000b080807a202c031140700e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 147765620 1250 147764370 147764377
    0x60d0b270601240e100c0204092303030702060c03060103110c01060302030c0a030519170406020f0601050109050904060c05040803070c0e06010c1e0602040e130b0108030f040303030e1c05041406 85
    0x2da13889400a000d410402d02034981c0c0d841c082d51781080212901200941c42c0c80c071070a0062802401c01c03400000500340b517071701003429200c0ca00750309178020010001b40d140d000c80d1954114059654407552a125040100d010784401e0000c030760040c4000a03c1d86080034154085000c4034800e81c05c2d99030580e5204100841c0b000755120290080d000303480a0100626a80c4003000302c2803280e84130090101402c1841d0340d05030001e0b0069005a07020989580c683c22080181900400003441c10380c0b125801c1038082211230b1806000281501d41750344182c14030034041d42c1500c015004540c101da403600b24a0a264011040c5840b03105400015407001c1402e9521a80c202c0e00c00c40d42280207a0903502c4412442c60104940b01e42c2038440f280c1c28003001c6941c0034050071b01d600070440200380403403140f59414026a1030302d060340005071543c0104440d44814841c01c090ba0101e0760542400038200811002c803d003000c00d6241003200e4403512032000d42c030564102000e0015100c0749a00a051107040c141401503912 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 147766870 1250 147765620 147765689
    0x60e0411030105010b0a031104150206101a0f09030c150a11060601020607050d02071703061f0e061608031806010e19020a0309061e14060d0b270601 65
    0x400304603c14800e8040c0d04146540391180e04202c3ca030655030380d2b4180061000d45816401a00040c1c2840f0f55008460848809004840d000304000d40039900b2080046c8140d070b0550305a110041041d044a9905021080b0480805480c0c0c1c0071019083d800c980a603448640f0442c00720341081200e1550482c00224684990010780091647e520f5050058805800100c012400180c08025140c00a2442a1110307840c03800307507078039580341d051072002c10031044031424130a00307800204211000035075440405260b4030704080d0b4455581d1200303c81038485803a07241c003018210210000901c00341d03104600381c410500e41d0020035586203903200c207008031104a00340d444826020003a41d80043c0c0c0c650a6005090510040c18001000d03486991041c1c15264180d0015440d50209409007000c80b056014122a03200314490b01001d601e0090001020b2001c40c290182c0082040c00000c0c1a00d9000380d8182811101c1b441603240150302a0f0304656545003d00402d04102c401c0000d000c50320914460240d00078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 147768120 1250 147766870 147766889
    0x602010e160e0408190201051b0723010906050c0d0501080d020303010620100e010b0103090308010902030907050612010305120304050307151b030e0601050901050a1403030706060e041103010501 85
    0x1c40c6480c403a00382c428009442500c4584041118403580207042c1c02031403c40000ea00085107520b0134403150a16006241c20380d840f000400c0001900003665513041150903104915a0b522034020700c8040d500400d01100001d2580385040140300383e04000d003000e807408c1400c02500f0b03c40c6030380b240741840e120302004464ad805a441400107001041c080d980c400e80f10045440041100014400317228613004800e0369041859a86422441d02c00c0d20a0054100741071342806c0c10710052941d580c0c020304864051003104081d5a011010820048080c407a01008090003007a6680f207000c400c2c0403003010002844206e07028425410980465840c4005582c811504000590704110040d25900f80f080955030140c010950b50b050b5446224914001c020543d446031b68000030031300a80c007082803a100c0183c12081c07160364030400410040c0d980f920040c00791440f44080d4204810080d0101f483d600501400030300807400c0c04400701b8681d100091281c407440c0105401e8820311861002d16003203e10078040d07603015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 147769370 1250 147768120 147768163
    0x20303040303050601170403080910050c0f0913060b030a15120803040606080f070f12120f02120f07050d0c0503030703090213020d0606110d0c03120f150602010e 71
    0x4603000f40e200640c842c1e0103040903e4055200f01170b0070000300007102c08034042002c51003030100d9010304200550741c4035070002003004581850711810826025000e1054900200015002e000e40c540310014001343e01525802c1c001039442d600b042000340c00031a055104540b0b0542c0c0b0304030b00312941000c0d80440380f000700a0fa030786056a0315561801e91009006445d0640c8500001550b00003c200c4d8810000c0c0c5280a030001c6420110310a250300500c2c2d1015106080707201800d004030340d42000030000c617030103810146142c0141da001682000d42200030700701d050402151195090720104014802d00e8810f80580341c0c134501c00c0c00305880c0c2041000c0301414a034000e0000070221070190744111091400100640c0c07031807401e005040260ba010402d040e4a1684031402080f4868003d07013503c18a808040140c41400c5041c20b00038141031050b10050704020041c524020300781000d51014045a540d030205000d03600c1e10800300c0602100e00d11401c0d00540c606013201d8102e00d401724800c2c02d54038400055420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 147770620 1250 147769370 147769373
    0x302090a0b04021201080d1b0218071404143c0a0306090501090605070c080a0315031a06150414090702030c030318060f04080a0c1119030c050f0102030304 68
    0x2042004101500107500300125113154803840c907058003c1003040c00a064010810700d00a0a5103c1c0c481003450384404424a00300594940309504546540074100000c80c4d96407407000c4a5000c40742241503448200003501040e018405101494141c4c0306440c0c02d400400308913008408201c41050700c10b8041c0981c48042003081411040030040c00000700001740c00303501c1f512000300721440c03400f040728240e5450036004208030441c06002e81c000440d007401200c8069644401c0c260703100340402c031000c00d55103003d440c60108881c50000082e54005e00c10b0300d0034903401e400a11070900255130f0b240c0705002c6541075114807052841140d064541b01881e80c0ca901c0801801c1c0004120003030f10300c50541c007091106001d031240800c003031071040010003060454203109001d140e09007400a010300074240341d04400c000c0410440e00465031803a105103020311080c91541020a6008800e00090b13078441c1034008070501088003d900c1c034060f280030709291540310341d0707642c20845040d101c42c9155025810a100180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 147771870 1250 147770620 147770641
    0x9140d06090302032a1615030c03180b07080f010f1406040905090d0801090b010503132f03060916061d0907050406080f01030c18060b040b0c0d050301030209 69
    0x1540760700c640101da041c920004a50358051491040e0b5820b08909038070b18101e094410401c64039000070030007200100c0c03420b114040900b50014007074003060544070507000e041c02d4440d41c420203003940340000036424035100e0300d03094803550340c02c0d070380c2100007084040442e8900d030301000c0c014100c0e00c03401050355000b0301e8420010422402c2c041c4c507079444981403100054500007400759520821000001e0103588900380005806100c1c103800641d01c60b0318055540038644d0304001101e0b00a0000110307410549082e2800e452410b003507060507000040c4003054001d003070400409040301c041c0100c0c29224980c3d134902c2003da4401c0042c0b889400d0050b0030784104032840c003490381c50301c400100401c0c0c035614004078800300340b800e03d00382c4615001401c00201013100b141e11900b02d6422441d04001e100080d45161100000c0369001c0c0502c0c2580000c11140c0030002015a004d05c008040810a031504c039662084156081e4101400946050103038450b02130b090380c402c20490741030341d0740184019001e41b5800a001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 147773120 1250 147771870 147771881
    0xe06030601110f0f030403050607030b0d0b060f030a0507050102150402090708070207030c03081201060e030a110d02040906050106230f0d02040b1804110a0e0f0609180709140d06 78
    0xd040328041e40303190107800030060096144e04401840110341e15455440c10616200700181071401301880d10180d92a5507450300c841401c1c19410107284100b85c2c84190003d404d03001542d2040350b01d407260040c10313010001c010810000300c0c2e000b6000e81301002800d44c1041111641124029840081c24000030012400b81d00c481e60003c1040c0704640c0c0c01038590703940412884481c0c1080e50341d4000802e0204c4e0355201005014050121072a01c98002014074000c80d41d104003400005006040782e00b141c051030740741c00d080b070610b1580040c02448410351031700307104004110a015440003d40b102041c2e14074130387c450300248504e290541c1d0300f602d0007101c00405601c503000520020701080d005c000001e26000c854001c0c044e00a26101260128001801040103c0780916040590900d040c40140320140e00070182e1a444401602d007c01d0415881c0c00061151141c00d00095011202820000001242c8444103100e40d0340c613190b030030030207403180e4421902005408180d51f000c040011908001038403504030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 147774370 1250 147773120 147773147
    0x10f021c030b0904060501030506060a03050c010f121503050f030702131e020a110c150702090c07020409080a02062202010516120f030b040606020c1c061d0c010e06030601 75
    0xd99102ca0000066004a05031802c1e1403240e1a1001403091110520925030400c104a07185a1110700d1613031040d840d810440041418411880501012240191450b210803042c9060410060300344948113001d503541030006407003600c150600c02126180c008100c640d02a0000d200700300d401d90940c0c00101400c8600c08401e4200085401e103d01020140050280710440c0d4540f4041c0c017141d80c2c1014a0121410382c0ca5128400170f81040381490034a1085032002601600e1039400c5542d85072070070100780709110f002900203207081d900c2014006a000580603440465083c0d0320107807a8041e10350f900e007280141c11180310050402c9040158052001004000e01000101200300b141c2d441d565101100d04150030302003110039208a04880e454411160f11400c221010051181404402503030761804800a03400385c101184e030440000152410200010350203d41445840503500900c1c040000703501044202d8411500f80210541c0568500040313003001505450440c0ea0b90340045a419044010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 147775620 1250 147774370 147774377
    0xf07031a1905130303051f06031104030510150e0402030606040519090302071404060b030a0902060705031804050f07081f051903020a0605030c0304080901051210090b010f021c 77
    0xa94403401c4509000d40382c802c1c240907203041d004055506001d800e40304020641c0c07c0341d5808400d81c0000105250300342c4251b544d00c0c5400100c0e031495101c9a6003d00c5250401fa2062080007410340f41d007905600b20101910030841301964003aaa00e0007035040000c00d680081d0300d0341040c2e00085080c14240d00c1513603c1200c4c12840300420701542140011990043e070305900503002024103002c6908110b540d1080940182c0c0d00300301d9940f030449c4100b0385020141c8002c0070300e13440d80445400d41d55101c041d610001e0704102680e6032005242218591190144000350145041130001015142d4244800384038801039200d42641341c0d40d82000561200c1002110300800c5a030240205a030b0301c1c2d1555041130141281c03260781000b81140100461114142d004c81c0c10040200300300f020501300c0405480e04607a021202030780700c1c031046006071818000c02d040400418168010059814070388030304001150b030052010010362403620700450708081084903010260703000c4100e51340e03604004d001c00d540c0460b03d8034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 147776870 1250 147775620 147775651
    0x30907030c06140f032211091302090402120f030406050301091506051206060d0c12050a0c0c1209170313080d0518130c0810120c06080703060806011203020f07031a 72
    0xd0a01041d00803e142c1581e408211f581240041c0c00e0032a946d40e00118154030850780c81c402ca900040718448001d000030701415000001c140a0f103010440d211000d40080f058035213807a15210010150b40091061108540c202802246c89041000c40801510b8441c0d81d024640035199030255286840a030619030405000c200c0c804554000303108a06000b009543c0d0303100d9100300c006c89001070354000f600302c80d05207240880f038105044c7c10403e4820030950102240d05080600c1700182c80b0920103501944001180c882c4100f001c0314007000610310048504031070000e941e02e4848203a40c444090380b2900206d40d08111205008044611520801c10000c084403400c449203016082a1840d4214400108925005104045910600c1380d006003024141c55101d9a5582c1c0b1102001d0846100358018000400041102684603410001c081c120360740855078196900d03420301d640000007641c1540140a50744403002440808500301003202c0d00050132604142e030305006158a90006006614002c4900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 147778120 1250 147776870 147776911
    0xf05090a050418110402041412150403080906100305060a1a03030406020618030a090603020c03070f0b0a110408030a1809090309030b0a090b07180308030907030c06140f03 75
    0x501840f42158520881000d80d4030052400d84404048034651a105078014002480f078425070301402c40441400b10780440d043c0ca1103134500e50914884862851500180d441000305154204050706d000f801e6000854803d60780d0540c1017640c0c6400750000500a411620101d240710000381c228aa465021900300110542110f0001f49554041d0b80f140015801c00e60401036142840d0f50404180d0031210040c40c48c001d101100101141401c0c00b0b2001815404a030f00490301c1d034200706884403681e02980041c82c0e203205080c03464070b9450803200c1401050410100d00c92041441c0203a034201d803d102c005500748000503409541e102c030303040a084a80d254400c070014400c50140110004140280c0310388807401d046041400840302c008254000c035509119841c40020b2120000300e07400803035860185100742001c5281c0004070340c113910141c0740840c0401800060701010034800c04036846450200d0409545500907286441d4150003410740002c28003102c4100260000210350241507a200245140c060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 147779370 1250 147778120 147778129
    0xc070c09020a1101050f010e070203040905100e01150e010302070c09020d09120c03020a14030c100c090906030302300a0206060a0f0513090c09050c0702130621060b060316020607050a0f05090a05 85
    0x855501000349050fc0d0104000940000c1640c0035060540d096902490a840050b040b00d0b4035002441c1050390001e0b0741020700c10303003031024000b80c6401c01c0d087d5032312416082c00501910401c001592035000441c1d5540201380145800b504286c0e154028000c02d01203903c81c441103403240d0f01703001910f000c00c0110800c40074041c0820240c2c01d5414000103040401720500800d0300b80c1d550400d1100e14036140b41440843d4000803105040394050072100c05000d58001403401c0046403070041040c024021590141d4aa00891294420328094402c52810ba41d1459090101c0300b403440303607603000090b140140d2178045242c0c116600e80c074010b80d000d900c0039903115800022100100d0380b801d06010089004411890038001c9001c0100042105005542c02d20780c510500c0d00b4500840d04d280e0070440d0b004000c111a82e00090700010000f00020b480e4600b11200003034803c20b002c02c44005020702c5000480b0305015a00340c0302d01e400265506081c03815000b100b5100c951003640303510360181c22a48001044e984 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 147780620 1250 147779370 147779381
    0x1a0d1e060c0c050705010c17090316060233070c05070f030305090306160210020904060509010306140c07050a14011d0f07081f050c070c09020a1101050f010e0702030409 74
    0x307a03642d580a20240d02d0412604000c1650443e0341003144681203040801d41180c1d149007402a500007003543c0d41501400249000728001001c84420300c66a000184160042a603490b100f1410b01901d030100e9414048800410107882a00e40c11f0424001060b4494032070b514018906108904440f0956242c0c54031b413031852050341c011000a50009140703006400d051098a400514180307202d80511400c90700030351258011050000110b0380801c1c41d007850b80e5650080b00007030001401c25002941c490520502410b6854481c40f9058046030205041c0503028044442c419001000303461604110307910302e041034258116000b480d64860900784c454680e030031b0080e0914200c039402010040e0230f500b02d841c10310746643c0c48004250002200d81d009002130f0144204403403440500080c03182d46501c0c580c02e4030b0181600203004803400f03441c041000009a80140f2a0b9099510380d10b05a03601c00e92154243d8004594a04440755190010070203d1150003030150484440c1c010f91741410f0721a54024120ba1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 147781870 1250 147780620 147780641
    0x30b1b040f03030e0306040201020705010f0c060204090c030b060f180a15020f010b0a05090f1b0f0c0105010e010612050a0e030f1e070302150709120b09011a0d1e06 72
    0x12801d5004008050708a800360b180c031070b0254090300d00d1380307015000030351200c6062140f00c0c1071002002c0c054002502ca9800d807100349610407011500c0316100c509410051000000740c50202c5c0c83c0c042004c103149442015584020842c10f612842e01e41c0040303074a064030305e8100310a90090100b80001c43c1450214140181da82c009500815144810358002400e482c2880601030082011010510803922880e403440c0d4001e9001000c0a010f4480e4410110074034503070461001a040041403002041c11190024848101004000c1c0110398803a080280ca40c0000e01c00d60340030410b1500310083c075036103c0d003105601076108600061400003a00380541180d000c0956210607007000506401c0b03044109810b18008041003a045041c007940b954082d5440580101da07880c015005400540324510500041e0050604141082801e012a19281100990070b8407020541e501713008292024001d10404100c11310001031001ca000d80c0c07143c03506c50001022070300082506c80c16400c0759001c660280915900d02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 147783120 1250 147781870 147781889
    0x9020a0906060518040204050f0103110c07030812090102090603070c1a0c0d050c04140127171504150b0307120b040c0816171e0714041104030b1b04 65
    0x41403c24911343c0d00403420701c040c070311981c414801402203403150300d0021003000d003e003400a402140a110482d03e80500d00c888c144501c280d51011040140300c4000d4241c4400011210f42c3c41d4483c2c0580fa0700340e000c0c2d0b00001d5006035040c0009015107200345141081e060188110700e030003602c182550310441208a079529034402001450181c58980c501c0384541c045598803c0f41e0805003040305001d000b40d40d0813010703810095258003850401040e01c002d4803581700049410904140e40b00c103003600c0d00107200b80005060080c00303c108003c054103201f0b01d100b2079002c02032032442d40c582000ca5008190f00400d0070341520a0361404204100d0103034031519801d0242440d290b00c0c2c5000c1ca0031418044544d0072401d00d54010691883d0300803844035104003542c07008080b405159116406c6180740c1141c43d5100804150601820040243c0110307402080e20b40e440c80c4012280c440f5001d000603107078002e00124600008020030408180042c900c2d40d04602901040c12860280c10102070851b0040c0c0c0051000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 147784370 1250 147783120 147783127
    0xf031920120307120e06040201050f0f0a02011406010c050d030213080703050a0c120c0b030604020d05101a040803040e0a0207210206012c0405011104120510020c060a09020a09060605 80
    0x21560000480385000100da0b81c1407145c0c8148109490b250440600001d05005c40490040301d8080d80340c00703076845101003054440d210a9030030340080c0600110413980c09800d20000101d62035502ca9445078000300d4200340140707480440442e0440095000d40035103c035412601c04081030f06401403152a00540c0600001d0841954078180b24043e00c0e111b50280c07c285120313250100004100c11004c40854000d4800c0396141d0b5078442c04240684500c00c0721202552801c1e042010021502e1030f110107907040401c0c6818140d000e5a0307011110f10032402003814039030040c002040609810f503034059204606440150800c00940e880800045007004111070000c8001c3d02544003075410401640180f40711020b100302000380c000c070541d0340035188140c286942d801c07000060a1010035000106504141e8071500e83e070796a0b03640d03041240800250200d44a0150012021070f050082c000e94000300c006030098120b580b500079605000300740d001822030304903502600000c3e1603441480303024001c120170740301d190b030303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 147785620 1250 147784370 147784381
    0x6140f040f08130b0403200307030809060708030106030e0c0103020f091c02060f040311040b060d090611040b120105031b09070c15020301050f030a0b0604150b0f09030f0319201203 79
    0x403019400003500d442901c0451041c01c4507034000649c10101c90700b16814564070300050000c14000d105102c0007800c007800000c00024000d616500c845001000c5c0c505070349400c4008001101030744030b611520801c0700014000303840c0901e440712511000490300400a80403000039404100c00d07400c840080019928013107003c005002c440070281000c0c00003100c04001c20301c010400654a800703017241403031401c0c1d078504800c0308204c41503011400416070400030a48880d80c2d0201e11140780e00c004200c81e010360040000003030302c3c10002454080708203148a0f9800708680c22042c4003040000a1019041001210308400030510240480710004144040075030303250f06040910020500c0311950a0080c1e109401100100312010010360700840101c90114030703802d0b1200d04101f64011074000c1002d2000c00911388031006070100042050480940503500c0c11050000d440b5200c0c010340240d00701042d820721480f0503ca2003490001c0c04828000c1c1d903200803802042c0d0580c54081070400d0045050340000070302a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 147786870 1250 147785620 147785633
    0x18010e1009140105100308031f09060501030b0105040f1e1e060e0d02090f09010906141005151c09150515060705150c0f0a0206010306140f040f08130b0403 68
    0xb02e8161580000303201d0b80c1048401d21900c1c410303d21000d0940440880401c0c0070b0866103501c2c141441020340e110202c1c42d01c070010600141131030720030180400d18050b01c401d095402202920200c40c0f07266040d40d04140b5040b184010300f11400b40b2408181c0f842500070810900722903000682e504202a0050072600b00400603060003140c0c0c00691141c109004c14900507542d441120b5440310b41ba40b911241a107809503103031701400c1b000000511442c01c0134411494003030540703000c6109960f1000060314540c1e8620030b1040700d1060410190800304100140c000c000b0100700706c0e040c82107088000261050003922004c56a030f40c126202220706480d1000e011030310468440000103c2c004a5050780313800a55510300d503650740c04521003400c07103460f140014102c14010f0240c81e4800d030504a070503600d21b50158001c1d110f890034041121142d2070312a4605c50800c840014a2045c420001c2c90742c4961145c2d11801000051184111442034082240a4003200f101d0513040040c050001a40d0301c407400c618011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 147788120 1250 147786870 147786893
    0xc03030f0c0d0c050c040b120d0201020d050c0703050a050304050c0a080a2a090b0a12030503090f010603020a050103020702040605100903020306060d0b181c0906030e0c030618010e1009 81
    0x18802c0080090121004c654041002c0500b00d000300c0d800030740440d000005c61204028420403001a000e1000c82000141e010340082c40f405400400400c41c540d00c52100e6549402820005400a074040c0b243c00d00c500c1c0a0303001150020701480455100e918040001805044140c12202c00b58110b0148201084a1203903040c4544140c60203842d81503a0914491012003030720300c81c001d0410707203440040f46140c540d110304601074000b0401100108415090103000c541c400d4a14890521604510390354801c0e040c4110740a40780c2c001c1039840040c0ca451700440103900602403c2e0781c4150b135035000140c81d0381d41c1e040500340c000282e222601100d02d140109814141d000b0301d07030f5002d0150500581e00158a440f8481d40c81000d030700f014000c10300600003180c07414000750401c4915080742d20f0701d024001d0f000071208044402c5542c060041802141ca240d4a540d800007020750940d1100000c03071102c1b400e020408600703c182900004240e40181201b528001154019054079907440c4c44101c00e110900c1d0a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 147789370 1250 147788120 147788143
    0x423030a050d0e0114060d020d06020703030605090718171629070f0210020f07030c0e160e04110f0706050a11070c1418040b072c0f030c03030f0c 64
    0xc02c6040050664605d0070200142000d200e00b150701c4080085541d421240544035400850840d12101149070140090078503005051040b48150300181c0c00034441c04032900d50180b20350460402c1342c9080d140c000440c40d84c1ca8280d15500801c841c0b0741100c0c81c1034075410002c204425405030034099500e42081c2d0342550584000540b80100150800f041c0980c25081850f941507405410000d81000d08904000c10b103a010041401510000014045540114829981d110405030301c0d94603401220754002c0b4054842c44045128440b003181a07141030350006400002c5510748602d82406060780c0200c6500488045031041d41d00c0d42445050111403080c500150b24440180d40f503c00c2c55180c14400d081c0c0c0d48601c04207104020380d60341c60b42e10b80c07005a4890541d00b19081c40e042c24a032410340c1090385d048030ba03400002c0c000c0d40d142c2d03a280710000b0705e80d0810f000300b942c003512104140d00303005803052010092905449800700081c890344080006003420b21403064850317210401c20134481c0c2004080c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 147790620 1250 147789370 147789373
    0x6121d0d12051f05090604062303070501030504020f0d03140408070807090c141e03070509040f0c170606070c12060c05030105061b010912021e060c030423030a050d0e 73
    0x303210036007146180300c04003038400c01c80c0c5d00c10f070030755a0500041c05440c2540002000e649041104214030304801d500001c1140210142c42c205912a8011811100101e40103940030340450035021650402c002c60710183d0307000786842008800750304524007666029920202c01544080341c2007103100703002d100e1000640781c0b852050107100d80d14030340200b4109100034255000c180015200c1400001c142c0030b603c0c040480c3e0300487d101d1501d0800580b607500810644e50150b8100b0b0740c0c805075104240300e070b04a607041d02d86032001284484403031200101001040c0581240c0308008207130100742049a000020503002002c2040303550907180c03041c01da0b46c141d0044018440140700600842d611481511541070745d14000c00b20035040c0240e41da0140920f101e020301070f0328058401d4864554003144054107411044607011804112140d81a500c0504541c04400044140b002c0350009603003482e8958903444400d603171661000c401e40840c1c25036110688682c049400040c1007412101d0070301591920240071030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 147791870 1250 147790620 147790651
    0x6131802120d0804120c02033f0f090d140a02240a0c021807020102031f05030d05160525061b021003092a0b0406121d0d1205 55
    0x1000780030b09801510042001400a00406045d07100701c0600d9a000d4004044921014080d0220b02c5101c50340610f140d070092400000c030715110308000050101303022070f1840d20306d06154225018100d80003581003951050038165140c021520b2001c0c0b0039022141c000203049501494030400a00f03c410300d07541c003c02000d400004a5004410b001e40d4040700751400c003291020500d00c002841d060400d910b100765503020f0301c1402640d5605501851255209050642d502c2c5020740070300b0b8045481d4481c6680c16808051003a4003e0f10039401340003c446507045441022481e40d80d240d0070041e8034107002c120f6402d41c0941060050006107220000c218a081c020392003070b2100ca0f4041c0f07291034420080d00828082c6d00e881c1d6451321aa0250840130340104260031a010f031701a90400c41404d290844a107082d24400100e00007220400301e0341152410b4031609942c4142c80d000d100580040140c3c08812180481d4450b250303c414800305540e0380442e0383d4221000c01a020348000c80e00c0c040d0520081c1014103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 147793120 1250 147791870 147791893
    0x2010c080708220f030e030708010b030a15060f032001050301260321150402090a1a0906070303090201030f110a0c11041b03180f02090613180212 64
    0xc035038690042c1521402103038010183d02000e005900c01c84000300340400c0d480d080c4080c194805e49a42c080c80c4210261030020360780e51300310f0b8281e5a15100071581504030743c10725000035043c0c400c00c0c03802070783c03003400416100d94454488081c102039500650f003c0818444140c80f152103420000c2200600342042420b5504005561020403800d00d801d148008003c0110000310a041003a02d2501d001c03040c001070380004090b01803000c1c2c402660040314210420465504600d064000c1e900414001750103011020325020b4540103540d030702804010b007440f04000740069520344000a001080c000d0310041b41c0417100784001011034021103600c58000307107841d407d07840726500d0308201c9840e07a50768642004d003074605050804050880200701d90307000d4a448090354030042c2e0001034001ca1034007920100098443c1c03050802c1000c07030006000303104244d445034000042c40c11600359508140003071701030342d6105031401d104002c940c903c001070300c94065458212000c514105105e00804100310b4050074030715910 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 147794370 1250 147793120 147793127
    0xe1b030402010507030309060221180c0904061112060f0306090c060913050403021c05040b030105130b03070f0906080a05120318060109091a16050c070b0d0c02010c0807 74
    0x2400003410050300113038040506100360001140079400600c21941c4e45130502000d0318210021881203c6c929218000070040041480032150541c1e004010700b034503580d4a010070a034502c00500c07c035a01690b0380c0c81d801080d614003014081802c40b84907070864074106981000700e42807180e05128825440320040102c80900850715407a41c600545815444113032110001c0c080101d01880f8480540c903200800c02450303800030754190136aa241031003841503504010110369510943c007410195110400040041c1d0600388114150461001d8002a000c0300313080019003044402d40c8215514000044280092581c3e841080e0040c100d4600a041020481e61403d4035044008000205464088005190641507501100310704180b00300399001c540e100d4031688020200f01500381c5041554a03030041c0d0a83c6e060802a00400d40c4800c0c1c60141d034007800781180ca070b5103c0401e207140c1d401001c0c2c000404a0240020706020401d0700008100000c400c500203007120041c221100030400c4150038040540e41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 147795620 1250 147794370 147794377
    0x90b0703020d200109110924010807092412060e0105040203040c050909030a03050f040b040f060f020a02100b0d02060d0c140c01020711030610060810050301060803040e1b 75
    0x102c0307041c190680c01000c3c100640511494401080303950918202d0b0040089030f0703651106c1070f8811200483c06440f000c429400c48442d508564884d403540d03100d04405036002d6100c1950040e041d14101103141e45488101201941a035110156002551050070150387c002003031003a0b985024408220f00c030b2602020102814040c4141c6000b1a070000106080c071041c1302414018080107000d80c1c15074104140c60300e0350796000c2044000082d25003004103018800700030340c40307014542001044c0c2054455498980c0c2a000480e01200c8441d0744000d4003480902c90300140c00c4044040d006804415600e030716138400d0710b64030003a8a00c103141400d0380e03600503030340c07a02595100c0200c0f95000a04102c190001d58144d4001000c41c1c41c00d8102161a0340d6080054005010f0f161185d2202025161001c050640e81d82058414824012100300c0078800180700e0f8204590010182800205250703503040441d0031103140703812481c4243c000140c01d1109190719075840e42c00c418040000740c070060406203103480500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 147796870 1250 147795620 147795643
    0x1090b1305121608030318010b100f0c060507050c060c0c06010b07050f010203011202030c0301050603190302070b0a08040b01060804020102031801121e060602030f0a080903040801060e010501090b070302 89
    0x92100b055150419040286509003849100140031031510f800c109070ba40d820031580c1ca181e00940c054461005101802220905480030703101124040c050802030f0f441c5c6201019403004c0040380800007000c180280206801000a82c45060740c43e20350b441d0f0241082c0000303189044445c0c041000003407a4400140340d504442421901c0e6441c3c5445250181c20410343e1058010550f00201c00400c102040c00000d582c404c0c800c0701190014112102403600344c85081360003a074942c10007555118905449041240e40d24841d2040d80d0496454807480392964100c481d0407000651210300300010081e9090106000d051a030034810418a01980001d569102c0e250a105030180135224002c002d9000b2806522803060300b640038004c2c2001c0c07441c0c035049100616900d0381c3c0a0704241c40011840c0c0048125000030381d02c2810355150010000c000e1304c1111003c0d0403004c40388001c01000500020a01c160070141505003a07400903035140000051401c0c520340c20411290300b0130050720300042d40015032640e509 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 147798120 1250 147796870 147796879
    0x10c2a0c0303050306011115040b0403020307080c01021c050601020d030b1504090b010f171906080a03020a0302010507050f07021903120306051008090d030c030e120c060a0e10020903011104031101090b1305 90
    0x252f665103003c9045008194009100b0310b00850710540070310064001d0541e004540d100042d840d002e1071928010b482d4141c0f8150b025821020012490a100760820300b04410080c12000a550350030714140c52550165104030091562a00280745d950781c8940d030542d0741400d40c90070404070440300001a91100d0003420103200c01083d00304450b102403864004900a0210300306441062815040c065103841c127070001200154607040004480d0350117181035038403452100944604105040d030a103c030700d00c00c0b0300307402c4001e541c070080001c00606800b685032228011035801041d00e030310307000c248016001041040400d101c803d4041000414000030340e0100401301f8640400c1d00042900c1c19001080c10b405200050b000b0200f030049058800c800502854070a0130440384145d5982c000001111503002d1401000c1d006920107a040c0391040c0c01030201400002c2c00020407441c40070017180180c0c01a0f000700c61401141800a01a6030003210303040c024601d11620070f2900e61b29209003c94100d00e401440e124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 147799370 1250 147798120 147798143
    0x60c02041508061602070609030305090607060507050c01062106050601031119171302010c030905210d0c12180b1b0708010c2a0c030305030601111504 66
    0x6554841d042200401d01c003905026203075031250002d40d1512402c035009952105a0030070444094400201a1308644945d179905803841e045540c2103c1c01d500c1301c0a8568014810302400d0080303900c51007014041c0170f05031030365035039076030808050750940d8010340c0000040c0f035008064110107209a40040c1a6641c81031001490b50b0315a001a8000c210001c4400003404000c5010942c41c00007145191850215444048403e90b80c111009881d2404031001c6c044d00740c0301c540420040d401000030f0320b0320a1280c00c081c125a40c4803030210315190405425400c0d02e4001c00c4503400c0e500024000d40881d40304900d880c4c0301440310b503100c400c010a01100054100310030040384200d0481030042400203030801c0e45400c4c0d569000d004042020407000800300800d4021800001241003051103490111141b0f0344074091152114200301c01b501c040d50644003400d00c0f076001355030001482d100000000d14130075102d01e43c80342044000180341da1440b1120004035031103001813500341c03440c00e49240e0344aa4080d001444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 147800620 1250 147799370 147799373
    0x4030f0305041a010902130f150c081209071a161101030204090f020d14190b0d050d11060a060b0f0c010b030a0f0209070f0503070311041d100503010603030504060c 72
    0x8000440342001c007a58003d034400811003158603001460b004001c41e0016680740c1d119000c3c4c2c0d400700c8481c07040100d041d2041082c0b00c515405040f603464114002c2d400c0341c0c103003002c001d04084111001c950f16101a08000c4041c440400072805894510794807481c418140381401161580380043d11b040a080c1c000d40080d040c000340c2c0309404440103805400300c1800504403101e460070103504000301641809052207031502d40303c18119515441050900c9181c1ca41201e0812440c0091070f001d2880c0d504102e4030200381001c41c108204032440310070303156101480214107015041c101340025058094250400000b000000725540589881d0160315010569408011000d98010601145010380500030307003d40c5014172005105a1101c1d078000d66074218140e1706c10300d084a24035401010b00001c66002d1002c90603071480b80c0e000c2e0300580440d00d5003600d03240e1110303032314648a2224141c07507042c28181010090404203039404407000748010750003404a1411a6400b40407802240a100100700703000392500c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 147801870 1250 147800620 147800633
    0x709080a15150303090312020606060d05090705090705120c03010b04060e03010b0a080f07080c090103030809070320031608031e040e0f1806010807050d06060306060b19030504030f030504 82
    0x149100c8400c102607250b580d01d10740507101d10110320003a1500160000039880d41c90010071128468034004110b40e01d080d190102000041102904140403446603100100d45500c9104000303018908035200d05450384451490f402c0d00e20707801000200542c1d020301c01044090708080c165029035030030b4103001003400500000300c0c7c014050102542d03807084c1170410010b480c2101282d440e140084c0c000956401a403100203541c2c0da120613030301c0c040d00201482e0040010a215002641d0052060300980b4030340c0341c0e00e440d1710070080c01c3c001070141c03801c8400741107842c146401c000d144820003022048182040c9030400c21516402060000d00b0711102c06440110b605a80e502220050000507003a60442d040003c4005891641100e400c410a100c80b81d15401c00c10000071602d041700c500b070000700f110608000501040686156080319016100c100110001d2980c0c000c05d005490030b0032144e40c44807102a240f800e81c1212500c0c039014540340105100100342c0c00424001c3d00b882500780404c2c251a18074005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 147803120 1250 147801870 147801881
    0x3100c080117011506030207030813020d02040f0212100906050f090a021e0d022106090103060c0525020901060f08060108070c02092a0a020a020f030109021011060709080a15 76
    0x102c131560038030085803654040d4003030b0151038085e646484407035840c41000d030461303103901300c020754003250030ad01a00051920303400c21a4002d54401c0e0242c10041400107007400414140c0c3e00501d5190000d105001c034501d18460f00d0001e25040362080301444407240441c01640014000c3d240c4140c001880810410114480f0066041403112290340e07900c225201300000d4103e61540070307a104500403504603900c07103102042c0c010b0364004c041e0100d59103190303a032000034117440380b1805c284682030251035031149100d01c0c4040c42c500c121501d556884164410000f80c01d405820000500126215481100e03074070843e1103074049802e00b41115181c40d02101034130080f80e08800250f0002c004010004034000001004a180c1d0a898142c4641900c00c0040c0c0304501a1204000c01640700040340ea0240c41d00e83d9200c841c4500140000500f00050b4020a4079800684010070200b03454551900c0030000410281e035010b115803038030040c00350410550a8a552200f140034081042001d982603003081503070b121 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 147804370 1250 147803120 147803141
    0x3090308040b0a08060a2102040f060801021206040c0f0e0109030204050c0a0818100b0a0b07050d0e041b08040203010e06090c01020c0a0f0b0c010e06040b0603100c08011701 76
    0x11645480e030b01d90090041d80d00003c014800254a2030205083d4104603845a0540f406283c4c10014501280410815054155026680701e511010301703081d034407090b1241402808242002585e07400f08001c0503908a20054101406a85440503030155154064074410b4600c40c507140000004144400407203852030700c2c3e0400703540140341c0406d0bc031011044074010108125a0b4558600d80e540d041d9901407a0300c02d0110311022900218401a0600c6e013550000500d4a002440001d80c15102c0a4080580d0412002140c2c1540410103050303046410683c1c081d0444011601230000c031441032201454121500c50307842c1444003910101d0215942034101594880c4900116841460400c0071196904030034901c1c240507008000e09034070b032820540448419a074000203009601c0e40340051130312203684410074600580d582c91075120305807442845210f01807405131080b80b840d410944100360900c0c900502da0700c6503500c0c101c041451035030008111411180d04400101c501801140050f0141c10700c0700c0c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 147805620 1250 147804370 147804383
    0x30206030406060915230112020f13030305030709091a010c030c1a100e0903040b07031101140a0f050403020c090703181401110c06011e03050105040b09190213020304030903 76
    0x652004000d180d42442040396140d80202041c0301994840103150342481b5052030000d5038411800d20495401d40050145800700a8002d142c107030200202c60b6421115002240000d00c000240418140c1c0aa4850040c00d4084402c0101a04c40360b40448500d500d8038100d41800303109005403007490b0054090440329900800218464003401802e4828600229683d810400c440007000c101d40f01c2c918004da1060846c000114981400c007000022142c014600072000c110000c000209201400e006410750850340050201203401c00304441070642e00c0b080716260501c0d00d00010000400c8e070004031690300130002d40b005031442d110948110080c0120109001d0381c0607410340b000341001070141c0070944c040c5010740200000d40010034032104920804140880070790081005000f15450300c8403000004658100181c0c1c1107540790348060130340300304981c15a218801d04040100c03200040c40300440c2d188990940094002055000403052800b106900e1100b43c4d01000190805000c2c0705090b014503004817 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 147806870 1250 147805620 147805631
    0x61e060d02120105100605070201020303180703020d03050306010f0c021c1103070f0806060d0b0f06010507060612060e070f030b0a0b0a180e1c0f021f0e010b0303090a0302060304060609 81
    0x110841e0113050161203540021301700220018505209a041e2106254140e000d5465a01c80c600780010115440004014501603100e0010040e6101925895681d100781c0701d15440e45031030000901608803401c0c001d0107101100c040080140c0d221030b40c04003c0191070360114031501c0d40d0f0030115480502204565018440c01d6004102603680e400003600b202e00040484280b03030f440006200f205111808010110507580307020840b420030704c9e048140e12031070614005081020540b220010b85415501c80c89044101441c2d8200b4000d440c0030700300c29009404020800c1c1450102010119540781c480a0410310200c40801d000c50210740101e000860028501105e054840311220300540c01001035400140c64824490340c0c14402041e42001d41c400c2e8a02042ca00c600780c87e007034503003445206000d0111b008001100c00c0040c14507203040f001c03940107040043ca10641c06040c0b03003141c0001d903503a1320a03403040c0050180c0c0d40d0740c500e405040d6541071b00c1154480d2140d01d0580080d050f540c2000120740e0528 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 147808120 1250 147806870 147806899
    0x406080304030c0b12190b030703030f020d0f02030d0e030405030109050606091003050304150509030106060503160e09010603090c09180b070509090705090f030a06020406020609061e060d02 83
    0x40c200740c2e4054407206210541d00c07280c1d240507104401058801a841034000f82d5038000f1030740d40600b0402d59480214405650500203810200180c0045010480b01078070701030225810402a5034512540c1090100085541c2c00070703650340110051000016250395049403401414020768004006c090300074003041c1c00038505107445000c01c0b910302d030198410200042c450520300c1c0c41c02085a8005029500d8641480940c3c0c0102c0c00d1104c9007000d1140803c031203082c64400344180001411143d54031030310f03810241c4a1510707200e120b920000800012000444690350b0b41444581110060704000510309054909081c600102e40e004040308c0e031400700d4100c9c00206001031501514030500c51100c1da5074984906581502824500c01c0c1c211652074002090300b0f02640c01486040401482c0407040304010001a00c1c0c503e030b40d4012a105a004502004107036010450103410055403005049603240c0701c50018400c0c10080c1a120913802d001e004520300e611000c815500858014185d00c0e800542da = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147809370 1250 147808120 147808123
    0x31603060606030c02071202040203060d080a031a0a051e04060e070207080d1d0f0a05100e0a1403100903030f1a010f03020a14130b030405210a0c120905040608 70
    0x541c850b00b804681882c0d400d581c19480402c3d0941910f049900c0e188481895400b480021b4000810058202100c03040c0c030000f1500b840e0143c140642c403542e01044001c0307031840310009000000301050240d90b0313980082c0311903940c40340a440041c134129643c01903202d03400000f4000e0300303807076021914a05408040c0802c0c180d0104071071082e00e10103004ca41c2c4640c15550704075900c140091910040c02c0500f080a007882c60500c4240103044001800030060300e44840000c1c0541000101e40b2010030561807207441e0b14100b2000f42801084070341c8802403001140004684c40340d035501880f4003e0743e40c9092490400d4045e81c06035101c2001024101300241a8200c0c0c0c222001941a00c180807409103c07000d02041e119008031418041e0542c0c95002540764441c0d07030a41d0341c112002082c44411170031004110000701030042c51140d801b0720000c01006280401c0301003419216004a1079100042101e03501c1035401c039561925203944001800d11404415900315110101d54010950090601c280021041e40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 147810620 1250 147809370 147809381
    0x306020c01090210320406030b044d03040f0510090f02130509031b071203091505030103020f06210403030e10050105150307051b0106141002071403160306 68
    0x45034178807080781c8410900e140164400300702150320407120030003003404068440d4000c2c140100c0007074004940003144036070b40c07030210080c4030004651440c4800c1d0300c2d0301c1c07450b1661a0b0201c028600341d0100ea0f80f802015501072840f0040010304400101c03400842080420860510340d844045001c201d15003ca1410080c0700c040310005074402e41003090310226038a003070b2290500551443c0d000318034000c400345286540c1c204402c0c2182c4a4020f1060006070106d851110540c502d102c1d40d0b03201000c0341400b03902c43c0080301500c070780010400c0500c018030058444841a42c4a5102210342e684c03a20391390340c031541c2001c05c20244002c40008207400c2c0400c15130142c0100114109c950165408031011481c0b04040b114244901d0f07600c08c41c94410700007600f94170001075403c08414a8120310706a8a00d40b26200145170340f00c0e0f001c07603030740d148410001d50300300c2030300c1110585085409424601030410020741e1200180107900b41d44159410b85103d680c1d0400002c0f107032119040700380c0c14250f66400c0040080a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 147811870 1250 147810620 147810647
    0x80a05070213090b06010809011503021c14030304021c05060f042108090106080a02010e090a2a0f0318240c0c050c030c03070e09032110060306050a0306020c01090210 73
    0x404050212348800411701070f030014601d0940c0802c07c40388c03442c4c08101490000e2004100030500148000c40410748950600401103544c1c2d000b10707a2800c061050181c9040070124406c501610f21107160001040441c0581e00000301300000d2005480d54102506050141e051001c489595041c80f032171000c2e04902c03800d03c0b81880200030041d0316503543d034150b07e504500d407000340010200c3c02ca000c81c0385002d014041c2c001800e050001900f004039107414115580c5a88098000310300659001a0958050f1045000101c7d9103824415466010f0b02c0000c5030660803001462a0b07880070801c0b00c1010034551880f45404d9507401072002c11640300028004283d902001c0c1e58500030444c9a400d5070600040d860b003043c0c1c3c0038008003d03c5182892428034141c01500f805020300041012111184010304034504113551051081080c2c10700d810b10090686c159071115061504001c420481c5650342d0481c0b0f811a500031402590741d61141e114140108200070009502c4103280901900700780c2c3c802903010060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 147813120 1250 147811870 147811877
    0xb03100f0504022d060f0d060b040e07021203010b0c120a03020d0e0c1f090f09021207020a05120a050702040e03030f130506010303111006090c1b080a05070213090b0601 74
    0x1201c1c20310104d00060b4001041e80b030300700607003911001c4a05000c4000c081840c08210511b04010f445603040c0181e41c659030201045180125017404048500b5010a03080103580c00180480fa103042e4808000d40014411b0398201da00c04154400e40500c1803049408803a40d04812075035418080320b01078029041800280b110780e103808030050240e0400290301000c1c8200900300c0c684149203040794a10b03d00d800203d0002c006503444006441e502d080c5801d0054507070a140980c07502c0342d94141c14032106000382400c0c215402a00c0758008104041001400c1c104008019a500c4000602c159400d100e5148001e400510b0440c15045402020005d9405080d40c401c240b11b00b038a404c40451034145404c003002d0043c1c1c111200420000c1c0c040c0e00742c0c032504040d02040c0d0740d0003078001001c001140e02d19408100141c0e1248054006281d020390020b0302c020750410514120880d544540059015100c000b406000c800075071013040d5681c008110406140c260400c4c050340b64103143c005442c00043c0c401a010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 147814370 1250 147813120 147813139
    0xd0f02010f090f0b0907030602041d1e0403080709083304030e040c0e031b030606010c080418060506040306021e030613090312060305010501290307030b03100f050402 73
    0x11040c00b801868162504a00c10100e05450790b00c0d03299403108094800e190b1403044440010010390366001820043c201c0fa40c01c120280012401c801d400b000081c8800020703414184040012011350b150a40c00030340515001030242e840b0032050354101100c0c0c0004c4018841c00001802c0705181640041d80e40d00026130209021000646400425109840c02404a040c910b01001c680c20a50300002d0100c6080c07a10346850342050020074100140c0082c6400b108161000110450a04100098001030300786044c001c1b060481d00d400d011170241c0c0c000d51206e021080c4001c0e5259403107411181c0034020061006940e199030380b8110000b58410411000c0d03030380d4680d15900e18210b200c030913213114402c05481c84901040c07140702c110051034440012018031000f64032503032111515214540165106600003d045d5040804000107500c8000d0800c640c070016902c0540da2814407810b80c0c0d045020760801040030002d07200060300340b00d11000e105554524188507240d0300000342c1c12030b600030350003503c06840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 147815620 1250 147814370 147814391
    0x1503050705030f030c030418090209040b040c0e07120f0b100903140a030f050313061e0e030304120f02030d110d0f0b030c0d0f02060c0303010e0a0204080604110607050d0f0201 77
    0x200c3c1d0060117501c3d0781507001400200b05051080343c004aa48459860029170380b407603075001400400e07069905035900c4031140d00304820400c140c0ca10f02d014242050f01d48080345051075000341510780004010490a44488080700c80601d581c0044144105c003c145040805001e140200f407002d03248016101c0f4480c00100300000c0d400400c0c1103081a80550f1020f4095040381d005456a600240c801c480300e80d8071040c40004035106200c4da1083c9000721801c018556060707010700099038254040c69910b0707007041040c00b00142d0701620034480040c032810b15020403a80f014082c2d0640c000d0fa441d10301c0303280c1400b146084c03015440c4000c0c00c680c2d0051760b08002c641e441c803190303a00315481d9462007074169010146404082c9010807507140c5544c4900301c0020880c00c02d5000c240280c0000e040d02c0c12962002c80113204000070300000795444440540218242480c1402c01c0e48d0381d402c00381020304213644a054140180c1c039800304852000381c00030b08944844040000040c1200c114000e000e0042d46010745107030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 147816870 1250 147815620 147815623
    0x503070209010e01050a0e040302030c010603060608070b160f141f2414060f0412020f0d0f02060f0d150f080a030503060f010c0b04061e06081507031503050705030f 72
    0x5060f52800380030506054284042d07d849a100a4825015031105100c001e40c01c1000b40545000395106620104811b49441c124074502803141c0c0190078916018810500d85408420101c80d00642001410913007006034104010b00c000544007914141c05100401410342030300d901c6012100641030b1007044041c1003400d210404200b0341130380c2c2d80d411211920402c401c46506c50804170185008010078500740c10f2828280f115806507011496070741c006231302401549003003001841a100195880000c003412b075601e1440120703010314001e1207403002040c20b400c0d503a000c00666500d80d105240401c9412021098429620b035940f040c8d42d0011901c00c0e001c201c214011030918841c83e41525003a065448190421a003001c0c4c11224074104403103c01200c000c5072810b0182401640600b000160b86c01540641070803840c000050b22070441d0030032800304482d8000040082c540d0b403002e48501210344078020210003900c2000403045400c64101c101000340000820070b1412554114100e85c2d40359510120203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 147818120 1250 147816870 147816899
    0x501030305070f031110050121020d060507090b0301090b090a0209060a0309110a0608091207030912060906050c0a0210180b1e070c030f0e0307061b0807050307020901 73
    0x2400540c003800601c000410214a61450b01c3c030900b40106042c07401c0900e2450506e4103418491004c3c4c0307850042050903034511041c07120101c03a440b1400490110307000b25144055084005003420b0341c0d980010441e500c500d40d01806042501002660395a4a05032100076103282c20109114054180205880e1030445c403c0311f103020000b030507450502e00c2d601404e0b00100318094040e0340d4800b000c00d40c4802942c8031803202e000f03041903072070b4219142010a4680d01d0b2010f400c8240b803860404120100c08a40c102d4403103002c17a215000603241d0b023048c6150030030113002c0080005145034200010f010198500d84043d00450071307035501321001d5103150b09000c003d6400c11452450740f0b408620812001c00c25901d009a03104600c844c00010801c03505003203101c034040444140c00022038005d00365080607403009000d0140100b515218088482c0d40c40080c0d1130390b52501c2050148203c456106460002c8801d038003001e10740102519460309140d042c00c1d500e0b075210303400c00c9105881010000c204940030101c43d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 147819370 1250 147818120 147818123
    0x70b120703090b19020903011103010e0108030a0203042105010c030c0e060301030c150c0503030106030b0a05030607020c042f072303073905010306080705011b080f0d1509050103 78
    0xd1900361a80c1100490380354544c0030307000005400300050509600c007402188841ca0000744495540d6241040124800d40d060700031184030740041040c600080e500100b03403401c1e200b094088030f00f94012280c0c07510f01c041e042c203002482542040e00c000340d00c680503800b0622804143c1c8802622100782420071113284024000180120806001409090b1519030044000403160800c20082e420903101e003465034009902080000e0345401030b001207410420540d0005100a400910f0141404200a9241c1200122540c091660785d00b02200507100609140c041c451204520007404045020002407607000b0407081d03507895191111400c001d9019070b100400341d600d103c051800d1400030b940d1003540384034906024035a400c8000702100d0b146002000c44440d40c4860741107401082c500300001d001d41d1465400345966400640e0100000e9030031061581c80c1d02019810000714044603d0421030b103024940423007076140b00c08500780c10010665405000e052000310802d403200e40d41e8510880c2514400d000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 147820620 1250 147819370 147819383
    0x703020102070b0c0c1f1202030c030414070b040801060906050d0503030a022d0a02010b0102030c0a02220c050406030f090c18090b150a14060f07080903070b12070309 73
    0x104030f088070b400042c0405540100540e604454080e0024089605106808800140344150b12802c00c0c0c100421042c8001018025419442c2c0024109000c0c00010009000c2c550903a1818204080610424015082d161111900c0700d4032924014020300d86805903403a800e1038090b000c500d078982030010705a12a07220000754515600c03003454102a40008441201331038500c2c0c441c50318181e04400b2418440708080c1d12588075600303480001d00f5140d203c2e440c5410b54000b00b18923400030a02180c103008054060700c0c2c50482c440c5040c4002c0102e44101c24000701c142c540030409101ca94007200074001c4070708582e400c0c810550078180d10400c44000c181c00410803000c0000400c44000030f504d0b0162204000c100c0014001130750b8907552628102201ca881050400c00d207078020709e280810000024001008280700b0303812610002c6025803081c40c0c104070b80c40d800030400d1010010039004a03541940007400f52103400d9558070901c0410782002c203024000880c0350002410303080c800e01c65514503640055 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 147821870 1250 147820620 147820633
    0x1006080f0a120c020303210a0504050d0c0206090405070c120908030301140415090209040f0203011a1b0d0c02041a0a05010302090303072906010804050c1009080d0305070f020703020102 81
    0x103807408000702c0e801c00010b0520010200740405a50240003901004650302c007400707a4940800c1200405503801004484ca00d45407234144008124002008040d600c52410010082c5001e80001040740c0102611113a00504000070890720a6100c813030600c6403441554074000d01004500150b5002806014184483c1d105200410262012002211510704003410029070425602c0c040d45501d4240d81202480c240c0004408809040c90311868503500340101c4214115410210803a0054032003015403540e4070004102030013040c4210902d0800301711007200b02c541403241c8440241c122082c6e83d030240d21451902e01e5410a402c0d007016003d8030820010400b00c1641d040a00544c001e410511302130750148414445440024008014030110b500c51041040a048580c01042c1100000810366030401c0424000d00001913000544030000c0042140c21545040b40c0540480701000c0a40c4405110b1080d040f252890300e4040c1e0040c2c1c0140401e9440204160503590243da0b580c51521000340141e1000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 147823120 1250 147821870 147821873
    0x1020c09070e0f151305030610030804050918030304050606100509090402010f02120406030207050c04020903030d050c07021305040303061703220e0106050c060105010206011d04020a0806091006080f0a 88
    0x1400c480e82d5116004203a41180c4200e130280c00c1e070a40060702807810944810702c0600440c03070100041a408035940f01100c942c00e06603a24803015010301c1c450540540141404507a089031200c840408407421402200d4031303850f282c10003540c0d403502a20f060340903640d441c0c0020312041c4500216403108a000d0480f08032501c80382e004444030520340302c00000718000c1c0400d0001c41c0c10707080c006200902d8503a0b009603e50f141c03070401904103020583d080c7d00c240c2c4104101c2c0d0042e14040700b80e5041c40c1c050740e00025280d8411030408040d1142c190700943c03041c200049800f0500030360340700d24000c80c020744c2c0c20840c15841710094000e0941c840000d00c000e074018000207103050141c0341c44050800c54400c480064507940c0c41c261950b03241c280c0063303002c2900800c2d8102c606108000031030045c0424070042c440d952604c1b41c1601c0541c03000842180740c07003035500014107544860040500134040781c030488046103449411703d40c48001100c401d54049050180014400c07000040c941011250400034103c2e40005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 147824370 1250 147823120 147823129
    0x408120402130e01091a010807170c030703081c0506010504090b0a1a0a11030a1e17040c050415030b0c210a020703030c2c0a0b0409060501020c09070e 66
    0x400880e4081815850050001e8141c09044440800f0300004200c80f142c618003140101944404094020203905c0104018000016a101112200400032408a11008400d07040020310461aa00761155100000c200721849000b80310043d0340080e6255050352602c2d000c81518420365041d400140c0500050200034441d40c8880040007004020200f101e59070f03003000c0080c45a4090180c5851804984d001e000d9411850b040c80703200c2418040c515003807240300068242c0d19580d007800b148141039000d003500355014100c40881683e180a203040d441c030300362401c007207096418040d40b80981d0403c21284840c144420001c801d903a40300b4100c0e4110740e542c294543e41900111550320350299000c003c0c4800c2c902c540116402220003a002503951351060034060b05403080310a0390300400000f410000000e41482402100e10412105030150061030b940000c1c6440c1c80d960860076040703800003800215040160300080c11260282c083e5000748440c54201314000c0000c480040201c1c092401c101f080303191 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 147825620 1250 147824370 147824407
    0x60103020d0212010801020d0e0d0906120e0f01050907060201020405031e01110a05030906010e0124020709230606041809052e0b1207030308062b0611030408 69
    0x41107001810102004842410b0780c030284d001c605680d6001883d21010f900c14021002c0344414540100135019001034010150003103032040300c3c2040400000100c1444a07a004400040658011121407003080c02c1c4040c000d10f0180d400a0700e42c400c0c040006210b50040c000e4404461700103000c5d00010081c09400301c1801e0700a0380b88800c0b0b5603501c0300785610a440001410024685644003612490035006407032401c281038000702d240e220703541c1c0104200c00a29810301c02901802d501003400000061b8140e2070704174660450410a41040310340c40b001b100c281c0400c00a4416101c6030310703082d22440240400351180c1d0050340440064070804002c2800c0d640c01c010b44541c0300d00125440700e062140e256424590f108142c40c3c0142c0e00000088003050f182c028514481c10448206503a0074480c2c8026517202400e2100505001d9803000181e026039803a01211419100c030140c143d18035056801e903038440c404070300d01180c9032072502d0058070807014040260b91103154400740c2c03146040d80c3c1d8640500b6104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 147826870 1250 147825620 147825637
    0xc1501080d0f120f02040b1c050f0109020a020106030b0112020a09270c08100615090e070e1c05010e0f0102030103080906070809120610060302093601030b01060e100806010302 77
    0x40d00d0344600402200507100420040542e41034048d206c41c14002403504802c031081c03469801ca42020140140604202000ba04560507400010303074071244240c0036400b514040d84080d03c0317546103100000ea9152000d000c0310410b41f01f1602005203940340c90340314040714828060300201043c204047d180d008109c0500c11015809a1071540d07900740d80f013207001d2810589822514039662980c0042010030b40150314103484444509000c00d00c3c0e4144184810380c80340041041040284d420261030341511540700b000703202143d0040000103825541000d60180c401a034035049288159881d2180c03160061007686e040e65440801c89140c0715101d0700300181030704035450030b9440344400c0002d100d4907070311222040300180b41c0e10050724562900c2516108406419807000003814010030445515680d081280403110310075201980c05078000b1540550071240d030758882d01d05000b4240000c000c0c800d50400c0d460407154a40e480d11401e211050910100416510107000460724442c04243d0942c044e03000b42030200d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 147828120 1250 147826870 147826907
    0x20f0a2112050c27030a02040f0f0609020c06090604030c15020f070606030b06180a090501020405120a020405070516030e031c0c110d0206040b03040f06020c1501080d0f 74
    0x6008a58082240c0c03040c0c07200486500001034010b001080c0c45403000c1c0d01d0b1036021340c04494030000c1001c69152104040028400e0b80d8030150324910000384d600c585c0b01c840340750008219150315425140c0007544070b811031840078450040050b050074130005503c4e00c00c0d0303072540d5890311555503951110445160180d811036026003d20a94650a40201c0a00760f0780d07008417004034a0520714104026440c20151809004500f2854040d80c41140c00b1140c94022050510006506030607050003402802140c116aa0083c0101c55005603540000343e10b4084a008403010400354490400a880c6807141010351400d10700c081f82140301082c09403032015002400030301070b00d902501c0440800c001e440488034000100b84400ca41c2c0c0207204901d1180075a071801900c02c0e540184654001030b40ca4011445803200e000c400000040c00c0ac111039800419150b4049030554440b8100d04006031204e103008001c03180c020041d4000680c207400005c408140c0659030701e42d074001d000d2900e8104e40c44920040c101640 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 147829370 1250 147828120 147828137
    0x12030a1d4e0c10020d050a050702030a0f08040306050618190e030a1706040203040302070e092415030109020f04180b04030e010809070b040909020d050703030f020f0a21 74
    0x820403907042880c180c450480260000301580001c00040c07030025900c00c000c541c1320769541c5641580000071540c0401041c00d1440c2c03505610b2000078034004440c0310042044045050807000c00004a028100f500c0c4640c00a00c540c4e070701c40d01441001c81f082e91084000b007038404080399a1207a1800c89900c08001940c0c086081145004820300d107030310155000d000203c01821070315000c0c29074804190807801c111410351550400344c60003940c52019025800162031094007143d482d69003084222460f4015400364404d50309048646007400e001161070b2201c00340840b911800601d0184506d0b06056801048400050311040c00e100c000d100c190040d007221840850007101103240c4074546841507209541d420420741456000400500d0040c00044084d0301c088403e0080006010541e002d44140702400038030040c0a000080c01551041006040c0c0c0c0620340020007030590000c40341140b2941364084458482d1200d500365601c480d01a00604800304061013502c4042c1c10404046010260345443c0a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 147830620 1250 147829370 147829489
    0x3050304050c12060a060f050609270901020a0906032903071805040203010c11030301180603020d030909061208040e060102010e06161701080c04050612030a1d 70
    0xb10007041c0d406410795a403011041142e2643d4501946d000b600442c104c51641600d4000499000e016900440b8400c40ca01c201e0340f0042c842c0c0e08103400017207085079541480c5060600c401d6000754094010b50000852400003c500c02c0e0180c003980d40303100c1d004101c084e0b80c0e200c009504108960380080d1a0b41c14050503800040e00c5192003801e08000610b00c0300092182803e104050071102501a10024040c5a100080d40b0303a4000c000ea1b8115004141e0080c00040c0c0140c0030001803c89810081d8081303040c011260034198061110801d50301c0b405810031070740e40c03240418054440713500070041040d88100018002101c0c12010290096018000811304031504141d060a10100710360400814040c100209900c962200d04030b01c1c07115031a100d50348694100999291141c0110904900039a29040400c0240e160130104220480e07000c410307030b91210386000c4000c088902807186988251091000b00041c3c0c900048034001c581e540003804074046011102160800d010503107503400c4152440c440c0b06 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 147831870 1250 147830620 147830629
    0x30903140a0329010f120b0603012628060f0501150306050607030813020d080c010608060907120b0a090c1403010c1d120a06060e1b0c070303050304050c 67
    0x1031168250300e002c2403001c0714000000f81e0030310840b40d4031540c5452500c0d40e412640c00c0410b9441203985440c2c1410100381000720100a02030851000d6041200040001042c1d0142c51812658043c4a02c0d1001000314103842d17a0b55994440641c1c821800048010a40c02c070034003c034540c2143e21035031020585550406082c0304a40303099201030b9400340c0700302c0c1d000e4100764140300340c5c00640022981542405c2c1c054500501000c0c00802401800e03035a0108803080d0340d240400703c40c900782d01c903214507901c0280a030750038040d000500c100c91507031281030b000c120010004141e02e0165858403d07038500304126510307600307070104000d089803120035a40c40c00440801c81130f802900162414840d0842d6941d141ca050500311400800441c08000a181c804803c1e03907800004140f50400407129030b80011130b1006054103000d44d0150040207a850624001504240d00400621031182e0b0500061259001d0454013a10f110f041c4203088039801c00d40c414800a4010300c05135030098041c40465140402400114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 147833120 1250 147831870 147831877
    0x10b0a090e090718150504020a022d07051c0602030606040f030c050907111b060c03130f0e160f0e040c0c1707021e0f030712060f050f040303090314 65
    0x8100a800068081c0300200c080301c0b1450b64414000c50401012800e200011048070046c001c10348203030740014910b11610310170003211030403e40c51510184e41c507086c0c02030183d0f600d401100c100440d000300d007800075040c6408030007114039a500811030f001078403881e580c00000f50700050005501c03d00500010401c040a8001c0b030b00614814100002214244403c11045210080603d8208402840802c051210220703407410075401030702c0d5050109141c040050114041c18600101510020801208120306422075804030f45603460403030b03041c0340c5407800c032590058101c4091000e41100e180c81d0407a188203c003c504552614a00324205505500004059030200c80c03040c0001800d110b4040c0500c089099100d207031005a441052416103254049a4004110f0006030040d5118010f565800d4135000403440b40000010241d038502a12200c1080607401e0140040e95280c1c070b0f080c044241e4140f44d10845004104082c0d0300d950310740d16035408a0140140040c124200404a85900389061484028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 147834370 1250 147833120 147833131
    0x309070305060711100c0c02150f0f181005070b0c16061a01180303050f04031a0901140708040f062406030e0a02060405010503040501090203061501020f01050708010b0a090e 76
    0x182c80c1200d0b18220340178034015420b89000049843c0000e00c594042d042881408026819035201da0561243c0c01d01500500500c41220b40c5c002d0700041c15400507030082d002b003081c3c484215418030702d2449003041c00b402c0e0002c1e01c0b0181c00703c3c40400002d004038101103c0c041e8085904030f442c5181088003e183d8142d11101507085804c2c13600c5604a5181c840c0c0301c1000181088207180c662a41c030b0400d04003034074511651201a080c44400181c1c188041150400c0303801850f0041f0070b13050807600c084100d90204108548200d095487c10001d0804510302150a03401040c45a40d4032030242c4580d141d605402003082030851303031256102400061010b00c040503801d0300d2040310398034885a10f0000003400b65400030f158044030750400d41d100001a41d0304000c0c1ca0a41d6020b181203601c075501d030f00e0080c0c0108800600a54144244000c0207045000000401ca801e14280d01f80c0300301c0c2d405244442d0a030f030300656032600070078986030040c010b044900000c2c0502c4a20b43c507101000e40c4c2d4030481c0000800090702d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 147835620 1250 147834370 147834377
    0x90402070f030e030c01050307030209030c1206060a0b07080319090b10150903081e0408030301080a0c0509130b070210061202091b07030c060209270601020a051203090703050607 78
    0x55824181c010f5031002c1180420350160039141100c0c80000c100d80310060420080c10703404100d0b01c406440c200301c2401c00040140c00b400200f40c0149500303a8a80c01241d140e032158200c0032010036622464020303941820740c86105c407030450300c0d1240f034010742600140358015000e5071451030f2400b0540c141511401905403279003c0864070b05160707a07840180d00c80c031a01000d10132800f00800004400c1c00455015034110301c0362a0040440c26006901c5200382d5201407a5407001000110b143c0c40041040d01d4694410140d41c01096618003c0c80020081100c44072250b520b000c607a540480c0b03008180da03601085510503a000090a0350703500d0300715521900720007040000c891240045013005181d15401c01c100300d1800d00072a45200511009200e00f190050403c40700b0008441081140e40580c2c42c1ca18000f0191282c1d1082014102c24459010307948007400b2035120089000c1c1e50004c44c0e084040b907009000b030b20114800300d054188544c0080d00000c054420000000702041c003e001340f5000c4c0c822541e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 147836870 1250 147835620 147835643
    0x10c030314041b1a0304121e02030405040c09080606010c063e03090d0c08040e0a090c170309041d0105011d0a050705071b0b030c090a0b03131709040207 67
    0x442e940300c0038819000508108071a8182c1e1421154010640740c1c0203030301c00c400030020b0002110454031215110b5018010745500723500c60760300c140c000c03024000b9a04e00780e60030003669001c10f0044800b030404d481081340d650407070000704180303500c2100751201d0a40150f0b0042140c1507035a00c0c810750b5207410307c0c0c3d0032445180c00c011413815072900581308840a401010083c210300b02070303050a40300d004600c000400d016100c44000100103021007542d0090410301d419070090b10700340944102500d200f0b4000c035400d0321540e801048004000c50b10070f180b607030920000c0d8282400da4007400001c0511540f560500420680c0400c8000d0b82400340d039010f0181050080c1800b801d0010a814018020b800748005c50304180c204900c1a0b80102512101e40e0402c9100c0c0e90060185000107215580c0c0d0014011140c3c00820004d5045c00c1800410102e441500c0820245a80742c40840b007500050f1214812000300740750000c04604603101c04100440c0001001d860104c810700003d04a80c840c40044416800c41c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 147838120 1250 147836870 147836903
    0x91515210703030332090f01050f01150201060b18030c04020403050109031b03020a0204050612010c11070f05030a060902031006060c11010e010807180b030406050f010f0b0702010c03031404 83
    0x5002e041d0302541035407035029020604c02400c1018201044110002c0030305540080c03c0031b0383c200031303005203011110003c12007070400c1e51680314050b02c00d01450790040e18004003580c0541c414450304084807000700344942801c54043c00704419031581710242e40c1c50722405011303081a9403148024001184a0000000d08001920380a88058490f9500f00b80c8407601180c2480401e030041000c0070301c0e6504031000030b1150380d800001007140e40c144400320055807800000403072050b00660000c180903146e000310385201e683c400c1c0030791120385240103540c0c140d000003916400203146604042e41d2584001e0940c0c01c40410003015900315604e9070711507800580c03051030180c14040c07528030904612000386008010128480300184c28031310b01401403420044900d10040b41414094400341c0501100844117940381000d042c0b0402410342030700c5494a00805200020f081100c20704003400301c03081c800c0741c107081c400d40c0c3c2c00540c1c802d24200c01c01e80605854000304c0856820070b41505102e5413281c1415541c19448 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 147839370 1250 147838120 147838127
    0x9020a091e14060927070207150c02010903060f06061d0321071203060609121a0a0b04090f06050105090601020d0f03150b270d02040e030f190809151521070303 70
    0xc6c14540554120310010301c4205250b15030302c0395104090074031101aa00c24401201c154003507500160020b45030010840d800004c0c1d810400c12552541e46144c000301c0c0409000341c0100c4502c42d26070381980010250820708901c010181801c1c070010b5400f84c205000c0f5292a004c07912a04c5003403000965030300d0240f101917005030303128020740344020000c000c00000340c0c3c48071170300c020160341d14802020742d0f000152403103215004004071000203082848001120302d0b02004404400c4800c41e116410100081000c0c2010044140b1410050b801001840c081d6a82514000d0041543c042016115410042102d00740c03840d0b00000e200410a00d907454038445045050100c02542c84400c40400100d100b40702c0d40d400100b50101c2e90101c0380003d1100d40d052516145100d251419641004041048040c0c1598001d6641920082c0d48502140340d851a0600e81c0302c0400b80000740e40324a200001c104850587e001442c00c16002414900e11924002c101c00c2e01103014641c8582c0341d900a90080c420541d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 147840620 1250 147839370 147839449
    0x20403030f170106080105010804020d06020d0b040506040c0503130c0f1701150501080c0d0608120306031b1f0c240c0e100507080f030109020a091e140609 68
    0x800b10b18100483d4141034006050303040600c11181000001030101c1d06541d0f0700c50a258a00c1e80c041c20841da15188441c414000d403c0c1c5141c224401d40ca008009182814540190704010300140d68451850f56a40600c113401c1d0144002508c000500c00404951210440e80c07150151400000c003041482d212840c050a68413468641801402000f0b001c0005176004000160059041c08081e6128860071050304001e0045600c054041e10440c0d250b8516580d0007002940501301c15400d580540c20503030341c804501c00003004105c0d0010101c0c5a03092086000b80380070340841145141803450340c0125210300000c4940780c2445900d4100c0600c0d0780c0340f1014a031080031894003484c100030140f240503100007039849c07400c3c1c1060014010002098010020908100e460031342c1540500398513075840e09a000e000303410000124011030035024003c55003098403185500d224171480b410514685c20034441e8180009a82540e9401440c02d112201003550749013000748100b00c0c1e42c610608022a40006802c0400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 147841726 1106 147840620 147840647
    0x60d15050105030f030a080112080403060e1e0c060301051201021303050a17281b030512070c030507060b13020703050c070f050a090902040e01020403030f 68
    0x5499446141039910540131a0b0181c101c8400c1390b0f94034031401494002160940c07004004007508400d002d9581031140b440d0504007030b520b9491302e066907a840840c0d2540d400800e02e075918907140c81440300c00440020000c00c0590300c0c41020858030302c018018140506400765440000b00c100350112a0541007001200b2209030b070341d041c80c640314445a031741110548502e0350114000880c2500f51040c040b00442400e082038240c2e42c00900303400c4000e510000740542241003184c1c42010403407011100d4041c0e00c48640e1600304004d480f194079402882d146c03c2c048101d1451001c40e92010070780380c9140d44004002030030711901c4000703030010660545050500713000080e08010158418050b00c45050302104a031202521000d401102042501501d50400320480301040000c5036074102c8490980003030000074803240d1040324117084e0b80c0315800603808a6900941c2d4803505603c0140004c840 = true := by decide +kernel

theorem cover : BRFrame.Cov 147661870 147841726 := by
  have h0 := BRFrame.cov_init 147661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 147661870 ≤ n) (h2 : n < 147841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
