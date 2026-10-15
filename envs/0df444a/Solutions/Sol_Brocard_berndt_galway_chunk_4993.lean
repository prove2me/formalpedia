-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4993
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:23:32.058976+00:00
-- url     : https://prove2.me/submissions/08bb4794-9d5d-465b-8453-f15993fbd329

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 897841726 ≤ n < 898021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 897842976 1250 897841726 897841753
    0x219080c120a151203030f0b01170a0f0b040e1b0a0602030d050601030209090108011505040510060509030a0b0f0901140c07120210051317180904030c050d030c11 71
    0xd180035120259040d01d842c01107480c0404200e00d20004c01d01180b000241e00035a190140c090105000080c03040c0e4030b003a40000c000e5000d0500003c0c00300510841d001c0998413080c0000040040001030900180da5903502110781d03c82e4071030a0080710590008220100841000042e02aa46581030303000399000e420402030346400005035885001000e001142d076540c0c100c0101d0003400f80c00b10312907005150400001c0e141006600945024550101d00740c1e1243d100c5041c03000b91501600c02d05002040650104030303652041003d40322082c07009003074490350013442d1101c403e0403000f914044080c0a189080c022004024881c1d00d20484511040780c903181703080d2060380d203d4011080302414540b40d4460280703980344244a41005c0302200e040400107801c0950485103500780001e812a202c14116035a400e02c0b20480043d111104049070124240b41d0444051101004001c1c2c02201880264044d120010b5010300502001c51600e0780c000581302c650f1813004020041507503103001990421906507148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 897844226 1250 897842976 897843007
    0x15060607080a1b060603060c0206090f0d050d0f060e240a0b0a030905121809010e010b0f0c0604080702010f0e01020d030203090705060d0f0b0102030a05031311040219080c 75
    0x2004490501d41d50748481c0c1c3d4030600808096810040c1110301d09480841081010f51048a45100e60b600b16031050b65600c0304240e903008a000c034040e00da4403a03212246903d12402c014180d0421307200b8041404958240301100b0350b00c25400c25400d22021408100c0c550591041480e904840b4109a01405002001180481d080c40c06440c803c00e4000807507098060082d0400e4005541c010101c649030b186880d01080a5040320b034100034a1440c020481000340342001d4014141e5440c01c80301000307a4079010600a650780002030b08514110b007485481080c5109210252290340a140d290b513032640c052000501c4001c4c0a00c001e000c0c000d0345201928a41d03400034022024140038200165691940c003001440d2502603409268003103000a12020301440b5600450301e24041090184030010440b001680c89029159601c0000350040c40003c0d00c0d00e520f409450001d41c0039000c4c0c95081d040f080041000d90b0b100f8010340c2e88441608140100803907004800d550300c5070405242504004107010301404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 897845476 1250 897844226 897844237
    0x40911030f060f0f12010c0e15091002010917030106030f020703051206030f07030312050c0a02060a022d03040b251115070801031a04020a06051c0e1506060708 70
    0xa140f0034000412540302e00340d9600061a000b000c0044440e007410030705000e0501400954001004080951043d0404031203c581101d05640d000e810414460184800d0400038120325086640f14409200816444968813140d4455821010390325814604003800365420140c030041c80d94030400136100466070000c1602c0e10800e1078000c0c0d1465403200b5001a00d400c800e07650480c203034001c1000000801d40c01140e000d022110405080c4003c0d920442440c9240c01011071008c05600300c0310005800c0f1510b6401003000c1821000141003421075400380c171684041d0820039490485000083c4010b0040c42c024981e80a46040855080607000c200803009005601c10f414040c04400e51038070803a07440500c50850100140c1d00341e440c1c2d525040b04010078240d42880107032040c908a404c48805202100b40c42881240c025003200d03038152402d6012070b003981c440c404a001482c0c00aa20300340c540c0050080411340d100003001050703002c10b01d020b8405c41b0b1720003601840c41f44504004000000d5202e60a440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 897846726 1250 897845476 897845479
    0xf0b13030f0f050316060f14070c08070b0c1c09050d1103120406092d0b1e1005010f0302120114011407030306030c0509130b0c0915040911030f06 64
    0x40700442a803420001c02d9003484001012400f021403030b000c00c2e801d040728000b8010301401c2d080c071019031308410280c129075110021004d04000100007880319401788902c400340910803a0010304e45105a11608081c00701520f202e4600c210026005800c648030030384210015201910410804480359520340da60396481480780306002d0901014038640c0e00a00540303a0320b40814490503030910780740c60440b00030f10b010082110702180c1a400e4004400725250075001c0705000e6075807648000302d65180c0001c5600c0c01071801d8030f801c603005421032585c0210540b4501417086107181e80346042c00c00e030000d824200701e411214205481800000240713a900e080090450304001d0b000924070806000403144040d10740404140c0070b0b03000440c50704040c0d2603800402120300404c860010740b51200100044071006a0f0280108100408441e0204451003c219040b080c1340c1102840c0c81030751400300302c00543c54802c40010342c801003820000c0300701501411500070700341061140f80d450401008240c061001d44000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 897847976 1250 897846726 897846743
    0xf0807030c0306030b0108060f1f060c021c051509010b0105030c0904060e150f060c0a110a080f0703060e07210f1a06100e2d060c070f0b1303 62
    0x501c4200d001e07501601c05550881e50603455503840c2c0f40c259682d660140c58800b41c01d0314140010b054968150107440d000110440010011444c1a00840751441c540409030390282140541c4280103000c211006d90300b42c4a08054440c1746100086180c40860092200035581d041c800a41d015aa0103001c42e903110804540300c685070310300f1102250083c0503d802001d17001e0740c00000c0c40300d410301204610b448080f08071303150014003200009021480c01100c502c014103502802e41480001e1004070102d0510001410a00c050390303641d100c0c6e5207400764032060365006410084090082c0541c038040c4042030171a140040155074902060001c0f8001505002680c40c2d403250000340420007002070f42c14490381c00ca8000706003c00030400241d820803043d50900e1050b00203482f42e85000b802140c42840175580245108040d075141c03462021090500c00a00d07118130a200082060395a40c0320180c003250900c98001e08086080050103a0328008a41055000010900400c0514044004420240c80d44544034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 897849226 1250 897847976 897847991
    0xd060e2a060c01140c180102150402040e010b041a03100501061e031104090b031606050301170a120c1704030b07030e031e030a1a0310021608070302010605100f080703 73
    0xb8a8014805482c00c07041c0140c1860500a60000d05405011083c15491040a0220b008401a80d9856004100317030068904000002c002d8036080d070100840c2194a0300204502000c000001e044901d101130440c00782484d071007204100c3c1420810b0810031454442d0800540d41400006010b140c240511010388400001c40303c46814032982080c01906e50b0421600d44407900c2d2000b80016003055801e090292041c42c980050500d0b1005c85e0740215820303901c5451039642410440032030803241002c10300040c4039076111580082e10900510f0352454641c1d1300c41c001d030302c101d00d8280c40e0392190022190200d0014030040c4045038001640c60341100d803d040c0026141070b900c2c42d86080d03000b071690000308844622000d00c0d181000c000114031484411604101d0042c6800d000b1202000d00701ca0603802d90b0048480751942c0724194002c0c02c0080d08816000903490880d602d805c826400000102d0060b5140e0701c04000c11309003007020412003011814503e074003c41d400002400e12034002d103004100342d100c0c0107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 897850476 1250 897849226 897849247
    0x10603050307080a0c0b011206050f07081801090506010b1201080a050c01030b1c03020109060f060308040e0a09140706020c10050d0b0f030f061017060a0f0b0d060e2a06 74
    0x2c2690382c91b42c8080303800c1e115070f500c6411460800180c0707020740321581800001050311013120401c51107084251103400041c0c031984e02000c2e00304102250050503650383c1c4088808140c08000485c003c203c1d0311105c59884084a50031000034030103038090103039a0310100c51a0002540403580210a4000307281c0021541f200500249000b00020061459441c42c0840c4070107256040d0425008140100014840982c047d038001007200c5151102a00312075060005002da800d0b6000c103d60080c8036200b01044e4881589c440314041002d012540c6565030081400700a02c5805002c164100e8504440c4007031840030521300a040c504c11070034030050b006c0c1e861030b10449075911594542c1540030060101c4a042c541c0c1980c02e6a82c0400760344540c0c40000310030000ad6281c7c0c000c280d003581040000050003140d100c1a01c064050200c406202003c0b64460307000b2426a00c64210368082c140c09103202245080148240ca800d21006820340c2c010740030041010311011400d50340030401818151007050f91902c0826 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 897851726 1250 897850476 897850487
    0x60806061201030609140601060c06050a1d071503020301030807062c0d1b05030712020a08120402040b01080103020307150c0503340c0b0a0e0405010620010603050307080a 75
    0x290303a024807041c400021090150325805200f1592154101e10b61101c030b500701c4c6036942c000034404d1034005660307262200001622904516081814100d01041c0c1803a45d20255545210800034086030303600c80a81000700c000181c88403031081c98141001c41c615411920351042034842c0300030141c46240c030f5003008404411034084600700040c1038a001c00071441610340321520b61100030307107007800548414035a407040080c01030a04007069202c001149052003658034243c05003030005050017540075005003640420401e100030651010b5440d55890545014030420049034548517501c0c3c10882144018001071b100040c0c0b00d010340e41021195510f041400c0011205d201c000030004281c2c0c080843e0949803503070f00e185140008401d040030300500d807842c1002040036460901c03004d41661880c01080066640c01c0b00106011012480c012068051031030100342544d0080c0d11440019244221020170640340d040e543d8901c598480090059902e142c503242d0b5a80284c103c0a041c0304030008550380e0460251 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 897852976 1250 897851726 897851737
    0x14090d020d06050105120102093a1b0611100209060f0c01020403140a21050f0c070e01290f040e0906010e0a090b0f0c040f0b030610090b0406080606 65
    0x9190100e2107600345400800362400303124840c081e10103003515201700e403018020f48400d200d0140c409100350802d40380440b080b0284d0010110303402021521500801c054a0300400b401c0d000f1052449801e0301003080e0351000ca0298808001c01800344100c015040010588680088000f003000d6100c200403000501c0a111350b01c507150b03a0040c0003034400d09880040d0050812a8000c00c50bc00c46540380c80c00d051b4840711400340003044e032461603240744900240c0a04042080440b854254100a002901d0001030b602c003105861341684030400400c005180400558054480d03940d600c2c0c0960500044400c0002111882034501400030400c03454400d2100150350040c4503510040516003001c00d40e203500c6030400e0160741030210402d000160642176134041c030f13203025034400c110603030366555080b0405154001420f0b415001d14104030001e500d55080e1b0b10b800141102e031041c07960b130b824005d040091040c0081b40c0401800700810301040070904800c1034a0803241c10b828607901564482e070000c1c0b224448c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 897854226 1250 897852976 897852979
    0x4030909150906050901060c120c02040f0b150408100b12120304030306060903020f04181b0f0e0903030106050c010e060c04030209180709021303051504030207140114090d02 76
    0x1009a0a0681c841618200e4100d4000c00c408018103500c0d90207000700c1070400d01a06d4045242d511707280303000a0344900041c1000030b052403e1400c8016550000c2d040c1c8440400483c2d040c0c4d1650303d03d030128a0f0240510803140d0443c0f95481c507280c0307042e88540c2c0b074403500b509290318980d4510710a1120740301e00388059200e01d60310307068594401400740020100e400980b0107400080c5440000b04280c0d0107245100203a079002803010100d06202c100b004050210034001010f00312281c685200020140751280450304596030a0410a60900300510440012607100b110303828800c4d410f024851001004807030540d02c007860a590381c0c3e800c6181007400f62194021044403071280c4810007181c220701001038000c2c1c0f882210200003d0301e42c050020201c2458402041958000340700811000d190340e80100a845828000800d074966070303840d444d0421041910340001284040100300c109a4140300001c0034000c030040006503115098002400380c143c80c5c200c181040c2c40003032a258039030781d40708440008070350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 897855476 1250 897854226 897854231
    0x6180921020a0c0f08070308030c0d050933010e0417040902040e0109020a0905210709020901032703120f0c020c01110c06090d0f0803040f15050708060904030909 71
    0x101068000c0d40d608a03418283c0722007001d0322022641c00f070a00c0603181211101c000512085d401c5840d01d064542c805012410040402c00034201c2601960007201d01c6294610302600c0c05281c00010b1401366015401d0b400c116510741d2600e20300f000c0700a02414191007a070f42483c00103503150303d4080c010400d001d0140c07148141c0854001441d0865400410548107859403907980769030b03943c0954082c1d000e40000103000c150a28020f1005041c1159191052954510090160501465107900703006190b0403601e007c580000341c80400b0f5030580521030742d5503404412103510507588812080e450782841002001c200c0d0700c080901d904140c07908595568070018000700a0b9085404e800fa40e03c42854500901203a800580c1d10340388c400c0813410160716240908841d1512548038100920f50013044800c031256180080d040000c5a0400080c40c410352003a00021b07140d80c142d050034a440c1d0000988400d00318209000c00080650094003150050303000d0790204240d8941c0e2800b901d2400780c0b078001684c542d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 897856726 1250 897855476 897855533
    0x8030402060903030318010b010c030c03111207060e060c0c1905150a050f01050603160507061503150609020304171305031b12070b04120c0806151201061809 69
    0x9406d0440069100b40c07500204458903509005594030191100040d01041145030140c0110f80500b04810709a040381094030281d100004405a41c0d810071242039850716664101000c50003000c00c849a081015080c5a42c2010b5610803480c2d07075005280440c4c1030015a4507019010010700704124403442103802414010792800041590050201700c41010380384504400015250919004481c0603015040030b0000305004040281c07400c6d404403504440bc103546401c020380d03010641420202462084c4207518815003490314030401e0701c4558002c05141131040040c0b00c005003005c4040300d40104028070460316040003182c903600d0744295600480d058007070402d07100c3d1a5000800094004c6a040710800e20580e00c0f00c0516541d04054007898181c01c03000c01081c403400410b20000ca00c40b520540e08080320648034102d03d403c0040030b94180f0004958400511020720308044030034400d0b1403041c020481c883c0303011000c008402c0b44202299449594203802c00611100340e80d8405000210700c007904646 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 897857976 1250 897856726 897856741
    0x603020a24080f0a09050304093e1602060c100606030c08130201211107060f2904090b0903030603073c12141612080304020609030303 59
    0x1c0c4140300c035500d60300409905009545002d000e025000c0c00008510070803e5aa0300c0b090030042c0301410b4250792600c014080000d44171114040c0000c020007101c481200d40702403000506420070700140c80011000070707404128025000805461081e03c2200b180400721b041d90001c60241c0c850812211228003510040201701441900640100c5d00160307000c000c042c41409023114440e01c2520510340c58030b10010103902562041e050030704410b041144241d00e12021800c004220703000c01180140e03007440420000180044c0d4400c400d600020510305000b1554030240c001c550b42d8486481d0341217181542d80c1584141c403540d00a58a0a6205030f031001a4101122296500c0e0000c0380d64620038800c4401c0880c0c00036031002c5400c03503102190034803518058110815940c1c03100c0702c100200c6071549041d00050941c000340c075030314145004000180d0600c150203c000c0c1445d00019407601c890082da202000481c0994002050036600319103029200e0b04c1d14800580c9522601c4503240d0315110201c01e0010740d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 897859226 1250 897857976 897857999
    0xd110d0c0e09180a1401021b070f060f020c012007060e091008340605120106030b030a110406030204020417150c120403020c060412061109220603020a 66
    0x503000b120010302665030041c001890025016103107800b80c11107244080060030040001d0800c2103d90005401c01c40720503000c42803115070301c45103045988203003000c11020f0441c01c0d40001500b0a464407440002020130b003c0e50718984142903d04114403040c880d40103a0403460881200003849091b28601c965480c802080204800e05161160844d640070480742c0301c8441098040760801c0018103003803001c0c00301c02400460031007005103a4030940f0903c0e07400340803401c4040d00507061548a940d15044d09890800d10844141c004600f0305180544d410b0103035800192510010390304c1102c1114010f40351012a0203450143e03c000e41203400800d01140000411050101500c0c495013100c43d51003001001410221064900043c4c0782030800c030f00d00201309200201907206000740101e800001035900802e1117a0b00070f61001580d45d0b5000307003240c1008501d0080140219001a465050040110004020404074802c10b20419030b0300400011801094214400840c3c00411140c40300b40d0340d1358040c55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 897860476 1250 897859226 897859247
    0xa061a0108010807050904080a030e060703060311010e011b02130c0c030f0503060a03030e0301020c0f0f0705120c012a050109020937020405030316050c0d03050d110d0c 74
    0x2107807226002044405002401004441004048400a07211511440000e60040d841102003644500c40648000b0040006500940495500080d40c43c51802d01910700e101caa05014104040d0f41a03400d0542e83c021404041089001e0503100103500e688001441c848402800303085190505a40c3e19409421a8004c0607a60294035060480c0d01040ea00301d6a40c40b0841d5407507804200c41c030f0b041c8086441a0344c0c50001200103000103147c0503586d0140d07840c2c18090f03c030882182d4408250000000010300003100104002c0d501e1270550141090307200e0b140e04090a0b11410820415460580100286c5659005071174004c452a0054002c1c1065400382000500aa0007241907501050b18040014a100d100d028a800d000b0101c02d000070a648420214004040040f034083c400880e00c0d0b0303014070040c003036209210580040900c0c0d9141160030002c4071401284186841d14011002c20b4200c81140d101c0c01000d00009203074102c9025405036805075007100f6510030310702850a0003858000c0b11502 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 897861726 1250 897860476 897860479
    0xe010509070b03010e01090507030603020d15060b040e0c070c120302060105010206010f08060a0e01110f041d01030f080c0a0c0905090c1c06180219060e0d0807140a061a 74
    0x407400758850002d18000d2100f84a2411141d50100c01000506141c1c0e10058022190f85070206840781d80384c00180b00f80c0064001610090305c014400a070048080c800c2000802000c40c074941084c0c5019401c0b119004020000c0c0e201400002d4010104080c1c0052000900200a0b20400d082e030070303080081d40e0700d009002d5140540718410010440c0441100c4940480d08244d0007030042e0354802100300050300b99040c070840d040d03417520207a040e602030400c09000041075280d00f59486078508101c4064100455000c0b900701e00d030078070062005c50855006921042c1d00551182e90715040c1e10506880c08518400151924402d1140850300081c9604800d001d0704030002100c11b503151aa00700074100c840c8010a11003214510720701d170001011500401003a40c41a40c402000100302d8010804908076241000c10b202030100c1c0a00c132150704408002e80300241a2030001e40407402d90307101c800904c2100d001600000751801c100450380410071001c5c032000d50110080c0441d014014420020444110b09603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 897862976 1250 897861726 897861733
    0x11130807090506030148050705010b0a1d040812070c12140d1e0606110607090b040308090f030a0c09110c0a080306060c0312072a02060a120e010509 65
    0x1419900c0c0500a034030810035100980300d0450f0520780c44061400c15401d0349005c0c00340081c074000316500451007180c41d14921f501c40399600d8021b0b1070003074216000740034214814414504203110421002c0d4060080880030306140a1075180c60510401d24011040c002035011411420840381640c0200009489441b400c0d03540c141c1400c003007080c0d40400d1040d5450842d84400d200283d01c0d1141600200c1100c2d0780d65404003440b103003c203000c03004c0c1c814a401c4100400c0c0c031400c1543c105602004403a61051140c074015802a0510546940d148694030010f800c2c40c20224060810703943c0d042405000e0780e00142180c41001c06454009404080b601c259204a80303048000c400107103000003281e118500d40409014010b00325036504c0201c0e04041c02032900000180003010707510380100010407071001c410200c600030385060000141000c900f009111180c0b1624030050b412a5004802d40402c254112407080d20380c03440c80b00446017010360702a2050494240809121040d2047d07029500404d00001075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 897864226 1250 897862976 897862981
    0x2505010801050402030f06011202090301180c0e010e04111210060312031a040914060408030a05010603060b1b0c04061e08030702090406050405160602150603070f09111308070905 78
    0x1c00c4200e0001b20b0784101068850307400078500790720404030145503180c0078400604101c41407000c00e003101c1601240d10044401ca407006018049095689001014440e64007003103581082c4a2403440040500010b201707980a0001120f40c1e41c413907001c0003c10406d07804031000142180c6e001c4010f0401e41c8000c0c1c1d80900c2c0e008810003010b210307000326464080311020303071400121100700b03020040a080130b06682c0b160003024000b5840344144480d50160b401941d60baa1a818000c91010458a042c0e01230024185003080c10840800307654280c4140c5000000104041c002018200d0b00f40700100c46855806454802c021505100d0705502400c02e01d00105002101602e401c080da0383c0340f10b4204041c0d8004121000580090f03940d03044950701c01e214505075800801c2e03008903119800e005402400141c0c124125110040785c2d0548455070140341140280320852800c211110001c0440c0a00c00e12940c030f0350011813498940104072580003000c0c0010040c030582c1d601045444408074000d251245060001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 897865476 1250 897864226 897864229
    0x131401021b0f03040b2109060907060e09010b0706060906180e01230c041a120709182f070c12020a06030b0f181b0f16020102250501080105 61
    0xd12602c0507880c00d0040d460141421111512a0041e900814104001c0840a0070f03803902c546e891406030544000401903030401c08480d0341800e4068100608002d020089130140d6550381d946941114401c8581c01e40c1e650f414180300d4058050794006420380c60801d1000511012101d800c1c0004905801080060300401c2507124241d0300d036925070140b040c108134080b01140580313144964000701d100d0340c128907143e9111020f078444841c01001031305040e40400c0381620301004a100307035440211854104000d500b03110114210090412404942550360008200c1000396581034101a07048950750800b07514500d0300d01c49856101410807912160100400510030780302800304022503500802503ca040d0070302074120000d001205910303a000c0d0f040d00e18078485480f00390000d45050103050a20b200391038003150004007105034001040c03d01c40200070804604154070195040b5825001c000c000455641c00100c0ca400b98182c100e0710100744202c0c0e41900070151000310000c486003a00c800d0b074181e0baa0360 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 897866726 1250 897865476 897865483
    0x60408030901153005100501090501060f1d011b080301170f0d0c06060b070c030203060601051812030f0c0106080d0c03020c0f060438031e131401021b 66
    0x208281041c1c4c0c800b080120240f8291040e011550452000b0780d100c0c580b1074035443c1c54103460070004014247e803480188010119802002e02500e2141400c904030300e10224002c0001003100e0321900c0c03650140d283c120140c2c0c803030110100220302e9001105209402401c1c03080340769000f0b202c0e401d40001c4603582c2e861151400305403404a010540094000640380e0b00082c2c4e20000004000c50b1102d690f00e00116110380303042c0180038042d0007951803980850443c814146080006003d03141440320130b000031403840b1074910b1100040d0300140d58400c045021841850301c0c60250078052111640c02082070000014150310110445000a00320345030398507901815624019010360190060b00a40e04501c054201000080005403018081038903250703840040040411a001074500882805070f14000320b01c00c2e1090b401c0d40da44000001a1440c01c0442c0100e08483c00c00260030314a140100c0000c00e45820340341008952504801e686846082d9000c41d00e00039880804a91700c4c102260384c090031540c8000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 897867976 1250 897866726 897866729
    0xa08150a0606080f0a150b160309060e060906070503070f050d0e01050324010c1e11040e03120c09060403060605130c0e040915060e071d0d060207060e06040803090115 73
    0x10768991584d51908454400070b000d00b211b005d13001c04143e29000509038800b8000304960080102440d402c04c0c8a841d009000384925800f200401905000d40c58a42d61201d04641d62400c0440d81d9594658861502d04e04502501001408100000b4003010274000c020a003595000b807503503208412285070301c0041d00c00740030580d4540d001070b18080700303403071510000a08008020b1050520740e10300449175469429101d0781100c0d011901078485041410400301103d0f40a4404c0300b01c40510003108008580c81c0d480c003544c40c0086046002a0109009080440445080d514007401ca01d6445031a130925102410707581c170403d40500d0040d01c0340013031701c0d45500c0758a66030b10352503a40c15040381400d400c000281800f14001d039004045020342e4407180c52144280c9000b001a100d4030b80c19498a4031003c0c105107000d180345e00c40d0f82c1040e04140c090b60742d03c410070304d0320b2036100d100113031240b500c2c0c01d00c00c0060680c4262101c0742d20034041032105000422014521640c0c2410081c0002410700800242a4246 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 897869226 1250 897867976 897867991
    0x305030f13150c23041503061419090f0b10020a1a061306030c050f010906050f0a1106041505060a03050a0213020c03040e040320100b0a08150a060608 66
    0x8034650001e1184550041000c105013842e203016862500038601c00ea500200107441c1100c4000101080310828046041003200b03c58281048002e1502d480400000400c1100300e11401441c440c038062516001100070141c0781c868801c00c01c0c254804168002001007001c0c0e18410000585942c26182c40001c000c901642e101d106403014558146001c80d174440301510741c9a0090440c1309141101080b8800e440040d4025241011507502d8030062020300c00c0495004c42c10848110010700883c3d070060103c03502c283c61428100d542d00c0c01d01c1411280c1e0020301071221502d00480f82804144944096687c400107050b020400180c0c4a440070419810750501c402001504190711110151800c240c1102a0000080780580350180c0d640e02981161701c1303900001d02110a090901042c950b000074900048568020558912500c54040c29a00e01c880c0d544030130000c1e21401d0f4601a6102d408940008020300821660001015040d400a0794004c03a20040058a00345000a0382e034814114113001d000c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 897870476 1250 897869226 897869243
    0xd1b02011b05010b0d0602071a13120302072a0b1e030c0705010e0a050609031c050402030c0a080307060e070302010c080a020a230d11120a12090305030f13 68
    0x21802560044208141080c0e880d5544d540c108030041e11352130300341d4402d14400c04005a0312030103890b0510402d00300c5100e00500c0b501c075000f0041c42511100d00840c0090f0064582940b126003140200d0280c820750900a1040c44401591901e00403102c10f440520321201c240e680d000c42d02c44882e00611b0180b6860200c1a95050303004406030b0020b20011500003450009541c41d00d09192201030a60b030650507081055805810103500b07000c4103020b5160028180c0001c6c525080356044080c014031011903441c8003150b40e4401240456400700305c40c64102c207014142c0310500d40e68405040d00d07600040804d9900314200124400060f802051190a81c0d074142c440d00d251074216194200f846e0000d0203030b101075110300900000800c01400b0103403100000641410006000c00304090704101040c60500107008642c0f444040c183d0700401c10140000c40c050070191a000d031140220741900f0840c0340c05903400d103040c0c1d40c3d00c14140e00030001d5200d0b92038207034041416103070880d514544a0541c0e40280c20400c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 897871726 1250 897870476 897870497
    0x1120618091112030f0f1b0604150b010801270f02030601020f0a0f06020702120303010305071508060306011404141302010f0c05030d1a10200a0804090507030213080d1b0201 76
    0xa41002c6d00007035000040c076a060111310403480c003440581c01250042613101c6d500300010406400281403280741b001000740040c411460028290032418041c494840324440448046c030113030403100850000c0f203894284034025189812000a5000307403113b6005015001c00340c55405000034135100080da00440c202c0c45851540c480200075000120101c0c1d102d01c052400da0a890800c102540c0030b035014001901030070303183c129a0005690154581410310480d002004030fa0764010440d141111918824019110740107800900200b030080b900760100400d20080c0100d03d00c000a000100e24401e0329000064120b5840a03110b1b0b01071301c1001031180d4000c02c5454804411030b0005441c01c141148480e80850301040091441c4103108111000a00c43c0d01241300014a59884d03400d03900c90740d1000d00384008440d2101c2640f88600d014000c400c40d00c41010904843c401e42c11513403001040c016801c03040c4e459440e0070f602c81007002d2001e000102100302650704204d4162000c145650305858814140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 897872976 1250 897871726 897871747
    0x1c051506120a060b130905060402010c0203030c03220605040b030c0913020f13090605010c20041d100218010f11030f0c070f080c0112061809111203 65
    0x104002004250403041102030245507850070072151403094882d010201e950304009091103280c1c825940e410344000d040c00d840201143c80803600a810a40a1800f071482e80c2450003c81c2ca940b00c1d0840c503201922000883c0340011300d404903507128420300d0307010040000e0760f610030403a25409140203190f0003140070408500100303c80300041c40c080b10080c0c0408500803030101d03043c04a13041003800300209000090f0340034040c0c0d00704180340050401280d00f00282810000000c0503125500c0c1300421035140301d1500e202c115001242031099882c002c3c014403441845120040e400c1083d1003c11045210f00e003040411507126009481703040f006403c40e0101d8100c6180111a8540c0845028090202c3c0c0440b60040c61010b000520080500040c1142c1d20034400803614030f05600c0da84110f04100103020b040c03000c06002715070503d02c04070034030b00b408078400001080c01c02002d066100065080221440851110705a0041c2607058058a0545004c00105090004517108102031141541040103e15502c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 897874226 1250 897872976 897873013
    0x403050412141027050c04200c0703171602010c020103020d060905070e12190206040905091c02010e0607050c071a0403051908030606090d0807111c05 66
    0x2950044502c403050401a0250a00f001c000d91440c480f001c2d2544082e02c45161214200610b800c10030b40c25003122400740d2542602c81210003e40c0d1b03c20390315011151a0112603034444603514010a011656a641000c07080c6e9889620b48401c55184490120304199200e07002c0984003503590404054a0021b019801140d00b040c0250040f414550b00348020154000ca611800001e400b081d24001018249680064450201c1c0302c3c01c0c9105035401c511054101d2408030303070740c4030f500d00003e412a20081e091001400602481e00300e0a0301900d080104140320308002620b0305481102c0704280c4482e25114012400e0700c031020b0852070640c1c09940400c8100f440f0b500101400070a140507584007a403620f507a45909034880007150600361020509101f408070038000c0c44842040301c008000c01481507a03c6080600004000c50b1040001240c43c0302161141311501e601183d1140d000d45e03440110346091142810810f4a03140140e03111120040c0d00610050500c0d42c49811100504a04200e0000d6144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 897875476 1250 897874226 897874259
    0x601060804200d0807421109030d02100510030308040210030e011a1002010b0d14151305012f03100f0f0305010c08040807201e0307050904030504 64
    0x10890707140d06940c804640342202500a4502c101c40d0b11440e80400064810b040c484461b0050441c11325402241c82e4001012085120000703004000c990454000111a41401040100c54240c024582601e012039404603159141c509000020800703612030b820143e0502c442400002c0200707180c02c003c540546031906001c24030300030300d1401040c0500c07480501030075101a5101982c3c08014500c2c80e0070310b490a0791980b0010001c80c4000c020003487e01c0f002a210b4003140d0300280c210034a015840c0410303c4103220205c10b10000301084441401e000c00a01181c142440781a26207501c0d084201056050850011038103030f070180402502029a0a2001c91540c406441d10030842005800000e80b403034810034160041c05140000003070140741d41046425504500303440c800b000800000c200020b440c040950f14100e800a20045034004c00c0d2a82205560100c00070301d07444080120310b0098003040108040c5c11180580640340c15540c1c450601441140942e00140031910510060001402041000700b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 897876726 1250 897875476 897875479
    0x801090209041b050405090603010c0f0f0c1e02040b0a0b0405011409100509030d0804120c110a0306020c0706030605061815120406060b070b01090e010207061409060106080420 77
    0x1941d01283c2004203100c03255541908045007021408010f90b02c5d01e03007102640800254020300400140e804c00801408641807100c051101c11801914280d215081c0b58145980c0550b041400e2146608180303082800c002c0102c1c4190300300041806141007044007070003101c40a14030380c0d00709428440113540081041c02890001d45090100ca9402d54401141a01c1d28080d511140c0e030314507a4034181420101c0c0010581c09020f200014000003a03104008509101400c1c50058101c9000f40341c00d011b0306c400c51340b0943c1d1122400e000070080c840355600508015503440112690540c3d5454250251201485901c1e40401e050080042d01200391400341110000200500341030781503004400d406411071840e0030401401001041704000c01840f40d00080d0100b08600c40c201540e41d5985140400c0c1401091207064442c900080e21750400d405803203402d9444042440404480b00d02c4000c4c1070b0b02101c112055124480001440300d000c1e2104034044c0fa00300e204050b050f1400008014003144500c84c5a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 897877976 1250 897876726 897876731
    0x201020708040f0608061f050d0209041d010e0f10021b0604081e0f0304062c1006050108070909050601022a040c2a0f0c06020d1b0201080109020904 65
    0x8408000800c041d2480d1400d0f11100fa0070b00034010300c04000188000d005082c2015107695101c0201901d40c9074520501e8503550743e05c400c01d0b00c03001074000c010303010740c0040c101400340c00d186151680f41c00728404050b000b0403550000c4090342d0340e541c503132042064094001c2848040d1012242c1c000b400c40a0348607000f1500140e41900c410328140c4100c5013030744c0041001c51101c00b1412404074000400c140141590b00304214000001198400904000c1000d80d445199000326a00490380074031010007091040c010301c1c440c0c40125191100484050742c054500100400d5a42c0a19603440c06003a0513500c0000c0c490800c3d40e010300801010704018150311800c2d20044804d166403a2010002e0302d01d40c081d00480089405010a0344d04182c001d000380103032242c4040b882da101b41314000b9000c662540c01d401e007505034180119080f84501d00900042c0a603407000c101d03aa00051150454541555a41c141d080c6156480c190705070008030007400168220010084814140c0103030003d10f1004000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 897879226 1250 897877976 897877987
    0x1409090f03040605180117070c050f100b090a0c021917031608090109150902010302041d010602061018020a120920040501080307121403090a0b071107050907020102 72
    0x385540c10581c401400100700040c0220307841c000981c40c1d00c80017003e080540141d1111041564540c4005203038000700310b803150f0f4110600900300602c1d547d1030f103a0780a84548084002c044d42c050804d15410a014070001c0000c2501070b80180b05030040c09006a000e00281078034458085110305523858181c4032091054110955030340c80c0802117019000891681440151100d8050300141d0003d00d4030310940d241c000b0020100b0b0001c0741503010703a940c2c81d40001d160900703880140c0080c002e58201c580020f001e807064040c0d210703509001e541a81d01c55000c0b40e400f0741d51220200da8854140c000c0e00155403050f2900c0070002c006401078000d145881c18404d05018201c1d0b81001100e001032070546140d001c1c0003c000722031702400c420b591540c2003030340c041c0b001c1c0d8180076030f542d500d1160200082c45a031518401e040000d1140f514104102c03142e0082580d241010221181e69100c035460680c1d9001c4204040b416940c00f40d1f4000420b4040640500182407808040000c0e1140060084040d55002c009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 897880476 1250 897879226 897879253
    0x20a090c0206071101141603020c0a0804140d1a0709150c2a050f01020118050723031c0e100315080109210306170c030d020601140909 59
    0x54280804441e03000300018a0282c400420b0540d0b640485501039250110248000b03203035020b080e42c0304815540c101e00c85041030030110003d120f42245840d5a00900322004100202c40700100200c409111101522a010608011412480c40001020380a001c105402046900c11701a90701c10300c1760410762071a59543c1046203d61a0141c0107000003083c0601070002c008250400031010900000e0030110451100801c054011a5004403807240d40b00700e070600b1440c0e100b504940081954155801403210413031605039503c1c0070a0146005081c0f100c1d911200c2c44190111030306403144001c00506a81d0035502d4550406030a10008a08100e00150551180c1d100c40c1000c0d5038100b0343c1d980000345299141ea62000c10865600009000d034102005c200c0030502c6000c1c40c00180303252200340c3c1400d00020005030000c182c1a8000c00001103048000c0700760030b0300442c40b441c42e9041981a5a281410580101e031901000d0080d00014020000060130504104101c15849691142110640190700e503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 897881726 1250 897880476 897880481
    0xd2c03011d010c02011a0a2d060f02070b09010c080306030114072304150f030e0d0c0209060a0b0f0c0c0a090c4e11040512070810020304020a09 63
    0x540d240580e444104000e1282c0c4d091040d5890641c1d5040030800d08001701002414005940c400d2808003807409000c2a808610600d11001002218911000d00741d50b40101501441c280000400035004401002a1301c0c0851411210760000c160764002c04450180d89a80307140e00080c041c103405650302c508801040d07654000b03950145959481c0d503050700807100d00c07120800c0f803101011039000c2e50503c03007000300200d8603440b00319505250400004400e5980313021401420001e41903145841540a00009540c004042803601402940c03290044c1d07550074144814182d2922070a000e0b40000c0261400c248403400250418403054416a4903007001d11002400a01854114a03112a40d4489420020fa0422003d04022941003949580f03028880d00740c10032429480022002000c108101030a0329400380030402c80e884203440200009441d120850322160403038010b46020310507400303c0c10700f40440016003c04880e8208014603070246101c5501c400b030741000d0000c907007020001002040b44030850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 897882976 1250 897881726 897881771
    0xe01150509041e06050f031e150103030c0b07051809100e0a02030114100804330c1215121a0405060405010510050f010e0102030c07090b030d2c0301 65
    0x8594001c0d500483c0c2550400300c0740140d009502c070b803000c0414017a407605d001c04c22101c810f1403410040160309800c0e85e141e08210070040d03110480c030b070000004400c25412001040481d80030b4004020a59079400007a9003a1141203201940cd16110b582c180d01d80c43d040007200c1d40407402c190700304407159440101030a2031005641c0d010207150080018000314581c42e910000103001200e050210041900c00607028000c0a03101030181c0d030201c0c8a40c82d000041c0051280380c3c100100b180011101c1410301e920040c61029182c200082c1d00c10340020170f0100500440c420803484d0303104035003c1e40c034120a5a8074131440b41011030b10201c107003100c8001e8010841c0d0940c4558020005000c2c0791609141c403d00b19000200300c0c00c08855400703c00d01c116102d960794603900c43c0b82800c1c04154421010011b034990300400901c103546102c1d800010914800e41d400c4050a54016000c990014132045400d071164070490700020525a0041c2d01f404400c04c0318000700c00c0c104006000000c04003a20038000350170b80c100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 897884226 1250 897882976 897883001
    0x3110d1407080c0907021501090f110c0a020109060e061206040e0703050307030f03060b030c0304050a050706030b13141603021c141602070501261e010f0e0115050904 73
    0x110140d4800d800c0c400f1115071701460510244c492001d041013510650401801819031540d910a1113500366030141d80001d01c1d0400344090642c450340072041c4290341e0025203000701d00051a07071b0b1000031480d01903c0441e1003004010030441c200210106401d1500000074042075000c2e454004034030706201c050004030080d5008034042c503604c84907822301078980150341c99040304140c83d04008120900d040001d481d0405500d1400b02d40e203440b00d0a06038540162040050150300445134002803443d05039022103000c0350b00b5600f552110342d20041c80343c111a5101c01034505500302900051040418894900100e1081d05005091865a00c25005840200c0400480499641c0704a200341041145056804100894515001e00c04480d009440398110f200d00c9060151080504042c0501c00c07000142c8058500080703403540c0703809e60300c0040d0000351700c450170b080c0304074000041100052101c584050302c2e2500121012640782c40364072202030381111007440400009009181c419501c038001c03400d80000303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 897885476 1250 897884226 897884233
    0x9070203040f06080601090603020a020c2d06070f030c021203040605031014010e090601050d111e1201030f2108090f0d1d030a050a030c03170103110d140708 69
    0x141102c00400c00b005410090070300c078032002040080d0b0ba1050680054034061714000d82c507404500b4099103070801c0c1007480c0303134800c618800b09c4080000e9008401021143c682900030b604e02d550051090b41c1c03003990340181c510404418030402085c09406c803890703040d01c0608008103000d00c0d4009141560010780000c4000340c4004103104040d50f2000243c00908110a400000142c2040018002c0f210440c20107014101801c000b4945a0040c0c00b942e10308142c001c0c0600001d49400188500799121402c0b215150320340000c808664041030050700e0f40340716006241c9010364219165803c808850340c6d0100c80c4a10040714032010400352a8030010b801c0101e03111118203040c4007100c60304110240041d0340180d0301c0b4038038224100c2e40c0b00318010100540c03401000c4100311608003183c208001404080c010348265201c1f07000705903000000e208401d000340d444400e00040b140c4403121156003807201038041595090b000142d468000702503a80c0034400c0c00e4606c80e001c540b800709410201186e010403030729007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 897886726 1250 897885476 897885479
    0x304140f010209031203060321191119020907030e010b1008060108090f19020409081201030c0e0105011e09080105090d020f010509031c1e06080c09011a070507050907020304 76
    0x6041050b0b0380b00c2d005c480c07401c03415440d017030b0007099651710742c1a8a114050701d900383c80402e080b003c500311181e049503200c442c4202400040d002e01111b000d14046070803481458070001d142d03001086003409499008003441c140307444180b421006064242c4481515550307940101d1900e41e200d11803999480e00c0e40c0c9409620789007280001d05a681c0003000c0740c245411483c8000c0417004041356030b01148034501282d0055440038000f10f401080b21b01001400c96100080542640c04c0129010341200c1c4122070340062039071240e510a45a4000384102404620948555120f066503046600304400d100e191000340c2d1565040518292401a103a0326110740091541c441100c2d8140b10301034040c0d03030007c02484103040100301a55039200c0d0100c06001e0b00e2008502000901a9400148103104680402c7c404042c0e50760046000300f6162250300814810760f08500700307a04201760b6003412520392041040d20240e200b0040f4100c0d40c4900001ca4560107550130100391955120501c0f802030f0002d078011a1602d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 897887976 1250 897886726 897886729
    0x71721091009030f0c0507081b090709030b31060e010b030714300715020109121d030717010b01111c03020c010203042402040f05060304140f010209 65
    0x40441d452811540c00c040e541e0300425048440307104a003100e0303d00306004036014200300b410502c10303401011250046260314200390f95200c0c00000d1181c1c046410701d5180d195500181c0d41000980320007090000b50000141c0030010b07540e41c803125104d01c6c030851904014030511500041c40301040840c0e07441e5441b0281c0c110042c017403142100003e1705800402010b4107021120740c08183ca4008548184102c01510b80c07802554041c1d846045800501c1040c0405080b003055140c0c079050181d00d203505041201c0c0405944140504404a40c200080ac9425540018101c6806800c00304a04081c0d411003000b1540f902c0c100320300c2d8006d18040141c400f26041002c0b81d80d081d1003c1850042c104041d030110203202000108030820340d00301d503a8800c034850744801e0060f0701a010780a030300012544088204018403603546002c0011880c042915104418460341c00d0080380200d00039800d00c100c684005000a041000055401600561000050f01c1d141a400f500d4038440807100714540c3d4002c104072480c1d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 897889226 1250 897887976 897887983
    0x302010f0e120a050c0715080a060b030a0506060c030706060e0c03040210081e0403050307090603022a030909010b0711100e0607062c2107172109 64
    0x1510086400380034901d000705030140c2d2071410300b04408a003080010994011405032089805050116060302d8145039103140300c024440400358480c000c42c50400c0000e064017894445c640a580078a40e043d81181c0750001c0c50001014020081e44d0080d0080055041d0200204090702d04d144c45003d0226a95017845e008510948016015a440b0842841800016910440700203481e0400e03191004441e41d4501551640e120b5825051441e02030041c10b0105041d440401988946440e8940c03443e62507030b40c8d104034104c0c80f1312209022100311a0004210f1040d4120038804020105012a420a40220002002e4160030ba004e510340300070004107102040b0b8600c44100390008200e401d00c1248100b443c002e4000030b41a0100d5104010008105040241c15440f000e84482000008618078250072140e04000e01e02c0d01903903105104001120ba00f0944136001c0c01028012035500ca420710340079035940d00d0310a00e000c040b1004501c051007001044048074038002501040d03040d0107411800c1580c0c907a4213 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 897890476 1250 897889226 897889241
    0x150303030b182806120803100e0a050f062b0305122701020a020d03110d0608060601031812111002030c0a031407140d0902040f06150219030806040b030d0804030201 72
    0x104241800ca0410031716091110f680e0216401401d070942c1c2c0d0381e5004072842000010307003242034000028014007030224003541c846489840780e10f010709181d446020800500070700504000c5000254058415002c000300c80c1210b00c046e201c0d003800c905040c0d100484a2228004558100031982c1b800c40351244000c0070803c0a00281102008610f0000d2601c4002d4960100c6030041040c103844511507400c0310000c02c11208513180003503042010548403401c1686881c015a1681c1c0000d04044c000b04000700c00101807c00164040c0c000241c1d400c400a0549183d5607401040040c0e01034040650440c1d0700030b0008500c10000310b50016501d2484243c00b608443d216001c01086071501c1080284640c0c2180d46800441140d21180c0e855100700601c28000c1c2007001c000039001818403500944601c40b5410203015944005146e12a00305048412030340c902031003074848500440e40c00c011002c01e000d05503040d0426000b900c0132801c40c00e01c5000c00c0c038250a4401500014420030200018580c0c280305115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 897891726 1250 897890476 897890551
    0x20414030c1504090216060f050a15231f110607050c060403030b061e090915010f23030c0a121503020625050a0b01050103150303030b18 60
    0x8140c09030b1941c0c04959801140034201c1e0340d9500054401142100885e0f141200f44d01a0040c4070b440f807070542ca64041c010942e02c0072009410200c100802e8210b00c40f00c14141c0703070f104403c02401d034038844e180c0e1001c0c81c12960940d08003204400c031074924031980c00e44080b00883c946450200c144000cad0310a19001001342070f001008001c0c402d6002d040c601140007904180c161602142c41c07940d200010305e4030b100351010000030035242c1e010803648080360805040701303070741c226108482580e6002038101e50500b0b60142500245645c0c0022440901034a180f07505460300798a42d20000b08240212040c41d4016540b03141d07100c2000c11500c3e00710794040380489054a40c02814007c890140601c0d401c84421804020712039600032500500041080c040400c1501a044400800d101c91b82805a12140503800a80f032041e074070300002c40c0710f500030302410f540703002c8520b414420348d0325680717048004201411145912410a206111000c00440c0110380a540c25107440001240c0f01d407144001e04241d01c4001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 897892976 1250 897891726 897891739
    0xf020a05040e0702010c2007091b0905040b2218030c0525060c030509060a090518041104021803010507050d0c26060109150c02011403130201051606020414030c 70
    0x103641c0d80c0e441071150351080b0b40c0d406200b40221f0300c004643e04051098010076142864070ba59146280d91070101c030500041c454503060718082d00c90042c0020741d200c0b8940540c00002103503c1c42007422140ba0803844800800c00c0000d81444014025551040d204000b5000600c16102d02030610030b042c812005503010410002c00042c000002c0090010703c1f03440348100384183d00300c84034141801402100c0280c03100400044d56065600d038060100e00681c0103242c01040070244140c0c0100070b400c01c050090f500076030704070142542c4004001c0a540108895009021b44003e0000951401d010b0320780902034580b5070341d4460b00c1d00e00052040702d101565030010005242e81204e0300b58041c00d803000c000180200148003aa54520068807004243e9204031100c100c2c284001100d16800711026240a2003640d034050b801c204404590590702040d501c07592101c0240304000300540c003a500421513000312803140b11220001e62502000c0f6082548444003004202807203000c030386018480e4040f0b01c1d000300c441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 897894226 1250 897892976 897892991
    0x5180709030b07031508030408160f050f0d02030d0c0204200708180a0f030c0509160804031202040e04120302120f33010e041109010e040f020a05040e070201 69
    0x1000d422403480040c02e80809200410003141c440c4e04000714111a0801d072100e05683c40c25900d0382e0b64824443c0704103601403144114682c81000c0c03e06002c4460740390704841d16038180801c002000701c01c04ca60603400280308034200f0068400344000440540c0a0311200b6070029140140015204880818005444603040d0900401e00365030503240c904e40c01c41c3e4103907107035020324101c5c1100c0009010b5281e409848400d000451513241c0c2c8031801501d20074441d4254160303654084c000131210940e110042c90f00d003015210b12092040032142e5215000380382022002d100e03100410200c0c0d01c150020151200204100001d010205804c000030f80703803910b0110710b414008a0815940c040150504c5000180b14021842201d07040c801000121166070340d1240f02451455081c85440d1a904c541d80032070722a0b03500918525080c0306c0c90700000c0720325400d10300c0c20a0354401181c144828074803892b800740c1d03030301c10000c0d00c1c0003140f000c0c145160340f039118150b8881c100308006001e2540201050308580c1020032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 897895476 1250 897894226 897894241
    0x717060412091d04052d070f0e0c030a0b1207030323190c02130b120609030307031104170102070201140414040b01110f1c02060f061012020c01060518 66
    0x10743da00300a00c5607241051030700d071071410342d080001c1e01c1e0355401c0405880441204011000282010301c051820844400540c1c80360307808041c0b07940380700e05004d01d00c0c1c2900086d0041c00d60401103070b006101c2c0c500098035685900018405140100500c01d156100703200900405820046002032011840000306000d0800c81d058101c0e8452100750410410015104040b99070149100901d40b940c024003c00403896884800002002c0140c4464410340440050f0031001e45d010aa46000712240800380d40756680e00101507000c0c100f043e800d01c0000000304000292010185031441c90040c0c0000050703034811190000600213a035161440018510421007082809040c45030300310000c0045d074001c60852801c1c0c0058030840c091091050050003440d90110b01c821000c00e1a180101260390680b5842c00400f01c01c0b6a108801c498518210380d0240102c1c51518082c0001e0640742150316007801030151050700c1d002a600589401d00180e911075200b4491f525104c041c02000090700e40c00e2000e04d01e040e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 897896726 1250 897895476 897895499
    0xe061216050607020102070801060608040b0703091a1308400303180b07050d121806051f0f0e0c1c0507051611030d031b050903071706041209 62
    0x100c1e0500c6800000ba0754011a402400000c0040c540340000f00401540e810001c2d0105000f1141280d28a90640008040502902c5050a026001608000d549070b00d9404401280d070094890011000d4078001d8100042c0104007c01810700290351650303225103d1122850a4400022030952007001d00b02e41c00d400c5417890401c041282d03010b00d4202c0f00c0b9041481e000c10500055000700d002c125000911a05106c400900b00702080100d5560000805c89070543d5000c0310145520845051442042400450a203802c204c0c0c001d0b0203080c1c440000348000a60903e286000e41c85440b208108410400041c0c1c0c00c10b0009074410803a0240a140000c0400740090501c0c01d25800985541c3d6280402c11440c8110700380c400301c02c66070596181004950500000080250f0b0a091081c071441680c41d100c40e03c079004400340000014440484002039501c140e4150300806601505480b0300070001a224451a015200c10f0325800701400c4181454101800c03120248103d075003d02ca0f10304002c009400c800d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 897897976 1250 897896726 897896729
    0x7170d030905030708030a02040f0311131a0607060b040207050f01110a08070f020a080a030207060b04150b0a110a03030b2701050114160305030f0f060d080d090c0e061216 75
    0xc1003a0390b81f82d403004003103002030180b41c001c40b078580072401d800700401050100001600004580030410200850383d0fa006039464011035400b07222007200c207140581080f0010b0140d4038814280403c081501401107012a00722520945a0f4ad20070721a841b15601e00780b183c21880711140003024074000308164054101000a010315042094600b0224416442481103070445075005440507074130800c06800402a40000000380d400710300d0701c40c010910340341034454000d04101c080b1003855070610304000601c19400c0b0101c04000d00c03142c400315680754581802120310480c400d8a0015644414405014a0814001f41c11029280140c1c00d400b8501c0c0c6a60381d107044802c01d10f05000c8450407a42c031130f41d0034050704074142010064520802d0405800c40003851082002d07005050782a550240001c0c800801070f51640d800510414006011407182c0f0000c0820344451440880c402c0800c0c1d880c8400040907030701c054090700700a41071000924080c50200c06070440c4070300410030b075070300009140ca00f001c06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 897899226 1250 897897976 897897983
    0x605061c0b1203130501110a1113110a030b0d03091a0417070602160e0114010509131e0c17060406150201090c051c030806060c07170d0309050307 64
    0x105060030019401070300815840c400150907450344030440490955260000301c440008281c0c5940702241d0707944117031600b001454400d0010711002c02181c5521040ca0105015190001e942800215071480306020f01d0224a1600705055600d850b803140c010704482104015520414400c080b40300400d80c000c1c065420350391040400b02d481400c3c100c0e003c8040c4956403180045080f029800c44080d60003091520855105400392005040c07c0f0403484c03402c4615001d01b00c0110382900050210403144072100c105031b1010b04003145040034180004041e000f0380c80c46001d00d6521070180061480348030044841155070040240b0000304c107014050905001070944640d0b0480b070100064135640e8903008000203004454600c1241d500c940300c000d0107001c07011030070b55060a04100004090400003028061030b951259001c1581d40076580807102c0407009000564010070038401d01019403002d000d40743c020b1407591440140407c1c030050316400e015001080f007050515001c0980081980071044903507d990 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 897900476 1250 897899226 897899257
    0x40b070b0603070504090c05041a03030f2d0a09060e10211401030308011e05060705150109060303080c04050a12030203070b04141c090519051017010801060506 70
    0xc0c0c00001c2840d1421036400103500c9804c12403480c042c447e82c04901015154244e905114100700074401c040381005581e6840d4044c0c1c403c00200600c160864050400c019038031b0140340d502d00e40202000f03125900254241703040e0400182200c1d0094110381890014015424004401c1d10703840000b40d02c0001c150304080500c04081c0b1a40e810b80304051044c0c801c413800d0003040001c44ca4080c242c590800c0e09000c100d01241d110300021804503401d0301c2120311401010008010039050a09004845d00404c2040383c4501c6909900000c444002d00090f002c0d10320203000040391741c0b031802d0003482450064682c0b140034030300300018031240d200d01002e0400d46204803009a80546286012403070740c0300e8250003a081222020601080100b8141c0540c1d040208004a0365400b104502541e03130788212140d0200801c1503400100035605140342d80403c1501c05c2c6080f0080c10f907550001c941d0902c6025200c1d00002c0c0105140d169581a515000d800340c40800001c0101506100c04a8014881e40700d81e48807040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 897901726 1250 897900476 897900481
    0x11d030901030c0c170309060f061c020d0c0e09010c180605031017150a0b09040201080709030501020c0313060903030c02190503030a020c040b04090203151e0129040b070b 75
    0x14054130000000030350201800040e68100210305109400c15138008080d40070303020104049880c010040e81c080c080091500080b00aa002884900703038a1000403071f04909107003101808070b5040d0b541c24004103050343e032400081c50711460b80c40c21555490507100520504060f00c084034400100e01d60b041c0c2e000c60601a6480d100c02004442006040d4032070300c90741000e04c01d58084503d001c82c2c3e200303030060718030200e50098407000303000d02c10303078a846411a4020b00d9580020300590b1003541140c0c2c0001c09030070601d41598982d15007609a071701171030321150161300c005a07003240c0310302d0400320100a140303d207001c0c10014110380d4020840703000400d02a100706a43c031320000d144482882c058000703241c000d040341e9840c02c2d002000380d25a01940c0c1090f21036450315800f03440606050062041c0607078018042c4c0450626507096030720305000600840322184180b10208903204401c0780c058060007540480e00101a00c00c40300200342c0340c500c400030788060030502c0100048000382c000d880c4510751084402985a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 897902976 1250 897901726 897901751
    0x702191202120d020d0c050316030f020c071d090321090c040e06040b0a05151903020d05030d0c02031e070f0b0c1b032115060318011d03090103 63
    0x1a00042d4150a2041c0003e200d20328003a843e40100401da01c08103040c0100072820006403160b0004980907001d0051070040700800700c1c0f081d40400b03021141e001300142801c00c0c1070044c03454461a600100d40c48500000e6801d07441c031800c4a45c44d40422000021480d0207410500e24082100070542010038103582c1010504040050000d528a2800904200145520602400e60300d0409440a40380c00f2254030200c0c030410200c0c0150b40c072449540f000c16041c80c3c100014030142400d404100c051821803044080010781d556000c0d40c00480c007910084d5121203194440e00102d03035a0426010135036004000710651030031100704120344001c08038000380d159500d6003042440c034800e2082c0107080c50301190410481c04507500150012284410584880c004c40005032581d1b8410503000174001001129140000c10704d403091154031440d05d6024880c3c00a003000410000e800584000030440d01580320694038070424890702200303089808282e81c0c1800351703d00e815140e00c41d140580f410141c540ca01c12107903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 897904226 1250 897902976 897902983
    0x40c12080903150a1a2b02060c010c11010207020f011b15020301140102070b18031f020316260711030f0a0906022107020a120c06080702191202 63
    0xc440c80501943d880a51481e80e00d000500100c038486005458603041a1070080c1540d0881d50140c005002031b41c40008211400c1203242c01d20384a0010081c036002804010784861014129842480b0004181c500c03442d1006170002d41841000b8449070700c14010940940e0b1082003100c0d01e4942800c010074201131080206280e020b0107400038045950803034081010401c1540210304070340040c0c01d2681c10700003510049840e000703284103d01308aa01030106140f8261486190b048240300142141c9414000e414011260300002074064000d030f03808420000645d00181d0810403864091600d00c06c0c2e5060f260120b01c0003050b0803103240a081c4a6030000e0121800303603000400f861312141c00c50352104901cad20001c079282e2112001c2c400240101d180021000e000080010960f001032b03c6125000088200c41403aa800c5180103a078060f1001d0340010302c14209180c0c001300035025a82c0001a1401d000d00034200481c0a80140308541c42800d0000f008003507003403d82200b99205001242540070110100d00c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 897905476 1250 897904226 897904237
    0x150c080306090a0b0405070206090d051c2a0504030c0e06090f0403050d1d1b060427060b0c0f06061e0d0b180c06031b03131b050406080105040c1208 65
    0x81043c5001b0038000381a80001308184141c5001003140d118506003101100d4501078001e400c0f82203111548501c0c1d007540b564014404010034680d4a00294107854107015180c503500c0650408120009800c0c030600c030450081c80003900107050340702e481c7e082800104040e400020019402000e09e800800c0405219500301d499503c82408d080c031000c031400346244c06032010f2a1040b505840340c0b2000c02185a0f5050000d10104030080c8042c0c10146494640d1005220f1a50408180031404001d1603032503038144148002b90101d81c40c41601c0d10b4404942618140100032030581d5035104604001803665a074215002522154100c01800c140c0500820b0100c0c9880d440103207400d00f442c00300441e0010b40c11074028500d03c3d200407110142d00785030612480b4801078802c0340301c540c41c1c40c0800610041e03d9000f15000304420201140004054454500d00c011110381c0b279200f040e000004006c00e14041c05014060812540200f001741060381d100c51112500780b0480c0e0010355204804021311901005850 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 897906726 1250 897905476 897905479
    0xf0501051603090b031639080c1204090e0c030c040f11040303050903190b04030804080d0f0b1207050a03060b121504021c050a060e101401150c080306090a0b 69
    0x607100e0500486c600c401040b07200e2400c0000701c90b20704140d07035040c0d1f481020f80c0c003090445140301c404160810010203002a0001501c8840c02041903c0818200300445c1040410001d03c0036100c90030035640310180d44014103100c0c1e01d50300c0141c81c000d41703a83c0400c518176904400c03900003488010003020172015012144103003080c160040380000a01d5000301c010301000781d0403410745c0e218075054001d204100e0201c1e0000703840c0401600000300024003400c98144c010b400741000c00d040038010340008041d210018941b02e1140e888856050306810703c2e649041c182c800c800050b0014500300b0010502a94080c0301c0a041291a1040700715252560f140800307030000c02c04c0580d0440075881d40030303010900054030100c0c0140d200003201d40c52000d0f844e952500e43c6038010701500c210704542e00c40e08080d2201b110000c869007e91100c501804035144502004840740002c8242c09614054052030301a003c030100c1010f000b1f52103103050002c0d00e03403021294460741c203c8030401c95445502c00074001303000031140301d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 897907976 1250 897906726 897906749
    0x110609040f0207390504020a0c02030613020301060b120c0f130e040c0b070b06242205030c0303120c0f0d0207021e1c0f020904080a090f050105160309 66
    0xc1131002103400221411451080e601484c4455548455024288039862000d03004001c030611040c9070940090113480071601c1d0400302c85242da00044d050003c2640d5500c00d4018404004085040c2800b414005040b10146c1c4c40c200a49280701c1d04000300018404051040c0000d5041070011004090f9011000c0070f401482c0d40a0302c911010105840a0380c06503001061070500040130301101c81200c005540c000140303003003a202c02050204010314031a0315803400004610380d060001400c2d018140c0700725122100e203c608415100300c401c00d5071a03080300b802600b01c0d62000300c403a2000070449250040320302901f041556108810415405196103542e101500000c124607004510f0f0080c00030039000302c81c6815442c1c4400b0000081000700c0c580e898102182054100d2202c01c0500784039541d038007464560802a00e80d0f8005550000103e40880d2001c50224283c504182d00ca40c1303072800380c46000d8010715800e04100004e803060140b0403d44c5d40c411804032840c02014400c020032402007100d81c2c10b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 897909226 1250 897907976 897907987
    0xc01080613113105091306021606060801060b031602120d06080c010c020f040c020f010203070503220b1803162a050a2d060c0c06020109110609040f02 66
    0x4016903501804480007289294012480040c49003800c0c9400d0501c109105a4010701c4e14040c402091001025244140d0741e00401001050300f0f1300082c40030030a29609100e0103103981c54134004550b219000444641e1400030280012141c2008403904100342020303000074002034401c01c9140c091350700307855484038201041c4100105046d81060081d21a0f21080c5c030060070a0800440d004010902c02230b60103401c415002c00076003002d41c414011841c8a106035003401e8404028140ad9034001c2d184840016000002c025550708104011041c80303d2103000c81031811015250f0b881660380290000000c4580076481c0b6503050000c104992254048001c8400071031400c2c28280034841000300e0b00900c1c00c0649190b02e982d649000c0c412070580381c004103528445030512254011444a84004050000c2800342d26034070004800020b4004000310b9880b0310034440d1900e4900405330050780b01d14190783c100342600d00020704150b40603d03e1002602c007140c880c1580030000e07000e05061010b080085100040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 897910476 1250 897909226 897909251
    0x50d0c030618120e010f0516200301060e0705030402012d08090607050702030703080c07050904111e010f0804031e080f0c0a05040e1512060717090c01080613 69
    0x180010050f004450b0840007041d601c100741c9280000991603030004002c4030140b00202c2c0184043c00704411200c0c444c151702561591444140c00c1d0895074200350024048100c1860f18090090b000640380543c107008490070000e40c0500b80f40400742c0000d041c041c04047c1c4000d00d6229821000b0200c0c800c2011b01140d200c10b48015100c1007050b160039540e07024510000f41c074640910300310340341164041c00410030986036449810b581c0c0c0161952840300c2c090380c44006801d07940c24600340e004a000c0d0b1440010039040e501000603408100300281c3d00312813a100b0b60003140c2c0e00104c035000f0008090400b0a01640c2e43e107005c8400c280000315208020380c1144c4659034203913000e44164480c000324480944161900001c10919024007030b510030005d01e082200f80007003065040700d20b8109517010190012450120001625195400010400d6520010412400e1548000700b0101d5113440004856030b410084000f580350950904110305000c0880d002c0ba0713054884204d504081602c500040062414090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 897911726 1250 897910476 897910511
    0x14010915060906170a0b120f0c030714060a030e120a0809030915130503012d110306010309081b01150911040905150d0305210c04050d0c0306 62
    0x221840184411240003190703450069941c80d0039240d01c0e481e124000580d00707090080d1030300300901030603449071156251501916540c405000c241c1080d40a89502d04030380c140d0303a16100c05601c41384d110394040ca07400c00c0300c0c030719004500282c400150341039035650320000702c2500640344403981d0403402d129402071080c0451000740a00321200342540c401c0c001e81c0359170340c0107584d90141225a41d030019000c4803e00802302d403203008011058030442c1890701c8950700c3e00082e0031507040c020404824503a0310141d00306020300000d07400803481522000c0150500070a5001c07128000100703140d050590300c078071080911040100b40c9040070601001500c160500340040c134041c0800f030620b210381c40328035000411801d4603170251004400744100b01e281000c0c80e215840d00039203006400441b072060030201303115a50b02d4021604400c1c9009449150b5150101071134002e5030b0542c01e641e1110341c038881c2e0074031070300448010486003210740480e60340000b048a424608609072903644014042071502000825a84129 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 897912976 1250 897911726 897911741
    0x1605070e01050a0602010231080706020102041a13030602250c080d171f09140f0901200a0509061303121b02190801060b030a0606092304140109 63
    0x2c3e503201070102d0b940d550590070b0f801b64001c800c884c00310992000b40941c0103110f4802c3d40c80500c00115030f65942e41c0208074101500b61704880c005035000681031051044940c2c16201101807214120700d4084078017003400e20403e140c0402044144c0019003131140c044480c2486940544a000c0042e20355181d01d4182c0e402c2880384180c1c1c406010700c0d0074149189000d400f1607440007080704852001c0359500240c40c12891009444280d185003801c002040741c10562107540b050811084031041c103810100d4041d18501801005108140c0c1807a02c0344004c0440321600744420054401104e846840e4210140e402d0b01540c8201d541040d40440d01941d40c0c02e00006a0048a0045680c41c0303021007007503021569121062080701b24080000d51581c01824404154120520503044648c022a00d86d4805801d4490350b51107006107020100038402610b60a05c00c6000501980c181400c0452a140040c0342e4541da001c90400c061707540404062a64650742c00c03040410f450b060b1220402d40e11000da010040680 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 897914226 1250 897912976 897912979
    0xe0f0105070305010b160804030b0a0e011d07090b0a0305030a1d0402160b070311040f08060c03070f110705031203040311070f05100c0b07090305160b03040204021605070e0105 77
    0x8050114440d64000d1042a0603102e5001700680361581c200a1402810781161b42154182c0c010000000801c0444005601030718246001064901100b034203107007502c2030100c07484803c11480700d07082c00c00d190024181007103c49045000c103038070340e0f09030000b00802c3c2c042e800a44a0f0000181c80080241d01040344800401d802e61030107030740304600044c00128081c45e0080d8030480f14060044001c0713955015107a07800b20070342c5000701d805c50240b0000b0103590004c0c1c0c4042c07840c418910f409c1c0541c0c10140285980071351820b07606421031030511401028a43d01d050b541050011040036040400b00501410300a000b0140803a9004000c4071101101c9900442e019000a001003a040010306408a500d02c00c807104040710030441401d01c070420925221030600e810a216200b030601d40006e403d03007241d03031080d41a0785520171385600d03509046080000c6400c1030540505001c0342403000c2c2995206517500103405440050310382d0081da800c200410303885600a4803030302c20007000140d41004640d51a040c0d480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 897915476 1250 897914226 897914231
    0x30f0506090f01050103030f0815131a040207110418050d021b030f0c040f090b01030b01030303111e031e0f01090606090b0403140111041203030606080105030c150d0e0f01 75
    0xd40316992404c84130207010040000300b40c940c0c954180c92180014580107054060010510b50380100081d6154013184100d42309540c456212100b02154100381d28074540040d01d0039494803115680e001e4201d015008401c0c851956000c0407500c0c1d1550301200164964050b04a40204840c0c0d64083e5076640300303032503e01908049900c1011b03281000b21300d40d503010039031000400700140b90b14100009006241d03040a50682c0c0e51031800c0209040e26038040c02140151000c0301194154200201a60540307022407803c0c0c0303002c20564800c00381c00312410810b100c46c80300882c0c60341c4540c4400e80201d4600c0550500b0040c2c40e0040c00848030050075014100d8880040800c4259038528080c1c0d0091500d120755001e6000500c0f00b0400301d10f0b0482c045100036441e01c00001e2803a502d001d0b407203294206800c20440001a112000101501407051718080c12440c00e01c10f070190314050004c0d41e60769241c042c00d0301605040404d0081085668152001801c82100c01d011182c41001072603600c180c4514001a00c0d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 897916726 1250 897915476 897915493
    0x130503121014100305071e08190608060a0b010e0423181b030c040204180f020f0910030f061202130c020316030e03240a0e0c011107030f050609 63
    0x110101401c079500380d030141185605060804064008010040c031900a108486040008038200c10480e00d50010462302ca40c005d50404070b07184071090144d01d1020310003502e44101440403590005407281d102c50023100100740d6040040041301d00c10080c0301200d400c2814200310440180306c2001d195640000030710703429443e650700c582c001c0490346425a004026003102100a020003a11500d40b0300003440a02110100040303900810700703d9020354490136415003440c03285041007a80d030041da8a0407150000940c10554000b503090110702c6291004c511500031024070903481c90081c0c0042d01c40b111403900401c403940e030f43c1071010713901700503010224414248111846940d07a200d00ca21880c00c115603002f5820100c4449901c2c40030007210000340d091040c641c1640031030f5a000c2007442084101c90300341070f2100307211365105018490083c04070f012440c240600323914580d90004440411550910340b102d040b400100ac1c55041614540000c0c21800000360030406102c40016010300540d00c8008882c0e056 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 897917976 1250 897916726 897916739
    0x4051311031b010f020f03030a0b09070201021c0c03091b15081e130b090109021509091f090912080f04030509091909031701050a0302181305031210 65
    0x303034441c24140b0710110b078a6070004500d5200e000c0d48414030403140103c0d0460804485a24a950402c81740800520f0700c07018030592a082c500b4800d034200089000950400e03000e1440b00042c200d0001880820340d550790320164110384030780c114607a0140c000c0700d0001c101000075102050a0250301880d107550301d00340b80090b0b4480c0f00d070b41c940b4442c1c600352380022050b0b64074550301c0c0311401028040c07039540c0100c452880d011a4000d51100d010308485000024020241d105015035456021031140444c04140b003402115181c100709681d1003003c3c07800408034580160060101203203203400404c16180781c9003581081203000184c014035a05580c131181480c0d590414002d039a43c604840040c0007070300610025079542002252103070003d0700115141c0100090a51a40880759000c2c02940099400900706030850720010289025102c00d4030380300c10060071900030466100310311551000d011885c40024280e80e000f046000c0e0002c0c0e00c01e042d6035942d070804400880c4242c0c1583c41e21000301c1c40c4840000c03207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 897919226 1250 897917976 897917983
    0x1f0809060c0c0615400204080c0f030f0706020604020a0e0103080708180d050a02100503010b090613080607050301091b1218020a0f210305071b050405131103 69
    0x79810000c007219912007104000c4901c8505800c5c0c0c001402d045020a0042414400f59034000030000c000090100310420340e40da01d0f003a1111014851041105010844001c68141d2000900b5034044004402c110040303441e0201084140790307a406508004203c2c15408204075000b68000c42c1c606d510591160280221110b003880024010704080002c1e000240340720300a05503003075080f400051720900c0c20011074006001c000080b80c05421011090086141405029a0034012803800e2401d660400c80d15040e5032190190b210f12900300401c2c0c08010100101009003d0305404050f521039080c1728801600e10381003030181d03240980c00d2a148034000c6020340c190428050f06030313441c03000500f9a0300038200182056046040d2450030350450070301603118003004400070183c0c4055090914906070a00100000a49241501440c0c4240500109a01c40c0a07251815048031180c0d00a0300c51080c00c0d180c0c609682d000e190001c2c108800c004641e0040c2c805045190301622012402605140030140c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 897920476 1250 897919226 897919237
    0x200a08240c34061107050115050a06050c0304150905100503041106090d05060103080306030114010333060b04050112021e0a03060e0f04140d0507111f0809060c 70
    0x403840241c0e8440d094400b4030791655001203854140314502c0b000d00d490354400d030340ca01100f080c04034400041003010018240b0660000c0407282d01d1a0208604000005070000540c0c4200030800c0f034003103a2a8900d140600c1100c0c01400000c5840d0070241400f040039101da4420702c140c5224051464110000900075411284520382c0038501d140341c07401c0b550070060b458200880203500a60152620340000303104004c90350285004051054a03403074440205801e40324001111301500f0f000800402c0001e0030180c003c007940c60502d01020305c58504011410000411241541c0da041c100140040d403c030080f00200140c8000f0790b92030140b20040826481039114215800c400d541d00900e080a6440c180c201801201c0303958a80820819a180092820103100340d84440c031001c858003d010800c0340035001c80d01e40e1400320340900f1481a90100141103030084d002d01a01d000c2081c400311060ba81c03180c070502c9042d44003101446480d095040300800c00f0704112044103161068402066004076028152030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 897921726 1250 897920476 897920497
    0x40e061906020c060d020c0115140d02010507170c060705070204060905150d020102010608010f06080115080a030521010e090d02120f070c031a10050d200a08240c 71
    0x1900c1900c501c1400569172101d01d00c01c1c6007a5080c0080d52a2030400e000d03940c148800502c4d0000700d10306229040310b41d004c580c2440751007024504440740c0141d80081c00d545440380c00481c0303c40f00c40d00c6400b00451500c1142c90345000d0307001c4c1c64204076080340c00401070f00c409402542e003000302503112041002265401d461200034044024103000740f5140c5055030741d2403c1e206200118806075900307070007402d44104460300c86038a500c0e086c0c11300140a0912441c500381e5100035102a074030b4134010459845043c0c64074054100240081c00709815101c803c084461400c881c0300c0c40b4565a03440c1d0726098030400c00d85031a500c0e8058100c0e0019100c1c400201e5a0000c0143d10880f0b02c0d0144400b105140341e400910102c6201000c0c1070000302290044256000750b240c02c04240581d8078106000420404454206074850b03808604140017240d02411030003411059215100090301c85000021005c07041ea60021440344a014056659490310100c0129030140ca07803220039054803074221032030141c061491810b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 897922976 1250 897921726 897921733
    0x60907030b13050a1227030305070b0c04050603070f200706200318030d08071b02061b01061a030c120709080106030506160e030a0305031506040e06190602 68
    0x20300c0600c1030707407198402d103124070125415041c1c19500c1c140c1308041c1301c11010100d40c107258044172103090140d024405219060b003040f4141d040d42d0300509940602000a454841810005610081c0c03810441e000303080001d00c950785a00e0b00791002031514046410480c002240008501c3e043c50f4260b000040240c8594007600342e01e400c00408982c11004580214006140464000b118840604c02808030400010140c4100c0602c3e030241490040d0b03a00b1404200415202000606580481e0080700c02144108200c1200000e000090311030095403007051440404541c0c24200c071105600c104110713100000d07007032403542515000c003000f400115000000c90300c00b007014840300c4214140349035100c603142c1071215000c0d440b03203401401c4a07819001150b080d8002014400745d01d00002801c5000e00705458a0702d0f180101c01c010a888601042001b0b0a200c00440880c03106c1500103c004075107240034145070780b903a03564041291801c1095035514001c00349001b2001c0b0307410035440450241e035000d4004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 897924226 1250 897922976 897922981
    0x102100209030705040e060403030c020613060902011101240807060c060b121c1e020d0e060d090501090b0703090c03110d060614010807030b010906051605060c040305060907030b 78
    0x4080d601a010042d854000c003240811260750700c4c0700300d0400002c030700c0c01030601d440c0c41c1c034001d011034842c020b03200700355888042040744551080050a400320742c003180101c0e899019100682d0032107910001c244542d42825044000b01440c8107081c50b81c6008041c8048006a48504407504c40d0042d00503180050748840044c03011030541d4120b22220b05010b80f598848000b145401030030035a2260030351400e504520100c1c0283ca60002c04180340d0304a850070301c002e0341c0d50454084d568051134801241801141d2698881542e01c000640e40c00916051040c03143e52000d14240340240540002260881c1184000c030707078014801c1c0f05072203095602c03021040e456030451b122030501c50b030b03a000c0301c981c00301e00030780b802c2d000030842e0003080010072148051400c20400d101c0050700248005000104052402400303070f4803a0f1b800401c1c08100e4115007086a506c00510015441500381d03a03401030910312640302804100d030b414a0040013201d0041d01600c08036207500c0e004907286d0315036120242a6034113180c003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 897925476 1250 897924226 897924253
    0x28090c08150901120b10080109082212030f03060b0318210301170102041511150c031b070212070501090905010f0303080601030e0a030f02070602011b050a02030403060f0b011407020102 81
    0x805034200c9040300e2202e400c203a0394031f4a5070a4a401c080220303503210340441d044040010000780745000b00d162144846005042118134004500d166501401b00300d02700305942c0902d40258413203000b400300c102685582349070141403030b1030030303001050301106600c201403000144000201404286000c060b007018556440c00074a04443e4219121840d904d560802001402020120000342040400d4403244001200c2d09042e5081000441c446140800c03024100000c040341e0408407640404102c0c0c40a0b41c022030701c80714820394059590025009100d211000800003000070356003003122001d0761401203541e2906e030914256003003841080f2041b00f0802c030501c0000e01400000d0b0348110107140018000189041c081d2401d446410700390040340d041030001d201c0584c1401b0386006460305000134005a007082885501d0486800060b00801c02d0100d148d01003548240100d400a54120f10144503400c3c40b81c041d000142a42c854543c041070a4241c6085500d00a2041da42002c1d016000b40902406108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 897926726 1250 897925476 897925493
    0x10306020c03041805060f031504031d0a0e0f160f0804030c1a09010608010c020a0f051203040605060a21020411040b0417010f0b28090c0815090112 65
    0x2581c00842c042488007003021200c0b528180b840b0090b141020030581002001c5c080030b48222030383c0c0e5009030000034010701c144d0a80061941c01a80c54030f0b00e588620320400300800031003a040c011641c02020301e080000c400715400e84041c01505c4003061396443c3c0e19020350100412108009070000b060010009403481c034010341c483c0e43d201d4040c1c14410007003005690340240400200380008284189101031115410003486040c0140c103005008001d841c3d10040040e56079000c0140081614807505a0304007041018040850b9810100c800c0302c2d282e0a292170902d000d00001c94419000d0310190000081d13030000703000410020718102c1591200358429400b80406029289034200750801c2c00c12001651080300b10007480140700058040d4001119031045500351030341d9124503411182091070302c01c0c0507559141c140852000d844980c1800f4080140c0000103200342d6409010100e1405610800e45030f0032645203440342004080d040e40925902082007240c92080c0a680300340030105500100003902c54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 897927976 1250 897926726 897926737
    0x120615030c031011090d120305070e062a0102071a0705090a1403210711090c120405010f140f07020127050304050a09230103050316110915101701030602 67
    0xd0440178500030301d04003c205422034003003044607034000c03816103000c40f198140304045e086803092500c8414203400c04002819805480040c8440d42d4050542400a00b00311900700034000d0b07244001e6440c1d02a508103003421011010013400a42d850300001400c00303203c0e208607140544001c1146102c0303030401a0b001d4056281d140165007600c5440b100010619800804500034003118012903511a4680341038a0046425490b480c00b61907801d0a11088003a10002e843c0c0b903e149070b9900841c1e50711800d003580503100402c5080d41042c038019800c1614800b00c0310b55403086031000210b10240c1c40e03d883c128221083d0b200410403070080150b0f88000241c0c030880d0100003030700074012642840d4889002510319420f550003049820754034216800750084085c80340340b4254440130b1000301989591202074403031040c0d2200d031041e0780081100e0b00811010480032a140c07080540580706501d0103900c112420055510b0540c869a02c1010b10410035114001e213110b01112004064181d920310354400d006508075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 897929226 1250 897927976 897928001
    0x8070309050a1527030302071b030506010515030402090117030702030f030d0c0f020c0907090b070606080f031e030426040f0f1203120605120615030c0310 68
    0x340c40044000c00c00030040001a00d01038804207401c014030144007800c0b02d00c15804c031140c182d420305415040c2d12020014004039601400c01503690384103458604c851030200321001010f181c0442021041c480c001070098140c8000b03461300800162819104c09040c042214000c1d0700001c0c0400600600c626001c42510200c238803001c4034149031499000a0601d103101003000683d6101040000b0308000302c0c024000d410031241000083e0034a14040203459040e240c02a030301a40c20440810740c0300d841481228001e010404a150310352009180410140071544181e554512076100c04000c0c00c103011084401c9403011b11ba40c2210303100c0003031200c1055000140141c03060764200c1c50a40c0c1009030b195041103544681c030303030756540c0d02c0c05c0c0803c0407041c01079900075031406808072405204400c1c003443d03101c1c101e41c0c15003440d1440c44a4444c40402030607441d0002038100741e000c0100044004002902c0b40039220074506081c400800c002490b84d19481c41d0109a40740e481030400040e40400f6a018484603c02d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 897930476 1250 897929226 897929231
    0x20d021302040b0f0c06061c03080712020a11211b010b030d0c150c0f05161b230102030f030a0e060c07120206011a0918010e04021003021207080703 65
    0x250fa42081c000c68000d00007052030000000b9000c3d8000c41c0500c0b81561144003121140e81d203081028100385250040b0720001e0901800c5008204102e015114007020a042e5103015540c54100e010020980100c40c0b802d42418440d01d031015011700c400c4011403007011203e02141d81424003644501d04190004540205255610141495a602d052180b100ca41d4100c0c0c583c504070301401e10304001001030340281b0030851881e1009161582e607002420741d140c080b04d854074075200c903041d01c0148000c0c58036241c0107001c45070520b075040740d00c03c00703805050455181c0541e0150007042d5507403010748100d01506050050708100007c1c0416481d8101854003c07030981e10000365800140801e0f883d1102c203555148032180e003c0750902c10804001d40704802101e403172018144035450031a90a040e05031450302c6004000000ca5401d40646800082c01829a209c003800006960342d40901d00191a090341d050303004080306080c040071903009000311010b00085001c421025940c2500848400c1d40207840c8504254 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 897931726 1250 897930476 897930479
    0x91a061c0b1327030207170c0916140403110402030c0f0a02012a090611010e0709090c1e060305040f02040915060816091d0f01020c100603020d02130204 67
    0xb01c900e4603540011074440c40c00601040320031442c1c3c64078409810403a44209a6040440000303034007098600c1100c2025806a06550b1512a0075081c1202600c40d203800c0b1581c4010000000c1620f803001c1800075090715102462150544e100540d03228074003014203202d010f80000601414198000c5501c4821030f801c00781022030840845039190300c100350380d10042c3c0d1600100b45041c1c035594100c40b041400306202070940c5a06d03010140c4160044d00c01c3c01d003400f5000c0f1040036070400c203410042c03069040c4820758004544480b213560003410030041c140c5509100e490040360005644200c400e103044503103002d034401840c3c96022009004000d10868500c200c00c81d00c00c0041c1c54902071380300020320600c071460002c0c13030394000d603001c83e5019409110b41c0d42c0401c0300d41003480000c1011a0a44545c00b4010514540820058400307186000540c0c3c510702c1108200940c5042c10350203400764984000a45445032000107000341564041c1c00041d46c0305107603000d82e10041c80e210b0088000d03065480310250515 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 897932976 1250 897931726 897931729
    0x14010513030309050f0d05100905120c070f05030a03021005060415032402091318020315010602070e10060f03060b1305090105041404030507031e09091a061c0b 70
    0x60216520480203d21101820f1100385891802040b100b6401e951410340c000c819280d42e6075500c1025001066669142c2100042c48001d010500d82e494070005a599a400d1b02c132499551044a8031400c1058414100301145a01c1d02217403890400d0f070076034020a140c00e480b8141e100280000703802d55601c01d996840316003070f21490075100401503009021a100101d10032451090000100481c06c125130700c1001030042c0f80d500c0080001407580741c4440001e40c1008035104031710b002c41c0d5000189d4140314405500a5078204040d515060395102d0782900d500713a5850107460070080b015100711034080c0002000380221031040d10b2142e0300d01d1082c030380860046c4d6a8402841c2c1680301200411880d044207a06010505011040034010107094038200000e21100c404188bc45102a00041c104440007a4007400c4c14441d071030559243c158541d03808202c00c000078010704802e944d48a029089030802554086041c550124912011030240c1340d0303480e040a24003140800e1502000104807282e80c0c03003506103903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 897934226 1250 897932976 897933007
    0x6031b131d091c0912150b0409050d121116050f030a02071401180e150d050706050c0a050d030f05010519051306090e251d04030c06140f06010513140105 67
    0x1807401b4039070500074101c81c04100010f407900c0003046401942021b141800203800003c0e410a0458545055071991303020b0070f1000d011344000c010940b05c41d140405c8000c200d901c6061300b62900c80c45082107980c4507200c0faa149441c5e00451030300c4400b680104d00c00f00303e020303041e0f928405074410515004041c4040105039840c40385560300090030451003403042181c2da0105850301070600074101d50040780c1b11b80d1956110f40e02c0360341d40994001c014004c03441071075a860401c00310b91119409001e451901c045242c00400400c05008c0c1e460307103142400300008143c2011006220604c8529146101e018100803d11085d02080e01402410540e501030000700c0f061584603a03c05200c0c05000303461940600c0c24462445000b861581c84000540e030380c02c00200b4199403400171903001c0a14605225681c0e03003070a0301c0da00848a4040c002c01d0520a960428a440289080c481c003d04140008147c0b5a00300454160003910654030003141d2030b100030300031072407800c00860880318145052860007000364000b011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 897935476 1250 897934226 897934259
    0x10f170c09061c0e060604140c0d0207080a0f120207050a172b050907050d030309050309090a0f0c091a070f050f060f0a02160206031b131d091c09 64
    0x40a644c2c607150303545500d90038030929402200458052007000c0180c203002494030001382c210740c80303150002021190a45240c0540d001d06400070300503619040c2205d07000d031a01311600c800f400010302c4610452030041c3c41c0e1098a0440743c200b8004e0407c4402680c07541c0c1c007429001210900300c0170502c80016003e01c01c50100d0200710050220f810380020040001080d80c0c4050700b080c256400500b0280856190041d40300710780e03609450041000d001500300981940705960703840c1e8002c2c0c2844d0801034030240c1030b00310009000055004200628210303104840107202801240d042108503852800100d480102414070707039002d240038403060802a81e038240f928281c100800e405400c15030402c1b42c5808049620b81c0c1c4004180400d62030411242d0055802d407840c0300c03001784a1500400450080c1029103600500380181c8503080752b50b48141d100d02d40510440307108500c4038142c1c5803c404013640920307605600901900c40142400b07200407a903100d103040058491810030510340d0000803080a01700003c1e5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 897936726 1250 897935476 897935527
    0x8031207142205121b060307080f070c0c090501080d020607120e240402400b0a0f09061e09020f0f0a030501030b0106020f0a060e0a051605010f170c0906 67
    0x1081c1d40100d80996031030b82c1c07020303000c4e0320641040c020006055086621180cac841e1080712003441c950745500003505c4c0c1096040c0702400c80c145240c00410030100a90000f410f031204401200d460542540d070480c0d484100325510000030304400442190314007a03420180c40b441000081d1001e07032403801054209010024000c0e101103480000380300035820142c4511030b109142d01c2c40c1541c0e10074114036410b40301d00008014844800200c0ca9400c03507903c81e602117142841d00910703000b141546c480590b20b01c405180200c502a0b0301d4440e000628424061030242c40707401006c2000000b602d41010fa900940050010f021381c01410048004444d50b06002800421401d45000503513504608207188070742d07070580148046d588042070030f0100440000700c405003554000c038040b55010500c0e01042c140301d0642e600074154442c0c84104501510b0018a00c002d80d03400380e9401c0d00d100c9484d50211100c2000d004070903208214200865a4403518034001d0520706405010b2034502036244040c842c0d942000d02059 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 897937976 1250 897936726 897936733
    0xe010e100b0c2401030209060a03050d140d0507021f06050d0213060e0403090807050109060503060405060103110703031b030b01050a0305061c06090b06010e0105040521070803120714220512 83
    0x601c1149040e040088c1c01c0403043e5858519942155036040e5a0701c0c0e41d4a202d428810321101c05810305401004070f40001058840500072401c101c10040c3d076400c4140134001c26150b9061412a250b1183c1c450141100c5c4d004190551a142c29001d0080002c00c60b40c09004254580e00040b6401c2052903020f40214402c0e5501c10060f8a000b01060a040c0d694001d2410440440410410345902c0025260400411280001d01da00e4180040c1c000f4103212040f110400c2021404006060301a4003003d4151116000fa01407882c0001d401c80c1241e070700e0f4040c07074045601030020103203251096000c26809840680b4030032003d10420361001026020b0b000c21200b803a01d961541341007026071410150083c0b82800d215030005240400680030340941e0007282d02581c0d000d1003085400321590b000340d5446804900391a03013651200b401c191240d01420b8402e441c5214400442c581c10b2080c009040050000c008440c20701192006030179082c03598802c0c0e9501410342600218032a500c250b51210703d641103c000713 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 897939226 1250 897937976 897937979
    0x3140d17070c3833040506220f0f06060c12050c060a06031e03080c07050309100809070e0c0d021803011d0c2d0310020c0105010e010e100b0c2401 64
    0x520203104ca8521110700400115a0002d401c108150f000c0301e02c12404507030104030313540c8183c0810b00c05015212501d010010100c503e012040c104e03405685400d061040a01c180110581c0020a60b04648135160000301590101070114000406800ca80c52241c07809518282c91a41d02c9490402c055076903482090341e41e40104200728416500c2c040e80d41c1001c8158280c280b0580300580501070080443d1101c4d20300003810030401100b44101c8803500c600a21882628480801c01441c0310412142174104c2d2107400404030300c8601260007a0301c1002040c1c5107074a0090307013200755806900201c59100c0104400d4038540c0c03040d40d0a002d042415110010500c00282c1001403240ca0007060340e001501550303454241401242d50401c45000340740594904142d0040794401107481d02c0850800119114800324520b0351040041d00110b048a100c0d03450b140199032a001d401c19580f0040d680740c40e0010000b01c042040041c1f10717010305112540c1c8810b940a601e4207212640d0301c08850709440e03031001c2c1801d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 897940476 1250 897939226 897939241
    0x40306140703051f0b0a121103090105061c0609031403090f1e0309060f09120307020103060b0f030411221509060e1f03140d17070c38 59
    0x42d80f54010840210120010040110b81540600714007800a0501d80051061400c500401c5906d07038003038011f072081100c01e80c1101d18030807540041e2072060081d400d02010032142d103490046401241644824001e00c0112075407590002c1a8000e406c4046c403c211480703013060304009002e03501c640b010501800b280b00c10b01c0040342c10500040d011014079005c14000050501000050302c480840542e40d0542c7d4198042115280340108122540d011003000c00c410600b00300440503180382c174800e8030305104040c0c541c01c0c80c0781c40d4001c003281003003a5001403000901245024003420056040500385003045903000c40e4100404454004c03442d040350307e4080790b1078540c4803101000e00408450000300242030400320884000d1a0142c141c1d003004542081c510ba0311000988100c006540c440d044c000341d00007041d040740c0c441e1620708260002c40c1c40c0c0032544145d8044e14104600c956241ea5444c12101007030340e5074522445055007954984180d2003d0352181c54802d00300c80c2142c000c0b20380110440d1070b0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 897941726 1250 897940476 897940481
    0x51605031e1b0d1a0a0f09020c03130f0f08071212110d02070303020c12070e2203090e0601091a0a02030c031602030f070807120816030305011a09180606040306140703 73
    0x1c1c0740e01032170f01c000e010811100c01c0c00c010300039110030880159541f90613400761307855409484040e807450269400c0001704240c0e004c41680c12107019130304140300315655883d101c0e15a0342c42d1207200c0ba50114100d0303030700010702407135207034005959070b03013440710116142410040c9010074640c60078001d60b211000c140141a010041c0c2803900c2c001311000e0300b01c01003107900d05484542038444c04440c0d00c24076011841d1548052080c1e42000802040c3c0001c0c00d009040042014404d4482d50039407400f040b02040955100d845034001740c503080d01c00030608440c603181231445648a11410811030000340322000f84900107000034002c0d202d061003101d40a90407801018104501200c0c1c14600303610000341000060070124100381103d01c1012569440038490604510904c0f80c40b42d014000900ba582403000c15416030f1001d4140c5949820704e46202800c810740c2100c41c861194002c0c1d11401305100100d505500c8282c1c580d0110010340b009080075543c2e912081640c3d0081d180743c0c01c0100300405c005856901d403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 897942976 1250 897941726 897941771
    0x30c14060a0e100203061020060a050106080105010e030705120304180c0801060203340209190c0e0108043c020310090f030c030207080709051605031e1b0d 68
    0x280f07821891410144001404c0c8900c0100300307003d00010384080600542c42980411080d4041015200c261400c07805400c0206003d0040700017040b880800404e503540700341529540d4010140c01400014200020001d5600c90060702c001c0c1444204004110b13080710310100c00b015036450380041010b140c8014040d0050314140c02c03030001c42d8801e0103032040c0b0100300c1e4440500e180c80c14101c40d03419220256100403011420344080d400c0540202480031080c0034156890b800c0008510401c10400014021180f8260f002041030000300404040780c00b140002d1040ca1504100da401481c9a0072a1031000c0103034041101d4100c14080b00d8800e1000750b00303003030060504400307028504101c900c400b40c0c0c3c0c076858101044405001c120160b058003040500800800000d400000101c610351507407600694043d244c200d5402008010500034541240d0184040da03006d5070111910b4901c440340b105030282c4000000f0074a858000380e855056131070f25080c40040024103165900400c140413044091240f80c2100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 897944226 1250 897942976 897943003
    0x270d02030409111e0a0e040504030f0206011505040b090d0203070b12070302030f041e02120a1112030a0804050106030b07170615190c0501050c0304030f0305010e04030c14060a0e 78
    0x4202c40c6034510324060b0500e54240c06006141d4541c3d0007684200c951b00c04002c145a0043e00c2e04041c4000e1507000560408080144e9007210901c0c2c5c0c0b80e01003d005002000d03801004550240001d0192046640c01703000d0080019000f20b803505902d4002038608049540650040c0d40c2c006002c0c408541501d0860380c2c08409400c003946507042080350b50b03184000041011388240c200010044880349900456001103070002e18250382e07551030255580c0c0b01c00b03114604a400e50440e442d964550308154104040000c07100c00507508002c02a0310980341440000c0040b0340b15584c1c2d2a010000071307262044c59008040310717920b0659909694041e044c030400c010b4800c92003a45410820301d00e070741000307007202c00d0458020005042c40b0b1b40500103688202c41076500501c15400c00013000b08245401e0099407041e8002c0d40d9801c02414102400d40c200e981c203000b09a1000603d9001030046801122251a41031103041c5008501000c04001c9051503800e49501d0b0455844900d07940a9000c10040881408030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 897945476 1250 897944226 897944261
    0x303131211191b03080a020c0405060d120903080a1706011d0609011808100b09070813020a03060f06050112060503060a0f060e040b0613050f270d02030409 68
    0x1610340c100355580005103807500e031403025001d0501c03c219504400340c49851104409000c0c907a180c0c030301a0702039000150042d0041c80703528000c4a01d86014081c542c007034140a41482081181c03030315900905c09102c1c41807c207100d8080d100100049002d4020202131100340e99140450400c06d44030180001c001d4036403410450305165441c2420802199040c1c1503108030703012540c0390701c00801600c00b451491510b44403041116000070b07112102140c10b5030001902c0c041007003825440c101308030900c0703400d5030345800045058000074000c481c0240c06d048024001040d03580403603a29a03400f419900242c10410105440e41020405960400f0300d0386218285110140001800c6c040825640c40c002000301a142d0b440701c0c40e480c1400c4803540b000021785450402c40d84640b82c2400c020b001c088040d2480f80c0030304038002c00b0090303c2c1002c3c800c441c05035070000c45408580e26090690b50150904800d000094410380700c1211014030704000c0142038402d0b0790080c1d030301c40e890700d030385082242c1c41002c88001c0c044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 897946726 1250 897945476 897945497
    0xf110f0a03020907182601060e040503122716240516021f11030406090b130e0112020918030f1b010c030603060c02010903050d0b0102010e03031312 65
    0x1d0b00c40c03502941c418000c1c80d0a80e41c908045d0a085a2010964031641500e900c02800007038004003405a051391390090002401480e540b1050025800780c1110040c00740d400c1400075491000c020b20080da04450300d4440000c09a40700b140e46001d655004007400516413000105001c500c5100c0450001410180d146401e4009c01840b605400f103058030300030081000c001810070240c2c500841c00e1201c00d401800d0710364401c1314444a0740e440c5000150754400310360081003c040010340002201d0540390310390b13500304d9010b2030000580c03155000120800040510304801055401040c61128000c008401d84000ca1000a005001d2120000350060303042c507207036030504a107c4100208590403081080601ca50b1906041d4417116803114020500b0602d5007842e20044d11a03a06800960039603004000410007030015417000c1e400c071003541800130b02168041c000c000203070409a001d01214401800046060f404107418076003503a1045508505c851003008403601407048403045545802070b181003408090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 897947976 1250 897946726 897946729
    0x215060901120305070b1509011403100b0409060e010c0f0c0506060108040213050a090c080a1a0c09030102190905090f28090c0503120a1b0503070f110f0a0302 70
    0x54005018000d02c49441d000c5000415210b1002c40f2440c50300101a01e0f000d003010b500c0080481604130701c2e548100c401c180003150300e2400400c402c545001c01002082e15804101c0b2040c0a890304070b040300c0d1b100b959502c2c0e880c003160480c024400401d0001c4000a250301c5010740c05811414110011010000164038800005000140c82c2d034208800342400002c641d198400250034045030352440c2011800d18041c0592002c0700e800000c0241e12440e83c1d400416110304150750390381220180a80306149003a4001ca45042c0b6080864000310440c062610b0091214040703402d81c2e102d00310007981805407c000d0401e06500044c0140a42021100aa440d0030000c104000b1742c50054403051007203d80714413400c880900d0b804030006041e003240c018041030420382004400040030b441514003e00801502c8404142060100c0b01c89922544803200c5040310301581c0e64030440d00309030455080c40b0400440c00841c00484400721100e1080701011040d00010080c4002981c840f0840d90141c8410f18060006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 897949226 1250 897947976 897947989
    0x105090303190f031e0f0e24070c030e10110307031206090203061305070c020a260f0a032717010b010c020607030302091908100608030c0705061e030a0507021506 71
    0x14094030310745c0802c80f0000b21003031358014420700140d50030900c0351103403148810707114050280e5203a02c281040c85407603450200a403000f5403030900003400140128840442403070401d481503803038007440c9000c80e800020b03481d41c00d02e1680018410340104e08d019a66101e86003441c040e4002031b15a100e01903046092040100d000d443c100002000c1454071703240010591445100000d00b070740c1d0001c0c00d4452143e81c3d4500000c0c0700e11142032604c01c08803410780090b04c142000400303c00028120008000d10001d40c1c5007118461040313101600200111222241644220000c081c0609984900e5651100409000900311007280130002e05001062940c0400b581d104c03020745d000160181000350f40d41102ca800161071902d03180c5552100142c070a0049044840000e00c174034159007006c01042443d403101040c80d540c0c080d0f642c20008a500c9484240803506140c1d0103014408052441d0403a444140c90400c00c0e03c2e00100c2e0b55843c4240c2d64410031071003542c10408007401c12050a082c8249040c000041404c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 897950476 1250 897949226 897949271
    0x903100e0303073f0b0904050c010509010207031b3201080903160302011a010309050d200d0f0e010509011d0307030203061807081204140105090303190f03 68
    0x140864030210041c105030044c84502150082c0040e9000340d603400c1d880400c180005441200400d160010b1a07003d070a022681e60300480d0090010690b845030f41d80119025400a1501c40c11402070110010014803102000080d00d1251a00c81903001c0c1007245411507100c41e01417520001840e43c03401c070740c1c0d6610425000c83e454021303e80003030682d42c0c0328145850b61160310282c5504e8001800041d0515034198801121800d840c07030346034030200c0036400440a5818542c00544181c002050950805000791504405800e01103844070400314100405402d0803405282200410080d258412415038010741400c41440242800740c00d00c090000000d1400d00201e100a192210000340181e996070100160b00056038000e08650302443c00514141019011a0390b5020506c42e0103808140c01e040030841241c000d403900555403e0030f2412002c101003a42c00f420840c117004080020b031310a52000c0c0010180707060b001c40805840f04d030021009103200c206082e0780080520345041d600c40210f0b80d240c2d808 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 897951726 1250 897950476 897950491
    0x130311150c030615030406092307091a0904210f0c060b01020f0111090907030b030d05091c0305120601080c0922050907140603061008040f0210050903100e0303 70
    0x81d101d5480d4808600b0034004c0a803804c8003880003004002c00c1002e00d42284501500ca424544081c00880300c018080000d008540c213000d03002000c0901128116030f0003190905113011141000003c010003061082d0b202b500d0541d40c006600300401c440380c42826100c000102e103460048801580a00300921030b420642004000548420100020368802c01a2001e0740301c03404020041c04414040342842940054603a40c0200710b20400101024001d2088814801c0c000d8060b015203505017904450660003080b00f0f952140312145001e900c0c5019000b0704400394802e031500b555070b0b41c002d211a14000d0380205a1410072258400b008030040600040e9605083d040e10306640140c2d2845d03070784000c400e8240c80c0303103103031482e0074200100c11034005000f000f183c0440c1c64048651800101b0301c580c40c481110200d41141010028000162040907296031103805440320805c075460f00e41c002403403440c0052210000500c04180c0b4bc41e941740510040c0181100208100a41c0710056010368507400018040d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 897952976 1250 897951726 897951751
    0x402010804031106130311030304030512041704060e0910031721150112050c03160210240503070e0a1104090e101d060406020313080313031115 63
    0x1c0816010b588018031000d4808295000c0340341030035034480018414601500010000c12100007003940c0882202e000e280c055070f0f845e14040b001e1000d02c1c0e4801d00613100300c40701c28814064035191034100010f4405810142e035050510040c4100b04219510094070301d08502400d43d00030800903082c0d10542e48158108510140c0304c4c401740e00000c0100210041808045103120b007004251065046011507040e82600c503010700317085150341c18044400c11103004614507010000f0580740c5403000034880204410f807040384c00030294111f061003540ca0004c000005070003641e60b0704600a02c41e9101c00d02412090b002490340a28060240e04155405001c40051a645800442c11801044200e801070404880d060000c45111a01d4036510900112000c0d0b400b0310f04000000512503040c400560450b4110041145031290785560000790f00140019503004406113519000550f1080610701c595000103408071805001e00b006020f102590303000d0300281e0480c03101b0314190a400c4076890340151718a01c88 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 897954226 1250 897952976 897952981
    0x206061009050a0e010503010c050a0e010c140a150540050d02070303080612030712210e011103090304090b01090f0b0c0c0406060215150616030314070804020108 71
    0x140d41c1e80c0625006650800c141d088081042111044a503040701c8098000f0080200f02040494442c000d4402e40c20009200002075801e5610070301202120070f0150004030f68004903002d81d0f0345050b100c100d0845001040510012004c507840c442c2c9a4440181120700a40c204007909000c161001300041d40c40343d030301c0c2d40c505c000442c01084140c07140c640d01c9412900f4484900c0c1002c0d41e128810b02c0100d00148d036510004405042000d02d000300918108011820404566035034050900c014610764100610030a416841000f09030403102801d0803900c0004008000f42100380c00e4692080c81e0350500c81c3c080003032104201d000011a4200c0d40842800145081040d004a44000035a4850320b9a81c820510101c0c07100c59102c0188414900c03081110310100c1000c06110035201e051140502607006062038072600c3c120b52010365800080e1003000c85000b414240040c0154105507900041041c0000103034040540502c52354000c094983e164400c2454040da0041401200410080c1080000d202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 897955476 1250 897954226 897954259
    0x70e01090f0c0207080312130f0b18011b03021e0301091508190213020c010c05181008150d020a031a070504030b04120309210e0d05030405060a090803030702030403020a080d020606 79
    0x244040c03a40d001d183c002c84060036041c424100d0004bd18010041081c00c1043c03024548140700341c8003040e00103404c0111146e0100000c4d1b0007900700451080200c1d48502c128050011560021400390031001d10014040342c00d40d6164040d601984c00940c0301e43c3c090150311003d00032111000455503812075400100c80c20fa03040150190160030000c041c15030800c19079041075a0000c022b0507600c0d01000c40c542000d4020020448480484020503001c524100c01040d40840c0e880d13840d101d03051307025107074507000031455003c109502c0103039005031034280002c05031825608200850541000c0d952600c1d0b420541140c881a101100140004151012540d41c1c4008540a038014107659900009111403e402d04809000100203a03205003000070490076140030b280c90081c503002d9043e0703000303030065051900705000e0021a42c040d070b01507000d000322810b0014075440700304019403040440d54045d50325980b42d4414004403110319001a600d5070890350720b5120141c1e002070b2803640320350201c421408403203500c0f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 897956726 1250 897955476 897955501
    0x171302030a1a0a1103061324090e0f1f02131d0702190c0312020c0303040815060d1101080705090301140103050d0201050f1602070e01090f0c0207080312 67
    0x10390040c070407000d000340210014040340100340304210a60050285046085a0101e617110440d80c01c0da000c06034a2075400000071541c0030480300b100808070003c444001803080c0742111090b038010a4032a4030f80b02e03640e03021034040c00700482c80180c080040001440480740c12440b144111a112107055000c10002c48440322100c13440010210340001c090740c88440c1180c1107240c401119904003510500c911565403503080304202034019088019002042e0942d074130340303a464060141480444c89a54880c1407559010320041c402000024020004000e21510700b5140040040013503210744200c42c0200302040701c10010f240301c0c103424600304649a40c0d001040d100d6000f00540341f60150720b0600c0d101701042c03241840605030b9000701c08545071407882101c00c07401d0f180c0494581d5413610002000c602a8030212014044240d00c50040d503100303948075100d043c2c81d15401d0380300466041d03c4010140c810f4420b0321031130b0f0031101c0a201600300c1034201041903a0b240700b16040d03010b09000301c00000b1700e12031818 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 897957976 1250 897956726 897956743
    0x40c020703082104140114100b0f04080f0f1b090a051b040f03170711120a02030303070801180510060c020d0203060a050601080123060c100504140d17130203 69
    0xf1040c20000d04180c14001000300b40541081010b600e0406040c050b074550001c030601c220301e0401d001301c49034100700c5074030f0054004d10003903150044244008210900240043c081171418680180ba09020075820030703142410401005412400b4450412036030f888400748036078804c0700c0e4500402c1d20b8482400208010094001601c400300000c42c01061501d0b074141a64101c0c1d0180040501e007509008000440748204880280034000c0110088080d00b005160401c80101041c140d504401c51074000ca4155403040f5103100000b80740100510124503980f40d1040d6842c0c440e04104114644489400b5a204090003004140304c14030380000110f41c2d40241e1003554590140696140e41040240b02c005002d085e140140071603900000800c01c0c0c4110a99100000d80c0c2c98184c2c00d8054521090180a6200b000c28511900610f102d4410489081c09028003681c4203130300b48608154010340042c200b0252080d80800c01907401070200c00c003905103401e00d40042da1a080040d05c9111031001900c0c06040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 897959226 1250 897957976 897958027
    0x902030c0f0c0f06040b160203040506071407230a1409011a0d11340201080406020c150103050c18040803180d020c1c022d060705030306030c040c02070308 68
    0x1040c00b003108004078444103070b0058401044048400021031f0301a61213000700d000d50380d0400c0081c88450b0101d01c12548850404007403400b51000b0350745070700c5c940801c40d8850311501810040c518950290f4282100500b0082540001280c460841c03c00002c80c10041032040e01d0384200782d12072003205502c4a4040740c03180c04640b02c0c10441c01d00d03089200c1a5a412221303980c100080e00c141b81c1a80303091076035648603040580f401c1000300256154010348070400e01400503201b0356824000c180745528104184000e5101c086e000c85000c2d89507250035481e14a007206420702800440b45000462186110403d800540c0030642d036031250360f4070010041041c900360460903244200b00c0884440742d00800d10745401c1000b82c0d500d50303103200c4166044190b40c0516000075004020351032074580c40c601c0c100b081c0f04002148900e0301c01e4844403100003182900100c402b03507a036070000018000c00b49000c1102c00795005040d10148010015000040c5d1a010301c0d10014055960000b103075100d4030495442c01c50203030030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 897960476 1250 897959226 897959233
    0x210c11010207060b0a0e0f1f03080d050a050a0213050d02030313030309030b0609040c0909030e1003150f0e07120b1c03030f0b0a120203010b280902030c0f0c0f 70
    0x90b9040c40c3c006400b90804031401610482070200380344141b0f4509905c640701001c070401c650380315201e00f0074002c410588201c0c44407418034404000a1032080c018941070031000b5001c15107050000310b00080b00c1020301098140c52040108074420810944003800300c030811185840306890b50700200e4114450450641854108a50040201600504100180c5c0c0c000c0c58015401e80d0b904040c051032180a40d80a880001001010000c41e41e4a0700402c50187c481c0c500484240d60000114909041c100c1202010a844031500c02b00c0b020020100c40041140114403209207143c007d444031200ca01030188401c004c0c01f610800840074181d00700c10a0814082d0000c03801010001206240022050f02100044d00309240c001070200075020b41143c00320000d289412040c0340c6000010220001c4400701d80554a484103000641e80f43d0131200414003074911250b14008000f040303880800580e80200c09814070500610221703900b414162600700c0315644071282d5640400c21180e103450543c030f042114038132 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 897961726 1250 897960476 897960487
    0x20909010c081b0d0504030e1221090a0605030c04230112020306210f01050f01031101081918121d1e04050a110703020d080601210c110102 61
    0x405520180700c1108a964001183d2111006402046800c44030500401400e02c0f2241c00c00b1015402550064072a0402c822050041c9020903140381c20611100130640026003050b40c29030b4019840c00c54480003141c8149001003175400202d84000c02d00801040210100c00608074a505030100c9018110b80110050b008803140605801924000100c60008140301012512b03208680280d9002e032000801c44404605180c140710901d0cc00802303072080c90b1160800e07031420064280b260600604500c0c3d1000070710760460800c40c2e0b840e443d100f03074941005066402c00020031200c2c950040c40140ca084041098140c010401e960356140080107000d000741c28410920203600a100c40005041241c9080200d200d20800c002600d009a0f880c100c007030400062200311072410ba400540d20001d110b034000750a000361004c6010030742091740c00b14090b9000706080009142c0041800e0f600030800d103410034582c8080303034107050110f8540c61400300044e110300c4003020250180310450204000c0c94021519607 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 897962976 1250 897961726 897961741
    0xa0e0a05030904200d1a19031a04080d0f090b0106120608010e0a030302090d0615180516030e0703060c030626060c16020307030305040e09072304090209 67
    0xd510403030380b29101e40d20b004034540c01d4201c200079541900080c4120355003449960324540c0301078541c070482e0b407403803050303030034400d0b103181d480b0910030391101d03840461400e85a0840c03405070101c004400760043e80d441da0074100320002e08208200d03840300c0000100410006682d07283c100103050140401804040013400200d90903500100c0002c0110740341206001c4d0a41e00c4624a00300d07483c9007040c8085800c10b12000001c42e0007034008040084001e02102010a60380d160042251501101100e142c82142010014046004012000400111020002402d0044200340110070303041e10b100070f054503403804c0c0001c0300f018404d00e002141c0205040c00a10100c080080080469009001c0300e00c90220582d1030210100403c8203454000d80024015516071030341d6100f05030841c070019010f20003030380341200040e10140170f45e5000718442c0d1922601c4070300702803075170813003590040603441540d00c201000c20403003041d40192040500310003a000540c40402000c2006040f940324003a4218004005100c0c1c0d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 897964226 1250 897962976 897962983
    0x204050a02091c0206041521020705120a021513051f0f1505060f270108090d020c100203040f080d081609050603071b050c0a0807120b0a0e0a05 63
    0x200349007103900c5041500108103602140d10803c80103034000c4401c0c40203001d034820821b00081c004c4083d05180e80d2074801d02d0035001c00403004440c502249500490403108200c01005948132500401621908108001c10300943d0384600c0c0c00501c40c0c220490000c260610048071403d82003c0c0c00209907072000100780300c0e1751103628000c10b50b46a401e18148000400f0015481001c000c05056019041006e01d00350400c0095005000301d151031007402c200814040d1008001e4801000060581540312103500c00013410401c0300074201b41c050f805c0318521b450141d42c00300f00040391920858403070a4100c0c0ca80300032403650185401c90355007030b80145004202054000340100313141c0305030b0381d607001c55036500070700350f45400898a503100100740390000501035450024055039000c105490404654401904103c5070700d52440000d45598020002806050401e40c4540d000340c90103000922003540b911501c0d002c081c40701c0e130000d0540603002001c5900342c0780940103100b075a0580c9080360100b03109400c01549 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 897965476 1250 897964226 897964237
    0x20d14062b17030f0126060c070303111c06050a0b0706090c1d0109230106110102070609081209190822032109030f06091113020c10090206250204050a02 67
    0x400031210301c0b80411006c2030400201a29491201070040b549a44c088403442d900848011003e240c0c4503800a0f20076103610010300341204001c654003840328140309001040310119048140581300e130200c01d0129104000c06c6400c500d602c41400988030015013814030702841c1c180c1281142550074181000302141640c00e46041e54804c40c420841c0c078080e24680c038248000804200301d000c40071001003020780e0003210903404c000c0800c000581b90011954645007160300f4050101e031070020100d0038600091f007914080f94444a0070005001d03000e00070710043c10220010700001e21207600001e008025529201101c0b100c03030340f210b00d0710581a03201d00e014114114080c1c1d290f9a0951030100440c0401d00c01e031401e43c2201d41152100b90049415103c405c0601101e1000b039900c0a800704601d56561104c402d010041211b84100603100d806440006041c070a9006940c41d41905090481c1c001d60b6401048403240300b840304001c0b96001c2219900703118904000d40180d4800c2c40d0008216610015400800b0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 897966726 1250 897965476 897965489
    0x60409150f0b030c101206030c06050c0c0d0c0b07052409101a040905010b130b0423060603090f06071707021c0305060d0204020d14062b17030f01 64
    0x140300782e80060503590300b4251050b45e805803c0d070403904070f018024007890311420301c8810302080c07030354403600c1d8070100310310700e51000001820020700034010420901142c07808980c00c45402c0c4400308070752100312015115004005030080000342100c20424100305003522031484400c5444400340051506200ca00200d0384030b100e50269007900305070001640b0800d290580b10b9100c0860784100e8030140801842e102008840075942c400403003119a45201c4100303044650790802003031000201050206807a021410128406614151440784100c054440c40d440700d010b4030b00d0b60312951040c00d154a403801902003910a4000d000034401d219a0101801491555101003007030951618902203135203880c034518080038001c08017802e1818500c03a8014a4209000800f040464095038000400302d80c0072000d04006203684413102c4c00202400c0481c0c03580140102c0da4104581c600b00452000c40840040000304d103030182812000300100c41c034429804000d10480b20391039240101c0d16280d003000c01e01a10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 897967976 1250 897966726 897966731
    0xb07030305180604030c140a051f06080316050c28050a0b030a0507020c220c030207120503061804080a1d031005060a1205150106050405010f08060409150f 68
    0x2a19800b0402c1c6500c0d07100012800900c000d40c0c4648044a0201204004030b4510481c42c440c40d9550384100a10b200003801100030b4607204d4a0503400703521b841282d070401c41c003031401d00c0020410b094010094480c031b0703110708901c0a09189075240003030030000d0aa4203241c2c0420b12456140035240104500132850b451941c070544081d4a820030400c014410f4031940d000d101041000a0302051150401d0f074220b841c0c3c1c01110603548880c000511030600400c2ca07120005400b5400705100e01140c0103114070301899003411031070101c1302e4643d9928103034412440ca0910000002103000d0352506818184604c0c118107101c8180c0c1030601d4015542e5000310070000006107004c03443c03d610346c3c3c040064084054001c00030044142c0c8030807008041c1c0001024117130302200c211000100340100d8040030311581d20800151100b90000a100c0c2820407040e0009030400405200501090343c0014074402200e8060400e16500da0710200001d0142c100d00500030006010103641c0f8a044485400962807001d9000b401e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 897969226 1250 897967976 897967981
    0x70f1406090a032004050a0b01271203121112060102150a1d01090302030306030d080103020a0e0a0f291f03090203030f0c070e060607050d11030408070b07030305 71
    0x204016409071010090788001c59080400000b881e081820042000a40d51801c5043c005000a03088400450f403101d125522a03510800541e44544a030034001d2111401c2440034001507290000c840382c40c040e9028a550b10304041d82410302403115603802c441e51320014000100001900015a00704041d20070319141c0442c040741040d800070498141da80035001e03030104a41d0300e0044800290100f00480e10210161007101c5180c40002e0140c000c03254065001192350382010020f240c0380000d61000c681c10084e0110052005039640c10041c030840300c20812003082e903180e45109600038980c103410070f29034500d000600480d059012818503075040307180840d4102a440c541c24028000ca00c0f0f01511101e0304c00740701c81d1070140e00950101c400701e800036040f20704086140800b118103030701940f00341d801d5a22040e420080c2c0714400e10f06651254058940500300511a50398a0740e0700d1303086003400c050090318690320000800c200180d60080195204844900f40d4440c2d5a014960000e601500041d040100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 897970476 1250 897969226 897969229
    0x40f031104110c2805031305090f01120209150d0609060f06080312131407090506041814030f040905060306060103150603180f0b090d080105030a0f060905070f14 71
    0x540300300049110243c80c1a15100401c081c4040c6208100341e0764050741e244e02c0f00400d00400207040d050802210441000d801c210170000100300042030030704400f1684005000f080c100c00692076005a06884c555180c1d102c1c650705603072000c0319286c1c1680040075410b4120500105410858840d4010b0f4410064a52013200040030f0300d4080c01400b4440d0f0080000210040340302140503440054030040160001881c2d035025444601d02030404116402501d09002c00581442000c0d0480000ca504020307c02e0b1444480428110810f409032520501d08130500710010103008507403802a81101443e65680c40c1c02c0032000600e01078500354041d10800000410550191041d04520505040c00110715850008210064a0886c081c1043c08001d40c81c54000200326429a45515109000c07030300407403510b562030a180408580301030781003104540040219450101b018400c2d1608401c3c822245c203d00d00304603015000d260320041891007940d40029400b40348004550aa030b081002400a43e11800c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 897971726 1250 897970476 897970511
    0x150531061203050d1d0d030e010b0901090e0106080d050706060506040b030c030901060b0a0e010e0f2b080408070303020f031c0c44090309010f05040f031104 69
    0x25154905960700c00c0800400e0140d000341129820540d03021135159103400b40c0a81c8024a5020141c05078043c4010404058246c001ca000c10301e4090002c003e4210070400103030800006129160b01c076031b074960704200d02d07000030b4100b240a000c001c021180c01070445900103110350700040302650031520f02000406e80d8036080f0f0854048a0b1038590160460700c030200e111500740d0015102d012103640c1c6150014480044a010307107022261500c1701c100380c0c00b072400050302221150005501c2501400003c80c0e9a075255818030f1032a102c5010f2104002101c03030080c5660000c918005011b488000c2000151030f00d0006504007501e2180d804d50b02c01d4010210f21035924010420500244680840c44c10302c00700031507001a08201c2140b42c5aa060030405030660400030621180d00b03603c0b50400b80070342a0403910011102210301c4d1820707141d072510704094415181e0144070446410410141c260712803140c40740c0141d901404c0079a03040f042d02682c0c1c0c5003070101a1080500d0030b00640c14008011180202d40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 897972976 1250 897971726 897971729
    0x3090d1409100c0506090703060c0c051f090614061512130c0504021209010c020c0603150d02060427090b070f0203210414061915053106 60
    0x85141c24424058200048240d80d800c88508000300e003a00040450030030400240680d8807040984146800c40c00c140c01a919180c031000300b07016070380700102c3c001180060100c2582c3d80d10380a0090703140b4001d203c02e02411030b0f008060401801d1a0801017640714203400740d0b003c1c40c402c45540c02e2080d02d100035001c090042c0c5082581140001001440d0f98104c8411004681d00ca0340d60310711350710f444000103400c0340c009068070132041d0150300403c0314003002481002c91100950000701035286015000920601c0020080350111302080b0102101e501c078060140a00703940100b4050302c07152a514268000703000203080708030b0075070809040380124205206107100301c3d400070703030b00480360b80c42c60002d41e44da0510020b2901144003c20810b40c001c0c801d00381940d01d40407185001c00403411f041c01d140e042d98803442110511900400180312000051544510400101c840c0c0480d0039529030481903c440011384c450341c0c01c03000c14241440541511402450121010b41c41920360030707000305501c001c84e1442d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 897974226 1250 897972976 897973007
    0x8120c070f03240f1806060b1e0f0906041205060c090a03020405130c140909010c0f0c030509130c080f090607120204090c23090a14041b0503090d 64
    0x44401a0302c0d4a5800c44843c6070580d82d488001c6141510300507840700311880c01c100e1404803030341c3d000010304011460040c00c00404c0d07801c403214240342280e030f016444080d290007c0d901c01500050100d090315001c0701545c624000052008d61659a900c13100015401d850b0012580c40c00f03840001a06402d0540c2036035070404000d00b120b502103041d070342480010000542103581c0240166030f00e800050f118400440604141d154140b015403100c2c052202958000e4a040a43c1e410002c1e01389006a0015a40701e000000d49401d190207101e50600361100d115400301250040b6500c0c0204040e81860b410100c0b0000b602e9850140740c0c0d41328140102909400d8810340144e42015021031030251003100b07044510400c1c910300600e8290f0b160440c00c00c5880a003031200100e100659030f5284404050300c1151a030840d0f0303426a00d000160303000920440c0c42ea0040301202c00d103400d2074242c152150b42c07007014960300c40c00c2d000c0002d881040d000382003134004803409640b0b44074084040848920452812154980 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 897975476 1250 897974226 897974243
    0x807180903051606021c0b01090518061c05250b0901080105040b060c011a01030506031c0f0c050610090605040e070b07081303110306060d08030a110408120c070f03 72
    0x7410700445040700f40d40e04003139525039000e02100c40d031074203036100b640c40d10042e40b2400250005400300140a2501ea5407082d4822003003200904808081c4000309a44404110303144141c01c40140e80c44402d48031031050140030b6200d03c504130948400c007200d142c040c10315071203100c0111680d5042100140c0c407407101180e00240c140d1004109070700700381d0001100c000d4018080c5080808203c0d03501d085481c01d0030703412803402c1c5003181c000c40c0d56007512806410900540207401c0b1071a450150320100d1180104003000c201440784030403600c0e441412050189540034003a9115030900f4014442111f60342d0003040551860010002607a180c240300e00411b461001014091061038400c1c1412980c0000209848504040160118415402414102540c821458508204102c030145480c002c0000d150740d004030043c00c01000850b82090550b0b1380003000e0a00894402009020310306507015550005401e403143c0c0030850440030018014155000d201021a44c50a5443c07040d250000280d02c40a0070105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 897976726 1250 897975476 897975487
    0x2030711061b0115090b0a030f05010207020915090601050c072702041d010b03040201080103020d03030e0712060f050601080408131d04050118030f03090303060e01080718090305 78
    0x111a05021900000001c009500382140550b4120056005004020581c2d540c2c480c482c1c00c1d0340c940c504401c043c0000890401c41141560003003a00a900c900010340010322103038a02c0f080102c02d404442d03e03264060907000301030825180e0034005011400f13a4074462180c12002900300c0d407081e01600c442441c400010040305240c50303d1111400460250001d0b0002040d01c0341c00c004186000400040c40c0f0b00e0881d540804040c0104100c441060b0001c2c2482c400c01c005210250383d100d0711031810359404640d6415002a649401d030001c004106000c00b190241c3c2c040001c06601140d08402a140184020300070b45030b490603154202c8808842c810b002c24480d5000c107000c1440c1c02c0c003401c01595801002620300703803500204601c4a50702e421034141001d4620070070003040402e0140c2143c2003040d00040c90450f500d55030180c590201e005489040650fa404008141407194100c54010010128401d41550f1204003d0b5120301241c083d4403001c00c1c0f442c2c1c20f551044110310600e80c016815690307450402d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 897977976 1250 897976726 897976733
    0x30308090d050322050d09050a090c05120c090405070f020f060108070e04052113050d020904151806090516060c0b070915020109020f0a0e180114090a030806060406020307 75
    0x1c40c3c84150100c400d405a14044001440070046c240704403180d0707103e0302c01e00c1e031605082019208803900400d042074205000010310503044401d4a811054100900d00150b9881c480c004443c02000320159105003030500f0b000c101030b0010700300e13010640c0039400d8034519004640c0140d80d80c0001e20030100c80c0d41c040072080000501d08000690481e1240e02a90000d07560142042200095408503441c0e40c0c8002a0030510110001c0001c002410250ba8540c10502160001513080c04000c0001d8410140c002c680d12203594030780d001991035084101a2510004d032424001c000345104038040340c05124000800341040042d84100003101c01540d43c0010418043c0d469200504003d05040e09014800c0c070003052501e00c80c44c9141400e00300740d00015080c00c59004114920100050240c001e4140d06800d1064150000180d0351010a058452000703030140d608031401088c5100f13054180c441c1900c0ad02000700d0000c109800300d1030081d5294180381d103d9004204082c8030328846e0001581c020032000000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 897979226 1250 897977976 897978001
    0xa110a050d020f131118090f010b18030f100f05091603060c020102120106170a0501060525170d05060301180209061f020a1b0815090a020d060501030308090d0503 71
    0x45001c98032005c81d00061342c8006124a070055285840c40b1181c041b030314021410200c0000c0da03c0342d103060381d185c030f294500840e40d8111300c5110301b0102d020390300c042041c0039603c3c208541e54a128185040f03622052204001d50002e08500c3d6071a030301103080c400400e040340c5002032400354810341140064812741ca1640c88000400c7e14040a4040d13540911102d04541c0440113458000e10301d9446881c01c2148000d078a21400c0700007483c83c00c8240c980300042c400c1590004c20f0715520310040303501f1207011244404000b04240c0d040b030001d06040712001c042e107101c81048007400e04502660014099500c4040402d07090701d0015010746d05030b1a0181e501d01c0907140400d4501d410a40c00307062681003901460681e4040d55880440360050303481a030340304040000c656240900308400c210f05508603428032400e40e4458511b000503900d8007142101091064100b0f0081003004e80d40103100040c05c6500d458001c000d080700340b20541c08100c3c0400000e000900116940e100076135141e60703e528540d10400131608 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 897980476 1250 897979226 897979249
    0x9031e0c23241f1a04080f0a170a0207030506100f0f060806061c09030521040b16050d05091c021504080c0709050c091005120c0a030e0a110a050d020f 66
    0x4643d200074400074680b4607280c000c0e031151100781c0002c0d507180e081461440ca401342c10710400c050f651000070011701040300c40d800200c5c0e0f6100010910f0351b500440c0c60403498024160800342250290006100c49400c29401002c1200c040e24100302c4455502c0305441c00040b440c0c8101c602044040d80083e4051410740000c180c04d20350703610801c160b5030502081e141164008142140441c03800940a40650303042005c1d0701034000100452102031406075104821101e01501c2c800b1044102c90101041d140103e0585140381d811305000c20042c0b400820b0741e41c0d10040035002401174210b003c0f510b1103039403000c0f07164080e01d814401c1e040c920340c403a9610100c6d15440794034480342c0340c02961400f00d0000b0050040602507a03050384055200c0d00d80381d0400c140c1d03800e0b0034032620921200700044480308e00891205030b4032461032981640c48042140b0203901034030500c2e80054240c062210410700f0808074580490344a40309072840010349807181c00b4000b5000388420040d40c072000c1444035805514000740100c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 897981726 1250 897980476 897980521
    0x150819150b0705060a0f0b01020703080c0f061e07050a020307030c06060b04060305100501020304060f05091c060c030b06031504090c0b040f150309031e0c2324 70
    0x1035003299035001601982e0404842141da07a040764060100302040c42c0a003405018008504005501300e480c0017035170b01c40306448024402040410700350400d1000340508282808000180c80351440c014a0080280d5444511401c280034418040f50001d0304c07070820340f05204000d0f002949031001589007a1050040c140c2c0c01c035045038542101181881c590800391008145584004c281410001107844013084e59800190465209110411100d0b46c09843e100e205011400d00c60766507180540414000d07518000c151140c000000c85120402c152030740080414a0265410400940c01d281006968842039500703101d900c0010f0184d145a240c660700110701584203903d030183c01030380c80b089003440f0340055012007440480714404018096106d5122104101985001c100d4411541e401030480d0002c06650014816551700c620b11140c0180d42c103000240c4c021170300308250300702260607110b015000803021400f40107051140700c140c00300c0a11401c8800c5000760194a581c1c84283e1114507612407889079 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 897982976 1250 897981726 897981761
    0x406060305120705010b0d02010f08040602090409150c03060302030c130204081213060e0a09021606110c0c03060402130e0a06090501091727040f020c07150819 70
    0x400500200400d1011200b88003055480e44240d007800c0d070860350b00260007402440c0c84210740005030b9212403403410f100f0560501007200e88880c10904000c2c0640540c29800528000c2c0b15414081019112055014484001d000b0325011000071010b4a29901c8020b40541c004a051511b40c40d100140b40e40c4251031800040c01c00d641c03800204c0c40e00510042540150781c0000700614420700d02e854440151031b00382407210410b00500003180b10340c402c40c402c00c0705617070f404a45a640c01201031010581c02d50004000d10100030715075007a48081d800030129408d58462045407114504011410501c6140c0040000d82da2646001c00000500044e6002d00ca0b58004c00040c280000d21611403d4405c43c000c40c000240c4c4191458000a00102d001440041140a00060960001086500101c0a5904050003401850340003240141081c0300f007413210700b800450181c4030300100040074411035059040c15601c2c0140c01a0a440d611021388002002003142040307001c0280e26904001842c24010384075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 897984226 1250 897982976 897982979
    0x180b01091a090f0f0c03010807060c11040f151a0712031103040302010e1009080a0e0a09020c0c03070b12070e0310050f06130c0905011d0a0824100e040606 68
    0x108040011503216103048180010300050392000715130a0b034050102038070b0b54907550404440503600c9419100d04401c020b5240404c0040003403144050200000c042c0082c000764410101b40400b601d01c1d201d001d040c2503401000080e03140f2902c10b00c25400d001072a03610b8505002a140c201e2076800101c010f10626440d18401c8560010102c0154030540c025800010700c0c6484100c1d8904000c89240f08050b95030910b0704030b2000c00c0c1400c0866003d06194102002c92680003800700c0c029415507071100049510109500d07180700c00204655844140890517940f5650702e80e103024030580540c0c214101d4002800001510300350284188400188004040310121200c010813041990012501601c0201e040e00c04d01c441070406101c50010410140018080007480c014004c0158046115950400c80c0d00c940b02c0300c1c440d4032860000c42220000d48012826600c82440d02e64800381c404559503641450052032901903d01c03450306004421518601c080949401c20584c0818805481030314290745c0d5840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 897985476 1250 897984226 897984229
    0xf071a03090c06030c0705010b013b280b1e1c020a0309030e010906050a0509060d0e061f18020708090a080115050a0e07110a06020a0c06180b01091a 65
    0x1651140d45560600d0b41c3d10825440d11f00e0958140d8a40c050500052000c4d0340b00c069011501000da4210f00070b2000c580c03151059020740003015a240031900840d6507030490705041045d400c0b558420204000d14034030035030750f0304034014184900c01c1d401c40b20240c6075030350000d504e00e820028024203094010a00c00321400501c08003c0340d02c01c81036440442c5d99101c16800301a004120408841c0003402c5c0241490301d8248003400750300c203084440702002000510400103540d48400d0b6644a444510100590f14503407001c15a90740301901c1c55100284c10502040d4030303e20200400040da2048903040002c18055010440650003030201194001c1040c06004840e841e503030031004c000e2a4030f100100c0c000c840300d1700e00810503078690000da0040d018007805001c8490341c800c049030424a6480c00410703441070303c1040c60402c0300045004040344d00004c4c11103009a8000061100343c0d01480d002c04c00002c001040f031b280010340f2580186845980001040712001c2a8892445902e138214001c601d100c0030740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 897986726 1250 897985476 897985489
    0x1b0602030f0a0605120a0221070308041a0f0409020a030603060212041514060d0309030c03260a36080a0b160c0b060411030a09050f071a03090c 63
    0x700d601007080003000410600c2e880c1d5014040007040f003955042104040c2c40040741c0c0f203803d60301010f8011020000141100600d90b008000204544000c0d26045500d0f4505110550b009100721180c2e2100740003e43e0041c2e4a4404460000440c10f0401d4078140c9000d500c4006904501c81040503d82c2c0c2700c01c0040800c119000a24940080045080e55072500d46400c0c0d60b05854030184c400118588402003001038141070fa11600420100c0d4540001d034074614045403140c0da6600000d114203080c0800200300144812442e20303401100e241520405555440305040d8040e100d0a04001115400c0d00c0038100c3d0181c0c1030385070079007180c1902c5c00c6d800c07580500788a41800d543d208501a0384024226800d00400021054005540c5003c082d481c3c1900390006040040004004e0b1041c04100042961607a595218141141c101d41d544d5480745400300d4075400400000744181c0750350240d0308442c0001a0042000f80c2136650841c10058034181030540c090340c5070801050b540840c4100c1800c0c3d055a80c445 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 897987976 1250 897986726 897986731
    0x4120c09020f07031205220f0218070318020a0605180a1d100506030f280b030d0311030109090609142b050304060e0114011814060306071b060203 64
    0x481c08540c0d5892502d0000d117052200788007400614581024002c0c280d50b0844d8125401000400b0000e071805181070070588881512030081d440303200304400c1c2144800c8101018419280368030100195182001c50b6003094484001c02544400040020702806014101405c00303001c416400340c05100c0f9010224510800030341200c3d0042841344410f000014036905440e82c009550f400c05082d4501c0c00c8007040103070101030030f82402d42071080000388140418013403120103c03480400701400c010070015208028555510b429000e40034010340c0555050007800341344c0d101414404440c1c0b8603803030040320000034441400c0403941140c4403001c000209070344150352801040b0f4040a4000d8183c0c4411000460310510140c0d582c1c0d03407181c0310509404e604041640d5009800100100e021034400c490203004040d0450040e580030b40c0e00c00042407131030005070040380c00e00f100c003420803100c10082030fa6504000e080381c5481d0726502410008851030b200700c1100048000c003107003590014130b041e910141a42c004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 897989226 1250 897987976 897987997
    0x70c0816051e01060f08071410022514010e01091505040b12090f120d0b0f030a0308011503061a090102030f030a0c0306380c010603080c07081204120c0902 68
    0x104c19040c015450420007150081c541c0710000c4c104180f0301400100901c9084414510541d02629824003c50003807020341048000c1900801403d04114081c0102c01061300403030a09010100107040d442d40141944050002c0c16140c01903070700d03c1e04480894600d0ba8501c500100642480001002d048220160010386a044017641c800d1902d42c4155180000c020b800e00c1c1523502000641610100c4081150501d8048403004202c09151201240c25070745924643c68061041c4090102495403258541b0f050303441818403000000c4030020120140d9546000700d0108405140f40c9a00c5661014010000e03d041070059a050190604041c141504102e9460710307400c2c0c0b159900041a41e01d0302c918000f5141040d9150130180c01f10500b5400650020782100140c00342c00c445421020340b02d02a100c0f04610500280415602c034909011550001003441c1d405206080010804280100c3d40c1c2d41a400c4c90a9814203040c9410300d0700b80c031000a41810b9440c0c14064401140824560004201c0c9402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 897990476 1250 897989226 897989231
    0x3030609050906060a060e0a17010203040510110d020304150e160504020f1615050c09180705120a0212040b0105011205090607030902040204090204120506070c0816051e01 75
    0x103846061026500020040c404607000002002842d55514130035a05651031450003001e600d4613600898a484200e03045a4260006100d9400d040c01c01500214451482002078800140000b81100103490310880d1b1920311000030b000740300c0324400c103901450340305000d0189400d031406400000070440d04a40c1c3e90102a400605043d082184d51502c4d1500900058130110700e01030a41000a86602400406488240c044814032041c803204130203072042240703a800108450f09100c03025900c10b03031116212070b0042c00440c0c000d0380010100d8900522900682d10744900d09491240803400081c002007014100e1682400002124020403250703500c10707031007480c2100d40d40d4107003000901510744007941010000d0401c400c200320710030041142a000740b61400d021409101a20014003c3c1c0550b03046100414800300d00003440c5101a21151000b90259055401c103450ba44411140e61a00550142c0155007c04c566410251691703402100f00b40503005075043c401038800b944000d4404141c00d505142e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 897991726 1250 897990476 897990479
    0x120b060708070f0506010806040b01050103240b03012105100518010c02060a0b060702010c03080604060e0c04140102030a0e010810171e15040210021c0c0b13031e110307030306 77
    0x1341000194050a4082c00a101a150560b601d030b4002c041401024101925180801c1808805000900500e0540c013060210180c0f00d0982400c540c1003480740d10b04a44d280d007185041d9801c2140a0000503400c400a80080401101120003524020300f617120b903120342001e003003d004070a21500600800b036501a080c18103240c00201c0650350380c02d04042c801e507002c00c14900140e0300114010400d581c1410003290300da40d800000f5008040903803000e80b45045441c10403014000b124000c2c0199003c0321552103152099400480c0d0301d00580e8204004940c0f10701a042c190342c01408a90740c030103200500962030750307281c0d45903203482c1c110140c0c4410030340d000388620400014505100441040c41c1c400821607805940c0ca4032623400405040a40142c00014402c1c000174800c1c401c8003002401080c104c207140c002000c000700155a145d10070381d41c1a00e9500416254160300846c00501d64042e030320038240603050034000380da14800405080500016200c4040700c03a0040c8090442280030780c80028509 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 897992976 1250 897991726 897991733
    0x1b0c1302040f3303180c0e0a11040e04020316030317060f1008090a05070e01030c0602010b130b220902120601060f0c030306050316061e120b060708070f 67
    0xb8402e80c1c0044002203000c41c0e1030a22030003040c1030700d00c0c041c40701d203016010050320b0300003a0020800c402034481584d020401003c28810315103203140071118441102c81455541c03401d150b0480d46450a40071800100700003c0000914141e041500300f17000a0682d140710a0144994070030300d080360320440125100c441850307209038055524507400300c002d0b40d408110081f50000101880e0f03070f44c0104424854104041001e1170420003000e060243e106080f074903141d0b03c0f601c001901440900c41161095481c14021901c14418096100c2c030500242501403c000d0301458000544024400360b07800440400140b030742e000816a840d15100303180c0340c2c0003a1940090050010034000303100100c1c8540e1110004120069000c1c40c4520801e2862034842c42594491030110041d0500d43c0c40950700d80700c6e011000805086002d2060112441903c40341820041c1c026541c1c10110106000e0b00801d104000c4d000d2400043e40000c078a041008211034034210007076881c40d0f1300e5040300d1015107504220302000001c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 897994226 1250 897992976 897992999
    0x9060103290114100e0f011404090906050609090304080a11040f110d0f050103020612100e090105071d210f0f0706090e1b090604080f0a0201231b0c130204 68
    0x41340300310320300300e4128141203011945044c0209029810403440d10044c070f2064100c80140e074090420803009220a86860412502411080d83c9161041c0c203840041a07001c10004210340480c2e20360000b414140140d52a803c000210446403203401c1900d035140e051040449100b21040b40b40940da00390384070000ba05540301142d54100103805c55616103001030001da038030003042c0c4402aa00241548141d61881316100c91050140d0042c48041c04840a1000d03c1c1010b420051140401e0742e1a402c894040100c0d031900c0c503006509841c0c011044920010700f24915001e11092072107050304480d041c442854120b4605220825100025000b50800b802503680c03104440005041e240100c51240c01c3c10545c0c41c0c180141500111810200000c0020035070f12007006850080003c801a10341c8488050602521400280812070020302c12034140103002c46002055110303021460041d03400c0c443c144002c030701a0340b000e01e102002c510544208508641e5421011004044034550158807140340c0b80c8802c48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 897995476 1250 897994226 897994249
    0x40b090606100206060d020d12080723091203190504030215030702030f0c100c030902210a0209150603040f0c080106032d1b061709060103290114 64
    0x3240042e240c010280307650004129030407100442d0002c1d0712180d10b10003d01c8aa201100080040512081c1f80c1d003002c0e084083e240c4102810b441d4200d98000301009000d0310030401508411500c8248041c546908003140040c82c0c1400b0601103070b00d820a50402607035415401c084150019034001030500441c2405030310801c412407100c101a003142001c00010b900c034014420300b20140750740804c061203100000c00101060401c82481000122010071b8014007420341031400b41d0040441040c01120001c107011014000c003442000742060003119800c00000c4540941103851b1955001c54141c00b541d191001540928031a0b01000081c0c052464000000c2600350700041450f4500681000441d6802038412180000c2c0c0045e5501c01c05101c3c1c40c010803182881d0301030701c03110340d9800c12454a0018101181520b22a44400c61090340700c0104008044080b140010140c012200400005114042c4c0c0000100300c62a6000003000421604c81c4070b0000368001201c40510101403441407d05c107400d40e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 897996726 1250 897995476 897995479
    0xc0703030f02030f0c0a020115090c030c09080601061d1521060d0f2102011d0601181508030c010c1103090315071115010302040c1b0f031205040b090606 67
    0x50862400213244100d840c401008600c81e0380c40020078030250b0740300b0b40c08204204e1003038032283c82458442c441d400041c58404a24030210b8502440303062100d024102e864200c1e006880208000c0c0e007442d0041300e00181c09603e03901d4283d20404080116580e40d4001e1603018001e10503c0d07120844002503003c14503545414020320035036901402200c2e1581d000580302e4540007011000c05011030700d0a01c0c0800740e80c0380d800b405d40100c0e903a802c50740365064100b0090860b040d15004280da61007419140c58000a22440b000c1c10030801c40c1102920080d001400032000e00581e40c2681e60741d170308601d4103544c00382084034201d940d10385101000c59001510404004550b0f00118181000304012aa88500401e07400c6040c420325800580f41c00d204007a080544103865081d1072680082500d074400851007800100e02c6a030500c039840d80594456080d0204659125907022554003164444040b00b50400100303808012091300b1f40c5142c0541c50041c64000c51058488803074500c0c1000c201803c0c02c0001d012207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 897997976 1250 897996726 897996731
    0x1a15040f2d0b07290f01090c050a020c040f020405030d09051801080c010c0c050607030c0c0b03192004080606031218040e070905040b010e060612070c020a030b0c0703030f 75
    0x10311408003000192516030b58003044955402022074000d41300c1950319000040d4a5030340000300034070030300e00443e0741e4100c0da10b102050040b4948030b0010b1340d89002c3c880390038006a020341010780e02450b09800c88245040c0d10a030052a00ea1140c2c00f003800c2840c2c001100700450001c3c03000300014101035440f0b004074040118000503d5041c824560707140c170138070784405040020030700841c014402000c0030180200001016140d54035820b140203041030132940d17810741c0d24420007540007902c800f40400f01c91060003414150018080c0b8454202d0082440c03c0c1420300310b80204a924034905113a400070405000c11030300410041c90004201032810b6811414101f0002c400e0215054244254401516416046030003203000138100d0002481c21030349900c1061802d042038240014000072210136410781d000800c42804555442007448000d1107460444221941740800242c1c58910510180781e0040c4014481e642d42035032034603405e80c00c0c0c1040d200c0710464200011030300100740d0584544000e580c1c044505 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 897999226 1250 897997976 897997979
    0xf0c0503090705041505010e031c0e010e09090a02060f120c0d1802090a0902040b04020d0507080c03040510180c171513030509030a0c120b0603011a15040f2d 69
    0x17120000300181c400e243c14400340020414031030ba000d00c042d09594818054410843c114030900421040d48514002d0109811500340200c41c205154814840c030840001806252019420302010764001e80c1081d00f0540240700c285c0103901d8000e0780038042c00040552079203420920064404a4820b9845030720103c00310421800140c0310400c2466102d02d03a0440025500710500228024cc4154a4259400740c400900d03851410001e500c110300900304d660318100300c3d94400800710860b210985014119510030b0a045180400c0c5130040b4400c0074000b40340068000341541c03400c0c00d034006a000010160b1210300000c20703a000400c500012310031380100f039000504003a940003000c4507118034041d0812000040c074451646082000d090580c0d13112580c10822550750741c809448510448007140c6090614021482500d4140200c1a12034501031020513803103120401c0100b44280c0c128180a65035041c40000340c0315880483c071a0007003a24103c2c200d02a50030540711640b9080080385a040f41e1080d420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 898000476 1250 897999226 897999251
    0xe0a110a1d04020d0609050109050106020607021903210507020c0406030201050711010e1e040f05090d0305070917160602030f071b030c24050c150a0f0c050309070504 73
    0x800c80e041e000c044005800712065030300414040e106040408180c5070500500080700c084980c01541219036010b010041a40c80703803412a124074080d150040181d20003061003800303c2000c1040c80031588a03040c00703040448002c0001e0300d12900b40f4842040e00d5981c00411107100d80601c481500321108880800045095500180041c05140e1340504440c0d110f11004140340d020340402c088190303006241c41a01c1a5020f502c9420420704025030340110308205003c000d944603809414012070b80e2a014040003001441b0440003131600411304401c0001e14100000e1040c002d601b0100156841c0020744010080a0300c442d40484007944440d00310b50003000114090700d0150240c0b003409a1000c40b81c03011590b0b08141340326455090300050040b034540f00000030542c20200d40c1d207906031980d03c11100141503072102698127000b00300400c4000d810413114a03881080b984a62a4050701c401000120710084204031401ca908001032600424000410f01000350000c000000090000b00d605100f075010f540c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 898001726 1250 898000476 898000487
    0x7051909050102100e0304260c0102010c0e060c010b060309030409051f06080a09050318030124050f041107060507080a0905190f06092003011406280e0a110a 69
    0x4013400c0c0e0aa80c2d014044544d801841124002c1c5088081c12100704840540c103103107500143e995281610440c03481e0060f550041c0a2042a10001d444511419514106020040d881f410003048103560358841150641e842002544c00350300301c0710066840c1c2d828141c5e40000c0b103001500d066070030504c0c1d07004580424842c0e007400e81507400ca80362000040c2c031034120354400b401c00c8120050840c0404155641440100c02030449094002c400a00c524040c8105e01006c8a500322854005150311400520083c10480da8490b40c04002401c00107440d91001c2102d03009400c02c7c0c0017114415124010700055681c004106500640810130411034180c0d19610303550b44034101706d900c919001041c0e003581d042c409440e401c00d10060f0410001c1c003010001e4603004002150004018250340d4070540349440785d090501c100fa0541c400c0754803aa4413921220101f0a0840000720100c00812010130a02c01c0c4540e00c0d0684c10090081880e0780e01d031402c143c00d40348240c130140994042600000d0200305481503001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 898002976 1250 898001726 898001743
    0x15051c0609020a03080f07060b0108060a140f1302070c0506130303031812020c01020613200d050709090201170f0f2703090f0a0303080103081303020907051909050102 73
    0x1000006615441d03102040c4180195800500a030402040c0805e000200360000c10329284154020072845154400550703071a2816501143c00c075403100000d10900c0d041c41c0140d070a400d001000b400c90385a14600080381000c0031268416015004504001004400d40d0218041d01044a0300381c00e041701036000c0711561442d80b0010342016112301039801c440b41c4140002c0440d81d00709400301c05c0ca03c07104501a5450311100995030040c4034100002e1800e0308410840c010740e44d8040440040e44200c2890f20941c074481d80840795106110790032810000d03c04001c071000901841e400440e02c00030500024001070581d40126048034041020015540801d1541c0c99010807520000c1c5d20645a5030024400040c01d4049007424100d00b14001000c07110000c082d000d1540221290343e0040105014410119000c1c48002c02182c1c01000600008070100c002d850b0b03030b020f062010b0710081c0d9a40c0020f5014034040d034100011440c0000c01d000d0040940c4480484050181007002c0070526001c0000c0da078403481e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 898004226 1250 898002976 898002983
    0x213090608010b090f130f030c030e0f01210216050d0801090212062709010608120a0e130902060d0c12060f060c050a050d02150106080105010504141206070315051c 72
    0x20000141c1c641a1840a0400341c2d1f40184030184034a1181c40d002d0007400100d00c0680224004074580d84c62341c580041801d95924042e904c10840d12040710a10342c41d40401180c00ca6482d40038460b80c0c4034898141c0340034403464010001801d0a80d00d41001400844042e0404480070340100301c0044d205001c5000390b5080345040e50400c094651241954111074188584501c01a4042c000d104030300f281500411300703980740c05e01900e41c076401503404040184504404200420b0401104454500d486521000b6104800380003180f0540143c3c00a90140e00100b9840711869644027500220780d8001a111005400b281d8208585802c260404450800c0323886000c1c10400d2066201003044800c0c01078807542944401111130990010350069214400e1340b05200200e040d0b0000000c400e807242404034100d40c01a140c841c9480c3c2055541780d506144441986e8001d501c2081444480c0f104000540c40781c0b10316940003510a0461030790601c80c1d900c41c2d101a206499058001503203005102001003100e92 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 898005476 1250 898004226 898004251
    0x1d160503220c060e030a02030606010f0c050d0810050f0102060a153c0e070c060e1501080f0102040605122a0a0207060c15110c010213090608010b09 65
    0x881c01c801c0465052520001c0c104407500308000d2081100800c1414195501901c40b01460b690100c14180e948460650195040d4030402c0459800c4d402114074107143d5100b49810021050580c4808d4a400d11a45004000a010000300b1405002d482900c2c4040c01c0200e030b98a10340522840000d40d140d00207462418030071b543c1c00079013400b0620301c1c254000400c17582c000c0c4804900c98407044d80d0700c219030060313085a881c0e01086028041c540c07c01c510056a840003103c510715103030f030f1000b12040380c003450080311215910740345c01e006500300f0800c89400d5074178440403e13415810000e500e404c0152001c045150350307005210a0002e1508941910011150125401041d640e400c1d841035a00c001c00d44045031500d803418180146881080007000e84070750b0354089952182c0c0d110720844042a81580c040c005c2006070000c0c80144c14182c00190380089550603107403c0c41e0341c50900500b240d2200958843c1c881d0014410884800180074600040c4008c030000c002184900c400b050a030f003002005170381e0941 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 898006726 1250 898005476 898005481
    0x7080403080c090307030c031205071707030c0b13050706091401080a020d111b0d0e0103020a031b050909010e012103030e07030f150e1018021305011d160503 69
    0x41010040c3ca030002c000400300d45072250307281841607900c88240000c2d24510185581c40030514011012075004030385c40004000340340000c4001580031740045104808108810304c010004c682c5d125195400b82510f83e29412520700103140c050f107802500d600900500111040420180c0500010301103600428203145115640e0310f5079a000900c540c06020030401d282c101070668008409020f03142c002c01c80020309110041c2c100d44103950740c4004c0b1b018400502001e8185160394030a401902c02c445075401d0104428140c1e41103030b24500f80c1003000f000042c10110360009107152004100e80100040a0f904540d941007190301d5103455140861159946566805601010301c41e07400400c1013000c00c015180116224030744200b0400e070000c0180c0f070100d020301c50181083d070385100340340d1074240e047c0041030020400d000c1e4501600c8005007010310001702205040c00742e1101c00c080903228001034400034456041c00b00b610034007074410f1841c8450b80648020000c00b03200e099001c503a80300b2141171254481d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 898007976 1250 898006726 898006741
    0x1b051903210203011a090609010f0c0605280501081506031006150306050102031801031d0105390702040914010207051b0d02280305030a050d050c030708040308 70
    0x1040003908002451a40c1c940e000e144410350350296040c2c442e000c19400c8041800b29a403600341c041c10b0f1100750f010400300716000d031940c01400d01c854802400d041544000f00c160711403c3c03c6400072a81d014000c0c001e0740c02a560401c003540148480c800c40c420401265041000166075085a030701d400d41c02c0c04845c070105050b40d81c200f02542d079400110b2400d03c4030640303130101842d04c0700403103240360702107030904002054541c000700590304103120b0f800c00c56110f000b405c4011000f510940203880429003206c80e25070007200e028040c075446181c8800101101c0c18040a00400d604903d2000143c5285220088052482039104492080340c040310003091200303060602a42440400c1049240c0d90300c00103843c801c20070040342d000d201881d04a000800000e05000340082c040042000942c4003c80c00d140001001414040f1101868900c8010244a071030740d6485146501182603080030540204070400e4501c81030095660150b80350072079900b9070800060140036081d0107000182408001c10014500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 898009226 1250 898007976 898007987
    0xc020c01050c0318011b030e031204080c0f040b13020715090f030e01021608161a0d0e0f070f080714011707170c0c0610060c2414071b051903 62
    0x24404542c4107415908503500d0041c0100c40614203e50003405800c10034514030ad031441c192402c884144001d000c0148011040007204180e20b203496a10071340c1c440040c0d503151a04070f0700c82000c44c525200169171341aa03003040d06c0c901c0c054082d101d04950800702804001000d8100c0012030700e50500384a50699040c0b0010b038181480840381d5420710310380900c00075030b4800010312000c65020140907510764a4840d611452164104054040c1c5481c0c204000c00700720b1032641c000d8200006403810350703008451021501d420000c03039030310000303614149039410300180c00d00b446a0402440c140642d1510040040c001818030415815000040b5001320001141c05014014500709007411001d0f0b0b400030b10700700300060040e403c44c583d064440c0c4100b400207504144001c00c1c1070199031031030320707040504450340d41c07000051500c0000c4221000d40342048040d5964045c06004402105071026008a107005800104056540300741c10f124102d9000000010940104000426a02407002100740d9556400c041c0c60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 898010476 1250 898009226 898009247
    0x50403020d0f030810050a1502030f1204030f081e040f0b16030c090b0405060a0207080607020106050405090c0d0b09011d0a1b030b0a150b0a030c020c01050c031801 72
    0x410900c075800c8041007152200100400030702c40d031903000e4542c41d44c0e0040500d59400d03008060b002250218148a0403184405e18284940c281c03044074a0060140c00000194000c0403558404500a2052101b01600b1070790120514041c1d18100300e0601c0d0840c0c42c1b461059001e00070f0202c111b04a00803d051106a645d0645050b81049000d240e82c102201c43c50601d05034a207241c00000d28200424401a10555495003110f82440c4098101400c0608001d55588009050703010b5100740c2e0000034400c83e00b44116032003078405400010b4580d00d4502800b0543e900140200d140d50050424020360f5900c400741e039400f181d0420400012641c41031022401040c50006110340c15200e1041d032074110303600040405000340300380c812400d101050302c0e50a103074a64500000345901c10740030008004c000c6503030240100380f03905003a584182c1e80d02c0a04164591045412a000a8a843d540e861858042007603910300c84007880d21524100d10b461902d6180d006202140003c1d000c281052002c0b03a108054848 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 898011726 1250 898010476 898010479
    0xa0605060307020c0103050c090f040b1206010e090709021227011802030d0c0327050d0b161814030304030b090d02070509370203070203090f0307050609010f05040302 73
    0x195a410182c0d00a9541d05526104500090410001440043d5604140c03100d00b1000340003103014050310801c10000e081c070080401d030494010b048243c21076500b000007a0003007030009491101801e10340b0f443c600f0040d040c1c201010b00b81c010010a0f081c4001003480746e27844008040c030041a02100203004810440707024082c0b001d0f600302000551f0800f110420039966a02c200c040340e442d54410901520b86000b40070001c0c000c03903140c0280504070b810b440c80300984820568004401907440d40d00190700f44403041e41c1a109084c0c1901004909141ca0b144015072507030f0f50070580700281003000f120520718190b000f43c10002102e80300707500241d00d08009480c080c5a21200d013480ba890f00111a56444882d44880d1006100d400c0c0300107010304015070a240240b1480242000484000320341490740b000c102d80503541800c0c00a8205143e40542c0b0195000364081d0f03020310365518a000411025400c55403415200360010002046a03941e000700300d944074807003030a14030400c02c805541a121801a5070010307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 898012976 1250 898011726 898011739
    0x109050f0a031b0f050405010e2d1303030b0a0807090e0106091a33030613090c062a12050408150a2703050903031c062103050307080a0605 61
    0x210b0420f44072140e5605690542d484024266910700800003034034400e11442c8000302c44280840c007000287c14281d002001e031401c01c01c21070401e05902120a500407200d24401502c6400c0300c1040550601030401031400031500001e00e1800c01d441d01e5110f1507988a582c020640d103270400280210203420600052803001030070403c024081c0a05072218001c0440240707d050b60405141d90481c191110a040c3c50f544d0341e45c200c0d44c0340c18080d15003540d0700180030300d0390001181044540070b80303150044154440c4030b003000c01c4e8442c6c07030504d001c3d2040c0800705040e03a041425140c1001c0070781160b450b607160a500061140c841030303002038055410f442030fa00251200e000b510f90801c1c01c0c02542e104140034419000c8100031042c4031402c00090960204c0d001d044031011201920007191188000c0e02209000400f9a440c002000460550340c0300c000c0c0443e001682c4401c0100620045071004079000b01600e080c85081c1c642d1554024401c0c44010114024000c5030000f0a4200c0b541d0751001c1c001e414081c1c8032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 898014226 1250 898012976 898013003
    0x1c03150503121b070b070f06020f03040606030c1a0f090111101505010c02060a080a022b051506071b15020303090105010602071d040609020a181a0109050f0a03 70
    0x20102c0b42e0b0010711901d2074101580215002607a0004401342103502918240341041d110743c0e0f8401d1681e14442013994015024070084006c40d034600011400789129034030001c1d540e4a58a0404a46c44203984852421034004c8070801d0889510021607000c0e907150b03d4076a94500c240300040e100d810000300201d205118180041100b4441640a5200b1a06040d600820541d1f1140116160b2100d02e40003504101c06000c003a803240c3c0905c9840b038011060724405030034003014840000016200b101016100c081c1420701041400281c800d090b0069100d02003002e40c1007100001c034805104500340100050410480141c00741106181000a000581074030a244006540c0081d501e410075138110700c4652030440005400d5000150304003c460740c0100341c4c1d010400c0441000c412041c020410748081e5114445800182d881000144c0500302c0c650042c8505101c1d840c082c2c081f0780065449005566000c10170716500d0ba082a01c11003204c030116a002c0d603a03810300380440d50b9080d450780018886050030f2070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 898015476 1250 898014226 898014253
    0xe0d03151806030539060426010e0a0b060303070812070504090507030203040516032607020d29010b0702040906020c010501030606050f221107170403141c03150503 72
    0xc02000c1881c9500c03101d1714400010501450b172804002525400002004204000b051038002c5c156248a0f00d19658805900c1d03024a03820744003810b09070f00c25500402001010804014811f0b034005c802500210b0038018940ea0742c0401e4451705407a481c1e807410000000c2d1074181310310103d07005800c060500f071009082c520009406504162411641d6000c0c00c20755182420880054404680c0c00c00c50745200031079004000031840703103da14164090b10003040405c02603114000084402d0b40b00c0c0e94030450f910b06004201d81c0d110508c940c40a118007145004102c000b6102c020f40b50060b804940000c0c0300300040c90614000d100b400540707121942040000000c2c40402c0e030200040752810788902102401e0a0204010341441d180070003a2005100e5440c80c050000d544843c0c20190034802c0705d854521580c465040b00c0040042501020000040c05e00400c40d601c581c801e41c5804082c0288002c52090341e242c0c5819004481040c1019500c401d40c8900740030000c030440c01400c000d0265003c02100e0b44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 898016726 1250 898015476 898015513
    0x3090706031e0c0c1505041709010c02060f0408070f240c02090406061404110706090512030108060702010f2d061a03010e071701060e010c060e010e0d031518060305 72
    0x20940d1715046600900c12444020f0207824031560340412130500e11700d95091002019088080b1141c10002d00016180050f1680001426207004640e0029121440c00d00500d28008268114a040030000704040162000729030110040401441217802d4180c4c44e951700710345052180038081d51000100080c0020b0120540c84081030315000140741c1130304180c0d003090005903000e9031380d0009110720400c41a000304032151b00c4041034510880c2070366036042c4020400c083c3d680085c0c00003d1544c1261052100040d024868840e038444509014042c0c0200c48500090a0a15200707061500390600c10040e4041e005034403420151901202400360827002101c1c100c0e841d0424002c6644000c020f00109188500420041d100000d01d42c0041132240c0c04c0160480e4010072541d0140c1c144485e00e45142c0014100717005418941c0030b02000040c1044892582600d812440b1180314181464813100010a041c91602c0509072503160000412100d82e03854030100030085540040c000d8000d42d64158030045080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 898017976 1250 898016726 898016747
    0x80f1c02130e0705120604021207200c0604090c020a0602041d06040b0a06111f091e26090301060b070c0b0a02031614010e03041a03090706031e0c 64
    0x49500d03101142c44a9180d00d03048029225000810342c02e00a0341c44003140c1e04005507110b0405003000d41000ea00c1a00d03d510382d002a126076011038002c00c4100c1c0700600d0007013040b080410a0000b4408a06c0e00808549a44a14040d07a00c05c1600c40451108860080003080d208035408541103649a0f6104010917a13215282c0940400030f00450108155280502030b421071844000c00050b01d0514000c2e0903a1342d681003503400340190203100200b0343c000180350016044842400d401050300c40c268a0a0800e5560a540300030a00c1213130910040819910100c069201c802020580768121252101c01d90030301503005101e61641c28040c000c900a034601005d0704134144102000140c603503c460024109001d13076400340005a0052049400b0702c0d80d1581c251001501540004078a252403031651420f550100002049a6000003400c2280101d40b0802c6040c3c0c0100c000302c0c0b030031414500c0c140c5031544054400c0d10700701905c62040f407030a11420340c0d0310340f80400c0000c000c00241c0c042e08405019075604 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 898019226 1250 898017976 898017997
    0xe10030e120c0d091a130e0108071a0307200a060203040615050307120b04080c030711100e03120c01060e01060806180105060a0c0809030106080c0405180604080f1c02 73
    0x483d43c0c0380500c14000d40e05a0255200c0500d41e500101e000b100139200b80c3c0080c1405440030b41d941100146000d080c4403468043c061708401f03481240d090100d02c41c00700160420b4400120003c208000b02036a000c403980c06101c807542d600341c000c01c552088003494008400400b0700000d00c00800c4c84104540740e0b03c2203002500d080300320540d8980d60810540c50304802c2c400e80785401e006030108000110100a0030341e0292040b44414200480005418990f401c00702c400ca1708804410500802d61404ca00c091541140900c0c0c000c4801d030454002ca601c807201c403580713a6407054000c200340c541014290040300150500501a8034550b9503890020514a02503907401e020f4591229080c600ea1003100d2041c1c142c88024141928000c042d480031526517002c850159102d6900303110206280c1e90030301540c0010503001c3d0040801510711802c0108031440a0a03c54003101ca07020b040364118004030325190301c0390b04004040d40381e5180741c0400b0b0003440b5006045440d0584070320030051100003070b8058440c41a5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898020476 1250 898019226 898019233
    0xc0917030703080a020c0a0f061406040203010b040b1804092006030f06060a020f0d200a02010801050d08090a0e04030f0e130e01020c03070807021009060e10030e120c 73
    0x4024151503280c0c4200400a00010101d6001a5202038140c00400400112074200e580c1d00034039841d007481064403914200d1765982c4070916000f0021141803e82c3c0c00031002c50307085280d5403409100ea09640f0491054281210000c20040f9100c0803408080c00d44404c05002403051010b10b02e02003010344d501e02e0a01e104079200480300449800c083c0c00f503e1040c02e42e09414500b50b102c040c200550360b000302e928442148126603100814501c1482080600c02c8503448941c80c004500410340929401c1460001c2541d2240f4001c0d00942c0c2d01c48250360440c0c5003074071800b50907003841c00c00017840d1007440d85140c1c1001d00d400000522044026210b03100b60301a5030344a01c8241d101c10308890200548610030360088004103a40403054003503206500402c40d100005185c60307903004a039402d640040390103441e00200410803a040d418015561582c102e4145050381c0c0785da080420150480516a03002c0b03000c0d0030b409450000080c0207501031828201c4030401caa07410003082c01390303000075030102c0c00e194070703901 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 898021582 1106 898020476 898020509
    0xe03100e100c05120105010e01120507080411062106040f060f09060e1009020d0b03030c011e090b011505191e092d090c09 54
    0x1803801a0480701c141d09518022104501d0200c400d0150400c40950380f030b0031510115065078402d0a21200d500c2500004031921a68400211100d601c1c110620080caa0843c01d114482c074401c50400b040200100c05200b258020500d000c1100c41610080e50024010810303900d40c801005800021000c20380e00c02031064420643c0030303507035905400000740311511250103900702034250f0007030071301c0a4240a1078401881005100f80c403009907000c50146650400e98002c0300e00c40c40000c00b100d8441003984a081d0007031070599928800c0e2030003c182050f40500e94090400c289401c030041404d10380c40c103940261103110042c400020420200a151580301581100c4007102480d42d842216601409130f03591454211400d8490520182d00d9040101c0c1054542d2651100f96a0056070501d091000e81182c1e0010f194120041c00341c20000100901039118400c2c4080f074801c1505c3c000040c = true := by decide +kernel

theorem cover : BRFrame.Cov 897841726 898021582 := by
  have h0 := BRFrame.cov_init 897841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 897841726 ≤ n) (h2 : n < 898021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
