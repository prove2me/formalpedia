-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3464
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:44:00.552217+00:00
-- url     : https://prove2.me/submissions/06244b51-c76b-4174-8164-bae8613e9ac4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 622841726 ≤ n < 623021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 622842976 1250 622841726 622841759
    0xd020d0c06091202030304090216020307270b09130213050a0b01140c0a060b0d0507150f020f03030105090705040801020d06050406060314010b1e07080702011707020a060c0e060c07 79
    0x10b01c1d03030500d0f81064003c01d45903c5a0b000f003115103a00090405104203007894a46a0168050202e41205036210480700401c0c040d194041d80d495000481880c1100303880c0154003072902d00030440c2d12107864400c00841c0006040a04a0b0403080d60244c4030003002d441d110b01403040740c1a800100d040400940010b21960002182c2d00d040c072000e01c941003181c0c00c000742c1018000d03407040000030610b502c3c10001e40b5022072003200a285100d01e0034045224040e031840600c01c9a000e440d1211160751a030003c0e600c90482008901041c2d01c10300c0100061320f03000640a03080074040c14242c0c54181c03260310030740c26a40001c00740c4000c2910b5410030015400c03e44202d00040c4032a107800c0140914203443e902c40c0381c0061084030b05228001c1803801c610084d035032030281900724210001c1c1d03a803415460100800e8103c05c03001d03404200004060710705508180d08031442900558003400d03c5044680d1000003c003810710031306003080000744000c0c07000d40740c46000b40354403070900c40103011f0185008000803906420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 622844226 1250 622842976 622842989
    0x40c140103110307030926040e06030c0d03081f06020a051b011409042d05010b1603230f220f0512010b06070f060c080609060f0d020d0c0609 62
    0xc11030440101038050701a42c2c0c00880514006c51940c0c59030a290b81030003a070134010610000031011041a451030f641c001c00854224100b0010103a94030b001301511281c1403070400b900620910082c42c0064807a00186074004418444108042941d001c4100d510165800060159120041002c2408010411201c9001c0c1600e2049480483c00c0002000e9840f0000001c03246070002c5520000d07944c841c0c114900302c020500581390300540e40c505121032800342d4659522980c2c0b40c6000400d5900f02d4104841e4103c0300d4180f00585844035681c00ca0300020003800f1400e510410307800241103903e80c00003d02c4808074a503846610344405600098030b004020030010454403a88004101d02c80d8071044500485e8000c84001c402400c00a581a024149030390707187d13600150000310070080000b400000c08403140684810826440e0342402aa013990381501c000d9801070754500020060302c1c0c0340e2410744030340101408100307601c40d0940c04221014051501100c056010000074410f042d40074503081300410b007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 622845476 1250 622844226 622844231
    0x1302281706100c0222060312032c0c030a080a030f0b13020c071206090c050102060f18010e0f0307020f0d08071506170c03010f140f1e040c140103 64
    0x24100c0008040c0882e02c0030003028007081a0100040d9a601111555a034042014018000d002040000000e04d0b585c0422102103112002c2100072030302c20304c5000302001d0198018903040c2180200029428803441114645100d868500c01094a040c091519102d100700f8296803504c00480300a01030b5281c4418bc0e281040c1760440c0c05695690b070713140c25a40f80801040045c2c1d82c0b00c41c141d88501b0f0402c56041212202100f03102041003110f2907000304090f0b8014024500d455495000480e1250070640d10b0328596006400401c0320044c02c0100140d17000d081900009000f0446281b503400e2001b0004400303019003010407040250304010940c42c001000484581c02c1160490303840c624207000c0c10a0141040e00b0140c00c0882c403c00584c490009800f0070225100c0c254070402d8503580d1a80c0208106000c1c1d420320060484501d0759000d6803840640d5030713614540c140e5402d410800081d000800081c000400c01d64041c41c46030f0081c11050145004601d104205800d00603640e454810a1049030304151 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 622846726 1250 622845476 622845481
    0xc02010f1b17060f031204050310050f0601140c120d0b09040b15010201090206040e070f05030121061112012c04060b0d0203010203181002070b0613022817 68
    0x5910816400b000e5071000122803032602c0c0c800c00b01d000308200411094062240458414400460307101800845008504498941e61046643c1c41610001c2c1ca403150701c0045100800e4056002d00b44004074001c0d41110340d4101803040720300920340300c00842040801c1c44001440c20b80d0030101e0080c0d4041908c191030020b49828a039580c0d13056698000d00092649600b0844549168400c1d001120190b4009100356141d07521460305903200c5800350741090214111450110301c041c0200d0a4034100c42c4000441741c259101650555007000c1c0f602d07012602103940b481c9a594410764880030700040802d4000301d403070f198140b42c404500d2240205440140b81105811074060170803a10b030702c1d07502a0b448800451540c65040204010035503524000394554004020000022000c0384141c55000c0c0034802c0f0384800b90f03541c2060b0100e108071880506a91042d800040590400300d1b80002c50f2200c4410043c500001c081101d00290314515510880361241600100f559502c4154004001850322004d0a40e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 622847976 1250 622846726 622846781
    0x4030204151401050c0a12200105010302030d0c0c050904050106030309292508130f030f0308090709060603050109050a0219030b010c060603060e12070503030114130c02010f 76
    0xa1005228030f41000703000149000c0307000b81445a2201103034018221511059152800f802c1c0401014102000c90228402500c82d603505024860407030303401501401c244207202e20b045a0303550351760308150b42103200490002225102c0d21146482507010b0000021403505603d0000d000c040f82c0d40c04000c41d00400c403141510310090303e4040c0021020890300640d0340307000c002c81d00082c41003c0b1408400070b1700b041c07500d0140600f0100415108504011072150300d5150140c9840b418ad0f81d00001d0000341d0030707a00c0c8d0310020f801205a5078109800c28119401241d441c200c40098030000d4000d40c00281d10303a030042004c4c00c61401040d0300a1190002582042c0e20215041c0c950244440d40108160b16590220340c1c5900400451008580040e810311038580c0381c2c144080030308000c100348201d611131000001070480040003035480c82680000a1844c60f46003142241281c08603051644d402404040b4880d0400c8091190500ca8a440e030004600000101d020030101c8540045c0c5100d10402850f034010b04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 622849226 1250 622847976 622847999
    0x18040b070216140a05060d0b0a0504060b160302010b030708010903020c0d02010e0d020a092901020a0c09051906080c01020105100518150a0303080a0b030c09040b0a1e020403020415 79
    0x50f1000030440100b02c3c1a00000250b00c048240d108607000300c0c001a008905071107039000840d81d04015140c203410785544e04180012100507115001e02c1120074042d04a8a140104d02e00001900030f100104a0201000019003000300e15880078066079520101001095014000c1c0180203508846d0014400c40c5500060f02c0b111161500034454800d443c4030004540d100105d240180130205030421207142d4050b5014540d40706040203800307200407080700548941c400100401825070104151f8100c52514030424080c0c04041c0003064a440d42d1305203400d41243e2072140d9001812111b00400304114008000390855501401e90002c425400328240126240e0142a042042c030f42c01c0c4201403682c0304e44040000100840100354008402e54000041c1540030310194061b0013a1030341001045601000c06690742801e40390580c110041400043c0481c541d00c00d0568040107100010503007041032003540810154590081f080c0aa001c02c050003541094458130848204c55000c40510030b0030403900301030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 622850476 1250 622849226 622849229
    0x30a090f1a0304260c010608210d06050d230601030c0612090501060b0c1b030a1205120901060f050904171c020a030507110303060108060906040b18040b070216 70
    0x44600c0008003181c1009003181c1c0c0d200010350b40411120000d10404d05005555001c0c003041c240380d6007001c0b00405c140b803000c580c20008500c0224070ba0b5101103001c0b104aa650800c0f03000c5c141e4103a60324000100c90700c8200c0018071480c4281a0f031101c0070040754440610b48034500302410254440d40c014000140d0800c1120207581013400c004103402440c1c40010f0183c04211401490340d42416000142104202c01405420350f02d4000da03201100304060306805081441d1f6000d6042d80603d2200002c03840113012503403001a14a00b076480c1000b02e0140e03110030042a11580210b83d520581003008601c03207200e5002403c400c592508403401c1c07540b00d1094800c9001403004c591030300081d010510340030007800d80b4140384020006548075085003401400405d006c98800020034500111400c24031004030882c1d2003134030142c50308000f503155a0188805038500400c0203400c50340d03079070301c481c62540c2e10310361281869281034003003200b894a0318101f042110050300c06019544040310420034409141032410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 622851726 1250 622850476 622850519
    0x705130801090201080411030c132003091504230a060509010c02070311190807080606040c05070b060a08010204122108160302190309020a050907210b06030702030a090f 74
    0x125410747c0c0c0320000382072440d0041e14640c0504080150501e82c0c88640240c8004030401e5103042c20783c403c003200a00240b20407245400740742c0001c04080c0c10110490a0603400c1303401402818902c21a141d048103081e00440c0000040d580038001a0701045150300605a111101c007000340300f06801c0c984040d58850312408010b044031050b901005464607a52a9030700e000d6a4145540d00c0c541c0d591080079155842405840c0c40d5004500c0054030748d007031a01a440c4c1001c12543c1d6145800b420b621003d00154000d0f1003164809115000040c41e031000340050809002ca0281c1d0044200003850f1800c080119080c0c0c3c240301c070300000f901401c500d8110402c00e9010703402d5102003c0d40850b5050841c02445406410440e0840070000d903030806078580e210029561081d0b03104c080090b210f808000380c0d400c00b211004000381450031411080a8007103030856214500c1132010603040252030000382142c108031080f01c0140d102103010040203500c084800010807014515107045070400024100e0f031840c090824 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 622852976 1250 622851726 622851743
    0xe120f120a1b050307020907080703050702210a0207150224010b0f0c0a020d061a04140601140c03070308060112050403020a08180a06091d010e040f050a0b07051308010902010804 78
    0x21003d02001303000303c0c2c2409500a000d201546080c1c180900404415103c490000b8a000c00003085030307000040c40d003800c25107642e078001b90610390160102e0f80e0340804550000c600490600088a254039207280c1900c40c05c2c4e80140800076000c49500017000b1000d01c1c6039864800e084010001c180c08002140e010318071038404540c1d1030400803071a918000c5000c01c001d4015000000140600005621401c00c5146440c000202d900700d40e001c000581e41000e10865400044401058070366010b0311000201c550201e044504001031181ca19042d608024402d030f0100c2c014004001040da446000b4412040c0301103070400031030403d520025078a43c5008001006030380c0019210b00b100074003854220010a00802e602c082648803c00101a000c243c49010541300c90f07100107454034030803c040343c1d041c1c501011460995036900e0300c0d00c0030320304104981600c00d40076204012010030044000301c0c0c071900c0280c035465959804218842c1c0e04c410070303a1028803641d2500b42803600503a44402c12a8015030402440c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 622854226 1250 622852976 622853027
    0x110d0801090b15090f2413061d0f01090320010e01050a02100504080403060e0c030c0f011b1703071e03020309030304020f040204090216020901120c090207030e120f120a 74
    0x709000d240d106400b00c16106c402110350001a40000091030064204c4441a45841e41d4a034140d400000002d0061035206a0320b1410b0513509141d0600810041d0514180e0381d03055032600c5440040c6401c541c1402c80f5011500314404079604082d031880310f54401e203041c42c5842100c000094540c1c0003082864821034465010800340440b01c0240c402440c3c03c500104505455403074003d13541c2c00d0300b01840c4d01078061340e2040710301490301094420740c01c0306c10b0710b030700300d4840708404010788040c41484100c410300c0c5990102d0448880c00e030007951256040d9102e180350711449132198809094000203000401d4010000c100804d1070203c107403504154191401e030700d00e1641c00c0002d00a401103070420a5180d1001c124400ca8a061101d0141c00c10b009070382030b03091640c0311001d4024252540102604810681d481000350054950013403c1081c0a4609100c49114030f400003240300011400c1d0344000e510089190500001c1030103c80544500b0450035031800015500c080d007180b900744500704465600403c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 622855476 1250 622854226 622854229
    0x17070e090c040e0604021e0f061c0207031706060304170c0708120d14060d0212011808071203060f051210092d031202030601110d0801090b15090f 64
    0x284000c1e5100600c1444807050103c10f0599400c41202d00741c0c4611513070251000c040e09500d640e009801c80190050444e520f02c031051005a5000781c41c0e034458a095058680e028065610107444103501c69950b8200c010901c480d0507030301040c041c0c28644145010401e2000141c401d0f540502c3d650b90b83c02800343c5410812800b20b0070500958420340040c0120300c4082e0b00a44030400614800aa1150401003611005860518a50110b071201d0304030300c29400610140c0b43c18040c51051250060010544480c1c1c5607400c13a06c3c11403140200c840c10b0004c510700341040b003c191141d90210f8030703181c1005294a041421500580640305182c0201042e10512440c5c00c0d003407098070811600e400d024003103040a450301095072420900380404202104c0010444404415500400b40d501655a155000c00e6100358900075407019000a040c040d13500c404030b0840f0400d1080c594240c0c095145c802c0e09d036150840101c151001c42c805140b0541d0140013600c1190380140076503801d424240c8182200100400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 622856726 1250 622855476 622855483
    0x90136060914010510080d0e0303030109110d11071205160b09030c06130201030e06010b0a1b1a0405071205030f071b0b0919120b06060f07050609010617070e09 70
    0x111002c040d508280411003080b04c581c2d107080860b6295811a082241307466812138610020000303969050b0001c10040100e90001d41001d07004400b550703441c80c0b6100c82206404c084038050611700f40e84070408610f140a2051a440302d0441602c2c504040b450010141480208071040d12801405034212102280026004005540b2100c1265085130040d0078a00f4039042c41c030305100f8080b40040d040118030220660003080d564101ea214441c000c4c14942041070950312070001c4585502101040501c000c04201c41203103010007003525510114282c2071a042c0141000150b40100f02140c1b401b00d44000000d4001040303e12100d510480c50740c0701c01e003925148554140700b0807110709482008002180341019100108016041210142546801c001c40081081c5d054410f0b11807200e107459074640400e562401c615400701c030041230b440ca0702240d10180440d07a00b0880b03003550b0325840501000343c1c104007485034501400c00d070310088000c9400500d00075030326a1540a1101a9107034032021132f1803a2800c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 622857976 1250 622856726 622856753
    0x6040905031903050402091e010902030615030c0a232209050103050d021b0901090914030d06380c0109020a12060b220b0a0e0901360609 60
    0x182d00b032990701d894128010040d01040d00c059215456031408280c010540c40903855544007000d02080550307281524420003500300411643c3c00c001c0c0c048030b01e500f5254000003144214a0340441c6500e44038005001000c480c00f110180c10085107800f07850701e5440c1020300b500c000c030380c40040e502c07511816040050384080040e4020f514680c00c050020040080c00b040302d02c15410340c1d80c00c84000d6107090340d445800350444520b198005d8120001444441c21513080f01d81014054051403400034149070386189564403007050094526036980c0140803100c400c28001c445041202200b07041081401908201072942c0644441c282c0800202c4c02c4a100d03081d00b0a0f4a8641c0003844503480c681d40300f64098540140100440d81180351a01151041c5094544802c200035036002d541c00304010130b91404000c0207440801680b1822450000650b080044030440c860781c0f1620011961965542c5a141400f040029901c903225120102700f01d400b02d04c0b000c00203c1c41d040f50340030910182a00703004030f480151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 622859226 1250 622857976 622857997
    0x50304152106030201021203060d0807050a0b0703020a090518130f05030406020604062d05190e2404110402030a09060c090f080307050307080a03110a0807020c0103140604090503 78
    0x8071110400d031280a5020b842103034000c0c1c0031740d02e0400044c00139903107030705c0111000c50784010168100004650401c002e003c1082c4542d01b10f82410506440b0090051022114400040d400141e0010502d91003400030004080a446d2108842081c400d80342001d1402401707059400b2902c8110020b00c4041100b002c11640c1000640f42d4980e290007009403070300400c42d0151303201810485c400091030a1010180b003442e0340d9a14006000134482240340290502804507014600d8004208a84940c584a2140340038440ca0007000f55048242070750400d2001e03403600701c1a1420b81000c11000c954003814040c90104111401a0340740d943c03002540c01400c003040084c001c0b901d0a1240103005400515103004d44580052600b003450740d030141c41e5640c1c892040e0040c42504140085030014240f000a40406013407800c01050010441a01d44801d400003460074001940b00b00034810203a0301840607000b0700101b07180030b219503c003100c401031554601501041c000c913a00c1518106100051081d100350211 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 622860476 1250 622859226 622859267
    0x120a08030c0a08100e1513060e01090e07120609030903120c05010f0e0c0105030406061a040e0703180b2e030212150f040c050d060f0509010905030415 66
    0x1d20301d103805580d40180400e0000305504a01041000d4030f0308101c401240e0000e0f4400c00700c3e95406061401d4240ba159803907400260080c4000a04000341c003e900c0901213001a00c5035940c50850840290380030b10140c10310315003040c5000e10003007a84582c000070b0190020303000314141585180c119141009944040c080c1c51441018201456101848080050141c1d0003404080c039254030a800322810001c000b40c89034030807500000e2950146002c0c42c0e02900800340000c050b90f417405c0019a40300282d5a10610840c0000c050086084a40392103403c0040c4e4a400c0101c03181da0031524840301c404440240564080d00300094000c0400c50301d0789221445a11030301c51643c8010070940500d81c080c0000c92241807440d2501e0301d1560000303401648100101004070ba181c881c0e0151010207000504213480780d5958202c04911900c1307170000050074500c11200001c140c24104210002c4070307000b501b0030300142d050040c02d00108000000b40e4098078000040104400e01102003610039040d0401903000000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 622861726 1250 622860476 622860481
    0x70b040803181c02150f0621070914011a040b0d0216030203250c03022209050610080a0203062806091a18160c08071b050604080309120a0803 62
    0x4111145034900e10209400700d4100c501780040c00100300c081240ca1200c007040010003e1850328040800c89034941c60305425924501203c0005402c120854211910413900d408031201014601c0000600600381030409202d170044900441080340710764420301800d20000318a00d40106256412600d0898140f8903590132550700f440c0194132030700401c800124424403107001c81121113241d0003080c842a44200703400b800c0741c156403c12104078034095000800300c10103041d0b0b449042c414881c00e48610f002d00020186898600721520102400d504410b08981220700c4102c010b803000501242c106980c5011700e0042c0c1c0502c004200b44400c0c011843d2041c0d807c00c02c0c0002c043c07401d83d0000d1a050b00c409100910365801c0d00c18001c0707008003500918150700d001d00014500440c080c0b00140415a42e1070408410621511000c400e504550b01c161140340b070410708030101140561030000200b1080c0d80720380c1010719210960741c4a00502c000c031401600742c1c006c0c04002c0c03502030000d0705c01a5445003d00b9101e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 622862976 1250 622861726 622861753
    0x10c1e0309081c1b060b13020306040b01050c06191b09180b0a0b070807170a0806030105130609110a030b090c0406050901090207020a031520070b04080318 68
    0x5a80714414a007040c014400031941c0a00007152040c60f0150589034070302d0085524800416203603942c04196882551011105c486d5034849178111602541104003589a04260040008841904030050305100c41000504200300d0701040080d4802c4c80c01b070545400400c00c6551402500050b003041c041302d00e0040c00d10003c0d0741c0100001d01560301205800f010408604080422185003018031070b8400c031610020000081400c000b0101c6a2080c10a54204061540c1d007102044210038071a103100c01c041040d00007140d01400c00f0354015000c6000303000c01d0901d4003207242040d113441f40c041d2045458038004014003201075007032850010054660070380707259a402c00059103401035400399418040d100844405260078041c00f0306413a4002e0465100703920f0090407000944c00994200d8010755050400800705032a08140c03004c1c080300810208100c44200ca405c04103030a9010110301d00181401804041081000c50706d0340994446600b907540c0d1688040100501810100e012252054000755002d9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 622864226 1250 622862976 622862987
    0x714120a060e0a150507020a0209040c0f1d060409080412020f0303300702030a030b041e0509010b0604030506010b0901020a1e0b0a0203193207110a03080105010c1e03 73
    0x36900620014a070380700a00303110070030303101d09558241c0140d200080c08d101501c0c3c07000425400500c5080c590000582d5401c2003101200240d005407884039041c405035002c400c070303094a1507200340c048401704820f50850351140070358003e5000d04181042141c04450854440380785440c02884000c04894503144800c1348100c0d500803000e41102c51214421200e043d0341f00180515004a1058001e14241642208210014081c0c0b40308998000c2d242c0b00000341324480100c3c0c508660100307030340208003032604140e414203440003203120b540a400200010004a480440c0090640c0e01c00354200342e8031158000109d2600414800143c241040300d10840d44850140c0303680e10301e451040d410781c14142e4038602c2d0344041b0f000071a4030045460000c16407038075020382a840326078050008141025490b803441c80340110000503030b0401285000600074007014503000b61036a003400c03521000034203181c402c2d070303a00800702501031081720706010300d60000745c040000514104940328214000211b103206642070040a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 622865476 1250 622864226 622864243
    0x181a040305010c0f020606010f0314041a011203090b090a050603100f0909030e0f1201060e09010f0204060f05070c0905090d0f0201020a090b030a020c011104080c030714120a060e 78
    0xc0715843d01101c518160f002d8540d401c040789040c0c0240400ba0740d03050041d42c101d071003030a15004142d0f0368110450350080903480540501d0042d031a4850300d0494404030041c070035068001440090104a4000000341c0c4501040141d665450105072661450804500c02c00d92035006258060008020401c4084100000c00211402e20780d1a0b450140d403840701d54200e44206001a002075040c0020302c3c038074240803104090052001e813a01d990809815a05400c55900d504244000f00c180414088a0b00e0240580d1188502c65001140b525240c00401ba09103003134012070505002002c5000810704c650454803030000e1040a83c24080c5244c404002500c540d14204c6490110358600615422188144260b805540403615046907c40c2030160a102a1708020a42d21a140d020041c042d4000d8003070007404400041100039949803410048a1810400850340c520700903442031400304071551100030303901c20b08501a20b021f042500000301c1241080c14051000d01907904008521300e1102001a503120b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 622866726 1250 622865476 622865483
    0x181f121d1c0806010e0d02030a081602090c090315072303040302160e010b07050c12010c110d0e060306010509040c0e120601030f080a05070b0103051e0d0c03181a0403 73
    0x2004103101d002524109402d491580c00a400000e0300c680302d0424544030040140010100d80c00100d950b605c007400c6030700440440100e852100501c40450800f41c2e4415001101c40c100c840c1464000008690344101d685102001c1e404a44041280c031800f6995204103080c8080340e25142c49241c6232030011030b45c01510100c00600c1039100100d102e8407040050000e80f1400b021100c8141d10b42000324805400414041da024050f850310b805542d5070f5002e464441280150010801a19405000d8146c244003810100c0302d421602c0409821903000c0c02001d000703030b01210b42940701c0e110400101c50a001d5030440a03002403030509000d00c891341155408144c28011036111030328000124081c2d44070007007031000518508299050600046842c1c0242041035442d2421a0400ca0030b034803043c044071400c1e03105840f9034204820280e020341100e90a41b04a94440005201c0a051f54400030710000300d0090280c200148505004404611a9803200090030321000783c1c480d42c2140740e810049603000d88400c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 622867976 1250 622866726 622866763
    0x312130305060a1e05101a09120609071205251e05090c0f071e080a03050f060a031a0910022808060d0b04050106030c0b181f121d 57
    0x1c005200980038846c4981040720042d003002c1c0c0b9100e1041c01c00c03854070141d6140d80e0f0040c800d0142d203884400c00450050310280081140e401c00c000c0305070600901c0d4111581c4142011100701c00701c1d00000e501c2e0002d1080500070305004216511440d141341503600031400e200918810b001d540f40115040c40e0036141c040b1030703216050700d0b010400c2150b0b210b45412030404040074020100462482039070b400141005500614a0030300c15601d640c02c40d88450644808241e883c000d01544200d01c6c080b03164400d100351103540180303013940c44a1411041004006119400450000c2c000c032105026503410255164015034460200c0e50140030070312481503c10003400881158481050b2040d5003060103210054078a580c041d4050300c03446a031100c000c00a0b00c2d40c0d034a80400000083e4a90b800b10000c005031040d0702e40300d00540c1d2200c0c4104491110300e42c40341e1561510b0b03206c1400d003400400c6240000f801c0c1640c582c13940015010141030b100c41100e00c07440140452001c81103001c100e20b2000000001034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 622869226 1250 622867976 622868021
    0x6050702030405100305131712010603060e0a0209011e03231006080a1103010306090209060d0503040501030e0c0d051c020d0c021c052a030304050312130305060a 71
    0x2240e50340154400c07543d1050044d0780301c01801c1d0103544a15040703a05110150303040d21441d2038402000d0080300c158400c2010008001032540c5004602d5805450285018007407146004281c201126001d8000d1451542c0033038515000d038010f21414035030041c10f03103082da05c030710030144050700401000d4100c18a0803055030040324070301030f0500750300d205146008440c0001c900740201115200b03030090001c0d1540303a03604020b01c169203d0700003440c02184524008280c5030700302d00c10701c2200d00c005802a40500007801c04900003c00100944040e00e0342845c4c00642d445800034110310b454000c4003c0380d00012842c030344405008003c5551103508c030000e880c0c0182103102c542e04130395850603030007010b0018514204800061800d004408041207415420516980154070742c0c50914071000011083ca0100704040080f5075505001c00382094000c50203181030500d84804292a1805054403001400300010b500e0310303220b61101034801558103c402c542d01444d01a00c9140201040b48912701e90b0080701c1c80303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 622870476 1250 622869226 622869241
    0x1090603020c06070c0305070f110a060c050a1101050403080708030f0c160210050418090212070503060c070816080a0306090504020d1b05060a050904050f0739030206040605 76
    0xb1248600100b0005041a0f510f400e07085448002e400c0044040080c100841c0020032100c02800c00400c0c091081595044042d100304410b000603940078005000c40302c05070a02241e4007242d15800705030040728220344607400c900100c03110300c83c98000408003600840c0500602480d80301a51003250240400b480303c2c2c07100d8900c10b40c0c5010300314440c0f51a82030904928018146688070100c01038442c100340d4109902c0f60103984103038801803a80131a0a07074501d0b481c0706603d481c0e00c3c2110b0b0750104401500090382071901080d1213403001004003d4010001580c04208003290046076411403807050001001091032408003080e0384400c650000082c00e00301e0204860b08140700340c900855000307000a01180d030340d41c0d410b0102040910710350b0320707042c11580005490703c1d03400050098600590361160340d1400d605c01c1008a0f40064800341415040d48100107401340c000d1188111039091a804c803074884a924610007826074404c48001840c1982140c28080540000d851f60003948159001d0000755a24403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 622871726 1250 622870476 622870481
    0x20406050a030f0f020607060501150215150108090c060a09031518021003060806100e1014130608070e0114101209110909030301030302070b04141e0d1101090603 71
    0x25204101643c8828002081d180c5040007492002e0005401c15603151510012103200b6400800b811003440300120703007107034180451207a201c01c00c4c00b14030003810023150004401003840d040380e060000c000c011456072882045a0350700040700801544d034a4100210050210205200859581c22003c21004118890313029003840d0f0218107056100c40099a001c01500c0b40100308818145551000c3c017090b044c0b421700c242c0c0d11038070b00c2400306807030315103003150700008514004e0103000384403c14801031041c007030801180306000e0b104862840b034107540364401800400c2e0561013020a44640361000603d41c4072440c3c00d50403100761260140510403e00184851280c3c4188404000b5001540001c1c0d0944168440c0250f140210440851292854007203a4142415a01504241c0c0003000400030542d0400951025200313a04201d801c1078601030411040c0b40a00745d000d0300c40c0c4455001c24280b80100d40030b0b42044407008000320602051030901d80d0040c0c42c040b030300d08e000807181c540c0418514000d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 622872976 1250 622871726 622871729
    0x1703040504111207110c1e0405010608090c09040b07050304051002033301200a06020d320f0c0d05130210031a0d0f050f010c020d08010b03160e030d020a020406050a 72
    0x3c0d014001080315601003000070b80c0140b500e10a0058401d0802d1f0490301c541c880d460180c1060348036154641000c8803d24900303140001124861034000d81000300242c5800d0b645500114107091442d10ba03241d92810f241001c02c1e20800021991011040021400c0303500c00c09035000800d8040708aa40c000c2c04008402610003520450108a104020108065844804424a803e07140681d10540c03606c0d9034034020381e0b00901407003140b180c503600382c0342041020b4107030615004d494081b0800d10040105500002900003418181c2948a03800080c41840501040314862128014108128903000032807404100b9103650590103000d4421034034100d14040c1c42400440d11050000d980c50040c00c0042281e07850748510200d501c6c584100903040014400c20507060710821030b900116040b640044005e02e8010062010f108002c6914010401c8981d100c08494020156510858110144800c19a51084101c5a003505071140b5a0001510360f804116804400c5c800c50341804440d6580d4100000c0c1c1c0c409 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 622874226 1250 622872976 622873007
    0x40323070b0c0f07030c03081021030e0d030e0f0a05030a06091a2a0c120f04030605070c05100b1509190909050601080c0f0d0f06050f0103051005101703040504111207 73
    0x1101c1c80c1040c0007403428490785113307103001e0b806c400f0107602107132102152540c220041030b450b49c2525514940301c1212003000740180c511340f4550f460400041e41d640b43e004405412203075282c3c0e0783c0060051001e08070741c01030300344004081641005c04407a00038402044508a9041c01104030700c2a005807042251081c1038035400070100005010303202c016a44c0012a028212001040000006061030050502c00d4116481d0460003030340311304126080200d4428940c44403032030140d0980d156520301942c070800303220042201343c44068107000b0490980030414130224071500340b44006405d02c030702c1d007000d151144600140e80b903c0c0d03616031803540d644446901641c0d0240c00b0520300341c06414001003402e545406050b90149012054031890100d4000ba561310044105200040c400d00c40c04000c100103071441040c0802c664941504c505e1030340b4807540203401c010402c0c160341034000c0f002042a10040c11009000300283c402803000842c03144d01080c4030384c1600c00081c0006184500400032038950040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 622875476 1250 622874226 622874249
    0x2040e09010c02161707031713060804030210020f13080c0f01020601150503043e03060403120b0d06021306090f06020703060f09060e0105040323070b0c0f07030c030810 74
    0xb0175801d80c0114084d08280407551046040000100d03042a0900c05205868240555645030200e540c03c5504550b0700304009101c00720b01070200099000442800a020715400140ca980b50395181c120f05100b01e00c90400b440d100c141e0701255400000c12a001500e00448030100c1c104401001680c41c1c000920802000e400c0c4000040d501a00440095030b0240c403a03401010740d0f01070007148003846480007120b4400c12540700b02c0141c04d10714072080c00c1a140740440007000302c2d142c41c1d500100086601c2c8007004440c1c1c2c4620001c0700c16101c60031003030f00c60340d0301c002c080d91103044e00e8209581c41341c01c0d4422400051214a4002181107248200c1c030252030300d9601514201d400c603141e107800b8004254014080320303500c0d01e040011481030301c5a000358011000001c01e42d41404c0c2002040c480134542414070b0f07100204500005156080c0071622000e43c0252600d0382c1d5a1201404d807041d0040c285411842c10001a10004160b409018000c141c0e00c6900c03002d8454882c101045030390382440c01003001203203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 622876726 1250 622875476 622875479
    0x1b0306051c060515030d170106090e06010c02190b1c02030103020306130f0803010803280c0b220f0b130f020d02030f10060f050f011707050403020402040e09010c0216 73
    0x1801500982d6000702d4041e1141d0214400744081782c5000d000d0403448001824140b000304498075000c0c0660700511107850888049414a62001c1c008040a0001814450500400c0c02117484400f1a4403000ae030308004908001e654080440e03265200701460320b070201c804941c0c0c00020105100b5241602c0e0050000c107200c2d998080b050b032025405001c01d96422a429140c0740020f20028029806070245070061034035100a800140c02c40f85000e4981d20500310810b804540e115031208034030f0719043c0c00c2028410303d0388031134800c981180c0180380c0d8800000708580000040c04181d8008a00841c0320300300b0b0300601d5891451038516605803c40c000c04132444001090007500d0b0034084080d001d0700003410b0f15506030000c00c51601c1c10310005031201105d40c88401c200b0800082d844110000c0030281c2d496402c40300f00f140000c0080e000751042c54428251800843e0607644a0000d4901555001d0021940d60f61100f078915601d01080382c0b454030641c00d044c00502024404207240000f0321401d4118454075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 622877976 1250 622876726 622876733
    0x51207120f02060a0c03080a1127060307030b0108010e07081302040b030a03020106080106050d0c0b2b0506150702031c030b0301021617120106080a0905011b0306051c 73
    0x181010401507811402111081002d695910004e20304507115444030100c3c3d400c0c0b4580070b00b0b611001044006203034034141d082d01414202e4811980e0032a2003105541068203101c03401001c84e11400012a00300340301101300401b603500b580c86214040340988401e4075030780c0e88080100c1c520804807071000001e0b01842c00309202013045005d01c0d2680e84010b0000ca40c15600d44040ae143c42d404001c2500140e4481500f040008030a1040002400c0151100300c0e010f109600e4045852034148262800b180d0006a582c051241c0340340d07260340143d40a0041240c0a00c1e01d010301d400380409403030303452160401c00078503020881c03403504654000707a002c0c01070400c00c0e070300038807041800850ba00ca40e800c0c1078035141d1981107541c0030310082084080c10301d4444812006820301c0309441c0078107510b52915071000c00180021344900c60001e81140d04a00d80440280d50b81581180501503c0400401355800c051a404400d0592003400714030f880d255404019551396542007009000c0100000180300a00d2501d10010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 622879226 1250 622877976 622877999
    0x1509031b0b0a0305191404020607050a0507060c0c1205210d0f0e0c040e030d090312020c060a0c30090b01270506010912030309080f040609051207 64
    0x10348282502900080d960281982280c2c001100400041e0341c55040055240e60030703200d4415400e05a6003003002010704203051082e12400780010b4494403003c1003d0301006010800c0a58940d4000c090343d0100382d40303040c081c003001d8103580300700c41c090300e11000490510495144032000c1508240101440040301c1c17048203039010611000c8d07071200b6040003138050024040c0a24094120b590307400054410702030130024148034845002038421401c0442c40a000700b0008291050b05801482c00140c041c1d031480e090380c1140544000900e0540042900701107490086501881880541000e010f001c001050803140101007403a2404142003078440d030b41031144000040207254090f000300285c1d8100e2a101c0080e0f070b5101340d00c09083c0392030074001506020355038801c000002400100902481c109140081e004010a000c1c03803092420301d414100c180340c1710350040d402c0b45401482d110f0360f5904004401d0815801806540003080300320070700003101c1c1018000140b5145021000c7d010403820200c0c400c0d44c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 622880476 1250 622879226 622879253
    0x30a1a0106020a030c0f1a01060507060501080303010f0e181f0c0801260a0515091b0d0f0f0b0a06062c06160b09030a081e0705131d10150903 62
    0x40007c41c040480004c00c20500943e80a00b04a0721074544403125841c2020980707074140c0000351250001e100400019829010302010303981000c60303200c0740f641e40c040c00c2c00f0413600c003c0340c039010b41c03155000c850981812085040542d94a803d0300740826081008143c802e01401e00c40d0a01d214000c2c21003000c030800c1c552004894400d0001503510a0199854503890f01c0fa15a162003800541c0c0014092041c0b8100580b01c04031030340c4c080840da107a4040000407060241c0c084064808081811407c040226080c00030104943c042d1118040b4244a01c041009041c5030240c0c84c0031136407c4c000d03c00314080402e026031010340340e14402c840510401c814480c468016104800c003200d501c0c1d250070001608035442e9803160088000868603400d64040003464101c01810304070b00742115800b1146929075100320b0f1648080c0c0b5050440d036441e401a0301134409212a48a81c441c01000310f00555107031000581180aa0780043c080042c10340c94030100c0340c101a4641d050303408a402241c041000641f100203419 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 622881726 1250 622880476 622880483
    0x30e01021204080601090b0306070c02010e0103180605011a0705060a0b0109030c060e041b02150c0405120604060509010b210a0b0112050d0503100501030e0705030a1a0106020a030c0f 80
    0x6030740c030103403001d0302001d50407076006001560030030740040c040c0c4070091140030308889044006004074148060040c2191540c0d03140a410401060b0318054164060b070840e07591403070b11031802d101154441c1855401800c0c00c1c06030140e489500e4103007100c0c00c400d00065482a903000f0380600700c00e88452410b10001c3c2070f050031480c1809500c010020202c3e2401c2158002820540c9070303034020a840e00200700031280049040010740003040311130791403168006200c2e08201e42d1030720444055101c40d10b515515000d00d512542e4441c002d1b5a0200b440d24001c80c00a000b58410b40040c05661210802542079a102c0410560414203801240c880425603640b804c600a8000082d60800c1c441c5031a400300c0500c0c240c1015090b64019041d5a0422004011008000340c071441c6c110f0440c1000440545140c40500c94581010740316001ea804021090000000405000b0112030001c9001d180190f40c6e03203a083c0ca411a03c84419000195aa0022444079443e6615035242559a18150b442c05c96654a411094 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 622882976 1250 622881726 622881733
    0x31e0f0609050709030b0106140304030518062d09030d0c14010f0b090f040309150512010311120106030b0105060f0d150510170402060903030f03040c0e070219030e0102 74
    0x5451410792041a000f05243c2e80c4405a4904609160b41c81c1c1d101039011808200e8414100400445040140c036002945460078640d1440b0612800620851080c686d903070264002503580801c3e5800c0c0362201c0e0700104081c01e40803000b0381c108a0161801043c40e500c0e09030f04055034049500f441090240da0ba00d200309102c1c501096015041400c50b031040745c0740c06002d952030750b40b50001c0c40e003000e50390f60080880c1c102803501d140c17a96000b4025803040c440c809081102d164a80802e030302903000d03101a5810001c02107030540c2d580c1003090f40480c1c03440c1507902440009124260941043c0220006d4a8200108802c40d03441d01c010300106034440340115070800410712280b04000345078000d140418408402c41c00209042104010110180907078540910001e800301c401c0151044034071652158040f11585e440380503110110341588144141c150701c14000008100811132160280410b40303050003490011030f030781c4541c26603840d10f030310801d498201001da80c4c03080043c2c81800801940c00061040c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 622884226 1250 622882976 622882979
    0xf010f051c0204090b120709051e0f06090c25060906020d090302010c0306031e230d02190308062b06020c0c0103150e0901140103120807031e0f06 64
    0x402245648611003101c0a580014041115107410f0107030200c0d000044810140404810101981d1030903140700c0c41180545801c00502c034a08580611445c46c100110040220f291601400c07500c010122005885994800040342d280075005d0190340c0fa03151507a03032045290a01040700c07500420503000c1103031101d8684000a000078103a00150418408002c000715881c4590300c1c0203400e480480c40c0004c100b618041040001c14441005080247c003500c0d590002003c403800c2c21401203c11041102c5945030a900000d15158001118044003040364260780c07043c501e400e00c140103001c40c200082e000440c00001700d0030501c0c00f00c10600c4110351200801300b440410b103044c100400e100329001e075003442c0e0105040b108807c040c4082ea002510034a8100701c003603011120007481c0640343c02078402401441000400034038003580001490310390b401d001c3c1899030b5289030480303444488000c8034002482c1000400c6801e030090044c0c0705c01c002c55030b00c9544d0004041c4035032002030404501856401d07494250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 622885476 1250 622884226 622884247
    0x10e010323031e03070906140904020d0e06010e0414030403080a2001050c0711060405210f061626010909060213030f0b090f0d051602090a020d1404020f010f05 70
    0x1200e0f0142180408581c50789800030018103004c140381c0c440d20520a94007034506d6040b591108440e0101800c07200181c440c059510550010114072140c455180310340d100128200c40c407c401c092040d44180c030700d0102e221074200714540b82d009901c8024544a011b1150040d540d000741c480369501c4c42044e40c90301c450302e0490042c6c2c6c01d483c401d8034101400c680c0010200305001c84482c1d100d4440717400382c99203441d182c03800d400b24902e0000c01401b44562070b01090009402c1105100010031111a0b408807140d81c146164483c0708404a4141140461001400000c0ca401140c1041c05150140c3c29180000da1078100b108020700b4140c0e104444c50b5508100f030540007000680150003540c0910001070b0f000c1481d03d450002120090042d000781c4e40440040010043c0000e901101060035141c4980c48501c00740e04500d01055000000390720800c0502000395116059000c1c00110050060904c88904003101c0e001844905a50283d007140100140100075401110281d40f03155807403400300d00e4402d03002c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 622886726 1250 622885476 622885507
    0x10e03031e040f2301030207020d0f0317150d080307030906150f0806041e0c090c0815010e1c03050f0301090c021204051807020c06070b0a05010e01032303 68
    0x80007001000c800305040c890340c110307440558003a1074034590701418003440010100c20003592642c01410180c00194003000c546441411a22081d8001044210100c035071074054140c1140100080703e9000680001c0c0800c0c1007520000039805001c0c0004600c10b03440e03120001180c2c00141003800b419143d603101800100603110f407003018020751446401c0705041280001d5400380741d0341300032001d130312600c10f00000c507a003075184480b10900c1c940f0004031101c00d840d04410807022680080c990901e89036850213019000034503e4455890000182e4038103152500546620000002c4035801030a6404240445817010b1444d6145900078140542002c2c019120741006500036008501e8580d01c0d05069240b11fa010030004190015a19206080c1400c110204002d010035103110411142e00300d000c1180f5500078013460507001c0010708015580c0398241088040040103a401310303a891710f00300002030036582020b001411380740d12800c8544810b007010020a03e0a80880303502c90603020422841d40c0c0d101070304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 622887976 1250 622886726 622886767
    0x11030a031706030a120507150e0d0e09150904050c091e100608040f0c15090f0b0406020d180806070f0201053123031e09010e010e0303 59
    0x941e180d14010402010804031228007070481c0c0e000354400c100e8000090b04c450040e81d6120f5031460610307100e60362410f051021503105100d0042ca5807070441c2d201c103002000300364514800016111100350061144c04e000103900300302c8000c010501c5a01d4070708154500703014102d4005004000b249c2890602c4c80002d094150f040c1d64048107001960100303040e14100d980001d9004031030303c001c0f01c04146801d8010b00004401030004050340d0340c0f2001c1c001000350b01c0e02020041d0649010300460b45000301d0001d8600003050180c44c03000f0724030a80c002a00c150f400221015200c4a5010348044103403807034141c03143d0790003103d101c00000580c000451916030402000d40309241b150b40f420114503110b039010f030071548050003070a4206050010b40400807180a842120307400024140361040105003003400001b520003502c444140042c141b41000294004094100041002c07020708500034100c1d05e01d0b0380c07442000000d03800b00310900d0a41c44198003e207000021100060300f80da00d0801c0850807200000c03441d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 622889226 1250 622887976 622887983
    0x150a11070806014e14061906150521070c030305072f0c040f02090102070806010e01140d05010c1d06040501051b0a1e02011202090f0d11030a 62
    0x2e4401040a030011512001d645501110862119000ea04034070030000f100303c202c0002c400c2c2101c10100003ca84030081d002c42d41e00000c160100b40c002c90306442d114402910490b03425070300007012408955503446034104503903035030b03102c1480c0030801d80050303c0d55040030420401025800203070a40e0b050500501e03900c1044196507070707402074800740340c05000c441c8090004001c02511814144800d2680450492140004230040c0c2d010640d00e0011840c110b10443c407a500281403401311103803054140c01409100d5403d070207941d1840e031603c04035030365400b09101c3c440c00e4520300740c010000c5480c04ca030107100c412009080362038a60240c2d100e25007994440100c1000041c01a0000000d020840120184100c4111403151625140c000020030703900805915025415244620000c4040c0800100c0200d0340c4c405400054900c40c01e5848511241e86042070b804281141c40014200401d03108544072100c009010300e0701c0400b024280194a8980c1c101200c0340010180c5413200d9590070020384800a20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 622890476 1250 622889226 622889233
    0xb03090309210d030509010609060e0105090f0903030408090109050d0b0f0a051905090a0203071511030a0912030905060408011d010203043315170c150a110708 70
    0x858030600c001e61400c41404500c00c100c0603402c860807200429604041e040500e804034082e160b0b941c52a00412450b40071102c02450b011002400d00c152540f80c5041381c0044034402074607034a0f0152038204000444802420b134000b000024005102c1c480501180e0030180341000e440b03a1a440481c2134203500b5241a01da4441c1c100400083c2151480c0180c0e02c80289081407081c0c1c2480300313210301542c10750400000c1d0142c5440c0024220306e0301304011000507400034211003d60790b0743c6c1140d01c820f0000351000c41c001a00301d01c042882e25400000c54031018078940d103040c0b25a24004001d822003911364801c40c100070101a00003031039690384025201410f955800007130300c2403660607a01c140e030200b002000c403641d00500030480440c4583c0e610110003d441904c1c0c2c06c00288000d140c144410450100d401041d15000d100c0c000b0200d40d03240e80303003a10000b10190f1036444981001c10f580d012201e84944d0b00c0b001064000c00090600c0002c0d00c180b0190f414035001002c2081400c609143d62034011151550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 622891726 1250 622890476 622890487
    0x1b0c0303091203052208030a020d0902040f05060306010608010b070f03031503050c030f0a150e031603020606090c070b07030209030c03240106080c03040204090f0f0303060302030c1008010e040c0b030903 89
    0x82c2007540140944c1c80117480601d029042d503c11109010061000d01401d50200380c08462074225040170700919401081007100c1c2d8140c0000c04000c06003612114002e104560012030910301519890b4107803079004002c642031085980d103c1c3e0707504030015400c400305a1104a0250341d9010440c0e282d01851048014002c005100e6051501e0400701c254043d100d64000107013103010400d0070001060344080c1500128003e03030030500d614910b101d50002200f0901e001103448040c964081495402080102c41c8001c583e21000c6040c4464010700101070400f805620105104c20700030342c0240f000b8080038060b180700c8403403800020f09200b414144030704151b0149070018031010100d20014050a11801c5c804400e05000321102041d02000300000c1c0259600c40e1a04103004078980c0000340d46911800f1004103480382d10b0000d000e407080b4801240207100300340e4004018a4041c51121411940c4d5580309003981ca06071311341d524200d018106540c10280304001207075161002000f148580340300c200555403203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 622892976 1250 622891726 622891741
    0x160c030201022104210b01030308040215070201051204030e120a15090c0311060f1914032202150a1e1e0c0318090e01050a1b0c030309120305 62
    0x22201c0c4260244030030032811000f00201500b034600791804a0501c01c20014941600c45045003600e40282c0101c8505000008066024801d103206034400d03503114110804d2004407409030b00951740000c0c00705005000c0c0801c00329107001d005911a00900c0c1020140d0791304c0000c9101e410300f00340600c2e041e0f0055801070091240089942c100c9407481e500420441c0e841c1c2c0c0760030a14103002c0c0401003400800e20a0300303415030b407008280c400ca030491070309060781c0d104842c21081c400c1078160909004a02101d1841050480c20402d40e445509050182010040c5c8403194400c49046020226030014004181442c0b00c15020060084c0d000c01e0303181c1521103006800f144901c3c5d0341c41050b02c0c003000700d40700d1900ca0f41080c40381c50581003412030a2070f4181114901c0d0a8484035140c11030242e59031900f540024540340303181c021542d24440744000300300316255040c0c20f000355056100c00500b040b0824808003122489081c289182c1402031800090044c1665690b0700300e040c04460440001e601c0f4070500004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 622894226 1250 622892976 622892983
    0xb040501210515011d09040212011e0f180c05102d17070f030e1e0313050f0604050f27010f0801020a2106090509150c030c030606070602160c03020102 66
    0x4aa600d4140d4085c100200002d54221004100074003c0410340b5580c40e03511400d400a240901403c11915540c40000e0103510080c401258103040ca242003400b4600c40c03019884901100c260045110042c00e8103100a200f00c10640150a00030081d501500d0321140ca84c044800d0310080034041c80940072065040c006003400e1b0015090401e0309030038800c1c440718a03000f424000303509105040210b049400400301c0c2c0d0400710628641c4842c00307440030621a0b210030210041241243c0300e0341c140c03c417945807000d01c0026200c8000d9146c11050400c02801980741401450310740a400400000c00312407031061800b03078141e0f00c02c81d00003650308100052020030a1224031502078440c1070000c6040101c4880020200d02803611072071070840c4400015161031401e0b42080c4058105440103004600f0502d8039240e80c0e0042d032400c12000000c1402251244440000b142c0c001c00440c064a400c589801e4100302040d030181c681194002d50030001d010340305a6070782c4980040f40c0034032685560141b6500003e0b08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 622895476 1250 622894226 622894247
    0x534050409050a061a0a0f1d10080103051b0109091503020a0e1e070507110a08031c0c0e0102120a1b20060310140a0305030c06090c0603010b04050121051501 69
    0x2410b00c060080c1c06c1c0c182d0f400200502403d68a00e8500310b038036030980c01e00500c251520741c1c640c0c20130b2403080c04010468000207068120b070320031001c40b0480103220200d802c1458496950381e00040c90040200410502c5400c49404014a804c1090769650340768002141c8500650241d011805024104422540d40d2050350302ea0038442c2c1503212941c600480004d00c18882c420004010309040a601c007080d851f021755080161000c0e404503656880d440c10740089202c405400318004074100200c50841510910280904180c10f8005142c1909034910107d021340000f80d0f100c1c01c20504035490801c40e0b1001002e407415034000d00b0304540301e02c000b1090206a404a6000c0780c01f4407003c10a000d01c000d18080b1881c21035003c0c84145082104907800554441510340c006403092002241c0003a08100209000740250002c070119141c4004400522915010904c5845104181440300b04815402081407444280c1105a0001e8140e09407041400300d4009480c801210f401410350041c40707580250043c0c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 622896726 1250 622895476 622895519
    0x1236070902040b03160903080c1b0a0303050f030c0705030403080a0206130210030b190305011b030501030308010b0c030c0f030d110711010311040905190534050409050a06 75
    0x140b405007040c1d8008101c3c0710150424a015400c52041c200e1a84100900c0d00655403080c855943c5a85642d00075680d0001030b0f5840042466600300b40406180c041d8804080343c0d8541c55130b50422040c40d4035020316410081000015520030444072001600610041c40510712402c03140b5260000030714000d15240f0000c044006817140d585a182c05a0b48052700d00c90701407030303c2c0b40118144807803001091880420340448080e01580c42c00100c04c00c01e043d04148040d45040035041c442d5920000201c09035402840080c0c046901900144000031240008011103200c0c6c5007164500702060100b0b40c0382010017820058a40c1012031070a00288036402110364000302096481d0030040c0703c1c0c451401098100400a047c107640e0700c0070300e100169900540d802019104410082441c4c182c0c6c009066032009864070445a2034039002504e808403079a503805034150503a040c080741c0c2681c038251001e90001c4480314024008203100010307008807503001d6a403043e800f10001040d51031901c1c6209404009651070300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 622897976 1250 622896726 622896731
    0x50a051807030209070513030606031a0c070f0c030b07030507080603030405060f0d060803120f06040c0c12110d02010902130c02030706051e040b07020f1212360709 72
    0x4444256001891600350b980460326140d00b510781d10390554003407003070780b40014007908098800020700001d54400003c480c0110801d802c0b04010320300a02a40c0000c0312800c000301c0c402d104041c04660b104940e2650544900c20183d480c5880c1e44031844464001c640d94400640c48104000e0900d0384a01070641048007a8000d41c00c01c0d043ca80000c1460013001c1c0103180000c40420319000c40c160710f4000800520b10b24040ea9501c00c220005200d41002c1101c6114041c9040404264542041c0c854181d100c50180e0719002158078a81c3d0706400d10449800c00810859071441118402a0034001501002c050b6000010240140d10510080207000034000310020325090f00070030034540100403170710382c035a109200250359503810480820301c50b200c80d5034040c5034251408002c10420f000440d41c1c05000182c0071031b502c40b001102c80c0c541d90401c4400b00301c600e1310280700120041000400207900b00d421003a200c000f04410740484060810701108031404440050329400c0d29640c140260400b406000d02d09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 622899226 1250 622897976 622898011
    0x7060908030717300f0f042a0f0305061e070f0c0609030f030e0d09140109050301140f10080c010e04200319020403020d0602130f0801050a05 62
    0x12141c4034055007801a01c03c500009151100c03003503500481300d00d41c0d1300e0713030503060007042c13040100c1c4600d07280c142c060540810301c0010801e80e4925800d114860203040704e0580c0141d58a90780c010005144071451100d40030000310881e03102c1040090340e000703010850552100c603495400c1061510102828009030fa91883d842074240800480849a002204d030030a0441030302c106000300c03020607061030085e101c0381c136002003902090307886806103036450142d66003030080c9905200000e46401014100002044465104104510038002120b58110050506484059442d4046402d403454240c805c0c0605000130104900c0c1a56801101e420440b40d15030121074031700b80881d05039910340c01c003807003414440d811038801020307550343d00b000f0015682590b05040803032007903511760f409803c2592010580f5048200c8545102494401d03a0200c3e074005114444e00c204684a03c80207501c004200540042c00c03000214080108908107001088000000140707498450956021950b000d080f610240000c0b510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 622900476 1250 622899226 622899239
    0xa0603020304230a0c0305030901140a21020904020d05041e0b060112060b0a0806030705010c0b0c070606051c03030510081f150b070605070206041e020f21070609 71
    0x200e91002d0a42c542d250400c0c2e9040f02082c41d0400021004241c1d00d100e00010003044404806031120903402e03203403100800c080d0a00824113029400030400014035192103820900c80c6010400c2c0749100e2504010300e4a009400810140e034083d03803080d0070309034851003440104064040000c940c900070b0580351001c00480e41e2031a110342000b40c401d1b410401c04400d50b440c03032200c83c0e10480c024021080310a54076031300a503000d41080802c03a1000e109000b810b4000a032540603091046150742c0c00090350345983d6035140c003000303036420692056460310307690000800c50b602d59100c0440c81c0d50710071039407111171025481c0c000c0130342d60700400c850003100e800f140c20004010000f81c02c04840c502690340154004021195000400e040e9180403d11610a44001202c8442c00010a1140d010b480c0c103000c0c2d60b641c41c170180c0c0e440d0700540e0300800910509000842050f03424820340e43c4948010101c986546020000480a4250307055001c606107109500301d020003020031800000340580c1c01c14068040c9040c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 622901726 1250 622900476 622900493
    0x10e060913060b13060909052a1504080a0302030409050a02130311131e050901020c0304051005040306060e1909021005071b0303020f0d080c090112020d05010902090a0603020304 78
    0x108000c0940f0348406003411141d845900d40e03030015491080800a0681d9100014003400c00d03264292007030700130380d101c09032001801d0301c500030326154903452164010301c0d107000d00610b181728205a1400c2c200a0001198402d414030150010304d003c0c0d4015501c5500f00300300101142c00280100310007610402255203500c00300c2c2c41c05421250030085a020340c01040d8085410b50090780b610741e46040c40d05100c514018554010099000c504050400040c1d44400c5220308074800d540c058601a030051004001c10310740894070308914500c526200341080da4a0f5141c0c010748800303820040030421548208140c2030120000b40b03402d506010b5061200b44490b4000c00c0728102800c4588040280010310303603040c0018003c045150100d000711184903980c0d02e0034025251032040111035080e000d8851558041031082c540f041c05a085810f8080c0392240c2d100c0195041c09030400159045a000c3c0309040c1601d0003442064000c05501c100541d8410300c07c001c12840301c042e40c02c0141403510510030b0001203040c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 622902976 1250 622901726 622901761
    0x71b05070311010c0f0302030a02010b1e090c0d06062319050d11071b170d0f0318150c0207260f0f030901021932070e010e0609 56
    0x9007030702c807012100c01d00484510341269400352807010f07010b510341e0070541d00000400f14600d041e8000c21006100c071080042e030b8805190000c14000d07582000c1d01103444c00340384094000e14104802c0c0d141c2081c462a01c0d0603503507203511000c0400c10380301d106000101117407502c41c040c8203280c011a14115045460029182c803802503141044404200354800c3c400b150700841c09104041c00103038558050f46013100031820201883c00c600000310000017144400b113154283d48405a001510389912400401c032800c4480c95200700c100743e11400642e40800714012030516031400b1300c6030a1002451500c1038002e58004059050440d44412801c000c11240442da944c400c2c8c50b00c03103e160300317003000f44e00252030310061009134000c078006c10140b0b815240000006190f411000c6e0240e81e0840400b4606854141000e0000b60129420aa00343c000c1e20b15441d0100d50222412920308203070f022100b4583c078245141e008442e1702d480d488014402401c0000c400b03a0301080c11100f040c0c10b403401c2002800a400359 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 622904226 1250 622902976 622902983
    0x210a030b0f0618130e071518030807020406060212040315020d05190605100e0d06200d0506030f0a0b0c04030602031905060108060f1c1505071b050703 66
    0x948101100300c1c1d032109155804520001c0600b921600314404005900b40f100d100c052150008000342c8044246074050702040741204006042e9143c07400e0000039a1451013001c3c4420001034408407519070130140503a01c0614040c02c00c2c252903000510510040300d580f0340105040d5444004141d032030340d00e10821a01032b80d078000003062511040c400039001070701070301884803080c07414070042021182d040781040300d03040030320b880500c10b595482042c00301800d8230456040004400c08101e1000742400101d420150b84540b400058011102524031402104114644a801800a10a680c4001c10300481d17400000c03c40290042c0800c83c0c80b440d58030003465100400b40044100000c01c0d440969003500d00444d0049829903481c5442044200308900c10f4500c03084031850310002c1800d951185a50b030b0f100f204080c1c042c440f2040110200f19611a04c41ea101d01c4408051300072a001600c4206624002140b21501058034204224042d02c08046004254000c40340a145103001ca07030001404800c4075007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 622905476 1250 622904226 622904231
    0x10b0903030c01020a08061305060a09091b06050c0d02070f030b07020f06010f0905070c0201080a050c04090e030304020a3303090609030e0109140618031905010905210a03 75
    0x2200003081c214002c84490351050b500c00b140c0060825001800644a03e2080325903003025107045840c802100d1058407080e411800021062154040036840030083e1400303004800d131101040358004201c40b0182c1c0104001034030110303507400c103030b0410810400c003e003650025203200c9052000e00c0b4010011440003030466080c0c40f0200c1c440d2030083c84404124641e41051703516660310b078010305541c0c0400380304001000c1d2414002074460380c800c00c000d016642d4141e480a4030f17a00c0303940380c13100600b1020340003010b503450400001502d4481803041c1c51400a846000c0c41e140d252038010000c60b105a5440002105100013000d25582a0300390030400031040d6042c2d15a043d40030b100300f10700410a51000070b01c140d140195501c2030680200010008120981c4c80b900c600f40c0b6620702844000c12081015080310050190000401c030900d65a0302503e005411540741e5020705011050b2505000015078a0340d42d9140311006006040c4556860006900c1555010b0b0100380b001c3e030124414812010201075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 622906726 1250 622905476 622905487
    0x50a051c0c051f0212040b0313020102070b180306010e0108030a0309170301031a0c0f04030f0204180b0901050708060a05121006062c0105040e0c12040b04020f090f010b 74
    0x3490005809020050b00c1082080700005041c3d050080361222600584a07030703519100321008000440c1c0a480c49081050b0454a40701c06241c05081c4a81049055008107180424070f0728203200a00865144205842c20742c80a6109140c00d121040c5c10009030155200d0042c0010307400001240c060216604d40014800b00500b0b2044120081100a809242001000000784841d60103c0c1e4131040d0004031032402ca8490018a072200c0c4501e03011496000c005010400100e4201d28510400500151010820790501d000410104c4410700c03007100c034140e211003030000c580d000744541c5a02c882203050800150a00c5400104a43d1480c0b02c5ea038850300e905c10099044030b0090210344c07040c07000c3c104e0500c9181d07110744001d804401c5071012082121506010b000005041c41c1801c071042d0010f84502d450030f8203020b41400d1500000341001c46103582000900103440707020740001c0c8200d0050500035902c1c1024410000c65032028082c0343d110703e100390180b144124040c4252811a00071034203071580c84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 622907976 1250 622906726 622906733
    0x31d010b03070e0a0209150d0506042d0f0c1713170c010f0c0e01020c0613030b180a03050d06050906100f020a0506130203060f0f0705071103030c01090309050a051c 72
    0x3c6c0701d40c039400307500b009000d15844040c4000030301504803015403e0080c05175a0f925414031046404400e6021140301e03003070504108043c00d0401c0c40220f5602c1d080d001c60700d502c1e00d02c0c5480690b03052503110000030700144100e0005c03480d03c215054000c038820318400c034072181380d460304050381e840300018000402c0000ba101e210725000f54441802d1184655040c0050100c1d00d501800c010520701107035015002e18203a02d201c5107030002c201e0707078804804083c21500d2411903c921612540007003800a001d00650241c03882d040b010004201080c0c401c1d51025a250803801c603140135189541d000500a8400c0380a01070300b40c1d40c5003800011070311280f0b81000f01310b604031422803408010b02d00c0944a40101000d100000280400040c15180258110740b01c0e625802c0c15089041d1084600c00030000004c0041000745104000400c40e142c014520141003001040001e81117501c006a85030080c0e5651807808201500200c0010082034201c0381c1031b0080e40f900b00465008441c040464244803142c1000c0001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 622909226 1250 622907976 622907981
    0x80303071d131d010c0903051e011d010218040c36080303040b060303030709090b0a030b070818070503122215080a180b06130c031d010b03070e0a 64
    0xc1042d00601030203d05640c1145030150210450783c498194200707144514400e00401d401811650702c00c1c003c1809031007042c090380400039030301110480d954a5100e554210041c1043c1c00380c411241c44001a81e40360052031074407001e440d0f428524080d0381070a8180034260b42003500316031101c20442d5032f0381510300703608a8096070305030720781100f4070b800301074540401e0400000000d98400e6200d000340740015290003007095a640030803170340240000e0b03040d07a0600c001441070f000305040b100003800c1007807000d4681d580c1c860013440c01c80344280001c41307207020440340311901c541d81c0841a502c01c000e0070780d440c00c08012076121820b01c0381c1030a103c1d000242c51908000b0100003080c8041b40300d69080841900d40c0308d0031254002918152002581142c081551003a1500c00c03840d244610071161000841c0680e47c0305000c2074001d010550055030b08580c00c600540ca80070342040e00000359030004840d200507070704510410341844040b001d80c0c9412418211614000340c02020b42e81c12802030301540c0d4910030141c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 622910476 1250 622909226 622909249
    0x804080319050a0902130612230114090d0c020337030503091002210c09100320030f010b0c0703050d080f010b0a020a2a0b04030606080303071d 63
    0x7640780034100584260320fa805400401d2013100d0007045400401742680c1920204c0c0580c1c500704042a240324000384009555041c008074a201881d905900360701518211280c00f9113401540517840304204d4818014000303043e8414136414440041070301ca4001c40c1e500c0001c07420b000980c1401c4026090302c00a6a0f20303051002503001155030041200e03150060068106664000c024400e24083c0d6243c0c0341c2d9802503580e00b00e00c1203200c4070400381c09152100c01e517030041c0900042040410052880781c5a04081c0c3d100b02c50f46071400b043c020034406d40116201403c0e40401c0c006c103024000d1104400e0004221411901d8000c40c01e61140c0300e155031b00d81800016400109035200d4080c610404d150420b01e206c0c46011021012102d580c1d0783c1d0803941a0b48520000140180c102e0900e40700001c1035006c0c8916001c800070744007409002030010141c4500e2680d0008010100042410810024240560f60183c50000065411800c01c903002a1032207058110441e140005050224016250000c2495 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 622911726 1250 622910476 622910521
    0x507020f15071713051c050f0304020d14150115050403020904051509010b1338040f0506150901020703170d020a03050406060506030603070605070503040e09030a09060f08040803 78
    0x41e04e0402219264600100c100201e9680c090218011528141604003000162840e10b035140b03040b4001d014108194001001260b02c0321004c2e440c02e0200e1507000034a6030f220103d2008000d510b00406ca040d011450590000c14000c88010903086410780c840c0039601120b60507200686c0589070b030b180c282c0c1000b6240d9007800c1684040b50030801010340540005005031030944a814603a00e90300168010b80350515680c2020000b00e00048400b5503c8020680c503c00341d0b080c3d402403003c900c500050554407410781c0041a41c2c2c0b92000c0c42000d02d070036501d2480000b00c1c000f5880c03506624100107526103c0601c0043c0c0601060301010800c580c2e404100c030218178007000115514010900090010001920113540551400c10080380900340f840c126802002c004008094140c6401e00898055010032402c94079400184000105030b5074044c079040c00f0b1207045016640320f441021004050b800541d01010800001c2c8022094940c1c0020506030004d4001e40100d0b500d41d2842d20b041118404409201d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 622912976 1250 622911726 622911767
    0x10b0f120708060c0703090f050a060806040b04060923161407020402030f1806010303080a020d0e0a060b1c0c03030305040201020c0d05060601030e0601081216081201090507020f1507 80
    0x245072000c000300183c40c80b949515101923141c0382c01911a1a16019040c1c0041c12540c00384a0705016140e400c1d0300c40401440441d96001c4100443d064131010781c480ca10140c8c88080000c0300c5502050015201c1024403c5080c01d8507115030240004da010129400600c840405410f05510300343e02190009070300580155504d0414060400c00d648040b6500e45070b000300c1e502610011000807681604076074065441ca850382d280c0805507030081d40441c001203a82c1c0d0f0b031500340c1c03c00c0c0182442180d0380c050185400082c0a003880e014020000400c1c0c04100c41c07000c885020070009800d130000c3e5426a501031800003695551480141d10380b1959a05081d4811030107403406c020003a00140b2b07940300c0e4000307903810301c414460308580c2c0d903440c5803e000700306254000c812421a40103071071000c0d2100c140030b44e618402c2259a43c0b5141229401801c40010030743c2090010b00c0301d04001c0c010540c10144510042440c0c41e8042040fa44a0507452558698000c0d00c00114085510070b40c2984c3c0c002c2a00d4800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 622914226 1250 622912976 622912981
    0x30b092e0906081e03090117060604031a070e01170103080f0d15090c0c230a140c0a0e01050609040b03011b0c33050705040e0a0b01030e010b0f12070806 67
    0x3d496540f103441c2c2510124018403c030a4540b1300340407040d981d10b20b1741038440f108000280c0740010800c4000914070b50300220140400008594180949041031901d50300403001c604011000030f10101c441140d4038144240507100c01c1c1003200340064581140c1d000389042d030711581d600744a805503204148061040c0390038661155100c01e0f8240c04c580807103c0c04002045400040350f820380788210745100103000a40c5128042031030066090740b03c8613840090065401c0340d0728980c4c411034450340051100a01d9031200103054081d007440360303030000500031007000e00d03a0940c0b50100052262244514040c0625100c0c0c211862a032401d40248a10503407007415200035006440c0024000080c0c06002d0b141c01512000b04440c20f49003070040c491510300c044564500e0f1112001e4030340030b00700103045141001020080014040d2100303581c24016104d440010501e580c2110004068914003074050749140d150202c102c07500d96031095520380486043d41d20f00807078a00a1002c07424403186a2001105000d50000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 622915476 1250 622914226 622914239
    0x1020f07080309060105010935030403030903120207180b01031407020c13050705070b15040c080a0c08010b190201140103080702100314061309050d030c030b092e0906 73
    0x28511440d60341080b51090303031b80d520044405501512911815900250a1000b244409000ca0810420b0001c0c0744041c2410059038030302e198019401070700000c200c44000e00c20020107034040c028555440c40200903080c00d003010b5902030280d2a940d8580741e03555600408159000c3d07082441005100e0312402d856107070014010b0744a420304010203104501c2c1141d00d40d2940b445103d00c5000da0b61956400d4101800b03540c47c3c00b40c456001c1c0080540d001d40c0300e0201400d94070ba00400d0040d88940d51350240302e04110040d01306039040208118103108800005002c02d41003c01640c01c0d580308000c5662079294030000176401081851000b50f18066032000110038000c1400080c00041c0c400d503a2911441c407000c070110300b1101301601d401585050300b404901d00d45000d0300b20b00c562003481c0d48009203081d00359031081c0c58065044100c10120380c5520f02d0201c00da80500c24a941c038441036407460340ca80b601c081c0040c0c48031407042c3d0008881a84820403440c4048503854000608008502048001e8503800c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 622916726 1250 622915476 622915493
    0x8120c0601260604120306060212030402060304080c0307060c0f03020712080c04242a0b250215061e0904050c10030209040b04183003050609090a050d1101020f07 71
    0x5c032004641071040018103944006520036280c0d480f100e2041c219180d030381c02c0040c580c0c006841942e034184240148140e0b880184000c0030b649215402c00203000075800070203030441e09411503400a0610512030000030880c02074009603071031028036010301c850307a52441201d21070249800c412952542c84d080300b409140940071481c0046c03900d40702d080e5911401154a6900070441a01c0080304d628409c3c0b030b900180d0b2103400ca503040030881c4d15461005000041c2e81152004030201240141e008401108264007107109454201c3c00c00d4640b800b21201c1000c00040440138068458001e114417400202800713000e000344880301500510841c000f00307084000038040e40184940c40d02c1145010740c0982a442c040c8a001c042e180071900c0f0036102070305074594140003006058650201021285c00d42d01001d801042c60200c2c4640d034400203000d041900a129000e10000c0c840d0140340d1003c9903100216800013036207064412145010800040307a540000d000e40181d001c0d6807a0900c01042810030065682c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 622917976 1250 622916726 622916753
    0x30807020d02120312250915090b180a09270c09060e010303090e010e180c040501120b01150e2e030c0f031b030209180108010608120c0601260604 64
    0x100348181c154520b00d42d9401011b40282e20240200e210a01c00700107c0c00d103007881e000600342c18144116025511301d00504950310000d8145440c0b0642481144070345003444001010302030303e43c1c0c05c01103404001450b03041010255407080c40104c4034100c0604014050a00c14003414800300300b808250340ea2490b20300030003800c5c0400c030081000b00c04045944000070040034101c0f00790492041c80340d21010078010b0085100e0182000500809400e0300b81d40d2100d0051074000c081c20118a018500399050513041c40c034041c0c100c003c45403040c8100300509513001c1421400309008031121070044096540b030200c001e0003031541c4208000f03198818049240c1540c4400701e201200d484407001c140d590b8004038101e0b840c1c404140a80700d40007017107090b000d1082d405841e444101070310640440302d81c54160511240701341c1c0402000c0e1746501d0140030564040c1b1003065007074041302c03109050120503456203440d96814010010400c2d44480e8440c2d0f00301801950107075444103142038482e182814144808040c542c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 622919226 1250 622917976 622917991
    0x2120102040e1302180a0906060f090e0c03060a11071202010203040b010518040b09070e0108101103070c150b060a18120503040b091f0f03050f01030807020d02120312 73
    0x103540000c082c51052443c0c5210198001c0958141c04401c02c261007402002070302c1140541ea94684201c00241e0030711400010f086109000702190386011108019100c0800035407006402645240c111031328002900ba412031222580400c0600303040b404a4928003d41c20040c003100003520315900500d4040d40114003035801020300715660780c1c0381c03028002581e1404c1d04000c244902000040c022900d0f681c4c40981040fa00403d0744d480e9640c0750203240200d0004c1c0c00421082d040318441420012091242c81e241d20035403455a8110b18020b80041c01e600e01441015007024141d640d600c0c4000301e180d0080703100360401051070b5110400a003000740b42c0e01c41507140d13a0100502807008210006800500c00703026901100642c5031a00340004076119420082d04240c010040040c8100012031031903a002c80360800d030340e4202b1520a03542c8020180c40004d012042c500c00c5480051001c1200e21342211340c0301d501038603c020540b140d403000c0b4080000d2024425190b00004c1034a00745d060424809074001d00c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 622920476 1250 622919226 622919249
    0x503070f090c02161d0c040501120f1d1608010510090f090c0e040b07020606030a06090c0b040e090c0d020d0308060127030303061a0703110a02060a030203091011040b160212010204 79
    0x19440a00541442140196400700d42c005601c000d4050540e0082f01c1c1540c0c1d081008900c1d03101c0007400c43d04625440803410b42580200b001500b94503d080c00d0a03008080e01c000a12543c14841603140c0320060b01d0043e0b500c60b989a441e03120078004550000070105520281030340e04166900030051078000b00341c404442220034080441c840900c000707102c07402414010040c085801c0c042d50b5150040101130f03070403664400850000640c907100b000180c0010481003801180d20300c0c0104026042070041c006075840744810024150241e11740704c40882c44a40d150030f041046444c2c00d40143c50450000015545004820000c0f01481c070070000c031401104e1007078038140710050321f808038240246801d520000040805020ba80f0219202d881c2040e104101c0c17106448503078034250007040140e401410b070340c2c001c2038001040c80200c00d4100011203158078031080401004900c40398558840c032940c807a000300c05c0b0002c074507080b02500c4000305414090b40203043c40c1c41c0d904850350841c040d400c98403d0351000c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 622921726 1250 622920476 622920481
    0x120201020c0406030309140d1401020a02150c161e110301060506030c090f01091d100b09031b0f03101a010908070501030c0309021017010503070f090c02161d 69
    0x2071601030f201c1a03941c1034583c1c070300840c100b441c0b064414000080302030740300c0e5820a000307000c01c040403100800344258200150b1344844015001c3d103801e18550340302d0000c440103002c00240c11504000d80b1301010000080b130f07c140404c1d05007140010150201012000218450f607802c001d013541c0d4103a01d80400350000c0c450f207030341d500810109000031902449402e0341003110507400c0ca40130400d00d81e010340c141025861252251741e030001c600c0000c0c0164800c00e0951052249801d009001c4000510002c1241464944e040000c41c0d02c40c00040c200c8030f1000030420040941d5584e0500d2545060f0021b800c0301c103050f01007401100a4070603200700b10391241c10042921450f520075000c0c601a68030f04001009018a040011402070403181c141e00101070b130f10362080700140d0368444c4035282d0031440d59078064200c0401d070180d55240010b80c00a8440d6003e44010401d940402c07110008031400d044e40012a42151300080c0d08190308003400030842420700d0008510f400a5140300c901d0000040b820000c03e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 622922976 1250 622921726 622921729
    0x3020f0105270415060c08130f030812060f330f0310091b0e010903060f090c06110c090c0f0408100c030204050d021908030409020c0f01090b2e120201020c 68
    0x5904c80c050780d000503c2c824000e00204440100a2641403060504000720fa80d6500c60703606041c0a541080320340e5200054450820040c4102c8590040411141602d9004440c40094403152184200c41e006107001c8501a0074090842201c40e604014140350950b1210722030324100b95544102e03001929040c08800200b14441c86115190b8049010054586584142e01c01070754400350085110381008220440440051801d00038044031003201e14001c1203c004600d00814000e007d03410100400c082100c60212142000940b07021058054504801070344079031143c91424424441030300072550700050001501280094a00c412030310b907960411001d125010210260701c075610a00358006410100b620151406002d8440810740f160401c0d108190b50b10f220070b00756001580b000328a40e41c041848140c4440c28091090740608100003041031200c1c80d07591500281c00503001400c1e030900b40c002c541e07408060380b50440010700c000c40044500d80d80ca0700001e0030f926200004a00501409901c101c69 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622924226 1250 622922976 622923011
    0x10c020c01030f0b0637030603060506012a08271810090c031515090609080a03031e0501080c01090506190e01051b0c090f01060903020f01052704 64
    0x1004000f400c0c03611300001001d14041c041c2000b42c1a42c403024074180b001c49800c1c1d001d486c1d00e0740306a017510040358862440c208541101d000a1056040c0541d0724071030f0448160358549040c201c0c01340e0304451b641d0849824403406c58010168607809051041c60022150100308002008138902120340d0380e00c001d88181c0c114902c0301e003a10400650b00078a0701c180300000c045d4020700222252032800190200300c4003030000c401c030503a52201e000100d0301d00c00d481d0340c03540c0404120003138851801d20030081340c6444255941c44898030009000c0660343c0c4000c141d010b2a01c0340035942001101d0050005584415a10743c881b50500c00c2c190200300c0c0c0050000d1103080a8050b146100c00100720840001620403060b0b40207100c140c5202e04028042012420402c070a070144404003c481005103c5001d20809214207001c0c050000c0c155545d0b00001001040d030300c9196401941d07419a20480a1050140180c40368001d4218404d10507030b0304514214041c0500061808442084070b09002464040401e0081c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 622925476 1250 622924226 622924241
    0x180b0c12040b18012d02060106050f0708070c0f08010f0c080708180f03181c08030c0a050403021f03051012032d050301062c0405041103010c020c01030f 67
    0x1c82d0b00050111080003509400307107030070710305040c10120307544d03200c061007031030080400348201c98960300030009845e01c0340d41086681d014050504141e4a8078245403c01c1160f40131b0204000c0c40007070700050324010000e03100c48000c02440c141102d42c10b0780c1e0301c0310002400b07800c07007a840d545081d2821100d0340d04e440c80707040d01c0703801644a0b458030601d0ba240c03686800da0f000f02c041070501540c072612400035143e00d4200001c200c03104500400541805004c02080010700440c0f0360140400b14001500000c510404120707904000c519003c0d0b952814260000c0e60310b0b006684c0040d60058080c0900d680f14814402c10380c803401d2455a0810450f0303280442007288200a000da8203030740d11100f5030303100042e001d4071140c0d20b030703400c214054005480441d9125041c00813110107803002800101c010001107401081d003541c44030b1080340b1800425080d0003040d070900668104a0322860311744011805001d1b14154a85118070058000d10000c1d1488402940e079500c05012203000a00d09822466030a038540304800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 622926726 1250 622925476 622925489
    0xc100c05280b1b030108100e0d0816090803190e0a0b030f15130903020d09031707081201062001020c1b010507170a1b050c0405040c0e040b01091406030a080a180b0c1204 74
    0x2b10543c0711009a003800b5220001000284182860046041d0808002620841c040251041d1484000c2c010041040000d010921300803d00c03507906100d28503c07001600e50005210119100d03903a204d00c614041e01403940340b07664100908020702003001c070030b5400020a2500a8080f40c01001600d01c3c116100c000c2803201504d40342c500ca0010b01c01080d65001465900c2c0940081414040f01d0301e424102c80a081c0c3c8540042002450411451010320215a00040b0030718000c60800011550035525014444010401c68440c40c2d030b00b401c1ca070b0040d4260388559420071070150014035004800c030482e03804403980b00c02013091080d1344030f004445c084034440381a40c4040906469000c0704244000f409029004541503004800041081d1070440307076040c4210b0240f0013040c41545010088412568540c1e60340584c803004c482006040c0e05c001070b058003c0e5511034540341e0b446d8032986080b00c03044250813018840b00082c0400140d81d0002c5006415139613491005d0b03404040e00e081c0d00e01d02500c01c510801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 622927976 1250 622926726 622926737
    0x90f0c090614031b090703111b0f0a0b04020f060d1a040501090b010c081806070309030303180506040b10080304090605030d020c130209030c100c05280b1b030108100e0d 74
    0x2d0480e4203017010655001222800e0128401c1140310f09100f40380c1290082a030f00d0010032503040f00040c0100a6028098802c2000d40b107013141c583c8904404220040c0003a02580701070300203120584030780727040740ca0351441480104131907000c10070f0141c0000030043c04070b4466030800002240c2c264291043d445020016190340f42000c0c2d542d618100580c01103560712107420241b8448900d142c407103900400760345120f5664035181c54250b26024044440d140030504100341c806905000160300000c1f001d13003094000e200c00140343d4401c8292030800b09160000d40c40c0e4080410300080c50b200c40e030481c40a68070200d043d03880c59180342e18101c1e41c8010211041c1d5200a2520b441014056103900a09a20001500b5220640341c4400400c1e1080000d048080010300d040d0780000501405000d944152245515032080c60308039011070408404840401a220301c42c3c000200e0a01c50380d0068400003c04070203a00d0b0344a6948810342c0b41c4030140e003e48400c2480c200f178444c585102010807400e9040045403102e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 622929226 1250 622927976 622928023
    0x6010e030a11060d06030b07030f05010f060e0d0203013603020303060625030e1e0907050d1404050c12010b01050708090609091f09050613090f0c09061403 68
    0x21080842250911580c010f00c0812030b9070501c1c4000e0041101960040c6041409401c003428000c080383d00200d59002802d18101c0103010540c4504010f2040311817900d444003e001d041d50000d003210059181c0298950b18004001c88400030b000001036100c0c1d4000d500050201441c0c0c0c01002c61100018000c4c0103800810006c4e40c01d2605401500c141240100308000668500c074161316210b12645080c3d000c2170340243ea40f449231501c083d80340340005901c03040c841c1d00c00020b408200d02610142054091280104c0d50030003c4625038403030818100d4010100c605400c241c00c0c074030344a5440000e0203005050b4025a542c0b034920500500e040c841040e55031070b1504085e511016455003100c00c2240d8045070030099010a41e5401102c50b0060039004284843e0503100d074030484d00c2c82001d511000d565401e10007000078503030b40c080d80c15181810482d00030840d11315610b001c031140100804010150600700b00081821010303035010b40c080d41c9030081850701d407039105020544e55003000b800100003541030206 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 622930476 1250 622929226 622929233
    0x10e070605090d03030509100f02030a06140f040b1c080301030512070507050927060a0b010215061903170904060f05030a170c0d020c0a0905010f090908090d06050603010506010e030a 80
    0x496001800b00141d40d00040c03a203220000392783d207031200d031840160040140071100420780b04500041c80415101d00c505002d48000c16501e050070750055104a0b5294003042490311010402c3c6034080b080307c90a90400500c0ca800030741900280001e45091143c0c0300440d200030700780c030111030555070840300502c900e510b040c0400610701d070020324142c00116482008031441800e0244c40d420748403850b028209600d02121108221040c41d050903045503c00f0740310080400210940c2d44d080941625583c40000c074440c01c03284c1121040d40300805490503000000110314614001c0c1c160790700104c5040c0407955560246401d465400d014070340d17058001c460341d000045c000100300c1540b01035035004035080251404d101801e200b294607088025810411510010b4034200201c02c001d015000c8041000b03506181c4046040750281c0a220340865480c1c5504043c0884001031f1200070030000c00d000a82070440c54500302800d03003903c01901030740c20040850815801407002008040f0040c0c014200d40b0000e4a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 622931726 1250 622930476 622930481
    0x9050615060708030703140622050a090209070503011a04030803181509100f05010f03140c0901030f1a0402130f11030f100b0301060e10031805010e070605090d0303 72
    0x520950001c0100800e80000c0e00000107903208445580740001c0d02c2c60b0210f01d6440c2494014189882002d8180740a13802c000e08584414110016600016032641c440c80000001e0482e180040e5001e1100020031440b80c2d030200045040c3c480e048680001c406090100312194011804014002c0c2420b00014081034061500048400204400c607608800049a00d202c01002540c1d140e841d40c003d2554142542d140380110501003240010422031b03585814090081c207a11400000c00346800441c03460619001000020925100105481c8480d41c0d01d1a050f03091054070041114410802c10403070305141c00700d41714640f14a4014150348000103400e411130000b0203a24002c040d429039264000c011030245000a98811100940c0c01c015904100c100c2c50040200c070f81c40a280d1500c200b005004641d407043d40302d00010b405130703000d1000d0b03425070409402510440744c51828120000044030203020301500003c0e0602c05000694160680742c69080b50680f084010345a0410380070090100024440d6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 622932976 1250 622931726 622931761
    0x3030203071704110f011106060906060c37020901030b0604060b0403062304170708090616170f04150c0b0403120c08061305090f0a081903090506 64
    0x14074011082a030440c001d8800b00a041c0c4080d00c1c400e00160300c0c4042401c1031440d0501c085000d003041500d01c1c9481c00a030b6a00c0b440200007900444448010901d11f484000c141c482148144043e1006900915404511000c044c00d002003400709480980c3ca842000c51503403000c054014204881c56801d54541c442e405102a003117a800c142d03101000601501d0b40000390000e035215400c0860940705040b044003009100450307030380c03004250f201844002020360300d000014031001c0c00d810740c0300c003254200080d480c0152000503800c42d100282699140c0600d9401c095258032403c62401400d207803200f0a402406041d02d0305281701001c220134406524120200c24001c4164903200403007100559440f140300354141d03021804251500107600310b140450103041401c1015150002040c03400c6800645001401e03180300e03208682c0e50000c140c0d02c490a05c101c0c01c28051140403503010144502c1c01e580141e0000340100307a030b502d207580312542080c4030380104031104c2e030440014050740e29007048040031203011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 622934226 1250 622932976 622932991
    0x911090c0c0706050301030b150d11030313030813150e060f0712120507020a0b070c02010e300303010b040b2b0c0e010f020601090c1704050f250303030203 68
    0x601981105000822000010f805182d0b2903944a5146250440b0000e4020307103480349089e803003a8880e2498848900c2030070220f420000c01400906031502290552040884050042610a80c0070040c4404200107026120b9508403000c7c070503640c1c0381c43e40034801010700308400050f584203601140b460500c02601c6c010181d03041139494501c01c0d66421902c032151010f0400480d42d44545400d003c0304912403154003000350300280407450140e275605166039000030300c40741c14070040350b0078103056901c190004881004007a2501c88441d0692100380794564020b1040412140310100c00308003490080180d80c1201c90605c08541040d0074070345030041300d422910850168103407988102c1da0a0f50468002401001030000000e0442c0f070100c801001c201c4c1224007141800104842c0070400390b400100d807030440e140070742e0014020f000300340200c5455428001016502022100b44420703c840860709541c5c40401ca41200c901088096103910045644105056100518182040464040d8000715440010b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 622935476 1250 622934226 622934251
    0x806100201021308010606200a17090306011707090605100305071223060103140103080d0902040207140c030d0c03030b010318030914060903070315141305060a091109 73
    0x14107000380000640f940d20a83c003a030b44a42c402c00946401990960b480d0203032140c2c0000746000581c030241d6070820300030300170032130342055500106048181e0180c410000c8010162449945e683c1d44035010a9510102400d49000f00103000681814130f114440842d580a06014544100140c05038003c0500030400e41c03d01c42a000704030886540c911505140120044825610901c1c044805044d440c0042089050514101c0c02c0c090b9100c43e242c840f81180c0e070140d5140d90302c080b010003a00250280050080d0854004160001000b12031080000301c1d07902d003011198440701060400d42d80d00100c2c850700002c0342d10345003200c000c02e00c603800424550406047c0800c525100030005c0c501b020710700d9016000101003082c240203010b0300700071021110b40300702d840030700781800310000a45843c05480020000c0c00500c40040e04441d4a8120f102900350510380e420403890070312181c01c404c6600b91011030b124001c80c000a45203004501c625184660000e100d901700300c0941c003c1c8041c070503024080c3c0c0100310 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 622936726 1250 622935476 622935487
    0x90b0f0901140103050a0c0905060603041101030608010624170703020c1f0f0c05030919060f050910050702060c0d2a030209041514060a0e1c03080a060303080610020102 74
    0x5490b03107001402144254000c0800d5481424210455800e64000c0e1001d80d0401e02480b49580e50502620f80280d00321800318a41d00d00d0400580041199510400d0103509003003000406403904a240d0150f24150290000034040700103044030308203200c00c0d058039845e1205010038000c51003640940b040f0310030b1100b284c500341c1400003e070695950710441c4102c0c440d260000001c003d031240c0189981d1085a003400d9045042844540361100305400c4006580c220150039142842a56041440c4520182c8010040d038108900302e10388828107150804051810400800d0380c541c4009400c61182d0342040c141f6042400308401380c00580000c003080d4100c003811508211548001d4601546685075903100142d803420b10006100c00e442207040002d6030000e4005007000740d5600070b4480038410304112211591980c241c541680c402302e48000303054124038286654140c580e0210720010766a8001d4031041e147d603036085100b0099071402e00009000811700c401144080c2840d20414880f045507000150406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 622937976 1250 622936726 622936751
    0xc080d020c1b0f040b033307050417160b0a0e0316051c0206190908070306020301050a12050d0e0d1421120f0c07020d0b0601030609090b0f0901 63
    0x65004020b40b000c4400112000351902c0480d501c0e107100291010300008480c03900103610341ca00e4012030350b010a01c4840c50f5000401882d0a0701c5150301c2036541740f000d07040600d0001e00d1034026014100074403983c13660301000c800001481510804040c40c901c2c030f190741882000f6103541c006910701414007400c1441c2d8499a50300740f007290004402c0c00c01c252240c0d40f41c1010000029a10700c0b6400380b241c81403100c02d015803948421201c4904910030286044120070380111010007050b403211413540910003002c400c102561300118102c5104460204405483d04011161142403100051139a40140550400b090186181c1c040c15800280150f2000750543c4901070707410b094104260781500481d44940040803080e4903064505851403080f03051462090221a0442020700b0b220760032808100000e038029a084102c411180e4080c100c4442402cfd94a411299044140c400e54042401d00a000c58022090311502d01180c0e0840380840307d6031601021303c030907181d0103455107000c2e540f03412941840c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 622939226 1250 622937976 622937983
    0xd0e010504111504080a02122401090506040515040b19080a23060106030905030f1b010b1f0e0418050d030c030b0d1506081b0f100c080d020c 62
    0x1a030181072250000300d44101044103c1e4803661510299103000d00040c0004030000445041c0240d0545482006c02000301c03500b440c1c000b80c61400b546c6140602c1c00d11120882060300d0342e04846030300b0b03410701c4152200020030013559030440e80080142c900c80704104603850190001400d1940103003407240d010030400030524943e02e0f160011652544150400c0c02000800f000171081c2c860b040102050a4651440c0b15031100c2040c42440c0c02c040c0c4914015090080c18011a142c10a0000d000d03561151007010960110714074490b0045a5460021000000d0402c82e00392020500b015074140e4440424200c03d807910b2105200940d00656501904075198401c2c0c1d0841ca0124055001444010a0050000c0030781d02203242c244101130500c0054100ca07100c24260f210300550140c00027101d020134202c108000d1056501411843c403a00c2410b250b00082081c0000f55007409030303010100700100e44184801098002c0720ba0700010a001c0390100420006001340a404090304009480d02c501044460315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 622940476 1250 622939226 622939231
    0x213060b04090c08060d020604031b0b300c0322020d0302010504120e0310090302012306030d02010921020a050102040e07030501052707200a050706050c060c0d0e0105 73
    0x91840e40c0720020508550058007250740b110044480420a0900347e011669038040d070710004059254100c076038501940c0e4400c4a8000d45001400399032a201040c040c0e01500640d144094400d8006007000c00079404070650f41441207072100c241e1455900c40c4400c0d81c00380d69210003009544440e05441e2001680d50103548181540680d0012600e030410341003520520101e030100314140403407500c20391001e032800326050880d0075000600080f903072541d0600360301403c2409034414080b44201c0c0d008d43c010050546280c051503050303080f00d6202a506505034200d50046c0c40103808003510b815004400045241d00c0602c40341c442c81500d00b4030350305581c0d6a003640c0054101c008040c40300c0040140583d41441858010441280ca5031000701403980d65001030260814101500908000054407450081d103103080b582071026803241d124920342c504141c0321840d086080700c2601507445c00140d210311a42c1602c0c8125a220702414540d100e49411103125404004080c10703c9403254640005104203114403031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 622941726 1250 622940476 622940489
    0x90b01030c06020601080a17070c12241a040c0522080c2205060613030501020c01050a09020a0b0705011d0c15040b0d1104050301050702100c0804030c0213060b04 71
    0x100ca9090090207130074084160000c2040386d100003100310100c0d1003c82d80009926401d0743e00d65940c003090501310b0000915800440c40c1a0502d40c409003000300760482504008580c20249400d80382985803481940d282007081162644050100d150601c0c0030351002d0f5210390b850410500e85803414100c403005102c044c03200700440103d070004000c0164103009400c01c0160440b40c01000b0790200b101442c0312010391100d403820030394603030020b079071038603250100d030341e1200031010469035150780e8034105001c1d40c05810304480c01d50138007000c90001612809050401030340103040a0910781025040041500080416141c66403120941580122800084002e0b040203030043c0200c06074180c03e00003000a41200c182040808000412800c2e00d039006542c052101ca03140030600b0f8280764441c03151401b43e600710b070313a16500e0842804039240c0c001442d0020701c1d25010b81400f0b4104200000e1b904c04404981c040e0205180c15503640051400c03064039514100eaa000002e946038a1362843e0095411540009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 622942976 1250 622941726 622941743
    0x1b060d060815070219120f021e030408120f0306060307030f1b0e0306010f1403010603050102121b030603071503090f26040b1603051c02090a170a120201090b0103 71
    0x11100b0f660600141d061500751901d052400da016541d0701c65942c078208214001c00040c1080718004034828000a91000d040c0d0440d20711030003c00b40019180e034403911440209200740300f200060041020140c3d20a003114010240c219580d04051184550000305100109a034500001c03103102a244200251100071915145c41420054809001d01c88580d02491082d8811001006034640e0190400240d40175050003a44140194000c00d002d05916040144294008112038614070042c00c0b005200703088078200030404844556040070144001da40d01c6400d50007003607040c0b0409107801c10065205030b040c0340014108625803505001280400c03000c40304004121074400d580c40318a460a028011a11603003890a071a2500d441590f100b030820346414180c008002009040c001e030107031500203911501158140b007190b042d800007540b15103400d521810719450080390f4800d09210100808440d41c0c001c0036034110545030901c11600107021142199200c80d5904000303102c0351843c9000394410f03041e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 622944226 1250 622942976 622942981
    0x6070606121103011503240608060f01170a0b0c0c06240109050d0213060f0b091809031c02040f03050c13090507060c0c050603150a05031b060d060815 66
    0x164000d0440c41d81410b211360b0415106a4500e543e94444000700d980c003030f4009521058900111103c0480c90a1241106190810000703440001041951042c090303811241c51503030300c4820102041502240990309640015040c1c0000303210440d540340c01c40800400c441c1403244d010001882c240c8110740300510b100281406900c0196240c841c00541c401c2401c09a92060030440414020410490060b204030141407c4140d111560343c4a0000780c00c022048111964684e00442d2a0381d2207204614002c1c4001001401940c80a20565018012010241d80751284104c142c2918484185010050030303400c00002070260101a0030314000d6104001804501c2d001c4002c120054445d040181c1066082c030407584002000814000d0a8560500300f4280000c00c0381861080d41320710b03800c00364102500100f48240f1106030b481201c0166800c684602d85152100149919041141801c503c10900d040083d25245050405000003004211000402d0b075a00d0084030318000800c0d10702e4611920309020b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 622945476 1250 622944226 622944233
    0x100f03080a080f19020702041107030207080f011a0f1305011e0f0302060f0a0513030c0915050319050309030a03080405120a050306100e18090d03180f020607060612 72
    0x10943d501c1041d82003441c002d031400910240000f0002c0641216440d40040c1700350466035140d01c07454001c0300d182d00481c4c485a042c600603640e10050f00a002507071041100c10800024140149030383c011007000030500610a00090062410581d150305034414000d0800c00340c101098070a4a009188000c03242108a9502d0303418050000c4541040c0c1081000c3d4100340090703105d4108441455240106035a0382d6100000d048401d0b00a000a221914010300c0c000400d1001e034811020680784c030b644040096256000700041002c1041c4903054040d000610b9020094100c21716040705507005109807490a981c0c000000d050185022044002c55000014071060050400c8956a1150b91003440e41c908501c0754006401d5000c0240111300c102e41c40000e0494591040c00d0030f1071001000790248011440c0c00171a085081c03c201c1c0c01e81224810301c608040168031034020402c401c1c3c149400b0a0110a1070344030480c00790043c510070380e0000b1080100d00700140c0c0c80d1050a00034002c080318040000903625 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 622946726 1250 622945476 622945487
    0xf0f06050403270b090f011e030b0f09060a150908030c280f0b0a090506131506030b0103080a0207080d0914092401140d09110307030c0e100f03080a 65
    0x501c40784021240721028484c00000344210b4002140c00c840c0504042e042d800100c81c62a84070103079500022161059800d1240c00d0b4005002a12084034446251400d41d810701400e004122801070b40115103070010425424622041c2c0c0c202c1d0340320301c0d080080c076490314407003403840d44142503540b400d80c40808204c0d640203d920800201e030036000094203466015843d554000c461352080a00720800f101c01003540351440358003100a06900405480007807408240f04071086199050030b689540130300740c203a1070481075807180001360b0743e00c02d440e045580d0031901c1c0d5800740e800100c0c0d8102540716401020941040800c070003194600503982d8040c1e614100b0390000030688072250068062803101040c8200c1c1c1c440034694404c400d42110b968054403200b80700480e0300341201d4103010f244210004010001c40641e03080540e9090080d203210108048a1080c15650300c040c1c07201600e9142e40348800c2c0700655544018a4105c40c5141181c1e0f01c1a07100e0108902c442c000f40d01c12115420f00240d01c0e001c035034000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 622947976 1250 622946726 622946777
    0x2508310618050604030b0a020a0c02150a0e1207030b04020409170a030c020d210f021b0c03061b0c0a02100503160923040f0e0c2b0f0f06050403 63
    0x980300d450070030389590386d512550007025203031314441900859500c0945125250218403107400801c03080c01c400e000b200210305680103100040c0064884084030f800382c105581c07441100c00107075000744102032850f1105005560b02410407a441915000490b001c42e0440251000d64070003003a1650391a00014400780844078401d05000c2903421941414690076049648555411041b401244903925070b601460000c01c1d90900c00c0d0001c0348007140c91116510740f040d807400907600341002c1300c04510740007007010b035160000c940441031099049401c81d0340c1c110708000392030016148012107884440c0e5034000354035510740001480016030003104101210400c0c080701d0070302e1074003401c0000b0550b0400701508045814110f4800c0c4005031501601c025443d1940030160082c02c1c024200680304054103001e46981e07103048194400d2031070248c0400b052811808001800600b00c109207141c00369a525402c0380c40c06100d00342e0302e001a141084020605d1800384034031983c465500c01c5620764040c80e035000c404020303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 622949226 1250 622947976 622947979
    0x1519030b13051e06060d06080c03010e030c0a0f14070306090201080109140f0c0c010f0207030809160504090201030e030a030c0807020f0703171e250831061805 70
    0x701030a000c00301840c40c0e1008903101148844440e19624040420178611810b02070300741c80da00d0040d00041000000c910308030186000c038024041e024441009903624018124a03188a80008403000300007180340c4801c24580d882905c4115a032104401c4d0142481e44550007503800030748030103031070341150b0380000a540036201c401410020400109803003903100d00000c000c0a001d03100744010400e40d10601381038841242109000740030300c00c1119441e2010f9005030000b100800e80000c04120b5425010400307900d003103c0056048240e600c5c0204000c060162041d042c0e0500d030356103803505010503091000309186219034a011943c031110300c80041103c440240500d0854104c5250101c8400700810700c0c0040700d0300050003002c0381c8100c03040300c02280b00f03400d0721070300941543d8000002d0340c82100280040f5102c0b1145902c002181640124000d80070440080442d007003000746038035444d02981660615070820800304031480c600b8100c00d815030030a41000740811000c16101d01040c0400030350300f010303000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 622950476 1250 622949226 622949231
    0x30c060206061305070c0210110a0312140601120207060f020a180e0c0d0e01150f180501120209100902161103030a022d060f071d0303091519030b13 65
    0x1865074008110300c81e0500024411a0900d501c108560709c110303d01445600740c3c03010f4034104440e40c1b801418144015646021246c00c1510445080c9801c9030050321550068440c02659848111494002d500170b0304103c421310307a6000800c00310801c92002c0c00c1501c829480d42c0c0d00402c03148000040c04012a0b1240d40100c03a1601004071100900302640e148444030b40000c03a5110303a8580450140c4440010301c0c0c02c10141d044006500d5180408141c200e584419102d0400c40745810444180c441c240100d1508410000c40700006050120059034400c007241036540b10280c8820404040c1e9211410200480c61b45043d007034103202d080954180d010508400451411480c80700c040c0d11007515030641c02107021050f031020411810150205c441d44c00d56416280586400034600e4654101070342e0030030029840d07100c808d240c030040e000308404020000b0b0040d070034141c1c90f400300085440243d25a00311124280400103040030980485002001c0c41e48001c01c1c4105080b083c0048043d45c0030309609000d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 622951726 1250 622950476 622950481
    0x161502031519090f09051002030f0907080a030f050d05010f05011215031b1505070627060209041508072d180b030d0c0b07050a0512040507030c060206061305 69
    0x2460054000712030300f031000402d0308602401c458008007403900003c0d0043c002c44040e551010034039801140700d414904039136140c42d200e02c0c06190343d440341c0e8000c0043ea58020006000402c0c00b58910401c080030a00d41107240c80c030540c2918068440a03404414010581c4000340410368200400d06840400520200400101c100b8100051801480040e22008030b40d00d510003002d2007078020b10042c040b108150120603410590051640e8410320040c4d07911807034040104107424a80012818540108100d5040e110309511000001d6201f43c03a503592180c0c2c2c1301000b912121340240400010702c0b450000e00800b0f450a52084428880040c280ca01604400420020500800c2c80308042d1800b443d40c1020134607464016a0040100b100041c1d803510a0149141c4410350105505401c075101c0c0d000c0c29420384801a054809003c2c4042d140003152090000c04c80300d001000308a94018010011600e11503640c5d243e0040c1075000703400100068001000300055810001599401c00ba4142d008011a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 622952976 1250 622951726 622951759
    0x20a0804020d020d0b0f09060106260916170d0915080c090a0e04020111030c0c040b0a03080708130605040f030201030f0b06130302090c03010510051615020315 70
    0x1048000c000a1103456481c0c104425512503180d0120103d0384903104480f941813046806004070811901581944181c5001050603485140303034904000540c02420b804100107043c01811000040c02040e491113002c1d080940202c141c03161100400542083e12003c403e002030983c1008408030041c0d0a02c00c030a0310401c134440d025603c003840b8800c00e29101035180c0300d01d01c25108900c01d052100c3e6104686850205541007039508981c00381c0d100362141c0b491402244905905ca01465000b4001504038010401040c101074004103a00352004101e003a881c2d4403a50340005641150b00242c0d004000403034100141e40c1c01040d440c005d0070341d50902e24285440d110334140280081c1c00020304060700e1728204200350046400c038000c15a0000e100f2512040c480d9604401d1a1135848244d02c161030720008030390381c0c4a6200031a410781c2c0c400703080e14040350981e4200355410340c8800c89080e0b00c0c12902d01294081003000d0b075120402c55445001594a041c00000c5d00156800340c034445208030291000c49110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 622954226 1250 622952976 622952987
    0xd0f05040c030f150c09060f0801030c1221050c07080a0b0a0c050c3405131e0212190e0d0f0e0910170f03160c031a1801020a 55
    0x880e684580103403503442c042d1070250340c1580c84c40840701345076050061901c0c0c5d880c0c01041790402e840c201d6440701101d20b030100080b42e641e0000e201c05008021900014001740100141c5a003e0501842e11030030003004000341140304030710045191001513000b21301501d910200303101c4800101591001020f00300c00710b80701c1a400d810301910b4008155581c94418400ea0700820a482c80210010144d441642100244035209980404450400c80860340541c8000c095259600141d03140034003001c7c1c18503a150a820010074108111499030700c074189214104100324001040660648149542c080c10302401c0d01c00804514000704508074103091420101010004444007105840e2402020781ca52140d002d68090b080b0003844ca81200910342000300c403d80e9a494030044421884400562480f2100c4e090388401000242000302d81003017103401c015441c8022822691405103442030740701e6640380e895a0300703c0b02c803440c45600c0c6041101007080383c3c09643c05560f84410710344000e40c60b000441000810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 622955476 1250 622954226 622954229
    0x5060708070215222a0b180a0b0f04030c090c0203120709050301060f080d1806030203060a050d2a080a030809010905160f080d05040501051e030c0d0f05040c 69
    0x40b280f00e4200058004814548401c203003c4070090380e1241e241ca1802c0c110000c810042c524101482005496480045804455011541d0000604c1e09201480911003e00a0914240e80d03006210500c0441c3d0f2214200c0244840603030009469607031440c40c07501281440860303121040191030b00d4044058190084211281c038061940a4051170b583e0300f0701526040e80d0790b0000783d010740c42d00001080300c0b00c60740c00b824103450300030b070440700760001c840382c00c85096041c209605e050a440a008008442c0660061600032400420b1136a4054464010452501d250002620740d450780e00300710b031946988001e09a40240d14525543c01d400d00700341d5066a5110080c00080403c5406000199032a4082d80b189005990200c02e4900c07108610500b148901500c4c0100c58507c4035a45000805603000100300b015580d454840b80e003410310344401558a6003240e011980a08102076a104050742050001c0d0b2150418440313294981d045030072010308443d616210800c8203031810080c00040703406546e80a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 622956726 1250 622955476 622955503
    0x140906070201210e070506030606070311210306090f0402091306090c060c020102060c0a1b06141006090902030906010b0a27030303111e0a11070e0103050607080702 72
    0x1555a580340c8012602e4001d0342c40b0b0903d08801041020369a00d45980103034050680307843c121030b0f0340ca0703d4104100c00707032105540690b440401080174800281c00b0b0030048a490000806030380e01d000d00390410380080d08118004020901c1c0c0041080950b141554a450700420080c886c00c2c0c2e0362803c0c0d4007007414907101030043c1c080c01c048003240d1810883c41b038000548050b0b00c00c0f1071150555440d0340103040d5240c180c1c03049000d400340d03000090380303c81c00009460000205954180003403111501c0000302a08042050f510540c03142403c03808108034584440c043c000e000c80d1200550725044005000130480d400c6510420300404c2800881d200019415056a90700d02a00f503469164200540b052481020b210341000100507500e5001c00c0940c4030031044901980b42440008440b96440c0d8061140f0625883e900c02c104001079100c0940c000500700140c4142032030544d10712180d009038541076059100c4071403a000300c001071003000801e1220b181c0240e01414003a10f01c0c14402c00c0651502c08480040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 622957976 1250 622956726 622956739
    0x121803060b0303070f06060504140403170c0f180102010c050406080103110a0e0a020c0115211401061410020c090c07230604031d24040b0309070f061409 67
    0x801c07840c0e07000d0086540660340b09400342040314483c9440e202410b03641c405d0706e1060f071402e2070300c05005401c000c02c9442190f00d46e56400750b080010b0421444104090709019041c0303014002e11750b44281e0003005100550a18030340070030261520000a00b940c4003005180104401440108030640e0030108403410f40390b004015101c9108810082035a020320380e444280b10000140510110183c00c0c0d000b02051f9101c0c10091001c3c15680c44d0001d400d50040c41600e000ca20340b1001202d10340030100c0e40040f11403080346030310300c0856000f100c075080d240203821400c41c480161a21824624003420044500040d0380007400c0c046000200198031408002c00314160a0fa00280e50402c0100806105402c111121020b5070402c0d503640001e65511002c40c0c088020400c0000100c9868003a61408550440c00800d801e040150001c1c124003000c415010f40a00e5083c00d00c0301040c14221030002c0e612854400d0002e0244501d0406c1c619904926a070203070302170142c03a4882d0300b80c210058044481301c0c4400d4403072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 622959226 1250 622957976 622957991
    0x61a07080309030f0f0c1203040f020f030c031606020f010c090b0a030f0c120509070b0d020c0c0d030e13060602060601030209030c1008090d030b09070f260412180306 73
    0x6003548200c4c28001080c400025049025084902c080c3c1a400d0021003114600720003500ea40b01c8510050303401506560364403904a006141500d03804c1c2d5521006015604007903e14004280f8001d40303101c0c01800b14912440500940e541008000c4c0042c1d400b400034041c0340711200d0003130804040350060020304440011200030180c0250805142c3c000306000401600d0003114000344581511100b0070303882801d020200b144108005802c6003600c038844811450100070001860003980030b98140940c5001d1000c400d600c0ea80e6107080c00c11801e001e61100d006c036030440707020070140842904410520901c2c10b9010301c21107074001100f5500960a00700141e5510581002901c1c1180940300d40364091000b000c5004519801040316000301d40000c101c803121411403005905039411000c40a400c80002400902c01c640700c0d052a40030784c151030400350001c00340c250070b8402440c2e00c0030310009007101100a010030081019a5206141030701d1078079080e802010fa400d58890310880c0f00180c00561140c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 622960476 1250 622959226 622959241
    0x90203030f03040b0609070201091104022b0603051504050a2415090e01060302032d0601150e0f09070c08040b0a031406030c0904060507090e070e04061a070803 70
    0x4440341c00c020310303801c991246481e140c0140e6a0301c003100c4560003401c2c01c00101e501640140241c0c7c090365072002c044502c040c140010312000790045101c074844449800300040c941626030200b00c10748200d07600045070190450401c0c6203000a45001110407244440800c0003045000c9151030306141d001920791034942400c90f1a0444c0c2c540c02038000a030380d15000216605008415088044900540e8144402e545903101982281c00c140f1010b90543c0240440c0000d848140d4980900d00c00840952150a00540071451500740700760410701103ca41242ca18013196042580c0c0718840404030b031003045070b482820205001440182055091094501c039407010014001c0070785026203408860315440c0c01e000d010090180c110800d111061603001d00101e6481d00340825041c0c1d440c1c1005d001a915a1510354400300240401070a41c810041291404520140d40da100d8030300034003059403006402000a0100070488a41d40d10016904401030851140050320300140d605030381d0040940341d165501d800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 622961726 1250 622960476 622960483
    0x106050903061929240a030e03040e041a150a1202030708062a0307020a080706200304061a0916030b03071502070b04050303040e04030210060329040f0303090203 71
    0x3006004510811300082d007040c07090211040c5007401120303050000413000c0049400040d002070a9601e144040107a0720a0b00d000c2e1b04809090030100088900c0e050b900d8050f11544041941c0031200380c060f2040280c01b6800c5905070f81d03000260700d855003031400d10180c0002e03c1188180b041391001d228000750030007955005e2024400074042c80d015280c072441c0035049046c0c040303118200a2108402e80b0009031002000900303a0744a4207480c0c000308400b000d181c0301e0000e1600003c5041300d07803940b2080003018030b1200100d2040301610310303a061912424503242071429a0a90b82418001d414019180324140c0c1e44c8654040d00f00c03400a01d0310f60b58035011a0200e001d00340ca00d186a8061280da0400100070b101c002100b000605140d0955041c40c7e15003041c41410701c80c6108865040d481444140b06070034070504910781042c0f081c01181d03007142849184d0001d940859005031684005200d8803540303076403508403203a542106901142c00601d015519058906035041010301055170302c801e1441107440c02c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 622962976 1250 622961726 622961741
    0xe0c010305131a0601031401050a0b0702060f131508060f012712050c190501031a120f070501180b0f04211703010e0a0b0a050a08010b0901060509030619 67
    0x12100b1a028a04802c0103d0001c1e010784400340040d151068441d40045607404890580d5030043c481641d0a1a086100f00c19400030703a0b041e40d001004100660721101940e00070302d100c00d008500f182c109441c0c0001d58049582c6070480d00c040c010300608101199890920011400009003003000303940d0043c0d080341c4202101c81070413421098000c0d202180b03480c51045000000740c0b1590032100040800e13001d00c1890390f201040c15411030400d01044c441980a60004103c0726500850b0701c4501006c1d030005159001030f004241150b8010a80d00c071520304046c045c0c2c3d0080c12082c200402c42d002c8044551410304601d1046400b51000803a01c8500340ca100300483e0000c01880d284102041c1c004845030142c2002602c0440d490814600424030554881c2c094034100c80300700528154994aa00c031503000390003102401680580300703010126042d6146c07d5110050b0007c0000080c1a030080b106102100f80180c2080341800414000c08807107980000b803559000c150b2a403444100c5030904095000392001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 622964226 1250 622962976 622962983
    0x3030807092c0c0417031803030a020303240406150f020606010c060207050321010e01080c1e030a050d050a030b0405150d0804050a090c23190203040803070501050610030e0c01030513 80
    0x815920080700000001d8011485100e248070205111f0f101050b50720310845982c0009a0018000104908041d00e2892020301034202c003a500341d4102e000260131240c454221301e0782682c000001101c0d8507403140c08922350024500007880f40b418107400290182c0800440205281d0300003616108200040c400d513088102c84800c0f000314103d02c15400c2184040c00d0081c0d0851400b079030000945101d0004a0011454000c1c0140d14007003480300482d00c0308107902094942501c921009000010b501304943c1900c4020f9698507610781202c00c000070b09407800307030703400c03d1213141440284040424000b072030555428048030904105c110754074014070280a00c0d402160302c61001000010b049401d504004201d41041d40c8641401105401c0a502c02c207403c2c80ad0b228a10042c0001c01400210300055004041140102d0303040c00d0f038509001d0325550151200b120140d4403241400406d0614201026a406050405001102030310f0402c50703444e50010000c6040540712008105101e51540f04040d00640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 622965476 1250 622964226 622964249
    0x60206150604031406090f0d08073506030d030e030301121e1b060305040b010e06041404260f190c050a0605040b0c0f1c140103030807092c0c04 63
    0x18205135501c0340812140d4051901844507000c080d440c02040c55081340c0002d03100c141e81c80d101c600c030882d00c680b4820391011903000703090030000101c245640c59034008461005103855900d8100700741820040c1645909041c50304008035800c03240c00100c1909c2c15919900d1002542e03610b10f06184460b0858284035204039008025001e0900c6003420b80040b20000301071009280720b82d164001c42c111b903011203024007824400070042c01541004401150480002800030400e2041000b20304490041030703c0031200c02c110070f01b10710800d0040003622805a01d5161800b07003004c8085141441c03034031070562003c0580c0c0c984100c503a040c41c0114103203100543c00204850a03803d180c41c02500a20303081d101a01c1070501c0000090402061004031004400c0c51124242001c1115914003a451543d1b058060015190344402440211002c82d060081d4001c9e43c1e030b084503091807040540818185d42190204421403482d09041d10990301611641723808001d048110f0796582554008036000d00e410000d540300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 622966726 1250 622965476 622965503
    0x7060504150e100f020d0806091302030715050d0c02060c07060e1c020f06060906013905030d0506040209061603020a151a040e1c0e040f0501060201051006020615060403 74
    0x10f500c070030126000b860745c2d0225042100c07030b140291049903084501c1640720001c0b4000650100306101c103600d844d48054120343c0380c2c94a40402030144540038a09000250001c0b61003424100315001c3d25102c95020700240c6914104403446806c14484c2035406011316482d04000326690008100d19406080481070402e03076030040c0a0001c1d1900382c0390207042428030400b004200c03686812001d840c001e20b016141c4040108842c8501c14000f0312039043c408d0124400400c1c121003e040ca083c1108030391050010350360715680401413904540380500854080d501c1072103240000c0e11000215044008403c1466075910b60301d00c0d00700c0c50142102c10041c41d8050f9103140c01d80c01043d50300b0a01200032f10041e4100b8420001090100f00c443c00600b4020a80c0300b089040503c401c042158400018989482d00c02c600342c01000c81e0642e1a1036110a10080d940ca0040017540c0d030a10545411050441e811400d1503e8404c00a543d844040c0403c10340ba0304407041c80300036a407400200d038001d5500089040886 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 622967976 1250 622966726 622966759
    0x20612151e120111030a11040b070c1502010b0d0b060301091b0f06020c06030705131d01092a0e03010b0d110f0102120d181b05011107060504150e 64
    0x407041c900c4070501803042146090360010707041c003070106090240d4002d02d05540e922002d41c4c000c1c0c000f150190b404007804120118010744020300034000180203008040310780745818481c5031070301c82c2000c0290847e490110428002da451440c040d4469400511041003071b116003001074014841c024004140c40b0500d0440c00d442e0703408040702c0381190003003080f2140e031503510304060742c0f10000d4200c60313a446401040042c0030b00d40280c000d01240007140240b03180aa88698030100e6804500358a1101c1c0c00200300100f01044250080120800c81802c409000460480103a040b041000c0c1e020760902402501da40142c2d1401d500001303e40400034502403480350319040c0300504038004000c00e0b00900c0da00c0078a10595000040c95081c03098035407845032401004201c01c500510b60f50aa8000b0300c20711036858004190314103800c00c000045500503a0105162034009000a540300018003c9600460403c1299503001810b44045400d0b000d400d510340309049004031a000500c2c00543c0c0d10038a45080c01495 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 622969226 1250 622967976 622968019
    0x2180d030c0b0703021c091a0a060e01090207030509330c0d0e010206181f05060916120f020702040501080706021005040b07050c2e14010302061215 65
    0x485009004900b619240c03c001101a032189180e0740d60780e20301240c035400d04425140c0c0000110703405507001000038810410400b580d44e205540248845031034141c1880034490028484d401040136580c1140fa10b4895074000d4411300820f40c0c580e11409492401c46540188404480d1036002c3c018044510321850300e070185500d400c0851030009900c103160b01810614001c0510425070b10050b002403080b60754400c5420080d020004292032140030f207560040141c000410b402c421002c0d5007001281a01e09001400505440113020244180151012401030754100c0c0621180804440e004103c00c901c503207184010340f290800082d0024a420000200c2d0000480e000d410742c1d0250382560846140e156041040d100143c41c0940400481d03004948011f01075002001c6407035804064400c084103840e084060542091203410b15240d0101c04c103100d2010510030b1649851402c56911b030b003941960049080c07401011000c20610003001c000c546410702d0504040300d03003240202240d121400c00c00c0310b00e60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 622970476 1250 622969226 622969247
    0x60e010b130f0506040b0c010902060706060302010f0c0210030b030a1a01060909051905090f0f0123160c05120403030309020f06430f0b0f091002180d03 67
    0x30070000d1500e000c50002c0d4449200421194020031081c101030800121100070744c440300d02c3d5003180d9030343c04883e80180c86850103080418082c0200041c0b0600d076000141403031121807d00c0c801c0040544100c001a516075803055042040c0303250020311038420b4004246010203c230006405140781e2280804454506010181039440303558461600c603540c0c2c0081d00a440050b02c0d841d040e15040503000f008561a40e100c0703580940408201d5000303400d80001d840c00c00480d040701902903515850040156290340f0b0061404c41c4c0280714403042842d190381d081f00141402c0b1200001c02640384a007070103100c4100510403a0310503409056030b440d035a03440c01a00602a003481280075641198040c5118074081e01a14000f200d128810112541d80b003600700e0b0100804035002e6200940b0742d56411070790320b030108911003d83c444c0c403403401460481c1c24001085d1743e004140b2400410000100900040040362450031346000030000f60b02d407403080d6642038002030040d42884c0c21100510045082c10340c403291114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 622971726 1250 622970476 622970497
    0x18060c18090c031b0c1020270d0519050309090c0c010606170f0403110102161407080a1509060e0a1101020c0333040308180a020d020d0303060e010b 65
    0x20000c039107201c2d81194015001c0564086d040101664503d8446401c030051201c0c0032200f800c1c020f818012104120b8000303290007044010740f07903500071041144c4041e401e001c2c1d07002c4940e85455015507507225a50290200c1043c4080903419042040000403c144e070184000201100054501018031451581240440c00403641c200140080d2a501801440021203d08400c2080d02d60fa119204103070b01c50044e00032401c015000b94140b074542c00c21b04c060030b9854070101c0d1004003442241802ca400008a8903101290f4200c002e04200803079000400d00b621a5004848541040f4803103103940040282c80009080b032400d0102220306044041104920244900010340c610401e0000482ea1913020580c0160542e0008044404030903503200d8000511252070208007080a101d407440240080940d0103e0226180300140440c0e403010b000d02c070a02d09180c00080070045d00540009a0000600c44041e000d000c0b40c0045209240c800d40041c0098074040401e2000c84d6594034061420754060540d11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 622972976 1250 622971726 622971751
    0x2709020433060f17060d0c080a02010305101413020d060303270308030c1308030a090f12030207050d1a04110a06081302040c020a120305060918060c18090c03 69
    0x124481c0d0203400358103d072888a41c3c944480d644005481800000c001d0001c650080c01015024002851a0010000350050307101801040c0d6140c40058151030010345202030603042d15509001a10246200003962841218143e407401429942c3d50001e00c00e508001d1903450074601c0120a0581199140d0302100384031031903402c0d010040b501c911144a080c040181441c6080000c105400b5880c009400700d4180d428244441569a5891a10707652180c4520404a103400c1e104026099103489150300400c0d20000028100c000380d600251150b079103004d12481011803c00705d005000c1e031001000e9000000b0304182180741490f080c00b100b00900c01941c180b080306084008034a50303108540d01c83c00750100136884c086030103441d800c000c0580000d102650842c4660520721001c5604440c07100300d41f080b06c3c2c80c000b49500f402c00a20002030402031104460540900d6548140400010f0481e44090340d00c0c000381c0c5640300c01a0f043d80c024400d085855018803290248003414581d50000c600814041c402c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 622974226 1250 622972976 622972979
    0x103030f03090506060f060c060103051b01090815070c0516080d030b09011412060a15050105070f06110f07050f0114060a030305180402041e2709020433 67
    0x300c050b1402c0300402031642e04940003183e218140302c031040381800c1009003803070300f005540d458503840d00da000d0380182d8040d40134007070b80b8a840e20a4003d00c1001721003031800380c2c025400d0100a50340c1d44401d41c02070491405000004820520440450841e6940102503800c81d404168040f4841c40d601c2c003868140d8050407500c03401840c0240f01e092101c0c44040c04400142c2c1ca4000301d6001e815410000903088080c007032050310842803d1140034404c500c41e80f800102a90301510030031030b2525642000c1d050082c20400c25000c52108115108186d900a00200b6030074006881280ea030b0086100300d200c40740d004218807040000200740440300b00340d107c008001d0003000d24002c0040d1001901c215030406040207040c004607114000400504201c080040482c0340d81c180800d04aa00551001090f03c1c01c0726011020f01c10182d8040006120030f00d50740c0c0840d10300c1c3c00000c0300c90841d451a00501c40d86c1e010140115110758020321820001e0035481900380e640160401c980300c0244000141a5640c040c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 622975476 1250 622974226 622974257
    0x8070801060813080d0b090f10081b06070212062404110406050c030c07060903020108160e1905030a0b01030c1d04060f2c010f3614010203010303 64
    0x5520f03c2541060003281242c0040d84032002c907a400a00509580e507264a417400716501c03040307451409280c1c5801d407550b05140401d82001c40f9207464001c20920b4100d04660003649038800d04c0007600920468032903176254654800a0100315103502c0071016070180308100410800d038440b441001102511381600c500d03114a0400044802c80800c005803014240001c0c80030300d124a01402d454440325045a00d443c0c0b01d40e52803032800c2e19950003140000c01c2d684080c000c40d41d01142d201d0304544d10070a445110b00015101400c140320040e83c080c014210789551f0140441201402c10003841d018068402c03940840c1004415410b0902050740c2d0544820000503001c1141004001000e1155042ca071150315982e030381030060150303185400c0c7d15070b40720429003e01c841c5030884111234801c1401c8507100300903903c50003801d5a041c641407002d0203190868140100c0c02030315500c0842001c0d8a1914190a441c440300d408442c086000a0000e00c4002c5505205420550056068074001e4407019042c00c3c0c406d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 622976726 1250 622975476 622975487
    0x90a060f05040212070507151404020126040b09071d01050316060c02011d0424090b330f070b0a05011d040302010612080702090c0c0a03050c0a0804060807080106 71
    0xb0b00007004004d080000350707401d2050014050842c42082102035285010040c401900c41c0d40b0b524201c0051000140811583c00c003481a41c500707502042c0c0f000f1091580c5a9108140c401003004e001c4440c400b00040c0010002d2004002504c10241d170301c3d1441c10f080500050b4140c090154502a10405110a440340c46190400044641980d103015444145e9030046829100703048203c1403003140a0302130102580c03903008080413600c0c0050b254401c841d001e02c002c0302c28800c550010000b0707850701154000681755692181a031010744030b50003100c0d490144034501d4114003041a08800040801c245c415038070b14100074582d950051280c61519200e0010b400200c40082c49060b80b040190800c8a094805c1000241d5100e03009000000301c4a0382c604001c5041425240708654410001401408600e428408180c00c0781600c0007250910760302d41d04180c0d5400e03403840d01605029001c95580c070101401c104c00c80c5031030750081070180c81d1640c038080509920000c2e50303d03a0100b01240c00226400f4800c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 622977976 1250 622976726 622976737
    0x2c070e01090603240b040e210c0d0804050a0f2306070909091416050a120203030f0711031c020c0f01021f02120c0c070e090624090a060f050402 63
    0xc3c3c8146070300c44040c1203c03020f40c8904120310702c05c0e00c4682d02041655144592811050380e203025000c44504e15199860071209070070f0440d4091320034040c003010000002080c45602c1001d04010845840310b0410303602e001d0250b04020440003226202d4820000ca21032030300c0048078114558102408a50f43e03094403442e0884030300c2d0004880080400240000d078000c442498080ea80c281c2410000c0780c0e0450800f95048018410b500640070304002c9428803481060041c45103009480038080b841d40069241d20a110007a00b10030b50204000f805d10011003908580f03a00010100c56140b16020b80300e146001d501500c09000d4007c000745c45407107040c0b040401000c084168003400c1c010445803004400c100030040b4035200310f89c2c01e1001045000403013071018011184800859124451202118504106a0010039900085d13809020182a00007025600400c200507a00c2c0440304820040c41401820318100d5030010a5500340603140d159540a00107440c0f40000403a041a2a1010300c000c1c0d1040d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 622979226 1250 622977976 622977983
    0xb0a09180510180209180709020c12030603030703051308100c2a02040507050412080717071e0311150601030b010905031507020c060f0a0f090302030c042c070e01090603 74
    0x2050036100501d0035180c065400721161b24008504801c151200c1d01d44401e9030080740d0000e80c001814214000700300001d507440200848070700d103135140001c0429207038000c50708014140940410001903172810402c01c84085c10b5424212607440c880680b0440103081c0c0180000003180c07201c4c030032407090f0f580d840103c2070076500c01d0190141d954007036003440018200280301e04200001400045031031400d1181003075006020b00c0750a40c03a2689420300c034091407118105035a221a00b000341900103044810708a509040403444540d5800b82414251424800b4001d030401d0380c01500c0503600c0c0580100c00540c0920420380e4200002c82980c4019211b500e618060658164003200804001d05410550709a00c8007143c41610004581d034004507009400078022201729200108009020961200c1c4000c07807a0503901e448270320189542c02007a1907a034514680d5000700c0d2901c42100150811400700da540d100b544642e0341440c01f95003840b541700c0500b0301070486450442070001440490034040c0405803900f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 622980476 1250 622979226 622979261
    0x903020c270c250218042909070807150e060403060c0507050705010203040b0706050928060f020711011d0a0f0303110309062b062409060e040b0a09180510 68
    0x203035117801d502d2036480100f048450b05c00750509440348201812420020042d0303003056103441d042421015003005119045241281d10010040188400403a42da00c02120341c1d0514808006848000c92428451500041e0000b070804072040c03182ea90000081103402e000764141d91b6020307100c400480e12032003188644108e400081c40603a0216a50380e02c801d400000100403644004040400e03000e0003481c4041449841c84141c10308030a0100038051603021701c40881c021840d003001540c03041104684800342c80d040040c441c0c001081e005100d00151b0403e00010010390540c0c0c1c0d00c0003114030802c010300040b40012201c003040ca020031030000540d0441000107040c80d040101c0c140f11558003aa4400c0d10380303d032140804000740d40d0781c4948031300d5014ac403400719040200c12010046803480c5610760301c560f0401070b00d004100701c02c9078048560140d0980840c2d01156098005002401442130303900140000340c03800201c3c10800700c2c40c00c04100c0311445103094a0b90004080401c00842d001d5074090004600c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 622981726 1250 622980476 622980499
    0x90d050903030405040c0c0c1a070b1e0901020409060b0f041406040b0703050414010503070f0807051b0c040612050a030c1a0a05010e09010903020c270c2502 69
    0x500800140c09000d0014040300d04180d030b40d1000400351441134840b000458200c0c0756010a001440c841c00010f8101c0782178448092804550f058601d00c100103025101111403008244507207444084074102400c459050000750518190307044c003d6105100352403040380b62940000b00710300400155a0744420001d140d5081c1131400010003810000410401c1d84004104808605030440a01901c81c1038080d03520b47da103880c00c050201c140d0541c034001032414040140300300449581c0c0030b4602169030100d4030340200c1b20388500c0d1040c1c0b039074010030076020380004d82000d694400320700000d1f05200e1030604035424422642d6400440103a58102100a0220b800c1040044046030141c0701803401130748135021400c034410380b849042120301000d03540030400c252554010495010a1200d00c1c1d0040d0b0803034000c0004800a40d8041c1d80e582241d82910b00a8048a502000151040801000440491408500c01c0c42e000c4900c104175400003080602c0c0c08549405403074081004650300100c00c2d4003600111444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 622982976 1250 622981726 622981753
    0x17010f0b0415090806010905041209052107050604090f05071407030507031701080a06110c030409051003060c050c0d0c0201080c16050708030705010f141f08011a01030e0609 76
    0x1c41d003032109000b0f0110000002a181d41c04014060090030b44000024882c00d280ca0000081e0140704078406c00c01c43c1800040c040356503018400c100d014043e041190101405001d241e06005140c2d0280e64440400b16000a0401c03407504250000881d807402007100f580d49010548106c56030304411184c00d5002c0c80b0010010b4020700003401c2280c001c0c1040c1130f003204404c807240c1604000340c100101940140c07480d001084a640a0406483e40c4907200c1da00b4040003041c00381d44ca025510941e000e55480d030010448401714051040301841e008a814002c140e05044042e1440d48048170300211403207150300340071030140303e111004900f980c140d6440906884a5101030101e400400b0a007204070304a03a81c801c0064000c01514004010940c00345851313081c5130402a0849050386210020303030f03062859504540341541c9110b40e0041841e000c41580c2c4000c910740c0414156684c2201340710350b18140c0302e00000b00c410380346566902c0b004d0381c0078000e180045000c144c49840554840c62035611130384005055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 622984226 1250 622982976 622982999
    0x50a0b1c0b03010504080c0c0102070e1b1e0a1b08040303030e011d060a0f0501120f150f091e05060a0f0f020315190605040515040e0717010f0b04 64
    0x10609014004901c40180000207401c550b0b050b10211184c01e00040d040c660a030313040c0000c91404c2c409001405100740b4180c00c03000001e10080440c00140310842e1108022400001640c09014440440c00d0001c110b0300c030740100c198400501c450114070315000044480341c8074a000d14059900c018030381e04062540c2d405a0241006440300c0e04a552188540c801c0e030180b0040e103010309138031100145034508041349048102c60451106024190500005201c0d180710381801219150f0b2245813000c01100601f85240c08104241c0341c90a030b030b410155086010800c0c0c0e004294078074005c1c414001c0c05c503124405070361107402c000b000030844c0d0422000105204103c1c0d0002d40100d08400d0085822138400f1105412a4002c0714001030850381100d500c03905041029841809070324207003041041505110028259004130f1081c2c1d031288400d2102a2098803000b8140c0c2e00905481440c070314281003644014001c460051041d0700061802c0c400003400d4610010f6032800c85815421035441c00c1e0410802002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 622985476 1250 622984226 622984267
    0x12040e160c0b07200607080603031318020915070302010c110a060903090b0a0503011e031e0204020904020c0f010b04152d080604060b030607050a050d0e010f0e07050a0b 74
    0x44c00740c0c104624140321100700d407013000c030403000f40500403c0c90013901c0a0902c440203044c40f8040e500900501841c80c80d100e800c8800e45208040161080303c034012032202a1084902460300a2100e560f40c0303071507040c0880a001e03103030321a400034403600f00421021103412000685080c0c041d402109168046105507001050690180c0303003031130080c1c1c3c90f95803142c02c5030301032040400002c400000420450180341c1c070000e2804410300c42d41281c185035803030300000740300741030000a045101041c800e011581c4550494042800c083e00c25903c51090310510768451660890304a015401d140c0140103504e401d11170200800303900d0b8031900c01d80707003860548c0c01d0142c1d562601d1030aa513440101f00702e0071080002d84000070000e10300240f48030703e032a150280564101242d858025880301c018480c000c0d40100a030341c02c800307082c03a0550b1140c1d18111480058030305804015480c1d440c00c44107420030020354010403402401a0b08440e60142d490701448030000151050341856003050050040d041141000d554 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 622986726 1250 622985476 622985491
    0x70305010b040b091617100e0f0c070803071107060306031208010803030106030c03090f240207080913090b040302100605090603211b0d090602010b0121090512040e160c0b 75
    0x1b600c007030f10340071b4110001c90680d200c484903400b4060401803020812070031940400224200328140c20555104400341c05400d02c0100728036000300002c2c00d800c3c0300b805020200003080c4200c440c00c03036507244003a00902e8103000940742c00c00d041200d1104180101c210038102e89400000314950380c03030031800324000e00b0072164040815071510a2a808a02da10300c410340c401d4002c8800e0040c03115200b00640b0040d0308420a4443c1038014865500407a03900c01c140e520002c1c060b910381c1400c0200082c24001800c3c07c8400a050500d0700d4180018581c1c001048650001c00840c2041401d84403401c008610314121515641507111031015010380c10011400420140256192814101c2c2591014620b016458081900d80e001c4500c21003c5984803003c140106402c0c002000560420000242036200105404001c005001d100c00140091030b0f119098003a000001e0350b0200c80c085034a542d40c0ea2203445081440007a9201284201c0003003004283c1c058043e44135681514400d64415504910082402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 622987976 1250 622986726 622986737
    0xa020a0b0c16060f0507081005010f05040b0a030f0b120a080a0507050601090c1b2604090606030b0f01020304150c021306060c060f0b010203071b09020705070305010b040b0916 77
    0x10b40d4980b0300111901d404510599002c201e804601d0208011224000e020074100103101040c40340011060394181d090301c4080c40c0c03883d03115150004c19100d03889241c1c0112301d101c0b000100c041c0ea0580c0b50b4482c00c0b0048250a050041d410b40000300802c10000310310f803400a4101c0643c00d0000751100004102c150941d051850400b00b180d1503107800e11109901804111f5250320105040c550300c100710391a0700250510403801d009643d00d990071440c1c8450101c1001314801c848003600e51040d02c050340c00600581d6805d0194a48806008018103003030080079002301e100f91611081b03580040107640540e42d004152613030519465104a035510328400c0e05036045140301c0c2c01502c001000340903990240140d5100c0400c02092031500400711101e000c660716800c1c0c64485689840d070f030b01000301c0300d031560003681e46102c0d400d00b15001070181010f60320500440d403002400c042088070104068048034040c200800260004c20280700a58001801c05070707200c0561800100f1101120154100d40c14052614 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 622989226 1250 622987976 622987987
    0x720010905312406080f16050d0b03031603080108060f070c08040306020f22180b0a080105070806010f03050f04021e04090c140105120a0209180106030c080a020a020a0b0c 75
    0x142c0014586030078031151002c241d5107060001c1e94102c41c001c0d802c0f40c0e0000c0c1030001840c020380c41000c1f001034081c1800c10440c0000d003503524119140c001801e030802c000d00f074940c1d50f403207407024803440c07043d8107012000305021000000301d0300404a041441502035403010703005640d640c1c00c2100c1001101d103003215909000d02003c00072801c5840a4148201362440850f40c1d50040b100e440861340e15140c2210742d42c8014001030140780422103184040710500e0601290442ca0360001449851054100f0130307140d0728000400651551200f1860b004034002c3e203640ca0404a403a5088040d0340d82202c00d5034101c51501e0202c0e0050802c40e584801d81010042100f000d034203124000750a440e91140f056900e039000170401d0002030481c041c0242180d0702401c2180c6001340c6030501c100300c0c81c1c0003800f41c441300d07501044642c030640b20445030520b07038156003074003a060350784a5070301034000c0c065000418001644a800110181b68500c00c40300003074900d07002051510480c0e035a400c00c4040082c04010100000d000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 622990476 1250 622989226 622989251
    0x7060e1804110111010209030a0201030b04060905042907020616030212090604053711060f1c05061f0e03030706020c100501050a0902030705072001090531 68
    0x6920702031881050181d000c1e000300c40004210507060700c850b031004d9104000c07001281d6400034020040b164282404188a505000003c0080985901990070207041904100400a1880c004100c0000480c0040c9045040442e1440b0200c8216103090150703102d00041010154114100035241000b8034000d85044103150108290060564803010b86034020030520040040a0120040000400700f1039005401c0031017100320106591903541005c0c460050704a0b06000c214204014100005411a03030307621142120f4002661040c0c4200286194031f8a05240c0202d150085c2c07802000c2c001c090001001e4041e0300c0b1036500803d40c0c00041403110050050b49642c8003400905030740c81c012140182c85002d9010f14605014044a04c0145203281c600148240da456040b4007003990200c92005031a0703a9600030613540d601c10420040c1ca400c5108004251000700400c907294100404c1c1d0f01c40018950b24018444e65441c40724554003502c20745001d810300c401030490480c4002803c40381c0490b07102203000c3c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 622991726 1250 622990476 622990519
    0x608091204120b070201020f180a1e0612050103150203060a1e031b12031101090503030103300f1101090206070605091204080a030c02130516031d07060e 67
    0x9115a00c100b51841c40001404003100036182c3c4158940003c2d03241444850b002509842074500600c403401e0440080f8400e0384600c0a030101510340041140e15021700c48503603602800c243d100310b80000d11521400c05000c05e8500686048907030110303492401140104454000e50002040315400003880d01000480148680c01c061901c0c10009200788402d06504041a12a5541d502e602c40c24080c0e000401200581c411640e0030544c0600e05000e42112078400d0a02400c51700c4009440c41c8800300001c414840440b00a40a1840074007402c00541c031045420300802c5100c21001340462a00d00003c400c0b1030042c03120b0214440303110000900f404150380015219000460143c1e29640d842c01000b4080d00304101740a0204911088903047c06d02e400409540c403843c1900080030410003140200c03c544030183c580c440c0039110700083c4403c2c40c7c400c0711000c2840001c10f48000083c20700e608003603d02c49110300300790368450f010040c110090503c03034242c503100058090305401140b4904030090551118 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 622992976 1250 622991726 622991729
    0xc070602301e04091d3003090715030b01021506060702030a0605040b0702160603021b030c0a050c01030b060706050c090d0501060e0f09031b0c0312120f0c03010608091204 75
    0x458850f92102d0409160301d04032010340c500c80710707440410050804d181000281e540307100d01101001690002c01e24a01c0d0650520fa2980d0020744000170050008038640810054103650103106042d0015104e40402c85c107599135007406501503000766100a20740c80241070100c0e07203c200a0f28182c50200340d0741c0801e1502480b85e40a564099643c4d09020402c1002d0240b00d80080543c80245640703c40c411700706c1100c682600c11a4203043e03000507100e41c00400308088200002c1008103403034983c421a01d1041d16150720000444041c061088448055030081c0f02d040c0f180c0c20040c2ca010b0520106550b550000c0201401d91030002c0c80c14131030510309a8072040d402080e1442440046000d03450100c80028a14025060118180d80781c010003130340c42000415220081460011003140b030024160702820500344024107501409148000b00700b0f60604002840f100c0c41c0041c810728a83c0d12104070040f010002d4441d0003503d07100b000104803180c49900700344d80201e00d800a0b1800c46042c4904500542d001d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 622994226 1250 622992976 622993027
    0x20325210207061a0108010902030405070306091103010e01150b0c031614241f0305191509030f0503041b0f060201140f060111120307050c07060230 65
    0x90b480080001c540190441064040711610005a00e400080d1090005000d450740ba140e0100c0050180142008401d00440e0000010400940c25051a45428000a040e00d00a40c2402c40b8035800d8a01441101c1490b102054140c6101d428114454040d0b4010908030348548230a11940400c40c81e00910000190311900c504400400d41403e010305299242c8100890b5042c46074107d0540100c8601e000d0340807410343c0c65404a04082c02024441151942003e012403141400003080e502c1c0d4260001c040768021342c6c40144400c50301c0781c1d4605844441a000380020300c803495989070540110b0242d500648102c43c907000b21403070140b0304c0603460b50944c06800c3c910402081084000d0b0213104442488940c101d0307800d2240381c6600d0010034940060049810881600c2c0b000301900b87c280140701d203c0c030a42e07000c166641040c0342c0003001ca82001c10340c01b10a001756500011941c0c00004c0c0c4502440880e8441c0e4040d1008156030740d01020b8859000e5000001080105800b10404412564000d071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 622995476 1250 622994226 622994231
    0x608070603060302010908010501080d0e1801090e0705040504050703080717030411100c030c200d0b04030201180f0602030601121b14120a020702061620010302032521 73
    0x345000041906c0b2255100045591401d401405484800b040f509000754003424005000341540300460300382e20407000f0380b500c0803c0180c0045000d02081d00500d02041210044170740c0c481d110410041143c0d815100140560f01c0034404000003841140904481401440b403194003070651050707000340740d100310380c21901c8044071100030303529182c1030612a9140b403041c03802c031001c4007056401a2850020314409064140d181c00c0c9495000c8007802c490503108000780408070a00c2031880d0801a840c0142c500718003550805041a580b21800b070f82d018401c075003000402c411082580c462078005d50025000d94100015000107094517540c83c0142d5a240b412407111401c2c150b00103030001c2c862081c121300c0200c0382404100080d1003078103032400c136a00801c80d59001640c42c100c038400920140310302048003d4211880c24a1001c0c002c01647ca900c03000003c035203110803004200c00450483c801152482c2c9900004242000c0000d4100c00105034203069040110b0b456000b0380010081001c04030300e484500340c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 622996726 1250 622995476 622995479
    0xc0b030702060c040803031b0c0d03090606060c08030f0a0603020a080609071406070206032715060d020a092019030e0102042405071b05030d09140d030201060807060306 74
    0x41d41008000e80c456590501142400d00700608141c4910016000304484984582d815407200d88402c2254000c1c01e04000301c1e50b0710f940e4107a000e00908048074041c0c0d01307907140c03940014403035024500c00d900555018080714030b07583c1c800b00c0140030310001030010f5030707020b644400c0400107850701260b45001d841d10200a01c0329140800c882483d000c1d03a508450f013843e11021410146803a4181542c200381d604540b83c0d42c40740d0f9901c0050001080c0456040c50b80503010f070000c08400740205014000129061100000360380b400709004140c5003d4500a40005038450104020b07200c0703500400d4455200c107c04a0f0b800001c0f00c0c54400c42d000000300f80b003502d10f400c0300b40f411183c15104116110a08600030b508203803a00805000d44045040100c3c07030201c07170018000219103e002110f0543d54020314001c0b40c42207281d02840721201500495020348100400208102d002e040f03240101d0340d20a6036480d5407014102072045904641c0e1044095640300d031000f00301c9107024040b0b0005007401c1e582c0003c00d207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 622997976 1250 622996726 622996741
    0x9130905030714100c090b180310020a110c0f06030604020915091011060c09030304080304060216050f0a2903040f0506011d060114090301050a06090e030c031606090c0b03 75
    0x419203140c020413192034001d18901103034208082808603003104e40c0c1c42d5114907051041050440300072209552600940c81101d65880c0c0d03503806443d40000c00d92b501c200e10320460f8145a50780070020f05040e07000c00c080f14181014a8140025507005902800141c02c252900c40440c10300d160308800081e01c0240492115032a080007180c4640c41c44041c50701c4110070204007039860700e804010742400401c0500154001c0e09460420482d0020207090048a030750381d41d0344100949480003e200c2c524942e02c100c00001c1c40d0310b41249001c0c1d03000001000a02c85a240c03116180d10700110616040640d8807405c148422004400b01851145000345100744940783c0902c1d0250610805030411140b0245846042c0321010388010100e90040c3e00303090024201e00781402c1000c1900480300340940c10340c2003e041180d01c00e140c2d00120f04031807000906110000c500d408507078490040d0308050f202c9502c00d0207074903c034410f1350210100c003600030180020401032544414842401ca5003110102c030f5800001e00851 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 622999226 1250 622997976 622997983
    0x230402271003020f07021903120302040315050115350108011b08040f05070302060712020c010f020a02041508030c06150a121412130303090e01030809130905030714 72
    0x181d41092504500c1c2c07003400030369030001d400b841030040d00800c22070340406000c0611945e15400781d904040e9031043d0785800840207020f54460f01040703805110b010a00c0040904602455050717441c001c04d4411138915100017242c08400d1030303401000a98440081001803098445078550035000d03408440e50310b41c146007620342076620f12031205c98488110144004240c3d03210a10540040c0e0042e458403080d601410074520b0320b55183c101035032200d00020394100f000006505580d00d0800ca03029688480c101c040151f07230004a456009025810a00c84a0010302d8250f21161425a184017071980c81d035220441c681c0303075070045081503000364091400e10040111480c4044070b44082100c8020405050200c059034039049420010211162114030000b81c05080c00201102c101b400310303060710f50158013a010f04146540c402a4041840c41070b000c5038031642070300c00c18107072074100203110328003000380d403e01c01e500c281d11418104150ba207400110004d4414030040c407041e402102e10829001003000c55908 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 623000476 1250 622999226 622999249
    0x50405160617010b0a0e0904140d05181210021b07080109170304120311070501050708010f06030501030b13170408060a050a2c010b03060915010f23040227 68
    0x4c5034240442c0da900703540110954074412058815044c161500d1804182302c504403090381d0414001c182d03440c9601175105015003c0d00381549010405e05443c1d005020074075024810312440780c0c1040c3c0031000e00c01e8050f00103005008000b08106403400d0488842030030180c03990030080145c0d4640d500c00302031069142500c01003000c0540c1403440d604240e41c2d2010110700350140c900626851700442c4105d4045002510845a040030080c4064a0400d1004080c0642405100b140800da28008190700d44a80b1036203040c0c07540281c5402141d2540c140e59041c64074240d1080755190f010300e044c0100041e104010b80b00401c03840d00101000c0c1405120007099940c002c0001600310700e40440303920401c0001c0d807600d0b43c5410003004240029034080107280506041140550988a0031045c0040c3c1000050400c0314294643c002c842241d80742c00b1100001c82c07240c440c1a58076040762138135429450741806a100f08000007440146040500d0450301414882e40710b10b143c803950740e180c000030309081138a21004c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 623001726 1250 623000476 623000489
    0x2210c070e0121110418030f030207051b0607020d0309090b0f0d020103320108010c020109030906050906040906060201050907150f08092d010b2205040516061701 71
    0x11503040c550b056059401c225218151042d001c10a44103105003100d403c130200030b0161060090340e01080c644d1407020b82c041c10840004000440a02d4000d119100761100315030311001410b02590811503c021203070320131200c01d0b0f0088007045501c0040e610700a200d08204e2003500c1744010280f034807080600b280e101120050080b822100d40044541c0c0c1c100102004540c242030001d4a00c1442010b030704040103402542146042c68281009007400c3c00801034103c90101d4020b020424541d88100c3c265074900c4001070100e01401c005000b140e000d84083d110280000d0a2581001da442d10000c040c0c80d42c13a40b1000c0581d6540e42030040018050025a000c0d207903074541d00c4c04030961908010708403007860095404000c45000803608101c0144086201d41d0600620a941d09215121381d914201c0d400389125a02d42c64100c03c1755103404c08907002d00c907020070200c0c01404503d00c0450140540760050040360759009409041e49480210751250001d0140c9036605102c5070b40c0300003140712100d41030b003011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 623002976 1250 623001726 623001749
    0x6060e071101050144010e280b0705030403020f010f0e061b0d0209010302041203090623160212060f100b03010510202406100e0405060102210c07 64
    0x10703480c504850302c0e010000c403030440c80521000c20f05c080040b1080f0310b600d41c104070394208035001e55000000030701c441d0a0203001c030381800060b4000e501203c184007c05801403034036115070006241c00780a1805140e1050082c010381703400c940810601070031188495501031030203a03610300302c80450804029103581f00030580060b4201283c0810341038030900401c51016401600010101016440b0741c044d18014490610b501d0b50010251030003401c10307800e6014883c0000c481d103452004a140f44040d155026904100e40f619041c1d565148880300107030f184081e41c00030303080c2c030341c00e010300c10304004c0d440c0320f410250000c1403d4204280982d00c2941c3c542d0050298420501c01848160b440c102141c043e40024244207807078007001c07000301d035504044c0a054800381c002d1a088504c10742010b12607061350107421001c42d0055803840b0420290b0007108040e0070005241110b40040c500b0154403294102c4014012120080c01d4444141001c9440c4280003810041c007080c7c075401030404106500150041d007140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 623004226 1250 623002976 623003009
    0xf0e0a090b04020f0f03030f0a0f050a0503010e040218040b0a150302220608060c071e0b0711160602030912010c020a031214010b1e0a1b06060e0711010501 68
    0x1e0329030035040504041c0c454000082e0200301e559030600c00d05a4402d0140c1030760780700d60b00b0130344021154108074910350100b4840d8100c0703400039201c0c0341190447d4a498071400d0969007042d200108400e00180700300e0300500302c80700c0c1d20841805a2170703141c803403842114082c607a4503000c0c845109603101c45120648074036000034180300581d9041c02c00d001d00c06000c400d5805403243c14803090040c29a50740300c402d0701e0040005000f503103d41032004041060040e0240b80030050003074410703200450b8a0700054804041d450110f48894420051180c0e140413500840d01d0408092250345100380182c0c0c000c1c00980e00004000c940ba00303041ca9403180b400c1d55807000300400201d004c0003030345a24032054014100500800075041e040345550100c407111042c0f000540940da15840c040083e540b14101891030080ac2c04441c8074500c2030441110180d45c0c03156034662002058070306a0003c14200d0744112196500ea510104000c414a40f096100c0c0c04150b0340c20903810315180c0c8090031104103801c1040c0b0400014038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 623005476 1250 623004226 623004233
    0x7031103100902161b0609050d03050a0f020c0a08010b0f032b050409060b030601020105160504060c061808031602010e1c0c12050a09060c15090305130f0e0a09 70
    0x10208100c90b00380c0009a52400c91080402044a500c40300500202e40301c0c414180801c40640718105483c026124081400d13121403c126a05006800041c0001c004010744400036118034042d01d202c420500458100d560920b00146910004c4c1c0c008049517951022042c078946030560190a5903030040c2c0192190009140c044407602a04504811001e440d181120a1b440e100d40304450091018480803c1555110340b0a180c2560040d25124015800c1001180e04580d50313800040ca0441c29440d0380f8030306840c15205840490a0324030a640a40d07a07070072080c441045000107440ca042c0724810b80b991701e03d00981a21464640ca5000ca411a850a02d07840288400040c058041040c07202190b07400c940300260840d0700c0d1209050003003051904026000005400c0300c0600041c41d5661a60120262104000c8070b001420b1301000d4024561501c00c05c80e1902c5a9200200050007031400703d281c5100404484d400310903ea0140e4001521190100703e0344407040070751b0f9001824028280110381781d548 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 623006726 1250 623005476 623005501
    0x5090114060708040b04090b0603060a15030905030309160f14010c0606050303070f0b07112d0d0e0406090908090f0f1302041d040c09050a0b04060306020307031103 72
    0x4403018150010860651580e40c0c20035100520703030020351607a03150345844801c00d03507420901c00c80310400e04145521580b458984203581c429a006808204900e141120600c0e00f422014102001d05030f6070840e40011810500040d031060000d54001c019200320030034529206503540d44198400212054240081a44042004000b500c2440e08509401550070300e5401004035500003a4184000110141006104a000c0014a000d400c41c542c2903511001d058541031039074400b108041d00982280544912890310310801101a400503620840500e03030030a1030304031a401d449001c00c50032844881c851a141c00f070078000e00401c80007880210b44a03596540725002c0c08620901c01e0601200b40e10b5241c0704c1c020221200000180403c2003151100c11071002540980280100c44000ea602c0c10389041c00856018010341e8481044258941307829022001498050120302d8060380b12600e48126a695002d4540514011880181c0d2404c04c210042d044030380131076502500b417206000700100d012866 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 623007976 1250 623006726 623006729
    0x60904120309020303120405010b0a05152205090103030801080105091504021e060301090b041503081917070503090c0411040b0703051201121203110a030b011214060415050901 77
    0x307090100e00c001d00c9100090640c020b640f1240c58080c1c410080000f40001500a113900c0c440540310008259120002c0c4446800f08100c82021a4404c2000c00d000c1d02d0f161501c494000d464282e490300680d10340000412001d000e90064000549060050103016030a10883d50030203440e2000780040c001d0950f142032196001400170b44940310044005c01c60101c100c211000c00d0714001d000c1c1e41d0300c0da12002c1e00f0b0020f1011100703490240d468000305200c181751804c4043d041d031b908018000d060411400850791103098601001c020040e40c22000060207600014036402031120751034013603ca1400c05616440c28a111007502d00c590308144c0001401800c0700e04483c1503910f00c0d117038580d940d88a402c056525201e90320200b001c1c812b81000004400d80c0008005100b030388242c52448890300c03c00d6044003a14082441c1c0b4514200801c15400f9032030103035010102e000c506041035070810f142414010100c41170005444600740d00d4508000fa0340c035180c492012001c00c0b200c0c11362812410320007c1013803030805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 623009226 1250 623007976 623008013
    0x91b03031d03030c100509370206070606080a02040f0504030c080d0b0a0801020d0b0109060e0405070905030f01141b040308160c03030c05060c04032418060b0306060904 74
    0x5024809440070b00851305000740703220071944144050041013008000486403541d044c01160100c1c9081490202c05a0a0780001c1c04185400b031421350042580c402c0148007242d00c2201040722900094260040000600005020340311022090050100399030045000d07698030b520f40000c01001079001261240c000b600040c04035200c42c00c03050340384010a000e000403588001c0a032030015101605400402208404c0c0301c00f03020780c540c0078005580904aa0260001180000c0300d1500982081e501440c0d021203149410401255610082070030080403180302840c9946900803007007151101d5041980040b50f00000700130b080d40041e800c02e900d014500000305507030703000202401032034100c0c1c04e00300e000c0b030b001070407200004d5076441c001d002c0414004003190140290f00000700e0902218040c1c908030b980000d01c00111841140511a0100500c01d45008103507464920603070b560032124030b108116201304c100088000510f0109890704000905c8030744a41107500c00c200010360319015000d0092031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 623010476 1250 623009226 623009267
    0xa020d0309020112060e2707090b010210021b060c040b07140f060f041506030f080901140409020904110901020d08090a1505151008010b0a1e03091b0303 67
    0x706480100c2e50f007000000350040160030210007080c000c1501c41740314000d11905500d00100c3c02d40c0050034444a091100c250304a42020804111038141900420016001441a21190260240e0b000100d0b0004a41e640c8040301c0c4440c001c503520000c0107032507040140102c405042c07518090483c01300d171061100040003580b840d00010205501000b0f003859a070102015245d40349484010401140d500302d07802c0e9041c421503c03040742c000102e0b1254605070713034000c50107040040041d2900203840d44030b5100141000b61b071400182c00051500c1c094030213007180040c0540e641030003104003c180d030108120316a04500c00c1080c01030580c1c00081111010885040c00f02d203a03a520340e145804e100415801410700031050340c01180e030320758a0b44440d21810700050540010701144080c8141d1a90f407924000200d110342c0014040041d130030000c2e04a2109915011031541202000513901c0030300e52a904000c81d8960301140100030300481104540c00d40c080c40e04001b9440c54070000e050300d80558800c1210038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 623011726 1250 623010476 623010491
    0x9080309150c120304050d0c0503090103022a010e0d360306150e090331080307050303060307060c051002030c0909040b01060f0c0317090304030f0f06060b0a020d03 72
    0x65007802030300c810714074050039169200140151914958411602182e01d07004240c52003000034026400c0c904603c1e04030009500303141a06006400951005040100690000e01062412070124601410a800d581c0c000b0421400400c07030781b441d0120036103030782050144030340001d1508a071407201a411440401301c11058031541c1c040034000890640c0000c2c000c1400d04145880c40340c9502d01d81d50440e0b980c07989030704a90384d6006401d500ca0260201107001c5044d0752016003084440c0d1602404420035110500300d120342d44000340752031940107030001c03205504044100f040510b000c1c8100f40040200307060907003107010a07913500d580b282103409020081d5640403011468905500f01a194070354005841c8040398185810050000f942c2440b032403001a44801d42e0441291082c80c8486e4800c0e030584580b00314140340aa00c0c040328100600c0000ea034401404000082004130700d0044203140120410700010b2003a0504500307594032a003241c03103220400c11080220990000d880c2070b448549140008004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 623012976 1250 623011726 623011759
    0xe0a15020615010905031603050d0905180603070f12111912150515040e160303110307170c100c05040e13061104050915010804022809091209080309 65
    0x130100ea0000c5416100d880790201e81c0d512044110303029a400380044442c1c440d04000c0844034ac00c800d005042d004001501300d170360007100010358a50003840c000e0079529000c0d220801d0075602001c80d40a034040e441ca400854060206e58000e800003c407007580c0104018a0803404001c10038454413a010368444107000b80010321250b440d907a440440c216009110038202700b242140d209000a0600d032180303191900823540e03034000017110442070030b0340525904810300c1e58400b035030428445070741040c06003c100404400641074061545400314400c0b030305616000070003907951411040c8000301c2c0815240601c5402c415030072100740c0701210000580300703280341d0300c480004000580101000380401d08200c290100d2200c401c02400664505a4441c034065891034006885020440c2c2c031540850150f4002c24003504140d690f10b0750b000340b03036042c0d4480c40507036005030001d840080e40702050940d5640c08540410640c040d401d51155010715103c0a942c0c280569207449205114080f0310500440c012034030130 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 623014226 1250 623012976 623012987
    0x30f110a05030417031008061e0604090f08120709060e0a0b1c06060224040b04020f18040c03030e09040b012903040c0e010b040608040f021f0e0a1502061501 69
    0x103010403d100039200d0816071041000140340e4010100a4010100012441c1510041030420741c00d689d003001e502c5440d1907040c0070060004140c10f0b5440219403c10750080307107642c0f005141c3c0e80c07010102c01c0445c0c0b6040c1d000600321105a002401088415160b1056544d0741035158000c0e100c00c60023142e5201c410040c6100e880c00301084141c101c40c2440000144181c0114400c0150405014404602e8102540715022060304403001480e4a4089010401606003000c2c50340c100003020b811a58640c040700a6030a59010469003181c1c085508102402003503840004240b4034102650390081c80d0925030f98441c188a414055441d00c074014407011000004801c48144601569a29071641d0382414103107106201a1800764545c003040307030300000540807484000c4400f203409507940c4074115101d594821540c000c0f8040c0587e4015052503108400c0017840001611094860310b507a20110b0452050102d14050395015180f480144400b001146801092455000f6284043e0348011250900180d49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 623015476 1250 623014226 623014253
    0xa0305030a1e060609050f03120903011104030809032a090712020a081b1c1113061106070203090315090f0f03030709050303040f03083601030f110a050304 68
    0x8030209114181c00a611082d40143c041c1e030266a40c0007142070701c900030311480d07141c26882c241d007540c082c000c0403c881e00310b40040c00e0280710040003c0b680d0005440c2610b00c07a0416003081d5403420300007500341030618040204007a0081da002002d8224129800350101d11740c403841103e40100214000500002d124014800f10a03c626004548650941f840200169012640c41c20304070401075401010365003c0e410383d00744041001440d15603542400d080700103003c0d1405045a1000c1c241714140307400244c80e4040002c2e100340e5035201c0030000101996881c005000e840c1000359081000044005d440220f441c00301000f8003100400c958462100c05850300c3c00d0300103e0f2603a40903245507210030000110046009400c1035039150001603e520406460380320700e11852414428034002000001c03400c001a1484900204034060498503402c802c55441e49075035050390322145010504003166825201340707040070300e00390803c02101001d004001c1c042d10603504000306009000c4000750030417107640c0340f070038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 623016726 1250 623015476 623015501
    0x2702031506030a091118071803050a060b19030c06031a031c02070605030f010512031b01150e01050a030b060310090f0303290616050a0b0105040b0d050a0305030a 71
    0x155a0310f0844480001448150021210380c1100819110300380f903d0600f45c40c89a4820940b400c0d207440d201820b80d2000071121661400040380c030000004075100344940c0300d501c1d000700c030080b40a41c41301c0104003d589401000303003e160000002440402c02c00e2a00d2130999103142000034203e030f0310910000100b40c04000003a41446080034180717542c1100c100d025140c0300c20350212100b203500d9001c00c1c0c07a940002c481d02e080c6d03200d03c00010005441c1c0700c1001d40d01103011406591400e5038000d4140103581e2865944591691035500980c0035040510140300241180048094254180400a26a2082844090480e000103001b003696550140034500783c0c0c0005040401426410703103040c410050401070250702003490103000ea041c3c45028100d03040345003103400749001109180c078200540354014141e1003c60789104840b0900003071081002c0d2030a24040c045150070381d07150070100000d80300710a64a50103400714421003000a40006140e09500b0f615043c03054499030b5801d0704c031000304408009013 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 623017976 1250 623016726 623016739
    0x1c08130b030103050318011706091801020c06010f08010c0210020702120304141f021c050c031b011803080112020f041107031d0a0506070c0801060f08060127020315 72
    0x82040713000402403070b0400c10291000400044000150b23040048000f18204034008200029518540b00020355844081c8070400540500c59000c03030303401ca030031245005035181e03c00d00040c400740140003043c0d0700402010000307003e5414011002502c800381804800901030f0041400011599002c00800c4002d90170400c581d02e560b61102c008004d82c20642080d406500d080c0c1802c0c0034041141d25403442c17000c6070340040c003e40b5074042401c000141a000a1020040f080c00a0f20340d00d9824001440c0c0301c0e45011310707400901079051409003103410180304030740d60504402030000040d0300104624111040031200303076440d840e00d0000c14001036a841410f80d00600d0043d0100c001e9104402901269001c0d684040407540d0400170200b09030441a41c80d0382c132a1100b10100450b2500c00c2c020300c01d40b8400d540e0b01c070004c3d03520100c0a0a5600580003003594a4010030180b10082d000c111641c01051100601b40b420154003d2032030350b2052980300c6000301500080041d80f40807461440c0c81919030041c144 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 623019226 1250 623017976 623017979
    0x3270506040b0a110403020603060301090c060c050609010c0207151b0605010303120509031804060305060108071505090607030f030b03060708010515030c1602011e03050a0b1c08130b0301 82
    0xa4031039204440448410240001103001d101c164428440c400141c0c0d00403614190031a0208445500f00816080d4107640390094080004e95500030500180f002d52101020440b00c0d141c07044c24030703a0091003841c0c00d138500451091032940c0082d14004856020386112000d15441400b242c80c4100c42000000c00a0b4000078201002802e6000c54100e1b8044c0c0c0d210115580c55140840070780d40140e03504030080d4024400c201b80303991a4804070400040041000641c265a41d4665041c103401342d000c3c1085800210303003040074180740c101468542c0301524196103002600c600091990240520107001c22101c4245200c0c3d06002ea07103c1681000000c040b41c20b5450319400061056109001c0c00d8050a080f491403402c0440f05010790303000d070b010880e0721030a04e00310410900c0c0c40100f4881c1a410418110b40003e5040c079601405108400c40f65004030340d0f440c1984150702510046e406050003070b450514102505d01400848886d211342c880041031752100703240c000c03400c2c988140d0450981d600c1d00000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 623020476 1250 623019226 623019233
    0x50318120f0d0801053a020310140903030403090b0d0e031306030f090201020a0605090313030303050a14041a0a02130f0503070803040b031b071703090114090a030327 73
    0x1442d0440c0c248654900d80350382c0c0c03140140404805a20300402c1d0418245100d21802c601c038290307200701c0714100048800c2004082d0006880e2030902c3d23002c2d100e400d41d24182d8050b40c9ca000b2060550000d0040c0046180d410103540044c440d81262044600c005000304105202c4e80150b0413040404c5901c81c100c83e2038071003840d00008800d0042c4540780c0440e00d003100c00302014089015030102c40744c058010700750014003501e868001d004000d05045090108021003580c1020445209001d54029900042c0e640b07062a010021152208055035415511204200c00115669002907403510b01c0305080301d00b500c41d0904400070740900c1d00038602c1280b80d844013107500c0010010500840e0803c800b22916a60307980d4000d500d03071045001d41c0c0708201c4104006035a528000103084c3d11450302c0720f4214900b01c819285c8540302900e4420606170349100205100c115182406100c042c0070707190500c00c02c10f0400d241700c075580d003512502c02000d05444904c44141c0c6075500e0345120504518840c4510010401d14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 623021582 1106 623020476 623020483
    0xe01120e0c0d0f020a06120b032d070e28050f13050c0a0e01090509010c08070f140f2101080a03110c1201020a0906030207050318120f 59
    0x43c50b500040e00d9031000c6000601c41540c0390800ca840c10504c000a07250400f215910030350121281d150b42c1b01c0304001e0790404038510b054040121110708441401c0255550004102ca900d400402c020000c40c82500781c030780d41000714140410842000c5801c204c580c16203a17803001c13100301000a907503254200c000802450058045644449038000011a01480d51b00445032200352040104001d0300781c0d000d0580c102da8403400900805a002e0802081c24000070800010403280040559001e80605030403425031a00300c040941c1c510072084806819844121301c500c600048400c03c40d1341000e94207001c3d042c0c444060190130510304c40e0301c0403252441022041074490003030045c000000c4e907409134000310460000e400542c40307420402c0c02034102c0300c55500c01014103004014010009201000b1a004c00281d029459085941580450000101500105194890400c1c85050700a001 = true := by decide +kernel

theorem cover : BRFrame.Cov 622841726 623021582 := by
  have h0 := BRFrame.cov_init 622841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 622841726 ≤ n) (h2 : n < 623021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
