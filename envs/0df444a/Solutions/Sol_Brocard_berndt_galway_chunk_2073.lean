-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:51.875988+00:00
-- url     : https://prove2.me/submissions/601985fd-21df-472a-9b58-694b4c3c06c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 372661870 ≤ n < 372841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 372663120 1250 372661870 372661873
    0x1109030a06020a0210090206040302090601050c0714030c0102070503150702100203010b1b060f06090a1d15060108040c0303140d09210906090509150d050102070b0105062a01020c 78
    0x324928180311001e54000c90000e0018003842a1000c1004460310851948a40161a031800e07d07007076a01788a00e0a40260000b41406018401101d07401001c0001c8405025070074100b401070000c110170b040ca80f90940d0b12480c103540100c1d4051015031000034400d00d4803201003800210039240d03024182e0078442a407188008043c00000041800043c0400500300756910f0171050f10015110301a0741d0b1030313440c2540c9090110b4500404910b6500e40320f254039800ca40c0d032400004102544a0700c2e0030408481d01040c0419401c0f885210351880028090346e94480c0c020f08080d0b00a21300b503a1440d002d00684d0000030107001c08542045240310203582507840c403941d00041002882214100000384076510001c5201c8501c81081501685108510762170459a09803110609035041800300700d100d61008202114900d002c40c80304110350707540403c003218103000d607000598138000f81c282400e04c40c205070080c501400d0200680e01007090754903c4400b5144027550100842c0a118456601902c035950b2000c000b0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 372664370 1250 372663120 372663133
    0x2180907050909072105010605180303040b0d05010906050402091c0515010b0c0d09180e030c01090f1208040b041b0305030c0d08060307050307150c0206030412080601140a03110903 79
    0x251900b05e0305100b50100c0e1810341c4455070310440d030b446003658000d0180d1400500288180b02003a0030b1922040c0000600405490a02da215902c180007900000c038a400d0359900e1f0001003200e04c4240c030030200509825074056140007510f40c041340350941300d2141a08100d280321041828042c003800907180308040c006200499503500c41002803c1d4216801d0048a03000301000401000d0140c035070941200c01032401d0b0400c0700d6024011310001c0200350141e000324003080003002d003021020721840c5a1103100341c1c41460500b10701d0421405602d2158003250030300005106200100d040d003520107521641c0442c5001000818104100664040d0740c4018003512010402030f00305c49000c207040d07554002030380c0c802c2110743da25400c040e5190722a104668240d0001d800a00125400010800d010301c40c0d41840d0b00d4107a1f090740030500f960300032641a685030b841300781c54842a40e88108516048202460301c00c0c404e41071500c040425100703403400b0000303065070b4001c8103400300c119400703590035084005c080e01c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 372665620 1250 372664370 372664381
    0x507060f050f04021f08010b160c0806040302331801090503091903020f0402130b0d0b130902183403110a020709020901110307050c03010c0302180907050909 69
    0x6040b8425201248502000c442001c0306000940d4010f8085106661354a0716034a1b2034404504ca5100111100c1d41505048038400490710700d00718040101813003c028281480c00b07007402401c204928000151200c051280841c0e441e6000a007000e1403117120400b912030b503da0f600c52400c50448019030101035401c0c018030741c05010010000d0302c036600007524401714501486401e80d000b151030b800000d511003802c2482158a040550240002c8040c40212815060f11800b0714655034100c2004050850b03180d1040080a0070110505410300d00000028407403000c0d81e038002141c00f0502003c1e00c0a00401800080380206403600450b000410401000e0f040021010700702c02145040a0a02c0421b04100c400002c900300003044802c1c01d025680074003401d0b0b0515043d200603501407400c00c4d041010365000c8850034034080c801400440c1c841e070f0051030008607030b50030726081d9480020300c5e80c145403040c400c2507403420008003266010380d000c4810070003a40d41c44000340da4a0144500780d9810480f40c108201c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 372666870 1250 372665620 372665641
    0x60120070314010b03030706020f090d0f0302150106020307031202090607110a050d0f110d021c050c0303090609011101090615030c12031d210c010e1207060507060f05 73
    0x4090764007403660100805510480c07182600c00c1000b0b0503801d640100902008910389a02920400c1c15422240c2c0c0b4002c04103000504030360340b4003000d07150f0100c2114900704060301041540c0c03081d02050311a4145602d84180603449008038a4040c091002e034004507010030700964121421080000e18554407031702c2d1801c1840140b6040540c00c0e00441c41001c0101782440d20881d490f000e540d0124981041d003205a07100c0000c1c500d09407580c0d030428001400b000040c3d80380d000c01078410001494081d1002c5d043e08280d0320b0035000c00c1506000303820420810314291505c02c122000301e002030900500a07500305d188a0b004228111004d041c02d85840c0b00040202800d82000e000c5034000d0b10040d0301c43d40c8038112110441002000180419040c4801d2011190f48078558502d86000428921824441d41c8280c5c50241544850f40e40325008005650155071300400c00c2c18211400341d4540700701c02754440d041561050980960024008045004020003041d0781040d441d5604921b0180928148004e110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 372668120 1250 372666870 372666883
    0xf0c0e150109140a0b0f1314090a110a050703090f12120e010903020d140607201f050c36010305040f02060a0c02030a1a010501020609060f060120 64
    0x50000740d16102c00104400026149503401c0d030010414815645001401d031010361141076000070165050003101d0140346208800c60007402c2c0b005003032a0f480c03502e10401041040007048100300c0340c5001c000402d013103181029500760b00b005092490303850105040568481c42254441c194800f0001008507c4800782c50504003180c1c41200b0258028100c0c010559010049045440c0004c200705801c02c0940361410b50850389500458034a800d00c0c0010070500d090100485100c0003140ea0280d0b0407070280001000000345070140300141043d841856280098100c50016441055454a0200d0f0804484070100c600041000c400c4829200400e5102400640d800c2029030701428002c0d80d00307101c2d502034000d4030b03ca00c0c0e000f15141c0340d001c0385a003005055004002841e0800c9440800d090042e10200203408440b80544201800c09142001300700503150160881ca0443d0810001e0004030000050f445822a0401241406aa81d10801211480140b0301054180308880322000015440032554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 372669370 1250 372668120 372668161
    0x3070b0c040503011b080a150306091a06060405010c021003110301030b091e0a0609030909020d0204030203010b060f0a111615080903091018050306010b0a0f0e0d0f0c0e 74
    0x902041c0d4203105c140c1641c0301d00020300004201c0b101c00044500030325601001042007a070a408441d503803261203000885510340c41c100c5200c40b0711003070100c02101d02e0895075030107a400c9422903d130038104400246a004040002405114040244071030540680c0103079280c92010441143c40c0d42c0d490500c4618200251462205170003224900303214480c0348080c2c1c080c449950401455000102c0d540e5000416660b18140c0401c9078200c40803c80610900003027103402d401d1000980c440382107004040c00c68105041d00d41c8114400c01c5140c4001d030b02101511646041410308a000550140f805410000351352907502442c01c200d0408078035000f202198082036401580c55011030b0369800c590030340da84220011581c1c8586150130707140c4c403988035901c031001079140001c2e90304605a0303c60200385030000a0f000b4070303001000480e081005503486598180b0009a0b40740100c443e00c07840c0c1c0030480034040c1c00e8014020b24005d094041c203000c40783d58800c008040d0740c50250380c5890403803114180500010710 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 372670620 1250 372669370 372669373
    0x1707060e0115060c050c060a0c2024070b100e2a0c0102040b072901030b0105060702040213060f0207091a0418080c0606041b020703021203070b0c040503 67
    0x5001189640511590041e610120000c0b52110705104055565110900080707170b891043c1e0942441c2da458800103003110350100d456540500c0e0740b40c0f42c1448202ca805c00d806121294030844c281d05581c1b9004820b002142d132038091074140040c41c0c1c0400041c0b0604002030304e202121000d01c149848a64120012280320310008040c54032070b0400b80e407007462071701c0d00401515010b010400c80a40194020715174100088001442c142d91030602c409103800c4100141d840102010040c140d400d0000b404809203000043c6c444155030450340c030617042d0032060180a0140002040382021902d940c2c0c102c46d50b4201600700c49004c903542d07803402003a03500304041d50001030240741000902142140100c0b00c804848051314030541d00408140002081c20101c0e100d0288402d0001401246085004111900440d00a40000d01d483c1c018081995158041054509250b0036201c10345035020441505503a4121895041d40702c540030864030f94014034402400b00e00c503a500744901481508018001c60350280c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 372671870 1250 372670620 372670631
    0x918060f0504020f090a061d0103141c05030a09020622050d020f0f010e09010803030105011d01050901230f03041407030c14150a0f090e160c0f170706 66
    0x41496041e5101610b00030f41180c0006014034007490301869030f6501c40d440b103100140d05075a5040f01928500c100300441007620b0510014020300010076110006040850024a1030204140015260010410311042000808030104900038001d8105d080040d8000740040d8503109042c43d90408e81040700c54030b0300b8940300701e1000110b5003025680b0b0201950010500440c4c4400d0200303104034500d4070582c01d410031400c8120104e96944078600203000c2c01822004580300d42c100400980700d00c404d0390f0210418103906e00d17403d4960387c0c400211004c074502881c100f200031441180580c410107100e502d03154451030100d44260b036540c00401861180c0c0c018184640700c8408102007d44804890101034074402c80030308184010341c05412134210b5a6000340c1005140d81d007041c001c0440c0d821048856001554080c1e2170089180e0001c0d81801a1100402c01c090a0408000c03410f101002a07403003409210000d021941400304c50142d074080190030070801d0549100701d80c1c0d41c60072a4080c0e04100e130200e1400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 372673120 1250 372671870 372671891
    0x4020a120b0406120204020c0c1c030215010506030c091906230f04150210050403110c1509040902040615020a0c0b04030309091e060e060a0b120606090a091806 70
    0x2801850119004d440120491404a4092202941c4080d001d0040c074411203100803003a460311211702c800d02051180c20300350240035150083c01d0012a04010160350304034001400103541d002c0880f90004071403c80c0380c0d03030f03041c0c1c1001140ca14075064208001106501c40000b910310340014500300800440d005805003600742860010140c029150a644860b20511040c400394010a02491080010780119004141290b40c10425580122030480000d03c036080c4031a4031076005c1141da0420402150401881802040080120f0040340c904611990300c400c2071400f95201c9510140203845080c81c1440711720302c2c4d1074020b55a035081130341c02c40c0c030220304c2d401c00580c0d00140c00c10307501030340d45c59518456801d10341200131002e0684105003c0400d01100e460101b0318078a03200da907004104200301d14095103004420814508210381c8403004581c0b00b00100890059003c0000d580701c00120b03a15a1a0300d1702001080c040200760f000900c129280146001194149500c441c0030f5038411101442020b450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 372674370 1250 372673120 372673129
    0x6211d1e07080307020402030c0f03190b18041101090f080607020d050c0d0807030e010207060b01031b0c1b08030a02060105040c090602060708040212070608041b0b0d0207030e04020a120b 82
    0x100d1041d9280d90f00240002001490160003c64000c00b00903540c0c3e044c450074480c4040540d00a482140c3c8000382a07464461100442c0145044040216400442c1050200443c184c8001c000c10050061581f850180c15a070b001344910800380010075912400642c85500d0103580740c1c025030f8a08058894120a84607403031007402165407a40004018141c0b110148a0560324200f001d050300c424507440d84990340b41e01d8030074806800064043c03440130640010050014003290200c94441c1c00c44140e120f10b0310b01c515084101e044c0015031013071010304500407090704c589014100b5006103110740400141304041d20782c00140141a01c1040b10108210100410142c0c2c00c01207520541003d070308241d001807803150040b8403542c0c2c01400076200518280f815011541403030b9094100c0340219a1041c24001448407007450601c601000c40801c2e5005e0b81089031060f844c2c028036000c402055000a100000c040c4130b0b0071600f8512601420175506c03088051300c0038180b162400c020148803840d061122029280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 372675620 1250 372674370 372674383
    0x60919122f0102120c011b050d0c08061e0d0203060907150c0b07080907080601180e030403050319020f1f050a2a02070e0a0608120406211d1e 62
    0x41c140c005003600100c10340481ca281e00701c4406410555a540c040c1c1d280c00400035580c0d460040741e56100b95583c0381e00d10521080b1660307900c070b4004000d000810840780ba140e850421604d0780c0a00c444a4160341c8100c0018402d0801001c020340501420f424001510800280380041e100722408001480d10140300480f540705c40064090580d544003404940c0c8c95001d441d01070340180c02d8900343c500341600c5411940c80e104081e40003494400702c2c0d090041c1c20001600c201250341801801961800d890342c0c4409550340142c91102c81110301d007050050b42c05000f0405001c0d580b00c40340540d8138000c4400c0001c1040c08400004401c09814100019a00d0450f441003807074112448901c2000d03084255a0000f0b907910110840065110b681030102c1c00c2d0101142c4684190511213000c50300509141403682045e15620210550b410203100030f1007069004440710744480e20000c034074564800400309072f6010b06080e103000388400b40c984880b219400e00100d50850040311100014007555040c1d0600f940c0c408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 372676870 1250 372675620 372675713
    0x70b09090a0b06070203011a01140c0a022725020c0109030b0c1b0c011b05030d05061c0f050d090803090409050304050a0603020d060b070206091912 65
    0x800c24001803440740158841494210060b18190a003506540030a00311201407210310141782148810404070341e442150200300c0062580190709000c0360071815552800d5410000b8800c030542c900300300b035100003d019944610501250000b80d41070203290b5209034108100d100f811890411032900100d400001e002e40523200694032200c0292840d1105114204064411055080701300a01072008c0756259401c20559031040140c98248c1600b40090846046d401c09281c0000121602801040c0d020058800050220802148035541c94001900c0485c0e04e07452602c0013261009904144001078008400107071207241210003403611520f0946d003100340d91185a14541c410000010b03a400e00742c112140070340c41101128202501d400018403138034619000030000950201c4c1c00340c500341c014060396004101c0b51304028034100346600814528468440c54a004021007003010202c600421071040051025000040c80001c1c076143c042003042103013000380e0054030004644030401d401c40c07038004003c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 372678120 1250 372676870 372676879
    0x406090305010c17060904020f060a030e0c090903030a02070f0c0312091e032907021f0c08060616081605060c090120070f0315050f060a050f28050102070b09 69
    0x283d85d404100b1100000003082260412085425507043d52510390140c00c0c0c0c688982c0300841c0ca40c18441c029460701175885101407190074040280440d2001c048126508801c240801594a03003031403d1400c109129440d00811100c8150000811700520400800e50710a855440c05140c40e518040c411280e002d40784003408005011030308000007070705c450300f60f0344603802c2e030708003602c90b11200c0c00101a0040848054015030000001c0c02d011130101140f042c80c1e8600400304002c4040c00140c02040c41000804142c011080040d40c201c00e5940d820220401c5944042c0e219a0750107581e4815040c2d0004100441d00c500c245070208400c04072040a540c101c07101070759072080b426201d45158410303880f8084031441d035008200d0049000809482c00c0c1c00030314040c01c160b00d00c894120503110100d0360020460301e040b10a60041c044503a45103c50781c000c607501142c250800c0701030100000c1ea221004030603418038030f20120340c1650300f09903045403004a810903005e603144e02d43e4503040c4541034803543c0b5049511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 372679370 1250 372678120 372678167
    0xc100b0f01030b0103110703030b270402060c1606050c01060602010608100207021809010507090e040201120f020d0218030111031513020909040b100506090d11040e030406090305010c 80
    0x354420f070b10000e4850014075010404075a006501040c0d07501110301640000e44a80348800746041031302c02c2e01911403c5020301100039010740004407440c49e014200034880e00d0300203000c403414041001076211980c80c0300e4010101d183e545c0c0018050394009040c0713070003c1d420921b000400318010701c5248102c84500003e08480001904280001c2d44003031401c0303031711400c0e120040c0b881c606803104140c400c841d140000182424008009091b140c1c0c50f80c000c004a01c840310030000142d9200c441072030a41c04801000c10b0a0f01c0c000f007010080c2c00780b0304607480403030320116090189010461103a08080415802004113100a2a92060500c001c031880494802c40070244225400d000702d0850300d81c3c40908006080102040006d8200030095409840040700715090102e201b1080c0401e400804044500350701d1b001c0424086010b8000181e0040d2800007d415941080e46460300840040104042640da5980d25140042c040c4445404241c405619017400b81c048580102280c0003400041c80000c41b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 372680620 1250 372679370 372679399
    0x1b030312020705010e06160921030e040e01090c05090108150103200d0b06100e010f050304061b08040606150c020906040f020c010e15102c07050c100b 66
    0x80d500c1064200c840b5941c1e054170100c60502400f0032030003160305440c07210020f41c05460080c140c0189810084101d01d15466021902082c0d07846e00d0b402d10342c507003007050015200390000350091802d0f4010346c0c5654202a9240304100c2c81003560070070341d40122001c4030301d40d03216085507544d5a040508580c000900304018408203007940340301c2a40e00203115456054914103800b1550110b00301d442110409207207014458a841e20b40c4070400c070901c0f1454000c61508c0301c0310008000c40b022240f1b420a0143c000082000d114441c3c00002c0062036190010b00301c185c42000040c03902c50115401d540c620303d403d401291414a05d0a501e100305030b90360300d103100c4c20035a400300105040041c081c154010750b140320715485916a80060840c80100c03500000d201915081c4042c100718041c4c0c00c100b540707240442041a541b10f031030249400d40300c0817410304044034941c00c840620802e6016104248610781030400030100c1e8484002d006d13901c402e41c2510744094490400b02d0998400e03052080d44803444048505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 372681870 1250 372680620 372680657
    0x815010905060c0f070b0406020c0118050d0609050618060112020603010608370c020102041a0a050c0a06231611031c0209010201051008070303140903010f091b0303 72
    0x4044280f90580e0500e82c0030a8240f40b41100f60352190a0050300894104041501440903070b4088034203007058072a45070030181a840c0d007a07243c010349200b0501c88048109000035640324201c2b480c0d101003112000c0c240a80070000c010b0503400f4901040c812000041005004da010008042d50301401003425039007014804d65103a540204040000c13803294166134101c110f543c0451180c82c00c0c141000d6a400718102400c0180d401d24811002560b0040000304002502100841e144070040e403810350711a1030042d42212030f4803482c0740c3c00501e4443c000f0007100f4003010f9448038610044c1d0914403a011042001003100902d8122303888081e81561903441218103010301032404c284260902901c0c44c11b80840b00300722109046a10b4004060b6010814217aa541c0910505400640c07011070049468582643ca595443c010300005042041070750000d003081ca01038080d54a0914018004d0011400035096103004002800c800c1c0da0050102a00c1181c84001d0340707511054030740560718561240b00460390760 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 372683120 1250 372681870 372681877
    0x200102030432030d02030a0e15061003020408060a0906060308030106030509015106030e0114130807030306050915180610140408030310080f15060f120f030703081501090506 76
    0x22821f242c9961116223942e0050040c86103141c0150354015503030401605000000501c52000024584104401c0c07088480c00503240b540700350101000b140d070031900e140050103400d1350352006103529004400481e04a8064000070b100340344800081010340c0810492001ea80c040320346024a001d80d030600102c4100e0380c030080301a284689032000500c880d1400c515000c0e08040e5019200080e03503103010503060b083c01e010300035941015220640e00d03814150042840c040820f10018940100059944200350094011030001e00f4001d0846000b858080e1062040d038541640e403601c2100c1d00d0b10520344901d003c80c0c10706e0103010b015100b154102c40da40300c00e440b00c1c004000c1c07401d064403062100048071f4900f000110722844440d00c030381a09a01d801c054515241d0308010740e1134103800546130044900780001c6442d0380300d001202c42c034074042c08400114680002c2031440e0031140c059118902c1c01d007403002000303246080c800d554000c4195202c00070210344440d1030141d94001002040c0c1000b1614108018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 372684370 1250 372683120 372683131
    0x50c0c0f180a11300601021e1906020d24121103250b04030b070e0609041b02161d0415050709030201080703090b0601200102030432030d0203 62
    0x66864210307401030505400c10f0540036076800c6103210034011000c00c11090484d072a04294101040e081450010b9201c0c491403020030b24106025640e481c0c2890100901005e8140c1c0c0d94501900344024200319002c2e40c407a29160070200d05090b02509460742014082007880303882030000d00c866042503940307407811028201c1680c41696001401c0c805503000e1050004c80054130360905c0a41d1034000c00b009401e4081d40c08103c0da00021702c42003002c40c60841c84542d00c4083c034a40341041d10702040c0004d025001d0441030f203402600d80040c00d0042c00030b000b08400e800030320f50225640401500050305083e01e090148a2203001300070000300e044005218500c0e0058452081046143d005802c10001c444086500380005000d4400401c2556000051076800000f1031500740581c821545910807042c0d0040c00b03148c1040036a0481380100c2c401e8030700f44a545015807000350341e64149800d00504d4800c2a10f01c10b2032044455001c100704042076000300c256902802d0141d824860b166401d05c0094100a01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 372685620 1250 372684370 372684391
    0xc07062a110a02120c090c1306050a0c02132a020f01020a091203020712050106050a0b190c15020703050d05011d010e040c030f052a031e030d0507050c0c0f18 69
    0x203d5811990351b20060741c840c40f00600750b07503100c00c83c42400c06002c082a6101c03a041c40410090310f0394860b4030000000c3d28940644081070303400c8414034000d0041284000c11744040210020516070301c2e0b1400d600303010032665603080701c0d0085150304546080388038101380b18000c500110b0b03041040f50070902d40006032a0090040d209029514080c40d23680d04101c40f01128665036400c4240510300d42240030b01b000c0c0c0b800010840c144201030030800c0004074040c007918180103003007600c071041080c0d4006070b600319001200c003552901103514001e00030340c0100710f500720914240350010820907056103420030801d0320402c00481c981d10380303011840c26a90152090b030b10344079080000303c0413510000b840342c00c10784200f0080c4000c0d07000760022030200c0300003124070740ac0d6603004000700d003150f030001103506402d203560200c0140710b40e510208510f90310824004140f038500706002c0041d1982c03c0806054a400b80b242a80d40b0f420740a002c01c090025980c003815882003440c1100c401154040f9040b80d07100200c03da = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 372686870 1250 372685620 372685633
    0x10e0307061517070806070c02090f04020a0315020409060e0c0433081e0105220f06060e01020d0311040e0741030603060a050c07062a110a0212 63
    0x4018803800c1c0c07409000f50900d50702681c010481050308102e031541c0100c60f80b4092104601c0b903800554141005441c0d01410380800001c58259919014907070020f40e07102e0000c070f4110000406020207500706110780030034945030810000d40189020704482c400c2c074112007914901402c0280d4500c1d42d401e8604056021300301040401c5a441c2c0c40000c940010b6103c1d03c59400c80c0c5045d200340503d8904040c203c0300c6002102e0010481038540300141101a820440c96403080c00504000720002d060004803e41e015040080003d940c5070000303003488000e1400e80c01d48001e004001d80aa0035601140d0511200d20030400c070401c00712800000d8a5042240ca1a040302242010b4a00540e4903100840303408000d604a510040c1100c40b07043c581c0700d42440c00905c28150b01d0b00c90006074666100400c00c50301c0e241c484001518042c903040444966690101c010000c5000d40a04240144040000602a01070174004140074600904045a0b121000801401044903a909000e81c00c400910504018882c03130 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 372688120 1250 372686870 372686879
    0x1002010b06090907021f06140301020a020709020a030f051e010e22030e0603100f0f06050904020f1605030703030b2e110d030b10050702090406050408070b07030209030f010e03070615 80
    0x4040d2121b9140c0020085015400c004a005110300d249800511980c4100401c4094640101d4003c04030f400641c0c0060312144060400d0b4042c01c48440029882c518240402c03100e03104010400004180b078840d8444181e8a516049802000c15038071280180001c03c41520b410541c40000e4440074802c2c50082610760b1101c000c10b4040c0c0081d1040700c4000d114407024000e01c01c0722079604005016013041c5840d00d80c50070340050010f101d0880385034062900000c0000d280741c21982103d2201d003040031000c5503000c0b941000c80e125040001c084002a0800c5001032892400c0812030341149402200010b610204050103208503800216103402e00c0302d60300d51148140000d11100401c640c4548002c10b08492040400c00c00104100f00300c014001e082c03007000c0241c0c40302035155610540c00440042d40f900c8500301301040e07009061008110b841035400300070b145989a001341158440a034115240c26906160702400d940314400c0321301050380b0a01499000c2112034115900c001c150941c0d44520a80f907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 372689370 1250 372688120 372688153
    0x91505040909030804170406211d0304090c0822030e0301020a030e06060904030927090f0204050604110d110c0706050a0909020903060406111204030e1002010b0609090702 75
    0x280b01c410b9003c11410000c12041c800d01c00c1c1101c92810101d51420310f0141041e4010b840c80b29461052203080075040c04908229603154007140010400c0c8601e14480d03011011030a0350703a40a8064110854107081c49405481d000707010b800d00483c440c402900541c00140c4e030004d0300b03556894054042100401c5407040648081c4000d00c1420314070364000ca207242c40018220b00d0110040c0613103010710340a0b0f00f04400f083c1e01840240c103440c2914921040d131250540c501d00c20000200c403007001030380750400300c0040200740b5403a904050b04c20341d03043c000b90343e69000304004c031100d250107841444400c2003a0450391909a00041c03510001e42c5441b410082c000068910b020126082000072030070014042c0900b80e00002072800420b811841076140ca2400030102c0d03258440540004c00180d20380d5078070f45600e140030056554400c00030840b91843d241900b00100f81618907080d00d40034100b8000315014142c410301540c18056809011181343c140f1031800d002d40e4080c003c111404502513002c144440021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 372690620 1250 372689370 372689381
    0x30a06050c03010f05011e180b12010e090c0a180609020705060a0b0603100303081e09010507030e030f09090603010603050307030e19180911040906150509070915050409 74
    0x78403a045948035810700100f030130342c0030702d43d084103051001c91422003c464503a21101510f44101d482e0032150707021130400b03058501000e60040020042d0219041c2d003031001c1083e41c0b90480e80802e6404c003d82c3c403203010307040d00d03a50300205184c0c111006d40301c1401100c090301c8c0d04070364031003280000066596030b0300c400c8022038003c00d42c101d6030794100400340303d82082c0b5030040c481101400c40701d06295041449411901e580c89100081c1403004840015801c0701c035030340442260015200041c075180c500307003990500170003003203a1917404a49400b40781074060800105803407030390101d007110510b002d950344200240b180000f01804d925640ba40c40120016100b800a000b6103403282d11000503040d481400c00c81c1e415000c030030f11000d400c2600e404001d4400515500c200444034501c0000704505581803488003d90644501900941461020010403245900c0345401d03805103501c03000c1d55a11103040166407401518210005565044244005440715113560f620012608009281070740d00c550703450a661 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 372691870 1250 372690620 372690631
    0xe0c030d030f2301060c03120204060f020d02030c0705012003130e0f040c0e0720030403150507090b0d0204030c06030e01140c03150315090102030123030a0b06030a0605 74
    0x1d0300c030056411951260301400400360310409142d4070242c014800c2141d030f50814803c4000b080400c10500e418140941018680804182001c1d0354a9484070b1000c2e01401c0d46642e501c00510a0f190040d154520200903120b41b808000050072038070345880700460760340000703100c1d031400c02c428404084c890b08010002445220013803503500b1002d44c41d140746810f0f00c0c040202540071401c0c40c03804010014400610600c203460102908803000d071039840e01200c100344500d461001c000b4040e0600c080c2d40f88000098401c40e4829000c1e03440302d03001a4458401c1c0c0340f080d00c1c201d0114060900512107003d07250090941c40000d800014201541c0741c98429101070b0703a50113080801e64960281c11204400e001c0c2002041002e41009103a00740744c0c110003c248001072600d020407000380400c41059400307000d1a107100000009403045c03401c100c0101e5000354400c0c49442c290481c069a000b0200303640801c9180e420070004d01404002500d91605503424078000d10903075060003089811400540c1600c515402070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 372693120 1250 372691870 372691877
    0x604080d0810060e091b07170c0c012a0f050115030c090209010207032a080325050601030201031109120703020306150a090911030303180c0105120a0e0c030d 69
    0x74102154280c50500154003c1030400c00e800a0f080c2c1e080c1c42d903120740c03500455840b640004080701c0c1d40c541002405000b40041c905400c1440b186004109103000d4001380c0c0c004001c4d00d640c038a07944015250500c01c0241007032040000c42c03200142203c550440c0c44094002e0752213241040384e940d00c240c00c42d075000040c03002560000c403040c0709002c0e1848041c80945104c0b00304601e0716118800103966007603984401841d92088041c0e42d5007000c5031413806080511600c00080a6903154a0026200d801c10070b002d2508007000d540d201c1000319068100c0c0c0e4031541100160849034216001140503000c54040070010b940100303ca141c464596010340d05841c104c0102802c2c5003030640c41010f08045c00504030f558524400d42480c1b2056403a0f011344421071f00e119400054000d10751034099403404417a600d503645400040200001c444250300700c80720108a40f03003038581a000c0354005441501580c51072188074041000003810391200350707202c0094409070200f02d405685003000040e00d050752145900000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 372694370 1250 372693120 372693137
    0x506250303060e0703230c09040603060501032013020a05040f030b10060206011a0c07050303040b070c05010311070308070e03030a050c01050a0903050a08070909050f0609060102010c05180604080d 86
    0x160f0220505643d0403c645150a008130f403200e04c0900e0260101c4004414551410b001040d06030580800302c80e1019409801030012664904241c00142024401070700c0140c00303181c0100d80d070740d175a07120b141101c1c200600a844203010038054000a4200c030b002202403000c00c10000c42c240058454180095214903207003030b081d10b4204900701d5032000c0d030751086080d075000d0001400130a400c0c42a41e44411b040e000100c0c0c0700c204007080b0a2407c25075030700844d014040080c2c08506440b41000402141c0c1c041c002d441545981d03140110121615000c8901611006010110000b8070603481c7c0ca401151034901160003a243c60002803e40d400203100f18049003000034503010040d4203028440c1d0000c01c40c003040141c03203155180a0010f200364503102003004a00320001e42e40600480036040038028100082081e442c1409448a03a0001a00c8040c07146900f8000501d01d98414040c08104522598450781001c041c84000070a210306c03032840c240e00c5241481f0200b22102c0422500d0801c400c241c2c0c64829 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 372695620 1250 372694370 372694379
    0xb0402190215010806070c08071b15140912030706050c030a1d0a0807030216030c090e03070c0504020f0c03030c030402010e03210a0905060d05060a0603060f050625030306 75
    0x640000e8440b51480100140d00401070007030007007400c81e44543c46040c04191780b809841d000d0b40c1d80c490034000400c900f0a200c840c80c10150b682c0400c1080e00c6846e02500d1305040b00e031070241c40711100300d0b01d00010000c041101d8200c60510500908288070301c1000c0740d0805400fa0b4428044d144222841c0d100c0358804010000c0b20351003805001d101003680030605440d070307541e2803100e512091031050207480240300042c40c1040601c200940c40c3c0141c501c1d5503131030b651901da28040c0c040e5140351147c060304504128001002c02c02c04022152080e602520b02209070745400c05120103504002c65403000d055042c421150a00c00600003184510007404540d0341d00c1c9030920002d41000d84c00c410a90081d0301003810a205e4610000745c2d0082411020103990b111802c01d2030841e41600710750885a0001d1000c102c211046459802c02c0c5c0c003c036030844034400a140c0b540800c8040302c100d44603121040f000c003038040015003480f40c01040b000c040150118510402c1041201c00da511004040300000d41d0b4400400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 372696870 1250 372695620 372695623
    0xd06051e04061a03040f0804031a09070e011512020904060303080a0e0604172a10050a18080d0609060b0a090909030525020919050a0605060307120b04021902 69
    0xd0203031940c2001a040c0c841141c2c806031041c007001740010704800c8402004004c0c810b0180955008642c48082071807175400c4c880186410103030942c0d11200c14800e031400032604818a01209050b5020402420a0300403800001c5880200c1110b2040500354200701003521a16107005000255010b91a40c04031801c0501c000f0044858103240000e45421220500001501c1c401c40c50022502102c01c150300c1d8012280c01c10181d410303501c5071300514051503040005400d00810847c861401c0400e0170015981d904807035030b0946840a0040d440290141c1e038a400050b00135006c1c00441d2001140000c82d5034403451007104980c110b40110112003800314001c2c980d0381e440a880300242c04550340a10001100d550080d003a0b0184210345078212000c1c2910400d0144185c00d08511345800520b4a255030a20803040312a40c0e0034603542150b80f50400001034420b100a0069100300c440180c01b440ca1680c1d00401120308002120700c160441d515a140720010f542c85e0700103462403000c00c41d50194604030400019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 372698120 1250 372696870 372696881
    0x303210c03370218031203070f0503091009030c05010b19060c0809101e0504050603010b0307110604030f170402090c0a120e03090918120d0207080c061b0408060c0d06051e04 76
    0x1b00c088260400411052583c065203d143c43c0c00385080564070303600c45090f040e040c159100c50340031181e481c00003208117042d8032090b4600c0300e034020380007002807040c600b0034071400007017007030300707119220b1640d9001c00c0701a10842d80b0314815400340c030100c0d061074201d0000844004006045c940019010b1080401043d480d20410003a07e4084c104180f8140c50040401c003507000510911486000c080300040025025401030b00c28a01440c1c10354020b80340a150240c25002c1545485001071400c800c80310f138141a190304030b8002c0b0b8008009141d9135035a0f00c00950325600c06d9510200301700d007910751140c0c10003507806614002c068510240d41c403001e410092299081e002401020030000b00c41c42c8524880e0042a1590365070782e01502540d645a00850310300c06441880d0b03009200300f00004191601c0ca101052a03030003502e050040300c1c40000b102c914240207004034014009581c00040105440200040c014440f80e5441c42000c80c0f05603440f800102d0811010f0001000440c0301d1400010f285818403d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 372699370 1250 372698120 372698143
    0x20405040c080f0f0c0d030509030102030a14090c012106030506040c030b0c071a0702070506040f050913031704020a05210609070807060516020303210c0337021803 72
    0x500021804e440507950710081e0f403025070b029021000740c00c001e051164003283e464490280003913689060141280c030040040c00b8010f02c0604e40c0344d02240c40c1d600c02295403103107c50140e4850340b110103407044440c0b0020108c00c02c1c95256698250020008405201d040e00c11801a19215012455030400140100d0003c0504040d16010090311700000c03c0c1280c001d00001206d24240f0699403a80c40c280d280c124a0341180b64000c0021500150907540700138004144c50090320001c103d03031900c81c02981aa082a0001800319840d004d505900c2d54650380b002e5813040c0020f1129503038650719404116541d5010140d0204d4440d090014030301c18104000c1241c000d9490001403000a28103000700b41c403030205000d41c401b00301000500c0c030304c85120301015030a00d5800400346d995581c0b4410407041d000201c8210030303901b20074010010307040d41c074540d0603680f2941c00113007413a4544000f40e56021408a0328945240d0702c501e801c42c01113452100d031001d40400400c140b540345a004041c006c00d807409880009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 372700620 1250 372699370 372699373
    0x9081506240d1407140c01141f091419020405100507021e10031a120c01081305060a05070219110127090908040305010f0903110105040b1504020403020405040c080f 72
    0x14408003e921641401200c220405039036101ca042c1b02045000d8000c001d900c0380c6a10070401801480d24114110b569405140110403900650b6250001d01303030f500410700351844109040c00a0007200600c900c865405c024500300519290315800011702001004008000003400803c00d01d0031810300006002083c4e01110747d030310342c0e1024a40020700803012503039914101070300c50b00342e50305140b5140031582c201c000c010443c00f90002010303025640c446a8443e907070700107803004000c180d01c4d11170107043c82115600711029001564441c05024003400c4040c00c090308500c84c00c15402c424803a9404c6505055105d0410344140115031400100745103120380c85803030102001c4680010056270034071500c08031645c102011844010b2400c080607980100e60001c1e102d0750074400114080d101d5580405000e0303209458800314150000c00d031030f00322002207c00400b4658141c0104510301224003110904140080c80503103065181e5010500307a03641610211401d56100105220003402840207003102c0f00000f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 372701870 1250 372700620 372700661
    0x1103040620210d09020a08010203040302010c0504080d0305061c0c0509060103150e1b13060906030c0c0209100b04030507050f040c140702040908030c0d060609081506240d 75
    0x4040320799418074074110002d00038000525940d028556048104001e130000d1175480001c1e52903c00d01e010b07600c100d400701c00652030729420340d00140c0500141c074103444040000745030500e0700e00c50540061502421155012031540040070b8410351000b064400f06100b1040b9002c41132500d800e00800c141d000c4c000340c0c181400c0180820070051800c050004480c40ca5210354016280c00d14941c81705003d201340840c281c1d500281e40710000340000d04840c01c840305903071520020b55a800b403c908860b0041e51010005204ea45840702500e0401d640580080032040d42030340071580c2e07100003c0e0552180d8030031551500094003c020a10b49601c1d107400204082d42d09011030030b0010300c01451140c400d0420780142002190300810764403598403242006070700c05203665990916281c5542c90b03400c1740009854241c2094404505144500050400c903200b081c0240070b540400d03849039101e0480100300c140c129544541244142507103902d0f541082e030a0f940c0c0103641c0d0311592098820354810380b44122140c030420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 372703120 1250 372701870 372701893
    0x3060622020712090f0e010b1c0b060a0905031e0a0803040f080d1a0d0b01180f050f0f100f06030222080c18150607031103040620 57
    0x4984800311811580d00c40300560010501800082c011818050503450804110507078194101488130161219440340707901c203550715102044a160240030394081c400c824003902c1d407002440141d0540035100e08078041540d100b00004144903401c207160b5500068011513040081c0d050030b0000900362405213252110042c0d611307000982d01d11440c0c80c01849650700200050a004100545005040d400480d495880310141030f0b6102400c00b41c2c0005010f5221042c1011003890a04c04451056520080700b091a0303207811050500c03070388440f482c024800d40340c03030022500340c00600c2068410b01640c150f211103130510090340e5550702c00003421480d18002240f0103008100300040300004407030301e500d4090303502c01810961408142c0301d43c920000c54500070078081040c01e00442d00c0d4691500980b00361560102c10700c2d5040703001c4419076652544603825a217213078690078501c0007032101c2e5010342801007080700882c141303a2441d40150b000000140010b5820250b1040301041100d4a0840300002c00024080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 372704370 1250 372703120 372703129
    0x615031104052202070c090c050c1c090306020f0c01050603030a02060c07030903060f0506031606081602120c0a05120910030f06050a08031c1b120f1b0e030606 70
    0x3507015043c41800c08070a40260841141508001801c40d15015034888650740b0f07100c50032280074002c4607490740c106180800e81d14881d1003074500f0b600319080106003d000d40f102c102071039940080c00c03100300030021101102050490004001060920052640d591100010b007821034602410740c500c250003c0156624a40d0300091464100055071181a55179480345420744c2c034640280d000512560828540348511501944441d120385001c0e0240c0d0048410641c81481c590042d000354404988400e0103c3c1c844102004007401c444950f00480301014002c030300c400c4842c0c1000109003415880740c4001d10800c02c1c14021802c0401003070000a003040c0c40a8002480c1407503a044141c10183e456810090440c04c079082030005060150141c2009030700d43d81010f40f254080074502110452445100c80300d03041038031410418500c104070f01c240356810700c001182e13403102c111040c1a6140e210445031141030042c3c0315801e14506200e2a10100040d0400050048914203903480d109802880822003035485 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 372705620 1250 372704370 372704377
    0xc0207080622020d0812010e0115030e01110c070f050105030103032a020a0b210f0c0c070302150309100c1413080d0905132009040e0a030306150311 65
    0x1d4400d00d070071180c0110b0858084a0440c0b0406507006014403555000c2c00100d5004100d000c90006842180d0303a00c41800754500d6400b81b16002540403800c052900c8036110b580030450f20140400007066468403201007a141340c00550903451160032540f001c00900120038583c0008050a003001815589941c9014000a2007004c05000c0c04c103034904400c1200700f0b54410360181650003804014243d03103170180c0d611250004c03c40701c140002c180d404044c07005402e24203d481102d01002e8606690394200c1c0c0d001403074100590a100303600c10944040016600d03c2c030284800700a179002e9030349a141241d081d038a885080c401d5034000929042101c601a9845009402c040398602c9515075501c030750905101c03038284640d05c4004c0c81d0213000502000c00346e10036900340c115030040710740b18440020422080101e036a0b03001c0c0b00d00210800c2549228844486024100f0260020000101988003844035820041c00140440c0020fa40381401d00800c115440c1041f00165986400c00c101c41c81c6540040702480f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 372706870 1250 372705620 372705631
    0x1308031506130801021c14070e06071a06042f09030708030d020403020a050102030f0a0e1c050a020918120309160b0a090b07021c0302031902060a0c02070806 69
    0x200e548100300801e440d0700c1c0803210401c1d80c011042d00306036036907040e8078002c0d00540d515881c0c10701c1c807622090260303a03c1e00444c21010014000c401040e201d140003690585001d18400d500300d03509106e2400401d0041e44040d0322100010300d020054500081040102d86419240750a070070080e0350860061600c46180122048100203800e40c1c0b1000c4000003482c049985d0300050803071000141c2c1411a4265401070001c89100f039a007011a140c540f8016a120301940303100341c828040c14041840c46070302c686130100200d0f2005d031841c4981c80c1c40040c07071441d05150503800e594560000b20361008505140074283c0e03202c1305d1600c0544182c841d04686a484140d540790b40c03901118080045221000c09104080d418501d08842124442c1c4c0e4642504454010300f90a10200d01c03211400203040003088100c51045500501940030b40041c10000040c4034081d55050302144401d1150710703840c5007400d01c610b0003501e00c0d4006201c14a40320040704160355400340e40714210341000404208001c00041c0158100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 372708120 1250 372706870 372706891
    0x1e02031006031e030327110409051009020a0f0306050601140a0903020d051603030807091d010b070c081e070906082a0a0303080a0b010e06090d0503090d110108130803 73
    0x8101c5080440180400c1c140d10300326105801d40c800c00011044408006c140d10402d0800503440c50042080100c8007000030152454001410305102a055548107205280c401001107001035150100340080341c400c0e0f001210792598580a000003980c10002070003180300c440c6150b07441c213032410a00801c051040d120080c0030350303d80c50034041004400e2103814266200300d00b8078140941d81c0d0030300800c0203c1c00d0300c5040c085040e0359008a003094013030340c1ca20320100801c0700b00389850b4a0002c20003110343c00f0f10340c10f460020700000041071403102030042007115220b08441c4c40c06280200c04450030b050f15980f040d01428a080810007280034040ba16a514a00c241240400400e0228444190700090142c0ba944200c92400100402d500001e0882c059081032100b0499a9a0039005507412403c6202540e48500181320541c0e2a00c0c003038001c41a0103108005803414200508013154103800d00400495811080902070046941e03c240c00c141e212203064117424024089881722109840040c0c442600d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 372709370 1250 372708120 372708173
    0xf051612020d020d05070c03140c150910060e0a1a090703050405190f0c05090702060c031906031406090d05040506090406150e03070b07050303010905131e0203100603 73
    0x4007070b00d6030554682555840d0141301e18501003070010700f8068119000c4012410669903003a44414460640b07108122860007000a039448520000c0007603001002c2800c07600c940300c2c80114204c8140a080e0060040008000d0036090540218040d030300f02410800845081024007a41640c1c2c0c03881050700088207050000f0756031254144981012000908000704280d506c1451040040040d100403a01c5e004024410680e9111010130906580c20744000005900c40004901003c0400c401150003080120400714540f450903050030a40f811a03005661102007000c3c0000c0440b0b00340310155200200b440034107001001c000f000b400a00881c000c0303070300036100840c412440c2d131641c4e80322001410700c0242c00c01c1401c62041d0024508107000030300c0380c00307402040c0000a43d100390906442d00e10f0740c090040c504582c00e2001160044c9801803518001d14140380c4107001091001c404043e4a2040e5044581442c0090060503c1c04101000042c90782e494101c0030000b240c50070a070451100000b0540c01c12 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 372710620 1250 372709370 372709387
    0x509060f13080309090a0203070f0e040b031e0106060e03070303030e010f05151302160b100f0f0e010803090619030902060414010e03030f0702010c1e060f05161202 72
    0x780a614095103468002000108000768000060007601e401141e20074a155542c0c0c0721502a40015500c80000c00d21414941c01c210740911a400f0b40410081c000007980401900002d1170720071041d40c610340c00c0d0b01d0540a15000302d02802000c000e44101e0500b50038044000380426520b1000744409410150346e0300048540071001c7d003244419041022092006042030f42244010883c0815040d01c103940103103070450902c041b03001f5207035120059021214220368944843c604204020003002a8000c0900086149480402c422001e400c0d206650f0300702c00c0c1041c121112080d0f042c1c000c032030783c0d600601000c00c40da600e050460310126081c4000f4400080d110a080c0c02800c126400290301c124080750105c0d14026680900c08118000d81e80d03051801c2c02a0141510381c03044010082c2e00030070400100300554000c14005540610070ba1400005001805100500c03c05039081102e56540340c15040e8a20102c90195540001004095240048008202038403900c196185d102506801081405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 372711870 1250 372710620 372710647
    0xe040c020606100201060936080f16050607170711030703030e1c0e0a1a030f061c050c0f060307090e13050a0602190816120e0d020724050906 62
    0x3001850010400e00034148e04000400e5104001940f0b2840c039001c3d1072076000c44800794004400390740d801ca9a841d24040e91103003040c0079980219031401001e0021108803000800030490148180241c1d5511a030542c0c2d40062a074004078094820410009851003845070420044100d4442d07680c14140010207a400d608058200b9003001103003c00a190f1610b0b0380300c42c0b07820110810041e10111804580644c0300c0b01d40035050440e11514101c942c01c00c0c40018200881001401e0f040740d401408111842d030b02c00e07540d0301c040325034600c2100c4d80d0708049007190070381c06d08040b80d02608030215500c1d0308620b05503100811041c6a80301d80190224440c022480c403815401c2d04040c0c0c640c100c3e094600d00b01440c202403000e984900d072800c410649000002d1415486440c419009070360301c050080c10b0740c0361311504483e802445061405400d5592175845d40c0ca2070200040143c2215035009081c1d0b640c5480d084080740b45181180790442e407000e203500b0605d20362040071101039420403254140c403403c1c00000c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 372713120 1250 372711870 372711881
    0xd0c05040903031b0908010e0d09030f0201021504110915010c0f140d0504030b0115050409020c010b0402041e050301020a0e011d032409031206060d09020604150e040c020606100201 79
    0x1e01d0b04a0304c40c01c84141d102c602c440c15a0108002881803410510640d582c50821220000006090340070620000d076090102c91240e900500c100c1e070b00241d641e5405045000203813011118000940140b58680c10503181180e44044d403c0104041c0e9480c0e480060b042c0c101c4808010000568822900c1c02c0215560b110810030381c5080c2203036001780d00d1105c0039181d81d209001c240c03401e4107000000900d002040140109505c0e4640d54103003010302c3d00030068065048640f00d240c155484031041e441a440d00d102620040c50341d04e10803140800d0480505000360490b0704800c0c00780c0d00402800180c150094002088843c0a20f4085184822600d0a041c29800c40766070b1070303150003580c400a07221400350030686ca4180d0848001495504e850543c241e036445100206505409030900050039803502a002c4c1c204d102d0f40d52000714001d18a1ba0010b00340b41d0250b009030b10542100500680455840070b201681500140c4041000c400020400795850310010f020901c21600c007407621500780c0c408e4200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 372714370 1250 372713120 372713141
    0x604170c0f06130c1202030c010f02030904022b0603081e070210020114010b0c0a06330807050a050a0306090312050403172805060102010204030503041805060d0c0504090303 76
    0x2035841d40e00300660601618044610240c0d605610f1340c101042c005551034428105d29402401400c80c0300c0100c006440c48040d450041c0154001840516450784507400201020304840c0d00000e21003400b0200012945900c0e4410209945010030a000180051040752041c0c0c11480301542c1001e914a5410103502c2050030003900150103540003202c0c0d07074054000b070310741c04004a041c484c140e0f292a40d200640c015072540e180c0710340c881012080421150340c00340c0e0016507400c40c800d01110241c01e581d0b20042c0315181c250b10881108804101c0081c1c2444000050941210304004880c038007000580c2480a03804060b0a00e079580f002c080402d4003031500c1c2e49071030103c2a014000f500d0582000750100ca650307004100b1096669000803130800041600020402c4280c10780566030310b09402e0b54000704402072120741550b50800000c808258100b01600c002c15820074840911055000c056040d1500503114501601c850588040015a128104d00913079805803030006041d0f4450070214098510b000d103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 372715620 1250 372714370 372714373
    0x708010302040f3e0703020604110d120c1e05071505160602120a110307031a15040807080309030703120306090e0a0b0f09120306040204030c080307030306080604170c0f 74
    0x500d0b0390132032a04400130056940740c58014880c48070f00350210440d2084000c0200180c02400000e030008101048070a0500320240c201001c0c01101d9039400d03c0c28903580420700204844060110400c1251100e0f03030b004c3c14160b445100f51107010358905550360414002c5d02c8190052075110911648503405076000c0c4200d4500c1d000d036402e000d050101c000d40c002c00f080720618541400150700c400c06400394081880c108005207203556a8940110700901070400c920032244280750045903030f661864582515030070718282c1580e84902e4041e81c00d1820f40c0651011f0501c1d0010f03c20102250340225840f070449030490004010034501007003c90041c101500898031880c90154200c8041d100000c043d980c0324440c0d40350b02a00d80300c2c4004905c200200f1036607200390398414a000450388488001964014001400140c10182c40380e642941514098015130003560020580a05040e0715010740d42c000c1c0300c040098003540c2042d171926002103c0c841d0400c2c038100400107946402031000c01410040e08000070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 372716870 1250 372715620 372715661
    0x92003160806010305040f08090a1e080c03060105010522050a120b0708060a1a0c070e040c0b1806030603030d0e160f080318010c0519140102030708010302040f 70
    0x101550315100484158400503001c0c81c0040c0b01035020b84110303400346130409091301c1403182555401d00158400f4203071a40000044c0400504520081d030750940000004540c080c805042480c01440c010300c03106180e1282d4880c000400007a41c01034201c41500c04602d80ca4007443c4001000c05084c1045d40d0b0045400440030800000e40c100300042c0d85080702e224030001d103142d03110100105c3c1c8000303040e1031040d8000641d04080180c4030406841c8865070442d45080c0e818080c1018056081c50110391101103044110700802040140e03070307401d800190540c3c01d4101e08081c0402e01e04a5500e1140c08400d00800c00007012410b25507007081545c01c00c8443c4401409084000c20080d61900d403048804041c0315900c130307000b08452200039049001e64445034000c0d401c05d4100419460140e201d2420707a810b02c07007503980754402b00344203000541270780c117200048001e50003492401015644111020744200e03403040c0184003c042d403010303140b41140d030104d0380071803004220310510000340410203d08008200d080f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 372718120 1250 372716870 372716881
    0x1b030403020a03030b0108090c06130e0408031501020a151a03030c1f0c0e0402070f1a0108060a0207030215090f0d020a14010b0d08030907050d240c09092003 69
    0x40d051200a03c030b60f8007032280c0c1d500e9900544500b501960104804e0704075000b1142d02d4104203003d004000002d280c4601d05903035514036210f1078901518240d503500d200004003d10f80d41c03c2240c010f5584428401801000125268100c01c80e0100340c842e08043d880d6808508480004200d4003403a400c010248d0b0359039603020f148030355520014000c108540000b16455024501544151070a8150303036100e5400310160841004000d40c00a04100d880010b20201080420038100039800308085e581061b106c0c5505204103903140000007000c100f2810300402c0101d00003036003c501070203107208000803050680c480e00502e50034414060f0360b0007028454024002e03002a0300150321070b4140d01400100611007a80c020860a172400010301c15000398010301c031240010380e80401164841c40d10400d82e0038050300c40d00040c030303500b080c800180c035042209042c050303605101c180040c00c8510445c1c4200b10070000c01001414104141c4036060742c035580c40007649028201844801c030040c040380407195480c07421 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 372719370 1250 372718120 372718123
    0x4030b09010f0c05044209031523090109140a1406090c011803060204060e1e0306070c030504050a0e10080316021002010b041d0f010618051b03040302 66
    0x30304580342c00340703080c403003c1244903028408540c1510b1005ea010340590070560329000c2d02d04403184490092400f41d03950b160703800c00a01e002e000c0d40700c0c0d203549010310649035007042c4000400041c00702003440c1c030f004200c5410a4002820b01e90103065910800e010f5651061658018440b60f4409003404801190300405a4404560080804c3c8a17420044480c1c1307056810365a01c010480d545205a030020305511030300d6001d0009010720425049110307035019281da40720004e80c0c0207a848100807841c0c0280b0414145401c00507190b008800d2000e041148140d240040e0b66803102030159010b002e140c0b03001e0014140b05800b110003030180542200059035a401c8203000c030200c2101d40415450b000c030400700304040040102e80101d01c0c40d40031400ca40c06c6d00d40030800300342c3e134020031a01990f685242c0081d440d19240100701e042807581d00401c00704650882c1003400c112540c40d90350f02c0c0e64500030342800f410450700054083d01541d000000703030301d0b070399103001650110620311090440300010041004041d030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 372720620 1250 372719370 372719381
    0x20a03050c010908061909051c1805030a0c031104150e070f091d0a14090c10020304050102070b09061c0507030f05060d0b0405100204170f0303010609030f020604030b0901 75
    0x40030f90b2604412030340e404a56403110b406590b03c201034260364000348007250f8150040392009015100742c8011083c03d403488c040d40c911517000340005c9010584062286450001c0c20001004107802030815060650303141803914800340002456030701c4603108098030307441e0740e485403280c0c03000405425411910b8000030290030030110303046e600144001005500c4140310b050700c241200c54461907500101c00d1524480022040280740a0200b655840080d03070646620710668090500704001e0320049105005104102040307804000175944204030402650364009050350450303046050440d22265000001441032040e040c1c000080840d00c1c0801a180c106a80803500803030143d01c0810040f040c014280068500841e2143d500203445261003011070311010400ba4051b10680a5502240030a01c1c841e08030b800a0b044021140b051888124025400304012200a00e00710300030343c115031600c91b000700380c0d01950000900f0614058188000c40d20361100b07442c05180d01040660342454045001402402e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 372721870 1250 372720620 372720643
    0xb07120f02071b05180a052d1f0605040501050d0b03010507120515010f0804030917032a0303010b0a02030c2a1012090c03051504050f07052b020a0305 66
    0xf00110400129441c2040c803550744d040c1458560324641d500c81450314024174004081c0e00400c40b411105001400441c4101903c80c038500800c05030381e08080e440d0700a80984103807220020f2100c00d10601c1071540000c1a00c08940092800682d102e0341008401c01400c41d00402940540c00d00c0248441981c20800f2814841d1880c01d0810181d501c09400889070840e01200d03d01161280fa8000012031082c01da4650182c001c0c140007446070f550340034190000e4603401030100d283d0404941d451070800d040504400e03c20103455031440b903001d800210f5031a8881882501d000910000d10200c07007500a02c2622a0160080241c410000842d2180504030b01003031000758803101002c40040c0c81d842e0025a04940c486280e44040307540b48141c1003100102644a0241c400710141040000015800c03c0310760318103186100412528141803400c0c5241004c42d524400564000f050300740010744440e0120200654052500c4031500e11030510744d4801400400b020b5041002d081001c01402000a421061300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 372723120 1250 372721870 372721913
    0x81902120f090907140301050405070e0a030302030d0b0301090b1f03080a090609052409031f1a0307080d0f12090606030b0c041a030703020c0f0105070311070b07120f0207 75
    0x40e13450300001c50b40ca1040d4010741c0401c040900061005003001c1d40300540c85400d900f031040b044600800018000d41e103d6004400590000594181c40d807110f0051107503419094000b0f01402c00c881c1e0741d0280b03040c001001c442c6a400b803044048034002c2004002001960809d0a071980c540b0b190030000c0000e0590b00440b000326416100c00101030901d40201c40304031040e4030000c410482141002c942c145d00c007051031903040c400c1190385015000c1240d084009000c802c0c1c40010704d200d10031030101828401c00b01d1a4441e40018900300815100414184005903c5103042000300e402d081c0c0594000700c4002c0401c511500d85a0303400100640c42e48560241d034000c5401341e6859a581c0388100d038502c2103000d04010705550510205501007000040c43e000f0314207040250818504003962840e1690401c40303059079079102d030305001c030080d014031421000a4414486a1405281e501d40c1100c100b0040c01150400c006214002001c0d40c142e403050902d0198070f00d00395542d00603030801401130a134001168115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 372724370 1250 372723120 372723139
    0x7050601030c23010e0a0b221a0304030503042904061a010e010513080105130b090a1106070c0e01090204030b01050306061c0f0b011203110a081902120f09 68
    0x382218580401c02e070080803090f500f0302d40032000444103c13805407040c5030807092070b81000c03c2002400020300250f0581642d4007030240d440181104003a08158408074070720790003650b103c0c01054080210f03030f801501410a5a03072074840c2e2400605401c00b07a4580c500161790707402100300040c2c803038100d140170300e003c0c240501c00071940412440b50b1081e03544109002c50441d40f02054207501810281907003181d00b480c0b0760640b030395462950b825100c04907499012032200300c0c559130405c2000c42c1d1090300081410001c00b040d01b402d590300c5090880000810344501c4002c1900c40812008420040103455080010961707540e503420104080e402500040b503682c041000003244c507041c001050740c802c0100400021241c0380c0c5d21018060800c2e40c0e0b0702500e00912401320400840c0154044c80c0c002d010a00502000f04c2060400801c000880141c0030314036003040341e840022503892419120b0340161040a41c0c0f80352070400e0141e141016003020101066408620f060444540e00040c00300014142c544802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 372725620 1250 372724370 372724379
    0x608060112051012050a060203070305040201021501030305090609060c0a0b0702100b0a09050c0c07030c0e0c1204060b0d06050f0f010b040f091a030f0106080106092f090607050601030c 81
    0x10b440c4202c58010b45544281d00801000104203061040075014000740e81c108100d50300c40d801070740c0c01164241c1c042601c40c0144011542e0401846041036054004810310794116500102240300b5084050303c80c00340031602402030b82c0c680b42200c14626950044a00c5590707207250046450004951081c09802180b1000c0c8680410340640c0910b24001442c4006050400c00c0b608020080980304a40700c0b80148001c0c004070f023003005540003842c0a1444d40c0350540c90201c001200090003010f168074103900303211030b00c4840355a151190b002980a50081035446110020440c802c11840f0003815090900742403110607441400d0300c90154140c01040c980b160703203d2003034181503c180d105542c0c070400240d40c20401124540d0141c0d820030020031500464a00c540c000030300d07110700c80e0764184450350349140c100400d00d401d200f207800401801070b00340070100c2c22048101c00b00c20a80f40d402001d0704032000f4001c0740b854000481d0005000103200984607092420699130b18402400b08070741040400c2170204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 372726870 1250 372725620 372725657
    0x1a09070c0b100b03160c1e06050711031905090d0b150303190503060406050d03020102190f021f110408150a05041e020f0306011d3d030c06080601 64
    0x1030a0b43c285031410380c910380307405100c0460000c4041101082080c00540800010520b45800101e0340c524011200e01e192039003040d01c116840900600c0c203009030106c0d503100c0300e00040182d84000d40d42503a1910102004541600c40f0b11528144035805203028156804110308860054012040442c9608043c3c0c460720515940380b09000d500700e482380710160020750351403040c001140c0c40380c03000d000811a641e4400c041507401c4003040007100940d4000c40d454080703070b01d13030486600044c009141241c10410720b640080e4803000740410018021014245003100c20200d604034008038105581c90a40c1d03240e039020301d65240c14940b800094030111032030118102d50514042c460084d5081429048805444040718003141c502d0130040741c0200b03c1c203d0745a1640e909120183c001c014100c44500022009801d0140200004103e5884140c0c440c078040c2c1c03118119810451610042210310f4220311441c410710310142d07200e07880240721408040000c1040b43e480054039001d03450a880e6981841c0d5000301c0407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 372728120 1250 372726870 372726901
    0x241e1e05090303130f05060a0e010b041505060d02090d050109050d02061b03131407050127061107180b0901091b031a03011b090e090706031a09070c0b 66
    0x24030a5481440410302104c40940126a014440c038503944402d8215500c3c203090503400c903a45503a042d030310708105002e0f0301c00780500c03d1086002c440402540003182d07040740c0440b9041c01824081c050205001e40e818400d0f904031b800b00c0074001d0240c28111000c1ca0128060b1009502c101d070f040c010948140a9240005400d80c054010140c000000045401940010b600000c1580065004881d040700200e813181c2191105420041c014010386801c1500162054291482c42c1d90600380141c01a03000c80b88190305075040e94024600045000c042a516a1801d41142c2128000703100040704503100c0d030341d980e04c122a1500241c0e000011a0303650380c101c50403505000c1881d0001e40c0054a1038104030320a03844201184a0038400c05040c40d030400100c1c0c00c582d046107003001111481c918200c082e58100691a0081440e040020032078038010380c0050703e61415100d8101850f4075100f4034810a08811a0800c1903240a4092600d034500040010121201030305e05417807071400030011441454000614 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 372729370 1250 372728120 372728131
    0x7150f0e042007110a14030a0b0a1104060302120601030618050a02161b1401050d27030e120c0f0105090f220c0507241e1e05 55
    0x21010094800c03410300c40502100c6101d1280311103a0b9620300765040d80300025010050103075895a0881102800348008001c480e005906088040000b0b0242580d00040c07100c822580100c0d515070589a24481d28060611088160704024011a0100e10b031a03150303020302003081c081010300c00310f51900702c019000c0b40d803140281c11216070070310061306040c98a504150307001100407038014544502048910400c070b6510300700b1644600e040c0050070031040250105000fa00d105178030303440b59400d000000b900d00e11074490040c0c0c0494480d500601c1d807034003420340440102c07020b40044d0350700c2d80180350050000c45203044045c4250500e459260361300d4400070320a01c02400c00307007607050800712510054030650400311210b64000d130124160041d684542410303d10344108806240240810f031150b0100751902e0342180c0040140c2840b1840200c0c8042c032083d440b40a08261a5030340c20041c0d03007540c0c0508100c00d450045410440d441507141c6440ba071142c0000b2500d21440720f004a40b0f4015401a200260745 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 372730620 1250 372729370 372729377
    0x206060108160c0512222c04030905220516050f0f07020301060909031202030c040b090301231005010504030b061017010801050411030c09040b060409050f07150f 71
    0xe0004000e8060700c000c0103d1070040c0b085a240500c4040b54440d40d0f0300c1034681c000b0320040002d00e50148180c40003c02d0282c601a20034041d20401341c065104112107003c0c0d04070840d0301d81c00114042c14003a01d0400050700d030103090721400080f04084440c0c0308046841c14622181341c9400281c41c042d402140c0904007200d540c800386003011201c5215110f03001403a03280160312081040800680e400d12810004200705100410318009604001e00070b00c0080540761000b600410401a1401d40f035400c0b2400d6039507040c0940d40307030101040803d00421005190600302c0100701c60f000d01c19038007103001c00e11404071844180c50a545801c011a558010380c44014061690803000c552640b03803c6031544000c00c241c0c0340640d03004003084a00702d0340080c20b9014050a966400600c014848a00c2c14401545801c0e4002c19040c10b02c000850001d420040c00901000100c0001c03c02d5070b0341c0c5412802c85281c102d0215441081001c5a2a488064034400c00700116001a06070392030300d000e02d184441c00340c003d84 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 372731870 1250 372730620 372730651
    0x40b07021c031e02010608490f090b270409050309090c070b04080909060109080d0e01030e07030b01090506090907061404150e0a0816060309050f0601150206060108 72
    0x51046501e00e03c0698000a5548845004c1142281000303003000d403212038010b44410341001c6250b441c1503030f51100c005059201010b00101c42c01c600c0624003240c1141031a24007101003c0001c21115039030560028601d003840081e4824080c0856085070711124500850b2402c0400c0b50b5040100300c4100b240c2c02080d5800a0041280502d808107847e0351029220a18624103645c2d0350391000c01c19000c4400b1070b5030b0303031002c5401e03291420027401c400d0340141c0c2803c000581034200319140d40d0fa450500c1800c0c0401c03a8407180f40b001644a0342003040180c01d00d07422103070920340b00c1c50300100b030724024041c00c010646418005512441c180d491b4a015040030f4028152490030000219142400c2c5140745604000410001412800720940b0190f004840e41d05c2c110310030a9001007254803059580100001c0d0300051304840e024031520140d90440b6840d040010f90a40942360080c280303141a035941c2618000c04000080505640d05c03c10281b40583d07090310841d0780d4400066441c40420b803041100d221049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 372733120 1250 372731870 372731897
    0x7020109210b04050c0301150806010b04050109170703200315060604030f0f021309050f0703051b1f050310090c121d010603080d151206091403040b07021c03 69
    0x2001e81c541113400745064802030303105000420300391b8a0b0241c00d0a030164a07000c00700540c2200340041405001200d04007481e261501c4002042d0f050140074805181c00040d0740b8000e1700900700032030740086a000c48480b56003052840761016818111520718000c1c0100b00c181c00303880748070001c032034851007000300603604090454a03038032b54480000320b084808a4110304614007507514450400e032400041c41001c24501c0c55860900c0c148101c50040e03c0844d8820035050002400205103159601c0451035100c1d10030760044001001016401c1c80b90300c8022880c1c242d05001031303128004620078626051201300095540795a078084036144608400020b408102d4603401c0e15079900254104041c2d104a008003d190041c0d05085a415500c122080000005c88410b808a80d00410100d01d80502051b00b49074a007242b40da905000e441c4e07009000583e50040d000c100120461502c0f620400314048a0300c1d039444105885050f403002a090380302e80c1d011680d4070450b15100c4055440c803a810303a00c81d12400c154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 372734370 1250 372733120 372733133
    0x90103030522081c051e130806090a110315010f0602160e01090b060705010c02060a051003050a1205130e060301142404060b0706020d050109060e04080c07090c050702010921 76
    0x401c4c201010050304102030b032544066002c14115000c0d07a1000700d581c0d01500c03108002244407550109042c2e41000b030800800c42004901031241755001031190f100700d641d4074002410616180c462011074030106002007040d0380c60600c550309a038929021504880203c8034242c0e584549072040142c080703810300c014000d10388250000207641401410450500150307982d03190a480c00443d40d032006a000c43c082103400c021303a000d4983c22800c400040e912137421500d4032500e4030b0003650080c00502e0042c1600001c0c0c2e02c00c50449504d5145005005481500c4500b84c064850056411034802d40c03d000310400d0352a0250b0086003e80940070f940c2d00e40081c040c4023500300312071000d2802e0340596a103200107215020b0030010b00e00144104c0c001642d40c03640c0c510900c01c54206800c800e41152802c0e00c01d100200c451a01c00350000c1d0403590058441c01e010361201d1504c90940c000e1818507062482c503213020b50b0418040c0480d14404d807950300403682c8400041c1a01040328400c424032520a02c00c1c0d1000c60701 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 372735620 1250 372734370 372734413
    0x80a12030b0102010216050a0201080604110702040b03100e1e070e0f0a0b060f040e1302030a0b150a060e01080f091902010c082a0606101b0209010303052208 69
    0x6040c0005420a0303142c1c1e0602000c003d51b07000644e45908455021002c543c0c8c4010460340c80032044800b08210001c007001002c19000780300c0001e00444d55a244071240c0c0c0c0d0100000075250007052403e00c0f204c2640b81140d921403402d901c1d010fa41107100c0c1d0311001c4000e400320b00e03d4141c40c2041d58480f0359540310003803105100c2001e000882201d58840da005100d40300c0200138080405560300d40e940d102d14013412038410090080c0303c1c80503076000740702d00300050b40c2c0801c603000c000d504804400310548400e0110841041280d44590740000c060000241144d046600401603100c00d807900c0e041070350780b4020410381400c22a4065115000300c00081c48040e07885600743e4240e4018902000c103000140d40b60700d0340d6404107a104d04030319000c3c000140d030340070f0100d0501c012840031000b800084c14000c01084030b0203c0c0c0355117002072003000b00088405100282e13941400e01ccc0c00420340146540d40381405003580d80198481d6501080c5e607034403511a03603013401e501804c5454000042030355244901941c01c0128 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 372736870 1250 372735620 372735641
    0x150e010e012105010303030c091202100e01140c011a0405040f15330b0a020c0d0f060f050405160b090402030a060f08030a022a04050a0e0a0318080a1203 67
    0x41440080b070030701054510036035029510070b03200011840707440c200141034040300d1341c0a250107594903031441d00140c440400c1016003101d14182200c00e001000016589000070b00050000103001040f851000c900540100764000c501e004148450240b22013400151030040b80c01604020320f224000000401d800c1041c030f41d2003040500080d000201c1c08528442e4505030621074129110600c001d46c0780381d880c00c81c4800401c0f00750402490310100902c0691030700d503070b01c8545101752510300d81c01341800b0481540c01c0c0a10b60081b01000215014629080206001c0d10144c0710b5220302d0041c1e0401c0a850745411060700d4102c5a100d05000145040201961006001c40030080c2c9441c00041e020341c1120465010303002a41c060b41d02ca40008800905e000c0000d00e0345210308c43c03480c0ca40103a80002104421034080162008221584c1e19950701001d003500f800101c0e014801c1980382c1007450ba00c0150100c0d001e81010341494159610342c0c0481d642c0c5011880035141c900c251015028050180e40f0901c00003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 372738120 1250 372736870 372736907
    0xe06030c010f050c0a03110c0d1a19020a05070c1e03080306030a0b0702030309011b050a050c011e152907050f0a03080730090c0308070606150e010e01 66
    0x81128004c18105070700510201c002c80c0041004408056003800b16811a19056804849101841c5c851960207680343d074113048600c40e100c011a0240103102a850f40e00c448240e400d55960303a0002c00105142e005160658244c800c9480c003041000c40700e40840140480c99800002041c110b40311405e95500c0034051a81c184520ba40d51400510501085441120a90041c5489107000c02550382550780e601d42c8403004030742c03c60215800541000a48441040d18500369469407070391081980101034071084040c035003182c45080300903907003240c02c110001c4411842e402d494a50300c0341c0401c3e40d0360040014003100000145e1703203071600c511a400340c0b140700e009204a51055080c04070650504d4400744c025800100070340c040092850300076006078000544d8100f240ca03603003085128150a03110313000000d402c480e01c0307610143c14803103010001d0000c1c0d0317044031031690780c0e08082c0342810040007144140c0307010908000510300034902400c80100000010f840794049103202c0b100460b4030040460036050301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 372739370 1250 372738120 372738127
    0x2030913060305010c02030702030d030501030201020615030f01050906060a0501050c03030103081e0406081005011d09090f03161103120910050403061b09080f1209150a08100e06030c010f05 83
    0x883e000340100c505000c000c0d00695070700c004500500d0b082041041a0800b45400c1800400041c0d82c000340c8541c3c442c2410295900f04581c1e000042c0c01c1c02c0241d0780c048082c0d0309103c01d000e28218003080445c0902c2d421521807910780d90f504019607030384c041c510314490b145c1c1081c4010008600e12030000c003540c140d808503e114043c580140c203003503038210340c00500c00640c00c0001c12a03482030003d82140908001d09142814100d616000d48440d081000c2c0c2034060b070049000306046010030440c4030800d00c200340c1030b681c03078041850b50b04191940c40d24099800c42000d4a040c10b045c200031825656048110715590b150142c0c240910071184441140d80041280030040000030076501e11030611032050036014603c081d020802c00805000d01600040b140d904074030304442280800240703c030607203c0294401900c0f10800400900c81c030280e25440080c40500044004a960344840114440c601c032007294401c03582c40d0170f41c0c0c0d84141302c212581071b0550301c501a01b400b00c2d0300a001188890f8210315000b071a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 372740620 1250 372739370 372739373
    0x1009080f03010306140105060403120e010915080907170607030b01050702040c0c061121090114090709060906140f04330b0304030912030e040c1d030d020309130603 72
    0x32a5000f41d100b074aa00307a442103094107200a10200c14010001240d049003010b05507118050043c12105254040c0310001c3e00c0250242d0242120a00030030103200041d0240c0070483c00030380a003074103da03400070602509201041d10980ca404802196188500805a42c0d803030b01c070160010444400d54905101c400d1080300c00503691400b4940c084011540d41083d040301c2031900100703840910100810310001881050498440c4d41420b8030905298a040501c1c3d4681c170789e0f524010041000e480310818942000c1059030310000030410f0480c0c0d010982049800c0c3d80701415412101c02d4001c400c1012100d40080303400b480c0c10300b42a4804207005100040350304a41100c04c01004202d0950207890007120004130303005d68504d4141000300b4450246500d0b500d0f0568009003071001d64003800c03c0c442541c0c54550300b07040c0b050b000c1140c06500a0700802400f00054406840b00c8810f4095143c0380850000e1030f0300d00d080108440b800300590360002c40c20703e100c2004100c80c2c058030600e606083d036600c410000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 372741870 1250 372740620 372740647
    0xa05040b030a0912020c090a0b0a0302090703021c0b061b151602150f040204020c1207030804020906030d080f090a0f06020301060f05030f01211a01050f0a08100908 72
    0x5005908484000032401c1003803820300800803183d00710000b99040001c980803607440300c590b0075511032411080002c61427441c07000612044503682001c1d420800007000c00250340e0700355000b810b405a46000800c4001c004000345010f851311915040e0300068244400b2404020301400c000001ea0303131030b00b03880801804019440d034038501140d14140e03101000c00ca0040b445c0e0140890141503400d07034000035040c0740c0755200400c0c51001400017405542e001500c2010000f007400314504400300356081c40d070789200c0ea00b401004d1100071b4909034440d070305000c08241c2d940345c000340020343c581050701e030f03200750b41e480065900f4440401403440d95240a8140384c54001000505031408542c801d40c0c0c0180ca0707505000004200303031409510201442030401c140003031020f40030100f40c1100d001900d44506130701003000b910485a01448010180690300480c520301d00450020203050b01e03402e5a00d4031940c0b60600c1084101c042601c1a403c40f600318501c20740d511041e03500302e455402e00481100c5d10b003010620008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 372743120 1250 372741870 372741877
    0xa021c0209190e0c010e062503051e12060d062304060b030c0d120302040e090d140a05040618030f03050c01110415030b12010c020706030b0901080a080a05040b 70
    0x10a41c1d91114038070007460302d0301442218910080340d002070901c2c600400010b048075201c0c1040520410b4003080600c940c885004040158660b0850341d141445013510780600184c20080030103003440c000070b001c0c0958030156410740b19a140701c40b003014000d450b07480070300841c02d500e18420b80340a40c032021601c1c07142c0c43d000b05000c4809034410007100e1038509414038000312504402c4d0707a48aa002126aa00503540f048555078466030000e6079824000b0050400307038000d124030341c05414040b0080081100940010030746c508119080d8407002e074032803201e404c90580d611914007501c02107501800b05101c114400c0081071210709000b500c14030519201d84441c80d801c00500b00480000b04005024809200280075601481d00070340040c6050900b428502d403148806c14030780104065960001d0700e6035070744003180e540c24001a4002003002908042c4000c0d1034031464080d40010908000d001c94242c05d042c450b860490f01c001000e050710480700e0351a00c11035480800a502044018400403541c05c1900008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 372744370 1250 372743120 372743131
    0x105060c07241b02090138040608090111030c09030102070f060603031107061403090c10030f0c08040f0201110a05030a0e090f0403021203090a0f260a020a021c0209 72
    0x840c01899401c01850007620f03000300581c001064101c4001030300d030f0510480c10741d00c00030021340d00086e8640001c00c0380c00c052564442c03c6001400303140100c280303403401041668480d540d81402e41d81c038801000e0903070f501d1b0301401000307200030800079101c130106002500380a100100003500e41112034440305800307205204150b171141c0c0e907040d080003010341041b003e01c07002030030300054060186011000380601020030740e592000c50f4004000b0b19070400a0041d1724100078000c1901c810242c10100050040c0100841000c901d0b18080d101c0c01c50a0044100b40c0c840c9078040350300c411a016a0307004642c4010802c50415480c4261050400014001d1001c1c00d01042540c1d0b420301d040d0981c01c104040c1080260029180801d0a030601c03000c25408a8180c000ca140b07115095074a440d4800007a00d861802c80300600f00c3e43c41d40c0d056104001304002d55200c11200100011000300141904421038490788090202681c4030340041c0300182001c5071400104080b5903680f9600c100c0b00d401017078400300c00f283c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 372745620 1250 372744370 372744419
    0x3020c01020c101d0d05031609050d050601080c06160f08160f0203010f090f02190512010209030d0203040e04031d0406060302120f011d19020f070c1a030105060c07 72
    0x580d0042c1c4c040c030030082c10103015203000428028901c0d0f0405011444040c0251480181c075404880c100d80c01007501900810002e80030014503501810111380344c600c28000c91000703020705211880f6514006090307945250750488500c024064507139a814507038000e01e100300c84042090110400c0301181c0001c1c0301c60940100b07409030182c4814410503003192503610424841c54900844180400c0c42101001100c50781520003c1070b0b402c140f400110429500e0348942e500c10303000540c01030301c541e041d0040c00c04844290111000c401c00c00205a071640640c1c001c00c001c5540c1000001c011078400c080e0500100c09100070a1a0382e103c0c00040340955443e6001440400d800041d0078200042300e40726168004100d040001c080d504103050018607640d080d50380c1102441c1c104c0841c50150308401140e103007001d9130a08540c5c1c0d020075614040144c10182003951a501d00000000e051807401c02201d503500d0005011620b968206010842507402c5200484900e1056000100e01c0c8940075070031000c6202c07100ca = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 372746870 1250 372745620 372745631
    0xd0e0601061206270207060f0e010221040b190f2912060c07060f060323120901140702040606021e150a050402060d0c0f09140a0603020c01020c10 64
    0x45031041560100e602a01c07024180710a40100101c4282c000c0203070142c14013025a80d114242031000c041d18241d04004845890700d280c00b02110015070003041050181a5440820b4006071030071021010304650207020302d0342c003000141c1c808a10181c0e42d0200c4013800e0001404800100c5a5004c942c000b103e20342e502e000401500d5102243e070088a00020011036500035058661406152202e00c041c00c000c010303400219280e401c00007242c000e0031074031010340300400c4406c1d070780c2c10b02d45610b14030110b40040d070107501ca8a40d81100c001003001c412801c10000705c0b034030b862140001190403c070034080c0c1540302001030005a0050b511801803400904165009103404003004049a0b04a0100c000792401c0341c0c071483c40c00e41030301041030b40181d10640c07a110020300d554903800480c0c5107202e28580c03a80841d241600c41c0c4001600408021606041da03941c0e0203510f5203802c00748003001200a05c440c0d10010700312040024500ca50000e121461916002504014041c0500b91501075000700519131961600b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 372748120 1250 372746870 372746897
    0x1911030c06011a0a0c0b06010507140c0906030307030905010819140718050a050f041103012c0919080d0f09021005040b070b280c1e02120d0e060106 65
    0x201c4034000d440a0700e0f401949402c54078080a0102428550000c1c1070600e1000001d40d00c4c0c0c00f5406031525a03400045810f41090034480703042c0c072854422480b43c490050311000c60f00750708000042e140c0086d45500e40180039801d0000550b8090001040040483d80801042c0c283e02080c0c00355120201d940c502d407941c90308180e4005040c101510141d0041440701f141c040100f50707a21030f0f0b480215101a6103450000182c0000b04e4080d290b41c414141080d4000000003411440c480c1e8250040348619141d0148400c020314844070740d050542d0405d45c00d5014100300c0c0103410030038a0002e2414400c2c0c06040c6084440c0e007402064400c400010400341e640c071742950703041d410b00461000c12031001e450014589410300b5041c145a0007081005001602c0c4040051b808100400b01c5038240c40f0403044082e1560070b04254200036201e405078407000600c6e900c8009e601000c03079944815402125402610004000c1c5139980903a0b00916041c00c9125140c002c0e00005403002d0040d28081c200c565a5150600002d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 372749370 1250 372748120 372748139
    0xb100804060c0513030b0c0c0f1c0306050631271413080405060f070201030e0a030f0f0203090d030801050108010e27010e160f0b0702061911030c0601 66
    0x10382041444401c03c00c02c220481e802614200b56030303210741b08004035110b0404110090046410000403031107010241031150070f00041c4900b01d50380b080034081c4080824602101a940c09115064209000780401070741602038100385039081800c100350041341043c480c100c10b001e003025030104503110004c5041221150820302c58146030180d00c1402c0c0038003002a1590006581b006004592032030414000c40c0401c032466044030028a070041059407282050f035000c001d20341c031614080740440d20300102e880040c0404101000002d40540720000e1840b45000260b82d0036814012940c00c5000410684607190f80d68003403031015a002e80d13100d01007581454005422840181c0204220080d64800c01950b102140c3c640c40211004080c4141c84810364640303e0f014002085080c4914081d01c9050300114079440d0440e82100e03420140700c1040ca03600c1d04883c100b0300c00c03404060b4104400b00031007811076140e2014000c40715000d10304200d445681174145801c503042a800c3c072807203400a00041025156 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 372750620 1250 372749370 372749381
    0x1107021c02130203072003071b091b0801091802150405040203040609060c1805061303050f0c010f0e01141305030601090203040b0708070c0f05030c01021612030b0108010311040b10080406 82
    0x2000d8410000840072600f01540c0b0300030341c18000c1c40d070b403491070700ba81441340c055450380000d12107902c082c0464a001600c124bc0d401441c0940e4001880381c03000040d42d09460b000340182307000401c06040741115150207101103072054411404070241e04000006050f1282e1000713600c40c1e0301841001490384000d141400c103542c1c5440e9007508000c1e404001d85902004018640e0031100100c1d600e990301c41c60340c0c10f0402c00c82c116900140c02405152040c0344002030103d40c0c0030700c2101c02d170313901d0009199954041c1c440c030884034100c60000f498940d00c0781c942e0b40d00e80010040c0341c1e850307241c002e07c13030f607407000043c9c502171098201e541c01540100901080161880e9404d40007941741c1080045468200401400c0354007009010300051841e105260034400140201c400640900700250b654201d0980081502c86032000c01f154008042074030311004c10b1182c8560050084165500b220036461500c902e80c3e60341c0ca04203031541c45565201010300642d16011403884d00d20342a29010030514003814030108484 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 372751870 1250 372750620 372750647
    0x60503100207080301091e06031a0106140901080421050403031101090209040201120902191a180111030f04030f02090f01080d030c02010605060304050304030b07031107021c0213020307 81
    0x2030040c81002c00182c0540240d80c1074910070800040c104a1291100400c1c0c40410b0860780300130701d007038408400d11400c080c2c01094040c0002603000d03d66690310701225020300440c1c40030941c1070144403e100035071203020030a82240c05000807140412541e420302500700c1c140f00e042c10225400090070420140c01c40e81c60308000000b0b02c02001000c000383c0101e201510010002410050410300305905045654410752030a50041c142c5145071480503210740007841c840c02140020000d844549a09104540072507502103204203c00741e098911708015200c0402603014502240024454030051104500140000b10301412114115408034010b1040a01c1e000d001c840e5000231000051285080004507800906981e14000a581c2054a42280142081e0300807980c0a070000080c4418808004081d2013568064200b022544d02c0c1d901060702107038075580400e10711160521804000d880c203601c0020500032044960012000e00b0742c00110001c4002c0a0000f94550101c18403108030340c410f500c4641d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 372753120 1250 372751870 372751903
    0x18021f0206181213080d03090309050405130f060c0e0d0c030f0206250212030a02120c07050901080d0206130b0601050a140706090302010b0102160b090a080f01050103020301050c03071706150d060503 87
    0x201c1803274600a00000e458007a0a029540382e401282d50f03000412001603a56810030401a1206c841d031518a01601210b0001c3c0000348412140048a00e0310351440507003e54070080300704107289540d0381c51011900103c03050341e00c00804c0c0502e4031561040c0c0c1340c440c0000c0c201182000d11050500c100034413003000ca00d580f0382039801800407019458001658221154001c0c42990f151181e9026140c54507032190032064200d11071000003d20524001070541c00d44c2c1c020303001d590701c3ea5181c92441102424154020b048941c0480c003051041d400b41300100619542031529441e01c07103140705401055401071000700c410036075a2507448203060b421300c9a2012003c01748081d12119a03542d4240c0419100340c00780c098030341d00002d44114180e6806054100a00e0a0410380e6079202d03880da1210f0080c042444140e004e5420600001c407a003401d10304030b9204007102e4845004005020b81c6144003400b0042000b0b411401d84400c03510b410500e08054040c54150755000b00f04141000289420f2200e114807a480c103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 372754370 1250 372753120 372753131
    0xb030103080319020c100f14040201050a08070e040501060f02062238010305150c0a081e100620120705010f18021f0206181213080d03 59
    0xc0c1c0403004494000c601c80008003400360a000011000340b244400014851040d078a20450080094201406100e18010100b0108000c28400d0030040d1040b00d00038001401000300031000750203610343c550002d001e45407140031500c103000070604646082e046240840e080c0e81d96031080326810401c4960104c1c5512007601c20502e0100c0c1100002c1803000014900e440080c00489400105103030b071400e11080610002010060305040e40402c0303002e02058032035010b0704950700091709040482e140601b403204103481c6400b00142044a4a03a805002e10400c40e501c41960180000000040c5000e804c00d9944204114907002c3e000c1d002c40c03000d40d080c004409003920402e85204011030001c0e55680c001000555800c02454154010202003040021940c0340088080c0280003c40c240e071042407007900c80b54032101010224900d0841c00c1d843d84030040c7c0c44800001d02c00802503138040701d0744141800329880e100210717050750601d4002600310454141038100411001500700700c243e0390f041c11410200701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 372755620 1250 372754370 372754373
    0x5090105061806060d110327011503030e0f040606030e0f0703051005040305130626060d151413020102011503150b0d06140601080105040b090402040e1e0708070b030103 74
    0x60341c180c0240f11511810707002c035242c442c15025400409000e8540e401286e9280350000301c032544412100e8684a84201442c0350840e4060140f14068001040341d007a9044c0b20700d1598200d071024400600a504054942404405912a40292070207000b15840c041801c01c00986040c0c40d010801c0b0b0410125401840f0400204401050000800443c0d0201051a0741c0303905003581c1601c1180ca024000784880b40000075031590100f100020340da8541e241400403d0005141092114199080da80c04158004440c0009143c9650011340da82d9079107020a85800000b042c1d1210002201e0747c2c0b0010111341c45d00401c41d80e080c030901c1c51164085d422009554299201c0305602c00f008c01001c0c2c202980d0304103106496840c41c140c04581c9030700071414070402c00d00c0342c0300752100501520310f0703408030350018004101482c0502035001c03003120250110200b81d50360b40800000e020341030b400311114040c01041c14198021814410f248140303010050244070700d80072070356191851540c13003815040340a000500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 372756870 1250 372755620 372755659
    0x1401140a1e0c030209100f03050c0a020d0c050708160e0a050c0307260a020d0506030d051206191d07050a090e06010212040f0e100b090d080c0106090509010506 70
    0x40201c04a03060004011484142c01d900030312403940010343c011039041d003402c00380d81d00498a2507040050fa5040c401d135250514907032140c0c003591304040d001d03820040140e0f625900c40c14111804901840c21944010396a400590800c82d203800525039145440006010204104100b01e42201d001a02000301d842c203805205c26070b002c050603007002c01035070701903240034014900003170300078881c0c0d02d070501c8500e04001722800c0c003d5200c52001c82d0824100b40000d54a07223000724140e221040036444007840c0004540440e55440d500800140d444490b0582c41c40440001000b034002418801004540e4020803001d08403a029005001d901048010800f503034590354003000c518211040420300c0c00851b251440142d007440212a0b031079000e503c01040c001000800e012002084409418074860123032540c1010007030f0401d4070b0041c0162107004101d40400f5081c8004030711241402081e074141410405881d10703003035441c2540301e011007988820030301c54140028410160040c004031091054041a118080c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 372758120 1250 372756870 372756911
    0x2030403051905030702270106110c0405010e0703090c08030307051b0c0604030209040f06090501051005060c06041e080c07050a0611070509090a0803090d111203130f1401140a 77
    0x28080d4208147c0300440403882c5200982000d40005046070f0344d0b03143d1400800c06003400030025001c2c4580e406400041c01c03c0e200d0107050b01c91005071b519895554001c2900584030f1000c085a00e0b40c400000062812014000b450184030340b580d406076583c010100541d00101c0201650307059400100940145945090407a402c403941624030405a07550380c02c02e00f903034109002000e82907605140038142044010740c0801e1151403050640003205444106203c1a40076a02c020310965102e40081000f01d03102100a1400c040c0d01903030003450720729940d41c0050300e8214443e8002c5c1988648800e00603407a0940b07885000d0b044d945043d1b2140145540c80c0c0d50748003030078450140174000400100d240c000d400d03c00c2d80711070354000c2049030340c0b41840d02c00255584040d41c60700e00050000e0740300c3c140840000c1000c501d502c114901d5030341151206914202680601c000c100e40098114030f40340001072010807000c80140314040002500741ca098084141d030306004041c40340a03450898594450500100324 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 372759370 1250 372758120 372758123
    0x170303011413021603090905090c030c040b030f0d021005132303040b040b1804050f24090903180f01020d030b0607080f0714070e0402010528020304030519050307 71
    0x60001100050b9103910003446100600300841d41403281d22014150032801010440740c11a104110a95690040945941c20500403540c140c1042100340704600d8650001004041c0040544054a8003401001d10f41404050300c01d001d03803c40304d00c132295040300f485078580c88481c00d0700c441d6010700c1a50300e18401d40038a20401003081100713110280d203130400f002940c02622100b60042c0e170b150f481c1c1d6541c1141c0d4100d450000c40300d807001c84003507030a07041501902e40561804064011241c50718483e01642c44e0f180e030000031000d100a100075020740d40341c00c030903402018540d018694400100070200e012089030400075020f48000740005d00142d0b800643e00403a80542d280010b41c0084050011b03032184280382001c0c000c200c000c6921a0682c00343c00081c0303c1e01d4464900e004100d804501125110301052260551050840b00060b02650181c2c00404640004031980721301d452001040101c007000c99182080140e0000ca0306000f0031008220a0001c5441c04a00e01007600e595500d841d500c0c429800b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 372760620 1250 372759370 372759379
    0x60d030f0c0c08100609060803040e01052112040303030c0215070f09120501020406090f0f0302040b0105090910081002040e01060e030a0b091f021317070905010e011703030114 77
    0x411005002102c03803500c025014541c252034407002ca072050b21029241a0160000c650319104001070030240005c1141e04481d20f070410500560300e86007c20102041c0741c035100139114a0b100200d075071040c0c2845102d00d0250b106a18a403558110b040040440b12542084015035104018107061070324001040b9a0003601c500e03101c080c6826030328040b602410183d00040c0200c1c0680c504c07504200303064001d4401d64940c0d0f40d8000c1a80c1d0744500a0500c001d113031081086030550485c0510142c01d0a41002415040c10306000c1d291401400128081c06012910540d01c4418844140f02d48802804039003800c0d80390010941c142418415880c2156906108007c20f208416440007076a44041c0024450030760840303413800031480d040c0c41c01e585454403a400090040505152001c514406100751904280f9258800c44410704010a00350055100a40b0743c185100d0100d00142d500514004d031806044040404070542d450410b901c02010003031590441540c00500c01444a0318a079800c440c0c01c03040803107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 372761870 1250 372760620 372760637
    0xf16111c020109050601030f0308060307030804030303090f020928110306090612120c060c07031d010315081506010201020a08040f170c1b120d03091506031406060d030f 74
    0x54003070380149086440201180507820000050003040c48191030070034080e448051180d0381d035008043d01d80c1500c0c000100742180900042c0b010038860307802907081501c0f452441d82c818400d90001a68054100ca1051241015500403034900304034134803e00e02e40203182c0381170048201b9030070480302500000341424018104500003848603a208840740f1a00d220705000d881807c0f1004034469a540d00c0040410224428a00803031003002ca904101c0300b4041d01035440c0f0304d440340d03400304105064904010f40c504068540040c42d10824031103081100034818140203009000d80300951200d5083d00a0245065910501c9013407451600200907a6006620200c1c900c100c6003989400d11120702128440c946a810200302400e0050740018003c00c2200220070b805040103002e001c1203a00c81d020a51500250031041c4070107950b80c02500308900c01403044410002841364012980b003200d0a5a1081e2204001003205c003010010902c102c641000702500c80c6e2459141e075413000761a42c900c0208a200700405130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 372763120 1250 372761870 372761923
    0x60f1204110d080307030c0807050a050a18080312060d051509010905070f140328050c0d0b07080906040506012106060f05150405030a0201031e050f1611 67
    0x8900204115000520101ca07180d090b003803d00a5130030446a05010929200d6003040c064090341d055481000300d581d0310361038031000c5a0120703040d402454450060002c804040002401d604002c10041e1400c840255120341c0300008001c0503003c082c000034010030304c0f075030400302181c00421700c22410218120a481a9115080100e0050422910140c400c2c05a000c0c0403580400307840e00ea004440d2000700c200398107403802c2d041680b14200c005c2221111040c0b80000900c000b12400180c000d940070314281d8415060b0384012894461200c42d00b207500942803810000e1403604490380d560846034080082030145480e540e0965204418081d422400d41c2c0510080d4610f08a0740b00a200103030b012000f8011944d58078107036100491306009240c8107919002000b00c503090100c06a4084803001402802c022100c0d8005400070004980c048100d021034948000702c038412801103501804040d401c200d541d1418480d0040464045500c0d4410060601c014110f817030f000041007240d84040010041e03550030340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 372764370 1250 372763120 372763133
    0xd060218121e0724090603021206040b1302030f060a08120a0c080706020c0d0f050909010e07020109050f100c08040b0601030b0609040e0c030c0307050109060c0507260c060f1204 78
    0x45922600c40c030a40369500c44651411040c031341110103656202d0107103070342d1104000d605078011640d052030442d070004d00060b050b14150300906080c2002a0402d00c6000b0312030a9003050b07900442e000300950300d812040c401c4030700b80441c07014007d0035484003621500d0280c0c0400340141c41000040c10402494400150a0007078003400c551400b5070004046644003a10915185c0b11154002d4120200388a42c68000649025070100ca000420041c404881603003003480070701c41040003402031811596600d0b0003300241c020000300810f074015600030400403007014110700070f496088562008000c05076060200190348820501d0f0400c80c00d007804a8551b0420340490303101d00410044030742c020304100c20000000c00c046003691040c94164103842d48450440300389a035400d501e11410b4001922038100700b112500c14403051160520680550701010f59600455101c01c20b01611904145003106054a0002c010004040390b0401907520b80e04100003913164a50902031441c00d40404070001000404106c00c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 372765620 1250 372764370 372764383
    0x705010c03082211150405030705121e0604151a10021c0e0f0a05031504030201020c0a03080603150f071b0b010608040203060108010501050607110f0d060218121e 71
    0x100c10000c4460010346042c04030351a00c0c401c0000b401032a924408401265a0761704407016504041c00800c060751810007070004049a02075003d0380350142c0d40f007039603400040880c0615000300d02c05c010301e2a4202400c120049403960f1942501840c904007103000a00c1e110f211038024040e0032281d00401d5a0b0408083c1d0500c4030099541048521514050b00b8064201140d0440c500e402d40e0b448140c0440312080c0030010169004413075040c3d00090070500100e10001180d0f42c040d2180c4005420000c00c503009a1400c200b514040f0041044d120802019085c200010711002103100035400c002e0034a00e80000038414080c200204001ccd0302034024000101c014410304103594010f451000c15030355910300414014040d030741244640a0480002404041402003506891000300181c0c6402020f40e11001c41c1d0020000c1150440010b140300b803103540c1d6907034020b0000c0d03006200241c0e80d0380d0704111130a0f061452280c024400c1d04245c4c40301c00c144500140320304000c6075811814010644d6a418681703040c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 372766870 1250 372765620 372765661
    0x19030318050f06160c0b0a0c0504030b0709061d0d020105092d040b010c241107050a0b060307060e10020309131a0103050f450607020705010c0308 64
    0x2c103051814510b4140011040e10881c042d00e40c0756410103030200201d413002c00404000e08948080404601102141c1e4840140401642001458a50341c0c0c1e80e1420982e00c11207811021803080941004400e0b081041c00b01c8800d10201440d0242c00b40100145a10011280103410081c001c20b00540b607440321a4a04aa001c101440f02303440c0d01901c101c02c3c078810130078041a0003182040c60020b819405080495000b03644200d42c190103001c00703412942e004203c0100710110039102e07102c00c1070742c0d41c1440c0140a01d5002d40302510f400000707810190a4884050305c106c2c000da101d01410480746611590000d052403044811540001d04200200c0c41c50007821012903012100107160444840030b540300d034090b601000103501c4070200d400700550440d00d045402104440c1b400b00040c404049200e000d0031401d20040d070004040712106042c035480309006250f010b1072508c129000c102c4100400005a00c03540c00d1004001d00350816000804074402e0500040500c12800040341c7d0300303034000c608001e022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 372768120 1250 372766870 372766873
    0x111204080d1418060106020709020c07050a0b0d0614010e0f0303040503060f0a050705030c0405040902030703060510030c080307080a110a080f07110405040503160302030708030c19021903031805 85
    0x71a0080807141030400e440c04803c00f07141c0801c0e0b92200c48040f031614100c408540107411103501e03020105c8040e40c0200c001850b01e000d250000b00303042e983c10359040080c11111200c1c94070f80c015800d4803000c89000c3c4e00a00c1e040045c8045008a50380d100702001d28540d000d8603200903a607004404030f40b0390300503a002540e060080314100106c00700414040e52280070141340520050726101410b0f110b901c4141e40703041600c0002c000078410307402d040d007000c0d1196201900310f451503a62612144121801075448000611564400300700340a59211190f000d8182d54026500d0440d55a80740b56207841900010010310805500342d1025079014007143d140c15800c40b00d100d944103980450701d00b00b9489518103c42c5c0030302d03e02e600c0e26141001e200355032041c2e0740300f002103140a03c2d110712140c0c031079000c803c1142184004c001102c0000e81c101d0281d4010350380c5006103600d442c0c40300030543d8881c0c4286c07142c0d800c560120014441501140e540c040b4621340500f00021000202c070035401000c5802d00e80038056 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 372769370 1250 372768120 372768131
    0x5070c0509071110020403050c01050705210c1011040911070f03020303160f08010302090c27090f040b0103060203060604080a1a0112020607111903080a020c0103111204080d 76
    0x1e07403c54114002c40c41ea081c00da800d4031245161040803070189000c050131550001c1c4c00341d8010350007030006140341c9010714101c2e07541071454010647d100b607401001080740c01003c9112a02941e00304a0221410303201541807000d44c02080128402d030041d8030510a0841c0c440e1400e08082803d0401c03500c0568000010f86060b00f07d6060280d0350380c0c400d0750a101300c041914540417140d441344407007112056450340d640803141d02c1c58082000601000c1d1010082801c01c01c92486804420741d0704441146050300d070071000c120141c0810601543c014480c5120322500301c20000001c0c408802641076990000005803a9240e5802103103160040e034010681c144542c200e040280241d5800003201e00101c0000d41310140c1c0c076008901c00c103806420000750008020f200c0741c00090b40c04940103910b0900501415079028440c444500000350380d510a4a030a180007420f00f07280c0341d040c031070280c44502c282414800c1058000402c10300c0d110300c0505000c1c0d02c0e0400007003820891904101c0303001e0f602070a410b221 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 372770620 1250 372769370 372769381
    0x306010801091b0e07030b0109170703150c0504061d0409110301050114100509040b06030f01090b0a03030e010302030415020d0c271a07050a0606060e120c0105070c0509 74
    0xc000207401543d1001c0d0461103422116a4000c00009544403452007a031251280301c030690107451018207a90600444400224030250301c840d00b070004070030300c000401045203182010340c2d0240f0410325000145060002c2e1160307054018040300c0c1211200e1030400d44c1907030103c4c5200300e200c02d507400e5a0382c045d003029000400d100c0d00c2038000100d901e04400803c0a640d840d610501e640c444440305542042c051040518054010f40207402c00b4480908007061507208080011400d0b403044072223641d1204104018400300344588102c038030403075094910702140790a60310090240c2c0d500050007810181c00200043c10011440d04035400c4d03050501c415520751481054480180a1210203100040c0e1841e0705250f04071082200c2e9203540d560810303400069410b2403030311041e200306941d1001924500304104000181e003000000011801020009000c40c28290020a1102485e101600c180600c0541d580031500225219520301d0090030419654036440c03408401041c0d940d4005940302c00600101300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 372771870 1250 372770620 372770623
    0x201050d11030a090312090c0504020906130e07020f0c1807051e1803010513020f0a0803030c0a080105030c01020601061d032a06070b04060c0e03030a0e0a05150904020a0e03060108 79
    0x44d40284a9218405a403291200003c2200d00c640809418007414000c200b0440c1002d0303008101150004d01254500303140c4a90000d96803100ba401448801c40007810010a19414007502400c066a50302410b110102c4000060307000c10909403442140179402d010034840c601074000c035804102000a10001100300f5084665140c0251103030307110504d101c031040560341ca410310a0078483c0101e031404404504141c2c0074001c0403014020a9a0822400040481d07040d400b080a13600c5850003c650640e501b1070008000c11000f8180e00017800f941c00710004c08816a008500c19040d540c440c5004001300c11455030180003e4050f140003501802102c1c079100600c1a000060240c44088004484480c0301c640f06100d2240b203124800303001040001c0204000421542109413410181e184c040300e15445100001e0a40c2d01007511a07011800d0b5640c2c403541e90a10090200090504840c80c208202d02c441c2854020301c035240c2003d01c0b866001071107076200c0d8040d0703020201c500e8010b03044501540c1c4501c40d19 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 372773120 1250 372771870 372771881
    0x1b1513031502070f0507090e01021e0c071a190306030b04060e120703050304051c09060806060f0d051005090c0d150f1e051c0209040f02120705120a0b040201050d11030a 74
    0x41f13003500740500d184941704140229040c042c5d01e42401451a03c0c0030314200c90750780090040d401203000300c140c0080c040d00c030f1110b4401809040c0c00740c00d035604a807000d0b07010200702541e00e50060500f0f00d481080800c0704860441d82c0141c1040d0701103901e1232600c01403820012984045403420401181800130315038004007442c8910b02c100c0c2120300428920b2189000340110709038420020301400c00510480e4407482e182c40d040a4050070207810b006405060403034a41000b0303120303508039075100208a00158120840c20042c5800d41e81c040c03070380c14000c202e0f4405114601141c0015911020551840390010801c40001c117040903400c0f5289445141140b10044c1c8100041285080120007198501c5c01d2060004814400321544021440c983d0903c8500000100700351902075200d540c031809625000c020700540c070a181c024080c0780e401c000c1007000c042c45403c0150043d50228603040b0002d28980741c484d07041902420003076100c858108205010706400750120200c00781c0881800301918003038011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 372774370 1250 372773120 372773129
    0x41e0e010b031608061303230904051609090c02030712030606081e01090f020913021e0304080405010305062e0e101403070309051b1513031502070f0507 67
    0x507140c3d5a6030640342800180340e01d0284485540041c800700700d440c03c1036002e04a00da8070034107002c00e00002e0640c0300020899840c00341104000300140055191400d4031807035500c0641004030100c501c22065006000038482d001c0d101c0500c1c1e640c11100000b5000b0025108a19400305c00c001c5c0343c9000c9070700100644801e00c10903010441140215810142504c001c0c0080e0000090458181c0e280082041c0506110f10245102c5542000600c40d00c5d160725450300141550820056501c03441038141180455a82e40211641d80c001c0c414800024a140201c0d4126242442e000c20030340c40c4c3c140001c947e41c800f00c240204001c45640881050110440e1402d07107a038807600c031200d02c40400828030800044440203480000c6201e91143c064100900285403c80300d0385c40c1c00540c10005544a03454200940d000380c2950038504403010709403400c1080500806101c004039810711004100300b2040e40c80c2e07070000400a0302c000022000d40c2d4403950548240c0c07500320500e1003481000e81009a1949050f000c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 372775620 1250 372774370 372774373
    0x601090e1218190b0d09050706030204050a450c030e030313031b051e01090201080f041a04060c03050601020105150f0d061410050a05090402041e0e010b03 68
    0x41250307511490050700c2c080c90340c8118036510080a1020440700310070280300b04003c02c6905001283c881c09180140841d55009140011116002e060041c80e240b51b0b58460301c10140108401d00040d246c01c1d85890850340341803070314010201042d810103003a848811101c40250003801c505442c40b84c0c03400741c101c014001280204560114110100c0c2600d4081040e02e05c07079401007001c0342c2c0048071500220075080c040e207000c0c1c481c100c000c0c1c140c400003c0e220f41c0c10b4031039030700c03905120540c014248685103214240300020003d01c0460750020b400640d006001d00c0122409600207000c4c440c040480c40c07081106202c03148070701d01d06850710000601d80b580d64900041c0c1713064002034565005210ba81d004032401034114000020302d41c00c2083d001c21407560160018804480b42e000551240211840b5806c0800d0300e10716413030494094040e15009a22252244417072003000c0045480c0d03080519005034040d20046000b03188900c03002c00341d10824503541c09203460a94a01e00c4280b040d804650800021030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 372776870 1250 372775620 372775633
    0x10209041b1403010303090e0702010b04020f0d0b03071203050c07080a080a02061315020702060909070201050912121b0c0706030203011e0e060f120a0f0c1d06040e030c0601090e 78
    0xb007842860000340802008034480403403c1c01489049070304d4a511244910000c42d5041009020405a820800c4800c03500c8002180c501c0070a440c5009840b501403007034000f03180d01447e010710f034511005492409028844005011000035400b40200710140c80b10b0b90850b01c5c65191840e00c040300343c1c007450b001c0f07006010369800314018880103641c080c4025008629116000c904400c0c44e0002d5000550480c1d01540805c0502c1ca2921680d45a41c4542c2d115000020145000a03186041804031008904001c00c01c00410460007072090100da089015409e00c1c00b0f90540300c0d00c0d00c2000f807080703140800301446182c0c80054aa941900218140c0e41c50584850038008a540c035224049010300501d850055000001445420031080311200d110b4010030708024800e28008845c1081030411044d00c07954240d148003018032040904810041108030540c0c41c0d60208218850014a005050361b0711480c0c4410408450038410810354401002100580d55296901c42d610001400b01d40003800c40ea02415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 372778120 1250 372776870 372776897
    0xb03150402032403010609180203010c180e060a05041b03150b040e04060204030c03060b03011a0d030c020301061a071a090d08101a030f1f0e09010209041b 68
    0x14020750b8001c9101d041848107039030743c043c000a103040303030190030702d41540d41d81200141070b29180c000c00b06014010f80030102001418010b05095811107018a01400003102d01071040741400752652007152000c1044060944171100007540d41079880d8840e40c0e0103420462080059000d2081407030503d40603480c20458030101f0711120380d003440d50748210652540305101c10044000b42000b0268054801d01c4018506501c0e40e0750108510030b190415221240c0e94004400182001d10071002c620321086000040c05070800c00103802d280407100000d042140d4560712100b1034400b500040c0140415401400362081580d03100d422a800000080e11070200403188420004001c0d0106030041c40c221001d4118240158426261404007074500400d1196450300000c89000d0050240300c0344443c03040103544c9042660300c40b8030b281c074050264130202c7d08564003241115404440c10088603004107100030380359580300f0958020300a11a07800d40081c1400038011740c5500032070740845043c3c2c181e02c03400c1039003100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 372779370 1250 372778120 372778129
    0x140105090c0f030d03020c0106030f0c0905070801030b01290a1d090c16080f040f06113d051e0906070f0c061806020d0617030a0e1203040b0315 63
    0x581c0071243c05402c04000c4400c818440d0b0018606481143c0002c194582c1d41c0d62215401030f242c10040c0c0d0041c0070040305001c440898011160840ea9901c0c0041d00c0354155151068004e0043c840c28200840350981c200841c55034107684122207d031a90941e0700c0e40105040a8240340e01e0440c85410404080c684e1101803411004003030240a1102d03d1605000100000c051180450a42903079054011700c00d06413660300180050003d0041c4140100c405450310102038107400d00700d40f01290035000420f80d56000e580a10410302102c40081303410080603451001d003503d88000c22141107005050508018000c6034a8035281c80b05440d49584e0701c10f960f1134402030342c0c403580107480303e000050320b840042e4142841985005580c030b0041400013030030f062000d40c0e2085d103840700c3e008503005a00400d070000c45105078450000182000e0000295800303a90365826220321405400e102030118008851689440f500145aa8812100103d03a03550341c030307114030312100d0304100d9920204c0340d00169404c0c001d081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 372780620 1250 372779370 372779389
    0x60515070c170a05010903021501150c060f0f0908070201022b050901051b0105010602010c09060c02040908041206270201050a110313030602190903031d0d140105090c 73
    0x40018070040c006050030100040700d50a0b55070b2034000c1c0301e00e40c0201d01282003031040303042841c40780d0000c0c5462110301d50512860903050340401002c0511100e10204030390000c0c0c91324400c941c4900001001d2405c900404000d1039a101288030b0a072900064a0030043c54200a14809000740c00b04c40b54041400c44110f41440040c2c01c070804015911141d1500f64014006040440d005041c442c1c2003004114054030461082c6880034500e0f07454400410240b5028071503102003084514100b003006060000107000c04060b090001d00803581c030107081c2c0500078654150f40c042c203e013004400a150780741c201840a85a08420704041030740d500c105440b4142440e240114a540c180c482a003003542800b01606e840c482c04041d031800d0b01041142c4509a4980d100c5040610303c1b81800684480814000306410325441b00020107208441c88244042600003020541c00c44050204034410074010700031550aa00c0141c0c020105541c940412840d43c0040d00024442c4041c001180c07641c0d400300080018100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 372781870 1250 372780620 372780623
    0x60415150509010c06020a0c0b06091501080a020d0212101d0403030c200a061103090a0807140a0f06180308061c02100f08010b040303140304020f09040606051507 71
    0xc0a0501203160540254054040100141400013401c00951a0801030703a114800f80d07400201400400c40030800070f0000903402003020780303103941da83c030b001000e030315061540004540c1031107480e40000e00058156011a0704006503041c065444000ca1800704000744000c2e22805e5101c01210320110740428001c0c14144641041a241582500c40380c8040d402081410982801c01004068800c1000400c030b020b080205000c500a05418180341040c2c001c58981d81c088d0f031050403081060142d00d80c0c000070000812a000700006598425501d84001c1030b040a034580c880b24024802031405010352210a041070030702561081c80603070115100012501d075441001008a0014004500b440c01e10702030200d240f400f05c0500720908020b9400169211481c91543d4001803004030304d8181c1c0c1303079014030070074010a218103000d0700305415940d001d0030702c05d00141c00034070950001c000102950794601000d0f4903610041c000c48081e0a01d410024040d294174050213000b003c0400b4102c595801d26401c581145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 372783120 1250 372781870 372781889
    0x1428240c031b0b09060a0b0d0203330a0b01030609091a1503060f06010216030803060d110d03020c03070b0f031f0e071107060e061e0d14060415 63
    0x4614540e030503184403405040514042210101100c005001e819030f490044800e503000385042e2500141d1402940c4080340700134041c500c0b00710903c0040e100082c0e61a050402a60060b09503e01c2c00040401d40200b4900b800151500320288040341d03403a6030001c40e01c0743c001c0c1c0c2d061055070748400c2c2c0001600d0090000418031000f03000c407010881004513105420020a50b4211001c0080d540020314104041e922450003c403520203001d215038040046900111151b5980055a13145881da080c650100500035401624681e0140040080c46000c01182c0300c0001c2803030307a1040345814001c2d90b030305119502c280681300e81c400201780f03188000c0903500805004180145541d0312001d200c4103030341e02031600005a107902880464090005e014262090b10303e56240d07090000f82c9406145494401c0d441201800f1004400030015151141161041d00c038100d505103500e2040605803005100da440101152441d00c03001d081d411010000031801182c0c116018440d05000c1e8050901c3d1001e94440c0340300c01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 372784370 1250 372783120 372783137
    0x90d0308100f14011404091a1e0d0b070509041b110c0d0611210f01060323150a23040204050a03020112140f01030209090d09142824 58
    0x945c81440c240320500c0c800c12000d801e143c0c0e2062500240c0b17010000e62000704011080b40c54090070f140d0141080515000b040002048460b00481c861078030301140030309548800c1000540142c011011100c0c3d958000d44100005a0170420350042c0c031254080e440b000404480110b01a0100004d01d010964401054003103044102d80c0c9807002800741e900034000b501410f10409194584500031501c0e005284440b81c1002d280684080d104040140c010500389880e040500fa05404007243c011a0040004075900f0399440c1d154541c3c003c03541a8414030b601c0002090080742580103000b040720351002408038400b481749004104000d80c01140149908121000c408002541c883c20000c607405000440c00145045000020300c591442207680c2c004941058004004600306112107990290101c8041c05c2910042c0c04014440754042c0b00310b0f61400403503e42100700b50f0314100f80340482040c0c0c83c100442d4007590540716491001d28461441d9031400ba050900044201030568845001d071951002c18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 372785620 1250 372784370 372784409
    0x2120f15010f080c090102010f150611030c06150d1721150d030908010c020c010f051201050907050c030c160803040602070905070521010e062403060303090d0308100f 73
    0x40c503040121703014115034941d00c007660710aa40e807090001d03c80b125401f40030700307034103020001d00078003a80b260940c22a441007145040082002c5895078002000f0440b0f00001d69025000405075001444080e02c3d100304220402d44c0d48190301e00424101c0d890301580e440d045e0b9200d0024860b107d040300d101c0e2280650a441f2000351800c12035480b40c2d98800c0c201a0f0520f9115207180d07084036000180d034800340e40680d8003441b01d5030300300c0035030300600f11640790040c5400300320002604009010b1003a18002d07814079004c03840302c60240082e511054248002c507502c030681007200a546641d041454149400c2c504004951001c01008503420707a48039400500d0024074050b1404010407005206504125060040d842c0c440c2e55070344070401100c00c06100c2c8415504210078400303002c0004d894140b03c3c141a603000300064401400103004070354907104654a030382c2e502c0003103400c51052071489644810a401c04004040c5c01c507041600601c01411240700030f41c3c480c0b00b500650300f118010400201032900c0c8200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 372786870 1250 372785620 372785641
    0x40605030f090a0c120203212d210f0702031213080705010e01050708070c030503090a020d080304150c1e0c1209051201140c03040602120f15010f08 65
    0x5820125540488058002c1c1e5100c44d59040d2098002800680408011030194501013203c100c880143c41000c11800000e6041003c00b4803c2c0340500c4181d40602441554400c1c3c0026600310040c01042c15581d134841082500c4607000c0e52900a025142841c008980c0c107050310b100d610311621441c0c000354500b03440c1ca8801c041483d0010102e002a1451050f84400150604094600d441c8110000310b8040003c442c040c4c252000181004204520340c010000c966500c010507250041d050f042c01070383da807110401a4103221441d50b0107900400c41c0d140c8a001c0101c400019403189026078005a010311000b02510143c031340d8050120005072218000c2075400311261625403080d80541805051095503a440705100010f07201e1000c0032858002c0c0401950070000808010705600500070002450003900840205038041c010b0707580004c011000400700300036641180c145d0260800403080c1450640040b14091318122141c107004644c034041e107925075010b4018610f42030600e03142c500c2590f6070714400b034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 372788120 1250 372786870 372786901
    0x6080d020c01180503010207030806030d0e010e0433050108071d0f0d02040e0d020f12071716111804151e051608070216060c210207050405060604060503 67
    0x103c00101e441c0c1d40015130380c1c3c3c248000d0049074860346442c3c20620700300d0101420a88606121010300c281c504d0b0091191307a10606200404404860010304000104480c01c4812003050180303c1c00f40d050410000020120f000702011203009030784800981c1d0340c050381203c12103800d18201040401c80075a1814910b82401e0400030488098a241211006030300041d040e546921400c41568215004041d03203542e05000200d03210b08024002c0858540700c1c10600761038440c80d0005400840a8540000340034009011521940362252410400102905020200072903c81ca41c03881100c2400e5049041140c105000d445190010305c0c1075010707854100c042000d4a5500c024203e160150711103100c0d00c544034441c0c1401140031006602510b8000d00300604060303000b5100c2d8081d5803004032500034403621072041034195109880c00500036461441c01e000584164061200380307030340300d0759a042803a6000038108201e075400c88007813299032981010f10240344075500900002820400c0080d41012980841 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 372789370 1250 372788120 372788147
    0x16021206040212070e06041a06030f0406060504110d02031803040f18050106020c0f030c130f061e03060903020703061a0a060e03031e0408010204060203071a01230102070b04060e0406080d020c01 85
    0x8800388d0749010001941a50003100c810194459040c03d100900045112314805000150380030421510210103038040d0b40900e415001340c2035000000241c01e02c481041e001d54101d0a00e0803682c44544516a0240700c1029001d51a003032450305800ba071810303807103001b06412251540c0240001d5481e1100340142d1001400113560103110b04901100b1070780300d6044098602600050004020380d02c0c949603000d45140340e010700b4010103800a4542c03074000c0d0034000300840b54840c00001c2d8100c040d280981c2447c81c0c542c00504514a031040c80c446140c084a0060101081268550300040e110070341900c95141e03a102540e055170051001c003820004034038190181c0309090b2281401c0580c3e8a04403801ea91190304200010303000812208100304004070b201440220801400601d5810001c01215030081d1a91075080041c617841443d203644d009114040141044031945aa40e03510b504015001d03080b0000e142e4000d500e0850009100c00f0003241d95004002c99034042c2502d00028001110205441140e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 372790620 1250 372789370 372789401
    0xb130b0c0a02060a110901180f0902040f08121c0906020304030512072d0c020a090e060c0415080c090910081002040b090105070c17010c080c0c06040816021206040212070e0604 77
    0x4070b8208102e07100c9c04010058040090ba4a41c00d020411f0308200003076008010b2580030b1024003840c034422405440003174000104540c00003c821103428090858500041c04580c800800d0000341540000100040911003841c0102c54590120840d00b03103200d0310784d003180d2100c100c250410244a01c9041000d4410f14a801500c48c1c038983c00007007980005502200610ba51010703084140c20080c00030b241c3c4104030031503040c185440c104a5404a54422601000b04080e840c0050300b02c0a40105403001d000c006000300300325103000300d80c0e075901c3d0005c0d02440600d807140c131940d1440b540140c003c407000c0d90801c11040342004590340054446400502d401c550f1055124008070302c030041410f640b1540c992100001c1500e185040003d042c0800191007180c45100030400114819000a440c6402a600587d290b07a00e404481c0034003001c44207100c009501c1a041c4000c5001810b00044d42d41c0228000c8580c960910420100540d1b500d48034400c01c0c1c0005059800900da9103003d600c0b007001c070342c071000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 372791870 1250 372790620 372790667
    0x1a1e1f0308040e07080105030d05121e0a0c03050105030a080403110111030c010b0901050d260903070602030705100621020102010207170d0b0a120b130b0c0a02060a110901 75
    0x103580074107682182e007110b0704260301181008001a48603140f00d004190035400380000b40298900100306214150a905034054414003080001e6010344801d5001d03001c000c0d280401d400c0000409015003280c51007040000c1c14607002003420315008c15403140a030b5001e03032000d10b441d03e075039545c1c400843c44448140c144020204900141d90341440205180c10301e00000080c00c4c131010080101d030703140c183c00050150541c4810180000d010251800c3d90711031078107550303016500b41c050101c1c2034403403c0c07402505401002400100f06030004050034100d4071074400c3d5816404881c0c2850121140391042100445540d0080b81c844804000084805030062001500e415002c0e02e840600b8481400399040c01c0f2400100c603461140a4070500b01c22303400803198540c41601d44511100003004880d0090320b100f56410105903400c55440d0000c41e10b60b44183c6010035481c0240910000380c02181c04078000d4003585002445841c1580301c1d4104440c5032942c1e00742042011001100c06803018298150000c840c86c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 372793120 1250 372791870 372791873
    0x40e0a0e060408041a0702060f03091024050d020d0b04030201090803010e010303120c020726010f0501180902130902060c061501020d03140c0703050f03041a1e1f03 72
    0x107000300c41c855401000d005584916001001c61000142d952510a001d018444c031801a0340d400c084440340302444180680325202c02d40c0c240d0400e207d03100c144200c0d80c82c210501c1c000f1044495281200095000320b08000c643c0c6605201c1c4a42200c00000c0d40124401081c60004600e20451500700e0302a10000031406100d0740c5102d903070b0348280c02062070401b485004000301640414a02040d1501c54414400c0000e1840069a141e6240c0a4005001b00850f00c2c0c1c064240002d841d424040002c00c001c0c08a1440c400c601c0d00200020b0103002240303484983c04604100c0039000e40c81c800c0307501400c0314076031105129094000f0000d905049174007200c10044484504001c00c001070080c0304007500588111002c2001a203850716008a800600d03050440d81c043c070780c14850110b0380c070070212071b08130360303104a14036046540307210300e00c18240303100302c0071003803106114003107220f680324440061070700900c0d455070840c00d041c4d9038074040c039000c1031811240042d01301c21051709000741d1011203001c401c1a56890303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 372794370 1250 372793120 372793123
    0xe010e0a0611120f010905060301150317090904140c0a080c01080c120a051f050f280e1509060319080405130b0a1d01060c03020712030c1b050105040e0a0e 68
    0x589294070144c00100043c05241c00600c12180c0000044000b000078401c0c401009046181d184000703440344032001d01c62085200c0c010200d80d000e160080150b462032400d031030029000c502f5460b00403842c0c810b10344828480e06105032000291000c0710014000c4c49203481c0111030145004043d000340c1b190a01400c030320450300c0d400c058010440c1c000045410302e0030854035280c148514407548940c03181c142c8104000e88a2060f0040c130402c055816100c42040c001220b039080d0700451804c5d065a5422200094030011240c1840c0200e40e030180c070201040891041003443c18042d200a603054015480c1008000d41711101501034034812000641016680d0b000140d1440c0082010741409442e8814440c081c41c2c452138400280501c1c610700c0c9800c0c03221540c441c1800c0014000c000c00d0000000b10362060500808c5200003c00f4104450314026510340f40091481001c500c0407a25401c140300702c8044003643e03010403c00d1301c4040c3e41d41410685400380c001650b00e000752003041010b43d10780309032402090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 372795620 1250 372794370 372794407
    0x708060c03101a090411090d0f051e0f0c09040b070509031606090303030609020c030406120209100c120e01080a090602070b0406090b0901060b0720031c030e010e0a0611 74
    0x343d4020340d40c036200751034288000e481402d050701914800030491280180e41e42c01ca10014250084a800484421481c2051078100c1901e048050b070b43c6c4040d01100807182c0083c0d4108094007030380c2507415002220062180c5014140c03001403042801c103000405052098001d0210301e80e00904841800444140080e003004a0350490800180c8004040c024160103006000085c039220384110725003203a100c07040380c90303000d18040c40c000c0119520b00300f01030a0164040d1030301d4100c000e10303e02042d04952000b4100713602c292822605021000000381e03040f4050315902d03140882c1078461041594414103081e00405000404466450303082c0304c0e17040440d038441c25140c411445444002002e07490b034100716020103002412040140c0c1041801d00405645200382c42400d0341c0044240c00d06001c00b90312900002e2000c0f401501807043d6045083c080851216a078003440c80390310101310110289071264269102948200059402a04054000390144d07016403500203408901a00f05110f074181d2150307118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 372796870 1250 372795620 372795659
    0x120c060615030b0111060610121401091109011e0507061b0e060316030b0a0806151c030503011208120c040602070b0a0c020d060209060c0f0601080708060c0310 70
    0x1c95141c40c0030340150b01885440d01c000000d0030400b00100310b060304140d80b14070081c0b00c1406030420384414032142d400354160b19100f00c1c4c1e004041c0078400003440ea092000c0380034840d1841c0da078203011141b4800640c60088660603001a540c10b8004071140c91040c207110303108050f0500f0041d0401c5070001042c054032510300d4401c80600b040c402e4042d000c80040404101c290302c6403040328100240300441c580001c414183d8183d60601080c203000c420005403e000c0c4683c8110540d0080004000e482100c1418075120f0b10411900001d4511006802651103c0c007004001c2c017144c000c0005000d1381c01c00b61a12025103108801b840d1a043e0f40c5c0340c0b404050b0806595003585000040b07000d1056035014054030001d07000340750900341002c1580200412280d6200d80180c05000d4054000f020700002c0d40465462070001782029540f05558801e050381c2d0303038400744000d4882c018030001045058001c0b81e500210f821100040c0101d840351241180584d0003e00600c00b10300704120002110311754041d4810412 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 372798120 1250 372796870 372796889
    0x50a0501121a180a0b01171c27260d0504051c0c0f03050714090109020901120510080f061605031008150f0a05040309090207060906020426030306030604120c0606 71
    0x15403425840c2c0d0921a2180031040390b40d0088484e12301c0881810815841d418510b10f000100c07440408014404000550508001350317030704841c04a50440058600d1641c010705410300c0b5040d02c208d04580da01c5404c15903034900000c80400080120b8078000421100b201d45510003c540e0b58a5a86c032007030880d1240d440041d00408810f410030501a0a00100e0300801c1d84141c20800100004001354481d401402401e0b01540d0221782d1008991042503440b1102000341c008201a08210490200a55891050105501c070700180c00084210200e117850041e50060b00d98041d03507002820079242500010000d412242a285001800306000c110000200074180c402081904003800c402d104210700070a1385010714100420301c40000c0d4850342503c11504841301c01030b2a14024902003001c0c00d92510050545030000c9030101e24000616072406035480521f054501d034128102c50140c484c0400c0b500710360326401070400540410294000703401e01d00c01a151051b03030202d80c4d0355814204e0300f5a42001104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 372799370 1250 372798120 372798143
    0x8041d0702060c04120206030a0905070b0c07050f0a03030806060f0301030317011203090b03070203121005040606140f0306010915020a0516050310020f1c050a0501121a180a 76
    0x1180c042c030005401204141c40149054141018500c11040e0903a00034003504d000400940c130642c09910031800d4542c0001555070300f542e90030341007820381c01c41d003001c0c8500e0080b604002040e18002180e131030358210282c40501040d00d161425510500010902071b000882085600e406890002c01140614800d40f646a20303c2c445c840c40c5400001e05810075141d6800c1200d4100100e40c128050b00220394a04140c10b540750b6610780100e045010b1401c0c42d2060403101d009001e0110040982001030b640240d500700511665110308650407954040c0402c04c480080019440b9183d00070011940480103051808131196900c0b0034071150441c1d06611001600068145010404203100ca202c00041c1c0c00e1b1751807030050074003000076103812103901924072080c0c0c00640071420480090940c0c010407280311402108078012280f1034040c20045840c448111b00d011b00101e050188200044140380d0003401407072480341d1704040a042614003a0040c60000003c15084d80708003820020320000c18400d030114a107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 372800620 1250 372799370 372799381
    0x11061b10021201090203010e16180308210105060711011b030c020406060806030c06030a090203060906070906021b120c0a08010603151103070f090801050c0c0c010e01120908041d 78
    0x100b071040c2c10004a0314010401004100d5820303a8998000950502e54100d00c414124152007029088900c90812030402d20000240640c0d030001d000800c19410307034404440004011044002c2d02402202c0c0d2081042c00100007207550381e0454807070880d06051001d45401d4003c04001050b12801c01103000445034541c9000314140303401440000c03d9241030511807420458000380c1c60700c4000c1d1841e40514404800505580603d8002d69080d0f1703000b905a9100d410901d40c9641c485908459610119108000c009030451001a50407090021074445411854030b0b8401c202e1441c92091040680d0703c9103403400b01190380c1c0c01002c0707c014982c2d4800000d06615520700701203055861042074545901c5e10740f43c030040440c14400c49510019070324141248480000090303032030b401c03260050400e81d0710f0282001042e4001c0310042c40312500b450101d5030480241c0d001102c405940c01d4410740014031404010744484a40d03005002d515101c2d0005a0502d503c8020320305107040030240c0014103242c1c4009010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 372801870 1250 372800620 372800647
    0x70c12060e010605062b020403050f19080a0c08120c0d0e1504060e1507090504060b130b090103020f0f04060f080c03060d0f200906040911061b1002 65
    0x60100304008000e0001518080c0014601d00860700d075840a0a81400303100ba180102a40c98440c0c401c01c0c06c1c2c00c41d142d60f00da060003590f900b0586c803410a24031680c40ea00c0c001d010f0340d1444401590780040e00e6854022682002c641c20981c1500450b0605410302075601c0038610781402500c41c1d0b92400c49140c88039800040390064030140007001c130480d0021039458400081d80041e5580c000d40015000c19810402234419103428a004103000543c1c08031004e00c941c650344400c1c007c08a400480c1d062110360f0303d68070440c0d16031281c00d981c51081c040300301d410400b1100100186c040c1070814140141004449041c96141e5441042e400e842504001000d122035900150707003880c900c1c801e1403d9082840c02c200d00030714510000e030001d48580912661102003181e00c07241c00c8111940b10300310449050032004040701c07806854013070b144160515000a40e09050501ca0386c12a01c0c1c100e00780810414104c2e043c00640d502641039800c0e020400e8016125400c0100401c203a0b2600c94000180c0d5180c00568a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 372803120 1250 372801870 372801881
    0x4090207081b0a290610050f0a0302091008150d060b031204080105070e0d11060906160c050102190308040c0504060f06080c04060903150f06081b0f0a06050a05070c1206 74
    0x2e60100002641d029102c04c40c2c2055242e2041c01130f204003c2e10482900c040d2014090698801c80020700051000c0c070350b561640142c1280d0005489810440d40c0c10700d0305032041203003215407521309440c10f60640300c07602e40300c030010040d5401f840000540280c400c0100381002c44814074106c2d10b100008040000400074800c49511868510303000148030400310015074084d00310301c000b4181c00c20740180e114590365414121000c0342c074010845030b607885010801d034003503184803a419110700ca0484c0e4001801c0d4008202d42c082035412440d0083c1840c440d94050f41c024002400584011321050804280c50b2540d1050801a04000c40380104036407811800400204008040d012347c41024842004a00d420602d24802c0c0e0340d1004031000300321408488540140001701e0300c05a02401c090b80043d08080c0401e965075490881110742404840103014000e500d00d040c0c00b0103800c10006581044090301c03071009403405a2451912a28007099074880b50071400e00794014005c0828000500400c200c140d1082 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 372804370 1250 372803120 372803153
    0x60c05060609070804031d0907030609050708220c0302060a180b2113020312030105130908030a09080d060e06010e09190509030c03030c041409010b04090207081b0a 72
    0x4a4900250700800301c080185c4000d05201c0e40c1c10310200050ba401c00031074190f810140c00030200b850a1034004014001c1e62040d108182d16150100f001d02c1d00c02c1403030740d2284150120207400218009040042550000b4094a111000000110060f03a503c0d00030b150341c00d07880c4c0d00c00348044441104003588907600e9106242c4810100712450056032821450350600603250030389012a5030706910070040200d00c900081d8140500002051101c00d200044c5041c0c910686801c040035000c401500120752441002801080301440005d000990581010850521485000b800c0440d13080c540340984640c1d80220b03425401d5081040712a5a010360151052201250f0007045406d000f503140d40290b090000c50340701c82352500001404681d040003101c551711856812680d03245092900782c2d00315086401281e40d41290080c101a01d454081c0c100f505840c10044913500d0a0b1900441e10000e43c803000045551100c24401600703040300c0814012902d101c41405480540e456152074a00040700091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 372805620 1250 372804370 372804379
    0xb0303030f160f0c1e08030f180102040b0f0a090b0d0905060a05220c1203050408010f09051203060a09060303030209191401122703020f01050705180a0503010501060c050606 76
    0x2000302d5039403101015900c0e80e0481e001e048a0085c001581c09040082c800242c10340304004240300d5035052007176519100c0d110616113902d11803c040f800364244e00c603034428400d0340031041c0030f1040840c4403100144100700050810000d116914826852160400607000c40041d940d040c0d400306102c41440b0040c3e2042041c40304001030f00d012914103c90f4040340c1d031240c0c0e100752a444000204440e9280550240c8020310034285118603501e0002c0159000d0b02030b100c02c42d402d0013800070704030300c09020b0001403d40c0500a461211106030b40d031060354000829107540480720340400504440288100e1028600aa8001d80e44161031014400d038100c1449116588d000c1c583c4040000c0803e00d00a007003014030910700f104d00901c001d244540136140b0301d103c038074008007401c4042818441c41c05441d05114825001c0d80e046501d4030303c083e401c0b150111101008294100110b803402c02c001d41c15802e000314024180003400740c44801290031242c2c00d030010f10106412211000034004204105907000c40200c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 372806870 1250 372805620 372805637
    0x7021509030106080a1209120f061e150b090a06110a20041d0c01030b030309062b020406020613060e0703050105010f0509060a0b030712050f06130e070b0c010b0303030f16 75
    0x8040c031003e0311071002c003074210f400e655010001c00904bd00400d40302c61007030300c1d001905880c10514400074a2a000140000c04503010002822001074050310300c6c540004014450b014544101034413008081000c018030b42c0110f03140000001d081c031603c43c07034080c0e03400f206107030a00c40c1a06000c203c44c00d440c1212031210b140b2212401403c03000920040a0b002841d001c5004d40741900803d01c2c502403007915607840b8002041040844214002280c14440803030120801290746210f49000ca10542c0136600040e00f10000048450401e0321400c0400d610883c0e00103051103d50b801039082002d160800c54859441e00010441d0070504c50400001e010112441200c50900c000000e607540114071564011140c0400094079943c010250003501c0c2071094070a020074641003045840214007160960301c00c0c940300310800d203481221f110300e20b03810300c1000090050340d00f442400c1010380c01c00d042002d419034903980c41c400d0340d4605001440c080d004459003105203041c6054141819008642188104003c0c6d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 372808120 1250 372806870 372806879
    0x8010e06030a03050a031d03031b0c0d030c110102071104051602190614070c02030d030203010e060d0c0801020414030c0103020a121808041409060108070507021509030106080a1209 79
    0x300b1030710034496050800e00e540e20403072002030340586180308a40d5051550b9610181d0201c1004c40114421316281d02c00d918047d103a110b00c1661b5000f0b03034002c600c0e45c0d4810030700c00010b1402030f801b180c540500390809082e0800508015426603000c00300480311803045c50000e456609060080d60380010844020f00048003803450b00130b50390308414040758020f181400c603104c20300038a81c1c0300071241d02c220425840580f804500c050000300041000320f000c5e03c9902151030100d0301c2482540e050b07500310140e0003044d4480310300b0441211036150f819650b6207001140010741c54800d20040005050071304842c4100c810740300c201800c1c9030b1110318440c181401001040e6889500c60480020380c581544000761441c00d0000c422101803000100400c820000180400c1038140d00e50500c000000854050080f542d800b0011102c2c0312040e02c828021413410700058005242945070718998481d102555410020031100007070039555580d020701c6d056004207100c03005020803002c4070708482000b82000541d50340751 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 372809370 1250 372808120 372808123
    0x207052a030c0123131203080108070b040f0501110114100303110a08090d060b04022a0a1122061512020310030f0f02090a150f0302033d0204030308010e0603 69
    0x14413260107100700024602c59030256158140080c04107024029011401803401600d200c10a00034410340f0305c05c0250000380e4400c04421141540c2a9030907410125107460015544240075151490095480c0d040f10000f8101d18800a80b01d41c2e01000044d1035240b40d41005040d0380b21a8500d100341d03420448400020451032001c44d00c100390706440700541c2400c1818548003d001d0791a02c140c0c094000600d01c6030002c0c04107607201080c080e85a490031441c030744e080c8041d6552060800100f04000c0d650041d036081c645044013101c41056002c40e114100411440d0a084611039080080426502c0d1102c41d89e0035400005240719811041c021440c0d41480c180d034144018070b038032004051009500a40b010014200810f442c8241d010300b00c10b081b0308024001c60b0241c0403c2c08500310000849000191040c00c41074504203c0e9006400740400740300194100480e01d8901c2c8848040380012224684c47c48580002104412180c01005072603506500d0000d010317110690242208140319000d0100740e580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 372810620 1250 372809370 372809417
    0x1715010f0327140709060608090a200a05060c03070b070c0b060d060f05090a0210030204031109090109020d050a02130c02030a0c03090b1c0b030316060207052a030c01 73
    0x1004805909054424509411404000d06090142c1e0103032050004680011b50000c5080d21075a8036002e0440e921b04031490383d202c00d030140252200780c1d07840c02c0800c5004030480c10f00504801038201d034035443c0c0b030344081a1164002d003180e00306940001010800d00c40d210b000355030800c05034a412400000a0f445007415500c000c0c14a61213804440c190204012090f400419594151481805103181036a18252105c1c4011400d07400703a0012480c41d03215038400c0c400c42d4140d13640084460904021101448411100100224859036a6194080142e40e8040000554500c18001041c078044c0c0c92050103400c00c41202440000c1c2d0810126000ba00e8010080c0d1350301c0b080b913150554526906040c11541c00d48a0341c0314841000b00041d42c180c145c021140c254201401c5114140200c401c0d031000d050f0b980c400c3c0281c40341505035403111080094921307001041d410340140300709ca0003188881200703802d0b40e5180b02c0f03c865003441c502c1d00b580c40b03081c03c1c00003600264090803c60205510307103421400f40742 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 372811870 1250 372810620 372810671
    0x303121802100302210108010b010207080d2a02030a050a0c120b0c03070221091801050109170a02100e03060a0623010c0506070503073005071715010f03 67
    0x10340104000800c0c000c0517008015522180d14920010359591000f640208801c400355030050040c0d000101c0c20901c00100114140210382d035041da1984185040422003d42e001d01c94100c2e6141407107900985e4007088510b14060095000e00952400d5141c040d001710300d03560046d035484404405280104003a42561680690700030a8207960755107590b400c0b03043c203900d80c40c94000710b40c0142d58008420545030261100340810b992a6010328440b891901c1414000d108160001d0f4180384140494029950090a0b84401e80111071010b00240e00003200d14001d8224a000113040f5103180c031051408000c2d081e0070002e40e91040000031b04045541b400701500c49a01c0400c59082310803090141d01c602e000042c1540c002040d19034070b081000d00140a42c3c02a14400001240017001e8090051082400c5915000c0c04503000d2111031485520400f030007009060805109100f08800c0e400416207010714454001e000180085040000005d01340103142c003850010107240400302d42a01308000115500007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 372813120 1250 372811870 372811877
    0xa0303030902010c0c06120b0a030c030f020a09060b030a110c07090506031501030602030f011d01230d06090c0902041802070804050d03030c0e060c0604031d0a030312180210 76
    0x1e410600040e9603e00007108000c0181018110024015030300112441c050f003421541800031420034001c0100901242c0009850103400b40010800250645210080d5502c064400a519903540b20b28404a030b501e9401002c855500004009040c10b051007079405903c0d502c00002d06299030010a0741e5241c2d15405240340c542d5a802c003140c50307581c00f0010116400c04c1186c00103495a124505400a0740094401d41d02c9410800c0c00070414200a499807070710020440401d02480e80f030180e650070030f8a13800071522241031060001047d1621840724086540d80140030200b04c1901ca4a0035401c000f10303540c880c4100320b20510090000c2d00c4580707221020b500c0310750000f5883d03007900d0902c4041d511655004a82c0417010306032900425405401042c0124030742d89464030b04411140c01d01c1038034440c0f482d624683e600507031300280010340509000a41741030300450424580710440041000c0004941066022540541e03c280d0000c149004542c98511054101280400303c0e40c00322f20007001c0d41c1818400d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 372814370 1250 372813120 372813131
    0xf06040908160c030b010e0f13060906110702100206010f0324050f010e13020d030f020f10020c0105010f15120b040501090f14091b150c0c010f030b0a030303 69
    0x50000c0e80707080d1103030003040205544252416241140107070500b84812940c0b031317529000000e000c100f610900c9124044801d0129a19030319845a100c00b24a80d0342c00321202a0388000c094040b583d10f10419801c80704403254141e40d01014010003041c3c400101c1200110741c014030060006406400035503044a52080340c01440303416034806080010724011101c00030a1904040100b50380c614405c240c101c60100742d46001c140c41e80802880d40141245c0e01a420100c1d01c1111000284250381c40d1000004601c1504c1414001d0b41400d8105000c030406038900caa00415000640a802e101d41b40c014a007802c030325000c00e450710100ca41841d00700e1007840c00344803002c0c80d041081e21444e0484280005d00600810556868101120007401d511600b071101e185001044849442d99805103405400c00c907005180100380024601c240c245800c2e0f400740c002080040c035190401117180501070320a90388000d051032001d20000101041d180003440c900305410817100043c45d03201d000840c0c003940d03014940441d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 372815620 1250 372814370 372814373
    0x10f06030507062f030306190501050a050f0d060602010e0d08090a080319090302070306180f02090a0b0303070b010509090d080115030e0d0e151e03062101050601020d080f060409 78
    0x100c4500c1c03402c14461a20811303102400d50400b00003076208803021144404182601860329841e683c6c1801468080f41080145101082c0100080c1c00340c00c8040264614002c00c1c0c8008005440c01b0307070300c5207015039113854204600c03000503c19044420300500d801c5800d4642906400d0b0b440e100100041c01c9810000049556a2090302c0c40d03c0c040d610344c80b001d00010a207842e000f5615146440156800e51078840141ca51009a1201080c03480d000120481580300079020481c540a0150100c4803603503440a10b0410360310144007410246000e11841005507150800340081060000d007506a01d0f003020f2030000c8846d4110540c41d05441c80c15614000e040107900094005150300c010549a0b4400c00c1b0111607038903805015900140010f403894440da03200d098030a4002e01030300190080c2900009498440d0a400390003031980100003c0060100400207106403421004014118180b80d45590411220b03580400403401d03503400c1850405601d1400519100311820f000d8840d5100340e445518640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 372816870 1250 372815620 372815657
    0x1908090c060f0a020c270a0b0f010e0301150902090415080a0f03021212040c0503030307020d050702041107080a0e0303070b0a200c01060e090307080301030227010b0c010f0603050706 80
    0x40d0004024003550b150750302e0701b003e054041a1130110406210050800a402c00103107000d00c210078500a003982804440b42d01c015507007042186403d503010741d40c0740403051007214410340c010010b08a4401c0144ea0384003010901003038a0034009681c1c070341e21061104204c16500043c00303480042d00050031200201051a08031305209069002e01555000490700091081400400b640510310440c5c0750038007627030f03aa0207040c3c4900088881c080941c01503014040081d00420007001d1161004100103034030101c4040044070358100120583d45010042251510070f80c000c0f44030300301c2c0d0f0400c4000310f080000d1950307070030742c01800100012440364444c2d00da649612800d40e5040c951860722400c140d01c820552414a0003001c0a2044071100040075012415040020040304c8c1d003e60000706c4546940c1c2550248202581c14500e0251040507007803d4400a60300b80303112a010b0026002c400c0d40d01c40803120418255a5015254001145400401c10015400180440c01c803071580c00c11600c0200c25001a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 372818120 1250 372816870 372816883
    0xf070b030c030c07020a060815040504020303041511070f08062809050a0f1b0501090803030a021b010c030c09093b010f060f36020c031908090c060f0a02 67
    0x1b50420030030140414401d8111040318484ca6001543e0103c44500134100401d031002698080c1d0160010001881410020100c00b60550040d06151039141a100005840d0041a500078000a245008140500303002445151341042d40091110046074200a035601441c0601812885096440311040200141807082d207c030b642d0010504070611186040c8003418142c07225041e030b01c0c280b481d200441c05601a401500c08e45207031000560541c1d9032060640e000754483e0a03000f0304400e400382040c42640e800d026015043d806031341d0126100314266405041e400c4660403250a071418080d1000180d1a41040d1903a070100c142024020801c620b580c40c9241c00e000020004903508003d401e00c100b4209802c0b0000300e0300340c5120804115519440702d10511019003102c00f200184401c54080901e042c2d0000c80c0d0101450320061600005c81c0e409441e60744160001d001420303080304444205500080c20a80c00207084000c2c0101e883c0711400510a0300c01d5110b4104d80b000041a5601d4191080007107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 372819370 1250 372818120 372818123
    0x70b0906180423090a03020303040605060d0c15120b0d03032d02031e070c030c051203090609070f0f050402210c1c09120f021219020f070b030c030c07 66
    0x400c80900b12140c2080058060f18141281540d4540030801c1c0700350009404003480e400d0350140d410340c1c889580d442c000d8400900b0650b4040c0c206c40c08a40407800090207038000308a25804c04030082030559000e4800d5210200b2204505e1402440300410b1301c1d81800b80c8402030b81880c001800355111020941d450000640b40340d41c907500c0851100556903140e00644c01604420b008040c640b145160f03000302d10b007040350f03604001401d074150480064014103c014240e88a0741c16500341c2641c00f1a05040381c4c00840e0300c0041a80900140312400b5000c2c404e2070090030907100030105090620794002080320151083c280203690008259183c8002141e00c0301500e50100d240f801c244c04e020312241c0382601300507050340c07210003036003042c041c0094ac510504561950000104a4540401c581a074800d042c03e404401540501400c045403801607400802a60250224500b81e01009620003441d044035002c0080069001e000b050000d2410041920381c4142d002c46400d030390b640e038940303441d03481d0040c01030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 372820620 1250 372819370 372819379
    0xc04061a0318070f0915061b050319260702120904022205010215060f040507030b0a0608090d0801141020030301090509010c081816080d020f070b090618 67
    0x40128541c100200204112902c941c0240055030703110b0002c00c40c1c0420307441160041883c41c12503803101c42c64861048c0e0864001c03000d03241855181c1c61a60050400c41e150400014161025140c0e50b5903080d0b042107000d500d00e506101c103480c1030500603648400d111780814540c20042812680c40c1c0e00d60f012511030750f0b215100007090050f0005029000941d6000303082c0907000700301c99100032605040245220b1000100848088095202808014440078007290201915444800d200c5c1e216509080000c1c407140e941d561041c9442c2d41d0322403c3c509410719000c108144403004202401c6124000420280100c03880220b80d000348006442210080c010714400701240c15004060013804400742d812a01940424002c90b0f88401c4160b0803984000c02c54004661607001191a4541d40281c074a040701e80c4500710b41003092506260000c007d49036010320f1480c0d0110344418490340d8180305165096039804010030b04030741003802080441c05107100c01400303500d0204510040b82c40100c2c3c10200e0381c00150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 372821870 1250 372820620 372820633
    0x30e120a0b0702060906090703020d060f05160306120b01050910030203070e070306060905220e03070606050414162303010806090c060301051309060603060c020303090c04061a0318 79
    0x900074400031421981200907020360400580390100105115103e40e0b020030151030010b09540c20422120310341c5500780e034900c0d41d03006902e144916a21403240152000c888001d800443c00e0170080560b41c00742c1142482940c46540100007800c01030b5024103480d070482c0c072004556154424002d14608070b2707101960620a200d0002012021003c0003802072601e0383c1c003405150f0b1141c1c1c00340c512050b07600c20b540d08440340103825a100101803481644004103203101045202290030700303500e55003011200740c03425555200104031a25182c8a200340304000001c3e02030a0703107031180d03403910f924100760406020f03c203a401e01d08404049011840111030310810070b10b40c0329612140300c140d41f640c04072425203140c41540c8820f071040c40d109081c0c0e030403030710010070450001007152441d801804081c80122500380e190f400c044005043d174001c1d8101c142c41680190349918240010340d14043da080e00150045281c00c5040c400c60303068541c010348030400000303182d9880d1142144e10b03104038180078460200c0d020f141c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 372823120 1250 372821870 372821873
    0x50c040c14070807061d0705100c0311160815060a08122809081911040f021b060609130f0206071509080c0d050f0a0f0c120e120f0a030e120a 62
    0x4062040c443c446c02c046a10b016110814020202600d000c1c031404100c1352400100003e10804c9006141800401911f507500c0108003103070450704c0c01c0d81103c0040d801400c41c8524114128000a60005d000c645a000c0540780100c0b6640b52040b000442c40710000c001032407000780411080c060340e685031000b400100608046d100401800d810b0284803001d01403200f00c0e51030300d042030f80001c12841c0c0044401401d001140d003004010080540c901500d181c0074070400c103101c520030b03420300006d190b0700010380941d01c0e010b0100300b0b0441004240c00807000c3e48440181c04180003504607043e0980c141c49c280d50340c2c0d029003000c070380e82c40401e104070301a80c2c20701040404208118001d0310800d01303280101d4072400140c1c201510386004001000c01400350512001d140346218501c18a01a10320341800003d00071a03888601e200100d200010f80460203000c4680c100c0d00b0440010001d80090b180076080150074082082c1e251100d10001504002040d0074255556490070610b601075a244006c4624000d443d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 372824370 1250 372823120 372823151
    0x803040b010f080a0b06010e010e040504060605030127030c1e030c02030f0a050604020f0402120a020307120b03030a0e0a050315060306070807091a0904060b07050c040c1407080706 79
    0x74040c40101e07101c10b4800186030540018842001c41d0721400380146683c0302001114400700300c982c21030400100c2c052080303482e02d56103c4c0e14061402607002098a034102010f150030b45004107a800781d107018549a02e020745001041e45010a9031600d4401c40b0b0400c9070404c80c242d440317409a408228201640c00f08100358009000c00d404034800d130191860745461008990703c603103403144050090740140001500515149920100d10000200010305012243ea00307001400d400b190001900f42d80002404072954008804a08190b15404148845054400801d441f801050150790601414440000b04c03503441001c3d4802814010342113440160011034144010300040c0ca1b44c9001c6c0c000c510108042074800c500c000d10801c0c15031a50441c103441d2140c0401c0003655a54070b0f809001c014440042981d8136130041200908503030b0110b607203520391400c100c0c0c01c0464085810348101e01d4500382c241c0080c0c1084102352845640f1100c90380360316080c00c2c02c40492040d04030007440f04d49000346d001c503050320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 372825620 1250 372824370 372824393
    0xe150a0206010b090f0607140303090a03020705040c0519210b0f0901030209010b030712090b01030203011a03060a090222060f140f04022107030c02010e0703120e030a080304 76
    0x555508940e01d42c0da849450354864400ca81c021500200c000003c040035007400001050740620900708060b5000c80081c0c1d00342541c100782c03008040b94000320050f40c00d05a0401213070001e800308580800107224042005032040c0300c1c1c1400d444c12003103500c070308241007405031140413403020003000031409819001102c0c20041000142c4d03244a0040951000e21500b08481507134140c039400307010314000c4c0c0d0901e1087c040d20b410040403d0100b100701410884030b840b141c000e5030241c81c4034911010607941188109401d41c0c6000c0c01c0200d054407a10fa4a190380d0f40c002407580c3d00a21894030020b0381c2c03042070001c40d0b00e14810003103c1c98070105a03101507145080651040b021900c052442106082c0c0390000002d0135440040d49690204040107040010b2070705038000c040322000400d515a4682d110950700302c41000840b101000f181d62071030158455a02030060008220000c0040c0607070b90b05598505601c020154019007c10504060f458000d803001c004051005401c101041d40780d141900c0c00c003a2911 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 372826870 1250 372825620 372825637
    0x1050103050322030c0504021e070606030201080a0905120f0d0612051c080406020315180403030b030d05071203061e1508040201120f110a020c0319050a03030b010e15 73
    0x100c030f54801c02031400000b9004252075000d003144450700d280c101007002039001aa69a0311001e03203604030b100b41d4036400008200b0b542c810600816154a14000984103140083c00c0c0322846040124003400500e020035040c4d840c4074503440e0103480b0340500b200307001103000c4c0c1d0344503045c458608030012541d000307801d01f04801c4c188503500311241442d10385129034042c2c1c3e180a900c000b0134030a030003140c00108a50082c560108107019000e4201c01d151001401900200d25083c0e13900303441000b80710030306d903060240f05a01f103401e800a0800101801005109200d28107010b8a0309801002145410340b29802c10310040c4081e400701d03060b00509030411a400156445421920520f02210700030300c0b40070f10b2003540300796016110b20b03081c151800242800f03040ca011060707210550307500314261100d40c5140505003815850780184581c2c48803405040c98074102c180a41c13040721803e04140001440011143c9089505160104149904100603078414005070341039603020540c920001501e40480340a4034508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 372828120 1250 372826870 372826897
    0x20906040905150d0b1b07060507030902040f0b10031104050301110408060106032d0603021003090b061e060c070b0a030e1c23040e04050c01141213030e03010501030503 74
    0x1c3d0b030180208024640010350040090a04400040e82d201b0062011401d040754462218504403160342c490701110421200d85000c00d0383c8141d12419404c05100b8200030741c140d40000c02a04035420002054981c5880c1c0c01d000301a1110300401074034a042d81524028407025009202d002458440300102d0307007140c010640a84039040000903070f14824000d050702d40800c50061035813000780c180101d10400c0064002c00480707445d0750303000005860303207420640554459940000e008a10f0319043d045441c0141050303100d106d004c410421107500401c900c038003600d41101c460760384065420340e643c10144258003006200380c000c2940401980c1640061007d66409016a4002d030b003508540c1d0f071135954401a2070000354480002480341c080e454250400c030060002e9540c1055560740d0300c00a4090129400c44180d00030315010640c40d608988000b00c68020318400b241403416444000c419a14014840c159101c09400d4102c1494066030000320301602c0a0000e20041d0307140c0c00c2965885c0c1c052070512031f10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 372829370 1250 372828120 372828151
    0x20f0702180f06120a170418060f0608041b06080f09060702071503060f0b0c070602060708160302041e0519030b040615050a03050a11060c031606020906040905 70
    0x21540e140700c86100344660216106203895501c03d000b1182c00a0345507001d244182d002c3d00000c9402c1070204455264440d00e074540d00e604101041c0c03a003034482c10307900007034905140f420b001140c0c2ca03207158410348070b40d4a441517995030346003413150000c520000f4034901c2400d113000c04030302d003940329030031500c00c07480c900740d04c0380588038a4002035a4400c11655980103800004041c0700b00b19030b6414000e20399590b8074001c20442c0d250020811103003a143d01612010000091822001c90180102e20050505001420749481e115202a01c1e1001c0200a442a00c801a840081650095041ea4064018030200110040e034100c51b816100c1c8090090301d100d01d0017440c407072001081816904041d80d61043c00c0030026103455031850302030002420780749403010361007801240a840b2001050000c601079002001c00f0300c1507082462594190810b414007c460030041004c1040c00081110f003040d034459480d80303d1824a0400780001e0250220300d5a010000150002e5001003981000303004440b464688040e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 372830620 1250 372829370 372829399
    0x2270109050d1e05030d06080c180c07080d0f11090a05030622050f061e06010801060c03180b0309010b1e030d20010213080f0705010219110301020f0702 67
    0x80d040c6600400500701e040d218115400c5003014403c0f103000d98451011241040c18040d45541998a20340007040d0991100c0d580382c41c285800340380445040000342480a00d41080001a0b2491041c00d201900c51a40003614140d448015448002402d2a0100801080300340d45040b044991050040c644644040031000c2400e25021034054003d0090b04070f00e0303e114286d10148024032000480c1500c00340079103040c648510303200740199840f0381102c036903491819a00d26190842c1b810050320160400c0181300052218580100f4215012a01030a00010a0b00d20f122200e41038a42d581003038081c284044103100402030305400c18041058203e4580303209800040110321004071800c9038542c90743c44908041b0030303e03020321001141c070118143d00481c4202642030f100d0030380c4d000f418074082070369100504011031172043c0b002e0b80580c590b07207018102e030a20b080f000039954603481c1254003c0fa0038500720113081000710801c041c2a203001400964661880c00c8000c3c4440e04840c030700b0780c000c008c140e02005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 372831870 1250 372830620 372830629
    0xa0b120d020c010311041a07120201090b13060b040c02030c0d02160e06030a0f050a140f070e060f3a050a03202a1002070e0a0227010905 60
    0x2061000c0c550040400c425080c0044001e05005240060070300010040411204200d041c2c01103a210030f480c120342e95a1131803808030740c032800c060618011a4940300c0c080300055011011950044608035400110b08010709016008046c400d43c038590041c940f8010404054000c005400320400340415140d0302e0020030310507070319584880e011030710b110803070074091250003400e58250f9001a0040c0440e00308010542e20007800401170002500c80c0e0f07000c500c4c4481044601c07000c100f408642507003e042564100e021440c0e0ba29803600882150398104800103441b0344548180d1201032100401d054450750f14168081d285900e180c0a480030182446400c081908100d030048030103e5000c8024004d000c8151021500720444c869400303041c051001010362411401c00080c8010043d408410004110380d0340d5210051003280e00c1d69014486d4610940b00309038022958034210f41e4400e0600c0e42d1a40c1d1340c0d000c18020301c9000314000030301950b11920260b2000e04241103042003020703224400340710384880802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 372833120 1250 372831870 372831883
    0x603061806010513060803040e0f010603090b060f03010e120421030c080c10091a060102061905100504090b01090f09020616150501171504050a030503071202030a0b12 73
    0x3240e0a9001d40010850340c184081d440c11110009440000d01d10384801c070032802c40c0d0050348040590102d032028008981c0030481c105004144030304007000080700561720003030003407001404030344a00c0a1040456245c3c5081d005940500d5400d019a4070401c10f1101d80c01c07440d0060300400300e051007006040f00c440c0c004100d1039494540c040d2140040302000d0340d244400d9a00400d0003446a0054084419040b6054004c00403028031959059040750b1000c41b0300103048100500302411503003d0001e22022448600c1400c0451076044000302c0c1c6507a803070748086007500041e03000c950424a0300c082c0c0c41c103000c0244a258140d13010035100340000d80703c5052040648005400c00380d07000b6420055841080c07100c02a440516114043c1245803a80c0014400c080700c1c3e00764041200070a815040b180c242109001c480240380045100a819080a403220b65403081085002028040000040b5400a0140415421400030703208155501c0c54854204006403036280360050241d080c1140c01a0303e60780c00300e0b04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 372834370 1250 372833120 372833161
    0x5090a02120a1a100203090d0c03022d0d02030f0a03021608030403170c0a060c020c1003021c020a050706060f031e030e0f040f11280507081b01050708060306 69
    0x24405108043c00800030400d001c0001c607802d42c4400c21602e2166140c1d0340d0904034003802850140b020703502d1030052000d482c2c010200e000b004000080403005e0315100066042c4803070015502410300322124804240350000d4000060054032412000604240e0b00003016400d000900c1d103410480c56841750312541d640194000145040211840c070104942064090008004640200e030040d00303560b2100d5046030040c11900c00180c0024000305094240010200c418501314030b4110310b40250344804003081c6034038000da4640b040d000144a24854400c0090320440c680150302005415035402c2c1840a8070b60501c8111119601181e010002030304580000c0c40840c2c06031100001d40110a041108280450604a07801550b400815101c14640c1c4a0030f152011011406a40c4002e01441c1c0100031803264101c400c142d040030400700310b00c0c3d845000e403031342c080d440400251030f40207a610b40070240084c0342c00900c03290301c0e0401b00102e4030b40c00b4500a0154100b941134400c03a4642d0350007407030000c5103000c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 372835620 1250 372834370 372834401
    0x10821030705091813030807020316080d09140a0c15020615060c01090302010617030705031c140702010b010315080703080d1d1b04090b04080c0705090a02120a 70
    0x207509600070001808803074002031202411650600c5000c084801c01e41d0341000f84d03a040982c0b1030405400010301904075040c0c1c0000c60070000511b0500c82c221010f0300008041c1c2402042038010b076201074000b084856844101070000d807464075032860390342d050244181c8501d500040001842024000540000085c56025000d9903590344140308000c150f04c8440c50300000100b01c55800c901c801c1c80f45d01d80c418440c0c1c1c008104c203840d0000d10300706050b0b0103a00c050280c100308002c0d00092400012a400c40a411000101491070649158018a0240450000840ba2008002550b036040d03020f0b11000c60700342c03010014203894030754880c42d007001402409010b034400038051021600c40c501030160600c041c400498001b041828100340c075202c00c0300b0b821150707201d07012501814400040103808030000b0b440c100500c2a41d5140c0c0c1015600152016200700b130001000542a0010700c03121024010161127030101c0c0c1001540400258410b8461034250710f10000441d10b895098055259290b40d07500c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 372836870 1250 372835620 372835627
    0x20d030b10050f03130501020f090a050f01080f070c050307060e060a0506060a05091c0b0106200c280b0307030609180236060a080d0807050c0106030507030b010821 72
    0x10000607180c0d0005e02440c001500301c4a4100c00070350240010300c0d120b500320756080d45503003d5001b803240320405600024803a400c0700062611a99120744901c1c0d1040f03084001011070380721448192060784003200e0240082c00001801000c0c041241c00c190070015400c1300700c8075190389001040c001c5500030b0f65145c2c1d01c008104100480c103480350015280300d100090408001503000308000e81c51803564907080390301840384030042004e142c1100d4001985641c2842500da526410300104e0784403424a1a07036442403080c400d25070b0702011103624451004842c041a0352401d80c032241c8a010b290011500f8000007402d0403004112103160780201c41c0611600d090300081000e042d0300700007001d046410440d0700c100c0c00c00b104071007c00c54004c0c0b1861400d40e8007041c10240c04c041c42400b0320040785030442c42481e40901a40c00301294840901548a421440e0032070b140d6008491003800b602d01c55001421501c520036002c4103100b030035601c0604076540c100845030081010601c3c0c6082924943c0c03d45d100321410b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 372838120 1250 372836870 372836887
    0x90a0b18070501140f0d0608010513052e142706060f01030908030406060603050c090d11030708012a17012106091101080f0c04030f0c090507020d030b1005 68
    0x110301481341c084000e0501030074502601079004040e0828a0310030320550f11440104400310080c41016004801e01c0d401082d4407510761034266031450320106140c43c0740400700b0b00c3e0389c1400d52000f0040000112483c24094076007100c29076442120706403000c0c01031000449541803000008141c40c00280c6000c4d0180100d83e48105c100309480d444294802c0c103060f2035000b40400145038100451040740304240000c1c0b03550400303c1c0282201c0000700307041420101009014456900c1100f44020180e001d6903a111350451980428107140303d80c3d0202e42e9641c00c090780300300c52020410110708200c0000013603107405410904102c5984a03030000a210104a440051258118548124a0f100e120140b05a5641556035886086403020b420a9076015112000c100c150740c0d0285c40190020348403904041c06003822114502548180c3c800200800119400c020422020072980c4005110000702006a8070340654043e454050648001000a02d422070030729482c034102d01c40101d588815902e50341400c651 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 372839370 1250 372838120 372838127
    0x30405220603080403050d09050603061e0409020a090605090a0204030c060c05010228080f0108030a1119080a0f08010b0405150702030714130e1005040c0e090a0b18070501 75
    0x1042010340e403640380d00020022680e80030050000310300c81c50080030f44c0d00030194014446510f40c0c110620562041003440700356980d44003820000b84420740c5698140304c05200141c0103005621000f50422902240020018147d41c00141141c00c1580d0030307200e55881d410310310101d21a07800300400d1803004070000d02425204143c90308800e481600010b16180e14070540040c4208a0152910301405010581d1307400d42c3e204481d260000840d00280c00154101200340d0b40701c0c041c20701110100248688001e01e000340c1040b5074070320885a095080c0c0801050300b000c2030107a0001465402040c2d00c1c9100c00101481450824103d81010320705e142014106030030082003030111550f900702c0c8101440b290000d65070501501d0001e100901080c0c00300002c10f814845040303102c0c942265298900340140d0302250002c110f006450841000005261780c441c03030120885001da811039003441c65414100070307441c100094240390090141a4640c19036a8070007032450642032021450000307410041042005500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 372840620 1250 372839370 372839419
    0x20d06090c09051f06020c091501050d020c01021b0d0f05072316060c030206041b0e07050d050f010b07120e04020d1401290f09090c070212030405 64
    0x1045101c01d60382552404080142c80c1c2c02e4810204a02d03500c0e0014082459621031400141441d0000d0014005d06000080c810000202042c000010800c030b52201680300c0e904503507006d10309403c215110029a40d40c907000390806d49042903140740c54400130155013000a001000c00e502503032001840c3c10603040850f07964010301000c9440824181d00c0b03040304201c680502042580071030080156148540249001401662020091060588043e000f2a501041e20b0340d2150300702c200c0032141c1c205880d105162004a031b02c40124400200d091007001c1d90f10400800703030b4442c0100c0c24425925165010004500c0c00c3c45814a1004d0030018000002d40340501c1d10402565420701d034550411800100b000e90380030701d9144900903518182c8a41c0e40050303101182c051b20240703d10200c10304c2e0b040b05916a082f0b008084450380c0070042845969500000200c2c4e40c5480041c14000c0c190034641d80c6199039270010362080b480f5034082e82540030016000401e84045600c000c01c50380c40425000f040e481c0001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 372841726 1106 372840620 372840623
    0x9010902100527030c041118100c06050711120c070e01060e120f030d0902030615011b020301090f140708010603080d0b010513260109020d0609 63
    0x18003500020a40840007800c80107540c9090340081d2605c0c4100740b00a901c503080041303a680901e441005800c0380c01899600c5035440c20044e081080b1100101c1c0e0711000104c80c180c04201060f01c68000702c0e089100b50070140801ba080c00701035802c2c9002e45100c032841d1b4030001140000b0403c1000305000400107800c503421554101a40204801e000043d40d03842040110001c51008600b4000d42004403015001c8950351300300891a81c2c0a0250700809a01c030740207000010381600808100040c0c01c480c141d440c01408003142d1014a850050014240d03095980e80264100103003450f00d803803543e0760091040000e1208c05c41412440c0c0a0250000c03040340c0d04200c010000201001c00381d8441c40210f0101003004038007a00103e6290003601802c0718502d09407000015503001184d1b10309003079003103003c80c01d503112519807007a402e941040070000d4111800c024580080348255204191700c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 372661870 372841726 := by
  have h0 := BRFrame.cov_init 372661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 372661870 ≤ n) (h2 : n < 372841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
