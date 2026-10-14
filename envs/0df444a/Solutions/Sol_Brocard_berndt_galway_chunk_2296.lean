-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2296
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:03.370855+00:00
-- url     : https://prove2.me/submissions/b17a57b1-9585-4762-ae2d-a9a200038b77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 412769784 ≤ n < 412949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 412771034 1250 412769784 412769801
    0xf0106030506150708090a06090f09110f1204030f0228140307080403060b040203010e041b09140609180604030c02030703060f05040c0b270411030c0d110328 69
    0x50303c0e00090f070041848400e4009104541d025aa0300d120203944003003c4400040034010b400300550701030701c10000d4400c00c0d004090000c00c0288454030340804c1c0141c106959000e2104c02c414901658100800d058000340046640c98060001c1d0041e5000d0041c0030400310b5070030292a03008511075030920180000010074030715000d152022207907260241c0c00d12a00741d801921040310030b281000c402e503010f4100760013a00d04a5a80cdc24019030f0301e840d6503403180600ba4016402d55012200c1080004061205006248480706011074140180c2441c0d410300420307250051071a4480003e005088039203d03c0020142d900035014135050440300213510000f801e1242030f03400500500e00301a00742080d96180c2e40a00d000782d1061704010300e401da4408800f04103014400c00d000744040b440c0d910414202113404420b040010042000500ca20403804500241d0401d07908000010004900044100311910904100500520100d4118680406486151071001024103c0002204e00051407910f00750031045c1c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 412772284 1250 412771034 412771069
    0x1032f070b04030206010e13150209010e090c09090c0703142125021f0e010213030b040b01290a020f0d0f030f060e0f07050c010c05040509060102060f0106030506 71
    0x1d241001d0030001d40c0c94200707000301c5c40003400c00b0004c14000b0b07401c0c54101a4a0b68032852044d00340c040300e46940001d4000c282c40d6410722105502e441e043d03645200308580f080000c000e20940b680740340010311201c080300031325441807100104424404641c0040e200146200c00c079039090750350500d024050380022020304500116803005414441100070708000c0c0e50250b440c82180103010450104202da5407001c01e40300c807081c10710300c9540003c0010303036402000f42c1984900c00903141080c0303060700c80003c3e1400d5000b6900002c012003407000300f180e440895401802d0144040e04070b0900f12100c49903070356901265565000d000501c030100c081c002d106100400700030100f030316055000460041c100310404d10036000064031300518151103203624441c140a84441802c0201d1f15515440a42400c1c100500300a0500805020001a0280901030740b1446401a41c51035112072415050000c01c1001403da83d043d5000401000b451044503c000c6044451a107404606600c40c4c4002c1124001c19455004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 412773534 1250 412772284 412772303
    0x103060b0301050f120f011b0503071707020a080304080306010e101b06090f050705010f0f0206130609052505040203070203120a1d010212072d030213030f0201020c01032f07 76
    0x35061b407040d400320301341c2e0001c0036015905114601c0225602d00c022960380c400f01e0080942d03c0065018011201ea00c42d5450040300c0c2c451010383c807a91110303042102c048450320000001c01c041940e104580603040e180c2500c0070071502521100c0a4104252560400c490f0032210040c0001d1101d160407100015800000c10907140d240d5080c4682c81d500315000d103a020683c500da108a020384500400214640300703034040c0c00161284200540c80c0070221400740d84094854040c500442c40612000b5800642912100043c540b680710004c956003a950109100d40d10600420040035008021a440b80c2d816000f00c011a42c0e0364030081c001080100c60004048607a91514641c80384150700820f000000c100c000000c070740d202e0000b01c4680b11302035400844641000448080060740c040345061540190030058184801e070140d910609111ba4000d0700d02d010618a104155601031021507c02c41080c030b03050000c1041d460030404074404c03a49410b031901d145600307140c0c5480c0302c2d002900c0041d1f070300c1b16100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 412774784 1250 412773534 412773553
    0xf032708100509070503340803040906050a0b0d15090501080109110f010e01050c070b0d0911180c0f0405060c0708120301030f0b071b0605150103060b0301050f12 71
    0x107a038034601e80911445561900740410015540081c680c4222480140140524410211150a040034104a160340d90340c16000700317408041c2100050001d040580c0042d901c40b4a84600507055441d5980700c240140104034040c07050300c803094101e4003044000c400110f400c00306c98003d0440b0040341e40c8050512842e0a00101b6098019084510310700c3c0100301401e50700c0100000c02c21600c518203d0103021036061440d001c0a0b5004102421317618414800f52100a83d8500c1d8007001644542405140daa50f1110f242c01004040b1200d0401190255803c1000584445e0050210f680c0504080191071011410703540301c1141c10100c402a1402615182e2102d64802c0f0580d03031094a4040ca40c0a8043d10b90440104804281580d040f0380d08861107140d0b100564035072440340a00078061004004413151040c8020389448506900d0038401c21000525290803000d034078408800c3d203070083c1010705090042107044030910542e41500c07011607149480f01c003110000b600703411f40a003a4200900885004e03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 412776034 1250 412774784 412774799
    0x1c0b190609050103060503011401090c051b0c1002010c0906051318020405090c1e0310080d180b130b0c0a021206060306011202060a1107260c010203070f0327 69
    0x107080440750281c0b018130645844804043c280c03249603009041007000c140040000401d1030b001440c646145081c0a8070b4a1024180b152102405070311151fa554050b180320007003400c040d08100d035066010300c0200011421044001d00040d101d1060340108400420656641e070500d282c80d60041901c0c3d001c0ca50300d0000c00550300065045803103894841c00c0040001400052098215000c00041011b0001008035468240840d40c001a182c0b0460000482c800f08202400300a51664041c16072a10302c0341c404a404982c496003419000940011002c0c4800000c0a62102e060800d40780c2c071810164503000e89068080c80c01c1c64005000e54400120740701112201d0b4007042c0203006100c103400740c4102e03a88500c07000e07810200302c801c02504400204004415148559000015a2454416100c0486d51002c3c0100340c1301404012401e00e100d42554036aa038401002012001744081c0055801c3c140b0360745500754002030382c20300507083c80108414580b01400740254105d5a413071110070800c041e030325410f8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 412777284 1250 412776034 412776047
    0x110708011d0d0305010b070f11150c160501090e0406020c1603030905181305010b03030c010b01030b09071e020f0d1d120316050f010906140c1c0b1906 66
    0x7401031280c041c04407107400c2c180c424040c00d816074a44d407500a01e440700d10707506c10558400b03040e000c0c0c03408668000e103096030303540300d04c4101c5400340700c0054242c40d883d55180c00c0f41007c2c040810761140052000301003000d40d8020500c00c2c12101d6502c00140c1da030741c0d0b5040000103480741103030765915401200e000c54400320107400380f0000c1c0c0740a50358118490b500c07141841a81403107080c0415080403403500041440782e0344800010801e102d00d0004c9907055024020074955040ba01b85100b103651200310703c5286580c584241c0400b424216103140044c2020007000d489401006070340082c5403000780b100d131115130082000300c240f00d0190084454044c850040203100105040154402c5410b41640100300e1501041c0c20000903942c0002d1403902d21882141c240ca03151000b000c6039680501c0c0c048c49141c160070b20803e2240d5001e040c000c0f8000d20090544070511000400c0c40c89400c009210740c201d202c00043c00459141031040c000a08500748100143c0000742c4000c0413030071008416000f103a203560041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 412778534 1250 412777284 412777331
    0x51f0e0a060816020f0615011101060b03090d09120803060d0b010803130b0c1c020a06090c030b0105090c0909130f060b030105060d1109060103020c0a03050307080c0a08040311070801 80
    0x12440c080c3c074000c0b1038100d844885209080f0307016404100031030000140c0030581d420030305050408003090203032219040e096270055408203410040103c20408850170501001125900d94070f000b54060b4101702c031069000c1603007040135110a10100003d03404d81c543d04c1d54801e001d504410a9081580e4420f40d036682d903403111005014290040c03e002584191450540b5000340740c0401500c04e040140c40101070540446081d0801c41c410f0400c901c0114404c5d110303000c0440d00a451002c8041d0550800c4559103006a11140c0079107080d10070003a84005034000d41d01c400e0300071500c1000c6038940030f04d04c444d1008000f00240a44000202410410915501c0792250040030b80091149617505410480d404900c00000780080080740307110311040c58640000741e448601414014100740188202d580b07852454ac604401080c40042807120441c0c0000d45264001d020001e45890260b011600400494001d400103060080c031442c002050308007840b00c100a485110003c01803017050500c0520102c4c07505 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 412779784 1250 412778534 412778551
    0x11031203071b0b040605091006030f140d1b020301020918040203012403170706020403030c0b0f010302130506040e191704030b06150f0301060c1a01051f0e0a0608 71
    0x14502d5400d0605020311201540341c00c40c050020540e22034032031001038a402814480c0e1802361580314075410220348154005103004070f80717004000000c2d1500310b5400c042c2c1003220a05501c09041d618400f548140341035003503900b40d03007a070300c03805550b01c0800c0c0a40039000d50305511a50340140754a00e0f440e24a203451245000714024400284121342154039401c0090341240e40c040201b4052021905192800520304415400740345001e42c603403603180c03c90b04190801c8000465200408060081100805400c5030041182e942d4a514507400034500c118095101c04565844000003071340ea988991040a521800c0310940c1e500d0b0486580008104806403821120a00c4407058448266494000d440541e40d0280c800c007480d840700c8041100544c4010400306800754100b000d40003101201000d503000300015107809402d07221a1504421040c410169031402d01442001000302d55900c144c004c40f80301041c40600c0e9068141a802c95241c600d448c4140c1e0882403840c0c00140c200d60100400d0700c00c9805 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 412781034 1250 412779784 412779797
    0x705090315070219020109030f1a160e090402010e0a030b090f0a0506010909050304120308060a060e03151b0720030d0206012c0f19020f161103120307 66
    0x6080303842101c80994803240180d002c1d40144200a40384d803103003084140141030507062a5940c2d900d41403102030469003113030702c0c207040d20981442c580055145038112844807042da036910003810004000c0e00724130042c184100e59880100301964000c6107400b0402c000a0078089805841b414541c17024036080d07070294075030b00c01c0645400420b0700c00702d501c0100640c4a00a440035901e4901f40402a01d41490281c070300b804100b10000c0c40411403010700000350b00c82c2d04c81d4207440c9407400403c0641d00099008005100340c0c1d4841f0b6900b50b9010030400d5070040081d42e40d00903034440074801c0140b800c1c6400041c0307a0400000e030751030a0010f000f01c507880a02c2604100700404807404141900e800b450140003000d68040c1e80180300c801c03c880142c50141c505070403001c010409041142401c0b280581e0131403145d00c4844140007680514a11410640e001200154506160600d62914034864440500c4001070130503040d00400140702071860003c800202110350b800b07480f08040026034402e0f224000403510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 412782284 1250 412781034 412781053
    0x30b030102270307060e0907050918090613030f0f051606061406070f03080613140f0901110904020d060f081614100e010201090507080f010609050c040303052107050903 74
    0x1800122042034400b00c0d96004006d0711007a040c030860403000350405c01405010300200c6050784502910b5010f4540c20910800d0904120040c2030420308041c0491002000000c80f00c80400d030050030304814207200f031400400c25065003004460b00e0007108002240305040e02e0507441440f01e40e4001c80151100010415041641c0c281080580d1040c0d40009100401503035035500480c0c069440554064006401ca4490850000c0303408103c03416103c002d03000d0b8480d10b0500c1480900001820f510110b07840080001070324136810b10301580202640c0600c141e80004440a4003401900510000d0909444401180d40c481101a490380b4001d002c00c00d108210034000502608510950f110360f44020f0044644600c070a0811154520040c04e514155901c1e0342104c0f001500421014000300181c0340501441b0307200b8006607007500c400d644003484041c10641400f810501c2c1808981c2240d0b4141015035590a0107401042d24030741002c000515103100d4020807107401c0e003202c004d0410f0001202514041030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 412783534 1250 412782284 412782289
    0x17090d2306012c07051e190201090c120201020f030408031905120106120b0d03090602010b0405060901060c240903030c0f0c0303020d061809050f070311040507030b03010227 76
    0x800c1071603c0705182d04811060120805180010f41c102d4140c0ca80103161010b50b41c2094007420791400c104600380700010f0610216104207038480703103200903032009114801e00c68550003040c41c010700072511403400c0e030b1000701d04583c02080040305520707030303041501c0d15507640c1c1e00c84680740c1d000018603542900e021801000800e10070400c5560079141c05923956050703402d01104072210702840d8101483d8507901c0380400d0f42580c8001c0603418030307440390f03a401c1411410100020b003907900f240c11103400343d4202424012980c0d908041641900d80c1d92800d00100a00350078400002c02c044001201c90344a50b210480711600640c10810803d4040d850030300034100852400c8a00351400070a82d40013516179600600064880d40090101d49036030040400c0d81d680350030305030070031807503029041c416195904003250422000b44580c0d20005a460050a8946c0c90740d2103603940541c079030500c5842507a8860001341c030710380254804420448080c1c021034842d040b0300c1504a031180d8041c0c003014400e903107074006541403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 412784784 1250 412783534 412783559
    0x1050907091404030215131505010515180d0201140301030303090c050d0b270f031c02041503020d0f05011e080d0f03020d0207050a0b0a050c040317090d230601 70
    0x840e0304d03034028002d17208842d40c0602d58000240000c103602c14550244c201260301d482040030104a10140000d031542351004000d010030b02181c050100010a1189658200305a0341f80381c00401c080d12500c103d1465840100c400081301082c4803400d040110021044c5031303040c0d2200b08100d1240780744401d0b0544440410030003015800004000390b407034500003500803010300303001c00c0010300e1108001c1c40d4025012a00d070806100d046050115800030400e0302c10303109000e064131070440031034200718a03142c10080c1381000c0d90038030b280900c28140c002805114910071075011401e4083c23030000410080d43c60301c03021015140da1030100d24400302e1003007000c41c204101185000703000300300340c40d0305040841e400c4054010303401007910144025400c0c0203560110780c0034820004a1807080c0e4440d800d500c1c4c8030720401d0444502501d03903409070000380410300005041240581407184600f45440d103400049000a00003100d079000100a00100c0030302590213070580c0d180540300040b00c0c0580390240c0e00ea08521405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 412786034 1250 412784784 412784791
    0x80d180506090303040b060d020316061205100b0702191211090a060f050132030106020d050708070201030515131a04110a0503070219030c0209010603140604020912010509070914 78
    0x40d401c05201042c0b040c42d0011803844014400713030a030703406200c801cbca032011515542d030301c16408107030803080c0380d000e200c0c09100e100c1d07018900d09000f10480e0b08100702d405440c000c41600034041e000d144003002d28682400100c4000b020b025a04050b402c2d86c61500e8000d00d1522403415020703080c0607020940c2c04030507001300c0c03081d20395460b5040c1145142c00e00444128180c02c86d181d2110120201c0035603a84480040c0f4075000c8081d801c8035a0340c0d4901200286450588035201003042400c1c02035400088800341155003840d0246400b06003034031180c40c102c07694a4614038103580302094040021045142e6040329408140115460309460114814042620b4094586050001c0c040120f9144c9500400256800500c148101c3d54030101899041d00f0a40340c07400c0903008594007030846021881c0c60100c4034090480d928081c007200c480aa4000401580900f0003031007141c022500101940303074400f04495030b1340808000d0003581000c81002d0707220903081c021000c00310b050400b06a508110035090070300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 412787284 1250 412786034 412786043
    0x20a0e0913110d081303030f11031804020c01020a020d08060a080c091515220b0307230a09030203060109180305030a09230105150d0201030504080d18050609030304 72
    0x140e08503540d15000310621078001190300c072100d6005000428508005170080781d5401800c0e603c51421402c002d0080d40c84800410208138003e04400451100031050320700805040b5007564182c807504002030041d00a01c0114141d0b5840429100c1c00c495002032162002d04940d194001582c0b14102030204d03611040c0606100b0760320000c100d10450a1091005034440d580c08403c140c18240c42001130020500c4282040c030b108404110503090301540c81001e5400c00002d6500c0c0216440c0036540c4c4c96502005002c00103110b01c40035850384000000716500103031681650142e607528070b00e03207003d021211b1502043c3d000c0c0c490417001191040c0c0c5440344564000010b0080440000c0c80d41d0219501d6100900c02503055868000c28000990b85c40000da803d4114405500b40440c0141c00a500f100c60007020012a0090303034542c5103882e101c15034a8464241c080c039001c940c079070352401c1a44180c481c00c6d0030019401d16169298800482c4200c0440c2c0c9640f103201998140e88031920545d5403400103072400b50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 412788534 1250 412787284 412787311
    0x2210a0f1e080a0204080a03050304060f050103171c063b131109010303052701080619050d030207080d020105070e060a0c02030105150102160b1207051606020a0e09 72
    0x41c0d010310062a480301003003001525003074030381c0b15a9042403000304044000c5680403003071004001450182e000414030f245070801466140d502e46902d1803407000f444145980700010001c2a06030030714070505c01e02c403101b0002d1046c3c503526594008e12512034400c611a141a00107a6224030942c100d041a42030072051400740c0c26103a092003115212641c60b1f040f52520140341c2206000d45400b82ca41d070081d07009440c1d054440c00201c13000102d0303940e002c0d031108800c8510b008207007142c1e030014034240d000700701030b00c1c1003005030341403404002142c00940001e5400300c44001d40c9020180c0c001417040076100b41d0000d80740b80560300103042c0c0c01e0302c41c15240c20f17000c0b6039102403044c17860400350050308070003103240f5203051010110f0b00440d0840d40c0540b04ea42c030001c0c1c2d08140b1850340d40c040225010a11080c245501030078540703524820280264443c0d190030010240216074114840c1c0103581aa200207109404203445900d4444000d50004115001180404182c0e440c24501011b4041c41000054180c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 412789784 1250 412788534 412788587
    0xf0501050c0d0809150405010c1d030d1409040e0a050708070e04020d0804031b050a0f0e0604020703020c031005010e0705190809010f060b091f09090b0102210a0f 71
    0x1914680e03402042d2943d144178403007243d80b41c0c80c0d400c0880350146000704000a0f840c2c103080c000038640f210309821119084044010707448152000100494a9001351501e600701410440031031041d44650b40c1115489420034004050500c804190354194521a40807200d01ca585c514140341c407100a07224003500105081c00103009800c000c5000188284210703866072030b154403550741042d0034020101580c0343c040c40720014409c034200305480c40050901c2c0514669030303a14181415190070001002c00380902d801040c00000c0500801030a80c079900024103030f90f414844400301c140208000d1143d03032800c022071004034001c4c50003842110403a810000c2c0e81465100c0c02c050540b40080d0150420318150340c0c40c0b070040919401031150070f01402e81c0f441400d6a0340c42050422201800d805201000c00b801025048001a000324a0804036410001c011a488044c0700040c1d05003420020610303001021820702c0b0740070017845c0700180789444003621184107070f540154040f10803200040c442080b01c0e90310f0081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 412791034 1250 412789784 412789787
    0x3061303080618240111190203030702031c030b10080106030e120c03090f030304050a1e0302031209090f0c030c280f08010e0f070e0303070c0e010f0501050c0d 70
    0xc0d25400b030405042c0000d441e180e1006401006030480d4030b82c1900c4034194800e803442c0e080c0b2071001c81c2c1110900c2e295041e045420280b54682c01c5080b011180391001d1007400e411914203009594100390000e007a1401c2d448104500d00381400100c0c01580040c0c40c111445005250461469a003002c0c1590b900c201c9a0034144154014182c09042000e80d101c0d80a1039084210140010200c10070428080e544901044c014084016a00d10110340301e80c0080c0000e0003d9143c42000800f01c07411030140c1c01d51548442d6002c09640b1840d00043c1d01400740d502c04c810302003282d900074400078009545440e8640d450800c08407668005031090100c2680070030200d0140d988032406004051b050305003868180c912001201101c0f00c040c1d1001000c50f04500d91a01c0d07880d00100803500410002c00a1213031450311204c1600244402420207041c425107000c0944151400c000f6171f42c4541d800b102d051506c540712400c00300000024800c114035829000c0740414954440c030207485101700b0502c0240390b2500350100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 412792284 1250 412791034 412791047
    0x40f0b0c0c06220b01080f0714030c0d0212010515091302010e040c180305010c080702030a0905091b0d0915020708300115121e05330f03061303 63
    0xf25080d540d91254031001180c2210f40d102d009141d038400400901c4c20b5403400310b0901e02d45034000940781807032210810154801160880d40c400e0119800038a19110303200068814240b518803024641c40c0c0410080b44d5803040a014403a604100c80030741306a90750345500d0f150f07040c020400030300144200da840c9041341020303007205210414504045d1003449407041603540500407076100355001da459000c580da00c0c641011103a40c01c1b007003910156247c03041c0004081c21404c600d201d400d0080c400d03900080e0710101e807109010110882000b0180e91002074032042c50141c594414266034041240d0591b24450300d86200b00c65400c2e40c00000c0904000c511180715984a400340705009220f085100100003c0701c07042c7d01c141c06404200461004030f240448001c1900d12400307c961723900c42c42d00000328240300d6280000c078443e85201c800482d25a4440305e68103805041c21016582e02020200307444800c43c0810b800040020040c1e544450300c1c030221040682d58182500d0030208843c41d01f4494020920440c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 412793534 1250 412792284 412792321
    0x9011a1c051009200a030302070605030c1605010c140a120b04090501050f090114040807080a09090615081b030c0703020c0a090c020c100905040b0414040f0b0c0c06 72
    0x540d90268058502d081c2900c2c52142c0407501c40010009940301002401c04484450b00300341c4004080c4c500b10f550203580c3e84801e000c1c290a2103004130009101010560856618411002d0a40c4040c4241d10300503010705118292903022445000030710f640d184140c816030b1410070544c0d60308a104c03140f900444004190300140e150300161140d07800c07008038600340240750050428044c04501841e0903030009084945201048034900d01c1801400040368101d42580c03000794000d18095030316400102e003607540c2c5882c1c0c2d2000791814203004001441c1010003020080306030b02d41e19002e5895070b071040c120b03010781d56518440011000a0000c95016046500a024168802d0044900400c500b000264400d09164000c03000c03e5120507033450b0040e07051040003000e003806d5034100c1420f95140005007003900580a06406180c1c1d681ca0580e00d070783d603034004d40903070341a00c4455032090829052000502003040d00503210395009101040c03c65020400301d0b04020402006404192280d129120900d940301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 412794784 1250 412793534 412793543
    0x30f02150f07031e0c0e1206040203030910021e060a0605090103080a030209010c0b09070f0e06030a0b1308180909030408030306090a021c1d030408071e0e0f09011a1c 73
    0x8101041004004c0d125005c2412880e4031032080803407100c000c018604141d03c10b8000c4d01d800003800d1100584001081e14800c8200b215003200c00d800d000c1007203140003094a9007694201c000c21400c1c8002e00c000c2141070092452a406004980e101d205100714400284801444002d04004101a0130701c00c1c1c0c05462044030504d88840c013900203454030001c000c000e40364084107821070a001c00042024080300e1000f0046031400b21600d1819000003130f101e00800230007400706000400014806041c0403214400903034004880c5446a4020f182c0b500d10701507421410340180c03081c0001c60a00a0008180c2d000c580f090070007140795a907101c040c007800d50780141100c0c00311a007e003c0350b8030885141d422001d070400c0c0b003900041c020401480e4000980d03d82840015980c10030001841103d401090000c1920761407801407040d0003824203080304100c42c036030040b44441c03400f84c184010414011402d9008000c090000e000510300200742100000c900e800746c9901840e480854115820402900341880e0b000707 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 412796034 1250 412794784 412794821
    0x4060303021e03090a06050408010501091404060f0f0234020a031e20030607030209060a27030b070206010f06050405010804170a0201020918070215040609060603030f02150f0703 78
    0x4d40000c1403403500907400080204401160600000c0c20910030341d401400901024003101015100301201c03601d007d003002c1c1c00c00d51581d01001c40c42a268100400600d01114119503890b2071441d00e2044400a1003d038021a1003800c81d09000400700804452464000b00b00c08001413960342c40a00d5031900c14540c9805201000004005c1100785803112251a06070440c0400d010b00c4070201803c060b0010003c0007414414400e000090703d4038000c2e258100f242d4140200500040204d92000400c000500d040d000c204010200c10003880300c50343c40c000c3c040d5400700c03021641c0700e8004411118260060100050051008001642c8039900442e0000e0090107e040d48040101c04201c8aa0105c44d100e00540c0d00015501450b0400f600e0f00c498140e027035001c4c1075190401002c000c0d100e030740c03e2850030000d5483d00c000c2018010142d00200382c0c5c41c2e101d4410484595207150240038003080f158120702502907511445d10020207008410710524030074031085140c1c0d4481d0350690081c50f400c11100040c800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 412797284 1250 412796034 412796047
    0xe071706090c190903020a0e01091b020d03020c070504022d030405100923071502030c070b072301050a0e03030403080408030901060b041e0f0e040611070605040f1104060303021e03 79
    0x450180e8032001d401000f000284960614100c10148d0300a03900c0e485800354180c0020304bc00317601040c046039100b00d0349005039454000e201c1e25442c050060b0046a4460710000e0741001e4941024a2990310244c0003115507002260070215001300c0c04103c8010300f46401c443d0004121603919408044036511994043d0110381503c880042e105c181d0030030401c019403200c81d040c04101003100700c01c211895a44019460440707028940c5032a41d60ba449142c00c5038102150601c2049028108042042200745c02d00b81410107003096580a400156100340d40c2526181c140c400c00980401281c1c41035803d2344444546031519036070032007646e00043c01083da556840b18045400c542d01d2004100130b05038135842c80303074041d81d940c071b01a11000d9680c050140c06504000402192400035002544240c1110000801d088451508006441800c100400b030b42e10307010070041000300c641045403c1500800e6030400e94652082803104440d0f417400080e025910180f09801325035490707001c100041c030340305050341d08100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 412798534 1250 412797284 412797289
    0x706090311061306060515190302040302030319180302060a0f0e0409060912090303021c0215070215090610030b0a0605090709060f09210303060e071706090c19090302 73
    0x8003a00c0b90f046400308800043d00f03016260040c040640004c4444022841204041a045214006042004004000281c00007600075415203000b590003505980d66078035841700751524005800c04000c0402d00328030802170600d013510128030a0700d6000d001145420f084c04030551394285080d0000040080b08545c50740f0f9521107005582c91540b023114041030101d04d62502606240400407920100801d40008101007a400100040c400940e0001c030304440f61000c408a041c814001e0581c66502040c60030310089642c002a461109046000540010348880c407405c1d40b00c1c40181c4403154100040c03d001d02c00300c2c01c0303080d0881d0440d443c80700000f40303a55120041443e6036021114080070540621042041c25040b070340e0440590440d1514600060a03e224560351415142880b80840503018901007090302031340c8000b0243c0705800c40381859144c440c0008100c5040460783c0c3d1492020400032520700c3c00e143ea07034580190300c000d003980e00307004800e014000407500040101c810011045400400340c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 412799784 1250 412798534 412798543
    0x10507020a1707060314041e0510050c09100c0209070e0604030b0405030a0f030c090312050d0e0708070603090c0621050a0b0405150a0315110301080a020916050706090311 75
    0x100d0042c000b6081d400d10f0002c016040f20503a40c4803203000c004070010000052822100d4076090302a8181008200015041140c42c100392508800b184910704014031070081004000b8100d1040100e1f0090000c40c00b0038000c90300229031000080d0004681d001041c51a4041c0b442150340700c60107000141016504d0311a490104000c0d1030545882d040080e40c120340c02d522a010160191503800c050004440000e0001c203108403501c805080800c0000d0601042e501c144120707403444200d12014088070701003034481c0e0b85070309080c8076201d494400e0001c002406406401080c80281d01702001d48140d034600001600c1245c001082c10181c4104240c1c1201c0c00a03152180b94004c41702e001c000108030020b80180011504080c00741c440040031540f249146aa52104400c140c0c0d030b00c058100808440e0000a0b00540b14001e21610560f0010001285c100000100c41442c58000c80d20740d035075522221511401702c000c0704c10b0100000c0040041c030300801c0303140c0c0084001c24800c2c0f615801c0c4028010b1494200f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 412801034 1250 412799784 412799819
    0xe0c1e0f150a030b01090b0f030402270105010e10020601050402030709051509041116061109040c050304120516030c17030a0b040e010b0f010309261b010c05040302010507020a 77
    0x15154007082c42d0041a0b8148640c08100d402802c4c01d019441c18a114400389000b074282c1da010780d8000000050464560761680f44c007216184446031464802c078030003040c080509011f0b0034000341c4d030480f990b0401e00d8100e06000b800c64194000d801164281802e102c00303988010318080c1801880308001486480f40b0b40354185006014101e075440c1e404800402c41551030031702c5039448107501404250132070b09007609136114190380250001445102181d82d070b0000d000d40180141e002c1c0c0f40900d0a03013a140c0142c02184518400c05426500303001c00c00c1c041d00e103401074258002003402030f080100002400351840019582c00342410300558241c102164000e58011038101507211f4490418846508082c001d05400140440003031016a51450102300b8031110880004d04260f02d9106100c21701404503100600c003604000c101405011220005801d640450781484080c141c004800111141c188a02c203400002551050301d01455078004540d103030402c1300309a030b112000840020380c000700401544003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 412802284 1250 412801034 412801069
    0x10e0f0312030a060609180c0905040501060f03110c0c1302040b041205010f05040809010e0a0e0a140a1404060f1d1606020a080304170408060f0402040e0c1e0f 70
    0x1503d181504140060384e00305e0f44030740140007000105000308540000c8020122604510000c2d120380e0103101217614030705580c04030750414600400418802d60103105604610750545041c80031a2111168104603c103001054100b5006210280e00d6890803007aa5031503034410301700240c01d003500e45d055010aa401a4000141030310882e10b00020040207001c0c0c02c4d0495001c06042040b440e054840c5e45191003040e8102d41001003a403090704099403018000005001340c50080100e501d8200c81080013000030b40c40c800701c0490083c00050140903107009942e0340f9802c80c40b0300703281615a07564500c0540030541544441c00c0d10b807035115002e100003049440c108098480285200e8203102820080001d00c0c3c0c22581c1150841c43d01231001c2a00364007142d030015446410507548440310f5811050074010754000d640280905028001e168514011203801103008440030407072481240c48581d520780c002d070140c907007101c0d941c00702e40c1180800140c040404200a044a000c51f042d000c0000c1030940d583d0f2070b094 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 412803534 1250 412802284 412802287
    0x30a05150708010501230327010209010e06071203020906040519061d090114030f070b0c19030c110301180302070905012c0403030b0a08060a1a060405010e0f0312 71
    0x1d42540240d0060040c0001e003082c140f840741c5107440d85a00f481e02e00c21034100c040c0001c0400c010840445010a80c4d0380750050b09200f280940032440d0107544000f81d82400100c03280c2402031075103880400c039400b495015003058030b82c0d0801c0b013040d806074208514541e4800c00510001802d500e036070074000406203070030703420a0005003005000750544039984c243d0b03641810070400640c030940f102c510341e605403014000d501e01c0ca030401b180080d00c4c1c0300049500703419502800b000003407200d8019016140c214920700c03e0306c0c0306500c004408420b180d003110014000407a0175247d503001c9056003174428240000a000480c03680820078150303001c01444c0030b003140180d000400800c0010010320030540546504e0350325080710b0121801048030004200e0703103482d002c034030100030504041c001d40c080707141400d0103881c02074080c3c2e540300e03055204c0000306c581090031400c181c2501841c40e20b00c188541c007004002d1013581458103010044900000b08400d140d00488506107180d071b07030b9600704941041d0003286500203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 412804784 1250 412803534 412803541
    0x30f080f0a08041406090a02090414030a020d030f0b180915180712050a0b18070311010e0d03230d5006190603050108151e06030a0515 59
    0x106500000218a83c004d0740045050001140c00400c0c01c1803440d40444445c000344e205d5080c0310942d07144d07181003070090340f00010782c0c120155008501e034054600d40b61000c1280c03681c1d241c41c50f0181c42990607003550001c102e05101c0b1101d01c82d001c134940c00c03015003400c541401030404441e8404030f1080e03c2e11040c85040444814410a00b00034042c0648100700310221200403691300e640c0e88601d2000018a250000c01c002480b0070902100e1522041c900b404644d0300076038030f080c2300c400001d22420050004645440b400c100e810090303100c403503465050fa17032091031000e11004409551116051f8010000c42080b80d04c01008080c0a6002c00c2c0c81c8600c00c0ccc000803503182c804404403005a5086540c86030314090440848101c030643c20b114030340a806520019a200740c0064602142081341070385010b44424045940c076855403210741600c00e48412107210b401d240d83c485148400031569480800c940d00300c19440c81110114494001501400311081c0704c1c1640d50711428034408140c0c0171445110714040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 412806034 1250 412804784 412804793
    0x190503070b15131506050a171e09010e25050a0906080d020d050307050717130609050102070317090109030f0b0415020c190c1511060c04050a030f080f0a0804 69
    0x20f0400d001d0a100c0308010800b54400c1514000d0014407030001404008544201a10300400204100040021080c0594078040300032400c4034004d081d120451111800c00150380010520441054440c444024031100c0c040480d00d0071714000c09280324103058400000058161203c046030310143c07040003c04a02982807042440c6444094810302085500c40038428100503002011650804c0c050724107680da480c00c07418450442050711600f010b80740c2001070045c085141e008264030a0300d0b4590b07125944680d03100e004907610700042c0070103060110282c403403820f6140c10200500407020181007005030795540c0d4940c03d00b0450748100c103954180c0c400003000704200500b103c4642c0c420980c0e1003142030405004002c1e43d80c0c86c1c1c0380d15400392402010800024001c0400c501c600078003d03a01c9074a443c12a40c4001008c1030894550740910740300b800c000c2100120080305440544001600758a0300d0751460729940280050346000752a082401c104601000026038001c080c194020745800501342840c0c9013 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 412807284 1250 412806034 412806049
    0xd081b0c0310200c1e0a0302060a05010b040611070e010602030a020c06040e01030f05120d060905010b0c030307050f0c030f030103020108060a030b011701140a0b031e190503070b15 79
    0x60003406454480b200d0050f1818001d400c0101e4851210980c80d9001e81242503e044140309107030a0001440d208078250b0743c00001c8407015140310f5402c0d02c550b03444070400c13034080c0c0d0401e0250110341441440103204083c815255403041d10b07110000c07540e031643c2e50f403201e0b00c06070320a8004000507000000e07140c540507010020000070b44029500300e49404d01e4803200854074041808000c20b103007018403460050140410045c07505032800410142d132411400060300040429200d4036203085c0c00d00300005107412034034040d107140320880006149940e845000450303182c3d1241b516500181c409018040c003200c02000600a102061f25540381c0d6941175000150890400501084c4220034007034042c03000850700010f00f4110785540c1184a2000385102c1c0260141c501100121154107072001044640611600030300c4424200f58243c4000f6000e0b0101d1045000e40805070340340c03507030109003030b038180c0320000c40c6e000596170044003901e0900382c19995250525600b501c400c2c4403009240680085844e0501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 412808534 1250 412807284 412807303
    0x9010b0f1e033102011209022806030216030842030d020a03030b0402040509040c050411030c04050d0c09020a1701120309120201050906130303030c050c0c0d081b0c03 73
    0xc40c10085120340c032001c000071007080c000d04006c6801d5007000d2003000e0fa088800c1250b03001301610640102d41c0d03400781d8105025100750740c40d01d0b846880025002e009100b240d8640309441c280002005840d10282e404103000307441031500303491414944044824120b62020b203044455000c8060034900ea00ca00320340744c04407101c035100390058000e00030302c2c94000845c005120303414100410042141c1001500070302a44e840a9009521641000208100c84080d00203451003214100320a4150504034222070000312040340c00180e041001780190310300401c04c140301c01d1207000c48000c4151206151811390b0880040400800c03400380030000d101c000c2d000700e64050211048d44030060841a20010700e084064440d00310307100d00010914040d644100c04a03001c80c00c02805080d6241041001310200250501c400e80c00a80f40c203000549403031152081311600507030300004005020b015410030845400d140d004a45040c010032092503aa00e51a03550000026a10f01803c0c119203e40c007411705000b40d91 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 412809784 1250 412808534 412808581
    0x10e0618160807050c030a031d0106060804080c010b22110f040e0a020f0c03070501060b0405090604020d0f0509152a0a0203070c03081b060609010b0f1e03 68
    0x890410150740200c4001d003a400301145480e0045496060003500c0c0380c032562580e4102d60000050703401400e03030035401c201180020580c1650480036003002c0542291528012040001e034200d0200d004921100d02070065440b4070030001450588650001d9100c092340c5e9144120032048019102d40c102d074070710400c0743c50858410b0700341c50400c003000e440b02140b00701c1c05070b02602a034201c080740e883c841c1581681c0201038040300c2c5030364600501000c550f40c1d400500b0221200d40c00c010010803c1d20080003a5021607102a201c456982c4607070381004041d401607140d048a0b04e40d51511272800c0c0c001406103a0088600b0b001800c00444860404144041c0082c03e80c002c4c2d01c030b072402c0c1075180000210258116803964044e16103519100344128114420f80c040980114001d00340030092154290050055150110b0003440e00304108484580300e20040301c0b000c1d0311074401001003207051b100303800a24422100c00d00e800e1038400500c0444260350300c11140c408505401104005e40b60702c0000c06540b40f28520f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 412811034 1250 412809784 412809829
    0xd0c0e071e030e0a0b04050703050f0c011b02030a2a05030102070503040905040c0807030507050f03010b030a03180506160506060109030b2206020c0f1006080a0b09070b03010e06 78
    0x440d030541500340100c5124804265a0715056031880780b0900c51904455800f04250b83d146c1841d0138920b0703039001c19004c281c03154010f0045851201c20006001900d0b41810f031120010300f01400145036041800141c10b0b601401260718a40014480d1240c100d069446500c00d00740401d0b4030320500c50912911340040b40268410890310022400001c10742c4c0440d1401107001c1ba10b561180b804640400075580b28070f505100d512008000c03c1000304442059540980e445100200804109030a0b5400501707544e40507040700c2d500c00042407144440344920091a42000c441d01c0c0d44002250f141d5003e8444019043c00c5100c080c02040402d00407160803890034a0103120407802c0d506d803a009110064010044040d2240000b070781079180c601080d071300c1c1c0d0f0490301c02c540710521600c1d86034481c800c8803084403039030180381a00d0700041e18912848055850942c010036001007075580d505150b9034040d000000c00d1044c1907000801042100c01503001c1c1c80501c1c44070005040c038074284042e03004000281c100c80d031007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 412812284 1250 412811034 412811057
    0x61401051204120e120d021506010c060b0406150206150f030607030c0c060c180b13090203040204091b06140a0512181903180506041a090d0c0e07 64
    0x44801d071076001900001294000c2100310030039100780c2d260035041c940085407a00320616000b07001c122001440000d409030f4200c82d00c0005020140300e011034446001c10a040b60030008120654440c4501c200e002d00b0010326075440e054010125080152034400680c020740400c04083c1300b10036600c0002c002510984444003001c0c1c0001d0321000018208810199170b6061002030304d02c100c03030442d000d42d044401000051101c0700024001718101e87c101c6520f0220740400201e00034418100d625032a0265070500741d843c1862440e4001c0d60014105036406a02c1b03006103004500700c07240f83c82001240395003881000785858009081426070440d000781040090000b008096040f2046884041c64034120582c42d903070b5030780b0409203e68404442c91052050501c1601c08003030001d0001103181c000d8071480341e03c001d60030441c40f03042414016150032000910040161202c82041c21240e41070750040b580c200b19004007c6240c4284000c070580c2c20881030071040280700140c19519410003c40c5c901000b040c030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 412813534 1250 412812284 412812307
    0x60807081e011b050706150906140909030a0f0903020a08030a120b0901060f1205040605090111031509101d0a060803131e0b0f1206180402010c150f06140105 69
    0x400200a84144000010b0020400213540d1003281c41042c24117451f45240d845d07612241c010b005500a003101c11a4200b0041b885180946c0110701c5075607140c00651510040300011146105034440041c14401d0044000c001695213803507c0d0701034040c1300002d40e210100008010300c4100908402c4075003a1070140d4401c4581c8401c00a03d0640d401e5003081c40c0e000801c1d200448900840e8000d0800b143e29201c00e00c81041141d40009002e103035a48003d204c1003007140358004980c0f0042e03502d442001c850445002c140c2c200165030710380c4425032107543c0a1044da12040c0c5a4034404a140c031030941d5550804003d80300720f0345c0c41004041c0611200450074a045242920100c900d24040c0300c404c0c80d421421038001c504540c081002928a1103c115141c2c2d81e009400ba034603070400140f5441140600000802034240050013400c41d001b06c0311900c0c580d84480d0015100100d0280d002e9401e4424a8400044000136002e003100f000c0c03032000d0000f4010f14042010340d1030b4210082c07072410014200440c10f001c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 412814784 1250 412813534 412813571
    0x8040309060f120c09050a05060903100e1c020d080a0516030e030405130203180a05030706020702180403050a12050c07020f0303132904060f030f060807081e01 70
    0x11215420400e41c10300041c0401e0303d80c8855912080403040c1400d10a280d0300d40d100001d0b9041790402d4035006071980e1140d0410039640110a10150181d001880c4610044c0760360700914552410541540c1c0c51101d0b81c14580900140c00207403070701591003180c0d41c0102560001d610340d8003105040080241d401c100440002c0715050710f1500341010303114040b8074240c45e8144100ea0041000902c158500c0c9004e005d064040c0d00700721044001058418000d03101c10b100400d480c0359541d1702c040610f03d4041190340d240000d41001e041030703030410982840207405c2092104014003a1340280c0764a5204c103540076000348421070040340d007054181070105001101c00c0345801d8441050381147c515400c1066240844c1c514060503880280d01001c0700000142c001c03031038030582c0c109003040541300d07031000d010050784da01071066100f841c2c00a885042c0d1003481c02c0c440e500c85140b40325480800708815544000851030014640c1001e48580c02c2040d29075402403606800031032140740355000f8172012041401842c2e61 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 412816034 1250 412814784 412814789
    0x10030b010807031434090e0d030f0b060702011407020411030a0507021501050f0402070813030c0906050a120f1203020d0b011404120318060c03080705070b0402040f021606090302060708040309 84
    0x260a0390701029500071030080d03501805004442c804200328094107d5165840d20305054407004a85408000b00c41619030380200e20300540060b110901d020300c0c99004441c218064040c3c085050340030300c428801a0f5850154a4124031242007087d1203003882210700302143d0000d007504055510803d03a514807041140d4101e811107030121110603c42d44040041006032041e807000405403140081d0001e02071060001c124203490080c2070b1000c600c4e4840320a042211418010303e81d0100b20305000304554410600007410291081603007841815007991000c032030019003803003840400c1c1c010664040714411031080c0841d880d0b0900c0c0c050f06d01d905008840c19248200d01a40c1c082d204508403242c1818000d42403c60b20070002909580c01e261382d100000c004c000850341c00c500107405c2d2404221240d10640a44078516080070800001c0c0e00d880d400c20000789a00c200f8561440d40901c04814415100c02071904564003a40002c50484107610380203090490050107442407200180500c0082a4080c074100107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 412817284 1250 412816034 412816093
    0x14040312030917180f010311040806011401080f16090e0a09020411040e040204050702031e090310020903190c05030109080306031c080c071113091101081b0310030b0108070314 77
    0x170022400d000490192140403a02500c04400103400030318181c0000341030b030484044198031001380e204e08004481c3c850007510098040181140450401030380701c42200c0b890800750800d2040b03942c0d5041d07445898001290310742901c0d030740d035201c480c19824540100d0a0445040004030714190034034407201c441c1c400152010740940d41d01c000150909000b0400c03211518001d83c1c0784035a80d0400380c04c86249511400510307000e8015044c3d4450f40d1400d600a6444260000303028051100d05c0507007000c0307500d020101c181c82c001501500080e880d10288101c11000b40502c01391503a901d44502070501e003c06126404550b8a81081e000c854240d1040b038540c2c000b000a034450b50f441c1c3d4241456a041500045100d0b408102c110800d9078426099100d072000074850b001c0e10380d44121190040d65000c404540e00f40da03110b541040500000d810300015a8012000804c0c039800760344a44804a00410917046456558800502807003030000c00303030b64010406081e400901e405170140d00c0b01070410106084819 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 412818534 1250 412817284 412817299
    0xd05070c24050106050a0903080d11030426090a0501050a120509010b1c0506040b0a0902060a050904050a0c1b05070801150807080d12020f190801060e0906030d1404031203091718 78
    0x462b412420b0f0091003007a240c0e5881d95481c0d09240c00c2105024070180f403c60809c0c40e26510702d05800c00c0321410354142c8540140481c0c403240c41c200066070303141d114040000420507054580340304000c041c8951802100f5400000550b03450303030802e1114080a0900c0010404100042c5c500010340008400e1f601c03503030100594203603494240309180900301c00740c0b00946c0000085804070030598080302400140304216001d0280d038441c8981380007210101d00324000014a820780d0048641540d10744400c1c51441203084600141c1d46200d02800c61307148074130009408011007001c000581080040c640078001c08806030207a1109903001502c052200c5200d040b115030003050a039155140c3c4420740b0134042c1c0782041c11011502500780142020401d004400c04030303e0745086603602d4207003600b41e1445194040e000349203070200b0007420398004a0b54a85411074000800000c000100c042808d41260850794502080c4801c1d01d107840700e00f10010003c600b030f143c10140154400350001a0034580005070603107a42 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 412819784 1250 412818534 412818547
    0x1e05061c02120a1d0c0f0303120f041b0807050d033f020a0c0f0501060302030a29041211010b0a030f0b0a110d05070c24050106050a090308 61
    0x3038609984404400540c0e9201142540c01c003081c0c00411032241c8038003103041060110f011400e43d5204800c03040d001c3e00350b00091070700c401414140e02c01d1550040040442c3c0c1000040c450b800d010034021201c3e140b080c860300040c401001040e44226541c009030203100b000b61402d28468070342e60b00491190130f03c030f440000d00900906020741403000c08030300e0080c0c814050104401d22070141e50b408194007018034811061807121088a4800d840c07003070750550340b000505125a2155088000192002e0740d01c0d55940800000584d0208083c001d03440c802c4500c101c100d603035207034810351104242c6410484c0111000030000024052485003684d284107003480070380d60070f41501e03040c01402c280385005d800600700303038000c02802504542601010b20944210b01c203943c03110001c10a441640aa94130154814001c3c0320801140b600071a40c013a40914210030b04a002e601c8601000e091506040185c581e002c1f843c410900306030080d035001d0324550401a2504200c4e800003007031400140300c0a0821000414003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 412821034 1250 412819784 412819807
    0x302031308090a090c02060402030c0613090b130c020f0d0e180712020f040911090108060616080a03020a02150609071d0d060b09010e06090411130603030201151e0506 73
    0x2c0f0000b61150f808204862010400060340e03030081a1000e038803038480d21172484050302d00a02122070741d04d0084000030342d20f4502241d102c0035140180e00b1035400050001102c00c1d1604134480d11242e807640751700800c1d940080383c0980b800e042c1492100f00404c07804405803201c5480b65050120800100c6131302c9605641d403904102c40c84c640c03a41c0002503c2c1d0000594a0b14801130740c2c082c006450801c8010084401d881b102201710384940320b121070200f07460340d00164039071910704050864a66814003040c0a00c01954035564103901101013140403d40c00714201131510360400c6414211001e40007035620343d00700200021903440000f4590340c1040300e04d8940c01c84095181c020b482a10030080c00c44010141c081c41d007180905401c1c079416001b800454000507003074250780640c1d0b001d0440500000380c00c1d12642c64100c1c01c0340065800d07503002003490085130ba180200d8412800118020790001501b0200e80700103c8d03500c00700f6800a042c4035900150810814916240b080455104032a9581d441b05140c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 412822284 1250 412821034 412821049
    0xa1203022205010201060e150f01051201090203042f09060a0509040803040614190c050702121506030d05040e0405160902180a061b110a0f15030203130809 68
    0x9500340a00441c0000c0d6064604040103801d03184240c000340411525806000c10308042214203400c0c913480c415540d41a800e250580f0703c03e0700010b04d003880c9040302003030710345089100a03841910080d5000080000340701c03030424602e900c162040010040040e22420b0300c080700c10070802d0f25104501c4240402c402d5556142d114008110141524181c1c7c42c0a04001110350012101600c180e820002030440d04180c6c2d0715004e1144024094104040c404d0324103010040408050307032402e000c001c101d2807000d41d5408071214150f9100d03030300803c10b00c1c6030350000c0840914041c02090180e0301c031400965200341c00000b0ba03016285104112840ea40d41c3c0d080a0386084507018510003461031803240402c40b070703800342c0040c188031264100340403010034000c2c244400714080323116a100050360f10500131036248080c884003140358000e20100d02010b1000c0005400201c4580c42160013500c3c060041006800c00302505023060b40c00d0a0031403c0d860b1401d00700a5440114500402ca004000b0701075425990315071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 412823534 1250 412822284 412822297
    0x30803041704170a020a0501140a080403030f06030f030f1b0b09010908070c1e0501050d0f0b0a0909050106051c0b0a02070b15091312110304080307030c020a0801020c0a120302 77
    0x28143c201600356110b900d0740300c0c603500c2410703406242c20450118580d4040d04842c600341c00b600300c00034079000025004032803c2c500600708030300301902da034003d01d548242406150040d5000310b40c4024030300030903d8054540340c4a808540700b8004d40954141c00c140203110034582442c2c00010301d082640d14841000d00400c00e070701e0000c0440340c3c0802d0000501c131841c400c44050301c0d40480801c101781070402140c100c1c81c0c3c85114090000d1010040d003900c600158002c905043d4404401050311000d84000884c0151a40c00c0300710320540c0d6042c00000d000b000d010381e8000b42070a507440102e64501c19440c0c0c8284013543c1014150b403084001162400e46207a0443d081e19411420818442c00e200b240505000355800c1024441c4103450042588442c01c1141c00c40a0ba9105000c072070550a24001920388003c0d0000301c1209000a101c001035900c0c3c00d00c000c0c04140e1081d44c0e6580104407034810081150103d03003106546078410f000c1842c0c074003000902c0c8030403140c01000705280742017400c1085010b403150300c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 412824784 1250 412823534 412823549
    0x61407050f0706110d031a130b10110115080a02010e010210090c03110f0310110f0d02040f120302060a0f020f0a020106170102091f0c170d0f0204030803041704 70
    0x14070650118840c1020343c00130080d105075088055080303003600c035819200c8007624400e40c0400340515000c0006042d142440101150b81406d000000d00c0c409608190f400100d80e07602012440c5000c00e101e10b034a400e485c0501d142c452800d2010340740c0d03030300443d9070000d06002e4800403035009a0300801041052031040715007406040d0192400320208001444111940c6070841003400380340c68115410b6200c642d02800500304031030184600c80241c00b00109449188a007001100d0030000190b0040221208070400507945c1c9180000112031252990b00120b4640c8080c9148000241d0104800e6041072036a24007241c2c6440d4607903041d00031710071015030400c10080003502000c0f054043d048841101e86141900311803141400740c0320f0a070b11072703a8a056400101e13802040b040c440074020000620000c1c0c6000400310100b980d60642c4042ca030358a440030841c0108140d03a501516018502030526841825403c1c2455a640c0e03030038600005e40b00600c1c9840c80324441040072540c4040c1c60041114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 412826034 1250 412824784 412824793
    0x8090f100f060b03040f02032815020405180906090607020703030e060f0a030b090f13020919150f0f1a03041109010b0703091e03030c0302071a03091006061407050f 72
    0x5446d01003210310760540124017a0162140f807406c080d04031700c8461060301e843c4008000c00742542e550603000b070b201c0300c1c01d044485500380400710340c0c0d4440fa6100e41a240ca00d07002c0740d90b2428002a11490294000e00d100126480401002a41d0742e0108150b011264107040a008401c0b0040c0050345501400e040405140004503100c013401d6855009480c0c0210140c5051509446205212544040071102c1030001040740403100018248107064640c0900608107107010000c0342c41100f802d49a40a15580d00d030190b0380c1c4180117113459542c00400420307203190011a007510b070540064007a005003614584501d004000103050005048070b0441401d0700511605480d0303142d40d01c80d00c154100190030340008183c0c080201340b14000c60880f4112150070f9155035a2141f841c1d5003103441d0300c43c588040302180031341c1d440014100e085642c10201c1084003000f054503460311640084c600409120b000c00840d003031200411240b03810050000b2641c6c409100180c0c0c460303890a00350324201d400c84c0000c3e06440b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 412827284 1250 412826034 412826041
    0x2010516030c120f030e0a081c06030204050411030709050402030607030921050414041a1512011512090c0302060a05041701050405070602031c0504060b030102030a050708090f100f060b03 82
    0xc0c05440f4201400c4252006c10081c5401c00d0b640780d03101c404460003458280e040106105220303112074201c68030760106102040c05034a9501160542e10107a80486104046c8002050285428082c401c0901071780b8604210501d03240d00004d179950005403c01e02490340e51031440e018803022107607140981448464440004440841c024001c0c0d0183c41014155114001010072514050180e844440c086050001c20b0721082c0c0100b0900341050b181035522130b9020440d954003c1d06010780540240610078846407202d4407104094040043c05110117802c1d03103049500310000348020805402d4070703016908030b41c03521151030f8150380318031550b08034119070f004a10703503490320100540001e44641e1140d016600b44039520102030369070340904092160314904115a1554030f0000d0740c8000e030321500a0304003298800c00f01d00840d0890348283c3e800b52449865108100b850fa030040441c075000240ca5000b068080c018032803050300e80e4601c107541500d00e0746440002c0803903061500703c80060007820040641d20304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 412828534 1250 412827284 412827287
    0x11060f07021908121204110105040f09050103060b0f24091c050f010603150b1309060510051002030f0706020c0d08040614100b09030106080727060302010516030c12 72
    0x303280309410b040d1041c4003103618084280c40c01d030b030310801e9414440030094070f41f50b4814540007a0078005904004080c00002000a154101503000705488400081c0c90f5065080103000d883c6100c07116802004581c941c5400d0307489580e03000e01c150b1401a505010a861812540010310030742c1400d41d8010390b40742c504a0f04404151801d01130030b219030120303101c0748004507003542624054800034080d08007825000c4920002c5402c030b1851210010076110b61071400c0e0805008442c00700000b5541199158104040b1920120513100074080031204070003071941c00800256a4441c410b011082014081a03100821415406a840b07400d2084c05450220090303840c02130039510b0446090b2020350810400040d005801c04202c1d0042c2d0324070a10f0724440d82441420300060303102c141159011740d41c519000610600c10f201160181070074031034680038240407012005003052078030a82c1501916002c41000180e03005401c03201506022511102c1440b5241020741c3d411501d0500036000c89080000a0000d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 412829784 1250 412828534 412828579
    0x2060d0f0b0415302004060b03070f14070b07020d11071a0c100b1206091915050a0f0501170705060f1b03090a08030711060f0702 57
    0x40d106410304000c10420802080b00b41c81000e40003070840c0c003440509000405000d0b00d00c0071030300c00e900014200d40d0480e1498040041c003450040c0c6540341e084c54103000703a103440c071071055200c04100c8040c800315092441458003880041d00c038206100101d22030324511406020500118580c9039030642c0c4418513820440300d031590031140b010060107a06026806980a10784428081c85448024180d42d4242100031817401e4841d204550000020702101142d0102000141854002002c02098941d0041c09104801c203110500d02e00d80d8201c10704000d20340e040000e98417140070744041020b00c0c41c40c0a0400e403070035207402c0c0403805800c3e003020204006804203402c4a0400d1801c40010840b50f039a403020080c20218000d04101c1c0d175001910200f00b145003a00280c44952000540039103070904c1031765500c0c001c2e258443e102e800d9410216004200e807500c2250600101004406503103800540c1c0e07100100100000d06030f5100e0840450240b20039465103043e1040e10744c1c094500403c880c0c0500040801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 412831034 1250 412829784 412829801
    0xf051305030a2105070809240316020601060504061b060b090a020913020901080a0f150321080108062805010b030a05090f0a0602070204110301060807020f1212100302060d 75
    0x1050900d03c000c2518454401c803248250403815003800e101540c4104900e400d4045104d91100401058100d0281d00300c800840c0110100a0310170400382030a80040d0030032078168030403024404284801c0010350340051140c400c00000040034030301c0b45c840d45080d1004001c1d10340c465030031446d21420480303180c10369030007040c61800031183c8000240e01400f40c3c07410792142504550001d100c80300801c10310003940d0046e4000c10300d44d8102044101c11409030142092140d481542d400104508118004c040c00400e0001250a89890121581803407406595200d0241c03090300d151003420182444280010b03150308080180c204280a1969503280d6001190005d0710201c440d01d20386400b082d8500d80c0012114400d40d4814050001810280c44c2e180c003e41040700113a80050311014601059844076000354041d1200b42c64005160034281c5009140c00f100d0320b40041241d1020a8104005841d0401d8403140c0605000c021407641e1004489806032101798802074100c440810351109d40b0308141c002804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 412832284 1250 412831034 412831073
    0x3240910050f0f0c07081227010605010e0603040b0412110712051005060f190e16110c030c1011120c210306061b0d0507020901150f051305030a 63
    0x255803202108204e00c3d01c20301500900308901000200f8a4184120845500111400749529080311a2010b00041c0540400700c0005955411042c0120368028103d0142038005440700343c19850f00743c1e14540300c050f01030006000e501200385080c21261099030344682e51007811007a1000700d55500c00003030903900e283d00225858001c40d00900b421925034450380c2c1c42420300130300751284a052a030900424004000c40001181558007010a80c02d4090051a0080d00a903450316010702d030100d1f00500702034461400c818180c10031005c125407a5000207030490821000c44520308601411030060765010411840c1800c0b6003d5030307404010400e00d1801502c4c54050500540d0780400955441d4048070200c650300c0e824040d024070100300c580c1800d00141c900038280410000114510541a0b4034054a0681c0100091000200c0001714200410b040740109031101d240c1c00a888040009031910001801c01c0f410403802027075880a0700c000c42a0800185000b506a880300315160400e061242c0070202d0181 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 412833534 1250 412832284 412832311
    0x15031e0f06031502072111011b030b12030d0b060423030111090108040609030c2a06050a0e04050703061a0408060708060102033a05060102070503240910050f 69
    0x1403e4000d00071915416032208484044150083c00c10018055484900c0c04001c02120010b505072024801c1c1c248140c1c5000c40e00c042d0300580030005003551107506c0120b0060001310210104c0410010545900701c07000400860b009a04001141e014011580940c0f000400c480200703480000c10b4510183c4460154001c3c00180a01d035014051845116002c07400581201c0014002c502550301030002944289010f00c40b000341a25403201d140903842d41500d943e003810b02d002111111b0442480c0041116051103804c3c00056207005c0e0a203000402094012030300d400000e0509446544002d01914846000d10f001040761107603101a0341040c0a020031038400c9402048519000380c00091190f42c0582c002d600d40301c904401101404150f0540c0450344070b07a41969044850072481100051010000024252600f200024a408400d80c1b26074065006040002d80101001300c84170301c0e5110b422a01c142c030361034032411103150691901c400110390f4a01000c1c001c002c40d0180d04940100c29018111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 412834784 1250 412833534 412833563
    0x50702041d07030b040f05060c0a0906020a020105030408130e07210509030f0a051c0902030d090b19140f0403031106070c0b0601050c1615030615031e0f0603 69
    0x7418031500e400089242d07400b28030308100080c000b100c0d00b1341c003512030701c1c00107020046980c0d0f05103402e500b650f8100030702101007856032001d503106e40303007000824051005000100c690740020b806403001070800780c0480c90029910042c0d01c0704a4200c402010340c10340714611440c0201004103001007280c0503075401c03014000083c0560015016042c0a0340098011f1890132400390352600403980128202e00a015090201204034400119030303d5612540050200d005003840c030405080440b0014203c06008036180e051020a8070a0300b520300160500d0040381c81c02c08601000c4d01c200544003145400c0b004005248400e1408060181003164881d45480d200e41125501c85501c40d1012102c0700d002070b81105265010510b07a000c0c094100303070103040c5545054a03a43c1e149041c070104c006008100d8807a04000c00c20102034002d84101290145420003096040c0094101248407500d20b40082503260140d802000d429009034044540c21032070200400d403145003554014258030710003130340c1c80721210614 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 412836034 1250 412834784 412834811
    0xf3d0f050f06030108060601030c1b080301030201110105070806060901050c03071428020603150d050a0b07020102130e09072102012c01031509060801150f050d060203060d06020a05070204 82
    0x143ca060ba90b02c00040e000a0742e40307d004500034400c14803000104007410400c480f030340181c510180c44040c0100c80060b9258154000540f11840c0c061204409a1400003084116076021152541011080ba00b0942d02d00d00c1d000101c9090081c10060005400001101c00402104064101107000c1400556009803c0c100d00050141c0b03144815801d03c05210b0392480041c6800801123038818242520f12050078501c0c008141c448190803021602d65205084032414482d8040001d0340c442421300c029807030440c101704000600c012511031800140f8880b404581c50a1003403190340043c105e0038803401421044100c2350303030071501e440105902117034005061a040d8001605460264044221900005030b0008011001090162a44403d001048a000c80c03110020300562004140450000c100e560a482c0380d240f1210860b03000c91142d4070400030400c03841d04c03501c2418a609810800060305c0e50748807000301d28040881000203100c240f0000d042c0c01d070950040d0180c02d281c0d00980f01080b5170012041d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 412837284 1250 412836034 412836037
    0x1002040f0e040201020a1403130b07060e07060509041a061c0c08040b010b07060f02030907091401050315070201020712030621050c1c08040906030201080f3d0f050f06 73
    0x80c042d006801000303242012075090664140410340b281f0490307140846001c08490038000740d4210b900d5042d40092000d00348030150140140401d00e101c09440400c2c5071403030143c4a4072950200600135078030f070245c001d81e2000b0f1002d058035490003e0121603451400e0100200c0141c886c0c080b10703c4203490b0141c04001e80780b00e40d9065100365845040461036908002c443e00c01d230380145074115155a210408004803c65074001345001e0342c40c0d00014080142000c03919015a00c0c50b011216101000400401060340c0000d49805c0c024520314421810f5210312800302e029110380c0d0005001004403104010184e98154403d80032500c3d4a960304100c181201400c0c0c800f0101488050030035400720107681598946420004218495100c00b45045050350b6144145508654007040020303581d10300800565070420810b5501c43c14881498805180403904410885c81408410303c0034045a83d444c642c46500c6a1002c2c114150b1041919240b039039004800500034203401030602401581058442c036040880 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 412838534 1250 412837284 412837291
    0x503071a070804030507050a02030d031e02071e0f0c080321130b06040605130f18031e120905010510050406060207050411040f0e01030201030c110a03080702010e1002040f0e 76
    0x3502c5900c0c0303841c0c60701c040307945810920703040d07900c0e0040c08410f80040e5004c00c070080d10014203803000701c1d040c001e0107904001e501e00d0030b6809001c9401008179034001542c00340a10140c8810400304e224112150404111001030040c000342515046900030841d142c0000207016180c40c0412502e4600429a01d001c0c0100d80945580804811041840c0d0001e0440145240e110001400020b0030f55a42c20010300300e40c10b05a0421680c0784c0d510440c2c0344c645a1800303804182030418a00345a640310a0f81c0040044014003c00710b0390b0342c007901d4120301d00c2e0702c0380e4040840130084440501800503641000b034007c15050b80d598a2000300c001d00001d00c3e0803d405031030308440c5141c000e00000741c82c0c20140800b03803541c1150007040a40410020600031b062126040c0981440f4101c0c200560541c0700140848400c10386500a200000c2c0507034210540000c2c030f241d030700307503252505400a031030347c9038140d001d00004a080d0b0014020846036011108441e07002c1c004940e1004d8107000030341d6464100b05520034058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 412839784 1250 412838534 412838537
    0x1060e01020c09150d0c050411130b030417070515060f060414040b0a060503090c0402030f010303110c030d21050705160512030a0c0e101d0316030503071a07 69
    0x498006006182c801c0740180d00c030580c074401020501c41c490005031305e442c24010440d40e20711313800c8042c8001e081c18401d04480140381d49508d4980210024100c40d1101c1c0c6114102803d0000000a4100262406080d0012200c54801170f04c0d00d5062030f185072907a0103044000c003880007100001d003e45c034012840c0f0f00c1580020300308928040c241071900c02c0f80d003100308926821030b4485010340714030380f03030194540010000359807442e4607420302c680024107210000c0800c3c1c3c032590040c0107114aa94000c803d00381100d1349400c01607402c001030a44d00d1308181d05080041e40c140100c04030341180320f420140c01c41c2d071a90201400313440200d502c040c0d0800c0b07900684266001a01c144101c0300f1407440a03100c0d03001d8a000303204a921100d03c01241d40a182d0080700c600030055101c030503a40c40d003034022020350741c1510100e410440009803900010f003250b04d501940c44030006541141d400a4030140480281110781e4010803030169101e0500582e20313400080111125200c2c00c040c110b540044105060240744d05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 412841034 1250 412839784 412839793
    0x81f08060c030a0e01111c0905060405030a120501030302100c1826030f070605090f010f0f11120403050334020607020f0d05072f010318050604021215010e0f01060e0102 74
    0x1280100716402000280c480e42c7c20344d6910311001044c0d080201c1403042c0e1249008564551805034001c0c5800c0e40300304404251070418005000003a0045103183c1c0d8003001680000d00f0104448045401420395450031032505480b0f40c0120700c94000c0009981d8042016410200f0801d810012580d40d101d42065694840000d100380000207040342c01c410b4101c2452402c0b2802800d88130101800c48890f1921203194035500c2c0768640d40c1e03c1250141c10002e900c4c803851a42004503c0b003d450310b0030001800102040800400200344444d281248441c201042c104030886654085008006105811150004d44903070400202c801d88001980c01d1000000b8000d446641503051083d03485401240088815100d1100c404a00c0c031501090101290303e242c1c000341c039039050f56001504880c1606040c8441059408019010542c0011026002541510b200308901c0602414a040c003092000d000c080000c0080006140108914418000c030286203c80700940d82c0c43c0d10070765110501503142c9015800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 412842284 1250 412841034 412841047
    0x1208060d020619031d070e0708040b0708091c05090301180c061b14150a0c050f0c01060f0e0a0b03010204050d080d0906060f0306060b0a081f08060c030a0e0111 70
    0x4100c211424045441c100800c084104050082c046a44c174000201541e0192000f00070300c004080d107980e00462242842841410a0303200c840c072500008007514113000b00a000704800b0403003000004240c010a41c0000101390840c1002030150344141e020511030340c20040409403a47c00c85a45000c5154401c946501c030502d40399068401c19480c041081201146110b01800702ea94155030b8a0088448000340c42c2e10f034007000d00c0344049a001341c21042e882c1d15100c808001140c2001c1103980410700419110303210484402c016024000c0c2e500b18103e03203030038203800149184110a082d40203090303040e424401c01c0300800c2418200d0095220301507210301407030350f0700f404100071134000c0c00f00c080782c01c0f004584035800b9140c0d00281d030750300d60000c500880360039070400902c10140724841c0a840314204591800065050003004808040d15448040001c0311140400c1920190f1601c0104119002c0d101c40385440f03450f141454108031280406242449048803d683c0188100302c408050300141030f0070800c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 412843534 1250 412842284 412842307
    0x316030b01091a09150904060603020102010e0c060d1a040608010b090106020a03080103120e100806011407200d12020106060e040504030c2405010905180a0503040509041a041208060d0206 82
    0x5001178144460311070050000c042ea03403504481c1c5840f41707000f98000700f0158694400282100c03403480c0d454802d41c0061591100503503405044a4030001019800b00700000c01c2100566000c1c07c081541c0e80c4980342c801c0018001a040d045400003480880311010540e998060980e01e5169041c0b00800040007a0010f000160304900c081968580307900d4000740034040040800c490441c11002800170600d250104180d40da407043c88120816a4110a076081961698038035000d000c0e004a80c02003035a1510b00d2089646404660b00303900f68204058103400e8081d02400382c02410680259400240d0f9000f41007510308003070140b01e001c0c41d81595001c0014520744c4580148421528889102c1d807000c000e07500d08035685000d414040c011030b15000906003050207001c04d0540a0b075460308802d07000510603c01068002c02964101c0c0e00035607c40030103035550301e821105102048045840074000f5400e00003070102c10205c20b0300303c80e280c3d1103080060b202c1d001001103100b054a00294040b40c100300001900307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 412844784 1250 412843534 412843549
    0x13031b080d0c0c060207030207030203070501030b06031911040f050108010506190c05161d060922030c0204050f07081f090e03041a0c0105010504020f07060902010e0316030b01091a 79
    0x10340078500b01d20f040303c1c00d541d008140d9202110a50040e40700d14418020740ca01400f0302c6000708001d00b005c1041e4500751001c078005002c01814048450070500c80d001c1c07211010340000d122100304410742640c0b50f80b6003e00030b09041d00c03400343c207001811200000c01c250070b041c0700711a40c104800890070684045500103e601103103c1320101d070b01340103440d500140690311030303003010160001c40d00c48448800041c098040241004240074403c2d0304103424000b1441c9038100c05000c0d00c1d01070000c1994900c850809032841e81241c3c0000b9042860401000203044101090700d02542c025625413a00c1e40f240070b1044074501d0110ba1100b2921222181000070321540c0e8003c070320003940e00d000d880c20503544450141c100c050f41d0500c0a80410700040c400c00c036510a224003400b500c021141141010b910316440a02801250720051140d50348003c100b0540e070081050b01880e100003001c4a00c51515110444151142d034407048807500014000409d1142d460300400c8800d038900130550b400001e0050400059 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 412846034 1250 412844784 412844801
    0x3050603010b09180717070611030a0e01180e0a02041805010311010e2d150c070302010302180310020c070602063918100f0e0f0a05060313031b080d 65
    0x142c400c103103002950191b800c81c1c10744101c00301300c081d1801c1c0340b814030b0150000801444424107500200a0303804869044401080f42c4503080c41d0400751000d00e5001d501d0600030541181040101c04010480d103c540c0d90001c1c004e6801043c620b07803220320544d109405850003808001c06c00064048403c80755407040d140e98801c20801403001800c1c2d0426040c0c966802c038100c50f50118400c1542c103102c01420100d949500d80c0c4c003100d040901c1c2c05c0d11f410140c3d443c1c3c0c5060000a0425800003154560790414840349055028000d042d03030141c01114011600951000350200c900c1d0003180d40000c0c8050001c25924802e40760403d0080560300d40f560459160a070ba0318030810403001d0880814001d0080d20080c182490004030004000b428050400200f854004001c0c000c00404000c60200280e2026004000c54002d403641410840000000b80e0039080c981c0000c3d030008404410462515580003496440754001c2d124009400f019012105842118807409003900c2010800c03078410b40c0b0b0360b6000092 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 412847284 1250 412846034 412846081
    0xe1809010209130b030d18060309031110050103030909020405011b0c0f03031116060e0d05010e0a060906060b030105150a09031502030a0f1505010509190803070303050603010b09 78
    0x240c2200072000860f000c0501c0c0201c444140c1d41c01900e62141000c00c400c3c000c0ca1a81c0c10246103034400c6240150302c01d800c81c01104109a1104504000c040c00364945810038021441545c40103200c0d9001c810040200344010340015549400010b02c2c11080e00c00c690950324184d465000c0714200341c9011132f40c0c4150802c216030101c1c05041c000740b040362042150016500c80d035510340300d809041050034035098101e24134100d008452901080040e0704681c4c54171404405070b81900301e0320482d0816600410904070f800a540c0116146d07181040101c0c0c0c007901c41140700d11000c002280d00c44260030307410b0009000d600d42101c0350f000d0f00700300d4242c00390140c00d54034414501a81045e4880e607400c800c19110455560040341c0100c00d01070b0403c0c55014188040315040c9007000a80001110f0000021441c40765038140000091802a1a111400f18020b500080088107081c150350707800b0720f6640e40c40200250006841d0002042c10362a06005503510707400020801003468881186114250084149055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 412848534 1250 412847284 412847287
    0x7050f1302030402130e0618010605010f0c062d0608013303060207081c14010902070c1e1a03060f0907121a0a0614070305130f09020d06060e18090102 66
    0x4030300b40017500820252007426000b03401c0d203042055440c0300c040102c00c21028580d040c51000c0c461a41d00c0a80070201100c1072403c08980d0806003441c1008201504545000a200e644011540c020781d03052150200800241084070369a20b803e04c1d402c0b62401c0b1811813200440c0360390481c602c1c0c8000c0704c01009092861740543e509550b550303184100d0307000d080221150f94008c100003d69a214905c1444070742c401c000244404200c03150180070b8110140a4050155404203d40c4217010b02c0c242680060081d00c1c4128a0000c0340c8001003403201c3e014496040f4940c2004a5141c11040c000c0c140c0e0300940001d400106494003000c03c00450a9005100302c0c100615206001003207036a42c0148810403901d408001d0b560501002402206184e03504000140180e803402c800a0300c0d103401c204c41320950140f070910744401606101c0b52410119522140643c42580b8002c29002c606a0041c00c0c42c0070b17040c20420160369590011b403050141d6800455001d80c18484207880302200801807644550f0340030005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 412849784 1250 412848534 412848559
    0x90b040f05190801230603010b0a03021210051e10080304030602090112020a031406030a0b0c1b1203090c040e0d0809010f020d14070e0915011b0503030907050f1302030402 75
    0x2400c5842203400141c5002034003408009084d80c50f417103190040b005400a00190014501256a945040c80000e00070072000d80041c11051003031140c42c90440c1c0050090016043c04280c0840c01400280e542642d03052450211709030456201d040c0f41216580070145082c54950340fa032078000d40091100038107100811800c80000301c824401465212070580700021101030b9070071441c640303250080041b4040c1d801050700b1004a90300d007140e141d0014409030013a980c0e0360800e0700c0c0081c12a01071f02910841c400d000401100c8245e46c006144100c842c0021255201c0d500000c00041c0c9030702e441050495088591510411403042148951055140002080650040c6680c40890348801c10546000390348580010000a079142084d03080a418986000242d15a8000990b01d100183c8080d130b84600d00c3c50707401c0f4181d0164401e41840c1c3e03800700f0340f42814207003410000d4403036104942103003880c000c1e1035011419117080a20b4108807040038100e85c44007040a071141000750710242060341e00c00d4064000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 412851034 1250 412849784 412849799
    0x40b0a0603150903020c04060501020703060e01060e01081c030b060703030c0e0604141201090317041406040b010303080f2406070c0b070515060d0b061c1101090b040f0519 75
    0x245000e0510b01c020000c1c0510040c10700a0a020b210031000d4862400c001d82000103a034001400c80540c1e8200302c0000f00104c900034051b00405e060b03400756070200c0c804000000c035880c0c00301303110340600d041055148601314112401c80840e103d15200784e9022038203000c0640402c2c440e91203c40000d2b45410712203510285080001d500e500554840480c0c00750760502407a031400d10018080190400700005d021014580e98050070000e2138050380c0400001c0ca0700010107005040c03104450b8039100320180c40e41030419082c000e00d181424001034006c40c050700085084140f071848060f12039070301600c103565210307e1481002400c941004155500c50740520000c3c01003070480302e414005003203140c2c0880c3e42c2d202c90326240d4184401c45188110110030b0600b00109034075605040540554490f1403021a95a0840002d182c2488100107010078912141001c0811a400d0226240c1c4482603c60941e402d9503865003011501c5940146010300c02000820020b0b810b00e480e07418905800b5603e860310840d150020f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 412852284 1250 412851034 412851053
    0x7121202100614030f0105010e04080901092d050d0201211508070e06030307081e071a01061b02060702150f13090606030207020f010804030e10020a05010c0302030f040b0a0603 77
    0x8a054403e80001c0e101030145010050252107403000e500911080d0702d044100000d420000304081d0600d01c0000718081c085c1c3c4101c3c040740280100382c510000c124802424080481c0c80d01d000b00e0728234500325002090a00d85034614407162907050303480003048040d1103400b80c0c020b840424545130715601c482c030052146040034080c00180c01044001d081c59441c0c2170790f040380c0d0307440504294003d03002080741c43d0100b0304000882c0c01c60b9888000305071584442554003001031147d6074001d000b91443c140a944a680c0401049040384c2c095a180040e0490050030764030458068400298002d80807c00e2100504110002c0300c5440c001d034031500d086c0540e482e9100c1082c0d129840341c2d5041d4884450900001115124030005445585400c40c01c082d01d03680880c02a485e40e54107035052001c43c60004d0105032203005681952a006004441c00b001d180da4040e64546031b080c8222101e500300325240c03001902ca8801e6070b129600c40f048407000b58480780ca13100203031503020340585007450f20b401000c00450315422 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 412853534 1250 412852284 412852289
    0x703120e0703051014010e040f0305090409030c060b0f0604050409081e03010f0b0a05030a050615130311120604140a0507230915040e0c13021b071212021006 69
    0x40c054620402c203240450205c400c51070418440002060050248049456a41d0781c0191711080c0c0f1000810329003400d441d940174001550303030703c90700b0500c0c0f10041552005220000728456482440200082c0f030400082c100806601c1c1e4102d0310600003000a45066041048410f000d1002107240c400720001c216001880c03440300fa020f1a50000041101e401c4076048030000301321301d0340c0c600c1c10511000401407135440b0280c0391060135034450002c66039a0b030790445407841d10004100229a1a1781a07281c0190700d2050f0703c02502c240e00c01c605036035598100803038400e2482e000100502810303035450752010b4400c060403c2403111480340c00c000d0300018804001490103040c544190049a1089501100000c442010641d0107a40714405102c0c042c110041e944510680844021603d4200c0c401c1079441c0c140841401a17001e0081035056080f06a00e41c01010f040c0040d8040d034002405002c249640ca1086104d4094204404051080814101d100161070440f00d071040e03880308001da080e154245c55154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 412854784 1250 412853534 412853543
    0xb22050411040e010801060803370216050303040506040b070302070b040e06040e0312010e180115050a050109060e04021e03090c0f1008061201021b0309031207080703120e0703 77
    0xb50a110040040c80c4031401004480001e001c003e00300700c4c070141c89004045d5080e0340350030001280c403004100c0000d0425515010070383c491641d00700e40d01c000e68800d84081a00c2c1a12111100031446d42400f000b100c047c1c51011703180502d480d1a01c1e82c2000e01da070200300c054045010b25240810b201c00203000420040030800d07448040c40c10448100002c5401109034001a80c1c81001500040b075840a84581190040002c4aa240d0b854084188450742028480340e0f441d4a4000c202e030141002e90101d0007981c9040e2000b0310f10039125001510f085100e401840049180140e1010302c42c82c181d00100006120170200c5840034081421308040d682003a2280b1640ba001845101001c2c00c0210000d000008204c6852103146641d100150280d0405490a4015900042d15908540007501241c40b40262a183c007501c40d55855100386d240e42011070a28030031301812400721014001542039074800c03500007000500d443c82c1aa4155040304030135110ba0101a1194400c00700210140300c504001c5018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 412856034 1250 412854784 412854787
    0x82d0601060306091b1b0302010e030a02060a0b011110180c0810141506160816121715040902130b0418030801120f0c060f0f02070b22050411 62
    0xe2280d80c005031945c82c2c0d403a06010500781110b103030f8107500c2940018040407000300120042907504040f40900b01281c5800e180c1e100014000341159030006007540304060b00c0c2d004000580b10740c0c0044603100403603020225139604c102c0441140e10b603540d124000c000c080100080e050000742c1d48035481c01c8019130068605800955003160740314410b015004200761300c15505a0141b81c2502440444a104070301c00d401202e000c25485510228880c04070201c3ea080385074992240340840c503140d0300c5024080112003801c0768002004007a80111240c800c08100e02a00d00000e9540780c0002c5a140c02002d85030784d209854480c5580540c651240154101c150b145003c1400f929990131b00065070f61222111004207641298000800d07072111203a8191481d191071210a4075840c02c010301600c0e087c3c0c00c054840c0b40c141d50300040d000e0300711401d0214042c45444240700c1d148120000e9032245890f201c0d4864000c020030601585c5054000c0d810a00c61070a00b1500d94151101c01040848003c8004442d0301d050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 412857284 1250 412856034 412856039
    0xf030301061737051f06030207300917031b0a0b0403030225021c17031302011407020a14060c0304150215240402040305191209082d0601060306 63
    0x2500e00600340e00a403c071380c0d20240c2040c449920310440c1d02d21b206043c1007550104400b02000702d05029059801c100502e071203900c0200328100548030181003d284013040b41c0c41400907150b10a4140c07000007080b0800950b042000d440c01100d641d1105d907140310b00780c0c0030780350040c00000d08044916004038000e560050300c070815103040a080030340180f01c801c0007803a480a1480107a4921001150754040c0320780104205100b0b01d0158200422505c010007009004002c000507aa14039015070702441c003d80c0ea54115415801d007101c0107100e0107034080c0d04040c0c40b441c144001c2d4194011208240400740c041440d290b200c80c00c0c03a06580041c2c000440194a50301810f80da6541001034024080e035144d150b000600303148000c6c00ca0820350200401d800300485a005500d965203030305643c000c40c0c200d410798940e803140303c43e42203210080344001c03103000081c502e40340c40780c92040985400303944481d0018191403514003070540070404050000100c2004551070314032074000511000c0d00078049520b001c10b8450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 412858534 1250 412857284 412857391
    0x60a060603110708190516060912030504080306150c030a020a0b0a0c0503130611030a0b131118030a0609150e0102090a0302040b012a02030f0303010617 67
    0x201c0b1120380c42e608070401d00003000401d0745001118008401043d02d030b6074103415142d05440314000d0f401c406150802e448600e106001d1030380c103c41240c51154613090090f4500001c26002c5410a541c09025040288001540f90500f02c0028003c5400386403100d05080c4800942442c50b80100d1042c4016000351101d10104140d100c0c4994200c00030040034003031070881400041441c000240900c6608404482a00502c51a62701404c04103405400260342c0380750811000000d03107444000c69000300703009890740c855030030305105000300c004806010314034014003007248608042403103000710342c18000c048980c0002816440b0315049148210100510483c180103a402102e4a507915a5484c1c0d00400024071036a45800e80f04041c3c07541207070300140c291443c0d001200e407007001d4030071840340b000c01002800014078600403042819100b181194166801100384135140e010078410107003c07c40154046124268440341668043c040c044a030006958044860041101c121551104064540700040180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 412859784 1250 412858534 412858541
    0x60f0903070e15010f0903020612070f020a02010e010e0111030711130608190f0b0c2205090105090c07060525020606012001061208130f0b071101050c060a060603 71
    0x51550109100b039a1800070904046643c1d110566410400c1c0340c9000c42c1020301500d0800050741e00030f012541c0b030345000104081c00c04000d4607150b020400c100305200c0003510028800c85540e5043c5d44034061549010019aa5828032111090512460344103401c4904000c202403c602c50060412074035640200052000040d038005c000d0002d9424080e043c0091240010319008a082060584103034500c20b0404500c2d030310107070a0060a8203110b1051004080d07170070002e00b048c82c5040700000000f800b2084003041e00c00d10b5205140c1c00c07030040c1c3c004100918000ca160346d404180500300914021007a40c90408848084038101e6a03903052601084444d82c0c0003001070301510881c001414103042100000c0c01c41035000c600301c0000314007410490b0040001f0b41141d4000d010450040d0420b500f1494071202039046004a000703208001c10000a601520744400001c5503c045111890f010031911030352610701c9400c40a50500004000d030307506543d401c00c0031910841d200c42c80058035506125004007076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 412861034 1250 412859784 412859789
    0x21b030d0b01051e0306040b030a0606030c050d0314030406090f0804031a04331418030924040b0a1805041b050c120c0f10050106200705060f090307 65
    0x1002414048000c0080c4203110f012400d80c0e075101d03a561a55106c030005005000d00c1310b0b4041c2c05019040c071020410605820040c141c0344248103c80000b903e500034031040c038001d8035010700050070b503100d0b0b000d001400c0401590001c1c018000840c8151003621403c2c403540e0134400c11a08880001420003c0c03100c403804420500088203040702d1035060603100c1383c0d020744d045d2551040342c15806c04101003401c103412792a40a641114000d02041c0c2500740b841c94214801c440ca02801c2440480145081c0401300807284020b100504101c1c900070300c50000c0f0241c17505c2c921070302d804020130807004c210400298083c0421110b195100781d04829001c0c640104104190b220600590800d15003c0700c10380b449200c000b40191515005481c1e4480011052400d4492080800040e900040c204000324001c0340c2904200c4010b0105c45070119407041c228100c8009125188c0000c482144003441b4000c580d46041c01800400300301c81100783c49000140031507200080f40742c4030900000300c9100500342401103000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 412862284 1250 412861034 412861037
    0x12070201020f0415030b03010e0f06090109030c15020f0d0504061404050c01110115060302070b22061a210c041103041707050d090f0503160612021b030d0b01 69
    0x4042d620003402c5603038001c078041c090703d04812101100354248260b0180c1c086050040090180d07140324044076031516020045040c0c140203090024910b400140540d01340c4940c59558030410078041d4403504103a990289811810079000c001d01d0307140c403800700c018060031501700d40001020705252800d9000c4a10280070048000c424104000c0414130100351303428070f008282480241e1400006903540105010b8074603042c084407603c2b01040c101d50550203090454402c10701c1c8001a240e00302c501c400034850140740e400144107522002c0004032580c0000c0300096030040721380304180b005400a9412000e125441120203449240d04000390800c00030400c080c0c1c015103003008841164402604d2600c0010030103000400743e1841440c007c4020821075062642083c20385107030002c1c04200070328080e550b01c01c640440b0100c502c080344074940404c498400942d06801e01d1403203840d01000791419900034410040c3c4990a100400b02c003110203234800802075103030780070b50b9840360003c400301e08440800014a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 412863534 1250 412862284 412862287
    0x512040204021e3009101e05010806040209060a0b0f0f09090403180b0f2505030a030209030709021606090c1701020d06060c0812090c0612040b072105090712081207020102 75
    0x2036143c40031440d44010000c038100400c610008260f12400c00078121f1a40c603005191000019041c100410366602880c400c841464190b00c5007020081200e101b030261942c0031604101d4401230803665001000084038510856040524a00009080d55011038003640424600140d044514121492400140030707215030f56402c08032000b18850040c00381e040028100c803508910f488010014424100714194450100e035501c188181005019400c1482024001d1003900c50110307580c4550b0094603000c85100060034442e00a68603010040c00c50b22606440c07440300c402e070124080c08004058004549400c001590f5400c0d01c58010048030203681c02401040b2882076483c00250b1110300301d90b5402d01000302a5600e841d100071aa0a043c02094075690084000580e8840c0d0030220011500c514041e01d0240311a0741e4401c01550005001c030f182d01443c151001445d02940b072a0362045400c00707100f0084920b0301c0d4942085420200c1001e10a444045011955040c030007d95440c4035801185132000f50b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 412864784 1250 412863534 412863541
    0x2100608070b03040203030f0a02101a010e130b040608011a040501120209070203130f1701090b01120809090f040512090102030a2109080310060512040204021e30 71
    0x64881c0201d00920140400010100d802d65034200300350b4801d50040414640e0355009114065510180403c2e1803800c1d0f4109800e2610b6804000c1e8a12111401a11500d1a040c00b807410002d080000c10603040d58107a40300e00005464a4601c1420058a1030900015407030040030320100d041040a04c1d458441c60070200148011003908000c01f2059505580c40322160312014400d90860081c10840001c0c00c04a15002401c403680481d40802c5a0110740800f228170400140c59081c0d40e01c403103001e402a410003004000341d0011880780d5280c540514411341c10840d4480000304400310540b6000940c0710003000f44424802c00b4020003184400f007902c094989100d0f000081e4607030240d050100144920703001c40801d0b140504450f2101100f12a00070040540c83e480c00c4c00e1582c1040d100307500301c036111800100c1c3c4c06000b10100c902c5020121100304803a0b40d2a401c2102030740c0000180112283c1140b807000080c803010001c0d001240c4030b402410b01084d840040c4141100c1d2807c0307070070030027085982071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 412866034 1250 412864784 412864799
    0x501030e0c031b06041d042a0618030501140906010806070f0f030908030906040516030203070b090a0302130207031d0616080903030d06090b0f0102030d0b01230703021006 75
    0x4110318000c0e0702607101554071003070f0002900d6018a07482031400b13160152400d070810800c081c82d640700341c0c42601040c615154918281c040c0341e0104682c0d40248a09080a108d07840c0a4690890441132841c6070098580c0c40c3e585030740c00e441216204500d81d01340d180510182510030f211031809040703010020401c2d441c2540006090810100b1400140300c0c80c0c84410404074443d4122000a0350004e114554a060030440e49a0f600c10449090318036015181e10ba00e1120340a05900041300d400400410100d42000e0007408603a1108004551000c0e030b84d00004016211580d5070202480c00100058440206040180100002c070403250b03500440b124080c03109070364500039191030400ba9041200d01618a1611010a102e12881540d2500c00840c40704d91070405900705405031a400b40061000051403001d21283c05140003450780541c00c01c0c0000244410706510404065405152180d0403101c02c1e00700c400811103109940c42c1480f000105201030540400505203607140c03045040110904e070500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 412867284 1250 412866034 412866043
    0xf040b331c05060a050603011b05072015030a0605040501060c1502070f0609020a090218031c0507030f12020f0a0f08150d0809030312100e150103020705160f0501030e0c03 75
    0x402c10040c0d90341c4000c10100c2c0c40075803000e0248003a5041d2001242000e04d8003800b10340181404941c41ccc1c0e00e12040090481000300644180701020703100c1d1100c20b0910148802507000141840702d11036540000240035035483c040e0b18000e140584030544240b60318140300b003111701e2011002c204180100441d10002d108a1003028145130440d0000641047c40d10000360b50303100c698403004206001162a8068031a045400110202d0442c11502e01c50340e21550416280c1081c0e480d1004a80140400703c0840c8c0512004c0c1106801344c900f241d185001c0c003034550103c0c0c01035070308054402c1e004580a1043d40e000300d51405860b2083c00c11003030900c1e204452524615405603041d020f41008440380c02040240800d84403580703001000e032030b180d21900f0030f8004228011071710765007002080a000100104030100c094029404071400828003192940158082d512950003107585100e016041c40103220002200701c05490850000000d41c2d01d008001800d841607180800b05540141031010050380d00000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 412868534 1250 412867284 412867291
    0x7020601080102130b071509061506020c0f040207050708070306020d0605010206061f1209050c1c0c121502120f0601053412020708060703050f040b331c0506 69
    0x40e110743d1106c503494503440006c0042c084c0b41006007020302013420000150428400c415108015041c0325a03125001c90b91004203101841d00f01c0c1200c03480c03190509241e00148103450096040701d9980c0e42e180744103858800c150740169039159000c41e00788441040c0340100303001098248014a5141050000a001e00020200544031018a40d040b801424040c0d00188000c1c1d40d005030410940b6101c1c1801a2500341030796400d882840211801e03601d0502c01c07644411002d412007000c90310a810007908852107e0702510079568411010091710f40c0d08c2050000b0014581180410100c13814500729400c6080e0300036000c075040c40000e004000072041994008295247d01c82808500e41407008034841f5480202c140283c04401e03c450403900c090b4001032654103c8150204882031903890720030880c12150103a41d084500069040804c000c190546001c0da00489c440103070704034000703a401d0001b5142e80004810f08030605c400c101c451592030510740d840b40341000800d48515000596498503110030005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 412869784 1250 412868534 412868549
    0x1808090d03120c090503060109090f06110904050910111c0f0b0a060203031e040f060c021e0109050f031810030b0d060605041505100c0303021603080702060108010213 73
    0x28100402030500c5420b00c6482d041e0304050401001c0244080106100e01c80e0003014080d114403000040da1209074807404030241c0d00554050440c680956961303028207003242d140c0d4040241031141070500d64991050340e005215240082254640040041d401c0c1e90440036204110b40c010711180350140382c200c0c1ca101c001003088000140380d80000c403480d002405801645908001c00301c401283d007540010085008a054450b94007407900051450340307a290085800421810000d0051030020b074141c0c000384001c5500707005549600062400110350717500180c2510200782e44610b82e100500c4030620051a804480b207025614001c41c0740380f080326100754110600e0062180d50300c0b410055110350304c4a49220341c02050808103040394101040584421300410344690b00d0b0910b40c0300e12291524045040381ca010380400300115850030155030075064104190140342d002c0218100c2c12511401d00b124141c407075110200d180c1481c0c80f000b450440160040c01050b8030420032800503d0142d0243c0c1d00721106c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 412871034 1250 412869784 412869799
    0x9150405070309030e06090301140103060c0801080c010203071113090c181b0809030c010509010b0a060e090a02031003050f01020409053102041b0c021002011112060d08040b030604180809 82
    0xd03007012038010f0ad65050011030040003035001204204103034110100104581d660040c5907601c3d15034040d2911491561180960f004126030710000c4e000880d40c8008010081030b419040b010102c54000380d440680c0c0843e1581e40300001803140b040400c05c0020300032481c031800c025500b2003207100c4494080030f1403d841407000c16400101c40c5e101c200100c0e91481c41d010020700c4907080001e0740300c3c0644146040c6c0e9109100c00c100c0821013a11132050305441c1c04000744404403644610410301e00030b40c0b02a10148810101d886c01001050040041a00400c031801c001a034841c507143c00d01c8100c86001c5e1038000126902c0d1030070400c1c00c200c204280300845404014244e100703050302c006001804200d480c010b40c15403280c100c040c6135821200c0c54a2440c02912076161480428100300c0c00c840980001448162040c002d4605441414041030740c0500f020f40b286420b40e41d503803201d40d802e40041d4040003090400000300007241c01e042c0a1359000c0d080102d00c00c0520009a51540618012085564021145c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 412872284 1250 412871034 412871047
    0x1e0705090406092405010503010b0f03030a0e01091e0503060a110a030f140708070809030307140906070b0c1309020712050c011d1015140d08070209150405070309030e06 74
    0xe103981056040c0c0602d80310300c01300c03001048030300001d00001d128480c482e510744100c00728a42402e0b0704042d84940001c000d91b14000c16000c041d0b41c901c4181001a041240c607003004034162159541d481005082c01d4240c06201740f41c4410140307071100060821000c28100b40c0400c18000110f0309480c115209418042811100704030854014400c4903a10304040e1078103814808102e0b0071070320081c0504440d640e58841517a501203060795034801510110700140c1c1140d00700d0104203440e005411900c000424403842d02003ea101c050485509031074558a61000241d01a034810300529450000c287d030100c20344c02c090454170b48c0324015000801140502000045c11007000b84203500001d039814a282c2c580704000d0780002d0b82da50342c40301040e0a00301c151411510000300284540104d0440308501e201071070010f80301042c8090f16844010031a00e968083c0300185c0140c0c0d402054510584a00607691108508501084203540c4050106424540362034500c1001c84d600480c050500390099620554444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 412873534 1250 412872284 412872293
    0x312050702090a0504050c040c0503071b0c081e070e0c070206070b0124020613110d05060702033a0b0a1a0d06170a060525021e070509040609 62
    0x1054880c000d62140c03940342008581c84441d84814081d07402242181d07030b10204030b0f041c04201e0b220080d604001c03075024000a040e00f03104451041e114404031155052046052b503400a0040040e00b124042e0380103150120700364024041d42c22030143d8000d0041204618000103203802d00300c040c200341441c610010b65503055454a0303080b29101daa2001d0040340c250383d642003076061074516000401e44a0404a04982d5544c4000b80140c01211400070303420149500759250b80e40d01d07802c985400d80051400c001540883c10900c00c0d18418082034020b16075884100849020300e00d0b00100358407000f4007240182d04031082d0721400788284010304e0b2000401524a400103205d860141d44019046100004215082c22402c00505400404480140009526121b66000700b450b20585e07650710391302101044002c00c1c10740d044580c00003403106684940c0d20320810360a2103031300d0800704000564803000421074161942c42c440c28141c03040380c1c09414050f040030700141c2c83c41d80181003d0b2202da200c004407001d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 412874784 1250 412873534 412873537
    0x70801030605060a081605030607030209130906110c010504020901060504062313080c091003120302180a0605070b010905060f010c0c05040204030308010f0b0a140a02070806070201020d0e030a0504031205 89
    0x103052410403a401b8038080880c4520070303600360060754001e001d000040b4940b54041d000b0743d60603250041506803000d8008450ba4000c0c0003001c2d09452054a43d4142c2c5584201c1b003000f0540c00071502d002180300d10306401031094030700d010b91120041080802003003020540c00400803c0d00904080c25407851180c505402130303c2d0240d800c031041600c1c04224001240080000c241c6a00c0340c00755040249030f550b20300c817891002d00718880600900300d0100c0182d2198801c0c2d006103c11078181400040446944011503500141c13070f0000404282d0028401d0140140030704101d00400d00c185007880300e441c3c0840403d480d000884000c0b0b05100c60302817100300b00300310b00c505c007000b80c00060011920340f0354034140204907503020311403c42d401070b0320000404c02e012408100c528048254440300c250b06010b485d0000181d0100c401203086000360302021400110610406024007074603400503844d819040c8180c002c031082e01e4245007413540b0401c5000a80c581142c161401c90307412500070310182d1070840d010389d0f05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 412876034 1250 412874784 412874789
    0x80f0c0a18171005090c0303071b080607031d1b010f090312081f050a050f04022a0c01021506010807051201080d030b030109030e04020c031605030c0c0306070801030605060a 76
    0x8079001c2d899055151a000445511100050f8410300c1503882d02003140c0d46910071580100d41581080107072201040520080b40e0340e2110130b403030402d03800d0b540303031a8241000c0c1d081e42c811000940700d89102c005d41101a41c0c8a25590b02c400c00740038401840c1089080d2030030710041c2c8a06112040044904144c001c00b203d00055030040038582f1380030440200140004001c582c401c1011511601c401c10300800f83d1183e038140c41d009848040c0d028200000c11000c45581d000c01a4460340070010300d00140c0707a02050109204540c0d4030100311125241d81c150038201c40404a50440d40110004500d000e580120b048d0400c8003800d0802090300c074094100c03007520600f083c1c440e40306031142c00012038820009900008144940c1d04000b001204810523003601e01d4450081d000800ca5041e10071103251560081849000703080071207142c5400b032200300000c00035007038094407680c202003414044104203000010041c48210041d007480d00d003140c405040c0d6001800007400c035541d11000107481d40c407468001c101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 412877284 1250 412876034 412876049
    0x91a16120c0519140a03080105060d0f0e0a020420030a0504050a20031606020c10050d060b12070c020102060a0905010603020a090c0f0206060a121a0412080f0c0a18 72
    0x40e4541d070f406090441d29018411aa941c0d0340c4003852007a0078000c0317550a1a00d62556446100b64030300010032429400000c910f00c0d83e5581c58110f00300e040701c01c2c4078050452107550041c0000344114010082283d80040b1201d407003058a003481404000407004896004040107800500794650381807007403900040c034034000c1c40309800780382c0794400503201c44a140120b0360440403948910355000c001442c0e013a451141030096405400b0070141481d220143e05441c1c0442d20b000ca007082c060704003650545007184d00240d0883c10001e0300f80b41815544100f154440028209050107110a600007075039600b0042510a238681e8854150080000c00e400c203800840c2c0081100003000d0301c421004006011018a031808507454144400341c081c00810040c2c885c160043c20404024507100341205400302030740302201d44000b04503400e040c003005c03129070500850040c4038540420b60607590103000d5141c007621101c0101500802c100d0150b0206040b01c510454a1800c00d00b11990002c80038040d5110790040c2c007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 412878534 1250 412877284 412877293
    0x1120b2d0414180a0c09060501120204050f010c05070510080f060301091104200304050706091e0b0d020705011415010516120c0c06091a16120c05 64
    0x2030040d05000c1a01509810104140004a441000201d9680400c040c841e040d4140025040720b582010a042001903041951054400d56844807111183c0d0b81140442c507907542c4040c8500d5a000010b07100700f1002490441c58a130038000011900c0b000b0380403650400c00f004052404002d0b0034003c0350020680500301000c1100b18642c0905402d01c1203c0c0a02c071202481c0000300700f440c4c1406030a8143d50807520711f0801500d108140300c05441440612842c4076602c0e076003990308004040c0250320450244024014807800d0241c0142080b2841c1d2166107001c0c01c40c040c403112284c852240ca4111144240da41741c3d140d03501d43c0348101902517800040c0542d41b07403c01e000141c0000049140c070070344507408c0c104000d0141800640b1f0602420a503c802e0001c02c44040c00010204d5501079031101e6581000c0c3e03050442c5645030300d1010710582040001894601007007002d0200740c009900c2e680c4440e81c0590401e0b04003100207008402030b2501920072402c003900c031842c01c2d00031800014002d4101c006c1e503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 412879784 1250 412878534 412878559
    0x90b0421170c0c1305040b04120903020a080c0108010e0c270627121002031003150207060f1a1003060f09050f090303090601030f05030d0f0b0411090a0501120b 70
    0x1515040d0800b2400e006292511550b10803144a00c100d130310640c0d0085c408011502c0301d827a0101144490701072a014490466000b2001d41e0320240d010740203260220040519000c040001007000c01d040e441000900400030500c08200c02c544241d505242025980584d0b402082c04c0d801c0000008440d1a60021400a0207030480000c802c01e04904c803400b900309294924105082c41042318240e1460001c5808c01c40c7c1541848000d03400554101044c041030814541c0caa03111803400d601110301c0e0074104c41d80050503e0070082c0303601413804a2800240100070362420883c0000c000f400c03402e6a184903000d20425684ca56010364800f4028040c0c80420300031040d15010358a00418080d40c080842000b444001100c610001044a109412590213024213901e1651010f04031135008030126440d000c00d2180340d07002103141c0704807110848000301c04030b901e1480c402807008880c86d09401c408140010401289103444004804c0c084900a1924078402c55500080d40011f02c1c120380405d52140c50103460303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 412881034 1250 412879784 412879807
    0x60b04080c010f0203180d0213020f0315011409061c150305010e01050c0f0706180c090509070305120a030204050301060306140f01080703060b010e09070f090b042117 73
    0x107080c41900a0321041d115240044040e81e403030055580c0c50307000b548040d8081c0d00504100c802c09090500c09062845440a802c450f502617030050013003001111404010428100c0c05405002c09a004c00c1c2010600e0b4151070b030342c00300d65100380c50906008a03000140620450100d481d0507550254980d01001480812013541802e00500e100a9544d582030240e142c1c0c4000e2b040c03040c240584407511040d89403080c504440c245a401400d8181c030301176500c043da803180c40000d201900c03402e882403040101240c100f60b0044122100905200b086912800e410b10020720000303030410301001840c034955183d10388544200c02031b00c180d40081c4d4055081c150008100301d6140c01c448400c10903955190720075650700c2c552442c0c4900902c2407084070f500c860390130030201d007444e07101c0700c1c1115040c5019003100320340781d021903c0203509403211380019122041860465600a180304041c280001603146443c1c9000c00505041802542c0c058001b8071716000c0d401080311002403484810a01000c407511844010007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 412882284 1250 412881034 412881043
    0x20913052506031a090601140c0102040f090c021b19170105011d04240209040504050601080118022107081005070f0903020108040b06010504080f0102190f02060f070201060b0408 78
    0x314000f0070308100710b130300e03841d0040b850181036900b010300203052658030385004544003209156480000d00b820003261451b52001c0c00100040e2040c220405800380c0b400c00c82a080383c0081a0113401c40d0444240c40d491843c0610002d00c8a402c04c46143c1d616160b142c0c50104640450b9001e05d400d5540519a9481034406400850480d0504140c5020104c1400350043c2e28a01c00c8030001d040c04014140825540c0200410000d03281407110014101721030000490203c900598003614103610040c0108100f0000340181c0a0885940107a0070381c480203079020610f103035070724095060f040600c0c1001d030380b40c80c500b04401001080c840080b504d080101102550050009440071b000055003a1108403005004140d80422a54181d50707044140d51a0340790306250350409440da60401104210010f0280b1007007140103120310300da000041c0e85103001450804144040d410382014008011618034840780c001c10060b500601000c030300b110b1b5580344441280140480e4110000e46440450045179050740042d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 412883534 1250 412882284 412882289
    0x804050601080a0209070c2402180609060409090212121306090501091404090804060f2703140109020604060309051e1c030b130209150301030209130525 67
    0x1a9403550341ca0b03200742c64481c0300300c03034001e0340110508001c900b40b00d220303018252046010307a21002d41c082803103074941c1c54200130000d03050341c41d07401150a9004145503c0704000841c001c56240d480d00c4e81101c0030803114040c5110300c2142a035a90341e02c1e07003551100014100907125510642e8000d41d0403004001071500a95045002e515200d8000304500e4001d040c000196201612140081032900d079051b1110752103110203e402580b10180e0b500080c0d002e001030006031540c2d403180e0381c1980d803c4400801080c010181180398a80d030071000502d200c110034414003601d03080f010401e680101c0c061050b01405803000001d400240018001503107543c16440f280176035125000380e800c030420484d2900005e503001118511a5040218031070107481d0007045103685c0d80018200400c1050079100011000e034180c02807414055000201c10102d0f203401c420f00c01c80284200440d904650541c6c000c038544040013003000a68000c5108000188941080b150601010303090034192407240300c6000440300c40291 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 412884784 1250 412883534 412883543
    0x4081201060807020303040f0212060f011503051302060c120c0d03050c0a022a0a03060501080705010c05121803011e0e0a03230f16111002060402041505100804 70
    0x14800451650b00c030b24036482c06840c490b401136056480310b4440d4248400300400c2241c1c0242c04030f496203140d130403d00c8100d100c3c038984220030711590f240c40001440c060706440b40f281014a818100900040980c10000040da01924036549840f0745c0c50055140c65140081d05c4480c200100b0341c02c0070341100144400c4e1141103a902408240c5921a00c0a041c0c003e251200300541c00050b400c02141c0242103c2c4c40501c3c0520340c402c00e400b40894041162012590000d035007007501d8000601044104008480041000b8640b606062800b070301c03003544032046120107102c2d00c5000101102408264891300217032900040c0200081a81c0d0320005c200318250401d20000c0c44d05010005c144201c010644c2c4070f0304c6416882e8481c1c0700d0704280002c400f601c0c4040d2100c0401d01b00b0720461080417120000b614a40440a0804031307103045038104810300140004006100340c42840c6003804440c0d0119000b0b4000d80d044d900425403098602e060080302801ea040079030010748109003030039580c0e4040d0b000c40c0507a006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 412886034 1250 412884784 412884817
    0x7080d0b0901080703030201230a0b060d021201030b0108150106050c01060b0a0503060a06052a190521040609050d11130603030801151422030c030516050a0b16050102030408 76
    0x30041c94151402c03461a0301c9c0340b00043c0c0c00181201e480f0f41124850241c010002d52a0800c81084c030740480e004245a00c0000c0350200040c030030007013500401360140456400030000d100145400d85c0b0b5050050045004003c0d0204100038007900940005010340100c0b45626120020084000c02c15081120b4852146210490009070703035015204403005500c14201d1110070301110948403400e950b06da0700402e024402c00803090404822000c042141070300c507c4c080c003480042c601c41030a0a2580c0e601001c42d601080000b000340941000c5103034101c40003554080300100c01401e1102000061603091900008900403191410002c4c0d44902d040c0c82c403a1301c45010b05d9032110324080c9020080403650010a0340744001034400c0c400f81029004403000311201c5584a403102c21010494036042c0c0c070441c1c03401811130040c42040700c280030348040414200380041c03c09280c07000149851103a88900310b203010000442240c0305800b01c06000155400000940d0303a4103052070003240710392000302650140c040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 412887284 1250 412886034 412886051
    0x6010b0a030b1f05070f020a090207140303060a060c291f0509010501082205011e051303080703020f0c16060804050a060f02040815040507090902030307080d0b0901080703030201 78
    0x82240100e000e003d0401c0c2c010300c2801ca1440e09642d1a405810281c0c4c403003003001c03403072401aa40c00e4415406041300c5000941c45411603c2d180c540078040e60820ba5054000b8000c00c14941c55010750813040b6001031400c1c2540303424a061071031460071801d4160701165030040c403030849400f80803c030902070480040d01e00300c1c40d54141003c051621160042c158003550100c010040356110f15007844d00301c41885480e008142c0418803c40c4d6044840000300c0b0703a6511203c030300c002015070500586003448258018016440c10398100030300c801c02c8103401028002498089075081303100e50b042d0b45500c10410b0b10640e42c1c00013128083c2d80c658281c0358010200c00030010100d083c52149811500965102c0010b0242d070000c1e41d12030026008101040413200e03401d00001941e101c0c00c02c07000003540e06032102c03d2120b0510307060803070404038560403419181d1708012850740180c80003c00c07160172682040d099900c41c0554030091002e45565500203520611003800894514808a407900c12244241c0081040c0745 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 412888534 1250 412887284 412887289
    0x90c0405040506100e24131716030803060f03031c320414011a0306010602210703020c040920040c091412072c16050703090308130801050a0e06220506010b0a030b 71
    0x10820310542e40409c04000090109000d560400c034000d080c56031030006240441e00d1a0400c00c0032500560310070006c04180400d522030700b1442e0f641c40f0b011745c103094058004e0341410480b00c54960745200300c0746c0000e01440741c4409016007280d0002c0081c840c0408401c06c4000d40175017078500c14424003488000040c0b2600010b0030036601103105803a180710b00d0040341e480145801411041d0154010700822114070b41c2c551055900f41d51003191441c84000b503403034034a010f180c80c1c5034150b8010380c5014600300c0d00640050f000f00c01c5a40700380c60b9190000135900400c4032100000800410380c401c5010116080800b000400c03544001921034660450079035140e510080c800b9545c0b03c0c549081d07048640e84e0ba91042c40107103147c038041d06150000c07a0b0b4070f644036111a4000c10503241214000c18041c00502003e02541d03401803c003440038420318004050f00394440030b0240244202d4030300c0c1052407000300f240d0120a900182c110f400d8400720342c0d41c2c50418041d540000c0c89080041d280c0349403d0902e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 412889784 1250 412888534 412888543
    0x23c030106053304090204261b040c0509090a060810020403030c020d051c020607090b030903250c03080304151503080315090c0405040506100e241317 66
    0x1003a08070002d407129540e070101842c600ca01c4943c920030105041001040340401c0d40001c10040c507030101400c0b0040c21650070864585010801540340d5004400c080259003070409807440b805c40c0403500010489210701040d900d41c13141003c000d4108503204108202d00013181c0c410b4040381c0025060b50b02c0c4050a4148070204c0c070450100502041004030a2070240c20000105d9208034811400c5520804181d4074581241680c5441b01d001a403040303007004601507101001c08000c10002800e1800c2d42446141e460b20b0780a00d03d25521124645001e00e94669801401104465003014405030070507201d00b0710040b180d000301e86c260f55100c800c2c981d50381c0316005403050b22850306405406501003800c44e50341080591004d8080360f0075039031a8244040075038448001d1406800ca0111440d56580780c02c092009640b001000b9030301c51110f4101038203803070f600042d40c01e080358000c41d00300d41544440c112450190702c5001c2a40e140d60004a01d901600b000d11560380107850755200c09040c00700c04040925600c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 412891034 1250 412889784 412889809
    0xf1c03090212101512060203060f0306091c0906020601050f030304051002030726070b07030e0f060a0f020309060c3604050a022517030709030b07020105060d023c03010605 75
    0x7000d100e14041001c6446c0d5800745802010003000101076603800c40019151200a403003150041e001a01c1e03031021407004881d84000220303036007042022540b8112001c0d4585805100c0e1500540b40d00988061540d002e004903000307400300400280600450080c021764a40048c4402c4600c400b030708000840003004071401030b0200725440c031401e2a0000d1a0b85928043d40302801003800c0c540c948800880c8060140840c052032102400140168034190605800361359920f030440840307510400c03d001c02e400b008070340c450b84041c0342050507a40740102c4101c803120301c2c903036031002c0101c9003500c0e806104010521010094100b00701c4060002e9180c2c0c0244204900c5403404a040c0c2040440c420400002681f80541496000f981c4000c0b4095507080d0000b1141d1084454500055603640148100110000702d01d80100c19403000b00043d141110108030054000c03040a88079507103035403062640303010fa4041964003000c5c04903140104000303d40d02c00e0316880c400014a101c2c0d400c0080110f1030382460a05c4188 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 412892284 1250 412891034 412891049
    0x601090501050a0e01290d091110080705070309080d1101200a0c0204020409020c030901170f01030807060b1201020a0f03050c030c0304030c0f0f030f020f1c030902121015 75
    0x25a483c0007442500741c002d4120521181505081600c041c6e005480645440b0580c4000440d105a6900d02500220011217481d4801e0312a50400504a544103190300d500c904c2c2802c1007651101a410290703002d00a907848118a031059855070510340307a00c4162060400d1b4050020b100c10452229004803141c0e1580d10340641d6030043c010407a5540c42045505c4010740090401454151500e1601060b0391054002a8413644009512456560320500782c484201d1080c0c0318200508120214000e60b02041c48040c04000004c6032110038020070b85c0c05829400401810b180c0040c40106103a8041c0d000490800c0109500781a40380c01f081c000d000b1584a000e60192176413665403003d01007103298002030f2060741040209031038400000c01c03850810300311501604400121850a2900400154101032803404640142121495848000909817068103450650000030300c40400c04400401c00844041d521004014501d403141c0c0002c00d21000c880c021b882c040c411400540303d21410ba812610031000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 412893534 1250 412892284 412892309
    0x1a06010302031603050714070f0201140a0f030c1b0302070906080c0102071505091c0c1d070c0302010b130f15060f030504050312090607080916030615030c0303020601090501050a 78
    0x5030404d01c658415a440700040c01d0450b44818a1403420915030040702c01120002956940c50095680000c180030790029074294003031078602c9140c00104a0341c440648241416250102e90034100c0c011000040d441c0038502e52040406181c3c10001d59a1800784145039038a40341c407001156002000c20382610508060700141411498280c41e40342d5a103108202c41d017004018040002c40e07640301e8003881025a0208006140100c6a040c5104203078490391104101c0107100c40d03542040c2880c0303039006030302c02c1240c1080900b40040d4201603001d450f040c5c000315409040100103103e408040c0d480356602c88402d800170802189498180d488910f41402080d000c15926441c04022a02c00d40059a00601c1482500c0c1064071440c04140300076425110800d0980055041205547d40000c02c1076120301d110000b00301644024014408075031a070700001d0500341d03c461802c064105200c0d00d100065600982c5900f02940d40e050081d250ac00a01603120058200030000a4600d480b20507082510000c40302c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 412894784 1250 412893534 412893571
    0x4020c0a021f091a12010602030414010503010509061309050709090c08070602031b070506030a0905010c0c0c14060c030313030206091516030902040c0f020c09011a1b0303041a0601030203 82
    0x4211303054035070300321191000040216680500c40348100c5030082c1059001142c03a06e081c03036414081d040081c000e050400100348010007690340c581c425107402c002d0075900e01802c1c092040704940a8141d4681c058950300c10641c0008000c0c1940e4800c0700f11a00650300c289071182c8807514691588103501c52200103a00603c000f281d92a4091028903410030350380c049410250760350012a0454104560b080f8805907500010300c1413040a00800c85c00300ca0700d28000e1840c011580e580302040b5071500030b10241c90500390181c00e00da21a101152400134524048a0320392600e060303100d5031100c100c2ca0842c014015000840e028003c00104585443e0490282d1a031590b9429164011081444500400c141e2120038940158449201d01d03501c2c60544e0f580d00500c00b0b030300c0001a18202c41d10810303134002c50700d040040002d884403014203103103801e00c0003046075101c243c02e4181080c1044c4403d100503c3c00000f05100070840c0d013100c40110b0000c401341c046816919032005404034001102e8440b0912a1600b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 412896034 1250 412894784 412894799
    0xa18030203030a030509150c09010306090b0a1a0f0f210712180206030a0f05070f020312060301230a06060f08161b050c031b061608040504020c0a021f09 67
    0x89031b031065500c4219026207000860072084002d041e20042c103c0b440008030841103580c9409248090b06045806001c0d81c866a404198000d5107881000a03400181140100030481c010448000c01e1403000c1c081d8882d40d61100b9104d00d5406207601d51400392031a02840705410b00303601d1035803182102e0b4841c942021a1000300201400c3c01010a80195025858030320069503480041d6004071003000c00020300501c01000642218005030400c420720100741304014509500004541c008050b05019000e19114407000c01c4c0500556403001504100380c840700b400060725010807510540050307106100e8681c0d00d0000361100d1000d1922100004c0f403101c00030b8051148042044454601860040382401a14526a00b5a1001d070001c5a4640001d10034290524080010603441d00c02e9481c264000311041002aa05200d0000c210f0f02009032030080000744009042583c00800d0041c00a40d60703102802e0b51607841c1d10752540101d1017540804c0e01ca102c0341c42c0c1440d1075000348480c3e49901a8881c1850207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 412897284 1250 412896034 412896041
    0xb0909060c09190e0703423b010501051b070b0307032c0a030807020111040f0513090816170a0e0a06020307110607031803080a18030203030a03 63
    0x30925000143c1009054104450346078070001000f200507144a02e042c50200141554040c40840c0c200c0c1ca03045040c10030a1002d0b034070b1104a051611103a0b40000c0c0a504901c02c0540560b20401c010500c00341d090703841300508802005003039019810070b01640021940d05481c803a0030b00038240020010712904140300780c8290141d142030303000303402c544400396070b400d0550041e8411650740002a4071060100304014054000341008498603040d48011245c441c500d956800c45d1003000f41c10450300b00d0116442030300070360111109440f1a003111740c6d038540b1a4140d0600b0f10301c0b071013814000d08100502858051580c420344844550000b82036240094807030480c030004201e0325003668030000c0c49000c030444158220003089540b489849003900719a0110401034200c0d003e07404141550410424cc10002d464046401804001102c0c031503101d19543c14101e601344542c5500d907009480404000c0180300e1030201600b003406a81d51800031980c0340c030781d800384070303216600c80250154003c0c04a04a002d00a41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 412898534 1250 412897284 412897297
    0x20106120f03031503060b10030e060a181205130b0c120306010e0604120c080f0303070f0c12020f0106330c120e03010b010c020f0f060d0c02010f0b0909060c 69
    0x640810001103154130082c441d1040d50040312000d580300c102074180e00300708a01360907a01140c01c00f00702c00c0442c221055100c040040c2009400c84d510010340c2c0e403544845442140594000512002c1451000006411980b110011848000e0080c1001480301001011106001d14160181040340da2091081c1e0880c0c00c042e15950601101c1540742c222034030380303501810040c039602e48081102c400c1070405501e030382040d420110154000e21494200c640000049030b401801a00d414a402c91813103004654081c410380004010b101c014031001c20041d8001212030b03074140103200802c07400d559451040564008000c660342842c01c0500c1d00c400f500a03030103840300350100508180042d00300c29542c40c80321802d914800400320f104455078015501b024411240083c0d02802c008800c4d01c12600090925002e010740d4911848902d2006100c603210402a902d1502496405111a0501c01c401074007034045112210311040c90440210720514280c4940d0303000d124190003500250311585035040e00343d032201 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 412899784 1250 412898534 412898537
    0x8061804030c0201110f0d03090b0610050421170a11300f0f0408070501030b0a0e04050a02101110020a140705070e0c0405090a0b060a110c0405070507030f020106120f03 74
    0x240031b0080005d009002204044126540004829640b41340019511202400c413034080e07070b00c642200d18080e810400711010f40b0b000403604481c216076a1218421109103010003044d11806141d03041030f900c00071026240aa049481e811540040c41032059642c43c1d0110410b1925203030a44000b5890400490066592030342c0806245804044110249140e124215044440000050404c030f07003601404010040c1c030b000d10701440390001c1c0c41c000861414940c092032200e0f004040c04030301000303010000c51500a902800c4000c1801d2005000f51860100164401c8103010344642d0b00300f01e240c2072007140c0d800040307a100d05100d5094280c01d5010303904400000c852500c01c1d160086a411181e5004038841c4801406e010b82d80e508020070300c025180003034012001c00707003442e11199556075410280c8000000f9894054001052190221b1400781e45400c602e8010f0325050500c2000703039004006281c500d009464944c401c160340e00d000c0342290310900c140302c120642d00300d030f5000082c0b4819292045600a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 412901034 1250 412899784 412899793
    0xf1209010516230f0d0f050309010b1e1008090a0b1308040b030106030c0507030909050a110408010b040b0d0b0c090d1a0106030e0a020a0e040c080d08061804030c020111 74
    0x707070b43e01d140c03824018584508450f04101c404000c10710400100c00304528038130203040004c14005010b82404842540c440a0000c088006807080c0c0d025400f512103160000d24203c8049181940c0341480790075680214050041d0041e00d400300c40c0204401802507941e00c0051008010a84902400381d170007400d214000b000c29200a0085000078025102810240c858240d0f60f515002c00602140c00b10390343c81c014400c1c10701c002c1c0082a00852500c040b50b030b5444001c1415903803603008800800304480d000c0c450010202d004240325805500181400b5401d8908100c014105010002d881c1c185810003000300311184001030b00511010080c001c40480589170b00c07060b8030241c0d140d03d07005000344200e030f0040c0c401c3c4004002c820360500130001004054006480071003a1600800d03004100c900600310300075100c10101e020400d0008a0074000d003000303420303140251040c080040011071300344c0300c4512640f600c4100c02031030100c100c0010b019592585880e09003035415801035403407480400750364405009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 412902284 1250 412901034 412901077
    0x130b0a0e0d12030b010801050603040b06150406050c070609300209150a05090c090f0a03020307030f0606080316060e0106210302011103060d02010c06060503030a050c0f12090105 78
    0x40e40341040d14080d00c2500103951082c14828000c0481c0c0e030011901d030410188000412240d200c10086036000740c1c00980c08402ca03500c5102103081041c01603040d050700d11001500082496000c405850300c42d195909036011b00d42c0d0707020122554803642c086c5030800e01c0701c004402d6581507081a484001c041c11090320341880c900340c000895102d400c48800b40104200d10184640340707841e402c5080905802c80b0b80004031f041580c002461030041c082418000e18280c0324403079141d580c0390810001164020200e401d41c50300e074a00150103200700041140c00c0d03400d00c04040f81c078190200a0300c1000c1c01000c0ca404c0070410039100e0b58041c0c24003203040c0700203550719940424417800300000c0005007418040810542c8801c2d10b07000742126070801031172201071024414059581e54000325140b205409107044941c0c0340e030340d040c0b920080c0403561081e03a051000203040500c1c0d5401001030006c08a0310700a494a10f100421551740380e00b40121582440c1104008080302980190054420b04088030f0401c80c20a9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 412903534 1250 412902284 412902289
    0x60a05070309120c03051c0e04111209030a021002121902160308062b08131d0414011509020d06120f050d11070e04060f05070320130b0a0e 61
    0x110b40e0a0184c0d44108200d000b40b0900c0001c011120000a0405031f40c482040d040704010a03204400c032256201d541c54003007201c0c200032028151950301c1710001c1640000c1c141804100d580750b10071000e280141c00f801d4419030071100c481c826543c10ba022075000d108503036601049034990b143e021410701d400035401d000100c01100032220401c4e40074425221070b0414144801045021416130344050310901ca11110000300c00c940e0700050440f07603842020b03a61204155074220b090010641c1107900f400d100c0d81c00d9920800c070014210f9000e14003503424580034661500071a0b09840c41070b50001102c1ca0302c0403003080342440c0c95000340500320304c03100c0004542d070311240c83d440c030700107405801e07107240c2c100900140600605004400c071100c100c0c14a00e0004240c0122161940c0172442400084a0000001414440e603a0030010050396043c4081205182111003e0300078124501e0300c1d0008440703042906800b0401d001291584501307800703801c6642d4901240301c80ca82e400644a0701c10020180c2680c03110341c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 412904784 1250 412903534 412903559
    0x708011511010e01060614040308180102030708070c050108010603060803031501020c0a0608060a05030a0b160e04050c03090609070f090902120102130e0906070e01050c1501080706080f06060a05070309 88
    0x640f40c410002ca0114500b0f00000c0076659501440d0f03881c6803081200b0400200301000300e070f8000f80001a8624031710382d040c0060713045020b88a805080c0e8031000502c030003042554480e240035a1400d0b204c105440c1d0721240308030b08847c1c09001c3c003080359001300003081d100c4408000e4a1901001481280c218021200101e0100da8907035001c070000c5200c17101800240e00c1c0c003605413800740000390700518040d40780e601c82c0000500007400e074160740d0b640440c0141b10703076100d0031a8820300f1038060418072080c10204184c0046500807100d00303003140503c0f0082a0026000b0511a08803450f01420b01d0089007401500742c003e0441c0881240d00207440050f240c2c44180030f00240941d00001141d00c0301c413a181c01e040f0002c890f0010008940c580000d000c01903c01e03040501944c4000082c03038180d84501802c1c041e6844c2c00c0362030f80c0803c4602071007000001c16600001722032060b1903035959000d40c5500d905000c02420842035a4050380260240015074000d0305c102d003e0710583d400b9103440040076950300c0124003403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 412906034 1250 412904784 412904801
    0x61c05071701050a0b03060c1602040612231c050c011515091a0c10060e0a0e060439030501090c14010c060e0309031006080f06070801151101 62
    0x1140c105003541c94100038070815500c00c5080c1c40c01e11505100000003526141c0c000c20080e010440461011010b00200e02c1c01e12044e03a02800409c9001e8444a42241d80c1500c0d900880e41b0001d10000403c414580c030003400c88200311000107100d4880c40c20b4104a03c440700d03c0c0700e0003c00405120701c200c0c1410034021044c2507001d004100c00102d090a0f411070000303031240703901c0d001e100e0070400402c90128103507903040d00e212085101c2501c0d8000101501d040c03401340c42c0c2441d040340c1400d101085441030440042d001d0004804100005070b403500e0055240d031340c01c480151102c1002c20751200401b4020b9003a43d25480d80c0d222010400d85502425428148650001c0e600c90b951072020808008111a00c00090040410b903e19550002d80000b04003040702c40e00200003a84640c0400c0480c4020015074400c400000c0c1541c804c0e804c101c102100810407846401c0140c441e1520301d4141ca1404103000b4040e000f250340380c000c1ba0b030030042001c000208010341c26041098144016540e1542841940031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 412907284 1250 412906034 412906049
    0x9031c050c0a0f11030318041a0409050606010e041a1005090d030e100503060907110c0a03031817060a0b180421080c04031506170601080114040b061c0507 68
    0x34858070f1402c01e15044000e803404a03019500c1001600344d100c050b045400311610b0f003224007103480c08901403034a002da59810f041c0c0e50040c0c14a80140d042050202c2ca0340c0c0f10308001e03a80e03a0f5021181304100f1066440000d40c0508580c5100c0d90b0030b030340c2e00300064111079078034443c100180b030f10040300041000c08602e40070079000a496200400f14501c0e144880c1d0040440c01d140071401d505000000921200c0e02503d100c040c0540b90343e10b1013800c3c1051080c600851401040d40d4601c95880c10083c0100030824290b00d5000028200418145902419409039110110040c0310503600e00c0c801c0c4008049110041d43e0013848062648114450969500d201d01c0c807800104060000d11800d010308101104107034010700001704108511400604240e5003100d8101501c030f254010000d103444010001754000b403001c19600c0e10f1040314400005480c604803011980200300740300c00c07070400000180003514000d20a0340302c2400b1618601d0a01c19020807440e0800d1544002200e60380c4072482d01c4c005610080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 412908534 1250 412907284 412907303
    0x30106082211090403030912030f06050619120f0204090b0f0111100c11031b2406060a020309090403031b11030706051b0c15070509031c050c0a 63
    0x7041e00750810018018001e01d88074110440d07000c0e80c880550031064054280189010000030302810f1007074103d11f52103900070460340821070000400030081c0c01c89104100045082c4403000546060041c12954000202054842c00c081610b00c02c85800c0310403818030722015181c004000c140d2109100410040022100003d07039065050103100c6000f01c160130480c14480e00c0c400117004140d0103d0750780b020075940c01c0c001503440e000c1d000c1616280c2c1e9010511460388004580012400c036000c001d0208003c8070003c4803100c12411061540c9003032038403008190912a1000f142003828600c0182c101c00c40c441c0113407810310b9640c3c0e0104030316400445060b03000075125204604005a186c00099040206240c180c80d00282e61200f9a600e211340071000b410584d98400141c1d000e40180301d80151101c803004600d91f00c00744000010707540d0255400003400c08910070007081015008400300c82e8039010242c003801c0c03403800000005400c0c1d0964240001170100400c65188121070038400c450f0024454010103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 412909784 1250 412908534 412908541
    0x60f200618100e15010e040c15030e0a080c061f03150e0a0f2303070b25081605030603190302010605042a030b0102100e150405010c030b06090d110402070803010608 72
    0x24400c5030103900007039004541b001400041030f4051002c00c29916000f80c100071441452800f100200700440b951445801000e03008000c100945004041c0a00c0c01c1044520b10745800c002c1c00c0d5480700c0111544000743c0c280600b0400224220601c00c4464400d050014200000810203801c04203480c0341104c40d400c280781001c0811a48c41e100c000d1810b80c12080a165405031403003117070341340315a9202030b082404c901700007072404c880182200c03241e004403001c201c17459910300c101404504081c0c880c91203400f07020400400842c41141541e01c64200213009120740308140300001550711440070150115500c509000c200c036110750140d22000540c0d1840210508001050540c42c0342252080004243c2802ca9102d42607900103000480c4a2903450002003400c5800c41a030f06d841d03040c040d001e20b40c4075507a04003c1400f9041d032005500c24050b031030031310404074810100102c51103500e143ca50f0180c001045140072a00c540e00308140c80e0b1010700010b24190b07440c0c03100140d94100742c2c00500029001c2d405c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 412911034 1250 412909784 412909813
    0x50603070f060c060209030f0304031b08060c0a030911030102160b010806010303083405041403060405060c0d021c1b030908180301021201060f200618100e 68
    0x9000040801c554a021a03504082c0014821000d140700640802d40200c0d01c000f15079400e1005a81d82d00d121421282c4e107a590340341c5921401c01b0b1100c0082518400103001440e040003040103845031b08a00748280c500b15a202c81034000b0404c050007914a000ba414040302140c03005d100402c1290180d40050315035080758900051000016080310900760000c000410000b0703005180e558104100a20381e4034500708100c540402d03840107450040c61000c019407100b1920341c002001700161101e580d488010080c00d40c05055075104140c5000344580c2c406400034505204610207000d0040b40e5200140c136142a055044201c030f013240580c92042540c41005104175414007500843d0610281018811165281c0300d02c2000d0103411103000c2154001c0350782c82c01321b5400307504072138034246000c0d00451196101c410082410a05000080105000300d940c5807440412043c11014040d90070f005080c00d540c1d5202644001e8040c55060900f81f20b40e048030000103a06002c1d020000c6c8030b650040440361541d0b0034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 412912284 1250 412911034 412911043
    0x30c060e03191806030e030c060c070614040210030e07030219090e0a0c0b0a030f090c05120c0310090309050a08010b01030f020a080a09020a0801020d0e0f0705010906110102130801050603 82
    0x48003030001e41240350700003244490f9071504440d010304000801c2c0030643c0c80e450030340c0308040b02c0000a010b41410440c0469022003d44034840c010041000320b885002103500510300166000b96029140d49050117145110742c2000701c0d610190f0b0140c80301d46a4a03030118003545001801c1c0d00310043c0e810000d00c00441d1503c2290581c9020300010701407107180ea1a03c14000e8154040c42040b10300000700303040c0d01c50080c0c01032500080103140410200440b03080c04c500c44280750081920800031041e90000c00c1c5000034131070052820040c0540340b02082c000346000203041c0003004605000400704001120740d200e00f04035008100c2d040010034144980c1000404070303090149980c003084d01c18404440300903805105140d01c41180c081c00609401c19000107480141243e0085020b90b0002504c90100000d90b0491001110143c2c101c40348038520035003090311000c1302e000d0700b070000e2007010302041030f01d00c07480d2040003502c2200001450201d424000d131608101541080060f07030344910600406080812 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 412913534 1250 412912284 412912327
    0x3041202010b06041a190c0203061b040b0903010906021926010303110a020307060c020f060c0a0b13120e01020c040c020601050402070c090c0e120c011b030c060e03 72
    0x300810558100398006011405580202200c241582c071000c0100c40c220801c42d60b41d00080044c0706a452080000103001c003520b860105d000e4000da402050885044040c1a070355888903143c001d08203428461007074016008417002c07a40c1592643d200d5000b00d40b1510080a1080105004000c0d4181d0840054981d881c2202c200083d40b1150990395200341580e50f00c030741900d5061a05854002c0c0151900e40f0f040e1810902031340c140146240060016000040c85000345e100b40c0f42c8901914131007040100340d000d8501d100f03903290000f100110005000214031b582c0f04440c0c000e14503030030382540c0344e9828011120b0303683c070085514244c44a00c03543c0c041004904690301185c2c180080340101c24000d4545030306104c3d29018540102c1e1400400080640190240c42c1e1410f0400c0a00e25551004001c4d036050b142c0700b0700800e10303030481c6070001c007000c41c00940301b0383c060b100d081d100f550111142101401c60708003541080145030718440020150b018101c2c50b00f074000001c1d0340300c080d0507808404000b2200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 412914784 1250 412913534 412913537
    0x24051923270f12031e01080f0f030301050d03080912040306020301062703140c060d0c0905030a12050708070614010503010506040c0c0803040203030708130317040e04141002070602030412 82
    0x307450182c192001940340d0580705009292610380c1c90f81030804421100241c4030f424442c2c1c0800020913003800c001075541c01e10f07032000d08403200014081030080d2203110a000d002c1e004910300f04003001107401040e074650005c012004031021201c03802e00c1c0c0324054000b40c004591540e0000010840c01e580a072861209100a003803c07a000390520340c80160590306031000400c3c04075030315064408040103000d4590300600103001e16079158007030b05010008103901d03484080410031801c4080f50350b090015510a095038040f6000110220004090310386812102084803207e000f002007000242c00c07800381d070001c04511541d0262550420040600392032004100c94000d07850541015509a400204800542c0c2c205c41402d959450360f001280c19031254800207810f21500151b60300741c01901e1210301d8100c81c02040500741c80d800d40724040c0181c1c89140304208682d05080c001c00c02207141e1442042e900400c060071180702220341000981a038111800907660b25502104010a01005219140003010b69 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 412916034 1250 412914784 412914793
    0x30e0f090a0b030f0102071b0b0304170d0f0e030d05070e0d02010c11060309060718030c061d030609030d0e010606050a0f05040e042405192327 63
    0x10100031036140d040007003540d034207191980c080c0798154605100c9030072886040c200039580c036840360174550010399080381440c54003400d000340010510098402d603805681c2c01000a462200199030711a00c0c2c1d000080031510f019624401c0040c0f01b1001e10500c00c2c040f180c1d030301458407220400d82c601c2c1183d07001041007041c4155003801807069502c0c02100c00c40f643e42402c10501e41025410011070819a440449802040c00024007104c4000018441d104002e103650b06a012a00c402c017141c4914124031000b41101c0c49010305020250040410305045043c1031440c0040036902e80020f4582101510b0710002c5070030001f040b00388103800340540404c0e00704010083c8a02d600d0b0103001040e40c49036035850020030088081c00c0130124480d0085034020902d01014000c141050300f4440550890b0b82d65072204100742d000c881800b04828007a042c0f0031401c420b40341780c0303501480441d40081c04604003140f1000f01230700901c400903c07414042500403100700b0070421000b00c1414082d55002c01d40300451045500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 412917284 1250 412916034 412916059
    0xa03210e01050a03110403140a12020c060301030f081306030203011503180f0c080a0b07080f0f0105090a1103010e061215060d0f05030d1b2109030e0913030e 69
    0x3042803c40394622110f01c0c0014035a0382c40f10b1509010302541e00010110030810900800e601000034002c441c0c0d03801510258000c4102c03c50a0343d440600022051700046c003440100045810f2200440145001310340c0a031411804010700d0003c158079810100100382e0110040c41b0324202801f4400580ca49410b0070004604144020440382807070600042060f8143d5000c00204100c042c03038200240074075021558a0388041c54500b43c00503040b200c4070b000441100004200300c1610f04024010740310301e4500c0c8070513400e00044c0305640301e0081c40d03403548944810b0240142e140e072000842c000c004081140005041c90010400b68800d40c101c0d010f51a4054400405030050000985401c001c00b29015a904005803500541c40d044068000d0300701e00010518100142098202c00c0950007142c01c07244060318070700c0c41a15400d502c0484950301202612010038070680b02d62250642e1402400e16100d1503d03c400014042c2804031854503d50041413000410190060942c0c0114542120507000910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 412918534 1250 412917284 412917287
    0xd09051507110f06040b0a03050601031a0909010213080c03070e04051c03090606090f0509010c050a0302180d05030714120a05090a03120c02030f06070215150a03210e01 74
    0x90000c081d000d502a40b0425203195955400044002c001800850301c89940f2202d00e076050300044031140110303043c04002100c1e90310a201c0c0c3c00c84507480540529484110300b0034000010781c010000340540d9401c114001380c05240e00405401490b55200420400030b19401307250918050313511000b4600b140d9400c0c44002240480c4180450035803010030307461001000d004038082d00d081d00014086c1c52500300003081101d400c0e004500240c04010040c00303203403210b0300c2070f9013242e081c00402c000007074091001403003280c4030341c0040455060303e81081d034204e0070100010311150402581124103610006e450300420244e07152128034031341c00c04098070800ba0314109402c1036106000040e410804005042480c5541d00c83c1c2d4180999000a80041d1420035010301401c028884801a0321900c10500105400b240001c0c525204540e00d501804120010310b120000304034000d0541d0000103d0581082c0c07050b1216100f54000f9401456040403010300c043d210403200da641c0814508014914082c90302c1c0f40d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 412919784 1250 412918534 412918537
    0x4020307050d0510090b37020a0c020a090504120e0307180e060c0d0f06050616050a1e020f010c020f0909030c010203150108010b12131a04050d090515 66
    0x114001c2d20b00c5040d40c5054038010782888000c0e4050f44089180640a805004050303000e28400d06a00c0c0070640720000f0306074020300c030720144000b0b00c1500c5201508229422529005082d4484460510000f2844e050340050409940f58001e075440300c3e079600070070084c46001a80080c007131f029400d03c60358001c86100403130f440301c0c4540240e0709c0c1c3c003211688205521081d5400b0362580b0700b03071b10181d40003418218a50381c0640e0040340e21406990601d48407066110b8039120310000c4030001804c980ca80341440200d1070520364111415141c070f009004054001c40c500707282e40c10401480c058a2030354000305104010090032840619410400005803410050715601e05250321200126a146142d030b485041d106d18503c6040e0080c516540040188203c0e03450060180100b18026244c18503140c1c0c95910512241c01140c110321b10f0459010003084000c2440001d284c1c0c2030303008050140c1740448a01c001041440c1c10b0b20211001e074070013001c2c1304410742e0160041000d40700458000c1e80c029440d1515880702d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 412921034 1250 412919784 412919789
    0xc030403030506060f07030f0e10050301051002011b030c17010305030d0f020d09080903071502100c020a020d0311100b10180f0e040c050a0302060f09130203010b09150304020307 78
    0x9055842c07000c600a030b5680001d8074001d0070550f04407680c4404a20740248101e40044032240483d054010000d1a0302c0c0c43e1040c4e40d1180015170303a69003581e180004100409103c52410070a5550703c2050025012940c5040039044240d43c03070214204c48070180c020803c01582041222014019005000085020084607a02100fa0324046074001c620110100244104503a89144a00e014010420800304502901010344214169204540d440e484000d000541d02070754401604181d0b0003c048100c0c940c0003c046d15494030486850720840d50119120020f10070055001c0755505000b001c0003e010403d20b0810b05916900b8081922408045003443e4120b50b0080c0607c14001d407541503460510034410000c140b4128010002c5613255252005042c1c2520700ba5054180000c002c076250500300306680441e503020b40664a801c0c0e000011b0030454021214181c0c3c01060742c44500000140d41c0091400b074111207a0311503031460802c04100d084008800e0808039240140100805690089085c004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 412922284 1250 412921034 412921037
    0xc03031e010b16060203071106100801050a02121314010213050f010e060a11010f0c110f060906040b0a1805071701050103080d0c0c05011e0c1b03030e0304030f05060912030c030403 79
    0x202d0786c47d8031000b030b5280500843d00f03a82c548036071020412010600d0302c0c101e04903500304c00208590b03207501201c1400c0e8800d20070080e480015810100d03030321101c1d030010142d510b805034042da22154100444a030030fa0b40110a0114a8102400240518908616500e032103c00900b03000e80800e0b941c01c0440c0c0c45d0301940c07218506001ea920322401c032504003900052042c0c0040001001a54041c0300e0241c40030072011807505152241c2460110030400c00102207000c0d07800c80001748440d80e41c40c1e50301041200c1c01170003100c4440d01c0305901000c8a2181d801421602e1003007014040960800d05a40c207c0141003500d01000d078184001000402c0380403040700d006102e810700102d40c00800080a80715680c445500600075031901142002800244414410340b0040c00d27014000d809503074504071f03019464598038076006d0b00208008400070b4000e52201c3c41d0940c1c844140c03801d041d641d80b41c59011000e1810290b50341d800c108104014a54140100c07100c040002d4031507402c40c24000703250755603808000c10090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 412923534 1250 412922284 412922287
    0x5041401051003060b03090106030309120b0c0d141801150506030c2b0f0506010302190f030b03030a09030506090d09120606030215090114030606090d080c03031e010b160602 76
    0x2081e110790095801782807a01390b50341c4c1d01d09244500c5030082c40244420b50020b62800408100c0c03031604400221425080300c0685480e0306ca9246040c407a52101c42c410302c103d0307558401d5820344400079240c14071901c04414200c0150f1401d2104509607281c90111600c4240c0f502c205202c10b0769501c0a9903009407103400003585402e6209000c44a50203080b6002c3c4001e4034403c1c0ca407070707611100d410401c607a400c0003800f40450f444010054081e0700070608189021a541e8407035001c154412004c1d02e0800200d40350201321410100d0201c4c1c10f60303205c0040200020a00d00c0c0c20300034401e0170800c00340c010050800030200350310030750002089108c0314050b041d8061881e0401d0414014981c00801c069600102001d600d05480c2c6c0b40300455501c94400c003404a40441b60002c00e107040181075a128071406000710345418101c40c00c02c50030440f540320450302d2040a1051440300602040a144100440d100743c000102440490003840c010581c02050b48100030000301c401c3e00038560740080070303660120016 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 412924784 1250 412923534 412923559
    0x30e210702030f1f14060108150a0f170105090c1513080706050c0c0415120201120c2309030d1b02030a151107050303070c021c03030b0108010504140105 67
    0x2800c0204000f840951403080410740e40321942d036900e0803c004004030904100c2c84011043d1505401c00485100b4041005000051146413124091071140d06004207082c00142d00c807403030b100b0b0456071504905101250384031200a00c0000344034080d0403508000041801100942c0000d0380030303114040140243c4008100488514152903612001d0201d480640c5c1c805910b0307010091441c1c1040030a03c4180c401e00000103400d09080c8030351602a1400c402030b4580328185460040803110111007241008104032076819100070070f208607020003e8654585110361030056030602000c00c100b083e00c1d21300c0c01c10000d00c14290307000209602e00c0d01f01403c0403040078030342c4400c9000c944010b010294060040c00c80b468100800541d15061b000c08580d001c01c2a8682c1c2e205202e00e5010323007a40106250b2040011410150003000e450414070701c002c2c04503454a4002e20b00128490008400300c0200e610b440f0400302039038000810038094501070b20100241000704800d02c1b41601c06108040c0070b0b01d04120702 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 412926034 1250 412924784 412924789
    0x807110c060d36061d1e03040e041a090f03030412091203110d03110403060209030309120105040204050601080403021b060f0a181a04140a0f03050a03030e210702 71
    0x70080484500c07050521401010000e642203441404903200d07842c2c0607490402011079500174a0b4012043c000f810040812003003000d28840c0340407404542e12090100240d10001014100e209500c501c18200001e04501044100050080d103080d42030740000440200c0002e00005480c1e126801606000d555903035014280d0701c1d001907800100002c5e03040009881455000b51644a1a817040011a41e8900d2820001c80807580b18190b00c4840c0c1c4400c000820100d0804d4000d4041c40320000c0680b40381c510640700007850800301c4c0aa01c8440d075114802c000330761401748500c0303502070750a0810f12518038050743c000b521000000421071010b100c00c0c9641c07819840e040c0680d1668282c0d56492603442c0003100b4043c0009001048481207011102c10210703402d10f050140a405003021603406080506258541d080d003249007000070b400c04900207000a41c4d1603000043e9000350301031360261030003d02a007401815616010702000055102144403200c00d105441800309a00580466075100e00703c6100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 412927284 1250 412926034 412926071
    0x2c040e0c061215041b120e030405040f06050307032603010e010e0a1b02030c281412130311180a0b040b10080f070212090108150d030807110c060d 64
    0x1006500186405551300c501e0141d825000c0c5d401c246a120540055140c1c0c2e841c106030380d01d685010102e40c005010400190400340c01560061400003800f00d034080d01e4a01280c9046c185a000f95803024418000719101c0144c6005440c2406005004915541c108611620004030622410300962051400030b00c10418070b900c030b5007031600b100480003a118040c007402580e980200481d14214021284a00d8421007585064420341040c1050603617045065169200b110745145402c45041c0a070b0a0042075000482009140380000d21b1004002e0b03500f1400d080682000d00400c16000e1080100035803035117840c2c8a409075100242c00c0000c614000306070085005484250031640e042101025025151500142254425001c0c0b04107070b00c2941d00d44004a03620745e60a440c4004602003081380d00c2d05075114003c400c0d4080e00702d0080c02c0100a21802040050403e0766013a40015504818410300c6a030182c00b80099030b01e190028461aa9500001101072090801008540390740c1c0ca0002951041100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 412928534 1250 412927284 412927321
    0x31e090d0210030e070f051207120b060d0c0b1804050702070e0c0d0501091b14041509030b040c210512090f0909011a0607030815012c040e0c0612 64
    0x1c4c10340791821b580710140c0348001d809008103445040c201d0552074004000051038011103aa182d0b119098008544503c20140c0028103800d411048040c182c0020889224040e4003c01c40d100c5440e80e03a2055041130210f0b46000321080d44a03c0c102130510403940e40c001341c11000d6030412510001280c440300750301e5072a0b200321031090403424180b60001901d0206139001d0003802c12160480c1c20090744040c0100c9001c220800c550303d10074810711083c0300925006203650700203030941c03d0880c5015280d0721401c4032079004a50032225000b00c0c00d0306114410803a190301d09100e05070b04a4546440a640d5015168180c07a40440c01602000c03507408240d40d81c11800c008199001783c03045015003001d10805000c3d01220004e0700489000c0808040740d4204101101c492a4045da1010510f8440d00000300d40c80d160030700120b04004400c0c1c7e0448410b411820341c0340000060455503e002442c407424070064540994045000350460524100c0d50b4885608491095400418044507903030b650004004080002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 412929784 1250 412928534 412928561
    0x30503060922030504050a050105030c030f07231902070510050309010603020a08300409051f062006010b0901080c0418051806010609090218030f031e090d021003 71
    0x760002403c3c990088010001c0c1c3c0c801f80c403071000c03c1e9143c800658183c072003139602c1c0c00082402c03c0080c2c440d0342d0809400e50440c00e01c2c60500400f5040c1c038070b1006000c0a400c10340c481c008000074140300c482e0070305081003c0c1c104a400544030703142c0b034030340002c91690f1012084014000d0000016640c1c0d082940040090355008081118260700d400c0e600743d40c4d424008540a004542a40c0c4c10b504000b501050440f14040f0a807107840c044c14009000043c1c0741c042c2000048030743c0016952f481c0f284208044000e480d19943e0707001c1c102c410a0840c0300041d2000602c48040c2c01580c01400340841803400c4880307609007802e003550340c0d440d5042107a15501c101d0703000700c80080000d9012115071400b90070150050702200c03107520b60ba12104c46130544402c0280301c0c1902007100e002e803c0044000c04e40150200b102c544040400c5c22200001203410401d0400c814171703140d08002035815051071080352034140d8030b07107006425040417640c0f070104071203841d01c03900a8030400750416a9100580309410050751460381 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 412931034 1250 412929784 412929841
    0x40b0415080610090203010b090f010c1a06010210140a2a031a060901020601060f030b0409150507050c0a151d0105070905010c080403060e010e0d18060c0305030609 72
    0x103500e4440c1c2c40b404169038051200c0f40c89080000e01890900039681030320f4030700f80d1261402070810704129403403002000b014180606404a000400c20400c0c43e41d2800f24256492110381ca425800241400030404c10707001254582102e182c1e0349400c805803640d204151100000f0704241c28910b8509110042c0010700014030444041940150316421140301a01108500103880300f600c01008194010f050b6134500503409180104030880c42814001e080740c80506001803052130820200b0140c0c0d40c00642552200708034450303200080707298410355901c01420714005041111714005e0719203d89042134090411100007290140e4105698003886500e0072904440e24120311040a443c060401219500d01055000c000041d40354003405542504079404401c0a24007419030f900e000041c6418562800a50740e10f00807800c01070400c000b81c0708800342a4030307891440340c2003a00c59066002d82e81c1041081006003016140040e40103010360f904440308072404500344c1c5d6074004192000c42c40c680b20388d58640301b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 412932284 1250 412931034 412931039
    0x30d0201020a1d09070311090301020a03021911030301031101120c02010902091602031b0c0402030c03040b060301090c270c0e01080f01060207210203120405040f0b0f040b0415 77
    0x10150300500c10506640c440c40741007030303480b007800f0300443c1d4114500da0080c0724000058041c601c03a6000c02281240c0c010f181b0b040c440b44001217404c9030003005499020035400140d4440f66040400710003c1e6203d10320b48844040b0820600070340f41d00042c0301c001c080d00100c107904c041c146c0c0180c4c02c1950b15004800200042804820024040c006501080e4094441817000c29910307801e60308001ea0441603500118648150702c021508200c40251240c80301e03004a801090041d42e4500046004000412155072039040508082000c0d02000d03042d5841380c0c1c50724280c600000c1c120784010742125040b08420036100a50f00c20f0401c205140c080741c5064500c0d0000b003103841504102c000315501d60a90310110709980e00c0030700b82407201c420300406025902c050380800c500c0501200d00e00310541a00c07041048a10319902282c0f9080c18501c80f0b0050440102e810b1015080c076105002c1090311a840030302201e81e41e54042031428048542060045484242c55076060300c0d1074021b00100f02e000401c665030a503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 412933534 1250 412932284 412932287
    0x203040911030f090a020102071a040503100506011b021e13050a060611150103080717031003171306030218030a06140f16050d060b03270703030801120201020309030d 73
    0x20b00864408819030302e001c01060900600241e040425941a0000c0a100e800e01010b040350001c0700001740458502003001040740c0d1024019550980c9514401241340d0501c00000352803a03101a00c1a076040402408034409682d80d0446120544800c0700d410000e54000d90108034104104588020110b04040c02c1c000091050750101c42281e01a6940c03140143c1e8820340f00743c54500c0c014100d248200c15100500c00b10f003601000f001c42611901107100c2140c00b20484018940045500d41409040042e08101348000c54500c02d560191480f0303001c0c9407150007009000e011b00700d40a01401c0690125140c403816030040c2103d140110010304440501310149407a2000d8100c0b444400b0004041c2d030041400060f8203a0312074061000102507940044901400300c805811145081035899103815000840704a000001c42c000c5403000560358003200c0343c00b801d84c0c00b18071524100d0002d84c032989040000c80c0d401104581511816035050302c0342c0c0e86500040f855800340e0b403c6140e250090101104455 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 412934784 1250 412933534 412933537
    0x50f06400212060901050a0f0e090f0601060201060f06080405031911070b0304060e010c1b061506020f4b010c080f070c020d020405040f081309060801060f03080a0203040911 76
    0x400d0104c8403650141e88034414444030001512445a40c580c4044003881440c4c1c0503003c8a40c0900c1c405d045441e800c81407202103151003001c0c1e01c518090b035034405080c80007089419a1402030010707411f0054540c1025078946550344a40c0b044000d60811501004590600c20038071045141594821100440e480d10340e1a041d9034011780341102c14501c0c005803141d80312418000d80401c009651140106148000032200084000b14011a0559582e0226002000583c1a11800b826907a4002c080c0b0406540d8210b1412311043c40014894480349480005129a0f021028500b00d405040c0740c011203c05005080d12103c1d81e114094a509000c04242c82540c0600c24500c102c6590606401a0722144003d4415000400010b5000f00044001d000907003007a412403038000b48100c00b12805120203450f05e102d03039001542045513180480340200880c00b100c2c01b4950203010900002c102c07191a1013510003c801c1d0380c1c40010a031810105001c40c490b03000703005a5008155882d400d014030600c0b0f14000341c49 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 412936034 1250 412934784 412934791
    0x30e0102070803130f21120c050706030605032a130f0c0e0a06030c0c0201140c120c160b0403030305100909230a02210a0f0501050f06400212 62
    0x3154484880003803050013103141c604001884030034010b0906c4003a201d2107000801007a500c0300b07201526400b10000790341040148020402d03541c0000b0700301d0a207020903003003422209504041c90084000141e400c0408203410407003420448440b00c02181200c0101c002c1c001800d07480c0c008510704000102200e4009417840c00703c0d0800c9601030842610307030005070704464002e118000001c2d0f1105880300194003440e00e0710349855601510609000701140034520b02040032031103203522040825000c05c1c800301007111050303401031a1010380140b41407031100c0e00c49000e0340c40040e04054a46020541101150321108050303c514002800690780e24203007080e011085640c00c400d01e00310750340001d40006000c5854126aa4010b0009012100107207155001566402d0140c0f0580611012040010422004544090320500022442d46040c40c0c802040e60030060005005414822a8001005a103203050651764584114800b50000548054102c60080030b4140800b0344000b502c1c0742d000c2440d0400d51310 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 412937284 1250 412936034 412936049
    0x62214090601061116050d02040906020d1d0a0b0f040201110607050408071a070311070801021303200102060a051b040608090607051804020c1015060906030b0d030e010207080313 78
    0x107041d190130070304503a034820300d4043c0045180b0410782800140340154007080001d000a0003c20700420341d803210000c0b45c0c0104040350400b50340341c407d2407450340310541255000003508094102c8420076100c011002500901c821000005071001404581c007139202c4401e1040d440c02195000d10b4544006441c590090180e07032050310954a000031030302240a0036031034a021020400d401d03e01242d03419141644a049040e180c5c1c001c82c000892580c00900c05040b41100c03410450f0315882c59414038542c2c036a0348044041030203400400503400c0341d8000072180d8100e00c9100d00000c0786d90317489101c403d0500d80315075143c14a0313000150001d074150f03001003914000d8800b6030544415881e01c0d40e068445110b114402c4200203034058008089152503800340001c0610101034852120ac41d48000003103c40904a40c2c1c030b07030344071500241325565204c20640054901e604081200c6003500e40000c0801e04152402420403800401e000043d03482804800c00a109460449480c0c40c441404425070310503d006444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 412938534 1250 412937284 412937297
    0x80307050f010c0905130f0203150a05090603030a050c0304030206040b36060c28050d030501230d020d060f0b0105040b0a08072604110906221409060106 67
    0x448801c018411440300040d41c3d200e03441040d103083c1c148203d00d848103080704103140e40e900c40142c24502900046229407400071040140d440c2500070400c60001580150b0b002d070361070100304943c91300e0000885506511500b006510340410340302162441c4956000203402003004100080e014403000054034440386074050110f58402c02c030782c0081c0c2c42070056414031799101220b04103c400d4145440146100300c0800195500c100c6e409201041c0511120301200706803118408120a00a080c400e208101010786000c0c0440d500d011100385008421181051210717030741c0481c01d4540d94030045800542907000d04140c1c21128036040c808010082c0104554041d4244040c040701036121388100d42c103540740e202096041035046001201c0a20b8020041002c0c80342103000c034551503880203001500003070f050300c0d0a0580e260501c1d100101c0d180c0d030300d00140940da054081c81501e80c2d035100180c1202d2004075851448800003900007000d010418100c0b68251032060a00113010070104015058030300c60703118103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 412939784 1250 412938534 412938553
    0x1101030f150b0913110d050c120109020a1b06052a0f0702031204031209171510090908180315040b040516090e0c0102121c020c0708030705 61
    0x40c8103460220601011404a040d400d001140468010f0080d82d08060820302e0702d0504110108200c8102a011052030200810902040e043c14026103600c40ca000e10254100784803016210525641800391b03141c02c84c3c0100700707080401c0c17241030701e240a4156034009140304e464500340350f0010701e42615040ca10246400c1d540f083e00402c1141c001303e40f60b401d20000e03e0404121108032043e04030381c008990600400020035000c441c601c0203007001e98000c0150480705004840c01420750b05041c1d0008070484800e10ba0030003502800700d03c07200100c80d210004000d540c1da645a101d0044100c0d0455542c1501d001c004a00380305919000d800b00c0121044400d802d0302007a001c0546d285580425940b018801c240042d001940c1e4004080d00180b040c000c43d012420b8441012114a00300d030004996070303940b802e8070b030420001040702aa1b01c1c0001c0c005000c55540c0c00083d86840d2141e4188440b44448600f0f0900040002c1c0d812200d100c0d48140554607030b0303900c85601544039403000384256454450040310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 412941034 1250 412939784 412939811
    0x170a0f091202061e0c0d0905010905090c0a09050405240618150c0118050118020321070f03090e01090209090109050903091e18040503030a05060a030f110103 69
    0x403041034949010070303414204619402c01120380e0080703c0519080f8510302580503080f00e80c2015282043c0040040c02d0002101a40240500074941c1f0950400441050070071041d160100e003903070040030755580d20355030b43c02810701a10707034800e40d500590300070745017008004490030070030116802a03003210650100c012a0701300b006001d000d040c00644810703040500658007031603d8481d0411990940060300d04106011082d00d085a1b200f03070064844182146e480f4080140030f01c18801c100140c105841181c807100d401090741d6056031381d0200c100d6010130104881400050090711081540030000103044909131a0041c03603403100e0f109a0324540380000001c0341e02e200e50f0003614905180600107513a560704c0c04005401401002c3d00412460200704401142c50712600205a896801c42c00701d01201c10010081c0f1003d00714021140206500da20140400140044106ea03080b00305c0c0000070400340c4684002810001446e44006e10500c8000c0340c0c5800c01c030750300616001040090703d0410181c03107030081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 412942284 1250 412941034 412941047
    0x11010209030d030c270f05010314041b03050316260a030902010903060e061605070309050d0311030414040f0207050c3a05010c030204080d050309010207170a0f 70
    0x2a00d5505030011000a140d0383e01c40d42c000440f400e00340c54114000840c25212400c0841040c1038162410103511040c03040740801c1c460040107202c2803a040201500d810700c0c1c2000300d80040d00040c044c50321202e03609040078000340c030a0301860b04682680e591786041c00d43c4d9030000a0644003140c95411480d01d0800748807500c1c00c0094080d45844106140c1041c901c401c800501c94100100d0503c90300c0e030004000301d00703544503004100344204020170581c100307000f44d07900c4100869942410031408100680009500006000c1100e005892041d81d011031442c00f41c5400c58010712110961102140002d007001c11840b02081485040d50f080090302c2080159400382c0c491400090520342c0849000d5009003400d175001240342013800c881d200b02295440400b400e281491200c024209942441d02050182c284949015240242011860585003030402030701c6109840400d4107004001c400180ba25000303404968074250701c081003160221820307a038035582d508058407400000d444901011004d82c05400c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 412943534 1250 412942284 412942297
    0xc0b150603010902250303090303061a070611041a12090d080c0a020f07060c03090b19050d020d0f0c0807030606140c07050904111305070c030804060b09090d110102 72
    0x1031205155a00300b8814901960004000b0f0142d10040786221041064003150b80c44001d00c00d075008601e0035110300b401407e907401a0000e14000030403440c20300c060700c2808101e5011950264020500c01407280400b809030140e070b400707082c81d100ca448403260080c0b4414020104103252880445041e160315089540c0d07180c0180f03a400c0400d28100208605041c1d5501810324070380144119203515900740c19403400e168460780040045001d502c602000c05800c480c031100500642c01c903180c200300e000c2e44101d011240b0b09c0e00d180c09018000035410207000d940d070110b9507001c1c9118805e000408071505540c0041081301c200100044400c0041919144240100e100b00c80d02c41d503a100c022450110120b03026442032041d20810300c51040005035949885d40694800d03400307000c881c00121001070030f026102c100c0ca441414841c3c684410000b20f0fa401000381c070281a05450900300641e910f02d4000c004211400c42c40364090140c0c1e0820a40e042c0c000b501c612140e6503541d8040506042c078080d2400d074011403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 412944784 1250 412943534 412943539
    0x30118060501050f030a0905120d0614060904090c030f0b0a0608010e100c0903021809010b060c10110d02031501110c090f04020105040b030709030303140919020f100c0b15 75
    0x4001d40030700613154a02442d04504d0a24001a007003c2c00d9440717a103000c00f240000c0d1a0007002140e003000040a038403540c8000d0280700d4100d190b402207540086c00c01c2c410300310640e210710fa4030701c00c0206110307030681ca02c0040e55202c4800e44040605040900303203020101c1d141003d950504d04003250b00030060241c004040c186c0b200030010760b0510034485000d021201002c2007003001d00b42c000005a59800384c0c82440801100920f030305820f00c0c6440c1400c0da140000c0281c003d4070b040185810544001401e01400c1305105000520341d048010041050310807081c52810705400441440240780c40d1900d80218144240c880044450302900215200c0300c0046817154030441070400101480b06085400c0e5106c4d10524099103803540320200d4800030b0b00161098000110068414020141c041c45154000e01501d854240e41e8a49585515036404140d05807804030340f510300c0c0c900210b440300c1ca5241812100100075000e07000d903440c002043c0c00c1c10403901380d40403022a070103d04030120a290b05089091701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 412946034 1250 412944784 412944787
    0x902030d090b03040609081e0c0c100522030602040306020c06011a0a0c050109020d140c060715020a030608012d090203120304030c0209010e040302010c02060f0a0f2003011806050105 80
    0x145d40358032000301801541030351881d20030440415185030210700001d43c1c1035400d00607916140000100c5140020121566000384411707001c04664a81010139607400c1c4000c0400380036000b40c9204030051290555000911007400131602004102980d000b800b1050000c40c1180d0721030780d031100c4040300a485180c004490380002c10079801142e11540c81d44084601550000c100310903581e0110b20048402e040079500030758075901c4c4418026040c0329000c2c0c031380001c444a0341403c0203070704c594040e01940b994050a03198002800d2618034000c0c0c1200004040301c4008100c0200d00f120f2078200701c2010040280c41e4244d0305286c11100e001071040f4210b10340c0146c01444003003100340c8111003e910240c81541444444511400181d484218184c040c1c0450660304586092915019003512100c52442c070541d004203040200c10b0501c94404d544c010b410920204a1090480c542001080c1d22019230050a41440454810882d210b00441c1224102e00049000f0f0742028142c1045402d64010315002032340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 412947284 1250 412946034 412946041
    0x3010f031b0501120f24050108010902091806030a0c06112808071401050109230f0621190309121109060f120a060c0c0507050415051002010902030d090b03 68
    0x3060f4440409820045c2e80082c140d405075a03501c90910300d800e0030b24445050b03054148050350740321044500400342200150b007004003010008d4403042d0b101030803001d00781403000060031300d5404002a10311160020910303240d49803501d200a144291b541641c00c103e1241907002411840640d00c2c8144100c9180156064800c05a80380240781e4072198080c0d422a2070301d4102c840c0003c0a106403402441ca032180000d403014000c11884e03c40b040f070841410422080030801c09105001c0013100c0d030000d0704650071882808100e41c0c25003c082c3c0003c11101e0340c8200130458040400191620b41664003948603104a56900e0300d1072200c0c0300c076002c0c3c020800c0040ba000f01040c0e080800e500c64109030003c0140f40000188804a2100200c00320342e10566403104415400b4000c1a201c1c0140f003c2051811380160b041586801d5039507025031203800d00031030340d4250842d0184058012480902030040c9642c06d00102d901001b070181101c0c13035003a07101e80203040369201c4e01401280f1103004c07034011215403800c1d40d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 412948534 1250 412947284 412947317
    0xc02060a0c0c15080f0c0c0718061202030309130f020408070503070503010203190c0309151d0106081e0f070602030a0909020a09050f0102010b0303031806010b030609240603010f031b0501 82
    0x2c3d4050316032100a00180287c1181403410302c0440e000d8002c805552044d1240600b12030103503841a4000308488812290708070150b200442100c00c14401612039096480b00f150b00030000308800984031400d03601c0800c010136000070200f448012182c04500316020b03c2e8a0710100b50807484140c4120f0030500817540d500e280f61348160080003605c2100e00b40011074901b2606c03844050704030040301420341c0c0e58940741c00c200440400d101403110641070000304240c50804901a5403030794951003030429204c01408460100c070f41000f0b0400340312208c82c11f0340d503d0b036070f5108060743c2c0350402000740000c5280500041010005842690b03401c180d40d640c0c41c8100c81c134101c18403040c408032680141c115521998544403075141080290701800c00c100317100d00c001101120b000d04011042e000340c840084200284415583e44840c4a0307005452400d54002d01000c4103c09103044800241407508404044000141e0100c210b10300c1c0203c030b0145a0743d500c00284003c00f01c000d40040d0280901040d00c04c1c02498458 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 412949640 1106 412948534 412948561
    0xb042a03051b0a0b040e041e1208060d05070602060126030a0806030f15040b010501080601090303031509050a060504060e100302100c02060a0c0c1508 66
    0x140c215941d040c0c44890508031070302c00c842e0315014880155070f070000401c0101003079407030781c0d540b00d60341d46000180e200c0854059400042c1c21605900000000319110100c542c49142c5440d542c0c404d0b40161a81e42c0046e251542001e64046050b00040c003c020361030141400b42c0081c0711540c07400b210194400f4001d0301e1424140c101c0b55160340b030381800205031a02101c89041640181d038a54010a29284c0d4008034400c0b107100703208000071501c50100c40d440c0128000d04100007141e89400040d80d078100300303440c802c2c00511240c100b000803902c07a50060314840301443c03581300041d581c0c0d02820191042903d040c0055565004108001d20303040c42640d00500b4505010350861a000701141540c00d0a0310003c1d0150265860003104148110f4030b150340301d0750003440e007526882080b0006110910104088034000c040640c04651605590200d8205071019a124522552910102d5005 = true := by decide +kernel

theorem cover : BRFrame.Cov 412769784 412949640 := by
  have h0 := BRFrame.cov_init 412769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 412769784 ≤ n) (h2 : n < 412949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
