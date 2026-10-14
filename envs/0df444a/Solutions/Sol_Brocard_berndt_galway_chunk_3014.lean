-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:32.07197+00:00
-- url     : https://prove2.me/submissions/2a80c947-9619-4ae9-be25-5fe30984643e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 541906474 ≤ n < 542086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 541907724 1250 541906474 541906513
    0x90108010e1c110d0c1b06050d151a03090f06010b2b0c0e10020703050c04050417040e0406060504020903120a0201152303160e13080a030510090605030303041b050909 73
    0x1c1c05149066040c0100700c7c0a41150840700c0c1d002c03410380001508198418a4991a2001c0d041843e000208101d8140c049107200c1c000e601030440101241c034210798180d1925600c03d02400341c800c4104040c052000080c50381446481c100b555882c5003200d2050501703255080340da5046090000401d00340e032603603882c00c2c00030f850301c01c007002381c03024102003405c3d0b480d43c40e5600000c0360541d010382c0d5164002018404e91215681040a0301400c1d07558035a51105121a01d250540d000c0d5002c03450614009010700d441d10031101c0d03c1e54003401420301c0840405140d00d0580100794444199520303241c0c09054030350791f4080351015140a020203c45002c200b00100791015001c4074090003607000b580740b000d08141e4112a58119150041d0607a030715561270300d0001030700b50300e4000282284000700e80c0040040d01504450b1003010012910140d01c1da5510408050b82c2aa10490340c0541040000c1408146550a8100440951055005180d644902007800160100c1d2000301c1a0407418604858420503c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 541908974 1250 541907724 541907753
    0x9060902040812091807050705010b0f091b1c06090e03040303120c032003090f160605090d020a12060c0e0a0603020304050a0c0f05090108010e1c110d0c 67
    0x481181494284044203960f030300c034030070014550200480d040700240d070f90091040c000f046449036203485041405018001c2d4104903002c445e15400c10071720105500300304102000341d4500418140147e1651803030940d42421100005c14000400c0145800941d210044000c2400e035026000454602d44003c0200b01c504458115006800c02c010800c00309511007401c0c000352889420000703144030034441c1503004048909101400f040b0841d07210b4000d515007000340d44140e4900041d034161500eaa4062901e074070720020800030042950b00c041c0511845840688a40000500300482c1c0c5107064000500f00038255000c40f40080c41e00070408200806805003c000d06481d007030031010b008100002580d8140e0038004c02080542c0440050240701040280e42892900030300c0901c106925a81441610f080c28001c082c0200c2420000084100c030501c2000b00070301040001e8002100403100070b1068401c802c0e8410100004580c0d1108102030902c0203141c103000355141c00201404c1454803003080300003030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 541910224 1250 541908974 541908989
    0xe061009060b042d05030a03120e010605030607030e0a080309061806090a0212010213030b09070b0f0a0807090b0d02130605120705030a0f1a01020c030d09051c080a0206010906 77
    0x910041140b2000396021045548000e104000003d1058100c190b00184c07951049515100c0c0c04102d500f415003021140030807890144d02881005e107a01040381c01d03220301e07202d2107405a01100001e40322030304c00e5003c000c410520302e007681c0c01d003505522203449a0704181c80c00385164104a0502c08004a0468001c1003450150302400c07036407401f640c10b15114080c1d41e4000e0b000d070003036001d0110f441d1400e50482d190f400e140d1003000360b221388030b0a200920a40885418410b03104008021071070740302d208203888a00040202c001d10b001d0708000200d130030300c80103403507502071080c1200c002c00c1550644025201c001010080103868aa5070307080c46c0c08a250310707480b12007408020440300710030307035000d194155001403a03040c801e40c2e07511840303a58001000003101c1112610300e030002908103004501312540280000360300b1207899802070300405480c0d41c1164024400b09150304d0b020001c2e400c02981d2000d4002a51460a500080a84230243c10f603005085110058200800501c0080424420b11000d0184c1c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 541911474 1250 541910224 541910227
    0x1205061f06020c012a031706040213140d0b040302010902041503080a0818030a1d09060d061a06041d070f020c0409171c0609020a08060111010e061009060b 68
    0x90020203920750800c03c0d5450304004036003200491160b81e403004481120003030041c48521003254100204541c20380c1e085d4111026030f0101040c0c5602e840c1c000d07940c031062012034001c3c1c2c075450b22030054001125400c03019005494850404045013100c00158447e90181e0008242d0070314a02c108000c0700c0000c808032145200785601400481e000f0000d0310464515420308070055220504541c50102484034019554400000c05251042e80705d83c01c0305022540d0b11010ba402482030080086043c0110740b6950404c804120700c80c0852416080303d03981e5480000712504110b6048013094003607000b6000705490401840045010700b010a00c0306602ca01180740c0a6554240b440c0002d49440155100e18452503c1d03a062038180480003040d44900000440040d6903982c030824150080085842c3e00804140b40c0000040c4000f000c0c000c8420140159450300d80598400c8015514a2903001d40740800d59a80d2206001540e01001014003a1802102c0e500b07615285c0045113041d01d5140d04100c00c800c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 541912724 1250 541911474 541911479
    0x4081308010618021e0d0c020715140f0d1409190209071d0901090501060f020307081911070b091018050f18012c04030c02040b0a1205061f 61
    0x1202c085103240c00319a01005640c815503601c030140d103040300400c5c060b0b104600095481c005a003903440a0b0440c0f0b800d80079140c155942d6904071000c1102440d114000c1a001080d08211504010040900b2024654114108000c0d070040c1c0781118401000b004039a0848010b21180c0b500c1003064400b103001002c0b2000110040b5404100f0001d0080d013040e0038407d03240c0484059985098526403401c00242400f0001c0d039442c0300240141c0001e106035000f03c1e1040d03841508603407002c022100c0e4180c00011840c0303050401c0d01201582c00f602e40d00c003000c00c031040810204c0c0d01018058200200680041c1c982c0300e100c7c0100b04a002002151500f0902c02e410b80903242143c0c55060420071103404031015440c0028980104c1d1180c0400c0881c66142c0840200100d664045011301c00400d0000751401200705084e8844524181c1084c0c4010740071841c1c90240100500e455007010202800c0a000c05044681d01e545080800d51303e0303402118030750400c804202d601d1400c0d0302c40703c14840c0e6079151915080d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 541913974 1250 541912724 541912739
    0x30f0506180601120e070311120d1d1003060f061b0b041112070f090c1b06061d0414030a09030f02240903010501080c030c0d050a020306040813080106 66
    0x20600e20038408007400700e000640c180c0c003030803c008100c0c202c10014031031905a48a2142c07100124003084403054481c07020300d882401c1c11180340842200c403000900051710580420b84000b04501c05c417100e503042d02420744c401504c40303001c031303905940041e10046603050611103083c0c00041c882c0c00c07410400c01640b20324000c80c8600301070141c425401c05d0f814191500ca45c2410228180034020139600f0102001440c1c02200e0002070040881d0a910310b0500070b03d854510300010348000000c084002030850610b82c20f030700d07080e100c2c80804c10710500300061210740c0c681c450311480caa01c000f0704000c92605e00070403040c0000c801f450403008000c60b02640c5098180b100c00b8281000e81e01000c1e2089840010641c1103440b61460002211841070340c40e003007504140302c41110f80e0f0080c0f070402d000c3e5082c8400011041d50009e5070400c1240700801a0140d10203002c00d20615908813201501e9500c200031043e009a10b09000542c019400750300311541d500c00c24002000290055031255006078501740d010800030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 541915224 1250 541913974 541913989
    0x1e23060609040504020f0a03150e0a020604031209030b190629030a0609051311010822030c06050702030a020d0503010305030304030509130e011505010c210203220303030f0506 77
    0x70404440010b42500c0c3c1d400414003001c00d000049410429014002c000d101c0c115130144940180503c0a1000b00d6514483c03584903c101031000750801020310050001035402c501d542d05020440c0b030541005550303501c8402c0c0340300307050b00c201c034100c0c00170848020292200c0c01114007400d80307000a040d5034606d0800300c800022408103120183d03034020002c5030350303c6200e41040c8001c0c40c04003018041c40c1818071509c0002e1002d07241c100c40803800419880311075401800040d101e262205894044003000d0740c04011803240c04901142000800505600041e031b007441603c1c05403d0301e500a585070031410340081d00e0821803d219200f403040c14001040001c0000040f43c0e401541352800c9520348080d000481c10410b000360a220085003040c40c0c2110b104015400284030b100b94082c0122007581d5480199101080ca00c00500401072a090304c10440c110b8030401c68040d441441282d01d41a01a548050350103100c01203000b6920910008105240d41402903c0c146a03031711000b00164109400024034a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 541916474 1250 541915224 541915237
    0x1080c1816050c24010504180312020f040323030c03180f09090a02091005030705120c0901030b0609100501050a0e010219081c0501030302060a020d1e230606 69
    0x44140780d59095040780c410016500305600c0c0d00b0440700c4000084986000140d00c5803100100110701400020301450f01e0300600385424084140c022455499407800c4031510340c4810303c40718558003003040f00d280c0756140f00100001c2d401401c42e425207011007031520f130040c3e40e40c0581103c140c0c018025030b14594404400c031a035040c5840e042008030503c85c004505080c80d0f07048403070307802400c0d4401c02c4201107000c41c03141c24551003140c070601150741d0709140d580c24580500078503806900000d01801281081841a603403040840121854407041e0400142401000d030000c03149140310800303021890402d005041e03001030301d54840d011000c1c14200001c2c52070044640d607404111034400f0721001640244444040c116040440d10074004007070920180b503a112209078020706001288080201013148500c6060b01d1340340d030181410382c41c1c10000b08083d40240c1c41a4000940d05e0000d2501c0c4482440c2016504004000210300309041a880b100c5410106c000c07110030b0703100e003010040a81c1e144011600c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 541917724 1250 541916474 541916491
    0xb06060f0c03280912050703021810060908100f0b06032a0412240203090c010212120f0a29010e01020a0201020d1202040f060c200d120509030d0801080c18 68
    0x121131701c4a09296240000650010750004100c03100c1804070800c1580c4584503204d1404440300721503603401c00701c498013407510030210650080340d15100560090342201310819404103010803401700144c002600c03036000b0b0758402a0301030590243c46594078330111290001885a03000c0d402d0510f00102c1d0b0640304803201c0020414440b00300c841c00700300e00b0b0104559620503150360031502c914104420556541091210b54058403e8080e00000e106180c03007107451995500c0c00480443d2540200300200701006049140525210f804502c2003480041e4462a14100d9407505641101c0c20400503068100030741e441411500068400b00150740c000881c11092210b03440c00c04403052551400a00a02446d00b00c082c00b00300f40c6400048441c1e114800c0400d4034040e45503000c1c1401d01c40300b41441c10100000c40c1e0f0308402e50309054004a0f0700d240100b0188180d0f42041841c203660714001030708181400c0c090b0b0b80451207440040c8440ca03c10000c00c5039840040c1c1e07034909000800c4104032003030203000b0304010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 541918974 1250 541917724 541917749
    0x807120602130305010b180c0a05070206040e0a0b0901080c030a1203060504050c09010206070203030f13030e0301020a180504060810020310030b040b0a0c09050105070b06060f0c032809 81
    0x20040c550741114602140d00385202080c42e02da04e0724074044c0000340d41e894861003071032130003048003600750b005140240b032021456440c01d00400010394158110110680e441341c814000065070442800b1014813a02010800080c02c3c820503040003442081a00a0b0810b1b501c5901c0322030300c90710b0000303c03454101d820404c074076501c10100c2402c45c06482140c1000750028205014000d03000391240c041c0c91510b409800307442c56a5034600049035a40000c07036204844e40384020104105240c1d00410200f214000e141160101007110046400d983c41100d1200000d1845484500030b0101c1c021904081d0038212428050071380b501452a9851041c00d602c4000c16500001244580c030340480716500840c0e101c3e828143c58601420040340c0c0c0d94084a0b80504942001c04141151340326490721000e82c0d10507196541010908c0d15920b034407400040059422080800800d180c1002c004c0c08ad01901030900021951501c002142040c21200d642c40351845100b0802400c0105800c40d41d5041980c128140e241d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 541920224 1250 541918974 541919009
    0x190f0f0c02061b070302100e10050a050706110c01060f050604090b0a0f06080f070c030903030c0c08010f0204061106130f0807060507032f0a0e01030f0204080a0c09060807 75
    0x10030511500501c00b404034601c0c01c8568030a030f00400e540c400c4078000c66070040f84000115054a01415204120354054540b000b04035590340034101400090015240240c18500141e503800c0c00c40d0880100c84503151004541c60200d11401d025900c040c000c40140c3c50f02e803c4c50030002c50214010341c001c032213881c0d4946010314020746554421300c00400450b01c192801c0c0743e48520181c2505020780303206810b4000f03440041c0100d4054140214126807654948190520b075450844003001c2d0341c4411079900600d802c0008400409001c2d50540300340784500181d803a403070f150024180e5079440280d040f15400c03520800200c02c01c2412280d404580045101d07201c02000e2408030b0152298040013411103191009100c2419030560004829140340d428020580001c248103085d41c0d100050b40c0f030612101006600c010f5845081e6a00d56034506040105200103000c4000d0140d0300203400622540d40080a071105100d034900399007000b0159002e00700301c81d5040180c02501c51416014420b8480d2030f101c0348 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 541921474 1250 541920224 541920229
    0x14030c0d0f05130b0c04060e060702030f011103070306061b06090203071e1406070506040303020d06081f060b130e060604050616150b0a090c0e060d02190f0f0c02 71
    0x1e00200c20016204010918154030064202d03506031805885240c0210f0010f80b0126a400454081d1031a6072144806640c02c0c10030850790340d10200040741c00d40502c40c1c007241700c8002405051b00034091003503c142c591a1040c00101141c0c190b43c425010040b000480c40035141520a1188600d6044500410b00140d2800130034035102c49980610301c15640303da140742030001c52018150980314203c0c1c4d503000d11509141085154054008041c046402240110300040d000e070b80244007040d2034000c045002942c4910329400d241101164200601d040b01805e009801c680c03080f10050030b0051600c0d8288005140f2024540007240a824610708140011980c16558001650028240100620f6076800300c44542d805200c0340c2d6004072442c00351850440c0860754140a5420100005800640c1c51490000168040c10b00402d10340c091200300f000c0007110340c45a900405450301c60030b4025954100c03680751208400d0300d1285180400c0300c030340840010380da485101180d0500032481c0990400f4010f000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 541922724 1250 541921474 541921481
    0xd0912080a0c2109060311090906031608030d0605010c0b01061110022802010b0d02090a06080d08040b090a030824041d07050a0308040e0c070b040f1214030c0d 70
    0x8029004480101c0000c3c0401400d100c00c1d114480e00740d50341c221881c1d89010036410707a442e407540491801001c2c4044c4a02e4101380040ba9401200201100c4d0901900c40c0000464040350700718441c1c07a0130005001242003058052100142400c0c070700311041c091a5240d1024124060262a08103c4144400104400c00b0065000d01d40303140d40f0110b50301e40c8188008ad520170101996092440250780211112500611840001c4000a0000803001655508008414000500340d04000e1ba540c0d0003c00e140d1003c120380a10010a61140003160809003444104800300a10840f400d034003003421100020f138855081500042401482103416044079045800f0401400540c3e800616040c41c84e1082c941c12500c00f8a02164003007901d0515440d07005000280406000282c1201b03030821081004000d01220150f04c0709011400c9401c100d026901c080704102c0c261025a610300502800c0c405100344116450480f92150074174401c9003d0340580181507000090181001840210300001c8035071b075580 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 541923974 1250 541922724 541922747
    0x170a020c0d03050c19020118061d1305040303090c0e240f0904050106141504060513031b1406030f0f0705070203102a0c0204110f0d0e0d0912080a 64
    0x400792841003065804088061000300c0046c2e00054204601c05c4c01c1c0382403082c058099413519039a00e040c2a8005001100c112281d0401c160414030202aa001c1c1d00310a00c01c0300c1c05a0b100c1c1c3d5001c100c0a105003030414084007140c100f00075440c0f125007400140000200500c210650081100e00d0400003680021908210007420365004a0300c20700700000c120043d803000090b10941c24900c0f60ba90b0840040c8202c1d10045005242ca2010410041c091240140003410003a00d618030100d880f01d07201e5464242d102c25015070081042c1c000d4005124001680510300c541e04002c0d81c03058154130b0520b0ba0815016400f83c0f8a00d01c015641c00411240ca00c01d00485540135005801c442842d001c044204c401888119114460442c0418400c04d142c3c20303119601018403526650141e4551482c1c00700001009074540319000380604000c0c02d641d283c040005490240f540d8940041d0490602d02010308003480446400108400380c003050151fa0904041d132040c5a4100c3c0c10a501c4c5c000a99003907a40c8290750 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 541925224 1250 541923974 541923997
    0x1302070609050618010b1302130b0d1e02090d02040e2118010e030307030e0105040909030507050717030a0302071407030f21051204060603140109170a020c0d0305 71
    0x401480c0c144440000c8a50188030300c5554210380d104130141090883c2d00e200c0d41c46034400d100c1000303c070f844202500a0458503000401145105560302440407495100383d925411150300c0790700c240c00320340b900c12406a10050000d81580303004483e40c001480c0064100c002845580d0710802c84c1c9000804200400d211004004000000c1e03500c00c680d2180c642049031100d481e05609013450b401c41d4070034554021403000c00340c01103003030540d15607041c0c440c3c05804082a04001062000140d5040d140c05804291806030b00c1d856030710301e600d0401c10f04040094002c0000c082011101d1500300c82c0c00070441e0000352980c5001604d50392503242140c902525203415035218402ca04003c01804040e100c1c5050a6201d001201458407115182102110500d01c0980c040380d000e0240102000d00f80301c12580c0a842804e000030030a07180e07901d00c2840c0c0001c100d40b4655a541d030030048200f00e01c0c9a0303010508045142100d0500c5903907a0003d42e1034100c1d40b0340500402d1300340b245404040c0200192400306404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 541926474 1250 541925224 541925231
    0x15120e0105160c0f021c0b06120a1401201b06070915030609020403052b0807110c0d030801060f0504050603040f140a0303020a030c0f090b131809020117010e0613020706 74
    0x1403140f08106c565545405075401607502010454030314001d80c01178611400d14029014507105901c1e110f04640e661840c000d00d954070384880c0c28041c041c0c09003001e0768a0050b00e41c19124017940044008407000d01d1b0858200f94007000030301c1790305a040240c3d5012501003106e801c0e0f000c4500707007085000e8109a4018a480750011030048108540801d465140c49d40020745012145002c01c0392081a84401160002055a2202044000c0e1040c00c003003424030350f600121342000c00351001080d0101d003060700031303400a0884030041c0145980410f01d50803a00c4c151410508060404001030b06500c000381005080303445000c1c9140402101608081d01d90400c03070159501c0340424100a00607501c0110004000307403401140c1c000c640d001d00c04501e06400c02d43c0c0c3c0d00d00050b08065540d08203a029801032145010300c408001201500c02000e40e5055520903000b0072110080d1001400103910100200d0344008144014070000d000141d041e43d005104a9485c4084592005104003e108466000d05607509 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 541927724 1250 541926474 541926499
    0x13c1503151401020f03120402040504022206050306161d1c030203070302070f210201020c060c012403081608070c0b130506030115030203040c15120e0105160c0f02 72
    0x4154540b9403481080c0c007030b200c42c1045280301d1504ea11a00541001e031641a40c01702d4007600309584260750161020b498140c402c50302c0b031200151046130303550354181952940740c1804135050034492241c01a98810303410035070603007005010748540107450107803e1460715441000c48079078170380754180800c0d812008129125a15401d0094482e44105004c0e0050700c0b4002d40020880ca41100d900210b540000c03010001e15030702c0c40c0320850b508100740c2c00d81c1144520035901c255a91a4001001240c0c0c2d03003800050008642010188804840f108400781e01c90000400c001198800088904007244030722040c030f0f28190341ca0868130600500901030810303070141a010906c044840000c1403200c08840b030340c40b41c0300d13510f03401c0121a103c02d0044542c1c510000300481c0c20b25000b5005075030028890188148020340707035100050a01d16004c144800501044178172000300c4103070302c10000b0040344540288428600680024140700c00d00540c3d42c208100d4201031014082c242401c22841d80d4001c2c1100c00104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 541928974 1250 541927724 541927739
    0x309010c113124120302010f020f0d0f0e150403110a0602040608060f03030405100e120618030304050c010804080c0d030c0201061409041704080105013c150315 70
    0x40d1265003000c2d85610b02070000d0790880300c4942c0f1401505140d102003030540c0c105a054003480340035281c00c03019507403034848001403035400f400038000107020012119101c2d101c1e5a044400d8a1126044011141c0303440016080c01501050201316040303005403d010649452608441c50900b9840861345030141800080070001c80b60028802c40d14190b590000c01d4807480d0410a4080b00c041081d079269104210811850071b1080c2130510010a50030704900307281c058004101c48640a65601007660014010000900a0210891000103000c0021400d519055a80316511216200c426041c00035120000b07003049400c4045810350301c64281621942501c0140140180c20040b03401c8015501f003180100740455582c080c030345151700040c44a00c190312548c0b80c45541c1c2d0102c0e042000ca000c400c0201181d151424060319000308040c0c6a20109501e0f000c0004c0b00d281d02c81d2601d400d021080c912105800034170455440705a4041401100d00d4005c503190070340040c0550030205019108101300000d01c0d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 541930224 1250 541928974 541929049
    0x50406090b150a0e060d06020412121d06030c0d020a0c050d020f03030105130902151e030c0a1218030207090c090503190507030b010e040507080309010c11 68
    0x9209a11410503074580280000400c8840300d02c090b0030085000c01080a00540c00c0a1604068050b0032101e000e9003c0e2100740c00eaa1084c1c100450000c600000c01d410040a01481004a0940c0c81d0103411115000305108402510303503c000e10404010020074a85031901045071000ca4002c8411135440c01201c0c4050002c010044e0160b1711401006900f40c031031800450307006c0001702008051445e42c2e08003401c01101800c140c84040700d0030b580e50540c000688803041d0074072001b5920740e007103900d8002c050a02102c41201d0b50080345007a1040c01807085115500060f0303180c210207402d003581000c403803019a42c010142d50503151070321031508090380149a00800c0200585800c4002400011091001a105031440b0710401e5019445010116400d544054626807002e10510940345521381d2a00da80c0d040101c2a00811071100c480001d2108200041204c00c0080c0b01e400065400c01c200903001902c01c510003100500b6400050703007007140710768403002c0914503181d140c045ea8207140100e00f03884840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 541931474 1250 541930224 541930241
    0x203030c07080d0636050601051e1b0f070b070b0601030507030e010f090218060a030305070602040e010e150102070f1202030a05030a0503071b170c100c050901090614090603060310050406 82
    0x2c0c031710f111009031000034050190311310441d810785506107800e40a01c50314984002e0800c06504901d4284501c0348180f9142207d20210004c1000030f100a080c1110b00740e00340300c001c0c2c0c4800d141184c1000307100c000800303401045601200c01d0800041d103039a484400d8001e06080e82c40e80b6000d5103450701c80045070401c1d5000f0907186000340c99107107815400044008410780c00340d40159005040c0303a030800000b8443d03030007003401900c25500541080da82d1280060595403c4c2c120307003000c0410b20b0401488000c0d80303204a58015003480182003282ca0111a060820490300480070f101c5100c100000964400b00038500c0e034180e028003201d9842084c84001081780d00265410800640001254031071081c41f10035a10080d80c210040120000007592040007640c0041c42800c07203402911400c24008480e440303000381c0c03140c041d1142d566800da0080010100d02da140c08c504103200a12514024481d5050180c0d0002d4100b95122a500e8840300f0020f441c1c900c606941550307290402c002c1004020b22500078800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 541932724 1250 541931474 541931549
    0x1d0a060305070e090408032706070c0212010c090504020c010605180103020f0306041a06040f051005270a09020424080714030303270a080c0c010203030c07080d06 71
    0x900700f85500801c2480c8a05550207084001e0510225401c805040d11000500c0700e40702c1003910034078810b080d440c10864200e840c2004079030101440820740c03c00202820070b0300c9040008110309220001e0241803c00070380200f5002d0381d408282030034620402d52240d005050000c1c1110303125400d1000620003c4400d000407030140b055111080c80d18100059101c2c01140d0001c9141d5008802c41c0c21500d44140060030075500c6038444000710001a0b46108407801400128407500c880c900305824064490707001d1402d03000741400110400007009001e00c100782c00c05403240e00481e0b680003d000050151003044030050030500c03031001c488c42c0201c07a55a8a0b003192200420754105c04d94032900c0b014404908038000b80c03d60810030008102844440f803d000f0990b425022850040d1442c200b00d213426a505d0044903001c03000141d507a9048020000000c48410900c0194139500c2d00210041c00c038003400c0002071000e40301080e50031590255400050181040340d402000042d103414510f000403c022001c0d08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 541933974 1250 541932724 541932737
    0xa0e090d03060f03060504081b0a030f02072102060d0c081009060608010519030837051b011113030b061816030209060a0801080715020604031d0a06030507 68
    0x254450080c00b840c4100c0b2180c0301d5001c41c19144d5110100600790040048481550070001c1e80036440b05424545c800c01c0c650002440e0030f80c1a40b0740609800e40d48140c0c20309647c4200b4081082a030304580201d040308130000b242d80328031000d10104d2002e0103100c5004000c81d00301000200e05a5002c2e20341441000c42c44504803826584d000c0c82c40c11210301e8011800014506c400500050510ba582c4d41ca0413200070325920680c0d03950741c40310840c0340c01c2041d04010265920072030715401c011480081540441020315100e41e61705202c03018045100b4800240d4200c05203c0b0440c07101c60081d44038000c55681c0c0b902c840d0340c2c0d14440e2081540262140401c0300c900c034030207020801c541031a0034042038040c080d0b0b000b2411911407221207107002d20600c94400030140c080200c3c0402e0789407200545040b143c40d0720784402d99410003010300e09103122900040d0521052408129910368006001c1c0e8126402d814050b0380183c1c4c0610038110038109983c0142c01003801000042c001d40e05a00084c421000c2d070b51401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 541935224 1250 541933974 541933993
    0x2131413050c0f0d0203010c030b0112062912010f090c1809021c061706012c07090512070608060a03030c1514040b0a0609020306061e04050a0e09 64
    0xc00440860050180c09940501d65542c400d0421405014020400619003ca402819030002e400d4a4444181c08002034442d00d1880705560014003020394501e4244040c44010300b004503000c03141600d451340b0200e40001c44200507224907028201d500307017603240c1900c54036982c40c1c2114940c450403a12070b00180f18030380141461154441d8411321384022440181d803d03480d103020300c00c0b0040d400c0000540e192103105100050200441e106010040c00030442e000150800c04280a09040c0168068501c0580204010b8001c0c0420101800340550f0030309000ca20303880303400c811136201c03c0580040b600020682502d00709190005050b1044400350b50721a41d840d9038a4040c80320310074091000901203491001c6103400a4000b86d1981c2c80305800d000d0020302e00a070302c0f00c40c15043c00d0685050740c03403c008a050105488050107140080d082c0303484107515504004000ca00d2a22a141030743c61004a081450614440008212802480004c01c0c40070096124a0b8030b0040150995a40b0214822410319 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 541936474 1250 541935224 541935241
    0xf0b0121050606190f0e091c09030b100b0c010203090d09060210020c0c03030f0c010b0315160201060320010314040b0414120415080a0b1309020d021314 67
    0x640400350303200300580410380380c0005110070300416285100740480307000c0e40030034010051100040100305005519409080c44c11041303007010700c922200e5a490140c07000b0a1590b41e08146554100d03981701c06046229900e00f0352000c0e54200c1c40c1c0000d84482c100007030702c0795a00d074150051402003010b4400d54000d40f07690001901c030842c0620440d409a007118600c4242c3d20020342c09409100020000d0790410159400081c3c219401120800d01829020070525450402486101400c076030035402422400703400080410b11100042c05440601c40190304040c5140c800e41102c0011540a8010300301c80c030001c0d201100010002d000240041e2420000c50059513007003204034000c0780c00814a042541715503c030b0320384a0f80007441c1d42c519031182c050501107800d4000020801003006620184261405400080c00b1580203800040c0c0581003481900d210340d1500c1d104031646d0000d0700c3c00181d0902910101b00305608400000c1e60085103c070241d030280c85960410300e00e040c1441c0030715078141d0b1070004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 541937724 1250 541936474 541936529
    0xc0309140606130207020102010204030c0807180c0504150e10050414060313030809070f0b0d0f0e0705060c0a0c09050603190f03140d0c0314010b040b070f0f0f0b01 72
    0x100309501c5881254001c9143d03035281d00a112030303070041c400540351603281e4a40d003001c4901c81c3e000c04000c3c0c1c4641d8040104401080100b81c141c14404014407240d4a140001849400380c0e02800c40265100c00314059018024501c1040410010f8040d1b550710041c07050240c400e41051040c10904250f00709500741a18001040385c0c40717100300014006c2c08421a0b10200d880d10030041080c0000e110305100451603041d014440c1c0010903071414415919481500e680050b100791000c0e1a000c5c40c101480e152110f4400302c0c540041d510f05491240c1c503004400e8066161040044021303014620441c00452a50386035003045200301410b404813a0080e070255845000704401032406000a043c8800300790000e4416540400b4141003140001d00700505078910000711000d1303800744004207644000070281c0d0704c1d050605074014441d005013142010b20b449010090f92041c0f00c0001c218601ca42c488601f04089082c421000a8005003504541c061030316100789001c4083c0100c21341032281000461034010903c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 541938974 1250 541937724 541937731
    0x14010504060e032a0f030c06070909050405060f07022d161805090a120206100608130b060d05070303050409060b03100312030b030f010b120f070e1302040c03091406 72
    0x110003049180b0212102c0f181c44102540d004c002e40628080c02c0c00c0c0d090100003078814040031501070062400c1c8441d01504020155101ca466581080c04001c04200042307422a40300c60740640e00300e91540c401c101203051056240300c030007403444c2c00c0c8400c02212000c0503048560b00c0a000890740e19500703460341e801c42e010840c03056050310501850b0190200702647c00c1140c2140e010000c03541196195659100b100c2c13214564800164850010810b9020301d8040280084c2031904140d4180e00b490644503a1040032414040c01d940281c0c400b08689403182c1d00d503a0300e00da07000b1041c2c071106a200c2ca030050040d03103d0300c60019100e0621034089481031200342200e0007103d208420382e0401d80b541d40c41d4100445a100c1306400c3c15580c00310a4525107050001c3c0622a0a081c000140c0740c41d0942040800d8501030200881e990028051301e2520400003842019104006544034a80d41c0d0a058220700e9202c8150007500182080c03414040145c26800032488a40b0408841c40d403000c00084044d655141103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 541940224 1250 541938974 541938997
    0xa0611090604030f0c0503010603082d0a050a0c050f010203070f020309011d01180b0a030e0c061b0703080a0807080a090308060f0a0302060c0a030807020f0d1b14010504060e03 77
    0x100700420004084e9802e2490461040001c04051981d82c0d00103400c5030300591040c1c41c0d00f5000111590f011121810740b040201031069603881d100a00c0320403400501030715503800280318001401d1907480f4012403103035200c00c2d406003c0b0f480ea80241c0718071b503007c2c6d001602e468010489101c0c1c0840a1800441038403040340041e55078641d6100922480505542c1c920b02807418048015141c1005411200c0400e000d0001d120f0201d60758410f10400404440c040d2204241c2900031a48100d010760f5100b085650303407000960880d4180c1400c204441c02c20780355034001010124000b501c10704c2203800ca46203e05c1804251260041541c0f0101c40f0003c1d9040d44500600251616002503200e192084d1886a040b40240984000030384903070200c3c40d075510104840d09941d201c1c5030b0340010075611003015584808144041d2000d1820b0300c96807a0f4420401406200348244541d1856030129003c0c2c1c100501c80c0c0041c214a0b100101001c507900034001580d041e5400790a00780001d2810000100315026044517 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 541941474 1250 541940224 541940227
    0x206070807030c030b06030406090309090209130b01023310060206160203041e140d1205090312070b040302060901020f0f0306030a05030406020303070908060f07030b030115080a06110906 82
    0xc601d4202d0090070210f21079010325a4581c0240c1031034540802851050b40310f09400038643c13010b81405491a1025448190400d0042089101c59180c0c07410341c500008980d080440c403042c1020040c0c0c24483d81c903006c11200c1950600070078074801416402c8241003540401500d00e0b4486c402c00280c0b483c0e5070f00440c80582e1014020641d4201c50110000100c041031054a080540f1120346081c0048280d91607075840c000c440041c000540700c00b0f290701c50040c084808200300c0040c0d0b0349030490340b0f400000312000d0020208007401140c500780700c1103400d50a100c52140d619403903854918821034007560154010301ca050000f0749001014030843d150514a44001380c240843d9480c04100d642c0700800f00f5416018252400340000d030100b020f0005080300d070b000303140c5a1410f8000140740260540c042c2c100c03035112030b06000e40e100d0001c07201d030b03000040e91034086135025480d80403a024180351070389084c2c1e05954020006000038007044429005104602c10b020360302402d450100280585c11f403440d4440390 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 541942724 1250 541941474 541941481
    0x124030c09060b16030207031e0501050907140d031b0605010602010e060c0306270108010b130605010f050a0309020306090705030c04150509060d05070e040309051903060e030c0604050102070c0602060708 89
    0x313a2404500d000740319104075071400b82c03255101c18020504480ca04011003401100608115081c0110740d03104850400030241145401400c06080b80b00151460064441101902c145841a0555140042e206400702d41d200c030980343c041d004050900c64a0015460600210340104c8049034180c018034419140320f0035a110030041240701141e0b40003502c42c032003100c40c80031402410303481c00300e00034950207000281c0d411802c0180b003001400c220b40508110710380350701400140e0b00f1a0544601c074405107400d64981d0707a8000305400605800002070340c144601810089081400203015040c0c90b0b066003a101c1c1c0810031018401640c0e8050700c2820303212040481441141030000383e1313542c8106c2c01090f09034100b545860750b508100030340e00304107808501c10080005240c0c019038160b000304130540300d0709041070705642c60010304082c6020080009480b246403185141080050f14100c02d00081550001c0c185454058004c0d4040d5104031001c0031039400028045001092030340c4116040c0d11031900782e94 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 541943974 1250 541942724 541942747
    0x31306080601080103080a0306230f0d050d080a0605042a03110405120a0c030501140c0304080d110409180c08060103031e031b020c09010803040b0703030e0124030c09060b 75
    0x101b09040311030406948240004130707001d40802b11744415161082505100c2c410105000058024500c030a004000000c0d440c400904002280305200324a032820f00802d40310303a0f50b40c1c0040c0c040395024071b0b44141410300c50780848450040141110444006c0104611a090420f905403611800070f81045103003400104902c1c1130190346646242c10341800e6403030850065580700014a241e8005071130680d03541802c011414010341155420855407480281145495a940380140c42007030060b001403a100c2080308110907540b02070300c003d003074503003030901c0350452000c14252088000c4205990f10010400000351911001c07502c541a02c0e010303600d0010901c41d4090403048000c00d83c2d83e801c1051399907508041380707192503e004069401241d0240c0003900450041004400b0103805c1810b803038008200801007d215601110025070f4941070100c2c045440780340319801000b2108040c0002e208401c40b914108001a200c21300781c1c1d11078402c400400d078132194a881140e2450080b01303100c00013000043c1005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 541945224 1250 541943974 541943977
    0x9061003150b0408030705010b18040f1104020f130b04140d03120207060c02010e0d020618070801060603061a070b040f06020d0606030b04060504090c0324020c03130608060108010308 80
    0x6140d050281c001c450342e42c0301c1404440d4803d40c0140380c1908042510020010f0078040c2c6040544120342095401d401135440b2540290050300042400110841c03010070801d2103020b00d00d89a400400031074a5107000c001c2d602c1d4039401400c901d08100c14080300824982c5513401074034203031400019101c45080004040c043e00d4515800c06030284a034008640c851500203000405002d031140750301280c501030100020b400e4500640044260b0740000e442e0b0b00c1c440740d000032120382c49070010030042e55030354005554038145100c94001d18565400d094002c40e059415030450011522403c02406c0c200ca554864841a4002c10400509020007240420041240d62012282140c0138040042c981030f90038800800320380c0c96901c2100401c2d2540d00c103a54a240c10701c2140010801501c0502c942046562048002807035808002c1605800d45030041080031f1a070580245400d0208046640b2a0301100c0240d50b44c0004c818900610310100d40030071141c0c80346001501441040c0c490400c2030b42155a11140c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 541946474 1250 541945224 541945241
    0xc030702071703070c091820120609060c0315100504050303031e0a0b0f060a030b0a1712040e13020111071206110a020a03051615150509061003 63
    0x114461000081840c2c05207200012512148200031aa100c41c030703140c001001ca5540d80003030403d41c03502c06620810f2a84040809406078080ca103040340c80080d107492040401031088540d0041c114100c034450b0b01c1c0c0c0000d00e0300d02500d8400102c941d241c1c0e480103404124403044913484401e400c0d5403518042814145040d811800c0c807800c0587c05c1039260310100e45140c000701c80c2c0714600c0028952600740d01101400264001c4061503040c001c1d441e030200403440400e580244280156000030300004da2078800e610180c010309004109416407030790380c0c04049100310090740e001501e00840140c003a00500c254100c50803204013a42203400d0350360300e40e010400d81c1c3c0240b4041c1e05125051221511140b414400c0d80c002e408105250b541c841c040d402c0c034404540c0011118210180d080042da45c4090700007c0c00c009003541b41c64200e90324440450300061707904450400404021072481000c4080802c0d41003c1c24140300e510a01480ea40e444007000318032481640c6041d040000d031200080360700e2180d0010b401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 541947724 1250 541946474 541946477
    0x20f070506011703340b070e0a08121206040e0d091a0a0903020607020a08030c0f1009030905210102041d0f0705030109270c0f1a0301091d060702030301060906090803030c0307 77
    0x100320305d40d22113502059041b18a0ba0005801507041d22852400c4442c10703014043c800000e00c001566000358491078490090700f0665506000002082681c1d103400a0700b0305201c1c0f0003582c40300c85031144050b241a00501075805c070000080c4030021f650300b8500984120041550364029207502d180c00b40400e503445140c050b81c011110034070101e01014100010728400c1c604034024080d41200c1003010381001100403980e12141c0c100407040d408654082402015a1401c40d22811400c43c07481a0544500481c0c501c00c41950000c600018140381e1842c14110310804d24640400f145d035180f14a0000c0d0800b120300c00c2c040750b01031005120200c281e6001c150300404030040034000c110920300c0d88806c00e401103002c031641c00c0084030900ca03c00200460500402980f54443c20ba0160000c000000e80414001c1481065882102d5081190f4910030f0001080780c0030151882811314401c002e480e5402401000080355511350006a0280700d443c8540880344210f001c0c43c00d644826180386a00e41c40070302901c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 541948974 1250 541947724 541947817
    0x6050903070f03080115020109051507050c060406020301170a031202031f0b040f1d040602090a210605131a04020d1a070810030203030a03050a020f070506011703 71
    0xd0004601c00b281c500e116001340c544404642c9010352003009030342c000a2a40442e41020030020000c2c81c001072052060101110394182c594405204440500a110104902c0e01c0f0745010b01c82808000d40c0218180e82481d000601111a0900ca8036603500c04a00c00600144a804040045810039400740d900b11a12501c0041e5403007444150540c18045500701c1c0c1031560b0000380400c0740d0150000c4200050241c0070700f454030140382106071030203003500070009051503400065004850b40c0c0e14441401030070025515041d8a56810015104c01503101c100701c8100d840c10000c506840903103401142c0860b480503140f4654022070144050340d200c058405c98120400e65143e00024101542c50100721101c0c41a061a82c90200c1c1c0082c03500300060800540d901e140d81007800541c9011003104c1102d021030401084030f440d4424040000e20411501901d215804210042007000201e0f807031741203a84200c1c42651050802503400e0300d0f480340079081070701a0522012100c80c0700e40c8114100d00c11520000c0310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 541950224 1250 541948974 541948987
    0x71404050406170c030613151e1a0609030a11030102040f0e040b15010c12020c0907021006140a030f0f02030a06091a06030318030f07080c15070203070306050903 71
    0x41e0589105070030215603000010302c030a20f0036400300440c10380c20380100c00828150804890307049503060f5101000c0c0402c1c1c0502070106800000d40c11000166005242c042c405c000c1c1001c2a500806010b80107042c26803e00000c2000703071504030180c13440d40000401070a03a0040d01d0b034813203841c01302d1a05d0145d05950203000002e95074924400f00310040540c403441d400b00e484c03c3e01d00307200454801040c5103e00000c0c00c0c5000f07000d9074401d1840b0101a8049080b0921003251042a0302d028104065903500502d40d80420a145501148041461b10040c40900400b520b0ba221041440119141c0c40d0304151544420004a010003000d03494560040d1484140440d154011034144600800e0580b646074440086400704110708408607802a05429014042d06003400000d45a100d250004c1141c41540e140141940d0340c00d002c100c1003012503004580c10560740e2101140c45442401110f4440c04442d4860040706000740110360f01194001c010f001e81c1419a42d846008040c0034001100a03c001c0c0b00c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 541951474 1250 541950224 541950229
    0x2070f05040207020a090c03060303081605030601050d0f090c0f0602070b0a0f141303020f04022a12030a0606110f0304053109020f01020f0a0f111801051c080307140405 74
    0x8a103c1e91f5440d6401045c2c0c03d0071401c02034480c04024001001c40f903d80c2001202c1141c1c4441030b20b030448000d10300541e403186580410300107403041c0100714032042d250055000400c0641d00640003201c0744c440a00035071030ba503081c080e43c45204500c6400211001007040c2512580b00302c0302c2600c040f94900385246030300580c481d54002504040141200e280b84c46070705006614081003980c4400d40d04031025071516031030710041000a10344900c03000081e44100111798020070140080340c1e0340310340400c1d100d17141d160480d01000540100d116610210303500c0380c44d80716071041c08119100e80c140d40d100214580351070035062214038090000c1e40c681e40c41d0200c10b030740c2c44412031411f04504034901000114104006004110032048a104013070f040d9400f0350b0300001d10240101d0700307030b800c207402046048184115040c0398030003103040c64075503a200c0350300440d88082c506402495416240140c0c1c2c0e10f0010f82d80480d00304000540c103075001c2c00d04402070000541191007000c89600318400e1148990400e940e4102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 541952724 1250 541951474 541951481
    0x1060e04080a03110d0605040f0c02100902060c010207060510050f0307060c0c0905090a02011e0c02040f0908120703051003030c080a0e1203090f15040e07020f07030f110102070f05040207020a09 85
    0x243c880c861740d02d0740010040d900e040c0c0140c141ca9201010704111a02d54400041c0da01d01c9222032420066883e00307086c4056655504c00e0b101021038990095541d200b192030314030010304048451601d07100414002007050f080c0b100d040320f01104064000c12499003003c1041c4c5010b9441c45003252000c1d0690f0000c13811401c04d000340c500404007a1700520310351041d8400504010389a1200380b1400446c241106043c3d070f8043c5014080607010345000401070b442a00705006000d04d4440a422407100241e11042045040f880c68403800303646c0c0e4100240d8954080000c0c129801c0d00c401382c0092140000900803540d010014400301c10356041c040c9041603490041040d94a10302c0c6045940d400200f844903890500701e20840c0740000841d040001d446070424040c3c03440c090750180000000340400018000360080048104101b41d00045420096991070800c0d8003410a84c411516546804000380d03c6500001d5820191a0104911040641803c0074080250440842a03900640d00000010504444d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 541953974 1250 541952724 541952737
    0x40b030c091801090c080c03010605070f060216171c02030618330d060e0703080c030319051312050d1d06100e01180b120f0f01060e04080a0311 63
    0x75911050f5890328805604550b5006042401d00c424401040f940b50000006c880c19120141841034407011a401d0681c6030308032031000203108910000f4425541404c074071400140340d1045020451b05a01241c03170216500442c840348042000c0d40c0740c030f000112a550007a40d0300071070150210342c1040007101300c08035201e01990031420b802100304040f9a4005624041000e0790200e04008040d00c9681001c5200300a88030300c081e244907036460088400c900140081c2c4002e581002e50183c030b40c0034101929451b0b41c41a10080d03041c80035820803124034070b4280501c1388035109800366012000090f4445904109240ca00c0c00e007081800c0040142c0b0220754400c0c1010003034906d10504820022a80162503c030000d028402888040c5404000141c0034810b802d05440048a030008122080303460200940a46610a030788940080450f4001d600002150300388450480120b92a140e0000909822034406000d0038a81007440b0002802240c100c070014418989249000109281d00c0d0100005640000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 541955224 1250 541953974 541954009
    0x1207050a021512191b0516050c06072a061e0915050304050f070b030109361208090c040b1519120614090405100f0f060806040503040b030c09 62
    0x2018008881300e188580e40c0452203072100f8296501135410003410318020090340031170142d4200c0d02c0c0002c202040c01b035100d040001801503a1608000d180036541d0081d0388210000c1045082c55894112911055a41c11100d8a44a0b4070503031601c5c0301d1181c0c2d03a4a5501c620402c0c0320000c00300048445c88014100e445134880ea80e995160f041c5890074a041c4079100426041652080000340031051036803003201e044402507200041c90258022610140e40c5d581d100c4054900c2c1010f6000345200641555520382c21f20815801061110a010030b45101c8000d8403204103660001c1099081c80c10142d02a031307200c0100401340f06c0342d900d00c000800f540b41d200781000c1c000e140052028101141e08106811205549424284801030410000606d602070300450079106829880c0410188081480942c441c3d52490b031007030245c541a69008009000b0080c040c121240c40d14100103800c0c80041150b44c0503540c00700246103002d181c251041c455030005402c04120a01c1013040740f0a50b074034000916100d0114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 541956474 1250 541955224 541955251
    0xf06040b04090501080f031903060503070312020d0809031608040e0406060f060518040903170a060501020c01021606050a120e060601080915010b16150e1207050a021512 74
    0x10a01c0030019a5410390101603903501a0800840a6001100762032000480d50400312400148540c224043c0c0ac00b6840301e50103001c0e000002c02802006240e00320881c000c1d07000c40d5000700160a0480d0b040700120760142c03031900103200c0f591019841c071088200c0709019800c080e04054480131917a544c84c1041e0380850f403032656050b0070840540f14009000061125081060070194004c00088803980c983c80c400b80304035034405001040500070118411455217404143c0e00c5441c01c200704100412242c00707403901501c18580c107080c041d84000342d00361614014007483c1c880c20741340400a58254000110b40c0041c0200410180c10050417445a84002d80b100b0f401000ca50400b680094001507000d05011482d410032400c0c020b90025440e80d260444404054003603071281051101119580666001840c5099440d80c169510455802100b140c42501064070680900200ea8200d0b0f8410418001c1032608400d0511015242c000408012810340b000c2003803070005840210980a801112090086004e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 541957724 1250 541956474 541956479
    0xc0b0c010b04060b12011d01150311030415061a19030b0312030f010b03090319050d14010e090a0b150103020f04080d03060f080a060504062c060907050d110f06040b04 73
    0x5064035080e00410300503210741400c5d21f8880000000c660140181c81000005a43e03200090340b003584a8500e01d002000074548138240351422240c42d01c58206417141c0380e418018003098180989209100c24130010307070810710b44015019045c6010342140c0c2c618090680c0d03080ca01240e500d05000140122031794152427981c034901052406900c40068001403001c510910422540038400800c076002c2901450840e20511449401200d55210703507030031010480e0801090400c0d01101c2560f15040e9554580c2c50202c5644403400c0955910540300054801d03520039000c01d81d0b0054a80010341c0c0c1501c11301d40986403850520450540d603229038441e0b001d680c0311600c528451070b0f06118100240007100100c0003c585413207809071341e4281c0c912000e04400d0799180460100902980509510b262001c01410103003010100c10810242801c01e001c040c1c068040010400d800c041039000c00c6e204024801c2c143c89105807101380045181404551b0040c080c2d03404c540b0265140c01c0a80020408520119619070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 541958974 1250 541957724 541957747
    0x120304030303060e01030c05061303021309031205130308090c060a0906020c0d0b07030f090f030305070807030606080c1c06180c0809030403110303041724040c0b0c010b04060b 77
    0x8810380c0c480c04c482d00d805401031002940350b0b84050201c80d01240c01c541c403400d200d60180113000c25640020b60090641a0041c0d46200300c0d00280740c401d029031070340300f190754464038032030251101252a200070604031001c510020340a040c4041e00702e800c1c0f500311444005031402107001d560203e41d0410104105050421040d54104044400c90b08150340c42401d004407aa180c01045201802102c02d0540f41c4c0d1074203004042d039501040782542c0001e140040381a0b581070141c000d02082e10400005030144c00043d00f00c5001c1c1c0030740c03000c6441c50740c0c41c0e0103180e4481580f81425084a207107080200e00c9988a410807150b0380c081c03000980307030608403c02c880040345c03840c1044501c1c0482201c00c0c001e40c1e400f00000010003009032422a5007101030780101c2400a40004d003184290f400010a510303a100c1c8484032000000750b08181480c160000c10b90007052402588182541100e00070071050945c5c0b0140a4641410090440d1004c40c07400480c16450b00300c00902a41c00341c2e040014500c0010038130003c0030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 541960224 1250 541958974 541958981
    0x14040f0609081b011a0d021003050604020c030d02120c031e060f061b07060314060d021c03181a1b07262407030207020d0b150a09020a0f031802120304030303 69
    0x1c49046a000290340c0c0c0c107a02044c40007a54607588c070140750b07483e03000520035100e07a01101e10110380741040c0c0303586a00c4682e4090080d04a1001891070303040300ca0005410102c00001c60f402100c1e034002000c03003034580031012002030300004c10f569000b40044609130195160900600070014a80c0031300e00500100319940c91034584640e210600301402c1c2110700a1090141031f0064200b001503e006401603954008031712154103da00503c2c4192400d440e65041c1a80316891345a10035030612000c1445a039640700070408202d001003402c040c5410017089144418407607045040b050503100b030703510099a0340041800410340800c29101c0c0c24414921100288091082c2d002310a03d030640812450302d2141c19507458400141143d060541c00121003041d95200c2d2005500949e0240c007a0000c0d00e82100850042050601c0050003030078080408a6000014000c3c1da203c2d50160707881440f04034000b44114040c1280c6c455060720502c0c1c10b0a1000561982c00c8544a04241c07c401150385604e1850010f044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 541961474 1250 541960224 541960271
    0x30204050a151710210b0421030603020a1e030c0b18120c09071101020f0a020d0822020402040902190801061826061914040f0609081b01 60
    0x76408140800ca070307400c2c54007200400ea80600c10711000c440b16206081c0161070711740744045d1003254500200001c100d090840420750200015820b5000d0b4000380d010380c2079030035030700000b0740c0001c02c45410312810500c0749011211882802c9021f46a42d03807a1602003500030940c22085814070001803001d68141e0182d14030002250540d010f10718850003501c21511096050318261141d1407030f00118070aa40b00f071603941c071442c1c44d42d0000c40d519101c5260f020741c079034403041c40395001d802412155084240903043d10383c0724040b2040c40602031605d00c03801c103520401c000c9080368401c0d0b0900c0301180031a103e00c0078200c94800c0112803003032104e04200143c22003805034018010003440208103421456500750207400c42d00c40030b20041030403400440b1400540c2c04125801b50f036111300f07000c202c01012008020341c00911508010000a1004803200b01312010444014008008444e0303540009081c6078442c140080c0a15020340c14805a80d00300004440212001e100c140e444103000814540c40e0310f0350101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 541962724 1250 541961474 541961507
    0x281202070602070f21020607060609150905040b0a0510091a041506050a0e1c111009060c0206090102011401030c05091003113f070b07020a03060507030204050a15 71
    0x3514030b04445001013545d014401010510504400c0301151a4042550b0116a1018060080c50744070020407000304034030004148500011100080c040c80507101d00350059420100c80b0040d60b0f44c4201c0030300502005480c1c2161510703410310009110342c03d4071815804c40038021098401200302c0c02044241d81071a030b0214040c2c40718190810405400104407800d412880c01c15011142c1ca407000207018014580c00130000c1c1206136104002c000c09400d01d00b4501500f01c0c2c2c2c0b2000d00307240781422640d4010b00c5c06101c01051032401160090b00e401d030b010388524181480041600e0520f80d4000603601000c0e4412181008480c0d000c1c02a0710340714040560050200c81070754036103440d580ba008812444c4200090081c41e500801ca00309404000034907242001c001c16602000b24400c00d8461103c0310030300ea59650f8002c100010614010b030200700d900c119002051580058219194180102030140c44001415820000007032f641c0c44012413034005040144075906040002c030f001400c01d01180e0150071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 541963974 1250 541962724 541962749
    0x327080d170717010312051c050406050a02040f05010507060e0f100b03030a1d151605060a0e1510050301150302010e09071d060f030c1908040528120207060207 70
    0x4501e4a103c60303c0383d04603608683e0900d0b2804203c401035545105030486940c9060216a40c00036010864004078000c0d84038a1040001d0b564031410041240600d024440c144108940d00b00b0140d84100301402c0518010b0200064082008609618000b03943e01c81201a82103c000c202010415208a44510341c040c3d01644c54001042001052105260944207400b4903601300c4420f01d482e43c04c441d1030040340070a0919a2640d20008903440a039003650221080e02c503010004003182c440340100707000d0300c0c0000c000300340b0040000a44541d144004109441a503018400001c41e035030240a00101d001c04030803802c40c464210b00005040d00c22030600c00d8014030034182889038660340900e01c1056581c0341c0d15802c1c1090003502c0018024801c1c0e44e8030310b11806011051001c1b150981008011304d00c02d00300c01841032a06141c069480c0c00081714040c226401030601d4041e030541030700d00910341020030000807404121035651118464041c1c0c58140050780080000c0c40b02c550100146406821002e60300c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 541965224 1250 541963974 541963997
    0x60703020f0901030f0e12132102062d09122a010306050303070b0105240324060a0f0813110607110a0b03040201030f090327080d1707 59
    0x140540c0b0501009504040d99100e200076001100d81c80010300c42ca0301000c0e00c00d180c900f004000510b8108060304440008030f4140040d8201c241e40781000296007620b040311a0040e581c08108194200d01c1c84100e4444007910b40d40c0410702903501410303240b21907415698a602c58030b014003100e040c032103541c20180d40c403900310741072034552502c221130015000201d1480810b41c2000128060842580f086801d840046102c800300500e230f00c113140c107990040c2c038008985081e001001461102e000b400e9082c0510070400300b1010300702c40d41c000d02e00d2072600c440c681a6030700305e40100341e40781d1282c1d510000080500742900101a84505810b4000001a400120340400c0d0348030301905d50707404450366126050010f0084100000e046286840303080040102d080c640e926202b503495913000722022800245002d45480d00340d180740c030034189016011f9640815440045000c40701c40d0444088604041a024100242c00c80e410855451555041d80c0d600307440b02001150a0104030001d44000c0900058078000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 541966474 1250 541965224 541965247
    0xa02030121031d0102101508330c09060703051b0d05040605130504051015050307080c07050a120c0501110a0503071808030403060b0f0a14040f0f020a080906070302 72
    0x120103a100140900500303c1400005070b28040c0148032540a03d070030401003080c600303e025111001c64000c07000383d0b50911158a400e040360b640d03c804205211418444604200c01d85480540c0c0c80664181c0452401c030f83c4400243c11500881021400640c0000c0d01501452040c0b52404000e226140189513004c100d01d805061800345000b07540c1008000b144100120078900e0b100001800098000c110314144240b41d00d810035a50300826000e000780703003001c00e051449502103e2003001e042d80d40c0307180c42d2200c40c80000203034401c08096485200329451354000c54455032010280d030810751210a22185249001400e40b1000209165401c034107100d1a03d0741e94011080340d51000c40c030b14080144803c9148010a0120150402c0700c440c400410b0102c204901507108200900b0102c901c248141482000c00c18100300301c0c0288091902d040d86805100e0501c0c1e0401025502202800308645a5a901820807078100502031000144402d050110745601440300070741050300d5160640c07402c4000c0e0701 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 541967724 1250 541966474 541966487
    0x151e0f0117150a09060219180b0a0806040c03020904110309210f03060316030c03060501080303070c111c0f0b0906040b060d080f1803010c02030408070905100506030a0203012103 78
    0x4103d442e02d40b00c0c00c4803010060650f04803080750300d40c04800302880b00d410000a0080c40001005003600c01d4120011480111318001d43c1d1045200369500703602565a8410301001d410350340b1046042c55000e101244d550b941c4d40c0140444504024210350312454010080c0340b400602c1c04d10b00400d40da5800b0035003880d580c500300f02c618841a02c204030f91707a0340380c00340442e182c00018210281000e940b08008000c0001100350a4203c9004000a00599888803032068607403005403208008200800d4400380043c2c03004c414065642002480d01c0341199207146d10038000c4440c201c00721031006110200c04104148084115045003140c2c0060410303203000d40e15400e503100054406c07440f81061800020400c1207082c121803080c0710764250b00e03484900764030782c000e40d140c28049614401d5003811511002184000140d80840354014010100385141c005c50000a202c00b900320002003120344030110340ea460703c10056006454107400140c1c2d9614150700880c200c1030402c42070100c1c0500401506c0030079803028 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 541968974 1250 541967724 541967731
    0xc1314040803042102010e06070819050712020d0f0e0d090e0402030705040f0213143109081309020f03010603020d1409070303180305151e0f011715 65
    0x31003582e90320746081c135040700c000d003040810358203c256100e2443d00343d0640250701190300c0101240d445895451050341c4464085454800d1503140410000c0c42c0d48003600710a070031014034141000c100c0d07100401001683e1110000710340230761310f0782990300c002601803044040f0b130503512001d04100290000010f0070401c242c8661040c094000b408a010340d40c00b4003c203030042000520070072120000e0841d8002940100c80c4510300c104481000103500702c00e10340c1082031801e00624804a070f03c1400780c80c0078034261120b03050b44000f001d0300cca1071100715184580241c540c043d01001b500d0b4021140c07007016031100b03078100000f0a4011710019503201e40310410307a03054910604025848105118460005015811168140303100c2c001c00c3c44800180815201c0c2a07038041d90703030078240b100b0340b104242d8084180d110003090b5500c036100014a26130030100143c0c0001c1d01401c04001442031070941001544240c40404007030800400402c81594030240c044485400000038080e00ba003404001c0c00801c0008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 541970224 1250 541968974 541968983
    0xb0115080f0108070b070516030b01090b030609121b0d0c1b03030f0f033e030c0a200105090309040b031506040b0a0306110a021911060a0507060203090c131404 70
    0x200d40703201004022320451004070314401c0a201902d0b078a00341300d240d400007807040c480303150305e84108040907042c0811614443d48441c00180481145103031440490f81c040c030704490444041100b65984c4023424041d60107001a9941d90030100c580034107000e040c44a42c032100e422401c112400410000c0e0700540803440f402e83c0d506007001181002c5100341e001c1c0240e00300c01c02104000822051340e0412000c420181701030b000500c500514218410606980310680d001403400c0010f009850015106102445000c040c14400062003c1480015425510161801c040316040450803810a007028802d03403000280031030042100b503c0340e40441007003600250003580695150b03000c9600f562601c1c44444000e40d400582040304018040c07038403100780c002006080060040080e44981582c04c882035200c0a5004480048840e903480104001c9522011a0400703025050000d48085091480514840e0310040090500c4074024401c0000030362070400f0080c03100b441c1c440c13480c0224848142040d80141e20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 541971474 1250 541970224 541970227
    0x4080a030e0105100e0604020a0c0219051201060303171311030319021c03051608040501090209090f0d05190e0402040807060f0e0904021e04090b0115080f0108070b 72
    0x82800ca018040aa248100355800c01c0c0503c050724044400c00b60032241c20100d070402c181c49100c1003100303900c605800c1b50005070a50300d00e4130241c50140b6806031900c00c0d0b482e44075082a621404180c41d5028030242c104241d43d6020301304280f540044468151480040c940003182c03422510038400040b0305c440c00b401c7c0c444104010825030720100220345682c103607003001e0180d800800000940e165152100c10403842001c40310b038007030a8000d0141d9400b0700b021490020200c2205003007110302c9c00d802001a6407564890b00321201503243c0000450144c00307400040c2c89480c0d019032a0905d0040005005410000b040041c006010060208200c180c4014681086115907140018019000b50380180c80c840c058440c002510340d030456440c00d086c5185031200413021090b1420002c85030740485020790400e05464104100146902d045000750324000d00c001aa00c00e1a01c600000700c2d426007000300c02c0c4080c0707a085000140c01c4681281d000c40b86103d150000e60410048648a5010744203d1285240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 541972724 1250 541971474 541971487
    0x7060603031701080d120e0a17041701090201020307120e091306140f0a0b060c030a020309011d0616020414010801021b0a050c09100915030c150206010506180a0b03040b090601030b0408 81
    0x1008d0025078808d40d000700883c01110303c0380b040710445510a111700900307603e8103c00d8820150040c02510600ca4058019500307002980d01d0390300940440383e24480410600c0c6030200700d180e441d4038149002c0c8108609030b4294200c1460b10000702c50b021444502160001c108001c94425982d107840d900064980300803a0802404002c40c1950040d5501c100385808042034010304250b000020f042d003544242c1e118886107402c0131840004c54411011150000401c1060f402c810440541c51060640f000d88001185002c0c4078446000740d1080e080b0700321a0b50002115002408180a0203a0404040014001c110902c0d90781c00c0e030f1010800619030044180c3d03070026601e0103081100c000240340e11541485500300b40c00c400c41400d00240000c44094401040205088405600c2c0b604a10700030340003801c9036400d01c1e0400c00e482c0c1164616040d0152050402c405903181d100c2444010310003180069280e0909207420061008000c1203441700d94030903030040001c00c0340c90000e0350f00581c000c1c0b00d9a55860 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 541973974 1250 541972724 541972751
    0xd0c05060c030412290412031505060a0801031106131403010b12010e1006260c03010906020304020f040e06042a1701050f060a14040207060603031701080d12 69
    0x19980f04010f918545601c1000703000e840440742044240b40b071021000030800f000c2c2d0002c030390000d840141a01d241f003a610703508a8025404546a043d8004580c071507542d0304c41c00a00d03e640b10301d03001c1c00014428401082000640f120442d0700e100200c0300c542c01d018166400300b88030751180c4a1440f0300804010321140d542c80070f501c800e81440740034140000c2082d00d42c0f00c0ca40079110403d501c1c4420310501c00044012803251180c0802da64003050181c4840044095225030b000710212008002d00420360b03017001c240c0c0c003446000c88030781c0314000160300d91606004102d1000c41800e25240554100400313030b0b104100201d060b95010b5400300101450343c14541144174a4480c0d0802c424101da9590408500d0018a000036641e000c2c2540003440540e4680013100d0003004156040c3d030b080741492200340902c0c2031100d21003104c160094401424403003551100d030160f0b0300c2944198042482100f940b070000140d420031030301401e0104001c0c0800c2c044c1030001410380ba42c8410540102c1c0e5114480709070300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 541975224 1250 541973974 541973977
    0xc060f0f070503040623030a09051e150a06030209010303052d0304050105100821071505070906020604050a0212010f09030e0a0503010e0a1211030a0e0901050d0c05060c03 75
    0x480350904464840703040b850960340d00d6002c1d00a200104400c1b110340e400071038500f03140c9041c4000350042c440c219110041c1e088007412400d0000c440700e001c2c0c44080103c9641d403415241c041d003203071001420007658041c4c129242a4018088180d0a0300b06802172026032106c03001a070440c0e505203003517070b511703800b1040381203d80c0b00b0090001c8460a80351081c0c0320188046010f03602030f034042d038000c200036200c1200c00400c000d034920131484550028402c928020f4480c0704140c0e1003070f510050451030601c0c80ea4504070710042074800e020b80d01d59203100f40701000c1e0b0b205401e00050101c82c0001d11070f0b4100b6031103055482c1e05800740244142e140c001b01e0000d052082d0040c000e40c050b01c030428000a00245005840e91070200c684500480c6850400203291405000b0301d0102ea40002c00740640004580b0303039025603010f20580f5030500070030020703d0740d200e9003c00081800c400159166000100c2079000c01030f8800040c0c1c4141d00c1204a0b10107038010450507000c0303000326801220007655075200d80000d542035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 541976474 1250 541975224 541975237
    0x308031506041d0f0c18210a050f0609060403171918061803050306040b010e09041b0b0406020316060b0406060305040b060438091807060201020c0c060f 67
    0x201da0340080c840240c0040d10110500034041d00c02078a285035a00e01c0b00315080e008806e88a5a9009041c00c010114148030400d283c0c03140301010f101c2c4110003182d10f850f10700003403070b1002c0b915a070200305d6040c0120014040d181e04540c00300090000c0341490b8034003c1c090a8a039103e241d1a060042c00b00e0842c546030070089001e007000103000d21400c4403001c4014010141da038015903c4509242000d0316100c001d40d02c1d010f18540c5070f11a035045441c1d200a00c4001c0920262480c14041b04454066156582c07075003ea100c1c0d44118807983d454454118140c0a20340903510000b95948188002e00841e600070080c0d1324061034487e8081c3e80c035000d60900d600503280e0700c14001c1e049031514101081340e076030503000329106a01400208860751100e03010b000480c0c04540300c80c044144502d0140d004280203031141c10700c0e105c0f0115400d040061640006041c410b0503210401d000c0c05500a0f94410071003030000304002d21282c0000c50a040624000355203440c80304152500c039540000e0720300e89a4261600f61003d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 541977724 1250 541976474 541976489
    0xd0f0219060c0806121b04090b040f150506010c020108040c0b0d060906051c081c0507050901121e0e1e0705091f0302040b03100c0324030803150604 65
    0x140404504040004000ba14100340000d642e510006125080c44c03544081034446120061a00041c42120340324000d520b0103201e0b90158440e840c101c082059154040e015034003400c10207800c40035030f2034003103100380e15100044041424242000000e03a00300c02840301081d0203082002160b620b62820500f0100c69411007502054046000302d00014640d01210686504517020007000f82c03183c0804c04203c0351000f11040780c0b00905600400108118007514554091007107130f201014412130715005645003100d00700000703040400c02c00d03415030f40116121082c2e00000800c200312502d80080d0810401d40c4640190f005494440d41c4800040401031180c10649207145440001140002181c036600d00384549881041c0510200e68070201040101b03c40d0f510303600c1001c03042840c550a01019140c908151070785030140880f03c0705094024010b8512481d04c4d544c0005980408100010911860300003102050f0101c00051000401d001c0c00c9036001444500340c140c10004810015040f8030441c2c00140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 541978974 1250 541977724 541977763
    0x110c0d0206100501091809050a05030c030307082202010f05040e0c0d0e0d050d09060b101e0f05070b0a0e121201240e0f060c0708010b0103020901020d0f02 68
    0x80045501044450141902c9a0b000700b0041e075500c01160f5180040c003e04121080e606100082892564800d011891041080d2a0300d114036883d03280c1190407002400c1d6250b0000010049102c0e0f1008a51f644070a11000001030030805040111081d044103000906001c0d80c020702034521405101942d000301841040d06c0c07050326108111503140d030000808031003401d040002a400215020032101401245555900c0c148800c14043e8400380c080c0d1203003035401030303541c03c01129261220b05203000380d06800e8450022807810b100d5841c0c42024413007812801c0001c000e50002456a2140031250f40c03c1e00100450200d0301c0c0c8001144c020304041da000f9160340720b5074220700d422a007114041e10024002ca80108950383c2c1c1d419510b04641c41d201d050548110544c04211a024050309080c01498400741000c10308a074044003145080e0b2080c07209911540c01701c2420040d4120234000d8203480102803034250304110f4240000b075030f140f0750320456806000d950314041200c180708202c500080c108458042c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 541980224 1250 541978974 541978993
    0x4060c0e1309060b030d0c110415060206060109081603061d0105090f0f16051009081b04051005060318030c1506120607091712040303050903070e1504110c 68
    0x1200400b074090003103440070b00b0003401c00c00500e40882c160880c409692980c040041840d07481d04005240c208556500981d103820314908000f20741080c0020301030b40c0c1c0080c038690800780005020741c140e60f4007002c02ca9124403250754000a0010806040365401080800c201c05c2c0ba00382d2651982c0c02c0c2a00b101190b2809007000001f4500003140c2405142c000c1c20b90f040c040d10300b0421900c46401e801c0300c000705100c003e002c00880c10001c0140912026070310700740c84515210440d03e410040b1114100d220380c0c800c012007800f246440e10615030004001a400d4001614110110f2154003008261101c800600010b0410841c014000c85010300101d0081d0ba510308001d0342602000c40003541c0c1180204904902e64100c07601c00204580601c2c02502c3e401c24041c0740c0b441103800c2c140d05900f100c80a0245003141c041240d203a00282000c0c502c652540ba0300e80c40760341c040c145007442c50340c001e40d00c3c07100410503c00200503030300b201c2610110035180880c07017000c450708000041c81280c00c20400c0c0e1166603100d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 541981474 1250 541980224 541980259
    0xe0301021b0d11010c080103030c050f1e07090b0904140a0c0e04120c020312090103061701050f090706090303050304031b0c06030b03010221040c08030a080709090e0604060c0e 77
    0x18001c0a0b155866031002c12000b4000d80d405c07140002c00c1c4102140120b00140040b0b0702851281a041d8856012940013403080d6101e281030182215680e001d94a040c4000c520312001031151342c0c06021801007c20088030313003c00140180c80045c0c805400c0038032184090408c41010306c1000741c09a001901c50340241c0d62240342e07264480003220203644418944e0f28455040d840b508082050a03002001042c80d2200035500400642c068030000d0306040d5140c40000300007210846140c1c2d400c07410703800040ea901c0c00e050000c0400d00c0081120b03816800520051141e1608408404103407909450300507201da42e00e203800e03a4011801003444810080c0c403a40101001182503d100955101c0e550500c02500c3c03980c1458280d000c0d036810141d0750602d4020460302c113900d010400d03a01900a50b104030240d9a90740c002c038190b6101804500000d12028108402035410402010042100107810464044000c06294070f07194090002031000d0389548000c5441885400c001506801c010480c80742c0c1e1561100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 541982724 1250 541981474 541981483
    0x6012903010b091003053303011107140703150f1401120204141506070602040b0c1e070b0d0b0d02060d23040804031202011b03060e100305030a0e0301021b 68
    0x1400f611800c0d00383c41402850f0f20038007809010319003000c030820541c03070456070707101140c4c000a1040d1200c0388003103a21b0700d80c0d5070240503a04e60312440017142a920310041c00c0c0060605000458410700360300101c0304000080c00c0d184a90320800000700b00003130381603000380118054401461094242b841c600004552500592602d0502d030f40b0855040000070700b110701800300c20384116009041a42c04006159544c140b141c001d0015034898030f001031078141c48050b06101ca8111500303000240c1d01c05804101c510404041880e16410500014007020340b408041e00c0c1c4511400301c1c035141032a254064101592902c04001e5025035006085944031030194404100500910100e85e582c00183c42180b104002d0750000d290050390044000c600e85810758031001d00c01c01028036460210f43d030300c1013145040602d5501e030414002199401040042c54a00044001b42003d811141c0d12154170740b0410003d040041200c10f902d2081c1000b060b5002e0160000f8020300452003011140300c1d807541d001384400310214 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 541983974 1250 541982724 541982737
    0x3050307121503120f18150e03100203010503060a02070b0c0d181419121103040314073209061c050709060609080a23010c0207170c0306012903010b 65
    0x6480352600c85d0851021a6441603101580000c012140414090054400380e091207460103414021150a40702012078546643c0101d4004455400b10051015140a2280c1500040702c83c10079420080f807903c403610055000f5000c0d5500020007e80d003100c40d201c0b500326085d641c200600140410718641400520590010703c03000d020b0007644454644401a0000544400c2d0041138003a54141d00050594040a15030440102c80c401070100000240515003c4003172900010003410110b0325160302444401400c682c1c82c3e1003401e4002694001103044e901c4101142d83c202d0b200802612410046072183c2e001c00c0040c84400c10405040c5c2c20322400294000448800e00d004101e07555464008891160303141c01046402d810404a000214002e01846030740d0702c0348000701000800349521114210b0b181d031030b03d45001d13822003481000342210b0919841610308840c0060300740034000c0c0303000a0311607005009030524411a42d01000440035561510354004000f401c04903560358650010081c1504031b43c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 541985224 1250 541983974 541983977
    0x81b01030b0111030f0a02030408031b071406120a230121020a09050a1b0e0f0f060d200705160f14130e030301060f080a05040305030712150312 63
    0x30040e8420703944150040100120700340050340c14010500561110b03640500300303480461006100104d080642440104905d94544031005038402c0d050345810705114843d0322a03554541c01001600e1541c84440c01c45074154002c000e1052143c5d19002900c0003002d05003405080e01200154440c0c011000340052410b030b90b6014640d18900303a81c08450806529104170080d003000c0d9100c8100101d0740c4a404c0305030081400c9001084110f00d45549420301e901d080703020800180089040100b074240054440b000c440b054500405405440340407840c03510441700722455140d0740c1c500d414070740d4080144c0320482c2c140c0f02d0821503035030a041c02e22654804180754580450f01e03140c503001584000103030500c01100c0603214608448001e540030001080009942007641503100c1e524051088802e20065000c0c001c642ca42200c0401e00001c000d2004070014010202e00b846d04080c0000303c0d412030140c0e1790006151071302c0009401d00c80e481101404680b50b0019100746500e10210030050101a21024200907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 541986474 1250 541985224 541985231
    0x31c0306080f0109020f0108070c021f17070504050d0807020402030112050d020604121440140d0201050409020708280e060c0a0b0109020a020c01020303010b0d090c081b0103 76
    0x10b008500300d400c0c2c050020352003881d20b01102402d50052200741c0e070145450512242001c101c0d00851458401281c00d126200d0709030354010321241d00094001140300c40742c03682142600d01100c01078824800c40c0101403140860510f035408004250040310310155000d8010754503969110000308440901c00e508a0706030107490715000041d4400030b14244100d80007680b03400c54050520042d64602d00c1c006002041c103108012014000480c0030305d000103a032030241840c240014485038030200034100c807107441c0b60000c025410024441c0c501803488202000b16004c1e2040c6a40c0c1c4010f03107040c40760350f100b65141030004c81c564050058010180c0084500341196210103a0160300c01c3c500301e04c0c0099000d0106064440000080c2041405000c1c060303c4002116407500040e103c0542d9031030264408102d081d00042e1900555505204441d48038000b070005605550400402d0107850287c0d010f8400410382d0380580d00180a0740d210880005c0101c1004c3c0c49a550341421402a0301000b1040c2c240407a04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 541987724 1250 541986474 541986493
    0x408070b07080301050d0c080f0a03020105060a0f0e0603031b0109050d0507020d030c020310290d0305030a0b0409060603060911030c0a0612321b0a0509031c030608 72
    0x44080c01c0300c00980d07005050314035507828802000003800e80102c007510101c000306c101140c82501003040410f1b40301e40b20006d101800040c90001d080d204010641405088a01c00c10450301d030315411240196001c0e10b899404540d52480403074610301860b580f14070000c01c91304403400c1c0c1400c10340c41102468025401d4490b86000c04000f55154424a48029003000700c4915403030100703126980c4039442c103100609075600030303030b070440d03098241c4000c0d10300d2000a9000c1040c501c20041c08603e2003620726004d4802880309201074502406a00006000e180d4103034450221450690315680400c00c0c8550061b800c0140c80e8590038080010b1200403011100722280c250038484030b00c3d00003662141007400034007100388070341004003c850350308419041842c41c903118034403244141c08200740841034070000801c00400740e0b03d001800b0441c0d403014283c9204c51400200c0e0150507007954003142c1080019040080e0759860040220f07140000010100d030140c40380142040030b855168100c0780485180e54100e503030104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 541988974 1250 541987724 541987739
    0xa12090303110c012109080c0d020f010b09040f0305090d120809071503020f040e0708070813020108280f06140114090127060e0a080a0b04060f020f04030503040807 72
    0x221000b801804030380022240c801c003d00211051011000c3d061002ca0610007e40d50905c440d00200c07000f120a4008804810903142d040105001d000c02d01302c02800300d4010480460101c01d00034201030312100d80c1034010340525001d80300711820040c0c05802c01d03c0e0151141000344840c0322119480c0000381040c404200300640004403802910214588407000c8005a0030a42c000e43c400700080908150600c00005c3c01d003420303d141c1b480341d8000c0e116049a40f4004a0091101c1c2000b8030039040030b90400c0c180300140c2d07881340070305078400e41003d001c0d00c00c070034035015010200e0310305825803124900b04900c20765404d8007074200004441002e158446030b59414401581c142c0400410620011405d202c100c449601c503840058a002c400e4059001c5030551020301d0211035155000400811603019103014207003000d000c0c6200410440d00504507180e007641d64910440c8010340084e04a40d00e8030719007003803608103a044038044011300005031f507107a0ba00e182060300c90300f0a20407524640103100c00011b600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 541990224 1250 541988974 541988983
    0xf2701060f06110d1b080c0705180411210f0d110a0b0610090807030305040f0e040203150a0b0409052a09041b030b0f04020f040605011b050a1209030311 67
    0x801109000d00b8159069180850305c8500daa084a14085401d000000100305800b004200c10303170a540143ca0001d0500003400080207003403011020001409007080085841c0380383c00400d640c4210350b400c07010448a500c450305040b21024420140c040d264501000794000100748204800c40e46640d03000d8a4031b840c225483c0c20740000c01900300c2d640c00d800a2400c0c5480035440c01d0b8240300d41480304400d5164842d040c6020840d0700100d0114100150a00c021442c0120210040014072020401494941e01081d1240c0c0743c070580d20051b030b43c14008991200010740040c80e9090340035108200e071110a0802507514040c9040f107400154291402d40310100e46101f00903100000a09249110b403204e5940070700c240381020381c07403071102c0042002200040c44001030302d00401c8a00f000600310304050041280210703075200d040b4440c0d03181400420099030800041c2106a1080c40701c00c8450b03d403030a14078180b400140005200801c03603100d8145c447c0c0c0020f090310a4131300035036809203000998003170982d54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 541991474 1250 541990224 541990247
    0x1e0702010e061809061c14060115090302040207141009020103050f01140d030203070b101706090c15090a060201052706040215191d0103050f0f2701060f06 68
    0x89500010300c0e0260713040080c3c150340c02c00d6000d03000f02c50004c1c0b4200619401a002c0d82c04030b40b0f0920601550414140401040c0e000d88807020100b204050030a6000d050f640d1a80300081c0200d1300820341c80203120a406141c0e803c030050105075500c00c2a050b041030002c152112040380820700d01808600511003403c461030507500c0350130002d00000d600404001c220f9940d0502242144410010880011860030015020781c3c0c06403a155032143c1082001c504030440e200c46118180d01900800420807000500701228560607509032120a0403201d40303000c42d02c100e02e800ea0300170840240000b12582d0550210b4490005800440388104044568200005006040c140c459100d80c0115015140c80441510200070048010b4034002c2c2105c03000603000444810400494101c4540e0041c050038445a50308180c400d180402c0140b07030a0710760380400701000e007150001d00344003030000f800d002c0b008205051142003005c0381100c80010010720b40c042d141502618000030001c140008015005980d005c80c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 541992724 1250 541991474 541991497
    0x1f090b0705060a111903060303090905090d18080303130c1d0103080f1210030c1a030a0903030605060409090501200901030507031128111905031e0702010e06 69
    0x940d0f01e5081200d03000d4032580310441ca07610810454401e44080039001e0020380342c45a200482d101e80746040c06030040f20250b0107000c20398249001c016803403d02240613002d8440e181480f040000035000c1c056001e4030a900704141d50300c000014440041e07070b080304005549101d1681c900e105a2280643c903030313903035117420a0200842c0b5a40180300080310385001e448a940b508a036142440c50009181e08180c8098988004448100c0400d20500c04240c03c4080500125108961000410045c40702503201c0140300ca408140d640c01d01c50300f0140301e80c004000624004150a80712a2214202c078018100d031502107440c3d610b8034014800c06801c40315800c84940d8010380c0725040040190055000d054014031180406a9a040f00019403c030000074100c05050f030204c510b01520a1030007090300381c40b104402400c0c4503e1040c00d8141d810002145510204110078080000400345440b91441c000d59800b000002003002802030801040f00217010790718000d81c4c0e4040a02c030300400b032007030314841c0410010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 541993974 1250 541992724 541992733
    0x9160902130602071d070c021806090a1a060d020d021c200a0c05160b1305090603070b0d0e0a032a02091f0e0708071107080615030c1f090b0705 63
    0x16511241710b0010f41e21aa41d0300344410400d5280d80020107100b04001000f220680c1e100600503d414114000d035407064490900f0014086011407580244555a4446103d8980000d21005490880d0181c0b032044030020300540d2a03521504107202c1320b4044091400003c0d02d082401d14001e0840605d14042d110701c00740451414040c0481140c0795412988203468070311940344248941003481c21040c0c01801842c046548603910101c881003c5082a40043e111301052001d0010031703070380860400c08a80351301c030115075110030540f10079000d001409245010750003a11800024507070002011080388060000714144900c01c04110860f10980080194019050500145800001c2c0d81440030002e20310602d4604a9070382d0102c1d01e60990126054800110010144000c10303801400696181454001500d201828003400964407180144001e011303d0b000031900c011a01c051043c25006100640341e0405142010303440540c04200c080c07210001454500b001800b0b80a940c2600c0d807240d030110150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 541995224 1250 541993974 541994009
    0xd0b010f030507211d0102090406120c062001050403090e0901021602120c0307090207050607021b010c021210140a0b210102092112070503120916090213060207 70
    0x40e00f0b00d00a88030f240061640c40340800004d403481e103143c034800701c0c0170000965280a42001d10043e030b11554407035a035041d010107080c40000c0526500c01d01740c50240c5404013441800c0455000640761000f200180ca5281c0380c00c3c80180356100f4400829986c001d440b001d43c40e200c00c3c61480c200d2091040428844661543c40030052402c0e6100e0071142c0462012140d848241400103403c3c0030365030703000d1100c040d4002081020014240303c40340d40004980064801d61405000d44411580198034941c10024040107040455032244409041a1803100440d4000c03a408101c84000b0700c8840c00b0f402c9440400e5000a004031090701811000030b0025045010703070011f0300188514941e5010100a055409100c03a201d6074580014000200095800f4038401c121a08100390400c140f50003c00c001c0c4600b000040045400041251071000395040341125030340e5410400c508040106514290b1009030000c00548040d880e00602183c958140d00c00b424203a9400301a030f502c1d07085121701100d000000c40b52 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 541996474 1250 541995224 541995257
    0x30315032001053a0e0a020a09060506040b0706020d020d020315120304121401150914150907090b1902010605060a02120a181d0f0f0612010906020d0b010f030507 71
    0x5500444900341500700503001104d42c01c0242d601000140c15158403084906040d40b800303445d0f8400a00034841c0820245080c41c0110300203228078064807101e20300000c0c0010401441e541150002100c90000315210760361441e4800c0a175100b0b4640401b0792403a99400c401d80d1401905040040c010400110300c0e151030300200c0c900c0011421010355003500d8403011a43c0040c0c00303010f04103106100c0100d6031205810910080f0490303004900c0200c10148550030030000c80c140074a60003104c5d80456480d103050b07882100480e080c0703441c2e401010759071001003101c40c1a461112204c0f81110b0aa400070710003d9120070601ca010300510500c6c0c40140c0c0220b00c85000c0c102d2041c010700310400302c0d142c003d58100c060044032004484552180010b00c200342d404607000e1418008180d00b11200f5003268856051440580840d410080c01c014442c0103040098210007000751b11400e002a8031603020342d180c0d104402e003a401080c1546845010070280c0e0f0416242034031903c107142c441c0c85a80c03a00c0701a600420301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 541997724 1250 541996474 541996537
    0x604060b0415180b030915010501020a03200d1d2239170709050f031603050f120a0c0f0305072102011b1202030403031503200105 57
    0x200d090034081500150f0040500b000111800340c41001e6040365a42001c0307502c203161882904500600c0c8000d01c00501007030380c2c0400e84060041d0903103400609411072400140903503102124031100e510410341c6d03c00c0c1c0d16821a200000e1591a0390f200d00d0010340b000d0a01c611001028607521041c102d80c5075401c84010305c1c0e40445000c01c01d503001800c40004030b15081e050300d9561b012801a00e01d0b50414007181c1079120902001c40303100f000c03079003045091104001c0e10728010790150a2203410a0600d5108039101001156503402c50362a070f0030022a030b40d0402c0d03901d40881c110400001d0040706011000c05118200700c640080165642900700d804540f28001c440003801000c80400c00100a1600400e007810680083c101e42c0300c0c2d800c50b035500a00406400c40300c040c0000ad40962202007200c0740719400c129071002d40c0c0030b503070700150b07582ea1945021402880c0d0080d5080183d4800040401440141c2d6028100080400da040c0101d1092000543d20360081815000c00144041000d03d51584400c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 541998974 1250 541997724 541997759
    0x30e0301020a2c030303040305190309080a0f0e030318030c0306011d04060209060c010b190506120c04120302060108071d040f031e0c051002030c040b13030b04060b090604060b04 78
    0x451400f41c250000028250740c02603600380e000940100b000340d01e41240e8004810144035900301041142602c0e5104c01c00303801401c0d5a1824080c50204d182d02440c0900303a080000e40008040d87c3e40c400880809840c0c0710842c0c48414043d201d20740e40010a41400542c6c00d050315042042440000c3d0303e04003000d08104002e000700c172165000d02c61940c90741c4645014000c040d82c58000030a404a08105109240802e064020b000c5040e420040169460b0300084440c002075039021301c1c4040d552001c01403901c2c4515071002c0b0b111007494007a0b01c1455030104942e416146c0c2d4000382d0f14200d95400c0b854503031042455148140781102d03004039000070706a00b0a1040c661190904141429504004004c2c40754516102c20100740e9020f001030070040d05118804020306041da046040d070071300c40d005100500039802050200500090150b40c4900030600c003400665201d0040e03003540c5014036007200130f4001d50003542c2c01003400e0700c08540d061403d1b0003800d065a50742d00003542410b1900c030509035030010a2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 542000224 1250 541998974 541999037
    0x60607030306080105040f0203210324060301030503040f081605040252050303070e01110604110a080a12050306010c020406080d0e0105041d0c040e070c030e0301020a 73
    0x9a80010f0300140a000e100e10440c0a0070030702c11110303c01e005050402c85010308440100141030101803090030407000750b03508255201300c0981c14444075400310b80345c1ca0039088425070200011000108000c070002c002c0040c1c43c0505050007006a50b10100350b540c2c951400003d8444680b50024003590800e5409807103d0000342540c400d80c0701d141c00c0490710715003011500c5001102d4a46007400c294103050700000c242d1a591060303850000c0b41d034440c25101d010281078041009913007410401e0b243e101d0074007523a80900d28000c0c2c80403400e03d0702e48200204041c0c00d400d4014081e031840050490070201c0c0c409040743c0c10000b40036200761030b1003003210300e580b00500982c14865800c0071080580c44912401018040c150700400d08070414113806050401010002410004100800d01144800c124001340a0b900c111036006a40c0b0b0341d6240341d10310701a42c1c220582c1c00c0442c81c20050001c2d480403521005074040c0d106c2100e81004441854280e10400f050706020600398010f01246422201b05500004c101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 542001474 1250 542000224 542000231
    0x3070e011e031a1c05010b0a1404020904060b0f0c0c0d08030711190506010e01050402091f03231602010c020d0e0411030403120b030303010303091401111204030302010e01140606070303 81
    0xe080002c109640c90720764041e50344c0c240e080c08030400c1000d1141080c8800100c2d01c0c44012032130181b9403000c4c4006084054041c68011803000709503111070b00000c02a20501c00e030301e5100e034040c84041b4910303000701c2d00c401c407180b140845c02ca0080c00c1407905003220396044103259285035a00c0405032480342c074043d1290700f14496071040e11170603100c440003034810910583c05070115500d00000c480d040001030304507620481c41000040095594803000080100f01038011207808128010280c0044c941d80030010405035800380207040c3d40980c880743c5807240450700c101d60020074400600f03d0880d621b448018001d07912001a44042a001e10600105d041c0c00400103d40308940090b01e1400d0b0300f040d80d04a02045ea603008208944015004030030034180c05400941c119071540c0c40050060440c0d02c1024143e80d2240100081d5905c120513000d00740c40c20390215480c4c4420f5907078180d55503100348000e8005500e80400484c1102042c0140c43d4482c0746514a03035030a84442c000c01001d540b02c20001c80a0540c4c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 542002724 1250 542001474 542001521
    0xc050703050c0f0d0c0605091c120f060b0306090a0c020c04150f14030d020a1e020d2015070c060810090e0705011e02070e13021503070e011e03 63
    0x10208100d51426184d5a0b070492000b201d440d00e04151400030f424200710382c00c851742010210210460341c00202c8140d20f003808503003540008074001070a0030044000c10a050400100b50039a04100031400380c682030f921100076540380e511070f1080701c40034402d080058024041500f01443d16420030b440e03100710a40c071003041596a41040001501c294460350041e602d002240203245014454007003541c5031400600f40001403683c80d40f85510f140e10f41425081d4032a0031000c2551111255001219480303082ca038034200345c4250a841c650301c2501e00d5440350648000d03000715403901c18140c80e07009503c4000c02e03e80c00d0074914190b07035041c0700034904180880d44410018074540140144088521010701404905080000041c41030f540d0517200589440041c60460b01c1d16800910201110081c88401000e41ca5004c0003104110704840041e41c858495447e644090b60403030000c40c000c81d440c3c1c8032030349141540001501d028814440c0c12070304d1002c8040000d1740e82c0c0aa04011404601180341c520b801d50b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 542003974 1250 542002724 542002753
    0x50603060a031101260709060903080a03050703020d0e0705040c0c050c040e15011e050d0308190f0606270605030411040207060525112109040203130b01090c050703050c 74
    0x310032941e1200504172080501840c20f40029261001d04040d1a141a8040c15522070031454414039070000100350740c030000245141d2291741500c0c50010414001ccc0001e0101d14400c9580741041d015441c400c5103070200c10b03205940141e249100e61507012001e42900b103a0b11003040010090440314005c2c901079035004c41d04071241c03802c50b14040d120701103180003040d00c524500d00d004866900054001c2640f402000f02203500141d4070341e440b00e80120400303038000750b500d0003801400c00441c0e0008190301b0118007046054001361310b42070320050318040c4025280700300040700c1c400013188115400308400700082008101024440307480d003130b005003025140c41c00380d036540002c994007116025001d001864020a84851401e0f0407045400a0300c0c00d0102c0642c42c59070035880780340d600340110401144452035060f09442e4000c1d10b075192001481103449180a03c1c403401480c0c082c036800c40381188080000300e038142e1140304085040b48143d0f0350074200748842d80c09980035444482c50408500c9001502c501d0721 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 542005224 1250 542003974 542004017
    0x5011401031e141504140109091536020f151c020c100b10050d0603120c150507090b03040807060f1d010509060424050403020a0c050603060a031101 65
    0x18052500c80020074a00080c400f0002d10a00072110300c600c2c01c00201300080c241c02010941548c940000014107081c3c2452300000c00400c00b045426000e0034210fa02c2c00500600380703008080045400111200306100005c2200300b00c400070001c0d4840841c6440c42031506020307a0403090a0100c4241a241090342002c08204031121141303164090380015501c002008180703c1521003202001d02406007100744000100070aa8807140b5000f00715010070030360880c2c0b41603005400103503004284810000f00c6101c0040c14001401d4055412603081c001045000e501440b51600c902d480c0d5495503a440e09104200700c040d8800740040c0e49121090100c0008101c45119152a280d031500001a000008910190030305030308968a00084c0d1400d000c2000b030020100b00140e0040d07008208000e84038204003111340280f125620070005c01d2601003084101500000d5000196029500030003a250703130b50007081401e11003211211307000801e6950030000109a1054801e480d80c0c14144a00410002e61034504034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 542006474 1250 542005224 542005241
    0x3180f010c0e01110a0b070224040314030f06011202250c050301090507050906011e0c170313020103090311030d270b13050a020d0302160905011401031e 67
    0x2203075580c651072240c0c0380c0c104041c2074280308282001d000c071003500e916480d1124108840604400d48400c0014400707442402804520460040900500b80010b0610b003001402110120082245180d62045051900f000c0c1c174403803001d60000210541e90f01d0011240c41c540208400d5a0341d030203100e42034400101c00300a035404a0001aa175084001500348200410203540c042070082c4d240215a1001ca0700228207101924019102c3c0400d94446800403100d401c00c0d1a03003600c3c140324118201224607400094480b24a0003404101242c8071402020300c0648801ea40ca5108440700c000f6000055000383c0100c417040d4000e0401090b59070f420850039003540e00c101200d0180c142d0f500c0da410b101c40c00b03840c58003510681d508581c030542481a50385d01d1801602030080c0c140d0369891090300c0204036040150f444c0c81540980720b0007450741549006507032003031010b043c040303408880030000c40c0c015250704c1124101c45403003081f03c0d8900324a600540081c4203692030010150b4110a05025406c45070082c02c44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 542007724 1250 542006474 542006503
    0x11190522110f071101020c040f050712110d05130b04080c0c0301020301051c0302010f15081207030206070c0602090319030806090f010510020114100e0702030a050301170102090d0c06031404080409020318 89
    0x207c5140204004008422a2500d01d0f0103a190480300c0c3703c5103c2e83c0096400e0385a0019002034140c6842004800804510f00000c0902c2590401c000070019901e0140c0410129032084818440c816010982030380401d015803600003500c0400b40f0404089c0c484808080c5019000000b40c4e08003080301401901c1960000d0704240c0052241001402030820040c890701c00c803400d0781e608221141d41c00039140c41c0080c02c8041040845080d600510840d641160356408005080b903403100807105907041c0306519540d0039404920001e00158171800d100030003a12400c2a00000340a903800d010400c921326051b40c224004542d03071203000e81c119902c0144082d0180001441400c0301c02e1500300c1240400384014860300c1150020300c0408051500441600d05407090603c540c01640811600790f40240205010340354841c000907811810f01c00c0c81070000007a2165a94140181c01c50000350740c05a0005940090842100300800c00003c0400c0d07001d1034002c80d02d460090071184000b6089454901902440e10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 542008974 1250 542007724 542007731
    0x6030705070c0e18060108031206010504080f01051e04030c0206160209010b07060e07080616051603030605210a08070201020705152511190522110f071101020c040f 72
    0x2130140251880c142c00c8000207000f01415170420a0f07264503400f0b4400201024114040440d0b87c50f8015030541d405450f011048030381c03808440b88514040e1070141d6442c1d40070081951500300381c60311945107d20681e01038842a585440035820701c26a0350180000c280a0900304100c0d000590f5405070381c9008003c00d030340711a2104914140312089414005001d517181e80304a0080107040ba0100f0035907840041d0408140410200f007005503024414203440d01c4c00790741803070b01ea60101900b6901c40000c0c4c030070035512031107070031250b10109125032070034580014140e00154403100010301010060406c9441071041e0b400055542002c82c4c10200c00e000d1130003031024040790080c040144041c8180030420082c0708001c00011a0b00c95043d16162343c42c0a42c05207024110521658100004c4c2000500015142c07050182990240c0404e60000351143c1460030f04000302c0521410440b8251100740140000007490f041266840125039004600720a055005a24030310104c3d549038425410340c0700303040a020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 542010224 1250 542008974 542008981
    0x30e0418060f020c07140612091b0420090604050307180e01090803070c05120d02070c0b0304030e0603040302210c0d21200f121b0906030705070c0e 65
    0x809481e8040303490100700f84140226001e0640004040c0c0c01ca445501d0111105d0700340c2d1022854521610000c1100150342e5424021400d000180d40b4040c5003400c0c2000319903102d00c908010681f5508400c00e020b40310340f0708010041d0600e24009140d00b42008081c949080d070b82e4808241084c2556002940c141ca0001c443e0148000718003844161400c2c050003000300a6485e96010101d01000c0c0251003000328600000c001c12104001c0302e03078079100012106407503181c0e00c100344001c1d5110b0381c01103072400c55801700081c03003141e544180c03802941d00d038403050106014041030000c0d50b04020b009404621903281440419034030030041086c2c60014030101a070740d1000003405c6143c0800040004200041c4004600c00ce4801c00c2c0c0c0b5020441c3d00d1321000c140c550610300102c000444d0803405c1c0d40e2051740010491800842d00d80142814084082c510017150f46030303030310000404c41d10b50810301120000c006000061400a0045070320030014240142850065141d40100c00c559400c0180410103040a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 542011474 1250 542010224 542010233
    0x60103061e0204050108040305030a09050f0f10020c0a1b0306020409062c24060c06010f060801080c040f06031b091107050a14240114011d010c030e0418 67
    0x40e800940e0365036095282515000000f01b50780d80040019003002400b10108503007600340c0d0072076504250000c04498020301800701c100d4a40c04403030811041403250300d100c06000c410900940702c05c400003030701410350038010f40c954100c00703517550145c44101c5004210109c0003070341c10b1000d440903000350140050868181480d2104500304015505640050385450500840c403001c403d0394000b44e1507100d09811844c001800310110314015004d54010f40226854100c080c0c0051420304880ca0044000300c0c00c2d03564541a54417280a0007074900b0f03508001403044c044d080903044900c510040f070000007005640c1e52160304008414003a8401c4d111000101001075a200b400b03202030500e03c1da21103501e450095903906c0c1c5c0c1c0700d0080d10001c01c241405020341d0f02c802c4050051200e000000c4500390400c528410480055480901400d080120801c0c2071955952141000c5605403000300e1055007071440d91401914801d5410b103003101007210f030310404447d507151400307608017020074013007201d40b001145e150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 542012724 1250 542011474 542011511
    0xa03020a0e06190e040b0411030603011805030703030504030909090503090306060a0f14150a020f0601120c090203060a090f06050306011a0f0309030d02031e07090602060a0b010c0506010306 83
    0x150610a0b0700600c0100c00000c3c0b401c0c08200c03c140282054400c5403071000200380500005d090869200b03240c0170000401c0040c5c40019407184100302c1c001c1019101e040d6462150b00c24508018200768014041d0b9000a1701a90116810038040d05001007403503503c0d0403940c2a0741c11404212070340c0c2c01c0454026103038142005100d03081101221162940c50410401c0c0f00e0403481c9104240302c120850100590716221100039000c0e0b1404003094950f079280f14007002c1c0d6a80f8104c4041c40a9104003400024101030010701c48150b43e900c940d510146078601002640a500080c2201707a01001b41400015040b0140c414100000048400814100d10302801c050502e20140e100c1c107420400060368042c1100c0400484d446600f606030219240c2d15100140c520307500601c290300003c284000140b058031a591a14410341150910b00342d60240d9641c0000c0b00d1500c0c181c030400001da03019601007829a0034070703004400c0c0060180341011103803005440e1646403500c01e80c0142c07505a40c0e004120b203040980c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 542013974 1250 542012724 542012747
    0x50708040521060a0b01050904150e0f1602010506300a1b0503031c0c02190f3815181006091a03042a06030e07030c050d0311030a03020a 60
    0x1500300500310001002a2080c0300c0e524045209580d103107120070310300e086103043c1000303012405000381c2c29181c440481d6012040558dc0c00c480f035414146840e20142c4140141803040c600501801d00c007000306000b0140078041c6500403903050b60f00070881702c95103004200e82c2000318060055243d0344807550010222024058101ca40031ba0030800507200b02d80040c40d213500101c0e00b46580020f0780a4403100480c2084140b501c000c20440310340c248070050081d00110316080724012054a10302e01c258514014200038107441b8440e191072220406100c55011440041d8070219003880c28000084980000c3e910702c114441d88400c00c0b01440502c2040c040740610a00503050504041c172800e802c04e448410107590814100e000c405000000034208070a18800030142c080785001c03501d1303244084807000d003806150b00039500040d03d411010f203036011001592404032600016110f05103820401400306900e0462800d03006d125500700c01c552000c0007080103200a074500e68005840720f050b040020107101000c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 542015224 1250 542013974 542013991
    0x14040213060b0f030a02130303020106061e0818011805061b0307080c1608040312030f02040f0911070b1003030e0d03050a0c0203070b0c0703210f05070804052106 71
    0xa041c00701405210403104084000c0d4600784e120742d108216040a88541e0740c003407074030b00b00c446000400c140e01508907406907002c40d20703484140110b03804003031250790650944500182d06100402e9a00400800c41c400e00f8048100101d840d20303032800d039042c00020140080f213195102a040000ca0002580881d100720b180160142c0740d810500707401030503864041c01070448c1e000f0001d00c03d2210070413042081c4484d544030a580e034465075241001e106210f03941101ca00881d0034001e4081c81c0441500c01c480684841400e10015141040501c600800c0910b10030f0342601403c00900002c905880303020392166642040180c000c5081d0b03d4010511560310407028080e143c58050080041e030840d003030710f502050170300d0045060384150002a02c0c11003258840c0c1d802e84000115142d1180010541c5d10540740220380340c0c40317401c5210f00c10503603e4030701c80c8605000031102c0e800e1003038991058000b0514107006052860801e0b03110400101c01c1642144001303003d640103a080e51666070203205066006120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 542016474 1250 542015224 542015231
    0xc0510050c090a0e0112140a021005030103030813170d1116020307080a0b2e1502120705060604050415020d06090507030e0c0f010c0b131a070903061e14040213 70
    0x400d04e144080e1b01e80c950006103510584440105940c20800081c0302c0107800601c02c02032140103600182c030540c400c1c003050300012140c200044000c8000c44200700c119910240912144480440e08141d42e00002c0c0d0b940f0426864404c19a0381e4260f002c050b101c190030000c810000a0740c5481050b00d01440c9910200c401d8000940a4000c1030000d0ba42640c801401443c0a242c401007203c1200c0011030301c10a45000e103004240480c000728001c502e60201342c81c40e02140c0418140d150003000500030a00001c02e0340d84440c00144050034241c001c0354011f8400c07200c044003115031403603000590304524403070030706150b0b01c2d00200320424682c014160000c0c030b54141005061400c50b43c86849010219105000701c2e08000040c640d0b03480380000100c21b5401800150fa50f0801c81c0740c1500742c603442c072170035038100c0700509825000803e17560000f4050f000030f81768001028070715541c52019021540151305d81e44418010f0464990070390041c0c202804034000141e450b443d00b0710400041d6103485e80001a010314 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 542017724 1250 542016474 542016479
    0x705130f05011e05070602090d050115060305011406031501050415020a0309050603010b03040605180d0e0a06030501061d0d1a1b03150603190c11010501061d010c0510050c090a0e01 79
    0x20840100d40400b0740016007d641d0383c0d02c403008103039082080c01004144d58070700080d4102c020030f0403521406440f410b550901050b44c0e20300400b540640f402d030346036a04c0041000403841c030100d01c07065543d1404041c10030906150381c13083e610902c1c00100940c0c00c0540c0001140604242d40400480040d04040702d1450465040c00d0301c902c03d600000b80010101a660400300c6e01d607540da0403c0001c01130034801214040510500020a014043c1d04000d008103c48040800c1d00d03406802010b043c2d40003079039501c9280e11813483c3d80f0030128920604641102070003072558046a10003607901e0180b41207960580090901c100c00e014039214400400c0301701b42d010320912038109e1156050480740081200c4550b26600c500c2c83d5940c1030090706945e010b40501d840c440c034801c84d40100d01c0d030786490fa4030360007040240ea8540c2c0071344503510b050b00c4507009000e038201031041c10341c010310510a8440c060000c84080030030041c00c40d0211703001500d001e141c100c00442d850b5207618007248100050800b410401c1019407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 542018974 1250 542017724 542017727
    0xb09070303020f011e0e51060d0f05070f0519030503030115032304031d09280509010f0c03230915071805030606010c0602030705130f05011e 62
    0x100f0f83c05000740d080c0c1c6031140007207611410400d60000d1003658001103e0b47c1b01580301d0a0304c00740d0300b02401600e10700364910f02d00099449040240c03540040645610b0b250317100d03410000e42c051022001c603542c0d20300521420200714200141c8010306a00d070602210b29041108010450020042c400c440c0100d2010510000d00d0120503641100c03200b1050711b501c484000c10a8010307001c80840500d030170311440000d190700e41400b69038a0003503019455641020b52012901441001035103800d540107071020001c6000c040c1a0001264840404604d5005606140c80c4100c25640150341010b07150b91181c5080c0a003803001d00c201060340c4e0480c101005070b1a1502c800541c0e45100f070580e07a561010304800140d040106121140b540100c0340e80041145c58840c9010b07003040213020400726440080b40c000309a5040000303915000300e005844207041a0b0042e520480658801481c0f4410407206010003000550b4103088440606103443c10005110300745400102034820a000b8030b695241a011a17400da036 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 542020224 1250 542018974 542019011
    0x3f0f0f04020d14010b180601031d0a030e150c0120120109050a09021f080a02180f061902030d0c03021201062a0609020f0307050609060d06030b09070303020f01 70
    0x55034040c115007034480c00b110f82c2d9801080710448003504603410350840b00c03404038070b219400d01c605000d803410801d486d00b603103c00d030490f0401422411950b1003c07984401203801561202e0300c545c00105451884105007000402d41e41201003003907802c0c1c0d110b00c80c81c180078004040e0304209008030010b007820701c003c0c500341030700700c0506200310600030b584c54002c22101c1d0100d400908445030050081941f0006a0440303101000140710720b28005140880403e500c10110300032116103c04007210138520036200c10420480904003000b00d507102004225a1204200d207150b402041c00b516005192034107010b81c80e0f1030035030b450000380078209441086a84a100110542141503400b140ba00115a01e0b0b00c040780300a454009201c4d0742d5050802c0004000c01c802904494445032080e100300e0100710801051650340d45090003915071111042c0805920303401d00201400031590305a5012810544e2a1204880038900f501c286541d40c108140510034036404105c50340f449480e402c001c11050340d003001d40081a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 542021474 1250 542020224 542020249
    0x2030901030e070504050921090a0311010c02031207030e0a0305070e0a02071a160c020f0609030106050402070303020c1c1b06022710020606063f0f0f0402 68
    0x1410ba54540700c01440408002d00005880040d2041160741170044c1d1441c0d407030381d000d40000017000010b01103684006116081e80d42d458070280a00e1010750456691a064020b00c00386641005418004c000150b503041110815822071001096512041c80c1030061149500030003160042070350000030070014800040000c00c0320ba050050b8041e989074030821002034482c8910107451000c0400c00c0000c0c00311038010b03041c096072148140c4080060f1180b0160f5921940400c00b0307502c0a11448045101d0425400520741ea01d0010000241d1503152000a03080740c100007415000294041148000d00304100310b0450455107903a9010550220340364003d0404852a140001c5180080e00c1041082015010f8914080c0c0221151070200800c01d442061600e00042003403142c040941c0c0c00c0407a0303001048580c040c140140c26117161107000035a800400903402035a003d010100d4240d0800e107884a80051902100c3c110700300224141034580c1a040a0090719002100310000207100040e0f4070006680c0c031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 542022724 1250 542021474 542021477
    0x40302030307120c120f0801051e01080a020408100203060a23040b0619080a060614071e080301140f0a05130b01261f0303440403030606020303060102030901 69
    0x100c5841d200104c1c0c24601951000b00350003450007020800c135411001c00381c80b803802603a64034144e0f1b82c1c030020402d01c80c10a0742101c15210007a5003000b880e5200c1c6054a41c402d240e1340000d40f07080c2d51091054604400e904c20140502e07804000c1c80ba00c2d10b400d2a07050001c00060800c0c07020f2000c1402d409601c1c03120318949501c0b882d61000c039500141c032a1010b980d540c41555170240e000308054400903001d0b1000302d036590200c42c580000825030078051000a84c0441540044509004003030b580c1641c0c610707801c0f110f01088180c80440c0f600107500080198081c00091520030030185c10306051004070242d811550344100403001c001d218a48071400c840010460b91000443d1561a040c01a6000480c014078290b210981200292194403c01e04880c05440082e1842c1d02030180703100f00541000807800018001740404040380045101d2520003e5042c040703501c40c0f13143c410584d6070038146180c0d2080c0036000d48250020401819054440c1400030261070000c3c520b0b52800c200000c1d00c911505004c2030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 542023974 1250 542022724 542022743
    0x319120806040f0612030809070f0b0c101107030f05120a09020d02040e03090306151c05030f040f0e07080c030a0e0f0109080c16050303040608090319030609060506040302030307 78
    0x541d1661150803200c07995000034001c008041d20380c90059074910b04081c0c00d50204e248000461918000000c04400304d0300b04002c0e00b0200d0b4248020030840b6881a140581e2a11484010295003811441104110000070f02c10039030345e50807485c010b0b00c03020308401014280030081c49101011640300da40d60b07500c48100d100001d403070441c51002a110481442019401610781402c0c1d4403d0200007004240320300c0220308458030390741c601c4406680c01a081d031100d0340010404494a095002606018810303030303c51425241419100141448990803560000c500080700600400c90805603084c20340d00061545440c4200d840d054a094445210281c00300e900c65958107036048410f0428010244003405140c0280440e5881341000c040b80e421404136241e0b03134051445907080d8070070a0320402045610240240d0b00300351070f020040e10740000c01810034070107002c00c1103454210008a0745d010ba0300c00c80c0d900d00154560419118000312003894006c0c6000d01c40411050000d41da00000f901c401c640d21620b00d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 542025224 1250 542023974 542023981
    0x515041d0609060703110325050d05040804050405090102031308090a050310020c06010608091902011b0b180a0f0b0907120501021c0c05030a0b0f0a09060503191208 72
    0x11a01900020556035010701414482411404105903002d82d1440e0350510029068592401c0300e8807040da4040306200d07420701220030071181d80709885d801c1510b03800d10504000e80c85ea0b51405543c1c04460032154848000790500c4246000d21401d0380100a1200031400c620703000e4014240c20100c1803003d44180707808942c0086960b148400c15000d0712000d0b06903030030419090100e00180d006089581500e0140c0070000c1106c41c403c40807035200300c02405c010981d070b00c8038240003110302d070114401703074100700038007548002d002d00c4246038545d83c52044203844914a04011b0796a03140c5046141d41c64039410298008000c502e860081d600740c00d070818800c400b00d0315914142c510388840c541c0580b55044010410000307200d410350181110840f1014a41e1303540d50700954a40848815600b514085a01403020400010b025030100d602c0a4003e00081d80000e4024001940040c03180e210b520401d403225000c0c0b1083c2414480303040c2c0018280c003900101c0c0c1c0c0e580e5494250300e40340c1003101c00304581c84000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 542026474 1250 542025224 542025251
    0x100c0b1503030f0409060312020a02090703051b0c030a0206100b0f0c07080d020a050106060903022d0303031501021b0303070b0a0b0a0603020304060b0a0b03220b090a15051504 77
    0x311020114282c007a00d40e200d640c1c04201000d411135210642314002009000c04003a40042510000d20b41d004000c050b0960311614154000d10002d020215002006000045e03540707000c2c0024a28040340b03100942e240c800c0c1002c000e1500200402040302d50000300030401540310782c003050712403044000306080c1c1c40c0c98940d0406882e104903540414664071420340c3e510307161030700424440c0e005400349002340440c64940c1015103a8110510000790404082c140314400c51803d2480c001000322009805115500079000103441c44e0420b0b90103c0402d5400101d4403a01e41c0c04020b403d011072050711510005240b0500020b4581c05181d0010740400001c80025080030000e6000d000c0b182001014412856120b90f002002908100d40444041c0d1412250800310300c1d0a0803044119420119118035550300c0c0452450002003091880d0402d24100c42d44900198100e140c0c14031401079a0014000a0200d0070a90050340d4985400b8940c01d00d8482070007101300c1c0a81600c00355800c10313600420700042200b603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 542027724 1250 542026474 542026477
    0x3080919060818160e0103120216060f030219030f0c0201110a030b12100533040e010b0a030501020a090e0f060418060e060703060504020a17041112010b100c0b150303 73
    0x2000007844c2e480e8000840d24030001c881c402e05803030150240c88292203501034143e0b0342c0e0540f2012114680c4031014208001c911900c1000c00120f05460090b007810b110002c6a003142c0009a16000440d842c0e00d101402c43c100303403045507941c0303030580b0080c040034081c079460715298403803460310004150321120b680380552180b268040c000582a811159805103122118004100c1618600d00769440302002e403e8602d0a068011071a095201c0c01601d0100803604003c002c3c01e911501584035501c81c6900e100300e035a1a1030741c400031030045002507030300c036a06030009100403941d0300400914035448040c84038424100803060f520100070303600054246c0c451401c80740c4070030030180000d102c6030410302262030f1707e0400724409004d660143c80512046132181c040006030b0140152103c005041c800e02e0610b5844259a0160010300403003a66050b2410100841c0d95190104030242c100d079103801d0121000d080400d0302d00f0494820786001035011645665010340e080700504035044c0d00010b00c41065403982c0500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 542028974 1250 542027724 542027743
    0x816020406031a090114070e1216031406060d2d08180f09072c2809021305010c030314070c02030f120906030c0702060403080919060818 60
    0x3a01890110150641c51150f01c0c1156040d00d10750030302070600c640900380d000c1c450148080c0c0c1c42d100c0051650f1014452802c00d640851803140c810782d01300d4907030048a49403240c00345005244104124800f44200741c60244040c0c00c182c051941840b41202041d4540d203811040300040140c01c0c90300748080300d04242e442d9130302805004e0703082c00640011021001628054011001c0d141d4486903003030b1004202a425049074410045130316100703540c0848110207821601900c420003040d0300384100002080440400e0a18400185650000c8402c0752400700c90200c010503040c201546440701d4003004030382c5a00e03144207440c1400304164001e401c0500a4102100500b4a12518050b03440e14150080ca0125404000d80c003900907a042d0302c40e007200100c1c00301c805600307034a942e80c500a845030038044550b0002b44140710620f01480020010307550040104000e5003d00c100b0354a8071421000c02c040c8a0215030801e1400d01400010860a0f81094105901030b030341d074008084503004131403018100b80d5003c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 542030224 1250 542028974 542028983
    0x509100b0906131a0301090b01020106030803070e18040804030c0b0a0c0209060301020d052508090601030b06120307050105013b1803072306130b060a03060e0a03030c0507081602040603 81
    0x10713000414400200b1380914103c1c0d0856100b404440c841c4001642203c00500014000e008108000344a040c095020b012809102400101d10303107441e00e020304004003041c2c0d0b040320b121200140c1002448030741001400640700d01007805242c103804074070250009003000f04c000d000310b41f4600000c0c0d09503402e40c181c0b03410031001c08040c0300c1490320503500502c02070713221900d0180d0908440b180042c10f2003862500c1c440c40d41c10f0000c0501d030342151078030411000010b04a0fa4404000c003010400420140301800a1b80d00c07580001c6030650410704010300000109654036010314114076080e0748201c5000310b0710841042084404c005841d2210303150303042d0f00f400b00420824840081d170740c8100320301103139001c00408056414270024180c45004648a1109655010f540103030b414520001c03480001510360000703001480c02600c269665070b074a003510b4040e200c41d41681c11010180041c55054069207203071446a181a518000c0f0548d52000c490003171100411182310080340b000115255a8007540156411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 542031474 1250 542030224 542030249
    0x3050d0507030903090b1c02030402030a050318011709150a02040801110c07060c120e040209040e060411100f03020705010b030a080d0b031606080403091a040509100b090613 76
    0x700c032000c2d020b0018803204500107160b050740040c0d40c0e11540142c440c02d07406809002960542c51420a000c0c0d00083d100366810f0250359000000a070042008100b42545482e580c0b4800528500240c0484200c0450300080e10003881004034515010444105041e583c20000c82c0c00d407550781e0380301c00070300458008030070703030b41c41e0450324418041c40b90090a0605c601808461125482c1c4000312420614008014010884811401044c0c0c2c0a020706100020024000505007014240003909a40c01c4102941c11508034100380320038400f60b4040c1080600c0c1c10384a51511260710600144440c140401040c20980e000ca440e80400100390004240341400504803420040c40c0d042a289c282d0100311481805072620440c00e00d94240800e0403d0302c15030010b2317513a040e14581141601d141c80001c1003101000b01501c000710f5217003440b0070b1071605101c0d00d0040b0380d00c442c2010306102605402600181a4224280080200e24404011949428000d070f55041d1541c1910703071076900f418080d801000c80c0041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 542032724 1250 542031474 542031481
    0x1a0105030f0a1d15090c1c11040f020a020d0305040c1502150f01081635010501080304170f0705010e01090306180309140f1c0203010f0902010e1f0c03050d05 69
    0x3c0002e00845241c8800390785540e07501d505451660710008a03100b25040301802c1e40b0069030024401c2d04107034123070065400c1503ca4000da0001001c0b01d00511104010365408a2200140d540c10400d15105a0f11410100480d0038a600c40c01c00a4045200700340d000c0140f4640f48900c0b03442030001002240c00e03468422a5400c0006010590110900422025103d0004140035281e6465240021596840da07001484402c4413a510b00301c007040104034640703045240c0c3d2444200000d00c9214000d00e050400356449a0524440079144040058040820f9004880c1d040000e6404a12030088070024200510788010301401610700300426840585800d181800c0d06c001003044030506000240700e03659081010361144810108003000d0a21290880032040c1906a90308088000240941030b00c4204a982a5039900280c250380500e04141d0185031500029411560403098000901d4000c980c0d14100c460f00e01c100c500c84090f03040b4078004000841404200741400b0b40d007280c681d0b010b100c0f002d00c02440d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 542033974 1250 542032724 542032781
    0x903031819060507120507050d080103020f0105040e0c07020f1f0806060f0d150b0706060f170319030b12030304210903020112022b1a0105030f0a 64
    0x540859801d0140e1084600c01505018070114482078075142e032207070350800b03a1680329419252800d040c042e00340101040454049042003100e0201076140e42c1e50900b171581588184252141c81c05501418010140030500001c402c4c40a901d07402103012070842d403200054000200d00700c04e1603144a030010344a140c21243e10311500c20032221000d072a21150300544941e420311140b48190b1400003040310050200c2202e41445401c40704441152403100c6119a489260b1450251300901c01104c3c6241da03808100144c0b8120b5020f00001c4c03d80380d080342d88200c0384600d401e49a1041d18802002c440c010080f2010860090740911110300000d411910300d40c20101d8101c0c2e5075841a0f0301504d6003443c03540c0044103c6041083d003440c1d000e19640e140b1784580b42d980192085002c0421014600d5000d22407201e081c100c0707204444c44880300e003481c1100a4610030076481103c812a00e818070340e204903940d0b0001d50340c03c4070469800c03100122402c060f903601e055400c401085440042681d05009170105110f10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 542035224 1250 542033974 542034007
    0x210618140a0c0506030f0103110a080105010f0602070b090303070f0305070b0103030e040b041b050f0c060c03010501090e010f05091503070602010209030106060e0904020607031806050703080121080f090303 90
    0xd104001e1540302c0394031001004850b00007118800300022280d00180000785955464141000c0b000d00300d03200c002d4440480f5400d540c0c0c02d130844c49034482d07038401c10008213a040116100600c1602280b41c68120150082500e9104035203001d0b106da10080ca082e0201031243c0120307885560004605911542c580c0350081c80240d0b5168040d100702d0803c416007080307203083e218456500458401d1101500028030b419a1150007c04103001c03d0b80082c010412034030000d102007845000c20201490307880d0f0401001400380321058000e50350340c001c0c40e40180704a094501c10035003941c400722008582c0b070786c8030f10410340ca5030a1101ca05400d4001c8a000048103078054016001c854401c80003400700c2a1142e004961242009100c0b960041244003c9005401d01c44010880c0f02c0c040c2ca0011011841412041380ea00d999511000002e08002441c0e01850790082c40c1c0e1f8054642503101703a0081c01d01c4110b5880b8a112040d01400040d00000c8a10840300080c081f82c0c0c0018001e402e4030b490f00095940b00221 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 542036474 1250 542035224 542035243
    0x22209080306191203032d061d09062a190206010b0307050301091109060a0207050a0b07110603070504050d0c030b1501020a02010e19030606051c1509030c230721061814 74
    0x81c440c0d00035489c1303101102c410007500ca101040010440742d510b0150004444104945003070100b200da00014420000720300c0209004032012000e5000d100440d20007d00d00341052b444101089400c0c02440a0329502104881c1141d40e070281c00b240a4005492458803481510384880d032107540001c4403082c10390042103c4048841c00c1300e00e0740303a096446581d034400307216150004022841c40301c860f160502e020030165812694070b1411a00741a03d0740e0200303421410f103040507100d0b01c070310040400800100040c455403011b07000c100403a02101d1440040d542e0301c20050024180440140485034507161051409003911100501c40e5040d50f407410b040c4001c0401d4090340c0d01605604800d0000c0031121441c0c8244960301c80d401c0520409408440030090540280890400002003881c2d004112000001e480d80051401c054015226001c0c040f03107004944c0d031100018252a0030410404218250340f4050160000004554903000c01ba0303544840070441c200510000d0388445000540c5000140c4044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 542037724 1250 542036474 542036489
    0x30c130c0806030d0906120204080304060207031106070b0402060913150824040b09150a05061e01050901050c2805100603080304022209080306191203032d06 69
    0x1690740310320090607150544428401d012805c42e00080110b81d1146041000043c41d04000508180d1106c00541c1590f0065120800680c40800c041c4184441d038140c9170000d413405c640103454901039594804420703000901c007911400e00403600c100c1e9600d84100e44070074200d42040400c0742e08200c490000c4031040c81d004041d4944500c0b001c03800d111030124505402071000e941210302559980e61021031031640101074060728082d01d00e5007c096620702c08024041c0075030001c04034491615000303000c41254418102504c20303000b9400a00380380d030402c0840d4900242864000e41e5102000c503818508041120580c00490308028403200d9005c08007044400640b103001a10f8025040c001d400c010345000d0702010f000c440003007002c64018600b001d2a0070039800c0684409040b00000e1456000f00c5080c3c02e8140c952034000000c00c2541e203000140d01d0200b0300408031140c0e2003400c12203c0000c40d440500300400303041c5e075109050a010f0b40764079400040c2000c105c0d2140d0700b40d050059400505902e104d40070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 542038974 1250 542037724 542037737
    0x5010f140109080c0904030203070f08030411180601030f021204120906021f02070c030b0f0412031103041b050a06210c051c0f060909140c0d11030c130c 67
    0x202a076118003511000c840d8070100411403551a441080740002018004800b58403041201000180f2082c0c0742044490158480b40d0b1649080e0504003101082860864481e101c0c09625103500c100300d062040d08072801b8070300080c004000c2c500840081c07043c54902da100c2c024481c108810051a0303003d01100030340c00d544414209a0b160f4059943d021412150741e0140d080c420341e83c205030000d40c085c0000b540503c0070a00e03070355a42c3e204d540707020501381d031300d0401c0310743d07403810001030040000c0c81020f5007144d45801c02030001001b9001030710b400045c1000307004000e80307041170000c910900a070303c4c094100182000d03001503981d84d01500c1c100542c0840b1400c00a034610b00d540c2005e1521401402c002580c681600d0203100c80740d000d42d803e4401c0259003515a440c004114000c50700d01c14240034014018001070005c07154201b807a500d684150074003060341c0c0a845c2200f81d85d140c1c2d05909031031a905c9601081400d40300000241030110400200d034001a0a450020b0071060a8022060b00c01242c0c4880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 542040224 1250 542038974 542039009
    0x304020f06070c0314030d0c030203090d05130308071a130b07090e010b2a0f0c030123040f021509040509070e070e04021606020307090909050c01111005010f 69
    0x1d000d00784002d0000703d004602003000c1070304c000000c55500e6050054914102070200721008450450042800103a0302004000a6403410880380403280a1070904900f0244205a400071902d4103000c014001c81000c9004020468020040d4014452840c00c0c58010701d0400d03030090600100d00819200031190720042940240514240b20944400f148011000da007012404a060391184100811504a035083c40e281f64031030380203042c040041c40014054100c000d203821450b0024440409119914050b09138a0006601c54500f194a02406d076010321030740d40341006100096004000782d041106492184101c411881c001d01c4001e0b000c82302081315440d07104043e580c0d01c40314000c1100064401d404200e20a0240b1040107006600400c003518281c0b1100304640e01010f032042c200c1c0e1260300172040c04011504030041601800505030104041c44c25a02d43d42e5032102c100c4510f40c140016686910340120060080e00400e090000e002c3c041c41d60b54000000040145128882c40d072030840300380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 542041474 1250 542040224 542040229
    0x12102180c130e10050103050402030a020d0b0601140301050607031b1e021f08070e210303040308091b091005040e06250e1c0b15030610060516080904060b0304020f 72
    0x103e5000d60f02c04901d8000007802c20700150001c3c07001801c16a41840380000b4540182d03528500382c405c00344510a541d4842c140750b8000750400c46030301d11030401d004c02800107220f2a00d40e08140d464807600f600e000d407884181d01007100c12018100d10081d0001c100201c211030000a80d00017500349a00c240c1c4d645c1e00506180b41110844c0e840d100d20f000001d916000420440c920580300d1a00000004004000720a41c60b125060328901e25080023481303030408030400040c15040000781d940128280050700118590b07007480034000301d1400203144101f040c800411488013018119002620001d0410841152407038103443da1440202c032908004520b84a8a446200c00010a6890b144c5641c5501444025440030032844c20134043c0d185019081c18854100480d0417200000d00444101c9400c2d41d081040b01c003894203184000708001c00c0500940800c21005a0200440c3e03501c68103054031000c8a042440c000c2c0d0300d03104409103264814142100440c3c0c040400d4000d5000e1b5108a88110283e5066420b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 542042724 1250 542041474 542041499
    0x4032007060f09060f110106051c0c3008040b0f0903070602010b0d11030a020913050114131e020a0f0503070e0402150f0d060f0e0f012102180c13 64
    0x135035000403000d40f40a491a8040c001c03e84401103440b0000c40d10300d46800200395002c00d20341440c400482042e41103010300092105040250030301c004507a04010701c80c40714140c4520600f03840c0c0c0301000181c642d8002e0055440c20744001c0c08610108a984601e06404400b030340c0c0014003410320a0140000014144d4014450802c007080050071804850905441d12038284040d4071006806025280d0f4000059a51000e9540303d0311010180811800c0340703007400c500b11842c0c0f111078003418401c44103202501140c01c02002881c1e6201918a01d480c0c0c2140383c1c11080103a0031002034000c031015901103203000c00b048821f000c2d5031054080303c802c25520b0262078440d080545000c3c3d00400c608a00002802d5034a00a21b01c1a510b90011441c1a0704251350500300c407559402640c10f010206414001d14403003629a179080041c80c0c8442940354100150241603207204890354000b500782064440c115103501c100b45403512100c107000703d1540351500480d105580143e04020598a00e0000443c20214504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 542043974 1250 542042724 542042729
    0x303010b0a0215430309020a4a1627081b1c030c1a0402011103030712050720010203090c01021c030213080d090501020d030c0c0b04032007060f09 64
    0x7961200c44110f413840c1900201109801641c010035070100115070f180f414544240b480e40311100400a04480f168107403d5074256460f410200040304409100c4619550151608000d682000001c00800000c00350b072640303100c548a40b90412464240c41e054601072440e00201c88a101c1610068a0b8501d10400025103540c1c2296010b2004858052010303041158081014401d081040041ca01526412940c9042081d0307445014960001c0108550f40401c840000000b050000c40c10740c208460040e00c498a4407813400b420175076680004070b10740d1041190003802c421800000d0055900400e845000c0e501c216035a103114071446002007455480090703c4018401070910901040c0030a00003100a5402144a040308201000021625800070710094103101e860b500d454140c51f1030400060b0412040c02c260100f8103242c00003d0380090f4100d41c80b200d10550144000c00b04c0e0340c4034a0113442001040c03010122802e002280c8050181000454100762080c85c0c4504107084a440030440d040d407050b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 542045224 1250 542043974 542044081
    0x1140405031b12210309150a0b010e06040e0f0a1803020309040b090f04061a04020c010c030501050a3501090b0910020a0f0302180405070507060608010c020303010b0a0215 75
    0x2030101d0980410b8051900701100070180c40101012410704050850b060b110080230b240c1c4d44c0c0d14a41b5942e040013902c0740000042e5110b9040c14070b82200120742c014000d180015000c80b00700021840c1020390701c4407240000d481c01c0d258041c241410001d5903a0021000c0c240100e1402154202503d4402e90360f40c81220399804131a820780d6107980b80400741c042e495410420303038040054601d1070360f00e500150154a1050000141950580200505039001a40818002d528240c0c1c140802e0180000b5001c2408088090400e00407103c04d2040b02d64007100295a055413914100c0010490320b80390090080303800c001141c4c45039000c024114100d00c41d6a621101058121001e04000d90180d0042c2aa00161150404165460401040075250100c94400c0000d10000345a001c1081034801c520184c41d400000b00090641414007035941d100c180580070030701ca4086007031806107100300240b2001016900701500341c0d00308020205540000d01100f58803000b0f45040040a4250544010b01c885254 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 542046474 1250 542045224 542045263
    0x204080d0507030e03033001030203030a0507020d0b1807090c0c121101090b090d0e152a01090210021c050915030108061017070501140405031b12 64
    0x8200081d11581e00c1500704500f07104500f540b0000c296004d00140a2400782d0400030301c9290412501c900c0c5946007580c0a800d00070066005001613240001595001c051600b45199500443c1c0001000c01c04400d00050030b90070380a00300240e48080c20010301c0480c041c24115403504ea25200c00e01d0a86001c404400c0005251107a40000b0030f880d5090f0392031803001d40c20301e503080c581030419040c00d407020b60100355036244c00c40d014044424802c00c8000c10b03008407460320081500c1403000103100410381c10720210307100c180400c0707072010007039082e040c0380700c0700ca500010203911114084002c2c043c0080080030791181c600750022a00d01e0b800443c03036002aa1440c541c030700310541c2c5000155050b40100300c4058200100398040501d0016960003940a000404020880d034580308806000e030300710503000044041e00c924a000c0c0d440c1400200c0328245e410034206030420901d030821411b880c4c000e03580450381c544101c00c001c40884202d181480c03100c035800e4881101d600f07030032000c2583d00c0c420b011008038841d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 542047724 1250 542046474 542046493
    0xf0a080d02091503100e100b040e220302010e011107211e03051012080412020d150b010306140a210501090804090c020c10120e030f1c020408 62
    0x303999006040721107000301000041c06442180d03d41c1e580040b42e41200c0400480d509128036030b002d1045507070000d46030040c2c0e150340b8146215003105004910885250900349070100f824604424a400217001480b901e5004002e06820300a0180900794100c0c00d09506e0811000c801034103290440f1388003030304504a8440303400040d202040f80c1c8440a51413040203400403c40c4a480e801c489009410030342070754007203500d041682046ea030240540c0d00c0200d2460502e42c8200010300700c6000c0d40c048403108100d240c0103c659002045035440790103c01000c07004a5500303400b24a026a00c001050347c020382c0d00700615622003000b6801c440103140050b80c081170304001004400030744502030b4416001400d4810b81080981e84041c25550791200840b41074502207014055902144201043d828462009110024002c2c0c0803641c2d542c10540b84008005842219070650241da41005c9220a5000100c03903540d00c8588004415412181d42070600c01c030313840300d0006074039494000d49003074400c00e41c047c0243c0700c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 542048974 1250 542047724 542047747
    0xa12080f0c0f0a02070b0f04080f060405071509090c050c010b010f0e0f061201060807140307140a181e09050f010b0715050103030c020405060409261608040302030f0a08 74
    0x1c03c118009411441900004a0300d440c034a009480c145103004003aa44442c00c240700c2c41e00380b54480b080444103921090070440410301c00074481045500fa8420045a9107113100c040315482140d070040c0300d245082840368580e00354030000610300c0c070090030002c00c0002807040c011610500c040340c021b000102803040d800741d43d2814666244200a0041000e031800c42100411819004240c0c052004501980300700b000254001011061011207104568075514100401034111a5040340c00b41da5070300003081080b20640200c0c86030100c403410b1300724401c800340d444145420042d000e4102c045118421040010300d05058003c04d40142c555040c00c162a038281355010416800c89802034a20480340508100818072500c81c1300c4c080c5002e50381700d100160b90b50040c0b00942d580a003105008503d00107502000c40c3c01d052454100070385c0c1094842e002d00412109400501032851074031203210340c48040504000102e801013007264400d6003941d40c0d030320000c12003d031280c410710005085050200b00040d00315 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 542050224 1250 542048974 542048977
    0xf0102101a040905030306041d03071e02062803091119030c1d0f0105010e0103111b0304080f0313090c0513030807050715050a03050a09050a12080f0c0f 67
    0x200851a40342440000c014009015165000c3c0295141d4000205000d0107041c03600407a612000000307011317000d07098454151590303840791200140c1003183e0f101980c24462000020640c0242c0c00515803601d55080c1001402003a60f0810845002d85083c500c0d49180c50003030040141098000901e844401841c3c014001c446402d0814a4180018000c0110014025000040203002d1f01c0f40f440d0b00c442540e01d0584045000601110080208440100100da92144510046010038030b4045200c44008603d4002800707840c0f001c1c1a40040c40100d01000f81700000600102c4112000315800140c0e0071b0013081d22071040a0a64000c81d1f1520070a02c00012036400c4042103800500c2c000b450300b11401000301026541d41c00466468034009a00018040104041070242419441c44000314545401c042c0c650310440e01c0d00c0c03007030641304c400041d0900380542c0091101030b004419501c0c07000007490300c0001e24426540c2400070131030b10380106810381c0c20107180078480c0000f5100d6514005129001c0b2109 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 542051474 1250 542050224 542050241
    0x30b030705190e09150a0216080d09140c01080609070801210501050106110c0405060a120f0602030103060c0809060f0c0315030f0c03070504090b06060306060f0a0513050f010210 78
    0xa64628070001640c40c1040782e4151203070844001400381c05d140004c0740309100401070405078216006000300d071080e4080f0078208a601380c0c010303006c0fa60303540c1c01032001015100303035403000d040c201d401d43c500c08030498003066003908400260b807071401a68900c020010010016990301001511400041c80b803c07100c2c4d002c20100b07101c0c2d00d003c0030410300345503a080c0c01e440d002d8100074005400d05001059a03e0100584017582d10100c6040c850f910307245010900c5110a40702c0c1c0c148400305e91401d601800b018055001c003240d0048029940d07580c480c10190082c00c90b480c821400100c0c0200050a4144042521401a41a00000d031400d8440307905d60002900b000d40001c040f10106c042c1d500b542d0707030b0410000c094410b0000180c07803020b0a0b00d040504100142d40714600590410000f040060404080194040d10032155241c0300c1d02c500000c82c98a00034582d1400003000c00090020700690032501a014481d211600d03803d03c25190014041c0c84461840310f0303070251303104510107018001503800c070340c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 542052724 1250 542051474 542051509
    0x1020c09090304151404091506032003100806040b010e09030a0c06020a0509090f04030801140a0909170301030c180b1804030e03120c1c0203040614070c081507030b030705 75
    0x640703085c013441e00e5050f40e0040d07100b04900d44d5244644146100060b0800d0003d01440c1810048981c9840e000080c090030a420400d40502c0080020324111b00410920040d01001c002c6034854609440d007205070030400c4c0520750074150244001580716500004461803040703659180502c0107115503031240079411540080701400400d200701d50242c3c440301500c503c6a038244456000307605150802400d0000180c002d2f40d0034510382c2001980b40e0b15180b460004a4030300c1e10002821001d542400300100903982e003503440340d500010000043c8007031a0541c82c15203540001005080c2d144c041e44808840c4071075042c03900140d1600f0480c0b10b1500c001c0546501c18000d04141800b070070f50600090401d5038011a14900d08004200551302c0941008501440b00c4d4004103280440c1c0c14110103541c0380948c0c4204000c10a03920074034000b1440e484151412503034040081c1035056200c441c41c64881c1022081d0f0101072241c5400218428882d008243e889903014020304191820070007070041e5500c0324400c1c040d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 542053974 1250 542052724 542052737
    0x1a091f0b091c03050318010c170a0e0d020d031a1302070c030204020d090318061b2a0303030c2c030a02060a0207050102060c0c1e250501020c0909030415 67
    0x40c0b51502c80d60048680d1203030b0f0350f43e99641344c421120003556041100503065070789000c0014089a80150142e03150305085603100700c00e46c3d98203140034041d2000d149010614003c002c682c100c40c0740c00003000c0910803c1ca880c1401180381425400038412a6100c11a501c41c540c0035141196450303d40c0200700c410700075900c8001c241d482c0c1e0080347c20baa0010440c04111070740c83c042c90041c1680008a5000e2810807800d14516a14020f00100000756201d41051884401504801003021204000708010320707400c0141c004001c03845e0740a8020f40030784800d80110f4102018051498840d01c5040c031400c50013a8542c10008035184c00c00581084520080e4261041183c2c0e140584e807000b0142002d6035142c0c0c000e1100c1400c0c60002820301c10060556280d2324400d000c1102c5d100304c04150a401400b10311500d10a8042904615150842e404800b05c1d00580708001d0340700000035111024241c40081e005c4031303072113040c000512440742011100380041750402d11040c00346020a20001c48a07244030b28160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 542055224 1250 542053974 542053999
    0x504050403020c030a03020c0112050c0307050309190302030a03050c0c06010314030c0601240c0f0b040c150c1101050711040e031308030a08180d211a091f0b09 70
    0x5d01d040c440c41d100b035015074080d841802096a02c25020b01d400390346c2010030700850030300903c4aa40350101038404018818044000b49000302c0401c41c85005051050200b684c449480c1000303174032a4825a90040040d080c071001502101105040b1420040c4880003040943c1c81c54840405921190f94514201e0004120a14607500704020643c00f814480c6509900581d40d41040c114141c0400450000e001e0011a0303040858031610000c040d00e60094001546680d55203481c00c07000c213854001d03a101c80c4402200c140d5041e4007026810041d84940710410300b001030003005460302d00070440001c10004860284024904280c0c00209040740c2c4107046908050700b001c0c1c50081d02d640750300641d401d5400401d03440b01d025031000c0b082d6000b28140035011682d10b10810825250981c2d2900d410902040e82c2c6108502082441000c20042940208200301601002409902900d40391100e01c0303410300781c0100c2c8d03882e0602615146031010940a40160a1500b07001c000c440e0460100c40b40c0c0121f812228 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 542056474 1250 542055224 542055229
    0x5150901050a090237060306150305010e041e0206030901050a0609110f0d110f0a02010c030209011d12030a23040f290708030f150a351c030903090504050403020c 71
    0x1030701c5c06005203840119503d400c1074174007002c00c644d405c1c000e01010705000040018000340003055070450f402140e03c01440c03940d04010643c880d01a140203420003000403c2000c01e61040d4001070258440ca002170001c1a139500c1c0c0d030020342d07141c0841114032103010811102c0320009080280340d00d800c3c02030086a524610300800c0b105420010100b1810000007444802c116428814040e59503218242141005141d50000b082503510282e41c0d00106242c0e8010f1003540ea800c5103260490380e044044a95405602c40000d2100d1030803884101c6a6a0794206200c18100310010b0b5410b580ba041403c6a0b240d10301400b601d003800c00c1d01c0181c04020850301003002201103ea00074501c00b0300407441581d403400d289005950101c0c0091402d101d261400c08011001d68440d5043d6044400001d08403d0020800b101d180c018034011512107458840c0540744002018082a1000f4003010741500c50200d171000c130f5043e000d65081300002030008540e58024049032806a00554010f4040d1040b10070400c0008003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 542057724 1250 542056474 542056579
    0x1d0601081f0603021c0212070e0c070204020702090403090f0509011409130503161208070e0108090c0d0c060905060f19050712080f010605210a020705150901050a0902 73
    0x44007800750500080b00406e604101c3c080030401c007406001802c4251904e034030341c0e480c02c0b00a4445501e00c200000c5603c02d654454040c0c85201da0014400800d50406140c00b502201943c0b08454040344020780c0091685800d6454504a4036106500c000c0900c42d281040360311f140042c8000c00c05043c0c004c1032404610100060300d5002c6446d01d880100d0b814600340a91004e010704a40820020307501d0400c00410f0340030014024094003820302e2241c1d61036a8140c1d40c10320400300d0f05507400c109503c0da070b481030021411629003140da8584807010703190784075004d0119130300c40e0b80392003501c0d44410003401c2c50360481c0030140111000280b03455810a0304942d5001d14059020070800001154041407200e0f000203110f1791401050f00c0c3c1009442c24031411040c05681005102113100240c4501c005565903c9680440d0100303175001c4107075008150b100c1c0c4099103114056a01c10b10941c038000c0042c0002c0007510801030444e40081c200441030385126204a0300c03010801c16102c50b0140d00148504a818032103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 542058974 1250 542057724 542057749
    0x311040522030513170a030804052a0f0103020a050f0711060a020a0308090f0a080f04090c0503070f0e0906060a2109020f0405010605160c0305060a1d0601081f060302 73
    0x75903082d5105021150b00e40da0f80c1321a00b050400d500002c132401c680d0310700012a51000c981c107080080d0250380c0c5040c01c41c1041098528001400e84000e05111000b02154048036208000c44100d41031400e0100114124010140c1c81f40204101308040c6184d54401809810904d01c50408074100d41070000110b4255004a1070010269100300c1000c000c164102c14900d07840702c0c015000307188200b0400c01d007650381c1c41c104002901c4000c001542c20315450104e0100c40140000410078001070021000082c01580102d6a100c0000c408150340e80460703201d80c600f4448a00014401000c985891040042030b900000c0d601c014031000d090301e0102d01c00014560002000d4083c40080d80c91614010301041400c1e1074000780c4198a800d006003c015004025543d601c1c40340602075554448520b0002c2a21500e0707080505680318580800440701c489400c0402c1c0303400b00c4020541c04c00420011a65661828020490250450021130040400702068a0711000c2c1c134072800b00d4455529000f01e4107401c00013 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 542060224 1250 542058974 542058977
    0x30105012a0609060f050615191b0c0e0c090d031b1a010801140906012c150a0504020724020d09060e060c030403171b0a0c02030c0604031104052203 65
    0x1c075020b401d81700300c03032094990154040d03070088181d1406800781c403118455448104800401011410320291045107060400b24031002c2d000c070482001d0420b01200802d40c41540207009411000400c110154001d450495101819440d00b071142907406486865103440d0000c8031200e0340202601045d86101303001165801040e05070940c0d41003500d42802e6404440c0d07100202c0400005005188800240480c119403c00c96034110741254205150f01117150343c0044002d40e10407900b0310420016804610a0003841158001c902c0b541c0e4506100903405402d00c0503080c060001aa00300d0041c9000c030100200200c154010b1030000040321082c1262076400095529540d600301c2d0f11000c940030000706070460046030106003140f429980062072280f0f2000082e46128041e00441d10115101b50182c51030000c5a01c0c0303a85508540d040248031141c0100280c2c030a20a40c66450300904143e401c40d07054070b40184010003040119000d000c040c002c007800d9042c030700a00100341c0c10301d042d0001084144038403e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 542061474 1250 542060224 542060231
    0x3030106080c0d0f062102010c080a0c080f03091e10153305030405030d0e0a0c080f120a0e04050414010e1f02090d150b03070b0c12030105012a060906 66
    0x8019415201b41c010100000e80d1039102e01c1183d0260f0707042006080c40c0d0340d00c541c0341a910855800222804044500000c01680707000c100d5640d01c5204a01079481220303041c0803030b003034400e1190300c4220b041c2e40150820025000010203154540390354129020414080d513006081030354980c0d001000041d80c41c51401c0c41c1c29061103800e00940300c10118100c4101c2032504038114106070b2200c5132a8414a60700c5200e4070b555041e4215030000034003250702d0023030704801521071070380e0340c0c00f002900c036010012a440140545c14540b84190450810f4801d4415290703204401a500001404010040a0402c2d00c01074044104070602030024022000051058000303441071040c1160030700394040d82050300d4800e40b801481240300316100c00e080d50b007205801a0500c00c11030440d000780e000410030116810f0f01405201e0300132810002ca48010003048003004112540c00308031100d40c030740c0c500080c0a101e0000c2c2c81c00800c03030b421844110b0040ca01c2200391080c041c050b001030b075030941129440c0c2001c549280d01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 542062724 1250 542061474 542061479
    0x50d09030303051f060c050c0616050c0d21050c0726190f0602090d24060e150114031518060a180617010f05160203030106080c0d0f06 59
    0x7810b0043c1c1d500050a104c0140680c1e0001281d01d544030018080d880c10451085015000c1c0442000071201e0b08001603d003036545d5034401385510200190b41000d96807072090701e48003412818441121524280c02c20145084034110039030501d00d0f00c5071079005108120051140c41c070110310501c0300d0001082070100381001ea44000c4103062080000c079002d80e0b1150401d0052a1424410004c41c0ba0510b40c841001000b0151074a803010090086031030844e00420300c01d0406007000768081c1020380d031400b0100210200181c00c45120309584480c042c900e0343d1209580461300c1c4512003504401203880506250030302e088503122040c0550821580c0749207a821240c00c01c855030400c980000030100d80a03c03c40024038044000c2070b0050814821060810031045c004112600c2e647d0044001c0c010180003440c82c580007c410f103001c0d0907046082c1c0c82440c0b070301001c00c4408940941100c2528280d40107107056a00c0c04006444211000b008403128903000c2100440708500c0e4801e04c480041c180000144050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 542063974 1250 542062724 542062727
    0x18090f0a0b0111030f1e031303081003080c1609090507030204020a1b050c10050427020408070e10050402120109090317131502130512010b040501030309170c01080601030c0c050d090303 81
    0x24442c08806c42150030802d000c080d0100e01d10a817450703a01400c01e1401a10787c0784200342144241c0c1d00103094040c001c00e15215090f008141410f440003002416001c564840741d06400310f0f01020b1f0001c00c2030b8480007040006003429006441b5a10050030400c40720b0101d140701d0142072041c03403412981f68202a10341407075450700490854882d2414a081414141040b010391003907582d082414040c6030a40045030051485501250040c00c0540e051301c0115659881d000201207080e1410703081900b01010115850030248241d50b9940c0300100680540d03460300c007600008090302c25050b820070071008102800c910103021054040c4044a649107034482c1e05060080b000020901550b42440c010400402c16102c901c144105850048456000030907109240b14010700341c2c5512150460304020002080c140c001002c00c5c00c465015220300700c12003000d060161940f40343c00d00a40401c03180c001044155200394402da90204103030a00c20078911a80e12210f241044840b400030000700c451100b4400c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 542065224 1250 542063974 542064007
    0x6080c040914011d060604360e0622080a0c050106030305030916061e030e15060a0902040812361c0203060a02070c0e0a0218090f0a0b0111030f 63
    0x400c03100c544031064201200000d0140c41f640c0305000c0c003412605017032144900d608544110458090524000400901c00340e00b0103060a418a001b09004660000b062103907000040714001014520901c039072031041d69a0701d0203800a0141404003c3c503c840740c03000800034404d00e03020710b002e500c0e10758581c9030030340c0c02d185000d070000001d00110a07aa00c04012154000128540059070070b0440c10b900700d005013040707009010f0045201c00c14030035060a010360303440c1038640c180207010a44500d20080d44039481c200c268800e034403544400354804820380311000d2003507000c2c204541c0b44180c501c2c03010090100240512072410344040040b802065404036a08d8100c14154800e2070007049a0b0600249400107619400011b02884040d6000280c003004c00ca002d11030f81c80075255010b1714200c1414141c0301e10000f500310031840101005201c810b44420301e801c2d40e55500c541400d150f088007560316151508082c00b01004c405041c0007040500c480c2590051020300a1803030040c0c80030b5160504d40d540380991 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 542066474 1250 542065224 542065259
    0xc03030f021e1c0e0a0302120a0c0f060e1e04020702010309021e040b03010c050304080f04030203060103080d050c0c0c040f06051806030d031808090312040602010507180f06080c04091401 82
    0x313100361103c0782511500c0d80e0200101301c98044405400c032010b0100e44d2401d040500c04018040d0300d500300c01040d030000740588101918003980d41e94602050310400e00550b5104000000500111404c000c403040c80c1c075030000e000580c810324020031000d6103540820303500c420420043c0074000140c000c0c0e14881c1014425640c0c0900101c000703000321510524040c02c10f20003c0d2010f080300c3c200040d081031f00001c0c002150002c540c00340c203d03405036a4908181445800550b071201e9540e05200118074040400c400b0f0341c004140301e1000d0030b5150208800c2000a0a10501169185803240c100040c195a00d1005804e1400182e003911510301d0000c007054103040c4000146404e142c40c20855002c1c003600b000311201401d81c00000c2031794880c01c540000c0d00e064000b44418000b1000083c002c0380060781900310b40d005150589583c003520000903140d00c0a0896030083c090740c0d00d02c0c0e0304100f22082c841c0e41000d81042c00b80e000c41c1d1070617440340901c609550411b07040383d8907800900010084258000c0d0355151 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 542067724 1250 542066474 542066477
    0x18100203091c06021e0d0b01031a01121e0c0201060f140105070f1e02031605010f0324030606170d08040b0402060c010c0305061503040c03030f021e1c 66
    0x15108034000001c6805020307503249162485002d02800411181c0e03811a060340007185040c20b000141d818801010340d009108800c5080d06043d032203d20ba50090041c2c0701500c8980501c0c5030100382403001118680300c1540540a01d0340c888120158401881100181000e030034200840d19964462000e825200103a02030396a040042070f007004000304c16003400407102001d190055450039a400c1003481c0070002000901060655041146070842e0510941c0002c1d10945c04c1e1028804402d070007600100991042d1804103070703068024510f06100e030f804103d07079a0610503410910040001041e000d802a504219201560f90038144581c182102508680e14280c00062000841807400100107010140c0018040c5100e40040341c115503620f02590f116607260340080005d900041e8004000e0f01069460b2409507214842121514540108880c400c0c0d0700106010042499036804441070a00240650114000d8090103002e080d0700b1007440ea80d1307000003002010b01091110b1500e030866100c0700c0745030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 542068974 1250 542067724 542067727
    0x61401140d12080903040b0307021005010e07120509031b03130b0309070621140f010605040602031812030301080703031202091f0905120a11010f120c0c060218100203 73
    0x2400a1411100c0c54242c500520b00503030300d5190700c64640d1071809507800404c3d00020100400003101c2c4d00280000c0e003201c2c024420301040c3da9071210700e040b1030419510203000440c44080000040001d42029810a6460007140c0c50070f03a0041c3c005801803034502c85c400c500d41001484240889501844502810300166164550b052170054160356124030303c5900d0601038074200c0070801c101442c0c5241000b042040061144d43c00070412030440000c111401031001030355000205455204006450075600d5a070000e51620107041200902580c01e5141e0310342c026403120079030b50720007400e00c06540242039080042000030300b9850081c1240120f07420f080300241c814048a0125500c0e24442441c030102480f907000801083c52007100d100a8981019400c480013040380ba02d60714001400084e814081c42e402515420b12000450340010313032441a41c0000d5006802c01022061913111400b024071a0030811101a001d64a030410780e00800c10a0103628642c0380c1c003070901c1c1840e800c0500c0741c00d101d1004c0d6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 542070224 1250 542068974 542068999
    0xd0b1b040e04060c0f1b1b06031d0303090d0c0203030705010e06090c030615040f15060c030e030111030f0c0d11072109061b02060705010506030d03021602130906140114 74
    0x180320240d44500500c2140e80603003406c0038030080c0d01c204007162082c402401d1015494890140c0540010340d10001d111421082703000c0722880220690b4000c0c400403002e880d085600745c0007110000184002030382d2500007003020700c00041e401d22801c400345251401520141c601000c119090000c0c1200c8103000360040c0042142c5501801c1e11364162500886001481c040724000c400020884915a003581404c24200426040d42000d140710840344030707550b406040300942c018107090f17440c02c0411400103c014004903002c0941181400d521201c4483c40c6030421000c129000c06036080d01e8107849180c0340c0010000188070b40d29801a110311013181c0c0400c000244080020207203040c40c412102003042070212842107045000c04120510380040580351203009074205913000b40420b840ca00d10a00ca4ac0b144100454064000d07a580218003142c81c1024011a40a0221207142c580180414035915100300700029240e00c1401d00704a0600400c1c0b01c40d40c14550128038501c61505154860384050300302d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 542071474 1250 542070224 542070227
    0x607080f160c1a0f030c070606180e1c0c0311070902040f050904030f11072c01050a030c0339060905030c090417040510080609060105090d0b1b040e04060c0f 69
    0x1101d0801061100c0d04c0c0e5640d842d0105c0c511180105000105907504118002650000c1e03040d0141007100040740030480003501528080e980c045407007400f035401d0345904162902e6400390240629243c017904205140180b241082810301810340c00900341507902050a2180441c01e8444401030300080e94151503c1c00d054074050080058800f52504001c0e41e4030b6031070b400031014480c15000f000b40c22600f83c41001442003032603100606040408580384110000946172600c03c8a20040782d420501480513541551100141e0b10959080450380b1101d642e01c10941380c44018100c05003c0c1200aa01c00c1d03903090440051508007941d10040c030075400103450940c1030f9a000710550308581d00607413032002c6c2c0f8503181d04c01c98140030303d9120a61084240401d10000e5400c141c02d144a141c0071180100155100b10054ae2503000e28143c0c503400805501c1007074005190240c10940062141103c2c4425880440e1101c015500c05d0b003000c048428038505000c100541c0b4040c0300c12014190802043c99502d17481d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 542072724 1250 542071474 542071477
    0x7150306060c140f01020a1710030c030303020a1704150f05060a140d0f120327110109080f012702030c09070e06030f010519030309050607080f160c1a 66
    0x82c0035111503a0000c00030655501000341c0407071a01400025511140c0b4405c000d000d1980195020f451094500009010011440d804405480d4400d001c004205e045071030450003500058900028410502000f140c010a40d00004d03210f144070b0310320040c0050384c02c851941038450f1792140c00c1559040c8070034003069a8840ba009403d0750316a256100d00210000001000301d011075201074445000c1400d41420700c000d090052106d1300280c3c5060005102c46070300942881c201d03482c0d01030586207269081000408030081c01000e154140f500400c8503480d07001301e41c100801001c00c02d0b0103a5585200d40704020100849039070f14004940509440e1400d84c0200ba240e604076030038140f00d41c0d400000100e2440c00b0b04507800280c100640060b03240e1800402c0e20091b1402030185510600825180005000301c06081d0b0b825264107541d00f4100d58078140600a03141c102c0741084800710320070f001c0c1e10700c10482500034140140e480310416868210500b400071050901d600801c040010300604030051592000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 542073974 1250 542072724 542072747
    0x120f020610060e01020a0204050a090b011403030f09040e07180b0d0f12120e0a1e030c0b061309060209010908030a020c0904020f0d0605060f01030e0601030b09120c0715030606 77
    0x8014000d003c0c2140100e041a91800009500615150602200e08a1a4004038141307101e00c00800070b50b6201c0308012a02402c0c10302a40d8941e00401c6240100c2d500710780601242e20000e04046030080c0118005400c2294a130040c00504061540c4104005500d001ea244204410b03508000481800e0f210811b1004202c1c902a042d0080d002c1ca0301000ba110303c09902c0107003a10bd400300001c90421038041d4444190540648054020381d05e81d04c0c0e1000702c148480e4400b6419100d023401c110496964441d50440240080ea020010a021030804449402411101f0f441001c00590f41e01c40300d0000340c00c0b103916404c515000d5105000c2e0030741c03143e00000c40c0d1341015011900402c2036502e610001c0d070b075246c1d40e518550300b00b02c48003003810402241d90012030164508854600c2c126590038011011502c3c900c0c10356100f40c0c8040d00400225000c81030f51600030036040c0580c4c40780c101800303482d202039000040000c0c5503401010200946c5030103040124a8485924080c08800d1a24074010716240b40310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 542075224 1250 542073974 542073977
    0x1c080604150503071502060105060a0804020d150e1507111b030a06020c010c030c050309030d181e0510050103080906090301060e07180509070516031b120f02061006 72
    0x2500c1c4070001900151440e0700802e0000e04489105844518925400c0407813100100548103120003c2007603d003417003c1c1c0343c4800517560b0756826a562a002c111200c42c03400025981c040c04442181c002020501030411105440030040c429030041d0003482d081ba0384010725400c01c1010101c40303242d01c0200400c1983e14200142018a054040280000d0414a500500a00551001440041030001074205440740007550300c0410070b801120409540e18803040795802841d030010004496280015030040c64800d01c1d95036210716040c915518490068001e0b071204ca0541c450000e00c20400004010109207062603960602c80c07540755560700000e0307004025540d0320070300c4046141902e580b03003540080c00600c3da070242c100c00e40c100003601070302c0000f0602496056420024020495040014203070b07014640981e5801d00d0085000100c20203c0c2100800f142084150000300c40c2d0103801011100d41c241c00341c0c4070031284034140500541401c01e1111003038103640003a03040086c1004614120401c80705039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 542076474 1250 542075224 542075231
    0xf0f0a0807061503032001200c100e062a0403020d1e030503010f050f0f0409030c0b0705190c02010206060f130e0d0201180b130606150c051c080604 65
    0x580b82030400380c200180942582e1440c5000002815031028411502110080c81c542c4c050301205c000301c1c05e841c40b410381281301e0352182c401210020f81145c02400c14243c0e15013500d030541c2102221070203440f988142c100305075101209000074030b12002c003603003140c1800c0d0281007045018510f10184500440c4006031141c000010040f092264050841d0304200c002c00d05404184814138020707003c0c1d0802e00600c00172800142c000318160610f0b100109021030000d0602c16521215800c0202a00c440e0710101c003004100d48008002624625600b030081e00c0944a854481c1d800d0b20441c0d0040c060040c60b101007110b460b5034000580d0300486c11a40011098401000c3e620518021441400007889120b88240c0f401c0310003501110003003034801c02c0005550084c026010990040034a00d030107e000500701039008400300300c9031104c060405102601c80d102c0840c01c1030341c842481680c40404005000801c500b2100c0d41c4c10040c00384038410321412841c164801d6001207880040401304000c00c0c40e03004954 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 542077724 1250 542076474 542076487
    0xe0406021b19081305130f0e16140102160603090b1014010309050c100207050a050102070806010e040203010b1e01030b0a0b040618080d05040806092a2409030f0f0a08 73
    0xe521034900040c14006d4800f030108007400c0d031190b004100d050704070102c3d50b203070001d5880c2c1d4010200b4aa1103c41d00c4038a40000c0c6810070b0b10219880c2401140281503208680490307040d9280c000b1410018041c0b070f280000c500030a41064210700c0d41c0180420781c0c101d0202c00a10509001d46203180030780c0006e00e400501140d20345829481d055117281e00641c0b110415440000b0f00b135002500b0420743d0b5040d180c0001155880700103980d40c11040c06684010340140c40140640c1c036407042640d0740140020b0000c20031203054404180d40403900040ca01c500e24040c2c159800c5035816006608841800b80c880031a0340b031600700b8100090081d8003400c0104442415040114404d4080c8100036201c410305861601244e060701800c0c990103445841124091400040c1c41800080343d003c0004034004220494168612030014450070494022540110203050040c81c601c0450703a401c50900015042580d203080070002c02d4600b44070030b440c04030241e11000001a0201300820444001e035400b0540036242c58 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 542078974 1250 542077724 542077747
    0x60c04030f0f0c23030c030606091b1305010f020a02010806041107050f01050601110a120e0d060507083c0907030605070f111c050a090e0406021b1908 66
    0x422040014100f024503d02c04500294000c000404004012480f488062603035030515441d81c60601c1145e6050b04444001096800e04880710340d0f0000b00001d0001008080d840405e07602d0f00405054008045411003c0c072465800441e4080003400e140010a60070302035600003409403000070040c5025030b48941483c0e5101e008903082c0d4020039400002d950954645001450027000100c554500040079140c500310b000002040600e00b1075080000f030300015200307500c01e5510240138844650490010302c91040401e5640c400c0500410007075a03001464240501c0140c840b0035400b60340050280c00711010164003038100b00daa201114500403582480d0303609a4400e08000c0307542e00c0580f03010709000800c010740354440d080305520755080d190242c0d50749035016401c0d1750f9100e206614010341c001ca04156106400744c0040c29405030a468200c8100e40c030740030040001001038808580f21900840d01c82d100500c083c2c00ca202c2d02140100900382c0403139030600d001b07040c03040c2c00b00504000c000081d949c801c1d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 542080224 1250 542078974 542078993
    0x1080613060b0123031b040b07170904020d0902010906021f0f1509090b0a050903031b13181109030601060c260903010507091427010303080f0702060c04030f 69
    0x140013038a01d4218613404030a140b4515441100d402040c80040b0700081d92120000c0244c0c0d065413526450142400a142c0e0740c4032524015228039040382500340040b07111a03540380010940310324030020110340018035100140071100036403c20740c00d540101c41078404003e80714060004051030001d02042004050000c40020004444100d41004c0c1040001c1400c6000d41c1101400510030b030024403180d0b0b159103100d806c8440680d00700e00d55030820008140d403641906504415015001c21640c03410340ca00118440b0240940d00085529543d140007840c002030074465880c00700d002003800e03403500b440c0342c2c0021b8807603205004600c10310802803c01d006010203165000c5482d880007103c4007002154130105509600a190194801d40c03e01001405080c800d034940c1046841c40c07542c07059804900d0301004007070414180380f00e8a81c003171758503500e080161140c42d0900860080d185c9039554106040098038081c001400302055500c21010300c90000e11480c00c4400b125000418040501068034000c48003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 542081474 1250 542080224 542080247
    0xf0618150d051e22030c1b08010606030f0209030705060a020f1501030510060311010507080d0c080906010f08060c031f06020708070806060904060902270f01080613060b01 75
    0x75103003004104035032450102c021032803180140e00e003145030b48100d0b000450031800f107210022001403256010009016a08a03a0201e00c0303100c10b1040da0606a401d02d1980d0b0003503104035500ea466440c01c200540c1c00d440b40c0d4410402c2c504080d458007001c00c0100b40c0d211603500c06e00b401500001503440c100e038800c1c0410284980390006841d40d07150000908011180203000668540c011400a550081800e204503021254880440c400c409848401904d00743c1000b101650541020048429501080d00c00c24054070180e45503904107003030003040f062904805800002d200c40754100140007514001440d240d0040041300c1c0310790340307a50381119030080080204000d00b040c01203440110b080d6401041803000d90713054200315491240d07030759000340e6240070a0714256004440007000c41c012403190340180302e035a40054000c800842c2e210440f22041141c0358280c6034a8041a014409040d407181c41e40c0b030040044078028001030802210011444d001010002c028603a5401030020070b03400740f40b52108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 542082724 1250 542081474 542081497
    0x1406060a0e1302040608043807030908070506180f10021305040c0215151507020a050607060f0c0c0803061003060b13090506040e0d1101020d05090109020f061815 71
    0x12582d40c0c410002e41500000c7d0b4088806c1040c03050805140060011110102e41c0743d042c1042c80b80044410014080c100a4060400c064648040f0000304600c20001d0200600c99801840280341500030040d2461030800008140e0300b002868520b40d4400040c401f4101900101c01039a07052090300a422210f50360f07000c0c82c1c2003030a00150444a0b0f0300410b402d000000121410a420313a03642c040c03811486d0807030b83c0c01903021601c4041c1505004d8020007804900303202034074280e01f140e100c80004000c1d40000c501111260b89421a0f204642e00500580200d849281803890001039555501c20031030000400c07050144c0c08020301c80b243c282c400e0708204020103040c5012540d9485001a03540041140c1c00b40d0904076083c000414843d040622072504003000e050090803185030443c0049400b4010342402401c00d640034000c4100003001ca120b442d000340b00a10001070070304000e10602801c09072103904588180428001d070044c2940b00c1d580300307442110032150000000d91040301d905060080c00444078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 542083974 1250 542082724 542082727
    0x302011e091203030905011b0f0804080c0601150f020c06041206090b15030609120415120501090905061b04090207170c06041709030a110d02221406060a0e1302 70
    0x3010f141c0c050303108440060241c0f009114400d909090314a40034132001044000440100c1c86a0a040c4200c1d095030700684510440d40c600160120700b50718103030080c0c0000007981490304100d403126802c0021611040410300140c1041c940081c00512a801640718802c0b200c40c441400c00108203a0ba800581c046600c0343d031400b90341c1001d0070840086150880c0c900d000e407003070b40c010a0710303030200090040c454604200014645070034038410120520742d8810b10302c144032011304000984030490160b1406400e04030300000d801c03c080c0c105180b600102500441c01100074055111600e1540f1084809031095801e0250380c94140e4908200c424130f2442c00801e040034081101c0d1940800407804a01980c05a101007006008442002010348a410700131a8580e102c005107500142403d01ca04000d04c4c1c5c01401920340801c1e5401082e8540702d10103142c01034a000e5183d000c5d00d80c2652145544240d07450f0f007401074a1030b00e400801c0c07080c81101049024402075210005a035900c0e0f80340d100c6810041d103000d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 542085224 1250 542083974 542084009
    0xf0702030903060411040f050f01151713030f1817121605060609090327030a06060e09031608031b0706020a0305010b0703122a08090c0303040302011e09 67
    0x85e0b03181c071a0000402c1c41070b400c003d40a8562103290140ca030160841d4000507010703920744000d01040710130303084505050000320b441014012b940168041c5c130414004081200134643d030716000f0040d50107143c2c11000d00c0348040d90607044520030107c01c8103072441c900b40295640c003c2140b0a16051800c10005594a0000780120018403010440c0802501c21800c6404c2603c0381c4081001442e02200d082e0f51550081c0001c0c07141c1b6080155020b0682c80c8254511075562001e404030341404c1c0d0410082d80d8440d120311080003d0140040c03059400032440f4090340c00c0800586100c81284101c00e0b015001070700c04800f2130001120346600380070400c102010641c0e14040d40c5890400ba41042c451200824a80800041c181001d10202c5d4025503150380d811030070381110003008008001e080c6c510504c01d00340182d04000044080d000360301c1c4415503295103880d0710b020300c0300030318203051140a50300a41060208000503600002c5a50741c064440800c00c1d00c41c200a50215072090f103c1d03000074100511030451 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 542086330 1106 542085224 542085233
    0x60c02090f060a1802211b0f0906031003030207060c0314031801020a1d030d0512090309040912030f0e0705010c0f0501240f0605030f07020309030604 66
    0x280b0b46961160001c0050607420344031164442d85c00034110320070a0540209011810302d928502c04289411003299080e0585030303d03881101000450344504c4440341000707a4104850180003240c0381e1030030310200744403540f10b4030003030300503018502010070003d00c100014442c032501500c550503101000e50380410580d1000708035101c1c400c00c0c00c0d612800d501081c00103201d00c8445035101c08006020300c00c00c6400b0105252603e10a0703100e400f041a07203903045400c1d21582a080d41404201c0e40d1500d240d82d0640c0f01c1c0081040c0d005c0e02c0d26550070208000240c6203800b003180d5940401c0f50030440d9202104031a10300c2080e200700d80c07100608004544c8120100164148640d190f075401d140d107503079001e0950700c164103550041e4040107000e400f41c9900801c802c006200c02c41e0702000c03040c035200740a022480007a08107203000003964001400c2d14002c004440d440d000280803200704d40b030715040 = true := by decide +kernel

theorem cover : BRFrame.Cov 541906474 542086330 := by
  have h0 := BRFrame.cov_init 541906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 541906474 ≤ n) (h2 : n < 542086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
