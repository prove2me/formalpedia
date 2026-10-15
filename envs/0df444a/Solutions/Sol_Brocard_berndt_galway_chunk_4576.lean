-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4576
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:03:48.30852+00:00
-- url     : https://prove2.me/submissions/d5d42651-f078-49f9-89cb-6312cad1b5d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 822841726 ≤ n < 823021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 822842976 1250 822841726 822841729
    0x80d0504110102061033030509121306080411040f020a200606190f0e01051c03021e070905041515030c0603020310052215030c05100309021003021305 66
    0x594089910602c080700f031740e104105086d40b50307a4580303001c00c00114000c1c0003820512400b00384055110f4080200f80c5070000d0083ca40c0040284035a010602c8074440d00b44251980c0c0b403c00d104062141000708024a00802c052001034014022070401c008c0c410841c000d01c0124010203500100250303070110f0140060a50803c81c0c8078041900c0000076809448642d5559080042c03200c0c18400880a4541c8480b011582d11a842c200d40068070058201a605600d001c0c100130403085081d0f03c0d0f2601c05c0c200040c2c3c40000345c0020f5501c601110441da2026130b0f1012464440c50100281d000c41c0f6401d0510302032001388071801c006c054042006040501a0204040d04450015000c0c48002e00d000103081041188a02c650302030350300144091100c0b83c1c0c556480c8009440601c0d4258518107072048181107010f90f400d41c2c400c3d01402c661001003055010310399202c04503500c1c07141c41400d000d50b51003a005011a03201394019603031182d00403c56800300320304c424010000e42100f000024003071800f903c0458a0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 822844226 1250 822842976 822842983
    0x605030307060b0420042d0602011410080d0c03050f160b0a0b03061914010e0708101220030d09080c030714210708010f0609090c050913080d0504110102 67
    0x114410380c5e00c1d480c0074030740b2805440c40021042e007001800140149002c1c92070310550800003d20309607001240041d00050b100411142c0641001c0c11700082010810080e00082080101c814860404011001c040d0a0a4440f44996103070b00c0d40340c07040040c0b0854203c2d40340d040b10b40c880d030080c541d40303095a0729003140d0340c2101c9400481d00e0f4964090790014040614810b10141d010f5020400880c1c20055856031501011082e0401d0200c106840200300015510509656008844445d1071514a240400740c120340c2020843c043c20780c603000c0a001e122124000c0d4030641104001e01101c0c0105034101c0001e2180f145402a0703900303030040c1c2c001d0041501d000a094070503103e0601901c080e01080710304100d445880300e1208015844110f0700d03210001b03018446540103040303c1c400490030200d0880741108607086500302d418803920740881e440100386541c1041c029201e060301c02002c140c541e092400a2002d02410060041074000707642c05034107260b5081280107522601e00c840032190104016601c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 822845476 1250 822844226 822844271
    0x301080d110133080604081908040c0b0904020c030c03030106090e040503090904050c031b131b0c1a0a060603060b092803020603130b06060c060106030f0605030307060b04 75
    0x7460f0384041c0c0ca100c01c0d401c0028028104003191001c142109a0b07800380f25007000b1081342c0a07118180c0120b074005001c0b5030306402806248071854000c0c0e80e841d080d40c400c00569460b004008000401003440c844a882d5070b81210044102502200e4440030450f540a030b4a90090150b90001002c0000000b030344600c03a0b150074011507016000d54140103511062060084000b0003d8506124500d030a1207a610b05110800254550030500444428210280860195500d4a0341e00300780c80c003048840810341001490032002410b14040d8425450b60500603d11340d20f84d0000c620750507a8005200720a50642d00c00e000311001914107000e419640d051140440c010501503035003001d034042802c404e42d80d5000440d085401c46400702c43d00542c8a40101e803240d04200c03003200d04044c22100e240203011418411907405081112401d107000500351640303884a9040c0306070401e154079003585000800c480c0e0000c9020345400fa00310303901c0708031600b01100074040c4003e90b140281e01c4c1c8081031f03140200b02000480e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 822846726 1250 822845476 822845501
    0x1c060317040e07031503140a0c080703080d02030403020c12250b09130f020a0c060e07060f0e011403040f0b0f0606040605071b0f030b150d0b15060301080d1101 70
    0x461540c0c2c0d040702500545014170071045400406000440020a0000c2810036501d50b10001c1042c100f15251000f100e40454010701440c0e0302441080001030401c404070307107488d40303410000342e201d032030b40c1c6401d80c5001001207419601c007030f200809052105001801090b003000e007001100400e080202e0311007940c034490040c00c81d411001c00c550070031b42c1411000c11001d903105410004401c071780a040d282c1203070440000d4a001404031440c40c2d0506c03215005100508000d02c0140155034075146010700b4402c10002c1e50014800c04014a190316030003a6040b15070903000800701a030b1380c035062820140c2c4031400c880c02c0340c102d8620400700e840c0c91403082c500c0744901c0010300202e02e01800c2c4003091b5219046400111b61001c413640380d001d642444466282d0080200030717424050b2030b0030751425061907000202044000072480712851840e179120308840f010f040d0000b1010f80141c444203140d101001c1c2034071000d50840c80000001582020005202651801c0c41e40c032500e05508030039a507800e0fa1118030112 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 822847976 1250 822846726 822846749
    0x60c030506010905010e010207081f0e0f030901080a060e0703020702090f0c0301061215060306081209010504030b180138030312091015050f06090310111c06031704 72
    0x600480d405444041c0a811b814011941ea041ea10100c03245800326584440644405628224a0005450143c42601c24000c0301402c192028045100d50301d009400d1041d0400c00c414001c00c01e200016800000a4030b021086c0100d00e2070f00034070240103035204540890041311100c0024508515440300c06000d031174007550b1a0b140d070b482c081044500071441c4003044026690398a0081510040ca80440f004002e40d03100410001e1804044606044480c142c11010202c1007005584686e8400f08440c20340394071080072407950721045920541c0507030f020502a41d66203400790fa00d00b110501440381c01e0503c036416040744003010041c8007104001002c0e44150300340d0f209004685100d54208512503100000404540e8112202c0e0000340c2955084c0d24000d00821032188240443d043c082d41c080400841650740d00d20b041c1b414004240d4821003813031141d02480c1d81d4101c482601118030125416402c1c1c40c40d400ba085554990b03040c0082603070f44021661034040508042c0000f8180040c1c03009c4030860f0410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 822849226 1250 822847976 822847979
    0x1051e090115200c1009060c08181011070605040503060f04060e070e0703060504110d0903140c0601170a030818030904060e0604060603020f070303091b060c060c0305060109 76
    0x81180450005080074000701100480407543c00308800c80045100c000240050300034041400300042540c40d456080010040c014004141c0058900e5801c0b07500071101540e89134200e03206003000340d640c44115481000b11a070f1a0345c096101d034001c4090035a44060720200c5580e000c041d1500d00c907511920b07030140c03c4100056a501444202e05074098080e18020030b1544c0d404a40c18241500754024408410380c6500b0f01030b5995051050002809082d2402c02014406885162003030140c5030140e0944c0e034588203600b003007500c40d962030402c807404400d01685407090891a144c640400b4043c080b10f0083d2107402c40c40454001400702c4446815454034029621191241301e102c58144441048900c030030004071801c0d850700c0c822034009040070894044141040d10401041e00c2180d0310003401c050040c070411001203c058111441594581130005910b4031600c0c003c03607004e14200001602d4504090300103512a001000340c01050300c00c60040101c22010041030341220425560240050b241100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 822850476 1250 822849226 822849239
    0x7080c01031121040308060a03030c0b0403030b1509040f050106090e1e0403080103031b02060d0e0709060b0c06011a04030b0903270112050108030901030203041406040b01051e0901 79
    0xc00e00c0204680b0042c64048944040800ca0a15001001c00d86216030200010b16034045c0e01281c000c070007151400c8055207107443c028400600381c100a4003111102c804942010300a5012200004000e00f0004101d03120445030502504203100d080c0c02103007440220380c1541d1143c840e80381650705e1612048100740c01d10f440c15140c2c1100401d2036402803c4c403409081d02da0320100c0c155205900c80e6980e1209503041d40f90042000440312080140c81081e503004800699815040e42c0449501d03c000080d6201d03c9034102d0700d805900d511400c80c2c40c1c40e115010031070b031044030010401111100c040710a03a1366950300c41d0040b6010307851041c0204c07400307101c20f0000654401c00a1b40025584e82240e0410520602050141c1084108c0c0c02030f2100d000714400035540c0042c48500746900503442000298503001c0ca494492143c1c0311801e0405600100060400917061440d0007800352083c00c50750a4645844c150504560a0040c28820000d0740c20342e2514500c3c0700c102080150015220791103e034613010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 822851726 1250 822850476 822850481
    0x30b090f0a1a0a1a0c2d0607211805010507021e0703020d23070302010201110a17040206070c0311010e0607050a0b0705041d061201200309010f060b0315010207080c0103 74
    0x20302d01d104c100000c0061091002d41048420322030b041501b0190b40e1103861b444680d141d5011080003d0040d0401da04000740e0300d400240d4421284000300402001c44a0400201b000b0403401c2400354a10b00b041a414007030000560055220f1406d0f80c0840f020070240c400c8450410884c1c01180300151704c410f109100501b05403a600701c0c150b2050303c01240b540b80380c02d40340d4072204201030750241950140d031003041591303424003442034000c2c44000600d03d4200c62040043c5000f5a010a00b9400b00429010504640f03400007116079141c0c00031414241151246041c10030040d18200443c001079000151281c3d91070203000702c955041d840700041c01160301d1035070740151040009011005101040c0f10000c1c0c006a02c0c1140447e15a080d20030840b2450400d042028078602c2e01c501d074242c4e138904106000c00d944172154407079801c0c000889440d165501d80c61010301404030100c0d0080001c1c00c20000040d02c91032580650f02030782a6900310041c0c50b01c04001240c0d216071601c540344040c2d0040c0c0e203194403940203a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 822852976 1250 822851726 822851759
    0x3110c2b080921070b0a0c0219030f08030912030112120c0501110702090c040f051e131d0f06060d1106031006080c0909040204020a030b090f0a1a0a 65
    0x40120504140c102d80004403c074a82110000001d42c881400300700e030201c14040800a042c03071060741401c00403080310003041c090a40e50028098013041e00420040b102484044005540c00840c4042c03d1481d403511a034683c1080c5c0740d82455101c8c40e8071581d00e20f04803400352810b03142106011402c00b0425142d50b0028000841c1c0070081c45650042400480c00c00c0c003e801401340d81d10411607440c0803d20502403222001080d4040c0d51000f40424019003446600450071034a003150062842c181c08040250344105450401381d0003030103028104103511254120f0106502c1e4410740d682d92071184071441c0d40300e48030444910007503046100065400d203000507140f50018010b0703010303903810790b0303204046051544181c885032000a90702d001008603980c0301b000507900115120a50341800101b00128240900280c40244500d802003900c0c03c034944203910211490700c000740300e982d150506804840461310706807444c085481c03d10368002c1c1c05001c241c500c0740b64007401034080c0d0b0050b031400d20a21000a080d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 822854226 1250 822852976 822852983
    0x3090a0b07170f01080d0507050705060309160305010c03110a0c0201210f1a01050408100b010e03010f05010302011d1503060a0e0f060112091505100b040303110c2b 72
    0x2407402ca03105003440400507110b0041d002d14039460f035040688003490500501a168200f020400c000c0c0e00050020688004895064440c192030303031074a02c1014207003d040c0c0c1006a0000042000009000054120102c84040e6882c204020840c4041011301d034460314124101107a020590b03540103511802c80201e210b0445c82c64400103c045403d0001551030607800f400036141c4682500c555010350360107012422409003081882c1600e004d941c00c0d101c2c601040c4480d000c0703580e8040d011a0380d00a1300b9456142c400100204a01d13401600d47c1c1d00100400c0c04141c3c0003908080d0407030124000c1d00013007460950000e000c10381e103141c0400344104960000305202d802580d8118001080200300d58a02d001d0480200d40c0780d994646030000426480c0359800c0c10305100d007000901c401041d0b04418407000045d2011001c500740e659203200039101c940380e80c484000b00800060000070306511a00c09450138001000751680c655418040181c1d083c1d42c2d10b9003245441080940c02c2c00c55045404156040d4030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 822855476 1250 822854226 822854237
    0xc020906031e010218030c0109090e0718091b0b09040504020d050303040b041208150d06110d14061915020c09070f12140a0b1318050d0503090a0b07 65
    0x581000c80242d60307211030054801c680d00031958007000c0c0d220b4400c45c0c01c010700c1540200707145241840000d01c1e00c1d40d2440b415001558550000081c1081400a0809002d5102982000102c4c00015100414a420b010b42d2400003213400d2400c3ca1009003171510031228410102c900f0300c02103c041000400d4080c0c0201c0c1c1c0425040b01d124000768013440510700c02c4d80030307080311842072a250074003400c540c0c2c941c1031080421070000c080011040d00c0d04410840a00140ca1580c074040f16458070900414511050062100022900200d489802e40040608010100e16101941c940c2c0003449013a90911a8854a03c0c2d11904107000c50f000c1d8000454201c0c03624411030300060950400710703005050130b5441350001011200040d200e85d0b04002c404114146041d800c000392084010301d06420200542041044c980300d241001183da0740b0440c0d40b1500d035503440200003000041c00703d414801d004e5034046916000362185070080714040d82c182e91150a04001504070300b5580d81d580350808000805043c140710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 822856726 1250 822855476 822855493
    0x9081b030c12100f060312030b0d030305060f030604060e012301030318091a0117060d110d0503122203091404140a0e0c0f0307090509071208071101080103030c02090603 74
    0x141401413045442052030b00144403411030900d4265410460481d60034942009a180c084d078840007907642d400380d01031400180c41c1d104c03a400105d58120a504803649803090360244001e1010951182030100b00c1a00200030245800341c51808040b61603141010305070490004101080c05503c82e41e00101c400300c1c940e142c0c281c03100d6418044603211070350a418650300c1003117030300d41d56008481d2803001e0143d0f004604d468a00040082c0c0e810303050031001071520214048141043d10340f41d00807088158850290707600c8011840d001e0841c100f04852090181c00b42c502040740b10760790022055290764141d50764003d0745041840306c840c89000c0c00081504181c1e1003c10380701320300b030b0080b10724040e4107005070115269504c010786c0d910b42901c025501c3e100d040c040804c50f41590300000d400c001c8406152012030315a490050007801c161072588218012a03503000380a003048008402000100e2050001e1000d04014600440e020076090200401040500840d01c000d840c0c0030750100c0e48114020203c41108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 822857976 1250 822856726 822856753
    0x702030a0b1609080316140f0a1a010602120304081306030209010e09060f090a09050a030233011214010c091802030c1c0908040609081b030c12 63
    0x2041186080c1c40784400380e814800604101c512401c410b100301d2030801241c44c01c260b1800e44920032108045600c01100c1120400c003d01103800a0b030070510700083d90104c03030b02c00018540764140101c0c12200c00000030030030302a406a20548606840c0a9801000b024100890f40f0328151300140c01503610040600050600d0000c8604d00341c0030b84166600907031110700100c009041d20001c03119443c49541807900700803540d2903850160b0114201100c0c07030300060700c1e04151a0010080c915000d041d41c00b51034225020702d0f400040c90500350515040c01c2001d19442c3e0018034150303841c0e00c0300c0a4006100001041b0b000c008090440103135000741034070f42c000d800c01c800300d42c2100c006a5210002c11100c11013007041500d40c0d00030b04520545614194079625005440394003504c102c440b40b52010b41d00d010070040c884181d9011290855020140c0c55550b521628040c0511650748103900c80c0e071250040305540315209082d8603002e02c01c090000d20901d004001000381920400790b0003205d070311501c000840c01d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 822859226 1250 822857976 822857983
    0xc03070c2a060f17061003020f0d050103140a0201081914100f0e040f030c15020c0114010914040303021c0f020405010f08010608010b090f120106090c0c26070203 71
    0x8103105050741c051a104010b0030f1008801507590074080307884502c0b03c0154207000f000d54003d8045802c10004e99144d2015030013401441401340c1000340120312100c40860903400107058a004a491000701040d81c480183d9034045404003d00140d07003c008902c07001602170382195801490720000c14111035a14a10307902c44000c42d00c3e4050b528500c2c03810407074150b000c03241102900c807107200e20100d89403607242d98100e801807103002020011940c15220a0000191064802209000c000d5503140d95020f0f60354041c010003e801c0d602c001e40b10703000060000161049000100ea1440c845071152341726101500250840c9030720304011910b01d0648511070015100d4694201200840145c4031414840010039140310303103002d0000d1002160040c0040e0750480882d80c1102c08250103166602821404941d16240d002c5044e500000409026210b180040d0841820381d00012000c2010070400e0008880c190140c00001c0c143e82c0003582d031040c8401c000e02c4640100e07083c40804500d046000c0c1d000c07030315 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 822860476 1250 822859226 822859283
    0x2a0825031805060f030105121c022802010c0210030f060b21090a060f060306060902030a0c0201060b0919080604030810050f060d05070e150c0f03030c03070c 69
    0x301c000c5101c602000e10704020201a00042e1502d50070030442c0b0b9101c12940c070060203140d20038654044e50540316078003040010700c117076180324114061495411000e5070f103c841e02804141001d51107001003903000a413039140209034051b074640084140b030760207000040c0c9003104480c00301512844062501212805400003c005030740b9615a02c4648100105881850320340c81c5400b642000309001d85903030b001031000c04444d00044005104d582c80d14481c4018503099200900c80c40c2003a9000480c0300840e4055442161048001d00511600702c100700d088480b64001c40c0d000e900c0c1808000c4003800c06038440040d0340c0d4001210f208041d103072140a03140c0441107400b140011400c0c401c021910740e203001403800905090301c4042c030f190302030f600003110b40c0079103804c8000c126a0f400000356200d1003041407401241c0701070701060110310f896412810a40c08a0079040091061440c86084d200000040b00d00c100c001824590960719485421204409003800984e5032503022030100000301a80140c1e1f22 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 822861726 1250 822860476 822860483
    0x9020318160306050c0c0705100302040807090507030b0907270e090109120c03090b1c060f05033304170a02030a0311120103080c032104032a0825 64
    0x1502a02d10314000b400d4980061140c002d8101c00c0c00094001e010000700c0c101525001c480ca40050306410340c0840003409543e12039101d81c0300391500003981089940c0468080e401710780d402c1c03010918581c284600c0c10340541d841320004e01c06102d40c0700300088041c4145010703030031107d05841c0d030740d48d80325015203440c41a181480d403a5502e103846c00400160b014900c1f00381c0303003506240e0361003c425100900713007680701d2050400c600c0c400154840340045040b4040b02c0c0b80b4602d003041000c2600e80b11051008030b05030040c18028451711343c0354140074407a2042059a55000c1680e95004450344100003840e41028000302c6609800000848003100340c0c901070880b520740d1360300450f103520202030003c0640c4e114501d002e8064008100e4502e944800e108040c2c1541d0b0030420082e0b0380d0903120015407441c400c6c0c00070308841000340300c00180141c0961800310b000c0ea00a560b100c43c4000394194000c0b4004d011403d602c000f0743d807901c64400180c01d11028203040d02004840c1c01c000c000c181e9805640400844045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 822862976 1250 822861726 822861763
    0x2b18081b070e010501050a09050910030203070605040b0306100203070c120b070f1e0207050604090f0f0513030c020307090207060906050912070b060a03051f0515010909020318 77
    0x1529961a005040d00901092000400626107072101c926003100042c021141004030003d0030346819401024400018007015040003410710344000d071a0703080902401b040b4400c1c00356080015200c0d01c14415a025607501c0c1003075611f9034851104114600e0340300b404e104254003040c0080c901080b180e905010045c80c42e0710540710074070781d1450b0142001000400000500a65114603d249944140c01640c0d9846100e0300362104002c148041c4c1c6088441da2009900c11400100801c8000d025000040f0b40000d008090065600101c1c0803420303100c04681e400303e40c50050025002081c0719000b0564001c3c00501510f2010743c81d00340b444183d0340300d1f06050314495101c0080d00208400e502c00d81d03500c180a900035120684030803054100c40d2042200c041d12410300200400d4a40c0e41e5554400000c650081c1168505c071090041c00c0c50141da182c070749440c03541c68070740000c080c03d03001d001514200c401603451803005801c1c007041c1c1e0700035040600305594400902000c0120100c0810070303900015400c0802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 822864226 1250 822862976 822862987
    0x402090612071221110c061201050d210e01030e012f0c0303180609150109110408060406050609070504030803190902030d0509210604021c060f0c090504022b1808 71
    0x11841c00d1ba03854020780c064501013003c821030f003004074906810b40b24110781081c210070013030408032050100b43c445400304c40d44480701c140440d40c11407281280c082003038909014580385086460300700d502400c07804071a00440b0069510250b118030300c80031105205800507040400c6800d00620f1a0800c0354410203c0d00684079019440c0c4c0100540c5901814607401030204032a81d004108001b5010310650310030a4880e892008044100ba003541d01819290003107541034507042c00c040014102c02d5070854000e1060710042405503220b48112015290024840b52540d1117800103102c401003624808550f40342d46610070300040c0e0b0140700c0000745403860740e036083c0c0700c072651000c103d00c03e202e620b0400c00c50020301c81c2000103034030b0104183c0d07401038046400119481e541b098070104d02448000080c80700b86411220454400c0c039502c1075295942a40d03c20302c11a88450502c0100d21039420310b90f5280740d441840000e040d040900005103444100345c0424042000b240111f1111f142003401ca441c1e0002191 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 822865476 1250 822864226 822864257
    0x903020316110424062a0b040b070c080304150603081204050d02010e100c020c120f010b010f08040605041103070e0105030c030a080a0e06040b0a080402090612071221 73
    0x1c210125001d40055a08907040800035481381c0801e1140e401480300940040084685121580c0038240000135002802009407500c10840e01d0304840454481c0940c0c00494801403140ea070300214184d100122500c0e58980382c072451651252942494601030700e031400403001406100261040301918a5600024141490294281808542007000f16031401c1c10444060800190340d0480003100d170360010b640c2900000880c14546d042c0101c0341c01402001d905051088000749540303030304920000800c48480d100d03004540303010341c0c00e65080008440340041400b244555001e035800900ca811047c0e20520000d0200c0e00b803034900c2e4018199055240700400c507500301072090707446221048002e01031009455171601400e0140010b140c0800c000d01c69108950b485600840f0040c040000c40140c8604000c1c900408040003100c003240921640804245d1600f04130550002c90314039032001c0d01040b070514102c41300c3e12080c0300d402e4030f03000210201216400c00011101601c444195a5803800c0340c1e034440e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 822866726 1250 822865476 822865481
    0x120513210c0519050d1104020a02030406030b0108010501080a020d0b09090d08061507080c0f01060e1e0420010309300c0b06130e010c020d14130909030203161104 71
    0xe02c0180035400d00c070f2074010200c4248850030b06030b6004a640f62012010350905200d03900400074115001440051000300040d0000054011104140e03400d2003981c5609004595541080c0300d80703400f180254000c00c01030800c40d00070700089150020001052094040010011002522401003c3d0081c10410382c120394011b011503805a0150391484000b02584400700382441000e030054050003021400c11942c650900c16031640c00262030080c0a50380c1c80e1120410704610075548148000340c9204012a0744911420030307841190490800300c403481070034100a80c1e48400010141c1003569914040e0005000c2c0c00c80344c0f0b0032182c2500e4402501d00613901112801c81084502c00070300c60081401c4001071544110964000703c00c0d1025204405410f85810203016029007440b100d50034440300d4240d441c1c0c00200726902079030503030703410401040415441d00076100d401480790812440c03010901041401e9000f5205942c440d03c1140d240580500395004e40c001091000c8540c14403c02c03c034600e40c035050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 822867976 1250 822866726 822866729
    0xa0519030209030d0203030123180c04090b01020a0c05010305090307060906050603190b222901050409050c0409020d050d05070b060108060108060111101a100507120513210c 76
    0x45c0011440c5504004e0344204c0c000740d4040c9101c0c4088009480381890311440c05040160311122955030460600c0481d120780c03900316004c7d8140061800b000d280c0c0b1988002207261050340c00075a004100ba080030011170140c1001002100700340f0003045001e002400d540328482e0301c103000307110018a0742044400c15042c1800d5030f48001e01c90145130107103804220001e1180342c000340e01c15820300c581c0070020b1008442c424040006001080c030424007441007084448030040d407000b0485001e086a0b280da00f08401c8070783c1034001500302d50024821401c0c5080c03030752011403224001030000206900950780d1903c0c0807800c60640000030b4012a2050801210290164003d0f200742044520b601c0c14200007032080000402e03c03810465045800580d10300c05008904003004441810b200c40d04e411840101c0007080500d600340030b48031980e51494052b2103842515038003648070021121442d001e002c121017a8020110070005400c0d1003400107041e0010000f070300c1700d074040000d0515a140b510b04041104007503e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 822869226 1250 822867976 822868003
    0xb0303161712010b1303080a1718031b010b0d121b121b020406060c0201020c03010e070b03150915090603070f090903020339031e0a051903020903 64
    0x500403107070341000d01881d82c1d05403a03501040f5902d808030301941412101c5140c1c4090b100080002d04600d00e6540003403589160700701418400c0e102d40b40c0001300300c0c80642d4a003070150190002e100041d480d10079a0360160b8080c03042000440e0549055001804100110b07208482c01c44440b07101103080e5030000e00d07428840b5545960a0812400350b240c1c000005141030441c0100300c1c0704920114842e0700c81c10741d01d0307882d60050420480c280d1241d001601031242c0700c005078050710404103411041c1c90140100c00138580300d40040e18226141c01c0c540056904098902003815681e040010900c2d284d050b0080e01c290411051254429411000d00071424000350207140a0341006009114410ba60142030003115540c0100140d00082e90030101d043d030207640100c004800030382001500d00c0c0c03400c02d140004c01c9440c1607090303401c20b80c035040c06a903071107807801281c1c0c0c2c7c07540d05044250000443e8040e05000c02c2c1828031601e041e07002c14410800040241000c3c010a0f0701094000e4241001c000046012030f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 822870476 1250 822869226 822869273
    0x60b0d0e060906063109060b0a09020705031602060c161401020f070b0310090e070314030c0d080406060305011e0e07061d03210c0114060607021002010b030316 70
    0x40010109280f00924130052803161717081800d0350380e030030381e0f07014003e544a4aa90003004080018a000384c058a20702100c0d03440380015172004a00814a4400c99540c540e020008600d41010000d07483d00001c00c4460980c0d011a05020010030300105101016080c030700500c3c2e54601c5424075003006020320107000240d04540c00900c1c0600c00d2840041d205069680742c1e101962a84c2d00c215224201d4916500403a5249040c50204030f012200018804103aa1003816041d12025104115994074014148810519800203081c80038060180448c2a0044d002c3d80001c1252900da4071503a0941e0303010213900098010000308210031030041d03c604140ca042c0070001c0c241251502c000205840000c407054405c004540c40c100d1801c0d6030400c855505d1198608480e0a03603c82c62440d49071540140c110030724a5400d00305d004000075182902188a00c4004140c075007040403a80a00003030003143c242d103109641d17032400700c403006035810009014400a00c45042d4403080c4036146c409000380300c00034000c03005c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 822871726 1250 822870476 822870481
    0xb0f2202011d120a0503031608040b0403050f19080f0601020d020d0806064006050a030506030a0c3506041401061e290901050d060b0d0e060906 63
    0x1c0e07111651980c151402e24489803840d0702c12000030418050b2142c0c0d81c21074031464009408211000c130145200d01c0381144400d0f0002040c0324203442a00b01203030010110901c032000580003034050710142c0030001071030300e19508000c0c0d40c0310a0303d0b0510505038414042003030003040000030000104500c7d403080c07080c80500003913084444060750340c3d601600d401c81403144100c001081602d5040c00d84114843c42c12001c510f200c040325418840c2940d9100e51080302c04d060b420700600502201040c0700700c03a60b96544c2881c083d5107080c03c41c01401c0180c04507a140c0903241c0c265020038800d244040103041c00c45114800155001c1803441c2c0c00360312032010f00d801a0300b05d807100c0c01d1250110f2070382c0c0c1c4503401922107035101880e00c14050051856070011803600c030044003440c2411003110451402c0c5c607004448140c02c0c04e850950000751001d841c4807640041e0341082220a154450b001400803250700304000700d03080d9292455a501500400140281503130384600c07030651b0007805c001d0a5040709032100030380003d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 822872976 1250 822871726 822871729
    0xa0e0d1a25023706020a050c0607021b041d0105070e040b09011d070c050d08041716031d1302030901060e09100218100c02120705090105120102070b0f2202 68
    0x3000380300c190b80410907950210b100302400c11903107490f0032540300004650701c0c101c804020303065800c42d0300c0800442c46041c0008005034000a524000318004203806680072261904200240c556210380d80302000ea030201c0030380d03818801d0180c1d03405074220b40c58200b6511054820700c811101d420104034402d220440040044160303654219520b94070b0003c9409040e5035482081ea003804400c28010518401c2d602c00004095000c0c1c0c49ca800b4034464481c0003440014200d468401e40210100c0c42c880d41159040e00000a01030117400c2201040340c140c540141411000150002d00020740350b0701d43e5a000810032680107000c0c440c2c9809032010104002c0c0c10304060031003596480d01042441001c66001400025500d409403e1100c588002449512900c402c410700070040308001600301d0050b030b2080b40302152a0004202d03034040c0c0328040c020800a0781707841d08010300901c89554032251075508028840c041071b03170590700768400c0e400320107151760034180b600c001484544081041160017988900d00c5006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 822874226 1250 822872976 822873013
    0x60402070c051c080a080108160620010b030d03140903030c0708030a15121412091504050d0c1505040e1302040b061c110a0e0d1a2502 59
    0x5441c01a00c0031140c811655882403d00c24200d1006040410302180c004a02a40000300300e050f1003112080d01e4841c601150341d125848818001c0c00d01061040402c03041c1941412007040003441c0300030001c54038402140c0806d050000c3c007000b02c070001e62112946c03410070903d199400d810820200045207180340c2030441c06102d0254800061000200202003910555140c0044140013214084064096651120502091005d000c00c54150300042c2070500310f450003150185206c0300210001d403429220360b0070421144103818068a17445005e110100c4d098407590300d0b50150a104282c3c04c00c045040c41c0c0d000300b9900c60300c2e400408010082009002e030500c03503100a42c0104010075641141c0009100050192181461154001d003000c40c40000115081001520750a140c20342004a4510b180e00302010384121140d50300840c41c401580e441604141c000d079850640aa1030031154400c0700300b90300c08100000e076042c0095981103866440e40d802c01400d10f00341ea89003400100006500b40c2d030101d64 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 822875476 1250 822874226 822874229
    0x4030c0b16060213081501150c0f170c15101205030d0c0203031503120406080903040b04150f1d1309210806030d080a05100923060402070c 61
    0x900c9404107070300c0c0e0040c1600c2044415954050025900c1d81c098000c9820000e426101c0c811203445010402d402c0c060741440ea16050f161441c0032003403034404040c1e00b030395402d41003202102c41030305144506000c501e030ba5151003c5000c41f1401d41e41c0e03400054909601c1c11080c4509807884622507000d00c072002240780d2901040380d4000c42d80707610300078584c100581580500f071180c00741a41071003011a00a60b02000a520400c085001d60203004168002e02d9510050380a4810981204000600800c1d0042c2603896000300303101d04030f910f0180c480391015859009036220202e11305040345107180d002d0b0030824a55038055549000500d1010b020242e00c3c0d02c0080c403070350324003444001a500500010580225035140e4110600d0030072028500100f444824110b0b990200081182c0082040c91401061403600282107980d0707880355484502c0310b84014900504844100c100241002a8140407401816280c5801007141150140c0c1010000181100205594882d42c0704004d18000208184013850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 822876726 1250 822875476 822875489
    0x19140907170a0f0e010203101703070c0306092f1305151302090307030305070c080c0310020a031506030509120a050a05090a050d0803010609080a0201200c12010f1104030c 75
    0x1c0d020b903c00250000800c0d8480015450354000802c0280c10060550480100c03021502c02c182500c072041078150b16170040c441d00410a1282d103500f00080740207030b04000c0301280656180e65402d1010161582024428040982d85a01c4000104214a0140070083e051480c0c090144401d26004000040c0d6061013100d1034400c0d620102d0028444503e9419604000009800c840c1141d8582c180580380d42c0101c401180e000004030790100d226000800e40d10b01040002e002803508255036190000690001e0300c103c410076a581114030020140303445031400408054500092605010f0451400c110301d0340200000d1030020011480c52507400300880700d040425140040d101c890340b20016040b040990b1003aa8441e42c401c807580144509600194107c810035154200840c0e13403030400c69207031050100041d0103d0788821400c405440482289000d44100c031096881105154001401140d641503040c5810b1707550720504412280306204142075014181c200a041624554400d120104c0b98040c16 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 822877976 1250 822876726 822876731
    0x42a05010f030e010c020705030c180c0f0d0603230601030308060607110301240e010b162108010f0b1207111e0c0405060d2019140907170a 61
    0xc1e12200c1c8281d001c1401c00c0c02d02d200a01461003101c500030341d626200d001e114401d004901030200c2c10b19004458031204011094220360680d00c0c000d12010f590003507080650362140420482c0a82d003100d22500300514401c07807485203c02002610000c01a102c016078001c00c2e8012801803000c0b0740c0044030241d220750704458840d641d0505281081038181002000da41540c240414101803060b02000110103404255004158030358906034030f1007241d42031003400c46010b010410b91004081500c581c503509801144404200c0d11984030001ca0707504440d20840003e60008010b01000820507052401041030204240c24030704503180441c1d10850190904c1c060041000001000c4c5600348196200c402e018120b00e0462040c02010b981c40d860804901449070f450400001d9039807924140446000e500700300f241405019041240d0165100011b503143d001c4e09a050840c020f2145222440160444451040ca110820828000e0051000d01a0f0040c0301012180740b24120000910950161540d40701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 822879226 1250 822877976 822877997
    0x80f0a051e22050c04050708130f061b090302040f020915031f06020f0709060b0702010e06130b042102101d06270a06211103010608042a0501 62
    0x2100c800d041244980d02d01a070741e04a091040c00030200e02110b04000c150b034240129620396404640c030301030484081940c1c110702e942e40c0000c12018001e5560b50340c4036200000300140d2541200f1503c482141000c000038034030800074400c60070300b4004d2800b8581c1e455015030501d04200700160803c044950204020400031001605041d5008030035480002001c2e409081c039901c4010003510703400d080b03110300c00912846a0004000b1200d110b001c3c02c84041c4010507040c40d815034011188800c1c12005550310030001c1c4290700110622801681c014544031180715a51858006103107a00c020803960306244008030700000c000b50721201d403010384941c61884e184035641c1c00b900301c1c20503010b0442191608018046005202421020121842c2200c01050280e61409141c10800b03e045140510320028240566401a07002c176400203d01c2440419404100301d48050300d1014142c1090780b14100043c0c0e004240b005202031095410301203c21200c183c1d43c00d895100740040c00c1e00c403d1191070b0400491212 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 822880476 1250 822879226 822879241
    0x5040b150309070504060338010b07060e010f06030605010803090d0f060603120305060102150c0a0e04060504090501020909100b040e06060c060703150914010b030c1207080f0a051e 79
    0xa02c00741400070410001b01d500c1c2d0030503001c02c0d400103035803001c46500e00840c1901d420b490740300307042c0d1900caa800801140e0300705800300c952608030240c2101d589481d10000803e2507402e0059001105091a00054003032031401c2c10400d545069002484a802c00c22100b00d480c3c46d21381c81a80c0140c2c01461840d00e280040c0f40110040c00342d58409448182c00b00542406541c1c5600401d00a25090f8210f80d080f08161009085580054449600c0804100b00006145004528890348441d000300001500c56540021806403088014220b51b00d9500243c072020900c1d100c3d11007030304a1110500994800d0410030326096a20a80c007800d03801d00d84803c00200141c1d907031001c607210000800c05840a0f401c0184015001d46050b030f07030001d840c0402d1440400e402100b80b207a1803800404040031a02640380c01c02c0040c2540c8042c20740001d1000c104109000d1040000c04540241c41c82d0307a4a00e401c1c41c2117050b5821048000d030500c404141027000384007001d0b09100441c84489507500724540103480b40207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 822881726 1250 822880476 822880483
    0x30c020307051221060904060c0903020a031b1a161104020d0c03060b0711190e090d020d03020405010806091f0b09040c0306050312030723030402010905040b150309 72
    0x20300040a40c8911410150f2107004400030380f024120380d00320f021200e03004c0a49142154001c803081904903004034009404104150484010702d0010b042c00d00c41c40c0d840e90040340c00081903030001c2c0e4003042c00703410003001b036560b1200350002813a4181c0c080c0c6091009800703004c0f6034800c0030f944101c0c42900030302c58014802c80f050301c0e03c003400c1c00600842d41c0d0408040000050a426004180420718007003001412294200c100d40e0010f0707100c00c14850b05140e24082000407402401200541000c0742004900103210030165400f50080d8002086d4410485ca0001d00d032894082485003014018071080041d660880c401a410400c1299031f0f00003039503a201e940465079550401601201450030001031041000801440300800c191824841511400000d406841c000d20500c2d401d5440380c10300484204942015507004100e5141a2260140c03032500035040180c0c0e002e114055420010502046682102219004080a40d800d100016425001903d40d080c002c5401130071440000024520790341c01d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 822882976 1250 822881726 822881737
    0x8090a320f0f06160309030e420d1a03121b190b090c062106150f03070e10080619080316032001060315090c03150f0504030f02010f11040303030c0203 66
    0x15040d920040070a44030804218100000004115032740404807900e121486e104c0718280508941e05440d05c2d030100040001444042001146200901c8000340c0942e400d00110203040440843c06803908a1a041d071020b8021862100c1a2540700e10110710007011803a583e112204c0e04010710308095078501e50a40d081c02c42c2c840107264040b2002644c100034000140c4001150311507032064005aa50341e505201401140c0380200d14803a500344500c1c0e0340070103804011944016a4030307080783c00411203070200b2100b40300680c80102144100d020040c2c94280407032102030b4500d014010782aa9840c01460030340760701c21202d0b1182c05d280000c3d1040c042c14014001e40d07c5035140050150b0350340c0e1028404c24000c24440c003040350f840010b00c100e00d008440c0d5000728080a0b0300841215034051841e55070791032a420703845021010b00e488031070350002c94071540b090728801c87c080d4480034521199a80020b0031140d58002c090303402c610f40f10b00184841d03d0042660300307403607040c140000d9084044409a10314002c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 822884226 1250 822882976 822882979
    0x12051803060103030237110a0e09070e0708060a290c060106180815070e040c0e01080a14010b0724060609050108090a320f0f06160309030e 61
    0x10074000104055000a138014200840203105030341e4452440d201c40c03100b0120b100355807400780c0c0713042110100e88103010924000c1c4004090354041c59036035412a41c500070446003212035403c1800d080040008008600b9880704203494010b81900e0404001880950a8014000385814074200c85021000f00c0956100800364064850b44818184256961384d040900512340000e0407601503190021182c504202540d03604005000254501009001c003003c1c01000d980401040a640c0c800c15240c0340701d103100041c03d035600c04000081ca14005845e0401c040d02441c40245018081c3d1064208801900d041d51081c0482c0e940c1c0346081d0070036000b40c0b82080c80a08081c411507540c0c10400700e50394801d10442e4025128010815a15401940d08100449a8218603040140480001f490044980700b40816040702090314518814600c40c00d130484a0400143d0b80c40400464680e50302040310740c019044203401021549058003100e03249a581200020130f2648402c0880d040600913550890414030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 822885476 1250 822884226 822884233
    0xb030a0f0204052e0203040501390503092806110a0b1e0609040c051012020f09090a06080717010608060f040b1b180d0602070b010314060412051803 65
    0x151341801103002c098840c1c031403140b220302c43c9860500c60010003036504840d030503110344e0340002a40e004841008414541803501c10100c1e103440c0c4c0c1007502820601c030403601803c0155101e010000c03e21220f024820071440900300b5503100b0020000039600484d081d909549042034202e40c00c1468036181040004004141c400b08104002031411142036507084e0075000c0c3d1050380f554891400f403240ba4801a2400307454400041e07001d02481c286540d8283e001c28840c038001e2440310300c0d2600340c800c076040020742809240002a1503030b0300d490501740958115007502d1040001515068040366a807045215107c00c2500e4131141e030003080c1c02075200000501494082d50240c0c5011400420300b80701c120742c1103c030100c2010114424095070300d141d5072681c4a110056151070402150400040f0004003d079030f1185224424400041045c000340001c1480b40c03003008015411031801c00308040c0740503d49005588018100004a050418505401c0d0980c1c00d0503940c030711011315a03d40c00b0360500e600540511 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 822886726 1250 822885476 822885499
    0x70b19050927130507050409020d170903101e15091107060c1704111318140604080403080d0b061b0c150301090507090e0703020a08060a0b030a0f020405 67
    0x10002d04881ca148140640d10500d10b507102d514080061880d00400b900a80c0255001d01c0302d0304103540308244e0940018401440403c86a07262444070281030301c200c0305004003181070070460a04020008400c1c003640300a01407401c01c080d004801d02074505460048a0b166101d1001c0000c445c000d18001d48900300042c802c00305a900318100a50081404036005403821180c581d01c2031040c050f940621b100003000c3e40054a80740c4031024450191603450f0790080ca01c04602038404035520505080168122a14910901764180309004081c0240c1d0a805030b04030b5010800003840710320441c0d00741d991100183c5d4440b00b100e14408018030309410400c2d040341c0000344070b00c03001d80507600803c180008101190490080030703042c080c200c1c0e0150490080c1050a0005200401c1c40d44c0050781d00403081d16016906c16955008582424020344103800829800102c504e01960300104050340310f4001d031800e07600031740f5104015007207110041004240355038035020303e100d440040d012140103000c01003030b505200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 822887976 1250 822886726 822886759
    0xf03061512240f0d080c16170307051504030e0901080c04050123010c06091a01030b090c060a0c0501060323150906070c060905071203030c02070b190509 67
    0x41d082554402c0c1e00c100c8203a00d0a0451601c1d5007600c1d51850098a401d0705001d082013800100b01d580700c02240c0c010340912400d402d00d01d00f001495003283d220584c4290315442c090794548902540d414003001e507002007000502141d00001d40c1d0001c0c0a00204501c091b5946040494080c001040c015500002c09000060411000107640c184004115002c1000340d0740c0c1c40a0074030300c840012508440d61440c801017901036004001150255008403008a411005035480010660074074851520071a0000014811300260221855120305004024094802c210300083c605010b94503240702081102d000710780400c8000c1d00041c00560303110940500400700c001301c11500c1520004584514820090100c241e81c15101a56010780d2007140504516264030108070b0305004240000e07203110381c0b40d41d40d840c000398003080258010800183d404840b01d80510707006055416004544d41150b00881d0140310f02c6080300200e64440300280c000500040f07c0d103100f0f69981c010110031b958400380d07074211400c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 822889226 1250 822887976 822888007
    0x1503010f05070f0f0219080708040b0c19030e1201090515061206060f060903030f0d020913091a0727080f060403050304020d02011b062007080f030615 66
    0x34011036142c1c2814500b0903001204d0704070040704034030016170014024101e03168007054840d050a028819817841d050301ca0303e8544e050382c001d0348090380350b140000f40400c036804180200484001765240240c6a9090381c3c3b0024003100903140c80620411504241027003e0a0941c00401815402001d450302d001e440c06031070307805041c1111403034003c00744480d0360010301e50007159079881031500500064201c06e010043c0922604849140c603007600c001c014840a40f41e0348005814402e410300b17409a6122400030900c1200e0811a0b0000d8041d400c02c044c800018004928142d02e41e184028000c180b5034441004869940804c009509808030540b00941d001410203020705c10b40744c0c0340044640d00310000e40b036207a446204840103070004905001060052804500300c50354180145044060b0003000a02c0040c80d2202103000c4440c07594030a0b00140100075880201024030202c0300c51403c100c0c468441411510501910b40c846260000005050b5a01c5c4444c3c10041e10300502000d0b1503196400501a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 822890476 1250 822889226 822889231
    0x103110c0d020a261803030403080409061d0f06010804050106051c0c150903080a03020409050109090b0c090f0105030615030f0103170f04030206070c03060e030904200405091503010f05 81
    0x1030b484000d61401104220013084111204030349550740c4e10f0544208100c2400901080300315038540001c02001010403d80406030000e031001000008220345042018822401190f1318540004000710402c0790f210b030442030040d400042070906000c1d6560701d180541c01044107401407a480082c103141d15000c0d0400a2102d07034054803031b0070032005031600e503040c5240c8200580f0700c8000091815400388001600c14018162245e00c07402c000d402c0607207907002e48054400c01d070040d40c44542e50304002c805021070241350740d40204441c40c3d02454800014041812040380d8010b00f0306000c400008100076450b00380f10302c502011074038076031522418400e003400e0904a00384401d8030481c15115240640d10700c00f5040703502c856181c4074598509032550f401c0c851140c2218400b034400081e0042c0c0080130410302e020782020162800081e584c1d52404000308000c0b40c00400d00c441000c10800700c00a466003c41c421581541c0c41110184000d0342c40310390782100301d040304001607015401c00c140400611182c0c0c00490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 822891726 1250 822890476 822890483
    0x1005060409020a080a0b030c060d09050715260a2703021e060c0a11100501091b02031305120a080f0403230d080a0e030c0f010b061201050103110c0d020a 67
    0x42d01c80e00d4613071171581699489440180c1c543c12446403c141407404000400d5080345902d0045010b00207a00d8190038004154000d06801600102204503503034080c040300c0041289a64166500c130410360700d4554004028505035207a540c61603e00d41c0c0b810504420444100607040c00d098403082d524000351186601c04006540c90702c81c41c20020703050300100384180325400c800e040500740041c00030111080d050724055020b140c0281c1c4096140300860740103140c007802d007548001c2800c814994610381c0f60a43c1302c1003182150824810b064840181d2a0034804590b0105c0c4d21014000ca500c42c1c0c0360800c501c1c030307074024811240040d040c5c0c01c0d50521009001120f00a000d4071020403081c1c204d20440200d10303000e00ea61340d0000c001b611076050041c01c1543c2c00a5202c00c0000d848801074140d149107074000c44a190042e4444171440b440000240549411400d060310100d0600b24818441c0b9032040c010b0007100c0c18140c03184240c104020070301003a14109000c031000c1340c4800c00d82450180d01c1c1c146508056 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 822892976 1250 822891726 822891737
    0x3070f18030f120824060a261b0c0a080f09090703090c09020a02030d05072307300c051002041202032109091503030f040609120b040201081005060409020a 68
    0x500840520061400390400000c41c0850f0418030410000c6c10750049062000b402810b046072200308074125900001d60f4404880e010190901c403016000389401c0c0d0800302103085080001c141c40840c041000c011165004175040d4035940d090045100c035001e814030081e000302404040100440c0c0c541c1101e4005da000e5031081c60303901c0c1c6039039450041c0d100e002c5040000d03070b1040250141004087e0312140e400a031a01d0714044001e00c0041c051031141580040c105000c2c00494814107000150701c150449442240601d82c1c5080000c0485241030042e0f070000c0300b408040d0b07441c003041c05410700c141e0090720b03072003042199a5902c0700c0701a4944002070303100342d0291050b0281d108014103a00080081040c4064946080c51543d104000343c8100050202d0b4101503083d2090810392810030140c84d5112a241441d91581c2c10082c009001017503e07131150002c03101442c10880031410600d45503800a40a190080d50780e5128031400c01801c0342c40e0300503500000001400900d0845a90162000da48955602d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 822894226 1250 822892976 822892981
    0xc21060609090f0803040501060e0916080c030a03120e1f0c020c21070e040b04030809030702011425060c1701081507020a061503030801050603070f18030f1208 70
    0x100c0d4111642d418004090840000c40c0714081101e0b8000381d680315110301c00202c1c0e0991030310403054080d0000d44500b10140e202e450604000c010603030005010b4455040141500141c4200199540d0030b40140a414485180347d0012141e01c2c0b40c10050100034010216081503007420a8506402000d0114581844c600f04280684c00d00c0402e640c0c1107550300601540c007827101000d41e0004140703800300c0760499104034403001410f0500c100c0e600e4840c5001c0c902c070090510780383c10041c104000c0285240c8058004200202c0180e0f00b088200320b2140801a81c20388807503021015810a4000a078400240c50bc200f42d10810030085411605000c03015a8515003001c0e407001c203540c9000b0080c003610030190001d40c031300012664480a41c40c0d11100610458101c400107442d000100d61400c5018000752550703410610a140c0c00c0b914850042c04162211440c0d460011401000d08480e80401c0d010031000d001495205240070701800017843d0000304440c40081c46250050014103c80780460100307401000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 822895476 1250 822894226 822894239
    0x3071206060e090c0a09060f0c020a1e0e04080d1505030609010f06120305120403020a0b01120c140603042a1d06030312040303020a031b030f0b03010506010c020d0c210606 75
    0x10f0300d175900751980b12030b0901410700d00107a800445030260b4800700700401c03d4030b501513940c6440b2500100351468104202918803800d101540135a0b401588282e28100144400210341004a5004203426880051401080800e00800e04a81e0303000a9062061609102000f0019400352500208a1008002150780c40d40d80c17441c0c06c94019030240100f0018000138000058400b8041c3c0d0107842441910040112135998100422081e0440b040f9041c0d07402d440400c000c12030401c42e0103060314010300400a202c00f00003900c20300c002000205000c011040c0c0407406030440208096001826044400301501d8050250380d080d81c9291500072203d0202c0800e61311309005c411900184040d503051081e81c0d46a480550196000000480c1055a00c404903241305103403000003041004c9030358011903004000359102c0c1c00d85000340300c207620a92520f01405500d0f070b0040c0441c420f01c0c1d4151011107610515080c0b0381e2620515074045048102040321006008140701d503103405d5180b04001c100100754480c00e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 822896726 1250 822895476 822895501
    0xf0d1a04061802030a02090411040303020f06040b041103100f0c02160b2d0f04081b100e010c0f0507060809280503160b0105041a03100203071206060e09 67
    0x20038000350b03101654401541c001607400550f80112603d002500d42010840424203c4140c005020600200800c0034010150b05001894040314000000e0001d800e064071040365104000d0b100804112180b050042507480602c400c3d4850540c5c0c280800510b00000d042001528142001c0390042c060907120080341d4000c0141082540c40710098142080d111159501480701d04002d00d040407030380740d54040c1d00e1078061001000304515540300c0680b1945405030302c601d84900207803c1502c03103107480d00b550765036118511880b00002e2680391902411a4500044c2c614030f0042c00081c2454a1306060f07030041c0100010b5034012100c065440c0070881c0d03104d4800c03989a4500b6520400c4c208110001d8036205290700909460060240c030507a0300e015803d00e4911102c200c490030881c0d074084e21000400c4586018402d00d40500c48003090340300d100002c10006501d805115100c0c1503100da001c008640b0641c45404420f0301070718141001c20020742c44100107040c1c04429001e43e8481e0703181c4c60000e20201d0300305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 822897976 1250 822896726 822896729
    0x5030a1d0d0e010c0807260c1b0406091104030507050111101a1e03010f1107062f04030209070c1e060f020a05090a0509040519080f0d1a0406 62
    0x2029040720303010100100e54000c40c1607071543c10000c2034000ca002042c0624000d101461160806640c45212aa130324603045d030241c010300b910400d091203c1b40e5160008141c005041c0c03080e00004070062500341c009030081045400c4080341a18000e4440100c070300789c100500c143c034080e8040724074455a58004440d000d0048403200140d070440c964105400915820001c2c09401000e03a0f5144103c102021480741d603c034828202c0c00041460a80305117003003e02c1001c1c00050084000e000c407024400c50283c0c18840c0100c01041c1540c1c8503c515406010344004101c407415200602242059410441d1038940140c002070f44180c4101000c03130941c0380128003402c00d0355030110302c2c40c117204009158180744036590002541d200e0340390b11115441c2c00580c4000e080205a54940355100c4904800340540030100d0b811a030b0041c0410010b110201c0d1000810015400700802a40310b161038500d85100b40303000e112601d568450010408440d19655500050703c112000312412841d09010420003003076417460f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 822899226 1250 822897976 822898031
    0x1502031810120203090a02100f0f050c0a1515080d0314060f0d1a0109090c1e0b030912030f241e06070b0103050706110106060f0507020112060605030a 66
    0x500d1652900c03848540c02039907005017190300707494441c0d9058002c43e04007400032886d6000540c0200442079070303e8002c04203150703558452400318100180c032f4031074540e1620948000303030101c409010036048040c05a080f0a4680c0f0015a820340d9280da190000c50780c4292540d6500b02090a18081c1c410311842c2c02d9440b071060350300800b801e040385c0400082c0701c1c600b071129009861084d83c0300c4450103806800740140e4000c0c6001040001d4085c800d003480c01c0484810342024a100c03180324001003501c03115010b10400d448903000c10072f650b40c0395400000d29206560b5040340888030040108414071a04045940c4910581d030000c00300580d521000b01207080030440d01d240d10001d0340100d8030030710301e640c050300708a034001a08081c90607640740c036071401c9500e00341d00840307943e0310208003840030503482000d40e04080001c000a000c05030502101409120810144c2c80030050b0100d901c03425a072007841802542807080300200801503caa1008082d64012070701a03500900705094025400c00034070064408502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 822900476 1250 822899226 822899237
    0xc120b010614031608061c0b070311071218080a05010f061e06051606110403030f0203040e040305090411030a0504060e07030c0b130e01060302090102070608010b120c041502031810 79
    0xd081c40f00380d5404101400d402e4000c0d40300e80385002e0341c4001e07100d00300100b80203000001d030341c3c40c9c4814010252078442c05060b8918106003c0d40d40062081959400101401d0403c2c4c4407003929840c2c5185808a05d41c004641c92041603c1001803100c10f500004659400800500840703444484045110030341026600400d8403184040140f02d1062002d490210355044450300b60072400c2d207070841a60304224081c0e900d081c000800300105074221401c141010300318000345d0700b001d00e0a03c80d0042400000c00c082d051042c0054901c0c0c40781d40781e40c01140c94090a40416032a414240340300c0c4001e100880d8103c440a1508003c203048000028545d0101c0358040c601c2c80b0300f02d0520031b054a40340c001c2c904103650008080f4020030000703000144c241c080c1c01d06550040e00c0d00c2d03c0c0000285095041d60201c03060003070ba040180a908261400c588040c9143c0e0f580300071030344892204048501c40c9a00c41c054444c050b2001c400116404002000301ca415038159070000f03c4400308200a40d0581100c40c40440c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 822901726 1250 822900476 822900511
    0x20303030a0b0a050303040618050d0b040f0302010906050a200f04061d03120d05060411040e0402030a0506190501080303151003112b0606020c0d0c120b01061403 71
    0x301e407500001c0440c10080c0001c101eaa5440d8042451750b001a08014040355814441180401822480b4002000c04680f034450610795619201c1c91080050006044500d4640705042414000d4000410083d8031020030405031070b040c0034160007807400003010007641d8410104000308000c46c100b504c0707044c10b0702c151240c07a09141c0b90094501018810704080c0003803400802000554040c000303100103a03822005240d4a50006189408950740184150b11940c9041a00c1d45101c006a0954059a410410945141d196800002d24105898100410900c2000104080d200b00505186018200100e05100d642d032035040c0d680d120f010454080d60500d0306000103411914020441d900c0174201c1c2d080028a03501d54021090f9542d04c5601203803045500d68104899406003030030814500e11110104218050410300001c0d100c2d0030401029115980d4005024140180d4140140040ca218400f103004148030f45041d104070b020900c90040800d060381000400e450b86801168422a02160f1881011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 822902976 1250 822901726 822901741
    0x91609060e030c100302040f1215020348040317031807061806030902010806091b0c1606020a080406081e100302150a0c121106040c0608070c02030303 66
    0x80014150032039240c41501d0340485244c0f2070310460f0307240514030343c0c0c0503944500700455641d841201c0d50101074185d001c0044a80454140d1910540d40340d055000542e880d101c1ca110800103001c110065512002e19002807002d000c3c1500d4507444513108000108100d44e9005017070081c0c0e00591002402040d100344071481e2040e580c0d0000c540c000c041151007120100038035119480c14860380c200401050040c0c90800042510b12200743c020001c501d07062040150960001f8007a0f00c010704018050219100403411b0324201c2e0002c04507030100400d00c00d41302c8003418400c0395140107001e807011040e1010718010840074800b10340c56001540080c5641d2510385460011200580020041e80c4000d07200c083d080088941c1d404002d0080b80000700002c0d049041d40108600010f5145000c01d291508100111841c1e070044903020250f90003464440d04124005020340300381c40d0000031088035024400411081190201d41d400550b2801d40d00d43c0115035031440c0c01e6406c01c80c0c031803029605a0040c00046c80c0c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 822904226 1250 822902976 822902987
    0xd24050307050409021915020705220f0b060a0306030611120103080903100e0a0b07050a230c060708150d0f08070512030a060e060303070f03050f0708031509160906 72
    0x1561001d01b00c840403040310712241e20001265004098102c1a20100600b083e50400001000e4101103511a60300030042032100c0c100101e4001101d449d540301c3c0400f064255213988080584000035003d16641c2d090700500400416040c08116401c0d0f10344280c0c581c07c1c080010a480d182072000450400690a60700d4a070b1540e04003a000590505c00c240031011194280e00a80002038030100080503181034a1601d140d400390002d003c8820400180001302d4016400307025803010150703e4550044890b81041e41c86014810040102041d10a10050111142e0701c0310b1014450352026460109011544d0208075031a420100c01404056202450390042440e18005006851080c0f04a0381035442c100d650b514182c00c02c070365482826941c1d400400160030010580e541c060001c5001d5803800140796181c0b0385240410780050200900400d07800305840c801c00c00c541c6020741114803240c40c2c0c41c04103401e0001c1061a03501c1d40c0208052000b080d102c01010181101300c82e000c3e10f0b007082103410458200c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 822905476 1250 822904226 822904241
    0x1e030a02060c0f1c09020a091b020c01140913020a0c2001050409050603030706090809010e0d0f081b030d020d0605041404110102030412060e0f12030a0c05040b0d240503070504 77
    0x400350740c1300054001a41c03442054002000c0a008c007240301751340c4000080059000103620015074000300980c030016a0b00c0542e00b13203c246d1140350b00d52144c0c1c004c004038150100070300101d001c1d0b0380700080c58442c15802c03884036400c01d48a480c0c00305d95901c1e0204003502c64480141828081942848180102c030300340e8200550100c4040d00712403c0c11665100e0741c090b03600f181000d582d130801c005030b0200d0035603100b48140c104070340076641104030700c00781d136070304007114101d618054011000490182150045104810401c011207022241c4404161180800a40c4034500c142c015515024002466003088d00808100c82c010b402e103580c0c0303561a6107031412100c01c020b4446046000c10480815442d500b0880c0c0105036000d48000284218150b584c00c2c0317401c100440f44040d60307201c0c20410070480b03116001c50380d00450206000c00c500442e003009880900444e007040c10800001300d5440703400000c641c003061148090510b031881424080e4044910240c1b50b008a68064000b0401403005042c142c10112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 822906726 1250 822905476 822905527
    0x130b06031b060d240e060a141003020c0706080901060e060d12021002040603050f010e040519050106050907030509120c0a0206031504050123060a0801171e030a02060c0f 74
    0x15110012401c0122011413003081004164015182070014110040c202548410251004002c940c00c2c120442003225103140c0003841045034152103401c55110780c040e28400d8144c04c04071045181c035580c0c058604141120f1895283d0b1038020005901492400d1040c00b0340c001a114103d17074812526480e60741aa80015441544106048040307805c51510003480102103559000510f414100a07808100d01c06030710000400f00c40e0000d02001c0b80700400e81582642260104208405141c80c0581c058200c90b8020341d4446400010002042e401d600814400c0e0070840c25121020407280d19854540180420301c502c9a01c098a084014144880110b07040780745200300d95036504d04130000400341e503001d81088003240444030714645103211403ca8544119400c546003400c00c10320350f00c000d01c2040c0500c5000072032003111540c403100034814484071010102206a5145504a0b00b014903034a038840305000700140300b00340000d005808414140d403a050f01c0100c02600c5c2500c1500c03a905000361340390540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 822907976 1250 822906726 822906731
    0xa0f0312030b0d0b0a15060320040b0417010b0618190e13031704050f1b090406090312141006021207141e07030b15030a0201030e0c09130b06031b060d 66
    0x40305106c5415441c18014000d079500070a0002403048107418503895503400800d0b0000c10700c8144442316020081c0c1d801c1d24181d280c05004039400c404134a005d8100c1d0b0b0a45e9070001000a8059030b03918040c07a44990510041d40d445486503448030104c01000710344d105204032442c1541c0450044414005400c8085009140104007145004041c0d0f0030031606a90848003584501310400c0c480c1c409002c030360510705500c518a240712540101041103a640240300030140303507580d4050001c26000e15500b50720824a40d000708940050b144001850f4103050740c0c009080d00c460080060800d200055042550b002100d0003410310400c1c1d900c0781c6403a01256070a2010f0300074000d61161980940d150700c2c4550440034018502c00f80b440c00d000790554409803d00080c8215018007290640780000c41040440e070a2030b0005442e0244440c2900305178006602550090b0281c05024501111a00082015001e40d6001c509a110201015030b1021441c101c1c0b1410790540781c0340102031a1107005003104030280a0007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 822909226 1250 822907976 822907991
    0x60610020f01050c0702091b070318211707050a02040c0e060f1e07051b040209130501030507140306150310050403030e1606051602040b0a0f0312030b0d0b0a 69
    0x1900790343c000c4038071400092001c074403407040d498007030001504000f4220100742c800803d0125228107100e04080501403082035002601d000e000e01c6905001802000c0c0341c241c0e20a1480000400c0f078031842c0c3d0954001005210381045040042c00326902235900c07000407c103a0055900348400381054103c21001d224600e006400745403078550050641081c4c580540385c1d6481c0040010808032031b410b00080002c8000d0000390300140307001800521100c0301c108204154100c100011300a441500d0701c40e50403c1100401c001121065000301d03040ea442003003501c503e291030b0050b18810703400b22010f855050380010007060300b030243c00800e50a0f4850140907074095000c18410369042c0c4a081d241140002d507516040d429006052011024860080405411180c9840e0340109140601588136220118111071201155910b074040c001c441c10240c002803030613a5901d0701d46102c003810b1100355804544200c4c10210039200c0e1040381e9200c14010443c1c00314100b55100c6003c070300d00080894600507075030400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 822910476 1250 822909226 822909253
    0xc03060507020d03050a0615030f0f060b0a020606181b0c060c04090c0806150903070f080c1305010b0a0f030b0a03051629070206040306020703120b090906061002 71
    0x2958881c01058008000e528480c0000900b01da40041a4a4126207851001d000b00755884915410007862031401041c40c45050803018010682000039901e1603180070380c0001d135814502c01a000c1c024041d020340741690707a140c0a02c00401c9103861b103001d0348100400054441c0e00e030f21080355180c4803d41001820803440d007c0c0f0b1850310038141d480c1079141c00046803c11940341a0701800c0e98140c1c0710b15041c2514140640802d080b540c1012541c10102000320303181c10507440c00c10110000748000d030700034607460b59140503c0703440d003210002c814003441103c2d0f0544040320507405058102d400181e2220301c2e00c26440c008507101000515032004160b1600d0480da030565a0340b410802950080d4007405844217249806840704480c2c1c0d0044400030920192903075543c4100d100182040303261184550341d101148001056032007540c1004051608c0070404205040d4000180180c8440e0f0500400545d82030501b0010300c950100c1d40c1109940c44100050281c0c01d0171000f55680811f07074011a04080f45105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 822911726 1250 822910476 822910481
    0x30711070320090a0b1f0c0c1707061d0103020711120c030c190504050402060c0303010803040f090204120f150908071b0602061602070e07020d0e1909090c0306 70
    0x48a8400c1c482e00d000c1c0100d03646003000009800c01120201000a07148400100c1d462241c6030100c040c800c04014158090140a0461100007992103400c81c11f1031529200c0c0305101924a96016860f4402c12a000c07031614000c01c05009400b075807000109010300c41c00300440107940092400c6840000300030900c00191110f1245480c1442800c01a00180c02504203040c81d0010182920303100780301803d80164039610114441c1c05990080e180840c20365510700109806100d243c11040c3c4038400000001100c00c0084054030945112990054043c0d9540c1c901c40140e00039030050304040a0650b418000040c441c84a80301c91510a004c0036841c40407000b041002c07a04102c0040e1040c107000200034041100c0504c00100f02650100d40c00d401c03a042190003591070314024080c000701102d032203503842e03250300804ca554001c0142c060110501c2ca00844003d4a4014044910003c510500440111032501e541d4013440c1e4100d1014082840c2c0c070f07100b5a20702411400c681507455401600c8080b01089450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 822912976 1250 822911726 822911753
    0x10605030f0717070f0f02030f121005030d0f0306050603040210050a300f020322052b2003030a0c030f050c370c030516050f010e0606060307110703 65
    0x1c0d1644101d4030403090001d4016a1414060021904100f018010301c04104082e02c01010032110302e50110741c2c0f83d070301000243d801d64014537450310445e40302421590340406404419403290350107101007551358040c400c00e4003050341e000f907000d1044005691520f101e0000b800388a5030510701000850400c0d1200d003c0410f55082c03c4c421508104404486004140075504020b00800c3c0114654030f8800036400c41301e1140420390002c0c044885409092100400c06403040103c0c5050354480702c500c07200588202e800c600041c201082c008900d00741c18022041c9594031040420b00070310310f56900c07501700900405039102c03c001419070359400096000f06a101d1540301e007884640d003d681e409848140c0740c8d4035041141d40004200c102003a10100c04a50041c40700c86503090030701d100f050510345020f031007078040d1a0200101c4001c0c00001e00600c00300240c0043d25850b000001c0000b01c00781c0344030584403070089030b200740c0020b4100003080c6040e11804007a42103a8494042e1491580c803661060742040a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 822914226 1250 822912976 822912991
    0x10308190c0c09061d010f0524040e0f06010302160605090708100b030f0a051504030e12010f0b010c020d0f0c0f0803090a0906080604020d23010f050708010605030f0717 74
    0x1240c40c01d002c2d8241e000c0304010fa2644013403031110b45d50701d8103013000c4ca01c0156008080c05040801d0301c6080040040d50880203203014035401c10303100da45410301c80c3c10a000883c0c070552101d2203d004641954000c1c400c2303d0390740103080003030781501c0000d45446000c1c00c2c01409030381c10b80c4073b034000000b40208140008040c0700201c200c00305011520108041c6061000c0860b20f0071070f042001d4041c00942c0c00903801c000700e20f00f1904100e89a5840c00e040da083d00180c140d490304100301c1000984004410f40c0315800c100f46072502000340e8100cc03c0115a15140160000c1d003050768000b804010451080100104520591446403440e0b1603a000012030100c40c1e202680c0c541c00440c0743e2100c0d180c00c40d104001703050034040030800d00e417600c40ca0580d50b903000b4102074040c4084c045400c0034401e802140d92045044001c0c00c00c08440410009070080007100406c81d08036242c140400d01c0d203881568401d0484003180c0e5150f0075500c6d409030390210010090000b40c00d000080403046c260b80e0001d00b20512a160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 822915476 1250 822914226 822914231
    0x111e040c171f0e0c070f0f030206070318060b0f2e022b0e03030f0721021c050c06150111120a030f060902040905090d08010308190c0c09 60
    0x19201c850003407040e01520b500c010b554000d4542e40c1e101884116101111100e0740140300d5031326640401242c5101d040c00c041c06503090030b91041c041c1f0150720b040e02c0c12581310741d00700d410700d0352a05c01c22000c444240401c43c1c40d40c161241c2003008116107803c400c010003401040032a000c5900c40c00603803a4200da50900c030250b22a540c03641e45000c0c01d4207a0540540482c0080c0140302818060f50b4244c6014690011903400008800c00c0010b1180c82240c0340d96074050300b1a503807403242c0d4401c92402e41201c07404480d0341c9200c00000320030b40c072007004800c100207047c0c00602d01300715980c96001c40070381a00d98a5003044014054100e15450801ca030b24050040a141c0340a0590110001802d942d40c42c0e030708026039441000184008001d1340100c46a4000c1841c0001c1e03184149603240e40602500c1d407141e0001030012030080344840340d941c00540500d40c801c00715035000030150819184000244070285c542c0d1024096084c5003800141d0b07102c14882c0e9450862000c0b2102e03641c0e0303440006103400801550b41d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 822916726 1250 822915476 822915497
    0x7021219090f031212021809180109031e0c12050a121b11010b1e03120301090204170d0504050120030c010f05010f0503100c020102040b0f0c011107111e040c 69
    0x6400a01c104980d003402d4401b50f1520321840700c100d4444d4400d1a04a00940c10080056580440c0046d42203d102400000b44242445824000d00c01c010b030118101081c0700982c000800c99004003640703008140c0c850304514030102d8030002501c203500301545150a01c44409182c104041451160007451110140d40c908040c142440003800c2d1054000c524045a00d0315074110110b40d40e04103441403c020380e41c9a2a1810840b0f00401c0c1080c040b80d0203180840740110010401d6010b60f0058020f4070703044401510f9600800040b190b480c0c5800d281200400c004000a101d1940b14410417269070704852524564000410b26092941d404801c000803c0d954400f40904c410000c1e0107114010804d86134503080d5a824400002c1c2c54020503030115082c10366807103944041a0003901514010300f08405040c2d115002010396a510764004d00c0c40203040d500e0406410102e0f60a001070710340c0c0c150049200011180e0080610080c200341d041c0160802d20802c02020071a52035009a4108040ca50303917418500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 822917976 1250 822916726 822916763
    0x70306050307030f05010609111209033702011506050f1605030d0501080c0f0405130605071806030c050301140d051902030105010506040b0304020607170f040e07021219090f03 77
    0x10781e120f0304803801c85809c03c10211406008201a203100104200300d0480301d48903140c400f41341d8890030b4400b0003410302c00c00650340054201065001c244040060400c2d1041c132001c000c900721541d282602c11907d4070341c0030601c002e07032142c000b0780f8002d030400860b07902c0d240300300c14048010855043d04071042e910000e581e05081000b80038041c010076415009080e94034154000a852589605071503000e695100005801048403142504807240c00010410181c14410b400a080100900700050441f0701641c0028541b4881c1c410003c41036066514582581d01b002d041c00318a54071035002660240078610f05001141c428048600000c62080d0804086000f500c141425200143d10043c400d240c144400c004800d0800b0031254015811200306a607065146480b4080ca80c000d031004134254001f01f019000381400034024025215030600341d851664a9040c200d0313442c1c2201604001080c0d05002401c4100d43c6409441103002c0781c3e05060000c1922071414607036443d00c0c0d601c240d402c0c04d5018040d10a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 822919226 1250 822917976 822917981
    0x41208042906030d02070b031504020d0504030306061806090e130c090b0f03010b0315130506011d090105060d03110c030105090c120a0b0f1e180f07060c0b070306050307030f0501 78
    0x2604c4074006404800c0c45d11604e1912404004d0020081c0c68203000105540da460341d04403103002542140801040c00e007030400400070840c078040c020204200c80d4051074a043d075500d0000498400fa551000018201798030203028038805811030495646165a200002d04500d80305800b03400320348000100c5034180d40422038200d80d07203011030380039901d014001310030754a020412100e50301480c00709195a4490f25452000e410b00802c0150960140300004108001440e40300d5000e180498405441c946860344100c1c2210b2007600c203544c4c48100d03043d00310300007402048103c0d14011000f0a03500002801c0300800d007541d10403115607000c1d0b0440d03c0f00610ba0329004840b00901c00b580b40090544602c1070b81d4130015074070050300c19500c2c217402100249a03000c8110921074102c0daaa0035002c858280f00318038002c0768244841564071405a508040c0c1a1000040d01504584060362040c0102103d9100c55503c0362014101408058581c0c0000c24a03807410082800158071031140c2e60a44013103418100d08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 822920476 1250 822919226 822919243
    0x512071701060f050f03040f0b01140108150108150109050a06050408010606030507091802040308070f050f0102090d020d060e0a0507140d08180120150105040504120804290603 77
    0x2800f04581d4091007036903102c0c080e24408000811100d81da6152070410b0008034101100041042c003041c0300115a0234400c002c00d01680e40c00fa22042003d8403241c2440c0311030f05150769000d0014510b0b80009454800603100442c0c0e00c101030529200f01c075180c2d80455100c031655044003011940008041210410034840c1c040200941e203020001410070600c02414248648540e4011100d005224004402d0550441d8015030340548515130b5605285060109221602d02c10786030380c0100c0c0c1000c1104241030084855600d001000590342401c1c5600304220308908010507101036039a64102c4003190130404c42c04c0c04d001d0041c0c005004451800c1c506460b100c1c01f0704802d600440391560710100240c0da00064811a82d054490300c1e0694181c10010be410031241100015103140c01e04a04a4030080450030b00309820000f40041c4007070b030b01e032014041501d1041d0b030020a040c210b404041540f612644039240c0080c442d005d002645604e110600e010843c05880700d01c0003242d40424000300303240070840d116 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 822921726 1250 822920476 822920489
    0x100e060913080c10020a08090f07080706052d09031b0f060c010b040f0c0e04090209221202060f090f060c0307020a0c140f090108060103120512071701 66
    0x418034900500c440940c0720000400402000700460640000c8070705100d1402001d8090100f1500c03170b001810000e0610a040d18401a1801a40c140c0116004c010801d0402d540c140c0e80148101868080304642592040f400d4485141c8511340c116407090901c032100380b1044201c030361240c54210072001c0609000c401c1c40010230410785401014119282c2101a0f20842d03000c030360070b5480b40113515415000d0901420020f5119107041c003080c81048941c2c1c45502400340d103030b44030072222248800344002c4808120010b94400f1540000a03140c0354410540c184070404000d03560041009560b807504408038800311503000d81c00180c100090540111803881d8030003140d5009041040404100c0c0d5102c0c02c020300348040a010020010300303624000c014000b50560304c810416403807965503588520701c1095201076403003440d11401d12a01480d201801d50b0598143c4006825a6445c0d07542c1c100d045148213082c0c90074010300b40021000030b6000d04030a0b10444c0d81e62a41589181002003010304108141c00c000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 822922976 1250 822921726 822921739
    0xf030317071b060f09050a06050106021603020607081207170604020f160c1508180a02010f05070203011118040605030615210717010b0a1526100e06 65
    0x2009544100040c001012079409012490b40504202024051a01c1d01c801d805040118440c200600040d110000c90701502d030400143e40c883c98200d88400700460100c0c0146007105c420701c09450240001c1c110309115070f00301450603500440b28851240300700c401002284078900150f00c0300400c03507041030f4006800c50f000c51174005940d41d1440310f03009119564541071001074941c4100003c0039020005415203034104020302c00c0c21200140705a404a03084ca178080045026403080c10000a01450841d90584807a1110030310020102c980341c00c4002c082e80d25648030001d2800810f0400024030640300203024110307603220914140000c2c1d5040e0703030005000303502400401035003007400d03024505140d801301c4d031502d201e03100d1800689210205280a14080c00344070070016040b42d541825800b8615a40b000780490a0076100704040c0d2213262060070020402d80368400e05045c400c1c004e0180301030754881c8010a0000380f102c40d039610841102c2c0542241261381c01403100049254190b41e0281040743d41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 822924226 1250 822922976 822922981
    0x30a14070801030305070c0b2a0d0e0915090703020702031603080426060c07031e09171c020d090b04050d03140f0d0501050901080f060c0906070204060f030317 70
    0x1d00d9a001488003034108000440c42d4002c122802c0b9001c0d00400b0381080441c3c44e000440344040903810003a2080681c0000c0c01c40c442c000107000308550300c180030151990811340b600881880010280180300c1c107031250500c40d00b2001c076034036408000c0c010703c0181d500584a44003841414500705000680e0248a0210813007040090b09034800c4034265055140110a00b051104d8110407800198071001800d000e40010400ca070030140d4068070001d03000c1d6440100b0f9040d00b8010311107440c08005004001240a0340070f2042d5409889941c09003e4003601b00c2e40c2c1404503103856a04501d04a80d02c20068000c100ea2703601702d42d13104004c480038001c1969041d20303182c9008009001c80c0101400181401070845040080c26240c005a5407102107880100c0d40d98007002448034001c040134064148035498142c00420812000180c0919070390b040b42c01000301c0c0c0c0b0b031031b207a0502d6a0007070004103500c400100840c03070043e115406110b00070206020940c0c40d807030841c078010300130000301c48a00e011100003004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 822925476 1250 822924226 822924241
    0x7140303090a02010521390f16050d03060303080a02130311190f03051207030e0d15020406110106050f0315060a030b0423010b031506031c05030a14 65
    0x10b000e44560b50900f80680d40c0c80c4103030300030a040c241c55405c0300718140840080040302140c0780d40281d00303110b0311200c01b8084020340c405801c0c403031792241000d515550144004443e00c0607440051410260001d41240320305216624546040036a0407160000707606c0e400100200750304061420717040180100b0a50034124030290a00942c10b00e84409480005001c8100010342c68040c280c010030302004104405954550780d83e4440c1c03100d03520080320540f00384152288c4d038181d42d1007074030410399050f9a8500e18a58030010001b010700c45071019640e60881e41e800d880407800f94070041c80281526150044000354040b000d90841e16a44d00882c0500300214490621b5a40410504000340781050140d89913110180414003582032508003c0920800300d0520050080c152915403940b40400c0f0402d03d410b148080c01800c0e02c0c0900e4080307416621003035100703511032542c500c003c0d485200030707040b10a07a0b03e11340051501d20a06624650120340d0000600107820b050b408ac80308600303001c807112055400d00d113a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 822926726 1250 822925476 822925483
    0x10612020d140d0906080105060301030b0112020f060c07170c1f030b040c0e09071103040b070201020f1e07090e030406030c0c020a0311121c111c02030714030309 71
    0x4400074412400c000d0144100b00c82d11140c0d4102c00c20000489100040f900800780c6200090301828020900b030b003000017098030b00402100c2c1a00d80c41840b028a0764a80001e80619071640d007001c91b8027207601a107087c01610b0362000b80581c5c980d08001800f915107031506e61090801816441e00640e0481a2950701a03290301052650941c005480c0703141c9500d9000080700101000e01c001c0d07034040e05005040c091103501107580340079210b003201c5003d601e449014080c4c075101018015061103030018041000200030900c0505401801070040d988800304403400c003800c1c1030b8044115480d0344210040000d614030100030610241215071420441809055034136942c0740074500c0707030800b05515000100100c0d840307000a400a15400341081d0102a203925040703d5104100ca61a0300501383c940b03101d2042c0000240c400301c07101c56514140c0301c81602c840101c49070304100403010450f215004042c510b0b0703400821000c0510480e0307400781d071300e800b507031310b450b107845541035000714170f994070074001d100c800c1d040403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 822927976 1250 822926726 822926759
    0x1f0503060c030c03070c0507081606050a0903110307030f0c0e011508160e120606040c0309020f090705190903031202070201080601210c02030c1212040b13080f13080106 74
    0x303e444589950710703120b044403107000b4800000c019000350700002030340441c00915001c0c0c02c00d06800114401e0745844084030107000711010500003810400d4100081810005000700e079400180c241e6040c81e44940b240300c1e81c0304ca1194119407d050501b400c216004d05482c0280c09000d00016200c24101014030040c000036000c0c0001590242980a000849000d42c81c54100032502404041e101455061030503210001102c50b18050350400c04001c00c5070f031003807040c10519030380105a2030702c0164a03000e0150b05a03008000c201400000c00494040c00300180340c2c5058040b859840050003421441c0c000e00041c40101c070300036164014003501d03005070b0700300c80f203a0303808042840c024030010344807036541c403402080c0b6518800051a02e94818800c542c0030000f000c0c044041421264110709140345550030f442000113280340c9a034280082400030341b0307072600c003608800000b0344080c030101c0350b07103500e050359100d0207401c14400c0c00001d0125005460b24008002032404070001c000c1145416440b41d45048030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 822929226 1250 822927976 822927991
    0x3070903060b0310050c07020117061320130306062306070302100227030a050c101218030e090106050d24060801061101061206020903030d051f0503060c03 68
    0x142d54103424551002c020007a0031540d048818409802d20b0080c10f9955031140300b09a0000303000e03020145200c10403985542c09204050720003041145004c190100038414080348207604075000100b5100d8151076070161103545080d11050091500d940780190444a0b0365201034030b4880303010494440d61240c1d4100c0c2d0707030503002a105265220b000d0b10b4124241040c4001030f00c00c0a101092a10b1400790b2003070350040411992410200b041c100004050740c41c084c044008105901012a00c11142840c040b10750740c0c41c040e800c01401041c20807900c1015554403400910035460030060100a160f03001c0c098122000c1d064038400595410301000800c184100102003450549494581401510000f00c44011003483e10496140684464005040c180280f10b4403000070480d0f804410040418402d0400715410501580070200780381c0d4610b000380d040000007691600050214191500c880d0080c0f510851410030441c209070b5900f51904035004c056004140a41d03c07a00400c43c850400c801142d821801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 822930476 1250 822929226 822929231
    0x2040209010201200307090614070f0f08030915010b0c07031707080d0608012909190507020705210703060f06050604081605010c030e09040302010e121c020307090306 73
    0x411030042c0c0c09000380d90440724081941000c414070384852840554028041583d4808032996504421100590b56103075031200c4807000c1119100080501e43e07802039072031044821074465030300f60300d485140307410441d02d015664001410400c10800d0014481d0302500c213124005040698102800d0755501e4603000040540b80c40c4103c0d146041000390549004546c011103240ea1140510001b401405203846540925800d20000141e022001011081c80a0f98540030312480ca07569810440400405020510300c41c2c58107003c04000740e0b26009161081955400411611349440c00340010041c42c01c404c0c89141145038091052000c02140342030071203401c1040840ea4030407810700000100707030541c00380d6032020b00007034000f520313042c0454030064000e001200513010664032b40040d600301106540c010000b0781580c081280c20f10b4813101050b0424007a10000900100d071190703080c81c1c803c404071004507801c1c7c040781146515520315004040c0c800900d200b5030441c01c2441c00074058000d5400b004004a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 822931726 1250 822930476 822930487
    0xc051c05040810020403021908030a1209021003050415050106200c030d021e0d0e211b04060f2411070902031503060702120c1c0503090f0712020402 65
    0x921038025036015002c0d04080c0c072103210a542c0100000e601c10701c0100d000f4601c3c800e40301c04200c1141c0c10b00f4100c40034000558a484220350044500340c801c403c0c41c410740381c1c1e25140c031009a260711203122541c841030b407000141030400c0c0c10560107141800070300100c2c1c03509000c01800015070003541542500e00092000890030b00340484075003050341c10040c0340d4040c856070b07a0420000d1350029201c0e60900c0100d090341460108c0440b49902e41c0690786900d0040f0381d8803080c0503c181043e46c074100000b2606d2125202c0c4150035200542072484034404c49280a032482581c0b0410701c0c25100d18002050b0380340c0350700e200300d103420034054400200c0da45403180605e00240e201030305409030f8010200c81d050b080070707198219101c0c0c801c50000c0d0406e440b15451500070940c103407181d04001542d83d0041030703141c00400240e410030701800002d034044901503c2601448551101c0e0b05044c206800d100e0320103880341c64403440c002c541ca80c9000c110000d42c0081e80d024100030400300000e4000028410b406640141e80c51 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 822932976 1250 822931726 822931783
    0x513050c0d0302070e16080a020a1d0111010c02010203240f0d02030f0304090f0612022d0d08090102011404110d1e03020d020105090309091306060b160209070c05 71
    0x207540c1c0702505170455001000301e101a0a540700c0b610a08984406a040e202e12115204901071184080041609040c0075a203150f0b245507200c01e98901454400c14a4200c041103609403030700c100b94400540e4010040c000021099031601c01c0c02544404640e21901e2500b00007003841c8580d10009010701c4002c0e00450540d1414000d031013294482408481e9140e940300e0100005058001c80d48144c6440c008000c10f904802c0500084819001042c666242c00b00d00e1140d90715490302c0300320b000d894070340a03010581a1500e40385400e4860040880e42d4540c0c1002c40007a0949408100070403811180c1001c210028011801d60801c400c0d003910304801108070341c58a00c3d01104001034103d880a0a101c0c0001010381c00641c44030006043d40c02840181c8440e04495541c1c01025807841e4003102110000e0007403403499404000f40d500170341020a000303035510071850140d4000b104080a10120000010950400070490782e04504103241a0046120340e803240360301d49108489500f6078215100150004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 822934226 1250 822932976 822932983
    0xc170f0a02070b01060e09100605031803250b0f0c07060e0307021c05160f06120b0402071a0c041d040f0b01080f010605040506060708031e1003060513050c0d0302 71
    0x7610743c01040d101c0c06503101c0300081d00f140740300f014261103501d14500080d0116050075102d0222012611600e0543d2150003a03200500421156601544400d00c00000c43d0304600e004000201ca000390009003100060609240040d801001032404403514003c0c4080590104211003804e50072040004540021506139070552044440180d030000b540000320381244040011800e1003481401201d040052946d2030700d0719403000e4826503204290300360040043c940a0580e00c4805075211030002240414400000e040740c100c2d050541d4081c481307800d0041910614102140c1040200c420907041516041c076800d0341d000310716003000c15022450081000c00132240308007012594001604490b0b0740c0c55810180d90341c0081c05982c1c200d0f40c02d00703000086505061080700d0103244040d0100e440c1040d603813a8110260b101400522154200d111283c110442c2c0059282c02038041d4200402c116180d41044401d03200301812800501c603034a0740714800500005045007100c20250745080585100d410140d04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 822935476 1250 822934226 822934237
    0x1b06030a0912170a1b1b06050f01031b18180b010305030903010b0901050a05040e030c0102040b04050907082809020d050a0302010e0a050709051503150601030c170f0a02 74
    0x1506040d5159000c0b41d009440c0c0b800030ba001c80d812003020358131680c0c114282e8410300c12001c6503240c4411440c01403031081101c80c0a49448002c0300d401d69405580e072070110340c81224403170707401c0d03000f5401401004985840c52100103d0091b410346150305205002140703805101030000c4069a40070842c2a00b010520f8030170505401c14856810740da50307400e045807691310208841c1e1081d40f0b0f01c8040c540d035140c003064841c16141c0103000c240515040c4018400101210043c03a80148014440000c1c0c4410900040c00034110380c0b040d658a0f2880c100c140030603100f020780740c6400d00c0440c104100403a80700000d00620362407090000341d011042c007921b0350001c050254000c0e422038240d00110041c41320005c0e0703400c200b521035070080081d4941d00c000300c2c1e01d84508038002000b03a00618000c1107007211a410458010045801c140c0340e000f00940003900d082000041300040b55100c5040150342c0d80c05110b940005445030903d640c20303000c6224410340d0501d0003407074518030031402d0000c2101034580e941600c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 822936726 1250 822935476 822935483
    0x70e060304213b030d02030d1d030c010515060c0709020901030207050d05090a06031b0e13090b011a04062c0904031205150d021c020d05150703020a0509010e030f071401020f1b06030a09 81
    0x1e03507400706520080d0103040122094685e400c41140c14007030600b813240450c1c1e00d50f80410003410340942044e4510000c1c2d44485a407504054003032004d03e01040c014408900401903503114dd95640303d10b80140840d5000c680e1201c42810710f4094036005c1010030781c4562403001c201c1d20300004924099800030f4000e03524811040110303441c00d641c07035040000030b01603907050300c6403280a4100341409c070042c0d000c0c81c8254002e0b80700080146a84e103030204140e842c0d03040c0e0706581000041c8540d12203c0402c2d03000e2822a015000501308440240d12081584a01604401e40d4141050b00e462604040b0340150002d92000b4010340003ca20345c501950320028401c80a540105070800c4101c1c0341c181607545010311540d0b00d40382031400e804200c07094024800c640340015151281801e25030007400550700c41c400e11803c10741600503100c001c044000280001c40187c1620112080c1e400d49040009240c0000400305091a45c02110000c40b215032601c9403107600481203418603a41d81d10a54040d004d0840d81c070004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 822937976 1250 822936726 822936733
    0xc0b030a091b09060f03081b0a0639081602010f0219140301050d110315091b0108090a060b01090914070e060304213b030d02030d1d 58
    0xe204805142c1c5107001103525000b070a0003010f855060441c1100154400181100030030040c141e41b0801115441c1b1030003e040c01503075401845925001c0c103031186030788a00800800031800d600c2080030f0504c0c02c1d5440c455061561f000118102d809032901c2c078064041c140303462048000d96641ca00c00d40100355114802c0106640310051811034858001d502c40d03809010481d1aa45d00a44201c5c0c0401e0340c3c12140020041100c00c1c0040c0c80d8203200c1001d0f021055050b0092000911420090048a500072a0702c0002070903440c1c191403000c04090380c0d1084142c1000075480610510700742c00200145155081803000500c95402d80058540f500550b101841c5141003007141c0100341210b100b0b85101e41e41c25260340000c0380480081100c18807089900500b0046803000b82a0005202ca00d103e6010301181400f00403165107040c44400980054680f001e540f00d100511400b12010599141000308140c0c0104000c5880a030080d48900503880017076a070740c1d0355907466101d18202e24000d0754951550401d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 822939226 1250 822937976 822938003
    0x8010c1416020d082a120d02041e030c080708030909090f06070309120903080d0510051c02040f0e06070311090a0b0307020607021902010c06060b040b190504030c0b030a09 75
    0x445080e0700003070240002e06480b01e0b0054880c0e03c0e02c10700c0c817034580180805812a543c0300385c580c0a103038004d10000f401c001d03402d10003c90041c10300301541460418034082c85520500c3e500d44903880303080301e030040e805a4102c04c00070403201c500082600c02e000411169506941d03900c007046031810444540c6e11035a44030b24410f2000494156000081c4240149544030a01180c080103550001452000901c9100d0401141419400c40c2c2e005a402807581130000c206d9581ea880040c172a034054841c1140401c4903100040e085291030320ac0c40280c4259110180840b0031a808502d4803031000074032400616440c0c2d038403040d003200c4903402c40c0c4400358003c00c41044291501c070b42c240381d40c104440c4503016100703400100d0007281c0001000f40607004a48101c0f0100603856004454a03806250221200c603101c94000c101d15070f00a01510103001014986600c60740308000442c08203032907100310000d00508210510100c1c0c1020b402c0000e6030101c849440d0380c0d80760020401d009103030242e030280420310740400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 822940476 1250 822939226 822939233
    0x180b06070b1e070e1305090f07060923061902010b031e011404021324081c0e0d020105090117041b050a0e06012d120608010c1416020d 59
    0x2c0102045a0740c1054000c0c69550030000c3c0c07034050300c4c030300d005501070714174410052030404941042d40d000900d44c0c19030712008008008035140c442e40c0e41140011541d40d00c23080c00030010100d004001d0706210790060039400e201402180244c450181c0c0b51f107410321400c0c0301e910103d000750054101e411000e0202c447e40400c61031801c1c0c0c4046d8800b00a10194208900c1c00c0b000307600030440c07601613a001000f2107418814820468020503441121080941c01000c1200c98841c80814003402000440054019503002c15680366440000513042005c0c40660081c0c8400c0e922005102c078100383e42820902c0d5201055030060343c0340d02d91203012510780224642040b003001181c4d0384221120300d4603000044850744038002c000345000940625404107011030300150b178070341c40348078104981d0402e0351401a00d4407131000014072103a4040d10400108030032140148020300c03644a10310040c0403140003000401ca030041c000b0102c8050503010000c4010104840c42940007040b50400380d5a07005215901d984010329 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 822941726 1250 822940476 822940501
    0x20030313060e0a240b03030304120f02030406020c0418020402160c05060a050d0c170a0b0a0b04050d060b1302120915071e2c040b01020106180b06070b 66
    0x2508499840c204010003250340c01c0082c0c62021103a01c41080030310035800d80401c6082540c4c05895028060312403002c01c0103901c0500041d0f004034040e4090900d0b40c0340d24000a048803034204070110844d4010001006044d42c045240d9000c0c2c04121000300d1010b244665402075054070b040080c2d4050301c0000c54060401901d01101401c3e80324100040b03255507100104101405480c5030080452001c0050381c0f0340c1030080e8001410103c1c207051103603528104410422410b54100c80944105541d9500002c41e40340050201004014101601d880d00c0d040902190882c410780f00020300c900e890b104c4c0d0008a40d02c8202940300050702120464035100455020300301c0c200d00f661603000304c0c090124404844250348010b00c0c0301d0384c0c05484481c080d5000b041114000d405c070440000410041100340c8a82c3c0c0305081803191500705050b54032903101030810400049958000310207056a16120b020010082081c1407a00c0005100500107940b01c07004020422a110ba070720002c00c2d0a80060400048200e0359 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 822942976 1250 822941726 822941761
    0x309020901210b0903120907171c18031401090204150308070b1305010c0309050609011b0f050d020c01140c030906011802070501062601060b0703200303 67
    0x8840c180081e90382c032003a02d6025614591100e21020460380b41c0300103c1c43c2c40b41107a822900c10b81c11289003010a480e02c5040c0c1c1c000762000801500040e03010406000d5003113000c10030b0404500904410200c0048401000030659450350a1062040c0c034402402c000c0c1801c04011030b000150861600001e03201c550081041c0c0f0800c910492074070040c2041c80f0645940181a0781e801140d40d4a40800d42c0c1707800d411001d000700a103001d89490040d40001440a010f6074803060110749000c507100003289003903130500800400c0303288648e1602001c15484140c84824040c00440d50034100340b00c490909088605100c1c20354038803402c50000401c00c454100550215580d69040d480410b040c0c2c5900403459420b10040c1c3d4070380f281e40d00c80c00050114140f01e0f00b1400103ca001381006240c00c4c250f40e9461b00356201544110007102d844103070702c0b001501d8051f203580015400c4000f0001d00e420601c1100190180010140400440400c06403414071400d22610380c001d5400d044030f44a242c0a83d8400c1c80c1000d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 822944226 1250 822942976 822942979
    0x30c020f0705060702040e1e010902040b090f04060b0607141e03130b0904020d18030305181902010201021312021e1c05010b1804020315011a0d1b030902 67
    0x98210441a142001c00c116050301c0c401009185060515000c00026110640c0da5640d43d0103009601c6401107545036000341c414441030000b048000f001c1c010003045610080e030113401400c00e20200070090081a00c41ca03880355118000203004000d91012030b600c3d0046032030051800802d0202c1c0f19816500040252841200c003a070720702ca26014005041e100d0082c1005c125052608000c1403040041000c0035100144001c3c2005052061010f0602c0c01d0300c10a80c1410000c1140d42030920500da0b26008140e40201000080d41d40920b1000c09103984402c0d40d5002d00031156401706140440e0701c01e40498080c0010240c2500c1142c2d02c0d0301c0b4120007400c40d032404900c40e0010f003503015840c40c2012090400f0840041c8181d5400d0a10040b20200840d401c10031180c5546c1c80c498000d0f103aa0ba101c11003e4910441c44201031460548141881c100110001400c40c080d1107004004603441c031032103040d2144130300c1891500c460f841545200503152034000c00208000e440070f200440c0d5030650160300880d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 822945476 1250 822944226 822944233
    0x120c0415150212030403050a02010b06041701110f0909060f04090c06090603090819031b0215010b070209061009030c0b0a0f091a0901050c1002041a09210c030d030c02 73
    0x199041c243d036140d81d10f01525102c034905000103400700380910f02500c00385017180000308405054078002a580d500030340141111584410a0084048091007480b6079031541306855850002d80c015402d2150180300000c03031103241d03050700240c01c0d5160b1388010303503402d40041c005000005031450091100c4029000c0c82d80000c45103440003803010700c203000700d1802c0360704940611b1404404040c1e552a24409030b01c484241903d0740c0e0722141d1781d4903010130001c0710140e550140914240d206d01d40c0380764000680c46a442030324103100020240c0d03210310300940c121100701e80743e295040340d1460984400c14942c0c005803207910240400070705c1030390782c20050002041d940d41d0140c06038401041070b10814014080d02d000d0780d254446e0440d500c520303207000b403003005014100700d814010b00c0c42c1407074981918000b00e00211a004601040480b6901c441c6103000b1018400d030605000004001c00d40c0024541864101081001e4134100f6160040c420b000c000540681a1a0500712003c4090054800c20b00e00c1d078018070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 822946726 1250 822945476 822945509
    0x30706150501120902010c030c05030c15011806080606190e011814070807050c2104030201030605030f370303050f100501020c04020309070e040507082a120c0415 71
    0xc40d9481107001e13041c0d050311180101c10594804a900c1561200c04481d180700030400c01c149103c08104c0040c404c0c2c010348019020b0341c1043c1100280b024400c0c3c00703400687c02c141d028450081c0124180760f00c02010f42c0d881104031404200e01d50480c070140d02030a440f0b01b18800109800719510050101c001c00b0100500514010300700d4990800ca04466440004580401061025204800a010f089507031012604002c0e50164110768050341440909009040003608008658040c0220002070204901400140700c41d0f0002940f1030030040c0322002c80d80d09401c008004902d42d40d122004804003d100346005c02d0032403901034028042907496030b0300070380c6d1100022989112184003030169241030b40030713001e070800450078040070350400b40400b5114040c0f80c6010668001c81c456681c401c50040004015180c64468079900340414500b1207030b14000d101094034003104041c0c422400d40d1320240e50103c242c840c0120000e00b8848804070140e401400d14940c080040c21203001c03401510340380d144914401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 822947976 1250 822946726 822946757
    0x180a0f060818101e020c010b090117120a1202030108101104150e063106020102030601051602010306151709070501171e01180b1e0d05030706150501 65
    0xa03040d044144603a039002d0640c1e4200f0034040e410410a015003c2d01c0151584414008801640c20800080c480382e955882c1c1500da510340103241d6401440313000b079000c50304013814469030780308e000c80300070a914618001008150980b0400001c00d03d20071b00c010440d1603586840c0500c1d21080c3c9820848001810804800c0c0341e1035852084a0031a0300d200c00c0220150b02420301a240c0720211014598000e006018802e100d00d44a680191740000010000d0700300c08103023042c0b06030034886170041360440e803041c020000c051b44c109003101d44055490355003510800291004801410094114100106907459502e00003a00074603100d8440418904144295880b4010a035480b0040d100d81d50000d603209c40d81c4500601c1100241d50052643c030a09010302d0711082080c2100b072420780c05107101c00090215017101c680c0c14841c24016a1044a186850316048180d0549070002111507611920051742c60b582003200030400c440c1c4490f40b042d014401900241341e0840302e401c4e940f0a650101b0130b06e0980283c43e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 822949226 1250 822947976 822948001
    0xc010501060801090b01110705040f090501090809150702030d0e300f010203060d021c05120a0e0306070806044805040e1612020d0506120705030a0602180a0f0608 71
    0x11f0543c040010080c161500c0f08000203011001d040300000b903940c16108020030310a01441d0b510278040e0790315550f103000b210284618084112911440328006201050041c2d4010501058004952a028645c01c00c540009131080c0620410004540658041c075601081502500c88001c0840420345a840d0904c00032282130348000c44586a000c042e400e00d001c0189824841d02c07140310082d00c0161421034645c0d03105441c141d040d0800410751000800d8260141ea030000b0601200784055015202c00d0811840143c0803110240ca45445161a912212080449008102644405001c02800c1004040708105142d0910a011120078081d4112003201034041c0d400c946c111003c412400c07456598100140c0c3c040310b18541340d8001c1107800d660860080745617001030405440c00350340014040c00c02d50104241c05885041000c010b40250900700590303940400c00408540d0130420150b07a510454641094425034904c405a2000c00313413402040c0600c10220040560300c1640f2240700c19207803211a16030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 822950476 1250 822949226 822949247
    0x30f01030201180e13051c020601030605160815271806091c0e0d03111005070c0b0603070308030117060c07211202030a090308010e061809030c010501060801090b01 72
    0x941503048001702c0d103c050f1040d03060606a01a070b00b542d00c21826804041014820b10b40c4000c010382c00b0703800500500443e80701c0d6580100080c0e038a1080021101406003219000400d0750b403050707a04444c103210310b4940032034042e010043c165010f92070194038110103252110540d4010304010141151025000c400240300e4019280840145060002c000b0b0810828800300b020b60104072600e14400c44607120303030041c0e00e10700e0321a07100c003045000d200342d6842c47c001c6a108182d0003682400c06000e100754220f9040151240c01812a0340550745040c040f03450000d0359400181106000000094042d182d81e031840b080c40c08490036901c5586607401c261400e070045240c0505003491120b421002c00c000400040f5141565013848010a0000743d00c070422030b00100d07020328066894038031903420558840f900034003400300c044200c02e0906000d000315005110101c0000556410540855000780c000c0060300d0201550760004d004079a119100104549428440e04410504016003611a580601d0078003a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 822951726 1250 822950476 822950489
    0x2041d0c0309070b07030c051501090b04060f170106120302010c11060615030403030e0d050417030322081213120c031d0112020d02072619030b06030f0103020118 71
    0xf6150400f158200241d1001c1400c0701440f01c2203801c0d40000c6d0040c03003140700f032081021554000d585403001401c15251520141c5108034503204042c01036a401211030740c196191403521844039620b481040c0c0c01002c094120310361440c2000112802c00d44e054004100e0061256184030300311100c524a1599a0002c0d10b801c0e0f844001c0ca0040101c4042420283d0b40c864080e00c2c1c04039640035010302240c2400d003144503800c00180000340500c11098a0100805541c1000000318034614080340c0066000200d200c0b54440803000141d02810f100400054600341d1403c0b040c008400e0814102080016402c940100c0d01045032031000c0980d00d000d0000102e20941603180e02c10500c071000e075420380011485d8082c82c184a40305481c620030a4451020304040100c40c1030050351043c0c10708100038000030840610403c5d201c481600c103030006c802800d0755000300000004044501005600f41c000e0403074000000d8002d90301100f0481c0030f41e105241141268001c1e00e420f2003d0a040d507500c07184030018024003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 822952976 1250 822951726 822951733
    0x114090103080708030a0f091103010c0e0924130b1c1101081b07031713031d010c0218070306170d1805040207080a0206010506090d0602030a060902041d0c0309 70
    0x10301044c4104003d55001703008040c001030003807501100e402240c501401c252002c4801d1124002d0a090034450704800b81c45034188602010034410014400480040c10300100003003080c034905145041850740c0c40d000c00c4c0146540c91441c0311220060040c913101d80c20034418582e8001130944100080c610079001900158544514100c00b00103481d80c1034080d0940c04c5444240c1c030f0a000f40d10400c07015000e0305119649014a05208080c8400d840c10050320440386016560400c10000760003c182d5804d1303c0380c400354051610084001a41d9004e411035019400048001242c51003e2103900c2051144055441c1080312603110346c815682c0084c901c40103030403540b0202894070100e00620a800703221295031221040a0385410208040c2d030405001207420810208419280c10340502890380034040580b800c5041900040002d00340e0000100c014200c01c1e4000301050940327080390015000380042d25015913031203644182800b29461650003c60100040740007040030488a1411240149501d1008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 822954226 1250 822952976 822952987
    0xd121805010309080d090515010902180a080c010807050f030103110415050a140a05030f061e040305030103080f3f09060606090616120f050c0d0f0207090e06011409010308 75
    0x11030041c946e01c0010f40d403520900640111644800340700314040c000c1c8110158843d4a10b035110030030a2000351f8038622603d2102c0d410302841030001160951880c1c2440e101c6a40d8454503003d61b050f00c030360207403080344200020010080c8000000544040340c01910100f0054401c04100b0180740010b004041e8000c0100108001c0c08007540c0c15012134100c0202000c101c10342d248006071034804995042495074111108110b0017000c1142007803c1d040c1100354980c42da140994004049220500006000c81400303d095600803101000750b90a079402c24100104001c114a01c4000910041c46160701c00098170181c0e802041d82181c01cac41c002c0102c00e00038032681e120501000841d4100245154001c1c1060110700c44a1426044a643c83c0d4081c0381100318070184640020144d8081400c0d603020700904000c00c9014030340014101c0030440d61071501c0700c0468048142242017401983c0090541030822506081d59100880e00a04a40406d4444c03c1c200d09103500740302c01051700340300c00390000c3c005100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 822955476 1250 822954226 822954247
    0x5030403170c1f0209220501080d0f0f0306051c1104090309170a0813080d0c12141606020d0f0b150f0f0a08040201140c0712020d12180501030908 64
    0x9101c8450f441c818005410701c90b681021441030350501554100302c40341d90101941d44c0c4024070400f070140181c1c901400007140420b102500245070703802e01404014406c0034074940c1324884d910041c060b01008180106000407a2043c0000c0d0102c80c40a461400d0041c120123800d107010300c00d001140b541503c1d03d040507840d010990301da00d5041c00041e01075000d2032000c2c50009140302c0045c4101100041a050082d00300010686080c621300c80c52000c1c418410f801c1d4002c242e94000d01231b0841341c1442e2601413a5402040c04045024004800800c9a22010b00c0390130045079401030300a00107600302c100072803800104400150398212410340d800c0061458044240840100149401800703c400e29282c0385003100d503e82aa840040c07004000340c14401032201315a4025081c0c0c00e1100502425810b00020403000c1b521340d0103074400c811208602108100840d100c4510504031683c028988010080d540800500380c0c04440310081842c2201c24004100c96001c0d100b920092600804410300f003151160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 822956726 1250 822955476 822955513
    0x20c090a020c03072301060f05240a030b030616050712020f1501050415050307050105070303290907080c03060d060e100204051503090309041d0a05030403170c 70
    0x2094500440d8080110781e1040780704000410203140305d880001800c1c00c41480a02c0500000c01d103c115a0341030980c20452842c1d2160104180d0340112508080600400980090b51440820221a901010400203120703078055021494100d0103900392200c90f6154000c0b545034a8590f045e01c80402c200744000d03004110a603480459078407050044484d580b00401c0e882d0b140c401981d807400c07c44000100180050704203030203004015002c03006028503090400c7c0010351233507028011b003810880003203001020316210350481d1008092406821034041c08010302139001794180c0d98007034001d00c200c0c40810003540c81801002d00c03548903200c00c1815500d8207010132a5103000321901b514500e895031a440e40e02403043c801442d881010100c0166038614103c14020b505581501036038846209004010040c5000301c11210740d5402110001034240340396000c60315180111000d60114442c1072026030400c040000201306903400f410040c0d85040c0c9034001d841d428030a251780440700303130001c1860004280e0941d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 822957976 1250 822956726 822956731
    0x6040e0a0f03110f070b0d1a0f0f03030d020301080a0506130f0b07111c03180308040b0705040305100203060102100c0f0e120f03031608011d04020a090912030501060906020c09 77
    0x1100384e4402c5400c180f115483d000c40b90700001d005000011b98000101d00a00c039094500414100300c204802021000031070347c803200c103502402510961900000e690b424011234601d042d030107008544075611350005a03030700c00e07211408442074410500410b0502d2416510014256840100519242c2c5140d03100300c1d40c1078016254605200c6000c0000d840d4010911010340613084010200194801181004050324864110100500b01c800c580c0c80c08a0381c007044203603109401c84011450754590320802ca615205607800035115000d04000f1200501070341d00218041d0000741e003207440f0f0649083c4000c2c12160502015000310340107010a1118500400e4110710038800240049205401c1c0c0c1c4003c0c0c1881c070462440d609681001040045096482c0c0005452401c00d141c203283c150304261002e880805109070701d502050482c40042c0843d503e100028020746205041446080102c0c0342c0401802030000406000c241083d0002c0382c96446079107008101d494a9000340040900358050220043d0007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 822959226 1250 822957976 822958007
    0x91d06010b1e041203020a0b061c060509030c03070c30021c0803070918020408060f2a0a0e030604020906044206080910180c030b06040e0a0f03 63
    0x611000800303a805100130340c2150b000e038000d05003005540c41d00100d20100180310720302c03070154010f040c8040c6180a528030003584d80907400003001d07120001124518020781e80f100c44140710000304c070300420940f02c40410842c0c01500304402036840f2007000c0518940341c4181903071203a1a201801000d440c01120035403000055041000c2e031441c5688440c45154022904013000c600084010080b0441c2c6030100d484c040d046080460a141c2030503645031325080054024407000b0a842c01080030144648000d95000c4d800c042500d40b900066403180407560000080e42d0302080b0005020300450070041513040c03007a40c5c010000c4560f540c0b04d1007000010010100c000f45100500f00003000d4056052611010300200344c00c052800400701586035060b10700381e400c541d04000d5002c1c2440001b900c00180c441c0c64240700710012840725400c0d01c240e4000101410050a0580352034000400c0c09051030b07086004070f10a64083c4440e1046008240e591000780100030040c0e8000504440803901c0340d00d02040d014803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 822960476 1250 822959226 822959287
    0xc0f02090a090609110109060e03031914041d0603011505150c0f01050924010b0a1e0f0f02010c0e0d0c05030a060e0106090c120c0513091d06010b 64
    0x4040e03c5240485581a0341220381c50015040c1422640c0c00241d2400106028605960400c0b00d80d07010070388a0180000800103400d005c018850154020100c0ba81c1c900c0c000116543c643d5601c840c00c0300c44003103441d0a801c40f032440c0c0020801038141801000b00c401600c031068803146251506100c020100107654003c90b20707003484241c07a4080e003400703a2410020464004240760800780d030502e08010300907582c002081c0e04040900500e100d001880d5045038076400300303d0b4407000014000c4d00c08032248104407840130080340a03511204e0300141e038034440050b00d8ad940d0801580000c02607080b074030820f070918042510003105410501d000406507102c030744140741c40000c5603a1000403d01c0c048044e50203e074559114403081c00c0410092207818024809410107018118a00101501c90760b1800c1c41355060035282c28051400f64054400ca07504c291031040c529901e607030b4900060000b8140c0c10030300101d0640c3d09030402c651040000b60745060710441c55015180c880d032022004030912005d4240a101300707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 822961726 1250 822960476 822960491
    0x3030f07020a0e091e16080106150c0b040803060607300206100b07080c030c250e0a0b0d05060c1c05010605091908030a0e10020f100911131b0c0f02090a 67
    0x1b02401d20050041c140140049600350405401c0c81712446103a815004000c0140e2114012510001c0034940042c0c01420072581c81d03c8580210310703d03120701c4001070900d00d110f00c0c0680d20720403e403400c4452812441001070101907000700c1280c403841d0644001048280d820000d001c0180c6c01c00040814520031303c1d21130b141001c071034001800d50304142c2c410801504140c10301e16910520728014880100d407080c5d4506443c0c1081140003000c13401424170404140e403003400340c0f6540c607001c56111609400c181103035903034902801619113550120311222032050015190860510f82c40c043c03d030503a00305444060420303400c070062100000b1442d080c00003500410000181403030303051000340a000059a80c04c0e40c000260007d010746a01030144600031503024442110101c0e4010130008030000c010900401c4101207401d001d07021004180d1a1135200340e200038101d004034201e5021800c1c000048815183c0103112400599480c10340600241a005400182030014500103185030340c402e000f00700008012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 822962976 1250 822961726 822961753
    0xb0604090e010b13060302010206070c151406011b110105070c1d0a0605011d04152103230d091502070f02090a090804050d020f03030f07020a0e091e 65
    0x1ca1070920100000e035542c9601e442141460300043c0070075007000a041c4800da207190300003903a0710001001a4104030036000407500304a0021850082c20340c1068052280c8051148800792207031060714900e001c1448421150020200c06148081c1d0035003200b110702d10381202c10015901a400741c001243c03240c0d00d150012400e203510410b050000240300340b81610034038021400740c0807100b0360703003000c0d05100c0348001c03c40c038007001c0640325070b101081510082703409640c0c82942c080e84081504990741520304180c071030410410400090030081d009a5480507503410a5107040d1240c583e0200c9200220410006480b8046880d004044841c3c4504040b100e001030090081e001c0340c0061208851102d12103500e942507107840714000d41c203c484c58004018008540c1d03a40c524074813607840340500403640c01400c0d0080d5030758112240468140941603a035034240041c0040d8096000c40802c9125241800010034004020b81c1d03800d20808204c801420150510304010000812035110805144200c1c042d02c0c101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 822964226 1250 822962976 822962981
    0x10b0a050c0d0f2607180515070209011d041b1a03090d020606030d0e04090c0e0a1a0105031305010b03121b1b0904060b060301030807050c0f130b060409 67
    0x80031829510f510380c41d0b036003200003810700744410103096035103000e20f10902e0031414280b84a508401c8a007420a42c00e1442e007115650b554480d0310a9900011042c80300382031410480042100f10301c01c4a414401d681c9032184107600340c1d05591041e94010300e010001c0c0c00079800d40c100101014a84400d000a140da038801d041415245c074441798101c180c080180280008100a1790036100d5245c0094805840c02e00042555202c00c1c1c0025400c02c10700300303000021b50301c0f81d5201e43c0d82a600070300c0b05010151a200c900d02d0740102079816401d41c42c501010792140d03840864416000503c16514917142da11150300c2e00d41071000c9800705888556176a04200002d1f42e0070490250741c1d5280e1103016454010740f42442040b000320380200c803441d40000c0241c00d290310004100c01824903046501c81c500b030302d503401c0041c028120780d03070302c5900440c00000100600150002a10070140308008a40c4200a50818080301042c40e84440782c01c04803000b00b01c0c00d162460340250582c45001b0705000d0905540e02001e205 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 822965476 1250 822964226 822964243
    0x18051c0c2306070e2b080a09050310020a050a200d0f030609110a080403020304120c0311010f080c031321090e0103030f031508010903031505011106010b0a050c 70
    0x32240d00110314208607020601c980ea9200e00241001c1c0401444180030900d1261040c254810101c202d0b040c52402c0324054800d252901e0708202c03020344401c150680686000f6a602030303103203c2d229004079580c030f00c030385802100c070b01d080c039580c80a09009040e0340a4802c8030b400340403900c01414401d0b99140c214001c0001411040b540d80e071310441d40c641c00b034014048481680201110a05150b46407840b001d909007104c80d10791841c40c00c007010b0790381c1d420101d00394000c1c0d40046c50310b486100000800e01c90784920100039640120030311110300445900555003945158610750100d01108000f402c43d41410025607400fa01d40b42510b00d65040603511014014880f103c40c44142c46280d1b0403440080e4880e0021010b491541021000d6504584024203030203441c101300c41c105030310369941c50401c418803c500e400a042c0e0360000d02000c055441d01038060042c0c07a03c20040c003410f6210011703280d07114401d08014902940c000e82007a900b0010f9800d442d80c4001c1d0680305002c0100a8403500d500200040035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 822966726 1250 822965476 822965513
    0x30b030a03020d11070501080103020607081201030b01053109030306050411031504060315180c0905150105041a07050a020a0e010311150414010212180418051c0c 71
    0x10a05002c00019040c058080721404c0320b030f0310140c07040c041030740c22202c80340c1900d4049450684810052401180512654182400d0440624000010480000c11040c1658011030f005805041e4204003501164a2021000342135155101035500c401358940c04182c02e0303402440c01149264850000c28240e071350380c403a54034141c2d03c00010481c0341900d500360714040d14003c507801e0012618585a0007450302807128010f8a140c0e40d0304802c0400e40d8150300414592740d01c955002c0745103560b5500300d0300405040f0781048444221030000c940ca980306101311801d864022400d140201c11b02d04410120742c02219049510b407140002d080c0141e40c0c3e0005d80310043c8001d058003c0b0f258158908502c0250560381110300403408400f410081510a005450030303510001007a50380d8a2411004070b29010602c0300040c040400050016901c9401d2283d02030300280a890601c041003084020a00b000704c40796001e88950040c000741c010350b40084495401a040a141500300203550361104081611201c0e41c81 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 822967976 1250 822966726 822966733
    0x115120302010b0915011b060606050904050f0f1f1a070c090c1d0d0605090c190f1502030d0f05011404151406070b04060b15030c1207030b030a0302 65
    0x4101a8240501c0f040400281d030f070103240d030600c4040c0c0c089030f1200240b07003030620840c3d06100801e400c080d0118400c550b0040e030306024031681d40c90007800950004103881e02460808000a11440e10208202c0c01820a890340c4035484c1e6445d03507510b00782c64031100300c034190f010284c01c0003a80003c22440c03201c003000140c40306030b60784c1410b01e07060035602040e9020548a90400c0b106d0350481d90890417001c100741107828078a80301d89103034002a0f01c600206c00001d203964075200504c61100c01c00103014030f443ea0203a44c1050300542016060b00441c2441c420414440001074050019208460300014000d10030700480e410700256810210650f00e1101d0400985a5510010408100c444030301014420090f01c0810864103c207180c1000d08036a80101100b0854044000c8a00d848007811960095080541081d0701c1c1403529040b0058068007820f03a220314464800000b250000d40f040303d0203040201d410300e00d03081c0202812100c401c00100040309055540301036034401d0300c090100c520024881d9018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 822969226 1250 822967976 822968009
    0x30907030615470306012604110a090e100b041812120c020309041512060b0406090213030f020a12060203060103051006090b09060c010908040305060603061b0c0115 72
    0xd842d0821140036040d401d90140000c1d0b01003c5031440c00700c4e60804400c0c03a12240d90a41324000c1501180e4614500c446581d40c0b10401081c41200d66205079030b15002c84460042d10b82e0388041c1002d4415102c11401190800d181242440425922031b1611140142011403848800000c0e03604028500c4002e0303070325036502c104820b00158041e4110f807803000030320000c022031902d012000b5aa03004070100305004554a04102c0f440c045100c192200070403c0ca8a2001c0c10804c520b0800c000d040c1c51825540200d00306400841c81c0e040c01d00035a807a411031008540c010618685414203101010001a81c001c3c590b44004620034649800b000d5466008640243e81c1c0d007020070004040310401041e030b10f4208942c100c14401164031075800812200d400c85207a071039110510000d000e80c85071004542c0d540d1700e004403400820039180003400c00c5a000e00103441a50755910305141e2900404c44420301c2291503070001100d080441409071004690b8440001003580c0401d0903070041503582e400c00405068003200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 822970476 1250 822969226 822969299
    0x30306041406010212130f1d0108060c09010f020c03070602031c05010302010c02060a050f030c09011b05030a120b0a030b090d08090d050307030b030703050c120102040317090315070c1106030907030615 88
    0x8c4500401c4448020841d500d0082a602c07040e01805c0c0c2400d04021011401c3c1c28154400c100400b403180004081c0e440c0c1c140d65034406980d80d40401a100d10000c040c01c0013440b002020b10072f00c5d04994042e1900402480154200001a40049540002d0010030720481180c11040c0014520510225584990700d1641c0b41c00034110010a0303000340d02501203e907040001880100948e60b83c01401d04102c007802800c8044100a40746000009402481a0900205001d900c15103d07024a4560050b10320042c0a03103021910741070f042380c0000342d0f0750089103603960741c9201c2d000440d0300c00450300e00000c00111090000b81060076a40c000da40c01c0d8004180c0029620b060036101f40d10b00140d100852502e4519601c60503940310703420f1407154031040416107032800d403002d108444c4040e1240c0703001c40d031619140001418001c04100156103002200d8001c1b6140c1c20400c003168065004a8001c040742807840c0c0d16a0301409452446039030b40c000c0d030309000941c1100c40d100140706180c0c9001404070300c4103054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 822971726 1250 822970476 822970529
    0x30105090906070e0f0a030f2105041409040201050d0f0c030b01020307152409020c0c0d050c280306091209061b050102120108030306041406010212130f 67
    0x90052400341c102d4018007580c40d07000401e2140e00c1e1404e88084000d0316071400007602d41c240903400a0841603141e6105820042d10050400102000222960810b03044200454480c051030040c414016215000c200041c40d000342100ea20501c14074200703142c542c081003010183c40140002108050300e07a611101426054041c3c850b45a07400c2c8011030800c1415180d0aa02c100c16540300e0003d15a1500c2905140e003c41c422801d26983c4944000d1071070381d41d03441c44d00003503200c03488810301d500680b4000b051f11f2404482050b401a0050005c120b40c00c015010020103600413003104000d074100100c10601d50100b0038040006500800e0300140780c80807820400031003c036901c040010800920010700010343c001011610b0b1180401d81e803400f04101d407070614024829034400c02c1d0080748401c00064600703000401148102404d0368103004080c0080f59035882410182c0f00240560401fa20044a01c050340c40908130044030401d040c0c0e0039554403440c00540d4281d5400c007008a8500c1d081011006d810f00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 822972976 1250 822971726 822971731
    0xc1c0c050609180603010f020c070611031e1804060b09190f030305030a11300709170c0913020a080a020a0512011d03130b190f05070b0a0203010509 65
    0x180c500910704110034000551224040f040790f00c101200c40e0124141380c800750b109000c0b031180c442d0300b1551552a1040690b90b5821441000001000c584020306904804025280c0c6110240941c7c0e20304100c144140003650404400050360781100d007202402560380303000c4c1764018054408207950b0750000d00c0038031280c480c00c88009030100c0305180003080680c860052043c1201e0305860420f850391640c54810025015045000c59400d40100b110305440030440c0d070642d003c1d1040c00540799030f0500030016007100311044400c00301250311203004001b00e035039021440600d60f000105903a42d031144039001509480c03040d034040c9440d1514164000c00c6091088811000e03100250052051451503400120303441c0701e0f4040c040c00ba0469102c24540403000750059200b03222080076030b8000312403841c00240c1c1c94005070310300501095481c4000800000b003004071014103a020300d07412001c40d9005400d40300301c00c25081c6a42003240401c010b0001c0b40440d07504034007450b0a508050fa481d45004200310840601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 822974226 1250 822972976 822972979
    0x20f1b03160e011d01081902060d0218010306120b060f010c0203030c030d0b01110304032907031a04020702010e1c05160603060f0803120415141006020118080c0c1c0c05 74
    0x880006005103d40080c0500044c5a04900d010304e1100510100301140500882b10010380c0c00861809a50000707288080071091003a80c0030049180d4512444484494400c0c0103000c480c44200800d1440c144015090120101810f01c0260409513902003880e50b8025402d4070850303000410740050242c41402030010300502480d100841d04000114a9281e209902c4010151400080420412030a200c94600e103010140300c024410f2600701400f82c0600450401a000c0c0803505c03400d10b84502d424402d80c0c2c0c103250107941d2101c8906034101880340624800e0305810316000d5004030383e030004d00d081241802101d40142ca03010450320342407000e000e4030031641120088110000c0d090000034000829035403404400e940100c00381d01d13142402043c010792801510381d03a50074402d4020011581030401400380780407091503005240d076104128200e504c81c0d801c3e000d02104035034110f008203240c44040e0186015101c1540c90b4400400001605007042000703450101c001c515100e8240968290b01d803004010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 822975476 1250 822974226 822974279
    0xd0c120602090306010b070c06120b21070b04150305090109082107050414060702180112200d0b090c1906031b050306010f1e030501080706020f1b03160e01 68
    0x40311f07941e0230701c0035085000d4401000440c485442c0c0c0f10140760051702c59090041c00d558843c01d0104088840c1a0350700c04615130600c1450350014042001c0c400304e804440d05031070810f141d0903041f44224090300c00030740010002d45d25041010041000c41d0010111000f465415443e4000268452601101d00800309004d20905003c00c1022114050500c11003c0c01141c45075030301c07221403000500000460314400190a0507100214030301c80c40c80e210700d02c03250003011508556041215032111112041e00e110b60081e01d03594100001407011407034a50404601e8082c1c501c0041d100c00414455104e5580c0301d200307250440002c20a0320f40500c90080e41d1800300c60301d51030300c00d400c0201900601c005040241008001192014a6807240450148192001d0580720103216880d0008001d41000e028280041c080d0940c00221a40001200100070940b24054130b0380e2404412000e440300b41c2e80a400e074050007071844c40001c40d54003400c40d80c0505048186000c0d9075050000504441103110004001d00f0f1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 822976726 1250 822975476 822975487
    0x1b0303041202010510212111030c0a230a060b010305061f08071202030c09031e120711090906040b06040b060403021e0a0303050705010f09110d0c120602090306010b 72
    0x700ca2501d07501503800c0c00c914403141e40320480e2030070405965a00c01801c0007508031f00340003501e0070098401500701801d944002194079101d500c0ea442e40310741155441581d100301e450030001008d4010840340500d818210440343d26000c0c030309904001c00524126040341c1d8900c8041820368140c403665030080d071b003520300e50450440603950029580c0401c0342c40c0180080100018991482505406010311624500b55107d0822501d081d1064000423040c0344030380141031903608000728181010002200032001000c2001c640000750010741d02611003a079407403149214044041c0c90f1042c11034052001c2900401d1245030074144128a00c40103041c1601c140e05103080e40f22607070764603c2660140e9030100e81200c04e90010611144038603506140003034016002d49800814190064041c090050103400207011099005580400700d58014000a20744544c0550107800c0c1d0811030000781a1a01c202c03000c90306540c4a8040c12410a00901308440094000400782070604041c840503005001c401007190801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 822977976 1250 822976726 822976741
    0x106090e06120c03030d150b070512090301061d0703051803090f1906020a0318180b0a09020d0b120c06030f07030902090f010603050709051011031b03030412020105 72
    0x400760105101c0ca039074001c1e01e00610014450441d402e88001c044a60301ca006e81c501401400d04c0c44102e028015404c040064140040d804440c0d020750701c80050709010f051680e0340c0360550030040d8a19015036840b01c0c08990a070801c0c60041d04185443d0030900c052618480080a03a00b00070030f210f103400164040854000c000000380c9001c00c004540080203a0279040c0414101681028580806450702030005030345500460741c0c080b440c1c0030f43d0358030400b10000000040d0180c1c2e207100d10402441c0e01030880b4450759256000e4290880010b02414419543d020003200342e802c0300f204414a80d81d01e04030115280b800703208140d401044100980b4400c03000d2030000307029000003014040343c80c15400000d282d1900c20740c03100029a03801008920346041c441c03620088000f00b40241c03c00b00b8600400301e82d100340143c070480100c030001000c03c0302c1440d000d9402c580c1844468400502171006100d005103035049110351001e206106002541c0f41e10f440c3c10301c5028100c4054411055914010034040d11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 822979226 1250 822977976 822977999
    0x41109030d0c0c06050901031107030e01022a0603040602070b0127090c030330021305030105090a030f05090d050d0e180c090d1e0303060518180a0c060203040e010609 73
    0xc42d81381d4288680c4516000c00140c0c041d104242c400c078840c0c040080c081003017540003480100703208001c0e400c480240c0844045501402c0c000003c0d40c20307030600c80f0042160303031501c0e000850780607105140141c1403802e00e94440c90b907110280c01c01d0410580e000800a0010300e81c1d0244d01820760424020b0010b43c0d0f5a84908a4100d440e010143c104130154003968080e0300304402030003000c180c410700c501d04014114903160094004c070030454903040b412400090035260500419024098440280569000700e950684080d84840017820a0140620030035a0607034418034215442c0380114080d050030018080c00800c080f103400741036840303021440850b0302c6014900400a40c01035502c001a5039031283e001c0010a00c540c0e000d001001c1c0340c0780101c00180c628030280c11340400c82c4681c809101c0c0584820402090b205000c081010308054a80010400044071085001c1da048400540d809040e580c3c03a4528840c0e50b40c0c000d4405a0700c001000c00c584820f5060752030040078a03141c0031170b8003820310078400803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 822980476 1250 822979226 822979229
    0x7080606071a04080f03010b04050a151d191806090c020303071112032701051b0310080601081c09060c030807200a02090108030903060106110c041109030d0c0c 70
    0x640c1142c0005003001003030801c96038515041c1040c80e443c0c5da0343d103050040942c064003605020740600f410000d62101c9554900c01c041c0d5560310788004004400040500030301c5060700690744410050f05018004c4001e41c6204041c0c000306071400d1504004c9440c0c10143c0e21143c0c84900b13242c1c134003030740030500a5010080e20380001b02031030035034060200d07442d40302e2600300c50482d00d4113111000414020014401101812080300d00345c188070440c509440120308848003143c070418178034180030781e20b6041890305008580c002403411100d041030392921b0000d454108240c0044100c5e034014110018000512840c180701008a881c01040b030608101004000014110006082c0001080414030756030080340586402840e0a80050b00300303000e000704d180d48128900059000d001c031680045910070703000c0212607404038050020001d80e460144106c0b9010a040c9078890300703009602441100e0b503940c0c046d0119103003003400e4040c1c48002801c1050b0404a00d039210744140260114200009038020f22440c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 822981726 1250 822980476 822980513
    0x50d050610022104090f0c021903050301062102031e010e0103080f0a030e0f01020901090918020f1201180209060f031b04060f08030310050108091504030c0602120708060607 76
    0x280000100740307039440f060246400911040b402c0100c42d1081d0401e940c80144005003990840d88072100034002180030020480c0b01400080c010401845030a008200300610003021411540d0107802c1485940300300c0e0816201c00c019003050401c14801c881ca11000c107409001071684071000c0e0352440d40d44181c4c500c1f800c1c5e200d240d03c403408182220300602030b134016520010b015061321628650403050310b000f98090364445000c5605080042180700c010311038003080d05030200440d039040642e6002c110000c0c08030001543c1c086c84041034284041000e0040a4500440c0010301400303014910400241c1c2c0c0c402030809005441640905245603070018000300c4ac0354002c039055802100520105002d04a16041001e040940320400518444004011440755021807419800907071a8001103a1f00e83d400d44003c0540c0d48400c45001c1c1c0311100c211210b400c240b00c0d0030500207051403650340070b090380c10080c18000b05401c1e07242000481034100800da60701000031511146400320b969a4025600458403500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 822982976 1250 822981726 822981763
    0xf0a0506060c0a0309030209010f05031b060c1006090605101209052410050303030123030106051c03020c2d030c0d23030a0c02190b0307050d05061002 66
    0x80c0e19038803040110b400b01c031880015200015040e0901400b542d00a2200b203001d13107002030000860044c0c407a030324425100010054058144003068004c2100c580040065011204200c86054540c0c108801010500381c010082005440c0003162401c032b680c140e104138015600042159142988400c00154140302c10500003034060303050818518051680703202404070401d4262a4031040c000403000c5d44038a07001c510030949a9164000e040c1c0b40d000a1085c8080040118112000c1d200060f0018802c550007600001c0c130a617584002900a64444168190003e14401d504043c141d042c050390800140a0340e6000b020302000b40c2d000210020028054000e1000ba04507400e6503400384020712212034005d0040007488403e04040c450380d90300d48050f000018440d00c41414000000c002c1e1001c0d8901174a840c04105001d2b000d1104030802070015001d6650031502c040b5020100002640c010701ca10b0f640c080e12a03c00c40114004c44201824083c0b14101d10040c6905140d0b0002e4041310b442001003c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 822984226 1250 822982976 822982981
    0x110909010b13031410051302011b030e0303030a1e05070e061b10020301150905010906030c050d09050f010b010c1110020307060603050c01081e0c030612070e07170f0a05 74
    0x25400c49003850300010408012504c9441900e600003031910004103c1c1c0748104001c0d1200310000040c03080403000240802e5090b203200c1203010b04210b0140401c1e000f81003465010100304006030469008a60070b411a40d0b03103413405a007412405c403008402c2900d80d0010005810100c101401843c981460140f241a0000d144902070b4012081014507c4280c4212045006083c012030b000c0d410034000c4070010b1001160018440707100342c189004580c4103031902d05550382442011005412040200c1d01070242c00c000d00c880c4e414042c450303001840d021b40003811965402050b0700d0300f5641c0c00d90344203040243c2003050390080740701d08018402107002252610041140004142e0440c00b580350003a10030740c6491000010b12030007142e03107503c802090341e400249507640c0c80d100380c102c0d100008070105946840005070035030070b90360001c0d50410401840202015038040c011860240160854501c445180d418001416041b03072071007892a00004400003d850408a10701d410000100910142c0352600702 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 822985476 1250 822984226 822984247
    0x3060e07050402070822060507230d09231305040606050607060905010c050c15060102120c0709050c071a100b07080319060f03020d08041d070201110909010b 69
    0x10540042102400544d15480c00d410420030a401964030000c0300c8942e850b50200f065411141501600d9982c3c4030a0304140054543e0070003056481c5016101009124040030030140410134089540c0c7e06a0f180d550640c200380340900750081000b601e030104056a60100c1890780c0c0c0c82e40c1030b1354000307000000085540d1a07040c11800781c801503010a0b00301000003048004d03c425900061041401600240100b00303450b20111614070030101c07024000e030018614240458904411075411200c144110790303110319104048803041c0c1c4080d4100f0030580c042d001c10441c131000b5001d0710750b01c4850040b1041c1040c1f0306495900f003141c07928080c600c0e550510700020340d68455400b5141c0c060403090311500d840f0b084e00c0c580000940d00640700003c8441c800c004403c00f800240c0290300681707459000c5000802c3c903607801d001921031400800c90300c8050900c4041500040da01d232210781c1d000a000091103a0405800103421285c00c014600c07200310082004042640b289010340d41103611f50441160303605401c0301d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 822986726 1250 822985476 822985483
    0x9090513063606050c090a0306020d091704030c08190b1b0a1d0a14042c01060302090f010608180a060c02011a06031b030601110f06190e060103060e 65
    0x7842140c2030303200041440c0b6080c5400b5a00100e0302c210403c20154580c8038100b14980603000490703034443c8000b401440058482c0c0c01500c043e95030ba07040070802c51f01d103a0f61303840107400c1c0d1403000d03104203008a010401d01c48100d50b428000c041c28006802c0f154003a0b022a80313a4080188003421000c1c40d1004204100841011001c0c0c80354482d86481c1c48040000d002049a07030b860700b803000c0041084449035078924104c0299001c48412007070320107001c81e40c4014080034000e5a180e0781c070794204103003d00090620084044001d03080180000968a086204000c03a12101a00f00c5803800b800382d005024054201c40c6003a0020b05121012000303e1548a490b45020989000100824104000c0c0032a85030150000080343c403683c0100102c4035040428007406010865031b21410203901c040c4440d000f03210600a5030041c41c103150480200307007000c242e5442d000511650764030341e034846010040281d02100c007441207000100c506004000524800035565001070001074081d5a80d003801021000d000c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 822987976 1250 822986726 822986771
    0xa110109080601030308040c14030d0813200306010605071a06060423010807020a0b1902070c0b070614060d12050c01110c0c12030403060b060d110a0909051306 70
    0x3402c0700c40075a102e107801850048165011070322102c0000c8042020350602144001050026004040700e4141d000125176081e006020303201a01038501100c00400c05148032040d02c5021101060a90040390091518180f4160300417001c002d414404480000c2000340c1141444114080e001c01d181c8450000515902c142e510018221f40086401d8041e90f600d4241201018000d072036820896039030a10030b9840d130303d4038032006000c05412000158000b2202d4400084030001a400505000c0c1c16924030001140380d4000e0b1111a5000c00c0e20010040903002d000c5076548020111101401e065021400f090034000700103200180c0442d0b0095090b110780700f0f544034090803100920424020410105103a4415504a0701c18008d521035a4020f050050704205544039080003180f4084c910744910009103049026aa8444020003111070322040c03501903102d4120708c182c0b441e43c0d1788034800340292840cae20701d6109452082c2000d0402c00d80243e06084000f400e43c001b6004a45000c065541e046000090b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 822989226 1250 822987976 822987989
    0x8040b04051524030d090303050313060e030301150302130605030a150f26030f0f0c0d0e040f09020a0510020114151302030f0c091206072f0a110109 65
    0x8001000240302101004035031140741d031083e0020800070101810348440060b450305010500301d0340c041002901c076a0003181e01c140d4203001171911681c20707520501a01c00034076000800f6807010005005104216806c0366130340190741021842d00d0080403105030410214400d10041c41004000503400828581201e071690031b28540c403501442d1100f6905140c1101d901850071128041143c0e50b00e050203246240c0c500c0140000190308102d034040018285601420400380108001d0012420b481420003014204d5051a120340c600100040d0a10040303807030b0910289040c6007000c07400e50150301c910040030305071a07041c2c802a800d00048001030740504108140c01e101c1c1000141003264100c0403805003140e004085440040c05250100103101340e0209071102010343c0e2408000c5003035244440020320050078094560301c0018032481c40b00f030a0420482c4d808000c103045251031703406c1d045e900c1e8034180385402d00e0149031001200840c0040c1e5030004100010480c1d22030401894145c0c0c024156200188003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 822990476 1250 822989226 822989263
    0x18060e031209010e010605060f042105150f0603010b0904030f0c0b0a09050d0504060e06091216091b0e0909010e060406091506180c0e0409050f0c1008040b0405 70
    0x2c10140440c001c2078810040d0b14117510f882000304c0c0b2854810103c803594102c1a45541c241828030301e2404000500481805002d0f007003200304000158140908841d64140000e04511443c04e540d04244103800206094840e0745271029913001503649245183d08541c01d403402540c25148541c003a0b503503000c442406014101000104034844007182c0002c641c440c854001e07140b01c3c205041090390140194040c2d0808a29044c2c440495814000b01a05007050b0041510406200360380f840d0b400d0100c0c0302d02c0c0462030341c0c20010500091515010320b002034290103000724000340c03072940014403003a0380c040300510807a0094040f4030031420940084210b480d01030142d60403820549030010007406405c1c0102c0e0805080c00c0100340e00b8000d48100421104540c01c2c07d140c0310316101505005000b0742c2c03030300800c0c0490758000140e662258401d419105210b08002c00070312540c0210141351803050302c0c802e0708c14842402d10180d019401043c0c00d4200b40d00c8030700405183c5a5250181c00c0c081c10440a050300503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 822991726 1250 822990476 822990481
    0x4030f23090301060902091c1509110114040b091306152111030601030e070333051005271905060906100f170702010510060318060e0312 60
    0xc2220010854031100302e000308240c82d07580014034240d01a5007081d65028070624040c00d9641041d5400078800d600c10303150440d80c10002546a0112001c001050310100030300000c028540d40c00c000f401c0c058001080e000c42c182450241190842d00c140d18510b07010b410414070200c9807042d981c2214001c3d080b1803006125580000324024610b0300200105034000c21521080401c1d0b84081c8100d40070b4526000c2c1280c5540e5071100194054204441c05d05180c1c4103140000000c01c220600340000b81c249000e107104240d400009200300500e070407006038501413078442071114a1100f245c584c401c554040d0f904032203510005a1003001b25a0100c42401090303952000c00801c03200750b10102d04031140b1980200481e4645030140101040211440342d000340c0c140c03040c01b540381e0040140ca0000c01480c6415009124100d140d001445016141040582c0d1100c1c1031000314242018881e0207080e2521301000007131074204443c90b030000c000c00080c0c88160790b4111001c4401d0300b80120b5a40d500c103003c0900c000d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 822992976 1250 822991726 822991787
    0x1090b030a1502120a09030e0d1506030804091109180405160e180f071a0d020f0c0c1009121e20150405100201020c0a1103070b09030604030f 62
    0x4c4d8000720114402215000006160305410b1040044803509503880b10040032586040c0410280b0a410130b807130002c42c1c08070705c0c08804400e01440d0007035032052010b641c4480c94081100192032100c0700b9200082c00c1402190b01e136403030301450708401121013080c015084e21642412030a1094400c03840308030494900e80801d0328001e003101c880c003610000204803440f00310300b401c40740c0310803c1403000d110f40e80020702704022270803403d41c0c0035041040080c15603290403907001c02ca508aa01410030070f18888008507050f1b08461017030000800c185030907202a0600d0b0141c4030010507420141c041c0404410107000703404207010540c0c8000c90700e0000a948200346d1b1000381420000683e00300342100e508648906000c482e030a28100b50440e95040010590400e820f00041201d0903080d403250604541d400e000c103112000c2c2c204031080c1594015903d80c5407141c600024541024000e400904c81c2150802c0415000d0300d0004980e64440d800d8581500342001c00081222140c010030301c0c6000380c208403034240010303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 822994226 1250 822992976 822992981
    0xb090f0103091e0b0a0e1b040f0c20060f220c0305060a0516020a1e021009081c0c030f17160216060c080d02090a0b0d0f110301090b030a15 61
    0x354016840300384e550391000c079800c045d24941c0014154680100c4640c44070700d01c20126000410354010004501e07141c0501c40d4100301d4200032442c17400a5000d000da210041c0d0491040310194860300040c1c00300d0310f0100768030700c5203400190080e024800e400040c0310100d1103200c085050698040c1c0c0c10483e0a907241052039440f441550200f40d454034240100340c020440b40c90f08406554513401070314101945807a00310441d50380e445841c850b45000c1d244400181d8810800304490b40d840e031250612941049032040c600030818000d061369512000502c00441d07080b0124107060740c1d05140c1404031031070b10102140d000030004070601e0301691310f205206c10713030000410b98240d0240f158210344540090700084204801e2521681011403402105180403c1c0700c00014854100e803408003500e041c2d44000441d000094650004480402c080b4003002c8072104c0c0e001d02021607060504c20300441441800d004034602c4184280d002690b600c0801110589060080c40394094000042090a080e60b001a602 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 822995476 1250 822994226 822994283
    0x20f130806090714010c050f060703090c0e071209060902031e190c0905250c020406050102031215030109050115050f011803170f1c060f0b090f010309 66
    0x240740205800a46019400908082111030101c6509244581e00f8015218400600c906444500915040085803042006124080c50303c6680c006070000c0107051241c06950503800144486006006210300740b83d001840f51000924a03d0000d550a62454030600811003d400290140210000d0303103111030211a602200d180b02c101900c2604200814449461420440c01070003e5000e00c0e05011140865012580c48407810503140780302c0bc1c040c0e10030310250700c074445050001039609043c8400c604050086000a0100713000840c104047c40b040e9900c4450020541c48031294007110b4000740d03035401d40040d0300b080e8109008101d2221a015030244034181800b4981c099140001d02c500d4651140c4101d03046a84c2290580c9000c80c2542e0754005e4091612050159480c414405216061030090007440b01442a111f14020404140e0a0209582076a84103508000c2960810848001b000c42201c0704201c048038000450180c01d00160014000080c016010311a08080030700c055015044015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 822996726 1250 822995476 822995489
    0xc1a010f14150c03130305030a030f140a090318030804090e070509070c02030a0c0905041401020f0d02090a0909080403050606031207240f2903070b030406020f13 71
    0x31103498254512220040800958100b04600c040362007100640010f40200010316040e2450f024003222800742c080495002a60960400203840080c990544625003c0d200c1510090002401c05014040d000390f00624a5601079242c40500080510a031100b121190345151040240c5890b401d2158079500140980502030b45008a10213410000041c10002c8990041c08100c8641d41c0302021201d20b44070b2803040342c051180385000000107226100000140c00300e81c00019407442c2a00f080144000d0a0761783c11407a034810008243c2c0000c0803011180104008640076a6640703120300441c00c45e140300c0e030103102018076165000041111420051040b03900410480341d0a0311010105620b030300301d10315a44e0b690401002000b00049a5607589001d42da036000c25040c1c0400c054010805940c8052080141a60b4a0301c2e1171400411404c5450491040884400c48207072403071707020a0340d50042c0c0c050f81100c03010200002d020820b05404032180c80d4403102c80d454441880e05190040458140030b43c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 822997976 1250 822996726 822996749
    0x1e050c1e070f05030304030822030b070305060f0406050a09020c0c0d0311061f0909020103090b04030306060906080f011703041e0312030b0307030201080601171f0b030f07050a0c1a01 80
    0x3d00743c0f400005580c184d9400178039036403804d05515002045141221109450b441040d1000000324003515641d6101d41c0142e14045041d10341501080f0480c41c0301e219440c865803500c8820b1100c1d88a801da0081556500d5600580c0c80c980c4200c4180b921101d4142294030580d02e102d13090405510110020650b0100f100710b4400340c0f2904000442c054681c40c262610000e490700c2000a405a41c02089260380107040000e11100681c0b14100e200034101d405402003030700c4240401000354451400e03402080d543c07504405a041031f041c031541d050fa061046140c0c2d03071070710703c0d280c0081e40051007150010301e0340382881003d9007500c05082929441c1848141c40801441001c00e00030350103805455201030005000e04030250071a070054803841380c05440181049075110a4540c058100d07c1128016420701e0002c010b40e8007164040c0c4c00405668202000d501c1041c414002480320f2980d07400d422801c5410640d48880906408881410081d031010b41008044001550810402d00031103041e1800010719 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 822999226 1250 822997976 822997979
    0x102041208090a1514161a0f07020a0302030f07020a2711030403050d0f0b060c16050114031605090a0e060907030209060702041d060915071e050c1e070f 67
    0x42c4541c4c002414440c40210f04464816180700c0801d400400d0700030300020004529003c07680762403202d80c0f00c401100141c40c88240a00c807980d18a406000e078810000c2c80108107110680e5002510b03409100c0f09800114408500d640c1103548154041011b03251844034004a0ba0140c0051402d54009212110005281020f040f5541c0c1100c81101e12680d0143c507110301d8407080e801424001c09140009074280355507042c152090380c0d80d62008007404403018008180140c3c1e10041c038078801c01240c1c04907043c01400301e10070b01c031603660b0302c26250f00035180c8100c140302d404443e0007910a8800d54100660007003002d000445d07103007004449207000e130390700399842030042c1d5401e41b01741d08a100300c500d070b9640600e06100a100529290b04400044401c02c00342c180c45070003101580740303001802d803400c00654101855001d481e01c2e03410001640300d07009190482d1846801e4101c0f1021100c1c8000c40810030000007200d5400481c03c0102c0501540d003940c0e0048bc2000200300152102014064800300140b6100c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 823000476 1250 822999226 822999239
    0x503120601091401121e0204030b0603030a080103081c14010e090a0b3108040e070e0f010c0602130303021c1e0e0a030803100e01080a150b01020102041208090a 70
    0x1140c0043e203503594801d40b43d0f000400c005540061141040399a0316480e040e2030785104038041d0b14440c100c43c400c940542c84600b546000303400380d18010701080c0642e00a106900380a80d004000c581101e42051a46503030b540c0c014a070150710110034030039080c1542030040c420344105402500034125150008002000d07103500107981c2d1142d0b6004030250441d0a0075002c01c90381d07403d0341d00d2441d281a01480c08a11114850510400100444e40a0760289000b090030003010f0780c95074500da0701003a05c0c5070603a0103405510020300081410503007513040090324514002001220350444a070703240c5441819210b240c2c0e03403030300035130301c0d85030f4503110f00c0f40603000a281c4405402000b0003407100d041c0d00090b0280c01c90b800d50444000028403002588480700031000408507416000441c0929200c10800403090701301641e8108644069102056590210282c040810803400004000c0741d0403000c040f1703600b03006c080102e0180c0a16081144203410402c04e2004000b80c043c01008003010a80d00d00030681c0e030707d01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 823001726 1250 823000476 823000487
    0xd0228090b030d120b030f060907060219051917070b22050303010512071503020a0f0f1d12030a0e03060c0a081b13060507020102010b0f0a0302040e010b0402070503120601 75
    0x540d0000300d0710381201d0804d41901c03030b040310b03800d61406411030380d00034140c0101030714115054030856955000004203100c00c40d818401030061a2510342640e03504021507854680d50515a180801d000407011081030800a03881c1040d040c903101101d41549074181820100c0500f1800d03903011000741190f45100c5d210300c0350340882d25042038000c005141180e1030b1030b00b401740070701100c280500b07076004020020600c5aa1203c2500f08103215503030058481d24031070805414070351610280c4007402981d1180c049000e034400840d030008410032500040d01c0719900d02265200c1d401d03002e140705130301000c207803205556404500c90002c030200f01c0032030318035071a0043c60401070302c070341ca220100007500c0d8000242d024029103003101c0c3c0c00000301726a51500001d180070a000326440c2c1c2004000980020b512415580d090096802d290002c0700c14401031101600083c1c00e800507172100078061500c1d040300504450082d40a943c1110010b0800c0d0366402041c0341c0680c896001c01d01e20070241101d5808a01c3c554840d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 823002976 1250 823001726 823001743
    0xc1701050a0902070f0f0c08010c08010509191508031e040b0a2303010303030e1e030306041107150204051905090c03132a170c0d0228090b03 62
    0x307000c0110381402c1c0380790000a948522000e4030820f100d8082d150000e454a0540090b85d400740b00210040da04140c0a982034445d09003130041000940b02c018000b507902c0c20b00040d000780c0390408503003141540c0c2458901510b800d03c0c0e241c0c030301403e0303e01c00108088088003c020032814460390b9039034440240c2c00044c150280380103110028009012800d0094000d00c00c00140c48920b102c01c0003c07056282c4c00860f9640300360000c40c00282c41d100e0f003000c25801080100343d030a984900b2200000d00340003085541380070042c01c03188600e46030f50704550504419022666025040f00d49134141400d2481450041e601901c00c1e00d020710b0041c11610801281c6c038640d801500c6d001000d01c035082c0c980c40e44070b11054002500a4449842808440d00041e00310b40300f03448949102030800c00b030380406250410341104d06500480b00c80c004c610814081c0c01c8003003540c404450045910301e5142c0c00c140040381400001030703507210003540d21b014800c41d030480c0488403504a400039901405440c6c00c81040c1034403103084 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 823004226 1250 823002976 823002979
    0xf06090305030d050403050d0e032113022103040b131203080a050711011a1c030207030f14060f06030c120c04050c1c0506271801020f07060c170105 65
    0xd01000000c103d40d40c0105400900900c3c145040c600d030010350004580209400030110780c8002030078045100c581c100d0080e107000c680055900c624004004001015500c44028803406c140b10081b80d60010481e00c0b00c1a05449000b12034507540c50344048801c0d94001c1c1d0002500c481e000d50b002038001001510240d001d030303140d80d5010175030329010381000181002910280522124880c8803445010920401190160540700c071030031903038203405000c0098200e000c0d08409a0b82c20702a600401c0d000903500044990008034860484850304000c060010300f000310795480d0054005209080c44000a51030007800114141c80d84660010100111091107240d0b03848c480c0c02c85010000d0358509640855404040340300401d02d811403104510021007980d05c2010482c0da918400c0c80058144890700c009942d6079982104607501726030030b00b120343c00340040221070480029040e1200c070013000e405441140103001c503d1a01c500b02d505c1e06402421590812000040b5001d03001230101c400e0b102018101c4a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 823005476 1250 823004226 823004233
    0x13111620031e0c06072109081f1b2d08010e19050901140114091b041e0513060608191e0b031207050d030203060d020306040305040f06090305 62
    0x211a034500c800b081d070a888200306001e06811440076849103c01001d0961040040c0c0100e090320350705d501e482c0e40408208408000d41c240040c41025000240e100020140e05408000304a000c50820042d0816800c2030301640b00310b01c8200c40e610703042902805483c001c0507055108900c802c18000e014074200c8103000000720080c004100710b1000184264011400c840d0300a0040c10510b44071f002d4070710a4410104aa43d2107440c0241140d170080d0050250152500c00d108015001c00041c000c01c2020308003d20801a1131100400c41081c6003c4400614a040c0d0000c1d0403203880d81c082c19240752502c00d45004154102d0801503003295441010195002900c07000019126401c80803600120b035405801030700c0c0e4803d259490fa4004181141700c0000c845000300d00009800b084c1814503003a8051884481c2c01406600c0c0011070116144d007034a4094900182c90350390700b00001d14107001b100400381d018003400d010300042c998081d00401c01d44d5001100c031041c2d1551280100c0300201c80344030243c140c1d003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 823006726 1250 823005476 823005493
    0xb19030c1707050c070305060709050f0303070b0705041509090507030207020307180212090105010807060801060f05031302121015030506011203140c0a1205090105091311162003 78
    0x84140a0303154101c0b1603440d0190500f142d01d582507280c2803a85c0c00544250340720b0020003880c554014414000340c04103076640e04001c002c1c103011a41da030051070303001009550504001141a8817500c00c1d54000c1c40d080c0c10403030030291460750142103440c0703038040e0f400403905003800624414000c0c021074017000d50140081141c18500800300c101000b146501c4000300b50200002003000000c0c3c0d0502e4000e440d8180000b50740d51500210f40e00e0f00300c9a512103001c2c0021140104002604811403060300c1107142001c50b6641e031180c000c03901e011900d45009512020b400e4100b40c51500020740004070b08880c5004015504401250002e11900e52100a01545c0001c005009120f1030f040c250b01c4491080c10a07469101c512000e5011a40026904400b00d5200c0e140803001d114990564bc0c00340691401d10701e01d040b08400c00281503110b04003c0c14042c042031703802c1d034141d070006600112412003034004c1d43d507c1e03246038120042403101180040e6014072410018806c0d071034600300510b80c4114010700619902 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 823007976 1250 823006726 823006757
    0x1602012d0c030201021c0b0f0d05101509020d050403030524120309150a03061a0904020c160b09030129010c05150a0905061305030915040b040b19030c 66
    0x448040022000c55400348146c0306502e240300910210b0403000070000c100003170018180003240f2248500280304005162002c00400c00c08100a0f0b1031554011001c00c414050360b8044601c0d0f103880c0e00c0420319a1000480500700c01050740114005c40c0300751343c01e22180d1502e0003050440b0450340c000c10580340404500da00340e85800d8030221010920142520304010380300f00003c40d6003503415142c50070480c00203107424039103905101d0758025007083c20550390f03001d41e81a10070040d4015420040d0140740c0c00103100250038010450511041001c10100d40150b48500d4910565002045001d00a6003402402d440d1003510740c01c0542d41d040820141400018010011100c031b02a1500070b032914001e01041c112400180c680d000c0c8181c1380d10700049208015454164a4440000d01e100d42d5001a041c01c9400190044100c6011a8003250015044100420713000028451035006103125a800180000c000c83c3c00070141c542c41303181d40010300c90303158107240c00d0f8140d03060a2055400100c035000c142d9100e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 823009226 1250 823007976 823007987
    0xe0315070f0903060603080316110604080a02010e0616030f1a04150906060c150c080402040f06051314100e06091009020703030f0509030408301602012d 67
    0x3041c5840c1c81000c0c00e0303603601c400040b10000d0b00207544180e0004104607401000c100100401656403502460914140c5d503042d4407072902400040040c0ca0004640d04014070075080300350750083c0c10003506c5182c01c1ca03000c085890101c482841d40440d041c41c0b0794003d0b80701ca80c4035254118a016113100340c0403042c10100002000f032004036018001802402290200356072261070003600c40c0e42c0b01c03140711803c58140b54013440100c110300214941008011244140d010440c00d070010b60503140441c1007100211050050055608416046018807a005911600d55008170300c04113107252007540c154548440660481d411030082020388650000825480c0c01d120f03c0300b96004200c80700306c520164a800452043e40d01103241600000d890b00d030100b000b02403d205c0d03540c2100300d41000f03500d4249400e048070b403200300080c10081d07441c40d4000030840e51100c4900e001c4144c03203c04450342e51080b0000100c605198600000d9000945510381c2d440258000d540d21203604100d03560b02c11038138240020842d50b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 823010476 1250 823009226 823009247
    0xc0515040f08030c0409060b091806030f12030f0108010c0516060204050d060905011413031d030706110709020a17060a17010c031109010503011a0c100c0e031507 71
    0x70200c4040c02050040342c02c001c06540180c28080105564514144903181a5517154100341e45c0d4240030030a584180c0e4589200740c6400d94001070248a9a03184400681080d07c001070902c1c0302d0041000e08400201000700640c42040c0c141c003420031a1b40c85400c9c103800c9403441c0c00001c3c0030070010052600c0c1c440310040c01c50303403143c0315603070261629499801103101d00d6840c40f01180e02d5902e501c0b4a0341041003e02030801103a1003a61600000e2078200c818200f901d07004c04c0c0107420f004903050b100702a01405c0303d041525030006401c03583d0703d85d5241002804024650714143c0580183e500c041540c0805000b01d590380301440e0707610300c6814100400c91002c000042c0070f50341c1c40455440001000001d00d0b007a861040203030000083d961054401c00380940b14400380004040a0820031f418203681c020b0b094a043d6a1010030f2862110030310f80300c039100c40c41992503441480c803401d442000d403c10079070030049040c4550b41e0b9040001c03451205065486049845242003442c498000840c0c0781e02c03135a0a0749 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 823011726 1250 823010476 823010483
    0x60a030b04141c1205040203031605010b06041401090f030c0501050d0b030a03020309010212160b07110a060603140c0108150a030c090207020306250804020d0b07020a0b070c051504 79
    0x381d00800c8400304516042e030466012070b07145484850f620065070020101030b0280b4507041e0503c20340ca0258002501d03889168540d00f5002100421a4240071095002100c600d04c00380201e5625507d850484400c1ca0184081600151060301e020030a2003111000204990703120841d1214542050011b4a2580001d01403665142d92070340f070144151303030421002c1076180c040e802030342d51075015000090806500500f1580c0d0350030308002c84826040b11041d228002d40d0086501c10303843d2a40310040b07808203120080c2c01c429214104e8100c3c140710139540b0a8085038400c07801c0c0c0150500180c0c5840d159a05540d4003400310301c40c0340000c1c400c00c0e10701c05103c2c6003c20080c01c040f15503840780d03100b00e6068425044214076035404105e1608504003044020782181400c0c548155452070302e00704c450b00c0c1c600140703640300300003030403000c2011910307100300340750f805580004800c0c0c1618089600030759807000c44509644c094922400b00780e0043c050202001c90a41000c00b40c491a00d40c00c5100301424005030049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 823012976 1250 823011726 823011743
    0x608030313230613020f03011404021908071a0c071701060e04150c1112030a051513020d0906060b0a09091b18080609061b13060c03090807120201080f060a030b04 71
    0x83e2261f85c0030310591607039581c010002600c41c145030043c0002007030031205c40c0030000d803031501c14000e03440002007140448020713484400c12503107440c0401640d8000d00d03c8011440c4180000405d0600304010030b001c03880414030003081410b40e5600e001500d104240c80240029940308040d442176491500200001051760615101c511041e60b2034510703000300082071100d180008400d01200c01581e00507182c00c5500c5c412b28500b070820030400a250039594900c8000d031280d000410b18040192500290000707900130b40108103140d0f640440b01c0259228101410026a1031100800c0500c0c140c031038008070503c01c812002d410040c01100741e9400d92102c0f95507680440482c800941c000d000c1250501c40d035032190180c03006050061301e0b0f1020005000700c0000c56441407001041842c0f078030301070701d08450551624002001050505442c0003a45070080200c42c06101c0010903c1300c0f140d1400c038006407003030340c3d2035039555184200c40d400102c041d070b2015404640341d001000400d0102d640c1d0b941081c05813060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 823014226 1250 823012976 823012999
    0xe0105010e4614070f12060902040303200111042610020903150403051806090d05011a040203130b041a0f01170a05060c030a060803031323061302 64
    0x2034407108580420207005211240302c1e5000c0301d84040c06280b20406900d003c00c03160781082a0003800d2900c8100002c4108000246030a01594032508044014003589004641e110b4890030001c180880c1c00810100c44041c440c00701c0038a000500c04d00c444036200c01101d9041500789041034031b001c500d40c2d100d44288440c0c0f0200e007034040410700110016280c2d2030300040c0c0e43c5080006160401c5403204c44d1a001ea1132002c10000800c0c3c00200f00c504500c41000c841d5115a24080002c250f800341900380364000105c8050f1100b0802c0c150706c030340c009103220b424244403140341c0c40410003a4401114010031403e00c03a43c1d468001450025056009485280304891300100b94510f031821080483d07a510310102070000401241000c552102c002d00c03800f50203082c440c4000c1e200c540d507407140a055801c0f01107000000415411442e0302c0a80505040710603030b84d03207040c95152a03c0d11000b5074800d0700c00d00540c4400c400780041c00c41140fa24034021070050728155413030500311590707040c03407103020398010000c0340d403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 823015476 1250 823014226 823014301
    0x122a16060b01032d05010602150f220515090307020607060f180b011d0405030a0804230309090601170103030e01030b040f090b0a271416090e0105010e 66
    0x184c8050400e580d0000e020710415580702c0106949040e0300c540c0654105c1c42214512000140300d40d030348003000080f042d81039100e03c4400c80c0a0601203070031549040c0002c110702f0401c0004529441c140c4c4000700e90030301640300c226009440b8401c00200a500080810107000010171b80d0300a0110641c020000198545030560310054443c1c0048049031040d44004c01071000003552583e15158000640101c0c0351490b20355a525900d20407141c1107000c0c001d031040010200000040040380e80d100032610f0740010a81032600c1540c07504821585481551400c0004d1081e52080c00c41d02100d528502c03e42503180d00e03688003910100f000034001410962039440c049a280c81c1c078040e8500d0448a140006521189812f01291340c000150141c0030b507604001002c1c450521941100c0742904580c405541108014504011805000c0240c4821801148880e400b00e641b400c404000b00c85503418207018520000e11343e030f401c0b508240100e0124000706000301d2283d02d058264000c2030b0b42d48a0409042050445 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 823016726 1250 823015476 823015511
    0x1a10082e0c0c06060b070c141f050a020f0a0b0f070225080c0901081c0e030a0b0103021201090c1401050c100515030a0c1406122a16060b0103 62
    0x1401000451a80110b0404010342845500c0003440c0215a1900b00381490b81da00a00105034860104082d064486400040d42e602c00c2011004040c10030314101e09440c0e010203011900b00b60a908054000c10f2000d001c10840846e10049207a40a20080155034909000b0606800c0142c8094214822004900c1c25009503d1440001902200c0400111494040150304d0010481d100500030620344004010b468000600700801012400c68054010641141114090103c0c4840f030b5040c81089035080c10b010b180c4452074143e900039160594181c021247c000d00303940989000400e8041408400c0214410f44040044228014508140f0b40001e05180510301400f40c0c2d500d0070700360368540504c000303880b11940400e0302050a07805082c00b0f4606813034058154190b40300d9444503c400015a40507503985500b21488054081d0440320300d800e100d02215040e64040066408041d442c0b0902d01240307040c5401c1d117070711100756130028514015541da940050003200e640d46043c55142c03401c80c0380e10071618 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 823017976 1250 823016726 823016741
    0x1f03020f040905160308120603160605361c0f03080c04090905060f090705010509040c0c0c030f11090411130608031b070e01081b1c1a10082e 62
    0x42000e41d48501147c008084011009421248241d0221b03100940c5810203008010031103084d0309140d6141c11003643c11495141c030030700c3d540c0008644880154000205214600c0c0f0041054400140c802c100d03520701c22640303103052030181c414140c4d500c5090000b80f090507519801030416003001c0c103042e034030200301e800d0f20103003901224640c102604001c007160074070306120343c040c2400f4020a00d4901e0040042c040340314922700315005540700c010500840f030090961035885903100c03652500c03007035480c01c0c0100034070154075049815050410200c40d90345000d0080d40d0003182c1291001e107488800d43d00300104c94ac1440300d104247c94882c00b00041168043c0041c2c03503d403041e80582820000001e4140d4200030340d0707401c0158103c89100040c0003600c0000303080e40c2c4400c46180c000c1c00182c98140040e0440c1c0051a010144500740090402003001c0000c140c48500030200d240d16035511a031071107003203002140c0111203895001940f030810541c10405420f603001500c403240d04840313080b60031000903200794 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 823019226 1250 823017976 823017983
    0xb030a0b042105162003070b0c06070302030f13050c1035060d0602070602070309060e0a06050f1b120306150405100507060b090a051f03020f0409051603 67
    0x300611240840a020400034810036030f80307040c520300303c1601011400540c415030f014120390070190440808038040810241c40800007003c8441d5180d442240da0b0f002d80c40901d80180e14060040812000d50281c002d40e8062103402c0031048140d990740c0140940c0e110202010b42d068071840c80034a4642d00d8040c1c180010400c0da035581051642007906001071803c0b200341c44400ca0b12210780c3d010441c03c0002400b40c12400c1100d5884c03c520190402201900800c0700140070755200048800400d600100700c80110b402d141c1302c4035809044601048250100c901c038203404594104080128800c0c1a401001000b079203600c610b200c8508200942d240140348171042c012100d00006100e150300d0004621940c000506c1c0c5200d140a043c0700100b162000e0910301c41080c0030000c10840c041140b141c0000b5001c80008d0050291480c0155188015000a842e050068120507401c004100060340340c040541c1d40182c035422150003454203100040c052000b054840703028240c00a8a0000d080c1d1400005601 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 823020476 1250 823019226 823019243
    0x504170316060c11060f04111201020a051902030a0c081e0304440703051b1615080c03061503090c040c0e0f24040f03050708070f090b030a0b04 63
    0x10a05400380c07048568041303000c1d0940c005010046092003291240d50b00507032040140c0a403103000c3c80030801000c01c842c6007903d154008600494103da115028120403e18241828840112104282d85a118190741b03000011001d144520205c0c078050000c00090800c1c0c20780d01e44034059155001c0c407a4009036400c40e180c05583c1034035940c0848440c0060040000c004039083d0002c0c040c06c503070307030f41d0400748400179120000455428140760140080c1c07445049078590000128a0100314562100380c0c6985c0f01c82c94060030007006c212404848020150403171203449418094031036210945803504010301c02070380710002242043d6040103800c06980559400801030aa0003104001c1101383d80c44140600104101c1204103c4c07540d948155130070041c03006a507000c007904406d0740d0100220100c400d0281c02c0c90f900050020700d00300110b00741811603000300c054418a80c0c81e07458552b111806482011007442108409204a807040d901611103401d00078200c440004d15952030915a40301224107544084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 823021582 1106 823020476 823020491
    0x121205070602070609050d0906091e050d0803010306050f0c030705160b070c0c0f050102060412170a0902100f08070e150c06100f06050417031606 64
    0x10340040c0c00b50f5940b83c032814200080d00b06080100c49034450341d0003c4d000c0f40d100d1031012040d6400d640da00c1750304503e400e000c207150601400748007080a1911030002000d6443e2124000c04030b1164103920386a40c59820316a0840303600400d480c3c06c40c501070040140c4c0310140b9040700d9011060741411a1140c0507a16546800300c00c2d88001040040d251003441110303500300c44144440382c410038180c1c18480c0c482803456150405446900c2c050b03401400840c0029817807c80c0b03450800c0d6249401b0940c1303210152244505d140507218201d40e80c0d915441503041d03084c00468941c2400c81e5080c030807080c000f0b600d00200241c0000b0b089500b0011105c1d02091a0f0341d0f0351000c07039400704c0561505030310b41004015880c0c48200940da182c81c40403403400000361006613403140804441c999260f80b07080c5490b000300c0909022040e0f0340860031b40010041a03051001030030381810301500442e40000c0301c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 822841726 823021582 := by
  have h0 := BRFrame.cov_init 822841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 822841726 ≤ n) (h2 : n < 823021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
