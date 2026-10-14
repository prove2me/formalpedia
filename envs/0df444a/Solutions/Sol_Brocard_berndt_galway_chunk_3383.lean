-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3383
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:21.513906+00:00
-- url     : https://prove2.me/submissions/96fa3d4b-7c7b-4e85-b2c0-698a1809739c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 608273381 ≤ n < 608453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 608274631 1250 608273381 608273383
    0xc110c030f10020306040906060f080c06090a151101330303020303160201110304080304201c021c030c02010908030309031b160e06030706020307080d15081f0e 70
    0xc04000906000d0581440241c2d00d0340020b400203420907801c141c0d40c454010000d40702c2e100d42000340034903c1120403000c4ca40701425140009034840f81c0c3c0503000601c074010071502c907190303404255524446007140c940c6003036100711180a104680003005608180c442021040c8200524440b40002100c3c64041342d1f100c40d4080d00d0041a00c070080c010ba00c1040003500325401901c1c0b40c0341e03044070ba20000c54052210490a04a60800d07103090b07801d42400000e220070401400e038010310080b12001964070104140001844d09807036005038011444200441c48115580d041142404071a16120034040719114100241400d459480886c0490746441011444d101d00200340d03071203011403d00070340c94459100b20400303510711440003001041c42130141440d14403410300d441d00302800c06044030385c2540ca4110100b41c07418005900a40940d00100a0349000c501190b00700d8610003d103c1000c1801c00303007440d5403000800c16921460940c011440e26281c088248101c40c2c00d000c420078800d015240240d6081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 608275881 1250 608274631 608274643
    0xf0d1a100e04020f1014070b060108091903050d240e0c12151f020615120304050607020307180f0f0c0c0f08040b070305040f080c060d1e0c110c03 64
    0x396000c00c1c944c00b100d40901d444002d9a28140491428180155800c1da0900c5241c0240c802154816260400c012031564480051640034030140011304591040405090139508615005010858009801198800180c00c421000300e11540021100d81242c000030302403031891b02a003507485118101244481c103201c0c0c00d0b10016501c0140c25030b640d40b6110319602040104015954105510300c545c2c020741d1820569014001c882c40e000f92006203000d000011a21582603255407040e04207880303021204c10000183c400340c410944140c0d540d140140002454103800d070707100c038038031010803070443c8801c80d09500020b070200107108080c0001d40b005020308054456000f900c030000780440c290503001c2100d00e40f0118080c1e00a0910074646601c840f150961a84901030503004903c0008040221807101e2004c500144103100150192490500000f40340b842100b07a44255a5100c0030509000382c0d072141007603544a507a1508000c1100d0041024142030340300b00f00d5400038020500c40075202d003004944 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 608277131 1250 608275881 608275883
    0x10b030f03040e010b0738010815010e1603091406131401050103120815091503100216080a140418050a05060108070302070c0308030a06080f0d0207050f0d1a100e04 72
    0x2145005a042010010a2003804840300600041a100801c1004107c48000e8045c00e428405040c0400b02a0000408114180e105103401d0b040c1e1070030480c64125116654050f494149004125004281400c010060000d00300f21500e006003c241700b00600c2084401e1b5429101f8403400c0d03a1000d100710002e003210070920000c1c1c03105000100c1c0d880000c0c81404070705d900401112101c800e00307001c80085200220103c030440c2d02d8172440310108245150401c06a01d80c0c4448290070b5160583ca0b200d413880c0c0701120080244041070116510310540d014040818016064550064a480d40c54503031800c80441040190f001c50300d030030003040d50000c09009140c45214180c40340c42c1d4a441d100c400310000c0d4002c0341c003034422140107000800001c41c401c0c0110301980c201d44000c10000c0c10000c00c94100540d80403070302c0d05c9038001080111406c1e00802c40340119030f0b045500310140c21b68240070a480352408040185410b070b41194803052541c42e1303400780340603404104c00c91f038800e600c0300005941e0700b1003918 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 608278381 1250 608277131 608277143
    0x60306230a0e060d0c1511010b0f01050a0207080607180b03151e03010603080309010e071d1008100c030506010504030305181f050705010b060301060f030e010b030f03040e010b07 78
    0x909002c5084050030140d00680090408142c00c2841e441d0100c000d100e54021010540b48103080c0c0708015440b41071098607081d414000c01c64402a5400188040c40d44480e003818008081802064540240485401408102c098950a140c103810090843c40e001c0c0c111507080118080c04601c1c16140020351780b20f140d440b0303a07078030f0403000c2ca004201c01e000c1020141c00345803a9590300050141c50a000340e0005510460405840c0c1c200540202e0940d5a58200072006d644650000c00c4000300c1030405a180c0c0c40400e003125196203070b400003130901e43d110f81c0000c07100e8420342d42d102280f020194060709094016a07400c011f240c0750100112498407a41c80003800042090024884d01c103010040b1400365034000f40301c03900e001002c90041410899429003c4082003000c10008140702081c0580345980c0350896010741765605002c0080c01c42070b00300341d07541c0406907244031444510340c003541301100e0300e400182101c083e00440d40f5026901c0c3d11502416280c0701146c00005170721081d4200b07480440354050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 608279631 1250 608278381 608278399
    0x1103100c02100902060c0a0b04060e032104080405090921130603020d092307090c080408160c12061107050a023607020d0e0307270606030623 62
    0x4108000c3d0030054402d0340d00060400c07508001c1d03031040180d046c0ca00e00c101501c0ca0140ba0500b012411035411b4030340c521a6800c204242d45004101c05403d41d104121641d0510313003900c650070003140038081c6800c41600014400c060014a2000189e4442c0d0000310750241520004d040000410f80e008160131f0401e1000c2000050203c0c0c0d02940251000003260b034000075008540741c031a0076480b00f20606070042e0304044802c441d5012014414980a0b040340c00c014001d0100700b82c3c00410794a03004001802101e0080b641c040f00340a0310080c101c0040e009003080912644540c401f00d5011035140c1d00b00c920398070340410039000c841840182d41c0c14036005005050f1001058080c0640100c0c40042d8850321140e003280c800c11245050240d008180f228041a0080d140c101c0020340b4283e40707a40840c042c0200902103800c1c5907400500da6094071040f5251041d06603501e4146c03e1400750011840c22410705110000c24552350503841002141d0002c02d070070312180400d03010310900500903012250448226 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 608280881 1250 608279631 608279653
    0x302010912151103011701060b0703080a0e0f010b0f0103090f06090317070c0b06030604200411031e010b0705060420040c1206060336050a1103100c02 66
    0x1d00c000358140907030051000d65008000100403a103404400c3c0501080100040c402007101400b41c0a42d80c071580000c02211b4200490b1412900030080020200100c5400040207040a0b0b00280340d2032081f001160f440baa4901304035070207090450226030144030000075403034a941c0319018041020b46c1000240c60540500d0f221301c2c1c007400304404140c00380015401101681c0c41c2030740b43c142c0328076031580d10002c281a00e03190030340345c101015002c03a2007a07006a05100c007040d240c2d000e06400074681000e1900a860300f0020401801d00c0c00000042d006000c401c01401c82101c00380f002c400700484c586102c160303803120181c04460203200781c098596030126002500180307400d02081c06040b03c141c85215610f449000040545440c00039110000d1818071076050500e078180a810301170581c0d0304040c131082c44600f465a50300501c0342d03035441c582100c0b081401104c0e896020307482d1645800c041070300c1ca09a15810215401c034001941140248039107081000d81050300e2254020100c9030368041c10540d100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 608282131 1250 608280881 608280899
    0x31506050f090406050a0e0402090a020c03031f120804031e050316030c080c0f0d030c17040f02090c0c1218091008011d06090d02070b0f0c0115050f040603020109 71
    0x3141d0200b5400941e90200071036a603964600c080024003417807075883c69514240c07041c4103c480c4080e0804902034010f1001c2448500044181c95002c0c0c1c0003603030032003601c42c020700c41c1c4144070181e4007026805800040b00320511000f0801031041c0ca0142005500040c403130360000600c0151018007925542042c094074800d81c80304070300c42000078020304d0114882e00103500d465040398801c8400f02e90f20303070081c00341c104500301c10f201110312251039007800c00c41e00304013280c0901f800d40c2d020044d4402c0c1a9040015041104540101d05119000742c080c00240c0b4122013207688690103055041a10301c00c0780719040c0d400d00e144084800c90b02c91598980c00c03c00304942400030036100039000790315452004e000885e1075071091081c1140503515151140340c519082101d0b0342040005000044103800c030007000d03180960009000c800303c5801d040340c40c0d0b0b1a070250034408a0381c0144d458003500b030f500704600000d004440f030540d102a9141150643c1d0907c20341410003080f181c40d440020b0100e981c9040400504070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 608283381 1250 608282131 608282137
    0x13150516052b021e060c0a110313050306010b040f0302040b010201020d0c0509010e09010531020f04051302030610030e0a1505070e0109030b01120c0509090a03031506050f 75
    0x1101e1000c440d00407000070780b02c0341000d12541c600c440480c840d05a004400d80c0c1004141400c44c0f46030180311a054102ca07200740c4883c03004000803034511000480a00c0c040c401c0162480c0001ca450581e5203031041c461030004070304401d1107524403d114050000c075040c0c00e140f0450b02142c08000003102021315560a11014140031941941595421f00818460780c00d6409105180c061503558179039035500c0c000c000341000401d112500e00030100b400c014019600d9102103019005d01203c3c4c004660609102811952a804d1030190f0107075001041c400b1b10f0020110207003054810031146402520058504270040740000c851607a445080040c000000d10b009510008074110424241c91184070152210001e62502c901d54250700c0b03035104100160681d000900d09008a001d291491307580789151100c030400030b0107004082c20390822101d441c0c1007003500b6881400603c1d02811800591030319000c101c3e140c515024041d40881d0521080f0311356070707007010403c0040d6600e94a600e4101800c00c00a103800350 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 608284631 1250 608283381 608283383
    0x81e040803070906052d0f0a0305091618020d0e07150314090c0f01020111070b040c0506030705041a0d0c02030d1506020d1b05060906180a02090c030718060513150516 73
    0xe03030401c103400700c1c1547e040040587d0074464034045079a04119581a2030034044144102815042d40c009010222491140f4540300c00303050409a00c80c094008640010503458400c2c00c81c80c841c9640000e40343c80302c03044400b001c0c000341c0c0b420819003000c89500791100c0320440348484141c100710400182840e000080c1c0000c0c0106200000394400b80100c5001d0f40c2d1302000302a11a1220b04c41040708120340f40e4011005088242d42c0d0b541541401c6202030300d41e001e030340a402440d4514000300742c0e540355150203490f408100080180084210504040c0d1640d0000000c0325500c0d007405a4081a003201061100880d2440c0e0f004041621150070201d801d08420300300e06e2015581113405c0d20100e103081040034061441d18015240c40e06042c0914004181b107804420407a4011080c05405070769122200703030b442156035031580d40c1ea54840d0f0b400ca4030510b00340c0100c503051101c01004116503174800e01074030720400f130002c90f010803c0e141e40c072416072400c1e990300c0c4000040c000c1006442039171703811150100340c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 608285881 1250 608284631 608284717
    0x50a14060f010b071505010611010e0307230a0b04060c020105100501020d1817030a02150f060108041b030605010f06051806090607050a03050901030609090b0601081e04080307090605 80
    0x341d074120503280d06866080c8c0c040d00009036407c0518194010a10a8004000401c0f0007989411507071ba4030071404195242e9a0b04203010501402218001c09010004016502613032110b4130b883d043c94034a00a2041a02600c0150301e000300081e0101c0c17441c901c51080c0d400503002001c1e441183d00049502c02c107011030800e0310520802c400907c0c10000e10140300052251000765440c0c90800000910f0a854040042c0c0c2c207560003001d0004281d00002e86580010007841c010000e03595a08150b040d09180d1095010701c000c4402d4000240562544014140c0703940320344403a0f220b6900c080854182c040c0d00b51480c801c82d42030742005000d18101d0004e10146001170041400c101d07150301c405003010080740040e0045030000400002c02c1da45881040003801e0382e14400c1024040503220100c008000600b0305042c0300c2c000d0041040540c0d4103d0800000205900004252a10f480c0910060304140d4412000c03400c040b80c0400c0081c001c0041d2811a400405110781040329041240302c403013200d020302410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 608287131 1250 608285881 608285903
    0x3050621070b13080105160c06050406180c08010606030b0a0e09210409050a0c020a0609140a0317070207060f0806060f04060e010e03011505040e030c010207050a14060f010b07 77
    0x1100e04200301400c6018180080104002c1c5003903885421b466005009200c464072180004807000d800c40b1000c8119034000000090503901c500d40300c001005c40761041c11082880f05040da003003024980c00310f8150780314030001b4402196a60000d50a8a107041c13686030303000d5402c482c144007907071200132034542c030000201c120360802400c81384505403241d08400008103200c00150a1080c0035042c00b0b401e41044858030200309035000384200070340352070040100070802a00e0b17200b503406000d041d28800021800030320680343c090103540307005410365a0b20311a480c90100130000040d00e1a0021a5100440e03940d1f46038200005601c0c102150100d0004000c20f5000d001032000306400c2c4080409080905095103404140580c801d0003d030012130740290720380c403a81c10700c00c1c01008141100071020031181c0940e00400c0c1c0080203088a821070107a0154840c0941c0f000c01d111060007070004400036850300424856612940e480030140c0c481c18115500001c961181c4010040c003091080200300180c012840009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 608288381 1250 608287131 608287139
    0x30d1412130611070507060c03050f1608180a0504090c0b0f0d062c190c020307150c1103090306040314070605010b0d1a030c04090311030f07060c0305062107 69
    0x104540f00c07200386a0454101280640400100304449400741c8040c3c1801e4280401640c2c0c000c040d03104110740109135450120750900801c00064088240c20f5122a2450b182c49104c0c5003406211440c20362075128140d90f00d000545c90903d486009200e07a000001c00c80424201200c80740785500c680001d0245440410006061281c10b114440c00f13402180c1c1c209a400a11510080541d584041c038405000c400005100c0b24804011150082c10361451001c20300542e2304009038154020b064010b04401070b0813000c01e071042d441e0f91008400d90641e03100c282801000842a0795a400f590103007a4060740b01d500801c001c680140058080141c0d0007031084e180c4a80d80e5580343c1a120203030300c5110700c1000850341040089a600410269014045480342e9005c4c4200000360307500c00400d043d5008550303510303600307052610401c601f82021000d18100c998070704010740e254003d6403110300103440c6c440c948800142024440d00840d8010800200144000341d400500c00c403405043c205e0101e50741c030442c14000303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 608289631 1250 608288381 608288393
    0x30d020c010504110303120a2301090b1c08030114041e0b090c070c17010905060c0a090509040807030e0f0d060f140609040b090705090411030d141213 66
    0x80311030404000041401c1c1000c0c0f40c03082d5200d1201c907403203202c2c0d0000c3c44400101194520400d41c05030a060707020500d500c507410f4581c551480c0e10303200c9898006110010807089040d4110310041001500c002c1005024230f1b02d810b084400014000b031807407800700f004009a089102c40a4070b03204000700005000d0390401140c20180380341c118a8004103031903819030036591a10270301882e4050710444156243c080746036280648500c0500070003071362411031442e480d407008095015841c025071201c02c443c1c080c20400d01102c900c1e04066210400118540404510384c10b00d021001e000b1580441b810741442110340d8113032200c041100106030410306022250506a403503401601100d40078103400107041c5402130074034083d9810003840b0702c0307020154418801280c5546100703a6100d078216400021980340c00310131509124840d0f019961203060542404180f0405d00c40300381569900320300b103508036403204c1000d483c505000b81c02074405c03070f100f480703101500c1140804d450341c80360000b0032640000f000c0740d07280 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 608290881 1250 608289631 608289637
    0x201020d0c0e010906090b070f08130303110d0216090f0b0a0f0302120d05070807050705091005030f0c0f0118120303050402030d1b0305090f031c090e1303050c030d02 73
    0x12400260300c2c000c40c0b2025581166041c00500385a14124600505001c070350039541c03042140081c1001c01c0c0203a980140007032841510480c002c20303031007882056170f80c0c2402811104620504211402074140b1404002c3c00000c002d0094041408075200051a0030340450040c020600d103032541a0301d0b801c030010665100307542c0310045c0c02040e01407c990b60940c010b02482108a0341840d8042d48000c10a0b65510307003100030b940c0c9050344184501e0361424245400e5040130b905078000d507000f03850802032011300038040050324103640040d000c035101d090311605c88940d15641d100d11260811100796078201c85522449007007001c0014003138940f41712552041c0b041a4404101401c2d40003a0b950b0092200714075091018905200c01c3e464192540d001030159007620b070101d00030060070300c41e000884009a484483c040c1100c517100a09881d0792034440d01c00b0543c00d14101c0c0c07034000040d891400210301c258240025034000c030405c0303000039440c04e8242d9040c1c56544c803c4811107454031050100b25140c1d0007900003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 608292131 1250 608290881 608290901
    0xd1d090108010606180b0405061303140c040506090402011d01050c063402062d0f0403020c011110020c0114010306290f1e040c080115111005070201020d 67
    0x1581d6140041c0208030f417003041c001c01a00202e0040c2002200c0301130381038500b036070f100719003490355246003203002e81d44240c07283d0008140000300f000d20b48540c0000300b80107070b0724041a1402c0c41207590340c00410984031021503000780420705100f100b420b68945410b10201646060400511704180c80200320700c1c0480850302101d00e006d48510a1b040702c00c181450b800944141540e1904103801500b002c1d4594034020f11060301c20b003480e1504443c2021118412034505401e00c08501d85040180888816660486e410740c050310840030381c100e05511a84200084101000141c08408000028040030794098001541950f496690107103c0f00030b4a0306080c005c510074800028030090300208500518181112560006010347da508000d4940001c61141d1450403107005203642c074914415800310707900e080d1a40e049440d1041c09042d860700400351a06856800a524403035151140c01143c0b05030010b03108820302d420282d0704c000103a12640206410051900001d814100888181c600701c1c0d6001103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 608293381 1250 608292131 608292133
    0x50421020105130806061503010623090d0320161403030415361403100f0f0b060906251208160206010b0405120a02090a0624020d1d090108 61
    0xc01e01076140352501c052020060500304041c1590b01d003520103410b100319010bc4442a0806445414454414a08441103440300421030008282035080041000c05503e441c40103600d510341d480300001c00001921407003001c081544545486c20f041c010380a503100d10861582620061201042a854450310100016660307a14809000c154541c2500e2490003100844030210942440d1f580ea1119114148144e03107088181c0605054034001181c0341085086141a41515002c0c1126412000760004c03041008101c0081c001906000200710881c800c54408a91041c030401509080740c00080f907010036a0503030f10010076040344544172102d161411440c80720015186004102c003441225184006900891004140d40d60400d41d54415610031401403d10a01c0c100f010304540203402c12011a6055010384500117600300701c0c090602074503032405030f1424051041c041d000d00381103c0c0079a03c042c621550003030901c0708262000b503030500ca240441400713070314100c44400740c0f5407100341d4014002c0c86002c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 608294631 1250 608293381 608293393
    0x18090816061e2003010e070809250504060501050909010e061309060b090906060a0b0c1207061407080c03060607030c20030607180314190b040606060504210201051308 73
    0x41c4040d5600050741d40e003d8044418401400034400201d18240d01c0a0740703042a010a859600c0014608240b400c00602c0040010260703840c10182a402c1a08484003950140441070710b48006403018000c0c0900c0a40008081c00108043c0320700b00c6030160408409001c200b0368015403400d981c1500e01041d000c0e82c8554076000f15060350700f0640d5110f41d000c41480701511850914800080c11000d00e4801c0c003258070004103010803481400e000c151f01070080c0f03600065a403040c5140600241680340707a1a8040b030040c0700000d0006000d00d40d154883c920702078030340e499941c64600300b03c1950018902501000302004000c40090f40c00806030304454100c003100e0901182407030406103400d00c014410b500b080300c20501d2210320942040c1d07440c01d59901c0400c43c0795510014071002e1500001d4000e004034a101140c0311400e002ca2085d006002e02d006050612017151604801d840724419032180d04e20704080b001c5140601c0c0b0a0108000a241c414903105103010502c0c0c1070115181d242c0e800001080d0409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 608295881 1250 608294631 608294651
    0x3030203010e060a0302030d0e03160f05100503071b0f02060d0f06081216060908160c0602030f160317092b08061504031b18090816061e 60
    0x1400b1207a10010845400721401c0c15a0301281d107034602d0b01001424010000e81098143d074040c0200100700c1103074420400c806607200c18403406420380f403003030324080c10340c4006e44080c00380700742e040342e1041e105910351100f4407490315001707a07a80d0031a038401d483d007208042a240060b0354810040081228265010a03540c0c4a8440e4004503181c81c1d00594580d0301c04031410103014115025298142e091810250320700485052070405480044d800034050140022086141100035445204103400b03040042c4640b615580c042c0d0340e0b44101c0000da25034603000e100310313240d01010030102e0050074800d10b4604030100e00c1c40fa212040c048141c4061906400800c0003071003042c0c410a5602c0d110885000203103046000c0740e005006200060940c0b4010894403816141c9442c02c801190000c1d5032102000d954002901102c002525407030045002d070754150140b42c2c210300700c1030051010f200c0c0c222200b1890940c0000001038041400340b0100c440a0316400c001d42000290303030083c81e41031051400840c401c030307030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 608297131 1250 608295881 608295899
    0x120703020d02070503120c0a05030d0c12090c12060209040c09060e030115030605100e040803061215010e090705060f0301140d120503070c0f210f1b0f0503070303020301 74
    0xc41c041480466000c01010080c0f03a600141c15282800450340ba130b6940d50b050903166060101c1c200010b041c9101c00240e24014500c3d6034030520342d0740c074142e464042000322500b0390382c2611040840505a610103040510020084d0350342c05101c0c2d8402c0c5c1005251071905400314050b1106a060035020031510803080041f0343e001034015000942c22070003048120401020388100394014080580030b0741d47d41002540c110f0450b046030015040004500709185041d143c074520310740c01100d003180944100224050010b4000450301d090350740443c5c0c4e80029a007010900c1c000c604000b007d031001407040030000143c64660200074416068101c1c24555258101032452240f601c0b2108a1400344041511640224600b034000c1d1442a01d10b00e405507681e01d03002022628518404c7c0c0c0034000d021041c182c1e40800c404013040601013180ca00c502c01a030246ca0206840e05980940f180011501c0b0b02c1010020fa80070004040505100d220307001078025440d180e40d4555004820100c001c07075400001840b1280c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 608298381 1250 608297131 608297143
    0x303120f240302011e021231140f130b0f061b012a0c0f0c1e2103080c070c1e15050a030b12060a0c080c090d02190812070302 55
    0x141c40009a41245c2c1114000399103490405c0d200355030f41000310329060401020040c080d0041c40c41c088000c0c4401d10b0300c2074000010010b00c55841d504100c8100d41215003002650709030820f00c01003242024140e1804054060308400880c50340c40441c001c522041d650310000600140304d142c0d00f40c508103141610455084465030180004200790401c0075450072580140c415818101600c0d00d46001402403506105520502c07070000d206240610001c40d081040780d141c4c0c0c010084250301c04a50550300c2003415050072034111803681e00c2640c0e680010209000b942a43e411411001d202c1c0c1c50110183c44a2560030007540080d200740e0300c14a1103a0420106009020192050609170f4064100749203002e171661041a418106158075201c03100426030743e80e4600c0ba66a0f524130b00b900d100e443c10f0203682c00181500d01e040380201d040759001c994000412816168490b002a100125601071038003080400c41b98032940c2c0c1c040e02240b400c041000c820510918020343d191649494441205240190606c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 608299631 1250 608298381 608298407
    0x70c0302060a0b060415030b060d0f05060d030e0d02060c1005061206131211010f0b1503130f1502040e0114010203032e05060c0304050a0806010303120f24030201 71
    0x80e00340500c603515a13030303118100c0303003220b000b8240541c21a400290a90180000614455001d400030611700d0003520a50005000280000c80801c1266155000c00440c00a240740c0034000480045200410342040680d007060980020200c900381400d8020311803400300c0c03850050201c0c81e10b900c148841414015800b1a80da02a813001d0600c84c640022480d1060407504000380a814180f0506800280514010119403003050020f1195100010f00480905050382c0080e020383e04120070304203003c3c440320941e805000260300520000003e601c0310421048060429101c0300d20280400c890070800e03100a000402c4400c13406001585803c4170b08485420000e825410354208004020400003694440030070451242d070001d02c8079401200c800c4040074941c1142c0d411101c0000d02111060b00000a001169800ca99095103a52a1030020740c43c0c07007080c40001e0100f4500e501c028800c1c100d6412801020380310b504001a241482d04600300f0340d04100060091030f070b50504c404d1084d5640051418001c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 608300881 1250 608299631 608299651
    0x1050112030512041103030d14060f03070306020a0323040203120909070c1119090b01020f19150c080403020d0318020127230f06070201050c0a0b070c030206 69
    0x264400c1d00c02070000e226025541000a250a000030100540030700313010b00207000941160b07220401c4d0a01003004019405e000e11942400c0c800180d080d21304083e6a84542c00e0140103003038801e1866403100069000b603402c00b0249501d400710700d00c40d440c000086074469003d42c0301c041c44030b06007401498100229075141030501032003080b0005554585100894000c8240d10381410340050302d05190380c01c40c040380030b5075912941d0400c514680d81c002100605c1900c205450820417945010016640e810400e001e0700040e81003410003100b03254440c0c0c940041103000322054007052807a0405201181d100c1c00b0420b000c60440c5061200341a41000000c80d1800c25040c100159070300c20129034208401c2220090400460a00036181003c00001382c1e0034085002030710360381854481d1450044014400300c14644c05900800b84000d91818842804000502522851605000d42c004545951007107000209910a1812020029060f40c0907e40304a0a81d82d854220306c1e0b035442d009007030900241002d064 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 608302131 1250 608300881 608300909
    0x140421110f090c07060609020309010b0405010e040512161712071119110301050901090201110a1703090109050d0f1d0603070e01021e07030201140a020705010e121002040503010501 79
    0x14035102d4488450300a00c0d89405152118002c0c0307064400b40c22a90450036000c0d0000c0180000707560150002d903200d0301d04660901c481c0c0c0e03c171490201010760480340030300385910a68000b0070700c0c143d1800070844040c008200c0180700101340c03650002d40500e03120445c2c100100117000300c8401c3c00960380036088599072822804541c0da21081c1640c408032104d10203051900c903c4100300b000712582107503500240c00783c028041c519000d01c41c07900a2004130416800700e42c20031586440c0c0318000c00d4010300281d210b03070210302c45080c185e48006550001403210341c0a6590340e801d840412000c01c0162240d201c6955203061040e8110001480c1c6541010104110305401d000030f050303580d4480641c1d0f0f002100d8035124900c2024a00101e02d455044882ca414014140b0000f14000300c0110f840300c00d85c3d00030b8030340b841d03105000d0805001e14841c410500e4010382140d04284042d61103250060034000e001001c5098514020711401d007040380f41e41200d415541e000408000e07a0a081c01a00c1c0100700310542566 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 608303381 1250 608302131 608302159
    0x803190e13110d06080313150f031a12100f0603020102060a0c1e08061801030f020904050f100516020721020402040f030605060102150c040614042111 66
    0x1081a100e50040a14503181d560110034561094203644803c0258942400301ca59503000c056200c1c0e203d0045510122a1008041b41010241c031701c01502240035a40c46410902c018802c4008081030300c01944209000800d54030240d856020103074440700e42e6070203009107a4024544000300e401e02010354021906240c400c20260780c0202d40e1a41c004001d070f00101c1c507206458821505402c141c4a180f0420060f0302e01600e94980c401c084500c42d01007628206110a01682e03010f00c040c009210040c05114615207100c01070404a044641080c03196084401c0d0703014100d00da0b420f0418070884605c400399110f0410410340d0304060726841031802400030340b40103410102405100e5500b144c2441c5211040b000860071501c4d0f660403540240400103810102c1e9031a880c00202400c03040c0c0301a0300612580010030304070811000d1a5006034001e207201444c09191090a441604415140059000d400d200025200d415060041d14102d07028004449800b10b81c503206800380b4600210724011040c8070b403c12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 608304631 1250 608303381 608303389
    0x306150203040b0313050d08010e06010816050d0e01060801090c120506071b060606050909060306100612091707141b011b121e03051303051608040803190e 68
    0x1505445050705103039501c2e40d6000440003900001000200755101e001c800300e047d1039014602030b060307907022840c03c106500c3e410300444204209407040040c401100001148103406100188801e2040070310110780e0b9844442300c01e00b11021503010204694440006800304601443d50101404c5162000f002c05c0c4c40544509595400c000c03c040240301c2c51202c044800d0340e0003240b0f44a050b40c0b00300c007400040c1d100ca00041a640200d21322600030742c66400401c0c51480c0108080388a6160300e03050542081c5025400c4854032810b0f400c0720041c6070b40f044000003003442e40320b2001c9954140345c1002d036203a545141c0f03202103c0d40c1e420744280c0e58000007510310b05d40c48240500c0d0304003002441c0440d66041010700c845100d030302081c4000e00321a07407800028040381d041042c01e404110b0141d041a940e05580700203500b038620480e1400c980040c040350041c0041d00900c0906111070000b9038034100c1981c0e9036078150b01540980c01c065030b1b59201040302c0031744d0890b10381c8540ca4540304d85072406107070141002003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 608305881 1250 608304631 608304637
    0xc1206230a291504030b01031209080a03080a050c070f0f030806030f25151805010207050604050d050717060f0612060406050a15060504080c0109120b0604020702120c010306150203 79
    0x16481a0f02d0b805008039040e80341000d640245411a003140720700e594919201824981101a00f404140340702c100003180038000c0f0b8020059501a200c0100e1030750b6883c100720043c0310013000d41c00c0000c0d0500605000c25040010715480501c07928042c0d0306002c60b81409444a02c00a0049200e81e02030000e03011404404030300062f80c04000144018042402c240010303420900c2e070000300000c003c910380d5a00b4194441e02d0011b1580d0482c010b03140c1079454100480e2100107034040c803a00600108001c100350306184c82e070207250b280204241c800303e603240d550484058030042580c41e095406401484842a00d144d40300b90070541c2101e1514082d0003002c00c4988072000180003030300b072139603480014108502a4110811101c1c081503148201d9480f02c02c0603141c0e40242c0070f0000a0711800201302d029500408001098440c2006681a040c91599030100300c1c5a0040415420a400380018130042c0c480c1c2080f401a10116809084d030512000c1c0010102c5619500c0f5902125030b0881d030880c00d40d004011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 608307131 1250 608305881 608305961
    0xb0604080709091a1e3702040f0605030132040c020c0312041d01080a0f0f050607030b09090d0503070509010c0209161404030c1206230a 60
    0x7011071514080d08169250741190030282c2404c01c01502009001c42010070360f1411501d218150301d4450700d5051310790a1107242104482d4501c400542d03002c43e0001b405020488400070804098038060310342040003d001c0450307000c480416800b200501075074004000560700c0b2407840948210728410320b458405101103164016009a0703a6400076070146109010702305100742c3c06407c17141c4250a0555002c019440b501c00d22800c0102015900b188541d0291500e041b2074150300140741e1ba1203581c65402154200da20215010060ba0804000042c002e0090b64860419510002000302601c418040c030b05900410291041d007200c8982c1e003100341c0144c1520307005000c0b49811519200001d0041c2d8808000c0f10011750700c2115036081000056102140003000304055032042c0b401c00c58010401c1e02030081d030000424403404c1000601c030250448810031006809880c0c003003442e02d440f0b100115043b0448094402021000c410046c00108501910130044119455010448040c00303c0449908100c64 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 608308381 1250 608307131 608307149
    0x611030d020901032c0c040b030a081309050109020703030c020d200304050406090905010c1b12030209130b03060c040303090909080c16060e060705150613110c010b06040807 76
    0x2803142c000d900c00da0110201e0310001190400c002c620309140001d545089036800158819120098a80d00301070164414007640503000304204540c2d949ca5200a0b00000100d21200f031024000194403009401024020074202c40016662881820001c1c191000444031406560240c0b01d18101d1a42c480c02105031403100c0390300c0100300c605402220b802d510881d07010301c0e40141005004942ca0556034000c0900d244604000c010302c3c4c090590544a2040600c0e80f008821040784040d404610f400e640d030b880c540384621f401840d02c60320a000a100104c07115866030660f50f5910341c03040c9402c04012240d040394074860503508140c5140d600408050300380c001e05c05050345a02c0224208540031701a145110404030035541c40401151192580344500d102d0341d000124030081c0c205d4581000030031111215048070103030a102503c00c4052900f80c5028184d56005041002d0816042a1520541c0342c018004402d00d81c1d02d5a00c44010b03070a5641003000a0300c1184100310400102000023609030403504860 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 608309631 1250 608308381 608308387
    0x30090309050301020f03150f010f0822050c040f110901050904020403020901032915040e0a0b090a0b0109050c0406080c07061a12010504121d0d0c0f0611030d02 70
    0x454122100d1000d9840250958000b04207070314000349010145108443c0c910030300c80360300c10f41d1040000040407038862074040b441004544501c588540c04603940030400701141d0140b50040301d0300c1404400d01035070540b515000b12820003d0f601e820b000e4503110342c0c5401d900380078880702c00008040f50f2051030b0020f414000c000590b0722003a103498050301c0046400620b9491a13695905003d121075002d0440c001d80b1038424101050b495440d15140d82c00395281da000c4400540c00c03030302840005c04001c00124003130700c14503400c3c03030005089914540c4503448440107812020703200e10b02490900010f030030000c6a07500340410004008801410b44007140c0c02890040165154450101c080744510075028100d14180001c80344400c4003c1c600240d0550161100c00d1741302c105480391400c9071000e0f40c004049100603440c0000d201d1046112103200e007140340b1111404200900080c040c1081c0d0b101c00c13190030180110030410718841260020040c042c034201001c1800c807021207161a8401c603400b00440035404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 608310881 1250 608309631 608309633
    0xf030b0619030c231c1418071802030a0b0a090b040e0f0c01270f17012309030d1a0405010b0703090303120f0c02010b03070b0c120304020f0603040b073009 68
    0x40e03140705461107104002000f0030716071003c0b200328540c1c01b16654111503504141045001f6400101d0b1001c6400c11100301442c60348500e07412010f9030020344980d204944a400c84002a910f051149004048900001400402e00300074001036400344011076a0030341099181d00d000c407802144c1d03298501d40918100e008004880658100c003007204e0401800d07844110301c0458001040d01080003a101c01d85064807200c032607141000c1c00d03900820001c0c00304070500c1d140188a0030000c80010f8000703c0c1c50043e64100428500da500807110844681403060140109000d03081c105032244502400b40c18040c1454100c141e100501862842c0c030000f000c10808041e2852076240fa54482d503940f681c040824020454042c000a0190a82c00030744c503c2401902000280c408000d0206c4030b890981c80040c000551007944da850441e04010000d9030881118054144590340d01e00003107204505c100e02403904c4d0f0400d81e2004064404158045801d03d00041d8a1042426411401c0c1ca0000e5440300204a030310003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 608312131 1250 608310881 608310907
    0x5041e0c03021b030c060a05070f0e030705030d030510050102121b0c0a090c02060603061e060315041203110a1e020a080a09060315050609010f030b0619030c23 70
    0x250f00110f001c43d0365070441c00d040840c0c080014802d101311102207421070745135180c0389070071900242d48105c082485500000c88542c0161507200c8850710042c29a03040698442c08a410300c002c10b40c10400003a81c0e1802c2004400003144510082c2c1020320040c143e200ca00440c0010910034404140745040c0d4040044001079420050b9508440014004000d1075568101d8038001d80071111850005d40102c20006809080004005108000864100d100906515819080501c007d030000f0341500580e940e9040508540c00f10728001c0e44035803030300d070f1100d8020f08000b4104c400f07001c0340040d8400c0402640581980c09418101e06034002142464028018201030340ba000105030010261940422081140f982010b007107001c684540d1002d01c0000b903904140d0050313070b0250180c9603014605011440095100f84040303c4800048d080008480090344000703032140c0c108244122154003400000c4400b154907003d6081082d6460610844140c0c42da800c4070484d0b41004010a080f49010035000240c41c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 608313381 1250 608312131 608312137
    0x2060c0d1803080402011112031906080f0307031b02060f2d04090608061e090307080f04050a090b0904120c0b0108070329070e0a03020405090105070905041e0c0302 72
    0x504800700d220481246405440c099046030103902081c1c0041c80b80801100c00300d5080002c580f40380945145030b0b0b5450032503000c46903180601170764581c0d0342d50210304a07604000c0900f0001141d4010f648841ca03600c0d00034043c0c2c01c8181c03152110640c01248000507101c900036182c64411190350b29468106501324007598500300c13403850354101815410006000c00c50402041660390840081c05015255080300b42d41d00750a2305c54500200c0c010031201c00c410044103d05401c002e8100c184c074501852600c5000e010f400002e124840c80c50005410001d510b01240200014005a2414441440c0c0c100001c1d41c0c0d01c100030409407002c1c0a18004983c0c144c8201000342c0c9165008208907410b50312250400d54450ba140400c4407131600680d4402c8922864008808000ca501d03020b042b40340e591001c04036950b4040090194000002d00f80200050795140500392286400744000039440c945039100a090f120194003142c041c41c50060304c2c4107964400350460074020340000c00410000d45419040380244 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 608314631 1250 608313381 608313401
    0x204270f08090612090709180209090c18190506010c031107051504051c02060301091113060e090a0c0f0509060d0e0303041b0e060f0d060e010b040e07050102060c0d 72
    0x10384005040c2d02c1404d90540f94502500d001c0302200c6105031204d8503501154403852000e011001e01403550303001803500c0300c1c14644c801d4480007900e0440300c00f0400b08003505905402c250070340d99140204044104504104113020b013011400348502d040080002c0c00884030070202030100260402c0c2d05203c00410040c0c0e00c000c01c0050700c0b0180414442c219143c041e0402d000d21440782219000e00150500400660011181c00400151840e464a0340d0038004000d41180641454428070840e1703da082c0340c0206200070300380c544903200750711030280c200049002c000340003010701c07841c04940d8208280d00001c80b40c07a442c0c00c0e0070100d039520500c200045c01406038a0048006600340741280d0040e0381d01001550080e4400c10303080c81111060051140d00d00c5003400f500c3e01405455001816a02d40a038030355584a02c05002419840f03a90380324a13056510a9000e032185a44602e18046281003034420f043c000c803c54001ba104d206d08200000752034050142042c401d0103004207000f0591010350b40019020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 608315881 1250 608314631 608314639
    0xc0c0b040c1e080120091903050307030c0605061f030b0109170d02120c031608090a09150b03010f090509151f0530280204270f0809 58
    0x3006001c1c2d070740340c110205070188a015500b840c0070303c14088220040280e8100364550b01078181a01d5801b8059503140a405c143e203070900428001001c540144010309409000342d90300c2c842122542010000e8500c041c2c0954017a00c240d45403406a1803a60000a101101c0e518000c16100310800040b10074034041c2d08140ca03c1800c1c2007441002e0100001d10b030303403150603580980e00e200d0590010344100340039808503c1d849400820050b66200b001590001005100e800d07a40d0401c80d14101043c1e488105801003aa0155110141d4803a0201e54100c0c000516a04510383d1456040c0040b0080c988c0c024800c402e205c64403100480e481c1035041c85802442d07214030071170321503d20f40304803d40a00840e01c1c03035405441010302008969401c100c000043c01d40802c140c5904841d2418072101a0910b0750766003d00e4034014040c06200703401500c603c00904440c00c0e000032401078920700401c012030b02c50100c202e00c2a403c01c0d4880f01a4540000c00d40c0d011500600030821524440c1407000031b5115061940c1c3e40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 608317131 1250 608315881 608315909
    0x1e1813090503040b1b060c0a0e210d080a090c090903050912030a0306120201050319060512071509051008130c090504060b0f0f12030714061602010c0c0b040c 69
    0x201c808138005044009a01c2d0840807424007419502c0b51a800300340c490750b89051080281c2c04640740030b00c2c00b062800d100500040889405203615109003d0850303030f903450b035400c61025455440c1e80007007055000440000100704921040d901d41c071000e5141e2040340c550540305e80407241490300030001d8407200000603094a144c840400d17032080e00c07548010903120109142200c00b10b502c154580006407429810b84809240d5155190000d81e41041d1032401c0a010391140b0b00410540c55003900020245c14150082088a041111411848a9001070541004080744003084156180c900c000d88191540c201800300d52120380041010004805014021240c0300d840050102000d42c0070521440c0960410084545400d04006401c075405154681c446000c20160140f40f07005110800a030442c03004aa1400e40343d035890701b03050780150300d030f40219030400c0d42008019200c07070640c682030b52040d10080200710b400c10001340114110510140c580c00000d40014100720007000358074040c003444170020b44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 608318381 1250 608317131 608317139
    0x90a0906051609140a0608090a080c0102040513050c040501140c150f09010c23040906080624011202161703010524030105060901020316081e181309050304 68
    0x980d14200a1085000806800c00000c0032803141c240d000d09890000e00c5d009109180441c1121070085c080c2a400050040045000c00160700b0402040c4040c084000940c49514060801c080d131441c1c1c01681e414141040104480805008200c1e410346d602407e10175218280d4a10890417805050b004118034484c04c40b42c00010000c3c030100a1140004a8034055581d9415800303909070745020206901040c0d540c0130381a4040001443c0310011a070b0303400007a08040d540c035200c4003910001e03401a0301c0b507002082400380d905c20303080314111130790041710b0060711200070400001c0241496075021000c050780407c010304005110401d8080d0030707400c802c41c0c9008070704d4040c501856a000f03101e442d10540c4080744a110310b03c80306250750000e1148030250f5003141c0c41e040a202d22035005010440c1140000c016a02e48072840020104840740074408154650802c031450070b8041306440869012041c05005600d40d012003030b0f0f0310f0000d07201c0503904020701d10003a05030a005013550b54001080c5000102d404a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 608319631 1250 608318381 608318401
    0x415142203060b010f1d060721030b0d21030f0509010b03010e010b0108131a150f010c080d110c250603060602030f0c070504020a02100e061005090a090605 68
    0x3542e001c0c1e00c04202c00512800150f90300c1c400c03103514102090030034541d00400448001c0c1e001c0f6006011f45981d1420342c659582615050b85000e000c104550b040b4411400954140320303408000200380d40c0204584c070183c4400c250f400312104030380c290900c9403d000c41020310a4002d00f881c995034641c10301181c100782020901900d0382d160614081d40c80c03c04210310b5840c05024800c500b9106171a2a07240d9160013039400941c84103118240c6103200c2182c0d002003085c250700c540740c3c0701b2880710820701901d101034030420025580c54240e4604006060161a02285454040314003401050341d0025015100340d225003402d00403c00c001d40540514046182c0544280860301c0303000d4440b9a250114940300c41043d421515540139680c0180d0041c0115640c03040304000a0115450324401c48000540d120001403d9030b00818000c401a002642c2ca400c50f1480c9003d50010340b682c42c0d002d41f901e454a42c2885009041500c0344503c161230ba0070209170742103c0c84d80803603000c5801180c2445130f860044100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 608320881 1250 608319631 608319697
    0x60b040305031e1602210601080601060f021b09090a020a1202040e190b0a0609051510020706050d090312020301060509030609060f070521250302041514 67
    0x44083e1403190000003400c02061011900c212412021118122a4540a10603c408030b40803000ea9001c0d0360b00d181804450802482e8020801c1100510740740d07041c41e900606204040455109640c0a1200040c114600d03a8400001d40b1059550407807558480504a01e00400e091010303400c051006008a0204218505112003e0090320140840f514017200305540f5059602041008590804020b0004d41c0a810054104207003d1010403207e0f1699102411100c050750319a032801c052600548207420140c0100c26400b1440c0040e040003441c06201808c42d00c90070300f080d1045030392103e18104041c00341c04519824400b1400854132582c4031031014120381c2c44100443e07c40e11030f020001d005a100020040d115209200e8006101d8603042c10a0741c4039009022181c0c655903050006d001c00c0d84010f50305074407461346001d0b1810300341656186040101b0309003c5c1c0c1410180104000e01620f16020008035603a00b0b1032500003001d2000c820714403418014003d60380e810081440110b500340a005d064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 608322131 1250 608320881 608320897
    0x30a0f120c02100605030705100e18071d0f01091401090b0d0606140301061202090a030203010e01050601030f0b0306130c1a07290402040c030e03131d1e0a060b04030503 74
    0x104104d80b94642c1c04069071040c42d481150ba015590300d6501851030701c00e151400207801d000d00910303d03000341c0460940c400d1104480c60303000580b07072601d0300b6840d003488000206c1c001c03400d581082101d100000001d08030600c6008800540c81d44880140b2242d10502e00c0310010900340f14560388030f00036170306020b0280159100b1440020000d0355420003891301c1c60308a9040329483e48902e00483c030001c01d444040e40220701a2a030003002e20500002680302806001c002d0500390000151900d0030200140844640102c0c4000d01c07442d0244600c8681c40010b42c03130340c00200700c0b0001041d603900f0b46400503c1d4010354104445a030000002c10756a0b141c0f210181c681d85100301c07804184014099034010a01040c9460135080981d0840480d0141c10680c0c0800113061b81468045400458102c181d0720f10b42c45480c0380501d03070aa8003001c0185822040344140c11307a40c440241400c608002d1a24a0544003e01c0c003210100301b046d020403c00001984084000d207400d0780000d4689a80c0d0074070680740e4011500b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 608323381 1250 608322131 608322163
    0x316031b06050c061b0906030c2a03071401091202060a050a051b0d0621021206074b020f0607020d11030f0426010509030a0f120c02 58
    0x3002251180c0281c1c1524840c0c07150000810360f0f541c0740644100304a06980316146800340402c00d849094481350015407051500080b4140d58000d2501400c1075000700d91030005802640480081c1d080c2404000c48403a9a040382d540032203c1000700c0282e0041c04030b0100280252082040f00c5442500442d20501c0761044120420040e070300c41c1390941c107503034044800c0345c02e004c0042e004991010500700542030440510400040658071038080303800031b030500040c02e03882040030707540b03c0114640405642207000c00329014021034141200003400728414400d100c1801445500d0150030001402c0f040a10324111031254800c04503c1c40e500e031321b14a02141c1c0040140602100c001c628000062518020400c40d80204003a02441d1002c540b03030007803007520031598001008008215200080908003a08103648071480384404421000001c005c680e0320100c031079051204102541c0c1c0d000c000d855620419040800c90744d10404401c81c0c074801d1008140354042e14001d0340c546403035400100c8102d5051a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 608324631 1250 608323381 608323433
    0x121090b010611060702070303111c020303011e05100809030c030d0f050106020c0102120a181e050a1d0c040815090d090b0f0f1303030f0e06030405060a050402031603 73
    0xf0016a8545104031410400343c3c4c0910001c0000910030b00300c4400355281a001c0d20600562031440c4c40c4138038044444000141d00c00b200520100d2108000c154140203030080c1c807800f15203803002150065030b11842c050180422a0001000310400340101d5120007119000da035030740e03000b04004400034410300484008440c60000003282c054000500c0c100e80c410140c0003000c854841003903d003038035400760030201d080100498242c540090305018403000b80003070300d01c0103003100501010301c1d9487c0304542c0a544980071421003040b2840460850040c00e000c81110400c2956a100c0300c42c2030342c4921390140c801b5101d03007003000359810144c2d028140510303640410f40d001060030381c0c2c044031102858010001d881004008070100031101c2c800615900d900845200d080038180705c002c3d240c1c0c4495500590104021000700a20142d01505c00444200210f502e28103500306525101d40d41c80b00180f0311410640c0c3c3d03801150544d40c080041510b2002c02c0d09000100c81e803245000030802d03039110300700b80281e5690 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 608325881 1250 608324631 608324657
    0x51608032514240c0a121116030c06050f0112120201090c030b1008010b0105090103051f0611190c0b0306030a020a090b090a050403021513061b0e120304050121090b0106 74
    0x1080480d009000035682d410001005050410010200104108110041001039881e00d0b88d032985c2004d00c40780252695403c903202400c16070150340008003240c2000980400500204040c18502c401107038000b44c2c0368208052000e02a401050394082c00b902c45003140400000f000b0301001440c0c45260602d8110780c4180d9521845800d0b50006220b1a011840912aa48440d407082e8000380d0300c00c2455440701e00701c108040402ea50101290032000024042d400030718103024041012940c02c030400382603400081c035240c903410003078680c902aa080500700000411120b59080080104480e0000c10403c0420783c2c42280310700030310403480b510340289a413600159190b4803c1c400c1c18445d68064010740b1489069044249031724800506072000c3c000c451103a070011503024415640190440e00761169200b0100201400b400300142805200c2e4010800d41c00380c9500120070350702110000e0810000e0f00034401c0142150380b4544a1004129160150038010b01101040960480d00b40382c503000b800c5100c3c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 608327131 1250 608325881 608325901
    0x16063509010932060c0a1107090222060c0309121401110c010c0201090c0504150b120a0b091e06010e061309060e0c030403081e0405160803251424 64
    0x4110317004208044244000d10450b4060070f6112440d00e508429115501d4541c03400c107007260450801c001d222100c0c5505a098203c600c0c0802d00a00314500300143c050400d0ba900904580050080507400c0070b40701000c0c001c01980b440f02d4a0022201002409501c00402c1c00100c5500400c1d000d02c00c644c2400842c0c2c10060042c803031500c0503904600c020f0b5086003000248405031070701c5000107080359400000040c03031008440c0580000c1c850f05035441c82a003801c125404c25070b1440c8190358400c403001c2051000c1900c40d0300750000e64403002e45954600c2e903030b1400146c40000c043c8441c560040310009012032031010750144c41c81541c810f201c00304012520b42146150b26482107800c0700a0490400c041000b203401040042c0d48450030f410100c100710f0100b400507003600030640b4205c070140e1100c491040810007a020314005045604c00841c10200d01905040d54085644480c0c3e525a40c0c00c04032070180842000582e0341c2d40d42c02c5040791008000a01150720101a400d400515400c1a10105400101c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 608328381 1250 608327131 608327143
    0x7020607080c1c0b0612010902030103020a0f050d02040b04110a05120f01030309120c03020409061401062c0307050402070b070806060f0f0310030516063509010932 72
    0x4007411060051000b0b5030325802401c01c80e513402d038802000e00c10407108814008096000e0920510003507100e51652042c059012800c2c0c00034031100703080c202c081c4066142d1010f4441d0b425012100828265a840c2c0402c0003021001e00101604400082408443c0c0d003010080038107245604a5003415629803112400110702030000400044c20703060200040280610b0502c0654069152100d4455481d070005003200d00d046404c40d075180c2c4424050f401005003003900c81c01070055080c00165039040304000b0728221030710b291041c2047c00080300d04506840400988001c0c14000c1c00841d030b5041c031400c00e45070400080702d141000a030702400180b05030038480103483c0d040152a40c45400d20310031303652000044d040117021450b035a201340c0c4000003144c0e040040c401d2400c0042c0b030b01d1042c03a0500000510301202c3c07041c7c95100005065551225115011150071a041e519400030107685a00b0740d03482c05000700302030281c81c19401d511400349d03c200d0540300b50501b02c60621103d0700c00342c08c602c0c0702c0e84a107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 608329631 1250 608328381 608328397
    0xa050a081e07030e0f15040b0a0204092c0d050409020d0b03010c0e03061003020a090e0c03010903030515040b0901120813061806110c1210050a0f0b0a0e0606070f0b07020607080c 78
    0x101c008042000103040003103860b0400155270025080903203d00c1c09600701c035020310b13100c0c6001c000400e5680103944c0300c02c8410103100000c0060403002e41035200c06480c0307109510903140042c0e80059003003080c4101d40e0040c800200010b0080c440c1e4078489078010405e047c884215442b80c050744021810004118621504a981c080e052110317492400d00c0050040806215620113400340781291070341c0303903020310030a5041e45c420f4800046505203010307910150b0302102227a601403883c0c5204490241d840c60504ea04442c41481c030710038502c4851801601c0350080c410f0b0040103511740c0c50003280a54115410001c5403444540e00811143e86060403a10790300348040403401500200f1440d100390520881c1c540a941a0604940f00d6002200004044481c2281d10264856031201308000c40851030040b0b034840901156010a480c2c00d08000780104c1030082c002d04e100301e000240007820031506da004c41c03100707641140c03c845a0349003409000e51110002c071500e0000408040c0050400c1c1c0c405420f4500c0e076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 608330881 1250 608329631 608329663
    0x6050109030b0f1305060414010f0b06070f020406030213020904050606070b0a09051f0501170a0209160c1502070201020606060c0a141e0d0e04020a050a081e07030e0f 73
    0x6443e1801510180903018002209000840d801000410344c2049018055442000c040c03110441c480821030846200384a0444c086051048002260b07440c94280c0d4205900700d08082488089440050010030881c0e000a4014070302c021014260312582c0d01624200300e05807000e120680d120000c2060314400d00d90024803802c4030304049005410580e001c050650310031400c464000e014000a0500002030301d000060321a00d420060101c0c8181441d12248030f8841c100425070000c581c0d0029207020070041407000c49000085030450303042d11400441c030520340c000e5540044a0b020004890180d403200200f640544204000300f00f540c00d000089a03500104040a170444002035507854400c50000508074040307204030315070400c0d14840818ac0300f202e404600c0c024220100d021a014203102c07036080a5501c82d0344103110558405810101f255400328851800482950300c80006c01ca2202400250303800102548081040e41c0c0d070583c2c09403082c0400705007180e90100c03103101c80a03554419001c0361009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 608332131 1250 608330881 608330903
    0x20f0d09031709041e02040501030b060f030106080c0d02041202190503030f2802060f0a021813090501050103121b0515091005040510110309250803120105040605010903 74
    0x341c460840081e01d40480028004503044178403541c20308043d0707001c803e4038100d181d0003d010010f943c2c0501c690420090103030f96035414090b0042405085010510070702c001e01950301c0c00241092076070005c603862702d800031030b04548079900e03013410101211480504a00455080010001a0380104205001c4980082c001c1d4a08550052144038907000070150b031040d01c80c560707000c00105102c030021b00181d00040c0e00810031454240c0961001000150980210a1041001840b08142c41c10402c0c00c40c0400d0383c0c0c82c0a08a007001c11280200a1182c015289520b04000030042049645100788000c4803651004425a9130b00002c40482000400040c880e40c0110040c0b00d102000030081a485600d000a40782130714040075642e005e0343c80440e400c803081d800039104080e4655203031264842c2100c09111407400e503d8040d00982c0d035180740f61001520300200e0001c0405c200507240202002e00803003410707682c940010340c00050341e000007805102c4c459401c080c00850907500c80c1d0208012640c0003000e41c55 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 608333381 1250 608332131 608332163
    0x2e11130612090f061a01140405040b01140711100234050303070f030f0507050a020904050f07080106090f05040c0603020309210a090e090d1404050907020f0d0903 71
    0x55003841c042084001d035071036601c1c07100410031904050b081c490007610302040e0703680300d110400303003d0001c0500141400055014405c0960f9510150380a442c0207540001d002850000184c1d80c20031289255507400800251f90810080b0120074400e0240301a07a103e802540204c2050340c583d41480b1140d924010b1104886800c4002848422820300b00401d0200003180c6402c003090a50344072080644000e52200035030420558000d1070107403d94041c1c6009400c28850b59141071711032900c5080030744140ca500740400c06204040c81118032102140303048502c3d16030794210301c90103480f1902c1100c070341618083c00000030500314081c003449294007140c00c0b0f80160030403500341c000f90005440c03056a071040c0c1c410f10300031440600c1c03052444410110890345942c2e80080c020880c00d000c1c0c01510030000604140a00c0b0359001602c892015480e01b041148002030b41703145c690070b0095a210550042c15501400340c0b840c1c000c40d240400d0f941190580d0b04a10196100381c5404a0b82d1000034032103406850079031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 608334631 1250 608333381 608333387
    0x309060e13020d1b020303100506030f07110c0603070c0c0b251104020f04090510060f050702040e0d0c0c061704120c02040507050405210a060902032e111306 69
    0x211144040c20009004c1421090a00d80e01c0d903070303014080c0503070310010510414601c4250407500519081b201e6a00c0d40ca0410098508684003600d240240300501140c406007003000d2103440060369024050a403245000c50000300383c91601d40c402e54124201e0600400c10a28240c2110100102007124002021104d402d03c0d030304103a044020740d0600700e47c4141c405290303250b0004003801d9042e180030549071400d04242404849015041407040400b503a1304001072508150702005124403414084e13100c40c034900200d80600b1400c08071680e01d01401001449454105900040843c061482001c42c1d9440c0c0c40243c450140e4440d9400d82400c10000280c00070310078102114654501d803400125010390307030340890107945c01038a0354808100045000e10050030300c5039003d40d010208a0341503500716851032503241c8034062803001411043c4c44440500664030204040d9008400300035810030745404140c1a003034014082c0c48110f444a050001d4052080c500400795018510071051010000e842c000b026 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 608335881 1250 608334631 608334637
    0x17071202030a0606030c05040c05090a0306050613020301080601031b0614090607140a030f2102030907030c06120b04110a0807020f0d02030909130c1205190f0309060e1302 75
    0x100c0e41442004007540c00a403c502401d00118407a0312440c01031400e160400003951224440001008030a0200c0301543e5120440041200d4116000080d25260800880d422444503541800d1803400040002413031113001429034100ca0140c0350100440207081141ca42d0a10103100f000e0015040c44000c0032521009402010020001810503241c29920703030307416001a2001c0c40600344c5400c456003c10038176810844220004085207045490502900f60030309189500d29120540a40e0100001b04104e00c200f0045000e107030843c0000501c41d0703803803c0060600d1502051280c01d1402c0604055050070721780501040e4160013030200d410410703014011105400010300d024118400c00220b4040c44406005020700c50816501441d920070b030f0702d42401f168030005080041000701241500c0040303102034034250195000c08892561644503400c0540c60711030510080044c0030203d0301100d040140980c00704029a03c203450740a50607541f4103065400c5000c500317407690000d03c1403c0107011001da030303801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 608337131 1250 608335881 608335883
    0x6160507080406050c0a120f020f030a1202030c0f031f09050c19031b0c171602060a050903060a0603050d110c0105160804080d090909080a0302090d02041410170712 72
    0x2c03108140746c2a04c0b1005410744482c914800f01e01c8114283c0059075052103040881450381c030081d440e055080c6001821201101c030103203402c81d0b020000c240000244c004072a0400d4144001580f68105111044000078a0000034010000d200034000352541c000e02861344074900c08030145003031001307542d000c1d8030720a4002a800d00309070b642c051a124203941030f10f40421845040e42c981840c5006850050b41e02d080c0301140c1007003040306014880c070044003002c0e801d2140354156641a21030303242010a0f903141c040c480115030300d80034400820032086c041e0390200d0105c0307004004903401715840715801c2c0c504040a1510620300e4101d40768010055005600928443c1076055a40e107080250341c64945d03441d04580c21000d080d421030010320300304681c440854005020348e0300c800c1003500a03540e43c100491103840385420a06401252000c0240c0d1026401109550050414040c0031180c1c1000004400111014850312540790404141c071010f098500901c491000010702c1407500341803403450350302c0070840 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 608338381 1250 608337131 608337133
    0x1180e0c1602100e040c051204081606020f071e0c0b22080f0105070212121512011401080c060301030609080903150405070b091305100504090506160507080406050c 72
    0x1d0403600585403108640c0454102c1c1d65003c400e4a542405c01060ba52002082c1c020414180035400c81e00d142004c0158000307a2041601399a6032001e000110b2107481d0082c0038207464070200c1e048064900e004020450a0f1194800400005520070801400058600e0281c11205800b0090114011040c01004140c500003c3c0380032001c09200c00c5034680310160003441040c0c00c9049030210482007400f07500d41065a84c000740100514071000c0c005603024464011001e10b03c140c0c01705840d0070b15607058092841b4040d0034182c0041845585038040c100702d49091303071100b00901c00040d0003800410703907070b0213018000d10b401d10316440c0d5119400a81942042503d0340c880400201e001694100052a800d02548035044a6031505040c85800e02100d984440d1440b0001c110700c00041e9a5100f603490a480500d90000e56922011343e0715811092075004290031074606803188043c0440010014894086400715254900d00e8440440382e03401280c1d4014443c010500c018402140250081c0000040c00b40c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 608339631 1250 608338381 608338417
    0x60b09130e0706210c0503040b1504050112030807020c1e040b04090b0108070801180303050a1103071119050d082d010810050f060f030f03040303090501180e0c 70
    0x200e012400c0655540c40396010401c043c101d01044c9440000c9061001c034818000c11031303003000c50310190562100810051010b480280003808811348030248026410025200304115a1a5403070390324442c0c1a03910035070218002200152102d4400902041c2d4914048d2031141211040700c01986017074050b14015500503112581c60f41705841e03d2152440040c0604890702c2d155252008a03401d104c0c083d009001301d64105181040e01c00101c042d0361214030782c149400940e56a41010b50030040c0446100714403004000424050081d52010620b0604541481555038042c048003404584058649004020f90020111804500d0251141582c0245031320070050071007044400c0090300c8002e40b658100b46a600c131006000712402003000f102e000440940400682c10100c18110344020010f20b420f00c1541c14821000c019103060207800d07240d12400085036182c130703141d01e009015400940142c074001090000407120b01c030b440700340c440212207001c690305d007407034541c00017266455110760280500503000c0303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 608340881 1250 608339631 608339651
    0x1203180c1c05030c0d0906091a03011205010e0607201906022104060c030501060e280e0c1809010b0a050a031107030c0506061212030901090803010303020a0c09060b0913 74
    0x28413603400c81c40f081d61b0b079512200c0c5c20721401070901a900e400003c0c6140c000840b911403205035608403810744880c2c038229100c0d802d2900d000b502402c07211941800a005100a005105070440144100f070700c086038401d4001600780b103030b4680d600c6020a11460a52003840420003240c1968000e084070032030746040700301180070924807140860b0b069a0454402d940c45464498040e413500c500c9016005601e41030710300040500c00143d0600304070060303140c82d9100034813680c400100130384400014003443c00b00c840350b0301d48445a822a82c00c280404100c0e1a50f4600c0b1310708030325211514905a40354444100d041010641d0202d03079030b4000f00b007030f6070a0542d101042c400c0c0c0a00d50b0041d0043c18030030742e1401e00a00740e82c94881c1c1400c1c0f0103070195010300f050422940182c01d010404070405280c0c0d0360f040380c49a941400381809400100b201400c10f403000000030050590110303040703503410f000d0401c03c5400b560f0f400d5603804580b00c074842c0c20080c60382401010300f54680603c1201c82d24520040208040241c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 608342131 1250 608340881 608340883
    0x50402030c091008060f0c0a27030b04020a090903080f130b090a03020717071802070209010f090b1005090409150509030a1d0109060c141203180c1c05030c 68
    0x2c242d0300400e00310ba40e1401003001800400040c2e5102480c4400e1044a040c851540200303800303581a0f240074004440c0c03140281038401d0303c2c00f03058800f060b90f20061582d520f00381000080b1054400341d0080080031000309008a5500640322044c0e419958010b071552900059861200090580c0682c103030101580e80100b40082070680c02204008050100c44444d803402030302e080080c1d0303c642c628205101149491803000b0500c0c40c11a04696a240c0354800c0c400400350003403181e48002540803881d00000700d500121401003001342c50820904100c0080b0030002c01c41009a02520100050400c1021024a08050f0040e110191003100c0042401c10700c901d000c0142c0c0c0c01164458007903030002c40c0c910750700e0342c2c00060080406074404141c1740407003030030000a0800d040340c0614424020007900420420040c2c0314030b40180c070481c5c016200782c1403103400a06400e070720135075071480d5400107107418004291010908100c1840d00801c0c2154900c005400d5050706503000c6000e0350345010900c80300c6c074036541c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 608343381 1250 608342131 608342149
    0x1519140706060b030901150f090c020f0313031403040b070818131a0a0f0e0603030d0603030c02040501090b0d120201110409060509010602070806011412010c0804020a15050706050402030c 82
    0x444a00103440e4134102c14402e085903190140c00261f0400c818041080502c1000740c1c800f070b0f8903400d901042046040000780e00e01180f401d0040e026200001e404c3c7c80130b41c80030032800c0941e48196075416401203064042942c9010300d000e1410581000c0211500080c4144010550702050300d0141610407208000202c1c40079a8040910001c0d440300400640e005540c24007804107c0704585a00c00f150034210040c103600020b004440b09520000003050450b5802c00c2a6090103444200510070680c0300d03e001011518010701c100e000e0313810100040fa40d00e0b000d009071380c000ca81c0605205407114050b15901c04102c40b19a4120540d56a1035a0b00030a080c81d10003000503000d180300100b1828030b048140035070040140d009800310b401080c0180b10200010440e90304541428050911655a040015204400c100c2c0241c0c050740c6408102000c2980080c400f84c400e40c021038061076242d40d6206200d4501d00440210400143d0400a07240000da8a5028a0300a0f001904850720320b00b201004c02c00e948 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 608344631 1250 608343381 608343389
    0x120010f050103140a08091c080c10060b18090411060c0109020a08150f04110d0317010801180b0c04080a03050408010b06070c14040f1802151914070606 67
    0x150300c5200500c01d0041c504041e807002820000109134950b10754491306d1543c020500c000d8460207031088000c40746250380300c0c1d02c6a40340d003080b491a034900c28403000d1035442014908000c402800c0910020f501041030042e5500d240304101d01c0c1d81c841010310100316180c440200704503035410442401c0c910b1074a601e00980002910503000042d890540c0c010041c061040f03501003a841d501c00323141001201505550070f90441207500f00d40c070040e01d803031520000c950080f15117290040030300c103040381c1419800f2240803001e02d00c82d107501c00c2c2c59884902c0c590a8a85090145191300004000d0b00d00082c01c1d0810141c0c000c124a00f400d0a00741c88003501070602c01551401d500080010905012040003889064140f21086940c14605681c0388c0d500e42c3c0480b224400c090030361805c000190030035250354201022241090004002411300711803003003107540b40381c0e401303900400b403004050981b50030010413600304440d01e401000c1d694680700b0003152250a600c00c8c003660b1440034400300c000206180601c0c0090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 608345881 1250 608344631 608344661
    0x5010c02061b2401050402072112051006180f170c120c01120b151c060306050702120315060a051b150a1802060c0304120f0212070f05012001 62
    0x5071041c1e40504000f00c1a04030070300c036600c108100341c0052420704e1461400403000e00341c0c082d403c9241c0d506544c0b2044109051441b41e09080070461f40b0010aa0103205903500c03620b403604a10750f4041d02c80384d00e4150b030181100030342c00e07003105101c01407498004212030440c100455080740000c40c0410340a1038044049540c5510a825030b004940e00000c0c1000340040c07900041103081940d40015030b12400c40c0581c480d40d0700c0000361480003000c44a1181800108200c41031145541c2c80c58590000e0508403154401401955240803210104001701c03401504440341c109603d04c8079104000b240c0d0300204082040c0b0000b00403450740e44124a14142440460b0380241c968018001448414188020040400c0d50300d0180c103c0a20341180642406194060341c9513519003000b41d480d01d19510840c0c1140c01c0d841000ca914408000c842d0141c50744007403080c0e074001442d404941780306071703911030b0742c010913072041d200c030005000c0da510846940740210800311034001c00900c02d90145003120405010140a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 608347131 1250 608345881 608345923
    0x70c110f0a09021902030c0c01030203220b071b030816020304080a050609010c0f1d130617150402101202040b0f030702010c180b03060d1e11030705010c02061b 70
    0x42c003050303010304404c020060f001a500e441c41d1418050f0716410a806000c0c141640030001c00c0c110111030910a04c07001c031802c421080218a0308104803000e20444425000501c403503807111030380c01c0d42d0345200d0b4030030f078503480e80090743c1c5034003202e0f101455406e21800110710080c8030004111104101e1820f48501600c0a8006400c09070100da0a48030910000c005000903c00e4135065281d210000344a010703140300354010011000c2c80001c040c0800c00c803442c80c41a04003100450704141101e14400c802c1250310807541c10074440c062084501900700e0b4062751107814030b003c8044250142c40b440800040d542d07001850562a80c5064002c1c1d00251a070300c0011f1408020402000d4091044048210107810b0000a141c1c03032880640021109020302108014017002140250300c4009444a40b03961020707461200301200901400c03c0c5102c48001e56510080d044030070294140400e002090320b00680d14106440c4c115024004558070070017000082c200510740810701c0b04000e0003401c010f000c0c00714213858 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 608348381 1250 608347131 608347147
    0x21b120a0306080a081902010b19060233090c04050406050106020f0a05030f07020a090501030305090915060f0309250513020306030715021f050406060e070c110f0a0902 74
    0x40b501c003030708031846a901455507000494909000d84450955603103401401c0d41c1c00035001c1b0b001d060300d48600d5070040080d0ba00000512600c81c4800d041c2c40c003503400c4406407190000304d00403a42c40445c0088138000480380d09450305008110b2260700001550494a401d038140300400c0444070b0488007610710f9a034800040c44043c0e414446200041e030703800002d0681d000c0580361992a44a0101d91384042c071030001d170001c115100d414030703a0014400388104001c90340c1d4900300a08550f200c0300c906480350301c0340b03000a081810f101c10300100945c8040c000900300700c4002c0590030680e2010b40306070810b10902e111301018000d020707000c07444000d8003100d090301a843e0400388034202600d0310052801a00510070070916450014140c01214500d060700310490407415816401c005040606084442c1424410703c000180c0d03401043c02140301c0c98041040c0c0f1358071021718001c12010703106200061015001180421b04080c0d003030741d1150004010b80303414030980c40014640322903030380500103080d00810554 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 608349631 1250 608348381 608348387
    0x7080403031d0901062007030605060306010b132105010527010606080402100c05030a0309110609030a0f060204050d050a060e070b0d0c1e0203090a0522021b120a 71
    0x20b0900c64030103201c44000c1c0500ca000401a2805014240c20040035a442118403104902000c4801b4119000e40c2d00c0381e03841c1d0414101621003114014068455030000003402c803a0304041340c03400d2200c950034011180c10043c1c0131040d102c801288101401650b04404007081c000c4c81158040e14503c001c01c09040260404405440005142d81645903d0044200003240d00301c0d8980b41e00075411201c48074501c030281d0090b514a604018050554480821584601b07501035018620541c001c5240b0050440e148003005014131a500304150181c00424a20001403119150408000d10640c000b41c181600c541c04508040c4c002c6c0802e850382d80c810017a910034007030b40e88906d8101d62224009800d509003010150141d40c0314441c2038030100c1daa901c140b1000580310780000701e1105040c074000c044040e04840000d560380c01002c1030b03911171300c1110400192481c0c004a913810354840c1113514a040d080120002c0300070b4210081c0415408d040341420943e0340c2e003c0c0027104c0d0305c03d0803542d015240c5041807801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 608350881 1250 608349631 608349647
    0xc060d05090606040605030309010c051603050d0801080a11130e1b0f030105130210091d09060a060f0b0a0e030717060a020405090a0f1e1d01020f040312140708040303 73
    0x12401359103455000d100503100401141d40020082c24110140c0c007251928518041204072241458481483c01008100e00030170a10308440603695031100698031441310365110740404000400ca480141c0c4003c00e90308001d1000208000f11040008d0300c1c2001c000b02c2070418000f40c62035108410030220006007071401c500c00e6039000f1810b40003080185801403002c1ca8110310680060b100b41c1843d940904c40d280304800b071601074040900301142021201501d60086481565214154000d0b480001e9442c2803500c9007108640d0300341d101c00c215510f814100501544103048900070004445111541610708000c080000c01000c00c400400d20380c1072003500e080000c081c0c40071400c5801004108865a910340e9010380228500c20006048034840324401c0040403259140c0c002d030348007a4840e2856000507030086280c0314100c982e9101c0b0004503043d15080307225420588510040501003480490341c0d49082c04400318260400c440490409143c542050b045100d04495103000001c040c404c05d0ba0200c13038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 608352131 1250 608350881 608350891
    0x70909060b070303110f0c012a0c0201050a020709050c07060612081210090c0305220807150225030314010b0304171c09120e03060106050a020c060d050906 68
    0x2081002500740012400c0c1880b8400028013099182c409202d01403400f01e04641004a00c22011a07131284680101c2d400b0306812440840300240c1014082c0100e02c60800c00d003a84903182d40c80c80501071030385e401034038180c210030406030851061820204101c0194803403036001d40440380d1820707220b5a0919100e4141c92964000e18440c10345203880c5030000d0044800c0e00c10052180c1340e00d000f255a0800b00008080d82640710a000078203154510038142e130964000760040b807610800c0c0c0c1c41d05440981d01c1010f00c40d213a0004151000801482c00070070011140700710400045840907140181042400241681e0050b52000b20340001489004041d018402c107901c540342003540301550740c035224490515000052000e8403207131310280c5001207220038108039000c000d2800740b0405079418580b001c00060268090031241354040c244000c0440b4012401e0030b01d000c0008008280b16030a08070101c8180d000980c05505502c04c02542c1070710380da5028050503004e9000b14002034607280807a085450402c000d49 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 608353381 1250 608352131 608352149
    0x1e0c030203101112090a0b0103030e0910061407050102070b04211d0402070c0509100513140403121806050f060405040201020c10170c0405031506060a0f0203070c0e0709 74
    0x40042e000c03ca032201640c41c4c4507910f40c1000100d6450900711070402c165110020441480c0000100806400401200000005a800c0c104650341d1281103c44000140100c4012806030508080348082081c0200061840740d400541010702a80d202c0230116002d42c1c04950818a4a1900c4414040d414120b11700310128a406002c070800b03103a0900c0c000c0c040b0041280280c1d00021058180040900750710b0042c0409000318007280f0b004040d6168040090003001e1090140000745501c3d42c000780070700303d000d440350360851560303413078a580c01d0340d1030000003007070b490500e407141e00c0d00311410030529030b14103c1c07805403801040e280b0f002141e4182994000f000940f1842c41c0006000c0541d0340002c21905030682501c0704c1c0c20048080030b0903501d038450a1119040960610100700c0b00c45040343c0a0401c540c400c1e0100c0f282c04401070314541c41c550040798100d42090042c0a25842503205030032000d0420310b0313801640c0c03810b2600c0d114a0482c02c02d640000d40100f0303a61080c40031450f4801300d45802002035003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 608354631 1250 608353381 608353391
    0x30807020607140c030c150709080c03070504091707121e0c08031b030114040b0604060c020d021c0317071b1b050a03140607050715091e0c03020310 65
    0x45028000d000e00341d030303e20036031080450f412030724100c20400c8a60030f05180081b22090540c01213104c455030403ca4641d00000e04000000074612000981100403a00007005041300c1420142444010080c000069411030a010300b0114041c44071002844480e008817a00009109401c2e00174000305a403d1449d800c001d00000102101075001111421582e8401a05903480d01c80410003c04680003400d405190140040002111140310b5140e05150806440600480000e1020000980105d128480202c0e01c43c606000c0185442018101c6162000f0200300c90249103400201062402650841c086611201150790300c0080e11042a4888124a0100075580d030329294803808803407860000f4600e0b2030440041e01c43308182c602e200d000d00805020a0303a2595641068148000218441c500600032240450f9501303102e0811103043d40c0e00101500c1018081c0300511000f0700c80d0100555441a62924a0031814030606c00c0d046041d01405004041d41d055004241c02c0c0f00d1221241010b8074030380 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 608355881 1250 608354631 608354641
    0xa090303090f120306051e1302190c06060b0313080a0c0c180f05060105180301110a0801140118060e010903140a050124030b040302070306020316020d03140a18050f06040308070206 79
    0x41c0701d02c11074031042035408016030b0702c407803100360003901400740351181990ba00040e50ac1c1090344160320300c030018060700d02401a56130302c0c03019511b1403005890b01003000396400916000b060105008060014052418000c920072513182c03001c4950075a00085508a0901a080c1d0300a07030a01417100201e411000c100502c0c1801030028213140b0030308610041e06c0c0c8030b04440f100c913a0707420b40c0980800600d20501965560365001c00078548082401050328003034006c0001c07402548602401f100510056100d46400c609004064560480e40b2403880d041020b4643c000c00060400005079a0100311000104240d6a0f145059401d40d0b402c0702c10050200340e00440039101c5503404150b0003c5980017036940d615526141012414000560030240c440c6000000f8400420765501004805116590a0fa84041c1d43c5c1402142550700088059420408c00400b1a944030038540c820100c000707030f1107044080200e01c0d544960401681017002e40c0c4940003003040009164010b40c0d40f40d0704c40c00c1403000d0031443ca0f00d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 608357131 1250 608355881 608355919
    0x625030b060d0f110a030902030d210e190507080705010219120203120702030409060b0310060f0c02030708030c1513030507020d061d0c1203030a090303090f12030605 73
    0x45042502c10181c6400c1c9001c403640a035400030710781c0c1085540196070340c818460041c01500b400803049002c0d214081485610300c0c41480c01c2118500286080400c904d00d1815890151400e201000b0060140c04a10405502d0001d11840624800c0e800b400e4074a213802c80e240d09001641c0d00c028155080041c4103052000701c000c0c40c200242c0e2150001800940e40f05049196001d10075aa0b221402c1c11824003607455000405003007110b45100041c0070481d1503400c0d12160340429210410306003002007082c030443d40940300d0000f04952510304a5001c10007500024640001c0f540b01c0c0c80d80b90000101409800b009104440c0048840709003284c0d1420501a4030304d2552402c800a401c018020681c3c00031956022940000aa08000e06020b0680c2d4145181c008103405527200764284103002d100c111a00380004810060207000001c0e5042d981c070010f01c90060031002c2c80440415684051010001c0e40c0d29a0072400e9500440107202d11fa91701800160488483e074000500c1200d44460743c001e4942 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 608358381 1250 608357131 608357137
    0x40501080103120e190806342114060604120f06321501020703030309020d2102160e040f022d01030516090509070504080625030b06 58
    0x10b0703c0020030181501c1000c08079441840414615400a215482400365102e60403a00c01910558000d8544030349880100000b054081e0b41c60044004d034086400c103100e07018050003c800c20103401c22420802038004203249070203202004031400c540e0390b180604c030f8a0f40078001c5a4000f100703603030003841c00f0f003031031a466680134034032000404440f0035400c03000400240b034101d03a0440308a510312120076031030480540c0302c45170381d5607040c00e503c4039201c0029030300c0b000ca00c41102d2101c0c040e005230010605540b0b0460103000325034011b0360010707503200071800000c4020101e082840555000c0594884d2826402410100342d0404086c0c54181013200b0700400300a200c203e50040c1e8001c0b889100e0381c80c1840860307031008040305074101810209418503c614116016220703120400d9030100040d545201d0000201401c4420b464001511000e05108034100102656003080c01c50a0a500701035643e0380407444e00f1403c45810b40010440d008404010302440c00e092036a00482c1800d0040c8810580031a810b40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 608359631 1250 608358381 608358383
    0x1020d0e0c1f0e0d03030b120105040b1f0b0309031308060601021e011509060f06030e06010b07020d2918060a0b0a08010e06060906030307050c060306120a14070902040501080103 78
    0x403203642c140e1450040c0c805241421010304a40e00c00e01c407038240a0000c0006a00c820301078800c070040c0315058401031044912540e40101c1000907034460300349401c9180c5d034034001d402d41e912804da0040390f280802e101861240341404001c65403454906c002030501040c50748002020791090003401007503a00490701c410a68020740e00c62450b039084e1000c0b2405420200400004034101407408a80c1000b243c1040b81610b010300500c1c20788556910045084906441440c9560b400072401400118071800c020410140020400a11000140c48001c072103210920100380044400301e42c007a94942c0c0700030250707004080c400314516a2500b800d07119242d5000503c0300034255500d44040c9000d81c2d034040c2d0700001d080034a00812030203500605444e9500404d680903880742c400740c4001401b81c83d00204481d14568803001400e07001c044103050190036000038100c180c1c4509a4440300f41000b00420004075034034000c0000180c0d6554410241c1e0400e2940d800c04115a40100418085a40c0000c5011304413 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 608360881 1250 608359631 608359669
    0x90a0e0408091c0f03032f121b040e0609070314072a0b060f0a03021302070c1805161b02060f070804060f090e0f0103140f010204060201020d0e0c 64
    0x1409a24550750f03582000c100041518149165003403d15a045e032180ba02a4840030901c4a4042d401c401e020042c2040342c026400e03a94104086401c1c025500305158000c102c207201d222402e29518007001aa4210b50080400d00710b41104010485c94003e280c00c1d04402c16040401c0020400c408081750594010031034010f00c94042c00c014580e50110001e41010209000300c0d40301c900702c1e450a454125010749006100c0c0c24201100100d900d4118012003c60764024944900075010100b082302a4000d0401a183d40d094907a00188018000307540740110030a032400000c0d145440116404221030320280c02d82084050122a542d07007024000b515401901128815150000c010709440756100d140b00081000c0070204000800c9a04802048601103103601d8145140d41c65a8001c551f0550454100000e00b255500400101e01c040c145100e61140b404140c4803c400900344860a980c00b551040b80143c0d4000f4440035400c1a61155507a2100c008019203400f01c83c0780300250081146440d420700c0303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 608362131 1250 608360881 608360899
    0x10b070302210c060c1201031205040503152410051b0d030b130504030207051002010b0d0822180507050d0e06040b01080d081807030c0308090a0e040809 67
    0x9040c001c100c4044040403406510b8405038900014950700e0300555850180351041c800801e004440c09416151100300311913041d034260b881c54642d5020007002e0030b44041031150810010569480900140080c6c807452454100f4074100070701c209144480151100f000080403101c49826591004c6a001104089285c91601e9682043d070108a103148074001c46202d22505510080c400d4158124140040041b140104031284140102c02a02c400315030040050b000110240613600c1c1480008000e841188000590020300c00c1c003041980529003020360b85103c012500360f03003c40e520a8140000e0190707100c1a05e15078a005039a103070000900e000d10f55902c4e00c860015101c075106c0c20594144212414060182074030345003005407640030668040e1402e104880000c203c80c41c1c002111804e20703038199a0074600340c0c2d50408820600c05502c1c950301d4503004140b00000270070b016490f8840958040d81040d5641d55204040029203c1c8590000070480d00850402001c1000041600c4121605030340e5000d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 608363381 1250 608362131 608362133
    0x2090f060d0b09040b0f0c0f091011010911040c0203040501021203070e150304110607050d2001020f09041b020601090e0304030210030c020106051903030c111005070c0b12010b07 78
    0x7002d8080d42980d00d8000305200100300070302031112403050054a404503007031032036141c0248201030f81c407540b81c1c41034407400d08014190385420185050742d885000c61424010141c04d85904d542518594041070341c640440420003041d51078188160a20562030b8001549468641800130392035210030840c60348049004000100c0b0503000307e4071940701ca40014191020203000743c104150a82082e202511104240f0701985601c1c1031103022120540e40200003410500354003841140d60082c0b1400400041c0440304844600c070300240007410145080344011515022184144000c0381d0480505503d0b41241540d41010b080d0046a031606481081c00c0c0840c4071038800280c02d00d1403085900094100c8891042c0303401c16580355011002400c0d469001b4001c0070f5807130301000114900307941d11800c0c60352354580801c00640144115000d0511401c1d07118a90b2094900040a105080941102207140040d1020400144010a1b40a0403900c86214249102c482e0b0f000302034041400b0740c160130303080018014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 608364631 1250 608363381 608363407
    0xe030306240c01020a050304030909110904021809090d0210060b030121020a0e0f15030303070f0215040c081c09030f050a0203060a1e050606070615241202090f06 71
    0x5080b036500e0000070740d03907080140001000c0f0ba000301c40980010f0040c800105016440340540103c030400c031a450340c10500711b4400c0000a6100540c02c00380448890080221a02c4154515100d5500718000e0071001c015208040e052a00380f402e00c03044945400d034284152482c66050744d040d1520000064500105129400051268102c010354002035403540003412801c1c0c2c9400a200d120b1280304205580c0300d0601c11807440307803034049841e85504144000b840c181d01c05d8042c456018140d104175510049040d80440d00c0c0f09041c2c40a407004908804140a003c001b0440b00d01140e4031000c00201d00c0200070001000060b50b070000070440ea14501d100c20610404008485200350010709450050038200700312001804003d81c0c212840600408032001c60700903100d04c620642001d41110b00d802c1450313a0340c1c402800f4103140c481031008a40c902188540e80d03442e103150860046552204e0401010001a021201002d001031036140104110230f80d81e107481800c513410160a4403141d0301c0300f2182c0c500c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 608365881 1250 608364631 608364637
    0x30b01021f02180402090a0b031e04050a120f080f040204022503030606050a0509040e01200a08010905060f0907050c030a03020915030f0c0c0a02040507030f0e03030624 74
    0x350101d680c05090305070014000b03a00508141c0c0010790140741a41c0c56209000a83c0220a40c2d5503200c1e402c02c1301041952500300013558030003040d20a190364a90007100c03851a50b04162003c1d2000c0d401210004c0c01c0122201d000c480e44826818126603410040b080107001120040c0104008007221010500315200c6406176981c41d0310403c400c05140002001c280007820f00050258002810000d0015107035000e8000c5505007007241c0d40307580c03500500c03100380409080d80c0f00c000500f640d80e605080c11404c0c85903104006201441080e0b643c0d81c1e9445d040104408011780154010620744000c0c072059699803520144640030950341d0540c290384000003035605018803c10b0305900c1c040050b016038219490f50080a0030002290500041c2046050540b0f0600003103450001324848040419000320f2000e02421110203901e044038000d1000f9801300f003c0d0380f02a20118042601c0e480c100f83c40c030700705001d1141104100c0c030040d0700714074190000481c4514600c00e00844010000d440780140000e040031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 608367131 1250 608365881 608365903
    0x3010b07080d110409241a07050a050102031603110301050f0d020a170c0102160b0f0c0c03030a0801090b180c1b150f07050301121113060f080c0619030b0102 69
    0x11881d1160f541d1311103400030384102499070301c8508140c83d141d8600400702c01c0e068207031030107903405900031b6251f001c0300c4c200b0794000407050310f00744600302e41000014401d000452040e040c403002e401242a1200025064980543c00040707189010700040c4490713151403007011401d2104440d40001241c2034004184001600e811a0403681040401d81c0300100d40040c1c003403050350080e400ca8169150300704030903801d04202d000e8038001203010484490071015003c06040407009803425100b420440c00e0000340b0b154041d10700500807801b4000100020f180c1071052100002060b5452010030151514822030072400400302d0b05410300210700c100d222441102498901c812045c00c40f5030400c42c1c403a041142e50000c562045002c01d12500140c0780034403400940e8121041002c0103808110103540f807008400385a0281a000183c0480c0039000d0400c03805a80014050009181242410000010f00f003107075803203445000721420006003141519144000c51203c0c01882c00065401c103800040b4103260b45108 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 608368381 1250 608367131 608367161
    0x18060406050c130803090f0406030b040305070c0816260606220e0c0f0307060215041110031b14070b0601200105010503160821130e040b0c03010b07080d 67
    0xc3c0200d10118004010440e00707004441501180355608204001d507115404004c09103040c0c0c10200d00028052409001400e02c103100d03040301ca0380c03181541850a421541e24000d070f100b46910030400c241d000031122000b04d03452110b0007585e9051041071983c0340700203084a4062020209100b50740914070803020861447c103003003401089046440340c3d5903500c829010f2440b81541603803410b69442c0010303910088810320b8002c0d01d807150480b103805400840c006d005603080c14071040d0080c0e05070b490100181002140703480c00101c1c1c2c40d05040003500c228400c8101c0c024402030400b0011961000d80680b00b40560124941e1144e03521140100d5001c80e15490403d1400c0b0514485a0020b1064000c24184e80090f022500041002800c4141d5800c2501c02e28209402c0041c00075801c1d14081495021402d518200328501141e10b0501d04a00350194403403940340703c80c50300380020410761105264000c0700340b0f801e4906550414102d860144a00d10000b0715800000640d40d1003004a900429869502c01c0707 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 608369631 1250 608368381 608368417
    0x40b252c0a0f21030f0c020a050d0b1b040b040515040906030f05010b011b0305030703060e010801060807140102070513060302042307030c120c02030c030d0c0818060406050c 76
    0x420701403030302c01050003010140b512020340c0304406002d06108140c00d0790190303902c05442e10524402d0310403d10040e0241d82143d42a44045440d80f52500303900800e6102c0c0744074081e1072801041100b54004440350500c84250b08000c20859041100240d500307585040701c070740a4040800e0800b951a1140354064200141058000024000c030074010b0050507005500138007403200c40c0001111054480c08002c3c203113441d84112940400d1044000d15800a40ca040019005490700304108084000740d000d000c5d1a0b44460742440350080c14040c010042880f080b602461704030a03000070752140d40ca0b0240e00d026240f014000c0e0020310840d00b0440055070050001c0108916880301005c044420b50711010711800840c0104503840e10038070684805840d40d030b5480100285070b40c400700c00b034504194528114030050007400341c0d03030300300340010311031507281c6100000c008214100181840e58014848a07203039180102581c1000d4002c81c0e00355100b60700c03490001d003070380d03500341d004040740582c3d00d905511080c0d003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 608370881 1250 608369631 608369639
    0xf01091508091606090b0c0a051c030f050103080403020d03021903030218030c0108010b16060510150203041d0705070807050d080a06030f02040b0303090603040b252c0a 74
    0x101030740078002d0400c00207807034003094003410021907001c0620980d400260100d00030090b12444402400b602074546095076800e81045d02c4051404621201617500c89002c03c07954203006805100d4450489000c003018809036146840d05001c40c0920702c00a07010f02c50103001c01c1e04051083c1300e00c1d280c1d001011014010070045081c0180250002202492104452a04503800e49030000758035100ca40140c0d22503800d6070030020100304541007010b86100c16065640e00300c00081c41401034030f00c41c001820103560024a40704001c000c503100710604000f5900108400e03c103152294035030504542211808a82d1034844c00d9049616200e615409021036402044600c10403101258120009d0501d507110a4552521843e1400b250b50501c0001d08006c600821a030042c140b5810840c40c07220000e0950303050002e0030011600c5036208840c1103074002008010051003444400c01892603440c1c0388140c05004220901c0070f0303c0110307c5010380c281104280d040c440105849030304440140c501400ba48101592 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 608372131 1250 608370881 608370887
    0x8061003050106140d02242106091e13080d1b030507020a29091e06040b040201030b0a0302100201020406021b280905040b06010f020114060f010915 65
    0x54001103409500f41000000c09460724030316110300c088014400070410896a0803c010585840030b10b0744240d0910190451204846000d070140320016882c40442003c4503403201070f10a070041550f4441e100e50401d02500810000c81e0150014603080c20300150344a00003900c08940250400402551000a41101030310442e0014080c80040c0c3c1500080c0c500a54820340a40e44102c84000040e84901502404115100000321900e0140c014070741a007420449090b0300700740215131078065540500c0c0440e1100e514170ba06444c034038a0b448080d0001d4201695588045000540003a04042c1c8a20407948103544007400540216802000c002d0108a4800068040c0d0010300c517440c0580141c00d100246881c541c000c0d500800001403601040d040086400c038150034000c15480c80c00c0304041c02c041900c914611845000d28021f40700c41d0072901d8248001421514605280011079041442824001412440b2690408403c4400c0350b040e40c04140100c604480076071102c08140c01c3c01c40703400e0105030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 608373381 1250 608372131 608372161
    0xd060305100c0e0109031113152402030301030b0103151805071e0f030308130f0501090b07030b030607110a020319022d04050705040339121101090806 66
    0x90b003912120300014841c1d005540d0000d10744406010518084000714140c1f4000700d030710421038003d0100081500711140c02c800c0500c0c1d10f4008214040c40208034040f9008103031820b1008803090301c011407966042d0358a800c28503406101c001d000341c4840c1c101e10305090701900550500c503140c5035401d482415a0400950303882c02403044a0060b40a60340d910342000d2101d00400a60740000205400d01d441c0d40d40071030341b040300100300d01c815803403911205000502240d4580303940c07805100040b03645c1c2c00d682002048602d0103030803e001c0c14608880408a9280441e00940c001000c1c18401c81101107402e18034282131858034029418001c2c801c41010a07070510130360070002d9000341c880c04002807580030340140b5805918022290440706540e03007c0c0750310309900103642c030241c1440c00c10304003035590b511060080079503500c245001c1c4840d601c1c0150101610305a011417806141c10918407894800c09802c0e42e030000324050901b1038010380c4221541d0051088200a0294004450061503d2483c14413000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 608374631 1250 608373381 608373401
    0x507050613140c06030f0603012d1404021305060f0d0c0e01140a120312020f0d050a1e0b040212040c060e030a020a0e0403200304080709020a0f050d06030510 69
    0x4051140100302d4240c005410080e103d40903200c030f441c640751118210708858004140726810341d2a1140c06800310681050486031501c0c8640d05c00c5074074034044050b41640e080d88441e0500d012000c0400000d650303000c0c4000c07c40404c0d00c1e80015541c4441e00415010b128245030150013641ca51125800c0008412150b400c684603507600420990329104060581c644819081740d12400059042c0700341d040050b403003d40d503031290824541d0348111460f60020782c0c00410b492149108042020900c612143c0074069011145130820001644081c088143c4040410110501150b80e030a4103003983e01c0303c3d1f04a810111030940d084c40207103001d02c0d003010314181902a00c80003448044000b03031715050024400785240d600030001c100386414943c130980f20b03000040c002d03400c010f005007482d00d49298030814a1440e001c0c11000d1a078442c1018042c1d483d102d0641c0c005210035104101d00403070654030640034645070f035803882e20303a40d00c84006a5200282a440c0c1010700b8034010b061400800b4a0f09500010300e403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 608375881 1250 608374631 608374643
    0x5040302330a02070f0212010b0405040b01090c0e01201906091b0b04090b030a020d03030c090b0403120e13050901020301050f060c060f060d1a01030c2102040b010507050613 76
    0xc1d0b07100301c102003c1c1e024946005000e1080812034000514003400e0260846c030b00c03040002003a00c0344000190a0351002da0b010b07241e0380056001400262003e0181c02141005400d01185200718800001e04c2110300d01040070b8000711485401d40000001e008580b0811181c85204100324075500740203000b884584001c56101c94503d680700104440704a40e40c04a8201081e054146441c2041500140c06449038940d858080c00900b036005035207212581050a004e60303000122000680400380041a258008600ca05018171082001400116072803000c210140b4110084890710707804901c0d01104030354107003005400c01d42080401c8105501540c1226070454004e580c4214580600440344a001c807400e0702034000341c00107a09034140702c4d00f041d041007024000c10708025042d06c4400003101042c0041140030204d800401c10710056a41e210003600e201703c040314001c0d04580c650183e283c40144000c0c066a100d443c075003603983c015425034007083d8024065501d50300e4103807405030f1a600418021598 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 608377131 1250 608375881 608375983
    0x200a030c080403050a05070f020612060901061701260f15010b0903030306010c0201271e050a060f02120301080a120504081e030421030806090708070305040302 70
    0x2406225210890042d901a21840d15020801c1821075655010f204240d0384041041c404000507260b02008200080d4920140c12081c1807400400026010680c844420082c0075041c0e032002900d031480701411905d01610700818481740d0030114103209042001899680540b110b500c10820b808160246d0909a610302c03503800342e0303c6c1e03030300b06420340500785110340c05074030078000103026501544400d01c10500506000940b0340d6022040025010200c1c031840a000300008100601741720110500314444845c42c50300e180d10b041c07001041c003048403440341c40b040040d13030021180345074000e101417151034817100b140390754031740e1140e6030b9603aa2101c4c1c17882164403e0985105040d0188034a0076582910303000b002804103880192804000d000d40f100e110b4115000c2004001045503009000240d20581c2c0e510140200b0711030f0801a000340c60041c061030042003580100030134568400d00b0143d0050355070500203040e46590074101d240c8500f44406035501c5442d0403101e5226003d03c0441580b088000191040f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 608378381 1250 608377131 608377151
    0x3020d0b1522051801060b131a07170f040303030e2e020d06050a0602010519180825260405060d091a01090b0a060c02100f03200a03 58
    0x41070052450103440c14401c40082d85200d01403030300440c1c0c01002010041001c40440e05141d800c680380303640480e8413401c00003454410004803140b0000240600000028441c61000750034145202e980b600a02100d1803403050515802d2311001d4a800c0701c40780b000e4036221616841d0190041032113140c4030340b040c4240c5124807101c0e441d40c0ca601d0049500404041410026412120082d40000494600d00b585400c03020030b9544a025040300148103540c004580c0d41000b030007802041ca0b903208091152400d041000064800b5000030203003d41d480080a40d58596000c541c1e1000740d040015020513145814823141446a11082048500c203129410f1501485500b0540d2041c800c9106160b0062014014004240c039964071013001503000d59035000100810105001c2c07455401d8201050382c503a030708103641007030404186010140640f4206080c081400750001005014603441d00c17420444040c0c1c1c0c01404a100350080325103641c03850b0f011001000c98026000891300a2000b000004c0c1c60a100c0c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 608379631 1250 608378381 608378389
    0x2405160627050a030305100914010905061507020d0c09020a090305010e03090904260c2a06030f090c060a020a051011030c210c0712030203100e1003020d0b15 69
    0x10415903800002840d814501395030540c05088024480c1240b17411404000400d04400d0107034144200601614815540c14040071704211040a8080303030086452515004510320b0407c00c0303400d86d42e011180740b65002005c0c40c0214022403660008040d081c008504c4468036900180c051055a101c0c90090000015140342180d5900600e120680d010071200c010802207400c3c1700a2100713030400011003040c80785c05092210141e520110f020005a44085000084108484444440044400ca07003a900d040a400081c0c1c1d9400058070b00c100e5221401c000c0f440103d010030020102080143c03030340d501c4805100303000e500c0b500a4403059603540111029130825448503c41d600c0c0d5503030412056402c0d07442d030111001c01e507004070f40c40444000012040c0d042e1420400000ba10502068001d656038012524140482801480c12141403600510070312284c4119449850181c2e001036026108507502c1007403080201d00c403036102940004507840c0840c1480038607181d0760b1107002c1d076a410710002d0040740140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 608380881 1250 608379631 608379701
    0xd020712051804110c01020423040501061d040b03060a0902010e030307020904080d0204031b031b0509011401170c030f092a01200318090124051606 65
    0x1070340e80c1844400002c0da680303895800b0881040d440c01005040051500859089034800d1300144880e4030501c1d920010100d8001084951100581d801d000a51500c9405011506040c002c0c19940803159020461070b121540710800c0c011000301258403509001c030008004143d21701c81a800203144c00c0060500e8100002101d10207075004d4080b200999540d00c48040580040c1e0440b18a80d400300000004680ba921601d02039844088203407800e00d2544c6002d40b403c15049050640000944008000d40d940301d42c440d07070449006001030700b074003018900102c821241d00b1801c0c40214000700180b00c00100e5420196204990a003000c200c01e44401350060717560b0ba21a10b005111104401001d0702e80743c01485400d502107810306003c6541010380d42001c2c0c00140d140c21001c03841e4400316590106003115140032807000302c1074030845000e5052520280040c1c62808031f400d83c080000c45102005485541101c500104201c1102581c50207031802c3d5000d419a14a0301d21541000510064950405204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 608382131 1250 608380881 608380897
    0x1603030f2301060e0a1706061c0b0610110106081e16181415130608030f03091603110102010c050a1707020705040f0b0301140103020a03110d080d02071205 68
    0xc028070320ba1030703c078007240c070204000700c1d540c0c200c04440400145d212080c555150038451050107048030f803038110280074080d10299015074400105d480404013090100d1140c1f90040c2c020784016109a22141c002d403400c0314032864150f02986080d46c000354400700403940000c0c1c104a190501910002134031595034031003e6041c6000c0c5c4a032281c00c10858019130591140c08070f00701940104030700d00f441450304440368048803031502088000c0e4a5561034134000c490350028a122040070040d050a0940b856035034014405003e00180c0004003080c604081003003125041110550480e070555103034640500380b008092911800756080c14040d0310400c0c041c0c01500d0003c070f001d5484020100a283c0d42500b2880e0181000301176000d07602e4040f5140d103441c00307021185240ca600205240d03101105250840e401c000e00030010280343c50052005079103c2488000b00c982003d10103040740c040100103462507140c4c060007060f40400040c4086c00d5001c54002c0e0007078901500000e00505411803003501c40b80301d2980 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 608383381 1250 608382131 608382191
    0x30c03031c050a14040506040309050603090309010509060c06011502010608030405010f0c030e100c2d230604031d030d0905040c030f0e0f060703020c0c01141603030f 73
    0x12507020210150742c0550341c00052141c000c54414a941e40c00460079505480a4406030407140c100070500d908041d100d002080700b40c412610714500300354000e44a018002d0901d040001c00514042c1c15a5400140c0b48841401000da641d01c1d69526044100e21103900c0402015500344003000480000c04400d40341103a40c10386440340d0400c0b080004a480080c2518105d040c01049031007130019442e600404042200b80e070f2100f0988269609150040ca10b0721042034055a886504202c41101c20340e5090b00510b52042c20310300c040741c440740040c0da6000d200c8080301c1d092098030b0800007415071000507004088550700c840c140340d6054000b4503450300c03809403008001c60602c442c10410340c1060381c0190105a40e500d8000782180d1031564400c00e4030f41160385000d075540007440d48075600d101401119005022405c0c00c501d841c010124298856044000041c10300c4505075900081d01c65000440301c1c1d0000814188809140394580a4010003154128074025031500070100304141403d010019550441b032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 608384631 1250 608383381 608383417
    0x9200310030b040f0605010e011802031905091207030206100608090604021908010e0c0f0a140d020d06050f150109081b01050c03180f0405130201120e0f0705030c0303 73
    0x1031901402c9030000740040b40d000c2c1802458501088075803190324003070060350040700640c1d4074101d60101440d8108248a010354070400170f1102c0d40400c102c6803c4405078800b80462a0b5440c0311f071080c109152203c4454469400040c49001c05034041a4144a40301075440c0b1004642c6850f0100e4036508101c80c0120300d03a0022000c90003510300130307040528000750b01960303c003610707241c0e40020b0948800c4a8421039a601c207140e03600c1d45103080e042e0300b20701e00b106031000c80c000e07450042140341d003001070007645018013216001001952507280c07405140c44d8000c0000e00580c103110084401d41501164917903503a0510743c0100000350701c121205000c035010b04000700b8810350b40701c28103454032481d201090f041c80b80c10001d00c00c66080500c040d003030070765070400401d220500c00c005001d201641510464030a038a04002c21407503501481e49400504d80a281404407084d14262001c02807002d4603000ba0750f48140c4404a0765550000799041c140c1d501030303003982e014848030814180da03405140d83d07903141543c043c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 608385881 1250 608384631 608384633
    0x6040f1a1203090d030203040302042007030c0602071212050903180909071d15032b090e090109050c0613060c03090b0f09030607020f0c190f0920031003 67
    0xc00c600c1075400c1e00c103009683c9051078890016040f440c140b04101c016030004142001036160610400d00e6681c80c40f800072209200001c1065084e2041d540c0c020140060000e1400501295505462540f6400795001081c3c200100010700044482d0503e07c01c61802e000020b1240030700882501c4070410400c2075261a0541181040f54404000b028018284038103600092025628603180401000507114002c1d070b030814241c030824401d1170400d000e010354007505852502c0460305c86144181e01e00d10300a8004688101011130307212140d0740c01983c0c0d1b400c0382e005205000c5010361040741d03581e10990458489070540c2c0180007a1b4081c611001c0b020010007042000003c1c095081076007801c0c820302d40b80f81103580701d0001c3c11454100007260000c080010400c4030342400e040001e80d80145030b50000704003604580200a42d60208840180e00581000440c0b44415200c5048030004d4024155030810076525005258002e110115001000100498800390349820a9040b81d0040901d6000d2500081c01c1d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 608387131 1250 608385881 608385889
    0x50711011713080d0203070c0c09050903071401240f1e050418080f07020a12170d1d060703050c03040b04020609060c0115030309090c090e100803070b06040f1a 70
    0x82d0403801e40d9050340412403000c0042191000798440c3c40d40d80c4607034401c0c5041e41000c1300e04011a800c0b441c0250328000920407644000401e0302c0b981075101c3c4a00c0d14100002c80360a002d48a20031b6011041c0ca00302c41c0a41511403408260303c00c0e20302c60800003d2003541d44100f51411189171800400b9450140001e10842c1400d402000440101c55400004c0b1a2603a564901e2503205c1c1c5000d604081020a00c0001c40c41c001c010a0001c00320303644010410f49046d01c58001819242d29640ca000704005146110074089403c003450b00004910421f81e80070740c1d0082c0341d441e0041150501c0001c0d00c1c000000c1c440d04e4405003680e0007241c0010701c03291140e84940c02d20405903c0168a241d00c82004d20240101d02070074020300007040294140010020310b1440c01420080b0350750404602a818100d120602036030003d0003e080b5035083d03182c00e040d500ca40e0f075003000c03040c15a0860062070000042400600c10398030415030041a080c8d0301009035024848221040b601c80d19540510f1400e240e1000040f80344c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 608388381 1250 608387131 608387161
    0x6061e01051606111b0705040603020f040c09051203180406061e05070b04050c0102010e06160c08040e0c1206010c0c030320030c0d031107030219050106030b070507110117 75
    0x1100e6400012404203a402c2c02003c0d4000c0b200c50040c00240f01715595400034240300c0c03075004120940d0148226811a030000d503000c060080658040c1c1e07aa0114555214456060b00009140c0035001421280d1042d500b076459904c031180e41904038204d11245559414a442982e003151103ea4800c4255076208000e00e603000500310030013007044000c2c00440d010411a0100394011481540103140600a0f08006403c0da58000c10300582c81d0031440070014002461007540e0a40c048034030300100038500c2c51802c41010300440d0003060201829101b0010b1280780000101481014045481c04c1071395000d004649541002000510740f40800408000190040546040340b074180c2031440d40002001010510b90781190b6600d00d800e60040c0122044650103100e482c408a10303041001b07181144a860280d9528a00640038120b0203240312102c05000c0203502801c0610351120b900ca201d400c003007a0090050b00005001c2c1c0d151251820721528940c058801988000e51191000c4815601c1900a40c4070705 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 608389631 1250 608388381 608388383
    0x70c020d11030717011407080109091410050402030625050c010207120509040b012f033001241b0503210f0f0109110d09030206061e010516 61
    0x482081d00c0c020242e8050004401500f40c0d0130710b41d43c0882c603d05602d400d544442c03150030501740501051110669208090a040d108204400f0402c4200b901c2d01060003035040c18940818050440b00101c001d100390030040c0164021400c441c45d5442d0080e0341c1044001c0c603000d80079610b5504070800c0000b070080d00a4800084c8010006061040301c0d1907103a0b010561111003000140b001400c10042d02e01b5100d115941d0b2020f1070700d981100107440c071441070f60100004200464940d107610122258040088455400703903420b0400740d01003282201d09840003d1800c11500100160000c00c2b603402004117040d0180450f5484158109200400d64041c03101048001628084d0039800c00401c10400040c4015185601c90201d40b50040c452109844070181014403a0314580046c00003014405415034152120840300081482c88a5100c003140d04c01c03000103030039042c144501d60007490340100f109445120150f0b0f00c51042e01307280b861040000c00310006240428410f0001224100700a00a0040d817 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 608390881 1250 608389631 608389643
    0x21020d0e01030e0d09092004030204020c070320040c050901051b03210105040e0d02070918020a0b07060c02010510030305090a0b190315030c061d270f070c020d 70
    0x41d20800d461420103c108070404c022503102c0c10204503403d07040c4540d01140040c41a4404080c056a00d490305900c118030000c2c2c401c030f401044400800c00103008400082d94032114586250b080549808000d05040b00b860f88124505440c04002a0041c5c013160214001652100e1170b000310208440b084501400c0000003e21040c400071540d900075490402c0d5000b4600800304503036240404100550390402c0c50511203070032000b183d01615400040c0f15003070f00c003000c0c00460f2400d080c241f409d01841e035840b0060340c0001c8040700040d6001d4080000c0c141c41e8021001806000c414460a90a070341007502c070051810703860700c01003010a00c11400b41c141003034020243e0042c1c903515041100e0641042000f00b00c0c0d000c1441d0084680394161040c485461002d45141091524685440030b0000346803250380117000c948501c1406000040d40b044550141c010010300e03841d6450003042ea0207034401d4161070210010307917020071f40400d20311030761034464000c90781d44101342d005990a003c859641c3e04021111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 608392131 1250 608390881 608390891
    0xa0b0f0d0618020c240c0309010b18090d0908030906090d0632010303170705070f0309060e0a080303070c051603050d08160e04020c030c01051321020d0e0103 69
    0xd036000b9488541d144039410320150701c681d03a02c0250b03414500b40c104070326064000c250049906685030117403130b0f030f00101c0b0b03406858413556640c030414090b00614858680c00321400d031300c101907110107108050159091004a5041145050341551251084d000301303141c40d0300501c10340d0b026203005402089031400241c107040c0c0700c01e92a90341105503000304001185460102ca105030102c1824841c2059480c00070041328419455901d02510440304084d01c500000c4118000481240c0204211025942d010303640100400850030b00078a20415409403000007048003a1806c0149001c03003070302065602c01005980345445103042a95803541d0b01c8021541c42c0100540d0b4061003070f0304071a00006500800140a40c485118402448040300030588600c02d0394070141c0b81c1c41130f81c0c016880c082104081e90016610280400c03940e1a6000d11046003000d51b080c90100f01e0135000c02d0004c011030314400d1501508881c41c400041d10a0b1008000020041e0b20144111385140d10034414080c88403818180026 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 608393381 1250 608392131 608392139
    0x100309020607050601050312120f060109050d051b041413021f0503042102150406110c070f050301090b070e04020d0608010902090f060616140303040c03060501050a0b0f0d06 76
    0x7945410560040d80c03903412400c010407090800b8014405407903580d5041d01d16040c190712410440030006440501d01c0700070700d800540306900500025020780001461740d000c11185140040e500c901240103000760180000154499050a00800d40b600850100c0c0707044659441080d4807980400e4907090741d0091280e0340d0804041604950a00b20301895500e06a032071405e410300691003503480301103d480e0f02c44c0d0800c8000142e030100d028030642807212444a55034030b0341d052a0000c8c2025060701920000006502e0740540000188442280d0800c650155001d81d500c040500300e480c41c0da07001d460810301e2400206035610407004141007180c002e2006050421598801c021a2401c1d00314070481d0307654400703030003e510f408081c40d58000200042542640f038a50041001801045800d00517010300d0301e00c2404009001e034088280c010248116902d0b4545030400725040c141c00c1c48296006880d040010800e8146803280c0d1058030401001c0500d00b0841003c161020303405403ca089040c0c0c1e40d000b0202e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 608394631 1250 608393381 608393389
    0xe040f0216030201050601050403080d0b0d02270108061501180b0301060e011d1f02030403140a0c230f18040809040b011e080414070e010303030e0a0c0510030902 71
    0x416100d0204107400011261450041e084030000b030901414088107000420020754880c3c2208c0ea243c0b04c619010510f0000d10f03000c2202d01060110080d8086415003041000681004003010482c0d5060ba0141d4140d03030750b5081c1d81d01d401059400e21b014085208580d001540603c5424541d05160321a01300495514042209143c000384c0044000500d10000303400c1035a802001002c031b0703035424a900f401c8040300d0000601801340382c650b203100746201121224520341c000c2c01075900075500401040030489002191039100c0040e5881292106008500400d01c4202081c0300b007000e80c058862045101d14007001c10842d402a0f4290603885025034908080c5140c0050342070740103510a01200362501416402c00050f2502c0305105410080502d91925221a041c84d047d41500e4003414143e5994490341050310060341c11b100403c80c984a180b900081030010011024100d80c0690340400040c80301c442034a0320b416144c10007825060788650700b40120b24250244044c048900e040001e500c011a41c045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 608395881 1250 608394631 608394637
    0xb06010e01180e0a0506040218090c04030b04060609050906150603181f0b0d050c06070c1508042306060103050702190c05040609230601021e01020a09050a0f03030e040f02 75
    0x5041d030b40e01400144080035203a0300880d50040030407541075050039042c03c1017127126031060074054800d00381d020200b0b441c00d1303204088401458120b98080c01600e010b04000b000352000b881405a902d140000044543e800820440e0080b41c410401c06060403c55040242c10b400140aa05c01685410311060051908002041512901203c075401d40d211503460703401110002c0141d02c0c068200c0d003805d04001000401e98400d441c030304841c1c0903240d504034100001916116002003045070a00d807d15000180c100008911070f40c82440b0409410314181d041c4003100c420100c000420750300901c0810115030080d008246d01c405580704690b000d01c0d1791544003000405000c0e041c0c4844061000501403030600b03000d11000380244510601c05150384c01d0010012558081e0181500030110002c1180d85c2e1081c031603607003a401607440d00350580c108006400d00170f6000100719004204601d80028450500c1c030716840482d075601040111451071510140e80c9641c0d28080e040e80700740d0350704a003900c4508038405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 608397131 1250 608395881 608395889
    0x51e030a1d0c19060e150c030a020a0c080316060209030c03010618050903041427010b040e06040506030607180b160302060702070302030a110d0c09020a020c010305040b06010e0118 79
    0x10710341c410045081c40055000e0414520482c3d9400e1028407581c1e801c50b140c14081001501c03401c04c407066450a142144c02040c0425219000009900c61480e500049601c1460301501440000381e03540c504142c2d60b031003048444406018a1814480070480c1a406001c0302940501902c40f40071554000a0840b403240e04141c41d001021514000540d40c00d2103415400341c41030005500d05801d241000080d04441207150340310303166104101c900381c4052030405980f1720300d41800300050b503110340c1072203040d41203805a002e0307840b86039000500d00d2400e80989805028040c02425103070b00c9000c412140420407030365448110306001030020724080010700030446210344580002c102c0d021407900071304000020300300608550008505001503600419250405940300908410400c043c02c04200384289146010f02500c500075000100072142c0e40082110070001d5007583c00a114032401034048074010344001c1c10b40300d402c40c00110903500030401d0b1821440141030907c0c4a2044e680319030b56800d85608 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 608398381 1250 608397131 608397133
    0x10e030114011a04050d0f0203070b0a120f050403080406110405120c120f10150b0304060606020d0230090916031d0a170c01060905010312051e030a1d 66
    0x10041004584444481c010001e003c0c504918040c50180022000c400c0b00c1d002424070308a41209100715135080016a005107200c00710b0a44038104000042c10540010074100070850500c2600621140207114451003580d00d900c0e81196038070341c0d4445c84010282030a41c9501904100000700702561804c448019081091004065005040e41440402070b404e00329940c20360b01155a000324000041040d54030000201000200c1150200c9120104107042d80140721042000051005000b0150842e02c165500fa400321142d40f480300100300c5c1e5401c80c1e01a40700d8041540c641503400743c0c0040541d10f483e1041402440e0402c6d461000140c1e031140d003a180c50f8049449018440d1308140c2500503489008003502100342d00007030304030f01c458644804031001025040d8a0301860510900e040c2074803043d0b40c5400080020b1510303441c0303001c0207210a00080e901d10300915800c04c0805c1c450b004503241017141c2a41000340030b85000500c03015403c00b500d2184040e445588504002c0b8404007000d1050103148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 608399631 1250 608398381 608398421
    0x6030803070e15042d0501091707120b0912030702030d0f0609020f030a060b0a1413031707030315061b110d0c1805060a05120307050a0c0609061d06030402010e0301 72
    0x2e100025060456a60b0180044c20717508100426078100387d02c2011554548603c0000011042149080c046c05401045170a0000500724017442416001c69105200c001304503081c03085440050031017404200d5800006901c20484040021419000705c40c19811800d408148591a50460b1042c1e07001851a8660345038080304000c400740143c0180c00c01840c05082413481c3c42c2c120007000704180c0104004070b94040300007508500000d034284500004542282014208036260000d41d5106d40c00b4080035000241041d40300c5000c070358040c05070421a00c00340c80c0c0402410f220041080c0007000248207668181c0d50005c9040b03503446102d86001141d2082da55500d005040401e00a0481a240c05a0310030302d2070403007003180c1601c49440c0c003c1502e4007100c8801620914010b40c506d14821000002d04034042d00c2018802c0201e4440441e040c5c40254580c0e01e4081d855040443d030314800c0260a60110264009203040c0c1e08000780110740184c0113140408200d01d10a01190079102d001200c01c0742c2500a17 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 608400881 1250 608399631 608399669
    0x2030408071e0605030c0d110c0a12030b0108060f12030c010c051309022a010209030a050d0e1f03020f0405031504021c1a150d050d0f0306030803070e1504 68
    0x15680d40050f06150625600311b08103584400c1440c01940030081d000b940d40d60240500b1000346069400407100b45044910081c0039103054041340d488503811300046820310758500c0d034960184a41520804c0042c01540401129170208460360000050a41450000300f02c000101c04003070141c0880c00c4080c1d100c071076039031007203030010a5a0540ca52002c0b22003072040c008241e110441d81d04100c10215865071100000c48880303805070091050aa100f82d240c42904030845c1001808100c02c41c0b5030356186c0300c0b24410880705003800349500104040c10007e040e4aa445240d4a000340e0242404281d01c01d4114281034850020078501112108042e0301c0d101c10700200f004600d8041200801c0c40c0700c60721040c002000c05d0361669202090f110300070008124200010307a4283e549000c0120880c001000c81003100440c0c200035444500003411840010420141001d45500034020b000072294003021240c03440c0d1700e400c2c0c11220842d000c0843d503070103071200c508618085100d802a001402e40300f4440c1c1409070403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 608402131 1250 608400881 608400929
    0x103030c0c090b060d0b151201030606080303061c1703180706181449110d150518010501170d1202120112021003050f01150203040807 59
    0x1503901c642d0186003401640855529a5000d0781d800c0c0b000b42601240c8204075000048600d5030041c44107010f0240852a15007070080084114105e0740103580c2000361549994030b00341c50f840225103048d044201d454032442e0044645400400d02c3d4083c000e9543d0242d115160b1490b10740c02640c49602000250741030000c503e400b80034110081080e420801007464050200e089000141d108402105e030601ca950b10031611411a000c50540381d8145101c1104650b006068058240810071030030710380c00207003001c0d00305070f289180a801900302c80c05086800b2820704200a81501c00c104903110007200107004201c03c1140906409840b10743c4940381c0613180d81d082c060844074164803003020581c4030040505c03507840104640504e6252480c08108401e07902800340e01a1003101c83c80040c51031503400002d00304600780f01d448429403080b22090f031103d410b003004800f541d006880c1c1185d103101082c010842014042c1b40054082c886d40103690801c3d640301728070b034208403940c2d00080140000070580109261 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 608403381 1250 608402131 608402153
    0x60e06010e03010606020706110102040906032a06170c07060903020304080d0e060f0318101401060c230f0a0f0c0501080f0115030209060d1d0f0c0405040303060e0103030c 75
    0x1e8160020448985450300080d03941e4412300c1210180f060b0102e250107800000e404442c050000d02e502844400e940e071034540725030119020491ba00d200200d031964020101120000100e805956a00d83c12048203045112500c3c00604a08a440001c11070000091514001c0348442c9009401458032503180100c0341d8100000c040c0b0020402904100100c038642d00c001c00e49203408486079405440e5580c40da0311008408010404081501c50f2180d9081d181141d42c120407031070741c031640140c1c4031641e07200f8082d103589912400003050f0f04101c07201c49458980d1050a8501c0301c4016013151640f00320050540d00f003840c620341c20340722144050f401c0c07001c1c4140717036a0250080c00c0a2826030380918000e0320b000d90340b120601408851a061910402c145031298040d241c00110041000b07a07206003042caa80010500641d0448140d91f00201d1840c090300301059107041c1503106805040d40d00c600c881000004e0500520480c14960780350004540b201080741190301071442611a81d00444070b0782891100c42e5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 608404631 1250 608403381 608403407
    0xd3201020a02060a0906150e070915050703230d0e060121030807050906120601030e0106050105071113020403050a15061409040201120510170109080406120f060e0601 73
    0x40c0c01040414032566002928a40c00044844002041036a52070b01c1c1014260b902500c0a0405111a000c214030b401103250500030441a2a501880c650f00c2007400381141007242ea80011800520504000c00e0081201c8034986107240d5104451313191001070000181c2101c070840011350383e6204039100034081041700c5070240c03001d91940301c10001801c03142800003410002c014200a541c4001c501c4007401807054418105000b0300980d101c40001c140c2040702e1a04455182c002410310007080c05124040c80342c0b200340c0308103a6400f454080c0c0d54946190700c65042901540003001d00003420640809840134102031403180c00900100003060801c1e44d2502d900d46110a140e6150990411035961031441480c010401665440c2c0340d99140d00040c0c8080c89461270340208917090004203d844242d031020401a689840110131185000600c080c1c01c0b100166070040410b02c08020a00c422409007004c11042010300b14003141c02c0b20040d00c1c44c4240c6030103911200d9210314003401e00c0700315038024640c00400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 608405881 1250 608404631 608404633
    0x30207080a0b010b0d0e1903030513200d051b0a060e030601180e010f1b0908101805100b090a0b0906010806030a050703080a0f0f09140d32 61
    0x10303070481d01c0394040401d040c41a0b00c10302c08005680340c03283c0410342080000c07001c0d0800751040c031031040b1844003d080707840d00e003100003e151030300156180d84240349018076070780c014992402e00810406e0002000c1c0c0240c5040307512090104030303440050001c00103202e850f151500c2582c0a10100c170113100200c08140c20103801d202440066414540300040e285044a00b0b80c2204400070114070403480080040100758015942411040d81d01c1c09000e8008001140c400d2201c4000310304c1d0310f00102c400149c01e01590400b40c01046002c0c1071142240c01c01403250b02d03c204250308071071180e80c900b45042d4541c03200700341d41500c481e0360744411300c1c0600604d0340c0709111410034400603500d0320006010620040c101030610001d100801d0003924200701070306240c4e5000080f111901d44a060102845d000f0220210010b0b601e270000d002c01600c0398403511540250f644500e1101400d2408554881a068000e16006070401c0c0034600841c00b054101841c2d030750b9801c0703120461155010f0000b95805d203072501d1083c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 608407131 1250 608405881 608405893
    0x120c150801060c151d06090c032b020f0f0f060709050108071809060f08060604060f141504141009120206030604060305060c030f01060201060506031f090509030703020708 75
    0x400307500301401c681c14a41c080143c2d491135403080003520040100b04140d0980c01e00541c03c00c0c004100000300240174444040c01c982141100d0340815a4501c1c1403400482c0c100e02000c1e01050046c0101000710304001a801503500c00c03410300d030a140c03408656925090081d8458414148128018040f00350000d005180200c81e190038200080c3c0907000c06420401049a0b514a5a01c500d5158002d0b0001d400c41c044280140c03a40c0ea03501d08034074603040c00f40605c00c1c001d6402180705441c007440f90300e0480320590044c4021074500008a840c944c5110340c0f1541080d04002005021b10b883c50051020785001d4400c070720b9091490080c0495030710210352040600a14201c10701891011200c04071480307a0460340340d40e80b5a036410200e40600380c5540000c00324490142440404114440514450303200000005c2c0c0300d0ba682c3c0012403e8402d24840da50300b141007040803426408030307100001008030700101160303120369448030f400c130489004540c80240e941000c40c1c000c00309981400400018501c490082c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 608408381 1250 608407131 608407139
    0x16050f06100e0c160b18031b070e15060a02010207021309110919020d060f080c1c030f0c0201030902150d0e0303060a1415130510050a1403060a120c150801 68
    0x2104000c0e00601404105c4e514000506140d034a00341e1800c141300100c01d0765100e5015040a03143d50984400c40103d600130684045961624003480c207204044080c840103102c100e40003032241c0b581c080c680c1c00c811950208560809a00c600800c14900c00b03101d440002c62a045040c0a03800320042d81c42d143c441c0d0200d800340500c000b500201901c0114482c800180d4034450f04501c0d0f0004c1c2050b502c040081c020310507000a000f003006c00c1402d070020302640e003d1070408000c50420313440800400014040780c80410408c0f04640f00704422031407288107040c001500c0446400083c6144076400c0411a9070400003490b50007032846016145031003800300000c40c11030a100d400106040418040c0c11902600200d00d60016629514182c01c0f00155500c060740d80c1c0c122100340d43d00400540212402110b03604c0c0030b60400d52040080b6030b2075010559404049114040844440e6407000c0c0c01030760701c0a0240d0000c01d0140141e000341e000d00d8490245000320340c2c58400700305101c60403140d00000703110450b00100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 608409631 1250 608408381 608408407
    0x40b19020c18150a080309010f0c0b0c0307030608060f04030201180b0c0c010207170a030c0c0f0311030408010f091104060501120908040902030a0902010801051516050f06100e0c 78
    0x30760140310359144683e5444012001c4150000d010142e884165035200086911011006003030642003a1707150561a0107078001680c200d460560010002c4c0c01410000e10800c46603409103811241c0b900d80881c0c40c41d6100a2030385000001d03540891b24103034848c203000406409209403402c8503108114601020a41c1d01c461000c00c000400d158501c510001e062050301e61700794100d40c4032607400908000107946060344909290840010030300401c1c40c000a09107030b00d0003040051074199010491409088066400311801c0c080d032880c50119200034000802e802c5030038040c8401000c0d5010002590403441e0401710400c0d601c008120f400740b072400c1800d001ca40d9103c40b0005002d0390011011854403003c1c0380182d5988515030004003142d1010045c80740352540f98002140c5507000766500b40403640c0300c4040000d40002c0c80d41c1200c110104004545016850304402042c141c040c0c0c0503142d81290f070300030b007c3c2440340854000c3c0c0c04164094041c002400044100b0740c0100d840032a25007030000724881c0d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 608410881 1250 608409631 608409649
    0x120f0c020c030c1525020409050a03300906090605130204050606070305251b0e071107050f042715090305181c0605070314060a1514040b19020c 63
    0x56401c03c1c17078141d030b0412420600124500541c1c0d000d00100b03c1400c0604100e07446103890750b0308400080d124250b03006c0c204c80418a0b0846042140c01d1b00c0801500d90300800000c051010040700c80c1038840c208200819124802d2510030301e41340301c20580444061040200300d49008000c244609000d0190341c0200c0d6119054540b28080e181e246410340b54450000b03e0700c0c1404820003444024001d13265141024403a507408100c840f54001c1400d6602c40c010103640c1021710410b2a409580038480030401840c280550300a110b2002c0d0000070700781c60b544032100c9140d003600d0046040c42e0701800460200000008001003074400c8001c2000803561070f83e00100f40d8070a06240c081c0c00b0301003100c85001640d070f0085c0428807000503814000d200106140800241c1011184440400e10300b5590042c0c070154001500e04c5514001d0984000c54240240410707541103001c1d52208020080c541741e9903842c40e40008101034010b00803416180d600407001003a640080f83e0201086400111100c0309a444005035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 608412131 1250 608410881 608410897
    0xb030604050c040e0a0c0e1c0809010302041d01050a0e04030c08090f040222080a050304051201020405060c01060e10031a0a0e16030b06150a120f0c020c030c15 70
    0xc0828191104071071540540203c0d00014424003091003486205907032980010a281d009454107440d900d035100401050805442c601c81c0e00101440f01000016000c8008056040050500505064990134251030038042e04500094011070300005000c140b522142c504c00812183c2d100315003a150540d4000d18070030303402c2401000c000e8040342c03508a50b551822201c0c465170700a881103489031019001c8240400c4251213120030324040c0200403c0303110b8080703039002d641600300000350301d06864242440b80c4021081c8400c00c0e60355003130001041c2d07944d400000f003030031044c0f44001240c2d860800f41084501c41010300980ea035164406800c00004540f5111204141e031042003444450742c940710103501038441d99010000d40d0162443d071000c001141131080b000c0d01d01900d119200ea40c0c9800900850001104038000c2a03201030114100191081240004107000014041041414940c09105a946207a102070144c0c00c04032800384542000c01a00e003000700d085841c407000001030904040c0c1031145401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 608413381 1250 608412131 608412139
    0x608010617060405190611070807020a0510090b090a080105040803071206180e0c043e070206030a1404080a03050601020c060a030c0507021c1502030403050a030c1b06050a0f02040b0306 81
    0x17001c1000c1c80542d40c00208940800302c100d5030fa90f629450144116441804100d208a5503020007250500380f034103d02d0b5024580e521940c004604028142456410440c80303540e018416501c0410030910a0284501641c072600c0466168101124080d0141d0100d00002550a150181c10014201e0310542c0781040b5000c80e9001818800c1480002d04001c0311042c0941c10a00304010242842c03a04c0c44000f25160035540c090321a5900751a02511a600500141d482c451003407041c0030251510400564225042503400503a00307200d0410b42c2030a40044405403907024010942d00c7d4060b4040c01074030350081007407014005080c4603a0020742c01d80101c0070300b0410555940d60b00d183d01341c0180d00f01d8005d02d40007003020281c82d107890f45d01800354403100000c40311040c0c500e4410080840500035640282e030b0549659041141041040300140095002c090400c0760407880d020314414910010380c0044d004110106140c9000001c41040c0c406d40d02000044030302c10002041900451810343e80c014004803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 608414631 1250 608413381 608413423
    0x9030b07020f070b0c1204080307020613080706080604050708060a06050f120a270c0306020306130c020604020108010807030308150f0604060302030a0b0f130f0f0608010617060405 79
    0x20000700e16241121082151902c608000400c040120740007900c2840c40b040110345034002000c0540095002d00c1c0704409055100f405072500515009018091181d85442095035596540140c245000340c590b00290101e00f02034140140c07030505014440d8498041c0c2070183c110308008001c0307400c0843e230784210410080d020802841d0700a2034411034910850b029904151418801e69610040090b0030700282035221542440526155103140c3d081002d41085103041840e1640e120300d406940002c0240398403a45100022504605a2060410108480e80101181d15091001400d40e18060704100001d41c440b440800000b58829112036120403100144940c2d011854041100501048060340c0c0c0540046408103055500d5030240d0702c01c841d03100d000d00c02d0f95060820710106112014075960800c0c00b070800d48004801503000406002c10f00b54002610069401c0c0722000c0315100d4001d6491a51110002c0203152000c0b080d01d0208100000500042c5c1020303622107035180c03020149190964415 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 608415881 1250 608414631 608414641
    0x5010203031605041208120901051b071a04081803010b0d110d050319120209010e0108090705090c040305060906061c050c0d0303020a030c090503060c0706091505010e0f0709030b 78
    0xd0b50648005203201c00c480351720b00c4010300d4869610f40011100f05403500c0540001000d00e02c05000d4a80180a2904510708007034220004d00d0003030340603210a41e0003d0a64072001b046d400358110321407241c1c0c010301c00142c45050710f002030701d241c211391080d4900c40d0307042596008155981e8510803078819405040e40c145000781101080e20202680e001030a580408100703000c052007000c40005544078143c1d184d100e809041c2e4051012401481a582d0015544041c00103665000d0490346401c08000d400f260041651200065003040c000c580620503554007103400c1007004000c002585e0040e05a04c050421450004046148a11018009900c0b028010b98002c244002404011100c0c0c44c058001240d803901c030305001c3c1c0a5407041e907070200080d140001e118201d512801781e0f4000d40300c00901a20440c2c581d010003481d00c2c0c010340800d45003280d40c2c4003048005001c12400032240004441e010a15614043d441a82180020025042c8005200c00c200b00603a22482d198250383d40244640800c0d120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 608417131 1250 608415881 608415887
    0xe010302160b041208100e06130e061812040e1b0705010203070306050a050609090106030e010b0a14103902030f1c030603050303060f060f0d0609060f050102030316 72
    0x28610040d10102d00e1070144014080c00c41d074042000100c03600c1d8100d071070f1144920740c2d10303500d814801c1e4044501d074100401c04030f00d0071048007000030002c4a4046060361a0400715414a04140c80d081101143c40094420480d800c2c4888981b481c0010855420603141070b0032001120030041c08810b60320000280b0910208140f01680d00058000c0000c40d1a807800c203002500070042802140d10440300c0500004807882c00500310b518500b0302800000a503443d00380154003403d04080145269502c50b2507032105a1101c01c83d80ac0240000d06d00703809a140c0b03000a00080c4035503c900c40080055080c0803082c200c02c1d104070300904400701d81c40d004214041220b551072000083c64000e5260081c480b000c1c92040740043d8803000348a0b003101554900e2004001034040f182c503444000d0807504103200241e92498910ba042e1030010b00584001d140c03d450582600c1c140c1d1000ea5141c5140eaa580024850700032248190005000c02c81640b101090500001035640c0c00010a01329001004080c0c8114042c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 608418381 1250 608417131 608417167
    0x5250201030e07170601151b03031e090b09030c031204080d11070605090d1232010e010b0901090918080301060903020909151b040305060109060519060e010302 70
    0xb402e00a03280c00781d03107584c02050a0100381c00c52207294842e0a00209048104001d540842d4000f07884000c011072403c001002c119040d10301c2941410354407021882c0b418030418018007040e8003490001424560b91074417581011015140e0200d0750f00a0240c034a69000000c110f90740000b006040c480160749070b1501c0c407241c2c0b04003200780c0c3d8020b08010700c41c0c0102000201400d4880e100d10018000340d6945007049580c5c100103000304000400881c1c07100f40711102070781b00c0c2d0340b0242120707008002064a00c00b68a071010441807003c1e100c4400c007004026442d15001c00c1030160a104006c28540394284000034a140301a00800c50041c0e07a070480c0c01c0c040c102c0c501180c1004c9500185032a01c9607580e80001e0036042403440107034080c808034000140c1d06400460324901d011001020350400e85c6821100c2c20100c0301c0d544088500d2001004040b003c28020800c242c0209000364000c103405003400180000004e8442c00810708122018040c0b0034283c02c907001c1c2da00384501307180050f114041d804d500300c4051 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 608419631 1250 608418381 608418401
    0x30301051e100c1a042612090d0206150d06050a50010308210a050711030a020d050d0f110409152d0815060307060525020103 55
    0x9540002c03054030240c0c002e030b40014440e0080e00081041060700030080c88410b41110000c1802c0c80c03070b04c5424100301d820000003a9413014155120f05014411000400091081d60b84020315401000445011b0303504102c550b60104481503400c04090701d49010411403014036000508250315500000c4541405901c0f00b0000800e2120240c050700207201e90303840e032a2400c03c110383e442201694460390b80143d60503001d03c84801c091a1242a8a1911050050b0b04aa20349000000e50740c0c000080c1801080e203003500030f41c4002000101c030304288001602450071041e9060242d0802d0004440c140e8022079125807640c65800c1480d5200301e02d0340410300510300380e014442c44925190000c080030902034090b009480d0849003c00c00d81491300301c0341e8983c00451040a0718599031130044c0400410300c11851218107855090700c1c0c1078503100c0340040e0900035000c0940700301181100c1004400d207805c2202000801040c2042c6140080521031440864030940c41c00501d00042d44101c421640300754080d031801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 608420881 1250 608419631 608419639
    0x40f030f11030a080f0918040609051b03030d0e0307081308010507080408120919030302090f0102070b04030618080703050a120e120319020307020601030309050a1404050402030a02060c2d030301051e 87
    0x608e020320b8010000d120b045000d6945114841c60503100e0408000202c8003401d004000798180320300183c080c1e010f845d0a0b807640383c01e80002d20091002030f0845020f003410710f1a40d0707001d4121500f03180e0200e0840e48006d100504021070383d002e00c004600518111070191607840318440c01c4d030b6102a072161a2403041e000e50840e112043c0106003c0c158560301410301c1e00390880e0f450807808040c5004990300d0110380a1500d41250411040001843c160321600c1000c0c8041204002005141c5812002e40c0201c042038005c1000043c41148455110440c020b5403980c0c440304000c407111840e8850303944c0006032961080f40800102248003000b00c040c00d800e092410400540d5a4944031400a407100800e100c21000304418000120300c0e403915030f8100381038500c06101c441c4080510b20400014040141003039800d8040d1601c1c00001da21844014800c0041030001461f03910410384c00c80720010791105022424249000c0d4402840c40040110f904450084412129a40c00741194dc040e0344015201c490340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 608422131 1250 608420881 608420929
    0x240b070303060e15041a01300204060309060f060b0301050d030219061506020105070206060d0305091f112a0a241409010f14040f030f11030a080f09 65
    0x900c4818801542e01c0c2181941c090080a850461121640d4020741c845400700310901405d1840c0425400c848070131014101f488c00415082c2000107040380d12980001b80000d403508034540038000c0c0b071f019042901c03209500401c00c0c036240030101080ea00040c01110f00c500040020501414804c026900d0308140603c0344451000c95880d00303d00400c1c0140031003200d10741c0344500240003030043c03040e18803c44164010b402c5541d50a0100492600f1035401181409000d010042080d00c609042031340c80c1005000030394560411620151158000b24513010b0682c3c4594107100d40790000c07200e000c28001e00581700320805501e0303100180560340182c10086a2411648000e406560504003d400c80060313501c483c1d2210400610801442c803c25070124003040103103c00b02c01c3c4511036481184202d00c040321050501da00c6500d0441114030740c2e0300c19140c1131520f00050301400201040050985030840003420041010342d01c2c11400d020307200961501d008003084902c002d803a9441427100001e1541d2030112 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 608423381 1250 608422131 608422141
    0x70213050a1811040b010c062c030f12060a1e060e1206070c03200a060b0a06020706080c161b0905060f040906020d1509240b070303060e 60
    0x5140868180a9250801e40000700364162040380b0b41e01c031030700200300000001c0d0722000c0c040030f8010403c41d5410403010748030380008500b00344100341c1916404118040b0032055404841800306c141c40d50710341c0b660010071800c1a0464118101c80080c0412401d038aa5a907030040061002c50a90340025049407401100500c807074003c0c0c040c90159401d85c0c440542c8002054140040348948403250055a4000000310340400d000d03250744c9904a00c01c1c9443d00180362041d20f0489840c0c00824002d02d50361182c24031004225640c020b0f514010416244800302e00c0c81c00500075940c80e42845103006210646021541c5031445400310b481000b80848070503504804c5241c00c00300c042c6101c0244c1c6003002c41841c0841c0c50207483c042e09000c0e01d0018040b061020a000820008000090003192595070803c000403c81c18940280b407818100b80c1c00002e5070500d80b009075000d0351410540003518450b0321080940b807854a200250a032100420030507207400a6280c00d400401040e000014041000d104100b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 608424631 1250 608423381 608423419
    0x90e1c05120109051e060409080c16091a060304050102210105120a080f16020a06020303180f100b040b040f15061d0d050a0804080303040b010806130b0901020702 71
    0x9502440300301424107a90f0740303509000f00c0c0c1003030300e001c030814441e0640044100d1003402600d0f0003602c0103100207801c52499030750301007a9001c160403045980014a004c16450461107491000340403044040c082000c0c2404401000d00f03143c060b0500c11440032000c541484001d606480e00919080048010041c2444803aa03c0c46000d00c1004d11811036210075140d007a40100300707140240d40c00f152550800040c2c0d80c10b40c2264100744003002110030417890f40c0f00941e4542c1001030017001580c02850b81d80c03c0084503040d422420626103409a4028800030300e0000c40001c08580518104030001880c4e60188006005802540e03150f640c130604040094088071b0441d071000d04141c007050184401d43d80d0b550360a030f600c101e042c40700100b0080154215250340c1855401152681d100d80250f454080b4183c2d120622a00141c000c0b81c1164408810031080011605085000d0800040204039038604a200c02c6e004080c400347c000c0c20b02e1501c001060040c04250151807007158010074a00c1003041d030345403071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 608425881 1250 608424631 608424637
    0x30519053a0f0b0301140411090f041101030e010c0f030f06140f0f060708120106110c01210603050c0f0d02060f0f0d0c0806150c07090e1c05 62
    0x10000900c140484419401420089034211030016040107440040d01c01c005801800054001121a5100c1829481039035080c8516442480703d03a03030120084c206401d290318181e01c2d0220b0980030751000d41c180720900940040440e40316038003d070126810301c010b8004802400b08850b4401c515800c003104001c1300c6400025500300c00207070b940c2c100024070540103403609480b114415160001c00d03e460f1083e00c1d0518104503d60000b01503d42c039030300c210074004210340354800f400c1590201d80c003164040c44042d108510b00e0040985103080c881600c890089a902c814083d0762003414040040d0482d0203022885186074410000c0702307420131020303079070381081030b224000c80d86207074420b80803840f0030301151030005a440011340c3c024010a050940da07281ca81e880c0c1d400400300c107213420800c1c060051540070501078a0804100ba9890100311b040610504c00851404400d90030744030828048203000d801d00040401c121280072201260b103040c0070001e0b50500105c0c0070b18100c19011144c0b903413852a001002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 608427131 1250 608425881 608425897
    0x305010b0d02070807020918161a070503040b04030803180c060d09020a09180501050a05010f0312050c010507050405040f0515040c0e0d08040e070918020c190606050a0512061303051905 81
    0x43c6e54549d240142c07a01219210f50041c402404902c00540d251929168050011280f04038100c038a066280d0f605a0140d13000341d031085850f13010000800418141c20071681807a18950702c01041c124030300301c001a4850288405c1c00b907107140c0c1c9010030000d6503104945000203041582c000c0100d00000c584404520b4040c14084d9101c0d0300300000b01d094400d003031181d681241c500c1084d803c126421596034044881c000100082009418055201c1c1c1010030700c16140a119640c40e200d40e00c07481c1006100a44030700c1900140c180d0b243c602001004010301c0e00c14480f0b1402190300003041e07c50f210b019501c0e030360b28008103500409008600070400555100074010768110400000965031900812a4040d015001d01c80740c0500303100c01214040c06c0c0750082c094142e4004140c9801d03610381d214210f1b440c0d0a056050f03d0042d19044200100d00700360016002610084d29003461a010710b0a02e030350b403824050002d00c2d0280c106d07c1e24800b45803042040d04ea401088041c0c200c540ca0000c00c0003001c9030800c0031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 608428381 1250 608427131 608427133
    0x822020405040606090b0a0f2606010e040c06020a02150f0409050c07060501050a240e0603100e130b01121a0f2202010210050703110a02100c0305010b0d02070807020918 74
    0x300c0d446440c04000000444808d5264242c0c0d16042082c0024068130300741d03c6940c0e445e554581c1d01901c000520065000e81034812a407030084c501818182c20300c029940c010015900f00b0f024081c0176850300c2d80003945909030300026640e00c1d50546150301461007903911a041d140e2500003440341a0034500000d080b824061402408566201c108220807000140b140707030003002c1c0788452402e000441c040254030f501ca40b81401d0000c81e01020100b1910f61040320007003040710320154140300c1c00303100540c4207400407105411501e50380b100d60f4551610741010b0040701c0c50011415141d03c200150b00781504510103591907a0302050a084076900001d0200381d40c0d03401141540c60100214441144420404540582c000e00b003c80507000208020000035081c1c0d0201500d41b0011210301d00d00000804a0741e00c142d0041103040f03500040d1400700c0314405545810503041c42d00402c00110b40001703850a1000c3c00500595855503403a04801d43d105160303000f03402014041c1006038002c0004078244000c01464 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 608429631 1250 608428381 608428391
    0x70f02040e150106080601090e0708071e020c010e04150b04080c010e0918010b0a060f12020415080703091704050f100f030b0d05070b1c0204030201082202040504060609 74
    0x806401c2d2182c11060480c0402501c030341c0104001032140941d20b820901c10b05080f9542074a40701c001d2160301040310f400000c82c0c00384050103551a07001d03450302c52030b280c00e646c04400e45055002c005c1d01c422243c0881c0d4104101c003086010b0541d40c50340a084020200144002d2403a0b07a040c000499401905c43d4100c1c60055030304a0109501802c40c480c0748034001840403499541e040b005440750300f5541401c0b0155980c501c812030042d103842201c44098862501c03980104081c0f500000c140c14140283d200c2a075005000070810844c0b1a2803840c409922414007100c540e40d0008210002c24901d400a4802c080102440816002d5940200141e42c0c0030b0700d450050414800c1406107a08500385802c00185941000d100618401d50000205a000921032148541e841d00d1315850310040b03422001400c803002588041c0ca031294000b139210581031103c250704003031654001915075400141002c04281c01d03520501c005000b801c0e04840a00e9006000300a00d08090030944010f100c940a8110414600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 608430881 1250 608429631 608429651
    0xe060106081602010203011d1306050c0903070603111204080f03010b04050117060d111201151409100911091c0203010c0e0a09020c0c0607110316060219080f070f0204 73
    0x18006c40f4182ca40c5412080c4a00650020242020703100034403585050522001340d00005000e802010f0003020303140d12480d1185c1d00362082508001d010342c031140c14985007a980b54410392101d01580c84a1451080c900060f81d964103041d010f600c124001150032034130000021445102ca64068801c0e42c1c42a07039441078400c5623803206210302031b003601c5e0298001c2e99070190000007498508291101c0601600450003001040449070a40303200b186442004007603070400340f1032389603006c10941a00b01c048a5102c441e0808031107040911141d40079000c11951120b451a1002c04100c08076000104080c0182c40941d4860074210395007403600d0000ca10a5003040c8640c01c0041c07145c0144c1560080040c030200c04189410103140c001d6000c0f90408100c0d000d821b20314403140c0c0c0d0f02009000624002c0d03000d0004c0450b140205800c009001c9803070404070003400400c0c02801e03070010312204031400603207000307a51403407038180700c0818024003042c241d110900141007c01c0008450f1030000c04c92003a58280f02401c13036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 608432131 1250 608430881 608430883
    0xf1f02040e060d0203031e0706050a0c12020901090e010806090606100e0108090a2307051005092101231006171504022a28060e060106081602 62
    0x5511031007541126501c0403441d00e02d04444200031031440142100c1c075041c40b803198200c1c602d01d1030409002c4800302280b1003090040c1805001e50004808204109410007000017400c00480c60300e400441ca81c1c00b1810251917401080303550081c091040c090310082d80d441c1441503031038070201c406030500e010b000045007460030000009030f80d01c02d41d0303118071181610f0000110b0b500e02006003d04010700ca2041d81001280600c2c50116446144905941d00c1512900840380b424005074080c6004214000c0300c03911907079105c0192040420101d61096034080d141001d0b508841c0c0482c5002295442d22040607070b16550440c1510500800e515102c9180e03031800c800000c803040500c50a404184080240154074541807030b150b5001e100052482c403080c44260215089070000c008131448100c0146502c150070300050303482c032441320500c802081d01190103030b400007200b01e0040d4405d001e014521210700070894590400342c80c03904207100f15699981d4459004001c40e10580300c4620b0854000080300ca0070344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 608433381 1250 608432131 608432137
    0x70302100605100c08160f052109100c05060f07030c140f0c030f0d0501050f091003080306041e06050910030b0105010e040b0d030e0108060a081207050a050f1f02 71
    0x1e40101540c3d01c3c0625418290b8490140306000c89240038100480504103c590f0500800c070b0303001d900d6000c009005440c0a6143c03407020043d580c510030a540c1c0301541141920100e84509900340c40015008929400560350308814060040950081d801089021030751440c42a01c60510355405004800c00e10b0016280034030b419032800209030b0b007085581c02c0d10780301200030030760825402d0440e403030a0803040c44015aa04030146090016444000400c950700d080220010b03006400c9641010350b051109045841d482c03a4032000341103410100010b1281c1d610381c0e100b0900b403001c40b0084a50701c020400c1840041c0380b5030041c948980080b03000b1030340018680e4404400d0329880820440140d00300401500e038103600d0761005600c6a1a00c0100340c0c10b444003040d00300114442d4941c40c11100320b0b00000340200c0f800410240c0a131450350388c20442c076200011720a81c403030400e210095980c01941055818035030039010142c514460640010300070725000500340b0140c15484503016443c4020342d40403003644 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 608434631 1250 608433381 608433389
    0x1b0c0201050f03100816090605060301081f0209041a0901061e0c0206040f0306021801020c0a0306091506060503070806040207200420070507081c080c040305030706020703021006 78
    0x5205100b15100041407400464100034800c900d41c4e0306658a080091a007400507290526240c00131104008098542c050000074100844041c0c1c1158103048505070744104c65180d51110242c0d0050070701007010150304842d01e42c80301800034440080340700e541810340902907074442d0194807503800010f0960b00c28410a081c00f01ca015006150350120401100c0034002040282d078090810400010504035105074030005610503031000d622140609540d4140301c0f0050011419900400c480c05981e0799141195010b40364082c00026401e002c50034640d0603442c203040b10000140c1b40110100f0400d1b0050040c601c2181150781d110120b40c0c40d0070500c000e038082c5000080c00c0c0141c2e031b0681c10200c0005408005200b4001e0400100301d1031441098000c144c40c5092407043c44000a00101802020710610028108840040c44d01e014411515007800b484502100104281d100200d52101081401c40b4019900f0500700e81d00d402c66130500c9030003036000381c5044001d88501041c92030000c51500661b4115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 608435881 1250 608434631 608434637
    0x906081603111002030423040c0c2301090215040f0f03050304060311070c23031c030216050708070f050f0904080d060e09031308031611040b0409061b0c0201 69
    0x14010b401800181e00c02d204801c0c0c01d500046c0300202e00e9098035070440400e80c00140d184a084604401800f0858641c1101042044862406a000708030603141100041e9a029154a8a4604992014014040c2801c007e5000c160080c079040380451840103081510400d8181c000602d87d03442020403d42c0a506c40141550800c0c8001c02266010380e000d0540035034041a0649403801c6642c0e10343d03840c402600100f4490304000c0200101203003800b0700783c01c0c40c2415001402800b0601800041101d1103911000c201500001d5145981c001342540130a0150b001c0121550b10f134407040042c0d01d40031140104c2810348100880045e5501c2c01e1f40e41c28108003005000140c0d04e48860311102d1641d44a203103c0010203417903640006480c0180a01e542c0300d40100300145803a00b03240c0c040c031070901083d80d000040c2ca0388107021428411203040b03025074490303038464640078144a01c0000300d0051b262400768640d0040c644044203051040682001ca000c07404001000400c1d55605800e40701702500040103400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 608437131 1250 608435881 608435903
    0x2001142a0a1509020d140a2a0306050903040b040e07021c0e011d0307030804030209130201021b011404060206102304090f080705100506090402090402010c1b0906081603 74
    0x4041c8183e8801d011080c00a0691131346010076454800182001404960701c5a11900c1c16106124a4200ba04130001c0380000150104078411135145c0e12451300e01014009990795008101c150000708102da005000203000c4680302e5039524040000a84111084409030103011601c1c7d503030314056207060107240c485844a100d602c007280c0044a05500c00b80039001404092080c02d4000e039800c20880006500c100211a42c2d1411071040c0070030110060301c0e40002400300810440140c0c0c0120300c000b6040e100e400000c0300c0d10f0484c001202c0105075100300ca40c007061300182c0450443d81c08121584a2038961300b0907610169a4030105500b0b2140300350001012100b840c40000030b290a41041c040603003d9620407168089986407861540c1c401d0350105e034150f000036402c0c01d8288150007403981c489003c40f00c00d00c4a113060340200e4050400240001d040000f00c1400c10104030001541118003078215458800298031980c404000740002d0042603c00d2254090300318004d409180008242c075071018601e24 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 608438381 1250 608437131 608437163
    0x60906180b2a03180402040815220f051507050307140c01020c0d110f0a0609050312011401090b091302070f12030f0c0302072001142a0a 60
    0x125a03040942d030080e000001c8904120420644000000d104074003030701450751042e800040c503000341c500207805406140144030811807010302003040c03121484840711400b016500d6100390444100300300803208032402014126810702c9080306c0040701c42481102104c00303071031031215010b04003241190141c000810400010b624207100c4c031480c094206401004504100f031400d00c0b1401d982003406514820343c4421010500c030303507110314140d0144034000050040300d09d51a05040d210b212a80c0040c00ca03e455240103010004100111410010f0001481601c1d5850b003a020649001011041d40090107c420105180c8025000c44001020003054160700c292020403540c065004114181d038100c10744496a0007054028900c1c4128041594001950003860003442d8200c1d030514484908261040c400400002c0f00b0030324000401c21a0928a13a142406d00e004880145c113000340e01e066140046060700c0b40884030054071564803500f000c1006503600c48490305507100121140030b01242c1e4000d00c0c3d01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 608439631 1250 608438381 608438399
    0x5030114060f060c070816050d17090d05010f0c020d180317120a090302070b0a05071b09090308190507140c0709050c0c06100f05060c070e040b0106090618 68
    0x2c403006000d042e103401c00852030101810128254041c0c1a20b400094440c01c1c107400b1020f100e8060001140c03910076100341a101c03010702d9998201020b03100c100006420b03d0f103070b90b6440100d000540c480001d004003c4411080d101410b036114005015209811103183ca0030b000310300b03c5481401040c00311090a20310380b0b07860030220b840140b40c03020001c100a01820f40d8403211b01644142000030010841d402d442c82d009103494070320b03400280c400d94244884405241d01408a0f200e0380d42240b0b55015641c03802918600075080e40d405426501d1030608003104260300803481c580b00358203030450499064844100c5d60240d07401215004001458880822403100200e005803100c0701101d8100c6820a4132203440e0012130b01e09460070740207441c0100d9014001d460420041d50700048024141e80d049242c0340510a28402e0340c0100d9100da0f00c041028000d040007084003400a000454040c02c090405040550801d60280118400960903081c080f4220707010b00084010325466248143d40d66250190307071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 608440881 1250 608439631 608439649
    0x9050901150c0f0503071211030f0f0c0f0f1b09010807170307050d1707110c0607080906031e0a0915020c010b0a170732060d0207080901090503011406 66
    0x8940000145001d840404c00810242281c0d900ca14109401d02540540c05064050f01d01800340d200e40c02008060f42c40c00030401a9028441e503402c2950b02c40724481120b07410600c0b08a20f540651184010700701020000151082c0080c4982c48850744560b0084103000a1030000d0080f48002e0348440c5003003003e000c072400301078603d94151042d03d04212096a4047c1400400720b441c40c00039410300e02e10703072001c3d443c800d000b41c1000807810003e1a5102e001c80c0a0389034000e0940c4a849000042034810610414000311006030310b0040606560340342c050314803170039000700380580c50615141c1000038008400b03d02c0f4011800d03030440024191600c15070b600c80081d511080007007500d0b54030f030b45031280c2c1c1c0d40301c000c941c00181400c0c0c0700038215400d0721024a407030f0003a03a9000c9a0030780030911140d1144940110f044507025115912451001c1c00d180106510340700343c5081e84a064400180d55045c040c7d994054428040700342e0725a04402d075078070109407ea0b000510850000a002000b040b03143c40e2000503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 608442131 1250 608440881 608440883
    0x3160e030d0c15060311100507020306012c0108010f14040506010b07170a030b13090c090f0b0a0605040608010f051806030708010915110c060a0c030b041b09050901150c 74
    0x8841c070f408085518440c00e8a0745507204851206020b101140d0320700d8600c2c8002900c0f201e52400c141408551f4000a41e100c00c10b101f01071241c0402941010749002e81414015a8801208581c2040d690ba010540c02402c071320704440310142c9410a030014491001040c1409a41c2103002415245d0030408203541980c040c1c5070882d100f144501e0545a042c03600e9028049101c460740300003c002c44658280880c1510020118120501e06070707032480059031103043c24080d111400d4000508840d08036200004000c14004070740d104081c51000201c8990140091041c0ca125a0301e500250b640c3d44c0703604460440902131207510a85c4641d6140840305c00c100703560392150b4020221703001c80e542c2d02c038101c0c210b0300c070210140d848a14000484045100d9401403c1c24450114182480c01900f0414151220744c00303090301309240c0d2610415075030340d0f101c2e401c41d0348650710040c0300300180091607808018108400c01034001051400c0d0002402c1d00e09041074034100c8080c840c044609903072080007200c42141c0044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 608443381 1250 608442131 608442143
    0x60907151209030c140105011503050406020d1107171801030b030703060617120f03130c0302060f1c111813090506040b090a0201020a2d0803160e030d0c 67
    0x74010508a400b401031980090207900c6900610303200e420003c03004c16003404112400ea040c200100003807070b00030384456110b401134900061191500d16241c4040c0c407441150000759410200b000d60b100003040014102584141c40700d01a10328540451002030150307802c424900721640c040d80310103501a421100009400070103072041103071070b81d43d0300040310899000b05070244a50040d1100e910002c210b0318101d0380d95840d0403410040c9080c115099448010881415106107034172000801c00100008000b4503401808140c5640808a9580d1241c0000b541e602d0070400034403c04510b07500c5c81c400e18642d0b02d404088103140c080216800e079411312074010040d03044925030101c0700c1c500006205404001d0711480c0646424201420010701010020f070000a140e00078480400050703800003501c003400341d44141c24042100f042c2c80f00003090304903400c6d070300480d4090b28850310400c911100210700c1102d0072a00c0b40c00040351982c0864003980c2d07118400b0340540c04603003e101546c1c065020600c0c00c51042d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 608444631 1250 608443381 608443397
    0x170105010f122103061e030206040303320a08010905100902180310140903030f04110a03080a09081902010c1106071a060901092706020c0a140c010206090715 69
    0x5880300c50b03003c2c0044282000a5a40c010a12007805034007040000b01d440150183c036801d0450300001c2a82c8554400181800782000c0c654101d100c074002e01c640b0039010742011450080c2034010b4841c059124000042c00140790800101d20b9103081c0c4581401074000680182c042ca00b4421103500030743c0180798448071554000018071040c0c1d420001c54104840ca00d00100d1a0407401d494036143c154040c00c602c140d608140100070414144d000c4003684580c208601615604101c400f06003401d070701c0c0d080a0114107000410b400c005800c41412000c45207403038102c0700c2280ca200805c40401075a0080240058424144000410811440c6030100340c00100310a00d004101d40d0f44501c2c1d00080880321001604402c00c0164a00d4101c1600340107080303082c01805111030b018143d190701001450104001c3c1551a801c07030901405505940344140302200710762204e42e69042400f800f94814a03040482e205036002500c0951000c5070769802124964001c14060b400d10340c0e40e04205030002d5403101000920 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 608445881 1250 608444631 608444663
    0x170c0703031a1c0b0a1e0903090b03041a0a290a0506120f0106020c0a0302060a090e010b042d1a070605070503191a01030207020a0e04060501170105010f12 68
    0x65030580f0700c88000c0d04a84001d4504615010161800051160030060f00e03100034980014030f0300204451b102028480010400039902d4140d90036402c0341c1004403015808002c0000700410340c06548400090b4171404400c50343c400140304140c130160343c181c2d840c0003082c9003a145d45c0c41407021150b07000200209000303001c58a8001017140c0d90031100410101c0031b802428050b402503001315040c0901070910141c01007075001c40124000900b01c0c40000d0103001c00180442d202803044411202505034030b0514011941d440c0701d0300d40342c2e4115014a0189000c00d0031071121000c03903286540720307030b003c0b2802c11010340f85498155162040040170400d10080300704030140c0010303610302c15a845075656072601d0b9240c1c200821046401c1c582100290020340c9041e0110554814544080902500910740940c0c1e520083c40401d81c402000e600540c0300700c1c15031041c401041080c0d00140c2c1a22a0707025a100030794403201c041401d070762082c0b2a544612104a4003400041c030940400c489560240501407010600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 608447131 1250 608445881 608445889
    0x16060b0301050c1209060105011b0501020c07150201061d0604020c0703060c02010510050105030403081810090b0106030b01080f0f04081606050f07020f280b0a0203010501170c0703031a 81
    0x1040f5840310f10030400180007015001d5208000b0b8101010000034034996051600107065094142810546980614443e20400800350100c90b00906171400703441400740e03541c42c81c510012921f0441f4000d542007900114070b03290009034142520141e1303144014151074032003d000003503021a46203955405040408400300d007042c01244c20b8440359074000a480c0c07030315101e24100280184c02840c10842c040041c40046540078041c560001021746250b40144840240c6601d402c05003454080708609002c4618180180d460a0342d04032a03994606011070003000340110340104040741d038180d58150480101d86170030b80701004184c0c410302c11a01c6519101300e40c43d00c0b0504c0c0e1518403003116070586445c10401401c86032030f05290040e242d40003c0000c4541d413402c1c070762118103048078001e4100c00310b440351510614441e000882c2507008010824682400d02d06080a5070007409920302080d2154004110111507000b02c80c030030070441c031409040c03003006e0b50110064085c6900700a03049112400517074107513907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 608448381 1250 608447131 608447141
    0x50a08070b04170405060a360f060c0c0e0405010605040e06040204061a27061902240c1e0a0c11060306030a02100903150e1507020316060b0301 63
    0x100503008205540342ca454150b10500c0a103034002424581480308104940720401500d449800c81e04007130720414000e4500c0204407881e40f00c01d14501c0720480c402031000104288090a1b507800c58000108192102419201c3d0060707544001c0244800369000c00489031180c8000b0707081480303174001007205581c13a000201580d0f90103809402c0c40d0420010b00c4118a8184548401440d504c1a1601032503290003040c0e00500803207089503001c1030f410701c02082d0800021000250b082c3d0041889482d18820303002e9200d510980d001900c0588152003034200b084603560b030b82c0410b42c201400303403560316a0345036800e054076004610113203401200e002d074000405480718090b1a10a540d0340ea08036180c0041e042410012000e00c13210f6008030020000d02c4041d44010850032000d54054604014400803843c045480342110380c40603003940200c0e04000000401d981043d210345445204450910198802c8025a08001e80e90328026a000300043d1800c010b1840c6100c844031700416001a000c000f42002c02c0c203640c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 608449631 1250 608448381 608448383
    0x3140a0204081510051c050d03020304052404080a020c1509100504050a2c0901140903030f010e0711070f1a030405030d0504110d1101030c030c0804020d050a0807 71
    0x64000ca400c2c0a014010400003a11030041103c008440c148841410000d007030501400303000301212000d12074600030328210031101075488000c0364200304000383c008000750025681140c00f4000c9107801d403031a4080c0c9501c039208242450640349186c58076916070071294007100d00ca0007540030700b04440030107a8811000104000806224696030310364881080048140300c10442c0500c10107000a000949030604203c00b6555070f050103004003000c10740400c0b000c0c0ba040103107820318040382003000504801074000c9000e2294003111104940c94242c0d00306e0b180c3c003080b149158488515001001a2030380c0d901a43e820250604050610031140100e480c00c04043e900030080c11801c4010802215190400d20315159100000460640c189503680580300d00c0307030a1400b00f030346444802003418030010f0700590100c0d01006200c01c801d060249412458030f40c1d900c0d00640442d00e070100140049000e4005c0e901085036a03600c02c1407070350f1a94200849407100d0502520313607100700c02d0f070303680011802c4005210349 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 608450881 1250 608449631 608449651
    0x30e03030708090d0f020304090c090512070e060d0506070c15090b1909170d1104061128080f0706060b041802040303080a091a0c0d0b0a03030e100314 66
    0x24540110803500c1d041010a10b2805c01c41052588001d0340c0e4044103071401d80e0f10718900031802810040040b541074080c0d0300015840720000e111006240301c0000c041c804c60303480007040f003940c0d079400b0200034094003031050152054202c4ca0000702c0203407142c0540364045104042d40b1141303400ca0447c40d811161120811180c560b404028081034803514002c0070b4000e00301c1d40d0300340807000c466661120780c80062640036024042c0032440e560100c140f904140a12032848021544803076031410000e01c0310880c140552514019103404000c03821036945001c41c0311000c01420b02005045035901c0c001c84e8414018001c08000c140080c10001c1d80c9801248000e1a20305840c0d0780301c170f05201ca800b07a4249020803190302c1c14410041000042c1d040000e06a0000303000500103803008407403c1c8406201005c051504a007501d09040003c400d00c810090078402c2d0203040300b000140611001e000c42c9000c075010140100f60840114580351601d0908208086038130301e00860802c0300c10141100064080da01886c40b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 608452131 1250 608450881 608450897
    0x60e1003020103050f06030a082b0207020f0d02090705180a0806190c091703070f1b080304080c090603030c16060314070818030c060f1605250201030e030307 69
    0x75581d05006240d00818503202c803c6450a14400003135031000025001030000a0100c0c49650385d080f0350f0507401d651044622614076002c000c0d419030000794807142040348103016002140c0002d088c25020b120426601070b040850740d8a80d41e1055409401480d0200b04c80c41c00110418201e84444100300014540705004000a06281003100c10204031449a40c0c1450310f049180701d2101e0344402282d00f142c0d40d41314100012176138601c800b42107120b03c0a02408141c10445610104511403154248132040300c401e95080a844045080c1c491040e84209009944840b41d000c04600c0d000300d00365000030b0000e040301d181103c0c881d1002d00306516515800b2001c42031107420414250580100c4407003200c18035030450b0615003210080c0483d80080d0020038503000111103001d001c0000c1007203c44e4203030010202c6450f4070b0100c01c00407961a0031150204640d2240000001c6980160262130ba054840a2041c1c030190261202800085154400764101510348903020301445081c27006500406040e40d445035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 608453237 1106 608452131 608452133
    0x705090601051b060709050f060d02030601180314120909070c02060c010e030405100804050a080309010b060408010e011b230910050d140114040203070201060e1003 72
    0x2103d030070031034200401000c00140c2d00e1062020755520304070103440f5414455860007c2d00d5680c0c1180090159161840e4141c001c0c3d98001c2044c50500882d40800c44280d00c1c113000c0768800e880c50b21607400810710518062010b0840400313011141c1d450403140c83c000c00e51340036005290008000019280008550314842110118800c1e54000d012510007002803135100e0340039214a6204280c085003680c5074502445203548130340c1e04000a40f501c5521500c0b0842140d03c004c02c00e440315541c0c4c000910032a074070040540044d0101200004848144031882402c40f088444800c21a80d40c000c40840301991020246000d1042001c654516081058089000340100c200035680811440e101e118040c0c0e002002e000f502d4003110f000e1200d0382c1c9240e100d014020081c003402038a02c0e883c040000d1142041c0c0c0065400c848035200004400755602007810051406444040b054010004100 = true := by decide +kernel

theorem cover : BRFrame.Cov 608273381 608453237 := by
  have h0 := BRFrame.cov_init 608273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 608273381 ≤ n) (h2 : n < 608453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
