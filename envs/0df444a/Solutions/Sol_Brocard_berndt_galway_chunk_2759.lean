-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2759
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:39:19.755615+00:00
-- url     : https://prove2.me/submissions/ac3fd9ad-5ccd-4e03-9852-f48326703504

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 496043165 ≤ n < 496223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 496044415 1250 496043165 496043179
    0x1150c050a260a020d140c070305030a0f110a02090403141821060a050c091302040609090902061204031b050f011505010c170d050f060406081207110f 66
    0x20306020382a81030305424044142104414040e06541c0b08040c8600311601c1c0059010b100b4105d800c52281e071344c1c00542005042c00700c0c43c00b0f41412a5500d003225a40080c1d440340c100003203050302103404c22075200d82c80940c2d05050703994049464420340c4554110602900690340d9034005000c1611031902c0390308640808203002d80b510b903803030061045c1c100d079a10001c2c0200d00201c0d00c22810b21500000d0074121544900910b4540c2d40c06250078060310340685106d0044106001311351265550000c01e03940203042e043c00603207980c9481c00003000d40e07982d0303445900c04610f08801d40d0056200c880440c3e91b08640480c07800c4094841c1d24040700e0002481c86408101210503d1a20400c400403c1c8030190980e000000d205019805c4c00005a621052085034003144801c46101d000684080c0d07100c1c00d65201c11f00480c14020703081704580a0b502c085643c40300e02d1707000d207007040524070b402d01c244405001c6170001002043c10341c0715188002d10030010081c140e00c0002d0500a015901c480c2900c45040c8080d14131 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 496045665 1250 496044415 496044433
    0x209012303060102070e060d060b0609090702031206060a051215040c03020c01050604021305012001060e1806010e010603090203010609090503030f1303050d0c02030c160501090501030b0901150c05 86
    0x203040c0a030000d4501d94018002c030100051405070000e0164065a0001c0a1041c03107415640c41c100204035a030505c541080c3d01b0700c450403899403220300c060700c180019001b455440154040007800450002c03c0ea0b480342c2000c1c0095a001c65012065403028991450400160386130600ea81080c0036040000d280d00504020340210041d0389500604040450b007070090005072601402c02c0282c2c0038030854600d03400c1040c1c40800c0130358820109003d890344049080d2901029500340c544c25034800350000302c4800300038010702c280f800038801a240118200340140c9810b506055100c0c04010061080004254030b540480b025943c080d0310480007400c1c280d00c100065034041c03500c140c50303820844504001c80c001d81e001600c040c40762145170100d168183c1d02c0c00c3c90320628180003002030032071200e084118071007440178518000b402c02c60030294a100c10040d40905180900041c442c1d90590003d604250500c5284100c03a1114100c80307043d180c042e01c003290061030307440080b02d46087c5098040c002d0f10030043c007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 496046915 1250 496045665 496045727
    0x1201020406140408060606071406091c08150f01170a1d06040b0403080c070b070c02040509030418090f0812061807020c09070908160f0602060103020a0306020901 71
    0x10400c41d5039548079540314450b019440800c5001d02e1103140400e4000c01d0028003949440030081c0216441070000c20f913401040490186418412140b0480c954811408000d240b5401520341c94005400c1c901070080e4506195028540301184480500454640b1103186403030380030703810600030b51a59070180841440c2c42030145000d040d0903510608901044102c1000c4540045243c610950b001618980241c5440c0d80031a400c8400402c0035940d18803c4c4120700c00200181c40c0d460040d14181c0d00d081d2800c00c0c2d070041104982c4044c01c043c016038000c0004002c04800004104003101030014002106221410100040c0716103040040000340009520720307240c0b0642c18a07078000c01040e2624001512520382c50f2165201c16240d00016034450700380480e041c5025211268032005529044030456030ba034000510f84083c111080d00e054940100070b01c000307090710070140c00419807440145915455034001c40c4071260a400040d0140e0b03000610702c1e090ba400f40e290050004000da400d03030b03c00d0b40c020300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 496048165 1250 496046915 496046917
    0x3020312010f050105040e190c1d1f050f070506100603180209010308090d140c04140403050403151b09030201020c030a0804050607110d0308091207080f1602120102 72
    0x140c42249150000490b4905285422106580042c1c40342c0e460f15081c12501081c43c140200304480c0080641112101c402e014050fa010614244c0c82d00f01d00041d4038140382081c0f4800c0101c40380281640420982d04032410480c02d0b00d0310324641400c42c0e07a907186940320103c6205805000c0c2251241e07c040c416482d512051181c00c54000c1c0d60104522025203501d8030f040f056600f4040c2d80034046c1d000610200740004000c0c0600c42006040d03020b0901c0d1a554043c0d82d1000da41540e14a13007003128000f40c241054060f01002c0b4180b4442c5d141c2d680303041d1360054010300641c040600350311aa424103810101d5640d2040042020742108546218a24880200300010302d0004074010700844528500030b050002c3c0007130400c0d034804862400c103824101440aa0740011a094481c00d6102258900e00e85a40410308a0b542c045c0e540c0310042d2070860700c21854081c0c0e255005040314000c101365030100b1805800d0b00d07400c54414904a0355040740707954007408d00c0704040c8003951100000380c00203a9548158 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 496049415 1250 496048165 496048177
    0xc3e01020d051e01060807020c060d15060503061c0c03030f020a050a0f060e0c0108160c080706150f03031202031806180f03090102033414010506040e1507050412030203 74
    0x34042e803806a81700c080c2112a0300c8103442c5040540d0080940d140c0d036180c01e401400381501c40c0c00300000c40c1502010003440c010324a61040d23005c51400018400f1505081e8079014000500b01c50040d08254a9580d10705100045d103c040c040003050804400094401d01240154940280840310707540c42e541060801150055030854681e417070315801c075501d100c0124441c2070855058485500f5aa50248007150b030505002000c4200b10b85a00158005a04440540790142c002c0c28005101500b50900900c00c44007500141d1302c0c062800001c000007544000200c1c0705c40e030140030150300c3c0d441e2103c0b07115030350045207482d0a041c00b5020410003401c2d00703c001c428007080410f0491b4078442e5803401494507440365094090050f003040200e10051410000b20103a07200c00180e030345030b18485410b200509c01d5031020080303e00c00041d1290303d40340402405540c0c0c0000c4221340c00c10440b104038403026980c03081c0607040c0c1c80e01c090000000701d1840c003540a42d0003e011101c40c0c0310940181c0e140081d00c9511003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 496050665 1250 496049415 496049461
    0x7030314091b1017040312181103030412150b0a09090b1b09012102190e06161b0503061512070b0301062d030c3e01020d05 54
    0x40ba00c40d5074646486030410082c0da48903100c2640941c15800340161000004000b0350030300181032012941d00c0440e10900601d441c044180032450081c2c4c0c0b814460800403101842d200f13a100348020700203040200c90401c50343e50320180701c1c0908200103402074040d100c1202180d80c4520312140000e840081c0f0380256425520480320b024940e5506880b41150351410307a82c10180f00c0041c41541943d500940081c510055032600c101440b1460401c207409992250b02017581c443c1c1000c1c114080075400c11481c061441c400c4a580d03041c0032520b08a400100c00704800502240000506d4015058040700540c0c0503050203001c2d10090700c0d003040c504c00540d00c1c2a14481c0520140d840581e003415010560005039808039010500c1d40e440c214040b00c6003120512481c88048034000d80f1001151032070741040d005050b0391400320301c148020401800b000202e000043c19251003401180482d41c001c18915544410302150b0300c44800b02d40413443c024040e800700c04004900d00814807580d111101060fa9103e204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 496051915 1250 496050665 496050703
    0x106171906030b220b0601031508120703121e111306030b190305060c0705120a08180a0f120c0818030106082404031710080f0d050904020703031409 65
    0x91500c451014850813405820000e508011a03a1503100741c12007104012030008095505071030f1002d0500700005082200354441c8001101010035411a43e00c220034595410100302ca4201c1c144e80000a1480c1583c980c030181c5d03a0301100310001c40d100c06807030745400600101e40d003454460078050000d00305440107900c510034004159404d41c1d1007500c03c8040d43d6000f0082c020076210083c1525050b00058000c940d0760050020001c9081c035250301801d40300314640e4480e002c07410310007080600ca5114040f450031a401c43c9803078401080c842c0e520240001e038450152151455104011a44120000c0d401400c07410000b0340c2e08110242d8245035000e121045008028030b503514051155501042a04881c001d2000b00502e5512440071401950050003800d00080c400c215040c01030044c4002c65018a00e0030b800e00c400c0c0065007041144000301c03000f000041c5580700180d5006443ca0103200c4006d8450303600064048201886a00800c5420340000d0500c1d21600300ae03100c058440c0c50b0741c00e600204c4c0c94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 496053165 1250 496051915 496051951
    0xf0114040207050c0402280e01080f0106021c030204050d030c1e0309030609060b0405040b0a0b03030901091701230717190507020a0c0f080c03060106171906030b 71
    0xa0607100b00c0d4846035003c00200f44082503e010302010b5002109104080d003803250003030802c0780d02242c080c40c202d03c180c0d5505071070424040015100d080e010704291800d02e0b9000042c0700b901d80015030080c82e039800100c0c1c00c03809090b03807204070041d01c2940c002903007020f107111054040613002500c10000b17610500400da40b0114a01d1002140441144050f0018550040400c04600168000f540c024064140031958400c01c01c0450280c5500350360480300710140c2010050183d5042c4075440302020203c0107545008004070009046580b140504d40078a04215120130301e5034000d5010424024645581c0700c54410341140032441040102c4800020925840400301403441900301180b217081d1100101e00e0359015503048400503c00204500150301c00d8403514000308a41800c00001400e203d050012803a081c100300509101c80882e0701070181e480780c1c005000300394100c02c0d207440e04006c00c0c0851a040d070b62040c4240050a00b078020304010343ca0300303001206200c034040b00c241c4034541c55400d0482e425 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 496054415 1250 496053165 496053169
    0x7060c03090b0c06061504080330070206061e090c0319050405070312020c0a090e0d080f060103090503040b0c0309040c020a11190b03010906060e060301060f0f05120f0114 75
    0x40b0810032045040d404c14800144985030113810324a00f40380010034142015122000c161460f40203140410481141b0144041941210201180401d68070a0010031700d00384544081d6451030040c01040c03058640d280344401c62814a030b4158101e11004100703044c80d050100714140c0a034400d0b1303070389245030f07428401c1811081900d000e4a406160310800601c08546552100c0700c0c40001c0b4607480c000c60142603058002c50b0f49060440e07014148490313000900840e088003440c1343c0320503200588203100016040100300300d00320940c00e03481032080c2408507450300d651030194198400d54100c000c000c20049481c1200c0c44001016065100c0f058604005038003080a0590365107848410003450003c041c5814805030030440c1d651440c1c101c0034003481c0400c41d11001c0300112508240c20440f050342d0b85400c00c11900d03600c4440320ba404842510720354a03550400710014031200c020307000310042c0075445405e00a002d10460807203032400da0324a0044c103542400c411401c0b8121080c4500710080e9540c480c840d1483c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 496055665 1250 496054415 496054417
    0x50c0a0b03010b070c090218040b0d03080117030f030403090806010e0402100f0318050604060f020405060a08041a160f020106060f11150403020604060509010501050a12021207060c03090b 82
    0x18600c210320041c1107a18000d480310f03140e405002c003111010001d41e0000340340d0350310707002038000c4109290703421840f04c415a05010481e140701661302d214051034002100841e400c444c260f41529500c0e0807400030070103400300300c40c0781d4401c3c03c64002c8154000020081815400a6054180d035005810398449076622030308130b803100c0c005a0700070b544900602c4c0d052480350300417480c0f205c00c0c1030182000f203070461a01202503200716041c001035480350410743c10802080105d11441d42152a4140110700301400d01c804580340e4055001c146050000020108080c06040c0001030002400050b0304117882c40c00c0100e07050302c0401d020310710020440c02815002e40500600408080e520030f50703101c00c42c4040081c000c5544461000d002c00050049442c505400c04001c211144214029002000c041c1010f1401800302e0750f004140b41e41c1c40c1d25040c01440700780d0320501382c50221141e024403001d01c180d8a00000e0380060694626000710b11800900044103034000000180f114002c1d141c0c2d80e9155038880100b403203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 496056915 1250 496055665 496055669
    0x103031d101709280c0b0a0c022418100807050a030c09091103070f05090108040303050601050c06100527041b0308040605030a1d0706110325050c0a 65
    0x451500140b000480465181080d4032081d204100c03141c0d040320402081ca900d1102003002ca418030808614000d110244078108003c003000785c1c500d482e001500f01c0080401c822104001d10411a01e100f01503554001e61030b4040e081e80c000940c40d5100c02558462000000300d00c41180140e585c0c110004020b4080c5042c140300e445151249860b140303031440f0441c010000c51920300e00f07010308028085000e0405200d44e10543d0f0b03809414a84e2410240d0000d08600c1c02d641400c01005030030480341010744da01029564000742d05080214194590000584041c0a90301a001040c801c0004011003040300f01d04240c1264002c2c0c40d1500c032031380b0071400d820441c650320540c1d4810258a0300418001400c800c81d040082b851700940ca80041e840343d840c8446c41e403090b4030050018030040140b11450441d44030300001d4400d5110400c00840c0690b0300c06850702242e05c10301c400d000410002c400607075002c1c4111408003010410750300d136400c9c00c40280c18a650039543c1c169514032411a10200f141031507900242 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 496058165 1250 496056915 496056917
    0x11a010e0117280203040309050a030c06200f0c01092c1f080a030807030603050c0d03180801090606150c0f0302010b040c0e03060f0c0406050906120103031d10 70
    0xb049280c10310b654800340c04043c151060ba0004101044014841411400c0003020240001340ea2420241001864803245421091080d16034203000c10024410352076001c103c602d941072090518060100da0040c00c40b6219004c500341c020101a000c000001080c100080042601c2d075031600e41e2900701e2920921001860312a01d0703102c2140440c003000c80c5000080e4480c80c01200000c000340000c01c4031130a4100e9034018400c2d64040d80c686400c060f0040441580104185010050549951103565a607108840300c68000c04c1e5003030003242450310513801509444c9580030b01100b0f05580c3c199090007805980800e0740da040c070b800008250485c1c14044102aa070003a40c83c01da040082c2d4603540f001e0403a460046056641c0c0d04119900fa1320385000d003515018482e10f03803a02d007400074005e05061503002000c04160300f4000003009100b00d600703025101690b01d18079115861380f80c3c440c0407c0d002d100b18402200c52840c6440000100340c0e000e120049024012241601104207080921906141c1e80700548 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 496059415 1250 496058165 496058177
    0x204060e04021804060803030901050903070f0f0c052101051305060c0f041d07080601030b150c10061e14010806010503090c0907030c0f020a08090118080d02011a010e01 74
    0x4034a0745015000b50071610300816066050402820005085810592218200b500040104910900d080c81226800344040001d1858101c5942d41d0498084052100601e00034449039082c05001c800040203014080107410820b10900c095504444000c80102d000895800c01c0d000581a49020a42d10700c501e40c408010a159107600301400b0750741d0008006924940001c0c00005840c039180105030f107548225645001c000d0824240c000c09012000f8a81810f050910030340340701da41c503051010b0884400900792940c075044500b034001d04110107042103074411828000003247d902202500d031010110019541d0700c00750b90b42c4034200070001400c0e00c41c501241c9114002000c5500440045500c071864201381d03200162a0360010b480c07100300b5240800029035a41062102c00d40001245a24454900040800c20b230700341d03505111441607007051810020034a0481404480803004c1c8400340402400762080d44c1084213000b0300034000007110b0b0360300c00d8031030b502072043d5402911ba814810b84103035142c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 496060665 1250 496059415 496059437
    0x308070602030601180306020d060b030906010e0a1e0b0307051005090d06181101030b03070b3103030513060806030d0309051906020301140a0e1f052110020406 70
    0x8503009420060041d4140080503619619030701007680c0d000701942c8180741c01600c4500c08100c09040718416086000741220400c01d100c00340c038000550504551060034506038079641c12318200701074000f0094a40802080321200b4007038070150740084da01428207a085441d101d03a0b038010005039100280a210210b8010044e40d84170b810400c0301c04280c20300410010895094007400410a254401e0041d2058200c482480318150f13491302401a6070041140103017031140c1030241e0800c00303224601d01507150f6001408210802401000ca40c070b2120710a02c145d0b00050b80e28100a411544a481425084001c0c000c0114082d0f015400303e1b4007030f19020f001020f8068140d04d0a40052104980a803401d00c0f0310b000301c000c00500b6500340c1d0403040c07080402503100d5140051611030600041c1240384220303070040041c003006000803103455104c80840360b99640e52003881d507c0c94140030543c01c0389410030300d04024164820b0760b404440310800b1489046684201e6241d180c0b108900550181c01d000031007811307030307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 496061915 1250 496060665 496060673
    0x1e05040b042006030403020d1101020405130b0409050102040e1509010e0c1e0307050a180b031909020414160305010b0a120f0e0f0609010605010806120a020907050d15030807 76
    0x40c82c088070240d2201500d000b4001400316002100c045005174055409004800d40c08031052903211101c400a600301030810b00004c0b900d8442c010020a803541d50032000d580e07a03550b50803104001d90408000c55495480704201058400106c0d40240c0e80401c154104005003031000c03155049510703c1005d007009890350103a0590603030007030040c5182d040d80c5d0203502840402030002540100d51544500e90f0b01c1120100160030601c0a4103047c1c0070040000302003111310807910440ba0b001c010381e40c01d030700180c2d00a85407100030281170001a4104d8135000f19074a150858164050040d034030b04181000c00341d4400e404900f0346000340035039511210203000740c8107421300070601d00a20030341c3e0100205441088591940c1201d000314000002e560042805407520a024080140c001071144002e100c194180700000e0310302d04016202900a10100051b82c5d07621000740f010001c10b99006000300402d0a0001001b01940c1004e8031a0800c0341c40c085510001c810903040b020100c4c0c1d0b0140c210342c107162032515 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 496063165 1250 496061915 496061933
    0x190611150f04021003090218010807090626030d290d02031203060f0916030c181e030b040b040506070306060206040206071a01061106010e010302130903030b0d05011e05040b04 77
    0x621002171648562180d00140d80d100307921000c9034200640040f241d072502d19003920740b50895020b02d0015150280901100e10803002500050602124003c201b001c02d044141c503501c22440002c002515102540d010030b440c0444203c00c0d00c0c0310b01040204510a1010840c1c10740c031050300294194803c03d81c620480c0d890001441e88a03900520001d810765014001c5815400d04480700802a01010b0514020940600c1811820405864035486003940d111229084515900034021002d007034285049a01c240725101c00051030b440301a142c200d04191030000b500321030a407011200390140500040c0b5040c40b91084030200d81ca20390080540303484a03001e1083d213a01c02c02041c0d03507444000c071004ac2d03400e6139240003900070203141e030340c6100e10922080d080d8100201030308250050010a0010409aa2480c103000710200000d440069500700e24682580144004092241c0002146ca20b100c2800410340c45510403019070313907250314028021040d0f0b008450084030300800407180c0c40041401325441d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 496064415 1250 496063165 496063189
    0x40b060d05040c120507031704050d1b03081902070501020d120905070302060c160e04020f040c180b070611160b090c0402161a04051b190611150f0402 66
    0x1c043d4034041340c803280c90156140c01c001017681c1d40c2d44152410804c22102d90004a075220180c000d1743d00b003a003020300047d00b0b030750340701c07006400c51038002100190219950100c0008542c0101c0d001d42d543c400121520200d010b4158903009805050000611540041800b1003c4181540c0da04c6146150500354401814500d0050300c031442458000710050f110a001861480c03906001004501007035108071915001c00e8101700840b828a00c00d120050311102c54080c035901080318017045003045c0300001c1f42c1855401c40c4000b004c40a401d00069103220000003000283d0058000380300a078060503d8081e9403044022070082d81158900c42004101c0b02c80030150040e81000a90b142400e0b4100003c0c20f90308411101c40410707500040080030410131030345081c040020141030000c1440c0580f150b5440790380d001c0c0b4901030b20140c004840220f82c0e4085407040701540c80a20400c02648540e0000e1005110300b28441c00e910403130054108440307415000910410840140b0115035466600748480b0300640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 496065665 1250 496064415 496064423
    0x1c05010513061401180e0717130503030610020a0b16020114090705060906040305060103031e020604240e070e0108060705070f020d02060409020309011406060f03061e0907020d0e040b060d0504 84
    0xe030100d0340004000c0b1b0340340200c0c2c4030b68480c410304c08001718030004583d01404c41095030340d00c0b201c02d50004a01000340e81c1c0c03200c2d0403500c1c1201d0441c8408168100414240002d0500b402c00d010040480c00456800c07004120b968020080d47e55840305961110406980e80e4819901424003000180b60110060410f07400151415042541d643e5030a4540907082c0c20450100e07a4000100240384118621480381e21103600c000c0c4524242915150020f00040701d80d000d00000c60b00c040e400c1c140da15044840b0000a00b03084550f451348c2c48001030844c940030300484196008840109038018441c009444806400c45081d0140603419800c11103010350300c400403a08402c080c03000051030a03451002d98881c10443c00046404030941001c403e0175607004009900c100b106100c200c0c42c0380840002d5075882101a100003128158801c8135040000705481a44d82c8040e440702000400b99010803164011440794a5108080380c1c84400c20042c1e07004407000d50781048040c01007108145194110f90340060003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 496066915 1250 496065665 496065707
    0xb0403030e07170118020108060f1903061b090b2209051602060a020a170c0f030c0403030315151b1509030801090506030d0507081c05010513061401 65
    0x1d02005030b8100b08a9034032912001945180d51810300d4000e01401200c8408401180031240d1154000792000c1c001420340c50040000065038071003038540400380c0c3c075280c03c51030305210425070303a26004000d8400d0b03803090300c0119a42941011400e00420150082c3d5124402c030504207400f800700c1504040c900d8801e4121412855400610b150152082c00c0c0912a89400c0481003410807602034a00400500b01300543c6104010211441d540304c440202c00c111107004080e09610390541042840c0250007003403054403000410b100899040c1c10041007200d2003514203005550175401400101401480b0b0305074a01c403100004900c461044e816100080d1001c01c10700100c1607191121a14246102444200c0d955156414030a25401c0a2418011300c2d41c490140914034125010a40340c520502000051080c0810900c003003080003400d880f006100c1402c00e0500d04030700c05030140900b5003842180e000380d5015410050408507070250506460990742c0c41e014400f030740c600440342224825040401100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 496068165 1250 496066915 496066931
    0x61101021207090e0912030105130b310204050d03030b030114070f090503060c12040317040b0103060e0109122307111002240406020f03190e070e040b040303 69
    0x144100401d0140b0071603600e4841d80d50400400c421524406003030034405503c150504400025210f0440c8e056840a50300b80860710440c40304c100c040c0032160411075121400080c2201030b410040c3c1882c2188040b4100d904100035810003ca00700d100e40d015840d0040103007428007010a000350843d440ca1380d03002e0000141c01b25545940241c4100969841001404000e007040045601c8181d00010b420102c018203405d0500c001f80380d0b00d0380707c0c0c298000c001d1400040040e06250082106082002006a084a4600d0103240643d40c000c1c0074002218201c0c5030111107500c14005200d80f444071540031200741c000b691202c2050722544100325034202910010107981850000c1c49000d0490944908803281c00da03101541001100168451080c0855000b01d0960b0444400654002c244002c24030f000401600c950070440007038414140c1c003480528000051040721464005900c0961000c000100410700d17100c0b000a850b45550700c50707291000b91798000310380410b50050307015402911a041c00603a4103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 496069415 1250 496068165 496068187
    0x6070521090124080307020d030219030207052b0212010e031b120304020a030b130807050f0c150901031a04060f080f011b0318080f09130203010501050406110102 71
    0x208101d03441c2400c0d944466141c0c01d0031030011044548544001000410f07282001c0351540d881c010410082d03c6941011036503414103000344890340340b491000c5900001031500d030070701075581c43d0b407882901d024510f030179001c9103044150f0b0f6051502941009006100c440540c00b04514910400c003488401d5584516041148508000030700c8281c8103d00d00d000c4440341c103181c203402c040058030140c11508042080100607034074a0b00d001c058a030b201c00c0c200e24603240c408c4210000e110a003001007a4000026030102031110001d5101e0008172150121800340c0c3c803000034480c1e12309084500701488101401540b280d0740c0203070032105243e55a1a00c44d0802402000028165091079000c02030411804006028502e0248980e01030b54607100000d12480412810200b03051800001e01401c1640e55043d0001405803107800f0402560040421511001d51800d854100c0e0f0081c0050751042d00031881e442040d000034001c0d60f04032032050f100c40c0e080c0f904d03140c03060359062030680d0703114415503080103241011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 496070665 1250 496069415 496069477
    0x9050f04020a0908190606080703121115010f03151e0b0301090606030c0503071509050d0312052701060b0406141204110f18010303111f09120c05060705 67
    0x7400d240d600317003002e8843c0d040c100c04546294000c100700b40c100c0c05003800800e9010400110110b960b103030084101c502c8410003030511134440e440030030f428140000002c03216079243c090340a4030b0080701c0d0601c1c00092492170000300c4181310078540c2844041901e00b1030a80380c0740c1c4451120000030b40007040c510541d507614012500f041d00119040500300d0400d211900782004414060f0069000c50000800c030075030007a281d95014403c2500c074040e440c0b084010544601c03891035208a02e4a800d001a007030a81500428007024105403111401c400781c09002003405000c0c040072101c000c3e000d9841c0c981010000c4580140da600d0503036985a00300400f1590010317040180b403240d80966040c1030144203040070041092204100544500c40c41e00407020700b000103070745650449070702d8103004000c00c10340d40026050204a0441010039000032800e122203503600d4019034030251250b40094400b003152401a1900f9808503809405540038000140c00c4c0d5004200508405241c0282c010600b01004820201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 496071915 1250 496070665 496070683
    0x1505220c09060b16080708070206031003050d0203090a0e07020c13050405010b0f03030d0903020f0102041d070201200306060421031403131e0f1a010609050f04020a0908 74
    0x4221100c80e420081c165241c400c041c080c280b10080c0340c1c54007407a041070001d500c2500f10040c0102a00150b441d04110480702100e0359190301400d02501c034540000c0804054000c2c0c8030030307205401440c012140c5588080100e50396030a0083c8000081824564a1480710000821000543c4148080075281c0d680340b86410300380005984010585140902d800f9081d19144034190740665060b0400102176074010060350ba0011020f6000031b036600c1c0d141412441d0041d6807421301180d500c00100030401e58030b0700c0c6201540c1c15000b14004035684030a00b040b4221080500c0003002c0465038500098051000380045400031401400c81e42032544540020300340d00b076040c82144e04a0000f1401c8020550400003d0030354168101341582189805d5005100c8503101300b900410f0b1007103400390382140100c11002c440c0010381100146d040c081d11380c0740104070301d0a00041c040d011403081c400025594402c850843c10f07a5000313094060000b030400284070294200c42000414400341d1348000c00c00203010080809 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 496073165 1250 496071915 496071923
    0x31b070506160c1703190e010f1803090501080c0705030d020c1c1b0c1502030703120506011b060f0c02100b0409080a051b060708071b150522 62
    0x704505142005004030011030240302d042c0b15034032142d08007055003407201d41d000340d600030202a56540c4076510281b6a58501c1d610100d0741e450078600030b10070041580503903498000900204007001d401100284c40441c040c0300200090401c201c28803a551040e80c07440e0b0460803040c2100e003821626074032a803c41d084a000c03d801c540d4045940070300010108240c202c038602d0f06000624685150000804c100190b82c81000701503e000c5a8030100400390305564014140181c0d03800183c24180c800035181e0f4803140095000030340065940012000e58446d085c0102c405071500700c203141000c0244640ea1003856000d48900b070340c82a4030200d207d4035001e04861521031b42d020b071440d00120341d40101210300c840c490b18081c0e0318003070345800012841000c0f64041d5150341001c6071181445a50a1900c00c1d01c103800090070300524081c1300079640c21a18007405509030ba241d817001c250742c2c1c01c6e80381d209012840f0058a03898100e011044181c40300d6101c15005030a40200c1c0701c244415085016001903d61402c40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 496074415 1250 496073165 496073173
    0x80105070804020a0b0c100e030f07080406030605011803030c02060705010504030e0a08070b2a030c0a02090a090503031501260402100e10140427060503120f031b0705 73
    0x45240030707180c2802a003100c50209050500c1410b102e966087d100013401011951841920102d4404005480700c454000002994803000c078030300b083d007540003403040b00007090505030040740702d40c05401c48402c0d00d9503031101030521501d9a10112819203e052b01a600901e04001c0640400d9003130003114425030080e124035038084510700030f00030b601482ea4005800da40040d80e051001d9074281044480000d03c0c1c1181090740c2c081c0c440b040c18171524151898003140301c00a031343c401040c0c0214050194500846200501d60b440c00c02120079110380c1580140560020000a10341c801c0550780b28850503410b240010056401c46400e021204040103460192460749081108510301003000f039602410318500124401d0981740030071420408481158180f00c000c0c402d403050405910107036030080c0b855900d02d202850784403d1244402810100300c820460820002042c681000161248003c1201a070f042c68161500292117682e040a0b00c1c0c20f0000c00703d058102c1030341d80030310090080c060040000d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 496075665 1250 496074415 496074421
    0x151c0612110306090a030e0a0f080615060909010308071104020f0417010903080615071203090201020d080c18041107060e06010821030a0e07260619020f040801050708 73
    0x280c840307444520001072080c1e000204003c4002c0c0c0104211142d0369040c241481c010601c94006584240c1030303000f115102c00d00410002d0b000c44001031080c004d62808000c1010000740c482804070901c04c070000150040c041368010000200d00c50001c00b00b10340110b00e40c5075070242000001e010f90f0f20442c0480008040071a05001c031400e9200c0548078092901e0082041e00700c2c80e9070150042d0b4000b0304180c4103135400000d904560303900c0c0c02215507050344011a50010030701e560b03025004200c1c0c400260300621440c003140d01e107240104e058600881e00b88103008d041014222550040740034683c4510380090f182d881000300400b034a8060a8840d2049501140803410a1101792034090140d20081c042d500110001c0030902c0d140450085d400d074080704107662a520500c121700603100c003140c00c0070144507100c0001030340c1401020b007030003020b0b2903d1001c0315910464940b40e5243d4040c2c6410321300b1900e0b40190200e034010b0f58014101040d2040c020340c1402c1c0c1c0d40101908660048400b040071038429010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 496076915 1250 496075665 496075673
    0xe0a0b061603030b1906021506012309030106031a041106040b030601080402010c0b0906160e06090d0302281e0305030402040c0306052e03060302151c0612 68
    0x4102150405558140c2001070701841c003024668a26009024140d0310b09401080e6111240198512050322a5040f1201d60340d900007940c60030441107d03200340c000303e0081080c641c03149801c0c1e070311801040d01d400c1c030070300c0c05800b80845a0300c402080c40d415981c441000000400d03541103000d04032900c104c03400d0689001c0c01d00c0a448001c070081c1e540700c2e540c20801408482c03a1901542d801941c20700c2c100c02e01c1d64803803006990000d1680c0f4040e007411006001c02131104070020b00c05204040840c01150380d07040569081d03443d015030781c1c00c1c40e40c0040144542c01840c2443c1050304800f50082c4111003800e03440382d460101c0075056a50000f03d01440034500024000388074030040c400d0044010741596140d05881c002c00500015200a120300e032a07222452040d0b2081c1c100c18083c0c10010040056440c0510500016843c04074040b09020041104d85035001d000348100c0044a401401c414010522010912420740c0115109001d483e040381014100c08403520641c0e014040d012442008000a410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 496078165 1250 496076915 496076921
    0x4b180b03010506030a030f12090f21020606010906080903040e1305070f050a050402070203010b09090f0106090504020d0f2d0b060a03030e540108030406050309160e0a 73
    0x1c0c141c004e601c54240d04000039441f885e840c0ea1550702c0e00d01400d14804a01058000c0e0440f4071000d00302d0003040d8820418440700c0082c0c000c03200c01144031a03d03c00e8101d0416a190401154083d01144880004201c0c0901540318194008c0506050f2483c0a4981c00e606c0c680320425114410509000d2640d501000401c11000015110f0349203101c04807842c01d00084c0c108442802640d02454000c1005800c5460035001a40c200c18018204282880e00ba01086e90300c1c080c0000d0b00641e036003054400101e201484c4100b074011500a096003503a40031584950304540e12500085a842c004000b201414000c070892442c1915508440c000d95256241042c0d0400c40780900381c1449101300b0072003000000c3d0415800c1c01c0008003500e4401c2d4450005804110701086104009020307030054045000700d6010300080042c00c0660640c042900040d1010035005180901501d80309038000c000134810f40b03000c0c0b0003855001280b84c0c2100c0b15004542c015200c0400301380d0080040d41142c0051101100141c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 496079415 1250 496078165 496078171
    0x90106030c09080105040c0510051204050607031d0c060708160b0103030909050f060f0607020402030c04030b10062106260c2704051204030503044b180b030105 70
    0x1c4001c5c0300a00302a22444000c18052041b548612035900b403a40034540518144c81c01000c10f400c50700000c1c5000c0c2461a1034440880305640040d107000301c983c2260800d00c646921302e22840c0001c20040d019603060000e240d002c0d0304160303880302052000d0f824924044008200886c07003940401e0041d4518036018029074650b4020360b212504110802c020303c8200007000e6030041c01150640c1070803004001041d0b140c442c800d0040d401134000020041d441c0440c1d0010011a44140040003072650b4065400d50f00c22000c0c0a2100040ca000403101000c10396044100c0c0500014680061103590305d030b614521500780c444500e440c2c60703014507201000a10070b0120204900041e680f240200000001800b012840b460202005401c13a402140c148074040007286088403a042905070358584900b8015541d410521409100c040c5030058600140001d4800b60010100c08078600308207075070103c0035207544503000d6070b11200040d42c010002e0000041103100c0e4110400d180c00080c911090b101781400d4460003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 496080665 1250 496079415 496079429
    0x181403180d02030c0112020f0c06090c041806020309072c01060807050409090519030210150308030a090212010c03062414180a0b0a301a090106030c09 66
    0x1a81c0000c0160314040f400300c200e09024608004542d1528241900038000c0640c404a0660b0102d40603e84e80380000d80d0038040c41c19207040f50f98548103c0700300030586a614000e4140c10041190980004d80b0580181d03411010040969034072a0700e4410341202c82c0940ca03824515184908030b000c840d034514500440c090005450021218a003454002d09140f04510880d410300d0750320001c22044c0b10062001074002c11410340110480340007420020360f1040c0b0302c0d281c901d04d2490300c1d40054200b01c0c0252081c04999001380480d04694508107074400401046e1340690704060680f00c80c0582030740038800c4140c12003094a00141050074850003a80e03118080c14582c80c50140d81160201041d00300010302c58405074414030f10340d1200349004182d81c8802038405a80c00c001d201e1001316020b108140941b15000c1a070b0b03549180c3c903d401002c0720101d005029184102044c045c084080040c2c19005184101c41d0642e0324020000400c2c081110100241e1250740041d170f50b4095846004d134441c000d1801004a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 496081915 1250 496080665 496080679
    0xa081905070f1e3e060f0f090706030e01091b0807050d05030d0902031603050604121d0928020d060e100e060f041d0c060f040918140318 60
    0x1500c0010305010100c9030740e240008600400000340456045400c3c200035070604820924520310000b1340d66690003600c03400740d81500980065201440c0700c0400348551000001010b62a280c04010760040104910280581d501c4241c00808103030610b1405450000c1044d0181d98140307031051550400115404c030b2072046a12010910105a0004c10b50b01c40030b0101800088054440c07001900e807407803510f00f00c4805c81c1c101c0c500100744013000c03c10501c2030780662060030094010410480750359440342030580c50b0303c0100c11114164141544101e1380701c9208103103610f6415104010150f2400201c40840000307400052002071052070307024400c00ad044c0286003016505010ba40ca41203010140100c43c201e055400020f070150366449602e4200800c0a44100070501210040405070106211890030343e1054070704915460804104a5420b0b80092841505050902c9200c0001c0d000c595000c00203490203100070804206021000903102007400001d540d9540c2005518103082c010740c4029102e052 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 496083165 1250 496081915 496081967
    0xa0e010e04180b0a0b090a150905010b190504090213080708030a051603030b1201050604060605030c18030a02100207060801050a03120e040e0f010617060c0a081905070f 74
    0x282e10114602216848400403030f060360b64809410003026042010303640807000500380110144140d1280241202e001440c1d004107071240880d000f91002841610380c130031000c025000080b5000c138002d6a20840381e285c041d00d4181d0b61000001070303811400481881d03680da1181007101000400c15817000780031890140d4201070300d915003c1c00c0c500440c9134502060300705c045500708040c0b02e41d03c00e10b038400d801016503400c1d2074a03501c11802404103c40c0180214580f42020540c107004100b44c0e441680c941d4100340c5081043c0460201c01c00c007030002d041c3c0620031007a0101c0181c0c2d031588003608481c0583d0040203403910b4100c00510202041e400580181e140030030601c0810407044017416200d21038202801a003100d0700210f40240058400b81003d8001c2c05e00408218206400c92812246420304002012280000350f58807003070305a0320f05030700b030404101c0d08103e14050440c280c1d02007801260301c81c0003246030980b401990411190300c030000c0c040c1b41c08460010382018511244102604615800708 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 496084415 1250 496083165 496083191
    0x715090518010b0403080703020c09070c021309204e21070f060c020c03061608070908010903080f01061112090609030a0b07021507021f0608030a0e010e04 68
    0x81300e540400340805400007101d101b070500030082c011200c100580004246d00d002d00006058000c403003003c038810800101c5001c4000c1c003601031032803510381084962461481154050a900011420b070396040300b2a041d40312030050301030000c400100b021000103182d5003064000804a5403070480d850464252015140c0b100141c002406103151003c1c0841511102d1b41844c001301038002c0d41c0005001800e080405800c00400713411014031031100381c080b41c55080c1702004244d12910202c1d07008510031a00c3d07403c8003400780700d0380312290002d0007424041802a2503034089030940b189920150042445241030025006c2d1450383d0358010300d070394075084012909c04400a41ca400c00000c0c01c808154001c6000e41069856504031080703541c3c02811240c3e52900703803900b8049100100c5209025004407604c0c60300f00c040c1082d00303d110342565800390108024000c0c0883e00c400340d80405a50f0345a40303020105ea0041c00704024414540e050300d600105100600006100b5105101c8545c0207905144d0b00030044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 496085665 1250 496084415 496084417
    0xc0c030a0507060804030e030f0d0201060503010b090a0f02250506180d08100510110c0f030d050c0c060d0905250504023103110603010501051602030715090518010b 72
    0x180740c80345010904c6481d10b0500311009081c5a926a906000300c0c0b616030417412002a1001061503550000e0020303581c4c0c1c03400c0508949040348183d8100740001c0000b08400b04940c047d468001d0b840300014100000d620601614118510301d00c0d041d224000b030003800b401410460688c0c031140300c0002d0034050004000003034030342a800c09880144810180400c03080008441500c0240c0320280c1000080ca01c43c600051280940841c144082d004d1104081d006040140700d0000758800500181400c0701d080008984550003a400365001c0d001c2c03402c0d612403594800d0b004140c1403407210320101315a000ca0421904024015480d408070b00702251101c510740380c0c1341c1c1c001812154201d03001a202d03518180d4030070807542c81241350040003030000c15002c4112031106001083c1ca020309202c1ea58103480c0030030701001e84001e0040c0c5000c10b40a000b00c03111000070300e401c2031701c2510150649040d5541c800401184203410038005020400818041c402418a0401425004029107003150554900001da102c0c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 496086915 1250 496085665 496085669
    0x6091a09190809030c12031b0706020715030204030605010b280f0f0e0301020a080f160c02040203060402091509010e01031407200601090c120213051905150c0c030a0507 74
    0x309202162103072a84d50148012650081c002d00300e05a03002ca43c074410360301c82e48089035007007001c80880c110441c0e4010019803601a150281c005200f1a818001002c94400c415104e83d820582c0070003011001544a00030b0344e0080054200003034551052008803070391003400840c05202070104240188030390780d0081c0c04144100040c100070002940918040318a100a40c52454040d1b000044541c00ca550004180348105144841c02d400c40c0c480e20001d58410400c03004e500e0002c2d480c0c202900c00b51500d5030045070450700c0103200514007010000841c030203680342e41c00c0d0071140c40049030021142d43c02c001c466080c5c0000746020043c18840c807198085003070300949110100720a0710070710740c11f0700000040c0c20104d005000440e040e81da941c000c6000a4420070b46a20002400041040200c02c4035000384c030041c8100b0501c485d04582040140304a20444451b10000766400f07210001d520b40700c141124031507032210001c03d07a44420480d01c0c01d00c1d1180b590f0340d480c0a42e114568080214201083d4802 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 496088165 1250 496086915 496086923
    0x10903020909010e01110a0809030a08010b0a0903020316140a0f0909050a0803040c03021918110d0603080702091f12020123090310020f2506091a0919 66
    0x1020b5180c011030355004190039030102503150300c0c106560010340c0302c00b8007400d0385003002d680d00042c036030328211040e46a0213049807100100c2c0b011001840400013540292070064520301c1c04a0b8000d40d282c00091500d0001d841401501800001c1800078000c4852602c021150540356862880d2a1041043c40c90060b84910b11400360f40300f0300700041117018030440100d190003018290f100d040900308070400c8a0f031880102c0c40b0f030141300004107111441c98003010845089962000004d1001c07091117016040c0841140c09015042128109209041c8a001c0c01303180180100d6407565014418403107210300c080c0c00c0010944405003008403000040100c9000c1c2c400c000b8039400241c0e06803006980d903841f0504080a0b034102a0244015240c0701c40141040b14411001c54220f4030060403503008a108161801e000e544c010405550801e44840254030402c502c452003102d0151141c8851044510b14901114400b4101d10150a0140d80081d22508404c596000d00605451080070354103865031048018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 496089415 1250 496088165 496088179
    0x50d0b09010b06070c18090807030804030c0813140609030703122616030932010507110d02030c0304030201140d0606020d0207061b02210f03040e0a0b01090302 70
    0x180c9000007904450000781002d80f40644030303500c600d85411009100d01403081c00c00d20321009074030000440d0061030065038010313410f140303030081a88040f650024010020380c1800b900d010b0b107400040880008101c51030800031042c66140c28180c030082c1c007100441d0024484c8005100d00d15480c0c1c5c011882000312540014a03951000c3c12103015106102e4140da03450a600d011004030000821482c4014802d481c000d090805001b09150194111165a540a40140544690710016645080070200c205100035299040d030980707106060301750b440440d40c920000c3c441070715001c1440c504125072080a0700703a0000e94284001a12800d58900a91002904000601c220182050b0701d010498200380b5600d80281705581c2c5500c40a5510700d18010500c00611a14034001903951051008000d007040d2407802a484a4aa400301300794910301d1504a1446c1c4000000d000310b0110400180800058103030296841e41e10348151b400442e60001c28030740c40c0c1230408031610040c0ea0320030380e0942500ea04803449 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 496090665 1250 496089415 496089421
    0x90f060109030c0b0307030f05040f080306010309020d060e0624061605030703030b1e031f1404050a0c0609080d140f040b0904050c190c17030a02030711010501050d0b 73
    0x100d403140e107150310260100390314190206880b44000021481070595881c00d21648036018036802c11540c00b01e801404103030401e004640001c003500011038120030141340c0418101250340000e82c130f155940408070b036040e50740c840c0b402000c0018084140e00c40484502d102d84184548115482c9003980b021581c811000024101202c213207010140c0c282d50b401200700d13600d0b20002e00e00a00100080c0f0720284c0302d00024031070b0344900f07041282d80c0790b807010010780502850020440c01c5005a0030028500c04241c1c3c4070143c40c410303254440c2066118a006000400240d001424201524262a080041001034160003070100410019031511824410702c0c01401ca03003101614074680d401007041151214a0008000444424000c060b082125003100c0070401c607102c4140481c103510070561000390a003012410300301c03c0340c017031655030f58030310300172042c170300c400d002c3d0700c1a240080e401124808083c0f640801407200c8181d101c0295801500c01e54020410b6505010004d5186801d40300001c1c95000ba074000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 496091915 1250 496090665 496090667
    0x2d03070506210c13080607030f0621150c0c11060703080114031606050711040e120d020d1407081602120a1209080702030d02010915020a02210310060e090f0601 70
    0x1250000e88030800103142440e00c80b00182d032106d40960b02100000d0409405081007a103910441c02100d56503000e5104401c0c0891094151494041c010340f1170601c5040401d00d0500c06000d112032031080c1e9a10b40301d10b000146030440843c2d54040b48240102c0b4103100c2200041d42041c4c2550560310b039200c2d100580440c100001c0e03d041c0851100e0082e0815a10300080c2594016000d030120342e00c075070030341042c0d060b402c1c1c03c2c4000c564000d03043c504c040d40309030010311007a89840c00600c841400408050725050949120205440401c041c2d0f60720350380c0980c100316105600c0503041da0020050001d00283e2181c2000082d914008004071000c424030019146050b24040c840c0c0040703c00000c0000d001182080c10b210302c190f00b014000368001c0c0240c035030041c0b1462040c450080043c2d406145004001c0081c14201d000350000c42e03c9030154883c0c16510b0000b1260041080110062507406507900c0c80c0c0f05160035020584c0c0d510207410711420480200c1c040d512246215400684081c12a6480c0d0310180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 496093165 1250 496091915 496091917
    0x803010b090d1407210503091207170604030e040506240c01060b0c0f0622033617031b01110f1306090303021504022d03070506210c 58
    0x400814080c0740c0406040304001c085110001c4800c8490900e40c41c000007103181c509900e5264000300190001c00c4010039518006e403414100138408400c54a4ac10f0315818041c02e03a0036001e10070889a804002000308055000c10b000002c2c5100356018010760800c1030206076114090881c0040220a0381c210003400c000d01d1082c0c58204800600900c59a555011411007d5005102107480c0d401449811000202c002a406003d990100e0028000b09510070368518804501003044003049031064060b0006180c041e103400c60011003a02810b00c8401002c090311900a0380e81c040d05140501401603ca0340d403022090f1004410000400c0b40d800c0400164a80100740c0540d1500c1d002e6001304900d512015036001406140d541e10700d000120307a0f118841a140c2d02200c0c40010010382c0a0001541c807000c690381e03e0754003c1d1000d4001212072000d00d0519400320260410707540008141000018580f500f0403041006050980d400c624101540441d1850740207050308030720381243302002060101c254a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 496094415 1250 496093165 496093189
    0x5120414240703050a020f120105130b03211911010c080601020c1c060e0607030b03010b0a03020d0c0803310b04121104020307080604050603060106020616120f05041e0803010b09 78
    0x21b200705940d488002d03502e923080c1d0000c0c05054015002c0300c00c020f190600600c2508240c1030f004004010701a1290032250000c400d01040441c40d400c1031104c0481d0b02c510580e14145998542c51313081c588541c9108150850f0f81070450356082001c2c5a06024050341c001c900000380200c02e4458117003100607103d4206400c8003525000340014684001400c0414002c0303469402881107a0b4203000c805003010405003601d00d0400402c0d80010309101c20401442c0843c0030b6031120340320703036040325109a0324140d07103047d0781103c40d001003140c800502058510803141321580d019a0840c225034182820164a03007039601550203140d00c04400c3d55049000e003c0d0003108a503e104004006541e0f1b454540310050031101c00ba034041e40210b08200104115103070200c4c4c00d90582d16168014400795070f0317080140540d209145071401c10b008402d042e4261000c200d022f010701d0784088540104050502d0310307115622141c0380440001407010740c1103500003c1c1d800c0085070704450f00780204984441c0c0e0400015188030341c1c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 496095665 1250 496094415 496094437
    0x191a0703050709151b030305040201110604030f0c031106040b1e010b03010b0a1101110409050108030a1403151c03021501080a0305030402060912010906060b0a020303061005120414240703050a02 85
    0x4440c17036400b0968960400352180b403007a0ba488040840c00000750b56203070000d0f54024040380c1a540042405441492400452402441c28a40b0504444030060515405030360a40b072900e28001044060007502d05040c82c1508044001803c03503141c40702d6584640418050120342e00d00000d440100c580c400c02c034200d404d020080c000c0110b4140300c41404196842481031030056400c2000001c2c02e4a808010388140050b01e48854400824844d039007201070740010301501d03028601411441554540080601024844003441c01000d078850901034502400c00d919049241000e0b00180300a22002c29200318086e0302d814180c0c6c0700c1d00c40c0d100080381c1e8010702000542004004100b0b0f10110015006602c032103009002c100700550b11510611307a40e2040c0240680540d0042010884909082013801b400d488185806400e04d130141c560340c41b9841082c0d83c2510f2212000b030345003a02c0a81800303003001c0d240c900b040f82210741d510250000d80c9400010503000a0543c0c800c000703074601500e42c040390045200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 496096915 1250 496095665 496095707
    0xa050f0109020f060405010c17040f090221040f031206050d0305071a01050d1e0506040503070b0f06100302090a08030406090e06180c0309191a070305070915 69
    0x5165402402810141401e92003a0220020042981081011141982c0040c0d6804681c402561114070034006c218a800c80d0810080200007540c50f80c2c000000003070700200c840503994820f070402429a1030b0380200f41e61450380100042c080001d0072031044001c51549414000f00d901181011480100740e29405075400220303140042e41050762200003881c02e188544142c14258044e26120b4059540902845400480103c2000302240c50001111501d1030099520444404c1c155510f6041000030b6400302c0380c540c004140c4000b0040c448940d164030001040040031685441c00004803050316800c4400b0615a0005060b05e454848031400f20150800000b100d80d155590380d4028851b0714070348200101642031300c022400c07030300d0300c400342072904c102078901503030962211406901170303a0018015151502c03c1542c210120481050100d0455000e06803140c21041c1d46d954a100041000700040e040515010400241c1c039007100342c48090315000c2004001e0070303500c0401a0364403191103640e1018060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 496098165 1250 496096915 496096933
    0x30a1407030609030908060a0b060a14090a0f180504020d02100e0d030801080f0303010f05010509240a03060801090308041115030103151b051e040b0a110d0f0c0b0601020a05 76
    0xd04642c0180c206c3e8020411a280c503500c0200ea10110f407103540d01107138000010450b20024501c070381d07502040e524403980898501401d203000203642d2880d070341c856500e54031020740401902c0c0619840c0282c0251547c0c080c40076150650000384440540300000741705000f02840c05a001e40315240b01540088050060354007420781d07040c060a00c0717500b44180182e52107014500200406d022056070304071030215400040d6103003084015105504444020768000204080500b411910303980d8104c4d1010400741c407195120704119004056511903001920280e0400807090000303903101080c0c0d0b50003600550000c0d10405039500117000b1006020500410405c04030000c01031000e01c03030b40d83c1c0c0080034030041007181d024038004000485107803800e40804941e0920200400e0022002e0303150b0710b00201c8002c50301d0261600c00c2c01c0c10710b8104690010005142d0f0031500c4c9221010810720344180010300344a680441032910003020603040f440014661007410000c0f400b9079000300b0408103001c1d480800e43d00004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 496099415 1250 496098165 496098167
    0x1503050d031508010b030304090c03150b090301231311031605091005090109020d060902040801050702010f151202061204120806010309110405100506131a09030a140703060903 77
    0xc202c886542022840380000082e02010500c100240078801801840c1414030f0100904001c004c4408000305046e1140f6076a072980c0b0140e0b0035040980040f0540b00d880f14881c4050600319080c4032111804015901e000001c0e46074204600c0d5440020b071000d50203039110307900d08041c21054050301e054040c40b91307800008210f28000c880ea415100e0559582c1c0c0d9aa42e012600d10301d00100c6e03c41c0942040ca45130040c00030808580051140c01003191011540b5079072514882e0880e0f001b43d02000c81d50359248240041e882d03080c0140c81c030b010b880d070b201888240c404810300d80480b800f5100b80c3d40c2c1a030703415406008648681c4165810b174020310203113044525190a10084801003a1850000142d40e800003414031340c01fa11612001581044230b003407030800110140801010040c3c418209031303001c03050000b038940e110801000d00c1200710390848450f0380ba03c08111803040c0e004101061816043c028404282c41c0050360100440e0030004e9041200b2141385c80d141006070030f820180129090081c114189 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 496100665 1250 496099415 496099421
    0x60105062a0d0c1e020108040f1b0b0307030f0527070e090d020709020a0e0111190309050316050f0603100305010207050102091e0a0308301510121503050d03 69
    0xda001d514909a84d586a019003011a600100002d0210b03a1590104011610308921050714a12940d00407030041c8102455489101c0e0f181d221207003080e00001004046507050144a840804070340f014801d5081901403000c2401c03540050f80700203003a00041180c50402041004010f2074044220950b6080040e82c1c10703200c00e002e6081c0400b40c0310f6510000340d040c0941c400c843e00c480c1c495403050074411900340111040324224000c0d8a10380724140403640e1a42094400c0c038a454800e031070340c01c507003071800c41411304207070b4003031005251034600c40410005500c0c2c002200036010320480700180d41742e4418030070a182c00c8164001a210758070100e2808104041540101030100003102d10241c80401031841c4013074140800361340c94101c03c11503010400115140c1c05410504000005c89200047c65203003100e01a41518002508041900603c031107070a089140f6283c400c0141c41100d41107032946000740c844101c240c1100403070b0303980b00310450051180350011006180d00c001030352440f041e070744002005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 496101915 1250 496100665 496100687
    0x316050313060c03090504021e13030b0105030a0c030b0901020423030105010905040f02090402031e160f1508070201060b0d0b0a2111040204080f0618060105062a0d 72
    0x1da04a600400301d4414095a01c58044552542e41c0d103184c1ea05003028803010b50400011005591880c5c804101d02052070303030180c806800c030701040744100c0385541803520030054113a205501a0b08440c80700780108400f040c1000540e50010007901c081e1322108c0c40c0e140280700e80d40c040800080c81c02103103076802c21000101502c1c004208e00910150340c131020301030112282564020401403040c0110001810320019003039201e8001002d89180b111004450300420300220303520100d0360440070102c0c013110020100382001d0141680310b01809030030914580b02034501046400180309015000400d014400d40080d40584841c04000307445404201c5250058800c128009100da0503407940414407011004c00090003490450416090700c02d01e40f80c1400c80e03101008103030341068013084003241061041181240301c82c566402003442d860100642168105444290500b5400840c0100416940c8030103403503014101205000740c804110784c9035606004d0003002d908083c010359614502064001d888000c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 496103165 1250 496101915 496101937
    0x81504060605030c010525080409020901031a240904021b060601021b040c0c05011b1206030b070e01051918090626150901094103160503 60
    0x5140e1501c2c10981c41e1241c2c10f010f6070028000b40540403914643c4140401c0c0c0500308181e002c9000c0f09916217009070741c45500140d41c501c0c2c001944070b5036035905100c0e5019100b030381d0080c00c101a8500c400200c0c1d2032503003503105501161003641c5003034800f00141215102c0ca402081156110121607040c4c4000c0c0f428100e0080ba401804000f9125500208017220b403940000070586202a450b0f0803c0020100f84500408000d01c0700c90304400140c0c248140c48924850050511101006000003007045480c2d0202d60b8400c0d080180810000e000344014a410007958100181508140c100496040c000e10070f034a016440c042142d03000254000b07502003036540c0000c541d010707066250407441c002eaa84520490201015140180440c140c400152004c0c403074580044c0c41103a5808070768040c02403000e44035800940d54807105001000180203c0c070003185903075800e4401116440c0a4030758041c0f40c05180301e1820140406500c00924148100c5680309951084194030307181034100141d80350010304a01c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 496104415 1250 496103165 496103171
    0x30a05010f05240d0f14040209101512020706091110021609020a03021c051e06030c0f2704050f03040e0a0e0c150d060906120807020a08150406 63
    0x120b26801c10304040001010407000001c03440645011400c481d600c801d01c030400c0303603903224084800c2944038010349a9007004c80041c040c1c04e003094010800caa960107072211380d15040c814002c001100c56520410155481800e0081d030548140b1003c00191207403940040c8218079002e60003082008a02c0d028045660a445c3d00703c59210004003070340c2d607611311081100200303203440c0108007507429a0000d204510701e1f490b0250411111072045900002154008016507071100200600c0101c00309101d0b1491648a1451030581807010109803900880a0a02d024801405600c60203841d9034080d141d5019a9034003003074001c104410300400c1148107030740807074881c0240050080d4100d000019101554203461074104c1c151100c650040c0204007483c08822103019041c1e0b1034685907100d500ea191848101c032145651003945625104c21113201d50009181c0714a0407c05000540750304690501d407a82c0058042e0f03403040d180c00024440310702035002841c544a601d050a0010111042d050301032407103001c0074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 496105665 1250 496104415 496104419
    0xd0f091a0309100515041e0203010b04060e010f05070605071403090a031215052e030219090305070501030b06040506030103050f0f010e0604030507060b041b0f050708030609041403030a05010f 84
    0x40025250140d03280640d099240048511742e1505a110141401e103000020b51030500e03000b200c0703040e40c10036817210391030110104d400c00c0b42c2c1d41c2020035031302586000d20306a240440d001d0340240042c01001c00c0504a03556800004203040c1c003455440c11200b006500300741d04e03494940e0080e03540d003601c104100c0000f00441e0540914003000e0265989001901100360312040c2002d0a02c003103154082c2803030040c180b44100312000307024200001500d0541650300965680c504281d106040c1020b885004d08002d41c404040011030310100d4688252802440c0100b00d280230800000c50b00d001d0380d08000d80c4084000000000c105000030510b601f2110001034904144514120f2402c1780c002c48824100b9420850004000a100310024401c00344260780029030f0441c41400329040340c6400400e1450016041042035601d50001d0841e990b0400c0703443c0c070900d052800c2c7c0e50300780680805000503000b40300f248040f9042000340741b4503042c0d002d80c1e481104c2d00c0b8604003003807101811080c41032a200314504840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 496106915 1250 496105665 496105693
    0x1315090b04050306130302120c151f0603180209010e0a110403030e0906061207020c31021b0a03030b0f0409021e01200a061d0d0f091a0309 61
    0x94a00b280d0006000e010155114865600c8001c1c01301421000c5000307010745401181001c0e0007070040490542d00600340d29440f0328102d1011200030b08030208440c00180c4011442e03076a020a50280c0701c2c1480c001c40e0b80c107001c2110742e80845207000001d5100c01e018001040b540002c03040103201d0008030b0014005600e00241d03482241c407079408050b000611104142c902ca013022410143c0180d4050201d902e031804d212082c1c3d8154009072009001038209a8801c00c0070300d82480723586000c0030511540c804ca500d1191841150810442070034529076004900390b801000890000440b14140006696089040d07190081c018444043c10354410520380325071050764182403060b9a52154050a44c0c8146c1810400c100c1e030024031401c403981008120350f42d1044d8038281c0d01101546a080d2801400341d1040d501e0400103450316101607480004400030001c5035070a000a83e00240c0b8413500380141031302185d038411120b0131620381041d9160183c0140d4012140481001184104058400d8a01c80020904 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 496108165 1250 496106915 496106917
    0xd0b090c010c1a0408040b07050609010b06090a170106150909060602030306010c02010e03012a0e0f030d051e0a050406170f1906090e060907080616030b04021315090b 73
    0x80140c0441041030303000840fa4034851000f07070814045c01009007030030383c3c40f2650000c81d401403804564981010050043d032003030900032419450070450b13106040c01540030108400402034810501c2200d0942c0c08400421000c0d17011201900300641d40c04500060034401410844e05449060542840e26000117034852000c001c0c0c0703004000507900d1030301103001c170740045441240806403581e0555850482c588850801210020309015800304d101c12016070100c0074140402c000c0ca403600504054601d85e0700d0b45c2c2d010442d00e4681109041141e1500420110381c0c42481d40034010b8210103034001a42280160440003810803107a940d07441e44503101f002480605010004c3d61406c1c2c00002c90004581c041c0900c002001d508401380500240b1a40ea40102d074085e21090310307100fa5107402c060140091140148074035000707410248001c000d03d04110344010418044040c01000b01070740c8400d504000da8a58045031045204814460707116030300d5820392a010034a04080d2404600741301c00010300185800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 496109415 1250 496108165 496108187
    0x1803030219020f131d0102040b030f10030b04030203070b150d020103020c15010311090609040302030706050a0b060c0f06070c050a02040b060405060f030a06090b03060718050d0b090c01 81
    0xa0301900156a00003152000c1c0081180102d0340420803d1001c5500d880d03000320701aa46001150200702e50a48640703400c000001902c0070000b69004020500c100c090010071650424800010bc1d516036072200d02410903a802c9800c002e11160844081c04207066001010301400782c05403440030306648412030b00200b2502c0d2480203540042da544582405503019034007600b02e02a00800350351800305444a40e004281098004607020001043c0e000024200421465403040058a4440950070592070182d81c80c040d0100042034180c4400004a0208440c0c000140391040170304841d0b00d40e40c001c03095540f2100002c000f014140b140c0c0f40043c0745a031240b15030254050b0424081d000d00c100710340034000a000600d0391140c000d0010440041d00e41c650f07400030045036404104003926410610060000e54503158481c0c180c09040030202112603a011401c40d411418030b040c89909603402125203d0009425801154441819503990051218051105216145034800d40302e05541f42c1e00152a554015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 496110665 1250 496109415 496109417
    0x108010507111f1e020c150c04030b09030f030717070f05090114040e01120b06010306030c0e0403031b02010204050f0d231f0902030118020906040b040207020402041203180303 77
    0x3d040e03a800303061030608160210011090086290032041e02c0104a18151943c025001d80d40090441048201404240495003001c00360107224184859103186030300030349c000a8406203004005c141036400400c00c8505451140c0c2566441e40352022024165441d4050881d14451005000401580c425040c0e0501191580c0300d06040103040d000441c5c207a13030041c400390007040e0f04210215a01c1000303010703540242801081e80703188444503e003081716100d01403d46410f241c140f81040c000510149408001d5078041d190300d42c101e66030707818220041d00ca0307801c40c542072910070540e02603101d03410b4005005803482910b080c10124111018407284006008004c0e01d501860141c0744103060380500d110701010b00e0f51007154021803001840c030712308118070b0761105841640c2c0d50721541141000c3c040c24056680b5801004a00c1c015500032400c00c1d0700007403100e8462070307032422a208070b035540d0703130550f1007054001e070007151160780341c00c81601c140a0700c66041d004101080980104012088880ea05980d81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 496111915 1250 496110665 496110673
    0x1050306130311072607060c021c0b010e0a0b0901031203091a070c060e010c020d0e01031508030a110a03020c01032a02010f23040b0406061d010801050711 68
    0x110040780400d801050710807010030410540070202c8200030803014015042c0d038140408221884401d1903403410103c64030070b00710740080c002040103941181460341c051f501910016000300030416841082d940e0858000c007030443d484c0000c142c60b900f401e00c00d403241c0d03501c510412821801800b04102680244801000d14440d040b013108007a12a80025003264450f031716180c2e491307200c0404d442a4001c201d902100086480e89603105200e03050141001c0520b078171000300302101e140ba40003921404150100001e0111034440102184d1082c3d02c02c0d00c66841e1f40c0300002019848107481078aa503c12840600090324407041500d00e0f85010518079102981341d0002c00441c4425001035028150345c01100318251008a100001c001200c510744800c0c0b440c540c00010401c9241e130300038003190482c0f002c0303038861507180c8000f10038848032200941d0416046000c0448595179403511001401c4030344c11004c8400b80d1404007030000046140054140c1d2000e0009021641e90311000701c0304401c0d02e040260990380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 496113165 1250 496111915 496111921
    0xa050106090621051e0c10080c0702150903160e09060c16060908030c0a0906020705060406030506031002040608160315030b060f040e210a020706050a0306030501090b01091401050306 80
    0x1c0e5019521403c03841001514020300b000e541e94400031034054601032068110301d0301d2642900c1c0014121090078030340d040c4140d0074280080c0c0e50101d0b010300080280181082845030710b5074003140e402d03650030110041c215402410951a054803c030428070554019410420104e0021100455045c0c8141c030001805410300b420002e403a102603007014010741e9000c1d074460094000c0380c910401144180c1151800940c1d9071030090700100074003260342c410360441d08510410f00056640800b120225862403a000c01e140e203800c0300003800c15580e18140782882c1c1c070021740021416045411180309221a2845075040c20f803024064043ea00c08100703020100c0304095040c000900c0030040380350400c0c0c0162100151444c20301c04030b4101d40a0000c80302c0b240e88100e02082c00c0151240c00707600c9030400343c101141881ca02040195480b0305900030441444804101045890b200fa4410340041d0b0300310000f80040325550912040c0d80c9000c1c000d4048890900403a0204070403840c240c00d040700c02c00380060103159 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 496114415 1250 496113165 496113209
    0x5010e07050306011b02040c08041202070311060918090706120b0d030f180e060a051c1403070503123102130f05010b0301081501150e01140307020a0501060906 70
    0x1015248108000102040c00750312223101350104130000c0c0d1038101e4103007450300707090300c0c0220302040740d80843d070102c0d8050001494642d01d00c00800c0c0151032183d1100448000114002034054213040c81448a00030403401c418001520022610b09403502920040d84401c00c500327407118120842c0d0015045030285000a1281c0c914500c4141e01d4a0400b419224000b504070803200a07522a0b07002a03600ca00340015880c0c400340500c01803008076a222400d010320b20303038000c42c0c6042d040050701410103150302c441450f01c00e2044910003584007059070381d1401c17140300c400d94114007500d004019010b150118194166100403110302040010341850350381d0f500da03080204160710345086888142e100c1c011031411440354002c0030302a10342210001e44a605042d511440e1201c4c04407c1101c0140443c01004111003100644d40070031038a00d02004031814003801038500355541610040518000002c0111540d40821001c0c840391055000340841ca5444c8501000c2c1c80c0c05026030025207540282c880303948 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 496115665 1250 496114415 496114427
    0x3060f1e0d170d0b01080a02071e020d08030412170103030507060b0415030501020c0c0103020f0a12181202060903040602100e010f050f0f010906030309050607110907020a0605010e0705030601 84
    0x241e11a0000b00828400107444054075003251400201107601c40c02c0c1d80c00d49603004107900754000490030045041a07120340310034050b6a000303550303900540a4007850005545960000c0b072800c982141203035aa03420145010b03000c483c20301111707000041540d86680ca074840700203040c80c101c036095a601e50030611b5540b12200200075201d14240d0055540502101d0111a201c010006501940c001a00c42d05c5c8080d40e035040004022007141010b10411515881c084070b0020f0b0350b50001285040140d190003100150020221408811201c441d0850280208245401380071782e4260740d50f00b036803240d40302c041500d680c2b801030340104000340e049034541c0c11460030307140d0122000e40c80c1100045a00c0300a10640b1044500075110312031600300400400c07501040d82e0f501c0034010004150700700102490354500408002c418001e040c42514001800001d1100f0000c5241c1002001810000a820902800307544c90340b60000407907059003800c1c00018004c4003180a40d101e285d01d40c0780c152071503440500440d56 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 496116915 1250 496115665 496115689
    0xf220e011403030412150b0901080d1103041a0f1e0a02010c0807021c090509090c1002030a0503040b04111207081b0a0510090306020c070f0509090a0206130b0d0203060f1e 75
    0x9159501c4004003259550b230b00303d500070880440a0105404140c0008240d800b031109115200d91040004100c1140c11089003051b0007a0000c00c1d60b2078800300090b080041c41151880c800858045004400b86081c90008284443c01c41d0001c0240415080080e42da821040320340c3c0c4c004d0307040a000001080200044110310b03103d1450600881521200001c504034001c1d80d1030f401c1c9a000c5000100d050800c00c3c90102c007405a40010350402c541020010654030009000400b02c0f801d0a0110f010051008006580540c004115041c2c46120380450b1340d8586462203100c9e041d2041480340c0c0c07448403540484500b0000054010700c089801c100c180a4071043c0c07020100c003004100309001012480324070250601f01c1c0c0d84405000c40d5441c1c40d04945d090021a04240c0c4076148020030f12440f0000020f2500c1e1340d83d4151009034581c0d421551074110701e0065400154041c82c0040c401003000019801148100d0b01101c8010b035141f00742040c001d0341000520300007000c072038001002c0154a0100e491801c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 496118165 1250 496116915 496116953
    0xe091b0f0d080c0109030207060207030f0611090301090506040213091a0c0702090a060312030203010819051f140f13110f040912030507020f030f220e011403030412 72
    0x281c1c040c4280d4410b200356104403a400b905035950902c1c034003050b81c14803030140140000d200401c48241181c03102070036001491002080203980da4441d00700c0d410b011090700c0340020300400070450600141000c40d11042d040b64200d11441f026100400c03249001c2c455070103029040703181c0b1001c441d0003000590418002030900342942a040c002240141e8588800030f10600c191040420254518642401040d650311b0a0805040c01480144009840003808040c0c0c41c895050400b01044207081050400794000303640c0941d2010700001d003040005075000001c03101407082c0800308540c0c030950178920800c001d68403900b22807265900e060105010200e51007418000030580d900004003600020101d40c07245600f02d5015110f245001e0285406100b850741c81807207070020349101405010810344030b120f03001c01d0442c0700b0000310b003e0004140b10095501c4032040c40f812001e502e03442d1031b111418800c0034460001c12007000305042c00b0600300401a141203902010300005010000d5841070784c075132851040303d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 496119415 1250 496118165 496118179
    0x28050f090d08030c121303081317040f18020703020307030807091203080403120515060703050d1d0f150a050a0f0903210504020f10140409060e091b0f 66
    0x2101140b0014011070140d041c0c0a030b40e41e5903929030700513260010381c0240b8100000d110f100000d404a07800014140c5d004030b0704d0104128010300c502d040f40c00240c0360484242c1ca0000800d021440c1c8421966100995131034142d0003061041c0780d1007200681c8510080180180c10034086000003a008854a51b00241241041407400345c5401001c28201d074507400c150005241d10060206054000c1d45c510700f903940200d000d001916012034941c0c12040c4500c041341c0100e81c0002c0c09418144100c2c1622352080c0e100c0001e100103403d090850480c020403400c2031400d07000d00b00d018000d060000a4980a482e00c080700c00381c60b0b650f540c2c0a8001001d008001241e0070341c030b0740310f044d10149242c4030744c920700d521130340f520842c2c0d4240c074140c2c01c0002500391441c07170031624000601002d03030f503500d030701c65401c00c0c045506c0c485c1d980e104075084550036403241180d140c08001040103d0200d4154200006540e10507070001040d9540c01d8040c2d66624604d000282e080e0b08030031031004a42030441e1301d042c040c0009000a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 496120665 1250 496119415 496119439
    0x303050a021207030207030b0c09030705090a020d05040501050417040f091d0a06051b0f071106070515070f05360a1d07050408120d1b0528050f09 64
    0x1400d5680d03c032080460040c5c000c2a401e108000035030310303800d400070340242d02e0505113528503010039511011030003603034030802d445400510505c00c107030101c4018100210061210f400d00703103020b90107003006a90885640080007000d200112a0005584c01c684600064030000d070711700305500004128000e04000b44105108941c045510204641d003203103481072100081c6440c2c40400c0340a0385190050441e001c5c401080b82d0301c03194181c0c0007903680349a0401c003102446844a000a2802e2280081c024000d008845101003000c00300c86030140300c0d142c2c0d43c03100c603103103400581c2c1141c0e14415006842c210aa60040c04d645581800000044404021042000900001c8000f64444410b40e000301c20130b80014010854111850f11807941220140c10002d00701400c100740710741c44510ba20302c0e4101d04140452045601d05542d0070207440087d0354201c2c61644600001c0040c080c2d8400101503140c1c02160342801c48104510038400f82401081c2d403260709040780d048821216a10440d00f9071783c44858032045c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 496121915 1250 496120665 496120693
    0x6050405030918060a05030f0a081b0706091403030403021f0c151e0b061b100c2d02120d140109060e331f0305070e030601030c0303050a02 61
    0xf020030000302032000c2190074680f40b810005410308a401042c06a0484511a06203981c001111020164410f10b480c1d1641441000348483d280c68001c04205803054500c001035082d0403580c1142500c1c0c84110f8029040c80903004c4c03694904c110300c402508810740a50076055140d50a19249500c0740301e140c085420001da407111010340305080d89201c0801c0d80c51031200c07248081c0960b00307802c0b0360a001d81807154080c0540041c05500840c91822200e07041c807070a590342420300f400803a600012100d001c02244200b000300a14159040d1641400c41c0c00880f1000d059414100b02c019030000c499009041d20760030710900303000380c0d0408803120348825210740c452445080c4222038580a002c103080d0010b101d91510403520901c40f000b0300101181c00004046840e001d541c001c5d80e0031207200041c002c0700400c182001117140c4c1c9054090308105100c031040c0c000e0b0002e40c5904880d0140859944903c19030309440109501c0b40004e200041c40c003104044200000380c002d0b80074100398801c0780161a45480b030744038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 496123165 1250 496121915 496121929
    0x103081b060a0c11150708040c0e010303170f060a060f0203040302030a050c04150e060d020a09050a0b0307230f01031416090605090609011101021308150105030309030604060504050309 81
    0x1c2e1003048140c860800e41c84465210130301110615208008000c50441322045040b021350140c0306d40c0801c07200350002030512042c001107800404481d0046941503940e070a0003489030900f0382c81320583c1b00403080460400441082403d0007a04028030304602035180c07100a80d8207040e0312a40d0000c0d80814040080503980c10300c5008401f601880192066400400400c4111800d0501c10f80031440400e806101d00700078a044141d20403015592422a00e1b403e00014054440980c0940541e0781400300700500e4604070342049080c10025400c403040c03036031200007021001407002443c6082441c6003c1c982d4843c80e00440c00b080c0b0381010306000610103e031003600d2a40e89800c0301c43c0075044c551210401c01d07007648000182c0c000c205034503045003807070740010000d800c52207803103615030420003d410048038044080d4122541d5910083c185c1401c40e950312907480e200c010702c40010a8881c1a02c0c00005d0030b040200490f456060003c015216540d1603a885078002c040161058506220510003404039488400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 496124415 1250 496123165 496123171
    0x6060803160213150608060406150c1a09100b060c010e24040b04080703090b0d06050102010b19030f050f01050a020d0b1f030b1309060509070f030503030103081b06 72
    0x40e4101d603580e1000d005110f02c030102070081001092500c071030011402900349048066443c3da19100105480d0000010058691071308071072070700005040485400c541250000d030420b44603d00b2031054009800351002603004c11a29440141c00072a44903500084c3d980c0305e6031082800130306650810702d040f80d42900710f800d03501c4d0318007c55002000ba03d1007082c680301e00c070110140a0669a40078580340d901d98a035140c02a000a00624000c03a44608060180d00303090701a0013001e442c2c1c1c1c1c440040341250780103480e1a21503079015520b001d0215a050410101100c81503640344400800503103143c0d14203150101c00042600e150213002030303294140f14280103c5000d4502c40d4000b6171907800080c0300804032661074150f90710074850b0040345060080703e11801d603909001420009000701902c0c010824040300402030006040c58403900c40100300341a40102d01a5421108849030395480361803d0384d403400d81e8000501030303600902c010000203a44400409615000c00345d0449803072446043d440c5032200c15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 496125665 1250 496124415 496124437
    0xb070308010f170d0302030c1b0c040c03110a050c030409141501030207030f0807030605151201050d1122230c0a05120c09060a020706020618150406060803 68
    0x3004014000340021410040c001440300d160200c0000304100f0f581d025031120307071401e154011000402e44941041601c81c815108400901c000360f240740e4144c0c50702c2480b52464807031450000410a203501c24440c50b048021003443c0340d4508201c03030005580982095860020710300c0104004189200380d40500f401c070440121000c1c2550070640d076840381d903c8182c05000c1c10144103022540100b54010003c0044a010b0f0900c800c060302c82503021400344c1038540080703401c20700002751403c20010301c0005007034030314090041c2c8000366254010451081d0015030080c0c00c051043c10143c61a16055040c540e0b403102c2e848a01c00c42400d0100640d050340c03400d54004001e0f2020500c140040a60a03000503401510301e403034103107041b806d001d01505602030b00340100c0003103901d100040c8000801c0812520b05110040400c2d031142e42e48103000b56907887d580108401406583e020445035450703025032000e04915440680700d908640d480704070610b81c0042041da0007948440340040c5031241880182a0f202c0c80e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 496126915 1250 496125665 496125677
    0xe011826130801180f1104020408070e060a08010b060d0f02041a091f09090b040e15011d0c0711130c0c020102060f060307031e0b010f061710050d0303060b0703 70
    0xa08100c2c14219400380d80602c0848502010a600294800102c600c0b89075008814170040000c00001c54028010b03a04460803034170509502182c5e80c0007040c03100d8810381c030403120120080e031501010740c02e80d4001e54101360480390510000358201c0254200070155400e401c0010300382950344880810078410061100010000020300c0c00042c02c11102510f5012100307211010010000c1000138012400b52046104499490f544032466680b80c0c0c22860048103417408032108038408011b1010111028401e0300c0c502c50b03040c40c3d95000703040030a103c2c0e071040d040c008426050428944402000a0101c0b003140e40c894550f0301d1520030780d6418401c103a1220030390f40e1084000b041d50b200181c544040039003229001d00c803850421469545c0050200c2c2078a41c0940184484114501c0400303140d8050000141040001d10002c00c0242e440901d40c0c01711261aa00d841d11034207800c007000d9110600b9075034000c0416800b08181702604000c02224400c0d4801d26001404a5465501010b42c0e007002c0d00071000145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 496128165 1250 496126915 496126919
    0xb190305061602060118180813060906121a13020406141309110d090b0a0513020108011a0403080403060f0506100e0f120d0903060e01182613 62
    0x2040001d40e510416100300307020078050710703207000c0d43c0c0d400b051003079a002c0e05641c0030a00c030b4141ca9801042244502000c40f40d1400d0307091800d8411038012200007828212000070010b0510310480c0c000045800716243c9841b1015403000355005810b0010000050004a65101c1c51544a80740645c041b099032000050712942402d04c0240800d018050400e080c0ca03003441958000305400341d00e44100c0d086510b001901d01e030180152340d060b0040c2c21800004a103482d540300705000095100600c04c480c01d40c0204465034030001c00e194a91400d1001a0014046c0340050001c114248511542504000502814142d5036034840005e9806508125009607c0d0030703400010b0b021501555402c55022501c40444150402d0010400c0c55000c00e03140c401c0a48038581c0e406078035000504d00c1d80358004020741e090714103028009030a801c0a07100c100d400d03a1a00d9011034000c2c034181308143c000c1c50110742c01800403005444842e17444002400c01c01d002e0055086044041070104010031042600b40c012001c828 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 496129415 1250 496128165 496128173
    0x60f1e0e011b1e0e0901060e010207090621061d010605040b0a24140d1e0e0c0f031018030e0315010509040303110d02070c05030102090307180b1903 65
    0x90481d020910744015090380700340320950070a801850400105444440c82c448a0310104d0b4a00c60280361541c00851000020401a90129000004030070a8007243c04d215130341d480e043d040700ca1600c1800101002075900d0710183d821001110005070007420301003002c20620b031150b0054402e094080c501a03550b4401005182424014405040003c40c0c410a9480c81c0c030400ca02c0461105000129840c9111800c00300c082c0103130304c0204400c203250205034403120701000306001049405009900b41007200b0301075184501e05d00071100710a074450040c010a80c011800c3c840403407203003c42c596240c0034150f040b001104151241c42464500240e40400e0340ca03960401401003032201c07051a0180e0001d08c2e024000f40244142c5c1811144c041e86d00790100d5903203080480052040c102c515181100c0041c0caa42000e03203a03006000b80500803041c9440080e5104109400c0303209007141c881d050380202c8800c00544e0580080c034079260081d004003141c0002201d000500584c00c95604460408512000348144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 496130665 1250 496129415 496129421
    0xc110a0906030b0604091a040524090f07030834060c090e0601020318130e01062c0f0712140f090604030801030212010e0318010e010516060f1e0e01 65
    0x4840309617010401c1142d2502c80070300d039a2401c0310a9281408040106080060400903c3c1c5a07440e0081b044404003818004911110400d80e6401e03024460300078074943c00e010100e910b40880b40d0202c0392600c0c104022001000000d10044040d0300d2481452503424490078454880c4c00ea5841118005820a64600e002d403020405801c9000000100c6040040c03590700002101d4128a40c09042c041d0b00031207800040c42400028200600c03103041c4080c141541c90150450b8040c0c41000e007022400200801040c0501c21000180203035040c00d0b00042400c01c04900c007016040301c01c0d450310010141c0d0281c0440d0070780e0107200b04418070380d40c1d001c10404299000c4040c07030b4010104402428460400b520300915401b410f000280c4903051002d54540e042109601002038040c0d4201a01d441d03450501d0603250f441030300c0304240e0100300032601c0350b05158801e01c1180ca00d8400c4581203281094640c0318540281030760a1095072880e51002c503c980e01c8400101c00040d008540404030300a100d400005080d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 496131915 1250 496130665 496130671
    0x10314010c080c070803060409080705010501080c18010902090105091503100501050316031d0f06010503070b0c060a1a060301030602092e05030c070c0b03040b01150801060c110a0906030b 82
    0x2c10190a0034449070701074031402c541006410510268503038481d0300000d001000041c0300100844400595030080290641001d8100c407a00b50684025903607e00074009041d5511080b81280001e2030018400d640d0b071540680400c91040c545981403840210206010b80a50096079400c20b80120070010300103030706d0b04d121024090a180490840c20f20401c103150204854a507401030548490030100b8400e000346d00c0071000d5800e4000c07205884108440c0b2900c803070003030040600034080d140010030000f91200466a01460150040c0981d554602410000b48210400c0301105900f15030901d2242d40c803040958042e600500005944521540030040c10115003c00141441d005000806900d220b0351034205454030035040266a81c1d80e44c500c41c0c00d0910981c0c1005004003048040482d120103030002652080e80300e2441400d0030307601c60700c0e50700281045459840020700584014881c10780f2401400003064890128592501d002900140f0881080d07008a081ea95940708200140180c002030f85070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 496133165 1250 496131915 496131917
    0x2030c0c011404030803040f021504090b040902010e151207080a1a1c020402070501111b03031b0a1e0f170f0612070e070806010f1b020103050a060b03010314010c 71
    0x100b40b01500c0181c030618003692101809862020001a052081244207007018a0b030041c089080000b00c03800b6050550004e000e1180c0e0380703140030700450542c1004d101e1146441e0f016100e946007800000204420040709507030354501c690302480310500e0448103841e864081c4095864442c868940b1b0302d03060044403004400c2580e2419080040316003501c841000e10701004020164a81d0280940041000380c40380703050060040d8030b4060000c0701100030a02501d1400e0003545000d6100101c0d0440396a03c4c0010303180d185022400d001260620001ca000901481e641410182c001c03002403c2d4000660741c0740d100d02804180c48098100c803c1da84480482080649010448003a0034001800231801c000100101d000c0c114500c0e01c600705010402c0440020818090585d16a243c1607000500711601a600e441c08100c003800301181d1035005403e4803145012510303d6900807000c40d00110041d2034003800d20000705a8841000c40d00007110300003107001e10301880141001c1800d48501c14211540303490341c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 496134415 1250 496133165 496133177
    0x90405070804150203090f0a11100c0b132d0201080106031a130905030a0c02090f01030f0201030507110a0f0b07030b130c1205190501080f0309061e0a02030c0c01 71
    0x200040303022040c500000f407803110040e01e99980c10f10103443c00202143c2c1021901c01c00501c1010052034030b4039000300703040680e255114010340070419a000c80301c0d0f406c0100080d50440000c0c950b0340e60000c000d6209400348074141002c01042080707511090104030140311039084804034000755608154458014880da28041144d10049889148140041480c151080312481c100d010b02103001d0300a0b090300354008041c0c03581d802d2100e90250034444003001c100c2c0200c802c0307c002094001c0d5610414102e0740c200c040c0c1144041981c1c0114014100104040e052000900419682c0340042200d4003485100300e90780010840e2070f0810382140a00149100d007054204042084551a07d04041c00050030517400807504440c0103009950003070358001b03094042d500d807004210b0b10919207042c0c0041c18100880c100111703600c030940796884c1c5119a51034100e50707201308054203060909400030005051504520307002811030782035900c140d40c000d80100c00180c1c0081042001000203200b000f1014109003050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 496135665 1250 496134415 496134421
    0x20f06100608040f170a030b0402091c0c0e10170c0d0f0305190518090702030412061b02010b0a0e0106020d0807030e0f1b0a05150f1605030904050708 66
    0x40d020460a4080c1d08100000b4401050800989483d5800d072540e2040d01c50306040107240d40e120080e0010385030580064140003502c00e803810315208440c9800b9004d020200c242c5107480542daa089000d99084525030b9111200007101815080c070340b40202941c1164140242c5403076040c8101c480920100c5046400803810038540340c0d0f0f070b410740f02c040d075038410307a446c0d4648600e04050b12180110940181c503000301e404415021540320006200203250340c01c2850807901102e09002d0400011111030001da801088203000d4084281480350405104690100325402c0e0144090f80002d401007010300582c1d1111560202d42c584940040041c0987d50042c5846615002d030003580c1d402d1040c805070034010914081042240b19030840315400352050115542c010341098140d030340d2a2480003014600462207901006c2d454680411002c40c3c800900403c441c58094110110303e0b403044a0144003400704000f250514904240c0550b4450300443c059a1101c460006000c11340c0c00c0105a14208881d81d810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 496136915 1250 496135665 496135681
    0x1314240c0706030605060703200105040b180f0709050c07060e030403060b0d030e06031005030d0f180501120c0c0b0f040b1305100903200a0c050a06051206150f0901020f06 75
    0x50f42c401f26094a00020000400c0a080a50684c05441c0c00000c0d420300b0300300010300007600c64480c007070040d41c0300f480140c14455803090385070f507407030f4140c015035411030241008a144117810007504665040b0680c2c0c6000781c9603460804982d11010010130036080400d041007032001602c03c080386460180d800a51100c90740c0d0f8020059506401d04078880d10011001c54a000d1180c074074078024000180484100200c4540090844c90307816021301c000600340c50702d070142c60308051454001c44506031203484503050080882c4015018240c0704008204004003a5000301c3c1149000c00d02440f6040040a8a03007840d05221100c1500140690030102800c0700c9000020300000700e494185000d0180000c0c45081c07480c044480c2640440a1011201c003c20341070040c52010800d107811178850b04003124256500c0c0248006424548a00740c08600f05121105401401e85441980810014150405000c0066001030030381c00c80c1c17120b131078030040104854115580402c0322100051482005003480d28080c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 496138165 1250 496136915 496136917
    0x50f0a0605131503082704020a0c03081e010e1b0a0801030201030e15010816210305030703020c030301061d013906020c010902151314240c070603060506 67
    0x80b031154120f41c3d078185455810203c044602c05150310441042c3d40398a500d07074203c0e04c904108024841451840140743c5245000c0c800c40b0002d000d41c0e00da044000c3d100c5e071002c1d40c484070001c1813401442e00b42c1503c01c40101128a1141c06803004200d007006500300388aa451100915507052000c800b020456000340703e400001240c1103a41c240b801203010007248004604009078541d208020340c84283c000b00c7c07d5140032902c85040b04e20182d555a04654a02d0606519980c07100f1806540c1c0c3c220800c440801d00c00c200442d0300500301e08025240128a448151440d07000340e000310005220b600762000750103000c2200d40c8054100340b0f0b0600d0004240c4001200c0980e8035404000c1c481440d03080c0450b10103070903209090a6801104c00c54440e031000b205030f8081d1035080400c80c426215142460154000c08041d1202281d014104030030301170601c04480401d4220000007035210307107881d80d1840140030740040080d518560322030b4192203000b95800989052101c0d0401c4c1c007030504002080c012500c1e402c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 496139415 1250 496138165 496138189
    0x70f0302040f090c050d1a1e060405010f110a08131d010b0d0905060a06170609030d0f380102010902060906090406050909280b07110c030709050f0a0605 67
    0x4500018111407003102070750740d0310640c4010020b1605101e9080740390b406081c487c0f0030303801d0103a0780a0582c4025684002c2400d5070100c840f42d20410078001403049511401c880b608003801810301f840020780304010b040c80c1030141c0500b25002403000660140b12902d003213021300103203c2036580c200c850034030841c68050701c40c050290152400e00882c420400c544d0507000009500c0d04070003aa80c1c00e08110810801030442801030100c3c00c800040a407a4103040041c000d4880c0030414095800c00701140b803050b000c0c0c03da550740703401603503252040011503148069030348000640400700380301080000b8a40902080e42e0f0349200b030659142030035030030268407410100e801c0203c0466a5903030383c11a05000400510300c0d9080a90405480810022102800140a5800c00c01145c5004517590402d17054041620328400080c029440f09010950860190401401901c19941580e40c04040c480209240402561000c40625264414001200d031b0203903156030030107140c05092000074188008603400724051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 496140665 1250 496139415 496139429
    0x6060f0c020307090204060305090706170f091f0e07060f0e0910150c030e0613090c020708010c120b0a03050319020a0c2304090506010909060f0212070f0302040f 71
    0x1010500115a814000d203c0038121801c1c1c00c548603521602c005008040c01c07100300015203c3d03110041b480900941d0a00034540c4100d051045940d0b440d04030304030000b800317021040301e8860382088600280704002249403100d120751002501e8070001c1c0601e1300d851165401002444201a031841d03a042e4021243d501d820070986040c20243c4400d5003140301600740380c0c00340d4070301e400746c000342001c09500000480c1d5290290345d0b400e008003098030805c4000e00c101511007030500b008410402601090750030414982d0002c1c01a614415600c0402a0a480e00d80b6020700026040c0020034500c480d4910412000c6003064a014000742c1c110381e41c080ea03900c06c10190b560280140700800304158801c00c2409005036008035082d4506644441c1c0d00500600c03096020080300d20071079030300c4040c140f500c10f0140d2107070000001c0070b0316480c101c4d42400416100c1c000380e6049880f01900f8064170071600003001510b8204010103294036040000078810100c00400030205070040208101d00c1d242c8404101c26141c203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 496141915 1250 496140665 496140677
    0xc0d1505091303050d06152303011205031c0e0708011107060504020d170304230a1103010b18010806011508161106040c1e1d07091706010503010f06060f 67
    0x25500b015207241c0209170700181c5090912602150300480c3c42c00b060140e248235120080da90314840c0b122200d60f81003100c521074906081c8010020280c0c405140c681c03d500030011369180001d509100d10800b000c40d03000310502510f409009091940421404005008660082101124440840b840c62050010140040e40c0362404202035544428058200b83d6110510001d440786031001d11130507800450301035490510500180e055000d2240142100c2040075001c1c09499080b0787e0303034100349842070740565010f660b16841e0390303415140d002e0050140e511001c55244d0961601d9010383c0b800314140c100e024a00894001d081640c3e42003000d443c1c21000445441d14145000502240c0c05403802901a20785c0c030405c010b2005000140c1441c500313a454000181c2089460300c9404003040ca001d12520644400c01c801b460200010082d02c10b0b0040c00782e00d407124207581c0e9140e50030240c3c8449504d86000350400c1004000a280920a001d814a01000300303220740d514180001e0840e0b2040d08414081c1701c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 496143165 1250 496141915 496141951
    0x150f0803040b09150c1c0801170604170c03071b0b040b0d050403022d0601060906050a080a060305070608070305011d0103020f18073b010c060e03030c0d150509 70
    0x203200c9041d203070403280d4002110740020320f20610586408010881b03501043d02d0303600114414260b80f0345d01a801030701c10028030040d152940d6199040c0e01c5051481102207042c8600780c0740403000d000804030760780581031580e07101d0048030048580c04000c0d405120202d030100300801039141c5440c00e94080751400000000c240e5a5401e041c2e04055050031015003000c03504045020703130fa1154000c200c0b100b1310042110b4580e0703268002a164080e9900034134020800038810000c26610484d402980504918008030769160b40c1e50750702c2d20340707a010b4020380042201c02d000c01000036418400c280c01410002c815001000c851820b0108160043c04060b000700341d403101205298855651000d1180f803055503956203441c02480c028000401d00201e11001d10400300c00203003d940070070380c00150381d2400c07400e4011442d100005446a15200c001200d44d80e8070b0b82024440c1fa002403014500c00d404054010307075030340400c00c04081211041d01201d03150b80c0046400b0300054070b412501e10b03070041d901552086461 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 496144415 1250 496143165 496143199
    0x1b091e030201350a0b181f03170c060703091e02010c141606020102090a090b0d080a020303060a0801021207120b0918010b1215130501150f0803040b09 66
    0x1408003c015081981015000281e01211106644240c403007840400c0070100700d80070000340c1e1490307452005800c00c1880215903d007034042c0d5000150003514561903150f6035255116808442c100503c40d82c0c0f10800324801040700e4042c010b03103522028501d410080790601e60345180506190304a22100820310b00c04590469002e40c1d0841384042d0080c196072044000c486aa599408186517030141051040400113055070050013038460241e8010304640506040c4000e241c028202414910f60201c0c82c503050303a004c41c0c1900c0090075803003a254060340e540d1801c1014042c029080b9400b40809a2040100340011041401201d030418032038600b0241e030300040d08662002d4041d45103069840800e40301030001d2802c140301d00c91880d01c00d110083c403504641600700a08101541d1407d800ea41181140ca1a8605070a0817954000c1403035201c80e001c0141038864134211090124102880b9040400a000e48401100380d03000901e8048004c1d890903003810060411f9000e01850030b40241c0101503024010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 496145665 1250 496144415 496144457
    0x305030d05071709070305240606030901021b0604021e13050703111c270f03210902121617120a080414010603020a1502010f1b091e030201 61
    0x4401c5500c6403113042268060341c545641e44401c640383d109203007120301100d0689084100d00302040c8440140d641d502801d00000350320003022104d01c0e5500b00f00401048841c000f103045c03809180801081c0e03a14041c810b000c05000c0d5580c00100f030f031081e0346a1524550391031406452440003010302040c0e41d1940902030340541403000d14a040f141000c103049032644150941b140b01e8001401c820321803907880342006803c1c40c1001a0041d04218549501d0700419210785038092080d2080c40d00320141030301d129202071044850340384084060349444000c1c003035280c8016620710301240c65002c0e1016041007411490300705214031600d002c03c0e80b0703000007458000d02440880010b141441c021581d56080e0703003000f04025003c450132108050480c01d40d048a4005210f500d041c4c88e03024141c0a11f050070640c0c0000041010344006003150340340c040002a8441c00e00849106028104805600c244e80d04400780c90413015400181c080c00000100b401d03085103c8c01c0c01002c0f603030203080601e0443c1440c0440840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 496146915 1250 496145665 496145687
    0xd0c08032202031015090203010303090302010c0f060f0c0806031f1805010e0c01080106020106123e2e0804021504060e010e450109020d060f0305030d0507 68
    0xc1030056540404e03a00810b03030004024003400d4100c280c90b0580f96602a400c0740001c0c003010300011002c400a00c015409006da030454280a1180300d00d01c0c1515585d04001e54008c002c1c141d56441d2190300072128541c04c2000346400000031405401c032032400180452104800c207103a405180d80b590340014400740c0810504200301d400030000d01414002d484c0da10380c4c400d0141e00b0300c1d0029000100000c1c402d4410300c40c03001603c85240d41c10108034003507119400c41d0300681e5210000c500100d142c035422500500d121108851403252040c10b040b048100300f00c28a04122044d074034407981d40720241705c01d00803100140e105135030394105100151118004224801000302d080c1d940c41c0000940450303400c0c2c01001c4003400750400da175598810404a0103200b51800401c0c442202056030b0710140200c1c08440502e40c55100c40d29103180403041c100e580010800034203905c1480c030f0544c0050985000426801140094044407201c400c00070315607511940d6034416446181515035880c000300342441d1003070f116164 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 496148165 1250 496146915 496146919
    0x2010c0e0f0a180504021c3f17060103020403050c0405090c120c0a09020421030e130b1203040b03011e05040c0807090f0b04061d040203040c080d0c08032202 69
    0x10826182031a200404060f00c00340e104410b400100b051124558081a4403503500c60b40714100f0044240c520102e070796402c02c014100300d921240082340784880d01e001310480c0b80302d66100b0203030000b035413905103e0700c501034480b504042c01000140f01090b400500c0e00e0203003009540c0040c80d581c1e1107681d1410103407500c50f82c640c40405480c2100311440d000505e900302d100206c58815549554035030301c034128071841c407604410040a28a40300080c0d05650303120305d000d020307040020311414140c00042c0075086da80506c89030b155503030a50b21a42d041186000040721800c000441c40d0038144444906607000522400704020107884c84c0e09540d030340002c80400105000350050102a076001e0340900068012120000084c1120b040010000344020904080340c59185030a850503003840000c6412401049990f031305a80c0c41041e03e0825210f40c07004501c614051030607000710b0341c1880401e60800031640c500c101044403181e500404940020101da8100e01b19040302d80741c0581c1214409184031200c10003035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 496149415 1250 496148165 496148189
    0x6080603071a071a24030c130c021e0723090a06050913020114090d080406020a1a010806010b070519080a200a02091e0403030f0c02010c0e0f0a 63
    0x41c5525550700094850759208004071082800c513100b14021400040b601c006491384100b2000700c40c8030200401d200c40400103001e85503a08900408030b56074003050481200c4860b80d074003961280a905000520706601141d404c814510840100e4aa42da1003d01030b60b50714220171000440c50000204440c2482c6101900076481440d0070701d1584000c0c100740c401c880c041c2c50b0440000b07000d12141c1000e03400c2c5a034140c50300ba07444003481452044640001494580010743d0011007008601403502174002085503038000c010312420740c40c040c40c000042c03609481e48140302e14014087c808011805a043d92000d039803168690899080041c5054002d0080449414000703640d02e00384001c8c1070080010b103907a80c03500350311114404110081100c45244030078032900107044210040c0f4200c0301007078001c01c1561008a075041d20760364450f8090340583c0d040b400300b55200200c1500b90018060001550f0441c00204110304030244050308000d80002114072420700700000f4421592100000340141240007203038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 496150665 1250 496149415 496149449
    0x5030a03151a03101d0a020a0203070f1b060903030e06211609120206040e09010209120d020706080105060711010201020d0606090302040b0f060703030c03090f06050f07050f040608060307 82
    0x80003254400d0f5901c0d0040200301c0d40114400c01c05c40032404841c0054080d1144903521034900d44000c0d00060401c08c03c5000410000c00442c55690401c00b0b80b50058801480e0080650f900080c42121680301201b48600b606082000c81e420483c2940810010b4501503030341e0048461030b200081c480b540f05800d42000d10180050002e1140c45408914055100c20350002c0c0c44d4449401d0060011390300a5100c131040009101c140c1c14001c1c41a00040c010001504101076000002c400005440c600a902d5000b250003100865040064400908460030200d43c19414480811560310644001a1502d81d4260001c00c00303910035030407250070f40e01101e0704104050721000010001f008900c000d904c914240406600d607440c2c100300c07810f075110000740420f26059a40c0d07006d5001d441461310b688203250392400440c010a10108215450a1152400213524944044100440000a02010f0070000c00b403049080c1002e103070046500361026428030b14210354829001078907190f05900a940904542011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 496151915 1250 496150665 496150709
    0x210a0f0b0601030f0614150d06080d08310f060216060f050105031e0304150e090a05010305030307120e032101230d080705060903041a0705030a0315 65
    0x40d2500070301c030907030f01401001d100f9901c1e401034505a000e1b16008080c0b84400003c1464105c0c43d24013868801f1091500344213032021004202e82040e0701c1400207422034000301c0f41d0705034081c02d42c80e44400380007403030110440c034902840041c12080740d418200d0201c0801440c140504200c4120096520400c107541e1500d00123408003a44045401c1242c149040404072019103001c0e000703041c141c4801a00600400000b0850750000700004130807403045000801c00132402040005035031500d241e55841d05080c240e201004d000794080d0040c916909645020014000170314080203c81d00401c2c0c40c40d1450348040503080d510010510381030712031b4517403000168010a2182072111503030705841ca646072201e10b03a0f131a0440c2c500c00d821803503002048211080a03500c035242039410441c200b4002c00400b41084e140c0d0307a55038a0208251075090155002090070406442c0100302c01c0750350f0b075500c401d16080c00419600c0954a000d075426003805d140d107400d01d100002d034900d644600200401c20001c2708031100954 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 496153165 1250 496151915 496151933
    0x60203130b1014040e060c070218130212030a020a12020304270c080907051c1a0907350a12030c0f031b030b011209110f010e210a0f 58
    0xb1030401c64600404003d840c0d450306215600f0098a8240a060300c0e9845070500ca5541d8403110040f039000d284085418054403011a801c0d100c0c1000e0445404c400b5800e0040011a0005078030303415032648104052006540d0100310a00029800b810b6400e506107144020b0f07045001d40c0d0041c003071840d0a00c214010950700b0721800d84049807410b004000c0c0400503401100c0884044444507800c1d800210200310504042c502c00a00387c021500c0095211001e540e40a0040328400581c1c42012016042c8184584180203e00c01040c00c04000141c48007151415030280151107100982500c110300c005c0719040341800140c50040d844140b0b615058860311000d00108403101da50400a6580f10b08070744118040d1068120301c0610090000c80541034020480c06003102d400c103141003000b04c941000e620300782402089040c5220b0b1143c581e0384185041400141c02c0b5008546040040c051a4000d5940321603021811681e1503969040006035013041003841d00b100344c00000e10f5050340c10603c5040c412525 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 496154415 1250 496153165 496153169
    0x14100e0d08031905071403040501061a13050a05130902060f07050a0b13030804241b2303010302130603020d0b0708060d02100e04090210030e0d031107060203130b10 72
    0x984901d0b080d407030b143c009000c940d012241480411070310818050341003010780103540c1c0035210300004108591146d0307001d0b9000304000c0119918210100b40501c44d02e0701c0a05280c0604016100c400c0400d140a0001e01b11a070f0f0207003400c2120342c1c0c0356081010b54440700119070303140105050007944c031412403400ca51b441c00407490503500303e00104003140c1e03c115007038100501e198140e034413031443d9161078441001a03a412641507010b00484056841d644840340244040d800c00303c0c411500c00500200c028100c082c5051600707401120f2a05000ba11100100c10b40b8103494055644000760380c1c8040c0c1c15402070507240c001950010f0254810800c000c076510b1800d00c140003903626030450781c40300c3e010f00440310410700009501129040c0c1540d04035109082062280c3c00050010644040c00d070045080b9580c0c0206d0740000a4940b80c0102c1031001c10051030000702d146260801499890f05d14210312800741c1100200140c0d0000045400701c80396400b42c400b61504100c3c10b4146061500514508029038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 496155665 1250 496154415 496154431
    0xb0a091523150d060e010b0904080a0207060203091e190e01031514041101020c0d06020403051507050f0f0d140108060106180312091d0f060a14100e0d0803 68
    0x7500000c0c2940d03500c1004486940806400820760081541c1c54801070410280300c5c100c02c3d942e443c2d240582d039541303c2042d4021070162103480d0351030440da6002402e202298011005551082100e500070fa198507070703802c400641082c00c404c0480310010025940191440c46070f40c0b070540e4540f001c1000c2c0840561a0b048a214000415503125003424150503541d5401145908041c0440014040355200200e520035010510644450320801000a0384e004101d440a88078907074080740900811008108ad0b40080c6805090070f18540341901340100380d4440c40f030700707a40c00c150041003180c2c0580984042d02c1c6802c0b5000414840382c40c0c00080171142d40000d100354803044c803411000048a5000329100347d00390407144107110034075085440b001482440c0d086218208502c40074001401300801e402c0380d107030340107400c4481c8107400e00014802c0d4403480a07110501c258402001005038054420030b041c0307410400e5483d20040805c0c8401a5190071103842156001200f8901c8841040002c0000714407410708 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 496156915 1250 496155665 496155731
    0x9010905030408420a0209100e0301050f06150a02100204030f0605390903030318070f2402010902150408070b182202041d0604090b0a0915 61
    0x2140d000d00d00c0c0d0054650211340102c0d108100550f4001d09003195020103816005880d0150b08404500b00d94907100003500042c074883c2000710701d4a002c1c024250851a1802c01c410103080a400244c1aa00c1e00c03032500300c40708400114858030341d000f4841c02c054400c10310401c5440f80d680b414800811140d03844100e52292030700b00012a002101d40785081105245504203141c1203008090141d44002100b1380d1105503014000d2407815a001c000640c0318040c0651561a41417061406a00c1c03d105904020400c118a00e802e00240704140d0742d5500105007a800141100000317142030340105032100c0d010b0741050010038802c42e0304240800034821030380b581003155107040e81c5040d481c0c95805000004030a0050075400d40c807803881c0240080d40c5078224180d0b040e1480c0388030b03003210040764004d5018801480c1044418100d0b90254208590f01c11b001351824001c80c90707107641e50124500000c040141a0340c1e07500c495130038070002d01340400030b8021198003004013400840714040003907115400300540040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 496158165 1250 496156915 496156963
    0x7260412020111040504090c030507060e0307080c010203090405040609210f0509060d0203040317190c05090f0120010203010e0a06170c0114070b0a0b0418051509010905030408 77
    0x8414422010b100d09070707a0045040c05e0600d03007004040c04140c5415140560300100100100c0c0040c08803600030100c2c0d031680389594403588245814481558881d40440d0011211034102d40d03008011550702c0d802c01c5030001981c5e070740c601e0301c500105072072400644541c900045d000708028070100704190641c43c079119440010219482164580308104100d90440340038030034400d000d8410b402130740e00140303c0d04081c5003550548041261662085454114080030a0114240b660b414850b5a441c0c8001c7e1409624091048002c1001109107411050400c881c01c0c0b88072021420483c20b00d0107045840001355031303a5079156168001e0003000e03034440e800740d4a80f01d03000503003041c450a00010500040702402c81c6903625030054078045d8050070304800307030a070801080703002500748411a4842c00d8410400500b0304100d0060004a503000802000e00481455440340460800074410200c1a03100a00b0380e450307500e079010180034003602d2000400310322011a004c02d040c01d01046900130440d00c01500e00c2411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 496159415 1250 496158165 496158167
    0x50105030d02030708030919030302071104330914010305010606020f0619110c01020a09090b0a09021b07030507030b07030c050d0f0b09010803090405150f060307260412 74
    0x540c50310241c0c0143c0e0080008038001800000174592090000b419100381000720000310603545007080080380040e074009a0441000054845080b24000982c0c0800c010090101c0c1020251011005050741e900198800403912062603d858080e2000140522004540d1561801545801e000450305c035401d006d03011401d14800540041e4461020004014588482d80740010800707800c0c070100706560b00d030843d600c41031003000f000b40b6400c113042000590b01d0200c1a402080d82c91160007071045203040540001c000d917606034910040d03804920780140c2e070342460301700e00b0440102c0442c00405401000000000d01401003180004c8038003580c3c008503a969507500031001c44050100d41d001084d010301c1004a2050298840c2070701d5100000c0019441c1042c3c1d0001e40303100c1090307000c07803195030000494072914107240c010160810030481d00440034240344000140c0306c588a20290307001d2000400040c00301341c41a104201c102800c0c92008c0740700c0b50344511110a0b00c600b141c096820a0054030030040e11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 496160665 1250 496159415 496159423
    0x110a121a03030a0f112d070f1406270307060203030702060403031a030604060f0c03090f03050310090504200d0b010302090c1b01020414090f070503180109140105010503 74
    0x1030000280914684016460251400041000e039402003040d00b5102c2c200010040111040d1321660b210301c1d007020f2148410030041d4010304030b1034115a401c020404c1040100d0300c0b115405443d401e501f2840d081c1c13402d0001c0f9940d4040c00085502c0b210303140360450a030307000300c80225402650690075a0485a200c06040e6031380e00c01510b500300181d00a10010340071034865480402201c00c540500400100e022000910704482030714207541da1540ca50325a1300c40041481124a100c440d1b041c01c3c400e10076540c403031b008070f00741440000c2d083c0b141c00000506003030360101351100603021000080241c0d0038030781013080c00c102c11743c1801e12843c4a1400940454604841d00120640d40078060208581c01e507800c0c00718041010f04a801909001d000c000031040121802c0752040840fa800143c44600d4245005000403455454600a4025009215810f03801519065228840b030420650384e1311440b000320b8441c1f0480c207000c4c0b07655282c294040108003880810105d0341100c071300244642e0f600c5404043d26 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 496161915 1250 496160665 496160711
    0x8010807120b0615181905060d0f020405060708090102070902030c27180613060e070807020c0901031101080a0203010605070f02040b120601081209010f12110a12 71
    0x78191540540c00020300350386145600240141a00f011003004503142c40964000740019490903c0404101c495403e0100c100080e0107080309200ca161840d141c081015031080c000560340381c50b1144070700c014040d000d4048034010b01d00a07010740d076541c84509102d03031290800d80f0110b006008a00000034114070341e001b85c90140c441700c0e050342c1c038007104890009058584a80c0c2800d802d8245220038815941e002c0c0d0101c100b0311a104c180700d040c80c0c08000c104000341c480d242068001d150400502100b413110318010760040090401b144551034150003070349032806000c0d5136540a142c40d000401000b80e13444220030070b10420381740c0b03c4058950342c042609030f000901800300010701c140300641c0030500006280407414000fa10000b00220b40c00702003503402445080b48034450b8400401004144010000c541c1d041c02000301407030400c3d1032180005c19005400000b0010007a07047c540440c211240d07400030b03000505181059954404c4860080c04188000c02804c1903240b034545100020140b20741da15075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 496163165 1250 496161915 496161929
    0x307080f06041a011d0a080304080f01020c03030f072c01110d0509010c0804050405010f0302030d0302070c17032122020d0f0c0305060106021b012f0c040204140108010807 75
    0x580040f0b510044540d40c140e004042403018681008213403a80b2020000c0001d044002e014540e594284058645011220323525030003541c1c410481d0f5021201c010060b070760007a01c4011143c0c2c0d661550401203407000350340c0e040e40c10910350804d0f081034102d0b0080b107a00c0459000780caa403c507610540803200e0b2640206a00f8002050081040400641c892038005402502c5a55560b040c241c441c80898115a001d030410001802d807800f0a2003546410480c106500d8042d280651926400c1c0e89e4880300031145125440040c04492000d140700c00040c019a0300c0900303814015101c526a00e5021580d13407005072140355050f001c030840c40d040c00400100840c00f4070740103401c1e440400300690b50fa09850f0b1042209a840801c1c0120100000d002400424000e00322917005140ba001c100c1c80c80031001001401c1641400703002400c89001d41d0b4401c8880c1800b211001286202d03d8001c02454184200c2d01c2c0e1480c2c1c4203100150100d00300034a80b6003800d2101007030762505001e81e02c031802d2540e65191170080d13407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 496164415 1250 496163165 496163201
    0xd020114070f080f0703020c01020d0f14100501050a11010c0e090601230705010608030414010e040b0f040f062601111611030325020405090c100c170307080f0604 71
    0x52010882e0641c4c2d07541103039561400604c0c00086404003400c81e001038012a039000c0d00e070114100300c60f00a0041c00c601940c408104d00590400707034000808852544100b41c14824003041d41980d590140318040c0c044601c0c84000d0280c0900c800c00246403030000710b0b0301845143c50700041402540b00d00310f082c0c90720000d00c10307101081c2c0e4803041500554018030300444041d074844d40082001d0005001600c001c08400302540003031540f1030b00140070043d144200900980c90501c401010f0b644980e04540c502c81d082d20001503d851600b10040980041e030000c560031120209898084051010440016098040204a503204418075002c041c4143c0a0050780c1d0b0f024800e505000c1040d11040d0211190001c0841e45409183d0700541e50340c4804814070700c0500c0701144030100b5801d25000b442d6000c61800080e1501c0b41c3e00100150700c2c6a080d40d0300504010104006c5820818000d0443d002d0001ea409019143d151088005201c1c040c200c0b080748501d404d070004a25039040c180100e0000c800d11410b50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 496165665 1250 496164415 496164421
    0xc0b2a0c0d03050c070c06053001030308070c06020a0f0215011415070c060f1b05060106232a24150405010f06030b01020a02090406020c0a050d020114070f08 69
    0x2c40251101408811030813030704020003000240c0007480f120043c100c64131096102e05c1000d20f507131480410f1000e00007640004002209445080c1c0302914152940f40c18665a1070703e070030307c08540540d588a0000e203403910014603003803030b10741021160007540c28507800c80d0300000c3c104040c130401d04020300c1641c2c1c19460003203c204292a11580d00525181c01512040c10841140c445003240080fa81c8400040340600540706211503000b20480d00036802070303c00052146c0c160355003035500c480500c600d50410400c9101c0300b44518001c07a030003030800003050f40c5940f03900000b440104641c42400c6035a0f00c107041140c2601c046200030034062541c9154914100c0c01c1000481104144d010040052104600c03041c035440c96613175244a218040c1c1105000d44440c01e040101c05402c455100070780c0360541d8042c815003401680c1d0901c0c2c1d075521590148000d612448841c1d140c52414020b218001c0150141030b50317400b809541544120144003071115903100c140c4400c2c0301510341403143d5015800003481c0c1400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 496166915 1250 496165665 496165667
    0xb070c030f1a01060807110a03080601080a02070203010e030405040506101d060d14040605090c06030109020d1e020705061501020309012a0302011406030712030305070c0b2a0c0d 78
    0x5104140d0048540504002d003041d10340b50103000903040000419200001c0c81070140e4404c8203405480c541d01c0092071410480d8a000d01402d00050100e030411003c03200007410703441190190764039103901400130303c00340141c481010b460350014000c02c3d006510345000940c1914100d010450301e00798944070560b03c0440c0c15541c0040f174003c5c1b0401a0007040400602668001c240304002c100452000004030504203840c03c9820341f01c0107084204282c0c400300300030740185d85007401c9a04541c0703482001691070f00c1501c0440050030751200304e51061104a90b546100a100380c0040c894284200c00343c61103942c0720036600020f40e49075003210340160300512090b5107030350207510500c150f0030444941d00b11109041c0d0490504000202c4104d0050351656000143d00b00c610b96200d17004041100940040e40c180500c0c0d034004404e03241e010781010340fa2008614a9405503001503109c0c1c1c1c001c50090030030301e00401841280d20100003440c0c0d91008100307400000809000070f451008100c10090701d4480da080c54 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 496168165 1250 496166915 496166933
    0x40201200105182a01030b100804061103061e130e030406030c080f190e01020423040c0c0f1109180615130c1713141207080c030c01090303150b070c03 66
    0x2030400c1c181903845c02c400c0707116a0b17000d03116807441c0303000e07914242275103468a800410b41c1e1138060701c7c110340c84082c4148001c075a41d1240c502d2a60420802c032005036803c80300024640c3c2c1580070841842c0303280040d20903a039440403000307006407516528103004020031a070b4221000003046800880350346c0d0310340c0890070b0040c1c01d50007403031010400311001c140c0364100140304d0b0880e4065845903142c0d101c0d04150760403800644c2e1101b04001c0b03046401700844000820045c101140744540208040181c00190b01001100c07100a040c120b000f503c12003080c500000009012154601551440d03c540c0c400516031555000401c4036521f000f81031480c440b4200000030029009204003801442390b03076500c0e44840f05900207000c1c071031114500400e02001306c0c0e08215907840e959051504d242d401000c80e81c50400d0f03500003241c00d0396901a0032107a559882e00f201a0550083c60007546c0e941d400c081c1010f05059041c0c2110300340d50221901d0902d403d40d034040504451268a00c024030f5280c1c010303410800310b04040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 496169415 1250 496168165 496168243
    0xb01031230051807060503011e0305060c030408070605070203090a09020a020c010e040905011a0f01082404060b0c010501091b02100203090705060f040f0b12040b04020120010518 78
    0x4680000c042640103c00d07400c11140340c05c00c000180f03000c40104400844e600215400100c04041c14160604680310306880e050001c2550304130004c0000882e0412408a007264030356034102004200c02d00788444002e40741d500c0601540d00c50a1012030100d1820508d02c2140c3c003406947e002828a20b00d51401505c01c140c05003541d5901c0781e65101c0316408100d0a010b48802e01802038030401140209008000d001c2c0401d01c101410400598200310b05208030107101c1441401f10101018030007851390000340502010340107502d6100d40421400014401504694140c030542c5074280501c80410510b00c5861880c440c0000040e0301c00440c0700003c500c40d5000f560800c10007002c0c0c8540e01e0712040450043d0f4011142c118070250001000c00488040d0070145000d0a4000344040c0350001c0303d0240718918030040c2c40900050161000305007103a01984030060301400d080039071344081540c0b40d400c40c024103088440c00d002caa00004880d441c0d10004c0703044e0707400e99075442c5c2c080601c4803101661030341040d0007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 496170665 1250 496169415 496169431
    0xe060a020a021c091a0c0106290723060604060503011509050408040f06050a0f05030106091403070e090106061806051b280318180f090b0103123005 65
    0x80940410b07405164100c4c6070340705d90070b001d52665528000304403e007140c1e0310b980402440c2c20b00d5449038040d036110704803820141c540c043c082034640e680b9060003030183c010035020025034648078449200d05100850340341e00c94441110104081c0e90340d40107141c282d42c225000000e020070071300d0090120003c664802d6400c14081d141b070f0b60429444401c5885264107640020740070400200355080344546c84480740070100564a826425540b40c410003421402e4240542c03580e0104c1103800c200b05d03880c02c21900c002010400b070300c0c0001e400e100803a41d008100c103000700b4000402d000d00260013802c840c0b08042c1107030041d036030b0103140c075801003509880f03500004c68004180c01141403c084519a0303050221100f40c1c2c0a045010403425840e000d03002142050700280544132210003086800582c103a2159290440d0381d0100c3c40c1020b418001d0b00404c42588010650800040044144100404140401c1150351621036184648600d001d111140c409460b4102003201c0c031801e81c07030b01c6c1b15070022070700030350310b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 496171915 1250 496170665 496170677
    0x3061306091712150d080a050903070b0c070501110606120a15021c090f060209030703020604080a020f030312070f0e100f02070b160609170d0e060a020a021c 69
    0x440d0b070350010445031610316602c0780a008241d20980000030001c2e00e070460b003c00c1d410500c003449140411080030403688003502049010611442d00c50095045844400e070050640b101e0390307291806180141c211003282d80c8075204280020074194000e121451140c0b5456005000e190707226001c1200300c140b901c2030b114540c0603400030400001c1e00d00344400e000c3c922150015803501000e40760414003c410007800b500c40da0a1540b800b0200d841d600a030301e8207903001000541d4528031390340030a06c0c00c1c0d038503032000303421200004000803104400b280800703602d4401c0324034160004d000310415589008030743c1d01740c1a40c81010045101385021f0310242c000507030141803111441c01904000b0700c410340501030020101e00030280c40c000007503040c05414083c01c8600c080c582002c003428003425204c0b0050000170a80365455958109100444001300302029081402c0c0351350f40c868400c074101400941c0440c10072407089801040703114569000f40c40e02403030a5402032811716011002070408910002500c418092 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 496173165 1250 496171915 496171931
    0x206030901110a02031224120c10110105070f050f03090a0803151203270307150c0b0c0f032a030108010b03071502060112030908010929010503061306 66
    0x10b005040341c20555005140c84829500c150854440010b01020722030400b042c0081c0d881c5503506800951031000da0f400e89010f030520310054900031202c88120350004040d0b0b18010342541c0300590350352102e5000c000f8091a2240304d400d807004a0312038081d00110b0403e2001d8603640c412803018503480144001192804099611200303c2c5501c02c2c1e07106141807440d81c00110030303410100e00e0314a43d444808000c45c500000d002071000d4000c0d106402c02c12064010f14500d60b1360307508100c2c0c2c9001d00076481846058030000320000d403040070b5244d01202d07456868000980700c40034410540c1c2851606c41d80103459036960070b100d00420701c103200b00c096800c600c801003800415251405540a0400f4400000302c1d210081d041503d00b064130b078420310100750303450034021141c1e03808221a411105444540c3c10084124641a21100c03080e4224400c950f1800c0c3d80c140c03d000641c00141c0d02074400e07000c4041458480066409038001c01d01a0a030564406400301ea80200d2030750510b0343c01402500c00203001b1b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 496174415 1250 496173165 496173191
    0x302090703020d0506010914040f0b150a020708030901020c01080a020d062705060a1203120c0e1219080a0c0b04060b040e280c0905091b0a120206030901 67
    0x260544414000070b5020400403004600380c40740035000706003402d01c1c4502d2450320941a035031542c00017138540156221055080350103525088089002e00080c41c00030050300160341c0d1070303207034000ca43c8010051088020000340d0903800300445044c51410790161207052405001034820390000f4142100860b801c101480d6110b07282c4c45030002030880404181b500c1c00e0070030401d0f80581450105000b0045c984018001c0a5542030181002c441110b10410300c51100f6040598aa04404854090003400d2443e00f0141c154002c000342d14000381190040c1c0744140e0070b45c1c210742e209a4840d040010141c50719200c000f00e100b14002d807604441a10341030301a100c40744e4034000c2c0c80d0403d1382c08403101511904485041d140c180074a003410004040146010240400b44869103105801d03901c5880b040c182d00c140c144801c40441d44064082c00348140b02d503007001e6924503511698050b0111111311040f0b031082d164a00704a244d01210310981c00280c2000c00c42e002c2010303950002c3d101c403040e076590380c0c035010b044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 496175665 1250 496174415 496174429
    0x40c0b0f09190512070e060f01030b0312031b09010c11030c03100f06050402090604060c08090603070f08090102030c04090b0f090103050d03151220030f0f010617061603060302 77
    0x7910380c4103032102c1214074040c00c1c4113058400c0804090180c2260000740019145090340302c0d40050708035003200200c051140184e00034001d60b14002c0e014081e08010240d030f1204c0c0c40c000c60044490042200340381940c40008039036405026006c1c0e001800d20080c01d0049151910019401e00b0000d0070307140d80d51608000245002070400e030303100c0c100e62108011490072083e03201c0c04e4001c200607a000d519040004000800a1080b402040c05101c4540c81040c188041c0321f0a0303c051110183c011070b0b880c2801500903020803040c258100000d520781b40011002c0f041802583c0c001c0010802e11414241016071540c040c1c407003500c10f04c1d008501502c4032a025622040c8280c000c50285d001b4000c90121ba0000030180c601c0120f40c01074040c00c0d05c0003000000300c040f486605031500400e02c504040c0c0c0c0303104c8200c4290b5015058a6040c410652000515080824000321902404000300921956200c25500900c5900340c4074038503400600004554000341d0f43d0021104400b40303030010f050743d120f500080382 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 496176915 1250 496175665 496175689
    0xc03210c01140a091509050304060f03020412060b03103b010903080108070f0b0f090d021003051806010e150a09050702030315310e07150314040c0b0f09 67
    0x30340c071382450100340143c2c0700380240000d00d510018070000e09981c440a9680c407880c0309000410030000b00c840d074098429070589010f041e82d000105242101c42c2056005000a890003910a000700351420714501920701c29001c0c0020500c2d8003040d83c1420f80c03e21602440000507400d00d12200d0200d00c1105202803150481c554826190000c5c15410180c00c41e1501110f500000070200c20580c0511442800500340c4440f2420780f0354042e914190302d4041451404c405000a402c00602c10040d5040c0790181c0040c1c1c4641d10f6203403c207201005092440b60354101c01e101c1d91045c030303000307030007043c842802103c0c0c0f4039400360701601494009540c1c03035028049442c201c5001005820100600482c04451401c400004078100c444031803000440000c5a2038103107803010140c2824146810b44000a60341c0c009403c0e07464107000b41c0f4951a6101d00c903224815810602200203031a0210090000c1c4082d06102e004030b800c10000001a07003440010300c02c540c4105040311100c04140070807401c1ea80e82d4080d0f910b0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 496178165 1250 496176915 496176931
    0xe0609011505150409050a09060f090627060506120708060106090b03090606040515100c0c091b050a2a2d020d0c050d0309080c03210c0114 61
    0x40c1509449100459000356401c0a44a5521500f20041d40150882a1826145115400210313a15072224890080c299080000c00050070600f0110740009079511911045004010512841d0b20000c5114100108030084401c00c10104043c440460a154043e03603002d40007a00c40c0c6081c105515101e03107080303526840344200b17078010030041c8000c42d800708802d0020004402c0407400c50411500c2540c403000010075080c040d45d6100c001400000c60341044035220100030b89004218220443c00418401007100c0036201e00311840000516903141d4030031030894000e4812526507405072428116031980c44840c01c48108180b8030f4503000781540541d15001114466807402542c040d4516040341c100c9981500c0c0090104003551398001401249200c1d0b80d01c41d412508000c2c80b02c1e042c60485050717440c542003542c00c000c1d05e4800d8810960402c80030303020b030f0ba03da1040311600000ca0f410190b540150303605045e035100e0511003020341100800050070030518002c0c0081404202d0703420300c440300c2004469503c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 496179415 1250 496178165 496178171
    0x402040b0a0306050d02090708150402040b04050103060b0f070f030311120103060c0c02030601120305120702011e0603030905010309020f1509100905030c0918010c020a0b01080105070c080901030e060901 89
    0x780854051140e440200000e507140521703246036800103140d00400929078000d000c000c10000d807210080c0680040c10140051045407101d45503981c4411a0f0410701400780480d1400a020600e40000402e42d603c01e03586c6100706142c2001070b07a0741ba82809001000b10309264543c1c50401c482e010701c202805501094031005286903240d41402001c0c1c0d0100108442030000a5080c1005a1404510503040d80ca400d41311081c10091841d045030030b4490f40c12501c58401e1408107000c0880d60641103070041c09001a181a80181e542141e00200c900360b1000501080d101c40041000e54040d40018800301d000402e00501001d40d40301140312a02d1540550146140c001103400c01844c0100a00e000580c5a14000c0751391810400400d54400c036003168a0700c112442c80010301c40350010032611044281da03400901c07540285c1000659500138241003142c00340c403550008500701005220312403040400e07968000c0507515a494a04403076110010701410151500d1031045140001c00c10340380160140b0b0000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 496180665 1250 496179415 496179427
    0xc120a0c3809060703020f07020a09090b0c0c0304090b012016170303061306080d050409060605091e0604080a0b01150f053108010507080f092a0402040b 67
    0xc1d4072503000c03180c0e0000044860801c0c01400b280000301d5580c490f0060600680c1c1d220b9480b03002410f4001c1c420000c0d03101d414030700081110526500681a414860316407103000352101c4a80381207034041c8249030851603009000800c20890f90790860003041c9418145002c02c80c20303a00021000401d844c0d10390380558403c0030202c0810f51020840310040c441e45d13120f0f4036450095a0a55103d00c00502145d10504103105802c1c00101c01d40e1203100281b030340c02c084601024083c50050310641040c810810300c3d51400e1000a8400e00440851f02d078500c008201c0d01c103645100362419600401c0304d110f640c01c40310a00010a98842c10885d0340c900d14061401b1251541c0341044808030245107011080c1000110320001d4a81900300058403600f12000096016880160b900341b00c544600e1010440e032480c034480000340c20f81301035210a014500d036599280b855039445600c0e41d0120001d89242c00303035034082089242a10880300c12200d95000e003070aa810620247c3c8001000c2e0780054000c80c0c0030040c00549 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 496181915 1250 496180665 496180733
    0xc010e0406081f0b180a14040209010e040c03080a050904150b1219020d14090a0201120905160b1b06040b041707061103060f01050c120a0c 61
    0x184880040340c06110362402c1c81c4810740c4400015202d00e00000b802c02c8001d03446080e42e040700008540181c09600b5803195003000400150301955250b4145152148420a01c41007500280c800c980282c10302a20340d180c07a4a1300c216460040c419561464180c5022000074211001440d08a0140d5516600c0b4040401000100e48100300002848104484104031101501d400d403260103202c0751000071150348501c070030405a101c00c50481c00c040e1001660b1310034a56160700c0385514110705800040d56030794154941d6038440d812a40680400e910541c0400d03180c0d91508406813841c8070f0400d40d4a240d034038090b218082c011980200c1904000411085648582844100b508007a001d005280504082d00c0e0300c0c0908501030000780c40b41070400704890180c0b003142c045482055201ca401c1204072111031b15130b101c6800940e0f56074845c543d2003000304085d6105005482d011801b4001030050201108100112540840340310b1003400701c0c074408c003404503510300300100070003415051950701110602c02d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 496183165 1250 496181915 496181927
    0xb0916030b071701030b0c0f040b030a020301030c051e13090b09030903010c050a0f03090c0b0d1401050f06030c0702010903020907081f0b071202010f0f090203070509090a0314040504020a020c01 85
    0xa800004050b03100f00400104400e140542c0d081001c040203140d40e091200c4000d4240d1207a41c01283c40780c0800010300000742c209070f0046049a000e01e81e58940940c42e00304001c0e00c1e0f103180e1100e02000300003400c08110780c0341c4030241000d034210001c1d0000b41c2c3d00309682c511200301c20071118010250000b15101ca01418280200510180c0c0d524040d0b00e41141c2e03450181403d28002003035030030160740b15216020800b2603c03401e000340c0030008440d5101d0204001d40000782c402a200f11845448070380001a45040a11140101d210010302103415555095480f07000740c1c201810580c10498050800805078881c400c072540100034942d601d000c0c82c0780c0181c4008195004500c82541014404410802c014054003510740711a40b000c514103441711661070403409400c0c10040c03060340781c0c5400442440d6510f198443c8103418429030940d01207a45d81d00801c070003100c01711103195607500b05450110000e41710b5046050b41088541089040c580c5880c08141203802c054000340160380b110035088500d682040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 496184415 1250 496183165 496183187
    0x5010f110406140c0a060e0c1305060f040213050405130605060a0308120a0f02180f03060105010818100f020c01140702070918021e100305010b070b0916030b07 70
    0x40300c240d1905107400e00080081e10348100c28000e1031000f00e121100f01e5000d008025a00741c01500600603505684200c54603410110383d454030a000c0d10b80d00601e207207241d010740b40c03180c000101400000e030100400d000281d404a45004440c401c001e5000c11a41d55a01c034590040c515200c825141c0c070381500d40304c0101c9502800d02c42c45076210090410018113000102d43c2e02c03510b850048016a00d443d40603001401e12480d800081500220740c0c000d90414a00320b403100604104c80e5020100628070034952140428001d032400034280400188041c6807600d05c200c6040d60342c0040360500c192180d440801c582c0c1800c600c1340d00580010f071024104000b40650400075000300e500e800141000d244c0070703540742c0c80c40c031843c03c4c15130316030b0001e600964902c4c0000350000c1d00905050a00018440a40f0b08040142481c038425280c5103020b5012030303c81d10401d4142c0388c0400c5450303d845410745912a9504004045050030721440d0144080e408800b41240300540c490007098149041410024200700044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 496185665 1250 496184415 496184441
    0x90902030c0304020607050114070509030d111002130803040e040c0e060f040b0d0b0c0406030e0303090c0906040605130e0606060703090e0c2a010b0a03031d1c05010f 73
    0x140184250000141d00300c0e504942e0449143c0c1d0b991010745042405040c07140e1514944500d0b880030040b000e50440000c0c5004c0e1400c4081d41e004a02095094410407013032a22040d46501c42c02d400003c2410b1a17009081c42c000000940c0d10b1315544144c0d56265601980020340070860400a1000f0019041c401700090009512001040d262450100d07014020410940384076507100c00442a41ba1202c0704d05005050b0803514440c454500700f81c50304400e40c003d20032140041d240031401c4407201e4000c0140c13801303068064080d041d4141c2c10300c20000c1d103800c042c00090313000b513852900040d0fa6869071140e0920050505000c680101140200c0d414140010982801072800300102800258850010020b64040e1020000780e0340310208240000d01a05902c44250721230a4940301515100444805410385501e009100790340c0c09505003c240c0078640300003400300f001800c03014404610720b00c09255854010b0864543c070f51441c80e1a144101d1110810380f10340e55070760501170154000d03000c1d82c1c90705030b06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 496186915 1250 496185665 496185667
    0x1e0910030e06040b040c0b07050c03070e0708011206060e19060602010b0127170a0c06050415051e21010e060a030213020c07170c0108100501030c1101050c0a090902 72
    0x844040700c1e8403104000c0c802000303103e00070001010442480ba00d82d0107082600145521095646412941c0b486041e40c903e219200d0f045c1c0c00141a41052855440b80450380d503100d21036440c00564200e80550090b00300ca90507241c1002040f030310b0018510340d03c01d042480214032280d01780c040c40d404443c01908042c0440e410300140302c0c1c00381d0b0416038603e44810208682c0411852500700d01040d48541d821105042400d50800d400000d000070304d040406005842c0e180b603407603032000c00fa6250b1040b8032420818040d42e884807502140128043d00180c2041500c603805150340200f6181940c2c4400d00007120b80d860b88243d443e0100e141900507000d00740a1820600c03d05002c4001403080003035120003032141c5d40902d005044d0f0002a011350b40101a02c1045900058465544560000740080c04070054070400b01d44001c0c56100d03c0f00c843c0984511010f11729098103020046015000c01d0a203681404021200380844003c24402c02d4805c4e50402c03a0162500d62550008007282e507981d0280101c540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 496188165 1250 496186915 496186931
    0x3070c05013815070c0503103804020702010c0c030c14010207210503070c080616020a020d170f0d05100f0803030109020304030e040f0f0b19030807081e091003 70
    0x283d600108114180c00d242c42d0383c4445142c90002c010841c26045a90140903464088414158541180b5003845c01d6610b07019088264100c0c00601c074212409080280c0240c00700740400341030960003464458011f01d0082004103090700d45100b0704010b90300860711108140e00401080c0030b041d40c0700310381ca94248050181c45140646e42d032040c0070310b940300d01035240d1034600420800c030003042200c10581e070044214503003a503030351500c0b901c42e603003229803201303003102d07032907400e40b141d20201c0c5148032194024207240c1c4108290f00c0781d44800c800701c0e58481e0100d40801002250400794405000900201d41c00440c04d864030012445111000e9404030380c0400f0580360034050500b0110076241500d100c04401a140d40d42da06045404002c154106508a4904004144405840e80003c00040d41042c4148802d110080502c06100005041c606d104000c010b02400024441f00c010040c95014181d168108a01c10039800400741c01c81241020b00300c0000707004005414a40b030854040440c600301080688 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 496189415 1250 496188165 496188169
    0x16031d031c02070e070201060504051308033d031103070e07080903090a03030c020405010605090303040302090a15060f1b1524061701050f010e0603070c050138 70
    0x80074100c5240062410003950055251081120038020710000141007003d0400c01e001a000784164024180203608100c001507a0f801c46000c3c1c05000d581c05840313240b0f555901410402c42504503441041101120260601500c084c03205030127008400d013041c568403524500d046101d014203469203c0c003c3d008207200b000580e10305d000040c1e0105450a1020141e95090a0203007113100b1402110381c0250188000301c01e0503400001029864400c1d10100080e0343c0310030058600d4083e10a45a5040d4010030003440182040b11005070405111000424072104001150081d041147c02880c006428071000c9508154010400400f02000e242c10305c190000359211030062403c4001c030030140548900048140d009450100e0a0781040c031484094859120100144441184904085212450340001c18546005080f80c000044142c4441da6456030180c03d104180d00002d0140041c4040c035070507400440c0d4280160a05442c03030ba4010b00b40f84c041038990900310401b0038039100300700c000d140e40c0d20103039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 496190665 1250 496189415 496189423
    0x90510030609051312050304051f0606110a080f22030803040b0a05060105160201050c0105041b0503120d0504080708040b04090c052109120c06060a08061614070816031d03 75
    0x20505c145409070341c99940d403c0141ca04100c04220701c441c02c803007486c0c80940c071065a0001b03085d503010780e4608ca02c014031503510359514007c000014020702410089024281442c4009044152841c520300c0d038540001d54840a0100345035100303a8800000008010400c030b40c52149030751183c002e01c0100000d050407400201280100307603840c070051400009100c150380c010010741c3d8400c0c2e802d100901891410707103032000c0b09102d0b5510511a2a4040e0b2020030342d46408500450581c500807015800c0141c12040040600030260080c1c030710010800109001c0b4606070020805030280000e02da03031755840e04c54004201c803500d510000c104407040c4402c1c400d148100807000905101c20514403805d4441e11005810200701090380300d9034510004400c9002d941c00300c1d1083c0314140c109c64a189603550342c0c009545524080312042061211071007021f02030307405010b801c2601c03160f44510074206401580d03500b5031507001c0c2c500034122a1711103285104040d44075002d486082c4143c0da101181c040a02c01180e56 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 496191915 1250 496190665 496190693
    0x16030b0112150e0a0b0c091f090510050418090b04020f0102030c07060c020310150b0c0c0406080c1908071a250c08161202010905100306090513 63
    0x40300c2030000c400c009001c1900920080d080c01d40c041008903181460f000e9641c0e4401950484450300000c000400030008001594046038019040071700703400613081260515140996910284951043c0100322600c030041c0720703800c0351403a4407a581d650b424454031802020b184503c000707000d81865400c0b0009840d84000070342003a81a03d00340a801b4125006034250f00582d040b03980b641c41080c1d0005a400e80c8807440d404407a0007075064456260b440c070014015200e01070000300050964000c00c00030301c2c410038010200c00f00e10b00140c42d00b0b541d40c440018141c5a413944060403d9200f107403407100d1450201103000c000c0c1c04100c2c160300d00c540303402803a41e100d0856100d51250001d264081821600e460030454207501038070201c0e507102030f000c5456843c0011005200b0b07a12950b00c100081901400001e04003041d81d421002038088030b01d0885e28000b0f0600e0108103e04021003040005030645828540d069240c095403008212a070a00040034100c60000704007014980000c81c1c04400311300c0c4050340c681 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 496193165 1250 496191915 496191929
    0x507030c020307050603090102120a0203090a031d06070c080c010309241506020708060f060108010e0a140106090602010b060f0a0c08070b070309020f0415091e0504110316030b01 78
    0x440d0440301d00010b410010550320254001d48004104500404194010400048080850b01c0651140c80c10f1004a00048540754865880340e0000c20200f0700811280742000c2002504200c4d40340c252012845d9504103110440b00c5446818060080c00c40c00e0180403031500c801e01e0304011030041c6440300ca824212284c207004a1400038801800c5055040d00b1000d95a5100c4c1480520260356100007543d41d000c61080300b0a40c0903601c041102c00409000c051300480c0c05955a0460f43d0a00f00b5a950a080c05024407012503a030b4500c01c2d590030700c0340005074001c0429485400740c052420303002078295003075a5080742c07088d82d080003100911100ca80c152014020b417894500358144d1176141c420354071302c10528040d01f41c00300d0804200c2103591503000102d04510036214010814640400d00060302c01c00d811881582d0030b07a40c02840290266440b0504481d1144405818207002019690071140160303019101841e16824051640c00c0401c015410609642c0c0d90700040351654950000c02e600c1802084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 496194415 1250 496193165 496193177
    0x90510080a050702030c192604060e010c050f01052203021e0c0d0503130e191a0d1104060f0f061112041d07080c090405180708060106090e0601050703 66
    0x18110f603208100b52180e0f613403c1d008842c0d405c104000705420788030345e4401c200d4044003c6140900c1091305003500003c103208203040b05003420f0802c0001e42c1e07281c0355480d000d41008107000f07556020600030480525903850303203000000c0303c1c10070f00080b01c1c131900c1c05942901103184a01d40e002c0007035400201c04141034108040c0417120500c1c0c0102c82d08002ca424401a0702040041521044c02000300090005428254815294aa55011581200608484010455a40d40941c03211000309412660003035040b0602c24000751007100004042840f641016103011900c443d400c1c1071030030544600405000f0f2039000d0307055103143c9681405c01c0c14103401410308105441d00c51f840015010000940c400c80c0e401030440c1c4807034543d440d100c0102c4030404103560f21804540401c942500840d00c2500840361b5560861074200c0311000e000240c080074003482c48022000c000030482440030300010340035011103006811070f5403524000800c0c00302103800075109581c6c0314042c0110760780c10504413148031780d140c1824 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 496195665 1250 496194415 496194421
    0x409150503010903091401091d060d021005040e090316030c0305041a0304050115061b020f040501060206040312112704050a02040501030c1b060e0724090510080a05 72
    0x50248008558000c54040d07007090585010140c02486101c1035031040b80540911004200044403140140d104818a450301c0404d01c1001280d40c42c0c0442d84014050400d00034403e8a5012807950449110000700041c00414144003078041c041d2607075003028204001718100001c03010004019940c2050003400c0c0244980744800701400341d01580c00414200101c5141d0902819014a00e44d1086504660780d5107000c480044645012600d030040e01c51665802d034040c4242105480103028991003a6403144240b0b480d00c6240d40e40f8000c0340d010340b4a039030151120781001e103006452000340300c2d170b00e04006050410382e9524100c820103407003a12581c3c107d240c110005204241105401e203030b000301d801038100010007121011a4000300101c840aa074104604802120203ca07103100c04003c031058900320394280c00120b807864101d20002448001916881e503950b0b0711081e0920341840c14a1174288003030079516645a00200706500820056604c401c540744001401001c003031000780300b85416540c0da404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 496196915 1250 496195665 496195691
    0xf091002100212010e0c03190c02010f060f140915100504030b04052a0d0602070c1e03050c0f01081603110c07091808070602030c160b15150409 63
    0x10042116001d68400c66454800801200c900b40d024020b00180180080124000d0b500005c1120300c41d4080d0681c0b4401218030745100800350138032015040456403500d940d16074628682c880c00000307012017409040e0031440e0861420047c43e500703011a03c9803416100b008040c1d1071040c1204070000e4201c44111600e112404182e44d94002c5410151031390002404100410000298451a21a020050340b0944088039140e40b01107241e07101003a08540d081c00d40c5400603440341c000d020410710808540381c4d07040d01d846040030225000b00102e0401507040d0350030400c0c020280f00b00008200c098408400e040369490000e4021400648110070001110b404a10313400d01c0b0b681b0081c2c0800c00781926580d5072080c1d11342c0c0e554880190103412011442d041e5240641c818071300c2c0c0180044e80c0301544a040c081d10b40c40d0703c402500018074074031070741304100a1003d11500c8001d90101c5a4810314100b0510f0034a100510941e070103245455003e00e9044080b42400c40c00710060310115681104081010420808 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 496198165 1250 496196915 496196923
    0x60912250c080a14010b0d030e0a1a0403120903031704140303010612050a050403090302011d0d0f0311010b06030606090a09050f06100f170c13080c0a09020f091002 72
    0x381040c01180004a2002404640f02240c01d0095040c040c504040740005801c0754419802c86034081440b20740d00340001d014400f04220b40d54000c1550441650314207040781c1c1c0040b0104000c1c0e115000150034010000100c40881b0b2080407071504070549811035a0181001a4103000c0b045503002c420000360411004509005030261001c064a4580d40c0d143d201900f40351040c20748462076400c210004d20487e109110b4548516055a140852185150010f40d00c49015a0f500e88052802e100b000032961100124483d030b40e4403503198103034200090b0500514001e98206940071990405030f0030415681c8080a994000c00c0c101c0d4540d6407221b100e80056084102d83e804032010a08040c20406400c1360306040ca84034a8080d1042541040083c0c0c0c1200e9800c5800203000c080f03002900307000b120701d2001d05407962140d0b45501003441d140c2c5000050000311581c1d071010816501078209100103041c1012072800901c1400c03810350031708103e100b034095540115036125003c2d245004a100846100b04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 496199415 1250 496198165 496198237
    0x3090c0307030804180e071406130e040b15030a17090406141c03210b120d030f290a050a0b0309060c2505032a060912 52
    0x40072200c850b0780d2882d003c20150032a00c01e251140325a031805400851050082c0c0d099107010202801d0850305200e002c0f000840e41c0800141c0041003804600e081030b05480c9071202030029a00242d03060b2900d4a07101c816918001d0070782d03000c0c02d007060032aa52600d002900c1c0448590028041c410081c2d10002d6001c2401000845c035802400c1440c000342600c1007402d0001c00c4c01c020751b0050710001089148592300401048001c00203405440006078413008503100f10700c03007241c02d8004100d195403440000c600c86c1d2040b80c1e00d40160800401411815003520821901c108442c10500c0006180380104008000d000c40c10350000e1214035003400d0681c0c0710820f0b2005044000d0045100c0354450280c2c44954000720f54010700740c40b50350b02142c849854481030712003402030401c0d1459114018103125110212080d41181c807403005004200114145c96105134841c04604800a13540340800340840c40d100c5d0181030b0007407a40211179501c0d205140c0108544800711520342e004040e809943c1d14003001201e0b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 496200665 1250 496199415 496199419
    0x40902031e39090103020d0b0606070c150305012102062212051b06070f03021c1d09100303050307090317180a0b041211030a0309050a06021c030203090c 67
    0xa03948000d008829000d0024500200c109a0a082c0c0c080c241030101082c0280006503100e01190311a0340080d1404181036803043d0302404241c2000318559612129603001c0e00180b40003e007001e00d00021942c10311815005244019580310802c99074081c4500240d203445000c1c0c011400007400034200f09544918080609a8404014401d951101c50440800e0050b904131400e014000c0c4980019002c894203158402e401480f45281c001c041d44c2c1c59843c800301050880c250f006d0100c50750910944101c0703507012508a500c1e5005480d0603020030410310310009545a00c200d01c2e00040c00342035888400003505482d031500340195a51940e66003500ca60303020b940000c2824502c40072001d07281e003030745003e400782154001b00d11501c98208410005c5000c00ca026000d181c1c08140020000a0000849102c8071030251400c403078403502210200e401c00c0700d281c40607404202c3c4881c1c20421814580342c0314004150910180001000079501b0360b81e0008000d600504040e004404500b82d5101400301e003d601c580 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 496201915 1250 496200665 496200703
    0xa05040210050d06030f141b01120b0d0506071e0309080702010f1407080d05070305040f0611090402045f1201150b0406170c16050318040902031e 64
    0x5911f049008015008010801030041448500500c2c103138840005881505071204902d42c680091905c005007210543c60303030710184000301440428024007005020781129a2484486007034860100240450901030400301407a0490000c04251170130147c0d100503a0900c1e102d00e881c0707070050089a00b8000c1c582801c0180c10001982010000c803000207140c0700642d49000c0c80160b503603010035011031b4001c8801508030451040340310300003000b0754404401105080e141d541401c02d03100c0030a0490304941c0100620108120030301c540250a039001606031340300c401281107098444000302000c900304902040e124118094401c0c0c40441c0d000c1c2896020201030310442c1e2007a032b05880c0e980601007000e00362404546030040803a9210f00329048805403041925031250308202240040700d00140217064101d0035200780000c2082d08080400e1280d0180184002c40e1943c103171401002300520481002c51240d40751064480040e180460700206c504144450320301e0100810501a08001e94001c611004005c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 496203165 1250 496201915 496201943
    0x6020a0309021011070b0f1b0105150d0302030307450506071e1106071b060207050a0e090a05010e06010e01091b080a3315140a05161a0a05040210050d0603 68
    0x15030000d4410b544000034401a001e42f0420f010089610741c1029005800c1000040c074040d01464030710014a450101203018443c04001c21160350b400004001840010009095098103044422201800301103c09601d08001642c9441d0165103009510307003a601505456820301590704100854104c000e003050703569801a02e014080341c41c0030550000047c900c5a000700e075051002518000342c1d10050425140b9030f0034504500c4004030001c1c500c103079034801d011211000610a000d00c03c51030032448020505541800000c048071300058100d1203401e03241c00c040414024581500d2401c20b2107d0034a4000c0342c45150009000d0020b0481030340e10925040188200340c031494039114000000140701000141c0c80d40ea0000007035444046401c0050400844c0f050302d162100020301c0110054104035142c546403540f112441004035a00ba0340e482d00f1500f9200d040d600d46500164015420300042103d407a09a0004552803c0040c8110401c00c01041c005082103803984000b01840e040303860406241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 496204415 1250 496203165 496203217
    0x1f1a10030e19051902060d091704030803090f030a0f03051e250507080702270c04090506010201020702130c0c061418070e07050d0906020a0309021011070b0f 69
    0x4402040101d60138454042c03004413000190360100781da198010119840c100c428504680544500c039820b482ca800102c140b014108110340003003005501c02c0000d00e490707240c604ad4003410017135000c4550010790810012056802c2d8000a00f003640801810006075903110591800200d26103900314104441400d800e004014100041c8a5006c080291003841580c1950720304071071034007030907800900c3e50300c05100c0800107141010440008000c0c403045500700034405620341403841d0381507800c0702c0602c40000e010f00402041c1d004165001600380003d525092944d0b01041840c107218ac000900b00355032720307400e190072840b48901154071900940b0034880320909110050940c101036940075500b40c180704003408403100c00b042a4089903010031206006d0740d2228016251a84070440c491191907035101d010000944c144043c0001c044141d0740010350329042d106004003450321085038000e0140000415482c0000000d601c01550315000e1925290809121a85004e01844500f84d2910701d004e14031803105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 496205665 1250 496204415 496204453
    0x319061a04150e0c0f0417010908030a060302040506150a030f11040f0807050108040b070503130803010806100e10050f0409080301031505010e011508060a171f1a10030e 74
    0x207510440303d4400c40e034030341000d2002c8505c91500300d802003400501003040505902845118409659000480c801c8140d5032000c1050748111100d4265030790f6081e051040d0b084c54070406920080c20341d001d0310046034002400780c20f40503400c07601c0304158881c25180b280d5406500700b6601d5060240d000c039217550316010031041285207801813001520032404002401d61044d500b0078012a00042c00e007071607480c1c4140449882d03200072f042038201c1044200c0c03800003e201c50001c40c001c0903000041c100341d0405131001072440550754001c004054040050150110314003c50b0002c8580444903c1c402d040f40101190240500000c081c10b8081d0210001080c009840c5c121600842900f200300524ae0700c503e000c090f1801c080c09000801880d0210303104109001b4910260040e10060441c241c00b5501d03016046092202c010705643e075001000101866486040c0464080c0302d510800c0c00300c0d0210198805413200003e82c0c545c459040503454180c5a4060b0780070086030703080c0d03000303a80d0030a4a40000b2a05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 496206915 1250 496205665 496205669
    0x60108030703030509010c050703050307091d0711010b0306161803060b01111c050a18032603060d0f020607050f010204060e0d120e0402091f09050319061a0415 70
    0x2107410100003803841c045c184580c4440c440152610780c18095552400c540b00e400c02000da005001c40802d0109800100d03144200003900c81c1c3e880420a0300d80f0300c000a08210758100200240c0c2e0400c652550680d4020500c580d100a14140135980d520410204544900c04401181011004588007100b405215040000a0303002a00c5141b015860561465660317422880710441c5c1a22407404044560f11803402480d129810f03180804200d40e2100c000d8080c100d440e44110744424840130f11070f441c1d0003d5082078801e0320940c0c00c10750035031410501040303181e403010500500f00710416911004540d1244259140140c010342111001310901500a000b5803050085074042062800000320034a400e580f040d000c45d501660011301c82c1c460403400e60b6551512049668010780900c001d4040c1d4a0700861068246d00403400038031a0b200380d03240540501e2241c2c2125002e0340111aa10b92110341840104120766071021000460207016001800425444a2441d6210341001003031070b149285c0a07140c4c0c003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 496208165 1250 496206915 496206917
    0x3105060603010e0718050709051206060a050409051c020f0303011d011a1206010302040b070c09050609160516171309060503100b0a03050102070b1005040603111011060108030703 78
    0x480c90304030f00c0145640301030718801ca50400e0780c0f042e42c1c40b0801e1039540043c0e810040e1070030818001e64540c0700180c0d8a049081c0d1a1920b039018404014141c03600c0346580e0000c250a403130400400265031a12a120b55411000b0450244c807c3d0f511180d461081241c880c10038106400c0e00d40f207584a48101407040d21011006021010704800854885014550307841c10342d0708241003c4c50f107070b07a410341012000c00040109062650900c0001035020348000140180d40c4943e54070034150b0b040c080d10303404840000d85124020540c09040144c0c620228a1001d200150350030030503160341c000f501c94205103902c000018000e180691003030560025100184c801c2103100b140c0c041e162520354004c0421642c542c0719080d4150300802003490a55420350141c00740d01b00140c03030701c40e45c41e8994072410300f0380c0e002e0710049500044601c200000c4d1110030300300034041c2004990600500780345844050460a075054140e200d00141010b40300154010901401c00000b0764060300c1d00740d030b5140395064032608000c1d4164 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 496209415 1250 496208165 496208171
    0x60a060e060c21030f0702060f0103060c092c220219050604090c1b0b07051608030907051e0109050913050709360321020f0a03180b310506060301 64
    0x1440140045000c8d8400c102a100900c4641e10310b858101c0509203005824003841711000700481d06111500700600c000406000032211004620307016400210000c044099000b14100040c0e06403480b40001d2a2607601240d01802c40b00300001c01c0034400186a105544c0124001000036480d411034000503120b0b08aa12903024005601400ea044802c0c0c145008090911a44c00200303443e0040011b4081c13003030b4108036000e5200c8503035103900341a030054842e002d540d4410901003201d45010100401890300c03c5a410090346401000680009610f002e0144140103400000710754a120840f2810040e8200040310310580d90340d0744680007803101d140381d5400800d00c0c070030f40d8059640440c040040441400801082b0503a59102140c5c10030700300b81c101e81c11402c40171202c06886400d0000c2c1032507101400203c2d03a161480c12000e01218400f10340343c0e80001407880c41d50017040a02009c150b112070780e0040d200500c2d8000d60340c00c50318060415599100c1c040e0a840710b007407000c00146e0034840e150540c020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 496210665 1250 496209415 496209421
    0x1e03090215030f0a020c10090f020a0803040612090204091208040b01120305030109180b0117070603051909021903030309050d0503190c031803080f060a060e060c21030f 74
    0x4405840300300e0381440c40d5505078000c20513540c01c1d030f8024407000d11000190303105045919086c20030b5405605050b1003600e500b21540081d07141c40c41100c001046010001c600d82450030a02500d98100d603014406029a10258481075494541004040c541e000e41201c041c040b02100140c0041c401340c40a85124040800214007100761459684000f40c068540b1400c581c0391420079805070002e1240e804401d5a40040c070000200414142e40c013134074046020581402e0480300d2585425040c0d8415400c0500700024032140c44082e8070565a10308901c4000304106103240045000e032645c0c400485c2214991200002c1407503070643c0000411442401a04c107010b800c048100d0790740c0400e5541008010301011504064810350740a060b24180500b000f20b40d41c1845080050038401da8201070340410740d440c1c10000030820506101da88424100c803204815410248010011615402039a01450f00050b4070300003503500700501c3c903000031a21f4800f42e00401190702c10071190030594003903c0424101003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 496211915 1250 496210665 496210699
    0x15090a020d052a090a150c060507020307110d02041b050405030c0301022506060b03011805070306081c0504080330061e01120c0f17040c0e06011e030902 67
    0x11080340302c1c400d00c8550380c0003041210200300c154802c0413480e030302c4081910009201c9139041422030290b005c640350380d0740b480001d007025026514000c5c100e204540040140c40000703000b020860324132010a0b104480051100c0c40031800621000340d01c443c2100589052882c5260301200500035142e00307806036000c4024160915080c1c0c020b0f0b80c20f2005400b409600038003030f0500d01010104660003a140030034180d40e11603003200180c0c8203030098200342c0041020110042824000c07a40c0200b6985001c0102e1458000e034503071140c043c051005203001028180303940441c40744003550041e2154005aa82e0340009840c0b4081040b5412106821041d840c05440032002440b40700c14400c19002d4044a50240d40c083d01102d05010028428140700c0b440e0454941c00c0c82034420b4502c0300880d5201c500880400c0c0700c000d00701c5404403030800c41d0b40c1c8400c0c0400001400d20b00c5407000310b42c030303020680f02181c4900005840164a840045040618504190184690541192001c0f038000e0301c0411360715082c240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 496213165 1250 496211915 496211941
    0x2041e05181f020906071b03021507050601060e0a0801060e041703281103040b09060637081507180b1b1006030807021e010207060815090a020d05 64
    0x181d12400000c42c1c4080042072116002020292030041c0b10a1503c51103540720350076611803030981c903c10b4401440c28070850920b04542c05050010050f89814004107541d025076031501400740d0400c001d0018164902a141e618984010740740d0900244040c03030300c0e003200c2c2c030b08071030119025186ea000c0d040361807400068810440e401140000415090a4070000b400e051914840d000c0401155460842c440f08501070006580604c0c8076521002c2e4504041400ca4600a8050602d82c42008403682080f81e00880c01013072411450704580c001c41400c0612010342c62849039510442c068007424016103100790b5508540b500c210721b41c1d04c61810f41581d03000c00c40c80d02e00282c000c04403500401c02c180d04500c0800c2c008201040101d80440300c10641510190f801d0318019841158601e101041c0d020451820311010130900000c0740b59860400c031010300003955888544100000d00c9002004101d1007004402da81d41321100141482c0741c54180102c464000358800803942c14036501c0d00d004502d071030388160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 496214415 1250 496213165 496213183
    0x1506080105041e0209180703150e0c03060112060504020a030f030f090e01050616211706040b0d0b090a080304030c11120d0f0207051806011706030d0c02041e0518 71
    0xe401c00d409541c9006c0b250986041603d4682050320500c1c000000041061054102250500001003102030101d481e40307160401d240c0600348039070003203030040c0b28004a002c404480541c0003c00403845482d2400841d2583c82a44c001618058035110181d00749600003000c0450320b2665a00c0e2030000c0d03590515910140e600f80a2140d10003001c1200c0c2e20200381e40c6010303000150040300e40da16840580c440301030180c4180c80d040b501185d07a6050703055810300c1c40c401f078590260301618140701c2d4181c40000a0028041ca0000904164580c00800d88040d800c1249442c2c00e0b5102d0180782d0780c0e050500700502103660500b0115401d0f13424101c00750701400c1040c2001d092040700c01c01008408400d20054520084901e1750b24214814400e00148a2382c0d44080741c0401818900c4421050a02400050401c0780d6900300e81d0390201742d403081c00035507200042d0300c00e881c8580e4900b010340c40d40c0d60f100080144c100414031009035180c4801c60701180506900540c041c400320010300320400034a10440303071501400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 496215665 1250 496214415 496214419
    0x12010b09010c060902041803020730030507140d03021903091502031806011511031801050d0f021803010c0c0f121106040c15050c0303060d1506080105041e02 69
    0x4031401001403c2c94019980c850710041c40829880104c0d0101c01c0415280d010540050b0b22868003000f0000c914140b00d956401d41e2101180c1104258294840b88600f4400040801c040096980b0030301c44031005c409480750000c0309541c0382c2000d07048014040c1d004070360108a001c20004405034414001e100300d040c1258420b0785401c1110300628080000d40009003021150b08500a00c00010381040c0300c1c4074041e00c0083d0510003000803015004080480c2c42d512861254820400d41c550900d0b00900244c0402091070b1803591005c080883d100030303041803c000c001c000e00100706803d505250560f0300050701d4081e8020403074201c04920840315040d4044000d40398154030104500801c0a80110300340c01c45075810a0040e07103004000d00d03407500300b007158250350700d80504109000303086298050030020120f919256040c1800c85491a44038400030b0301c000d12803c40f10003c00104401451110301e203648400b001c100196071380d2405800b0b00000c40b002c4407515045c12441c80280d11540402d0826030b00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 496216915 1250 496215665 496215677
    0xc020d0c0f02130b04020715060503070b1207120207060c030b01091409090a02030a03020d020d05040506031807090e010b13020c0d050a140d06080c2b1e030512010b0901 74
    0x30390240443c1c0a04001d00b0711a45868100e000391513141c038001817603184d1184074120803402040c83e0200c00c84100340c00541c032a81049001304036100400e42902c0101c203031920202490303201c04100352425040c1c00340704441a400410000d05200c1550311440026a66440c24444030990000441e02c6a589020301d1f12403100e0340447d03e2640c100740013181d5004500b4000c9414082032600024a011101241200107a0080f01a01c00140c0d06010706069254141800303424a8289000201c0c2400014509039041000d00c01409030043c00300a400010a521002000000030340c08903240030342540c00c0168041e010010100303245507814070172590380e60850340c0a0005e06101400460302a4055154807003007107103a81651000e521084014010061140c000203a054540050380b810b105115050300d1090510300804103491200880d02d0b00050080c550001d1040e90903c0c1412600522445140300344c581014a20304041c2c22100400300040c50940e8070680740e03031f14000150903104600010b40042c00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 496218165 1250 496216915 496216943
    0xa180906260c1e0f06030a0219052a0a0f0c09060e041110051e04030c05040e0604120917010b030613110f0f04180605060f031222090c020d0c 62
    0x2030380c0140f4800081d002000040e56610a60001c1d0440e0070035161084110380c0064000c00041100941023410155820058206042802c02890040030105d0f500450f400c104080c0070200411f0013090400d95006002c55403400040c10303c9101d2180074010400d01c2c0d86000c10100c2d0343c0c05c4007002a84910b511100f108044000d00c0b05102e04902480011720a018042c400700d580001590340307101541e50689134441d1140d2039400d03c4620040c40c2e501140c01103152845254100380701141e101c1c0c2c0030f500b280c0421301d01100800e00f2200750303101c1d03800740c001c90f411980c902d440704406400c03281c05140101c040f62815143c45118602d040742e51304000384441c2c50030100121508206001404002c00201984c1d40b61a211000c102a55581c01c0140340c1e0004503042c4004100d1300d445501d40029080d00c0704914114020080b960b40c814401021814400c08200003840e03124070789000a4109180d00c4060301d99546003c000c015084840800700035005025103248403902c500007003004550031620410b6404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 496219415 1250 496218165 496218199
    0x80a0902031009051609020702150418091401150815160e0f060a0507020306072109170406020d260601050a0201090b09030403060f09080a180906260c 66
    0x9400c00c3c0440319401001076103105502e01c1c546100040c10308010140c0d980a03c0d00c1040b00b8000e10910035946860240401e200d58104040c0c03400442e44d040b400000c2101c2d550800540c80b640b9002c480b101d0790b00f40b0b0214040100000c80f040100d600480032a00c503034a50404a6403508000c4410395494407010403200b240900c14040460790701c90141c0688681c40b0f40742c003c00c010358841090a404103c001800c90704500f400c0040d00d81c00000c0380381803181c606000384100c40402c400e242d00d4078025100c020701c42c14800c024002d0140f001001900f5651580e844801035110b662004910001c141c4450500d04150f1014003140c1d1008200030720b442031650b40400642e0140c010390b503540f0840d0342c0d8600316000a054051000c0c062021132000310341707441c035500e400c0090b214800c0c102180340d0708008600b800a88441d05403071013200351742410800f117003c0c1240c03070108135004d60001c00428200b05001030f800c2c0d40705180134903030400d80302409a008030380c25085503504410307104142c00c0300a2041007407200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 496220665 1250 496219415 496219421
    0x50312120a110304030309110f0a0902070812091501120c03060c02030c0a0506011505040b0901030207210918020a0207050603100e0108061008120d180f0b07080a09020310 75
    0x111080026208201c42d242c2141030b001110308902080c0d60b03864010600941d51891402820b0440c0c0103e000c08080010030054815803240c041d401d90041407050421504006a0b001c90300d07040d007070790303114505140340d141c4d1080c156070781e5801c1c42100b10000c180c124000d1940e04c90341e07811000d140600c915503595a40202a4501c080046000070b009500d0452028480c2100040c001c0c130003041c15506101c2c8140c2140c0e00c04280e482840000c1004100c895440740644405070400d00b00181c039000d140c2000c3c51440783c0000300030407040d6071350ba90b558240d030000060825102a180d40d18802080210700200320f1007080354420142c1c0c00743e401040306240c2000115801603086044880e242e80d510300b1140c5141d0280c200310000d4000c0070802c0f14060040d1041e0004220441c020404d031000304a06403590712541c01d03d6141075449501c0e050139a1a0104011501540708503001042c240909010481c10030544101c000504800082030107442c5600860200d2500140645a001400c524a00007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 496221915 1250 496220665 496220671
    0x31106072f0d050106090c020d0815150c0307030f0932180402030d0206010312110c130914060c0d0b0d020a120501060605120705070309030203070612050105031212 72
    0x10790002054041020b407618042d914989210b07900206035203050000010a0314030341202101194000c1d24080d14569000301402d401c000c800185041c0d507401c0d800810707003c6154001c0141c016900103014101c0c1000000100b010034000da035618420701346c045040301c1481c8903102e01c4c0811480007506481b00898113015014050551075a01e8004042e1004500c0b040c1903070b11030700c4201e005181008207600301400000141c0381d59201a2111b581150707140341d0700d40003040e02d0360200700c446a00e2046280c401c02503c0c05240005025480480203040d0f00b101405500904803200340b4054012506c0c220000340060107624842d21403030900001302c0701c2da401451040216035203d003500f102c0b50050789401c00c2c03050103000280b50001c07800c1450f0601a007920025480042045000c011080901e0302c00038183d86c000003103142c0166201d465040440b41003016400207941802005800210250031100794400d031451103c4c14041682c0e640101909c84060065843d200b0404129800320281e00d00c0103558 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 496223021 1106 496221915 496221983
    0x1505040c0206010314070b040306020d0b01031406060906190504060f0c0b180a05060a0209010219021c0206070f060c170709060f0201020409020c0703110607 69
    0x90b55510512020742a10500000c604880e2024070044000b002082001e070744842c2c0b00d0070010020741c0a10f80c8141240c0c0382c80400c8070030703500038003c184440e0014030112029694140500c80f655000c4840e4581c0b26404101b00c094031482c00d058540580020391b660754803281040406004d881c82280200300340581c00030780e01c002505804641c0c4d808a40f404503d4104c0c2105d420107403078920b9118000f0104d0281004000d00030000d0350290580e000240d00b03c91030021001310184a84000d0b800194101c50703103e40342009501081803003100d41e031028007a40d10b44a055112100c1d51060f00500311005031311107003c002915842003141034031110303842c0030b03603401e003840c01001d01243c1d0b07103100d21014460405c00c21200c45000f036068070000d102d428070556599256024240e03e0310a0745c00b0072280003054101c981150b0802d0429038044d240c3c001c284010064021180907215641103082d45 = true := by decide +kernel

theorem cover : BRFrame.Cov 496043165 496223021 := by
  have h0 := BRFrame.cov_init 496043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 496043165 ≤ n) (h2 : n < 496223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
