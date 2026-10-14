-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:49:14.212723+00:00
-- url     : https://prove2.me/submissions/a8eca1ab-c4a2-4a88-b57b-4c2bca8a2279

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 566906474 ≤ n < 567086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 566907724 1250 566906474 566906479
    0xa0b0411211e2215020403050c0d110103050c0c0109060f0506040902060f0d020f0f22050a180209060307110d050a05030a0e0f0d03060f050a03020f0105070825031b050c 74
    0x3081d0ba030200300140e07005203c2e9809020610f0040c00352130010420303801041500d00400413513404c042c04400300700095503141c4004201108002c200c3d50154080c0e0000d0b41c0000758841c00c9400d162800381c030ba5007101c060301c0701580e0440c0c840842007062030292085036003110007503c05000c82078080c4c003ca01144100ba0308020703101c1001880c0c40030385241d941981c88484000710036035521784500074a05000d0b001001404040203041e01c0860108100080c1c101c200c500161400c0003151408d6035074680e6070202d140181a42d90204000300180e52000004c51007030b005031315441c0b020059103101c10b242c00c07a07008898040c082c04008420303070036410000380d035802500f0460100e8000d03920208141040c504100c0d030401841800040c41800703030903800403400e580c85c04001c0c20441d41da43d410080075104905c0003940143da000c3d4a040c480d40300310028111580100b90640c41e0000c181600481a10705a501c501c1a02c01a6910410582d02c61040c2684065600d00e007040722119858503920791041d541c0236407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 566908974 1250 566907724 566907751
    0x80c01050f030a0e060c04032114130e04030908070605040608130302010b0a0305010f150f05040507180311011103030906010509090a0507080c0918060a0b0411211e 72
    0x940b44000d580104e908030340c80b0400c3d12841c1c10003144602e0290050701045820040d400c594801f101080c004d044440944d030b0303807a24000d50500c200c60400340d00c103070f410b061015910200440c40e10790b031841840c00340384079039604030100745041041400c18800e5008401000300c10841049056409141d01da04a9003102c1101400740880c5010b900509560f29580d40003501c1c02d400009003c0103510415030309003580018001c1c040e10b4401c01500c40b000740124442c0c542c4141c000e10145c05d040c2d2110b540075083e0705020b41c0100b01c1020300c3d04210440e0740201c07030300140440f802c0c40c5540d0062548002000c3c8000541c29803e1504032151100414020980941503070b0000408803034041102c50403064020b401d0710f90460b103400303499441c0c01d200507599018003a0800842c14000f05000003595038a0305c50050107958803100e005601911091100c82e910031b85440e12048806200c3c8001c0070700492400b003468000022012103c80b000001b8a19011300b400000c4c0ca811894844504d664000011800708 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 566910224 1250 566908974 566908981
    0x9040c0515121906050117010b03040314040f05030106050d030522120b01090b030a030804031d1002030903120f0d050405013206060403030f080a0f0c18080c01050f03 73
    0x581c01409448100d00c100d80c0c01c0014002c00c55000c0034101581c40c0c03025030902c91240c883c0015039009010681c002a8000320500405c04030144402864200d032192410034400f60424450700d0380343d04982c110b1405183c074114100850704d000d10804000300b4040d070301d000c1003074500c2c2c0300a02240190070010700129999007d2801d40010400c480c0301a1a285415002c8041903042c00c0c2c80641c1c09000d846283c620301501c20b01145000607030340014542c941d940251581e02c1c0c1c0e03021642544244020480f001000c90120b2466888105040081c000da6000399200d1426408140c9064601001e00010207800c10468541c68003e0781105d54980180030003049079120340c40c2141c010160541c007111558068a45402081005810b030540c3c181031904440c01c1d074a03200e04100c9644603074070009000c11005181440741c82d0003012150792145180340d001520080e0f85400006446440245100055982400c24080c1c3c031480c00c8100a403c4110040455010b0314001a0841c428065002141100070001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 566911474 1250 566910224 566910259
    0x10050609040b010c0507090609141512120f0d0506010f02211608070c09180308041a0408090103060b0c0303040f0f0503040e0a0e06070207170a080f04050301060509040c05 75
    0x1000c04c070f41d010085840241d0ba94110400800c00383c000c2503001428440d104a030b0f080782e007040c68012090040590b5405245030100040c26401c3c2c1001001c50003100040070a601040f0060090126501c0c11140d40d00024007500d030444a0040a05040c03040c68920301c04680e60004828500c0c0c004031520030b01c00c0203903004021441c041d1407044d5444c40440c40d03240d0100011305005d0003020340318a03404041552180c21a00503283d0403141698080c10780224900828402c2d80c103560000c0c05801c100354111070746000f0f18612039040b102078440c6c641c001400c00c07080d40e140c8990002451085c244a0510010110854580c40050005021500c003202200240102090015200f6034041c04907580c907660355060540c440c00865645418602e131000440ca11940400c0080c819146a80584905420458011a034924a194a07070542c880c1122000001d21440e0051403484407041c01180c40d00c0c9880101420b643d5107400841c01054200d0034080010000d00c5048142d840c00c5558401035895500d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 566912724 1250 566911474 566911487
    0x901020f03040606080f1b09070e04141614070b0a1b08060103140115210e0c030607020d0212030402010315030602090a05042007261210050609040b01 66
    0x8480328004001050004100da294045000c1301e66880a48003800c29144a19032103a54106d8451001c070018039000e00c0c5842d1030800168000000d04000001c07840304000f182c22114540d1900044124060600c0075481d03c0c0035440d408818186803816182500b42405d01943c000d2507001081d81c146100401c1f03040310907420182015a501e0f290841ca00403a000c0181030180c2030b510036000c00d14000c0c82803c1c840c0c800032024141c561074590800804208802107074094800720340303604601145124a5528521401440c0c030000c1c58070010602140240101801c001c400b411880965000d4060640c401d42c0104115010404c800d054541320740e16030006070060241c5420b00b0948001c3d1500c00300820180b61f01900c40c0c00d0054030042c903031603150020301003158965080b103561203030b503120362550001d225002450300c40e20405200e20040c3d645085031004c1d25100c0921000078101107001d20702109420700840d480110401c40340d040034504808a452807081d900d40b28000c540391003642849034000e05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 566913974 1250 566912724 566912737
    0xf07020a0b0f07060e0318010f0212040b0c01050112050a120c05062e0b090d021909090308090a0c0e0405160e15010804151806020d0911010309050a060203090102 71
    0x20841e42d0711058002550481da020310301c02c0320700714507155980010a0000040d52141d0010400d20307041022550015603448048440000440c03103155000f52160041d100a04004d0480c2c1c1c05054840c0482c2c011b650940300e050b00070802c21052900d800f404121f00140703414045401c00c0401c0103041c091401107a8441c0c014001414034410881885151404c2c0760750124030351501641a0905001d50080b128000b2071031188a0010310305000c3e4402c10320300320502260721031004041a09050a03c141b01000c420740b5408200ca0a41c2d501200c0140741d0071481590340400454040c00405215030389806201302d45001e2885036100850002d0b040241c10011500c045012510030070700c4656801c82c6540354981184c480061900c01a4200502d501401815004543c84018103240450001d4200c000f0b10413444034040c001c25800780324011130300610040080c03d8105001191031100c5007410350603d460041d99078101845c2031500c101042d0b010407890446648880c0140c0d40fa2150a107a601900802c4d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 566915224 1250 566913974 566913989
    0x7020f01020c0a0b130b07140417012f0304030e01030b03030310060905040e03030115050403140607081003081801110708240f19060b03011e0b0c030f07020a 69
    0x724144076110003d1040707140c1c0d206444c8402030b03940b12440d184502d03c00500007440d240d101000b00701504c3c00345103001850340b24145101e06040e070740d06003e05009a0103804a40e0344c0d5482c4070507105900c143c45000300102d0602c1c2842164005007141e0599440014006020021282c60340001c0d688280c00452280354028226512410903503241607191055115140c0494001480041c8a00b060300032000000f184402941c15a80f0b00300e8030042c1e8a600c0894001040405c010100015146030280300c10792101500030b004600c0c1c4240007800e452400380c0044503590000d0310410008544100b2929940d1380100806d05510b080001a990200500e40c03c0039035000700b000100300e03c0d9000030390300c2c810040300002401d59074019401210500d01540d01c030151181c1d4000042d0000009803c1d0314440040c001c2c00156181d5030400e1402036002a00000e00c503d01c240d00142d0304400044011014040903c00c0c14603007500f0a4004c2e649203d082e1130b0101400004c1014019503130703000d01d520014a2170 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 566916474 1250 566915224 566915227
    0x909020d08070b0a0507110a0201031d0a050d1107050901061b020a06110c0d02010c080304050a060518430e0405010506030609120f18040603030e010e010201020f1207020f0102 77
    0x114502840f446000721543c030070f080c0c0b4110014000e03512403040d094032802c046000d40040b542a0300110080c002c80704d0402981c000d04000b80b4a40b5000300107400c500c0e0302480280c0842d5200782c00041010202c4020310541d44d04c441000d2180303a48840c02141105c82c28201449003c1944079034940b01e519a48000e9802882d010340000c113160040004504080b42406445240c820241002407085101901178000b4985140150018413400c0096401c207000700c1c01c0302c0c401c8a40c2d40c2ca00054031406c4414109042c00381c0d4480d403501004100314002400c540c0c0e50340c0a16000752441c40544d0402141c0c100307907a4884c0782d0000d41e00700d41e9803020300506104e4890b401c0f02d1900d03007130150180506842046c081d104840c005417030441d0125078000452400e440141c90044200b10016090b0404844074807078041c0821149011345d42c40c8144030045109440b0002d02440c8140050544403480c805071f41903900421098113910244001c407003070388118001114050301c0703911080740780c2703c0000d90241d0650710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 566917724 1250 566916474 566916487
    0x3160e13050105031207200112060914070518040f020405060708070b0c041d0403030b030f0c030115051c0503090616150e370c230303040909020d08 65
    0xa03074001074180c44083d41128019481c10802e40000c0c494088090403009004000102800c6031206010a0880500d001c82000111455000c01c8895a501801c030242d520007001c03c0100d4610652035001c412820b1403803c14a06000600c0030f440009901841641c0c1c3e030071401c0c140419503051b134024200c0640303403d845951616014180d0350117a4030558004154100041c1d40c1c480510486040d165000700c03007100300400d00500552544050701c12000e040e110006405641c074104440040401124008c1c1614401c42c014903007100c01503181030620a001402c24049921105e03601c140e000f001002203196172159042c082d045014a955030307603010000181e141303100c6250f0348040f211a8021043c0314021300c15240c1d850200d4400400c04940c507006903105a120103481002e50b5925142c40521034290b214901d000713014400031410844245401080a00c180440c500200c1e16541d0315040d021110254200001d039070b80654440d50688a4803488810110b460b03031055960105d0380000030580310507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 566918974 1250 566917724 566917759
    0x90406111c02030907051009120606030f0f02330304020325090b0402030f0109021b01020f0a09080601050108011707090207030c020108100e010b0a09030b04030e0102120301060503160e 81
    0x5105844c2d110882c4501382001c5450b207045c2d07600d038915200daa1254039007107180040f810f10105540c44281c50a65880d8030000114401c400864880c5102d1441c80024114610400c29151180c03080c81c4400b07107810f5426889085101c10310030a25501b02c601070b03200c1e903441c40024944681220f000d2449480114200302e0b0040e41088401a101010020321100b03a040090104a01044030320120400452004010a160550090805919042201e0240300c20701030b06c1e6003641d02c110b003030140804000501e41e00c0590f200e84443c002d0000400a040c43c6c0d450314000a005d0300c818001e400100720000c5061292110410907a4018441040255100d4019040c060084a6820000d901283d00000001c81c3c804001e024a010349100d4180c0000340d90030508100c0c00c0750841050a0140700d1140300100116440181e400e00c154440d51300ea20350604464002401c0c04004110320102400503c014011140c11400342c1c2d0b07200380d001600c40076004010104444d840600340300140c1100c401038a81c8001c6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 566920224 1250 566918974 566918977
    0x5012706170901111606090b010e0a0e0a1203051f080313090c0207060f0504081203060a05091308030a060b0c060916050d1b0512031305090402090406111c02 69
    0x45040d200070019620340c0e0b81107080c1c2e05010410100d0460410460000c0b0b0003070701c1040d0302540a0350001480d50321a07079543d84184002e0b000313841d01e40c45c403a08210f01c200740c2c2e001ea03090312080200906211191543c43c8180964111200818161100c1c005103100c0d00080980221a4003201e68480c8a507403543c203540ca0358051028129a01c2c9508030120f040701540c06803c10220700c0340c0c01032030312501e070140403101800d142d440700341005000c110004480004100881d040e800020f22540d4a040ca0403c01c019001680e01140c05000c50700200000901c03003002d02442c0b42d401c6000340e5a03076078691403568010185a000320303813442804903500804080c0080d510788540240411100b04008129800c03514640c41e1280a6000c0a4001d000340000c1d1a844841a00c00540400107440d548400c00103042d413602c0409440b03c0c3e440800c50703144094040e4400030013084261100c8145040a40108940c0c07000140040d0080d6180e0441d14140400350702244c9040400254440c20009038001c488081d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 566921474 1250 566920224 566920247
    0x20702040209100e040f06051f02010e0f16050d080d1e05040b0702010501290d0e0613050606090105010e04020304110301020f091905010915021906051e09060105012706 74
    0x101d2130076109020a113110b11803d01034980041c81a10300344c4400c0348803601408407589c100115526003605183c8540e00700011480320300400081c00c0307035820000c5221040c05d074070342c08144549020380c0603002013010744003100d9a1012440300491000210b40d00c2c450861201d0041d60700291914040106018a03d0f407420f01991541d4002d0045980e2804207071240c5030040d030b074180380310980700c084040302d0b1306200205a4041c20860200324046165086810075104642005031840c0711a2104204201848002da01940407100c1d99141e50414000900d4204028442070181c2d0340003000c9418001c00d02e2a01340503000083c000d65071240c0820b4004029040b00000368006c0c61a0103407040300c02115280780003903c1c0180d45404040345400c04050300f989440030394409500903030b4110080c4100c0e0300d112804076070043c9008121400c040d42510100c01446100d0071508402d00d00340a0b001c1008a0700c5411290246403241002118888100b5000124680c41c5003040d4926800298103401038000481c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 566922724 1250 566921474 566921479
    0x1303080a051206090103020a0510111507020723130b0301060605130509010e040204150305030f0418050405210906030115090e0705031b041e1502010b0d0204020702040209100e 77
    0x6600c40f941809000c040c00e000007540901c0242080c007050616034440320400f03410340381a01d200307540c03191030034100000501035061341c0001c0000c0103201c3c5c1d010440d0000815000b104030301c0c09074520380318005203040030b0300f40b03485006451180c08078850a508500c800884c0200208038030b954441010b0481e80c80810404000e281d074050000d25440c107601858101d841ca80c525500f031340d80307680c00c000081040a003007425030180301300040007042d010400b405407950498007295486042000b0300f00f1418200c5281003429040004106c009030011501188540480551b0f4100e051030176602e0886004400d5059000500400000741c07001c002c002c0f160f1072100da03444e15601e0913203509100150150403035404000c100304001090f0003245100801e6049401c40307035982d081c540c0b15000c848040c1143e00726040c201d24120000e120715152590b48200095440c00200040101c3e9404a5031809416401a22583d40400c10300d0564a86804546080f1002046011020b40d2800007401d00c0c2004640e290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 566923974 1250 566922724 566922757
    0xb0922320a021314060d21030b180403211d010b0a050f0d11130f0b010f02060702120d0b1909180206042904091d070e010b1303080a05 59
    0xb03002545225136041c004150f80c0320b05099442c0401d0105054808504032039081020000c107444600c0c404400c0c51140c41030b600466071040c002e0801160640039458040c0c1d0608440074400041e400030003030017051080c0c00c41d0540828131100a50000c1c403109030844101c20081606d1602c4000c1903118a8482000b15041c840b80c0e83c80c0c400340984001e0901400b60410318100054000ca0255030205009000c010071072503400c9600905e02003a46e076140d04070b40400d604d482e000303612580c00000c0750042554610007060320b85021080295121220903050107010000103041c2e18416464002942d014000303440003480c001d4203d6a080c00806070306c2244501481c0581c0c032516100c002000e420203540040100d070401d818403905c0c0e01c0540c2642100d000109880c1201603155504801800081c241c50000144d50007110340d15107002064a140c03800d9503041600e0030f01000e000400010f06469100d48010344070b880d5001004000e068640000c1d002c450007203465075500d0781c06801002909104032014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 566925224 1250 566923974 566923999
    0x60d2a0807080c0d0c0306090303020726030c07020d020603040b01031502091011010b1302090a06030504080d05180708010c0e0d0507051003090f05010b0922320a02 72
    0x468844206002c0c1908642000e45158402d103482240f40c540c00d030054403440b168540e242c1d2014200d60404800b04e020940204412003800040c0e103544914020381202e034a00e00800011201d55884011b001140d4800086040700035921030b45101c2c56500e5000e4881940da0415083c4800d0f42c0c8400d1008840c042c40d00c0c9001e103066122030003541c0b0540d201604820040d4030910701661070300c4030600011036543d600c0c00116404e81c0c0d410311086c51045a02030040c3d8a0714440180581c1c41c0d00c6170025800c0c5810a0f0600000980c1001103130042c2600c2c000c0007855881d05c0c4014107000d021000440c040c0d1080c1c04001c1040381041d40000440c2d9529111100550281300c02d010b21203d417650040c0054124810801a40c10074842510500c0864030340002c28040d10780e5803070010700300d0340ca096515a54403000303041503091002d001c1d030300011003481c40445c1d0000954129141040108000c0501010140c9040614a90640200703c44030000065400e80743c5040d5141c0d40d0000070809070300ca60440c0e55075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 566926474 1250 566925224 566925239
    0xf180507021b09072f01050105011b0f0206040302030d050c0c0901030302060711030d0e030d050a090203100209041e140a0218150906030106050406080109060f030b060d2a 75
    0x40b07012030042851002000c03034202c0400c821980020b21610522450240b10720654540d444140b4510614960100500101c103080c142101c00503007240d414002181e1085542140d0680d100340c0640d4002411a100445807011030018040c1798002074040c42050064402035810402501d01100e001049803080c004036810410000002e00c00a030158100b100442c0300d081c460b1001340640500c410449140480d40c54500e0221000040c40064541010035049020311150041c0b0b90402031401040c000c5400c1500007986500b0780b280d880781100d90010361182103481d150032000240c00c5080e0560741021454100300050b21a0074400303205401c480000850000051007591031503055469142c0f5002d40640500c0066038900800490329982849200c010340d9a0000860180c0b6240e9105601c4a01e08203000d0009201a081b221150303040c11004d011449a404140c0c1c101da03044419440643c94810100e164190b0205000c0d018410f4400300070038104250464801820b480ca010528131952281e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 566927724 1250 566926474 566926483
    0x6080108060c07111c24112809030c0905090c03010c081302060418060f0f060806040c03021b0601050f01020f07060e03070801021635130f18050702 65
    0x1801000c455510700400711a08110146400c084001200c44101040981b1012405220040300b802c6450181205218200141c0500e403a070450b61415903007000310a205842440c0400400c04a030180b40d00309803500ba511850803500156005040203141c1501d880c281000f51004803a20025442a102d624005040521801e031080505a0701c0d0003031030711492000c0e048106140b1040c0d9110391300707000201e040708980c1040381803c04401000504203290034210f280c040380541c482c4c0400300014400b0800c15400c051555400720040300c0c00034141d030360344c0030039402070107003c251607004680e81101126a02c0c001998605070f9104481c2209080308041c01241c0e1151594202d0015030010b040400090b03006800100c8034900080c00e54a05c3c68072205414226000401000c10b4408450000000c0c800b5080c0d04407242c0c010070103501e0b4004c0890b0b541650403041c207850745214402c00584540300c0fa001541d000d0141c4014008660030787d80d68219040081103110042001510749408100524000030303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 566928974 1250 566927724 566927737
    0x334150f020604110f0310050c0307090506040e07080a0e0102070507050312090607060b04110310051507121409060412110a0510030507020715020a051506030a02040216080406080108060c 82
    0x202d502c04101d205000f40b003040c8010b501007a4042c4111441070542031018040c23140b10700b4086200f5612407520800050000d2803940c405402840c0801c0f060141054120013140d00c5a1b9904068401c0c0e1111600f0b500100122466607100e94404205070341005408114001107030400c90840b01021501c8807064014411100710303580c4042e007040101d0001c1d5141c3c010180740c080c028800140003401c05003200d01030348211540b203d800c0b0075102c14000c41c5444a90809101072010401d0b08045140d612402e40c03104058100d0103011000300c80d2002c1ca0040d40446004041c007400060700c1b40e0380c42c8184c61348000c81040071036100386515503d4509003042c801e410b0851f40010101138400322400810340090101070249400c40c01880400310700a501d111808a00040550040901201d107013801c60074100c0442503005102c83c06e0007803005a40e80083c540c0700903601103030010b984103113840b03085c0348107500110000c2400c440424001182da4000c00c8942c121402d04003900d12603900d2004620880c4502c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 566930224 1250 566928974 566928983
    0xf01050604020a0903110301021201240512010e060d12050a080a1107150609090803090d020c0f060f07050f060105120102070210080a0216050d0306140334150f020604 73
    0x402042001c20341c46d406400c100b013401380006242c50050442058403d2098010340041c4018042c03542d030803d0209440c011000c414503184d400c0244040c0c421124000c184511071a2000880200b084c554498000500c0240c0c40710405003201c0300301c00050910b40041507150b011458010001d4a840305902075105c40301c01d00e41ea02842d0907040e6440d04c80e440c1600c121900044e99031100403803404a58860f0392850b0f070103025810f803280341c10060246030818502c4502e0031500010f04070505d81d00c440707024004002c41100c050b40c951484584d0a05980139504000e4031070300c41d0307510300c2c548203801180080c143d5006441c000b600b80400050325080c0c1c410024004c1d00004c40000c1105402c0c45088440d0300028101000340c82c014078514070708032036045903c081d103039070704002d14040505406216000041c00c2c81c6d1000010a400100040c2d2140b02030307000d081250846000c4600403030b03c86c050f01c002c0001001c8480490684030401e0f5622001d09128600208001e51007111003e800040c3c49031065900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 566931474 1250 566930224 566930237
    0x50306090a260c010506090a09110906010c2a080604030210020a0e041a1f0c08280207030501050c09030604230d1d01030513140a0f050f01050604020a 66
    0x2076552a0310524110316800d42c00b1031400e403401014030081d0000e00c40c1000c0380001040c0ca0034071004003c0c0005011303010365003062511081100007105620307101c00c143c40c11a407034040b5944150060b210080d0b0501d00501d41c00d84180e40314910300040c14900d00f800076584203071040d10381b20840140d880380c054401501591210384800c1c00ca034916001051019998074222201c20140004602581d41e401c40203c00080c04514044e41420721120141100315201451160708480308805000203807910000b5190000c002942e0a01602880e400c01d000c001d82c40440043d041c070b0b440c3c02910f5044a0008403401d5080c240070940351540c640541d43c420030b0041c0030340825116542d90302d05030070329160708481d1400102a0701c160180103210641551190740c50b05c41c140b420124501d6806041d185481c1c0c1030501e0324041c02404240080b42a043c20b51004850a0030840b40b8580c2c2c0c0341c4110031000800107241911210700700b08000c80c02140c440c408100038407445c0c450300304000a9004075555080010354 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 566932724 1250 566931474 566931493
    0xf0815090a082704050106030c030c0509010f080c1902250f06270b0418021204080f090603191407020606060a030609050c0403051c230c010504030306090605030609 72
    0x50502002e43d00090f1295100b64003c2402150503281e09900000209a40300f510f800425010701520760308c003185186c8549481c0c030b013400180629084040348403c001c040c80c0024401c0c50410100e8024a01d000800071810084c65002036031050340c42e480e00f8402a400c4510440b110362089440d09540100c1489034005003040b0741211070100031242c189413085008007060b40c1189041003000544104148166200d041c818a10844400070030400e12031441002810260103a5100389a046a409111581c0d60003050b620b00c0130501a030000541e11038400001d1020203801004801e0551020b00020301c8102a04044100f130700c403080b92800301680010002686502e4408004c15001c0741c9800d0004001d40c85980c20412a0422200321052500009050090010402c034044041c83c54100c0c002c090031a80c10001c10b165818030420200c4e1292400707001e95041c0044c1502c1942c500d110003008145080c1c01c009001d4070f411703c02c1082c5d50345401400304041c02c3c00f0682c140b1900c0707a0030050101e03c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 566933974 1250 566932724 566932747
    0x609210c08070602030702151f0512060606090604090e03130801360606030f050f0d090b07030e0402070c090609060803090603220b0a11090d0b040c0f0815090a08 71
    0x45c0018521811401480749100710740d01c001c2c401d01d0140316000300040b96081d09103a82108007260342c201d5881102ea8450011641e00e0000f190340d0310030010b0f01c2081c0c4a4a40c0c901094807401181c1140c0c0c00b246c1060040359140c500040900300d480c1110311500c120650b135148003030880720a0028008201000b88000f070707280c1921b074103060301d05031450071710809070f01c60ba19000200c40060700121682410020340c201809070400002400c920308101501c200080048040c01c1d0b64483d20611900140c0421500d05160103141040c00459003e0025991004603103482c4120104901408091503e08200819071801c1c07485a1400e80300d42000a500c2c00c10700b0000c108042c0c20051001c03200b8454141110001001c400c220002c10344a21507074502030504200010542c0c080841d00c1e450b0a030f00344001543c5a962100f02244607420005c86a01030300e4500744480300f02c0c0c0c940c0080c01030403d8010002800b802c0061541d0f844d10b40107043d0429600c500242c582c07100305030138010300101401d008110100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 566935224 1250 566933974 566933977
    0xc0a03030f030b06040f08010203010e070807021f0906020301080307140705060a050d0617060f0610090501030e07171b030304141516080909060d03080a020a09030609210c08070602 79
    0x101c004151340c0c203050b0740f0004001020364582000240c0d0350044010419012410006500400d0a0030402202e1821800c001d540700c0000002001c64100c40000040606840e407120202caa0000c00565803907031203144070b03030b030343da000f005e085620400b030250185110740c0c0456101d0075204002e0100c5e02e06007070b441045504d9001050302e5118141c1e20603000030140c0c2c07000700e191502d9850401503c420314142116880d800c40080659000c0c00c01d0f400c55054466000108074180d503c24200080c1e800e00008406d40742005c1d640040107020500004240a01e0001914a06c1450012214900c0e440d0705000d00d900c0c0e0040e8400c5080d842c0300d0030071501f80c9180032800b04a000140352601d504210000380d8440d00c11902450075540303078000240c0d110203400c15010b0550301c03440541e000d030400109650010030000e0b00030800423200b80e000c140000c2443c0b00b90700f11401140c11071000e118100300ca082c03030b1003001c80f14000040140400b1280650550103800c04542d456042181c1505012803501c072000607 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 566936474 1250 566935224 566935241
    0x10140114191b0f03080a0207020a0303050d090209090313080c0a060e01020a050102120411010c02030a0219240f08130b1012230c24090303071101020c0a03030f03 71
    0x5105206030781d0440c00c81e0802c2844401030161082c3c129002180c10b01500d0504060700114507607004001007409030710344000310b0040301c0d0f161504680e90803400c000714005012404009500c0140c034014010a00c0001025100513210500d40c0900d4030380d42d8020726038803025200c4958009540c01d00800c407860190505510302d01c01070040e1394010006965403822680800c4400c82c0f403910b0441032009118001c0000f13800400c086c2450309030315841f50002580c50039107200c001d20448030320500700700300c40da200e4001000f466694a00c14900d119000c11840c480c0a418048000410614602c84220b20814075203000c0c1445410111144455403141c0308800c600520442d4010b903a400c0014045040019101d04c0c6805850810650544480102445980307143c0b545d0481d4019001e1011039a01c1d1000000d4591b084094200c41c00000e11003000726000d007100240d032600010400c4018070664401003d80b0007004d0b429a42d42100c20400c00c1041c0c2c1840c0000380000300d400c1c94924000f402079004024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 566937724 1250 566936474 566936477
    0x20105040201080919151506020a110d02060d0f060b07060e0d0801270b0d060b040e0102040b1602310501150503011e0302060a050903100204030816080c061014011419 73
    0x24107c00c6802c44501c0c407012507102c0001a88000b8121050050701c10306548401c0d02121020600d580d40d800080050003201050048950380c2d03900ca007118641075011600601c0d150a80030f48510041c24100024070744829415914002c181e03150752201e12940d40383d0b042e95845881d0408056440e032001c0004040144459965551206110b0352941d541445081c1144203010218007084044241b1080d00e540080c2c5104030ba0040c0000e0014100d480c1c25250726031503031100001d41e030f0760600020340c02100c8031820140e0aa80c0300390344915000d4281000e084100080320620040c3d0f81d07186500e00d859290a1a50000340050005008401980c1540e007810104400c4600b01140c50341c0000e0ba03c0d41c0400300040101e000007544481600b000d11400808032104002103081c1803031070315102d6441c8500c940032050100000200c1c000c0000c0b40040e11541d0070481c048418515044412200114640c000c03001d050800b41c0414401d5881608880429405d44030304508040d6a00000004200300c54441c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 566938974 1250 566937724 566937731
    0x21e210a0f18051504030212010605060406110c0d11100f0e0402070201020f120408010b040908090d0c0314100b040513060b01021f0b010311040e01121a040302010504020108091915 79
    0x54540da840401300261080880386552540b5500c10021102c0d01040c400b40e5a90401d08100003d0351900c003514104c030b1650600e0b50100700d844031014140b80a0040d141d600c00300300700c001400e01c02043e07080e130782c1c3c0356040d02c80d174542917040f0300c080e682c1102c030843c1c220000340640f4028205040507005414440c1c4103004039800c25142c02ca030b00d810610320144914031a0ba0204041100786424010143c1501c001e0702c040010210b41e464840c0345201e2040d505008100e402412030410900c10401801582c1007c540c80c0762109040c081c5441d4041c040c0e0000003a8100300d4071401c2d0b483c05200d801d008050500301070900320a141d0702c2202a02d50404c0c11030650003104004120381485030f01c48102d142410100003100c410b2140007504036000c840c503502d070003d030512003030040b05d02d00384129055030014038602a07110b14a16020200c1d0440f0800b0f40c031080022000c0c001059015004a40654400d803100070310341d41c0b080d4156a0320700012603400000c11000150760b020078803114034444903c0301d0030344c0072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 566940224 1250 566938974 566938979
    0xb0612030f042c0105041109100807020c01170c030912030901060509062e020c10020109050105091524062205010503060d03030e030c0a0c1502030f0409020307021e210a0f18 76
    0xc002000302409900852b803010200202c8503414418403601c84000d080003280c090054a030741015075402800305149440000126500703000401c0089401a500f01c2400c0e52072034140c900718060802885181d0103010342c10081000352510502c600074456081a02c40c2000071100c490b0080100900141c3c800c0d4056078001c440300752603800a101840b01150004160200c140c0b07801800c40d1001456071344150495a001038032405500d03401034102008582003144034101b16107103004810348004299114000040071a12450303046040b503c4040740c030070300a80c0aa81d44d0010340d8984800c5500c00d81c00b490101c41000003074025440600d24130303030180c2204d080801040301c3c145040500101592011110fa0b0201321000d070221442c449500144065030030203200c450340d444c0078000d900805142a03000f00004e80c0700c80c0f080012040d0480f00203048080c1019a02c0003e40740c10840c010148250600700b035400086820b41d04503540c05103240d40705921030042c880f040b1204d915000341c003140341181d020f00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 566941474 1250 566940224 566940229
    0x10c0f1b020f100302120901060803030606030a0e03030f16020d050f0c010603060905010905060c130501030b06130b03180f03030c1c050c0904050f130b0612030f042c0105041109 78
    0x140c09000081d100140d070780240f11086182d40400a14087c131981c10716000384401c01380801643e070010000d03510242c070383d00c643c9a0500a132811903900d02d40c9200c04400c000d06116241c620a00440e08414000403c0e81140c1040b41c07544160b00522000c1801003160000c89980800102540010361000040c015200e0b078958056070b0403418156540e0703440e424501d003401014420a0340100c0c84150f000c0c5400a0341b40c2020200501c0d1083c50b05040d52040418040d07140e51048440113150300070195142520b80d0003d044a410654180b8188481051611018007000804040c18101000210f00f19a00c1610040e1603503c0088a0f9107448016144c107044007681c4d009032405142641c00043d112400e030000d00c02180d40040000304c014610ba010300c20080d452180b40403d09401c060408a02e540b41000b09641e4408001104001d200004070541e1480400c0058001c0e54401c003041403462034101d6810074601c05820201c2104080c05004122918040d17000351540a43d443c1da4a04001c2d10707100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 566942724 1250 566941474 566941489
    0x170f07091e03050d050a08010b0307170708040b010501050a0c0809060405060f0a020606010507020d12180303030501030c08010c320414010e221d0111040305010c0f1b020f 75
    0x6641d041c0105100c28801c1110602801c1c000c0790b40303441c2072070030301038100300c01002c4000611504840400020115a2071071042c1c82810110b800420280414103049800034250b0300200c50a0f103c42024100104440d03102d00d007203516024140e41c0c0c0c501405240d03124024580d20810405501500400c000245502c40c90045c220964010b1003254540380720110103420300600800040c1003040030049800103135540c6103290744150b0841903018101d41c40d10429900a03690101c00f000701600704c7c200108169258120a041e2481610611801c92751078207a18281d4802c0c000e180040361070500c640d42096030750b071002c1c0362002d00d0301c140f8603514018110f00751072580250408800e88030900c0440c605940c1006403c0d044510640700301a0b00024240416a0a40807001d0342c01d40648508224104803001c030104c01102e15003400800503460605101c0071039501502c82200e1a50800c0c480c103804c54014041e10500207499103171550b001c02010404401e00101000484e03000680041c8000c0540741d040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 566943974 1250 566942724 566942759
    0x1120206131a071103010504150933060b0a0807180e0a02090907020715030213081912050901020c0121330f05010825120c170f0709 58
    0xc1c561590f9070075a0078500c02510400924500a078107100500002494a8603040020206d900000072154600d02d403001c604180100c003031446506400380300d40c090361001d01d203408040740c90208009540d0b5400c500c003240d000d4107140c0e401040c10040000e009502506400002c00d11442c3d00f21003503a183e01c040380005000b900c0c00000268040707501010381c18140c034516001610750000300000d03440c0c602c50045503406814000101030300030461a0400031082e11400207054100140d41c3c00c182044100d0321014045c02e02a20984601c1e4050904503000c0c1007202ca80d900181c3c0a021508203c80064480e0403000c0e0403c040388100d8500c2c0fa55202541c4280400c2410000090500701200e105c0b40c800c401d1441d200d494a500f41180400c650341c0c051080c2c10842c1c01c01e0030031441950b00d600c020241100340c1040c074440c6c46000303411050703100c1d4840c504d03208880d01d00c0e0041110140b1620b084800e5841e11849582521843d0003041021004820180d13018400740340ca8200c5d961500700401c068801070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 566945224 1250 566943974 566944019
    0xa0602030a0b0102031c02181c03091208070303021c020a030b0a0515091306051903060f0c021509031912060801050c07030f020118080c06010b030112020613 69
    0x401846124003960162001c2e54009100442c00e0142034601c4030b8901416a024003c861780c00122040d0a090b956218100400300400460b9861340d01a65901201000d0b1400c07800200d14110101e04002d895411482c26a0030401c0c9a003001d816a500394000d500090701c8500a060701150003c0c51942d90005005116066130003144084000c0305004401d801c80d00203900c200f48a803603c6a902c031030403041d41d5140724200c45400201c40c036104150020191030b004540c204480e107210b0080194544900c004980c8203070070806c80c0c04028000e170030407103d042d076101c8016003025207c1800442c041000d0380d005490701e816a0b01e8580c403d108000701c11140300c01c00c400720f052160903960601c601d209160003003440c90000d201901d069806000e00744030b9564002d0034040c0301010044001d100b50710207903a404568001c441c00803c2ea080c100c1d21500501c81d801c030a0300c608030002c1000e0b0304c0c2c001640e040700da500400710842c14259080007030540080c2415521003540500c0020b5103101074803411300d0403028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 566946474 1250 566945224 566945227
    0xb09030a030b06030603150c04031b0812120f0714040609052e05071b0e0103020429041109060f0913110702041d010f0b130513060b060c0a0602 63
    0xc140003609036000d0045042c80380c4018403c101003510b01082c08000080b006038060801d50b41c2880c0a0340700e00582d000a484418004002403110203c01c1c40c003010341d6081e0084880b80003944014a55512408002c9081a0030782d8020071151b02403070b00e5103504491282000b401801483d0039070403040d005a0b10080016484d0728041149043c100d002914040070207200d840d00c00385c4600d50b646a0790081076041c04200c8001030300c0003441503290865150854806003044074907680c0781105038503482800180d104603d0700a100d4108070003003400700710944403500d40d0f81641e51a4070401c070044c46403161401d02e0354070400c84404507603103500081c00c04c0484420559203a511407010312648061808007001c6007858a10384501d18408142a0b40c2903a83c11280400c4001180882c450f10440361501d0068a60810f4242030f0000481d421252081005035030301d080310000d24188101b1b8131010f40340803440d017244c1f40c4ac20b8080750403900706a40700341016160901c2d000510364814a0201c0605068400660 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 566947724 1250 566946474 566946487
    0xc0d060c170c09100507050d021b010f020d031104030c0e01090506060a02060c160204090b0f090705130c02250f05040b010e0409021507030c0c0f15050a0203070b0903 73
    0x400028054501044107641d40369450300c1d406800141c41000c4602c2c0c4244480440201001d114204844819030300000790382d041590840040d44d41d0314881c0d10b081c04a0094011202694450802e0f1032507010b541d80100080da040c3d520980041c107014000d554800700070080030000c5111660b13184010b1000c04041e401e1076240400f00710403a07078054901e900c6000204000040e6030ba000038816044034103022a682e464000c0044210001c040042c02500181440c0c5541d081c89034100d0014405c0e0310241c9580f03c581d82e003420039901c0e074a0383e02907036034803081d0700c07400792070007600350780040250107007030048400841e43d0754211541602014000040c200c00c2020500040e60100c0200000303000a40b02070140546500c006000c000100c1d0003640103030b644041c44410355403072860060500100c105400d80d03441da00d0900038035410115400381d03030648080e4800201c050701e10442c0c6085408410b100c0b0300c101821941110306034002c013406011880180003642c00700704005816030040d010352008650322a1b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 566948974 1250 566947724 566947727
    0x60e060906032b0c060509030a140a09120f0b01170c0d0804030b06130501081b0d11011409090106120f09020a181b0201051014030a12020c0d060c 64
    0x100001d2045000b40c10203580440c00465462040038011140c81c00b422412260000072940751130180006030110742003030b041c0308980d2000300042c441d031180356032103040441d12001c10028510031464628006852024100881000d003114509000c3c810121800183c01903125148005020303002064105451544000080010406011862340a80d401800c00b031481d16105440d014511000d017002244d0000100c0766580ca48e402070541c000c50030100000e5846506403540c0340307144849191400c50420351888145000d050784005590302010040000c13070141d00444085074025020300d880d102c140014501a5106100580a001c040d42c07164000c581400c60700095030407840c80b80007902e00d010300d9000540c6885c0201d0055800380a00b40c1c0c028404003070004000c102072203450049140314811600c6281c0e040d0851801583d4858035202c4a80d1035104080701749804403401030307041d408004140001038009803101075910751401652851082000426480c884251048070801d9440b0b0301500b029 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 566950224 1250 566948974 566948989
    0x30201060806072a0303021c0b15030f070324030f0b010b031006180902030a230c0a03090c0b07031101270f020303070c03050d260f19060e06 62
    0x7010516180144c80c1210110307501502d18110007840002e502410541891702a80448105030b00519980364241c40c296203020040c1b08070b10203030388a11001d5002d4200841c2410640313006e282c00d141c0602064aa1580070382c02003482416501381c0310140d201c0101c80e400d00307003ea40000c500030708010241c940c90749820600414140c205819050b400c0c03040c098404a0700810009070741c89030a01029442c040c00329a80a03d06070361020032603900001c05c200035580103404c422154581540ba82c02242c070805550310180c20201c60288131601c00348007541da5148039401410080740502c50100b640c688407542c11116620194081d00812000b00802c44054401d1013048401001d0540044a0171040c001c50001403503100c01c00b51001100d108031300e046d0754080c01220f2a050b4410280a00640e036490314039110810701211a01040c002503006200a2081c4d0b203901c4108040694541103a44680c0708000342400940080c0800c440840a0340d02e6079075610a03c009403000c4580c8200a185c50380400909 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 566951474 1250 566950224 566950231
    0x30d060e07030e0c010e0a2303010c0302040803070602090a0b0c03190206090705010804060e010204080d02010e0c06070f050705120c0a050a0f1701090615090c0311090409051009030201060806 84
    0x700b524262a0003030307140004c280307007052010918000740c1441c0341c5c40005041d04140e400103000d4003120710744030800d00f030281c08400300b005041c0d000380003401d020841a4101e000c1e034468905560000c01038400024015401450360510041c41e40280c50b441e02e6540b8000e4000c00c4542c5643c0c0e0000544400030b804250411549200d588010040da15003030030215211a450700c0390a06002c60000404c0800001d5044401d540968100071500c0d680d40346650340c1d0320959021102c016505c5d11a0714441740d040030a0108032440007400052038034240c1d1741c0c1c000c3c074420881c90a4410303000e04040480e06559403001c0c003100f009550020600441800100042009281c1c032040c4601e0803908100300d0804c1c10807044048520a9480e5a0b05056444c1c01030301400650318010980c0e8504104100c40c43c4042d6080020345850240070040c900c0e46c030100f9011a81e0000303540300094814040c40841d494950858000c043c413030303416a0700c1c9949645401c01603406d0540202c0251351940424041d5607410800a5030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 566952724 1250 566951474 566951477
    0xf03080a0623040b030111070c0f060804140a0209010f090b0616081303080403200103091109280501140102060c18060909150307090c081f0305030d060e07 68
    0x1941c54580803614091080e0b8248250b070710303180c1c0e80b55125503456104511030000a4000c1c0641c8030700030080702c096402aa0101c035031110b801c0001c030b503110790300602c0c0c6c05840642d1078040c0d40e503d407038407540c1e103818102d50b261020344941456030b00162038001042d40201007800d45554801d0400003001c003510200280c0d00d0158409100d00c12103610128541c155840e08218419a2044801c02d661001107451b0406088000c00240000401511a1008041603881c00031003404008603801101034035071000000e40380c41070b101d040896030301d0140d0f07040b40c1040c0c10900e0500010000c1030322003c40700017540784415070303550b403001003115081c061170034100c0c000c092018142500d0720b10072210223401144860703041d8813204007081e68940c0395030307089a16030b5400030100a10761410305070115582003110540d6001380100d42c0b001900c00c1c40ca01509491a1040c3c0301c890550381e4103480d901c40b00320301c24040c0c02403e46010b0000040759013840140015203080c0008104241400b00c0d1088900c0c018000c8070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 566953974 1250 566952724 566952731
    0x9061109010c1b08030f091905060702120304080f07030b091f0c0903140a0c06050c070b030c07020414010f050a0b0d0207050c090901091a07090b0c12070f03080a 71
    0x9400d40c1c1e00008196040d5030046026504070051140151100c00c160801c40003440000345086e000d0424201420082004446003d0490000c03031030b25550000f41c0c414030360031400900160300185091216204110f01300001c0341c0c1469a100c20403403405410258041040e00706600c240240030001e8001a4020603100052200c1020121041505985c1c0d1030480d0f240b82e0b86420a00c0118420642034008540111113101102c00d200340c1c4d07544499032482d080398117040d96240011890300800a95842c081c0d41c60280040514055284140360b00041c00369480038003c01411005940b01c0c4140b1072804194001c0000395030506802201a0702a5002284a00154a01007001400030022a020700d01148809600c0368075510b04a860000583c6415500c00740200402001ca0015071000c00c180e4010718628030500340440300c0400d0b10030305449003000242c0014090080588006c020a0b60286810440d00c1020b5045010066500300c02e500b180c85601d0580034209059200105030307005a10b0800c02c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 566955224 1250 566953974 566953987
    0xb04090605101d0f01051201090b180d09031e0515070807020706110a0222052a13052b030f080603031204060b060f13060f09061b061b03090611 63
    0x20380d2411310520032644628180903019481c0304083d04200340c2103a0180c0c80c003100e401d00a40001e02040d80e06a107604510a92a0b1400094401c0c24100304a0340c10520110f00007440344010004844945410b0355684903d0304800d031058103c2034014800d03840d0784d40f1001035090416000342007040b190301607420404105a5800f02d00400700c2c11507a060fa0465000c0c620007070380744c1d82510500044841041662400040188048440b1450490059858003508406800203109c058501840c120b0003070801c4400014481410f00520006031003480c052140806000034245041d00b0b0f002c0c0d0030440000d494442c3ca122410380024020781c02050072005181030560b82400005201401400501043c0c1c440803101c0f480d868500c02c5030b00040f8140c490560ba0090840b2420341d03d182482450002100300800305501485207c462b0203503510396949480b40703004030100d401000722150065800c155070300291284c3c194030349160b203601c42041d1400703d801c01c8542054401c41c2e0b04803950880340042000300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 566956474 1250 566955224 566955241
    0x603040c050114091201021809100501031e180c09140105060304140a0302151308030411012307110d02100809011803020d020c0102010608030405090a0e030a09180b010903060b04090605101d 83
    0x40c1c902f074442c08c0c03034000303800c44248003000c0c207150b200c14a00345840e2924a4010021050341c50b84a8201d0140301084036140d6100f0340c4408440400e045000e02d280c05400621040c5000001550843e0107001d0202c04504c070789030318504141d213440702180542d01c298029108051083c0000f40d211614291707000321501962600a10b52000400041505005035060351042c1e01072961060f64041c01c030002d43c90b2881650f4211540e51101d10103503141100d450000d200b83c546032102001169000e4500c400e03414a8510a40d01c444000d0703d003001654030303400020b2044120320b08000d4028026802020649520b0380060f040a00009050341164104034060100c03810000c110f904840d02503c5822480d03a070800c00000038108003003c02038a0000103000300c40c15500c070304400152044400260b4102d46020602011a00c01072411800700780d298408001081090b0302c46802100302134008201d400b01c80d03031440103c58003115403039103200300b10340c007400300368503082500e0003214810700101e02c01d003840d03000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 566957724 1250 566956474 566956501
    0x30203011103100e07080a15180c0207170715230703081509011502030412080c100615050703112b08041115120a0b0f0603040c050114091201021809 65
    0x43c41e0545e80350f140140c4188c04070b40c03000008010741c4403103406110140a809018184000e41c001c0107204180000c00c4401d0278030030350640000f060000304405c0d490503006410444407850107405002e400c0f101d00340d58500e03100c0b620084900d6610a90703501c1c403880c60080d007000700c00781ca41c10101080003060301d0705450b801c1905054076100d000c50003a0751640c0008902d14416a0080088442c941994504000800016180b81c0401005540030040750001543c200c500d5445062040d4406500c0b60100a02a000030074140c1e009241052202d01c003c034a0a00d0140c0200c175040f0318207140d401403210388540c00c4011f11140540e189c50021400d09480740c00c882c0d11016807141c4140e01c01c1000500c1010224115080020001980d42480c44c01003510001402c40001003030203005034800350b03101c0b40740c01001c0300c0c80303a68002c003081f07003240c10100110388000c0c10415444008804100414943e6254290030101403006800542d85030aa84c0080020500143c0003d0040a0303101c01d20140214141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 566958974 1250 566957724 566957731
    0xd06060912021311160503070501060b031608060109150f0f03060b0315030f0d0c05060105150328020403061d030306130510051c0201180b0a0c050304030203011103100e0708 76
    0x91010442c11300c807007002443c0e44660141d401c1c01c0b0ba248820300c0104500071000d480801d0003400200010740e0766402c01201032100b110001130109411004140f801e010300131194015a0624100c02c8841d00d4409540e810810f4040e044049580e144101324125404000401d4100603490240704561410105550a020242010800e100d000b11034121688007041801003504040c0d00311003045002040280c00c141c100fa1041e01e850103030400114260070024502d02c051009807580307a185540b10b805005403044140300f140b0304428020641c40d0840b041d070000e00302950140000081e0f0f10500d210035148101a050508000e40052007088850350314203102d445041c6682c04081555681c1c0700440000340d00c142c000c25032062681210422202c030085501509a1003a22040d1070264180b80e9152003484d076201e098520b910400642c80303941d00c80c1d0f0f0f55038181c500c00d03001c81e0308103510383e400242500c000e1080c0702c48114012081105180d109200c4e40028501e5000788a45810709c0759009004541c010f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 566960224 1250 566958974 566959009
    0x4150c0e0303040b0f120c0d0e06060901030609030c0b0c09040e010c14030403030213060305060102010b0409050d0f180e191b2f061911032a0d0606091202 68
    0x205d05100e00100d40c90032500158140703041e0300e102c2c3c5418603203104690090035005680c02e144c1243e1003490200018984d001d00c00040030b50840745c1c03840e640c00002e407540e0030040f0104181c441c24100024160039103503000c3d1041d440d2a5440302c2003002804215030303400321104000d82c14038036050080c40d0024010f83c410103240b42c00c1035403a699410250003078070030a0402914800e040800289481d80f503031000f405a10243c0c001e018160383c020803c420765105040180068102c42003404050703000700040031001410303041035600111500301c0e10001d00401d500601400071303040c040000020750650076800003a406a810030102d1040f00d82c01503d980b408071881d082c4806040d4200c4001000503d01040e494440d203001c088454005e8a80e86036907060b56465110101d58044136448a05c50040c40f010302c0c0950b4030716045547d11007401e0300460720880c0445191084051852180b80488010003034200700701c1d80880c030207241020041c6440e0f1b00e9031040700c0300003140c041030005075952041189804c1c8907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 566961474 1250 566960224 566960227
    0x306041205161a100e09060c090301091a04030813051f0608010e0d0806030304120807020105070b040f0309090204061d030f0a0c030b0702010209030d0f0c0b04150c0e0303040b 77
    0x4030070b00c660b460341c54540d010346a030400e010105420000d919003203200300c0f00c0704062000035540e40c140144940f020742d6903491540058000030300c00310640e0040c2000d4072004001240e04005a19103141141d01480c003203041c614280c040000f4982c001c0700c1540c1250b154561510090150785950b501c1c1d09c4040b01080f061246100e07014854406908000041d000140007009001c59001eaa2540d400441c2480d0002c00c074404000b440d24a0040240d9007115200d00e441d00260109a46280465100b81ea00328103001c402d00c1214080744605203c81d00c124818a2002410000350a000c1c041400b00c1d80440840c900401c0184071196114801c0003181c03400e402e10502440c41c03840001e0510700014800d8400d4410150f40a041c8840d440c40401140d02800f030300841c0741c0751040100d0a0303110340041c10381c140e48a08e0700d0814503445403008181c00443c81c9491204c141055540c8610300c0d0080e103007940c4440c50094441c00503507280c4504440101035041a0040c51100303030102c0d4603070103a4407500c0c6401d01c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 566962724 1250 566961474 566961487
    0x2107050f100c0311070312110d03061404090f060623061e1612090609080c0102060f040c0306020a03020304050c04060501120c0e04020c0706090b07030905040c1101050405030c0c0306041205 83
    0x504000717910245500901d01c400c12181c40000510310750400590141d00d02c160483c0802560003403013600309444010301900d41d81106001030001600494100f100c5c030500d40c00d841c0740498541e01c512000760142061020b05018001d000340c0c2024907240e4111300c80c0d10200106c03c2c413400203050909403102c1e41190b0780e444004034011054040c446290281c10308100003481d52440e80d1000b44031090b682c65441d101c82ca241c4030010030380e8541d030f070081a60141c0d0140e0089103108590030042c59002e40b10303a4030074001d41d89954032032040e80c11101c00240402c0d0080107100c2000402e100316001004151402c000c61840c100c0024184014100700040080d0360f40011050188030303061492070850054402d40d81d03240c91509469941e00907128610000c3d81c03d5101041c9010f6202c101c41c4030a03090750311f96a03018100f6040200514070040483c0c1403101400d0702c4203403484280507031842580140003440c0c4a107140d4900c2424074a510b0800d03442604031b40c0810000a19000401c0440c8103180307000f40d1140b9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 566963974 1250 566962724 566962757
    0x5040809130506132306060409090501060f12171b0601030507030b01080706142b060504050901020c37080c010c080403050702010e2107050f100c03 65
    0x420304405a800940101d15400403103034a401440c01071100b503620700c0d45041903009050860780c2c8010901041844c00386014940c2d60380103441904910000c050303a240c1541d840f10a0304540c0d54040031035050351641c0b01041020464100d1000424600408078245000c99580036149520b000305141b040a02181040364140402501e44138600c6c4c01044409a58503030030140d582d208a84003c0301c1c46003000c0008100318801044c02801c0b0703800c5031165400d00c4144a282002c40d004170b800746048480b2039070442c81300b01c1400e24940114840b100002595820b18040c0070a5030002171210b0fa40b80c2c0104454044030340700095007244078910040c00040201013050160440401d43e905400c527400b800c4488090040600040c11a02000700007008054400c4100b541d583d402158003a001c100305001d13100142d4010150702d0007440004180c0488010400c290003203405206c030768400180d00c001c0342072020703007892803400300303038803001c0b0b0700100d02510f0600000e006004420f001003c02c00e10205541c00407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 566965224 1250 566963974 566963977
    0x14011b0809030a080c0f03341713050f0d0311010930030b06040504050405120a0302070303060909021f030209040c0e10092603090d11010914030a06050408 68
    0x280300050666210034403130705009800b0b4101c0b4111000c2d9001d0051140d490b130f140041221410a58500c2440c2c2c40c0c692030180c1c202081c5e141103030b020003800c181c140706c0010f120090002c20541e10300054540722070040c103012010000b95004507000c1d410250464000d5580d00354a5a14030791300d890201004096850000c0c00f411015400401208001072201010354280403494160440c040d44d03e0001c80040c417044058820350644a50001c40800c014405800c0c29000f503688607000c0c10803110401ca6a01c41081c9a6020406040000354041050410180d16007d180001c00101700c003484a20016000140c00c00f90300b400101d560817041c24150320184c0250140c1d000b800c401417081286402c00c03000500000b41d41c0d64030500c102000c0c102c21603594061319003a0151010242e145030000b420f00114070b8480e49540d50b540c6240b00912070b00261b551414808071455120f161021031101c19640058140c060135080007502061046500416440000368500342a412042c00300b0603444509007580c06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 566966474 1250 566965224 566965237
    0x9060708030f180109020a17030c0a0b06030d09050a061b05070306050f06060304050d0521010f060206010e090a200616020f030d020a0605040c0806040b010f14011b08 73
    0x8251022080000e0485120355091281410543c50710a0011828209080701c041c0c0c00020344c07003816070100f0710070718845040c2c205e65450040c04487c0340213015584240f4260001a04841020b0b5040070031209040038448100500c0f000d0500c1128241000005900c044640c09118100a02c0060b21700b141e4212040c0c2c0d401554000b030590ba9402e0301c9042203400b40c50100c0d0611045e00d500c1c07010860350300384502124403072504240501410120707000203c54540c049080d40326122014071302420095424101d250007020b0343c0d00795088c203500e013038000390518805030b022070849814041040a4850041450850a40d00104a25100241e2a859084d200e9000d1009402c0300001c03901c2c40282d070b0f80e68400c824042c000c941c09002a2008030415580e8543da03080c00005810170800301c070000300d0701d400881d04688241012050f0a4641c1685882d00000302c80940b00358440400401c0084008100440903080007101004800890f130000381c17800a825000b41f2002c00d2954a200501c201d503025542c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 566967724 1250 566966474 566966483
    0x21b0102070b0a0e01023304020f030709090c080703020a03030f02160602010c020f060118050405030c010e06010303080c0703050a18090c0e0f1801050d030215100305061803040b090607 81
    0x4a5014480009256100441440740135100d0380300c030941a0307549044000b00b003903412440800c08082c0c1081c1811007c00c01b80007282c11030035079500e8806079a011f001c40005482401800071b1362140505041035001866805030f45c907078010b0380051001da20345460400580750941040d19202c5007040040f403800c070180401b1202000440c10200d40704e84d064018a648681603821245817107000050a0384840080c4200c0301c1c1c4a20032650008100c94a0700025401400350007540c0c1005020784e6400c0c203548600841c0f03006508004014400c15030042c00660300940915102070400d03140da0380c054094841d0100940034002802c6011288040c942e83c0000500031808060201005400000d0007099240e000c85104081c800b1107110a41450419a8035a42000010080320b034a01014485001760101040c0c0440c080c1c6103414200038048a00700e400741c8040740031000e009146043c400d003048009440d50701c5100c00c40001140d41080001580d0944003203018480c0d83e40c1c0d641c0001642b9210b4510003c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 566968974 1250 566967724 566967727
    0x130605010626160f030f060b030105100e15031f18060504021303020d0224030a0e03030f071b020904081201080f031c0b040510180b01021b0102070b 65
    0x300c60ba40081c80002d190000310291611441c020520750342c1c250211040c50651045050b500c2120344502a5024100d60700d00b00000c2c140c80f80000c030803d84469400c9a000b1210010042001c0c3c14911140144d241a525240504c1070b03003032002a41407030303100501c9984120040007180344c1402403615240403001504001141c241c1e1800c648c2c0480c5607168181d0541c40c80c0c0310b0005182c2c2400d00846d62940c2d000c0c2c01ca2801e66003140c2c200b0203040c1c81554160b810115030148481d1a04203074801f0301500f905071140c0750312840c009003600162101d00350714030701c240c00500c140501d140c050481541c015002d41040c581060070400d24100c600040310001e5031081014003408280b1010318000d0000ba46254450803060380c0790110656581c034141440b19499004115200e2801d4140e6160001c030503083c00c3c081090482440003800350351050f10200902c1011080410a049071210a980e5001c03040b041404100401400030391903829642111492880b500c0078003405038406d02244018286d012400d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 566970224 1250 566968974 566968979
    0x271d07020a0206091309060b010e041e0509190f0507060c081813020d020c16060c06020a0306090f0f0609050912070809040c02070e010b0403240e061504110a0203040e13060501 77
    0x52001d058040061404110032b03008079203c505260241c4d4401064003a07500d0032003940011300600418004260500901940046294000880d43e4440c17109d80601c80030129003206007070150800e16168030170402c0c000400d40d00d00000300307208140c41c044913584240b030f00d0007440040070038002910f2400d003503601480005c600300102c0c0d031507001e070192040c503000300c50948403485a40c0c1040c014901555000c640e50529890000d0070680040401004514012070041c2c0d44110000030b5603450b001850201d0745500c5001c40700d40003480b418004224603201030166080c08211a0340320301c0c0d83c4440c82088240003d9560902003603000b1214141c00140007040110a420002034440d25180900c02d0328403180c6000051030050f84003583d00762500700c03600060020340f078610403130003150b03400c1606c2d446a1100b00d4100311600c1888805c1c803503d15000055200c0d4108000c02c002c03a10790012080180c2003d00501004a9001050f101640c041c02a072070400d8480102840084810800040400b420040003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 566971474 1250 566970224 566970233
    0x9091b0c020301090803130b01090221070216030c0815060a0b07020117040f2a0504320601090b190327151109010c12271d07020a0206091309 62
    0x140b06800d01800d045440e990700d9040707903416441000c84244055207451036404e003412440cce0809412041c035004451038012a40c01c0e20340c030a481c07036109407941002400704000b41da130705011701c888000b08c018104010f0700d801000070320541c181d8003a03500f484001061941c00c690041d043c955a14441d2a4580317001c0c541450444190310214000b1200030540784094600520b42d20400030001d40d00403050051542010700f030000400101c142207420898080a00c135021812280c4550021102d0011000704e02c0c0c01000581840c40a501154210104100c0320940d0f81c10596094458466460041841d88a10f40e005034122454001c40c032901c41c40201c204104002a01c0080408800d91700510940e4041c144c020000d002c0c100d4000d0215403004007403000505403049005c1c0701d10313507401d01c6e82e142644118000502e401c204100d0b08003219100017402842c6446082880759403441713910302c149190441c0c00a4482405000090141e000855211845da031840e04811202c14140c2081005219a007407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 566972724 1250 566971474 566971501
    0xf070306080a051605100c0602130e070c020f0303040605120c070507120b0c041203110f033115050d02041d0a060f0501201c0f09091b0c020301090803 66
    0x50013243c20f42c08810000329410320b03c195882d40d21803501c40781ea00720350310784416020358400c01c100704052403800e0000c1401c00030701140c280075401d04da0f282280382e4154030601c4103138542e0307008103480381e88240420409981e0104c212842c06042c0e407080f0049071503400d0100a41c0c000c929008059000d030b45004540c203000300710141060350003161582410785920044507401d02c500d00500c40041d111680030300c0440d01407554800654000f074100c0e1403505c891000203040d42c0144000c6d004d541280078036905440c45d407810030483d80e0030301020000c0d403910323122600c22005100903140e000d01c00d010480b0752070040e5903416a8003d004095800c04914501c1140c0300c2c90000403078580c001285052000301e40c20000c68000c10035a2010385070313421400545001c400c50b40c0e40a8012540358820303042a400440e1941800c10740d03501e07898440034040a4044005400c00c2655040810080e2400201c3c400784107074002507021280b024103252101a0680c0023180c090700500c2c801400150f000010300400044850 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 566973974 1250 566972724 566972743
    0x110d080703120507050304030f0f170907090b030312132907110a05061b0f191b0b0601080703230109061e0b0f120703020910170f070306080a05 63
    0x21040040b0b50340c1410aa17514001610041e0003d0040c4400740e00481c0500d102441c1d600c2d003400c0c40912a21056140c1e40d020304201ca50141c2ea0f040103808001c10f9116000319000c2072001c03030246040c04405200d015002030300401102c465286e40010105000c50718080c4d020080003841006202c0815088490700c440c0140e0f0820006500d040413001160404650345100d158000701500d1152035219030820701d410815089101c6070401c2210b05440c07842d0100421081d00c00c0ca0031000c2440c4003540280c0840f078002000a0384040001c4444002401d1101180d4842c109081c20355580d10b4440c4224000c0000c44c405041d90b0402d09100c00080f8080f0012504903954030324240841501d501c45a103610091129816800b6042c1109004c6985000017406c00303801e252418604045034081e14081044040e25000c01180e400030b2084c009040908841c0c03444045411700401703042020381e40a4641c1e50041c00071640341200c00114070050321a030006002014080c00b100c4052401c2d00300720381c6500240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 566975224 1250 566973974 566974007
    0x1207170406050106080601050c1b03010e030409142a0313050f07050f01050a020303011511120a0e09010b0a0f03020c010e030d0507080907180b04020409050a060918110d080703 77
    0x140083d580398481d07030881e190030100c44080d0140449e40c460181c45052b44076101c9516540382c08034100d031755600304080c200420f1203050104421155909803045010b002e4204414500038107521540c8225110340300960001c00c2210340d43d260340d00f054486070041070340740c0181940980385c1024034807800050f070803090f0343c421904c404104000c04011740d6a441207a0041c80560014401044030701c0c2070b40c1941051070f1250500d804601e480d44001c0f82046a072240414805c4004207042458980c410504c00e03906105540408155041c500c580d0180d001d01c160140401000c40520321115210750107a03915040c408000f8855550001d0300540c89400150003004410720f07000008285e03a2090010310701601645000d010030506046210080d40d4032484025041d40d112404640e2a44891000788010618000001001c0c00c0c51000c2805540c0303542c0c032254145043c03010005640b001d50b8903180145900c0301030f038507442526502280407000e900030068400b5078081888010b1503000400642c503400007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 566976474 1250 566975224 566975237
    0xf130c030c0f0e010c021c0302030307090b0a0503010333060302011b0b0105120a170306030d090303082d010e06132703020c0a2601111207170406050106 67
    0x3000411074403158201030407030025942c1030300682c0703550054410062081c0041d101012600211f8804880d02169400890043e4400010020002d52007031070319003d8594080c200346840400c910080c21400306000207031070506040c4200701000c40064910f00b060f206a0301c450f14541090180b04010180b900c0207a01282803224541c2002442c0c2e41d8020350154070660104982e400c200070b00c0318100884c1d020034800e01ca043d051401140707426455204044009200030354038a4404241814512030360083c42c03d210080c08240b00003900700090a60028042c900c4002a172000c00c045400501a030400c0e0540e03801d104004640c4641d01c42e0384030b00c110300035180068000c811840580445004003141c1c4a180d85c80d01e140100c0000d1100c402240ca8002e104441c2d000c400a4000740070303000d056202070f0070710a13014000b540403071601e0440005050400002c024552848a440035144202804030484280c5003000a14103401014040010340300344908081c58134040c500100200400e02480703000c0f07a803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 566977724 1250 566976474 566976491
    0x102030601090b0f0301140316030f032c0603060105040f080102030a110f07080706090209090c09071718010204031e0c0f05100c29011d0c0a0e0f130c03 67
    0x51030411a068500b08050551451f0f18055083c0e0300b0340c89a00c09039900d4015010000444800c0e401c1443c05103006201d06c402049a0385000762a014104410514800c1201d08100318080020700903011044140c0300c054ae6540c9840040741d0364421900500c280080d0700d1000302c1d50040541c043c52051069400401c0303000d1106c00303c0001d45c01020380c070000b00d620402444002681c41000352865520030b410224608800d41e00141040d80704441c92080c5d644501c6071110240b5012280c26041a81801c1524800c43c4040410030010401410780c244484a0b85242c0e030035080c258101c81c0259081850181c450f00d0300f003220490030408070002c2d039460040920211b0001d406012080032680010080301c8024995001517400300300c456400d0340e0034118240400c1a00c8040542500c0c05545084010410340c1442c040c1c039104028032030741e03180310410b1f8800c109203150103600b180d10300c607010700b030010b07000034010700040c20b240d19525030303c0e00a2000c103030004440041e50030000d1703803401540f801d000080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 566978974 1250 566977724 566977739
    0x9010b010c0818061606020d0c050301050a060806151b07050603060135090c12160323070b09030105090615060a030609110c061e040305160212010203060109 69
    0x40d039400003a0020008003c01d10360f01a0000a400310464040c2556080c40001000321200c0303000c00a040d111140c001030000507550715880b4001d5a45100c0c00d00301c0c11541402c022031001c086074010030041c0210000420115990403804645001c5080c0c00d45507600d180e1000d19100304114000001c180c46800742c04030700c601d4200c00383d07403280e82c0681d1001191040700c890f4600e05034150a25000c141300c0c100410003c451301c0d280040c8202409001403103807c1003030040c003281300052611500d85401080d03051107040301c2425690100e0381c002041e0000704441d0f0102001204072449901c105210318000040e1406840c0e014109000045000f040b1039500c48407601c0e190300080b5401a480160117002aa09282c6030000d0603018100b840c00045294075a1511011220038084440c07003c0303404282c0f00c0050030204819a40a111a46030400fa0400e444c0e14088558010f00001e041c0180440c8118090390412842022540c005020721030081d104014035000758010350b501800180b090340b0229518 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 566980224 1250 566978974 566978987
    0x90b011202150309060a050a150e0106110109020303030f06400b010c080a0c020603040f02030f0304081207290115020a0f0803090102040b0304050d0305130201020a1103030f0a02010509010b01 84
    0x24040d680c040c00b0b0b1a81c84104002c0104801009808c4c0169611804a040508400c0c043c010f0061104290308071350400c0e4002d0415001000d82d5281681030048942c0103807804015290032141012520605444e1000021003c2580d00b2240c002291141020300104038000341e01c80c0c0a0781041d003043c02d01d031304651401e410780d0104c584450105549100b040001880170004064600542c50070700540c0445a001900307a90080e00c0c02d503214180150342c5000e624003808001d0b84035441030300175440c0c545031800c00382d102e507860856050800c3c004180c1100780b0105c03820008490340b480c00720b010001131205002a1441e8203000308884130380800c801c5d83c0c1681c0002010030205800608a00c000c01299a52a0ba641e100410702e1002d035400f40000501e1881402c0918000c030300c030f40041d090010880b000107084800c020564103007401c110f101400580d030080f40a894840c4c10618180c3c0e04c3d640785000c41d141d449010040700501c0070024043c01034070341c194070990150b01e0210091082032010001102c80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 566981474 1250 566980224 566980231
    0xa1509122904050a1104150f08070e1003031101020f0c16051203041a0d05010b0705060601020c0105180301090b131403040b0f0c070f230a030c18090b0112021503 71
    0x100c2c4d0002131880c0120300000e0300c00446420050000c2902965105105220780c11a0f00100300f007220940144020305041c0458001b030a09020036070481d00c3c0680460364800340d0351001400f4042586c0c40495001001c0d0103d80400054001065950341c0d41503800760390701e83d10025550701646401c00842d2500e0310b5940c0b503081450301c0c2c00079410642414203200894100c9101c02070003803020001182408041d0058a000700441901562600c0c01800c00b5030230920002c00950464000184108050380c101060f43d0380303440500110350250081e0404640103112051014000000240c200041a0001340490030305500c0754040200442174645c88958a001d40e02490760b03112070501580e29008401c8010745070340680c40b403c40701465601c2c501403150800582040703032884045c054054500c444c902e402013038007009540b404402855038079450342040442c021b0502012078402e011031048481c2e0000d500c07c41d0043c0002901d5691914845510300b8441d40403809654100542c05c01d9038501d201b40d920 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 566982724 1250 566981474 566981483
    0x1014071218080618071d041b0e04030318170d0c0c08220308040b1306180b0d02070c1701050708040c090b0a090c0e1903020a1509122904 60
    0xc0d00c4d100c11044203101c04404402e5441441800000580714001045e213110550240c0e2402c0d0250a00782030000d01c981c506030200742c02030001c500402c0703c05500c02440d81d001c3e825107030015410401e012a020780c0583d8810207407000c0340030b02401039640c04400003000d0210410700c0401041c28800c60030340c0d4141c03031460084c040d0503050107000c001c3c4481944880c2c841203002d15000c15591655180300d00c0703030400d0700b094054074000700340d50704070601c61038452700508103d0074410b2114002440b000c120781054080c244d000390010441403051f0805405680700030b60f021030044d9080d034441c02003011490000c4003140b0f1560800c1d01264540d8003e26010b40216000300101a0316030410800340046d00d0400c4c012500008141c000088002151040b900e10005940d1601d0380b0381405401c000103a650314002c0008000012000c00041e41d0b007141200440c0e011980c4071030300c00200c8000f40c0782e104881e4403484813411a0040c0030104203011642221902011030360040a0b403010056030407040301154001c0c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 566983974 1250 566982724 566982733
    0x90602280212010e1203060406062a1e05030c011b053403080609090606010c0615090c020a050d0c0b0c0d110c0d0207150e101407121808 60
    0x800341c00c2000480902107075010000c6130030300501242c0c40c904005210207a01031400030040c02100d07e070a0246078010f00c40351070260ba42c0309040d4519a01000c1108117407000303403124880c2c9020021490540606071060f8089401c403140c85081a9440f6805a058a44903504e0010403585503500e40000714044c0304241d4a0a007000d82d86800c0d10300065240c00e003590040c0604e03c40c00c7c10380f941180a40104d43c03203075481603118202242802000323000540b000b02144c00080402ca0140d03404840e4030310403504a000422059039044c4a500b100b03040d03810100110b8101030700701e0103154000509100d8184100221866401e800300c0072100403203040d100409100803d004610ba40e8000005030441e0340c00d940e400034100200620b8005240d02c403518581003600400d01c41d00c41c0c1501841148002c08402c10040c410001080c80100b500c1510043c1501c01d1070016403101116224061a04040002400d03240ea9103000707040c10403d20101c90385800c0012405404207545134485440320085901d03100050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 566985224 1250 566983974 566984053
    0xb0406033b0c031207060e2109040905150405070b0414040e16090b13020f0304020d0507030b011805090102120a110f03010b0702010806010c0317070c080a090602 71
    0x1907101141054540c00d2845400c05a410650b014468546040c580303405182c1e880149290205c02d443e00310302ca02c1201e802646070348804101208c0c2e1100c0b8205503a030000c0c0d40b08001c00000e0010a81300c500681240f141c5d80540754044400f50742540654018000c031440ca5560740c0320a04030703200794000c1c244401e1011003819078906060b000000d414030000141ea05403115141c80c0c41c040c50003913010383d050701d07101c0d0a820818281050445030500c4c1c2410103520300422200381024502c005007000340501c081098040601805214034000b941c1d0026207083d0a5954031140450490300710340c24801c0614080105601d030405108403444070415803002d4026948000b01c010003056402c0c110007104408114910402220500a501801d10300b04521b49491250000505484000340b01d681400b440107101c0c00401d4001104500f00f07001030a40741031a030b50f4501c08580004040d02c00030030314840440c052030b80e150445684410389a9581c01c40da4032403c601c947c00c8189040480c5581c140d816400711 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 566986474 1250 566985224 566985311
    0x30a050a030e060907050a050a030305041802040503030d060f0e1603151802180d1707020f04020307021506061912061220040912080712060b040603 65
    0x9040d5800c03090600142100d1240c1c602818440200e035654415000080d0501c524903010800030050541520110035482c01c55801900728440d41c0a15062186c01c84140b410004003a01110080c21018069030349611004031020003070f200302e000c0d20400e6000002c0100d9602199051b0754030034403e000010b0305400c84041e0035070003084070711080a202284a0004070301c0450010400c03041c4821804016030710382d0700c00340b0000c01003443d101d442e03ca80004009a0003082c1c402041503c480c0c44000750641d0343c6802d20004114035445001280c00500100c1002500ca40102d6040c540c0c407000603401074156900402c010407403107401c0702e0221039509103803070410b5680f00d0014075203809403000000401c90b0322550743d14041c4e02e02d0340c001c8911049038552030200c500c458030581c641c0d25050b00c0510092015544074101c0d00400d085000800140000091105106001c0135240c12031244042109540b2100c0103002940540101ca0200e4201401c10b045c0d00d41440310791064120001054000c03642c2103c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 566987724 1250 566986474 566986477
    0x221151e0301111611040615050a180e06030c221d010509010501150f0c02130b0405010b031506090a0e04080c0304090603030f1e083123030a05 63
    0x2001a01590b940c0421070300c1100032001407000455031100f400072008103142c17003403805110180960140c1e0401c1010404141d40c1c0205562010a60501d5500d0b4564040221607055001000411061920f00c00040241da51070b8540e015440550541d8014112201803148504010a000d4400e039001d40c8400b85028007a804004031900052400c1c1c020403400c1d2000c0d00b9200259504078459554400400c06d10381d40009007e2031107080d0900340384070032541c0c001400c3c901c1d406002a0045501d9810301c81065003d600a02203100d000304100701a585412500c1c40c2600308403144a0302540748d441c0c00307113145001001d64100c1a8002e140ba001c842c100b00c82c928082d50050000c070340c0707580140f1100120002c107002901c081d00110030000784491640c1402031001c00351032840028041d4505014030303144800051513051a0541c145103400d42c40b400c680070350400c82403001c8000200140c0300d42d800315541d0001e41c80500c1c015658064000301c00c14a210726800c05030100b0055134400c21140c14614044c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 566988974 1250 566987724 566987779
    0x1030207031211120a0c0906320c0d0f0206010b071709030109050a1113090b0f04150e010203040b1608040b0903070b190e06090c0105090402040504022115 68
    0x89001342415040103e403031a1401c10713211005041d0300c40d030f00d404245030f121046000820703481ca8240c00301190344220040c000351a0104000800c206002c0074010906582141d007651405000c0301c00200d11103800910401000582c00010300405000251a000d140107480c04680c005080205003d00b0352141e12880c2d1204920582554840090202044081c44031100c814001c1081ca214405610b0800c0341c000c0c074454690800750300e00510380b00030606400c145580540404003050303d075241c0b410180c4a1001001070101307a5400c00e41140e19181c03064000e580900d11036040001c25489000160245221141c10b4200140e00c0b200020003182e21005140d8110308a00113682c038000507034449401c3c4000446c1c4898440000c0d840c0da41c0550b04034414500d400c07603402d000d800d032802c008000f2516070b84221503c5040142c00f04000150380d4590b41160b0041030008c100f15a607005232031110b2220300303001d1049450712001200040542d00d010503a0180d5540051112480b00d100c0f900c0441000700d481e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 566990224 1250 566988974 566989001
    0x5040c090e0609011b0f0804020325180b0d17040902030a0c0e0a050a060f02070e070c051504020306013014070f080d0f17130b06010302070312 63
    0x40002180c010600c103102640c41c01c2030103000c861a0403009103007500c040c82c070600340b08060240c0c80c00c0e0303040c1d00c8019101d118121b480d08012a0715540006032400d035260340f250f035016440c0c4a2540100211100200c01c41e00087d0400004800c030300740c01000c940003041000d40020712440740d20000f0740144903400100c810007060904040d11603c03450102c0c0c2044a4010450b951003088000f8a03400440745010301c01e04581000ca0340d428000030a1b02e000c0c0d01c1c8200c0301401110085128624000d00c540c0000d02a8004440e040340740c4200c008010320440d0f1030a80b03080c0a03182c400303031590b0030040383d4900c280d40150082110340d10303054400342c038042c1c40b0741c60310341c4180c2c0003100d02c1003c0303900395185020324080d041c1301810100c124403280c14a0885c1e40542da104045030000c1108000c041088140500103041c40c0e102000c005074280d6111001070818501c8102e0360082043d68104000014881e9001d41181c00c440d40c0d40c40010340491040f0702c0090040b540c3c038503290841030482e4100b9089002c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 566991474 1250 566990224 566990243
    0x10b0c0304090c0314010909150209040f020c0c2d0d1703090a200904060216050a080406090603020a0509190812031608060121060b0a0503150909100504 67
    0x4a46851044910311003514000a1703c0c0c440d001842c0100c2181d803805040580343c100b004e041240c6d42d034010a0b040e50150140b840d008030303021800ba966544920221482c07580300303555841502c40405e48a40c505200d1511900c0d03502900e00d03864510340d4001e40b1078040e0703807900e00005000303c041080340c00720490116420b9030b0020b000810a00142d01550007085100000c04031451286000740381c508002090031494400029001442d98490349542d4000d5000307800140c0d151100005090244a48400904a031095050140070400414001c100319032003a0b6841400c3d03901d03000d0032410b038800c405841c00020401e2043c0011490049070f101b02ea141c503007408800440c0d0315402c450404107926100d42e0b038040301000300a041030411000d01c00a0707a41d460320040515100307001a003d800f2402400000700342c40b04111994422035071140d40030300f001c40c40740c1c0d4590041110042c01c907071003198000404001840c0007040d90501c17451a90103070090f00090206a80d414405200604d0002c2065815080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 566992724 1250 566991474 566991479
    0x8040f0c090b0907020c0105040504090f020d1211010203010f0e070201150603020a090803040e010b030c120a091104090b0a0c27030c06020a0f02060f0d0507030c1b0b010b0c0304 78
    0x5403110110000c04400740d01190600300403081142059008000000350340140520444981c1d0210456042c2c0740f00b2a0001140c004030305250701000c0910384000e400c4144070700e0410607c80540500c903d8151190b4030402642c8207140801d091780000c1c42504159104a401807084c400b40d00910380e4005020304c00002c0c01282030102c01c140e0202d41d4041c60200e5400109464000e0744084d0410103030420f40c00440c6401d01c0e180117410143c005214003050000c020004c68810140e602c1150401d90002d021640142448102da900404484400b2648075406004070fa00d14249409500c0d09260403c5030210b49c4d0342e4080a400242c48079103103240c10048810040031445c40c04000101005c400450008522411464042d07280840e9070000d40a552000040400040c00300c41d00707081d4039906407840e60702c66131003016018250041414070f6487e03500303080402c40166030581c1300c50035408007641c0c1c13448a80d8030342c9680803a07940040c0018203140352010040c0501c5003c10000d0581040b0340045030301d41503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 566993974 1250 566992724 566992733
    0x3100603022b0b03100e07060206090303011e080d26191505040e0c15030c030103110a090c0c0b0a0603050a0609050a150c020d030e0d120f0f0b03010f050c030708040f 73
    0x5514400701c100191b91000701d0f034140360040103850003822260005040304c0c01d00401c401da6a000c14440e031020030207052034444400c034030100070000510511049460709618040040d1118406d400d1403c1c0e441d100b515641030008035003591901506401e100e00c01c0b0780b07255510130009011020210f4000c0080c1680009072030b11244503600103014420051b202ca410440c0030482400081a10b60307800000500502450044100480707044903030002c00e1040c1c040802c804100e02d4019075100c0c1050074607041600441540203811392407000d101b004282039a90f900844241165079601000c0c007241d0104446500184040c1d02c0b801001d80201d003111400c035140d0340d660f041b01c201c07814443c28813a00c414411440f25010031a8400c8503c0c942400d1150584150038180e031264581401000c014900c902c0008001c0d003503001010002c8200002d1140301100c51410000d0041040110301030b600c0c100808180380c1c513a11800780105802c20146265440d121070840f80448040c00669100809590480c0000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 566995224 1250 566993974 566993983
    0x405030712020f0604050315041b0b0a0e1009050f0d0b01060c030e030106060e010c063201091401120309080a031116030819020a02060c0303100603022b0b03 69
    0xd2190101c00c0094500034410b00042c4801d00380c01901940c03061100f406603580118280b0608801d204001c21540ea81d4103141d851601800b01c130060320b44001c200890380d01c800e0708c010000b8114035140e14480d40100d5051001146060b60031000044284a0502ca00c0c42d09018202078404010500480c0080b907440390480d0100a0b4440c401090a4131855010160019140c21280c030044008000d550f20b002406014941c400284904004010488204006140d44800bd05041d45015521ba9118a0101004210600c40348001c2402100d000040300c0106000d84000c4810f40c2d00c000234076900c1d006a920106e1031005086003400010100401c80c0702c000c10108520394000d42e1000c2d041c009002030282409441c10001c2460041c01d042403001c11402811102100341c141d90340480781003101e004030704210068900070752215000501d45942403000010b180100622448000e0721607a8000c181d04a21414150b85240c0c10f48001e035209500c0f02c14a90710380003020a40c080390207080400001e081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 566996474 1250 566995224 566995229
    0x10e03071a040518070203040e07031b0207230619021504060504110306090c011211160506010f03030215060f040e06180d0801031103120403110405070c0f120504050307 74
    0xa071500860308001524210600c000001101c00110a10382803101c03001b9107d10032030051052580c0d9890104140c103201e80c3c81510140c10400b40210b0054891000035100e08081c8030303c0410351031800c1d1110150101c01da0308150b00314000c0c001403500d041480c04885251403a140780056000381c2c180c00400c0080040024070842c400d0100041e40d02d00341c980010390b28102600140603502c814108140302c000058107881c000070900f40190701d48103242d00d081c0a0a448a0f80ba00c20040100f0941c07040395428107044a4188a582617401503a2560558032107901c0500c0090010303440030001816880e640c240e40c030381000c40070f0042e1324812243c0c80070070140c0300740240c0280140c8c400c00820a44a81e000300b400c0144611318082c1c007c05201c0d02c00140f05038410b0001500c1c1c061000300901c1e80b0b42d010000805100300c49482d41e0f0300d641d6a03040c1600449400008203004900f440000b071841c610075007580d8820341d804881411201110f44895030110507030014841442005c020102d00c65408002d031400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 566997724 1250 566996474 566996519
    0x1091514040e1e0f4012020105060102030a03050a1506051209120f13090510090c021f020c0a05070b0a090b040e0f07020a12030902030c01090b09010e0307 68
    0x40ca0308000c492031a5880308281070081803d11030f014441ca40ea588422150011403424241010000ca040c5030b42c010031940d5803004003000c84034440000d4400914007035600038000c0700040341103050490241d0986804482550040c0c004214003850075000340d10050b04980b44420001d0300d0340d054548003e035010030703810141c040380e000702d0294a409100c224090380701c0803500203003a00200000c6845220700480010041d41d02010500150009940780e110b002010481c105101c54140303141e040b044081d00c2c0c05079141850a100c4d5039001b960000959000c1c0d94024540803144201600190b0000c2d00292024400e0380140d1220b480801c1d03080241101410084103819a2085a2480601414155400b407114410140f00802921101441d8942c2c003403210740c4440000c0d40c4040d812420810340b0a00102124204c43e0211021035055020440c0c091096044032900c040301d000548004000d4403d4007164101007110005039441003900d9422401e01600b120045500ca0102d508600c441c40500039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 566998974 1250 566997724 566997749
    0x2010b10200706080a0c2601080d021f0b1c05010f150315022a0303240307140f03010f150506040602060f07171e070302090109151404 59
    0x301c1020114030409000c11010008104071858180094034601c00180350103078090303861820031345e29070151007500072031040c40b04c0c0881c5011074600b01504040302030045124901c907042103001154000201c02c41c08048801158402002c10141d6401901c0c1e1034012542200404050403926281100818942c40c8601c001142c1504090324020440d0719000c1c84d0701c218103da1a04101081c0d141d9110b0b2441c261401c0c0150f9500441401c18407a19000d94200140e01401c80e14500d05460100280d406200790b442e2010341428021108112a030030380106a5040e00060801c00c401c614081e0f0719072802c43d0140c151a034202448002a0844900b144810441c94075043c9691241080d6590000a440221412420182440342c006d56a02d40100a0f0140a00c01004500c00600802044003001412140800c881c82c00c1890104591501c0714540305000c42e500128100c0d900900039a0810310040c0d442e503039042c0c034094007842e0071119230210000f400364a01140074086508c03001840601034055440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 567000224 1250 566998974 566998997
    0x3010e06061003110d02030405010209030a030e0415180c090b1c050105030a030c0305160602070f120912080d1401030b091203070e060a030b040e0703020415050603040b0702010b10 79
    0x1032111480c0800c00b040600d4002808522207055069408035044d85800584035500d074980700780280318050845070305201d01d01d40c030300405502c00030b020b400b1030017600c00340116402501440340030022801210f41c0202c900c1e248082001155101c000380c1885403030b0459000703984002d1801035900040080e1044104410035078100350103401410700400041d4014000311070720fa18000c042d03a500c400c00904014000420910041540418001c0b081e044001156030307520f40d281800079032055107012a0401090b0800502d194040e540840c1200c0d80c0038400000d02900781e44641c0192b002031280442c055a40e04440300c81600815600d000c0d51040da8040960b081c11100b403407410020560011101c136041080184150f8400f0180c0000c5900795141501c5110b10242a800340c41910500c1d07400c64a0014001d00748840044c002c0200d9001b500c082004c400e400e1018400c03d03005009403504101b0400c040b9000692000405901c048103200000e00910140000b40c10442400741250005082184d00d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 567001474 1250 567000224 567000229
    0x60603060105220f1a0306010824030706050a021603050c0d030c06111c0209030c012a05060a0e0a0206070b0403050403061401170a020109050f0d0c08011a060f030109050a0b03010e0606 81
    0x40317401ca4681c8000389411072070403000080000c200100007103000f164841c40720320401c401c043c88101c0320900405803003040d0340703407280181f807a000394600b0340040c81044903000030460201910703001d40b031300440030f4550014120140440540c4000d000c400b0004242b040d0b5010440a1007994500a0707008861a034814002c01300c064022030075040541448e10401402c00c1643d0002004043d1390f1003806c01c1c4d640d50100400181c40320300301a04d8202c0d2102910840000c1203c0800e42e90b111300e81c0e2071410400c0041a00301d5503500c0e40070b8800203411010401c150008100e100c0443c5038058801d143c0b2919080d22992440c042c1d03040c20f030044880c10402c0006004103460b050f00311150a0850006180d034406940000b40a50001d02c03035940210050b0940074000d0719109003560101d1703004001c1c045925030380c2c051a8000c00c0401c0c03031540f071001c0e6a0000ca02d04d2600c4c2084480050004039414150b900301166000200320203040c0301d1016680b10003288590700c0c203006180010750007002400b01482c08105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 567002724 1250 567001474 567001499
    0xe1f02090a050915090402011b060f0c050a14090a080a080a0215190b0415030c0509060a06021e0307060f05190b011d0303130f0305070e060603060105220f 68
    0x1c40d600c5001c94904100f21900000c000304d80c100421140307500035072114001601d40e2100350b80c441000c0b030001c10368481444403e80122000704c01d401e900b04000d046022040f00d0314020000c8900005107001d1003e88640d07825006885901c000811404d1f40b1036880c2151840c04004210864a114020446054282e0180b0a046410340384d040900940e10300140328440e01d1410b402e0003d10541d40e25140345032512280c2c0072012004240c1c0031012880d807641000c031000d04091280d54455004400015464100612610b045558a8004007403001c04049010141d5074614000c22051000344080c1c40440c2850065444145422400280d181460325041405910070502440401c0c1402034a5000e82d900c03202029240d903014580811182c1e22000207415440b800f80e00c190310501000010503115000000701080b06e1040040714107065541d00e06056200007143c4042d403002003440060401e5002c0c00c010048030029401d900c045107107021060342580b186401240c56040c03000c1d014015040c1400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 567003974 1250 567002724 567002729
    0x6031017010b0a03030804030309060f060306180807020d11100306050f030706050a0e060c0601030627020d030f030e0d0f0e04020405030c0d020307080102043003080a0e1f02090a 78
    0xc0003480868121000300d03482e02c4592200804000c103810010302458400e5110740d4403d98004814004400c00b0501c40005c1c003110f000a640c00341c5001000340a400d81a2926090b45610070740e020708040340fa0f02080340708082600e0595001108a01128440e0343e40c0424040398801e94400003a428241002c0c03000b140d503220b483c98040e500c141d00901c030a0b5000800d4940384012450301007042c501c2800400c0c1c19000c0c6d400040c5041c49210000b2040001a4112100b281c10303000c1440700c00d070780c11201c00311703460304100d0040c3d041141c0c1918407012a02c1843c2d600060f101da800c000c0f4440315801041440c0000490074a00041d060002c4030041d59840440c0c0c1111880c116030550401e81440000b0b503c1c0c1c144504160311410790f40b603005045480500c001001421014000c41d00d40750b5a030000054148914440703544007a07000550441d004019940780300154150b51080016590002924028a018454403100e403154501c071078210f0725900480e21421115040258483c940b00c010b0106080c001d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 567005224 1250 567003974 567004019
    0xf06060e01090b0906070f0c081212010e2d09070803041d0a060e0a0207030e0a26010b12030405030609070509040f0602070215070c0504050c1611060310 67
    0x1020150440c0e0b074010386150650f03410341d40d100d50710015a0000b9000348178106004144550f0b5054520078400300c3c3d07851030100c0382ca0b2029503041591030f64142602d8480c01618200740020b010051001d181c84ad40e03155030107038101100d032010303031002c900b1600c40441d10340d07040c800c86481408015442c541446418010001d03203000390300302030500810680c419000202000e0320800400040c1c0b911950b9000b0100901c40785010b218241429910680a584400b030140c01040c0c0c030b00314001c25800d001e43c001c411100c514100442c403042e0b9959a0480c0005c8a0310800b00b903403140c0103440c1e01d075070304071018100b980014001c640d210f1804c420b140c2040c0c0014030704826a000780c0810096603e809407040d90080d8802c00e0072800502c1031030700800a01484102940055030100d07440030000500f00105000ca014544d0710740f1165888003044196501114150403181d014410000d90500707504566500398401c202003400191442c002c256140c1084807003400c42e0030a41010810b100c01c00000e0307420840c4030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 567006474 1250 567005224 567005237
    0x90307030e061c0915140108060c09130207171b1c02070303050f040312030509012a300504140a05330705250b040b040f12030f0606 58
    0x14464060102991100c4000f00c983c0c072a03801070b040100c081c18400e40c1e03581d003407030400c460031246a11a03240d8000340245501d034420310000ca809031120300140c805981c1c0040588090b1107102015401079040020304541584050b005050041078100182080d001411680e02c030702000c1c41c00c050720349402803549280d43c81150000c2c21034181d01188241c1503907014284544d03aa00400903102142c412540701038030780c2c01240c0242d2003030356164108500882c4030900034010300c6450b8440900350400000c0c4500c0480c6200030b148451400341c03001c5c1404001241c44091101145c3d905441515000d600c891507090340e500070482040603980e02d400282c030a0b8002000341d0710155030386590300d244182400f074460001c2c2c2e840103017000c0118181030664031500922076040c104030030060001d0f00b1400d400724080c043c5854011218046201901c011900700b04030100548842c0c4620641601c0a40305070b46603030359141c0900100d0a681c0e810031301c56555503030004400c40300c142d681c0e0440307100f50405c0b000c1054 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 567007724 1250 567006474 567006487
    0x3010e010f0f090f062a0816020303091f1d1014040c140a15110111090114090102030c07030b0103051c0e01030e010605130204030c08010506010c121205090307030e06 73
    0x30142203002a40304100040706006146d500e070302d06004c00704610031400f40b01b01c020840c0d5800a409070040c4522800b400034008600d9007641c59000c00c596400507903001d4210051043d00900309900944000c020001e406104002284040c4040c4000d05003150f02c2600020032540c0d0328469414084102c80f90b00519041c0341d950a584102d003407240224240b882070a0107025030302e81e0751210081c68000080f500e85443d144010f0b10210b03012400c02040e5203041810000e48d560003003110b00c80c00c0141d6a082055102524610190300003658050452100b0311010142c0007003084018003850084602c075a2070362551034500d141040c5100d80290340c41d10380008120b141e80103d8881c00c2070000b4200451603032040f14910b401043c4c1540000d81c41400315554544105c0e05600400650f801120410034454072500140d082c0c0341c1c213840041c00100c18807203100100b81c1030a4681d40e070401900c0c0c0f5420900140b030701182a074030161450300780c070340000544408054010011542c01035003a99a50b06000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 567008974 1250 567007724 567007733
    0xd02010905060a09020621061f0c0f1703071e030603110111160b0a02070906060203031303050909010b091002060f01090905031b1c050f031b070203010e010f0f09 71
    0xb200980681034180d225020318003155074060644140d5460014001608100d08001b01991402500c4103401844403c0d4a403c151855062650080145440d44020184256100d02501c14010740603030b2043c210a0069401001707680c000c41c0034a0955403601c00035181000c592900f070a11038400d07400e140c03a01c0010030000b101b180003030880003024200b80c0c2c007595005008031700f82603a24035000e240382c1c541100820809203507009010800e0441d801c0b84c607225204c040301ca00f01c820310300a84000d64400d00c00916035007034802003550300c24400d28285041c48213101c04908011002e8114540c2520081820383d86400c114054840f10504e920051140e41401c4980059414044c0500c2000c25110000c09060140c01c0040301e600003801428000310540141007141c40d807140f030a42ea000400b143c103030320362039603c90007e17240102140104070b8a1512085800c805481c00c1100b0402460000d000d01c1d03016075828411400050007440000c03400c4c88640c0c0e04002100c0b28030394030b214414034060b641e0002c81d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 567010224 1250 567008974 567008983
    0x9060903033608010501170c0a14010203190905040f1803140c03070c08010b0303030115030c1704060903020c0409080f071a130201081518061309060203090d02010905 73
    0x16014401820007940e40e990380300485402c108441d03003184030781000026030014150b2105048880d5580c0003003072042a41100c0b40c90b40b420710381c0b50f40e001d0101c1d0824007000d01241303800310704145c0500480e442d2004100c81c1c5c1403000c24281350b0b08085880380d101002103050074092a41203c21400c001c01c200004c21118540100d01d10a000c0c0c20031260072000fa051386801c00440f40c0081c402c0007200d44884840c50104078000340341c01007181030750034407015944a007000070a44e0b041c1c50449070b08481c400c0c42100124002c0040c02544410062440d00e28000503009600c918043c0f030207000081000c1513942006850706c00640c06541c05a8074210114010510742c4041d15840080516220f94598142c28807a84030501400303c024055101c405100c440c0a4a081000c4690300c02e0b02c588402e552040040c14840150b41200e03900708006200c080001a82500d04540c0b0010040c046a940c0d0035040c030f00b01c12070b207240c0d90407038070254008103015030140104200480050355100034003007401c955031901e889 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 567011474 1250 567010224 567010247
    0x5120c1902030f01020c07030c060201020712030e0a02060a0f031a0a17010b0301110408070b091804020103090618060e0f032502060a030b010e0909070b0f070503030708070906090303 80
    0x501402881004541d42400b40d030041c0d0003e04000d64a501001941940340e11031848110364801c800701000400a0060007034444880c3c014000c01c0d01d54006980c240c028082014141405c1d00480c8c0f0100300603510b220281c1103100c1145d0703c47c0308810107003201404480c203100040b5007101441204055580e0f803010035006441d03290211030b524074181d480040c09003070402507441c1e155007001801044580d80002420031202014103c8641c60f55031168040140b269600054000b05180031001c4042d0b45440e072113401a20604d000503494540362280011610110000000c0c00015000d0000b031101c00d0090401740900c010141003c00880c4140729034030b02c0f804030300d65454024480d071040e4044d8000b6075190a950060803140d541e003501d034802030080411031040f90104112403503030b00e118149100705d07d1041440300020f1603401d041c4106881340b50000000080800820004100017500c103001460062400ba05e4020301c50030320344000340044040e508035100b00812914104042940090000d09 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 567012724 1250 567011474 567011503
    0x90210030e0a0512071b0e010302040b0f030610081608150403170c03010e0c07030e1912060c0206091603020904030c02040213080f070e0f0a0b100503010305120c 71
    0x1440440d00341d2050a1100000c8050050701810889904030b03280e01004000d8680b040c121103003030310082d4411a41e5058030b03000e15040302c00c60100510040c2400c1e404038885e450014520301e1003028036000a864440203d84103542240c00480c10041d8101c1044115041400351254070750007030030010003d981c1e10010020b003540400e11800710b401c1c58080c5620580360701d51454034100524003962940800d9000384034440156028100080b50f01c89500c0139500d015505650300420589040108107890b10003192481110a015400003886440e2610140301e6902c05c41004c00d2039561070344086c0c102800108551060341104126034128412070141c0c00079668122282d8443e602c82d800c1c201d0b4115602140250401e10011b1076059510f4160b03170107011502210211808186480321103500e4100c980f00e03d03001b1581050115029003800025140e001c0040e000010700d0300c0300800090207258100c0440000b0910000050052145c103009003410b03c1b100c003051a10704080070800642d100c429100e45074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 567013974 1250 567012724 567012731
    0x20a021309060b09040305090a0909030519051b0a14070f03170d180b0c0a0c03051803031306031116080306010c0c08011e09080f0c01020d050a1a030109021003 70
    0xc0010b26400381c090850090081500d078507203403801030300caa40f100c40100c0c4100074840340090344140d540a0711071802d6047d501da82c104a03e85003006003072121a0140820b22070144460b0400103010310105104002040c01096006a1402e052041850304950108a40c0040f0f0b0244034141c03100540c02d044903448030a180300b06404240d250307814062825540f103890b040041c951100c0034902c80034414240207035048040e5448000c60341300188a00503846000c00ca00d0002400032034054400381114010482204007100400000039046a10851110120b600340750707014003c403a498030461402c100013940c440d10300705040d2841e081c24181d40700010b01c1d6800010004103903900c1685504d03e0341e40e0090304613065648030301249010f0800a409401000c0c6015500c1500e10b4841c018440d0b21a041803400d1b10304039031030b081c25540381e02c80d518011066400700b0101c90714030a507104a41c4103025140e0300091801a80007c121925400f82060f0310907818038220501507034441000c071055806609001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 567015224 1250 567013974 567013991
    0x20a02041104080c1915080405010c03050906060d0203070803030f0f0c0a0203040312030b040e1b0103051509070c05030d02040e07030e062d04081b160e1b18040c020a0213 75
    0x1048050b040c1c1286c01694003403483c2031320140e04103c01c1030241e48200001e001c00141344400321300b201d00440f1940e070140d00080105507141440c035524101c0c03a001a0a9850312078507144401e1842d48140c0e044020400040e0030030003643c05520045800414120f841868034800c40307402540c3e401903010140400350b440c035401e0616030283d40030105001e000381c4140201030803c492a0349410000d45c0306d50614202003001465580309102c0c3c2c51003064070400201c812207542052155180d0010310180c18000c2400b0301c400481c031b042028202e20030b00c00c40c0141c0d0700c03810200c4600d094200070341810285814205000e011940c04203015611443c0c01d0160900000702c24150f00302943e6004030398040c000084244400e01020600030701006106c1c1032041d8549104542440d030b5280208414040c507810642c0c20b100440103c500f0070b400000c01d50b40b00300c03084141e000c2c601040e480003910341c214903040c80e41c15038035003001c1c01440c1d280350283c000341110340c0c1c4a130041442203190080c101c443c6941c41c0e206 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 567016474 1250 567015224 567015259
    0x604030504031b05120a021002030703120f1e0603030e090903120a02160303020304060605120304090507020309060c0c1207081b041503050a0b010803040f15031b020a02041104080c 79
    0x10380c1c010140104000480c0c41e801e10519146d0343c8408040e8083d01410a0000880d4000411142c0c1c0300d91507640e1011a807a2440000d0003032815145207141c441e00c42c198400400569141031050750f240b4100021843c4c910715001e00800302c15000070b80980800400c102041344003100395030740441070603400502c0740e40b00c0010034024410000b0507034a81030540b5851040c10352540c05148036500c6048200501500c440c10801044050801c06070303507600401081c4214000c0740c01a54001c0d009004980c24162100000baa26402c0481e10070800c0e031021482954600e02401d404540e076841d04083c0c02014101090a504c1d801d8000600c03123100d4840c00d4800c174580380c9512a640e85820b54010002c140c1d207a15045403102a90031007500c0b030784915400032400c007801008480460f81460a402000783c680040a2560400a2040d00925a9400452100088a9040401c1091380c6ea002d8542086144100411a024030741807044440c028071051210000010b0116940c440c2181c44c000c501500985 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 567017724 1250 567016474 567016523
    0x14011104230d06050612070f030c050303030c041208041a030a0b1f031d010e0313080d020a020d240501051e090c1c0f0c030e06040c1a040306060312080702060403050403 74
    0x46c140042d105000e00040c0c1101442002401d480c404c1503483d002e43e03524010103a43e80410354480302070260810007002420507440c100445244035099050400390b5818040300c81121000d498003c598001081112107180380c030851900150481e03c550042944041304204907194000d0340c0141607407000c0041010a04d0f9002030032001e036460092001c10440a0f4540e01c80c3c014078152030420343c0c0100c000c61030314000304045403921826401024203680ca0b0b020001c60380d0120809640744192a100b009424110b52050701003075040140c045030a514042c00c4c040b55201d0300c2d9503c41d0714003803144403d11644c0d03010101900803108446203925080c01d0b104002580d11666000050180740421254032204190441e410908840e01d003044260142c505035070b01d46004a03001000140c140006001c502c0e66140f5402c40c0c3c140709d003091810103071079a0b104000c0310841d130026101030642c6c0e0303040003020754011b1009902100d1840a442c0508150303401404600541c04001e00009003c0c1004954404555 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 567018974 1250 567017724 567017749
    0x10c02060304050304060f02060c03070f090306090b0103050c0103060e0411120f1c0c030806010c05010f0c08150402040602070e090c150307080f090c060714011104230d060506 77
    0x304015075904040c9060303a680c2d407292003200d010488161080000703500110f0345a00c1040d80c02c0d111442c2d65102c42084803110400c0c1021000d00401d4100400415010b109604030141701d100d5a144035415420018a064034035240c0d50f0402d4286003082c0607075072401c0030741c2e1341140d403210380700a8400390480090300e26000f6074402c210610a410045128840010b031b4030405010700d440106030010a000200c0302c818140f00b0140101d50342030302095595102d02d4001011a006600018040c0130170104002507803c864260300015a400c030600c8507004408181800d84482180e007107182a1601c08081c0d00c0c1c0405200f03c020b150309000000d06154030500004409001c0180b04ca80300f4641c0c2400301070507800a4488000146400b0000b5800f03074540f54070b09014040610041c0600540542080425480b04408903400c00d00114161030000003402920604413885200c00d450b0b82c203000000d0030000855071201003200050410a4003078070b450518100040e0407450110350b41d03550343d01007100101c01e403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 567020224 1250 567018974 567018979
    0xe0703061a1203030103061407050a0c11090108010b030f030c07051504030503130e15030c06090102070b042711040b07110a03060f15050a052806020a0308060102060403080a0b010c02 80
    0x111a82c2c20028003c001103040c2d07482284100864405285c0e041e6031a04101d851001080013004140241c40c043c04540040912034983c4242c0c00c01c41c0b5010841c01d400031f13481941560f448510104141c942840084d82c1d00e02d03035030000e40c1040d1032aa50142d642705244200350107031140b83c07083c0c0001e501940071a0091030704801241c1e525088942249c40a26881c411010130a1580c400f080000a440c2440016054000c000307204c0b00203a1010814107503c100c20107419881a400002507003080e81c03001e0030081160529901d5103401c1286441507440d030f5403000048080c074241c040914104440192800e032030400c0c0009844826510340600c40070300444003d0780c040c10a460002c100112500490740491001030240010f8650324030724000001c2d54005c11f43d00070300600d0b013441a030600c003e00f501c0b580d1b807058155050140628084000f85643e40120300184c2180d081e01007070540011289401c03503803e1006201c9403130207440c0200801d8002d03001d1079805843e41c61081050b0f1050601a181a400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 567021474 1250 567020224 567020239
    0x21030509031c021b0612150607020901090b0109120b0a050709091503060e0d0e100504120809010305070801050f10050c070f03020a080607080a05041e0312050603010e0703061a 77
    0xb00501940d1144181c4182c0301032000c0b44901e032034034200784d01681d4025150011000c0342d6200ca14901e4120712031058465041941440030308056982c2c052894000d00c2030030000904401c0070b50004240030042d400810103840302d0045480000c00c8a414603074400b0708401c0c000742d15192b1803412078078102ca41d031100c40414104031030010b00528605c1020110313486454104400b11301500c1c499201e5030894520804502103450101c01da0130315204060601d0031303901c1c0091409855641c0300070750302c025401c165070100c0082640c02d070a50b05480340c95000840350800401562400700007a032203900326100d40e4010310140c1584081c841c0564240c0704808003050a0b604125100c201c01030302145144030980c4100104000020f01b000c010641601a250700c0d501e062160b51551054005020083c100b1980d000b10038007030010458424032421078040c4640c0e2451003562400310440103a44024007903620a91601084185440000580e48110780c0d04c0600811507002c0700b003448810b40c22202d4019004000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 567022724 1250 567021474 567021523
    0x312060d020402031501020f21030406060e090714180106050c1501290a0507140c2205101503092415060207030f23150703062103050903 60
    0x48080080c0150b170030790854501038100b000d5159203403c107801d8440c41c00030250782c000046200c04025588a4040c50021908603a1100c0041035410100c60642076904030040c140000241c03542040207036141140e040c00003c4040e040c920f051001840350100348040081e0b0182c0381c4006000000309090030a201c80419a92501134402d050801e6403a425403082901240060710f06100555600405655500382486560390351440300c60400108008a481020090b404940d03803010701400c04421040c0c40b420361030311b005482c010340d00040c0080300102102d02091120483c2880303070901081640c607000c205100a420507000740180358210403807980d05041c014210f0f0200d9003201d01c601801c052040c0b0301d03581c5c941040380c030350019000c000c1c400300881c1150008034894060400058940d54401c50210700031950703503031410f44259240c10032406050704020407203405106100c02090442030103074010300039980210280d400d40d1030080501201044081107520204a484690307800c007018143d1320301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 567023974 1250 567022724 567022741
    0xd0e0a030908070b030118050702070f1202040b0d030c020112150e040507060207061e03140a090209060307030809060328050f0a0b0f01080c0d14091b030312060d02040203 75
    0x5403409801c046202c3c001001030300d1107014040368126846204505404183c02d1404405010b01030f0543c400c51241c886c01151381280c0009070f400038003402c000803841d400d882c0b0520099404407400780e4801c0c4414141540440d8100090403202a824a021554540450800001001c40040d0707003550060500c1b01141c0c0710b100c110918060380c000d070221121640d56107002c036038030b081074050100000d43c852407074000c078040300328801003600f01401c0203e40203d100c4200b0030b1034407088903100400d80d1945000c80c15410400040750f0003140c1500a048100d0540c0c80d00341480c8188540700b4040c140c0000003d18082100083c403400c1c2d2000c0301985980542e031002400500b00c160760051400311004046111020b1502c10601e8040c0d000e444003541e040f903400190390802d4010702c2c0e595403001c2080b0b80b441c002a02d1160b204c0385004100d0114903814103040240c90b08040400c111304248003080c107400d2550b400420b482c0c07400080c1504410700d5440c840411481100d240c002504203002206000307006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 567025224 1250 567023974 567023987
    0x2060720030a03050709080a0507080f06040210050a1403160e120d1101090f050d0e03010c0c0602030a060915061b110603180a03031a0108040c1514070605040b15090109020d0e0a03 79
    0x2d2f00c0240440f981c512840501c507844100130b5400941c004171400d6640b840b030340140b000d044250744a003450350340500046440042a401100c109800441d6070040303032a419086102007180600070348203403a1482a01404036500d00c120f019240501080c112403030f1400c00f0175013051007640d0340284034080b0b0300420b103801c658403a0380701c500f0b5001c116103040b00c26041c24140700780580c17070389240e4801b5506451070710740078002e5101a00307400c2e003651100344c04038590b100f50150b02d001140d00c502d5440001c0ca000700041c020301185d240c148a403120302554101260b440516070b404891f08403070320b941c2c1c0d40315400b05410381d40381c02000b00100c1c0220707580b1303000781500341e48011464002030106415210f40c010046a440c83c040324000e03c600a190800e000c0c8021700e007814a401c01403810201000050a4848640d035000309004440580c0c50b041004100300314454896080382c449128030b02429000c0001501e005014001c805880d540468607000e40800390700412507540040b0f041d19150040c9007001400b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 567026474 1250 567025224 567025229
    0x9051c0f1208180304170f0105043503061903060630210c020307030b09070b0304030c0b0403092403110f0403020f0102030408060702060720030a03050709080a0507 72
    0x200d0042c2000600c20f00c100e01c0c5800c08041c2d40c0b80510310706401d0904d00600443c0001c4020a64070034246842004a400d2040c01d0080d03000b5507031441005040c0207802d50128017000200c0c02d0005440301c90030400c11040641c0d811000440f4000c803076141802c0800490011540060700c80c5040440c00510340d504062404810003641a545a110a201280405000203240020400184e075100d181140000302800488461a89044640f414a42c2c000929064440d0401c2c6c035904145c1c2c042c016520001c006040c000d218205c1014150300e403684015240a07419403020786042c881c08005000c16100310100409801d9525600b003c1c04040d2200e4400d0303400d512891004079180c0b05001480042400503180303095040c611080c60907080d0385c240014420140403550552006000100f102c00d010b012261049440c2e500078801450141d000524084502e100030024420500c0085034406020040303a401c0c41c0b5504010a280e150b5031000c840f00005075000c1001c501410b841d000c00c012002c0340040c00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 567027724 1250 567026474 567026477
    0x70b0f09011503030507020103090206090607081b06040305160507050a091a151c060b070f05160b03040605071e09081608150a110406030902100f09051c0f12 69
    0x50742d800c5280c940340e05a01800b018011440a20134840150700c03a412004801d0300c050328290520042101068040d0000c41c0b084407c1c51004c5944507241c03d880d16022541c3c0944001010603042c80c0d103024182d880380e82101410382808403003123000d12404003c103400400b0003802e6803211a540f00c88040092049a40f9101c3c2000d55810160452138540d2804c24030864424185240c271220805500300380c03a4013614402580d881700400103140b1828000f4090003030141e907810442c00810b290103410502c41c8511401c41c100110020f01a100c1c00d2020b9aa21503409240042c05444400e016141503180d5241c0c15041e040080c0442c4800c2d50098044007103032008802c950408a601040c100d800c01c440c0a0b07001164410341c1450408128056803c0d04000c40040005501c0320000309101a5481178201001082c0c680750039400b10306002d0085400003a5514048140c0e07541c2101c000c0042035144103182c4141c41c030090164000002407a80154103510840d4600105040c1c40c1445000a60740807200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 567028974 1250 567027724 567027731
    0x806011502010510050109090c0201090210050c060108120a05030601030b1216060305061e0627130504020a05010e03120301292d091008090111070203060615070b0f0901 74
    0x3082444004d1215080c2d40d4140c40307254a02c3d00b0810a0b100034940c54400c6001c564907465024056210b510402400030580d039152030741d98085500c550f1403d041a402102a50300c401070584080240c6420355280b01400e00c0d05603aa40c07546001200944540842d0550010b0780700d184079100b82d0002280200d00c3d0040a046810540c0d40c242038044030b00c2110250780101c445d2501c4242c8402c00740d0f9001c4000c0c00105014102110400c10160800003c030000d0040355080300b55400d985001030004c6442e5084860a20281c130f002c1d4041507401c442e0b0b1180074140b0007d9070741c001044c5c1d03051140031210403040c8021910781d80d6800c6000000389040300741541c01003082c050400400400000c64072050041c0d803444c42d40c80c0500366040d4208480010001e4010380c1449605415580c2c08404c60921049603a10b140f50f040040800742114611010350300038450802c49100182c402203070b5598040c1003226001003075400400300704828482d21000510301e002c44000c014140440109550092003124001c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 567030224 1250 567028974 567028981
    0x406032901060c11040e0106170114010b071a091002160b061c0803060d17070302010b0906100c0503190c12020a0b1611190204141510050408060115020105 68
    0x75681c190003c540582480d00c10b0440e06040e080c15001a12214004400018141c0ea262081c0070620011541c10100365151500300000c03103c1000d040380541007407004549401342e1590380840f440400b12041881800040c0018189401408001103228003180159510062002d01030036120312590300312248000c00001c121507007810b0461015444403070101000054081c0ca40c80907680000304001e07800300d5040c0045001820701c5098440114030503240780c0c0c40c0c403c01d1a0207805e441c40c809000340142c0007402008195610090075000e407040340d040001884c80d4500341142140328410b0101040700c0e600f141030707a46640c030095103900d03513004222078803504204d800d0403a210454403801800100b00c0d600401c4815070030301034080062405040034a000d2240c48101c81c1083d40001014007072344807209115042d400c02d80180c5440030700c1c04152032a203207403d010011881703d540c034405008007020044a01c015000d41c007220007500c0924106c99256956070015450600b00b52042c400550910703011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 567031474 1250 567030224 567030227
    0x15040902040f0f141201110d06140f060901030f02040302061b19030207151b0302071e03020d081c02070f02040e0f060f060a091a0109060f050414040603290106 70
    0x42c00a50b8400c40078074000c10008803c021705824102c40f000c3d11550707907020000c94059010024070841d0040900400d4507450711691519400150403611b002d206809002006d6a40310021101c100c682424001410039540007040c000b4000d90b00b0003034004100007002d201291b41090740d910540000c40840d4020444151415080c401c98000140541d0200380c041c8030f01ca00c00318800090700058a071013844d221102450040f070b010081420340258028030720a001075001a84001c4068039914118442d49145a000c5000f03414000401350803007001247d500400171114461504114440209545501ca5030a00e0f18140030031010891050740f80040103101050085229100d040841c0043c100030350718905500c0c5411b00007401550300c10215140031901d038245202c0e800d41070b5195221040c0034080035001600c20b08203a0040c0041c04420041c4400a550080c00c6405880c00c522024004501400108000d0300c5a60401030070500c2a404000808803410282c1c9824603000b1448071450741d0300d110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 567032724 1250 567031474 567031499
    0x50408091912020d080c0616081302010206010e061f0201060504140108150a020c24070212030a021608030405010b04140603071707030c1d0a06210215040902040f 71
    0x1401d40060b4610201400341c5410011100c02500074618249012003070b440361820a00100c81c0e002d000705076100c1c004c410350783c042c1945a0140c002100075040340d031320380c0010b5555001441900590100c00c0c000614a441d103120540e402c04034141c2042d00314020706c030040e018107074030302400d80542d2800050001c00204d20060904a41c500710190050b8450300152895619004000d00051074003000b5842d04031008025004580d084404000c1c1e2460300318960440c0d00c400a403562003154041e0400c03441c0321401908030b03500203000d041c005a480345415981d141c3d049200202501c020000300c100b200384281900b00228032101101c040100003d100303084024940c01b034a015401d540060028040c00d0020007160b42404c00b440c2c100c406007660b0341c0e07400142c61519001072015146c01da40a1781c500d0300100100d0f4000e1040d043c1800b20a083c0313911100414900800066100d010407120740075920341f980509241c91000ca10076a03900d0701c441280d03000e90702510841c035001c0480b4100007203400501d0b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 567033974 1250 567032724 567032729
    0x30c0606031b01050711060301120209010b0f0307080403090906090f0e0109030f0507020f03061e090102090913140f010b01110708151803030f0601030509010b030c01120b03010504080919 82
    0x40600b105150408011201a001400100c0e5444512824158507a071842e000d1030003044505068403c1b0003240c03050160020040c0e102044440307080c450709080c58810015a5880119480c1c49820760361503060403110b01440380d201c60740040c81e100d00400d4021564019684900608505002c14804122850308070f070724454002d0001a00060142840e0744a4401414014001000c00080800ca400040d00b04482a691070322520120410409550074400c00c8990007049040218244049800130a040300b0300104000c08041810385410104204522480c020108010886101089082916008107903003000c0074049600d241c1c8642070010001510015901c88002078604080c4030b4869034800035000d0308281049100e0384051210150400203544030b040100104105414000300150440b14083d00c00311041c0d0420300401615140002c10700c500000038600954030744545440e035001004025160342c3d140d424481170205004048000c0c26807014129184081300c88034103a1498018240e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 567035224 1250 567033974 567034003
    0xc0a0b070c11032a0f03010f0603030311070b0c1605060a0501140a03031b06060510020d170106080f101203020f1b0d1704030803040305070c06030209060d0e0a0c08030c060603 77
    0x3001030003907104e1003000b5410082c010b440d01000c4a880d000203829514098288114190745500c100149503040c083c1494a42c2c3e02c01509203040300c1900c0e103520f00c8900a14605041200080f104802104000120f4500f40c0010580e0240d050449003480900028800d5646020040004440c917140290303105d000c6a40c5922000d01c0030543c00d0756040460b04070101500c0c40e81e0b4540d000200f40d2500048405c11078502c3d40039004000328850054160408071003a00c10200800c0d00501005810001c2c464000d40400e242c110140e9030680805801d2407d600007500241c0d04d841c001042540016000c8840040e9500b683c0720780050000840415050006240e4030a6045010602044424840140c4250171039810743c98992240c64281d0254425602107001170f0f40001d55906200d03610b40c4110140c015854154540003001000882c240624146911030b01daa6010900d01c0101c1042a0040558041c05004ca40c41d601d07020140c980d08500c1d0140d4180c02440b000541d079240c040b44111084115 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 567036474 1250 567035224 567035263
    0xb010507030c0212010207081c02040e1314121b060411010f14030c07020f090103170c070503010606020a0318182315030f060c07080c0a0b070c1103 65
    0x10703071400c4070340014008069030400001c0c103c3e0880c201c400e000415686004081d0180c2c0c4003040303c507002c11802e080341c40e8282d4600c140024401d00b854120400e4101580e01d000020307030340d034505003017440b100d0549018506203d07000346181008502c401034204102e10b1694030726654031401c1119141c010489000b081010402107083c010f40c01203102101000c2980380c00490741e0b5142076592060390007500c5621000e07001185403811031614850300010400c0c25108004103500d161703200b58029100070810034503540049007994041c00d00300f110780000c00004009000c2c0c0d1381e480002944a003a501c2040e00010017074100c03101c6101604490004949040440f005640c120306101c0c8018003402e1500390a20312041d2040319101d00a04a20b4010002601504c2c00f1425900401d484c1601301541e500803078000c8030030008840158415240b4007500454110303038400c0ca4440c00d504182c01814010149030310710062000c0e8950100104012a00c10340741e00f06001041010141e035180c1d121140d1945441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 567037724 1250 567036474 567036487
    0x16210306080706081306060801050f0a2d11030c070b1b0a0503060409050d08010503160608041104060e0f06150702130b19080109150501030210230f0a0207090b0105 72
    0x1041c8091580142c250020802108007580c03020107031fa603da40400002ea4551081c03150304d0320240e8085400c440980c004000b1500d4406025107660130000c1074014090109403007200c06941d84c1c100e410301e203d0481080f44e40340303404404004141c00403002680c08180080005001e000000c200c140022448032415003000c1007804101c42d96070004100c9074125071203150340c0d4001034081022003141c401d15120f00315a0360408003030614000382c14044102c8041c0561041213802d400c000016005134015000d0380a940040c000704015201c079074040702206840000b048244c151059145008400403500750f6080720245101040d00d01030705501951102400324100c0c032a0186502411134610054401c00204095a07032540440c9040ea009421a9440300e840c0310406c2496a030b44004a4100c800402181d41160003040b010001e00b1696414041c1946456801c2c00c3c5240d1903480f031007442e4070706698071480e0041145080c1c000c1513030480548a8500003088445150051000200040e59010706114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 567038974 1250 567037724 567037727
    0x70803060d1a0702060601020c0a05060306030708030c1b1807030506030109080c010b03010b040504030e0d17040321030c050d0207030c02030d0306170a0f080f16210306080706 77
    0x6101506055120164807848800111111000c0d84031990900d01d81d1014949150040c1c00c2c001c0080c0400e04541000800320f580e51b454450b03803000e840d42078440c20b44075644d030b03004a8545481c5030420a00ca22002c00c0014082000184a003c001000c402c2010582c40103418050400001000b41e03d03124002c0e40020005403090340101e42c441c000400210300460f054a60840340da00810b070554299440c0c0e18003103890304003406500c814940c00c0e06c080080780341c9510005c00030030301090b0051084c1482c040301c00a02c10f41480b00e0340800440e000e0300341d5442c0d032481c0903000e0a040780a003105085504125007d014042c1c8030310070a1461070307152149002c980a544200941c0003440450a10250100e00005600e0400003540c4007441a1000500f65040c20444001056050501d0000f81c1c0102145000141a10b1850117565403080394552a201404e4211440c2c0c0503c0d02080e030402c0c4141202c000b40720b502d0800c11003d440e0807240001d181d510041c1201545c0240c080c550b0b082d0300412080101c036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 567040224 1250 567038974 567038977
    0x1090c0909051606120b0d050606060f1e030f0114030606040e010f02131d0403053a0603170c0a08030702070b041410050a201204030606090f0c050708 66
    0x52040c400d031080d60101003c0540043c98a1304a000080c1000401000d0b61100e48500203813520201c942e04030384a410754515646040041c01c031805580041019816201c0c840217507002c100c0707000103070307030362500886000e807400e400417106101b0b400142e8000007445001125500c008400150251801d5560801400050140c8000580d142c3d03503108408039403600d403032001e84642c800d0301010400392840d01400192103000913241c1005042d00c801840006074015049590901e0206a12a01c00c0c030302c40f000d11480c0f041c1c10f6a89154124501c80d20020181c01e07800141074910607201c2041e0203080307200c2d580301802000000343c515402518147e000c1140d000246da8401e04510456400a40700c0d40e60ba0055007003640516080f07044104d88211070b280902910301d074a201c605d0320781d04144803aa0014101550b03060801089140d86c002c840c01d200f070500280500c1040000501d55880c0d403490010000c041c0d40c400c0f60707031041ca8034003a0200b241940c014801d2101c050359589003003503000d4440d40303043d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 567041474 1250 567040224 567040241
    0xd02100c0c0f1511030103050c181504060914060315100303080901020f0c030409060603020f0933130b0a0519181d06010804020a0b0f0f031006020d0201090c09 70
    0x484540004842400316613000e0700800802d03125200340c0300d503d940780151802421101252207244828800942da40c200181540e20080718205581020044400b2130000d280a41203110b0745420015180f84c52000352840c68003d010580032524920354900c2c12080b0001b050701e60161034146041c040010900c203080e03054001c0d00480005140c20423141100056620001120f100c0b9080410b04006103201c0d031044800070589401c0542c9090030141c03e09103648590988a403080c040036900740d40005000000d018000b212185902e00d4000d8004492202c0d0000441110003510183c00460340b10840c009840980c2c0c15038030354500349030004100244040c1880300c40401c00c14902d0082440a007001000c0000b0f05240c9150890298142c2103000c5025005102c0b03814020303004240f000603241c1c0e8242800f00d440f00301c84280c5441e00302020818901c140510207145a0b00401444541c0401007650800c940d07c0307030215080144807104c02e0b42079446130b5078058914128040d042084038800d070013500d10b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 567042724 1250 567041474 567041483
    0xf010b030a1d070305070f061716020c030a0303020405040b0f06090108070228030e030d09140424050418030c260d15080111040902090d020a0303020d02100c0c0f 71
    0x1002c080c50080c03a03d00126540195103543c05120200100f104d92a00d000183c00c092800200010b80900070002021000c2d095a510500d11034034640710074400d008014045400805a414000c0c0b5800d009000e5041401640d211750310384003060105251040c0b4145030a10040d041d00d041a6400005662030384004000c074040d40204140d0b005031b0001c0c0b100460546120860303048084a2500f001400d1004020070580641c0c0000c8004585c0d9400904800c115082c400c00802e80c0e400440100300502800d264184600c9001900304060f142e0404460043d61016101000100801a95800c41d00a40040070300403c6180c4c07614408907100d4481c203c1c9a002c03040d500700490710914500e155580c04001d001808079610900100d202005001502c003c100c203200a11403026440c1c1400d110388070b10f100e810281940054100515223a45903084961a0001e04c80060a6a40d0802070f480d06040384111005014044603411000100d11880c007416100795190002cbc20920703600c4e00d5034295000300544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 567043974 1250 567042724 567042761
    0x1030605151602030d051c11090405090708030a0507050f150f090c130207110901062c060a021005070c0819030f020a0c020f032803050418060e0f010b030a 68
    0x5000d61410091080f03c0d0650740d031047c0d0740d036812045072103081c0d280c07100c0c0c2d0380c0050034400e0a00a40c100042641d400480440b0300080640b034050400b80703001d0041c2e03c8031758907020102c0d61440c02600f000c0a48070786030160f0151809030500110340f681f102c00340000c000c504081100451030004084032501d078010111001c039800d8540110010b0281d0300292f80c14001541c0010742c00007000400b011510b05a201070b00c0704d1585505202001e401070388507100281d4415190000c4007112040200c241c8141040035080666607010304a0003911000c0020f42d0446503403c01c808100c0061140303040c00081d540003034406003000800c00b0340c050400b900c000301320100345d01c91101c0710341c0112910041c0496030f40e0740c030f034803031059003501c14808000c290000003480382e0407440c884403140720400c030f0103c0c072020340342c0008188084514040d52076020f1a0000703620b124103a00d603251075030b00c2c41d0301040954143c0e0f04605881c0d0344044000d0f1110109004c0e040400000b4404501003000a8202000311641c0d00c2101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 567045224 1250 567043974 567044017
    0x102241b0c150603010e0d02030d0b030718020c0706140a03180b0108011b0305060616080f0a08010513021e030c0f03090d140a022d01020d0b0f0103060515 68
    0xc03840d10189500d4441c60000340400d00011345000d00ca28100d00c4801d5010300310703403110b420001e0345034041c00d5015040992514100d50f1165814000f4402602e890010390408101101604009420080040700503201c1c6000100d00d0318000c500312042c100124203914542009400d049000d04640a0f8104114404107605030001d03011803c0316000c0d00031000006160008014140301c42c50308042c0358024180b5040c11b00105403240c408842c0c03000750a20a003004400743c0d140038065403003000c01c0801140c2c001300304003901c6540284154101d90048421050245e031386080ca008a00c9070900c142d0b500c00280c40c01142075a0481d02441c0e0203840108454103080d444040328031164400c950303c00194210500e2501c1454008494404c40c10011004604002d10040b02954406c0b41613401c482a820000501c5075568814004005901c02d00f4001e548800000012501400c00e40b10030030700c1005404803144455100788103801c11a6801840d0114281084018244691081d4074610040c81000d404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 567046474 1250 567045224 567045247
    0x30b0907020c0a060905060d0903020a05030a090f150c0b070e030706050d0c030915050a150e060307080d2a050d1d0d020105040510120606020a020102241b 68
    0x49510500203a00035140c1d6807280380c20001d14500c107411020901507480014080c545401095031001c000c0c030500080d0315000e5050582c940645a0402002d074400000d14408060b03001041e01d04480e11405001210703900c8030b0742d24130310764200c0c07800300001864400305034017007400c41c125540c02800609040c10100403e00c0464144031b1140c010b403010501c00900d400c10f814851162103400d100510302004240c800399602d20110503070504450030355071260086203280d84154401c503540c56488061548442c1c3e03e041134659010304a8016100340034038100040c1c0c0d80d0020450840c0180d10b0340d9012412004010540756101a0f80e0b079411100a00340514000500208800710840c0071035102e0340e54450302c8007205410b03151000200c4c0c1c012800d04180f1790041c0d0f0041d043d01c09840044a08020880b07020740304451214007058001c14050622100060064010402c212403900030790aa80841100c00000d00500c491101c0401480f060311000030600042c11102d81410004070601619240d4040203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 567047724 1250 567046474 567046489
    0xe0c03150913030207051212070606120b0108010b040903021c05090316180612080a0c06060311040b04050f060f01090305030d05070905091501030e0a0501180204060f0b03010510030b 80
    0x34400036407207282c8104424140c0400500c4005c110840b000030301b13488600c40711501d941c850b400820108002040c40000c10400303410100151035248502407080442c2e0a000d000da21083c400c0c5078a551034482c1c03041d641c0c2010b020703250150350190014004018a2441415250720b0058030f00100581030140340b0890303909220340100303d51002299404103041041440701c01c94000f0500460b10315001c400c11040c90204c1c15801d0407038111080036290480c104090b01c0b50100054024011440e0560104c01c21041c119610345003181642c04102c03120148051208544007907441c003520b044404000780052401542400d003801c8189020412a55203130f481c41d107503800c8100706109083d00c51082141c2d89600040007030044c141224103103402c0c1841412040c249010381c121604068481041d100c55400411030f6a24555114000f00500c8103546100c44e244101280e00f00c1c8a0381c1003910000d1350301000c01c914003d0b038852080061075640fa00e0200300443e03240144d0807080c103071580d880840356a40d81e038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 567048974 1250 567047724 567047731
    0x2030f0c03040302010f0c0b070e061614060703180f0f0f030906180312180f0f0e010503060c0a0305190504080d0f1e0f09080a11160e0c031509 63
    0x14001d503203450540c8000341c410501100120300701b0600088031408140300506d4190060640c1c10903110341d8882c0c0000c10a20320940080030140070000b0070041c00c12012003a6101c3e50010035041d19001d03213078104201e00b99904121444440c0d5101c43e14140420104800e081b41c0500c108070400c1e0705c1095541e00e4035000c403070480541c00320b81c012804011103500310740c00d4a240c5492640c9000b40508650b070311034500c01044000810890000781400f200710287c0000c40c00b41c000c0344801810140c0e62020500301d280d544c040c0b105c1005c03d0900004040c240094007600070711010540c0e40c00c11144660450040c84018445d01d0b95200d800b041840940c16445264082c0c1d0041e0000c41d41d07070020050303071416224181c40611140f0b01e00080045038090b48520074240359040390300490492884401c40c0c015150341c21005e000d040000030490405500b240151426215000944202001c070300100003015402c0e11540c035540680c0c40014800c803421300015548105080110300c1c10001000c00700c1d240b940e044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 567050224 1250 567048974 567048997
    0x1f0b130b0321030a05070503100e1816050301061d0106050d090206030a051509100b2107090602070801200708130303030209040b2704082713090c0509060102030f 71
    0xc0c01002813942c0112540103c240c2042495410b103103030640d026400e64829895540c03102e801103584103404907003121200d2504001c03140b141441c804d001c0140c00c180d02c02c080c802e42c40c2c90000a04c4500c075100c079910403803c22a48011a83c41e000781650250300070742c40051403641d20f4034a040141d40c0c0c85d02640c0103648480002a051404141c542541c110440b0b80b41c0c0305480400030404042505810701041e40c074210403007600c4134103100c1c601c9503c2c03000d01c0480300a05e1810080100c141d40c07042065084414503801c6521f0390390369155081c225148a400808200c0c41c0c03500020820304100d00800c811407041c3c02e090301d852a0100004071002d603a400440000743c00046076095440e0234041c0c0b4080c038404455250035549602241412400c101403d90740320400f80e0002018401e070303030b003e03200310032501141c081c540b180741104250400c0300851038522610010807601c0028400b48203529606520510007600141001d08111091400130041b034118401004840c01e90140c802c007820020038031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 567051474 1250 567050224 567050227
    0x1021903090e0703052502010902040609090203060609010311090c040512010504061b02060613060302180a0c0f200309060f0712080c0d020a030603080c1f0b130b0321 73
    0x8141c450140214043c1c0040201802c10f81446040c0d201e89601441e610041d140c030503807a0a245409034007400140d140a5402450140c0c00902c440d1036402c50102c03d4422001d96889603103001c100b00194100380009007200e902c40079032441d1424181c03100c0e50032415500c0080d05040d55000014005900e000c8881056512402800b00708950f50142c48410541c03c8200c6c44036a00342d00000355200001019148100f0390b15101d03111921040c0e000301d0145130080c0065014200078480c01c0210001603403020542e40ca00107002c00d010380700c1d507206c2c0380c40000d03940c600851181203401c841507580303840038540d15030008004a01e140e555102c014070100e0440142a510743d909410450f1440058014250900c41c00104008001102c0c00444280c210b10700b500607240c103050842140203000f00e41001780761110001e0034401c0040d000410014031602083c001e0000c83c0814015400c0d109284640361300030300c0e09400801c2000c40c6411056200001504503403142c4803410009109051001644254480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 567052724 1250 567051474 567051479
    0x1202130f0b09010506040b0a120b04110c060708010f030b102610050603031e0702180a050907031523040327050915270a0b1c08090102190309 62
    0x506000c02e43c01000110f03170481c20940713440c0008210303210f8103061408200721b8000002c6501e046912000c040e400c064004c0000b0415102ca9080550006100d44124440c05002031130041c0310310f2110341a65103143d4000c1c1818615035918100400c050700500240003201c0010603007040d007800c1d448111468108200383e5150b1510170504185800c004009054145410004281c034000111549498216030f0340029040c003d01100440c001d000c030080d0f014841a4090003050704845140e070250321030308410001034481c4d10440781c0e90b01c4a0701c00200851240003600d0300d1040315500c1900e030002070164801c01e28581c000036502c0c58804030f50842c04502c811048510310042c9210702c00036440110201e050040c11314001640c0c050f4000e010311000307101e02019031596142c113441c0c0c4170107800784034190300081d14200580124000846807804114a0080e0040039440c256403280032003210005020403682d510384540600d913008001c60ba0661241c0d0008041460b0303100da5018100b8000e903141d400c4a030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 567053974 1250 567052724 567052729
    0x2709220f15240509010e010e060d050a0804061407021003050903040e0c04031a0705190512040605040203100902010512180607090f0603060b0a03050613020f07050d11071202130f0b 79
    0xc010340055010710340300001800340e40c2c007180300c080c15100f1551810320036540d01c800040505103082b000904600038158503030100007803d00a40141d844c075491706116602e111904114500441c000a54000d5074241c03028080c038003950006410000b05402c1e285090b80342c0940350b03506801900c024040390000079042041c0105000420210014500450282c0c10003d10044c10390083c507195000c054046200320000b640108200e490004407107400002c24503003820020028041100d090740240034802030b81c0340d1404188501d40c0b142d9030503180c8500300420b219024050840003040c3c3c41103464400390307286011000f041118400d500350b07a02e40109a00b001034086c8245225407200c5c1c14542080c006118104000c3c083e620481000d2a00040d01c1da030724000035040ca00d00720184d43d03601c2d1000680d1004564900002e00025004d0000c0f40c0c44183c292804840d02c02554000100c1e58016036010f02080c800c002e40702d02d9040c002071000550615040d10391045520f8061a45101e0703036911884072450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 567055224 1250 567053974 567054041
    0x3083303060f0610271403010f020a0f05070c0e01121b0605030c03071e020a0c0f06050306100306080303100302040510051509062709220f15 62
    0xb0300b000d00b840d082401c000011a0801c2851490402070200110726400f50b0008003016403030240280908001180e0340b850718204603801b03441050b00a50a144049400040e02d00807150345c46459642c403a179407001c1980c200c0d0310760044072040302d404803000380004410151281c20390183c041d5454640c40070803d0b141402c00070503469800140004a00f0081050580007000d40c0e0340440084105680c030303624903201b11070f9183c80b00359008036914841404505c07103a000410907803140c4600c4914540e15100e5051807114035031441b4541c00124200b000030308609040d42490f4001c20941004161280c03156000340c00d58004888424070b007020903900300306606d006d005907504100c1c07880da012001c034188030108404c1000250400100781c070021f001e07603064880c03208451481c0742444444550343c0c110401e1080123070025810511400c1c0f948040748080015440071103070101d50b010080311020301556508100102008162420305180000440c01700c218040c424994009c0458105c401c00c1c43c4a170b04030302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 567056474 1250 567055224 567055231
    0xd03090609080c09010603020c0c090c0c071d0402121614090601050a0804060c020a05072306040b0d150504020d060e010602120d18170406020712050a0308330306 71
    0x842e0700007a441605074039200140c6064906e0b61501603658600c43da0780915120004d001140c01800e000100309003210120094200700000ca4242c070100307643c41c10212948070060f280074171001c59040c0880d00510300461011212a42d92050360403022400c00c2400d41007a461b40300031604030044030581c0c203d2400d564103070f5110800b42802801e2941049005203d00c600410040c516a81c481c1d910004074000c018030080c0b240e211f81150800d40e11003007641018800b850404915101010144e4500d16183c4195810307100100e80d454100709074210000301038501c49005451426980c0c40204d0a901d132070000f01408035030000080303044e83c5802d1600444080583c0308500f1900000300070b03105800c3c0b034811940140c03410440400d00e43c09000c81e800c408095858010541754034a451001b801010030080c00c1119007076000d9a10295a40b8002504000c040c500200150080304042d00041e0040d0211900038900d24508000703840d40c95840316008100c9506a20034030f02a85547d80c035840c2c104a5643d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 567057724 1250 567056474 567056489
    0xc0b0406120c02031e0c030408010911221104051302191b02040f11130e010e010e0106182d0b070215030406020d050a05060108061909020703030b0d03090609 69
    0x16810182c50000c1d00d80c01511260111446090083d00c0c01302c400c0401d4801a44144d41034079a2686c0c2c6288441c02030070009011180b00c0342d1030801c03041a1405801044040e218981c80c48010002056008000c210310140320400c00f02c02d010100e641d85860240400100b003d100060ba5483e08a2840701413800840384101044100c107490314011b915601025260ba0303041c0ca011903a40c4440d20030718060002d010291820000c0490361542c4104d040c0341d807000b2603908241c1c482c4a030340c0341c10030082c050600340203500042415000400400d03210300d8592001034944920345040a481d10046500811004c169002024900541400190807010314a00408079210310f43d1914a4950101d0b008840c00402d075040c082c00400000c0c18031405804840610785000700401c082c0c0390001e035a20040c00282c90550006400d01b00040c3c0c2424002010040c00103c19469002603207402000ca000e0751000380200c0801d0385a002c4000c1940318010040d4840780709444110b0321ba0b003802e10040c041d514030390105a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 567058974 1250 567057724 567057731
    0x150403120c050f130504050f010e10060e06090103140703020d06090203060a05010c050a0b040f1502031306050606130e2203090e0a06150905030d0e030c06160c0b040612 74
    0x40d0015004000c982c1c189048800f00c6844001031181c06902e109241d1109800500b01030403c5241070a060115068400c201080380d00b9480701100040c00c6401400b641c80450810f4041023898a4920090030101005240202d80700c0424050110040320541d050804a6008683c80d180140b2034006c2201410b0580030860840c07600c8800142d90081c0b034410309041c0082c550a400a20406014994140d40c0000034800c10741454074000282c00c13100c007019107500c0d60030421080307601118001c0380c0c0a20141c04040c0c8406201e03443c2d03030005007005032405e40e00c58020014002e00d000348400342001441201c1842d4880e00d00030f010031004020583e400d810f0322104100d041c00181d003210151060350010b8802c80e18a41d84e460425008100b540c00c00484004080c410b00c01e1240d002c1d02c00001e03a0710a605072022440612410756440200c015680d134980c0026100524904000c40503143e6101030703400301101d0404c3da8646041e24400d40d08291503000d00010b060200c9500601050a50030350381d4001c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 567060224 1250 567058974 567058991
    0x30e030d110c040e010e07120204060b090906150c0d0c051203060d03081018051501091505090d06060305060f10060516020a150909050108011a090702030c15040312 72
    0x540310300001c50340521070b5136a0f40350310f13503100c07025802507048483e000222030b8101d44071148140323840300910049214900b8032a01044410000701524101103015048060380e40321013041240540000f00f440d07030034000506c4a000c601d1030410200e40f0b40c00164032000c000110314104141015810a50030341d800208006200c083d840300301100803081d03010300d011001e90720b440c04060401d984540c006844c0b890310300c03240384c1c041c000c03640020b00642da0ac0d50f07803070036240079500190340301200c0340704000035036039480000d100365030040e00200002c0c54001d004c04000c8015039114000c0b219276400c265500c0d84403a04000080c11413020b042d40200881035030309085031901c6801400c911568411614500303010405404640352010100301600152030711000030004010010300060061181d01c803020304103000040e08184c18421890340c2500311000c042c05c3c000074800e007c0e1010010340075500314402000511008541840300b940d0300860005499840e00302420020003042520b14424001031509410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 567061474 1250 567060224 567060257
    0xf1707030506070f020106050a0905370b190b0c0f0a020d020d0203030909040506100504060b03010506031909050a170327010e03030a0905150903030103030509060c0a030e030d 77
    0x2510b5110049150501e0b25130b80e0038100300e01500d8558807064103d9405500860043c00070b800c4035100c0c0c0b9803290313440b48450001403505050001d0b0034092070403000d40440005040040e4100c0c034541c400c080c3c4181c0d0302a03035212003100000d1b09588900f200501c0868071404030381080c41014442c00c4200010700d4405484d400280e501d42e04070710b00074442c6200d40e902404544083c8180d42c0c101c4802011741d0b02034900340c140540c492400b2940d440307444c1103500011039141f0f00351080304266a24a11070b05d080da0300b8003007030101e07552014000c40c1d40d00810140f2079042040e14040d0905192050010f403030301d101d05182078644204007003003a000041081c000c0080e60f071a80c0c241d8401d040e41000301c460841c0d012520050040004510444150100000700900f4412603040840018441c40031601d4020081c01944a604020384040e1071a40003080100301107403194024121507400241105c0ca0702c00307202c690728a000c80304142180802c600c240e004a84c2e00e02400180036819490408940b092028042c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 567062724 1250 567061474 567061483
    0x8060d0809060310170105040c05030d091401030615030b0f01260c0c010903020c1003090803130516060201050711011a090c07020a0b030901061a0f0c0f070f17070305 73
    0x71034010100400042c0c1c12404890340d5400921030014800c103404081481c05010f031100711070031b90b0034060180d800501800c1c0024951052516582d0384a00241070064200e8400210482141055118007000c0381822480107000d079880e0454030005000510b0400f03100401140c0c00b011814440011b01d035a14090b480034150522032154078205500d80e030341c00200c240c070340101d21410040f98a010003000816800044284408000b101c2519140e0403044084041d20ba981000034850003042c800b00701a0031207802c3d8944900e10600c02d40c0d0b005262421483e0700601c46a04c10001070b07458005000505070000c45c0703401080340c1c040c024440c510381040d10f400b4a030110080e00e801001100d0018082d0344108095400f000d41c0201086041c40e51242441810781040e6003c22165281040000b520714409645203913000034070756102c0c01e2440d0142e008005800a4045140302e01421290600f503443c1802300b80080c011404d85c65050a081c0311400061114420305003180382d03c03940d000d04c041800000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 567063974 1250 567062724 567062737
    0x1a0603100f080c1c0c030c1509050301090804030b0702100c050a260705070314030901021e1306081305010c05040f0806012607120f060c03050f01030602130b07060c08060d08 76
    0x289090b80600151600b28454041c6600241220310084800706042340a20320300808005165242c1e800907031504201400c0780c40c42000140891010001000000e01224484d90300c0710845c016a54284a0021a4402d651054200000040002450074142c0c0e40210440846010740c080b02040c07083c8014100301c14a201031b082c0b20600130302040c40f00c1054441c081c041d07404404c10410039201e0404c034440078040e403c007003e02642440700d110a0a9240d504005482c2d031728141d20b40400503e0b143c00015076003400041e00342039100500e6070900c1c0100b202402600700704001940c5003030b520f40ca092582e02e10450703160040400c07070300042e00400c5501c203244545042c501d504003126036006c0818440341d203030452991024003142c0030f00751188c040c4601d0208140c40d1600a5205002c102041c900c220201c8004448800200b105400103001181075a03001e8440800030140e062086c0751140103c01040d0003030031040300d1954803000250201c560141400382c0003d010740c1c0c60060b00c069030350f4041ca03500450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 567065224 1250 567063974 567064009
    0xa0e040303060533160501140105010906050c0606041a0d0f030f020a0302070510030204050a090515090f041403270a06020105010e040620180f0307080d031a0603100f080c 75
    0x41404420000300170f98503141c80380d01c0300c001c00c503c402c4d0090482d80b107142403041c140403500440300090281d000300101c58002d401c0801a003e56a500710401c801032400c1c04050114801e5540d1051960300c1d47d1155030080707800350380701a60024080c40d0062004030f0000d551000c54102e2121070300001e4000600078141c030700c01c41d0200090707050100d0071002400386502140e40100d058800050300c03980707584168002c20b86185102844000041030248a00c42a80c0c100440f8140c0f600040106503c0700344044c954100314103032841d09007100550061103048180c80310780211b12800188440c43c10507807060080c0f18a000a1241e58501a1002c502107170041c00601666290203004c508404052001ca800300c91024003562500d00082c00c40c603a41a000022a024511314103c40740645400588c080407600484e009008080c4030040447c0500030070603030740030082c1e80940c40b00210399602c0042c500c00da8100305400003552810f035046180061640c442c2005400c900880145034807414503124906518 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 567066474 1250 567065224 567065227
    0x1a010f0318120914010302070803191b171f1802370801050f040e0304050a090507020d11030a05030711010507031a030c0d110a0e040303060533 63
    0x4840950442264884000c2c12401800c4030101240c0c1c2000200c41522024150520401c0b11540150100d01c02c1c0300c00546511418030020b05a280c0d41640c2041281440c0d00108070980041911030114445242d064041207480000c4840e191402c40e0303803030388000c03d0b52508805148030004416801e14500a040e0340c8080c40d0a0402031603015011200c00d401400c80fa008240c120b10500c80d20079004480d110691100c41c560443e045106102e4030341a900000d0402460b00900d80400001b030115000f603000070301040c040019240c2d200f40c80440103101300040817034645040c1c00003d00b01112079190701c05210159048200c07d9900006490450041e81403a5983c0e848440c001d89140044003440700166003171030100100d0301c1d0f01d500031042d0b0004508004500300e060340101502c03440300c4001c10341c002e14415449004624a048410b074110307005058552602d481d1001c5544800d4121829000701e41c84034010004d81c2042000d1884c0001c10203480780e04200817080b030f581021203104154820040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 567067724 1250 567066474 567066491
    0x1602011403090c0109080604120e0a0317030f060901120201080402040b0405090a06060b0a020a020609040e0712110901031a04020a080a03120c0903030512070c0b0a0f1a010f03 77
    0x14200440980032589640c40c1c691a20001850761000e040740814009802c8480015a0440004030240100c1d44411449103401d12107e08541d816144094540c0c000318000b0b00001207103624a18224071340680d00080c0da070789826124840b03e11005040a401414803100422240310084d494061a40d424030b481402511540000307406001211000e503803240c58601801500d01000a080000510441c6d0501c9225a40c815048141c080c0320360800260300801908001481e00308014032060500410024019040c0f1600b03c6c45d01526410110b0a010502500002d1283c40203540601c00c0040760091280d40c15980c07003052443c10141600595034a0402050840d540d0040180282004600701c81040c280c0303042c001d03d82587c143c450a00140b5000c2c1e81c80d44284100d400900740c03034040d2241849c01c8081894007414880061100080240c4440b9000c0020311425103203000b1020701a01191015900e0f02c100d08495504100040f181c00300d0080c0e41b42e40e600090204040d21706403e0000d20100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 567068974 1250 567067724 567067727
    0x910410d060f060f080105061905150313050d020f0106050d02060f0d1e0207140c030a020d05030c01020f042d140d080a051b06010b070b07020102070c0f1409010b160201 74
    0x707440e044000c1281340d503403000c07441010550115200d040111270841c00728507100d0426460030030324091039030015803000780b040300c48201800940c3c01a2400c00d9070310a595546d11064140301140a0850042c0c1101281c03c0400b0424000c41001d02002c459040484500d0341c001201c910640d201030f40f4641c40805c24a00a00d400c2d40b1500401051802d81c0446608030030b0000b0003944441b000b15028034020320345000c034203130000d00030400c5d980140061020903519020480d0a181200c4101d68900c010080c0440040b402c0c00640360360003a0010f6a5165410945c402c90141d040e00e07601002440107040190001c800e4070115411210f441d0018000c4000c40004039045000445001d0302048000520001055102000306000d41600d030581400c2460b209050362201b80078461101011014420b4034040b039040e01c241d0381c0001080c0001481c100b020368807400c1000c8103030720070002c04c400c0c070004004140384084194000030b411110700c0c03804c1d0b040c0a031501c400d01a9041407140480119442021079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 567070224 1250 567068974 567068981
    0x2041503240609061101060f05040b0a03061506090b16060e07080105040803041202070b03270f0601241409010e06030a05070f0f0c020910410d060f 65
    0x41c10140400030105446100140036800c8a00c1a040000c030707400036612034981c0c18440c1c20260351800102101a524140802c4047c1000d4010303190300201c841400400240c0c03512072140d0034003090503581076851824101401c0707104564008148418100503500d0071050404203005090340c441703400a025141c0380d0080c2d2400d0020f4112240561802d4240010f0292003400f8601c114451880d01c4845140d00c02c00303d03181d411500c10010520014000319402c5400c5606031000c141078440314400310aa543d440e1403a0141c020480712171030f0044801403200c65808070000c1341c1b480110042041d0b04005070710040410320700103980d0140580209040e06561700c9034008618550340140500d44a04003511060000d0000742da8590200f0b8104041c2c0008070b0013000b00c0100840e250f220200140c243d9024409218401021a0300c001104807001c2091090b0001076060003034010000168a8000c40c0809202d44107619112003c4115509004180d5101c01c5a180e510b9070011010812440010242024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 567071474 1250 567070224 567070271
    0x70e0f01050d030f140a020709060501050a050414040b0618040b03010506060d2403140607020c0a0b07050709020c032215050a0513030b07032a210906051902041503 72
    0x50700140b18800d8950010f07900b020341d52788200410040f0307038540043d0340900c200103055002c5407080c8020415003054900b405000130015001084840d075103400542030313510080d2407101c2020140c030424031608080c1704103056908154000c0240742404800600c1a00031048800245a00c445a10390310708448d418285540f100890b0003826140c9900c3c0c40c40c80754051100c0c0c03072402d20600000650f498030018000d500f954000d045000210300300242d0712550340c02440185c0341c0b80b14201000403c0a26032005128070103900c00a103850721050340403000c007507c01d00c1105450700d040f404140001c1071180c1071101c0701000c0d8241103541d0b10840c1401c1c0e866004088208040400790f102c0041448910034019100740b140f81d808105103403400381082c5802c00401da58110300034084006810390f50080c0c011304024420104503099010b841c108440c162000844112002a214801d0045050380e08502003c00f204100b010350606042487d030b001007507020b00b104810185c0300d1003003252445014010049 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 567072724 1250 567071474 567071507
    0x12110f070c033005040b071205090a0b09030c04020301080d2f0a030801060201020a1205060f150d1d031909030209090601061b050705040906060512070e0f01050d030f 73
    0x400758121645031810a918480c103c0350480d503001030f142c410b01c284225402e0305c030080940d0f8184525511103020003910007030030100703101040002000c0c6640c1d040d0824000c041c4505041d6691120340107150902c1d81144400d402070303006200520901e5404264044d50b800301d8602100201d60760f140c3d00c88012209400200d03a220014000d2512010114050522902039252011580d0f60303000102e08074401ca10340b400000d41001c01480032103840c0e0700000d42007040200303580c050142c2100000c100c5465104000051040060b0711a04000140a561480044a002c1c0d040925500c0000b07078403807144951080c60003a00b01c0302c26440d540501000c10246402500080c054038103c240903644071780038060b1002290103655100026a0400105001a5403090281c08200d1810060001a10155008561203906c5030404034041c0c0f145080550009000300091446034070300794039020107510141942140c1c8201000502c0316495115107145134542c1458800040d94a0060854007207a1914000c0c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 567073974 1250 567072724 567072743
    0x1c02030f091908040308091f0f02070509130210051909171203040b0c0f161b060917011d0601032a05010f0e0301020a020703051002030f071808010207060c12110f070c03 74
    0x3901680314400e810030070040e400b0bd901031390701d990401180c41c404440d8080c20014002c00d503801810008541d0045140364241181410381a86401b02d500f03a43c0c41c1c1c404000340050804011115100c0710441c0224500b5015041441609040741c8040c0b0002b4800f624020740107001c02c43c002c1c4000b088404101641e0303040e03922031400b0a07034074a4211a50a0940300c141b000008101042d50648414046400a1310390076400c07490004e4000c00300c0c2a202803020195612890f0285100f4040c000402200f08200544010741c10b600d44010a0710b0446501c8443d040280e0786080c01c0740000a00100362242420072608140100b81d0449840b011011440d406500100d186081c0540006025081c0d03442403041c5c0c2c1c00d20003d08036980803030008031207544821109102090500340030b40030280302003d1058802042d20344540740d684c26039110301e80031500306079a0340e4990f88082c0c0c0005003e030140102402030008003814007600c140d0740070b20781d02c01c243e904002955408110103c500007005540c000350a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 567075224 1250 567073974 567074029
    0x90406020d0f050105060d0b1906030603050d021c030207062c07051207302004150501031a1503062803081c02030f09190804030809 58
    0x90181d080084078030001e90030652281102c4205001e03040c103803400034103130b2410b129040c0d4200c00a820103003149070f000f08031103801c20300c40b1a049954030058900f0f901d0120b0600c1c03442c5007252420561806140c11034001007039030310400c520000055441d444600e80940c40303201d1424802d0052040d140700366040b032603920342c8810140868901440d81120f034004d45071110fa0349d00521040c1015801010303200c0c0c2102c1010b010307080c1c0301c1429941069170390744400c1c4001180510003040342e0481b81e00f51290210241881440d02130049030030040072040e6001d101c172507080d0405161400050140c1ca0525840307016150705030240381c007000d0120070018440360700c075900e00c40e01c2d0302d95600035680a40135005212414241c401d0920824032510b003c044903210342407654803130520503040554401c40c5440c03c807a181000c4100f500156000d881c03008007400b124100700c95420f01d4800c02c08054500001c40c20342c014041f03a4508280e408482d00492003941c0e42c0d00c40c000142d0034280101d03481c8814141c0c0d4444 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 567076474 1250 567075224 567075233
    0x30109110415031b030b0a0b0c0118030c060515032e090303020913020c0312070507080403110102060105090c160c1706070810031509050a0c060203070309150801060c0c03020904 78
    0x600d0818519020300c00c10840304403044058486c101019601f000a01504000d011000801040da00c409100001000d180a80950301805501e5005030005044c1c22020001d02200784500360f08543c8854102030040c00140c0803d807141c00c0c0080c1304080f120314a0a5440000000a0f071071f0032100340c05002c00000319189000ba0003904060314403401185518140c01000440d80b088070f11002014000310708205107680c0c2203101ca40d00410000400006015000c0040e003100043c1000e180b0800c1d401d40d20000722400249001c005130b01882c810042042440011104101100c0902c0105a0b052016814a0070421078884c1241e02c40c900008440c0440781068001281c65401000d4a42e1000c0c01502c50b9184881300000900026000d82507901b03031015071590944c044103040d48610140d419620304c3d41c64898000407190b11140250700700090314410181e00c4220080501540800c0303095142403604003c0004005010f0a024840c40d80700305001c1c401c00000b640000c41d0300800c500b529140910300b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 567077724 1250 567076474 567076481
    0xe1c02030d0507050c2b030c060207060f0f2c030c060a060503120703021002070f02090f070311070b0708090a150207020a06230f090a030605060a150503010911041503 73
    0x2074031940119041d03030ba01454400198482e01c420440c3c6d48008419035040301121030340b103000032006d010006000500044450014005081c025900000c414000002e09001c0c1c400031101e001030140307001d91904001d500c27844624081075496041a04002000008a2841c0714045e03964165125140c00c008546419402c030600b44c85044d001d4844605946020f9181d50180840040158204400042a0300ca960b400340c401d86000b00c0011421010039004070b1150383e0305036040e031150003c0304104121140c05020385000b15022040391880d0560948a0310605000a000f0303200700203264000c40c0d54400300300309003c08030340c02009902a501502c01d0010080d48600b0b0128082c07130301c3c01030008030a4000c6419400440c0c5c403001d40b01c4409007040f94890030351b000701881c641c4c65000b803011a40c161204400107010b1071046e140000d203814524100b090350078540c1c2c85040c588024541d00360070280d20109807411100d041c040407441e000c940e0001d1030117006a8024445d480362a40e8450300b0395600d0340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 567078974 1250 567077724 567077737
    0x181e02061c0c051603230d090506060f0303120c0906030109060311180f07140a0810140307090b010201140415060602191b0519091406010e1c02030d05 66
    0x800c02c01c90341904000583e0240154a0300345044030404c0640e2011078003c040e401c0d4000000d074040080d00040c6e04c150400e40d08241c016030012a81e40f1b0160b82007000030440b032a08243e08590304030340640d185000950702c1c41581ba8901604240902040344a1040810b8402c2c0410081507a602c940e150b004120051905100541300102d81d150084a81c0c1080d81613510900350000b00c0550f2595000004002104081c0c17003142000018804107481d07100c81e1340949019000e07036540d1892414242480e04100703003140c00000d000300151510142599002446070708984c42440b01089607442400140d006100d042c02c0544500340e900204410445100b0200b582007070750700410407460791110706c101c0e59910310041d142c002032001c10710400820600d400420320f401d000e0030320f20261500e41010951140750300c5000540500e4500c1c050103a810b143c046d1019a0700d403440c0160942c03030442c0c0003c202255106d8014000c0948030050043c1007500e030301065850341c003c0d04903030b524025107800a01650103803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 567080224 1250 567078974 567079027
    0x31b0a050d05070309050108150307062c0906130908030106080702060901091e0804090e07030515041e050307060501080d03060e090c010810080f010207060f181e0206 73
    0x2962001ca800d00400903100802c1c0c040d968280e11505103001915880c2c0060480c00d414802400c402e03c10b640c040250b90042e101584d10709090586a1425900540900c00c035111f0f54000f2440364072042c2c48490300c0a030300c07190485941000b1840300942c50000c03d0b003400090032500d0008004140300c1d80084d0034900940c030320b81c01c036500e9039130b012003035400c9940d180001404140340c1c1002e0004444810304078039120713000780074040c0b415a491340b400c0c0c211140315050801036041214200144142441281000400f40d00451101c0c981a6681000300b502c0800c1c480c03020950308848424440104103a901c4154014010899075031a00c412a03601c4400200110020b410a14042002c003080c0070b2541c05007411400a181180250005503140e20005000415901707a4800004140b80200f10039081941c06100040c0da0307a81c01d00b06401a00d4041c109403400c5400c00328400b112101407140025101c0d00707c0c1905050a0b6503070204000c1c0413492401030b40c04400070494100f4040c0b10290721540c601c86 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 567081474 1250 567080224 567080233
    0x10203100512060402011d1201060303090503030f0d0f0e0d0206010f0906080303010b0306011701030c03120e2223060306070207050d11041407021c03060b040314031b0a05 75
    0x441e000c00440c08003625a0007030030342015001c00c0055000784103480200d240e107901070200200080208046030807d00380518640e44500c4104181a00104200c0281c10141d01940ca80000304020010f00e00c940c9440201c0d183d41d0300304064000001c1e9014400ca030803c01d0a4444000140400940c0c4040130301482c0c5603942034aa000614940b0f034482e0004982c90384000d9411680780031480704542d040244040d0601000d8018481d440c0c82c00710101c1d019510501c66aa079003411810030310102d28400c00010207003e090304100c509139445000c3c0f00c182000100c0320384000f14030300c1c0c48400a01981c2400c42000c8084024600c018814503910a01c103440640840300705a450030404c0ba0340d00b28034404c464100711981c0302403010443c00c4041e000304c0400034102254100040e4400d600804046540c0e0340140c0000307074800e001603d13004044030020440c0c41c007070104030305200d4401c0300f521913444002e016011040c03001100c10014010f0754086800900f5004c0d085090440a1352101404a01100c46002e07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 567082724 1250 567081474 567081479
    0x4030e040504210e0102070315020d0c0507110102030909060f12010c030b010210111e2b0c0e150a0201111812060708040b13051c0e0109030503070605180a0501020310 73
    0x104281804e000a4164010001d141c515210610b154103001a141f01c1a5020030090b05201114040c6540804041c0e032078a540b51002c0c1000444c040004142c1411508100100300060362a00701041d0060000c075035003001d2072003500004500c904242d108001175400c02142150b42d64140c0d1203c0d21400d000c0c3c0076201104400c074401821141d2515005e0300d80d100a21014080000800c08803c0700d01440d01054502000381c88003440c503d1810070551110168159644a0b00149003c2d581e1099483c1c10914040050b002c009030300740d0450340640709807180101d1803005543c401d401080c1e100740c0c800400c42d40d0714016940750950602d0a10224016211180a040705c29000525603204080e01c0daa0346170b0a8595030b480c42d040d03440203003468187c9800189401c020410070700030221014000701c0505003040350044040c2507010114401814005203c90410216102000700c410301e941c01280060744c1c2c1c0c4d8450100c1c40f030707801c12941b1507000d1082030605400c0050550086016a5100c1040c0081e140d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 567083974 1250 567082724 567082727
    0x30e0627070b16030c0c0b07060f0b090a0f0902180601020105090601060f0f090e0f180a0506040b041712010801140106021c05090409050a0b06090f040b04030e04050421 74
    0x4210b441090350b500300400080311403550b05440903111a10925044213800038a071188003c1160b5904000548800064880d00b0000c5502c594003440401780001d000d00c00840c00080c0011100803c400d2443c0e4956800c401d6030000ea620003103030b0b19401001c40b640d94003054484d0041c00700c21903200e4050342c40c11000caa0850800a0201d04071015540ea00080d2780d40700704110b50b4010b02804c49820b2000c1a00c0c04240c4c22002d4050510849400c038020071645807500c04000381e00404050182c0130340050072403002050010840545c490b0b000031540e9010380307507072801c1d541c080104103048020707050214906c114000b55012441c12201000002e0000490700132103541202828030441c40542e104070043c0785160000030301520910080e0810300d040082c0308020034207a03413403140200c9103a00700a100a0410410600954016505594449240c03404c803090070541c8a0207080902000070a0740020700301403051b120b100c1b440b18064014001c03818a0301c1d00c402c910400c001d19400026054503d0703403145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 567085224 1250 567083974 567083983
    0x2071109160e01120624050301060e12120c030a091e05040e0f070b120a0c090b030907080d0f0813030801061407021005040608100509011401030e0627 66
    0x280c107005885501c002180c002a41c05000c0506180d0500c0003005506010499a106950003050640000b100b06002c000c0c148040030480f0300d600050080900041c0815a882051241c0b402c1c02038448458a03508030036514a408144d0320340b00a00c001c0090749844650000c80641204601c0d6220903241a41301e437103840300e01c039418148071403c0581e242d041001c1d1034242c0144201c8082c6506aa01c1011141c40541c00c2c41c4880e08032503541180064110700a4241840701c0f42d20840b44c142c200700056241400400c05041e920881d0030110010000c80d0004906020b03800013880e28108460105810040241210000601c5400441d01282c0000c645403d503604500700d1551595910900b603092407010740340c0d07820a10204041200034803680006031554100c044695807d515541d44440c5050401003151070010259603100440120070880d0b500c1d540d45081c10b444a40c94000101b4180c00b0048004058900320325100c0d10603041130103600c1030001c052249000055101c903c610b000045000e82e01e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 567086330 1106 567085224 567085231
    0x405060115080f010302010e3c03030702030a020907090b07050106080601080f0a030c03121a03071e120c0503031c0f0902010e0f040f020d02071109 65
    0x1858070300488044451003454884040d00d49805448086401031000906102d0a40c0510816a41d0a04d1200c60900d179400710f1070708500c000b00e01d02c2030303504140e412081307010100d4800d078480e0a01004030761913240c010b8000d0090382940e44c280a200c202c024034000800914203008100507407603900504000c0c0c050800410040d091a03030480c02c1a4069010401a600038400c00300d110707001094440503103803d03080039500100f45040648419a503a941010b14515003d0007041101d000580000401e4003901103564803504d850409c200000c0c411410b600403012468100146050510380403c854441d101880d220f0342e03640702192641e040701c8030161480c19180c4244500766503d200310030504114174030170720400a180d00080c3c104004607081a003c1c6440d4489141f003602c0e0341c0c0150b004030841841c11940c45140e43e58070070094000c80d80c211102100c6030014440c0b4034120401902 = true := by decide +kernel

theorem cover : BRFrame.Cov 566906474 567086330 := by
  have h0 := BRFrame.cov_init 566906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 566906474 ≤ n) (h2 : n < 567086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
