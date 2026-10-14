-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:58:13.441441+00:00
-- url     : https://prove2.me/submissions/b4da4bf5-ffb0-4ce1-9d85-04e81c82b55e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 22482020 ≤ n < 22661876 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 22483270 1250 22482020 22482049
    0xb040e03040510140304050f070f0308040501030203040828030b010203090906190306020c0601060f0c030905040e101806050906160c0804050306040f03030f09020901140f09041a010b0c210405 84
    0x200704001d016902e400070700c10100501200f0200ac0c00710703802d640b20710081b400356001d01414168000081014020100e003035070a5040f043d0b0616154000540009030312800b441e82030008681050003040f5658000f2058a0440b50058060044c2da40c480c41001414542c80b4038400f9006a070b16004004180310740018040007448000900655141900061503083c114a0001c200720b0f03280100d200007076014520508580046a000c100707414030581e45402c0400f01c51204880da490030000c1004056201c003480c6c1010f0042004029503528010119121f42044170b48984030518001040342d49400392401480080c003e450f1141096168000700e07290200986066503a00b15451603802015414015001642c0c61200240308000b0aa404110380309410702400075400e00280da01c040725112510341c3c0c0c52000c0000c0800c0c1c10303401e11303040070464400e0000a05001c40c24582c00840c001e5a1401100c0a590101004010310750380d240200c032040090000c502c100740c104201c0011140e4555680051a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 22484520 1250 22483270 22483273
    0x15090108060402010806010903050303151c0308062106040b0a090b070503060a0f08070302010302180301060e0108011415060313120201020c0f0705030d051602040207080306040b040e0304051014030405 88
    0x2820b0500014007a88401005241003001c8400d043c000180040143c03908a003e0303007184646062a5400609106103103810004500030351107440c0141503001c0b8615014034000d848491541d82c050080e005418401c03140c5100581c00324001c940000c545000095200c2018600051003044035550780d25a48002c0d91400005080401441880c0c6841c401d420004c000542d0f8243d2030702e150051a40c0c64010900c8064141a1b01040341080118410040c4018490040081190607200c0d0000600c05c9003c0c041c0030303129843c1c00086d40312102c00c03040781406404072903642425070706800c04000301c07548010322480000401c4105c403000900454111841e00403543c0002d40c84200310100e0340d10700302c0c1d14454041c181c0d1051004000e41c0d2008a401c15a1849501e05107a5441004440a1010b80640402500103100140210038080c50b1005907020f603000316410301000c0540e904010540f040050310b64603035002044200454904091703021a041c1050616040c10b82a030103224805400843d0152400d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 22485770 1250 22484520 22484533
    0x10f0302060702060f13090b10020c0319020103091203090309080a0201080109050903120a0b0f0a03020a03061d0607020309040606022a011b0507050901050303130303080a1b0e0108010504020f1215090108 89
    0x249c9030503000700c0103451103031009142c4d250200001175981d2080c1025046001004005001564844d811041c142504034010000d00001441d000b8024004e12405030001410810301080d0300c0804035800180d81d40507074a81c00a81d00f001c01190041c5009840300c80d19110030419903403030250b0848214418031542c4800240d603541e00c014802446a50400903108000313680c02400142c0d51007804c181500e800400001d400c10710081d4405242d107000041842030710800c01045a000c0e4000014005000255030520440d603643d90241d9507949050a107481500700848540303403c0703200da40310f40490401458002d2440001050448441424100545440d04040741c14429401d240314050f004000c140c004528200005044802d41100342c0801010401d40101280311442960000c0505c05203403540c0211100310500081c0003518180e0600740400c030302100029041c5864070a6440500720000d40380e14004d20040f034440d9011000380521515003500c0e02400150719a4141c8a01074110040288003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 22487020 1250 22485770 22485791
    0x10090e06220201021207020d0f120212030601021903030b0604030804080c010503040305030c0a0e0909010f05010902040807050105070204060f120302010e06040c030303200d0212010f0302060702060f1309 89
    0x4481c41441da07007110798031199005400503680000c48410380c43d6103845142d01c0f0308151000600000034070b14081c0810415441c4581070124111004440240680864506c080800e28000043c00210341e0980940c0000c00054080c0081458050000c0d01ca845d00003440a0500c00049a0740c005d0b0b0410b03607504070003003030902518000300000007086000742801c13400c1d40b5143c3c0d0001d106d031000801000320b03403801260042030309026500b40c1c0e1800000404040e05481c0c8034100070b009008080b103c01c11181814000119100181700f118103940700a0003500300903051000540b03090740f11040807030f001541d4107000100c0310a08090300e03000c2c2400130400000038009080083c00e5441b94000d110190b00848244400a0080ca03101c00440e58107003004078440c2c24040c02c0910101240040029880f40050035040014090b80203000101c0044d000c40c03103503601c85049011000f01804005d410040c200700910241c504540601503041c0c140c000740d464480c0300298003d103103030907a20030360b8860b480703111005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 22488270 1250 22487020 22487041
    0x10030c06020a02040b040504050d050f070b0a230603030406031509020309010603150612140319020303160206040c0905060a03060603050105011517061003090203030c0705091008060f10090e06 84
    0x2005c0d0f1008803014800da041c82e4803000d4913400d80815140030b210307002446944942003035082ea282c280c0c00a2003100c00e0b2400c5000d44018144000400044041c100729100741c91000c001100e00818010740150b00705420100b00b03500801c0400d561a02c3c00304015800603010405c0e000031407250b9403000020030080c0c5140f9010f6244084004c641d04154141002070020704c20154000795090741285009008014485140341140f007004124484070345080b2004c0d181c02d80000042d0300034404c003000c00d4240c031f0750020100e0b1104010f03240100400d1105004000342030301030b086507401a400a228000c400d42c0c0b907545000701c0b8880e5104581594491004018402098007503050f41000e0b8246644c3c03403003034401d4442a0b19401003420344181d08a103240d0803518425031005900036400b03821641c0d540003a0060a549000a05c20345100342030040c000344d400466103c4c440c04603824a402000c80340c4401001c41c1640c50000c2640506071111072000890764002e0050038403919103c806400c0c1c1e42064000170 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 22489520 1250 22488270 22488281
    0x50306090a1403190507020a23030c0114070605040203070f06120606031a040e01020f07061b05070c06030911060f0903060106020c030c0d1b180e0705010f050310030c06020a0204 78
    0x11030b00107108503e1004d02a41d00e07032551611510f4160380c0d41a603031002031000c2903190042080018980c00d04507030481c1042046111800440444580e0000d00004484207444680400000d54041c0000800a07030f00f90001c0d90814030043c281c500041c1c032056a030202c10b001d903000d0800500d000c0e5100c40146050701c20240a8031003494180065109002c82e00c0c40060141c1f000350150303986216600c0341c84400e41c140d0b1101240010300741c7e5144010300380280a801c0d91084c8011544440703070001c01f95400781d000c680c680303540300403941006031402b5002e500401d60584107503a4120a50140040c07552054014161148042e603c6521110100706152600805030428003c1d580b003003140c1d003225580007500420140007281d080040c0e84540c6450a460404680300e02d40041e50454089003d0384400c842c0a1116889070302003100c2d502055a05560703560600c2441e020400000d541070016124000440e4492200d0b91500c604075601c0c1e03503071030b000382450b40700b0130040c2c0040c44082c2c00c500d80390260 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 22490770 1250 22489520 22489553
    0x30c040608070b0d201b0a0f08070501060b030a0c11070501081b0405030a0303050a1a150f04090903020d140708030a0203041e060501150206190e10020f0406121a0108060109050306090a 81
    0x201f0901d40c0b40d5491961075610082c02903d80d0b103020a202c42000000d42000e0050a00c2d1000507840741409000076014140a80c030002c00300f4800c01d40a1041c00b000070300c40080300d03416074502203162202c010250020301300080704580c0c480c0421001c0b80503201005510713000c522940c0d0004852501c0400c2d0310851302801c00c2140c0340c40d0b040704008080e5590810750112641340c051125555101544440c2483c403450b0310100c0d965040010307a509164020420110040031500c44000b8108000c004110522038060000e1200c20240b008c54801c51140d409035901c01c0c4180001c450401400c44103a20000c4590001c0b144540c80740c005020300c45001c1002429044140001c240c1418400e04030500f1098400c0b025510325501e884010240710b00f0411101164030680d000c550b03030344c100500120300d40c0c468060003020800c41003102000990600c5042e1252404410b038100c480760780c800448208902804041c100142c114010a103640d051205a003e0440700c001030030b04089078640203880cac6901011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 22492020 1250 22490770 22490773
    0xc14010504020d0b060301090507080604030e0604060203070b040c030f0f050f190605040f0b01031101020705150307030c030e0f1f1803140d0203070c02030c040608070b0d201b 77
    0x41c8001038071402d9918141c80d03440301044407a80d0751400440d0060a01c13203409042482100700024402801107000c900a601a03031382c0001049020043c0203d6100303510840d030050b4020420b0b2000b04160049081d0031900c1011452505503a80d10313080c0032140e419000380c031802c400d4440302041103010828008a503603620003600b03001d80071400403000c0303003012400a0003450712080000c0411850301d1107540d0947d44200104a40e586a0030110494a407280065016110340340d070200e0286458000001c0f04000891705038915503ca15044020341a180c540c01d051607280c1401d009088001e10850b003602c040d4000804440300b10701c00411081245054100c80540362490101c2c90180c070700140e90303080d03403d0301f0250702d08840540510342d02d03c103039060b10f402d061011080c0000d850788241d818172014021412a645005440c0401048644503c1501056408184200304d90095a00035000c011110080091800c88242c1c0410200744604d02888401100180348001d1195080048148442560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 22493270 1250 22492020 22492031
    0x130e01050117061c05070f05011b03030e011d0309041103060d030f0e030709050601080915010909020301090506070801051c050309090c0d060b0901030c05130b0903030f0301060c1401 80
    0x10018207805568180c2001c05106800090840e86503442d841c0da48444d00c9901003855640307801c00c00d8503540e0358054452214841d840000340ba61140703001034140a004200d410001031207540c103800030415050140c0565480342c10044c1c00207464a050705a40740440d0296030b41c0d0b42c0104c204812210700c21240c0210000038810b1115a85441c602540000d9040c00d1100b50640801025583c200c201800e403541348c45061000720fa040300c039420940c000e51081c5c0f40c0a82507214084c100d6151a420815011a54070034801040180c0c0d070780e040040010b0001e400040c0c0034807075880d1141000c404407504000f06042d203004100c1418140c14101c1c070b0280764000d10800d00136540e1245d840344a1003403800e01c80c4c2c0842c8003007001e581d2207100700d070014494080704016a035624600b80707000350400144a0301180c907220302140003e010303400b154980d107004211008901d00301b0003003e9541d0802c1c00565014442880314a81c014084002540039248507102d80a21001e00d2130441649090b0f03203241c01c00c990401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 22494520 1250 22493270 22493279
    0x108100e0d05030402010528090b12150f0a0801050f06030f0709050703020d0c030b040e0706080606030901020c060f0103060c03060e0f061909021308060106050708180402030903130e01 81
    0x1c10015000c10a074076140e9500d03190340c001200c0700d0180d0030b00d07a4201d955216424440fa5880e410440f0036828a454110313019645502050150080301d111031119400c0d03100040b4000f10b00d00c4148075244c4020700d1032542e801000e01040b90440b0b942c101c00c8042c0c0d9600c040c00a440c0203600e80c1540404210003e03d006541d0402e204d440b0130052103802c1c0102c0e101c20100309040c0c001e4040d10b201e1700410504010320144a9001070107001c4884041780564504904506030410201c0c450b0240c417900d455a901903281d0209200320f07903100a00101155500b031045014100f0240203643c0078650013401c0c24602c1d41541407040403107045100300d01c04e0610f01a410813000c104902c65680c44014100c1902c04d9588080100d0301111020111840d41c2410840100c3e1a113504d901820244030828001b9000700d03210340760742d0b94902c02805400301050080c028040000c141d10010000c120700d4070740b019820001040402e080e81c006482c1400305400c00f252201c0903200030300ba40d00c020701d00f0888a802070b5141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 22495770 1250 22494520 22494523
    0x70503010b060c1c020102070f0f110604140108090309060703020a110405010e06010507030c020312041a070c030b0415050c030601020f010606090b0901030603080f0c0d210c020c15030108100e 84
    0x804c003180f2030300c0d0080940d81c02014001e41c1911815508400c0d1101c1d19400b034905200107801c4000c1c102d8000d107020518040720700b41003094070259a01e0744100300510305202c006407080800141105480c0c4000c0204100e40d88506000d0000e685c8241c000b082c60f1182c624101990305c094040d4a4081c0c0e151500400031440c04448040d0490001e0a0003a510034044c207085900d210120310103500752254080b240c403900000700050084401c407000c10b0080c41c0c2c07584e1850b161071085200140c8071007074800003440418203222449412038400e004860310120810060026600110707900040303000040200045540c05028400802620b40003c100c8182080f01c060120401c80c0a20103466002140403075060340030b940494043c68002501075103c01d03041d247d43c20203600001d0040c03801c0c003420b1502030301c01c3d00500000f2040300307a07492114010285a05450001c1204451020862080b0280c59080d510389038801c054440403407000c3c60b520760518081c1031606c0c51000444814526110b42078952040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 22497020 1250 22495770 22495783
    0x12151302010905010c1109090607030c020a020603041707050a03020105010302041121070302040803030c0903010c2a081209060a0b0d0503040e25050705060609071e12020705070503010b060c 83
    0x102420021580001800e184103440c188881c6c8070340141d102018800c2c19880011924814981940e044c001003040140498688007901c074001e40002e000d00c0450000307845058030030070001200c40c4081c01c004403601c41034a01411886d060380581d6640b4014010f41c00e05000d41950040c84090141c900b65440307645103d0b0411002c0f101c5100c0e074401020980c840d20a0301254010107001040325180d0416188a0115621020885221758640740d901d000c0980914109420344a03212000310451007500700c1c5920035031485404071106001001100c1c030400000c0081c0e800382200c400146190302d402e100807021641e664240d01d00c184025240c60340040c1c1c00008883c2607540c1c2c81e00c03010ba651104140c804081c042c1e00f60300b40c5000d04001c1c098645952010207007406500601c11100c090312407100344a0f201c01c042d03600e00d0000d06001d90b0703190100c0000211118441081c81e005140400201d1600101c0e0071108044415070050300040145103424081d098021303004035910741c640694060762554135407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 22498270 1250 22497020 22497029
    0xa120f0e090103050c040e0f01020409060807090905030a030f0204030204060612050a02040f141201060305060702060109020405011409010e04050a0b1509060a08090106120c03050d0804020303090609040605121513020109 96
    0x1d1f2240d400000103441842108809459030b0029900d45445d0300c0307910050502401000c106208880e00003480750020f00442645076000302c042c510740007039000202c0180000c40744403e000c1d84c0810001006840d035114002c010980d941d510311640803c5079580082c0c0b10003501c0c281c800f070b0041c0300030b00141c040700f010241101ca0b9030140400342c03030701c0c4000f055140010920b800f43c0b95107020000424004080340f554403d400a600790f41090380c89030b054504078000d42c02000d0008020003058007011200070018106401c0504010740a01c40d8075000400f525000c440c01d548194a880d103080c4a41004c44a502d00300079001011801d1549441c04030310140180d60005040024405c08518070403001e500c44800f404a0b011860082d560a00b0582c4503141d072480200c40501c20252403d004a100d4080f1500855008001d90f1030565a0410010f10350850b5550552140e0303119800034a96035609144180044c118001d88822480001200c00007070380104030800b6549000308210061f80d220080c042501c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 22499520 1250 22498270 22498279
    0x30d0807020d0e28170606210601050907030e1c140403080a0509060d0903020a020906091b0a210b0411040e0619030f03030b030c03030703050403140a120f0e090103050c 74
    0x72121030031076240f0020580c40511500c045c250417440701c00e80410300502c6120195406014411054070209001c1080541205290000001404540340403140c0c2500840c003460702007803080e503090919003800c62603420007900240c01c92840c440260448a04461840509002c504040c51516032565920078020030304100000000d180d285a5112001c0d03030007200c03d10340100400d540c1464040d59418031030300300303900c540d0840700000e5403458900d000c2c40c41442c81d40840560110004100c0d40d4503001800301206001d1702e4084496010824803010103000c00c8804040f40101c00300d0144000c03181091060a40900b0411040c813172208804140d54000701c00356110300c030501c220305180e070611401d500b0017000c0d00d089212102c20705900d900b010f0349080c01201540c00102459007056038034461581c1c010f01040c42800100003141000c58030090201210094601c680c90f1384c2d540b2840203880c2100100400c111546400e803143d400300310141c000006550365000382d41180c0320503640e003800d501e000e07204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 22500770 1250 22499520 22499569
    0xd020a02030f0309030d0b0409050c01030902010519021606090e04030c0f02060a080f010509090a08030a06050901030c030c0504060506070b1003140a030806031203010510020c030d0807020d0e 84
    0x2054401c10031580c1061541c00c10039128204160800c1d01c1c0d40c0a8402d0100d01800d04400c203246107411320801d109507500034003c040c00d592110042d0050700c1401001c0c3e0611800b4003003000c8550858403c0881001e5aa0207008401c812528200310301280e5080301081240c408020300c10319205144440d002901414400220300051403d1201c0a5485070000d4008001140e1142c201d82c01c180d00c00d001b01c0d10340b141c030001c907070f00e800c1880305c1c0d01821940e55503154000d13110304000c01c140c0c000850700224800300200b5050348401c04102d65050030381c812500742000e09810000c2c032446a070380002524007264103101507440c0000040c040c0c018044050311510000c40851501812001450020b40d440350036041307880c1d6800710107a181e84546409401181104c3e0000700c0b10700e0003007140307080020700c1c11610b42542d00f480140000a440c8c4131004055200e01401d0303076880d680401c1004081c0340a076030b405100d443c080c034000f420b0601c9801510144102019038003919502c1040500300c580041013104030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 22502020 1250 22500770 22500787
    0xc020c13090c06030e0f0c030304050613050618030d09050609040c030e0105090d03180b131e0602031803030f040602030c0706061403010c1403011a0c010507020a12140d02 75
    0x20241003070020000d440342500000d100707406404c4a10741c00c0c90f01040c1c0e03501e542109030580e01c1b44040b589007541350300100002d01203480c0c40005090f1000900c8030001c0c90b02c0e20380c4081100c07075010b00540c02c00e008000b910600b06180c01c1091a41036031180c6000007055103810081403090180800444c0f2503600c408511740c80910a91002e003081c214035000b440b113820802d1f010750b11401c40b0a041d500080c104240700c840340f4080303a41c080c40e4590180c50786849507500040300a4011100d80c00301e84004240280707803036200784401c0308500c0c54001d410050b9603041c403849004440181c0000c1c00d900340c00520030401c0003440160b4596010360800b10240e9243d54040d0380c850188102c2000916040c41d14a0110380003420480010089006900030801614804420b5900404440d001e441c002d00800050101c02e11100401ca1005440c10707d0300c3c1800307421007026007560300407580070300164070501c040c0050085c2c00307034000c0e080c4a0606090000b065000300d006494880c40d003204580c55000509000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 22503270 1250 22502020 22502059
    0x8070c0f0203010c08090610080c060903150106080108010501060e03060f07020111070803090709050118020d150902070204050a15060305090304080a05030c1b0d110a050603010b0409050a0c020c 85
    0x362220350050080060160045028094550a07102c1a4103031090000007a100030610400000307071074040008100f1104040200310541c3d001040f015094060005800044003048000d9406031100351542007071981418180c50840340164043d03070410501340c030509155100400c240760845400c0000303140030f603a10b68040e809048014400d1a903100001408028000036001a50003004031f0070541c0d010301c1d604c03004442a102c0278007451440402c3c01d14200840c1d480c5a00a210302c07e1256804102c2101e005110410b25040e81d000034840c0b90001181011407a003032280c04e40c0000303407900c1040030100440070400000700300e0040c80709043d41d50000c5460010100180c40c0103101705411a00000d90f40c0c54031503100c1c0c00c0017071850f10340d1049908500a8810303480c0304a1120304050702e0714400784d985840d0000e50b407000d1518541c028503a040045195215040114045c040c60105503542c1c0e071502024108513a001422140801d180c031034003411180d804a4841180c0b40c040740d440d0822200c108601e03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 22504520 1250 22503270 22503293
    0x4110a12061703070203100903020616030f09080403120206070e0f0310050a06032003030d1a0d060b010210020301030203101e050439061103040302060c070302041b08070c 75
    0x801d071503180301240150b1580000000c20110b80300781e040d00d080200d1584d90074240c5051480c010b01503000003002414050050000e03030105602d51a0204860002c030016108544e00b41205907140700b0002405d1040c030608000c2c0c0c85542c401407004000510304550028508980814070038032500040350518141d50307080003a66080600604208190305040031041e0081c0024402254030210020410a03c000e24001001c007403000a03000d5171405601240d0352000705007980d8000c250503041d030510340c0c40d5182d44440c15070491043c02c001490340010400a03240c08041801e05140a00420050006880c0807510340e4520b100c1540100e00002c0700404490841515000d0318030b8030b80b41c036080200303020741c078603514030702018649101903c81c210882c0e070034505d02c1c10064505c0c24001140d040059510442d91a07400d4003040c810f907800d04d5226400154254000300340310035503511404040c402d500c0c3c0707442010801c164050350682424080000030f080c0d0b00c00140610b0502c20b10410b41000e0103032071141c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 22505770 1250 22504520 22504529
    0xf060906090911010c1205030a060e0f040c0f0303090312030612082106100c08040504060602010b04050c070308040b06040b0402040605030708060105160f06090c1205010b04110a1206 80
    0x6201030350315440741a004000c4200309032444820452901c0895000781829821240c00c04810600b41526201c1039405502c007401c1000703000d036652000100414041071050107074440c0b00d41c0f1030b928200340c1818010385c42c041d04020b000f032216020800000c2e41012400c412650b01c99a8401d040c003040c0806d030001d00d81540001c1800020041040400488078002c11040caa282c0c00e40c2d2001a403540c00010b402d0080b91041d410081901c081d03011b05000d140000b010b540b094841c2031807e62690f020405552241d8040c001603911031589070f8651130b040c01001e07031144101c1d9031a410144036480080207040d014201409800c0500b01107511a1103075042060054400341c41507503500c0d42c0e243d00400c2c95208485e221700040c6000c0200750190f2241048501c00030b540d0b0005110400c07261110843c00140700d40403544a41e54000b61000a0081d0b0b907004020700c86150140303400310850510909460041e0240f902c40da24184c129603091285405580b820001860000c5001007803460300c00c0240380c00e410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 22507020 1250 22505770 22505789
    0x11031c02160f0302010c1d040b03010912030608010e03090a0b0c010204080102070803010e0f0907150c060906060303020f01020403030503010b1c0603050106141f0c02012303040201080c030610030f06 87
    0x80000901941d41042d4141501c80e50081109900c4440c0403950b0050308007150001d8039028418003410b10782a04000043d40f0010000584540155a00038103d03800321002c0021a444110030480000e00f1301c00c140004110074081e51801040c00001000e05000340120702c40c1d00c3c000b02d0820450403095050718050700850000b15602d860900f0181000d030800d10845910302202e000298110800180f100d000b071500304005d01c0080d040c4000e41c000440c85005480404c40c01c070340700901280c240e015504230103028880004c0c100c1d0642c10b00038101404c0407018003151b80100300410001354840101d81c112403080b81e0344c6803140031010840980d140c1007169014032605120021050250640c0500100c03542025501c442e81070309414040d00709424407201c2d100c04805402c1c0c102081c0240000d0805d030b0720515000c40300031a01d610110041c1300340e03080125940404001c1108558006c85100e41082c040c0742818151700d0160b00103a400c1140100040805440340003819201340303030341c00c003d0140c010380b01e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 22508270 1250 22507020 22507057
    0x60402090714040303081503210a050d060e0109060e0c0a0f05040302031c080601090602030429030106050309011401030f110a150503160509060a08060a03120f0201050711031c02 78
    0xc00400701c040c15141010b00c098610521407c619001946202400304a000c0c441807007041c118a100760380082a0f90001d01400704003240d0040014400c400c040c01c030030310106001394148030508003219865080303103030342624280901c102206030b1000e540c0c148403a0f1424254210800b130703045546004030f0740025051312501e04552049034541400110100103907842c010140d0b07a030300045940742c07414030685000d40c008003c14004840203243c0e40d400107500c0c8502000340341c51503c0d60300b45035009901800004a000c020700c0b10101c1c00b809203100ca0840800002d0b415411034842100519100c01d000b8004500c805001120741c4030080a20300410a000b0040341e50b040842d006040c40d40100c0784000b0580100c002c80920a004009440e5544805000541000c1c003901065480c3c95010700060707808101d00500200107401e4010302c6041d01081e9445803006145004064296600a031410081c01b65103034011022410000030707207d500c0c1c007a10846001c0d46440d140c0e40700910400d512107d4032440c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 22509520 1250 22508270 22508273
    0x20c10020c0102010b01050405010c060f1503050601180b060901050306041b0309050c0a081e0c030a030504091d06060402210108060708150303041401021f150f05030604020907140403 80
    0x8140758581d40303020b0f0000e00c0300c16810300045403144103501905000c51050303400750012480030f40c0139000c40b03a02c848001400702c400b2000c0c40880801503100300d4040e031280c001407003100214103041c3c1408051032414803000c5000300004080740110010103040110100000d100d5940c0c9400c03455030642030712151000700a80140080c0540040102030f1030500c294882d05c1a9804d10940103c201e07020172000c0d0546107022114030800e82a175071081c1c03c1c42c0c8a141859a80c0e80c2c1c0c1030115403912031003606c1e21942c0d5440d0101304000d40d54182c4500401000000f24150b01403400309a055000004881c0103030744d41928070b01c00399003040c0504c00c8196603030200000316141e1320004080340a25400d2b202d0b80080c0e40c03504401c11200c00d55041c0342c0c1d05a0028001040046918030b01c50407120014016900d40c1c0e024095801c2a0405c805403039002951a20180000c8d1a120046107000d0503480d0030a5805504120100341e40700000347c8005d00503003400e40000c582d41d21038156074551b500024150707a9140e659 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 22510770 1250 22509520 22509523
    0x60608030d141303030504020d0b10050a0504020715111309020409141003020d03110d02060105010306050609030a1e020618130504120f1803061b140d050601020c1002 73
    0x240d00070103401c2e15040c050648864080100362040b80f20915210681001e560704801900015004a8000700b2102d48400003452210110b4442c40c1c03004400341c03a1380e103040c0400011803515408580950b01c10040d0350f004c07603007442110360803100f1010045222400102d481c41c0341d2191101d5100d02c80c0d0400b40c0802e00c0652500100100c50b1600010b2003c00c3c403002e03d401b90f05c241507c0203040082102d508000508104241c00341c454041d0412038880146003050030b09254003c42914010303000417005004d6581c0610407a006080280c4141d42451050b001180d5100140035020313000c102002d44050100303207214103000ca0180e0241c400e80d10750b00b01c0c14480500040e110305080c0305860000c07a01d111510f8a11850f07116641000011000e61803480301a11120068503448080200c1c1080b0f40c01c1008184225a00540c4520300002d0b0400a90320358191a66000d500d44042000c1c00380c03143c40b0035603042c096962091000d0350002e41902d5000050785042d201c040b40e50b41182c6401a80d4040540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 22512020 1250 22510770 22510777
    0x1508042d030e0a0609081c03020d0501090c0f0315090515030313060815060f091810090e010501080604021c05100218010c020913060608030714070e04050703020409060906060803 78
    0x205556180003213854480684a03000300f4014420b45500a07190703403250030010340b000c880c070100c0da04005240140c449020401d46109812484040c6d8a800400c50000d230f000b0301400c9010700925080069075217590000d41c240800327200d040403007512140400c03201c0c40582400654108010200c035030300e034001d10140100040920038100440e040174001001e07580b015003001234402c5d0042c00580b0300303402d03000d041020350007400b0740541196015005100040d480c001c118014403644101c10409454000202e0540d000d114241c06180d0421004000860300000c4503900103030b04841d803220040c00d0942041880b0500000036004d84200703402000102c00990040044061005071250000200d00041d00c1640079100300035040091400000d030040810040c012140d4818803000c901c55503100e4203185140c0080e2000e4070170f030340303034002c0131390800002c00400d801010300c20142070083c6001e0300c40649925241c0320103401907440e0a40c0004004c00e5600c0350003615030049042000035143e200e40d680e030383c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 22513270 1250 22512020 22512047
    0x5060a02010510080d02030306090c070209010602011a0303131406070605100f0503010903021e0a050303090609060f04050a030f090503010216050105070c020904080c010b10050909011508042d03 85
    0x200fa400c04240301e100460f90702104081a002140b45450310010320041d40703802014203041220500003480182c0d40c2504941c001d004540c004108a1010f40e509900500c919501900ca40d200b0401c044980c0d50040030b1208031800c40c14501c802600e0b9401044070b0340700e19403004215500d01010080d10032880003541c03050344d000383c040507a510303160b0781414202c4615070405005a48014560034031412460340c0003000742110f070b0584030704032415500d4600d150070540e28010240c002c5401c01c030054408001640e403040000340c1c0c541141c101500e88944944060a000e410440503500d0081094054050700004003009002199114203842e400e03074103840414400c0319035500702404030740000c3c0700c0c82c40011401c0e0001c1880803c1c2e01c0b11381d50800b6580c0890081c179080c1d5207a807032480ea250f072080c94036a449141512010b03510341c103000c100300401c90144c00410b811034006001c00002d942c80084a036000341e1160400312030319900c44480680c0c100c21035100d0740c003007440340344082015404001c49420b40e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 22514520 1250 22513270 22513291
    0x409021003060305060109050103050319050408030406030b09060603010b0d020d02040e01080a0302010516122310090507080403051204020102070e0a0e0705031b06030406021c020a1209020f040902030705060a020105 94
    0x2070347c0712100d20003507031002e1001400543c41481040c241c0e00c0010020f1503542c2e50307410054542a13035480e019066822a41c0a00c001c25580c42c2a190301e800c01d451503592014048521500d5581006600301c0d0a0080aa00c030007400e601207401e40311030720075a048070050080031604544a40c0d44506c6a9952950b8030822001542040702140c40d000c1458aa03c0741d000c0981c403182d0f54005810348250040240a020300300300300079400400513203615101a80d018120300103202170000e092911990a50b00080c0c006000c0001080070040400e50005c00c2d030f4000d40e2450141d10007501d8600040346881c2c05a045088040c41040510400e02c80540c0a42039208080e416510465514401c0541f00d21364a64001802c40d00086081c099261102c0150381c050b105540c0141010070807103c00000c0c41a00d581100e24a6000035164130003038000d9262900160003e00500c01600140c0c0400c140700101001a4062034851142400f1581c0901c099009460083c3c1590744844015800901030601903401e509030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 22515770 1250 22514520 22514533
    0x60b01030c0c020a181416020d05030402030604150b130e010c0201060503070510090b0309070e060603270f0102030c03010f080a05120d02091011010501050f0307090b0409021003060305 81
    0x40c0e0b0064089642d52a0014070b84001113140260014202c500c4007203c003170496440107440c1c1c20700c0520109074060b5148009260307418000070000b920340b16030112500e00303021041c800c220050782c00041c202d90080e0300c000303c0c1071003110071107421000d0813282e05507a43c01241e000640c81408500e034010a43c103100d0500a000344c0d42510350a0382200c7c12401202e0705500840c4052103541094560340796101c2462410a5013035030b8855000e041c0b43c0080d90140b00a4000f05400c00030903a00103500342d045942100c0309407950030500b80072481d1014400c000350000700629000100a8820310005013603800c81c1d0006e5641c1e1812121030b0714198000d02a000c8489682c8001188000000441013242c1d03602c800145000d1400e02c20700c00460300800243c008440d02048824020744a40c502203101c4049900c2d880980c07400e600c1800d0039200140c0017070f8010981c2c02da000d685a07030700081050850f0f000540004001042d900428050065680042d41180800c0c80402c40030741c0c50b51008080700c0c050015200d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 22517020 1250 22515770 22515791
    0x30c03060b070b0f1f0602030301030204060e0f0a0e070503100b090702010b060703050723010c02070501020c03120309030403170c060603120301060e01090509010609090605041815020705010603060b0103 89
    0x540e015020001d810480c03e5000601d070f50895041481d00800c182d0b00103070b03003002d18074820a05001141c10480c0140c201000410440c05c01c1d000d28009460448041103952800010a009250707000300554550b0340c444c2c1d00d0000000040c0201c801428016054800419aa01c7d0740304c080d0103008405801681d1500000b0a12881840380340882c5100810312854074a0503103007103031035801082c401e0f00c0111200300c11035540c400001d4114040083c0308d00101d1032040340d410203420144541d01090540d000042c1142d400e50300810050041185214015125194510042d1844c0203640004040c01c1401e24400184044400580301c0c6250306002c03143e1030358441c42070540314145007411171420442440144007841c0504110701c4031110600d4807402459a03000001c84000382a4080300110344240c005106007080c81c0103041c040e18003035800380000740c034896a811000014600c060440e41500340031220000c3c0903011204880e420000078020181c80b070801000a094610620f40802c0c54150000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 22518270 1250 22517020 22517039
    0x803041805130212010204150f0f020a02100c06060503030a05040503120a080f040302010905100501080714090703021c0603150f051302040b04020f070b090d0804050c1c0b0403030c0306 81
    0x24850100354164880401d0030f80e082c4540042c660b800c004941d5020701004c0303032490001800b1105203040d5075815010303075484100542016040002081150815901c040158444076020040c6484901c0c100c080d4000c103003007440080c00150000d03541400005000c0107030b941d0003009441920301c11000d40c0d200103042656030b019449004503920200344e0300720005090f403d0100d400c2d64000d000f40000301d5081c2c4107607140760411418101c00400755943e40010302c80102c04000100c0a8503003210036500178804400018500100185410205a00040c25148412110b4595049080c0401091000907203c0c50445100c41a410400844c01d05d04a0521070450003800b455001c3c0d80304003000030810140e038003804003400c10b860180b50440d03002c001e04088030480748001e101060003140c0018403820030310300c0349003000144400c034000c00c1104070501c0081000840c40307440c903020885200780094840302d4900714007641204042d011801c114100001d140d01900200d4400b44950703030400400c5e480302641e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 22519520 1250 22518270 22518281
    0x312010e15040902040209060d051006021b0906010e0310020309010f09030e150f070b0105040c0c02130e070f0311040f0e0a0b04020a080a08040e0a140411130608030418 74
    0x60000e40035004808420304143d4807101d140c80c0050005898050203201040807644844205842031b640c0700100050105020102000b0300410b00c0038000c000d4480014006285482184074898202d81000c510541e028084c24a11000007500303940160001008420094200b1200c80c041c030350900342e80f40c44010203031007000b6442e5030545441c40300407248000d00c480a041e100b01c5400d600c904200201031152140007900301144500308034402d0350b06020521040d075000b41e24007030512204030742480040c1d4074035155040e00e4007110300c001000000da55002d842c184003507202102921000102000380204c0104c4148820401c0d01c05020318490918503c048072103002041d005034005041c5c0c840041c0c0148256034001e40024941000507480c1c00645084c0301e50807800b12110f110002c0d00304640406204925400850720404002014816941c1401020000c000411012900030690f40faa9901805145500d80c41141000030039281c5000070f90700d5101c0d00036865040a110840c40201c0080d0090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 22520770 1250 22519520 22519531
    0x1020705090106030207060b030601120201170c04030f0305091005030403020607210c1809020403051e0303180102070606031112030705030a080c07061803080a0e0c09090c030a050312010e 82
    0x32075082e80703000000c070000d4101c8202100c000c1d403607150721201c3d9501000014007074900c1c80c640c410718410600c009020b1494140c0c0d0b40720481254010403103c007000700140c030216038108030140c5440001d0700c3c0c2140ca9119414100d64030801c65003901c0c01c0140d2101c00f56100d80e1290f0200c1d03250351110072003560320825103014148414a0289110940d000907003200b54a80546e00b041110440c140f10881d11081c12900301c1c5030200d40c086004c005114003000521244010030000c0324101010502c500d880f031000810400f507042c0c0100f10664491300035411030350300b10303000f07502008850344910b020344001d100c2d030f0f8412784204005811591181e40100441e640e0380e510000030351510a4842003079403900d00003030540080c4102070000f074000c119240a41427640c020140388808044891030301411484016002030740107807a01040907140840007482c0c694080c02181e01060541e2801c00e40e40c544940c446209425003c3c901c2c11208100e0000041c04070304d2440070a410050780c0755030009500e000201c95 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 22522020 1250 22520770 22520779
    0x3040b07030f140f0a0c110a0f02060708070f050d020c0604120f0203060403120507030b060a0c0206040f09091103030304051e0a0605011815050a030201080603010b030604030f080601020705 83
    0x4914024025403004285080c00100401c0c1d5403c1c1d0028103544150480d01c0070b010180e04400c01c03404901c2c501c240d42440140d800c154440809048405503a5805020000c0c040403c10f402c0c1c00c1590b44407400e80381c455609c514190780e03034100d41c9403100c41c002c0040c0c800c440e90b1181c0c01382c010540d800440c84031080d1a000d00607a003418074000440d2910940700d20113961407101c0840d40c5002d40c8081c0030151055000381c4406d010190040c500404a41d0001c00c81002c051070310514100b11758a00302203c030320640c10302d010b03402859a400050700504c1694001000e41045000000340005180c0241c2c508901652851903191000414140c480c88103ea00038411b4000310681070f14001e003c2515201164120110780150744540d645208036a000e8000a40c00b100c0c5c0282000c14801034010013064007001804000501c1c0b82101080c3c1011180c040241488000000104240c50961214110110042c102c490506060a0240040c00e8407142d540000d0583c0e40000c0c4070703500005109044910141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 22523270 1250 22522020 22522043
    0x8010b030706030b01120207020406050607051b0f01080a0b01021002180a0b04030803040213090507062007030b0105060702060903030712140705070620070b0c010f1a04090305040e0f0f0603030304 86
    0x580c0140203520006d400c036031143c0c1c1d401000c0750b161221003b40006d64828030040000e580b01c0d03007003080c41030000c1d1b00751031041c41d0258001c030980c0d9201c001190456a40d08011034040b65000042c0d0620802c81c21160000c1d10124900101e003807900007102c6099000e5030843c00d02ca4850486900c0e52045000c00340ca00b40c3c0801c04a801810701240c00700d508109441c4c00a50124155102803e00420380d02050003e400c0d445600d402c1c2000046185400055400030421240b8680d651502c9107414810248036000c0410140d0a64a41500f00e0b08003000c0107094a03030702d6030a03240c4503da0006e08003c5c1380000390868404208104a141110b413003c0d00700c0000d1440a141c000111800782008076600014001c0c040411200f04080150401400e807111310700340c4a008440c5050300711a11381da25401c3c1c80d802c140c03541003400416074100102c240240c501180341030660905403101c1c071460b4026101040c0c4101040b1000b281c3c0340300280210110403981800e92a040c041640ea4042503401903c082c0904 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 22524520 1250 22523270 22523297
    0xf051c091703120916090902012d0e06070c17070f0608010e130203030c0606030d020304031a07020703050f0a1506060e040506031603030203030f010501020703030f050a03060f08010b030706030b01 86
    0xf824960741300c80d41c0401c40d10311008220030743c404020719511481100391540300803011581c00c01480c0d0081050a000111003e0001b20801d55441600e0f5940c4113200180d0944841900c8100840e44a16084031034500300986e1a0b424804200c2d11641c04401d07030043c0320b00451012035400f0240110341185c0d4a81000f642024038105108101070540c4e40c20a4034501c15000684050000d0002d54026070080d0016241031401d060802d14200300d81c10131904200400d1001034501c5c003c40f4041e114141c0104203a81d2116000ea00c2c110b8070b0303003001c2c1240c4a49601303101e00c514001100e0404500c950f0045c0d042c1c141d503c4108090318090b000307207008155003180d442c0c0103042c41c1d030006900460090448003010f88a0342d0001340300316141c00560050b00b000042201a11118800c13a005040a10048c4420303071841c1c500500c1494024000000c01030300080020315a031003a00281e000d0301c05402d4540c1c01580c0c03218140e0082540d6090a4041c3c01401ca0005440f0f000e446102c61215060312000841a0701c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 22525770 1250 22524520 22524547
    0x203030a051003020a080105070305010b0f04060507060b12060709060807050909040201030f020c01060e0105060316140403061a01120605010219030c08030103111503070e0405040f051c091703 84
    0x2072035020b00c010a050000b002d65150f420340d40c000c2401c1c10000803241840503005054039030507081080c0b0103e040040c034101070484811070b41100d25914019403035007c0341c42c041e000f8059090749076a10440c3c60121034a4a00b0115681d8081c0c0d5081d00c0f0011103035541c92068034030050031640d075000b08005101084540c1000d0240d190b1083c030516000801c428038084001c2240c00401114036581c2d55880c043c0000c0030740510b07060250100702e0b03040d400c1d880c01c042110000007a00c0c00244c00c0000004c0d40ca01403203a0001550080d59000809019010a40095480e84150099428000780c000e000c05c1010b0303c243d1142406480060740942804164103001c0400c89015817021400c10282c0001c0030007040000c0c0146010f540328904e50124080c2c0f42003000100c0928072030440c20b0300d204000744110550010300800c2009801c0c0e6002c20710f50b4503401c12055650181d44041c0a07401001e001c034424403092155103842d264143c4072102600e44940085c00415032500160440c1d510401c41418440304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 22527020 1250 22525770 22525781
    0x17060114120109210e06071b0f08011b03150e0c070b010906170601080a0b040c030501020a0e0316050102030906070c080a110f060a0509190504020703020c0306070e010203030a 77
    0xc000d0400d0303920a501070040da0846440120035144c408200b410740c07105144000194007014141d1400040381420400004c03c1d40c4106400140458003c6810141c14820040721304010010b8074481c0b40703843c0d61901c640f8080c0018508040316041e41c0f9059504050080c8a002c5000b4202c0150b0030080c2e01f03020800011030805440303264070102c288418000070710751096281c040e04e441342c030200340545000d4035183d51000d400f8140719a0f40201c80180601c00300012006e104036005828452141c441d400e00d54103000d003d80008e881940001800504a80c01111300740710002c050b004c51303c2c00c1c503542e1015000e02c04580251b030b005030400c03c495481c514020000d00030311070003036105044090741e030b0b14168940546e00408403004000041c0c1c00c80c2c00d181074181c80818485c15074580d840d02d0318061000f0203901c55481c0c120b1040000c41c000f10400c01d0030300c2076a4050130b0040d00465484041d810043d41e1103445d81c5030b1502c43d21400002610701da2186213420780b0303c0e00680043d402d546402049001408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 22528270 1250 22527020 22527059
    0x1404020d03030b04020a030b0a170318040b04020a05120c0405030c09190c0f030e060c09060703020703020a1811040303020a0201050307021906020a0f080c04050103020c010b06030f010e01170601 85
    0x41d2079036902e030f41590f0b41703100400c10010240c03400501c503900d4200f441101c2005500c806551580c02101819040011003240d540c040e40c40701072001044c4080000e8020405540c8141e000f0703201043c1040001d40140003000a0502c000041010380d036200080e00c11071185008041d016040281c0c00c200c0b034240900d007950010140840c86040ba030035004480e089520341600103001580c000b5500119503058814605000711410180440d403501307940c031142c03920a40603010b0140344006800303414103109001a0f400783d81d000704140c60b056516991410140f04616112102030302e052a200d4100140c58101d608581d4950007404202d1041d0700191207035000140007009500444440510a011003400d1a520b14416000146c45e824401c034000c100e405c00081420921441f50188840c610800045e102260404d181c09a6148900708440307000d805605510f580100010061260302494034405c1ca0580e000d04600019a030f9071580312201c28400040c04c000f2503001000180904078001409a0400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 22529520 1250 22528270 22528277
    0x3040501030915090f0308090309100e03011509021902030705070611071502010218040e0a060c210603060b0612010b2b0f06080f100b01020f0f06010501030c031404020d03 75
    0x8900d0641074070309840e848041102c0005c618491482055000b0000641100d003141c000c1d4141030f0580003249400d218030a020303050100c074915800380c503035003500b118007030106010001e0b030801e5583c0d202d440a5004600d07600c0001c4d10078200905964800000d44da00035030880c004054403403810505a41091107445c04e101c442c0114003000c07c2c065000c0c800c04d405914181d000583c2e50880c0316203c0c41d8098207140c041c0c0701d1410300c130303d20440c800002080e000041c4c0013500020540550301c0c007552414181c0d40d1a91a0305010461842c0000642d40803100b100e0080c4c01c00c0c0400c6262000b0407251713105218580454049100050148950520107000301464540c00074487d646d45006000500006110309441c46441ea40550f40c04442c40c050140240301c02c0005107824600045155141d054000010601c40c0c2d4807070710801107038070802c800c8940760030810944090211988003943c8600090040c0c82c0881d00f80b10b60840514401e100d0320b40d00078407040d2000c1c010f0f00e4540c08c00031081c7c0080000d4041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 22530770 1250 22529520 22529543
    0x20a05090904170f0d051311090601090f06080412020105012301180902030907090606020a0212010b10050309120a050403030e01120609020c010509060c070b100e01030b060f0a0602030405010309 85
    0x441c40010014001c401322180030a4031020382d15140000e944000301158a4500b000541c0d0f0000b9110072041007403e00112505862562220300490310920240d0110303c841c14004400614560400602d42c000c600031480074540141c00503060b4240d400038421952083c41804440c00405000c231544221400145000904003c84400030900101113412801039142d0000a02030b251408200480c01000008000d03c05207103041c40180d220207038000003038002d03c1030290381c0307040203c05c0d0720560303201c0c0700200410001032056a000b45a500112046402072080d54850a054080d56003941d184410aa54103403400e070075035400325040107004141c281031254160000c42c040d10f0a01454024014a030703801600c40030300000c11825150064811800f60304540309100d44c03041000f044500300d0341c10603540507058407884081c101c58030403075120800c0340d004500081300300000c050019005040071030b03005004034045010040b02166500c10040075074010031003000954005d81100281a0207030140e400c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 22532020 1250 22530770 22530803
    0x91602120c010e030d0506030c01020a02060406050903010605090a0b01110105100603020c0309030106060201020a0219021c080c060c031b0306010903060c0c080c0c1c0b0114060706090c06080a020a05090904 90
    0x11355040100f030320003440e440d4801c01c141c0d0309080014620081003480201002140ba40100780c180c441d502411041000004804506403825004034000340000b9004e07110340d107070890201c0b00800c106420140000c000001c810105113050180c3c50185403c40d1483c0966403a043c1c0075070095000b0301c00900d1501040c44100d090755020b224040040030325400169840c0801e0300000e0910306046900040c06080d91109400f6890740364031a48a00e90308070300c00100c002c850824518034040c5020081e03041c420901084402075070b010145008107800c1900b00d05102250703400c0400e5010407544c06002a4a41c5030070008646c1c1034000300c003406418100700982440c0c580f02e84404c0e910501c0110300da6485407220031294101806805400092480781404090450f40c54a00c83c2106210301040c100d000b08000386a82e07260000c440c0c880d07034040e07010032407084207187c040201000d40c0f05140208030500005007403c0c02c02c0c003c07200400071640e2514a4103040c5070400c03c1610014100b611241c040c005440d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 22533270 1250 22532020 22532023
    0x4030b010e150405090f0f0d050d0908070c060e03010c05090303030708060f060c03130902041503020c070506030a05040b0a0e10051905070203031005010306180203151005040302091602120c010e 85
    0x28050f04411021b00458140c0070f0302d5904c1d16840e04500740b07403617001c0d0481a6082e40d0080036212480035041020846a020341000400c0c2c1c051040050488801c01c0380024220340c0002d100d24040400754000e0001c3c21007030100340c41da8020300003001e815401c2040041c10302807103020119031011009259980380302c80c407008a1300580000c07018403417517440000c500d0791f1843c8118101c070090a401805525190400ca03800040c0c50004480009142d000315440606107400d00200000c1c0901406d2a9113918119050401814081c3d805a40c40003c000c0801d40300c407001e00441600f8412640140f100140c0d1054010040600902c2c050820790708441c0c40c4090340d40b42c001c10b40170345460f5000715128207200f585c030b04480129030300442c189480d188007000405071841010201d40c41555006849030f940c010000201003296a04640c041950420303e036015410001410550b8000c0c1d510900d00c1d520301800c0301020030b1413038402c800340c0d0114000f2501c2c040d0280040c03402505010010800b240c20f041c049 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 22534520 1250 22533270 22533281
    0x3041101032d020c0105060307030c0303050f0904050a0606030e07061e02070806070504060f020a0f0803070302070f080309070b07021c0512040f0509070201090b0708060109050d121404030b010e1504 87
    0x11540c2c01d800080290825000740509508076408030090070150389166600030034040c0310302c00141846004600300b80c042002d98140d8911040140051016241021000000b40140e004100100385801414010000c0c00034210050394800c1e00e61400c1c04010311100e404d030441030840d980c02c502c90100d0215980b101404400d0060600340c4a254550f1300340003001e001d400240400004540c04a05440003142282014100d09a00000c40959945641c50101c02a116003400130b0905a80c43c000d010070016288000d40c13043d000101030707684550b111585130865101e42c400280d0f0041d18580288250925241d1241c16644a041120410310807510190450f401c5640500d078503101000c410841810300e050004d03881103607403000300508440e42e650300b1072001005e0140710411901c03c00150031640216040000751000801c051102ea10b00c0c42c14403030350318005c4141c0000841400361100111406400d40d1709595104070b045d6440e0b800c110500c1d49541c0010810b207400701c05c0800b802425250791240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 22535770 1250 22534520 22534601
    0x403060b03060723070609050d080f09030f040302090703060f0b0304030201110c0a030e0f120105010503010c09060801030609022103030708060a120b04050307080c030a02070503030304110103 84
    0x4964020300104041c203000c00140b4003024007481c9015105980c41c001018101c901400841d1900d417191420464014041030b14010103e21409280325025a00840c2c010301c10741d40c284100f521a901c111220340c5901030314040103100481400203000500d015040f0300e9100ba11454000345917a40c601d04141802c0c240da020301d02c9050000248420b0660a00844403a024000300301480d04030006c1d4002d64503101c07041d0240800074040c00c3c0409a60741c000307100e5070380b1600800783c1d010030003140320042c02890300b0720501c0d2103580b80c444640b250f03501801a0b00d003101c030741c1c2e140d20b05160f1940c1c803440007420b0607120403a403005050b803c007205981e06103d080002d01407540115140d140000c0080e201542c090720b22441000031300003c00c603484000000101c0280d000a1424190300c3d075142c5940b0350b000c6c2080080076003c010812420041c030000250040b040141c1c2100c01c401d946209150301ea11098030064a00c0343c1c01c20b0b4841165000e81c01c00340c01601d0300d03c0402c012404c520380080081d0b52000d107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 22537020 1250 22535770 22535783
    0x1020307050711010311030112020103090b070201270804060f020102090d1a0f09030a0e010203090402030108060f1006051602210d11010216021002030d1802041d100b03070504020403 80
    0x1c602d0140f03e0410380070008040301313090411403900b00d2011044d00d804140704414085851018400469100f030300440f080541c01210956141040f20010b030103010b11583c0c0440702009501d110031008031109070380741801c0c0c0000311030b840d01e81820412160104200302d0f2005644d02040040b4841c0c84018000d0b541e54000d1202a40c015911004640c0b03883c000381c407054203003d040050046203440441104c0721001141410080d403c1c2c0000140d04500903115130b075034028404400000c036220082481445074180c1d0558440f0380e036840719610b00c50360380c40c002d86000403800d0103006250580040e8114103940010004c0f04036454812050980c502400d0001c1e45940046005200481c0c004c07040e8102e441584000f03500301035001c0d0845082c9010110702034491f000b034404a004450080c01219034040c0c0c800010b2004404101c0c00e107120000c203000490203241b4040d003989040035110711060b0030000c2e039800b90030001000c2d09440003a00307203140352603410300500758009401d6a0300c1c8000c1004511070398 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 22538270 1250 22537020 22537027
    0x31c02030403232a040f020c0c0d0b04030c0804030f060b040c020106050108040204020d090503030c0403030f1115040c090c08040507050609010c0f060212040308090607020d020a02130e0102030705 86
    0x10f007050580305050078108035802c0c15400030440040209491082a074103150982c102c05084091107940c030100b400440d007003458254074807107403103540d0028440014a081114020000340090041c0814003101c0a00005501000308001a02c20502c04107400d01a01d07009081984a40740d102411502c54403c1702c1301a558406000f990609004201c40000c190008000700d605d000000b9140c044020b0000303101d5031b40020030111520807a4850a0b40c580c1201c11aa103c0c90582d05241c1217900c01d0005501103001417071412134941c42207a0030300c20b090b90000a01443c403c83c188089240780080e208650140c03a1030004241446640b08403681040e80f565141802e0400781046410800c0582006010b4881041149003e0340c05c4410400b1955100d800070106443d1818910b000b40114450007041c242c5030703001d110034035600c2080315018045030019a8030a03111a03a081e659904050341080240c0c0248403000d01515000c406040d983c0e070441c40104001e034003141c0003801c81c1e000f207078110007240020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 22539520 1250 22538270 22538273
    0x31c0903020d0203030c0a05031f120510020906070303090201020a0212010c090b28050708070818030105010302150a02070504090308070801060203120a0b0607050d050309010e010203190506031c02030403 89
    0x108010002d03000a80051861030400401c02a010310075031010074140140000464000b08010000c01344504040310b003402c08980700c503841480151094402d503010721803900881d848030414800c48030405801401e071803902c2656a01036020340700302a01139040d070080224074070141c0c030b4101c19904140362000c0000b40c0781c0b0282001802d011140d402c10b18000d041400704a200c031720f1a51860381700b20b001c45080b4911840b080f008881d1841030210003080140b000ca07600c800c00c03c1c0e403000360041509164102a0b41071084081c142210030901c0080e5102c4486000c545207c15611300a000000c82441910042c03916000440d00380e8900c05000c07000290601d007040841580012154090400d9201131403800343e1040f80c1c07080d0307100050014802d071585c410f00740c040f50b41c81a00700c610b05603110080e140000f560700e1003d451600210b030155015400c1000310348000c881031003164840d00034030350141440c5200700c110000030400140a00e8051183d1110f035041e40c0703034031a035405000035a82d000395500c5055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 22540770 1250 22539520 22539523
    0x220f0f0606060f1103031f0f06020105070806010e0901030809040f05010b0702040b0a292208100c0206190209030a050102030402040606030501451b020705090f09031c090302 76
    0xf4020b181040103460149500f4250000c01180d40214103810310310700401d580040019001425070043e001c1c80c50106d4006034540d01900400d00c07440c2c098071035407072690790741c1c00644080034185900c6601181781001403000401840207002108005840000d080000f000c03507030b0072510283c00030760244401050007021031400703004a14007001b066034200e8038946850543d440302440810913080c44e0180024a00c0603c00c5101540c0001c002c07054540b403940954620041c5c0c1d140c40303008241c0a402072071582c0016009500642c900c0640700d40c01040c11343e0380c94000c408580742c00008854000c0d020400c0c40d0181c0e03420030401c12294060400166a4207042c0b04100468800da030040d0285402d0100404c0001c640740d804194400034130041300c07041d0380850541c3d01c2c003480d4440550111090f60200302e4107802954400c10544501c81e00170840308a50b030a0590755900c1510407560302c0315400c800114992001d0a11941003141d840270cc0341010700f6040345c0c1c2903144d10000f084070801c0c0d44230784080c18183d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 22542020 1250 22540770 22540787
    0xc031b030714060d0515041b020d0206010602030d0905070302030703080301061b030906120f0501080a0204051b0915070c0902030603060a0e030a11070803030c0705060f220f0f060606 80
    0x1039000804207480c000c2d1001ca807960240402e1040640e994600003010952940c480303120202005008000c4420188154030502d84c2c40d00040b0300510a022241500f0b500000c1c0c3d0074140e421503002507007003916240c2c800d0050b050f0054110761901440e0000801600d0400020b4040cbd440b80d03000720384960410f1130082400601c0402c1c6944c100324420a2404680c0200802041e80d0b50742c82c0066901c1940380c600c00140000d2404001070f1842e200000500c540d021401d001a81d00c00c0b02e0501442e1a21218410308207004084081e041e40d0811030040c240c07406680c06072010142e485200c2c1843d0f2641c82e910200750316503002e01d0102d40c0000c100480703481c060003040e6011420b400100442c0c02502300c01035403406003003400428800b00a8101c881d02d0030821180d40106000000c4070b40c0c0e4549083c4084003500140d404071211702c10840469142803a03461080c0c882c08601039002e204490300845034005c01500d034810f1721150724900060b40030410000200d0f5006000751b401103092860080003d24400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 22543270 1250 22542020 22542029
    0x4060f02030414131410080c04090c0e091c020a210801030803060301020906190314040b0703020f041e060206090c01050706090507081603110a03020d12020c031b0307 73
    0x100304002c180000380c0080d00349009001c00340c030000c02c1e500c541080c0100038039003420104014080401040784100004100c41e050382e6001c01030755010b403d682d050100f030701c0004000034601c0180400901c00030032940055135108080804403211a8446c1400324400e0307401e070749140c006801c00a2600c0620041d001480c0421510054021301d50030351000081c201c540602008140d2000000824455582501640d005000003000c9603a2005603598035210201ca601c00c2a001c41d04104c510402d04800d000039500c155085800c00c4901e9844540860096010006080c40582c0600000c100041c0307100028800056004142400a04048002e0320f4440004c2014860707030b1001002600c00d0341c0c08400d07224907030352103000414212410700d4214108055900310208610a00c07040c0c1c00044003c0d1110b1085902445402000340c07085001d0102d6030059000c042d401030164007514002503103096504425a800740306490f2245004000a402d10001c1c8402048080f5502001c0d42c091030140800b40c000c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 22544520 1250 22543270 22543273
    0xb060604080309011409030706121d0307080307020a0606060203310b0702040207020612010315060303140c0106030b0106020a06051501020d050a0306030209040b010303081305060612150a0204060f02 87
    0x14a0620704568a1051407005410008000c1c0700310340644000c01505c43d080e00080945400702d0300e40600400280a80e0f54006c03010742803410005106841010415000303800c0c8018520b822020f072101d00c0d6035800a04040c086125402e42d51011400d284980000b405080c0e01640c0d4860a90310300ca1900b0103038000d612240044e825602d0409084151190120b400c0b0b10012919500ca90000038000d0043c504c004c0d401060010701000340c201d5200ca058181c9105400d1a41c6005402d20060125030240c00b0040100708030600c0700e00c2e032110910140411440000001c038020307807256a003200e410000e0344042c005d03a008525890401c06503026883d4015011081c4c054410300840c0000d41d600d091140340018040d0000b90120310600caa04400c2c0650b402503d02845410310749050303211114244803d4002401c1720001c115482007030814284a550018000c020940368241003001c0c00e240380c0a4600c42d8810f01042c0c2110100c4804014881c1c00c40140060300d440c9000006800e403c004070a54086 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 22545770 1250 22544520 22544527
    0x60305040501050f06010e0f22060314010218040915090303020a0e010c080301060c050f0105070509010e030a0f0809030703140d020f03040602100b01120f0501050a230402030901110c01090b0606 85
    0x543d034402100c4040e0707102108c21410000032080494445040603d007101c1100619208102030b85813a0040003c40b44106220180030100d142d07242d0803802100411648024869440d0a00d85401c4d00102a054020309030450001c1021a0355802c03107400c0f403030880201f0340108660175181d400c14042c5440c3c02080c20260031104c010354a0602910050055801b807103640500340c0c062001c1001105181c0c0c024000800c51824000c0020f4010340100341c1c1d603400a0b803c461000458200400d442959545c003211030316a01d407643d510b090300c6410688107103401d84030380034002000c51401e20300c00128000400241088840d114802400c1601100102c210340e40104010070125600140340500c42843e031000042c5a0213140c0100d030307440d032500c050620031400c00640c5409a40c003540018103c6008036400c00007156101c0e81924490440c851085042034602c1640004c0c0c140341d0000c6034402d140000000b5111928040d041c10364024a44040130350703550b00320b071000300714000d0607107604900200c484908 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 22547020 1250 22545770 22545781
    0xe06040513020a0201200c07090b01050910030b100512090105010e13020a03020a030303020a080105040501050112091106040f0602060604090206070f0c080303150a170c0607080c0106060305040501050f 88
    0x2a00401007111640e40d0760000c0c0c0f40b090a4400e600201941c80b894844a8032800d018880d14800d41080301031002c00d0145007000140e12200d8824540803000c1078445905241c9460100400c82c0308520000c02032585030040c8251681e1040c000b140750b080151101600c40124040c0200503c40041030b50120f81e01d031000500002c1d80c81181142d0000d00c403080d604c5014210310115010400c40c0e40008e402404a010100c20180c06402424038150296035521460303a03250f0811042c1c80081c456203002c80e00001200d01800107a13040020010b005400035a054060040410b0180d4441d50104682003c03140c018005544d0520615402190407036061002450360b40018440b407241c000000d0010624107419400c000000515100804c003140c142e0b501c91800b5444000804135014105110307028014020408403107108811285441400040095516400274050903522481c0e09950361350045c400050180f1090040e6009800b4590f00410f040c2010303d0000c0c213445014150038504440301d000c100307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 22548270 1250 22547020 22547029
    0x4150210090b040b0a060b03010e0402090f15010507030306080706030605100c2001020109350c1b0a03060204060c0303060e0613020313050307110f120606040203041103010510060e060405 82
    0x83c0c01c1500450600e90b5919082803103801004142d001e03042100010000040e45124490010700c250b000350764014242ea940101d061206404581d08108007890540307026007540b082c009400c1061182c200055100d0302c0d0244246040341c0c60b800080029201d0b08144164100140f1001400a560034844050714180d60b4144c0c1c10000700000d00c07080c90364114034610a80c400d4000030301c002c0e00318080c0050458140600801e56241c0c26a80c400c4c040c43c00201d00c441d207000c100703c1d07403888076000143c403166010322191a19101e04a0145a100c8000f090110100b00c0c0303880240002d0400c1e40718101c040d0b019103000307007c0d02e8003607002c0341041400d5801c0004c81c5d05c44001440c1142907560b00142c0d256681070100c091240442d0000c5d0082c400890030741b08101d000100055018011540c1c4616004a5010480030b01300c0d010801c134090300030358007240542c1003540140d80c006118070807001c0808840d5000c0f0b402c40c0c000711290313840d071008298200100354116a00101c0742c402a82c0b610703d000e00f01310119 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 22549520 1250 22548270 22548293
    0x2120a021c05040e070e0910060c0209070309021008040314030403050909090115030c0305010f0e031207020c0409060219030b01020312130812010911040509041e05030415021009 78
    0x8400748101c003a0200c0d4180c0c490300c101d8000d0300c4c0311459640030b800d10001c0103203d42942800d140c000c0c0c0808003c510342500000102048030a01ea880045016244e801c0c44003020024040d80c00385900c0e08050703001070751102c9004c800c40c4030700d0756078100c285441e0400418603d10502c400454400410502012940c0201226450402600ca10380207071610780d0301a004110040034a2508a40c245004c82000501e817070b42012203008200a00600c49000301090440d80d0503118080960b00402c10703901c0c09490704503a00d501000782d005407101103070310202240588610000c100c3d04c8560004030448140c46004100c2011140d0749804c00c8a088a24000b030759034480c1c0010300905040d031500040c040394414416000742e0703500c20440340e01c1d423140c0c26210052000c203020301c0114034144400540d02c082c4140555040b200010300c88415030311140c458074602c120741020741031034030300b0002c00402080b003c00041c0000d0840c02c600c00c05501c0b10540085c206a51240908070240c10310720700d90f02003000d043c43e2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 22550770 1250 22549520 22549543
    0x1050d0602070302120d02040905010801020a0915050702060a0507060e060105210a060c030501030c170c010e01030b1f090b030c121806040309050a0b0703140a020c0414010602120a02 80
    0x10b0352400c203030805a2600314030605801c3e00110005240030318140e1078001c0d2085482d000c0d4107211503622007035814240e004000c0010002155a0303410170403403906c8010354071f0300980c034201300785041e01503004a4441e60113414800041080020083c041142a100c0e2144001c0c0e1403002e0107440d41840009416104040d14903601c0060003896400d808070113100b01d109c4e080d40180c080103500d4100c1c2c0090b018000900c42034031040c18503d000105050402013003040341040c44040c0c035601e10250015070382c003041c191b200e43c101581c1d8030300000c03640c4810410387c00040d404002d62280c1c00d0701c024000e1a41c0f100790812141c100060040c0601c00842d58190783c801d00d20300091914940e5410108603680200148840c40c07031195505100c1850380017070080080e02c1e0700303440c0350b5035654441c40581064403e040340100003505403001e0b03c1c1640c0ca00009801c04411070701c1600c0f08009036a001a0a480030060048084d20300880101320181d010405a101d103002d1010313060508501d02c5001c0d4031481082d82 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 22552020 1250 22550770 22550783
    0x30a0e0126010905010f05010c050c01080a11070b010302040b010507020306060d110d150c050405010c0209040c080d03050603010f0c020703150609020d0207020a170309012a0f03020706030501050d 86
    0x42420840c00700d100344507034070031014107003403590307075078120840030348028410f200d00e48013005000701f255480344251203540740e003000041103004081001117450410042c400c400f000c1d6640322620104d120500149242030007201820101e5055004220489848000d12030500070100700e48001a18045405d0754000c204076070312803407000784c2d0500907011400b02c0410340d070004204030b92204000d030b00c0c10959112407421200700040602080150350364841c5014950106400c01012401450402001540584254001c881550b9180c9840b441c0c00c10440c1c3e144080398035001007100505092291112040d9a90014040d8801c400d0029403545c00c60300000d0a0b49016009850a007030705500a9001404022804c541d0341d0000503495009400c02607003284202d0b603403007000814403c8840f007510603482140140d03240811860041d01c2d812040340f410324a00d500c08420320319042c86c200003c101d180c040d411960317480043d40b50080c00c2c4603880c0c00140505103800010b000e2901d4104070986180e90040c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 22553270 1250 22552020 22552037
    0xa05220b0d05010212070e0109030807231002040602010506090103021c030507020306130209090d08010b0a030605030d0801290a05030603030c0625030509060a02130b03040320030a0e01 81
    0x1004106001c908803000391031580005030150004000d103020500c070b040f03280d03903401204013500011502c1204a01c4044e00c2e4200500c01140491246900c4c0c108030484180c01c0150560302034441400d00d1391209121000c1d90b0b020404120b601d1702802003a83c00300c0c0403640c500e0340350305560020300310140c102c0c0d0041e90030881442c0301d030400d80148100e440241d00207045900a02e00006124480d511090080b07000320300030030200d403401c0d0000482d500c0c5046540c852000e40d070b08060f103c07503594100708106030425441d4640000c00342c90900041c040c051035030343e4200780e80d03042160900c154610480061108042d0912014524024005407810f50700300d49800c039079940702c01c0c0000b0310b14021804403503941d000d000c4c1840000041c110b1001c07043e1900c04412000b09501500c01d4085078021113801d000b682200001941000c001d50042841c02c0c003210150b00003e4403005039804c1901b04550450100301c13034161000c10b881d00700f40d19081414002c8029464192001001020b60b400100468140300301c02c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 22554520 1250 22553270 22553291
    0x70e090709060b040f0506090108070305060607060608030301060809120307030f110309010603060e0a0b041203060317041e08030d0902040e010e011d0c011407110901080a020a0522 79
    0x901042004018039001400b406446500c4400c4551080c41440c0103500c4018000032a418228123581ea44003050b1a056041c0d940c002042c0c0c00323031000410072940048200001c00002d440f610480c2d024120b4040203644a43c184440609005000350002031540e211071b0308403880542040840382d100d030f420702e40454159102031500d0080c1034080e9060f01008408000c0003e510b0301580414100e900401d414410a030b11141015243e031b07001c1201410a6088400060116408080c424016403062400140c00307580d80d11804210458100c0042d083c0381c000404000080c08009150082c0900d111560034441c84c14115a540c0e2060145007551591646104400d43d40c031075001032240d400c4100240041c01200703489600a0460134020074040c0c1d0310310324a0000e903100003140c082c52003040c0c4601d00e01c90518100324040d50048102107501d400c5403d86d0f29913946138008018000c207420002007e01074078510401840b02d101c1d41000e4002d51045212010420605161100e0800310358000161100300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 22555770 1250 22554520 22554523
    0x10f050f01180222060309120e060414030a060501150f090e01051c020a12060f0501060801030b090a020d0c080d030b0105030c1608030f040b0a060308070206090d050a0305040f050a030203070e09 85
    0xd2084030318035070482d202c0083c1c0160075800136509079103c2c040c40039000341c80e400c0c06e648010012032701c1a00003100703000070300c251210320124004040e001000c46112800b16540c4500b610000d810605180f084125140b030b409412164000c4800038074100f24074280d0a203142c06114960500c07980d880b0b888003003a101140044054000d4105401811405e59180c032131649030408907200c3c03030071601145003480b00b0b0138800c854440d445c181c070310b681d8400300700f42d1031903c0b01d40f90780101504615480c085e41d254000141c0c0c54041d042c6c3c0c4d0b0b81c424541000054600140c150419020030205000d0500301040841203a91010440780d01c8076015200907210081108081d40900107442d00422600e4000f0034400f540803101c0d00548268411004503480380d403040c5a85050304d03030600c8002c00100d03080c000c20b001032030044094486210040c01780704100f14551900c600e400d40c462000c1e800704000040030300040c240c084d99880030f01010382e07041050300d2443c0d003c04c0d0b40b00003500c285000d00072010007050383c400c030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 22557020 1250 22555770 22555807
    0x5190513020901260c0303030103020d020111070e0402090c030709051014122205070501030b040e03030f04060b030d0509091513020a0f030603081b030c0a0302010f050f011802 77
    0x4010b450041150303100e5258400118016509111a602101002001140010326a280140054055800c50f407031507082c440399444c0000d0403810312024100121810b1020080c01c0700900300c1c207040500c141801c2c0140300e42d03168090000c0d50104801c0040115658020b060b0004440341510082059440c0174000c85810aa2a00d49440703050002001020310059001c1c5a00418001c1d82841360016002d16600b070b00003103d03e0042c100d80090b202040b0542c001d502030010040c01a20105070504a098890b080d070b07108440d20465002c80300240710a10200e8400c0d44107000b4194020b04040268900c0035200b030142e801007a10544203017001804045140051092810015111358000740124003080c2c0a9041081d4080018004402e50a1014840d015803c100da802060007480d1800301160327014a028400c040700300d2840200104842c9007420803500c65000d0086c3c4c00015110b43c2c50078413a00343c4034040c1c1041c0503544181c0040c030404140c0300d1540c00000214400507a42c410001e01d4001d0001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 22558270 1250 22557020 22557023
    0x30803150f060a0e1201020a0801060f020111031e0901052404060f0308030115080c0702010c0f02060301120507050a08030a0c030207030512030a0506030106030804060c0f02040504050c0306010905190513 89
    0x240045803c601103074010406500e2030004a40400e94041c0851586080b405010001c0001528030001080558000e261001101d8150300c004103181e00d0783c42010b06950700a8402c0c40d031407030b0142600040c047d030b84040d19811114000003808030341001a6a400450501c960801c5101c18031903440303c05581d141c0c048802044184490800950f072410881c601d40c000f4443d000315034103c06141c05030640718000d102e214440c00f10440d1706040bc10780045807034400000d4116407502103409460007603520200514001c0202d2000007103543e030303180b410394104001030b4072850080003c0d000034800e242d000310503a941e02a8030b02c1c10b82c48810140c28200c1c600b800c02e5001906a01130154418007010f940401140310720035000f0140701c503071030f28003c0c0341c2200c48620010300305030010f1105001d0f051140c510000d01c10700503c0302c02031000007500064100c85098a0444e01640119543d140604040c00340034014416120201f01500e42400031090304184005085c112981e90000291521303100c3d0090b0000e02d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 22559520 1250 22558270 22558279
    0x50c0601030303050108120301030b01030809060d1506120b060403030e1f0e0a05270901021b0f01060e010605030103081c09050106050301060b0403030c081e0f090a06030501030803150f 81
    0xd581d00e08020740202070a02926065010304119000c1900160044a0480382e009002c844c0d182e10307648520704580c200500080c2d0242d8108420f04030503c0c42d0160800798a841c90000c80d4482c030b84040079225469801030312500505003c09042c15503200f07019070b01101d403d81880646007041c04001682081c1400d10f0b00e0204000103607441d40301f580460748500c0c4070819100c0714650ba460700d0401400d03000400c003900c040c185002ca40d201d07000300103000540119403507002600307000c000258a0120071001e01c0c00001903006070080071800c0c402340510401000e15030400c803615410050000c2c101e00c414003014041d1a40043c032440f0f00d41d0f6a00c0e4054000407a0042041419200d00d00340d8064652440392910035802c10001290250b044800c07581101e81c181c942c0142030f595a0740c1e04816070015511050800c512000010001030103070001d018440690030300c640d540d02800c0c10080725684640100c403c041c1780c1001400050b02440031290801d00c2c40745c00f902411070000c00a5550281440d149400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 22560770 1250 22559520 22559533
    0x21b090c070507080c01080c2805130608040b0f060a03030c0206040504020424080c070201080a0b0909070305060708010f060806030c2101060509040804150e0301060f090c140a030c050c 81
    0x82e010100c1d403041c0114003642d401032a0f031240030f01100b04d40215003036405035a41d641080302702d495020590b540e003d9020b0400508001c82561240076403040c60344448046020502000100301420344180e80c050042c40241169060582c00f03d10b00210314000102070000030000781c015580c40030252070091000501c00e654990705c9620100c001c6081d400c000305241c542c000170340140740c09008081e20809070b11240380c0c1000343c0c0740c00449089001808540c040c90340c420450603a034490284085c03150881070b004050740707440c44ca0128a86007008120303008001c88034005110340034007508503008944045c6000b840315110900000e0030541c80c001e8040d4442014001c500039008600328282d0301c042c0100080000c0c27581c070703418800c0070030040701c005148070800c0105103d007542c000c0071107203640c2c0700c0e11b0034140314900320b004a801c61b810b9401100c240045500f042226281a009840f10345c0400e140c07106c071111194210b0131213030080440c24001c1c1500d03908440b030164810302c180d035410040b10088405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 22562020 1250 22560770 22560779
    0x70806011205010b04050402032503050712020102100903140c010f0504120207080a020f090c070609051501060c170a020c1302070b060604150806060c0109060e0c01021b090c070507 79
    0x8070504220884081d4200303d00c69901e07141c00e02c00c06100b1034025002c0c000707401c0c81010340884082d960368420100c0010b0350000c40480d008000e003501401c114014240314095074000a480c08060440b20002d0307504050911000a902c145614004017100041d036403540b140c0392031903025222548007414400d2415081000380403001c000640c420a5580a440c20142c031494055150000d103080a50003410790041e66a50b030808100d0a688580086c0e986410582c513039440740c0139207001030800c0d201035110704407035099051001a9640180094200314129404a58a80107040f144114803042e68001061703881042e4000d101a03040b42c0001004420f80d2682c1002c58802508128000d8600c2c0c244a00003d1060030844102e03400e440255145410205010030100c60443c030040c400303600290700b03201d080c04564007401854503ca104038008120700c080c0c0b1182510300400950700b10704551101420107061a14464418a051029961601683c0e5184e40032140c03803048060080c01485800d20001c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 22563270 1250 22562020 22562039
    0xd0b0406030f030c02040f140c0a0c05060f090d0e0d02040b0a0b0f0301030b060f010915050f07060b0f0405070c0605130b070504090c0309020a0e06120f010c0809070f0b070507080601 80
    0xa2110300c00c8608009882c24415a0f108841c184e11074008000790359000700d80003080780405800805070790320b44034be140d5046039281ca0810600340c1e050030b143d407022070034821b01180c00c2c404003002c41c40501d000078040081c480080da01c60101d0101a000356030301d210f041aaa00c0704040c0601400100c0c1c00c003640c42845484000441e80244000e1b03c280d841c03140401c000d45002e000041c072002c0c0507036511b104c0c281418a8400c40010000032a01807190401004280c1ca4510001e0980341d4041c40d00003400340000c506020720030071000d00e070500c200d10f03003c2045582ca80018240455a4100100040a40d1440308108002036071030400381c9000081c00030800c003690702c80002c00c182d4003000e0050201000130a0183e05440c4c001034000d51011a400c0e00b07202c07e03c0d07441642540007200a0200380e0260a0251090800400340c145882c03d94644e0200103566130003681c0141c01c403900b200208944c500d41071801d0bc0b4180303640204485900001252414080200100c8000e00042c1003a62030950b90350b00d424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 22564520 1250 22563270 22563287
    0x13050f0d02030c070f0510140c01050a06080c180a11070b09060105010f110d050306010201020d0f021806160308070512010906060e0904030210020a020109060504050105100f0b0d0b0406030f03 84
    0x202c41c922130b003100400c038498229026000c440e0003074103250f00e00c401d00000360740020010000d15801003041c0f0080c82507281c24010640500b64607000016045c1c00d1216050801c5415a005400303102c5140d4005150081a04420360214040c2e00000c0d901c3c000c542c1803191846403d0300500707000c5500f014020b014101145843c1241e6003600c1d41c5105444186003038900c00189007030300b8200d8001d0046d82c0041401a0021540910305100042c50b06070090003480466000d00c02c02d401440d40407031055111000100350000c00f0b0b0301166241d00f0700780106c444500384807c03d030009040ac101d0102081c2200d000b8810b03503001c41d00c0341e01007814641e101c40b041c030010030161140304001303291130080000c02c1c2004017266000c1e0360141c0c003500d08001d00c01860390181d88481c0d400d4007150b681c1c000e9240032802c9403007843d000e640708000114580c2040c9090b40b00307000107900811008031030180c040000000b8242199804075410380042140c040510008008010551010f0f02441e00000103404055101070761 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 22565770 1250 22564520 22564537
    0x402031512060c030411010c020303030f09010c050403050c060a0309140309130b0609010309030e030706021b0402210a0f180b0703020405010f2102040602061506030402010813050f0d0203 82
    0x8441c0c0719184411140d60300c0c0425504112000300c10004a00803800001016059003418108580050001c1d40820b10310340c022200584541100001c0c00342d40360742800390324195440c51400f01d0400d410744d2582503c8108a405613445000c00090183e503080c040d40011003900d400415911480c65140c083c1a00c81c0c0c080e280d180d01c207040301381c03d04c14a0403040c032a0f880030210180003d030900103280015002001700c02c0c000d9062019281c10902c02e41e60070800d1a019103915406030a07e29000960400030142c40d40d10303140314500501221645a140480340440400342644280301520384504410081072100800590182822080415899038450b503840807445030f1543d0449640314a4210200d005074094580019840101c0c6043d9030f01c01c56a034008054001d05c036510381c054403550030089900a40c03141026801c840204040c41409aa205040c15015a083d03495071800340e0000b4030401008090b001c095454800c21014003200f0803101c680783c03019004841c0d000f055050003942d640c005610 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 22567020 1250 22565770 22565779
    0xa0303060506040b180d1205040306060f030521130603020307020c0405100603110904020d05040507061106070302031e0702011d07080d0509060c07030305091314010303051804020315 80
    0x300103540d04044085034201d41d04045200e081c010440500355010b04560465035112401621510226044011a160f0140700c0e0312441e0343c441c03461a1a0082c0c6003140d00083c82d41c2d02049040021400105039600712414640c10108001d000d1030b0030903100c0c010804511204441500013040507600355000714041c0a071502113407400d0354007808000948104803030f801c4c5082028801001403a0007900104171416036101d90ba03003483d40c4040418101e030007000303400c04516281d906010a210b41844a0300140070389281103007800403c90300003070751036030040c2c584403c16a0000028030603241d0914800a400c0e00d00414068a04100c48002c0c0640991802c080f000380400328040101800007500300c0c02c645440d80945150011000180c80325048552041c0d00314408100c4407510740f4060003070401070351182e2a525103401141c0280300d540c1e440100305000c0a8680007003c0c000200c0c3c00403c80c1102e0341882d0855960390000a503440c64280a60360b181c02a00102c10b100701e4221241000d07481100c140e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 22568270 1250 22567020 22567031
    0xc0c140d03140403020c010809010603080d02040e06010503040b160e09100e011707090c03020f0304140c0103020a020a0f02060d0c1d0609010f031104050a03030201020a02070807081e010f0504050a0303 88
    0x102503403202c06068600401607406252503240c154000d116440d4404095000003840b540e4903110401e541e444600420b03980f5030700140501c484a11031180e25082402071a01c18103520b0203030b031814184480a00500c0801d41100c103080a001d109244026140130085c191000600303010300d140c0031103a100e0040441003011207001107204040c2e100603c8142505c1c0008101d45440c003404a401042c800c081c15040640030040081114414801140036078807815080042c001c092080d241000d869801040c101401003220102171070340068128286900604118190141c82c400074040344503006400b440203041c11100005180c21408141a40000c26a42026004601d04000861207003008182c081000b2050188031684281e2040b0005c0031000c0c0503d20342500e840025840c05855882240142e40010b010319440d0785c140040e8000b001e402c0e000f89076107070600402d20f488001d10b80d80c243d10846542d01c0c8030001c52003500b042c0034000c0c8402c01040b250900f401d006894940c118002e802180c18107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 22569520 1250 22568270 22568291
    0x40809040e060628140607060e0d0201050c0403020a0b03132001090812040b030c120a02040302040f0605030705100201021306080103030f050306030a0f060209031501090605010e0303070201030c0c140d03 89
    0x1018107401340c071824240615402c2c14405c2d100300d62440202020340016041c020180000c0061065501011890300142070030020301c0e0009080d568010024910070505020810060701c511aa0348207542001c10350365100d51b01d1394120039001a441d200540303180b041010084070b80d08550500c01201c1c2c0c0032390b030b240d003202d44a603c40c1d43d6032000e9003140620030804000800c40d80c081038010750b4201000401c0c031440c100740110081c0c003840d4180c9001c046540d0000c0d0800452800d4412510303402503090050000c54507010000344c07205e82610132240107001d0b940004800a20039811902c00c2c0007101418410140c40e500010300c00303202400100e000c00c0312074091020460044040d1380c4034540003402005451420fa139a0842c001d141d450032500d540d000d000e40c05080e50280401c020603070402d02450055032410091006070340c100e52015051040c08100501d03161000300407205d08a8081c2408507007951440f504641d5100c0a08001d031803c1e0450314808071b00f003000b10341035410318110b64041c0b0801d01c41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 22570770 1250 22569520 22569559
    0xd140603010605031518160603050105010305010518010e1305010908041d040c0b0703050715090201030b04020a02070b091503010303020609060601110a0624080a0209070201090201090e040809040e0606 88
    0x48985d40c3e24091407040000381022440c2d44500e0b0481440d9055400800800c551036140501c9a00300d1030202c0e4568005002c2540e051240b82d00425044610310300d1903102c01e05840050340180a8540d207640b40c81c0016511411054007100c000c8d502c0070081242c55100e0a110f402a0000d014034103002800c1c02008c0031113200000300c00c1c000c5410401d0012003e2a240ba94001940008811002d00009028500105240028071a07000c04105404500008544001412513554898542c403c03807042c8600c2005946c0001c010083e140c200d1800d0f41d03200b1403100024415452841160500140040040200343c0e0104806006100c46000c5840544644005464001c94001c1160b22984045206800702c0c5003500000304086560256401260342282c1012800c0348036000440e86520801d0307442c0850810200c5103500c04011301c001c015500443e80000c080d031025101e8415822024800306042c000c001e000c45032001d5008000308484c0c00c884c03c0300307521442c0c00c55030544180500030b60174031309604 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 22572020 1250 22570770 22570783
    0x20c06072402030115050a021c0206040b01050303031005010e030109020603190b03011802090a06030b09031b060601020d050d0b060d0b100206060f0409030c0f060203100b04030507050d02060d14060301060503 91
    0x2d545010054078030610380d0441d0103800c0209061f00f148505000c3d169400c1e030b84034075200881e000b5800341249241605182041540603800540a98410420040e884444850320700070b5070001d00c1c100d1070030354001001901600b02420080c0d1b11480020500440b0200545554501354141a007400f080300030b001050308940b248181c41c0305c80c081b005188030051500e5490f0b158400320790f4000141c803075265141e044009904840d05040ba42c0002030221f201c101043c080c1d154074008000801d498504440000d4681621a01034018800d02103a522107003810f5401c802c540740d0f000780440d40c0b00c0001c05000c40c0680110140c541c0110a400744a2509510104000b8810340c40a000c03110364001c1c0703005010040c046a07a0039020441e5008421000401741001002000c1c012600540c803420070540000605095900584c40c0a0703017008100f00060020420703c044a50884014101910a0012a4444c41007240762951a0300d802602502c440c0d510442c5070013540300394004c105054560007416610344 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 22573270 1250 22572020 22572029
    0xc0601150e041e1109030c041a09061206070216060201020703170a1d0109030906090e16032a02010f09020a05042a020304030201080609010608070e01020c060724020301 74
    0x120150402201428035070805440071010b02082e180c06510f1603035800440b0304141100410180004002c001480e0411102218290071581007050040621186603000080301e062030150070000000755107696007031409821018440141e609600c4e00702c0c070003512807444c41d20940d01e40d0750108001c00c00610510a6403440c1c1c1d407503250007840c82c241e00d04410f000040205480300b4551518a1034503510b500101108582140310004030304456945009080b0905942042040000c5030a04001d44502c14200c1038111200516040a94102c81e02c11005032400300041414007208421a2400d550030303044034415984940e00030440000c4200d0a01c00355200d01d0b00c080d510140f0081c0034422450294010384183c2c22680303080307049044003949100030204c4041500007580003c9010007d5582003001d40381e01c0f41c01283c5c48483e540c1010030203020903c000d07248908015100500181c181d00070481c00b504010000e150f03c0e290b420b14a0036401060b1030242e060075616480d02d000780e07074001500a9074142c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 22574520 1250 22573270 22573277
    0x901060306080c010c0501020f0d05040204050c03070f05071a010305030307021b010e0415080a0b0103060e19030507020109031401090318030c1205010902091603050601110d0e060c120c060115 84
    0x3001500110f1701600340000179540d9550811080700c010710600001d01d1070540c980400f14540c60a801000100c400c001e2010034154420000c1042c1b5690107004040c420546003051501c030000703030400c2c00034011402804055851000004401d006000018501c0340e074107030f42183c94903052030700e480409501c5136002d01c5c003107640760f00c01e9100c0c0d20306a00480941e242c13803050074900c1a0744400c034914150a820045d602d10310f5090061003800240c0c010014080c8c040001001e456109101b801d0000405050280800c03501042140840e0300c2000010010740d00100354442810f10988031500070001000214080344101a1062240d11015581c004481c2c000c01126040c1d454081c0340302c0b070124019000c840c50356a4400000060ba9a4604240180c1c0d0100203035581d85445800901101c401802d140d05020744d5900011621800080c0000110007a1810f40310144107100425204d00844480409501880007a042034480e41e40c0a40268000d00080350083e90742e403031003004400c1c401c40d04540003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 22575770 1250 22574520 22574533
    0x50613031409060c0303151201020405060301180902030607050d20040306151503060306061d010b09030a05030304060902090105010813030810170c010f110c090403020316060605090106030608 84
    0x41408400b90501d0300d00030300014503080856451506640c002c4034030fa25900c2010b050381500d403c00303a0040c0302e5800140c00031882c09041000140d014001481510800e803d528100010804a0307006241e64a50190884485080540c0060b12a4000c0030050b0082440d0045c0031036241e0f64a600a0141000a110b4514007030564407440301400802e0749410b280346500710b0000780d2034088a0b0042481c14035550010b41c060540c030340303601660900d07030100c094003110241003800010f003d00001e0448440814950b514031002c03011a04104410714080d0080c0008401c12050100c65009000c03220310840f44140503a89035070064903980e0303042ea4000f041402a5000768002405508140d8021004e4090481080d41d034890041c0040c14000745850140c001c011410140e50704503d05016481d414108800116000e18020b5590742810051911a500d85d101003001e0600034421101459951100740481c8103132420704c00301429980c440da50003284000c0c00040c41700d201c4d11826094841130b8000e020f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 22577020 1250 22575770 22575797
    0xd0206070213020408071502101103071d03010c05250503030a02070302070b0c01021903020f120604060f0816080606010503040b041a0712060f03080306010f0903060c0c05061303 78
    0x64030404100742c80b89982000003048642c41040040c000300382c0420b0311043c407002400002d003004158903c900d103050501c1d240e120400061015030b81d01c08550724190118078140d4041c050303006941800103400d54038015a094a40754040700800b00030750040c0b40d0f54004500f2010112089410b184040c0054109101107200800a03400a01413903029104a074045503c8124044c00303036218110a4072260760004030051b1815800c98400300d51003850408609115041841d0780142c807440641710014001640058402e0b5a913910501c0513001c3c81d007282e2411910f4001c5a903030303100f4800741d45444c04140c0c50001540a00080d2842c03046406944150940c1c83d590b807901c8034004040c104807032000504003281005080842e80d0351107a007180c0e03104032000001c5403005d8119030640c2c100d031260354a109014408a441002200d130445400c0c60004c461a0820318200c9110440e5040241500e041080e980c14641d0721442c17001c0401c2c02141540d042c0e44951044049072054000010003145c01a1400c44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 22578270 1250 22577020 22577029
    0x309030a081308030a0806030f1605061e0a0f0801080307030c0b07030f050910061208040324020c01020301050901050d0b07031109031c0e010f0509060d18050703020f0d02060702 78
    0x2c808011010400e07a07841d02c07403071415070300320741030110021b03015004000c0a40740400c14101c2c07905010000c0e0000f6040340f03010400d81c049500a043c00740c5c4001520003a5256605610103d14028614103600c41c0e800c408010700d0300401443d0713030001401070340c0013007043c02e0080b040340e61650741034403069080800f070742c1c413642c1e2a04004c0c0300909041d601c59002c0e8003100300f400340c02d2090350b03860060180580551922012604107401001d1030254002021000610100c01ca4080d6070b0000804019100740007105140b680503070828200c8680007041d40c1415290540265050720f00c229210b0529a03215014003200d2212341c1c0000d00030b00c92000c003041403280030368454010f84204501071803401c01200007103441e0941c4110390340c00c16018501d80a648070b82c4511591304059003480c0049200840b00001000c5010f00a1494851600041c0f001d8860103070b640100302c2c00303c12200746149403030700d801d15607158400c83c031080e4080e80f0104030120641c43d0040f1002e01180d1700924440c24541c00d6020b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 22579520 1250 22578270 22578277
    0x11100908071806091d0708030a0203180301060302030708060114010e030307031101060902130807050103090305031810140907081f0506040b12032106150307021203010909050f0309030a08 82
    0xe10483c0c1d00d9001299054050240c2035035090f2035503066413100440d15a0303a15200056101d034201d90401e122141060307601004417240c01041101d044060620751000a004010302d038002036040c0700c3c0c3d078000541b010022074103604a461803201102c100d028500107442130203c0c07070b00a0364582c108100400c0081c0c003130003e4010365a111000011159142c5125400301d901100400d21035283c1403c00b040640300400240303006d80000c0c40c2c24003204072a5a00500780d800040c00780101e900c2c000c240d0107140c2d64200700103010616203141c10310101c00f20350a581c01d68001612030328050b0040a002140218001505014000f1820180c080b508881001040200406092107138400e40310303802d02e09542e1703c2e52444100b8402c85c00141d50b0300c031070310894035031044803d012483d91031a04c5401c019503503035020030702102c01d000400801d17900d6559500c22410607558480c039580309900440045004034440d0f01c0f240b0460320510840e5176000c018040555079003c0c1a01f010f42c1039100015800018141743e000d07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 22580770 1250 22579520 22579559
    0x100917120a09090e070509010e070201020f27010207030203060c0c1c030b180408030601050903030d0603050105070917030406260403050d1a030709020a120501031110090807 76
    0x151000c1165451110205a11a841e210300041c40d0381e0082c001045940724510503800054014500640b4002c0440c8200750144118060017040c0400102401d00079012116107581c0b9189040c5d43e4201c801034840da498040000d02c010180c4904080760075400082e2404c1540d40040041c0244c0d655030011810350343c000c0800b21114046c0c100150000403126100d000c12080d9a140820761508400030701ca06009600c8041036629200b00521010071b01880440f60030040a00c0d03c26500e510b01408070389140b04c2d503d00c0114042c0350007400410302506510050241c2131345c2e030701e0302d050aa541203c0c90030002c0b6200c0040c00c0360001c010400c00c690240000d50020802410198000000180740051408084409401040c0006003e0004010510a04040202040d0600359441c03498020036910390a40c042c0303855599000500030a603034004e607080b41805540d8503062100e582c40789030a1034800300503002d2500804807210301482450082d0045002d5926030001800c01d103241100103600401000708 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 22582020 1250 22580770 22580773
    0x3140619022203050601060206160e0405040201030204051f0f0c030207140a050604030506010609051206131509060902040506090106230d0212060a05040204080c0909070801060320100917 82
    0x2509036403081c0c800c4600003c41c0640050306031585002c0020342452401022200500362010f80800c8250f0007a0f80040c112a007610700180940d510320040c0c0003407280750055030b402000160700d54030360302500c07481000e0078501d60b8640c080750090b405c040da032210000344000e0241c0c0010000380108141d005800112000003458814820b0340c13103002c82c1c0198803580042d180d6420420041c000c2a82052544004100944602e00c0000500d01441d854020251007540155181801082030022410509110361780100d0200007492151178000024450840308074004d904140006001d41340c03458a0604071880798480c180500d810780001c4c40c800e420700725104080003052000803402c88052014000347e07104480103107440d0418404100e0b82c00403951155225500401040c040c0c80784c0810740040841d0103840ca180303070340c50b02000c85080804907001503203103618110000062003e03051203c00d2030420200490a1894000180460341424090b601c010502030311040200222000110035071422980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 22583270 1250 22582020 22582057
    0xb040b0f030a0207060e100b03030901080a0f0e010c020a02040506040506030607050304030203121017010903090b0d0608010e03030714030103020108010e040503120708010602010c0513060c1506030c0314061902 92
    0x80d40e650849001e0b54621b00158051040c2c0500840144903940207204110025810b01140300c0000304400c40003003c180031262240d100030340d051100d07046064200c82d0a070003807015030300e2054020b684405214050303100d2030504002c103031641407074807030180030300c1c4007401400169403002815600d55102030f00450452000704404078648000003081c0d4050030b02600071009003807408007154055096003d28900c1c50745803002d400d0001c1e410070038460032194030455035a21801b076201120005e10855025500c9075007080e120a034452004001103218800e42d8440c41c078101004501032031280002d002c0240460386c1a40180401c030014410300e907206100d038040380e02d08100e01c843d6202c0c0c0401030714080d01050200e001804602e40a02982003000030f00d2520a042a5070545040761301d030302034810f0701c061018110040e82405080c4441d228410900c0005008642d52032819080e0b501007880252408804202d54400c5450080340c0140a40b80a50300314031140c040e0902e4000a41c03101150079010484903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 22584520 1250 22583270 22583273
    0xa030525080a1202031b0c0906040506030606120a1a070207080a05030a03021315080402010e0d050606060304031e02030301080d0504030503120903040f060e0907030903020a030c03030b090c0a03060b040b0f030a0207 94
    0x1190841c1b001107201002d811009444030901078035040240c1080d21a41c14002040b0258800107091980701c0002c5490120070690351030150300304090508043c008050240b40210410400d01100d03004400780e5007141d1426507504101d6881c0e03034210900a10b04d400400c01443c1c401d110340c02410340e400d406001a84041c3c0c2d034003160742400d90450301ea100807500070000c02055681012a0120203d02594072001441c480ea48050b11180c0040625105410100210b020302d07228101c1003541908482c490420800e0300140a5500d8100b44038030b4510f4480d410b42043c205100300241c0f0701300c980c000b00450500301d401040218915009240c0d82261005020014400510b840c199000300581c1d1203410103000302d01c05212a07640c0040600b41070508001801001035400111000c0d242d8152034204489807007032608401421142d914282c1c07100c03045041c404c00350300000080910030a203840c204035071aa918183c003001d010b00e11960074581414025909211003445c0103540c040c050030001850300c1e069 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 22585770 1250 22584520 22584547
    0x30b060a1e03060b070303020d11130e09010c050d0b0f090703021201080a020d0f03090503011401170d020606010c0f08041205061b07030c110a030525080a120203 71
    0x21001440001e01d64200c003240c40d00044009040101c072482c1c103200c071074108120b0f0341c0e0307511410400508141e80020b00c03000e4020994840107c181d100319032940e0340d01b03043c00039025444242c01503e44081c407400201d0200e0340144038051044e032031500d55504100541c203200d401086101d8016070440c03003543d5007500642d100120944920101c1d140142c4460395000010030300d075416040480b095000c8101040543c3d517100d21401519800744a000c60300c8850b1500315003040c040e502641d015820060745409038800000d903a410b03640c82800321410054094000d943d5030314101c1d900700140e041140881d040303504c9501103074040c2d4024800854554503681e01c0c00c4141d0b0066101010344440c0d204014100034040c07140070b0b000140481080f88100f00310026079403d101d9004d005040c000700821142c10440c40001014a081c4000d00083c041c55403400d00c65102c401c0040340341e4801600c03030480e43c1d00b0300c0c851449005544c4000c00030109400540d45000510340c140103000194482800f08282640c03d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 22587020 1250 22585770 22585777
    0x40b1512010c03110405030a060203060a0801060305030403060b0d1a0703020714061006110c010507060e030d0902010306051210111b01020a02010605060702010804020d0201090b07050105060a0e1006050307030b06 93
    0x54003000240c036104400300107085903a0b207100e0091140e030800c82000590750028021039a46c5e0000c0b0016601d8407800000b620024455104a00381d5081c0640081400804805070044074040d00c0d00f4014003000780104a10301c0d480381001009208440c421168030140000c011340c0c00207242c2801072904a658403810185200c00000c840070ba1b02031400c2240c0c2008180454004002500f01080c41d000300342d00c0c480c0c8900202c2c82c21410030101103101c0313090064a0f0040c105400141c01a41d03620103180c9040000307880c0111041c0c1c0444c2c20301500007980c0c01e000140016a450000c00b1f80b0f403800c010b1404c44041c0070f801b885514940414800c01320b8060008648014a001e403074001661400c070b09d01c010f03080d18502d40c407030303446140180300707041c00b60340c2004035540d0042d07040710401110041e07880140c2c0c00e01c2c0c842c1c00c4480307080381c0441c494040010541c481802444100c1c0c00000711940e4081c3e1048203031045608409440d604002000000c2c012009150400840d050100b9405200d4002c070340c1c00d40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 22588270 1250 22587020 22587049
    0x61b10020c1b030a1205070f0b01030f030e0603010b270414180c010509040b0103060801020a210501050102190c0810050f070e0102071202010201020f0708040501020d0e010206040b15 80
    0xc014400007000351440268800301c100055000d804c1c8100d168944001480300d480c10300c2d0911100044281c20001c03079403600a8006da000c039680c051543c40c7e081c89194600b0b40441200824070411030080f4510703140040d64120b90604110070700e005010061032903c0c94183c001d051913000000d02d00300841d5680d001e2640442c0416242810614041e00558510155295011659080682c0c10f40260340c0c480c048030110041a1804522420044012001044a603010740480d5102003502c412941e40006140c054842140001040082c120842e104640d801e104450160740851141c0000715a600d9640980502032140e05908503690015242411003002d0303c078882540d41c20070072400500304004071317402094626080e002e4002440010396140c0300b41c0107080b000800351000c00308580c401d40450700c400c0380d030302c0c05561500c18524000b51550807078050310b800f502440d41e404446a00c13480b02103070340e284140d00512903525203407107440c80024064000710b0968100010040c086e100d00780c02c0030840 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 22589520 1250 22588270 22588273
    0x20304060207050d030911010c0302150702010e01061e030303200309061e0f01180b04020414040e0303071205070e12070302010906020a0b010902030a18060509070905010302061b10020c 81
    0xc1a0503c2e0071420003070381005100c189803400c1c0c2c55002003007000041d040500d9084c03d040441c00d545003030503450b100e10900c503140a98480700421600580c190845640600707007000a004d49134035180e0141000c99072600f0120142d048c2042040800e2181c1c115442c9045d030303066000c0b4442074680d0480845d80c412645151a40e001c40c050011241d602e8184180032008a0b2001d85241000c0d00402c002800601c0b801680300d001c20402c040e40140c0783c4c0255090f84004000315503682e5103002022040103409290741c8141d01e0400e10207001c00300841100d10441c07283e13a074150141e08a4491000410780580094100003082c903841403641c9910350f0201e04000c044005140052562000410880380d64000c00304640011803a01c0c00a043c5511080c103403075010b400907031265950540b50005006d0321140c40350103009a8071000502002da440207008403490400e076050b0685800c0350406546d000e00c402500510200b01200c19503860360340380c281e00c0c40302405992400e5901c50004090360404004c40c41c15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 22590770 1250 22589520 22589527
    0xb0406090b0307022d011406090c0301050a121506060c05070603020f1b0c0d08030a15050114070203010b060c151303080402100c0203031c0507020c0913060209040203040602 76
    0x205504030240c0e90050510000080c5149060700009440315100004500d44400860007140d01c07207040c01c0c0c82c01074030110310020054046142c00c2d5200024081c1c40c4d907070081d280c000c003180c502043c2c1c2d41201e05943d00075202005c2d042c5030a64940c40c2c46018030f001d6441d00d005c501d00e00d40d18001c5005d1800140050750b10782a20320002c0c2407503420018903900071414184100402c055008580f070503240d211803100c4949520380f20b9800c00509180100c0c85041d4400701a00b09207040003c42000743d0300410020604112000b0b00c150a600200740c60701500d8003060800015001d0b000da1a401814200e03c054000b1601d111480c3c003141c004d40141e902081980c00581d03036804a0000201a183e01c0580d15002c201448403580300a410201d010b00064061004003580224440c001e01ca003c107210340c054100d1f036642c030002c0a480c10003c1000b0210102e1402c28020401982c4001240f100b80d4800070801d1740c1a4880030301c0005c032410201e03000c9480301e80038401c0c00c0659950344040c6100781d01418025a8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 22592020 1250 22590770 22590779
    0xa030203010302030c031501140d0204060608100e0c0403020618040509100e0a020d080906120a02070b0c0903060708090f010e03070302070f0b030103030e0d0803131106120f10080303010b04 83
    0x522850385d821038000ea00550720400a0303c1c043c2e04031411685200d1401800349001c07000b1520060100310040d400500b40540001c0c03030b40e8440300541c403845442c0b40c80031419446840700b8034864810340702110700300c0e018441400507140c44401091606103113a0711480c4800740d04c0104003a030344210b6001c0440e4000d0708420b0600a010300980c1907540c0540058602d40d0040e0740000c12102030940d000d400c00001041901090301c0301c0c0708580c682480710b0700040b541e151503405000a94003558044403a60b2601e404501a40c81c0c0b101502c902030350050284c09559200e12044441c140d00030401503640c8108002c2c0308007071400388070342010000c1c12806503665440506020f4a0300d0410780c81404455080d100800c8040000f00a403810340f60b051130044508809580001d41310800704030301904600000040c0070403c4051911130350361911034140da000342a9038000700402401544000c50880752480006401000c41070103140d8010081e03203000d406291208000c03460368100360030540c00503100240900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 22593270 1250 22592020 22592023
    0x60f040c06090609090b01020c030a0602180603010305030a0e031c030608010c020601080703120c020a0e0402040609022d070b0f0703110405060405011805030102030702100b0f010f050a030f020a03020301030203 92
    0x4081c01407800c1211155182c0b0303900603d03d001512a01e40e40070743e01c0194a801381c0c030a00c44068285030080441d090041a828458025031200c04884ca02282d00742e4904414203118081d60304894210001c0d6082110040042d00d010f405aa4070703580c10700884044040b190403e40c1344029121035079600040c502d0800d074925007103800d50304082c1c043d980158010007030b8180c0002c15900352a404606424a540c40031001c0e140c0180f0407500a5205031040301c0400d900a049108501c140d00880301486a0b0b903650201100328407500e00c0541c00c8100c0841c2030175640701c903440c1c8200c0c00303000350345c0c0d0b64504800fa0700e0315141a1000e640010b501c040782c100b070110719545401000308552040010a242c85e00e04000125988214810107040c400c40d411411202c0050240b010b00521010b002035550385042c0000944540c80310484828003403078030351841c4075410240340c2803030248010b841c0e0a8500c141c040050390700b0781002d800d8004060311102c1010300e0540da40080c05a50440780c0340980c030380d4190720406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 22594520 1250 22593270 22593293
    0x10c0e130603020a05060c070f150201140121050a0b0c031806060619050d06082a03060a0504080f070b071205040b07030c050d02160201090503030a0e0f01050705060f04 74
    0x10354480c1c20300c881400542d540d1410001190000c80e00a80c0c1c40d106414030368103000180c1e000c1d4042d030804520004c1c656909880000c1c0c0300316154004c1081003c4242160785169083c080c0c07101c1c0b00070900344c151068020040101c1130703d0260007180c070544004d0707980c501003260485080d044902c0100a0280c0c1034a05400b818800700d051003c1c1c00e080c948a07020a80740d020707400741ea8200c100d0000040e40d50a0180c011a0011100c604081c4035160321448115607035194482c00b07200c00704100c0316014580c801c2e24004c0801d9640100940040d440703d481d10b801800c0c0c00351041c0d030010780c20408204244040c100400a5601c1048031229614000390049c1288100b50070003140941850100000a07480580090344280241000600c40c0044001280c0c680500700310f03c000548002040001712a0300003056400c82e10034ad071258041c1e6152014591680103000c0080c0106004010044440c03424440c03401d4000810714205081401503102c00b8988001a0340c414400038031071090100340012034001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 22595770 1250 22594520 22594549
    0x809150f25050c01030c11030a02070e0a0b0a050d0305130905040501050105060a0507170c1515060408030403150f020a050307030f0204081b1f020610050301140406021b010c0e 77
    0x241c0306040e8252078403912142c005150074105a075034501e00003000d0080a00c0f403100b0f108502165220808108042e6842c41e071402b070700e01412101c10009003101c0ca1b0380103c144c8801301421191020345000d0600907400c4002c00d0443c107001040c0080c0b041d05004068006c0244008c050104650078030f41401400c542068200e60300460080040d000070607000000c40c2c608a07407044224440d4010701c002510180600d80144986028010419885800c1c3c4030f0070b1805004016070310080640c140d0200556881244603810f4a41c1040c08104041003c06107040a00742c441c2c0001720786d56803041d48040490344112841404140d02200344000c0c103902d48200b011001c40204118070b010709007401c441d510001d1180007603100e5042c0c0c6080c122520b8a07480041c82003c5032010998121400748007940b591000c44812548858413800041c1710720301401500d0b01148580d042c544503444544540c0040d40c880c41001700c2047e90300441c080391207402d22528124603155a141780e02d80b0642d03001c018540f070b180f521 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 22597020 1250 22595770 22595827
    0x603050403050906070c0801020d020a0311030103030c03141c050103060506040501030b180109020a0603090302060705120a090201110f0706110a05030307030b03070905150907020105070c0809150f 86
    0x400c030000b5000001c90326039003001c0382c21079100c0c28145841070f14261160065241540040754081070081d460b000b030030040c0e9241d00c092108031854412400b13036010034030000d000245c0e80014400868041c00e0180c00c4404d0150b000d501d05080c0859002d9070304003141e034800c002640d400040003405464421300d42c00103000c076000c2c421540b442d114140310500203080081c0855103c0080701c0f458100354000b555156001d005010425941c2c44040e00904d90118107801600980c400142814800c4040301d645800b06241094991038108601e8001c01a07110304a06110b42c0c038903c4030138000104902c12004d010350b030041400500300030005102006c101032a0b400c903808210301400054011054982c84449031800003503811102002920341400782e4080c80f0020300e000c0610440b412411070310303080007109840e540c3c881e40311080201d0803100304591400015a10103250400034224400074103d551004180d802060f449950318200360f0710bd90301070500800002000b003628a001c1300c1092000c142601d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 22598270 1250 22597020 22597031
    0x16120c0603151a040504060305010506031903020604060c05090d05060601021b0f09130f080a0327170d020c03030103120509010210020304050115030807030e0a050d060905010b030f0a0c0603 83
    0x8820b02e2456050046100c1c0c1c2c41180c1c2510344544021064500401e4010001d001c81503032410018002c0900360703400c40c021700034a40c5021040105180c03c0007541e905500610031981d45407070f20402010b01040c1e103c00c0142c2001444810b9680707001000c400343c024406050b40b03041071000645030582c11f41280c100c40e0101102150142e0b100c107070403c600c80d400d40c0e1182540d82d610803602c185540c4061b009010003011500e220500c01108054002d0329500c1d281006490702c804125445486890a40016400104040e800060f40860301c0050b6450800071a41442469042c0030180e070890b02201e01300c1d81c0044010000d01403220401c11700034540d41080d40c501000d142c0001d48407220302c00060400d9800002040410002351300480400e440c010507481c80c9a203e14040e00c0c258080d207800e4001a0315029081ea0030301d44101d0050480300014114802c4080650b141c174081c000c1d001058409540c1d516280d0100c0e1400c2c441d00c0000f4640c1c070080c10003103100d85407240d540300c81908850101454613 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 22599520 1250 22598270 22598291
    0x403030e012d0510150504080606010923040905010c0c020f04150b03070905030109060c1709030301060c0203030712050a0f02060105010503010b09040b15040503100b0f040e16120c0603 81
    0x441c620070980396a82d1011905940d81240800e40f90f159610035007402042004100200d40c1c03140162043d50308610580703190f503c0c1c140c01110ba0301001d004140c40c00404007448010304a006107140c0384004050004160300c1d041d80c9941f800c64940d01a58000310f6042103981d421031606840562a451044074100246100d202590b80c001389540a82c180320342c00000402c4105006041000050100030024000d0503003a24044010304034040d41180890202410138401c070036121000c07445131070201c00440c2183e1034250308550000c00c82e0380071780e0036002c20081c03030000c12604d8008240302001515110340c0c0300f46001001b444624442018170454000c0001800389a074404212030456420f5414a5102c03415070300000e0091044007452540703c60784e4208480c5032082c61010380101d48040b400c3c1c4000e0346079912032a007a43c00d4450407d6000050000c140c4030307450b295016549900081e01114490f04003c0701da0205120300d50007601d00c40c1c0507800d83c00100a03d09103075a01420301440e05000c0610b40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 22600770 1250 22599520 22599581
    0xe030304020904020d060204090b01090501020307210e123703140c030a020d020106091802040207170304150507140a08091204060c0203070509270c090403030e01 71
    0xa00002d10802141c00801c065684014044690a40100b000c565965035140d0780e000600080a8040c041254aa40060315600100940702c420350450401d80e41800030010310800c007140c15626200b4450a4a4201c0c2641c0baa12079032026490688010503071032039103103031005141c00b040800059103465900221941d0a151a035540201c0e4581005189011402c0750f8641d80c1c003906840500350311020a15040c501ea00007040541200150004c00c1400d45036540768050755180c07000300002034181140000142401e50003886014000e04075061a038110040050b2285d109440c243e848100202e61000007498920070b480c0c1055250a001c03021000c07a1f5401d403480e0140b070390080140140c2d0000a0600c080600010040c0700014085540e2180c90f404040c240d015100070583c000e2040007800702e69030401590311400713030000b4080c2c0f0b01034a000368881c80ca40c09010b108000207000322002c1e0507194840202c9980074074460344002c20758800000050342101c15044a04403600404100c82514611 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 22602020 1250 22600770 22600777
    0xb0405060112120e013b03010c05040e0a14010b0706180308070302030601090e0c04170102090922020411030f0a11190c02030703030306060207080109031704151109010e040e03 77
    0x1c107040044401309950010394460100c51140300e2100310040031248225a0030032580d80303980380098024404c1030080305241c00c0365a080450008220208024020000d1100400c0d500408041c008250581c5803400040c81e180281d020b80014040800c1d0001040894021401c405414103099003100c0001c0d01c00520341c0700c02030458010315500101254090344500b6658001d000c422100320501e04000f40c0903611540240325841501c1c01c4070b5518404440107000700c84186c50010031035900ca0301c0342c814081007128100d00c10b01c1e07102016516a0700603140c070700981c00224000d4010701d844c1e1818000e145a4101700600c03010390316103015980481900d17410140c03903041044480e5001402c42e80785007a10303b00e03246507019502d0312402e4000410994150409001c2d15450303429140c2c1c041c1d581d05c3c841d00380c03100030381c009000c6099042540365500b02d1a00c040c0d40076004200078000d21044c201e884084a81030541840b428500181042040d6042200c0c0e00407000d05aa04021400e100e550040d00ca00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 22603270 1250 22602020 22602053
    0x10b130504050606070501060e1501030516180e09060a140601020703060b0315041104060806040308010306110904020d1406010f080406020901091a030627041b0906030b0405060112 79
    0x3a41d490103d01107071258804d540761583e205000b0003086481d007032503500031002103030310418a0300364400c04003203035100e405814014621108820203151030680c05680c1c00c40040f0110a040d902520002404480714440d1801800210090102810090a220180e41c50306030304050031000314090101c940d03800160b00d002c80f600314000094106a03540028103010006103804c40e6401000240000d00000316001c82403c1d000710360822419603a640819100c0104135406004551640010004114541c00603035085650002492805003001d001500302d800441080e914240e0b58000210f04e07078204410180c0014007400c240072281c5909034001c0c894940108001c0c0741176000b1404050316400740d582800603000c4000b800002e031348a51031101c92504111841031003108000110000004c902c00c180181600200c0800e04503900c540b1180842440002007050101a8801c000350002d0580308060180d40714802105440c200b03810014603054040c0c111040c00c50710f481d154030004815075103e40102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 22604520 1250 22603270 22603279
    0x51801080606010309060209030304030b060a081c1107030605090c0a090b030d050903010603080a050309100c0c030c020102070803030c040815011523030414060702120d0b150406030e06010b1305 85
    0x30303002c0c0c6c9480c0c406405142c1d40301c1d415200c01b013408400c01420071401445582c09950300103100c1d6a401c000740e80c2e072280c00c1c0490540d106007036540d001c052261b14508404028402240c42e01956075481c1e1040350412603803400c40d6000400410b1086c901402e4110040506923400c0c00400c3d801000131781c49103400d000c0c3c42c050080c0050100c5c0340d511b0a4001c44c0082d030300426800d403900e507161000f80c035039841290070000a000c1c0d020140e10280f528445c0440e4030079243d4804d8078284190364103481c0100b01d00c80c02d0b4150b00c915540041c1c3c03035404100440c85a407200700c90b00e8607580b40400e41032038030100011080484200600500c250b44407808032015081e100d2a010600800384883c40290050f4589901c1590000004100c240321141000300d06001208040310b006584540040341c0700d0001500070751140301c0130054000914403980060301c0d80303c0c00406056583c0700c03030504040a9409540b00348007198641901d44905a0700740b0001b401003687c100550319004600d00c00c1840c0d00130500600388903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 22605770 1250 22604520 22604531
    0x80702060c07020a030b0c04051003180b0c1303050d0e0a1404020307110609010902090f0417030a020903060a061e030c03030516050a0614070908070504090206120a060518010806060103 81
    0x3c2d55200190b40000390340150b000019400c1c020041c03811030384580219401b45400004404440d44244903003e900102c2c07480d461031a2009a03540140f41c0f401401c4c0807038141051100020540343c00000342e0081d84154002e000c10307800c0100142c5107884e481c180da40b150f11507003170401050b01c10090055100b001150010396996904500f5141801100711800152040400700525404150322405980380200c519884036682e0380707104101c3ea181150014049642c4147e03842203801001c02560704244050009414000c03504c000c40c2c5018000c440f0440c0d1030762901010000201404141040d901440c00d004c602c1d5415910780d510301c034446100017010410f00003031440c08400900b45490b00198018184c80b1424040c0c104000601081900520046542d10219070070a002e0090041140d8a8038044d005a03482c000410000b4910084140d0f000041002080b00400d40031111720310804080ea000200d003130500040c010191251458404004441c9005204d0040002001503200d4000d181c0400d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 22607020 1250 22605770 22605773
    0x40e040c0806040f0302070e06030c01030e0102160c090c020712110102010b0d030809010b010504050a061202070b01030803010315090b15030a0203010f0e0105090106030b0123030a0b0115080702060c07 88
    0x1025089940716001030300610b0244810046006500a003031400f030f6084900d86d544a980314000302030b041d260350742e041d8020450040c035540039400a4610441800c00141448410300c54496120300c202022104040701c00e00500c082c403403a1140350b217640d2040c4000e010503410904404a00980b00c0c8000d09034040c0865443c1c1c0ca0b81c401d401c1000b9802024158203000421860701a05005098030729003065402c01004007800d5108100b65411550010711544041c0c1c50110b00303550b00b8044640300a140d40d001c000071404100001d484900961041d00110303965803450815410348032610f8044940c240c20012400003098142d0b05881e0400303010000c089010001200091506240340d000039015402c150348800820702951007182503c080e9002400290743e5128070b40e088908500000308268849001446070703442601c46901d890940d002e072900c0c4507013040d0009181c140e1000d000c49941c2c602c400180300c2d070501c0c080050304180080c14101da5605010078065110000100406604000892006d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 22608270 1250 22607020 22607033
    0x914062704181103010e0309040f0f06080a020907170610051b1c0e03030d0c021f1a040212060405190e01061a0304080f030a060302090a06061e0203040e04 68
    0x61541800074020000c41c01440282d031600260141c0c190f40301590045641c04509060003920700d180d421002962908141404203c000c10811052a421039900e5909520110503482100080c0c64200b008144006103841003040c2c00d6001003248041000c0304c60005c0400c4540402c09402c68402c4801030502198004100d0382c13400b44080c00c4403e03c40c1c0441103140d840c8041194040483c03542d900100c006481642910101007400001d50550700802140c0e5441c519a40003440240c03440c819a0001000c045181c080300c1081e03510001416914200a0071300c280080e05d08001010540d0254180082121105610b800040c007803801607407102c0006101c000c0c907203072000d508403d0000070001005501c4465000340358134001c0207803201c1400d03102200b1803082015a485150302502c11450b141c00b5918003600ea41000e081007210303071340301e84c004401642e89500e001c0c0710301c036002c80004009181500007047c0543d0006188454400210200c028030740c080211416188030500204807500d075481c0c0380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 22609520 1250 22608270 22608337
    0x20303070e060d050a060302041805031602030a02100215010909021806040f020c030702030d020610120203030d09050312070e030d080408090307060504061403060901060c05160602010c091406 84
    0x10712203d031a03c810800301a64943c452420f590007901c0c10001c0082c05150301c20450a0b82c80e002d40a6031091082c101600202000794240e02d1000e02901c031419020790100c2d4110000000090140e080850350210507044602c0b400d00610340313103009000440030368002c5034541d20000090f03900c00e40500c0000c0d1050b00d07a42c02c07580d134810603a00110750712001c040c4d02c2c0380c994205a00891090040c041100f078254070000d1485c0c0203060f0150352400b160307d0002100740140010104903054003080c00101e4020445e44140589a40900701855841c010204003500d2140d00900081c01d000020b00306000e281c0b00000d1141600d591810504105d444509040b69980200008540d0501c00d021000c40c0d11a40300001d0001c1715016154089000785504a040c0075010850754990050407510041241a10840c0140003260080d025100320408100841040c0350340d6400180140c1e4452422100d03490340040f55000030480e042102d800010001d00140d0140702d00c0003c2c0703c01e000310420380c2c100c150041914 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 22610770 1250 22609520 22609537
    0x303050417040f0314030a0816020a0210030501060e0306100603020a0905040207080913060513112221050c0402070201110706020d0305010801090c05090a0b0a03050303090d0f020303070e06 83
    0x40320b49542d43c40d00e00725a1207000f03020407108143c10800c2000c0164001080e507140c136903d6242d282e01348d50740c7e244003500c001708110300800f1841241c00e0b8802517101c2e0183d01900039070568000c6025810180080c152000001d0b00354042d038041c1080005050b9864100c1080c1c2d40e1601c3c025030b54030900b07101103c008405030041640284006419020403002400030a40f0403c1a12082c481950034000c000490b180c0384103658000d5030952460350245811b42c005409200c0b419911410045031074110031030b44031100000c810101052005116465040012071854541080c5051030341c4400d9603095114943c1d40365850003541c001c1440411a03004d4202d490a8100d1101100c2455030b442c0e000958901d07040c000140030915050020611501c180a084069908003020318401450002400320700c0304001d0519040e80d5070f5600261042c0c0d10b01c1d101d10015405207005540f6030904c80012802e01c0c0c4001102e20900c80c2500c140c80505402106403948026203080020340c2126400200b8283c2c45580e01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 22612020 1250 22610770 22610813
    0x9020603010b13080f0a0f150f05100503030a0210110c06071d0103060501080402100e060403050a06050601020f0a03050c0106030c060807090e062101063b1303030504 73
    0x1103898080c5502400b1a40700340c2906640f0140c0e02d1502079103030b044074881000725400c0340c006000811100d25a40500c00c1c4510000b1f1140620960300b802100c401002000303480d81ca520034000b58074012071501002c0d00c001c030055450002c2024010b50344449001000c0b24442d142d00081107824103590580b441400e2071002e84002e80b5010400030104e4121401da0300318926002c00c8010a94480e1040f881540c1068581e02007688641d0200803420703020303009601c200420700f01400b0940e00c90070b01a0005602c00d0004002032049886c00c10709481000f846581194400303404040780d034200081d0701500a81608001d40d940c2d280124882c09046642c0010b40343c518001d1001442d140d00401080c8102400e5842c611065114400c614030440241c0c0c0242d40406002c1c20301121280c0419400c141c0e10100c000025150365070002a507069610703680c0150441c242e42d403000f24059003076000d60500044040c088200307240c0344201e00100344402401508050340e42002800b0041a491000490050020b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 22613270 1250 22612020 22612027
    0x15120503040530060708010e061f050901020c0d0f0209090102091009030209070c0c150201090b01060c0b011a03040f0303140f090120030606160606090203060a120209160201090206 79
    0x1a10b9050604a8212100036204009000d8007428808540346011700c4140c2e451080b240d1030254182440320005d0180d507441030001d1040740e04100d50005a401c20452a1141034440c82c80100190900c645980080d01412076604400009802107006090341ba40c1211019800c1d2110b44081d1b0080c060160502d82103e0707841d541c41200c54020030100c080360f01c00c80e40c55046a03106007040711142c002c0304004220b0460b280040c0004101200c00812041084c80005174000c0161941250071500781e00107000b081300c41c0c181c1018000000051400343c41c41000005050311000040e0155110040014000c1c103070100d0341404051094211050391a520308010307405d42400c0032040002ca00c192000000da40c60500d036002c13420309600c1c550001c4800c00c065a810746d030b43c0c007003404001c0d40724503221202c4500d41c144080000703003284200c50281144c0d100c01a00ca01d441424000c00c5c5a0603040f03d100c8102c0b0f51304a0b40165a80c194113640030702d4075804e5a024035003851003603000d0409070400960098012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 22614520 1250 22613270 22613299
    0x150e09120d0b040501060e0d0b090a02090c040e07020f030307050f040305030a03050105030105160e0d0501021c0207020319050309010e040b0a03080c01140415020304150501030f06050604151205030405 88
    0x80d00480c201d20b400b00d80c2048a40d0362480c00307031918405205140d400028141000d00881c41c0880460b500140c000c00340d030000881c980c006684648112403108105030302040074001403103500c8107150700060341e000510103002005c9101d0342d00e010040c4007004000c00003e00782c0c800381904054500440c0d10000702ca80300c622010f0080c0280c4802d0040078000d40ca040c0004a2071204c40206034088405070322440a030a14040500c00c05003d41c51054480d0343d004c2210b61400407408440ca25080305240005844c0e030064030416042943c8002e58007501000401300380085400802196003443c02424500e4603107120300045405440002c2c51164040074400d0000700b840007081c0280540403008008010407000c3c680001a0450140e501904c10b1132003801c8508100560303402150402d01641c0c0b0700c00c0300c0c08001c4454080c1d401c01d0300200c5e1187c0502403505c08216860082c1a00841c08032000d02c004000d60540c0ca20010491141e2582441c0c201c1c0d80c541801002d20440b409401c014142c0c2031000b091 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 22615770 1250 22614520 22614547
    0x601090f060302090907080c07020609040e0a050a050c010207030312090311030a03091403040b030c0f070506010f06120506060313170f03010510090503030703121b0801080f01150e0912 81
    0x565841c600a0710945d0010700351034805c1c4421032180c200287c070300d81490226002d204040c1c2150203201c3e045650746005150704002040100802441500100a640c0c05071600d9400d00c0c21503030041d8155808040140b0000c0d82214052400e0345007848002000031140c1001c90340103419940d0f0b0f54090000007504000d96506801002d00c1074024602e032500d040403200c01c0782d0380c0d00c1107204180c06000103202184e08501944014680e1201c2c0c510501c1c141136154440c58105882a400302070008079070f060800140360801008594240003500400035880d1040c0468901d1000500c25010481e000c83c8003010450701c0f0808a86981c0802141910742c1290340b03106160798428060030340302d03040402a4143d030034841c84400c800d0340c40c09400f95042c124240d0302a030321401260319982d411a11401d0181c0c217600a031100b01c4003100156100e180c954034262071b407030402c0340e81030402c1d0312a410b0100c000d0410710104d0484080320709560014a1541e40d4240b01410604c440780f401c0b10b000300008950561404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 22617020 1250 22615770 22615777
    0xa1401020a1d090a090f17070308060108070e010e0102030c010e0a02010e030d050a050f0405100f030b0d0b0f0a060b0a0c050c0406030b040f0206090d030203030a0c05030702070e0601090f060302 85
    0x105840d0151000e944071000c031001955800040c1d8810f1095000503007a00035a009122000d1161058403410b54069031a10300104800c5a000d07000f18000c2802010305512110850b0098404c0c2072110450822910007080d500d10707207400c10306200700010184e8143e44200200c0d044103924100801500c4c0035105116202d0317590305402d03400200300508520907440c0103c0c42c6040110b1130b4403002c0c580300d500301040d0384a03085202c100c20b0605081c080080c0039110450080b1110b1802d6075035a180c400c0135180503080fa810368403c80e000302d080f000c8840010310040d00c525004001052401c099030f441510703200140c0f0a5403c021020000802d9104540340c100040c0c05101c0e20810948011004100a01c021100d9030702c00035010440c0d110200d40464052040784503201e00241220785049010301c0418a0402816800c6006070700010811041201a21944465007098540320386541010403000713503110103600519110841841c08a405680250410401030500c0380d6001d1210b5602d003c050300940 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 22618270 1250 22617020 22617037
    0x41404050709060605040608040302030f0304110a09020f07030c020a0504060b0408210d0b040e0d0e0a1409040209180712060e010c050a030b0105120c03091b0901030201110a140102 79
    0xc900407010825085500500c01903030f10710341e16541818646070046881c0080900143e080d0b0100f004944000154040154032860141010701083c95a80c4144000e2920315030040c81201c1c07051000c14840c1c0020001c9401890b090300e0700c22003061160002510701ca070181d0040358003070300e4500300141e80c01c5580050011102c2c03400545071680d03101440d00204140e40c900c004141c607400c010515810620360301451443c500a0000240c0300701651405141c0ad001e0380880021070b182020400307240c030b008000e21024208006018160941910210b29403010140c002445403001500045003081a003045032858045001141e010550340e00c4001c440f0400310308140c4000e420070034805080381d014010b5880d0f00080d0ba0340ca9141500c605421001040c81c07104940c1000b0041000c08580c034103d548050151402c41e031220341c9c9092000c0e0705460519000303202c81d10024a4070b820005507030b401103007504482d02805c101284e0402c07411624101001d00030006c10104150401c0c42c03c40105501509100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 22619520 1250 22618270 22618273
    0x1b01030b090103050606031606020d05030403120c03150f080309010e1c0605070e09060d02090a060b07060605011e09051306030b0405060108010501080304030203280507080c01080106030e0d03110904140405 90
    0xf2480038251300c4401880c0034927805a4001000c100c9160b00c150000c60f40700b0300929003a900c2c0c1c40d2001d20302c1c055494000308080000e450301050318019820050b2540141b41c1301c900120041c2c6440000d945a0040203402030600002101c00701c4a61161140300000b442d071a0010072004040e490f0490060500340c0c2e1180c0011204051240d1a0800c2c0190700d00070600280606007030340c01c43d400c2100903034000b072403103a50316107803000050b85081c0400a030034010300c259008071f140c600b000700050002d81011a804030500502100300d410f42e800400d13010039214241c440d0b16207000d0503001d0101800459000600c1a281c07001002309109000c20b039203040e144898001d010340c0c2d80e24006039981e03001d0760001961580052102c0d400b110b0400f60550308018007066103900c2e058040d140c01d41856000ea02c50009500100c1c41c035580c541c0c2c890425070143c1180d040400140410001c01640e035260745001e50249650342d4003404541c0e03004003d552900d00010020301400550f420b2099510105407412a0075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 22620770 1250 22619520 22619533
    0x50a0e0a030f0609110a08070911040605030103060c02030906040603090b0603030315010305060f030616030e0712030c05010f0f0204080c0409030807080c1204060501080606030706021b01030b09010305060603 91
    0xa403a0980c03a540880e500203000410b0305246466440080c29004800c03074100c0c00c100c070000b01d10f0701c070b03040d80c80000c0101c04042e0031040e14254121050740c0c850011145080b504010600540390040141c03030541e90080d100040e80074002005a19611440c01611340c0b145000c140095407e6040d0081b903400c511801c0b0700c0c0304544540d0140b56490105a5401070703120110744074604194032a5100c5980030708000d03d08000c4c03940d4103011030f007007203c20744e910301200c0418108011201d070540180540d09890200611105d86041d59221160b401910010700f081888044041403000940001880ba902d500e010405d2071601c0c072207900298407031310036480140030340d09140d40b041c58140701c0c0b030708110341503180d0140550700d0b44802c4941d040010070100381600144030050444c401c0c07e606c0b611603441514001565418030560f1f9107840e6005064522a038480030040c01403d42c0440d584d0314090500c0500400d40e1a41d90058015065a40003a034002c145c02000005105000400601410040c0c041c0c881 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 22622020 1250 22620770 22620797
    0x6030b0307030c090b030709050a0203160c050303160e030105090309040f0203100311060409020309010204031124090607020d210c0b07050d020c06070f020f0d0207090518030406050a 80
    0x101d0300458403014296541c0d2010822000d225604405c403c014010182c80541762928a039408961060383c0d914200d41d0302004000ba440500200402c079203581d41400240c191045d0759480e0741c0c0c40300030300d141404d48001c0101401030340a018203c09440b00100248420328040e110303c3d84c0c0360451114144100c0c1000035242c5210f00900c00c9034020030f404141408102d065440740821111000301c0c10790856420040000c45c03ca4600c0558002c080840000d40e0f00d03451401e00e020040b2800c90b106216031200e00d0000380419080d00e090020440100d452901d44686c4000200c03513001c2ca11010b17400c800100c0481040080f0506003048260703095131550341e074104c548411902c105680b00010445210303280800c10359406900a8403624540369030241c40c000c2c90325404d0342480d5081d150720f00802d600c0c901d000d813013030f4040c000304058541d45801044010b80014000b075951900f80b040161144d40c50000c04c030710640d0a1030940381c4151300000c40e5520750307a8400082113944200040e00000301c0d255100b0302c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 22623270 1250 22622020 22622023
    0x414070f0608160207030f0c030210030b031005090705030f0708070905010303050a05160f2108060a03020f0f030102070305040609080a02010807080a060503071202030c060304020904080705030705070f06030b03 92
    0x4065503215542c07110280e0751600700c1c0304049140c8014505502c02c1d2000040084c0f450301191075a2441102c03e895042c1c99403041c000c0700700304600c04000341820440c0c10f04058600203440d079050303015060045134548074485181c2c20b041d49030f0040b0390107014080080c00d40110008080040b500c91008440105548007605000c541d400c2c00010b002420422070315a41a120781c028082401c0240001d03400d5a00300d58803010101c218080031590080b0340b110025007046640c61003030960103581800c003400d1600000284031032450f400001d1052200c0c070703400002d90b00ea07112000303440c08018008541e54251800d0182c92500a0306c9101c0000303003004004180a60f0218030fa500340b03239040e12961200d07181c0502c103603102c0034004c3c101440b8544d103110002e17240d80d040005000901c1c0c144241c4500301864014035050900704001680601c1080040c4001a1030301c080d000c2d8007580103c0c0f41600d80c000b0b49021811481034950207403d5100344c02d408030350780043c420440d04450240e01c003041003401907000d05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 22624520 1250 22623270 22623299
    0xa08090c01050405090c0909070e040c090e0109020703021005150a0f03030c0b0702030d1401050a0501080906060d030c0501050403090e0a05100b0d0605040207050606190308090112060e041407 84
    0xc0e80055001d1100308040d0034180c0e040c5401c07404052000d800c15009501241c4c0b82041154954001420070340c2c07a02c0030781070901c160781066444d0704c2c0001c0352034244180d9030f4484c2c40602c10034114540c0000c3c110249071081c07202040c49022004140324909110007914280701c84015841d2040c91151301c009820f42141c0d410f1012203625490303290724100071341c5803541c1141c4014602c1c0c00b5400300300280c80000000c0d214508100440c4844900d882d41080d0070b001d108207081c0c00040c18850a01c0c28402008000688554070140440da101c50204203880c040320740c080800c400605560a0505001c10542c11800302c1064800740001591607580301d804c8102661000c3c0e43c500c40401246000b400207211140040030102d440c4100854181c1d5034001040807640403850680ba542c00c0794051116520305000350100054280341c89400060464a8003401441102c45c00c605100c5000e05030001401c003034001c14018881c030406a0124507150400d001e0074a0504043e060710300030504045000d51101148 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 22625770 1250 22624520 22624543
    0x8040e0f090c0603061503040f0c0f0302060d09110916031a090f06030705030a05010203060f0f0603010b09010e090403020a03080f010f0317070b1303030605010219030305040f020405010b0a0809 85
    0x104424800c1000340f100c1070380003a0840c0c0d000300040f00c2c4210200311400c001c60141d4402c101c21004c090b40d90500a01c00341c40754100c4c030344140c07030b420080025035102d40c2600c2070300c1d0980e080010b01c05c0341c628001900d041c1600340150411100c3c010000707208007025650319440303100d45051082043e400c0307007244400720701440745502103040004207103040415248258400c4010f000c4034440c40c1c27101e0002c2e2070b021190701d003102c40e40c1d0004104003e0381005400c000c00c140040d11008034086140000070000d000500032100034031404500444079a1040350b07001d11040010b0300c1061030341098100252030f01440082a004221100085151a42d80c4071009040b1200010014001401c0d6500c5035442c1e0070400f000d1403810010b0024801080b142d405040c01108441c0c0a101030030703003e18000e8117a407000d0f4040e0341990411204032940d1601e12501114181d4141f0300020385a542d494082d001a01e0f00b038010350040d180500200342c4601c1f110007000c000080c3d4683c01580e6507080380650765036282105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 22627020 1250 22625770 22625773
    0x15060f02120318010603060f0b01020c0901060503071101090c0b120f040203030904090f061401080d030207050607050304022d01030605061309091a04050a030908010b030d050c070f0308040e0f09 85
    0x68400003501403c1548106550000714030180c2d01d0700d83d601a20568200528865500c0000520560301040a0800004203491040c17040d0b244c20300c082c0541c08000c011209021b288150325108090a5001d0317080940e00504450700c03039494031041c2d000d580284000001c03040218000c070b60b0315040030403031601c26a4028025880c02da0344200b4030000d4060a00203c40c50f408844c070840014425019001a10111103a410f05540c989020185441d015005040c00d0510410400d00450f801280303030391b070103030060030810ba03030351910710208015400c2070042e40742c03000030403882044950303446841d5140c00200340da090045540315010030400384240500c0c4211130303880590030811074806402000526026480d40c011030000031642c1d150a000441d02124503401a549440805401c5484c64001c1c103801c400810150700c940f00420355406c6180b8201c820b000000c03411215044d0f040001030b018042c06190f08210541d0791914860701e801c83d00500344000e04407000229004008240641726460950 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 22628270 1250 22627020 22627027
    0x81c05030402100e0103320f1501030c050d0203040515060102030a0e1003020702030703060b03010f09030c02130e0304090b180705040306090c03022205070f02070501050f0d15060f0212 81
    0x11000d603045540380c04c51905041c0c41c0c5038501c0740200300910764500000d1800481c0350790703d401078260742d45800081070101906480c0e01844500d051996214150900c00e09002801c0c0f01400c8042c1d036140603207130424025074000420482000800b00700865100e60010002405880380401a47c482c010040d54400207803c80b2250092031038a081c881d864804a8100145003021030b401207030410364150419110b2540b038103c0103a03e800c0c00d00c511403416803034800801a140140d0340080c030038048014041d101c4d8011405007201e1680c16400340c800035115501301c030b41da965a181410050800e10800310301c40c0c000740c8040c0e4001160b1410917481802c0c08d035961403615055a40d444003c0c21822410340d40d00003210000700c01600c07520250760940d48074400400c40010b412a0312415108000c00c0441081066190042016000103055040c0ca009090041d141d03280c0b000f940c42c0030301900151303840702c03800c0c620328085001c11081e00105443c0c8940d100700007128204d10a0781c1e10601280640400340f03080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 22629520 1250 22628270 22628299
    0x9180c0a050d06050406080a122c03010b2701090204030b130507030b010609030b0a06050102030a1101020c06040311100509070510030902130204170105130303090c0e01081c05030402 80
    0x510050400d61040d0b80d00107502e684410101c2e0440c0d20750b03040b42140e54405080c0d0014007240f00e200303c182c83e401e4605049600881200c0388070700f499010120003001120040800f245c0d80039000000c4120019140c200f4846141103d10030020004455000e0358002100110741002d60f40201c07401d9942001441450ba220785145a070001c002603000d4031a40a00c0a0101c0010356a03010307140205044e0b581c0030022800c41c10000741c1400050301200d03c03076141200410143e6000720035103a40d114541023500c0d09981101c50a80644160541180d80340100c80812081540284144074800540c6044800da04030790807644045070010344201c00700da0720080c4100018a840c00d44650258050b14020541c07a010380c1c0454a030304041c09846140d56004102406034a000505203269070030824001e02040c00c10030f2449000186405002d010907031201c0a170010300ca80240102c005200307400e00c0707441c15a52505800d4649032540380b58461101e461070f102d0001c03849001500d0041c3d400030401d00018800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 22630770 1250 22629520 22629527
    0x51510110c0d0804090504050309010e0102030c0a1b0b0403060c0e0a1208030402130507030608011a0114070203030f0a03020901090906050616050709020409020711031906020703090b0d0209180c0a 86
    0x9403541111924804c10000c25003150ba03024007030095100b08001c64035011904000340400d0485841503045600a00072030392283d070006410740c01701c0d07044041e0010841443d04480500a103a070445020b9a8000800204216490344200e524503590342c0c41e804006101410014598800e106501040f0303560100306010038840001560403910041c1008e11040800716404103807001151440046503441404000f03c807800c3c05840140715a01049030003507459100040c00d1510440c004148461020448204645041003124655002e403c0e200e0307240c6095040013030196100d0942180055550074001501240b207010b240c1c29904024440c0c0e0814441041c6003108503450700080d5014401d20b400000c0b00403040c401803002c0c0c1341891003d42e48060303a0402c412404440592140a0b5100e1039110752491102c094500506501020143e65030310036090403034400100340c0000105410000c0c10040b80b000c940d009045480055810a40048000f0b0340700c00c2448040714050803c036010000b0141c4140b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 22632020 1250 22630770 22630789
    0x50d0306050d11030a0c0e040201020609030a0906080402040e01050c0706060f050105040b090301060e150405090c030604082d18090412110f030403030206040c0b0301120209070210051510110c 84
    0xf40034080700c15060140e00c03240803200c15503100c2d130344891410f02031106650b1305000b10381d072010300c40c401540b81c40e0440c240100030813540e21a003c204003026001c1340444d543e80e000f542511007039800902c290701f41050840201d510004007102c0f140c2c03030b00800044054020441341c04880c0d0507110541454907143c1c51401c113038045614558595a46d01d00840c006140e0a0760340d015018004030324821407d100d0501007281c102521481e0700750301c01481c91400c0d9800003a1203900903801003007191514200030121042c00c0e842c00104d030564400110b81803089810070003030700f1160b00d403030042416080007005210811005440c003030035140164841755143e50081c0000614116040100c13100b5039180120319055400c2900b044005070004010701c42840b00207000c0102070650301a002e8039651404048003c207104001c0c000340502c2c10300c4001000b10307000780200d0710a032200007410700071803400420203545420b20f48642481556540f1840024030b00c2217240c0424800710720b00408200300c131442006510b20307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 22633270 1250 22632020 22632053
    0x32301060b030f041509030201020c010c020102030f06010c080f040b0a0e040902151b0304081c021504020103110c030a09030b13080301090921020303101a0a030b01050c03040f03050d0306050d 84
    0x1001880b031007924904a20503083c401f40030b80c0c001619200d01c829403d0a5800d01c60810301103a005105004e003014070003816a41015090804409900b80c91401140c0c60081c034203002d0701102c01080000e00310441c80d0040540c08803d43e03c84a850061504002c00c540101e240a03400c00305c8101003500880e40d5200400c0704e20070488600c10388100e11010280303164010340013000c0940051141106459259420050303050682c0041e10a150089442100380c07075008002a0415845407056018400100101d0f1080800c140680780d4031031680402500000503132000f2501468180009a00e140550415000b4594452403007403850b40380c402c403c0042d2503804000e0b038506040044da90480351845d1180909100d640d0080c0d903c9203044440410100959846603100c107030074202030003c481c0440110b80d40d81119040004020800100480742d0380a9001044030314440083d0208000074000e0302c020803644543c1c12600d0001d8a031000321f0030303100d5511490760083d1480c242c0f500003d629000886288 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 22634520 1250 22633270 22633283
    0x50307080a15050d050c090a02040303170402060d060b0a080705090607080f0408070e041a0f1305070509010603060e06060c030a0815130501061101090206160c030804032301060b030f04 81
    0x201d8580f0f00242c036818a50900f140d05504c03925950000e410000403481c1c1c00000340e90110304141c61910042c2818940c600300f4194445068002021940d409003980c603e00c15000d000c01c0300a4542400ca05158040012040410071070000250071034841d0086172000302000d0415410403540b603230f8042e940d4115482a00c5d038030700140004074000e00100004c100a103944c003c600c286080c9428403c8100e076554820700461110542046403c0048200f2107410450070b001241c4a242181001820016140c01c51a4404204000060901d03816000307007059401c904891000e580394141000718600c03840d40a0100e030f400c01e016203024103015608040c0c1c040410743d41000ca9881c0080000c0d440d03903030212103031111a0340da4014400e40b60b11488c58210140c265000300302e068941c2e000a03000b8003440c0361b20002c1040c00c03003081082144506241c4001c5912a0361151103507164a0030150550012142d0342d4000c20305602060071602c1401280308869001c1006840c5031105200410034660081054521 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 22635770 1250 22634520 22634561
    0xc01180b03070504030219081e030702030f0c040c030e10020307051606060e010501020d0c02040510120b0106020f16060e0409050f070305071a0904021e04030b090d050307080a 77
    0xd11000400940c031408007669120390350742c2584100f1141012000410040c81d4502009129045000034041c480d00d582e048108095404688013526501c5035210080d014046c7c00740502001c20001a0300c0301c20350b01207030103000b190702c10300048046900502c1e80040f6030b4400510703401c4101180d802181c01c200945815843c110089080009166507110100d0301541e40710400c11100701c0c050412405008244054015030180a000810003501b1200c087c1c422039a41000c01d640440f10840307a0000e048102c1040c0001d4418200300e03c0e540300c2445900058000d41966090440b0b000c2441680d03c1c0310581040f030346500f01001250b203603021221240c3c02907a1510400080351041008081903c1d00e90010041181145403003400d180c1e941d0310034100001840c07104030549172402c05075412920150390058840300301528681e4280c4801e051129941030000e0301205000f40514510321814000741217880130318922908580911044030401c0010300d128022580071101504444106009040000c18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 22637020 1250 22635770 22635779
    0x70b071b050a020a0f180f020405040606030e0c0301060303080a0f110712120c050703180e01080d03060b090906040b0a090219020601090603020609090408040b0a0e010314090c0118 79
    0x1203914100d00030750381a03101c10006011444c20208400c09403595283d03c103c400e28001d07440c010010741a841c15000e035203030405c2c01296185035041d28020075000b4814400729a45100c0030300142400140c00c0a0360280a01d111f90741c3c1814041c0c0000c03070364141c0d00e41d0fa06507240320660000b031001c1e10424034035070340301c10404007071000c0e28000c0c00b20300f4020141b040b01c0c000d503980007078010340314102c1140340307242080203090740d0036046801e03144441d07054101034940400e0a80e2251900c3c2c3e0503000b0b9001c010a000021401030000200c0b1004a1010344080008a4882c1c2112140d8011166017690103010040020400d04064025540311140a800c0d800800c1e15a151141660800002204048045516480c15540c104045401080642420441c26003143c010034014418540c0701401450604082000c016180c4101e400803c40f2140f110748500405400500513243c004130700d800030b410310005d907400c00c060618007800355109200070a01d050705200151051203440e003c021030018040f00000c3d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 22638270 1250 22637020 22637057
    0x3010603030e010806030a08040b07032307050f0a080f070221010c0912021516080403060501180b0906042304060b031c0203030f04020604033302090105070b07 70
    0x1406907120340c60320b900c811040400180143d400401d964420b07813006403c3c02c04941500200c0d416503411240e443d9540b84079050580e200301c4c0c0411016000c85900c00380528083d0400007510340d00d8819000c5d03c203001f03100080c80e44c2d01c0118402c041d1940d1070410440314446c1c0f00c200203040d16407019003c0804040c0c0c0c41c0c4403c044040e2080c61040c42d944800c1d4480c03e0950112802026080d503116600c0010314540100340421003244d44102e40d80000100031a48d90130100314911b94560060340d90361760315128900140980000c0c842c8642c580000588000c080c40305014425080c0400340042c40c803540c0d01e00800010301030140003000c03107840d101000c0600c4103803050500d1065000e10008143d030f2410f9070605103003081c02c0328150380e50080e4440c100359071903000c0102c80d00001c404d1000e800302e0b1128000509075106940c4004c0246201200039845d0900d10a080031880f80002d44420000c07104070021001c1e88645601507000032030170030001002030000009250082c1c0240f829000ca040c9070102507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 22639520 1250 22638270 22638281
    0xe10150905100e04050a0605091003050a0213060807121b0501020d08060109120b04050d02011e0c0e130506030d1404060302070602190207080d0c0b0117100609021e030106080f04110301 81
    0x8446c00d40c9071442031105090028040e03421510900300e4014140c035640301c5a45401c01000003c6c4900c00140451f01750f0070251b042040075250200a84010b542e071801025100b00c90340c44200d035a00317800010a0501c040d225980012100103070050544440f04810440701c15500804081c140080c0000216804c8901081d40c00311303501c12402c20403103041038242546003c000900c5c41c011a030500611140810f002e12401245607800b0303901160b00041c000702a1203001e1500080c0c2d4210280c90307040c01010f84e05401c0180204410750a54507007618487c0111100c028854010050303000c100410850644654020103a5a022703642c01801d01181d0040389400e110134001000050344120f005000c400c03001c1c45500d05403552410581100e400c0c43c0e6500c986950144a000c20290103010030081944007800000454002c0980811540381c4981d0818000c0d00b16420441c0f60880c01160050440031500c1180d05880341611003010665030800c0c421101d000080c8102c89855001c00b0408090b1002d0140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 22640770 1250 22639520 22639531
    0xd0f05070201060504060801051e1308030c091f05030c0f04050a030503041802090a0e070201090218090f0f210d0906050f0603062406070c0e10150905100e0405 70
    0x410810f203011304000940c0c416401400159140000b40560f05541400c0e41c031720308030f03550792000c1a60759100d0003590b005011140681030030f200004000000314081c004054078101281d680421030503c52000c198407500300c009a01056040000c00c0000b4044000341500c08281c185461508d52900c0100c3c00a5011382c0c02113076240d0010805104d03c0103038103215031003509001021070500b0303005030000d0042b0a8034480d0031741d4400c0c03c2c404100b45500c0ac0d0000382c074054000d4040c509820300c4a144240090702120f541a20340141d4000028052000c030b142c01004140340000c12810203140345c04440300c1d0b8074100a101001040020311601302c02801407501303071401920001040d10b448444296404002464a072094020f44108000040907a150744640d41a00c4404803a00c0c001da0081070040c402c0c80c0c0d02034269201d020000442030385410304070703108002e01c2c240c0d450415078450404043c0d0341e0380b19002c4003084a080051005042150266400108519140381e000c40c042010404441040e02c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 22642020 1250 22640770 22640773
    0x903062719060b06030c040b0703091e03050d0201020a05040e060118060f030f0c050a0311130b070212010603020102060c090402040e070818060709090b130204060c0b0106030b0f060d0f050702 84
    0x1ca0740140301207803060001c0003000343d41d4585186400182e5200320700c104c0c01100b048803404121001030501c03804402000e042001c00031039407200401d00c0601030190501c401c0b18903102e15a5958440d41c4103009894582e4529124a403c2905103004000c4a0360001d003103078100061030941400010315280c90341c008105a45808004100e542c0c0e005042e00d6464061103c4241016855217285502c51308940d600c141500e0001000b0900901d006810310404284221075101c142021401d002100c1c01004000d01c201d54070000309400604d41401d0744e40520020b8056001074000422500003500201040340c1d00803c010320701038450400281900c0240c0315440094101004c1080b4940981d40f02c00000a0036402410103280198004051843d94060440f4150300c5000b032078a15101d00420100301420f214065464640f50f020040071038050a009a42c9403c1c1000001940c6010b88200d000700c00d03001d410726203851036030414003404d64400ea650007085581c0f80c0000b0200c2d2101d12495005001c55070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 22643270 1250 22642020 22642063
    0x20f031e0c03060a030b0a06150315090b060703080a09020904030314330102070b0a0f26011a1303030e03010e07080703020409140102040f09050c09030627 68
    0x40e18040303004014a040c092080800610100d650f64610719021a6482800040641d54145010020300866800004001d0404440b141301c160540c108424143c1400660140d25503500c2c042400c0d0347c40300d03541300e0300304d4010002600800d108400e080d0740506103e601017009141a404100796417011a000d0740040d0350303a140015a603a144640940050386c0c01c08000403004407401003c03c100141030030200f07074649800412020b900a00440c1c0080404208203900c8403070018001d04429000c0c1d89c14070010f43c031406680c1c6112420342c60f44001c21010800303d0314582c240240049242e1040140d802ca81a00f400100f00f800d01142048010b14842c0c1e0302c500d8401c1d030103c24582507541829507010950040d07001030000750350000e140c2c0100e03a01101c020a1901050030f0415001204050b000b41e1540001804074002074800c00d950300b1a0b80c0868200600d64440144400c2030098105503541900050f000c90007050041300000d0401120f10310790403080507007001c000d14100f844c000181f20051400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 22644520 1250 22643270 22643311
    0x2030a06050402120708130203060c04060207060203040305030f03040f050d030c0f030902010e1918060315050702030a08040c0b04030506090c01020616030509070504020c1b040b06071401020f03 85
    0x1402110000d200c195019402c00280d4141404d04400013400c0b0410485d1203400100c001814401c820300c2d4a8000d82600d241c0c0c10b01c80070010f80c41e4014001c50016114001d070009906d4400003c85049a4004000c4c0d41801085079030740c10294005001510811101c3d440c03007021075001d206103c14200d9031b450000701000c08031380140c00b820020182e50203041ca05600080540d81141c1700e4450241c0440e550720807500c04252030a40c001c0513401200640031000a88414101b040d44031a042e24016080c035440d0101402d03c481c1070318401c44800c00160001d10550f888240119903860b006841a6a0106c5150b15480c5c848083d030000c1c0e00950b1554405401d00c050040288402c1c06824803e1014005900e815240b03404c007180110100010165201c00003860641c1c00c0c40a40d010b04030080055642ea0f84441015554440c1500c4170320640040303404801c083c1c505441910b0310804050b05d61400c06025466007a000c080d05068201d0b595003c01030640c401c0d44841c01944564070595520b40410b101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 22645770 1250 22644520 22644541
    0xd0b01090f09021201140a0b0d020f13030b01091104090f0e03210603030a080c0a09030f0f12030b10030207020a05210d0207060c0b06030109050706050408100908120402150d0203 78
    0x180d2040d100400080c41170b10003500c2e00301c0c000003a14038040008d0303075640c00724401c68000c0c842d00482a01022022070042c40701101c0c0001d0108481c055000010f5590701c0d610340a044422116404c490010b04010030030200c4490b8216400130841d11000003408040020b4190959010a5400761680c01e807504075000741c00302d24401030708034006800450a00600200140007141c019002070400c0001150044442d4801c0041801035903020014a4481d110b034604941d090030044012105044141460003015101e40710380d0200c00f00042c040481e02c10600d40c2a0b000707512144003640c10890381d103408034041c0c9501d903054501038041a065000c2810071182a030402e03105480a80c115000000104003041c2c1c04021100ba150b000240d0070700d25100c280c0003900419440700018841c0c052540c001070029041b01c003a1040702c4404003520005040700d500403046039001d42c4010246603080c0710303098603006854041540b03d0320281080c01c90748141000120190002d00491a070a0780000c100a0880407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 22647020 1250 22645770 22645807
    0x60e0c10020c030601030807021318030323010302011206080f0c0307060504032d0609030f03050a0b01081803090a03120e04050402091305100f150b030601050d0b01090f0902 76
    0x1034500c05415014008800662544010701c0054000d1201141d04002c3d5590100c001d895880826400c01040e0f405500d2509100740c006016800720f840c04245515044180110024400c1c52809002040e800c590064a9001092002c1c03010941ea8840102d06540c080022184d8a050080202911003250707003014a8500950004001c1180511040001078401a40610000c0d0043c0d40c21a480002901c512940c000c000c1300649000d00b0000e0b0b85061603040304101c0901203160390184080d031b07503681c03840c02500e0318a401c4d18002040900000c0c1048800c1c809050340d0341aa10599203020069000100815103642064515040c1017800780980364101c0b201e814805000d443c2400980b806800250894400801b49210105140c12010401c201070041001b600b032000e00070040b02480c001c560005040050203c41034110440c00895580950300c1500d100c0c60050359601c0c5005081c809000240c4020007086043c00700003007001c42c5030b1521080c144082c0203440401610f91115600b200381024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 22648270 1250 22647020 22647049
    0xc0d0e0307050d081204020d08300c0d02070203031b1c08010b07080702040e0d0c020909060402031f11030403030504060c1404170c06210106021f0507020a060e0c 71
    0x440c508490f00064035103041e900b0203c2d452007004940e503540e0003c100c0c0301d42c01c40b200506c1d82c080052a21400600000707a0540e0030544501c0d00e840c140694151030f0602d000780c822916a40c0180000351170b400b0690000c004080c40036068a003841c50480010109214003002d8034000d4204999005110ba0740860300c14003111946451101ca500d08031404280b48210300014007210f10020f603450070340d101d68005d0072000c0e040100300c1c2c5104500100c010201c00c50010300301d10904984020507050304001585a02480c0c00a0280c00700100b0f040d00f031140d480c1c8000c401103009440b00104150405003078080c612540c0aa1000f00c2d10345003500c0c0080407211103407445401e000c50500c40039141c01d4514241d5003502c120745201903890403d00140e03460702036040b100030750062001076406041428880b02c40c0c20462202c9254803a6600c80105036110b040c0030b9585c42032074011000341000312038a40c001d55081480e80c0140d81060700e0036194071341a034452071a04070041e4400c04403403090742001c0c482e28a0b6070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 22649520 1250 22648270 22648279
    0xd050106021b0a05012006090606120304050306010501050705100504030215061e0103020d02040519061403010b07060207020607060903020a031803030503040b0903090a03060b01121b11030c0d0e030705 88
    0x49104000203070000314140503450400c2040664488408500280035540f03d440c5c0040347c00e41d152800c0d87d19611903046416034001d06404521041c909130001c1518140e4000801410a607030030400110748a420080d819549032082107000501c0d400781744106030281c3e0003507000d018080c5408189261110001c0c000c2c501588004051a013815192484170940c044240b03805a684e501548601c1d001c2e000f00e03001684d010709124440035a440302e64a1001c100c46683d100c405c401e200703082c45045940024454a8000c6c08108051400600380e9030041c080701b4402403419007014000c1c0c8a80e07049401522003140540d003c291188207264121480124442005100000b51170030f41d64014101e0102800c0100152030000100c0c020440510564100c008040e004a00d440c2da2414408007401c84014401e000c43c5a078070b2021101004d50140103124070326801681c084108880c01194620110103103079965000c103002c0c1c2c2040c58400e0008400102490351f4502100303007a0001c040c14000c0c50f80c000e5104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 22650770 1250 22649520 22649563
    0x31506070506040609020406092406020606090112030210020a050c06101404050901090209070c060c050708070f020114040b070507050603072c060307030608010e010b0306060d0303110d05010602 85
    0x40c40002c0707503a481a80202c010500c0880e0f44013181c040c20454208003a03d030b080255040310000c2c52000c1b01c200c2c141c8074161f500010760b92142662103901c00d031082034200c0c1c0300c1c000501c81c00407550281607506200e481119017401101882400303d030030012135480000ea0000d040c8044030010403442c3d40007184200c0741c501080c507150610b003043d0b080ca80903074040c80c0c803000007408802c2c0a5202c040c91903006000310000745000400103029400c014030884520749004070744c040203072064003592080c5900450151a100c941e0f11607040800950034102c0c1013009101c1e24100f064008030152005008803034960383c88446034640315080c9101c40d04042d000707031030a1041041841d8440d68062a001401d88810b0800740b105204a0401148141d82900440c0000034010615890b038020400c44403602e0082081c40c6445603298260380300f101c1110750540c03040e0040380151400304160302c01c1c2403203814002007a0001d1050188960030120300b040e000741e514401004895014060707894051410204640c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 22652020 1250 22650770 22650773
    0xf0a020c04060b09150403060e030304030206091605090408090a171b0a0b0901020f030307090509090307030c1202010b0d050102030403030507050412200301090b100b04060210050405070302060f03150607 89
    0x458007880e819244617101d02c0240ca15255081002c071000b0b907411903410700030036506007403560b9268000e45003103005100d004001468a003010407000303d0300354003001200c8024540000c102c0c070541d0150064989013000c004600076a40c607411000c00a007001d690040c0391002c0455540c1c1040d05d403041010703003003075039003602d000c6940c0f03003541e94040d2444010015180c00d0b0010040745400c141d006091914070000080c03143c1e0076080359000d0200d0f501110414455507640b00040d88034068601c000303020503c900d06074400035035201407668000001d480000361440c1c01c9030010701c02030842c0c00240ca0507513002003403009069141c01a0340c0d12501904003249028a40380c40e03c0c0301a1800d075070243c81c00d880d03008000322000420034820030302d602c024000e00100308941001c0c244030301b081ea4142155290b01e6070009400311880142e904644042d0080e00404c7c0d0320001e500090440100200c62030b008010004c00165592030180c11551060346070607840f45000c0038a403000c10745858040b8458030b4244030400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 22653270 1250 22652020 22652039
    0xc0c16030611250609021008090712080d0902011e050403050d080106170a02090d050c0102010f05101a0717030a050703020f0901050a11070803070302120702030c010c050703080f0a020c0406 83
    0x103990b40100894209618071a0601c1802040c0d205d00c029032002225035241b04150f13000040a0180c11000c090340d61440da242c0760902940d5082c20010010701d42442150343e24034090b881120842c0c018100341500c880400103007880c41c401c1c2c001c00000300d0710206050091010400041481c2416404c0010729541000d4000c4c0000b80062070a2000b60031500c00034641c1900d64041d110140b00c081d100198250341458851345a0b004004270500541c68010180001c00c0036000d01ea0040448c8601079440c80d0900e0406c1c0c0103081c4035090560140001c0004d100040c0308880e00e911019101d500b0f442e00d0b03040881800042d48e40252903403040500510894241c916120104d803140c18090a2240d5504480d081c10785202114a850300140c0c05100740004041d4004002049194403940c20766180e0b1104410501450041800c0603405910203030050341e142d4082d0602c070707a0940c0224111803d595407035445c0b842c154003005011080440c0403400902440d010002c0c000c0c4800229000e0006900f13008150 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 22654520 1250 22653270 22653307
    0x6010308090d0503040f0b09030105060a0302090a0f06080312060109080f0303150d0212071e0b09010c1419030801050d110105030604020702190501090b0a090902030c0c16030611 78
    0x54441d1205003450401c0103001c004840c011b094009801011586d00c0e030300020700d43c1100d0003442c001d5090200040c024039203010f1500c2a02e13401090300c05180c80f40c4c0c44c0d0f240240800442d145c80180d41d2040400c0002040016007014501c410600303400b8940000010100160303540952029030191048515084011040e40c0c3d0091255031078504d081c4041000440d001682c210294010b8810345401245001c0421898161881d0400105075001940000b030004003552060540540c030609c0661929131140c500080c03018001c0e101104058125054203003401145054465403c0d01c8600c44410140c102800c1d5005250845588810f0380d250384940082d0541c4c0b80f03501d4100040000041c60a6035a54152500550003901c52801c08441c1001806d501205025407404150a00b00000340d4440180403036910000a56410001c5442d1040c0790001c0d4001410f400d503071050034420b2068035601008021401602e518010402e40d00d581444002c44948403d060440c91003009159001d00c90304155 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 22655770 1250 22654520 22654537
    0xa03030c08071a04060504060b01050c0705060d060e01170c09040803070804170a090f0f03080a0f030207020907030c180609050d0c15020d031a150304140303012606010308 75
    0x32140c0d250410714154207406a0ba03c1141407501010090000780101a406581b00701e109807810840401c00c07100548090086490036103855000400c14420360800401408200d0000c003004200a512483c0302015950240c1140584d44158015900e000d8800c100e0b6204070702d02600d010025040907120030400d440010247c0c0140705002c00441e003000100011000f06410812445440b40950b181c0181030055503c00c1c1d0303400c02c040090105031130201d08040c0d81102e601034181e0740740c1200384074243c0f65620640b0000d400d01d079081c040d0340d0258540c0e070a000c0c0f040c0c43e540e60000341076401c0320010340349003a40c6100250b0946544010b000c4160000e33210310954204aa00907110600b900c0c0c9800c01403040e4100c0104000c407441d00c4802d0a0700002e03070920110698030144100140724280c0c1c9540b8003580d60041e405100c1084007104a03518a0007140c106001c1c8412904600c0d40200140c55a4000c0c1e220040002990b003448038404d0218842c070500602c104040c00a039495902e07244d1050240110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 22657020 1250 22655770 22655783
    0xa0311010c02032517060414070504020a09030302160b1812010e0109120819050901180308061c0803040b0c070c0807031401050f0a1e06090509010b0a03030c 69
    0x21020a580c1c0102000a0500c0d030050031940040d24000c01409208141400700060812182c40070808805141244c8980c9501c3c20040440d5550f42d160b1320700400e8010700000700c0b4010020041515142d40c0010601a1259113400402e6480c500c2c5c003c0c54840e8901d090102841100d40c1808680914021513940c1c000400022501c0c00d03512002607400d20070100e0501096103802d0f040600030303006402c6030032198020b501702900b146011100b0b655011040700d450201c01901c00c0300ca901c0c10303000d81c0181c2e0840e0384e00c400000c01a10030918211084c40000d01580425001001c000c20340c500203d483c2500081c44501c42040c046954070a6103c1c04090070042009041500242d509130102d030640d4401504180340724541580c0e0000c030303605d0f014540000c1d1111441000c420305040014041c0b20f01078002019203070032540e80c00d0301c01c00040151658103506400550b0304248818451700501c0b0213003000010002c0d203410b1403e4000d00f11101188000e00421041000300701203504a801e0102c803582145 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 22658270 1250 22657020 22657043
    0x7110f060d0501170d02061e04030509101106090304050d020d021c060b041b020a020d0221100609050103030203070605040c1809050609010e0d03020c010e0607050a08010e060a03 78
    0x540940914000c41d803220346040000107044507402070251281a008058500c546039a80040781c5514040780e4500b0f50003049004c610344100c0b50303c44540e01034040e1401300e080c10803810010b56005e40c03422001000400c0c182c20108008010300c41190012442d10066190074605808542c80d004040d6020303106014000c00d01c0d065454500a105480880d451645481880f0f0315001006020200c0b04a00841c40c1c4003181400030141079488640c0300319500101003c413290341c01c100d02202000401c0ba00b0154100600e490310a15410151034051030360080e0400c40002075112f4115541caa102c400014240801040032907000300407911115002440401c880c3e44070300300320304580529807204100e0100850342d60008001c0d6804615131a1040c41a50380d1903c0f02a040c0d8203855002c030078240c0b9500220050b102480c0298020b00ea42c14050340003042003c000e4103028200042140c2001c042600002c0500e41d0b04d50046849015040e0310a000c0c1c42d909024010941c0c094003400700500004c00c0b00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 22659520 1250 22658270 22658299
    0x2030a020d08060a0f12150209090105040209030a080a030c020f030f0915040b0d05041109010608070e01090e090303060306010b03010e0408070302011506050d0e0102280c080c01020a0e0301020711 86
    0x13208200b01902540b0120f0700150340d6200316404c4183c0c5910103880810704041041040074090080329000180140000d00590820041200a44c0540c107110340c503100343c0c81d03100001280c040240c11a003040f903d000803050313649400a41040c0c1506a4039a858004000503c1e040000740140c2c0c0c5508001d85491006207150a42c1c0c156510032500400b0108402188000682c0c802e90007052007584901e420b103210708040c005004010fa001e02580c0301081950001501c0a03214855400d03402505140001e4800d664070040c80b003402c0150796228645e04008100a40e42c1410000d50340100360340d120071b034034540c0f5043c0065804000540000c2030b0b014001000c005241c400d400520340c0720344440910300090f0740da00c00503086920000c0d8181c0180c3c00c02540d07041000061099440801c00f4a194070043c40000741111200c41101d02c400d418001044140710118951102405191001314001a6134501c841c601601400402680714030a03030042011400080d000001c00c000301c4016140442e1150b0203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 22660770 1250 22659520 22659529
    0xa080d051b0415030605010e010206010918020604030b0402010305060102030703090302090406020c10090201020d11070306022d0a030510120222020c03090414010b120402150a030510050102030a020d0806 89
    0x24507401e04501404078001c150036040000e164005151501e0820660b42e8a00054966503060400740740035070807020042101c5041a00143c51b041c249040480c01c414450307000560b035070400d07081078800c8401c0804000031543c0610880350401005d000540c24004940d41c0100449c4c01404000d010300c245901180404c5a0f94055842281c205415918041d1040c1200c0c0020a204141a07005100e029080140907002e00d960350070646070400505100760031612004046c1d0302c45c1001c0d144402c66a1010f010086045030500c1d0030707000380c4042035075965946900600381c03140030742100081000d44000700104600c074410084011360640d811400c0304041c8444442458504001641083c00003402d40048400800100300b2040c0881d02008145da000d083e010070400240229180d5180c00c000c4200b00704403403450f40340d01c00d1000302140c2c1c2c01d07034010003011026000182c03080082031310340e020b0107840d10390b8045102c040c0100384004d600b08903440310000c1d0381d419094041028400c2c0d840124001e41c59 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 22661876 1106 22660770 22660801
    0xb03070203090d020609040c0801060909020f030708040f020301180203060903030f0402060c0a020d0f02040506031f0903030e0d050a0210020f04060f020a0f05010e0706020a080d05 79
    0x40002c00e1100c8000600400d0b81d0150003409035603e1580c5d1401900d14070801955015040e514010000e4281d40d4507030040030305507005003c000400c3d0070840507070783c0c814020700e82a144c503225400c00344421800d01402941550812008035030705800a00d4170f50409200f0f03411140306980308044240c48c0d000c15200000342e006044003007409850700784044d1506511490a603034190f2010f600140b0b05444110049401190701341004c41945014810342c0d034055403d8000c0e150007544110710f5098403201c4d00c00400500d50340d489030401e041c4a903008180f06220a4200c032160700120710050004e070403511a900041c41680400003440c0418000c0e111500a060b405900382805c1c03480545a0050000d00c1008510900c0400c90200721403144114109004100000300d9010141000c0d06061881d0814015940a14103140000b24a002160f414090607040040e030f540740c54000104548 = true := by decide +kernel

theorem cover : BRFrame.Cov 22482020 22661876 := by
  have h0 := BRFrame.cov_init 22482020
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22482020 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 22482020 ≤ n) (h2 : n < 22661876) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
