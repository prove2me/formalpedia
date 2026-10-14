-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0879
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:23:58.826594+00:00
-- url     : https://prove2.me/submissions/b32cef39-5e8f-4803-b2d0-6a4adfee595e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 157913669 ≤ n < 158093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 157914919 1250 157913669 157913681
    0x15060417120f1c0209100206060102010c050f0d0f110c06100f0506090402031b210a020a0e0d06090204140717010e13050c03010c02060106090816050d020f031f0e01 72
    0x8210700420052403440f80d40701c145024035807802d03c1015081040c2c1400140410422895610050f404101000382e00d6a09002d403410520700c1c0e0400d68604035091080c241030344250100f464049071a80d00562005141d680003e40070510f0044035502d0f0094000043c1d1900c0b025510801102004000840c920703002c500203000711103004200c03a183c00c0001051202039040100780103d8413001e001128800c610b1200100300100d900300842050402a414502d401d44024202d3b02c1c2d4a80f05024a1003900e41164031b400752800212a0503506102c145040c1c2c0182004d01c2c002504942490340d1200c0d840000c1038940d0041410b604c03113000c0300001e04005d00e00524244294003038020260045640b0107640800301041c5c60049013690103422201d40405e0a49481c2600040103078003500042208541c8952000c000c0c0842102402200e82081500c0480c0c0e4501d0050520030340c0c05040000c00c56a8070200b0000808015050b00d61000400f160a0344000e400024001c500c3d080c1300c002981444d0601c224 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 157916169 1250 157914919 157914937
    0x305060c03090a0201080403021608030307030c1d0108042112060b0a0207030201030c03020c030c070617100b0d0e0d0e0f0402090a0e090f250603051e1506041712 71
    0x1400c55003c5078004545280f00900142c003580544003000b114222001c20520240801d40019992410b0040004040341c0d4030030f49100070400c4010707070f1400c59a1018807a00d08030303a0918103110151124145040c1b2401000c0e04285240260341b2140c01031a00030340c1240d0500c3c1d002c1c0040000560716000c01103d032140040e05401030b0404001400158005d03402001140e1091800500307059036000c0c100e146901408140031142d01100040006603400104a0148450080000c0c5e00d400c01021a1040b1041c40c051040e82d04800b04102e206181103901124521340c004003100d04040780c0e414060080007108004c0c078040d6420605041260800d0700848050355005000d200c0f845103007100740d074002400a03040b80198041c0c91045464404200300307182401c08402010150029280e11380340400b030441d840601410f05110411291001c0032a100341d920101102460595030740e145080c000604d844401a8043c030302180c00714403a01e0070388955840c034811408070340c641c001800000010303000f03000f14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 157917419 1250 157916169 157916173
    0x10f0806040320030c030c070b09100f0c020a0e060111011b0e0a050604060f2c060a0927060806011a0a030e07091a0904080a030b01021f060305060c0309 67
    0xc180001c0c49480c00000b0785400c2c3c040e101c07500d00441040c0342141c2c003500034a0300a6101147c1c0542c180828801e4900800340d10308100d00e80142200070807900728440403104140041c50a03040d910601519600c2100c41d070003080c44a55948500300c003021403000f9104180090112031241881400512445590111000301131140c0c02041004032a1080c0207204250003071b501544c0000c0e03903203845010380043e04072501c0c0c040030b008090000919100c00540d41c00200502030000b00242c41d400d800324801d000090f03ea05682e00e2011100303032f0f0000c0156001250507248071600d01158442d40c16140002080144240700041e0340320700160b03940c9001c0c090b0300c50004c038030002d00820242c01001481a01039500740440c51841003007440e400c2640d168804009141c40c1c124250310301c0c29040c0303900000b000840d801032042c02c0c0741d180d5151078010002c40400303150340c1b40402040e985c001c201656403003500f103000000c4d070450098030300b010300003a11017240c0d5407288601090f00c0d91f4441c804d892042a031040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 157918669 1250 157917419 157917421
    0x806070201050c16170301080105071103040608010302040f02120c1b0120070f0606080a060f29030712061d1504020d080415090618030305070204050601110609060f010f0806 76
    0x8190a001c25815030111441d00b418010215081702100c0507500030302c0c400000140a20f4403000242c424506a000507106400c20001880300503080b007102415a0303016100012031f003000c41d010b10028440c6ca0340d4414515000410000401c1c19400280f54120386160030007c2d00c6105040c00d401d03100203045550440280c0704241a0340320a290280042d45e0080ca0805410261929068211030340c0350400f440342e401420252061140e5801000750a070b8040404002e03121422210070211081c1001813004800c1c0c000c15101565400c020b503a0180030310907501a142d100b60701d8280020461045016a10b0701c40280c46003162380c0104002050350070351164108555101c0e0b0801907207003080719044803404000d1002041400134034015845040c826250b1020050510303a01030072455014001c0c82c54940c1d021024800694010207807903401754107032404583d40d241d071001a180320b90040c0d10440e041c45402c08021001000040a60192190b49001c040c203980316146286014600c0c0110003055020328 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 157919919 1250 157918669 157918687
    0xb010602010605040614060c0c060a0e150406021b0102030408010c0203120903030403090e0903210703050a06081f0f0903080f0105040b0d08070f0c0f09050a090c031202190c0806070201050c 83
    0x400401c150510781c02503800c9c0c03050000018240d41c0110900d40c001894100713103000141412100320400c9182c818295081c0b0b8900350000795074810148032440c5581010007028070303903402001030350060300c400030090040300501c0600a55035088054a014020314a201190001c1d47c00b00c1101e00580d013540c0c0d5100c1301e90a00d403081c00c1c501c038050030005440c0300c108501c0119003503418101202110001f096800e80c105004010f06540f00544031407042ca24080c02000030903000940d01d9240c080d201060f15001c1152a2420020003052035005805411300b5011030030103500480e5a4450301105000102c50307601c54081c00101c0781ca0000d9240c0003100c1164540100700d0003806006902d215000c1d4400301c520301c0e07482e031204698641c1303c420190a00c80301032155404900a540e844051003a081001d0356043e248c40014018921001e0004500c6255041c4135510901041031780c1c0010501c107a109408620b496820445c0c21301c2a030815001e8034011582c42841805400d00500c288200c013800c8c08468 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 157921169 1250 157919919 157919929
    0x7140303040e1b0d0903020f0721060f020d020c0708120a0804020409020d050606040b031606050c2a0f0904020a0e0601020304180501060206132f0d0b010602010605040614 75
    0x98500f01d482c40c0440c5105010210b02001050107884070380300401c1404107880d0191600801200007605a0051241401481c00811150400a030300f04410518007000d42001030040c0004140c6900c1c560000500707003503070300e100d030018140030740c0c65800c03181d145555504098a603513040a5004440404009840c152427191403036a0300540002c0000414207540e900080503c041c0e0501182c0580003103040081e54035041c80340d410a803e0a9002e071510741d07101e18113413054503201c0c0601000d00a02045100e03030081c0401292034140490315400008401c400e4180c01d01d0501e0070317090380c0300e040d12500030040350030244000b6010310341c0a400002640e003008050020034000810300380c11844140310004060304004803000c9a40a10700740012079504212009041c60341c003c210140040e500340c01d41340000e486640d61484480c203401d400003a91100c01691704c100b514060541e600c40c0321015240309000460610504854141d00200441940c0320f05000503034490340f040d42d084038005212521a4102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 157922419 1250 157921169 157921171
    0x112230c070c09050604022724031f031e051204051e01051303140706030c0f030207052b030b0901060f0305090c040504080d0b04021804090309030b011707140303040e 73
    0x42016007040f082d1810740c1074405203a840c24110400d410408601424a54100c245503214041140044014500009018070010b0031800302e080c800c507962501c000b5005584bc015640c002c001000009010b8038a42040804201c240d4942c01012907110300045400c046030212200900580310114140000c0c0441044c0c01c00e125050107020442e5540107020608040050f5226619502400c0d00b0200450703c0d2040a03084103042c036207499011010650060fa040c0300c1d41ea0a0715000d40d48030814508070741000304801039042c01c1100b580c0358840031240d0141400781041e5a80c0d0070004c5040350801c00150f620b0a1181401161502400c00c02440c440d4114a46c8650319004841114480b040464212802103405036240c1c28041500905200680a01d003a2607000301d406608249907100d00b56002603194a4507031155550343d000108160060540c08001c0d9046010b0300d50940c0d55400a20206910f40e801c90228019900e0214410110101c031007290303480a002541040e0802e80c0c0d00d150100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 157923669 1250 157922419 157922431
    0x201080c07020d0503041203030e010504022b0f0809030105090a0b180705191503050601120515040e010222030c03060c1101110703080f130305090112230c070c0905 72
    0xa40c0160000411350401c0100b00074180b4103e06d01d45401581802422205c9290440c0c203540d0401c410701c0302581d101c031500120421054103841c091401d480d8415440f07041d07020f0083c00071144d0340c44c107800d01002d01d02800300c5d250150000d00241e900c2c41d03a059151469050000d01011181010035841007645040c0c0480d000170300c00b00d555090701c1e1800038400b05090b0141c1b0a1815824000740603031800c1c101c82c02d02c514401c0c141480036080942c0060052010100042c5110341c2e2803000404010880c200d0360b207880b80203070007000024a4103800501035408010110500c04d07040d402d82850903000c907c1ea100301d82d0880c500c5a042801c503036540c80a030802401041c03c01c55203020b00d541000d1300707100d580440c403c070408540e50340301c032440c0291518000034948001e03800c40340108140321003013148014040740d252402c50350303400c0450700682c0d5440d9080000c150700ca02d8a10702101c4100d10301925190410b40000a1f003041d0b58000741c050840c82040802401d8021803201001180d11641009401c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 157924919 1250 157923669 157923679
    0xa03030f06050405010e011502070803031605091c02150f090909010e0709200301062111071406130c21020d0809040b01020106060e1908030f120609040201080c0702 72
    0x255a41c40003c050710703000e8000175465501c0e0b4004018880c40000880049a00c5001404640c0d20346800340b600e07800300404102068907a90192542d80f482501124000301000344503a0b11a6565410340c81c0644880c84100d001c2c0200f081400c0e0180140402c1e10602c3d042a003200d03152100c60414080b0082003d0700240721592070b4140b01a0034034040c44503101504000c8030004038929516046040c0701c12031942002c800301c0801c014000c07160f200b4000b10038202142c0301c200002481c030324484010650a41d90304500030000c104e940c01c0040319401c503c12602114100c803519100d03d03035050a17040d4030460003045e42d072000300f080001c0c8003102c0c0302c00c80400540b00c000c440b202c890380200380034401110085a21001c001003106203840c152059401214081c4000c101590130088003500031541a44902e01c0b4604100080400106241d8280c010700709000540c1e8440302c0c06070340f000d0b198010342c24001e01200e100e800500142800d0311010710440c1c05075240c04044d12550030460030b41d40310b101c0903a000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 157926169 1250 157924919 157924931
    0x90c040b03030a051b011107120c0305030103080304050c10030b09090c06071401060b070303020903061506030a0b0d02030312061005091c030c050f0f0c03030309120307020f0609010606110d020a03030f 88
    0x10701001c2c407c0071b1b18080d0300e90b0416a517242030300d46400300005000e00e075001e2041958510f0b0119a110050b6410350750720556041c0c0d00c2c1c0301c07420300b249081c41c018292644a4162020000b0f001c0c0d142e0418400244103650a135200e48401c0c44c0c02d616041010940e82d080710042c0088004106401c0404540c1d81507d000003408a442e60900b1601e0390012105501090300020711068504003084201e80c0305c80446409650800800300260380382c807010300030501c01622004540c006075103c502810180e036008044964940d483e078180c008155085413002d100782c51800700d40006600600442d991000001c014a010070007400a46843c000e89610a07000c118440d080c19000034403c024800303d107400760307009000f915140c41c02c1e1071400081c0d041c0c10340260802e2060010499001420611240081ca509620384d603075031504070324060614501021a110b04018003500e0801944100300380c909950300d44e1504a03942e0f00c41a0786402444a0f100141d04c01c0c5425804a4426031201c045004074000c0032402e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 157927419 1250 157926169 157926217
    0x207020105161a1806151810030506010b030c0409090c05041d0709021312030e0d0c060e1012091506030605090d030903091413060e090c040b03030a05 66
    0x1074082c0c4002d0031981205004024251045480b1a80d50b01c00701d08100300290040c11000c45895400103001300d0000b040719060b64600360b440045895003010064104045450b1003034009850300d0252105031454021240042403031071a04085900c6605010502458145040e454400504102e1015280c1111103800800c2035074443c0140844c02e050070303007070100380041104c40c1130904a00d0780c0602d02c1e0b07034810010704401c04a01100201142d244c4041041c42000c64201540c0348010b080c2c0d41c40e882821041c28004001c00300c2c410030192010782c0e640e504690a43c505008040b024070386400d000c01d0311660001445106a04031061041c4103108005581c01000500c01c1030700c8694004503003540d141e40802c00f02c80410040c3c183e100c101454180542c2c0180e8030040e0141070980a54521848103a0801d041900d4003445c843c1c0184100f4400c10000380e0301d5400384030981c0b050394902c4039401400c0489070716150078000d601d07500c000280518544000c401041d140e5500442040c0200240304905000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 157928669 1250 157927419 157927447
    0x2007090501090b0901090623040603060e060403030b010206010302012708010c110114040c030803090a05070909051e190f0b070801060816020604020621010611011d0a02040207020105 80
    0x4002c1054002c0455480c104908110203150144c10103a1550700e00f500c03c100809640e000348800ca010f0348009880c501100c008103020341420340004d000107040081420a040c00061521301c2103009990400001c16240d004a071200340c284000fa00040c00c8240000d918081c13041782c0b420085030070075001d040b81d03610280c040c00d58407000c80c00000310f1a50004803094440a0043d851240e83c1b80e24882458034103030b924001c0b40b40b41404003412104002c0001800c01400f0403210043c10b4100048600307495507151101c0c090700b0b424104994a00a84c2250855510f000016035000300c0000041c1600c1c5100d24060b8111100081003a51200030b203282e64008124002c0b540c42c01803201d1b80e00c0140710342c10441c0c043c3c04c1da40081c02c2998182401100c840081da400f0840e15005603045520741c1da81c030800400c1501e840c444401480c003440580000196a80d00020781d03000000180000f0710503080c0d9445c68904c070043c6499810515040300546600500e480e0b8020200c04d4414103100d0b05001003062080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 157929919 1250 157928669 157928671
    0x15010314010b220315050c160807121701051002030906030103050601060306080a05150a090812041707050a0b0c070506070207060e040504020f190b0c1c0201050720070905 75
    0x1031208100001e11030b00c1e000c2d00c200000040a0851044000240b5640c2c1728051806240703070680000707544101086031902144103da40c0701c00b44000082d02d01c1e4041c14503881c1588120001c440d0701000c411403a601c68040d00b0a545116207500e00d0903090380c40d003000c0c820650f840c100034004500040004244a94074a000345002c0c502a2001307045a6040c54000b070200c1c1c0280d0007452641c1d01000c01c1000186001071500010b030b5030102e242c45161100e1040901030401b6800041140c0004101817200640030000c96116034002c51025803041d1041400301102d1040c0f0750003800c0c5400001a410101384000071140d003207480d144403540380c40a192070301c5080030b07016a141c400503004441c0030495a0b5120709000e0380c40008940070440303414a0303800103250041040c0c1190080c0407041da10035000380c084203404000c2035040205561180c03070304082502c4040404000b840c044288020341001441407144520841042c0c45006030940b030304410942c01c240135003604030035204842000c641074900740505 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 157931169 1250 157929919 157929929
    0x102070606031103030304050a120504090204120203070f05100e03030c030c060103030e03030307080106030f0e01021804050f0f010b160c14010f020c010801061103120103030512070e091501031401 86
    0x1211800c500c3c2000840e24207110180c842e81c410320902001c10000318031101a82d41c0040c003074482e2a441d100565941c040c66000317202c040e2021400041380075507a40400c1d58140308809642134240c8030703c5e41c180d031000740d03004d041e40120000743d0360800b049c01803003142e01d812002000c40e418102000ca1041c03440e0f0040d00180d501340c2041004008040d008014080c1d0544210091402e40c90304000040c1914014400c0400701500c41140c10010690755020030b0310035221000079595001645003030f1000d40c200c0c0704038900507403400c00002c1c0701030144452940a240b580580c0441a40b030070000b2252500300c80303501208103000b034180f0000241852521b000900000408490401c910400900400081644241550800242c40070182c0c0e020800a055036043d0a110141c040c3c0071204030b01d140202919075581505d064004028543c109000d4040c60080c114080c00c02e82d40ca4034100c1d01403c3c4141415003100840b00030603041307140520b50b0440c41c10306140000350000041280c41d41c019003a801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 157932419 1250 157931169 157931171
    0x504170d0f02040f150309020d06050c070b01290408030d091403040e190b011709010e06100906050105070c030602091804140c030106050604090f0e1b09160e0d08040801020706 77
    0x1041005568000c900203814051341010400c0c7d03145500812004400024028041c503920b40c0010502c20b0300c0820b0f15200b40c0c00090200d191360b110200400f000c51517000c030555505c0c5541030802c000c00404d080350152030380034005d90b00780180112510064425080112601c1c24a66400902e070700c000c00c041c1c07009220344203c0c02d02d54144481d00d003c21101881c00318184d10b003042001142a41c01030b50005441304410130303005442d6100301c41c0d2801000d400054a1b410f0240b1420301000103500c11140050310040b14082008659910055404c6c4c494110010403146410398100040360b2554040c0801c8003018021855040d402402007945502c01c0303a0881d05040805550b8030206420080900740070001e5008000803070400d40095828055440341001081d1201d61000300a032036600410080058041100c4204205401c4002040064a0142c1c05640f10800042403001500c025444a8041e61514013882141005000c0c90100c514020345082c0000c100018403000248000c3c043c46000d504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 157933669 1250 157932419 157932449
    0x307150209030a0f2f091501020f0109050c0906030105010f0b0711060a0507060506121009020301150612050709140d0309030209070509041b0203030c070c0807180f0504170d0f0204 79
    0x4480c1502e034490403980041780b4800c182c03403211a2540e100762034011182d580c91641c150700b070100403454680e10004010181d4200401c01042040020702d45440c0d50b01141da1071b60311b82d949400c2c1401c0300c0c42449030b0740305944602c00400c00704500000500c802030040e1041254091303207602050040d03001d00c5003803000490001321031040c411140328140c0c0016084411170403c2c80903081e01c2ea518098803403256042c0382d659515100312341c1d0951003545180b02c003070066505543c1d25000035042c000ca90b01107500c0c5074204800105002c3c85506150240d80c840d00032080042c911200f03000c0d04c4450701d0012818005041400320140e564186c5540c40b511003030380e80c90f80d50200c0300140015203100000c008088800c441c0c85280741c45c2c01000b900c3c0e0024242c40e04c55161151410074a115003c01e62059485005624011500c850904810a0f0880303004c1d00500032188000715034802c8400841c0c015102480346240840c2a40e4003a000b0718103480021000304020800c003418600b00da001d81d1000d46035038280780d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 157934919 1250 157933669 157933703
    0x12040c090e0c010503010501030b180f010608130c03150f1407022404060e1509010506091509010e07031518060522020319050a0b0906030307150209030a0f 68
    0x1014015540ca6110080c2042c1c6800c0d00001c1c1031400103014603414140c88402d51403042c0c84100e901c4200305001e11801c0c129040468019800c07500038040d00c80090313400000110001c0703054900600c00d542c07110040c08103d02c0e680715205c144800110304503030300e9201c110400009201e40221041c3d91040f00e92501242086400607181c2008114800e84115980b4070702d120f03940e000060240d100303401c4200401c0040074052400c0c01d28011301c01c0555041054418002c0195055020764030070b000517074540d032139030701c64824200508031030200c466401841e20f0700500581030718059540e040314070f608021840207500c002e05034110311140c20448010905008080401d00b250040a006003010b460041c40b0080d66030402c01315841c00004441010f800102081200d60b0041111548106400d13040200d81014964003015141c00c03822700303104944000104000e4078020048419241d405658600541d60501070000070350032020046502d401400074600108007001d03000260140b1821941c4001c544c03d0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 157936169 1250 157934919 157934921
    0x90105180d17040309050a0303020615040e0606010e03010e150a1d030a03020c0709060b030f010806130f02030c06070b0702070b090a06031a04060f0602070e070807080c12040c09 78
    0x881109540010030652005411915140b040d400d000d41c0281c041ea41c84c1401e4858000710360105801001400002060640c041915401400d201090359440d14010040009a0b11440d55003003c9400100c08a4012340c0203c98100e603013500a07002094400300201e03201d05140036248001f07151034007071082051900c41d52069603981002c402e052052006660703a10359582c050b47c05a0420305038001a02500c0180800c4810002c145901d0b0612603561280c81da851203800a460540301400c0707040001c54445008941c0a124a000102080c035682440d1109691404403031410381c0c0502842400c40c803582c03603c01c000c0030b03540c2c0920240d002d203003444c1d03400a04d0314520742e0045034111014812030b1069554103510ba0115400c0c2d141c045511280c0740300a8050f802e0300360345d40740d005103003980015407448006146011101e2a400340c03102280d84001c047c00104003218400c0000b491034002581c910302075105c00350004410b14046042c020707960a01c86007180280c901303131007041946600300040700c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 157937419 1250 157936169 157936201
    0x91204050d02012c0909161206110414121b010311040306060b0a1b12050a05120103050106180203040f02090907080604030504210507060e03010e100c020c2e05090405090105 76
    0x201c5801051f50041005c039000c62052140034124041c54005d1320503040c4080d94210101e12280c1c0d09666958680d030301c180b40041481008094002e03585443d01c800f400310003150003040060700034905035415200c50011401070006061803845214140004004690980300c2c06015010080b1403030b90322140620040d000d916040240c0c028044000d007408006801c1d6410303c0303608519401c01c030752541180c0324199018054a04450321511a4034000002d00c0745c1500202c04032550142c1218801c2c1d82100c490040e84001c0301c000d0708220943d020780b0010f04044403000ea02208a20030780712620f84829140e42014020384061340000e8000c1410b01000340c03d28044444415021403400070382011755101034403038040e803207048188661042482d00760f0b02c0030741040d01250014801c1c2c0e03160401780d940203c001e08100101c1001031140c0c0e0913100840c1007100b400b10700e0324101e94550318141c81010074500d10380d00c1c507c05501008024820035410340c4607802a00e000c2e10b0007000110b400d2420840414070307440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 157938669 1250 157937419 157937431
    0x50c01180b010b0307090315090b0f0406050a0b030712050102040e01140f010f020d0c02120d1205070c1502030703021209060402090f07050405150f0f0a0305091204050d02012c09 78
    0x300f0001e1000454000c0886c1e02125400211071b550001d500035a80000c290014015002c20740340c034104022074184080e00c42c0f156110f034801b000503440d0a0410350855803103d1859400d0b500c07032101800300a20380c00f0440900307485100050702d0141c4400c440100d1841c00c5c0d01003541c032030420540c2040b034070f410507a07444460001c0c60060303403d01d107895000752b589442c00000c4050102c40c0b8032a80c01e640390380c0c0d42100841702e10b1045801c1c103403a4000040800b0451360a040ca01803401000c23499452288540703592040c1c1012005c0303582000001860000d40c00070700746c881416400c1103d0349840008080070f620038403080d0050029442c10380180500401c00500c5407028000c01c038100300d440703a00901a00d003032322810340c0c1d41c42900d6071003248a00c262086d0303004600000390215692031a482c001009004d000525642404991201c68525544844104c2c01d500c20319410700c0140702504111666090703060051600f0302d10f04891907212a0420441c0300351040d0301a10302e0008145042602c0700390f4000c1c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 157939919 1250 157938669 157938689
    0xf0d061d010e0309060d38040605090f1b0c07060e100801031e0f05010905030406090b0306010804060e0309040c1e0c0c1a070506070e120102070506070e01050c01180b01 74
    0x8121000012103d101e80c00f50741446d42e65032001c4007122041c0500e43c5403014110301d02030a40e0b884030007404001210400240d4422803e00f140410039080603481d43d80100b2a90700e40800c50f499801e1904c10000c0e108000000c0d1990038021145c6460701003007010020301c40b58680c00b4902d1160b0041c001b100c0b030b40160400900900310010000903510304100c4240021032208250342c0249480c25110a110301c00b000b404a43c01c0542c1c5c2c3d018810080010411a51551565440c0d10365a00d40001540012100640450020800a0003013445900082c19070451031050301d20713000c01800047c04807961000007800185842e80d91010900012070419a00c2807141094210410715a82d001f0300c200560103008210708000d440807e081c0700117002d86140c1c540c40400e9811600e0074000c014004070381d10780c080e40724200745d00310a070030b0080c18400c8610762500301024060642d00c0c0310b401e5541021549440f41007200800041c130807810203106007174100801c008811040400317418103a0351144181c202188071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 157941169 1250 157939919 157939927
    0x1080a050f0a15050a090e190803040f0c0e0702010603030206010605040b0403021c0c090506030717030d150902040e0114010e01082805091c0207060c020f0d061d010e03 74
    0x410901c110a40d80a01070503004100f040d0300f140020002520b40d4000c60700241e0350600403c24085075085408400e100004a48548910380c044c8418050100009402d0036010030106020520040c00c2c5102c15000300d20020070140d5815440074011070490f003050041c0d566035070a204059041c01228010300592500f141014100b00070302c803261180d4031000f84564607905804560900c42c072000d5400641046080c501203a43d03521250103404c0841e0518400e005a040c0421000325850003401010801c40003903060907100c400c6a0000c02500301400e038114440034000400c00e002d40020409008400d1035200c65500d40000300c2500022070f134029040c402d041c400e0f4000351b40d1121100c1c3c4d005900c0c0c0c1c481e51600e016032001004030712108000c0352540c1d04080820000881c0005c0c0303c00c4001703202100c68045426418120b8551181e8015040015003103144030004d0328028000307140760310703005004801d04815650b4400494120030341007140c5408000032100416428441d091240624101035450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 157942419 1250 157941169 157941181
    0x2060910020d060b030103420504141e0106050d022d030d050a0806040501080c12120a020c01090608010e07030504030c06050423120702210d05070201080a05 69
    0x3034248030059004416408103140c0e10203146508540004e0124007905036485d40c5a0400075801101c1e03030303120800e00702c0004040e6011001c090f00e01403120380c02c040c07038032410394200b000d40301409010b001600c1c03401035401d08240e00a0b080c405810203003804603010714404c4401044134203651081c1c1c0140d1080e91001462009600c403103034848056030701c401d000e46514550044000380e125200440316018850407484110031600140209201c5030f0688800034140c0e03906d030801003607800902410284d0780200c10440d01d5400c185411900c6844a181910310b5141203d461074800c0d00001d81d00760041c0d101450036007035540c000d039002c0041c09031441c00714220340c148003540f02c12036030140020081641d1400007506045c41011010725665100da41882541030030308001c42c44807036070300c2100d54000d2a0f2905400100002032008082403140390385030f0a1150980801400d045900003440c00300d00540c14003030841606000b44188124180c980c6500c0300e03d036000040050350001e02a090080ca003070b0502070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 157943669 1250 157942419 157942423
    0xd09261207020a080609030a09140a0902030a06090906051501021b1005090904030e0306071b080703050f030405030315060405030c0d0821180307030503152716020609 73
    0x30841640c4184203988411a20100c0d20a8a580d0300c148405c1c000d02060000c041d40100040140a1160741d501551f944c460543c0310412400d405016404480349070200a5002c850f005503902c85800700c400211076994100013800e07621811310841e81503540d5000c000e50909940395152801c0000c2c80141400c505400c4100c440c024109075280c80364403400f8010181a1045085540c064800350000120341003030316018001c00221000c40d8800d0180100040c0014400e404600c1003041c9191014101d820740d80741d00650703621115090b4208102003040f54100c411100046015502c1000115924640305040d80d00401d1860100752080d10208420030259400203942c0d0794654045030380040b401550718049149115001400c419020f0350560340c5564550f01e000300307204140518440c180b4900d0102219283d2060444c01008035105002213810030389001c14a9001100203440780d00506081030810300b5600b440c3c6c00d00010721001108101500b1900e048080c07401d11140014040d070704282d00495 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 157944919 1250 157943669 157943683
    0x405040e0613170d0c08040b221e020d03090e06040b0609011b0c1203110d05120a020c070e070e0d0201050405010c02010e0d0b0105030d05030105010903120c050d0926 73
    0x1d48020b10009103091030404460031070f01c2419a086042017100c0203c0000b0306069012102511241610760000d00c5031940c000540a01984140100c100564203581e20b0744051a0b0b0b8901112051040d982d1f8801a141c009403070380f6042c0a82c61f10511a8503250759044c146400070259401182810740b001c040361514011380e4142d2109003400c114102040042c10000e052444000d041401e100c0e03000a0203003511002e01510714025500c1c2404c0003c0c107480e555685a001e070000000a00030040c5000800720106602d40100c084030000d490284010340b51481c108182d0089034680c050403040c419031540109413440031003015503140400e42c840d500040c00030b004a2240d90305100f403190602c0116032003000a821072a070010300d070700005034075030500d602080001d001d424007a1080303051410b007036030040c01928100c4a0507500c0d014254250b90764008000d86030088401480200031071a40000c00622901d9446030159644001180c9000c4220b48105100c901c1100c81402c0e09030074461400d0003103001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 157946169 1250 157944919 157944923
    0x303020706080c0d2409112505010e0d08090c01090608060609030a0609020f0904050705131b0804060b060403021c141002030a060e0105030c010807050d110405040e0613 74
    0x15010f0741d48401e0070700b240c81005258410a49894401c14000090740c0fa01822108080031004003d611203030341900300d072580c00c1c0c52070800b503040c01003502003500710340320014084000002c0c030044140d980e980c5d42551088078414900b40c22282540c1441d80c1e101c080705a004507100700030311400810100207400c3c0300b134a02540003001041c40000c0c4007504c1f0710048034000440501102d0460919007803c00040211a4040f88a034601e110503150b1850b0100074a406150420044c0001c1460142040b0707030720381c08a404404054844130b066410309221855a8400ca0080d00e1701a5a481e0070314000c0200c0341d80190562003000144400d00c0940c640d0b45109040d200c62150440c114100740c14900e00511b54080e40c0807603030bc0742c19007a91560708190007841c0500e03030000341406019102c5200004041c424010190035503c04010408198071685c010750700581c080c10564540b80294034203038143c0d003075410f008602540010381007003107043c24404c40b40d141c0040300150807603050802e14800b04240840700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 157947419 1250 157946169 157946177
    0x2f0f15060414071707111b030d08010e15030a061409070b03010b0d050c0f031003170301030210120f0e0706020f010203070203070813050405040606051c030806040c0e032b090303020706 81
    0x1764000c0d01501c641c00510040360200d694465513010070825842d02d45440070701901400c0c03692084035002d42d03192030580d0401030320401148d8a0000d270314241640582c041d641031040d01061004035510744912042c04415441a40c240d240100368280fa03d641c40c0e124560740081000100075507040802603a0420741c402c1d0b80400c49441d0b0150380c0c0f50500415079a61040c600010078084006061070700d0008407889034031405030391824244842514007007440007a4000781220024903440f40316403a131802e40380303038000009001c4012860640c116000c03052030300826844000d00f40590f41d0100102444000480004c2d4030f1407400f80402034036805107072802040864042803003000b001c0c4130a074990290102401c10040ca241c9070900d58041c00300340c07084034050000c2140000215014042d14803801307426444e13012582c1c80349011f200062080048404c100002d090020000d80c1e401e00089a0300d00200380281644c080820440c2044518100320741d06014401008000183e0003048000481c4c3c89807c4c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 157948669 1250 157947419 157947421
    0xc09040b070c0201050c01050703050609010b090619181502010b0a032612070206041205030f150a0308030c0a0906091a03071103070309060206072f0f150604140717 72
    0xf0042e03409004180440409500300410040c0c880d40c540d00043c4900c8040fa011101d41c0d907070b20000a1903100c1c001c03c0303980284007042006c000210501c0800c140d19954540996916828200840b1990440d00700c007401050b450065405940c5c24010303d0f02507a000c0300d200058520f0350b983c103da5031590014804410b2140010340307074403020000540d14102000c81119507103141412009403540001c96046442d0040d100014208511030b5054901c21101e00401c46104c0d2225052030002c12030043c484d03503110450041c0400000c908001840c0030f4848401d20580b16140300170050041c8070140c10410410042240400c031103901c281c00070707182c42d000d001030603943c0d151703400125905801405150b0003480000b8040007019484460842100d0b0182d00342d44085d00c40d64000c840744054902000d6240740040000c100005c0c01140c10604113060404075040b226500c4421410491078401200203200c60400b000b0850070180214201034141c100c2c80f00c4540382c046c0c0d002c0c121030010300c41d20030085a404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 157949919 1250 157948669 157948673
    0x1a0405011d0621100912050304030503060409021c0c0f0902160f0f0c150809030903030706110909040308042907031a031c030f0b0d2904140c09040b070c 67
    0x110244481034009400c0c0c0e0034030020782d00c00e5009002174820481d1400704a45008030158414010b0301d0041c1c1d41a0389040c03940d00e0345c0e0f041002501010703109a038084011f521340405d6070311102d00030010310b00c00c1241d07269203868107450038000103550380500b4015004004540e51102254190368900303a010500010444450410a401e00003105004010050f18000891b4481c89858a42c0140704141d4030780c01c2a0f9641d4030f25a0303da01580c000e0075056841400b010380060540e81104c52104505111030b4202402c0b240010105081902c003540410020014171082c0200039000303004802102200000303000400103c40002c1c1d10042c80748003050b40d40c004003007810800c4e40801921403801011598440f010301e410a03002c41520703c0340c0c2c01092500480c100b41081a0044d0750203103500030075a440c159120386034540c0c00502c1020b0058002c19062240d41b4401468100501550041710401044422170b4400e07403400703041c4407265204008100800c80050303203460005034030044520346030755801e4680c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 157951169 1250 157949919 157949959
    0x20613030c0215120403080103060b1221131e090603020108040212150424050c030103020d1b140406080102070b0109020f0403140303040501150605031f091a0405011d06 74
    0x4c14900441c1c200b85018041803580c130040880c16240910301c00c0000060140030000b030300416180440080d00b080c0200e0200d00c00141240066003844d01c106441c104590203440c032102681d41001040c0401600cca0003c019501811f501400c030000c402c22101d421900041c10081e002440240300f9081412007603000b1000b03124101800c0b08102d400190b90404e4a0040b00704555980751071103445103015401284000c40c0a0f00307015010038548030f49182d081d502804200c7c081054255407181180c2e061748421641c4814440040598860f000c0c866814034041000707a481544c400d504503030040c88003a000c5065aa001ca04403103030302c00016592882e02040c1c0ca8680031b66800544010700c21741007401c201101200543c411441b8400800003070240b80c00407003201801d405210300042042c0000740c0c2404e0190090100740c40f550080c1c01d046d81d65007003201700b5a400f2070341c90b400407031511000740001e04042c058070f07014001c0c040700c01c0400f4410340241c3d40340c964001d003194401c0170000c0c8420010390746 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 157952419 1250 157951169 157951177
    0xc031909080105070e09060616060b040e0d0c030914220b0d0602090a08010c050f0703021c05120708010602120306060403060501030b070e040209060304060c110d0f020613030c0215 79
    0x1c0000900640c03901d0f0a015042c0000c1c01e40003805401c100000440903d030800c1120b410344001c012800222041da02c8640040021302192500103950b40300b9442007907000c10080190108a5450380c001c0c8250b880d0007810215141c0c8a404482410b800420845d0340e00040c041044900703031049010000081e08035009004100241504690741c80c0b900414418181c006044400058848a584135a00c902d40c1c0d08030f07414440300310000740050102c42c255082d00d41c01481c14a020b032040f08c0b00c110388030b00501d141d021403c00b9100841c1340040e480f40080c003030720ba410794031030401d00708104290f2404001030345801d299114112885000000036266a8400041d90702854110004104968680c60100b004110544d01c403000f199010b4601c0c0c0c1c03145018005c54800b104007034800b42c110380381c070741c0c551005d88a50010442400000490b940da044401c100c5070405a50503030b90f0340511070100300081e040c550081c21881d0000150600d0302c3c08682c0091001c40715030340c142c640c2184c0494038084099030b405 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 157953669 1250 157952419 157952429
    0x1c050f0403260114040b0904050d110a0c0e0f06010f08180708030c070e0a06050d0609060b120304060314012d1d060907050304050d0e03192001050c031909 68
    0x120b000010030103c4d851482c101d09040e0549040024036403400810200707007404c8400038001d0344000c441c2c070f1629100c0c1000001c2c40f50720204032a07520410b540e900c640500706421030f189032003101c010845400100a546030b088802030810241c50554410b0042031400000c1100440c1c1c41006e6049060600c10003052005040da00107403520b0b1035150500c0d5880e0140e82c0b146036100e981a00100710892403610950703003201c02c02002c107042c1060360b43e00d403000390200f000c0549206907a0540440952640d041819905010801440d0354500b000b5000e4200c0d00100d00840d000c16915006100164188144c403c00da860174034024440c031420b000c48240340300746400103039012060214080a1701e006800c02c1c1e005d00300c201c0760b801e49a601c00307400b12400d01049402505079440000003210721400b901c040f690100700541610a04004480e801481c000d449004650224550700c41903140f01c0d015604180303100c424a44940340c4002c104070903580b4000c07400d0030260064035002c0209940c1c0540304201c0105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 157954919 1250 157953669 157953737
    0x2032806090f1a0106051602011e09080601090207050307062007030203031905070c030c0302120705030c010f23060604030c0b0a03060b041503050a09060504081c050f0403 75
    0xe060715200541c400e003040100c5a0f0540040c40801501030218214181c40302c0da41c07114140300310a04200141c421410050381480703940d2041c2d1000010140c030704200c00c1c00c1925011095454516030034500348050f0f01c07403c071035031060003e140019804012142001d4021201140301204400011202d000807820076410f04800a01e6000301500031020314071922140c01c041c0100c00c03c4140b0386080d54030440b80c00d400143d41400c850000f90040c800040306500a1040383da4040052245c0c00c1568000c02040d80c0c0f660010400c026840801d000d0340e100c0d0b01d10762506000136a4200c00d41089142495001c170901e07104400000c401d80c8401052340c008542240d17001c401542c2c1d4200360445a481403890380002401e1a00c0401c6592004084070122840b54202c0b940070b10015400324010070000c2c00b4513810359165090500818620b010301405140500c3c002c07581e4414000c01d000a4141004489000c2c9091204001c00071100e01d860302d60043e0103080440b401e6100104510301c0e0050170390100d1140e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 157956169 1250 157954919 157954931
    0x8090306160305010e0103150515060307030204051203041a1b01050c0405030c09012301030e010903020303091005010b16020105070203010c0915020601140402091804060b010305011202032806 84
    0x920398440e0700c4490010341c4042010b640c0300c10300d254070440240005880f407000b40102040d110600d900055200e0030b004c00170707140c0b00728120000c0c2140c0e005036241c800194001c2414811440e01c030780840f207039150500c020741c42c0515041ca40d20b0055039090b00c50145120218460421601c94428983c2036400303034000304410b00c0c04414810503500940101c0b03000c3c1c1b20307030040c086403400c0a40c04d4034181c80702403c83c3c40408179509001c000c122402c805050416403036000a030140502401400c0e01540320790042c41d22407070241109450a9050b94059900f2820200100804220318040300d09a10440315082120011070005075864890310000135015868018004081941300056906462031202c101c01410800d00d0100d0740d41100313000d110101c00d40110004594585a80100007501e000703080c1c081b03c035501458103200f03014102d4003518400d4560708020519a4184550b60144c08003c0414500c2c43c955000300359640110a8410110086400f20780c0032140342c8044050b005500071014040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 157957419 1250 157956169 157956181
    0x25090e0f06010605120906060d0209090712050304031106190309030c0b09010c0806010c0203060f04020d0f0b09010506040905030304030c030e22050703020c0a081e1b120f0406050708090306 83
    0xf40b41e11107060842d03034250b8407010401021b80031034003600030200180a08032641c05030702001100040501f58041e1441948800254182d50a03501c0c0d81650142010716215441d60170804400700e048100c691041900b040410b840900c0c9040c00e088440c0b05142c001845801841c5c2503840d104002d60140c040e80c43c500070840480b0054210101070a02a034850005486030700040d101c035003803240000d600d50006000201510203070380240f54000d000402c1e401c1155541d460750f0303800002e4144280e0b4251240c070f081105400c82406101e8002d18103841c01c2190005545400341c6038040900010100b0075105800c0c0300b13140c452044212580310052040d505c41d03001c4030300388039542810b03151018180c2c10000051f05c070500910070b4410390f41022000c2c0c06010556031b502c0c41503034810b0b08118840d80d001c03c4003043c009424406010a09110710700e52800320000000140340030300304495038060003010082450b450301400c00743ca04031490760802a80310000c91801504c00d025008009403d03100300010088 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 157958669 1250 157957419 157957427
    0x160311010e061305060d0f0507020f15100b1e04080102220b030601140c1c08090105010308090d0f02031203070809030301060c0803041103010e0f25090e0f060106 71
    0x144844262a1071088944080520420f0f025203e807080d5034200f03102d410000b034103100e0f00070690480b144000060403554000c4ca5012545c0507110040164400d0b00341c0c0801080c100000d480030340300c244c1c150049142004540040c0425405110000d0700003240c0450300c603440356009101245058016601c81c0e0301c03810064002e40002104812025601194000948400140700709076000031705050310f9039a0741d00064a045a0540c4440243c080802404000d44024045004c1041c010640340c18502e2428100400c088401f8000d0107083e40b40030010000200054121001108207a42c00f0020040900b001640ca201000c40a0f4041c0950301d003000700307001c014008500c00c1846e61542c540c0c98403050443c540c0d90100740107020100c0c3d041d202010101d016980556440783c8242c0b4016510120000401e0035141440c003040156440f0b00242520381c002404070510303206404104082c1099180c40d103001c2070400340706481d203140e03444814040714401480b0b00c14079810301904480c0705580da844014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 157959919 1250 157958669 157958693
    0x30b0904050d020c010305090a030e0a030605040b060a15090501030c0504120c15050403030c020607020f040905010b0102060a091106070c1d0115050705030304140309100507050c12060a0e1603 84
    0x100050040c00031403084c40d03010340700b22402040319600804c1e401c4a942d8090740d074640c4e4080300e1940311a003010000002045801041d106a10400ba0b02c100e0b410300350180080902103401c80b4480e00381a24035486041c1d030015007103080790024078011451070b207080000c2e070b15841240c1108074070120490480341440b52401d901c6003141c2e01f01140c100820504002107a84d400b80c1c1c04000c00107001e54440314091700d040c802400a9a000812022280c8540c1000070115689200102d40903519502604441e40c1c0500c41c5a50120b20b40009100b468195911003441c0b22080d61a9442441c000c2204400d0003260280080074015404603268000206103145011540911503d00c681c030203040480707c40c0b8844e605803041d095004004508549417070b60b902e190744140c504628040d1000303001910456481c041c903100c0f401c101c0d4a0301c69590110381020707414141c05490042c0a0342e42000c0080c50705000080341d0307900502c10000040c0140420310a1402d24a180601c1c42d100040c0c01404001d02000075841 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 157961169 1250 157959919 157959943
    0xa0507020a24030f06091a011d182e030c0603111902010f11041d0925090507080118050f010909060b0301020a0c300f030b090405 57
    0x7141400c0d90700e40381c2d4864204404008030702c8508540000700180e01a8001004043c01c4860104d1160b44401c210307012104040050610b404041c1c101c51119600060065589a07556942c240e10f5800000400c030520001d41340306691075014400900e040d08001c3d102d410780001010f1511828001b140f4003090388189001c1640c107c0600003001442500a116141c50399501504040c1006201e40085450b907202425007029552a52030a501144140c41a10420064a0031240c1c03514100f040d01c00301d1103003002805103900f4034081440500040000d0007892000c1408030300c0240d10905204011111141e8001c05105040400f40080950002d000034181d44078070141400000c03040310b0340400d41e50141c504000d180216001405800c100c0c2e000018101e00900d00400ca00214030080390882e4000c084080c0094500c1c03805804000d203a800c013481d010104890408113070718603850544216074100302d0070309103c4103074039a040d00d074003079048401c2c5240002e0aa11007460503041140d2610410b07404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 157962419 1250 157961169 157961179
    0xa0c0b07030c06050c120a15030b06061c0f0614091501050d050106031b031415010c05030d0e070b03010b030708040c03050d0f031503030e0d03030b03030711090708041511040b0a050702 81
    0x54800c400d9200740c0c146004000040840c02d8512b44902a1b4101c026103615040301040105d0103c4100b405402c249410030807000080b4000001c0b540c1080752166009020300400001546040e40c0d40d070070b52036800003500b002c240080004000103071190300c10125190f0380f80e418200000745068042e4401c0d441c02d49110745044620311903603400c80844100d8980c03c1030451042c1c0104e4101e9192240f100030580041c1084400400981c80e443d1454000c289084445500d680140741d40071418071483d0300070070b24001481d065506083c80f02c3c043e030100034295410040e4400c001360500c00143e008000542c0c00209035896a84480c0300146014040440100840d0400c0e01207921243c01c4152181180d405540305402e00c01070750100610703039404403415410540c50342c0d89a40180e40c18001004100e1050034080b41000914003408200b590040104040c00b140b10304010100d01c3c0700c2c02c1880100450400001c4501c2039210f0b0381d0b907502603a00030f400100c0c1d0100e002e40798190040014040e15000711f40d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 157963669 1250 157962419 157962421
    0x190b01050405010806070f02030f07140708060c03010b0a02010609020f0a030e0c0a050411120f010e16080412180b040806091902010c171204060b030a0c0b07030c06050c12 75
    0x103000079501c2c02e10070003c0075030002d000901001d103c3e08102120720860320640e4a0240180b02d8144141c001850684008281c83c0b01030b404020100000340003014020050700442c5064120848180014407400820b0100060b0354105d02d8401c1d8410000b4259900302103440d2499019505140e4015203280404245410402d411000000a1030685070303100912455130030382450140005000d00700c0420840074014040f83c18581c0320044100d1050013004000d59896140070301080d69144c2c080c0100329055146180f50200070341c440380040e445500310301100c0408040441c22289650a540080c8600c01e034100d0108009803502c00400c102d03041c91003107500d00d0f1104102d0b0b0381c8842c0110038041e0f1481007a01c4e440e0055003d9a043c49816001d001c8241071820b8140c0003062a90100402c071915581c820104030070071285216a4002034025401071000300c1480c1e803405601081401914803040000c1036440c201480790203200750b80c60f48000c00740401d040c046002e150342d8100c00c000143e01c054200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 157964919 1250 157963669 157963679
    0x6030d030e0615010903060603111018050904140d0503100f1211060f0c06040210020604020f12010b0402040f0602010e03030c0715140f0711030c03040e130203190b01 73
    0x10003589034071a09840a400d00d42c0b030701d412403200391000120040c18402010000804070b140d5120300801540100d68011001c5074072420003030340c018840040c20038030104000c1d03450031052002501094907410398a4904507212400c0001c0101711022900c07400f88110b18040f5030342c0b82d0002c003860280c20010181d044180d2a000642a5090744c0e010b46c3d00f440c0a80b10403000071030200b14104404100140c50240f501c059217916a03c103034404071116040707610103c240011828102c07072440c20a1040d101900c500e007802d5000621b070300806015107100d44901040301782101400e6100c03100944009004565507a51038002889080c06407191f074001d07501c0c0c604032890221003c011203100300700e0402070034502112952240e01d60305c082c082074801c0c00e0f540c915102145280100c4a8000c1790780c140c0c100702d0f0340741031038009109202401001c40a904140510910104000291070540d5101d441c540415920000362800c03540c034501c8041e616101e150221203103104031715007840d10140540100c0110360780314 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 157966169 1250 157964919 157964921
    0x30b030a0516080d08150d12030b0112060b0304060504050106150225060504030611070b040807050705040c0e122e0f02030103030c12090f091512050604030c260306030d03 75
    0x401e01540100d014a4006003440b032081c6d0160124030402003116003403400c1a00e8400640c1c8440c5004404a50b88070700c448010344c1c00203120540d501d10480c082c0311550a040c60b24030a808003034001031540d82c80c0ca0114080010030340148020304040840682c8401c080b1000950705c012424211500d2554101c002658010780d90324041520000d0f02d80e5454203245075070b000001c007800109411051020320500c0001180001c10300c0c061409109a1900e035011824810308110007980a2407045190076407038110305400004240200b141100c50860503036095402c0e03400d190444805c20138000030600103684034051051501c0090408017030410500c034004000800701d110030701010300030501404060f000200c540030900b04030354180c5402d0b900700f6070760708281c00c7c40c0c22160041d5440c0c03600d800c64905041642c1d2aa2001880100c10350b46180345262525074603400e01800150801801810f42014812901c07601c00c8800c0110078001550100070142d124150401c0d944144a401141c0d086a40c50303120b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 157967419 1250 157966169 157966183
    0x201080f01051503070207080304060504180b090c09030f0706030e0d0e130203070e0a03080a0311090a0b25030201020304020f03030c0706080601271d1501080403030b030a051608 78
    0xc00f816000000b6034020150440f40c10080458007144100180802c1801040c4042c1c001000140c4079039840d40e040904445a0322a0303580740392042454610303000c46680c2c8580340e02d900942c4a200403903888140d000803d0030301c0c0c00e012400070350f489070b1000014010ba16030700c02611100d20109407130241c942040304450205242c00019441000001303100c8e0008490790003150440c0c12800c000c1820401307100840e4070004d0300d510070388038410003084c21164641c1501400c036545044400c0c4619000c0034600140d01e01e006400388050581c0c0214080140b50f44c00c404000d044100aa0114400802850028080d5000301c0e802ca0060804a15001d40c904000041d02d13400c0a040c00071709995410301004075104c800040a0700d04020031140d00c00b04080c00a00034001d00030010701038500e103905249044011400c0142000c00300d80c8042d04108002c01c7c1c2545020b0050003d285c40c519503159414110003800e0340e01c50301030b030600a982a0404001300011070b00c640800e201a4240300d5a038503030030152240c1d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 157968669 1250 157967419 157967429
    0xb0a050c0706240803120609100306090311071422090b0a0501031a0402030d030510150504080d02030901020a0b1902180406061b0f02030f0105070504080c06040605120403030608030f070201080f01 86
    0x490040400c50612340845983e80c4200c0708202c2212084d5030b5180c03a816a10005403da010901c00401c0e100110b4040c046640904800401ca4821040001c04105020051034150304103c0200170f040406100c02e41100325000d8201c0c004185600b050a02003000704428842140e4922a100c440701201d40c3d5002c116100d180c004001c0d041c803c03100c02d000e82c0948401801080a040c1100001c40c008034003008021411105a0300c09840d5410110a01c0c5030142d0003140030195841400764041c241c1c0d001846070700c801c3d440142082c40c1d4407100c03409030403040b522080b5030450703001144075201c1c00041c40d0400c805550407102441844d56924017600c2180b014501210f28014200a81d0007051030010f142d1051403000d03040361b1603c122032090741d003140d000740c1300c000004400103401c00c0344806c01c01c51040600c100300ea000d4501887e0500c05403452040507a5503000110a80c0080e007414080d9010300004d00c11038080e41da80d50380210301005a40e014580407408030301414003003007008451408150607a5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 157969919 1250 157968669 157968697
    0x100614010903080306040605040f0207030e0307080604030c050f07150f080402011b05101a150406080103030305070507050a0b0709090e060f061906020601210b0a050c0706240803 78
    0xd821603c036a0481d41c8010142c40e00680c41e12000120b584a600c02c40c20030b5000c0d07481c01070301c83d21185401410703c251425964865404509c0c10700409070080303952900550316042103205901c03035151003410081148101c0815000320100060b240210900303c000c1d00f01c60343e440c0e500d0454000c400741d070340142c15680139001131004049401001b40a0445c1280107000c1da04843c1c04012800d03450080d01ea54004c1c0000845c9c0d0801500340a09003003d001a01c403500c0c2005904282c14104010207000d4148400b404254980e07003c120010b01800403982401e410a05540381c00c1114185004401c1d01135072420300082604200080d01e10340c61191510040c0301e0405403025441b030112035868680b01410141e07222040d0010203813400c5e0300050150050030160064071596151011500e581d410400a0000300b203959180d0f000020500100ba5a006502c20b40c000740c0e0351504174059256000b240c43c010f011038a0401c143e0b54284510314003803030f0001c590944c403a40715100c401c3c003500c07401000764608500c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 157971169 1250 157969919 157969937
    0x1e06080610050f0a0b07140d020a0503120612060a0e0615030a0602090103021b010b030106090905101d01061e090b0d110f0604090b01140a0e010521070210061401 71
    0x15140030b201031802840010b060071a03a85c0c49280503092540192011903d00743e0740c1c1c6522107c83d8060002d82e4000800380041c14401040d038817855100e20905444d5102c0e102501c000405503520a040d0b0341d514880d20080702d1841c03800d11100001450b0110b8041d02c0d500c101400070380300e0b6894114600401e0340180203001c3d018015541d24000e500190031084c18903400b8000450340e2520121408000342c0404000310302c0030381320720515007100d069400100c10a03082c044108042070000480b90000c10101c4800580c5140c11405100050050b041400582d42402d0f0009001c6800c503c0d15015089220044040300d5a60f40b0020b04883d18903418982004080b80d0a50208500d0500780408240103072105d609404904000358055200d60040c0d030000c1c0c0e0780c001004181d64444005014182e503260442d207000054603000d0403525a608100781000000120030038100c5950918039448403d0b26114481030500c0ca1000e5103c80c082c0450040c002d15060b4001024548030f600b00b010550113848038290 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 157972419 1250 157971169 157971179
    0xd03030e01020c1c0809030301120b100504050c070501050f01060c120c020303040609090b150d09030c080c070329060105030405030c0703111305010b03130309091e06080610 76
    0x506880031200209540c00e0206407101801805040314007100140040c0c8602c1885a02600d0400080d181401070380c028030040c0100140391540c1c0000300e4208074414031994550040c051003a80c44c0c0c0107203420900b41401c1c41060070f4120050250148608028881561070108a01002c403003441444001282c6080980100c0c600c034003140382840c0311b840d15201003401a000b091a42d03000ba070096000905408003003117118418441e40300118400c40d4512595840811195000c2c060700000710840c0b981d074034031502018043c0c0c10090030030b64881030564403900c98039811504c0f41c0580c80142c500d078000b02c2040c128010300b0301214030fa540b03594031710551720340ba08001100c107500010001c8407203200400080703500390020011130008601c40c5024000008154090254414003060400022030501e8018001c0320420800e5030390141a009240211000038141160b00040c01c2c0e20190b00d0b145000b481c65550038441c20740000c050179181081c0603055441011a030b541d241158807420903000d08405100d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 157973669 1250 157972419 157972421
    0xe01172a180403020a0618110112020930060f01032d140f1203060d0f0c0e090c010e1e0301110d0e0705010207080601030f0203010609020c03071b050d0303 68
    0x4a9a018003014201c448094a2100d9424181d50540c0907900c458042000c20000740a400400920000f4491880e4042c0e600d603d044851f0081d92410300030714150500f5039030050740c16a008c1250080039101d0070200c0185044000c01103c0103851011850302160b4120403000600c140514191300e6051240d81c40c41c1c40e0704d29a000e403020742036032401c0e01c4017051007400220085102c80d0750052411002564003440742501e0200d52005140c3d154000002c9207103558805d1060300d51105050f41c007000051035903e080030040b0401c0c41d00900d076028442d008561980c500e00094450f405c40c0382101d02001f0804010b4504481325080d243e03100c002c0b043c0d8540307103903802203001d00d6800700600040707038040f86c1d8001c880045d0404122664155036034035095410381d400304003800040c1020b001070007c040c1403c00c455140c900500001d4900070761920702030219242541300e840105004501151280004100c4503242da1226a054520350100e916200881c01a448400110340008010510154182c0e0b0190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 157974919 1250 157973669 157973743
    0x3080301120f0206030a0c17010f06140c0f0a030201050a1404031d04020406020d200303070f020c0603130b090d0207090f06080703110a0b04060f030e0f070e0117 71
    0x101c0c41c0e900c064002c401a2102006580a91141800031441149a01006280340304105440007908100801004500311000000090710494548909800d00f12088980a481a22103c449c5449440c20803d00c4400c00b04c5e48445031440b84d8000c0c0503e0f01c0b0720015500740c86402955621842402c4003140c0020b0042d000c00c0500413a4052080c0b6840506001034200d8001e0b601c00300160300701201d0961115070100c1300031035141c04d07000c09140603002480e0480c1d9a0100074181c4051295514000408500801803001c034008000d2511313650303240040f411440843e2846003200c0d02c0301600003007400301d24007042000445030365074000c00ca001c1c82c080800000d0300040d40d80f90700d020743e40c40d00400c160324240405805940103d42e6003400c090b480040c007110354034a900040c085402844240b204a52003052424030b10030614002c1084400c1d4281e00c0e0034400c107040c00504c240300b42a000945d145860341c0c868100c41d07245c1c443c0350504503400042d540b035603c02c65410b107103002e00d2041060041004911782b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 157976169 1250 157974919 157974923
    0x80904020c011503080c0111030f010603150321093c03080705030a021911090711010e0604060e03040605030c070503160b0f060d0210081b0d060306050903040308030112 74
    0x82010200f00d000c0c00f80102203a00b050f00c48100009000740c50003000d01031000c0c03800c41240f80b603180d40f418518070b00080300706008603c20036840b040500082101e4600c1040559000110840c0a01a6650302c054008081b0210340110341d603004005072142441040303061111410b10b80b00311402c00c1d0100c204000d01d07048468540307119185400301c0070a4100000d4924184a44005d503138583d1501c0010f480d08030010703001450200c2402c881d900282c10081583c03035010083d501801e00c0d807201502a1142030003140c1c41b000c0380d842c1c43c0300d5405030310b00014083c0c003039030261008008902004180b1501da100302d0217000003065081021034500c1b180030000345040d5004105803814031035806403040034000030307180035280c1011440901003a650300301d0816810820031074100c0104600c1342c1c00f11707100da0001000c800034005a140040d004003c407403c503408640804d5103083d0359500315040100100f4481c0020b0700e0b020b00d03050005552920000c1100c2c2074a81011078542180e180c2030300e00c03203008000901 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 157977419 1250 157976169 157976171
    0x2030706050619060e04050c03010503070e0406090f0308040209010e0c091c140a0303050f010608061e0a081e01020301061407050307080d050610030605100509010309120903140703080904020c01 85
    0x102c0700f04074140b0710120140c0100c1ea113400048440b80d00308000c1d110058445d600080042004111039600000c0645c1260252450300801e5a01c130705200004140682c80608240c0c41008100101540451054451407003203400d01526600c80d07041c9140504200d81101204030200154421881c0c00d003252100e420f56110304036a03065041d95800f80e07640185c005070415510981c803e1003007607018020240d11a4558013000e103290b1504070010018480503280c2c902407a0100d42124507449202204414a00050a00f120090b910141e095460b80442011128881c001107404a40325040c02180e048039500d5030b0f601e606488040071560b40780d01c4018225a2807004200ea0750004a565001d81140c2c8540200011076182850500038840352000300c00e01011302d4030005100f036540f100122486d82c01c042c5010354450000d01c006078000c0c1fa02102c007130000448201a440545c5d400303c85101528464402d90701500d044440d4243e0714020b9000040030160b0601100f000740c00d1550260212100d00c0c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 157978669 1250 157977419 157977439
    0x1b0f030e070504360503091012050f0108010c110604030e180a0603201003050910060311040e060705040e0c040b070507030c0b09090a020f040302030313030308010605030601020307060506 82
    0x1508581c3c060132072a046806004207190440b0007504020803d4201041d056a661000d68400e5201c0c426050068811000082d800c4e9065102d01505120359041042c200224148080c2c2400504801d100e04001d40d0b0a100e2090151849207241c5031080d20014001c103074585075a64281c601e20200c451854109035103180c0110b454a070030300c400b8000e007850440003c0041c15801c00c9404008100300321400603403020741040d4103454541401988900901e40001c3e01d07107a121010b802c08510300c042482c0c09081050200038003004446e401000081120100541e03408400c9043d00c50004580d04000304a080c001040080007515016500c000e00e001814039054648801d90480d800c40172050b61960311940040c0308010209450303201038124604d1060030824000c0009680070303002840b25440e10780200388901c00f840c4100680e4051503000301903035102ca001656101951800b8401030f400101000300019405000750120b81c055001a4055494960141c640380003412000e04840e4204070640 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 157979919 1250 157978669 157978679
    0xb15120a090b0a050105030c0a0b0a0c0201020c030d0806180603030f250813080309030703150b03120d06062a030e0303030a060801060503010c20030d090c0501031b0f030e07 76
    0x460443c4141082600060031354106014145402e40b0444494040c550b6000240014201c22040d2341c40314042d40303044020340515100407820002a103541c02d4062203504010000d003a041602d40e8841e8005840d2000601424203550b00c8141090781e138181c041d041000301825030030308200248008210400002a0011400c10f51074100310341920680d03030764401040304200610200050b1000b418a64000c42c141540003000039220000c070320008000f0003d54070b0b01d40404006801403602d2450090a0702c103000b10b0600020380a40c082c1640411035840d100d030120b039640c0100b183c2080008410740828011030104641900c49140490581c00d0045100580b01c00740c1d0104021407007000c41480102c1c03035610b80008075082d2a8aa0049440f990414081442403a40400c400c03145074078080c81102900711003c1901c2c00c40c401c05c02000b12407130800c0c0c40c110900c1b8594400d6400c9410aa0f000c06ca00b806144800600304013600b070240000d5a4200c001e0080c0e40709400001d0724280020070b440b90140e9034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 157981169 1250 157979919 157979933
    0x306030c031416030507060507060e01020a0305040210020607020c0603060d141612082d040311090109090c0b0309071e03060b0904080d050a0915050a0b15120a09 71
    0x1a80304075181c0005540b2507000720310a001000d0951005140d03140043c0c1103030344003904e464040c002c0700304015010502d2014891590080c95560f030014000b195902803420380200030340001c42e01030740980c0c91415030025507440012040e210384c0107540334003c82c40340581009801d0f440580306a601001d11a50340000c40c603e419030070344004050300248510a80c680e01b48201c82400e82c02151480a110a1240414208011500301d5000380018480100b00201c03505043c200000070042c074000e000c20044100000c81e030070344220000071030b010003590fa03032007800c14250340240c103000344000c030038910420100025401840c0c01001510598120030348130510728061a1a107002c41c0a09030740711801b0002e005541c40340c00c46a44043d9020200d61030691a003000038442c02c00d040e2141a0350307100280090103254050491070f42d2001501000da540403042e0006854160b626011051409403c40740354645a1340c00340b421300001014901b007140101100050a400615589102e6103a03510b000007c0c641b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 157982419 1250 157981169 157981193
    0x1203052a01020c07090f0e0c06220b0307121e09061e02130b0a0804110411070605090717100e010b0607050a030207050f0607120c080d0c081e010302010f030603 70
    0x1d00401451014a0981145c00b42c80c6c05d0010501d03007034540f0281086d400400f18200c00c049030306071400f035a604088203113600c010011403d0070044010395000455003c081e0b20065014044031b41c0d031414002c101c0440300086401e17138052509886a0b9820742441185d05030826601da501840c0000344d15000c0360281c41407001d0741e8550101c019800106c041003154090100b101030400d0f14a02400c01e5508640540440009800901401001d9441403d50396540d0018070486415150355512030080d890b002c0080e16003540c0050940c054039201040d42403814903e56050610300d0010a0840c071880000340041c4250101280319540b2841c0d524038507228140140422441f030401415400440d05000b401c14929400041c4902c0600044c107955564560907203501d00d0f0000c0351021213015005050b6124134100380000c1c0503000108109000300f0039940400c9070801c02d62121031041e0f55011411112451500c8083d510f40b09107001400554811104599a1245418002080d03034498590341000f1071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 157983669 1250 157982419 157982437
    0x81b030a0605041a01020303010614040902040b07020102150408161104060f0e0a0515040b040b0d0606050301061d010b13030c030803060f06031302150f03090c03071203052a0102 78
    0xd180c110810071403c00d8410601c075541c51009400d00c442040340001d44910040c41010100f064142002d040021081b0407a402845940e400310b503107a03940c4282107180d4102a03020790250140c80000041c01c07800100540c4100e600c10001403900c07100071340c5101c40d82624942074421813640000e8640b942c689204146c00f4107070000c140001c09240410030071b403045004011414903814501840b02c0300d50080c00000031030004443c0402c00000d1003000c140240300e0000c6113544801e54141681c18002c83d0341c044000c1c1e5206070000e200c015220800f55816038403c040c202d00300c030202c0b40100070b6070010303c1c013401e284d6460304000300700c5580d01d481e007085078000e6800648002e24000140714031460001c1e805070690409403445401c51906040080141c403030030101030300a02c420800714009014402c02c64980b010b003a07080b1034507410310841941d42d50401d40345581c001e03c500c0c080840c0340410f9400300d0710a00d50543ea00351600004000550a8034448417020340a9a102c68203442120400c1c00074000e201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 157984919 1250 157983669 157983671
    0x11010b120705040c111c1b1a06040c05090907110706020105101202030a020907180f1d06092212020607080115020c01030b120a05030403050d020d0f081b030a 69
    0x10b800e04080000f119259140d070014400d036141c3c100c9440c00b0129130b0241d5818846440942200e00303a0b01602ca084000b41100725240c1280e80f46c3e802c200a1001358080039034450a80303441580d07030805000072110401c000c03c0114100b4400384100b850301c01e10450784400b4500d0001101c01084480b6481d05820340c01800140c0d441e001008000010031016800610556550303121360501c54010a0300ca0f82c50fa80302900400c0d003100080c0e8041d006000300101c00102c580c00f0a401d03541d030a448804c240740d030f000d03001c07440c01c685d400c8600085548100c240102c42c000c214400c2605d495540c003c034081f1031039000014101d0000e00502060100707100b40300304061500544a2407801a80c01404110146c1042c40d2980380c0410303418105030b00107030b0303034800100030f00b0b0000e10310740c6010000e00c04221140e6a6141072007800c0780c02c000c0042c00f0000e0f0040380e103d8030440b0311400480d0803c1e600c070a00b90001b07500007240405048034241c45034034242e4100640a01e102240240c415440c0c2c06684200c440196403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 157986169 1250 157984919 157984933
    0xa1e06090807200105120403020c09090a0219030201050f0703030f090c050906010c170d1b02011e050c0307030b12100605010e010201020403080307030e030f0412030e180711010b12 79
    0x1120f0f20460300440a60070100d07501e480c402041c0060050f00440c0ca0800410f4040350000d410140200202c80d0003143c010004e0282d8500640c0d507940d5001c21581c12800b800e40d5243c05180d0302d0303400c00c006080c1e81c0e0503120641086401d0800b0704030ba0308000e0082e020151602c5005926415600ca010315113801240514071b80c0c0c0c189070600604000140605040002401000003c03035400c42c560074101c030107550b8903075540c100050010050592205100140c128034a41034a03460f1301503001d40c2c5400003500305400031034054400d07602240c03021070b410b54214074100000703608075201c2d600c014140d0100a000c072001c061400031003890b0429451620111664130a01440950703004441c55042070800d100a5141030b08598442503d4040500010149070311844c0303049800030188203541c0d4102030744c420240c0b034507524010b080601d41001015004281e08540414946c20007845404603011075140c2c10fa91500e8003d400c450140000d4100b0300c0319541c1c1c92a80900750f4400e52403140c05440c405c001c002c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 157987419 1250 157986169 157986173
    0x50103030c060c0813080c120d05010806010501110d120609020310030c080109020105121305030309101a03032a010e0f0d1b03181a03040302070906080a1e06090807 72
    0x320b03894800410f051164540c1004603a0f00318413002c00e0782d40d03807007488151100d80316a001880c04001c960b41070000b640200c2c6240d020700c0e69070301c00e03812505040c00f110500c0c0d03620380c01910b07085800c1d4003404894101c407810068030750003131064401d8400182c000240c6155206031410480c0c000b5903d4078070a04805a0420506c4400d0400c0000303422a8002008040345581c0080c0083c0b0070051a00b64100388003002074805100c1c00d051141094101090b41c1c1c3d00e10349400c55030b0f06d07400100b02082c041c51518000011450b5400c01c002500c4034040c0003103281a002d11001c0c00f40200040c001c029071919400e45120140307082c09225110249000100403013443c24580908140c101583c810402c06000781c0c92641034540d4070343c42185509401c06000d0403008100907940d62401c0d402a400348034441440721024810b0720025441140250b0a6030407032a110614072013502c0ba41c0c130610f0031aa000c02c10310fa001c5030901b2500d04000207040c00700c01e2051072a9443c0010764048400641d03003981c000c901042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 157988669 1250 157987419 157987421
    0xd0b03060105190e090f06090f010c0c03090b090a05030d0f080f061c030509060a09061106040b0705090f03100b01110c0a12020f0301110405040c030608060103080a0210050103030c06 80
    0x30241c48100c0d00140c1c190b03900143c1c003520144900c280186000200c0c04642e41510500151303000d4030807070054445602e0a81c00307c07903869900da1280c40c1c4a41c07800b091540d40c58403800c04000780710390690b1840c0c6951302d007c848031041d402181085600907150308000925690410816481c0304007502c4082c0c5000c4640703000340c030b00c0c0c0d0f008280400c44a0398404000043c0e42c0c9990b601111301703072a40041e08140e050708080750765015119002e5040180092941ea03c40d03048001030301145e82680d20782c04248902c1c5c2486807182c0040c2e400825452041c0d004c03407403003070003000a41040c410103014110070041890009103004c5030345a001c0e4040d95135241040c01c2c3d5a00082d0f1030440441d00c001446056994400710f05d24002e540300d4003132444c00080003101107548084041b504400020020310445000c1c41960740386601c940b08003482070345012000f40c0c00d9070080c080c81080b64130000c090720f030982c039544407280e42e68440c16031201140034140d5040176103180751003118040c5004e41c4d1640400032052130620 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 157989919 1250 157988669 157988671
    0x1f03150602010501031e031205040b01170c010e01200102130501090506190f030902060d0c030f06030209130f080c03030106031401030807030315050312090a170613030509060d0b0306 80
    0x100c1164140401400401c50038010444c04031b0104841c1d91440409081c05c651511013005640342e560300300410f000500c4500002d0034103032030095181a00000c2c1c0d100b5071544d100d20b45032035103011a800465940840d80a145030300d0314081440e980b0a20001000007540c01c82e03010b080c1d130344404c1c808018180031a5030321405a02c00b8100581d1440d10b011050402180c004030b040d0521010403502600c2411a640700703030084000150702409030fa17110304071395002c0e4000c2c183c041d1100b00040e103048588480c40c040c13409004104ca4016010885544842d040e0078408840c05a040d41c07801070384e464880005240b100104407401008019544a50400e80002c0c2501c10000105d00b024980030010310101c0c000400300d422250b0325041c0040c0412401d6298401000c4a500065240c0580c406003980c0b244040010305281c60115141001262a061101c02800d03c0300421100b03507000f40c00148120101030011000c15000e410164140443e160002d11140d11a841c808040740d15a40c443c0124241001b8003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 157991169 1250 157989919 157989929
    0x911040e071107150905040c030c030b190b0c03070b0414060105041b05090406080303070f0909151802070204110702030607030506010f0302090d1b0810061409061f0315 74
    0x2030103a8049031540c880e0396011a001d2000c901c10403030512240701703000f01d21040081c000600180000704042c08054000c0c4401842d94000ca800c0c10102c44080c41c020610a406400b81024030764420b041039010f420781d42110f030001489110030000c0002203180380201c02c0c4034074401c030340891714000c3c100509400c2031410b03489a40502d0404000f40c102c080c424102c480912010302d4129110365149000130040c10481d03101001c5800300105104016074081e111820502e4261640c565455492002c078007100c42503105450a1900724900703002c20000040e01008000c003039603000d0706001c140e8002904458898040940d00701c0c0016020302141801d004555002005003420000e510707020002801c603444000c1004c040540c000340f4a8480e654203150a13010a811041c582200781492401d6006903255000b4000184540045200b04903568000d00c0151040c2c501048440d84008081c0b103800c10300604901e40c0710000d0007029004e58030742c0805040c80f440b195000f050010031280420407800341c58103c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 157992419 1250 157991169 157991177
    0x4050d030e070e06010215040302010f110405092205060f0703052427010e0402010e0a061d040b0d030215242e050702040609141303090911040e07 64
    0x15a0781010310124000c011950810800400c42e690200102e00f03083e0140118456030001d40140400e00d17605500005082d110350104205a4410040b6501e1501991107017590200f94000020000d0028610080311225a4a8a15a0080941e03105801e0a504984407a9032084074010000840e5050051035003003d82c04803140d00002c0c038940e503074040303030340c1030400c50b0280011104040c2d8980328010104081543c07910020200e5071100c044200d045016a003d03400600075515031051442e000d40fa940440d0001d444019031020b1301c4458500b0500400030003584995541c04202442c1c45070403032540300610a86c0506076650200395112a60f8001800000484060b08801d208504010758154076001089a141000f49080180c0c21000000d0501ca2025071283c000001100d40e0010003a01810707200316030512409440380402e804854070750204002d0880407401050700c45800c8070303042183c28003910303050381c00d241c50f00e041405460580d101001c1c094030010b000c101421503011519004003c920b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 157993669 1250 157992419 157992431
    0x100204050d030c0519030e10260402010c020a060201090c14060406080a090507120c0b1602010c0201030b06220510020309060c01090c0e0108010e011b0e0a0b0304080304050d03 77
    0x1ca80c40030168070005003404010704800c0c044c881c0410854507004203c0d282c0030035032040352900800a2540d1a80203000c0c0b903010001400c0680600030300303103010081c07500c03c1d40c07070031118891483d800002404c142e051010310b02040000d030f1511007002010b486a5000440c42c01035610302595006080d0703000180c03040460380c18100550359801210115034007480d020402e501c5034002c410050925103c001d00b41c0c4207000c800650810010b0b0340c40d264900645054503456551030203e0164407511040f6040c050980c08003500541c01b81a500e12514018980001d646551a01041c0140d0004111416100403c20342c500b28000b10a040c001070082611200d006541c403580281d60390151018451195101040c0e14520650075031208006d40c3e0000c0501c0a129a1581203460895080c095a5440c0d4203080794081c03081c105000c1c502d0f4001c414503e14100c290121421119056040c010903848484500000784d21250714029501481c0500411641c9092926005203400d94480e005000c2c141041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 157994919 1250 157993669 157993679
    0x1104050f0f06030706120902150a0305010e130b18030c06090f0f0f0a08160c0303050d1802010c06020a030f06030c05010813081801110f160609181812020d02100204 72
    0xc031911b01450100500442e1a1002d1300c001040014030010ba0360642c0317004115150f02c0c540c5500414106c400d02c00d2640c400e170701d038940c41c80301045000001501d40810742011501c2e5019041412004007100416241803a80c020383c030780d040c2081618144c0096100348000390f031404061180210002c002ca004200380000c50440d29180c207203807400a00490404100080400c0c0905400014130b0b6002c1c40b1002d00700e48038603014049400c10716080b10603078603041c0081e245c580d9602045c450260140c4982a074282d03150346cae00001e0740c4854400c808254444415031a000c0e118090b0320301441c0b044103041c0c0c80741c0c24070f000100085001403007619449246118840854664401c4030700014140043c2c40c8060000ca0040e40c007108103850f11549842007002d05158883d010a64041c0489604002449035545007021a114140d9000308440c018261804800e12001c0d680708401c50a03250541c01000000ea4446003441035036400f8000c0940c118002c4200825814040303981720000a45085060a00340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 157996169 1250 157994919 157994927
    0x2060a030e0f150c0c06220b0f040c0506030105060706050a0f0908071a06010503010b0901090b1c0605090702030d02130803220906030804050409022d010e0306070215041104050f0f06030706 83
    0xa0302d003071170011061001122480d03101f90100155604070701800c200741802010807005400072030701581e460303070041c1c00411545000c10440741200c000a00d094140700081d15108000d0102074510803042d541d809440000b01c903d4054560141e01404006440d10b2040c01c1c006030a80c100c5040c1e1150f24190410000aa0b0300402038074103451601403500e84400000b0016a565441a044520100340220b40e000d04c24134141c4070311411982c1400c042c880e007a03480080c402002d00a4134000d001d03070006c0c0918040525503601400441680b007a07003d110a582d14141d50441c2c1c0030005500102c00580c0040101e141240351060040030342500400c14103203580c41d601c3c850b00440c0540c5100c1c1c0e0320b8160810a40d80c1c2c1d20046102840c814807a100303400c104411000f00350036100c191074089880800400103501e00030406500c1041250058440101081110301466200510843d581d07010710341a40141d484a101d100d102d100c12804241003400c103130707010700200c0c01d0003010b052080e804400140045940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 157997419 1250 157996169 157996171
    0x207020109290d05060424050112180b0709080f0a0f150c121401050f061608030f04030806240a12020f070c060504030f02060a030e0f150c0c06 63
    0x1802c802c401c02400e81c18118201070103100c074160318a001c2864081d62105500c29800740c80200d40070846c2402c1c80c041e0400d01c071507212800645144404007048154004e140f80101d0410403080081c00301c540103088540d4041c0c1480c2070340d040d5207500400075600e0b04071944901801001c0000d092200b488074101c1e07500c80c0d075410024242440f00511104200310141540720070230610310184458485000d005101071078902c074450045080150300d2002030b58040500b810303500701078082708912030070307806002c070301d03070125042c2e6401c900c0e1440840d02040040307001d1801040c0c0c042502d840381c2443d007001800c0ca60702a241031303c031717460380d0400c42210f0401c8215400d050000d030300300300d8035450700d250b068820344118808070b601940001403100186c400c480040134068410407001101a03168503003241e10380103d0100406440d0301c00f561102505d406009442484200c0c0340208c0c004622401140c01e0070b880c4034100d04141d2007070103241350f400c0c03100c2c1203141d010031820003007403c0003241407905686240c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 157998669 1250 157997419 157997429
    0x50a080c060a0e030109030c0203120a05031501090f0608090d031b08090f0a050307120302040302031504050c04140f012403051305060c040f06031b1d03070b0414040207020109 77
    0xc00018000d81e9640070300c1c1006084031008008000f0310a1b039007006000466080c108922a020382007600c040341e10220181d5001d005a030380c4e100c0c216600c90040000b05c2042e00e4005040c800380000004854600300312200103440c40741d90300d200c141015014141741c02c4c4154444400e050500000c0d019002c000b00c80c2480c3c0c00c945181c000025190300b82003c1c284988070180c200c0900464085209008002004082c8039224024072460691000c2c0218101e005a00000b503150308070400c0401c00c14403041c0b05c01c1d0420300600c1540d168264400008040310301c1c400c0300c0c03500418000204031111214a4601d40140200c5c0209055200c012040c18009030020804500b03240c1d4403000f18400e4080c0400250310180e0080403a450360800071131700c010a030040c0c81058144180318030042406803003401035a1800904265920b19000700c2041544c05448019901c1003d00c90b845114440c0e580c00c201210091624111f21951103080114104c599030f83c01100301e0007680104083d00040c0d80c010a1481214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 157999919 1250 157998669 157998679
    0x10203040e150d050f1e01060803090d0c080118030216032414070207080d0509060304060c02030720040b04020c0604020603190203150a082b0212040b0304030306050a080c 75
    0x10302c464002586030b03240c656003d04144940384103101c0c80da000240c0d450104240d81044125070303040391310306c0b805c0e40d20074001c4000540061050301100d04000c076850504510842131240040c0e02c85000c0c03800c540c40c44200103040546044410305254040c03000708080280001240e440c141140c9481d42886241441002c5d00703800388054901c000c0440e40407094190604036840e8050170441e500075031b240c8040c0101e8405006074040b0b0781ca080d001d5401c580e203c802c040c5c802030541d81c079511010010701041c114801940020030139880003c0c010400084541c1d8280408080640d003e018441101c804143c6280540c1c410042c0c2d0204000026540f9481541203034050ba481d521101c581c6001c0d055080041c5d0000e0000c01484a100c0078071510040c120425108041c41c1039458403203542e00d0280c0400740baa0101c00c814483c028014552200d6080c1c01c1a0045824844400d41190100e0780154002e040070b03c008020f000826605000d500c008020031100e5850349804d0000c0c00342c9480880031024419 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 158001169 1250 157999919 157999951
    0xe07023007020307090906050c070506040308060103060803030a0f0608190f03030b120c010201050a02070b06150c0a080c010b030a0213051b0a020c040f0203160806040e16090b010203040e 82
    0x145240000c5481c11079001d419030321081e5490030014060a482c0c04100ca0682c28080000c0700850640c069a51b119007180042c082a1a261015500002c018100f14109502c2d01d101152060082000f5405900031800020f9042c00440d10802210110f40291345c81d40c0199040d522001c420240c20031006400a00c0da145900c01d91509400500b2001a07840d044410071480345400c420124048090340380a030003d001c15a6a6072040c0d04174400d00c0e1004045254000200d916030801c0d21506c01c88540c0c5400707041c94098800e030002e00d44015811304031280c140019040b04104000e02401d80e5540007078000706840c1109030300041800e4401910110b005950310b0026208014024039108c00d401c2512003541c0e6203440000094540c0c0c2aa541c0600990401d100f011a080c540d100b124840c5010030140e44104a41580889a088000d003030158000d4460806030540a814004454440d10070043c0d6121070345030010700300641d55182d00136030549d0410b00080004502d200c0189038010088910302c214 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 158002419 1250 158001169 158001253
    0x50d0f0c0c0c061b0204150807030c0918031b050c120c01020f12040b0f04030204110901020607321201090e0d050a17040f1704050415140906011b05070e0702 69
    0x401f03070341c42d4840f0320b4a11445a00105001030384e80010700340c8a44020038040d20020a00c000030b16412410000c002a41c81902204500c450041940c0c2181c490380544100b284984009941c8a0542d01541810340164103d40d20f02d6070100b0591108400f004090040050701d40000b00d460701440c460040604c03400951402e901411001300c4014590050080000c00c4c0100344070405034011515482c0036200b80004121814010440201d5003842031492002040c07000c240d03290480c14800c04e40a1240d81800241600020f200c0d1081c06030007200300000d00f07602c0030740ea046e1501501d030001c4801e00100f008003900243d0304c655110b8030f002081101b03240c00e40701e6107000600c1e4819080d018180152075200e07120f1040d203070001042152001c6a00f408000844088080144010300c900003501c03c00e640900342c1c0c0d040062a0941c0001c0505010b282d15030500365104101d00a1081140c00390441c0e0030a02c0325402414515170081c91602c01030488034000c00f408012809801c180068164200d05000341c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 158003669 1250 158002419 158002451
    0x4030e0a240807050306030c01180308040e3106090f05030a03050105010906091202100e0306100303020d03050f0411031e0105220b07050d0f0c0c0c061b0204 69
    0x742915181800d000d0341c12039030215400070702003001c000a091100460320107413250080c1d0303014840080203420355000180c01510302405291900300100d9a403072000011811782800340004029448543d1520b2411202600e4940e40101c1d980e00104080c00091401000c2c00e40040b07482640b10400184001c00c07802c02d07510803030300d1b904000d03c24400022161180c0e58540c2105049801c00c0c0c80c2c20040310786070380095030310807a075018950010024800c00005490030303600c2c121040040e41040355000039044046420418100c440307404040c05070500b0030030150304020240702e000d081d180c2048507013460440f040790414080c00241000da400011034015075014090120420211200d482e80c09444032443c50103800100c4980401d0b41c0f05e10403071503490032000d099005060344822000c07602d994020341030351281c001c1014981d000d9910381541480303850030b104039100a0745a0300c4e000c0c1d04800ea494412034909a07034109404100c03120826502045469243c5400180d040301e021030611303a4410018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 158004919 1250 158003669 158003689
    0xa020a020312070314060909030a050f041505040f05010801270f0f141008070501050d290439030e0105250e031f201306080c0304030e 59
    0x40032100d844020300950f190554420400010f290400003c6640d983c41000380c1503000301c0e5030086503082000440c4000c0d00c604010f020003c1c0ba52921400d150f11044076241b180c801309641400708200203024400c0060445000340107082c00d207406403d9604203040d41c8220940c03941c2c9603402c1740304a10107600c4109150407891001c100604100841c060090346500600741086e007104402c14a60045845420900001d405803190007000703180d170078a04001110180c0c800c0840f480020b030345d11a0503840c840801c1484404c102a01c0c1c0d82c1d0310400380e41041004480a40e46042c0124500d5951860104445100c0d2040d1018040796201c10300829001a005400202d44205c0c3c1540b13018100b1071048050028030280c8815402151070202509070141c03200110100c4860307150b400700b03035407425000840100d60340c0f0701582140403881c1283c8804012002890801051100720081601c8025907034035002d03800109458500140942084280740c0260703c8040c0028003040039148040ba0541c81755040340d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 158006169 1250 158004919 158004937
    0x307020a0f08090a05040b030c0909101109040c051204120c08030112031103070b0f0c0403081930270503030609152d150705070605070b0a020a0203 65
    0xc8950031a40e14049400f80d000105040c400e40c1040004520350a0510528a111401034000d1522406500800c2420360000300034003170522441d0140380d1024624040c44440b8503020800c15101e940d103038100820b80e40003621354000c01c44c00317000b0700c074038006118001c6400070781082c1c8070780400e00c4000701160401c1030118003602c184000030001590040b008440c16072640a03a0b50340300c0d01e981446201e41c40344140c4002610010a80005c5551046041d194a821032095508103241540d680c0d00c561594111900c0600641c85161008200b9a004400a80d128170104640304041c80c81d007441c481c0150510f03002051003030303440901c0c6c0e80c82141078010048980d420071a40c1d1a05c162443c00c42d9996004841183c06101448046407480d00c50702c10642c41800000e00300d1031300021100d101c900c0d0030601c00c5128076075017110314461071541f990004e0b00c08a00e0101c0c210ba0b9200c0c094241145440b000e54056810013100b00a40008907072140e1a071034010590344d10244c1d030340304056012480e41c0105814 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 158007419 1250 158006169 158006183
    0x31e0f070e040b0c0304051005150d21090f060e030f010524060319090f06050c0702010306141c03021f0e0d020c090a0b0d080403060c02071215020307020a 68
    0x300d41c0280c0540c5280c4594450b016480041c0c0d034000c012901804203440003015640038600d5004002e102d41c101d83e520156202d5003580004010b800144001d280c00070681e4015010500712001c1c2c084011000d82c10240d1382041c600180c54259446440417884c41000200300101445040e550707018000b80c0500035007200280032500b86401e02c2c80c1080514100c01d201c00c0700604c011131041c04e112094034490810351040010b46001040600c0152500304002c5070050054404c410024042d449114010703240c001d24107032104458400035013207810542204808580c90901c6c2c120b00d540744400d03078a11004041d408941c03421540340a1307141683d10341c5030301c10f11071404408541d221015409180300c41f01e01411114000c406035000d90302d034100c3d030507001d4200410f5400144018501e400100103190081d011a02940943d21100c50039001600300310385180e15095512015a0f0410000300a040c0c50954139088000c40d960700c01900d0380000c0301d998000d40101c00100840c0c001e00483e8204c40d08051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 158008669 1250 158007419 158007433
    0xa0b030103060501050102060106030c0525061a120a0c0312020312091f05040b0a0b0f03030316030c0f021c031b020a0c0603150504090c030f0b07020106050f031e0f 72
    0x6000e9020300800d001d00b038018460323200005000340c40380c01134a0406034562203461818134076405022804003141e00090100c1070040e00744000850a00c208882604aca00f01340c10340042da00108000780142c1c2510000590240c044040401c25000b1150200c0f540140c0703031011810044001d03130550213545814854100504200a038441011034070440040da28803401e240b260721041c1c0c08003101c8090b14003910905e50100028031245141c0d2064600590041c100c0c0511010003000171f14613802140c45400d2314041c1d8583c004d4030394142c003402c00041072a05068002a01d0044000c1d074404032194888101e100100c40644e455020303501c101c03402180d140e41207486060129003c2d40e2080713a8501150f10161650000604034401d00c50440a02e1761000b07031076901032400c01000084c0c05601401d80e4000540940007001070b810700303002c00307141c1c0c45400444454604508082e007100d100d41e01050284800301c0017484695008524100d4562900f03040d80700000038a10260b1815180c503180c16100d2103085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 158009919 1250 158008669 158008673
    0x130b06031501021629030403051605030c03180a05030a0302030d0b1c05030c060705030601020a2301020310030605060d15051302030f0708010506060c0c0d0f0c090501090b041407030b0a0b030103 85
    0x1000e07442e0717032001c2190304040002d40c422040d824801260b0280000307070b0600040c0c00d18100418840c035641d0107030040303030300304810864070908590054040c0d8007851001010b91a0328202100140010705080f0050a03103403000d504c001c3c0d164424500d418400703955400ac400c00964442c105810302039040d001880034500d0342d103440395980e0b1004507007044521495001640b040c0c4110304580c882d10060340900264000307a91200c00c0d41499107001000014258000d840500d82440554406c00315642c0e8490b41528501780f950446801405407801038100600c0c071400b03d41301d50000020f529043d42d000585036a00c4451000b40700a00c40001c4d8140076400030350004c000001510000e54142c100200701c540c80d00c10410060f4032405030809000d81107a8020046441d061402d801214060300d0460102100395444c010154055001200f60903940e80041c000c284040c810354200b80b4046d901004158200b00b09032803c410014207610030503440384840d920588408005600409005c41034944950b128 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 158011169 1250 158009919 158009939
    0x20403060e0c0406030c150201090516060906050405060313080702090420190306020708040810020703030f0209010e1306030506130b130f0605061c050a02130b060315010216 76
    0x2807036035416180304401d0b203000203280038800c1c4012664041110780031603141c06506e0509a00601d140302c195507035100322601044060009400f100d0b41d42c0300d401c1070281000301c09072448402c3e410080800ca0b00303010600683d1500022243c0100307071850060680b2586240401841c4140c40c0c000350030140030400d10040082480c80d0b061034940440050385200c1415090000c2210b40e0304044002d444545420000b2400950040110368000e02c0b050740b8050300c40041c9881c1031a0011014401640001d07a40241503151044c015130161804003940f402100b000001e117a5010800342030300c94010a006a01d052006600010045601030b040e640f10345405c98600d80788111000f0309561080240c000101410141010760300d04503403041800c0030000c11620385d80002d24000307010f039800c110380031a501d400701c0600d0302407004030b0b22034001400055414410300c581919000340d650302e403034103000e030034a00c40ea070b0a0140e07580504035a5444403001c4542c0b0040703103011200085036030400c0301c03240040740070000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 158012419 1250 158011169 158011181
    0x81603031d03090303040b09031e070527060103270803090c03060103020d030507020102011107060e070504020903030708070c030b0c0301060212030c0a210c11011508060f10080102040306 82
    0x101e2440390595480c4010100d40703e11550410981c180c01c00c01040c000d00845001a05400f2000340c01c55003869200c41d440d00105441010480c80340e84295810011880e0007880000c0c890003400c1100d4141d00204031069043c1d101421542c1815180d43d1900790410002c2d40c1310601d084202141494034000d402c20b00340075030090300e5418440c042e0f01c3c510ba0090400180c024100da501400c1d24000c509180c90440340d50b04030080c00c07411075485a00600c0000b4400c0e000c0c250143c01240000388805103442d020f4607020941d80b0543c000c2e4014010030490303640100691700c4098110f4140c1e40d42c1d000f98582070790701100e150002000c003407401007840b51840c1054061410703565150215030031001128824003140c0800c4403940142d80d42045611003071480344250041c1483c0381d14004882c1840040c0384402d4490703d0f010800010b48101074100946824041d440312810b03001703010100d190618801b40c1e01c0714002001c444605c207002c2d0100c0d8096005541340750013003001c40021911280c59140c00300203022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 158013669 1250 158012419 158012441
    0x102101d1204080d201e1902060d09050c06030c13080316152d06060e090106081f0b090f090610110a0c0e04020102160e0601080408160303 61
    0x205500c072284a845031041107a040e5212040188010a2545812280091a6005045c81500442d000e01000c10304200003001c07940508074650080217440350781442c1440a108800d81704d8110421171001d80c6508045950307800440c88086114581410301c513242c0f038200030b61150811800000c0106404884002d2704080006812000c0340d190395080c0d05581e801000c07072400300120075420300000102440301c48000942d010740c3c04a21f40c184001441c045034803000102c401c0c044a5109604200c1c3d141c410b02c4050501400c0c40009901c51901003007500e0b80c14048c00007400881300c04540b50f13a00b0b121710100c5101c00080000581034450b12000866000481d805008010403075900070140741c41d0070301900c07840380942401d45020361004101d444003d0708400c100f850040440a201103254294082d01030700c0c0441001501c5e0510b403000900d80f4101d40c402000624030340340e0502c001d454900900f03401140c05d2030420810786441c200040a07205451441145203000d04e004010540c054000c7c000d070b04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 158014919 1250 158013669 158013673
    0xa03090c0b1b030f04150e0d030305040204060b0c0c04090c08061905010b09030a06050c1b031b1f09052d0105011a0a14120408030a0e0a0b0103110102101d 68
    0xc40400b25542d079001d400c0e801c0201c3c800601043c400c6540d00d184040c91400d291400840c2d4140040c041031024050407816000642c480d0104825400c05028140042400700441850111802c04540e200d140c003041d5948102c1c1c440c2c2740101130040f8000b001000d4a0114180c850905200050083c08005000e030a6803950820000042d41044003040d10981c0c14050050300c5003a00991b15175004140c000c100e001c0c5a03030b0500651141d812200403001d0034010719001143e84d40d6807211201c20040c1038000e810459801a00d9280f07940d6280084c50307119006415010900300307010f2a015003062400f00c0644104c070440b040c2e41103502c6020b03200c002800001c0c00200510b0740c841210074a051f01952848480c540c0400c40000598882c00840c4200b4003d2941e49090140c458140180e00c03c0c242c030241e0741c00101006011840281e03208004c0d803d40600d0050800082981d0f8540c0c142d00148400707004202c000f21203401e164000d010422008040610401c40003d11a69141c1c1525041000040314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 158016169 1250 158014919 158014957
    0x30d021507080c0406110f0d0c03110703020607021509060f0703030b03070e0c1c0f15060c02030606060904230114011713031211030601120c140a03090c0b 68
    0x1c90041400500801c0d07800403031441c1c01d0a042d400ea40350040903040d00b01b031707200b640282c1c0381100060211120340b00f680c1c0c2d2261020007050034007c0200d40708107c4500940c000a2003000180e5822003107505190b070540e40b12400038400c42e0110158054244142c2c3c0190000850120340040200100446c0d881b07030b1010000246680b044c99034800f02401910b081074200c0020841c642c1e50140580140c1d150040101010704800c01c221060301c1c4410704011441d070f02c8070400c260000803c1465006800940742c0851510b0303054001070340d11074015190a00400c00098086023585071078003c0300b6500d0641d15881c50000e00401d455181e52000d2207012050040761040c0c034411740c4600d500310b02c0090900d034a180c00b910b0360030b0017034403006440300200d003803217005019003080300c905000303400341001c09803101500c9240c150300160900d816403100400851801901e0f01840342c1004520400010180d18952203116a041c01d50003403030150405440540d607041e002450a0a0380000d103408540d100744c0e00f080e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 158017419 1250 158016169 158016181
    0x120f070606090e060406180807120306051203040909031b050c01031a06070b0705130e01090f0b0102030d05040219030b0103060c0807020a11030307060f0b0f0901050109170a02030d0215 81
    0x403515a04641103503508104d0108000c1100d0b6000017580c0418000c880900482030783d10030340141e00c4200c08941c800d10728002c50010540500ca0840104004c0c1c80c00c9900b0010786e11050303201d03c03c1d8040d04015650b150511814940304082c0d405042416180c4821011000d007030084d520b00030b08042d10700007030400c0c8900382d00d10b901d070003450498900a01254140111942c907080e00d21f02c020004010000244001c00d03100b030800180d40020010007080443c00c0d41010302103820388a15042450030030381013002c445070999000007250384030180384400280c161a6440020429203592481090840c02d903070011040c045200141c0e0f040342c0c0716180030008004204400c0c0c030060012580c0301d02503044140224042500351420383c100500003400d0364030700040c0d5078541003121143d41c1b8071308102d50384038003d20440c2041608800d09000440b094507080d03240c0b0300024404c01080c007510b1045481d42c1c41024071034108008107880b09030b00805890180d1a8240001d554103c140381b81c0ca00d14080b1400301d01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 158018669 1250 158017419 158017421
    0x5010e060907061407060b1c1106120103110a1503020a0201230106110c03060f070f03110328060806060a1203080417120108030406020d08060303040314120f07060609 73
    0x4115030850312250303a19100d51401400d160050b03001070f0b074916212082050103948149000d1b0751400d403410150341854044c03c000327031940251400a400740d1020806000612421880241102d42c001d01c0c0403002012240419041c0800e90300c4410740940407a0264442034064005d0b180181881c1d008100c0254000e42c42403600b00e515070842100c101440c0144031446c8180345d40038000c1c00d54011580c001d28241c02103864981d0880300280c0e1080420140128558404501c0325240c0651906100803400100034440c00c0c4405401c070201e001e01b0321480d079031100e01450700300f0140414603810400c055031480b400307171500c0c1d00300c0d0b030940f041c1502a001718100c90602c0c0c1c1c982c0300d40d400d541c4011050303685039a100d10a0416000d50001050144200d000c482c1c44445007602a00241d0044c50710b591522401034034043c011a503001c140f1210000300101600d000080d1811a50000042c0c16020300251180e400d000041c0c4040c840601300142040402a4001c001c0c951244130301c000b0004980e4840c1400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 158019919 1250 158018669 158018683
    0x1a09010b0c01200403120c08181008100e0603070e09010f0b010f0503010302040506061b0a050606011d100309080a0201020306100c03080a11190e040501090c0203040603021c060305010e0609 83
    0x103142c3c49043c031090000c41e0040b0300711218400f032800d010782050300c66142d500164110320101c00900ca040802c07040c3c00e0070042243c50742001d445c00c18180509000e40c48e0441040503000d000580b0700031000040c0c065408001000082c40170100c80c2e51141082e004e402c0c06807190b00740b424159811303c101000d25501c50700c036004c0c00780b1081d030350750b42540d003181d0800c0081d01003e00050f47c0300c1000d0015100c460300e10310500c1e180c4170350b0b0402444a51b20503d821130800d01c005104a05000500d0704040d210500800d0020980004032003541301a1401c400a80c01821000c101600ba445c1c08500a105079405500550241c8000c4a054000c0b51007100d0403507060b040e84100400240740c0c0004920700721800d400506401041e080080d0505281c0803220f141055450000800101d00710940c1c045c071308281c4541405060f01620500008070a0350000e9034030b21407032180c0b02c10590b00041c1e0750750a0700d6200d804100c0d03d0500c201030004503540d060243c007030890382034012480d008510200340600c0d00000c0d92 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 158021169 1250 158019919 158019971
    0x1d1c05090a031403280e01030e070e130c080f06010f060f050307021c1706030f071205010216030801170d0f0e04180f05060c07030e041a09010b0c01 65
    0x20605411562800144002c2c1d8025112620042c071214545102d41d401307005101010b15030714003030035070f07130346001040706d00d010740350505140c6041001074110b10081f8a2000b0ba520070040f903010380c2c482100e0030041c2c20302103902038003008249002117003800340803401c2c880741c054040450b489a600d0782803072042d606042c4194000b00744003030140c0c80e000340104003959221000e0300548442d1200705155049840c07106c0c1c0e00780005000004005036401c04200c00c660000002d500804c6031480c0c00303540c540d445529016000f900792060110100b00a0250100c0c0c400844100b000801c80b00c0d54640a0701e1501c0c00e0241860342c4110400b002c108200003e16841144540c0c3ea81007001e03501c03900180c801500c0f15202c0c60300b0640340c20042580507000c2c0f500322003a0380f00d4448401d00c00c2e41401c0c103505101000e030a03035032950360030495030000c640d2140101c81401c00441c0c00080310005031143c640404a03516010f41c22403411800050703042000c00c0030b065445900b00003444400005900082c0c3c00311000d540d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 158022419 1250 158021169 158021179
    0x90d0b01030b0a0b1c1401060b04170c03030301060503060a08030c0105040b1302010905190305010e0607020c010807050d0f090b0403020d02240c0705030f040909020f06040311040b01031d1c0509 85
    0x42051100c20056140150741c01181e420030050502e501c110b0235a0000d40020b0215000001c0030800a403031010020244c10049000e001c19801640000b034a80c40184503445c1005030110101d0603030303510902c034003000b007040000b1a540c900310b01d00b545002c0d081c21a01543c034008008005031503010911403c0040d40d6050395aa60700c80c3c00d01042107118505000c0c21084401c0040300480000d60903c10b1000c0946144c000389964503003080003d00e0000b209540713504100002084c441c0c3d01c1e0300a420345019664100021540301c01c1e483c205001444803000141c10a0071140501c400d040d004103440840740055820360340d0007e1103500d4011081c003a411040b0f030300e034007107000034501500140c09410070380e2060080d2460445030401848840e081074001c03584060351540e00000b1885e01103042c02409a041e40c030740f801c0524645480c160b80c0346400032070380603c0e100c0c05400704503031180d400710221b00146c1484e072660304009880c8a607501209800151000003540c9003000a50084003615101d82000b06 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 158023669 1250 158022419 158022439
    0x903020a061b02090711100510050a0605180102010f02071113020f0d050c0403050f071509121103150a09020a050a08030f160b0109090308160e01030e03090d0b01030b0a0b 75
    0x300b445200b49000384510b040006075088140901403d00002c0c4100b2074844001c0782274100515001c080d05a5035018620560f1152010000c2c01e400205544281504500c01100d0301c1040300140e0141c030420304c0c0c544c40e85100003002c0d01044903039215203d40301010340b110b85070031400021001c1244200c8500c02c80c050014841d500304400300e41c04c4a9407145030303424105d0a103556980c3c2d042c600080045400c1e400e0308200b4080c0400d82c25000010402c4240b490425243c610701111040002e03e40080940384c80e0041c560036416840030440030403d8691800c3c13032201c0d45411000c05004226412040784502d04500c00000c20346070540800050300e60200180d0b01d010b0501541200542c800072118005c040001c1d44040420310051a5034024014200082a5200c8034070300186071413130060000c2e002155444050070101d9100760090034114085c200000c52080038044036245025000360183c0c004020300781c2d41d0400c15a001c03140c2c1224070a61445185880701c44800042d208004000c54100c05021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 158024919 1250 158023669 158023673
    0x4150e0103141f050a0605190207050d020d020103021e03060a0e01081203090708030c0c04050601021603140f0307060c0e1503040b04060e0114010608160518010302190903020a061b 79
    0x40c510780d000c01500164283c950b9a03c1000c183c3c0d01c0140d6012001142c400b00704020103243d9405c4070f5820f43c44610103414000d040000003100120740e104013130301440c19000071000310390080d8121040f080c89405280580c1d0b11644403a40143d0003110b00d503000310404800080c0c031000c44081941a1290400542050b02e060311a20090b60001020501c0d1881440c0c0c00080548040c001420060b522002a041030300b801c005100035110083c2c20b0381c0c110344c48501e180301e04c80400003010060b43c1d807116045240d1444400716900e0007401c40740540e514000041c00c5001c01005612826112900342c4502c000400c0004c100400b2503500c1d0880d001300502013001a0004030300007080c552140c400c0c000000e03040341880d000c0703084654810046402a100900600036113401514955200540300c4220a100700c0d0810010128080c1171109265035240201610190b0b000b50180e90092025200f4001010240c80000b4840203042c03000348d000b800f24500100f0000d2003009481411380c3c000d03c1e00c94000c0f0550b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 158026169 1250 158024919 158024941
    0x504021201151401031e0209041109100c210806090a050c030c07030c0b070804051506031b0f10051306052b0b15040f0e0403080f091204150e010314 65
    0x401c3c9001d0415603680f0303801c030403541201120002c0489050300141c9513901502404100d034a14451903190358002d000851255441e04420340c4454940d1800250a43c1207150002418074510365210f0b9080e844000ca04070550310a8140d80319682c00c8400400c0340e00c90160782c000b20780042c4c4e0340054206081001a003082440c0c03000b4201d01e8800e2500660115003034440c003024040580d40c9500180c0f090050009100003000005034241c090848030130305041c29400682d40e40c82c00395140c2c100c6154402e0f01a159030b100d511421a0a801400d0000030300400300c002402503008400320301c0d0030300440320b01007422442001580e0041d60000b010006102211400d070300c002106900382002e95860f004000b00a88540c44801140c1d100c0c00a61501c0720b0400000f0640d4207500e03001560820b51103001c02000c603030300400980e0008001049000c3c40d841341d40e01c0f0303401c0030000c8512080441d00000c1c0014038545807848400c2d5180ca07136440c9004084840b0044003920000003140b5502c03901e500110700780c0105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 158027419 1250 158026169 158026199
    0x1609120c09020f0c010c082208070c0306021309060515030a0f0f020406020c092202060c0a050607031a10030b0301060f030501090c0b130303050906070b0901050402120115 75
    0x1514032a951980d01c1c0100c07002d99112284034401040b0205100c1c60b01d03032003400303500760b03500b01410940c0c01842d2034106c02548924040c84180c0c0e10003e0304c02103060141e00b07412903040c150011003d0744036a4a81c20640042c0d0f10072110000c5c1d5642071007002658620074400d850596034000c20714403004030b0403141d1522a030409070005498640d60a05500200058880d100640000c1d10f00561035610307050020f0700b4454050700c1c0780c0c0100d0344482007010608581410a2184a0340100e0741254180da002003501402051048025449508104011310200040d5030744280c585650034452520130b464404500640c03000c1550700326410064910744a400381d0068141d286020340002245955164540d040780d019038000d540e50307552590580c2c10300c440b4442d54400f400f10b06842c82e240500380108110303500181d00c00a0100100494451910350b240700440d07282982007c8006040d0a000c040c0d00c0c0241015a030407031040d1041160340784542c0060240ca8141521400d050907140d1405001c905050f030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 158028669 1250 158027419 158027423
    0x6020d0302130e15040e1603120e130603060b010903020607030f0201110a030f0f05090a1401060b031609050306070f0e060403140d020f0c090601030c0c050d03090605160912 76
    0x718081003c90f003030100d07803140c1e48560389400c80e4140a40c01107007844100d50f4a0350810300e95422210140c0c4800d090030080004490713010311001e404e5803000740300311400128440303001d0340403001004d080d61448098002c40c0650b8003c8400300142d0b0402c8006585d03002c450720000b90094018800c5c00082402200d0707152606550f4000440c0c40510040358480315489403001402085d50b4140c8802015840d00c2800580c440710b81e410401e50501c09141c80c1d070307100c03411402007160700c1c1d10360705580080d429000f01000f402c45c0042507031a410510b001003402d6805c60540360014103420f400059070b00c4c0003d0b4007401000d660702c44c01407050005004076140700082030a95080340c010000040019132020304140200024806802c1007030f94000000e08120b01040c00b07101d0381d8410012260036540c0d07441d072a90496000d081c0003900c1042040140c540c0c0c00710000c06070103402000fa00241498054100700e505504c1010f04001503a03400c00000040c41480380d91200040e810364040c4040108490410350240c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 158029919 1250 158028669 158028697
    0x9060406150314060301060b04180e0703030e030c010c0206180301060314031306050f1b0f01060b18010504080703060203180303070e1203180402030c0706060b0702011806020d0302 79
    0x1615000c00c5026011407040341d0000996403200c4101002541000c1504400220000d1180d03924106105115000f5400307041d508503496084e481d0481d403140c0c082c00441d00c001096503401c940d6410302810b42400303240c05901a02907001c00446a42c400c0400002c0070ba40148018201100a40207810520ba01201c190300356684080c0130000c070705150103c0c2c0e80841240b00446e40d4800c0581c0b0213003503140301d030b02070f50511000380711188069010300d0030351340d10491060483d460b101a1180c801e15100c900b60a241855103000c0002c1415011b003401001710b140a0f0010100600080d0b00460300c074821881081c096030404041440040c0329a001107401c4440d44416500d036652480c1d4040c1190f01c2580c0c0c1c00042030220402e0384541c200042c500d01e80c020715101030740c14041460f007503802041000403400c3c46030780e0000000d40700e1510442520080c0703400540030001c0c02e44602003001c1c164004c5800f41e002c109602c146a800340c0100c20f40200352005903000d40761110400e4401e42c06500400f50440e914 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 158031169 1250 158029919 158029931
    0x80c0906070510020415020304080a110117130302060705040303020712110a08060103060b0907051815040303020c150a1421070f12020313020f0a0e1303110304050a05090604 76
    0xc200304000080c280003207404011703512890710341651003411b0001e20b803609640081c041081030181c0030038a002d007030360044000350310450300c0401202c4581031501e82400c2e02c4011420700000c0c0402007144d1013814442c1d001c945807500d03074007404e48480c065448001c00591004005100c0e50700495210a5400d104a0750a20f00c0300b003250006103002015003246001c4da01c120010400c1c0085030085169001c0243c40e00241410004001029882001003c000e02074210b601402c90391a6050f8038103040b050004559102e40e2a0b1400a403101da0f5500002c0c41000e44c40035290200500c00200c90000c038003600e0359440c030300c070070020384907107400144243c10440c1c03410a4101200340226a8603114030540d690f00e14001d446402d02400360b0034605400e0340143c4c814030401a24410000040007442e80444108980034165000030703100308481c0e0403000e1034008010074405142541c3e1601030b903642c842d0315001a85407158807a0303503907402140f1400ba4051100c4004005034142102c0154000802070000305d91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 158032419 1250 158031169 158031173
    0xd08090d05030c06070309030e09070e0603161103030702211905040602011a031f0b031b032103060906130c090515030f01030605060a08150a110901080c090607 70
    0x400303103100d2003603071036400026410410301010b01009a025400742001c100b20a00740e200100b1050404544501590001c0d021441c0c81d40a6201c2c8400501d0003043c0d070f6036a103450741c800c803d444000c21050300480c0c1c242071512107906010003507038801c21003a0f009010840d0801455040c041610380400103015080103100d1004203c217402c41100c0181d500c92990742c0b80307031410081c02c4805190303034206815410005507110781e6020034000c18550b40c0e20b03400e10b016034000720004020490582c007039500d0703c644108071100c01c0c0c01001200b0b03114811819220503a40c54000995000400540030401c0740702040001c10500e403405800d41c0003035000d0032201e03050700350304c00c5807040714255800040030a4040c40100035900c2d0440711000c2d06807442c1c3c0c58074150b0800e107074100414041030000030139140d15440000d09641790805c24070000e08560f021212070045806500ea4070660a503401c00039103042001b440510310042080756464603060303440d0905983d0782d03007444900350001c80405038085000c220081c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 158033669 1250 158032419 158032429
    0x2150304030503240312090612150f0d0302101e090302070e010603020f071509050307030503060301051e07080a06080129010c080717070c240810050d0809 68
    0x1200d640710ba01c807541c0c0c1e401c1c00c2c2c00c038049506011007242e00e4000b030398603015000d4901040ea01061182045415113903d004000501c00d8054a181d98038850102d50030030040840c40211905981400d5417a00c010810031801d00c1084035110704040d02680c0084a050010785c21a400904c00000784403005400c0904024004180c5608040580040e481340105101c10000420032600400090070708516118855981194a000d0640058000103c030040c0d41c08403465230300803405071075020060f04e60303e000e0780c600544180c0080e01c009000c0c2d0300c0d040c0018180041d428440c001c40204024240701c03a170301c1c1c020450303010400034400c01185880d45000502042c0901a080c0c50fa03c0c8452800380201b03100000c9070101540c00039050410827032466007008100d0060849540b0358200801411041280304600308074401c44000400150305044002501c2c420030302e4914070356118102d540342624000e401104c40110a6501c581102240c0b4810061440c0564000f4101449415118280200100058 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 158034919 1250 158033669 158033671
    0x61217040315330306050907031a010602012007080c0124060809061012060207020a090f0e0105060109050103020903280b01060306080c04020c03160602090f060f03060d021503 77
    0x599152180f0110340400030007550328103000310082412201c0c0c1d00002e42481039200038030028090300d64510204040d150305205000107145c100990343c42d0740d40241004000843d00b441794030015440c2c003003c00c1a2410425452410000e1200198100029078581003c0c95201c001080c000d03641e03030701304c1c02400001c05110103c01b400b80d905803d02a46480307005054080028a1100d01d80c00102c00c00c601d1213010088001034510144400321803a410740340040c020300c290709020390b12104291300021000c0c4190000002d5071541d000901011800d44109400c2e141d06449050116503150010b100d9540310350301500402c0e0b0000c0440b80c3d034800b9000c2d003200000d00c0480f43c0320500450903904007030000c980200c41c010907803440d04200c0ea910b000c00c00c94441600500341d5100d035400080604030104100259203422500d60f8080812000c00d10b0010002d6104600150050180022500c1a0318001003500c400844854490307140d556142c1c01c000d034074001d02d1000c0740e202c42500100074070030381030310055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 158036169 1250 158034919 158034953
    0x90910050f0105030903030f040507031a07030605120c0402030721020301060f020304080d260f0a1107020109052704050c0406090612120e032406040612170403 70
    0x11444450418041c480e51050056807070b810310408009219102400004881c1d010000c00954030b503580396468941d0800d102a030010748198410100503100401c04c2d02440d01859094508001285d9a5410312921200c10220000550040080c41030f4a0030540c009581c06031041c03130030480001902000b0038045408a005900c0b0741d501000601c10303650080a000d020103d070f80000d50506190104040e943d212103d219400c000500019040400c20f5001441400c072100d00e6000c05032074030042c0f448444004031210a0b8083c209004103201101350f07011a9101901a565007403443d0030300050000c402040c0160300102c1242991110480801041840c0554071400140c120044680100b1080d2051500401c24440c6030000070400041d003e00c109000652002c09000d989402140507140000702c0c05416405004812540c42101c1c00110200394004407a900001c050b2180340038002206e8640c001e0903586042c195104d03004c901a080340c0c240480c840c1e08c00381e06c1c29842c1d1380c514004540ca440c0d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 158037419 1250 158036169 158036191
    0x110a17010906050601030905030307030b0f0901120201200304050105131505070b10120204050a0b030706020304050406090c02030a0c15020703090801050f0c03070c060e0a0506040c060f0e10050909 86
    0x18140810402c1c1c003945401550929083c080c11220792191038891002400e010240351f03440071465620740350844001e9440310000c1c00e40c071007584d4649840203c050035420803400900352079002c0d0664078116078030294a44c0308000850605080900541703241d44414180400004d403681c00080c0c0013a90031034905410050740c0c031251203414618140e5080340018014034003140400c403041c001001c0c01310401d0400d40c0c04035404a05034540340c600074020540c01c03107140c0d058015a030001c90715540000003401121000d94042101a0b5644204e2049402d00000e101c016041040b084504520411880d03840c0d81c0141e1f202d40d001c82034641040c040340d20141d011400f00701c00e40d20030040400207224450f80210203000411140c40d000750708040601c4000c1c01e20040c001221280720030301190707a10520b440341c090301c00c917401c01809040c0b8503076810301260220703440c2100b002c0100c0c003039108040d1000c03501c2d281d1b29540010141c0300d080240000190141d0703010004244103007200c0b030b9601180b45010b1565260 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 158038669 1250 158037419 158037431
    0x13051501061112040509040f08130801330e040c09050106030603020114090a0b03100902040902030f090a11040c0e04050a090308100e0a09030203161a0708010303020a110a1701 77
    0x1e0090070580c4415102403c4082071100300705989480c081d0540c00340c0c3c1b0200c5c1000c0003116140000c128010643c10100307401c00c651000c5000901588900749041e00304080e0100640e070b10b0000e1510100007034000c012030b00000c2041010a8001203084d402c240708030345885c03180e80c0700e0807580c003101c109920807400a911810104190350b045050741040303982801590b480c02d0b88a00101302502024482c3c0d041582d4000001210661040300c03076000b400e4109401c2d580c840c0c2d155100c1029400c25281c1c100c04141c0d020100f441e003500010b80c20000380e808440c4108205002c1d08101c010401ca241440601030f0840140c2d4847d42c031440340358440c0b01a940d00241443c01c50030014404a40240418064500504244003001d044440282c0c01007440001080c500c04614040f405e6004520f80401c8400000b0310381020081c0300c40d9a102041c4d1441404800d603500c2c00011695600203110240140e00034640c1000440c01c51001c0300c6d250fa00c0034004484a69442040445581401e03290342c80c543d540302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 158039919 1250 158038669 158038697
    0xd05040308010506072012070801150f0501080106030c0c23070609050d0f06020c011401090f02040317090415180501050603010302010e0d03020709091124031305150106 74
    0x3410705405003605440c0782d1304013030b100d546202001c0d060040700c0e03440381600280c40c1d445540e581c9a2448106c507202c2a00c081d103641d21a07a40c041c016010480ba1008041000480c20340c074240d2400c0100c40050b500d401881e403900f242034008211248042080102c185c0070f0802142e40405d01c0306501400c00003a9140e0300200a0007820301382c1c2c6401c400100018440c08215580c0d584451910283d00803688a44011192805400078072903107071548400d5007811850b180f10b0a0145030036040b00d50b502001d08c020400408500104e104500006203440040c0301c0300e4420320b449401030907281d07002810010320038501031024207100c8441c0d40903a2005a1503203a084006590f8003542e801008103484039400c41d41541d0028242d00d0032450444c1c014080c0074280c2083c0740c8200a03000082c01c00d81c20822030b000d564103048460100000f02c0b10f00a086009240c1c1c0a404600d4880389007914821003103065843e8407820744440790345000156401d00c0f50701d4020301c01104541030b5034002c180686504070300300d10038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 158041169 1250 158039919 158039927
    0x4020a0503070f02160506161a0103050d0201060b070311030912030a030e01060302031015090203070333170f1516050a09090209120d08070201050a020403081b0a0203030d050403 78
    0x700b0900f0707045410402c54840f000080da0104402d0b10012100580c1361100c0c82000c080740c10a0304400f07407002c1300c0c083e03590301c0c89850540e005041c0c034011000c0c1c2d0a2060044002c0e0309035641c0344075000c1018410004070010034031401146c25a009400706883ca8801c1d0000040c906031408101c03a40650000941d1900207509403007201c0c80c6a013802c000f030042a203540c0000e51525000d05221282070b40342c01c5064410320441900f1006022103150440d140e041c50301000b0010403000e172160350301010301048403803c5030b00025100c011032000c00703400006601344517010380d01d4911541002a2486010340020710440b090120b010802035100e504e0311030f4549080a5038825004a1031178040c01030070801c00000315400310111003034500c203010147e82c0c0e52444000c40c400346a80c840205090240c0201e003080507500c034051902401599009009175241c180c0040200d10840c0310003441910200107406402c130399001e2002c00c01c06414165a030851240d00428110b5001e212000311055840c0b08000800d600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 158042419 1250 158041169 158041187
    0x6030b040e070909060e0706020f01050109060e070f02010b0604030b0a0c0c0510020a020a0c0306090309090b0d020f04140103140f03070308010e060d051b040b03120915070204020a050307 82
    0x11642442900ca501c80107039101c100c01d00078001c91503140c032543d00500c82240c000b0031050340080115000c4590b40c0c90029154040400944825400c04000155034200381c0036034010385a4000d201d0030140c5643e9016a0340055600300c081c1076549840c00460680c0d0b030b07440a0802580900c24003e100c1c505101c82104890440c801b480a02403070b02003150109200049400c41140081001a500c40e0130380700607413030a8482e440060521900000101c1000301d0340e000b1380c81c164031a895805070a52291118800d94800030881500044000792001c0545881500106203140191001071100307002e0000d03a405400c246c03c29141c0c0c00010b11141e500e44400c119141d500410b240181d41031459903a0001c060b890107119902180d140b00004c155695034040034156019800380c1180c0c10804141d90301c03548c100740e001956200f07600d401c42c174008500f00032410580343e040302211580340910300c90030011180d02406081b9034640050010800589070342c03004242c0b4074981d895203a201d28040170005c0ca1442 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 158043669 1250 158042419 158042441
    0xf071208100b0c0f030d0237111f0207050114010503030d09140f07061d0a051519080618040f06020a0c05070f051509030a061a0316080601050d030f030903050405060c01060603 77
    0x1800d201d06223000200070106002e02103140782111560325203500303551030031010700c04011403000d203444160f804400d03581c01841c07075900c035000900c03003950441c189054010342440b401d6015007041004c2c810320305056004980da10700c01c6204c0110003814442c15803509030b140304000360980c0040c0c0148055600040e40c81c0d1035140d07050115803c0303049040841e10601e55403007242d02030460044960310307160944d41900c00b0b80850980c03109003164101d80042121109440c0c46d405100074200d5100c01c55100c0024074800e40d00452640602145569100000e52080c00500204031501d055007001840a00c0944020182c4d00740c0d0358001c41c2000100800c0b10114510296044000c21030a4260b80700420500c000c9504004002280840146070703220480750301ca07071306505004441380792281a00010000381610521411074005030380b07510600410060201019001ca200494020706851080d0800240580300b4a003950810741d840010403440e0708100c052651310b0b5140d000a002c002d605214104100e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 158044919 1250 158043669 158043727
    0x804051206100311040f0c080f01050414040f02180103050601081204080c12120c01060e0c0a092106020a08060f0109051012110f071208100b0c0f030d02 67
    0x10600c1810b802c155030240c880108444802602c48410740c1e51a4414807a03828046424003a02d4007889006203805406c465a040f001390110010819091620a030340030a01000000d010a88580c1c079406c102070b20003101264400700300303000c002c0302d0400842d003c2d00a42c0705100403c01c550400301a54203180c0f0014402c0d070100400e00013009103400005d64003500d00300c1900d5000540d14240c201a0415100704070801900c08001002180340c10154440c2c02107075854201c8061503110050021130f280301d0605c9000000311030050070300040502c10040160742250f05034a0f10608003070758410060707800c0308908c40041442c4500308026818505100120408240303801000c0905040000300c142201c4420034041241c0024040c909000360781c00540182d40381100305865410314480152143e00540e01214007045103522003641da802500741c1350041c880100c407048040c1c2421540c248507000034401800c036204030780001703480a8080c4020034500c0c001180140c1d88a0071440d124800c50079124582c0403039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 158046169 1250 158044919 158044921
    0x50c01061203080601031a120307060506030c220902090c07030e030d08070f050403020a030c050312090a090b130f0c1106160e130213030204060e070806010f0c0f0804051206 76
    0x65440f030402680441c003420000b03a01050030f0715402e05140c1d60000503422090091041c100c07042c0c0003010b000b9036072081c6424000c90f60352505054407090030000541c1c000880d244940843d10010b103801c4441e2080c540c0004c0c26080e1900010444e41080d41c14041c2d0310f1002034004203155124052400c040d60035002020b402025540060201d04010700c454204612003140c0c1522074403400031100190740080100d00c1c2c158903400d0002c0303d0b251a1150500c00c2c0301d08600d240300443c090042e1000064020b010658241c40e0017880030262600021650303005094070007110b0710308014441d411002a541400051450241d2009001c3d180600709085199005108000316807a04181800407102c19181c0700c143d41c1c0c0c075480856150a008110660180c1c00400c504c845114000890bc0440e03008031021b00945544114035000c0344015580e100c0003c0f519800956154095401c0c202c0c03100b4503261031061148903441d450181e401004d0102d41450000400300520710700321070300303040642030030010f0003035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 158047419 1250 158046169 158046173
    0x603050f0703050702250f1725030f0b060301051e011415120a0b010302070203030a08070e0d051005060319120201060b030a090309140d08070204020c010c050c010612 73
    0x50100c018801420143c8580000b5840e601c02d2080504144484110007292241d01c80000c000781035a000b0301c925015403c0c0001a03d45080010f8103445c070302c00000d40a019141181c494000103542c90850410f110b0ba00c0020009003002e40300c14450380a5204003040d420320b44e0425003034810182c00d0004088a440c568403031810018200c0381160182c401444100b8078040c0802c1e00e01d200c80d41103580903c0f010a08407807200c29025402d201311840c550401110b800000154100e026a02d030103505a8070030302c684043c89001c2c3e88260b42141e00c2e0300b4502c0d01000f40d0300020b0703d1009440400c85441d0458501ca01080b14640600c1d50403407000c0380903083c4000300788146180c60000f000c012300101d0049800c40c50340c6000390700410192028402195403450007291b9440039141f0a10124006501036100144400300c048048a00c4003004005c98411740c0581c889800c030303410204050741c2c031941c00c003c0c298041000344940000c80b81c050301ea15842e460281c0c0c4007030844086a1003804800150701c60540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 158048669 1250 158047419 158047441
    0x108030a0f0e1503190903050c19030815030c0406120b240108070e0a120201020c010212041a090a060c140c060405040c05070501050103080c070f0513020a0c061410060305 75
    0x10044540c0c14402e500c0c1da44000d0550f268640072444160740c18502a071b40024140d200c00107041d00140441298040c08907200c44d003456240e81c40b0080e00040f1803402003008030710301c42105100280f0060450743c03502c4800c0c0028007106e21035408001440c607020462020407103c01c029a43c4014003560001a143c500403601d00740d40300158010341040343c15400036015500402244070000c0c2c0151440456135100c804e40d40148000e00c1d0241d01500c500e1100c0040c07984005a4049264042d05185051078036104005450442081a40e02c07490700611030a04c170754072808801002459030f0395840550312150308280b0030211420f2011031440d0025001540c1c50340b03032071080783c00b1070700103550000707105907402002c5500d0702807050014095400d00d0300000500002c00080c100c04003001c4103881c030181c0c0c0c0e040c82d100780c1810380c4901d541003c4404040d01c202c401540c0036008015203410400b2248005594040031108401c080448030030a07001800340710301c0c0e44050080941043d0070104924104000d541c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 158049919 1250 158048669 158048689
    0x302030c0103022b0207060b0619180302030114061908060105010c0215030406060806060f0a0e0403030e0d090f12050a0213150905090f0a080d0507170108030a0f0e 72
    0x40c1410340009048440d880684c9900104c14a1040b00c07400030b81c020107829019501429058400e60f090000d01e40041c0752100865850b601a001c540020384131800c816a040c45904c07100b95aa5500341600002603142070141c900b81c0200c0b991080c856141401c1045400300c2e00301203c20300080381000c2800300680000344c080c1964400d086c2009521002e00c001070184070290315840301844080203100c2040707501d4106d041600d80c030724103a0703296946042c02c0c08920007501010580c000285001007040042a20b480d0f604207020303107408500c10543c0e010103854140408111030020705401c408000303883c926019100a4403c0a41c90060041e560329440d580700e6003084064031032004541c102032194400d0b031018160500340005d0448144c0d031a6041c3d0010701c07080302d100e595405030111403442884085000ba6080340c0c4251aa400c1c600800c05400081200802c10307410310461000f10b5034268542c3e105540246449030045a032801106c0c0000d00085400c1d4011f01070003d6030b811800b0342d030b460700d40e22 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 158051169 1250 158049919 158049943
    0x6010210020f21090709020306030a020904060b0301050412140406080c13030203012d05010501050717090315061003050f13080706140105031903080403110109150f060f030203 77
    0x242c0ca81048019111003840340c040c01d0191030852281c0b02c0d44424140f070a051007415100c0079203003c0380c0d5030ba02d080d0036071004644455260300034080000062502c1002c0f0b6070854050040000c400055602003402c6402c181c806403400548050707100c041507030154036041000c1c41c481d849402e0910b40200508040300280150f850750360b011a03400041d0066401c40d900840c2c0044c002d004029100340c0507514505204040c0051087e09100d050321300d802405414101d50041c2c0d0f500b480c2010649035122601d14010916115400403c010034084c0c4c2c08100202a202c40c0c5140344109090000c02c0140f03d0500500101c24981030a081107048880b05440560042007403100702000c000a1800030b01c0c03407142c1300e00280281c0c40e01002c00e917134110708601d40f8141c07402070b802c550032860b880e060300b0994000540014002505a00080d001920030030100c080340c0d185074004030310b080079503960248040388030b0b2400007410b650b04036503103103400380b4080c12000b808064003a001c1c4e01d007142c0109485200344620 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 158052419 1250 158051169 158051171
    0x905030703081f0e16092912070806040e161502030c100203010906080f120918130203010c11060402040e15040c18110304060507050c010c02070e090606010210 70
    0x52941c5a101100c000300ca0340c0d041c000c000b400d4130f0344c000c840805070954403010402071501d1402c1480303004004d404140c4002000c2025031941d01e180d401c48205251a03050650607080c0706002c021801030411601503806925442c20607d071000a202c110303546402c170701d0966403141003d0501d5444130078000050b00c261a40300004840a4103080c0d203148190700705c4052511681c0122084140582c2c0510306131f450b099418012140e84501455440000354028403141d045400c05100107048080208007034080500400980c04903250301d0380c2000c004840340b000b2513916582e854210700c1e0a01c030b030f00270a0a4a00340007814402e1100c0c404d995482c0204002d0042c0d0380d5030b42e01811903e0800184801004030707062a5164985490088250303e80c84c400d91503040380703402113504031070003e00580c0e03c581c1540d2595400d558854a0754005044082c01c01c3d001e0140c204042c080d5103a0a0055103032403039594000340140c51070306105648403c1c0c0103080c210107030002c00a001c1680c0e404140030424a283d508 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 158053669 1250 158052419 158052421
    0xb1302040b0316031101050705070902071106030c070b0903251e0305040e010602060f130309080304060302040509060901051008100e0717060102010917070503070c09020306090703090503070308 85
    0x2010500812240c5900c60341442080180d4184612071030074801900c3c4180420090700070b1140042d80e05c0c0c001d0260041094104250902c1620040c2d0f0142030700070b025503901d100c40b10070200410f0b240d43c4140c1c1d5860310b49400152820510014181040c0c1003160000110f1030f021140c00d074049009a4001542c401540d1110114140f0010800340c000040d42080060440d00c00342c5800b03030459101c3d00c64004c9503644e50700000f5510780042002c0b48103c030340702c454080325034900c95070640b00d9104a0081301802114007012840340b03020000b40000d030402c0e4800594950402d01000f9074a180140303200c4c8207502c040014080782d110108485603414250400c00714a80740c0040c08070003250181c20004100c000740c002c02055541c84034000c80c0c000d4880c420f1220f5512200b00490a8541050b00a001c8480800014400c0c03c04040140318044c0503c06036400c0101c95668112403008560011600c1c0c2c0c0c01106002c034034031f09102881c0e080320941c00d040012516942c0c50a03228050745a0140a11000b00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 158054919 1250 158053669 158053673
    0x309150302070602130611010c0c08030606071a060301060f030807020402090604080109051c0809070b1e040b0909010f1d0c07020405180f070803190e030a050a030206070c0b13 77
    0x3406950140303503c00c50564492407800039985203c462881103c0c001404003004484560b13040c420064a03849681d038146044506803141c42060f030015041c5a00b2240402001c0081905802c2500003082e21403092000390401e07004140c203440365500b004008a00507602040060300d48002c443c0c0b8607905440160712840d109001030310602030ba5001d00d00f207508261114081010104402090070031a0000c1c0d01c8080350041c04032001102110710200e95880341d04180f10f0115840042c0c0f2000c1803818480401000000b44403009130416842541103039004684000c241c90494070440c05404909030f0003905515040529135144801030040060078148030106010f80810300441d0401a0054818402800d0010b149945030b001800500483c1c040d1032910b030114040440d100c8101c4140900135810038500c0391104404226449101e000d2109114258070b0588060002d00207450142e4080d000c0c203411818080c0c10410010081780c1088442240d2a000400750751200d90414501c0d50350f100010814 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 158056169 1250 158054919 158054921
    0x15050909090a0f060506090f0103020609010311130803070b1e04060b040920040e0318120c0d030f0207090203130b0603100e070302030f0c032109060d02030711070303091503 76
    0x10002d020141d0f0410341800f801180e40005000b01e5054070383d0091566600145076201c8001c4c00000d611280800440b006503100350084502d0f6840c5030222460710018110110b03030500958006000d40c1c001140c3c2c00140058146e13126403220303207000603008131214070020400760306c001070004107410741d80c5042d985680c590b1740c031142c021688011500c085220090440c403103250001e8129101e5810030f107080801e0300011041e142ca15010303494945132440324108000d0300542440b4800ca09210300032001805680380c44040c80034501030345501c994022541c20003810039103d6003250803000d00400070300000403807201c100764699420280869958880c10006410140b0381c140c085410750501c259403d01d41804170b102c50469208504540500c02400c4000b9221070501d01d400390f05800c5002c2c0c116415030610b22001210100300f00080c5007a018400081340d64024030b1079100e240f40c0c04010406455000703a4400078140d40301c0014903915245550007403003103803031340541101009510b803565203c9000b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 158057419 1250 158056169 158056183
    0x20918010f020a0903120306050f0d0203010b060f130806040c060f0509030601060216050405010e04060e030d1404030f0e150f0f160b010f0b04060804020625020a1505090909 76
    0x1070700305558a286108005100e00e056000030b40e081d810f141d404550650081c031801c0121a0301421a40b6103001ea60b04000010b62070343d40c141c1e0595210401c00c2c0707459444400500c90707204001966034540b12084026601e45507189c20110140d4058814407010a0300844504101c1e0300503d004c200340f80c101e10080b101070041703100143d054865100040b0358160040781004000c654a4442c3c0c0001e81d403030042105468080c810340781c1445500003c50b0108849400200e107001d1584112444c000741d5800b803400b1200c07041c45c80ca0513070160909010030181d0210410841003e103241c12062140040002010151000b041c6040c240f0005100c0380000403039400c0d5142551110f0b26180c4811040000300c1c020310381c190301151805150000070030003521440706881690303e462025420941000b109803140407010b070059a100506000c010402210464890418041d03003104041c00000f80c4144603800b00315403c268146112110107803900c41d031100c180c94242c0000c070381a070415103507110301034100f40b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 158058669 1250 158057419 158057441
    0x30708070c0302090f06010810180209150406170618070e0103060b0f0301030c06031b03020d0b040e0d02390a03020301140702060c040f0302190b04060207170a02091801 74
    0x80014100902d4805c00708281e8890341084c0c8804500d55540c40341c249080e400da020707400307142c071178900d0740c03046400e6a03805002e0300580504562030040b403550a000d843e420907804900007580d244502240549590b41c0325411200035107202032518021000005c107203100402071002c0004280c00507407541c1c403940101d0000e040b0308608076500c0354141c90542c5194000d00007540c580d94510000940c003807103807140e1034081d0503100e1542e045d0183c081040700a0f51244050490340c5031a16601c10f000c0d0356510404100341d9611004010303100b130482c0061708010504821189450914004a4110f00b80d0314031180d60021502c00000740220100c002520040e0075000650503610709070704842e0100c1c0702184980158255000c8900c40e0f034420383c2000840c030031405020024604031104000504040d50f14000c2c00c00808900c007125a2100c0c08010345800652017040140e10102041210b40740901c411000c40b04600c1c00303000c0780e020300d80105801940c007501c00e5860456240e01044083c1c1c0030741c03100d05c5c80d00f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 158059919 1250 158058669 158058679
    0x7050108040605060d140d081b040e07090b0307030c03290f120307060506010206011401021506210309041a0d0206090d12020c01080703020c0d030b01020304031e0303050f0108030708070c0302 84
    0x40c85a110640d032858402c07c103030301141d480d1022810007182001c0c981601040000d85902c0c00307040c80001d203584040507000800340501c91034042000044540950700c80e81da0f0f9500054140d9030440c1c0102a5501454001910711036544090102c22410000071100341041d07921082801d086808213110380513680c07001d940350001044c0041084001e4210034000c91b004d0f0708854050743c03603850f146524546002800e01507404840401506510155a16880700c4014200d02182007500e10a503000060010a81c403590000680c00d00689000d10070159151500c200740300c0c28078490408518900d80c65040a4495107010826699a03540d103000c1c50080780c0d0041c0c106070714013114000070303607108200c540a902040d5003c0c0001c2d8150311034426604081d007210000c104400c4210801e4006006a884060450104100110124124414200429003000703132515240c2c0b88ad0034001d0455a001e4406050343d2400001000065400820780e521070350006200381e501c90a81ca018148400c05500c000d400c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 158061169 1250 158059919 158059943
    0x120601030609020406080304081906091209090f021c020f040b0d05220b0619050613080d0302120103030f050909150907081b0313050118050c010207050108040605060d 73
    0x8400c64102c03041c064400d0b0b4051241540f101281a242c0c0103d016802040d8003d0105034035120006a0b40d1402d14040c0034000f41c1d203001a1511011940035541034030104040c130700304000070b490a00c180c8400c1d41e0038000071400d202030030001c07207005804924020442e43e0086000b007130a80703814044900404a01620780c0d80d80c1d09401d80c0c8000741404503140301c11004842c038403030389800c2c249045100c110b50080e01f0703980071354885042140401014020380084640401c0104180e1a840700414044000b211f005009910700301025260000b04004041050b005104484003200d0815856054a80c9070400ca03074090640a81102e10740187c0030aa42c2c056106000c1c000a14503441c3d074000c0f1420300752403140c444c2da50700005072200181500c0032807002c0311140042000d42c0d0900c3c05190858001c00150760854a90340706c140c01c0d40ea5080e101c11044106a90220030000d04201c83c051214007030000d011407514100019250410003003001d0442030312100007540603562001c1010201d0b070b11400130703211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 158062419 1250 158061169 158061173
    0x2304090606020a0b0604050403090b071a090c09010f06020d0f021f021206120705120c03010509061006090b0a030507210b12160302060c10050705070303050c03060a050f12060103 78
    0x242d1159000191035106014010905c1c0303041034041e140c80f0700c0d00340c1c480414140c0340c044045d009030311111003a00c180403411400319401c074400700303885e0040e840000240040480e51041018000041e4001024546c0300c41742040b0868012540000c0109981005008030000080903030070800100c0c801c84003810760350142c0c02241001e034040c1c62428100c800c24205580c0d40418001200f840c848003c5003907011650403c070918003981030b030511040a50031340b0030a11050000c03070300351041a540349003150010003c210380d0824070600b6500074501480c04d100314a1400d80b001c0054030400e40540c0c1016150350000e42110b00034042e41580014410b81070b44a4121341110400a000103044188500000354840b00200400200401145601c080c120fa0302442d541c204007450340300200f0503903a40546034460701000c03c0d5101e014419aa60f444141c1e81c4ca04900d0b00070200c8030020410000d6400c240140012a150b80d03100b4000e0b15015201850050b11074400540c0c131400142c00c84000340700355400813003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 158063669 1250 158062419 158062423
    0x160204020a0c050a06233907060902100c1a18030310081002090612040c120507060e0105030103110906040f020d0f0e0a030f0302090a0f080604030806030d230409060602 74
    0x300100c501c3c00e9107001b184541c61804034010195003a10054006040c4103140c10b44c0003125100c0802c142484031070a120f22806452160444007003500e406648000040550030300503560307c14101140b0b8241d6034a10280e84004004c521403400c41c0c40ea44150000404c2c00180502c00801c412441c1d08480d264a00b49461a9950050f8000d40a1502070314a58035440c403468004e58034180002800340b0b083c412840b510950780f5400910135500003400050000700d16007038014640c2503a015401414080b0b00b050009451003e40c0e80c2c500d410400c007000100301240e400000c40900000c200d0b84090161980f5000034041d240020b80c0c15540c0348005801400519554002c00300180122001d011072565682e11030b446088100300a00404c40c81446405054480e038010480714000901d03800107581c545900317404020b980d070410107999011a09000a054020b140c8070b50000049004002401d40c190004202850000750800c03080c8000d9400d41f000c04005c42170358081c00d101c481c10040c40d95a010b00039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 158064919 1250 158063669 158063681
    0x6040312090b0c01020702010e011b061503020604151b021309050a0204180213050108030306060a02010207150501090e0115090e0c100c14060709170a05250605160204020a0c050a06 79
    0x34042009d200c0b1001e059400703030f25500c02078100d503400c10b02400303200c0d01c408025110040c1c1d055000b003982940803006903201c038068809001d980c0751106030ba9100c40c1018242c89841034545096005440c0340c1d500581c1c80100d9012481d14819000c14404024a400e505d008103880009500c14108901107454a10306450540c43c540202d41010b16610403580580403110203014203002c1e03400810001d01030f814120000c00e100b200a20005203480c8035038480a5000d1011f0a103e980c00c0d8417140100002165400380b9a400140c01000b000495101600100814010310816607603980303694021984040900024048541c0a0200d0010024003035006000000c2040304a6548007203100341c03482c0703d00000c0d00503c43d40c0c0b02d490f6200024181405100e1500d090700301e03126035126140c07815000800900c000d180090444c245074409044e600700d101a00790240d0001410003405100301c0e01c03006039440303100814640580300160f541c806000e00700d48941070040090218425007502108218265001c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 158066169 1250 158064919 158064923
    0x12110c010609110405040903021009060c1e020705010810050904080d050702030a08040b18010c0305151002061305011103090c1306080307150f09151103010506040312090b0c010207 79
    0xc100282d1100b596038122805414412200d1000780320a0100d410141d01018000b8060700444850340700f0a0b082c4000c0e28002c2008554690f201d0611406103600700b10300030300c5040e26401501c03c00c005c129001b55581c0e10340c0b240c0d60400c42a01c0100e03040c00c1d0b01089041c094400a00749134151310b07050500480703507405070800172400d0f45003030009504030b44040166211003500340c5c0c810501da1034546650b2409030002c0d10040d0605825401101031000901c100401c210700d82c0c4000c6081e240581c85030903040407030b8103118043c1c084034503a107942e1030f4041441c0754818182c00c1043c82c1e01c0020b00700540140141044403202078070020500074003800026844040480071142e090300d411f100d500b850b05403150307481102c2e65644103000388000125000a429030150028900150141e5451307044420349240307242c26901c100101c841c0083c00c0381a030090b0310b00c200700c2035282880c65262070b001c28024440d620010b801440c103400d021301190b1041c0b80000040c002080c005480d030304c100c01050b00031745c050241 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 158067419 1250 158066169 158066171
    0x605030d02011b0305241c030f080c043503070b0f0604020703090302060304050f061f140102070b1804090606050f0f0f010c03031103010305010203010305060a0b13090312110c01 78
    0x10050098864000c2610501072050a5030045042807010342010f00c0c00340a13140d20410031f0400c0026000701844020400b4000d1792684c03c958800b420240240e44003511040e96814104002e002410301401040d0303610340c0c0910054000764604014403400d200c4115940740d00e0000045101c01c2c4550f070700066004400c0d8054070040390321840100400ca1181810040c007158840c032040000d450303c100550b40c80341c02101654103100c1c030034000505040040700c0c1c10078610503550614582d600c0e0010400058107100c603035448902108030000c0d41d20006440384c3e0036401b50010f803c00503080b03101000d04580c46c02400501801d4803a1600c00e020300387d54069140a89800001c94809141280361900b4440015100d407100607001c00044030340084203030050301407546440c1c01420441c6088021402507010704001601e030350440c5856810404013a110466a40c204460f0002d10340d50742e48501d525101100001806032250326040d5049804440507180c21031610b00e10200341514007004008a03000307000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 158068669 1250 158067419 158067461
    0x90d0206011203020d081f06080702010c022404021503010803030411010e0a0501080a09140a05010c0c030e0603041401181103070f05040b030a02061306020c120a060f0605030d0201 79
    0x280c0102d50320b80880300030300181e0040c07030f8039207001c4e0140358102c0d00030700750280d400440092488000050819030740030000050084e030401540a50a10940e126441680f000d0100b0750b401d0b842c203592400700d4801c980c2801c5a403901080865031505840303c1d52100c3e00341c07440c3d16981d41c1c0c41c0b25034803500111010740d406400d420341036015621806066010040050451034a1030800004503510040107005202195803030300c0c00000300d1040701d9100c08441c0450020a0302180925040e0f0039505003a024400388071080403e1800203401844801242d5001d50343c03e5100d035a0b40c1000140d2b0ba1008a846049500e0100300280950007065410145406002d40050103040310042c1070f07840880384188030388071180c1c81050240e1b16107070b00101588100201161500c4429400284189e4080410302d500c90070f04c0710041002070f40610020080d035100325201407880070010715490711009443c4004210603610f40d941201001c09500643c0640005011620341404400d006802001100d07034603107a42407898 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 158069919 1250 158068669 158068679
    0x606150c07081b100f0c020a080a06020d1512030e01021e0a031103030c0715060b040f140d020d060b0102161e0e0606160303060e0c07060507081014120303090d020601 73
    0x6041340c030f981d504036940d080c910640c001044a00035541c4008982c0500100b60001d03a12004220b000382031401550010b98441c0f107035400c801100d81048031645075001c1414200f11070b601c0410403000858241c2070548910400100407410005181060380e000c94044025100d074150015003044001c2c801d480302807004210303510303142d524041102c1d0741c441644200482000958552454031802c20080c002007030103611000c8039a03458010350082003440044201c02c010280d41001d17424180c40054421011040440d00400c045505d10782c0c02800490301c510204649074403c100b5100003900304c2045502e2541c46140381090100c00d81a82c4480c12a000408546000c0c21001107000d4440200000d1030421344080704940d0000a9000b41d00345651b0744030000d0032062800180340301c0d007042080c031542d480c142c0c0f174031404480c4050803620401c00d0a034100071480034403100c0002030350014140000c41c1d910600014400200319a4041a130740400b109220f5941c600290f18078410115400743d0300d00c2d0b80c0b28 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 158071169 1250 158069919 158069929
    0x60414010b0d1407050c15281d0c0109060809100504110d03030b120f03030106180e010f0509011202010914040f090809030105061f120219080403090f080606150c07081b 74
    0x29070310f98540c0e110740c2d8003a0319008c12060301c86900f04c0b400400410322681d4020710501c800c14406a8815036006902e07100215a4482d480d40083d050500f401031450a110007056a00c000865104030902d46e031301c2c04a000d020031411000842c08000700610f20103455403030000c0142414811f0b45000341081c20001d440e04c140400d0711030301582031400840c00d6a203000c80407254140000704417541d4070211000420405120040c0a000e0000140d06c42038491501061010a12050f448030305a1040e088003000140c1c1d00000a40c21240c5d510307401c0c1000d05a02000500500c604112080070500d48601da02c01c0280340d40243c012044101c0c0200982d5852a05020301c07011740700c1c1c1e02d0784038000e21700f8505003541c09941503122060310008010304000105002900c015100a0060045001c803410081010740c4018640050f10543d0705042d0f0030f901d080d040365900c0d00013802d020312990b000305d11040f085041d1400e5540e2441c0042c00c807408030359102c0c1000c1d01c842a0174416040300080e020601254205 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158072419 1250 158071169 158071171
    0x402070c26030306090a0e06010303050c0709020a021c110d03050f0711120706061809050c0102070b0f18090f0702070b0901172703090108060414010b0d1407050c15 72
    0x341c0080c51a65440c801000018900145908400c9a55048120310401c0402049020b140b00b81c40b40c60756220810402458a14954000e078400b034010050325000d140d0206000034100000c11003114500289a025240c40c5000065007005101e944210000307154190070180c0207182a81c2c607a6165140c2c10021542020700501301503d503070041c4464014608844001c00d503250140e000001c0ca6a110011301c9155002c0d150040012519480500180241440707290403040d02400204207003454948464420701800301200301c40c41d80401c2e10522502c0960640030340240c011b0511019240c803419115544502395a00320052140441c00f25402c0c660000f21248058145c43d030020552000c04047e9008200030a5004108031290111210142c070701445001c420040001d9925268903000040503924001c0c01e491141d820f0142141030100241200c606680e001601d01d0f98a8140d6480e10b409040b040344a403000c0b541900070806155844800b400d1040c5101040d103048140f40350220449280c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 158073669 1250 158072419 158072489
    0x2032709010b07060b04090b06010806090105010e0105131701020a090e0f01090506130515010f020703171317011509020c0c010806040e03040f0305070806010b0306090c090402070c 79
    0x21128005200500d0702c1c901401d0000d12404012609800305000710301074582e000c0d000c8440f48200303000d205003580c005480681c080416101c040d41c0798501030000b040e10001d0403113541071060000c0c4000c1c001a00e030b034804d4054001800949100303e55102414000c0d4000d8011900041c107160b004a0a0089000c2e518054049075869841e0703030f420040c0315001000082d124580c840b00d902034190b541002ca000740ca1191a654001d000c600c014240090005035a601c05101150848241440007a009207000e4a401d00c0b44000703691208100045540400c201d0781001001c1e1900d04042c2c0c1d60003205405c164041010703c00c00001e41903403a964442039003e111455a80360300300c2c10380b030748055104070b4120707074403041c014804a0f102842031403040c21039020340c001c00a4843d1019050090101c10050a002010980d0090416601d010002c000601020302035512820140c8041003456031030780107540003c080200308641e030303071583e140a85403103d0603c5100c8400c0390040c80112a02891403036415009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 158074919 1250 158073669 158073679
    0xf0903030709060e060910030f0e070303120b01020a170a0909020c100f18080910140a032c100608010e0d030518120301080c040207021005030603011b020327 69
    0x18180f0030203a561484032500c554111009204c64501e6035142c079031744020141c164500084070380340c3c801030b4030646003501ca00b100154880d1404000281d840003890802d49110000018800510f40041307040071600301000d49600140c2c584400340c110500003c18040c2059114011495a2448120141e000d100e0641134150000f5007110480301082d0030180c4a402c1000000558041b00c0044d0601f001d1048810764120130702240200640c01d191784a00c840d0792050400c4c001800b0074130b40840c041d2140c900020100741c0ca031f0300c19080401103414140ba0020440c00070802e2460400f00300ca98401100d03000114040c20300c04000b82c0000103208400e00c40c48444040e00407403c0158064004e444058041048030001022205440400f4030030380e00c5100a801d80c2c5580e07940b40c2100180b8066050420b20310a9204009641c0140d8500404d1400121a8180191684c5c0d809001034010440c05110800000e044454585103030742c04801007884040d1020342c05040c0328003104540e0f01c2c041082c42d181d004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 158076169 1250 158074919 158074937
    0x3172203020a0e0a06050301021305090606090a0302060c070305060a020d1b021b010e03030a020102070c170c04090f140c130615031d030f1201080303150f130e03030f09030307 77
    0x30f0014a14031640c020503c00012038000c2da02c1c004a42240d101e40c081510010307024400384050b18080700c581c0c1e04410100c4040d42000c01200020340c159145100c02441160001040c0004c5030b000e011403030046401005498952800442c02c6010f98001111209854a4a0784035803d07072161495146500038554000c06011340c0003400c0304010003000015078103218541504082e140d4080000304103210b4176500158441d4000d11b03000c082000950130258000500300d105210b15030300010b5a891500702181c1c045202440c1e4140000200302e408400790900c0d801000406c0c202030001109811031405503510050380490118540440790103014409004030310503100c1000c85c2c425081400646c0504140c18140403115845c40d1456101c0310707043c0070380040410b020482c2254441568018a680b501440c40c5151840030703803015901c2d10301500e00c1800c0030b11030034000340c40d500301091031981580070030062486808442a500d8102f03e581c004d03141503040004001202c04019203000d49181e13200c1b0480303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 158077419 1250 158076169 158076179
    0x9100203160b0604060503060c04090b0a120b27070f150c060507022a010e010c0b0619080f0a0203060601030603120c0516060c060e01020f090609060403172203020a 72
    0x201501ca40c0d4010384501002c02c45650501c411030051021010080e2b5552500711100300b0b0303600c0c04c00e081e48245003c8004205c409482038500e1031a5600c41005080c0c3c0e40d0758190f42500c080b410400411001c0512260b42d54020300040c21400c1e15840c5524001d125650300244e01c441e00071707841a000003043c0104a0f00000ca480e008540c10000d98016a4240503030014071000302140462031010891009400d14a1960001100e21800034203207031421131241151540345050354007900c2c050141e1007105982c813450f8040c0c0782e24030140402c2c41c01c1e41c41c0d0104504005a40705c048550a9100e4010807010a880b58007034031a4904482d07000f5110481c018081c217058503480f441d0f11080e14170740a5944131080d641c0c000d10700305015003040d80b6200c004507428100b00341112000c407a420310b180c0c81001562a100744400613110049401c031881030740e07006a140444d480b401140c0c0000d08031055058900002400003000e400304954940709200b26070100b0320154401d05a922020f500201c0d40d06007802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 158078669 1250 158077419 158077433
    0x120303050603030a17100512100b03120307110106050307150306090504052109030d0807111b1009030506090102090916051b0f06010315060e060f1c0c0b0910020316 72
    0x5401460411340b2003001d42c1e20004030340c40744239003109a182c235007295085000500091045020548080c2c0040582c82c250029080a0b40b10160040c024891000c1c0840c181c5c01c0300350000340242102400f0342e40160303544c414200c8d00344000440040424281000411200384d0ba106043c45245c01c9401006000652070f2010802d0407030454a409803c800c200b160701c07a8404000c40d9450000a5035402007520348503c0c000d080740000350444100c1d0700091103142c81e0310f40b001e10508140008942d800c82101d00c0c96010b035100034413035100405a005032020014840301c10344c040c0ca8407920a49445410b5502d500d0b100d110303180c0c05881d240114005002c07168884000c84079100101c086901120030700e07060b010b8a2803906100364030450f07420003100d404500760082d90044900a05055850a01d681424800502d101c00c5c4600418007548104d4240b40c10081143c0c0110030803900703d150800085e8540071002899400b070076100e0f00882c160402481080d10001c103c5450582c0300f02803c0301c1c010541c1d1400307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 158079919 1250 158078669 158078671
    0xc0f110105070803041b060c02090103030806060702040e060a0c17040602031003020301140106140406021209010c0c0b031501080408094608240c0d06120303050603030a17 75
    0x160400505110311000508800004d600807801051482c02544115039100b0301c0b903941e900907804008403134800000588400d005c680c152a03142c2001c945694a031000b04145002d2540e000e94060704000114000d45404100c40d0b028099a260600c0190b04551042c1c4401035110123401e0703407854140c0000c0214030740b54061600308000310168650b61343e9139000282554181c0c03001c8100c207010381c03004111468005006c0001a0380c2a810706082c1441e010003e9141e40b100005112820b5001901c17500301d81c840c003c10543c007688400040c0c1e0710340d120b170449825900100c41042c126204505941610340c00b840c0350a00c915031215a06241c480081e09111200e150081e03c100744d50001c0340da503450031035125042c0310741800620a852240c010346015090540d115031185c0d810342c028038006610826030358400d11070040b88000200703d0b9107038030585101c2c51080b0859103030400d00d0110086061324a582c42000c100b40a0781d002e0000b5140e45041545030b00c1450f62490100741c110103031910081115100ca = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 158081169 1250 158079919 158079953
    0x606180301021303060f240b071406010305070f0518130203010b03100906060f0e161b0308071115060f0a051e0907020105090c06031512010f0c0c0f 65
    0x36041c00f840e120720600b2596103410440340c060300c07802d4460007030300c1c0c42c402c60183c103203c01e54080300702c2c074592800d1340d10410500540b0400d200000e101800d0100e01070003070306841d20f51000c4a00f590796030708201c4e840c0c2420380541e140020884c0d00c0002c151408411f484500f28211034050741580710000350880c1ca0a8410049030155281e1079100420382e000c4c03011071b120592206c4046010724042c64540100c40003608440000c0d92902c10600000c400c01c0d2545501c0301c102110600509507070282507841038500c20490b01020311100140007015407021506000310030715155010344401c082d420a45608000309014031154420000402d02d150000102c8403500b00034144035581030300c400124284602020900c01072040c12004488a41084a525588800300c0d01c020461410044d41c81c070780380e841d072128803441081c000c0041591903201c00ca0341e000a0600030281820303d01c0202c15240a810b500400d00905494641820074050007060290b600382e0b440070070b00b0043c074516910084624444142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 158082419 1250 158081169 158081171
    0x30c020c100e030d0201020c0d0e010c0606080d0314090d14040902040801051005010c0c230d0b190908090409030203090a060c020a0b0f1803010222080c090606180301 73
    0x10030512500ca01031803070890240c69a940071070074096000c0c14a06014400504110783c8104041171030000042010b005803c281d16000300c9605602e001202c070500b034080040c000920b0700e0000641d204002030050498030154400b4003996082d20481211180d0031684000540c00030103103c029148202d40d0420f025441c07140c03860405881d00080422a0081d8208401c141c0d134620170301c8440b015401c0380200601d002d2800c11000100d99540003000f104a2007007241c0c0f10581ca401d2801c4105000c042d030712050006c1d0089019801a0401d480da540c801d4031421490541210180d40d140c0d080c0c01012035403908007625526000485040c003005050103841901140014440c085d410342c5c2d4106201d00500065407030b010382e21418010811705030140d03400065005da04001d580d032410032140c160b070b09985401d404140c200d0301d20b202003800f902c070340c034941c0c0c0c0c4140c42c144544c071040849003000c100342d40381d420449007540340f504180310b1210030644446e0780c00481400001e0b081e0402c0d010b02c0b904c0c1032010700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 158083669 1250 158082419 158082433
    0x8121605120c1605180a270c0504200306150304030c031805010f050924030103050d080709030602130513020d06120b13140d03090b060103050105061905090a0905010609090c080601030c02 82
    0x10316079a00340340c441f04080040308800080000d0107003003c51030018100c11030702046502905804002d03181c285008400301da20300400042c0c03055903900c028828841c260f1485d25a40c0c80d0a00e001002000c1081049000c038500d00c10b640c042030210084c05094401c10785900b440400307c0803003a5216000a954035510103120b454041c880400400041c004c0c16900100584950542c5031150504d00d00318a80c0007000011820480c429602ca1031a900326504a000142d468001584c1d0305128001a0012500201504007403003c02c4c101e64010402485401c0c01000b401e5110b01505601103011800601050b0811000c594840010f6103000c004502c208012100a8021540036081283c12a81540405c2d55071202d00c1c2480b03020702c2d1455024000340307010052036040c000011001d000b9165801041c2c0084c154200c2540d009004039600350800070180c02c80e4607a41d403d0344000d0002401041c0c0090000300c00024440c286001c0d41c001c0d40e9980d102e54210f56242c600440007441180c4650b021841000d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 158084919 1250 158083669 158083691
    0x60307030f1104080106060206090303091906091205030106020c04111209100905010b010306061b1401020f03010b0706060b1c050a1b020109050c030708121605120c1605180a 76
    0x1000501c004c0030032200100301c00b480c0502c042d0600d07100628000040d0030030804c120b03104801042d0a0501800380d003e08100c4682414020020200c45130000d0000d1880c00c40c0d00b0700300c2d8020740954103c2d4007a03800c450182a912040c481503619160012480440c240300c05454919a1004264440340c14821201b030b07501e64104034015070b13800c2d80d42500d03165502c0c501c45066503458015040a407032039045c11070103840c2038105401180c00011003c3c080b4100380b95003408500c1c00303404a40c188100e08036525140d58440501240c2c90f48071321000c4459506c0c1501c0000c030961058191012059921581c0483c40304180000000c0c0000501e9030140954039041d00300b000521882c9440158126800012550080d1800c13900e001c5907110154442d50040400300500e0f040059802e98800a412240b900ea0a0345203c081c1102030703080d0f00814a020380c0707420041c42e4490101402010640c0e004960034a03102d1034012031100c1580c0180303074020040100e07422586c3c0080717580941009082800007041e010f11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 158086169 1250 158084919 158084951
    0x10326071a0603011505040504080c121e0a02031903021e0904050106090602061f03060603081905090f040b0a03020306010b030906060904030903030c0c1703090102010e03091804050c031029060307030f 88
    0x54100644010804074050201055111372110040044002186001c00c0030f10b001e0746c2d0b0702408000b03e4103503071002d028020f9140700e81c05031407408828075200c4410710b04d181003001050b000502d07054000ca1814000140b01c1e48201d94030320031500345130007820080c0c5401c4080180c020043d00100c0c1009201e420010001300b480c130518004501641d40b2948035030100c5421241c007130760380f072504040000c24010230740d480c1d803900c04031450300400b01c0c0c00145520065000c00d0082445900103507140c003c0c100001100c900040003035114403d058242c503040c1c3c0d500c10400c90780980943d4081d00156642c3c009100090246d040f0030222401900060001580d4401106a02d51030115800c620342000c1401d410550b024040e4101c49540350020b0760514500002244a50040002c50015082110042800d009081c00000c240c1500170303060307844070300300c215041002c0e00e24030301c041b04006602c940d00b040004021401da480382c20000c02d52403958480b8942200070705088450649030a50b1002248070307581c21 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 158087419 1250 158086169 158086183
    0x20a030e0304061e022a0f040b0604090b0d06060e160306060909020c031e19030b090a02030601110a0b06150313080a020c030a050705180f010326071a0603011505040504080c 76
    0x2000422130b41d01e141b8101482521042402141d01650510310700005d15503690003541d042e900c48010000704907103d000082c2200e03801d41c201808441c545280031880c80c03001403002e40f00e2120040042d2418074800c10407800c03181e15104030300000b41200e86c144540d0031113400401c1040e007064103c0e82405500c0c030711044442688104d4030f007d031900103a424020740c4000d60700445600d2a081c20020364100c1000700d480420300800e14007102e5400000a020390f030151080d0b0908003030340c01c12140b40584510300183c00403802c3d100c061150340311200040c0701960070310440b4400e24a55400c00441212a590145075400c800781c3c7d40154014090300c203000e6101000900090b900a01c0140400c1c2d01d0076013809505504910100c9101d078a2600b00600a000e81c100d40d811280d124420240502c0c81d146103960280038074002e502d940740c0000e1000c090180b024440e000d82c804054100b00d1035102c9001305802c0b9140d17081b01c5900c2c0b01519204020514055004070350046c041d2a00c203103010300400ca22418055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 158088669 1250 158087419 158087473
    0x60f030d020f010507170a180f030801050405010b0a0c021908030f04030c120819140705060f060306060f04050c0904090506071e0806090a090510020a030e0304061e02 73
    0x301c15141c030b5a0142c82405000e800c40d400d42441c9030200c4100c95007450140c0003d02070340115446514500c80241c0710805501c6990300302642e4240c0410b40d19000380702081c20700c502440b4509003000030960f0b480d607404981d41c01c60991905410943c9581c02c2c0041c0c2a030fa01040074840c92022800100b0600510041001001c0c81071140d07546c6080d40303070080c0d08034801e4201c42043c4040d42040c80020b00c1d1003084849405c04050280e51f643c40c01c440445102d4001d05481d822902c3c00300781c000c10880c002800b0781c020b07401d4072880056581c4034410715940c4c400444140c0d901c01a4481c2216250800c0d510170780d00050201174003850402408003242c1a2000f801c4100c0f01a0311882c20040c842c1d40c411251182c2102000d00030809030344105006081e4280078108500c40c1241c81c0c086034048400d23038420544c09078000c0940c2c10784110821003500a422050144c00424107100c0020951100801243c0550f00680c0315a04442c078050320a41300c5241c0817801605610032039101e8810b14401c1c81480701051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 158089919 1250 158088669 158088673
    0x70605092110020a09080a020f13020d1a030c0102010c050f07030207050603100518070c150e0a1101090509090318010c140d1b0b070305090c0d0f03110604050312060f030d02 76
    0x1250040c00d082c2c080c0d000761b01079040b030881e84005035a0f400070b2105118044460307159050206020718000c2c072407031895082662a100d104602011f56003c6c4001510040302540c1c1e070424000d0043e82030319000400140050000c000c150140c9001f14040c000d00790203441200c0d8066140c0010501c66072041c1c801d290441e100001c00c000a25010041005000c903085403081e241c148082c0140c8401107440004010065182d907002d15080c0c59404001002005806c03142c03100420b041c4034440c00b00944100d40001c030f1400b008035a6040c0100550302030354901b4000c5252115116840303038981c002030300503410403224008950100d00000c070742d00c84510500000c0c0242d624003990142001c01000103c19036841c45440000c042110100d450380d104603030303040115480ea61100c1183c00c1c01f6800b500c4c940d0007940c01c51410203002c0c103091803007400751081c2c54203a9582e40300c1107900c0d138a0b80f0071200240380354400c10501d4169012000300d542c0041d000b4000140245200000030b0a1000144d1540c0040e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 158091169 1250 158089919 158089927
    0x121d1209040b01090605070609020d0210030608010f060f0302090606070803040b060f0f2103040906060503010806010914010b0a030b0607030e040b12070302010513090203090706090807060509211002 87
    0x1031900303115928414009003004e01515151000251480c011910043c008564070741c0c241d402c1d5102d0003020004260700401d000c040031040e51001e001030680c0c1c0501040c56280200c441e501c80064821101036030310004460f40c1d185d01e1030b42040303425000204442c0d0072682c107100150001e03c00c0406140150300c16808402e00345011000c1c030003015101907141c3e11a11415896000c43c1d00ca59500e006106843c070f200036040e02c0030012151640c031a940c030112540740751003400141da55000020b14117850088040e0380701640d80c3c2c1c0e0f03000c0544403035262140410b8030700c10040010729000c00c010082c0340d400f82030214014032000c00043d079070f802101081e00414065241c0349072070b00d00b80c46040c40e544d00848103000100d808610032942c5034402d000c000c0c18000002081c104215041038400014071190400f03642e40e107030548090740c5a020350700c03131030021502049011495810108641007918515510316040404c040c08002c40309506158180340700d100050807001c03202060280446134000c680c40075070340d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 158092419 1250 158091169 158091187
    0x1503070501173718080f030402040b090705041a0309070b16020307030c090507210e01090605070c0308090d0e01050d1401060305150916050c0f01150f09020a121d12 72
    0x1519038540e15210900c40e05131404000035504030689000c004031540c02c58503a80e803403000c43d00800d15504010b0780f2140900400490300d070f0110061083d9003403015110318440131104182d002c0e002c00e170b80d2000d181c1c0000b40140007407107205000e050a941903000d0400e0340714140d004a170070710701c46420558450070640390a00c907488490040d1500006503180c1089201d803100b00d8910b034803081c14043c00c0e42d90388640841c18840c41c00d4000007c12078100310100100c1c10000e202400783e5207950012804100f0000004010780000b00c0c2d640351f0aa000e48034118403043c41001140d942e0311406c9000902c942e14180c1c5405158401480b60280440740c800003454200303230b0100e00302400a10302242c8a44410400c01c200640d40c10b2240030b51000d0350401c80e0301d454100417200c0c10058031034980c011662030030443d00c0352821502102011240c10303045d154076558444800109900c40c82c406140070400c0c140c203110382921641d2010044119042d60f025926003002150b5003405d600209010040d4804980e0301c00e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 158093525 1106 158092419 158092421
    0x10e040603020a090219020321040c08100b12012f0c0a0b07030f020406020a1403130801050a230106030902030c041415030705011737 59
    0x4105600c502e9000700a40143c890000c81c00d00030f030386c0d80b102580003000b00e481c0b0004200144045c50340d1100c0c4001d650601030400c5500380c0c00980001098002400f02111095802002050030182d00b41000712400036030b0b03038ad2210380c1d15060340c110081d841584074105120300d2011942000c1500c024081140c041c400fa800d2540c02010710000402c140880301510800003500c040200140d0364407000100c2c01140588005a441420b204011643d240d0282c00c0f2102ea4200300ca18040c00084900c2c03e1980e154000070300e603034544040c0104040c00e030050400030008980c05155500500e1050150305006108640915580c2e2001c1c2d42552401e201c1810901d0015105110034400c03040d04201061080b03509040c01909030341000c010346004030300e08048440582d01c03440c40c0c02006810080082d005006820300e0903402d4820b85161104007600286a9008800042e2903c0840f0200c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 157913669 158093525 := by
  have h0 := BRFrame.cov_init 157913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 157913669 ≤ n) (h2 : n < 158093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
