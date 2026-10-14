-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0684
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:08:25.874213+00:00
-- url     : https://prove2.me/submissions/fb5ee63e-2d27-4ee0-8d19-81a445622790

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 122841726 ≤ n < 123021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 122842976 1250 122841726 122841737
    0xe06030709090e15011203031d030d0f0b060c070609080a0b01031112030a020304060206010b0301120b10051c020f010302070c120201030f050103050d021c0504061103040b1303110402090907 83
    0x49004100f140f004c4003c0b600310800e110b50780d01e40505e150f00f40000300440c0000d08000400151180c00c40e00c0c20140e052a038061800c1020035540c0b10010101c0000c2c00040036110003c030000c50311200c0050401014203009050fa80d820a00c010b000700c0001c1d0711000c8154014000c21000c16040d541003815070768001000350704501150b0004402d400c0f240950701007070100049440102c0d030000006c2c001c41e00c060f02036428680c1d0707032400500180024131459904440039150440001c80c0b03010f040e80d001c0e0001112180345a11007010401241d00102000002054804002c0651420903800210301d48246000d40c81d20415580b0004110450b100d5121480e050410407411a030082d007000401801c40c000400080da500d0602503a00c4a17002c04040c094066180180c0f01880c95040200c402d04440d101c1501d40f234034041c0200c0c0d4211a100b03640c11640400d0101060fa03014004c001c0030500c40c1404c2940449080d0b0901940d41e4131101401889280b0400c410030f40d948030034200503032000740317400c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 122844226 1250 122842976 122842991
    0x70f020c01140d0212040b0c19050a09030c0f0305070f05010509091302091509150a060c05070b04060203090a0f080613142a010306080a08090105071704060e0603070909 74
    0x4082c000c0c000c5299055010b400030a032021402610651588142d01a203e01c0d0610707100c404c12840584910101c2e0602c04070a031108100d00390184005054400a500e8006140c1e9540e4803095900c60564110400656030085c00308240700003001060050106e0a04003d20540b84c040003a005100e12980c0b103002d2211140042c2c074406484100701e00c0b150f0003800c1d014582ca440f4040c00d032440c120445030391041440c4000300b00341c907800e2214160303020009403030100c005082000a40c3c50140e4100216454492a800841c044000380082c00c014112a0001c50300c60700088200022072116401c04540b20301628000c1050b9240002d0040c0c0104502180307121a809a044c5a0100018800c0d841003601c43c001111103207107800e400409907070001c9040301851241050044080c0d40b510300c16060154031102c80f0304042400d1600805042c0b030141429450416940e440070801024507001603031580c4081020400a41c1100030b155031010b04941d01d138034516058102402c559818025528440e60700c400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 122845476 1250 122844226 122844257
    0xf01170307050f030a0306051f1412040f0c14010804140109020d06020706200a03020a1e0804030801050a05181509040308070806100f0f02010e01020d02130506040303300e0c0108070f020c01 83
    0x3200d2f0804200309031081d0902c1d090500c4654024004c204440400307a1000004100c1c0c813001403405000300580d00e100d07483d00c1d03a0700c2d035501101114014000075582c0301890300041e9a01d0342c1c4802c2d010f20500c0090303202c12160401000301c9025170075040710080c0003162035000c101c03214121201003000b42030043e1195a290000c403485004100c41d0010741804a085034030241d000003603180f20358800c0d903c0051603a00c0f040bc1c000700507040d02c140340d000315041000350041c400e012081640240e00307a2503034a4160782a000034400140036035099010078130550910400030b03402210a41e029505580440030321305c010390300a146049a0320755500700121001c2c81080c1d54400e4014174a010342c540025520741c00350442c500b0007940b0030301c2103011000302a1000642402c044094904498040e195034905808218403a01d05c840e02c000e6080e050601e0880140c6108c4141c031900500c001c8050040c406043c02c44000360041d0000b8003000b0903c0f00360388161480e99400a04105162002c1c030342504a41b0707a551 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 122846726 1250 122845476 122845517
    0x90303090b091219091a180f060d1802090c0318010c0e0409050f030309011517070b0d020d050703020c06060a031e140102030f0402180f01170307050f030a0306051f 72
    0x1007140c40c410b00186c2045007404071107806411400450078210b0840c0309035404003c41e412040610702d4001c3d070180440f4104600130303485035032005070f441a040d200c541958000388034418111f80c41991f40d04040240141e14000404001c601c500c83c200030031200d01041c40c0500790540050106103da0b486004940400070f092180315001071404003280d03160301341542014080d000310101c01c49580f00038840014150003002a0782c5440c010500941021070038041c43d030040d079005000d80c85140c0d4007040008060f802a110300c03440303a481d6a03401620307091300800442c20418003404492080c1700d142000d002142e18003100e040100504100300c071204805150805a5402115440300254804030400c0403140140302003d03c00c5100b00c0e10380c82100d2040009009881003039404c84a4982c44030010b228800d40450314010308004e01381207a0411000e5910585015042202d010650f00040385501c0300c1501400380c0409032078110340e4800c08914407401e025403000800000310421502040301084100e001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 122847976 1250 122846726 122846729
    0x2070f170c1302090f09010509040308091f090611070c272a020a05120a110d032403050c040b061e0307080106030506031c0909090303090b09121909 65
    0x2e401d018188000c0581040290440c05601c2e0090792062221a0540f800200742070580d000140b811500d42c403152801c5551680040c004181c41c0b144941c0603a040c400c604115001d070001050100d200c01d4a49405801d6512a5001c05e0011005001550000304071000001c00c2d552400c641d8010346410014222007041c41f202c400b09010b140c40d200741a070131b1641501800c5103c1c0d101c076910186400000072a81c1d00c818440240c0990000344060b650884104014102d061041c030f4804100100c90988609150429a01b071300400d0350742d5181ca0f440b62100c0003c03c480000750039440741651964851a46405014104c54440c0744c0e02c0d01381140c155120f0041d545041000c010401c0442c42e0320032564095402900c0c2000405d08410001034a02c0c481d001b064403440014001d04203008080d000c14000c000036081a10900c0101103002c00c0000c254400c0724921406580c0c04201c017034140c00c0c6517110710b401408001740d94018401c1c086502e1900c40850340008140314107952440d00c03a40b0222661f02c582e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 122849226 1250 122847976 122847979
    0xb090d051204121101080f040303230108060901050108010e0a080f04120f110904030f0c0302070806071817070605030c07120807030e0a02010e130e0109030f080702070f170c 76
    0x40380100340d440301c10300f08140142c899020300c5200c0b50240010340710a08200c0303100000d07681800c000b6001a1103900054007010f0024480d8420540d980442114000240c0000c3d50039800f2208001188109004035070051011a00800c01058241070310b90b1100c10002000e8100c41d00011a07140101400b4101c1c1d0007416149000058800c0d1131401c043e40402042080d11442140082480c80d49800040e4a014541c03540398801d104080300303810307114019110740039010f40c0201c88000851060034881d90303110380c0160f07550000b00b00052a009514041c150850344600c02140e000d01400c0d0f00000780101074400504115071079603200c8074154424071564000500340715034060300e14081501f0051040c081e160300e0310f00340301d12111443d505540340e01448020780054450700f8002c100c1e040119403a07110484035800030854a202d0882242076440088003100080c10840c0c103261b12980c860040d6400180038409091810f280c2075594405190a01a00c0640c1000000040020000f080002800c010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 122850476 1250 122849226 122849263
    0x7080c0f130b0f09011d06030420090a0e10020c07050d0c080106061d09070806090a0f0e1608070b07030e0d1e06060801020a120c02010914060a0b0105040b090d05 71
    0xc543c4285035207421140c03659000c81e0445200e0401300c540900401384848025010300c0c02c42e9036585401010100700311505003402e1084000903400d803214548584590038110000c240c01d50b652484600c0c100c0b606814045080c4140a00d20a0b81c802003070410403240c080310f02c0c110b144050300348004441d02ca81c1c030401040d842c041000600d250080011040c01440c040c0628040c4424800d101c00c0000031628030303001800000000d203561910040c601e411441a542c0020303140ca906099400b2030720000c03014030160b84481c160725081141c0303150000203080d03200d000e03010329032800804041c14011840000e003072000f803214030800e81c3c80d1019000205504420148140c14104152408642601c0e2082c0c41a60a04801040e210f00c14022140c2114859a501c5410351842d006c5000030141c0ca24810115522014072602203109132881c842440420030180125082195582003210b0019400c075050000501c404c0107640e40e50b00076a114840c05031034500c01040186001e500308540d20702081c0f900103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 122851726 1250 122850476 122850487
    0xd140a0302060f0a0204140409031206030b060918060f0a0906020417010c02030c0d03020903010204080102030f340302070c080d110c1e120f0105070f0807080c0f130b 73
    0x66002460034059a00341a003e192500d40e5440c41c0103910840c05120340010308003415407100c0c209a030184030014080c2c500810445130f0080c45c0000d6a003160700a885840e00034060061615150f8181d503082903d05400c001c0c141c204480b81a110200205008a04410b580c002003031141f0641280101b141d001e40c046540c0c0e611405d26203290340b000080782c00c0d10b41c039061410803401d00010440b0709030b500b143c000744070807040c2480880207548150603140d0195028440000e03641424000345001d9001c0c04054000b600e01020100f0a03c3c07240c0c80648200c02c40c1c1c0018540c242040907081c403030200170b0301d005a41c80b0f4003400c0c0800f40d0310440d4404007241c8100900140a6030b80305000524504804007a42c4400810408200301c0c46003080595840500c04840407405180144030942444103042c2074070720f65100700040f5421180d00f158681c000c15501c02d098004150300c440a1b81d84002c040c200301007d424545030220f03036801804034455400b540060003400320150040c80d280180b0241150756030f01d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 122852976 1250 122851726 122851733
    0xb01090212130302030d0f0c021501080c040213090c030204030312150b030402040e06010602101406060405100c05070e060f030109030e121f09110102030715050402040b1c020f040b01050304020d140a 87
    0x4143c5140da0f100107000cad5001c141c00410700c1e0b100b0141210428401489c03a03803400020040254004070320401101043c10b0006040d1510740130b5910100d5103032301e005807034506e181030280c400444030040342e02071861301001080f44610604c210dc1980c03400011143c0300e90702d0344041401840983c0b450403142c03191600004d50300358001100c19044002c040140400c0d00680440090382e0310943d14540d02c440240024072550074503101d00002c054007413811a520074480d40b59141411401c2c0c2000c4241600c040c02c12405080021000454081c150000c00c401d440d291001840000b80c840c000344914102858410044010000c441c1d060208602280c480040c2e4035407a801840d0840c02111100205154951198004402d680340d0703642106480c07d1040e8280d540b40020540140202da01560310b95070200b20307403109010b002515840c2d00c0f02d080c0c11055070040001010060f101244610b0922015140c1a40c0c40130075030350170590650b2404401802b5142100b00308412041810b07041c1b28060804060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 122854226 1250 122852976 122852981
    0x6040b0601020d03060e061c12030c020d090b2704060806060a14010801270203280204180902060c03120a1a06040303181802070b01090212130302030d0f 67
    0xa50002d03000c48003a165049400e800791900da00c00c66951801410003e000c41c18154040c00e5250344000c2000c6510f001d507507c200c00c902c040042000000da540315440e0b0b0081d0104040d4845c800ca60400c00c0581c0d180019100e201d1150800184074400c002d6014041003034031402c4508420b2004200b03202a9031581e02c0c96a035600c0495807984030f10700042c00010000c000d10341c8c04413510f9040e5100d021903030a20f54078100202801da0103050b07045800141a1815009101035400383c02e20794a08a0303400e040303c046005d4a08142d2131000364510402c020000e9054084808810545c0f186010031220b966000148840c02098041c40075400000b0b5111503902c58030390801d02c2603125040c104110054250028518000c4c0d84285400c030104200510210f8082c194011a540000302000340301500c0b0156000f0a000309105094070030340100725542081107814440707000d0400c0701011810303c0c030000100c204140003d0851142d60901d22626418035109100719104500340c18014452000f030711103003800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 122855476 1250 122854226 122854231
    0x1b070b0d050109020f040e041407030c050108090105161103070f061407030606020604031d0a0b0301091a06040b0c070f031b08150f07050702130e011503050d0c1406040b 74
    0x48a91501c0008110024148256040804c86020460500d42007034610110408083c20540f8180c401c56144080c200007003003460080c2d482a56404d00c13503072411001401440c0300ce401e503441a41001c08009000521040c960600c0365145007000300c0c00c0401c102e03130b810f40c420000c02500580500c5905024070281e60400c0041d0f50f000e02407918196100360302242150300c02c1c000c00f80142c0040010a0100b03204e0500642c84240606416080040705c00014984651a51055030b0904011004005000041c460b01c00c2d490b9051070040d00c06481c0f80c00180ca644294000c0710700b5404042001c013040c000030071145003e132002c01e1442a1442e100c0c20001c5200f00688065030544c0751090000c030308440d0106956814102d5600d4003240c580302c0412094070388034000e0200c81007001c10b200020150355107003610002c0c08a04440090740d9800344d0409420f44800d83d00600d4280c9140404100023a00026514400d840600c0c0040304803460340340c000180e40c41028038a440744120000d05c030511001041690 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 122856726 1250 122855476 122855497
    0x706051003050c100503040b060604080109060f0606111e12070302070509070306180f020c03070b0a0605010c05030d0b010903020409060203060f090108030702010c06110a020708060105010c0b0703021b070b 90
    0x1c80c1d12002504000111800130701c510f00040f0240302280000e4401e6960300c1e0040e40080540c0d04060b21000c2035400c5a10f03142064410603118841002c000c41d041c400d8030b002e82814a0901c02502445a40e80c4c1d40c0d00c007a85501806804000d1102c09040d42401500220004c6160850342e44031107080081d030b10813850142510944405001c581520300038458071003154500d90300d0718491061240c0b103000800b40202d00100385502005850018441480101402840345d080c8041a0400f40e2420040300d1168004130b05010b0403110050100c1c9000083d00c01d5010141004240100803500403500728034076900082d0401e050858410400200380c0140d44078a50030fa8944144000903410446240e00030b10641180b900f0400040f00554880c050110041e0f0248002007441d410030504c3c1a826403107409d4200058000c180b050001d8031040c0203440c0100f0003480d00817280300e41511010b1041e103003e0000011f241d40014203400b613890355007c106e02e8040c0c900130b4500302552001c2200084c0d00001404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 122857976 1250 122856726 122856733
    0x1e070b010338010501050c0c0a09060f0f031e05010b150705010b010309030914010e060c06040c06030c02070e18070807050102070b040806070c021305090307030f03050708060114070605100305 84
    0xd10780910845000c1407840042400b42ca4140d2820006481c69800410300004500a1704104501d5494001101004042207480000c0451819049118035442900001c1c0481083d84080011400d981d0b50b4100c0b0351408804c800e446102450b06900400c507500540b50440c1c02c08140400d5164504017034007a00740103100920000480a004404507a000840117000c1400d59200f4042520348408490030900e060402d120090004400545650070400c4088c4140d8400c4082001300014880940d000308207509050100d0109101d0180d12541240a100d225000890000e080590f80ca00d440c3c100c0c491100507104480d03142c82505440301d2450081c540540306071240068080c1580f422241101c003c030010302425190a24112041c22102c40e00343c0e84805030801d500f00d42d100500c00d06015070918401160389034454503024150000c0c903a10340c01410701e044204040d50343c00039001c0b03500503024644045029454541d0320b4590180da940544003503e402c040000408814891200307990065084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 122859226 1250 122857976 122858033
    0x3030d0f1508060714031b03010f0303020c1804080f21040209060a0602030706020c0f07090219080603102d050105090901021306080c040b030c03070806030706051e070b0103 76
    0x583e54500a0740c8180005071302e41c0c140c144584461000d1500001c4411101a0214004003032450542007a00400c1021020181c10020550100700b50720119506461647d406400c00760052803650004001401c00f80c0009401031095131050201d808078040c0016890002c0146071415018a4046804038024207002d404609145404c1036850308460980c1e00841c503010312540d07401c01940024043c80c00714856207400c4080c040c004d112a802a0131681c90050f20f42c0d0784032080d1940d0401c9044071005010000b4148029a00c2c082925058a800c06001007052288541400840c012402110755864210021108444415082a4121076044442d500c0350380f182c0801900300d1113000803030740304021000c200700207060150040e254001c4d0480349280c2415070700d064044965104640051404200104020000780c1007002d1039006007040e4001c00006042a4000d069403060702141141c0360340c65190354101f2441c844c1102c8505a010f42e42c1089543e5a25103169840b801060400303031500d6000743c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 122860476 1250 122859226 122859239
    0x8030a0605010318060b04090203150a0b04050103080901111509011406191205031c022208030a0e1f0201051b0903120912070b0307020705040e0709020903030d0f15 72
    0x51308088420301c4806424958159a41c4001481c0740c1e60810b8000307446400a4001d45da040c00394404904500364001d0301761828480c81c204a54032030b500244160314010050021500071400c1e611444801e00300000c0c0f203622810054540042001d50b442d10351510401c0101030603040d0441101e0041104225071310b034865004100300204240d100442e021898081005994648804c40e80036a00520030340c0e2400e01401c1592084401c45d00300445115000903800d55426901c196240b10b00025183d140e11803410308281035203d224240c080000c005030820740b021039585500044c100702111001c0c418400c0f01c00340000c0d000c1d100441301d201010954464030701500403100221410000018041c08440140d05104c0203e60005902d941c3c0003000040780c055520001c00403013001c2d08801c220240c81e4034103000001d1500078540c00c945d02960620b0401250106c2c0002c1d02d00640700c1e03a00000d81c5411032200440d01e18081c00d140001c0d02420078100c0080503026074415040c1c08000e211104459440d401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 122861726 1250 122860476 122860481
    0x5031305030601031104051312180501050a080a0e010209060c07150c080304080d09021809070b0c060c0706020705031912050103032003160506010512010e1903020a080708030a06050103 81
    0x4c030141c404001c04040d55240c0c03800341d00096001d60f40b41c81d55020800b403070f00c58403041d000075521030010030003c00071a502e501024405400400342440c0c61440e1581054006000c020040c040380301990300c40b00c00d109a244c00307406452116401400c40b503146c008500d01d0740d54400c9d00b40f1030700000b841c5440b540700a0303511801e000c12038103130419591403641e1280d9030754104a51020f441450300568070a200c0340140d582d0000403801d201c00c80d64049160030621811400d0800a605c0100700075010085c80000f02004550075078410301800825480d1702c0d46047c100064402d13404001c055000c0000c080c201c60f441203882404400079030342c400c003c40e1104000801191003c4c007001d4003240c0c0e2000e050038070041d0a249100115410000d403400e00700c405104406242c40c502d401c07640398200400501c12428400010055a4103540090101450054401da151041580401c646110400560007414020800040915486074500f5070b03454950521540c02c0e003041e6483c00203942812000034496100c0d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 122862976 1250 122861726 122861729
    0x41701060f0e04020303040b030c0c1203060109060c1104051807091505040b011e020a0201021c0905060a2714120304060e040b0d0812010f14090a0e070305031305030601 74
    0x4803070008505002c600716000c04000c0080ba40741c84208000300e0003030203542c041e500070200300007025120030503060071905100c000011140c200758240104140c0342ea00860010807074513a030600c041d668a480c1400d142c2d00c0704c0c003610a5009402e007024005071208005200c0c41c50f680b810f0560381c20307649401c0c90b8070680d140001130f60709508a400080c0b10514042d40301035405c1005042100d501404010321004c0349891128440140e00001500c3c1c040d541c050241c0b1040c22980c203040403082140c0d510140621b5a90f00905016200c04101554020700651901070116102d064191b08454481c1c0030365841c055501800c5007160040010a0309404d103010f03080300400621020350305050410740111029a2071200e4590301a4880c4003421003a20b03900c0080d80c1403401000310075036611f418142e0a42088041c3e002001007590901c0810404082e031072224580740d02203c0c1024503403100308021014001820030180075001e40c05c000802c0100010080217490198880100c02d56031350b204058594209 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 122864226 1250 122862976 122862989
    0x20d1409100e041d0303010f0608041e050f01060f17061612060e0405060708010e0f06060f041e06030e030405030307081605030406033c09060608030a0504170106 71
    0xd08000418090140380a02c641000140000958404c0c00b848125007110749080c020050f0400401884811040310702e0401030300c2181003244d031301c2c2000d03690b40c030b0b042948000510305560580d00b95004c01c03409026400c500b840220080c80b24588030240d2040880291250b5041c0072800c545071842600041646882a10304100c1c4401c42c201c9c1c03410035680070f4545118185420340c0c507000403c211191004290259001301b000740094507014501802260042e0440c4034040b18070710801c0394011011000d160302c06401d89500b5181d01c0c00030f6011049008541182004503810b00d901c0207030102075250b401c12500140d400707000e0340d1745013106651207100314010150903800800018000c100300000070404454a450000100d030389540740e5500703540044d004000040d40b41d210040030f02400041e182080c003041101801081c40292b60021400d81c5408000c0c0450786500110701801525441440103061680a40b556001141d0b8000c007554824010401c6001c8201c0200c0e040b42d00500c82d64003520103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 122865476 1250 122864226 122864239
    0xa060309080909060303160305090a0801180825060e0c011e05160602040b0a020d030b060703080411041e0513080301031511040308090f0d020f130905060403020d1409 73
    0x180414803c040301c0c028a0f081d01484200140300d0f28400006400e0800c40c041da0710346494211000410502e0b60842d481100c1584c10021154104500d0040140313440f54080780a0b44d80c2c0a01580601806403041c0ba0300703030000303c04c59981040c0601d40d00207920002e441c1054801d510440710040d00c44d00c4003220f400221704088920400030a0080004003000401000c22801841d190398840003a030340283c010794420b5030003143e0f0044c1280c04001c8415207203000c0c03c042c000c6144d180003048140c0a40000942041407400100b401c0c44103103d00c00e120b0f010040d0060003d541e1000300004041080c1c0507596640d458040044d14a03600307031b55800407903680411818696440c603265081ea000507100661503a540c0c82c882091782d0000d007030080c0015803084884035108c40d010800c1056600d00c480045000b4204240110300594595501c02041a02210fa08175058504041040104024007004200e0300c2100140b1040c15000101e0210064050f581c4503140030151184040324094940354075002032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 122866726 1250 122865476 122865487
    0x804050607030210020313031b15050601030e010501030b1803070b040803040203030d0e06010e0a02090901050111070305150f0618040b06010c02031c0210060b0f090a031b050a06030908 81
    0x1410400500041c1d00a00c11100b041030350f003035510b08981c8141c4032800441c0f0f00c04514000c0507000350305149801c03c4104250351450503901d0311106c001413514085115542c0b1000500b40c1da000303a2180803e4111030008110b551384901c1c044203005001e80303000803900c40d41e10380c07038504500001c211504c1c1b9503c0300c0031140c01c1e240c559540c00c45410140c402c0368940410700200c422072400c1e01c2407608018170300c0000c00c0c40303501d402642c020200015040c58502070040010115548a5006140c1120021f01c1c0035180c02c0140c0c41024109181508020300138000c03001ca0119141c01404440d001d014042680f43c91521030b0400c000c0b283c2005900c0f12481e005e640e0000d0085680002003a61148040c1058508060183d0000741407400c0001000c030303c071050401104a0640c104442c40802d03802c40420000c171420710400741c0b80342c040c5d0002c1e41c4801c400001ca40c8181d41314981e51400031031b844225602d850b40747e91300c42040340b05280200d038060043c60708001221480303402116602d0340c01261140c03901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 122867976 1250 122866726 122866729
    0x408030415050c0a030e19060206070807142701050a0801090e030706020412050c03070605041a04051002030d05090a0b010e070903120c05010506101e09150e1804080405 74
    0xc2241ea0714400703114003800150b40b120403d022580d9042c2c4a542c608035408075a008211441203900c039083e1402002e4041031061540015500e074118109082404c030941c2c1e4400112528040c0c0781104100c02000315011105507441e16007550341e5112040300e400d4512170364004450b02d008000d900c4002642c1c91004101c14030007540450000108102900d28248481c0c035640181da1041e44140c04881d55009a0f4091103014050300000c80401c43c06050310500d0301c0401001070055005410380000c078030007140341941c0d424044030300402016010151120325070402075101c1c2c110714542d4150905100024a007030b4008076169254942c1f040c04a610b5908040c0e0b4511384000007420082800307503040010007c280c00062074a00f200b000d0340e800802580901e805829140d002d0011400b910350f098204003541d401c45903107855050341d9034042c5695280c1d910b040390900c3d202d074003444108000340c1900c44619400305d410401c40c01309885035005400c2c084991102c0d00c00854000d40040c000f840284120b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 122869226 1250 122867976 122867999
    0x70302090a0e0c190e0f150409022103130807050901090524030114040602130b03040b07050c15010801060906060c2d080d0507030e06090601090b0d0b04032304080304 73
    0x44942905614540745d071200180350100340280e4490020880c0c4608001c600e00b12080c40c3c8001d024251000d00c1030400702c0c0c0c04104412103170780001030700c100444411f027008a070410544802c802d03005500c0c03040c140c3e96008907440b203040380940c1d801102d006001080bc8140750003071602800784507114101e04e0807010104078101510705111645552a003c4200000f140d00200314000d1303000702030050f42c44650b4041d010490301142d10188880b00240308101c00306000c40c28450303104644e42045690784d080c2c00c00707540c149940e6403855804030080d0400460b041c00705510030019500300307800410000e42c0312a03054503042140b20000f000c1292105002c8880000084030700350b00d1503402c10021826131180e0b00c4841c681c10468500d01c26a039160204100d0544c14000c9080f9580003201401550504901e4ce5440720300c14010704401e03c0e142c0d0000390705a01c0d030501041c40280c11504c00e4016040524005020215030460071501c1803001030078000c0300b03c40d00219401c0310b901400840c502858408180003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 122870476 1250 122869226 122869249
    0x10303050d02040e09010b01030606030c120b04060503071203030605010c1e0302030d0905010b0405060d020d080304080702060f13051903030e0310020f04030b1e010302011b05010c02070302090a0e0c 87
    0x3061034080c000014441030700202c4c0c41c0111004000800c0000c071020004044070a01e07409141018100020148080e0f00101c500e09004420000031036003a03402800709000c0c0c9840d9111a403d44101d00c03000464110f280c0340304103c00c1c4a55814018107580b4001118448600c04002d0040c0c000c61858010524202c1d103a158000c2c402d0040c0c3c2d0034a0074407c803110807650402802c0e601a5100d03070782d140c0103191500c00c285d40b01d40e00712028000402150081031046044250080005000101003824002c1d0303402a11043c6500602c001d80e00c203807150240900350000049200080e92660b40404e8914001072042590010b1000940d0390b07620310348084802e904614036040c1c0501620000d00f0441c0054002000c5020030f07003000540e01c916514009461440c0240a12403048e25802070501a0507910440d40c1106e80900e845d0540c1e124880c12070420760001c00000f000b035032800030007480c0c13940c010a94000f01ca008480000390365a0b0b141d014010303103201ca81a50034a41048690200740e143c21440d60a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 122871726 1250 122870476 122870497
    0xc060d0b0109170a06110a050a0c03050d0603200108010e1303090305070f1a0405030c0411090a09050115020a05030703030e07360b030604020f04020f0d060e060105030f01030305 78
    0x80300c16a0f581140074810f054040b80200f40e0700002205030600149020b21181590002e07001c901e410080c0000806a01030840d490040256030b0122806040c82101078070401c0c03219010030450150760b4074000711584000403120740035803680c0c030483d401c56000c2d0030468102c0b002c080c24003c03070f599164a01018207811003030403014880780030341c044081101000782c00080e0000184000540c1c0c100218003108503405844000519810803041c4501c1d1800b050b030108508050783c020ac5c00d2080c0a101c0601802202125500a0240e0303200140024982d040b150490301941a02c1042420641040f6180c007403090029200d540100804000640302c1d50089812118213000d58580a032180200bc008076843c0c07503100b001940000392106015014400c030290b40b820910104001c50040c0c021036111100180701074401c1a643c40b0050351070315240c04407201c181e038111080c3c0d6561500050000202218000c00d50346414030000110300354022400c6901500c41460b03445150380c41c59904031000c0e0300401848 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 122872976 1250 122871726 122871737
    0x6020310080106090b041b0f050706140405011a032406010507080c0604021c031706030304051008010e100b0d0c0c020a081e060c0405120a02030303010803070c05030c060d0b01 77
    0x7401480a22410001d070001c4480800c0c902c01003402c000070744400c1680b00301c400010040301c61219400c85000c640c080c0590402540361241403c10800410015606c98410050304040104001c1c043d400404103030030340001e0111800c03080d414117031364140c221091610304102170101d98400a5003002d456200c20145405480e0105943d142c00464210380703200b0030750b5071140e000d10003180303031003c0f1465003070540104898001c1e00544005101000e01c942040642000c003001c1070305030724103100301c601030140135201f5014540381c448020300c205024480c4080070300101e0081901c2d505000c0f4440100d030700124082d0b00703044e440c0e66548001c0101040c2c84060101590b4501c0040e150420984000c0c0041c401415101061444414110088485c00d6040d40c01a80410603000d00c040241d800351041500da501a03040206071543c0740880c203280195241c800030000203004000080104042840740c084407a0301641c0b4401e09d540c5144a502d25680000e0500456480d00900c0d032100c0500390051420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 122874226 1250 122872976 122872979
    0x9060706150f0f0801060501020c0121141e0a021315030b09100312080402010f140c010603060c020f030c0a060b0127050111060412050a05071401050a0e06090a06020310 74
    0x80b00c0900e25158041401001042d00420940500b841400c00401080c00540751805210303000030450700d44900c008082580322551441d60841960044503c2c17411096040c1e11400c1c54080c034540c882411115241084c04d40b000109040101d0094480c852440d00c1c02c20411401c20b04401070b40000a19888101551440340310181d58580268502030046461907040a5003541084036401d840c190300d080034418510148401070341d2209000041c0c00d060302d03000d1054000d040b9070146034418405007042960a054000c018450250f10003604003800d80c00311034107100e403211600d40702d01600750b1003420b80e041020101c0200d04c494000b403080c120145000000c0314580c02d40e000043c1011084d050b03901442d00740c14801c658200d00e110f540040e21100800c16440c00d40d0303400040741d40c0005030900300880481c208890a0080d025110f0b02984a10040840681501e001c0d008200807a07440540d1410030011100c02080401c04a010300b0303520015080c0d10300c6940b40c1e0000f0758409050300782c8125442e42c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 122875476 1250 122874226 122874239
    0x1e051212041221120506040207080c0105100e07080109150518011806030b0c07030507290a0507020606040c122405030f1902130c0503070f050906070615 67
    0x601c05801d122401c2c111207850760030043c0c0c0e0003202245545440e0b00c5498030100359a009004408000401c4001141c0b0b43d950401140203402607800040400c2da001c500e580e1001c50641003544185060020000c105035102070040458030280c1c2e0680c0401c0c0711a0050128890130340203003840309590003144110643d0381c40403482c0440d810300c000280c0700c2114010f111692200500422540000105010842c115228a501002c020388803071a000d8000440104143c012000d803040650044850140c5d14450f4030307610a140084d4030341e030500d600101c00042140b01e09100740b50203002c2d0307540107200c81c0d500c0e00b041c0001000321105010a01100148001d05042c9600604210130183e8030181d0a845540154411040b0f4640046121b0307080200c0740190403034002490014160f100060290780f040034004a0001d00c245607103403040c5030038140980c031801e41000041d802045240d07030f03020808040d090111880e0081076502984030004101440c08036215030040080e00301c82600001c0070341c4d0f4898 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 122876726 1250 122875476 122875513
    0x2107051903050a090e010602030405060306031908040806060d0825080408100e03070819110109080304110d020102120714010c090503160e010302040504060b0d08131e0512 75
    0x48000500c0050a483c20030341c000204001403045240b4490207506080300a5181c1c0124011180070b601d0101c0080d80c1c961301088001c2101c00b030044a014a40b00c0d030b00741480c20380c0c028061410b10b803244a0200c0c5450800b81e03028220b140e00b0400942c14241907c00c0e10120f988030000d540c105800d048510004501008002e2000b04040c000814000034841032510984a1083c288181c3d50414030500300483c81c587e0484883d442c3e042d0000720318159000c42611455107001800c000782d031a00400741c08115902008502680c06600b49020785a1100104107004114850090041e000480d601080c809400e0180645900c600100d007201428182c42c6405c440d1040c5e000b20010326109010440750a06118052400303460300004100b5a0400944400684040c803000f400385603960002414460594401405007000070002081e4840302c0c2070a0145401c41c00c282c0001d05100440014480344103064240c3e0f803070350b944040844900d42800c0101d6105507400392000c2d0f002e559181044001d400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 122877976 1250 122876726 122876773
    0x313050a060507050d0b0a0b120601092115150b030915100e07020d05040e130b0a0b0a0f0f030f050114090604050d050423011101060b0301080c03210705 67
    0x142c0e613298590045c1c414000941d601c807150180140200c0750103001e0700b02c1c42021120000b8002c01c402407240c440000407031302141c1f02e5004048080c0c59070130041119200078042c00c05c05d40941080c01d580c85c82112032500302c66400800422050070481b0410411449401030b55011964600369440c003a407600060080c4a0110342c5d45040075541d0f00b080c840c4003c59039202d81c00042c1c40c40180040e540441003e89203215500520103241c100c00005040c0b00b070740c1000200001da10242c041c01e03d003466080140580321800010784600d850903c0842c1c02781c4042381d860115092502c03801a04c5155031500903030100181d20550b05552200a400d001c1d0804110701c0b0702400e01c00d40140b6007864541000f50a00760012002d10401004120400085600a00c1017070f0610050b1840c60804443c10016124407031035013043c80c40c55090400c0011141d00c1e08026504032850300c01070320310014403841007507181c0e440340b4548240191450307042c8a1424081c80a0440240f00b1001c490b050900c0502282d03001240 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 122879226 1250 122877976 122877991
    0x405041115090406090b01021e101b0905010509010c0615030503120403030b03030306090106050c15010609050f03010207081e0d06030b0a0e0106030507150504090e1606090b0313050a0605 82
    0x402e20303180d00302031041a0090000c128100050051100001c1d1a050640f030b516071624102d004240c2c500009008014011001c0c407001c1002786046031070382070394402c040b0044003c60840000020300f07500803001c139072140805035551655000d890751100020b12030039003001031142000c82e020000900800c01840400402d0641100d0b9150902d402030954101c0d82d840c0740070360403c2c404e1141f1900c1c0c4040107810b441c83c3d070900c40d80b50015400c2c03042c0340c201c1110034041034007003c400000f4444d801070040c00584805940c1520310580f400107050a030321968400408a510400600b51701410050350009102803d0484914296200500000f0381b0302c6901300b80c91150040e020300c0720071031582c411149032841c4a402404510300e1a103a45440e000c492003080b251020350000207600318465030440b000740030062820011403070b0745180269070301e520113440d51048031145008103070a03008042c01d5049070714840903540385a0322000d81c41552115890110351900c101103072000054103502419114580 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 122880476 1250 122879226 122879269
    0x70c03060209092202010305060d1a06010e030a0c06030b0a03060905060114031504020105030a090209090307120935060711160803071b0e100905010b041404050411 72
    0x450700c04000c203482020780613180440d030110701c20110210030108000e809809080020703040d510040840c03440501c50398000c25001414114000e5204942c030214004e1400781d840b1003181c5d10b40342c240b50362115a02d4010740042e0f403104080000170701c80d811508042d4006040491074940e40d070b8070031040c0da07a00a41140c3d950803003070050001d014481491440c4440441c010029000c1024001082600192019040101c00000120320303070165040f8202d2507502414070002d51030b00c880095125000000c0460700c4003c50f007150a04140b08100c00c03010303140007244000e10fa00e06030810402d18004d07030f80d03138200000210048404c040814089140701e15690740b1070042d54a0441582c42c142401001e921b083c0c07003602c0b0810711440c80000182c0313492540c0048c5c1d0380011f852101d800b038100c0a250f40304030340444464080001e41c0544801407030489007841000e03c00c0f40d80383c200c00c11a038021406140d5001004035880b40c81c03894030703030803098025008002d81c3c4072060344035011651520844011009820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 122881726 1250 122880476 122880487
    0xa0206040b030f100302090402041109060d060503060f061e0d06050109090c0501031e090c080d020f070501020c131a06130815061809010209090f0601020616140a05070c030602 77
    0x340890388150344403c080d00b0311304d01281998001880054042e001034002e6a03200d2441e80078043c00303011140e803404000d01068441210751039200140500d4002c59000b80a42404a000700030646a4075010b400d00400300b041e0f401220040503001c8001c54182e607803250140900d040819054498940030700b03040d04011076401002d04003002c3c107010990041d810540341001d8185984003038217003861a0604c0f0040484d0040050404100c001c049400010340c0d405500c1410421980000c0c0c0b000d4070100304420b54800c103907280c0041e0b84070000103610903040009020780100a000a500501400f003820208040002008020800d03c0d000542e0300007440012200034441900100555610308600c505003405030303c1c00102080300203960303e00504040b803044001c24240709003901a10307000c180190080341d60740b5101c02041c02130318065a0351409070061a011035840018640e6900c4c041c030441d1555103d01c8000c44000c0c00e2a4888282d0004014090040000240c003010300d840086005800158446 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 122882976 1250 122881726 122881741
    0x316060e1516180302060406210209060304081c1d07090b0303090609010c06180204060b07050607120e0a0b040c050d1122090f030906050f16050a0206040b03 69
    0x10311140001c80a41880008000ca001006480d4203204601ea24045a842c0e18210440c1150485500000d600c0500428041070b41030b800030813482e5601c00441104010050481500300303d204a078121900403000b0000200401e01c160000c0c0030300300681c03c42c0516074840200c00ca08035560400c0a08905200c101340d21b95000d01002a03502628240c00100b00f08080000001d42e80d01c118007089002e10400b280c20314041e80104040c17008181c00c12414401c00e624407149407481c501f0b04038200d2013145406030200b1202c01c20426602100d40c007200401e2203882d0103000fa01c0f6055080d400c054034035215002c503004030070f052007242000c42c4034040060407400d003440c2007840c0842580020303010f104a01c90310004506280640d402040c2c0a40d50392008042540c98506803049101c403c0702d109040030070340020405403003d551089800391307964214843d26a81c04482c280725034044519440030621044030004c1d04600c012603030500c00d404540f0300b0300d0268046100b680150340654068500442004407c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 122884226 1250 122882976 122882983
    0x504051008070e0a0503061801110d150f1412070807080a05010b01020607020304120c0909030f02011a0a0302060309012a080108070b1209070b0f040815010f0608090316060e 76
    0x801c8484d860611705040101c0c0c2d8425000700311f0910141030f51503c20b801034084d40000240c200b0040c00503600c1d0324418811029250058400030345110040d00000c0c40d082010045069a103003005980315448590200709610030251400e1029014181001450301c004120a100038042d410203400000d501e42485801c652803002c255065401030010406007603800b01c2102c040d1108a1281e00750740480382801c0d0001000d0750800d0b01110328281c07019007859000740c001e43c03056520ba03000340002010b0034a061101034641c210350750402c0d010319003403005140040166500c92513000001504403035104940f0450b0385445111414420442d640c404150ba01c214224003404103a402064a0792805580d00402d00c40d010400301403440f401c0106205c441e003406000c0c010075800081c1c0707071162204400c1480b507a00c54810036049202d1007891004078000095105d040300d50003007500d400c41d454010191100302c0010300903040e03804200411441144030811102045005110001c0d000500c1100c3c24034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 122885476 1250 122884226 122884247
    0xb010305060406030f02011d0a0b030a05090106050604091a030a080c060c07080307050304021206160906260402150408100b0103090b1b09061b0c060c030415050405100807 75
    0x76a043c40f4060010480181e5060740f8a9030a281c03c24440940b02002810144511489a8010307480000050319541e208050350094000440412103a21040c100b142207881d684601e6809c25800e003c10040240c65912401c0034918580c0240d18440134580041c0c204101e1400449100b200861600c01e080020412150300600d1020014a00050794482044500008049100304080040010210340318446040003c10607901101d10500740407410300c802006482c41500010380e10301001031038600c02c2801c0406c40300f0104804981c1c090920309100365000c010010781c2c10602c0754507082180480300004200802e03205003d0002600d10b14102016100100702c868105818108802c010500000c0c056802c1403980e5a00b00c0c10704030518000909002d80c82c01d01c0e6110304045503049804004038a800300548002c025104640304c440200071180c05580d20101555000740402d1209109600030003442c0d1159080c190705007984c943c0000d140300304c80700710300c40050085404d0200541e081200c102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 122886726 1250 122885476 122885479
    0xf070b04031b1211062b0513020109030609060e10060608010f270b03010207050f060108031e13090c03020a090b0f120a09050604051605010801140609120601090b01030506 75
    0x100181d140ca290101c101c0003600c0041d0006a00103040c907469610381e4210ba001d50a50b0b0000080e107000490581c031b141562102d9820900e0401000886070070f040000102959416102c140c00c00d411521000c0007440001d0701100d000765038040081c01f444007007188500c20010240042002403c04034010225041a03005855041c0035809c04d124060001510025507007903500403a5201101e80413150180200c408020b07050b510004022081c0704001c030300311801383c82c0340003102c209990b18202c10340c0d648a0b101001c1000342700e180800d60341b0000c43d4002c00f90000c8032000f910140717850b80310704011034400c82060300110750300041d414100b580290301c0500030f101c2150264100900407040790007070311619003030040c10003503540043e01562041e070041c2400742c0c0140072241a4a01890003071f55800003412082814042054006079a6102e007020f0341c142c8038450009030202d082d420134480e458110b12807180d4007500484003083d04200c20072082e0700a0210110104034044d44e000094111040a003800c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 122887976 1250 122886726 122886773
    0x1b030c0504051c0606050a060504140a0515030703090203100e0624010f020102070f0b1b13050d02010516030306050f010903020901030206030408070605150907020102070c06050a020f070b0403 84
    0x2080b00f81e540710f0420a00d074000600c02c0142c0910391410100509032500b05a601c0b819400d0003250f8a54854040e0003500d42006075030310816110820000e0364400b5104456100740c1076164184480c030008041e582254250070041580b016503400281041c02c03000d803901d0044d5490340c1d44820800700b0405590442c00d42c80c1c0030004040c0035886140d031482d20240103070602074200800b44100b4400d40c111201c882d0020025695008a40b0381015144d001307448405da200805401d029a0801c0003040b21003201000118007481491320040c01003d180b017500903030500000f03002c1c0c0402d02031100c11050006100350303800280d560502c1704020318030900c4d04500d0304220f01040d040c40141c0321495142d055a0b0102c46658030381c0e549150003405442420802401e5a0500c0140000e90280da803038080120b600300c1c0c20740303220f541d2800c0480c200d00480740080c0509180c4402000040e0040009126900480c070649001000e000e8149241070000d503c41f119413000000c04000380444502000303212944d29088 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 122889226 1250 122887976 122887979
    0x30f0504170a02030c07030503040509010608010b300901050a0c09030201170a0b06070f0303050123010c06110403030e030708010510090209061c0b01120c020a0311030d1b030c0504 79
    0xc80200202816140c821110006044502d1034002c00941d1100381c003280c2201c114548070701d0300030340ba07410500c1130341e02503144030700003045050150b840141620740da020380e40d051030f5441440009c81050510814110000304003044640300380384012a2141034540004074550600c6000030b402c0341c032015802002c11001100510050382d201100c0d082102d4410003401d41e0f03445000350310000342145011568881c40000d881c60801c40c0102500d21060b000c2e8508220681c0e0f2010000c404d60031909031035050b25010f43d1201c5072503000300e60a0181900035a000102c85440c1000549241e2007030f04250007090700070441d01d180707140801c0428080c04058000f80010f003014030301910380f10490702402090907000700300190726440e1202a224100c01e4800503000658801c00b6640017007501440320350014a0248200ca42c0895034021503000418030b40c000c01e14548540c0b0f00b110787c0d1462544401d4140820407003003041407400e02508041280291032010300103500500a0104c541080c405814000709020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 122890476 1250 122889226 122889233
    0x140306061212031807080601030c091b050a020c04020f0702040f0905031605150a0203060108070906050f090a0b04150f03180b0406021308010c02010e1612050a0c06050901030f0504 79
    0x2241c2d1048502c40c05040d03165218050800c0030550443d900ca903080c418181d001543c40d800217426412280114000c1207010744907201e007000e1380d25181d1000310580003890030581451040000b0861200148196508a01503100140a9038000440c1c81c0766558003186413020352a041c130402d0700320451140200000310341603444985034015a1520401045064845800e100c0103000b224505105012501960704d001d804c028000e4106a036502d001619820000d030116000750045816915581c070b0725410038401c0f1161001940c489880f00b030b00f01d00306540024071a025000600040c00000980c5045c640b40c00380010b00c90a483c00710802014200064000b4221000500b51f400541003819541a541c4a040560191150081c1d02d1220313103000c00001074030501907003c0314440c04113a00038061041e034480712690f5200001c040000b59030501a040002070f1480742c11842c40b5100c3d00548000c6100d035120070701640040c0d4401800710f44d0008401e0929a814412800002402141003105040c1600d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 122891726 1250 122890476 122890483
    0x90b0f06130e071101090303050a0b01080717060112110903010506090f150f0d05010e3903070b0a0507031701080a03030e0c0a330c080d060905011403060612 69
    0xc0b03240030341881800410407540c81408030030540c00b0500c00038804103805150083c000c180403034407100134600e0454242040e6100d000691b000d000b090765070b0368071303140c00359a041814030000e804a81884039641078001050400e0041c0891501000c0c2040c0c1c6901c1c81600b0306081d5000200380d58441c41001c01080401c4035884030345508260000400307500b6503180c0d0701041109001031a506d5204031540c9400040010540044000c40900000c3c1c40150000c03208003900b0344005040300c0d00510012481a04626601030f109000201c010115807903c1e594030404a1158040200b80700001ea0000d451020b00d50440b5000070021110030f8840f0b81c42d898030300d2240e00c0308041800107040545502004112610800049000c444010101d501c0d50359601390201c070030007034030981e21446c620981440e1804120100c1e108035203000740c2c648040e400b030a03a480140503840520010070441d40c0e40e5010455014900c1a076011340104c4401e101480c076814105403501e900104014031070380c01c55582052503000407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 122892976 1250 122891726 122891729
    0x503131403030f031e01080c03010e0d020c0906190e0f0c041a0702010905061308010509030313020108070306080d081e04080405040b0d0203030c03130f06020316031107090b0f0613 79
    0xc50a541c0c0b40c0e21525040714198a02c4483c0f0360008030700c0c02c001f040c0008041481c0844140840c0200980f41200b500d26880c1c003004403080b40580c119002d0780d1381e00d0812034981544460020410b4071000c00c6092606004402c9d60071215252034004100150045000c01150300103840741c800c241018509490080b038000020820307100c40a001c507002c0d045900030029a006414010161a241c02100c0704104424849100e144015030805000c070b464440040101da008440303629410300c64000e10340066910500c0545050101981c901c00020304400611101a01410590b03d022075401d1003a145041c4845c8540d40e0004c091911081c080091845012501100c1040e074001c03c07401c0070803000039a90b220448010750036010003d043c4501070300100051400040070084e102d60301d515910755126280d12409205c1c003681c002c0141e01d03d205051012000c00303038806d10341441c00000310300c0e07105d00708040d5a000c54070701ca40b1044411040d18004200004688066600508160350100c80102c002d849 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 122894226 1250 122892976 122892997
    0x7020a0b0a0f020d060311040b0103090b0601030b01020a060606171608060907020a02090903120c04030506070309060603240f1119170132010c0b070306080a050313140303 75
    0x20350074008000b90568054a107494800001045407070703a281402c0704a0100c020381507100700c0c54a81d48125540c041d2140062242d00032542c20300715500e0000650083c0071030017040381540300e80c6040d6400102c59003c1c01002e440a9a01c110800d60001608000c03510044d2100b5030042d24626076990303041d44002060b0b8400022140b2400e15111070800b40e0400801c2c84c00690020845000c22071140c4000004241200544105104980d18803100c107000f8022401b0051141c0c2210700810040c61094004102040c0141c4000649590f640d64049400c50140c3c1031a01004550449401e0062580308507008240c490905110b1200e20303440010b824400d5030103c03592142017889000006108001400c80c0343d20740c0c100c00d0100d584808907800e8a0380c40880f5507051074408000010481e8a010031508201410b0310303407400c0400143e54244400d80010045002c06d0351707070b52002480c0c0b0010048840b0b030030702840c00b4580d03988520f590407803030340b08980140c010400c16102510042d2400011507008212 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 122895476 1250 122894226 122894231
    0x603020906071106161112031608070c05100e0f010305010f0509180d0804111009060e0d05100c090e0402150a0905040204060f1106040803010b0f04080604110907020a0b0a 75
    0x183c00c002851402220641494908004030351403c000d011603064000c0e0800700e174103800310140142140d6491141c4460700c5151901c1c0121360001480000c0a400c0c0c05d0720601040c11b4841c2c90310003040303901107441e10300d40c0010041c0001c104031b03040852a101c1020000e18083c0070380d41c14024258501c1003a480b44900628841d40020250354510408007258189a000d039080502888001440803d00303503030644400b56255912440c038540000c2001e908441c0f511004400d83c6462800d440d0040b46a0450750441c2818442c031000650070701c41c0b056010b2001b03500099000c88800010b0040580f03030800c13084c1c20000c90900016a58031204111945d00d46940c007a40c80c00000c81c1110302581c0d5900c815001380c00410045440b0781c06c081d44101045699440d4403802c1140c856040ea070310720948000d000c4200400c010b010105860004081d0f00f09a800074524203507680010910340758007102c1c16613064081003218010f0b03140002c4000d0b0030043ca440103148030080c0d41c9405102c000064090841c069 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 122896726 1250 122895476 122895503
    0x30309060f1902010c120501320d08130b0412060b06160f0201121401031e050303100306050601020a05060610090e13060b012109020a030807050309010801060302090607 74
    0x1400c440032980c0414882c850144805551007029000e8004001c03030300e01080030100c0038505040d284c82003a040300d0241010040324192010549034980e031240030b0505041020900703140c25110050726100d418824a4580d0340ea624090280c103607070800b0740146980c60020042008a401080205000580c2001002440d008110009107052142056841c01c240c04503201c4000d10110407800d50b4464000c4c0c03502654040c100111404403404801c0000020300794100520104550011030810910761404428000c241c2d901c42514503001201c90103451000c6030801d00800c0030321b00549410803801e00051101c43c50b036565490319201e00814041c01400e010b52151a610321400d00380d0018205420114101e080a0038001407802c2007500903906103007441c18101c015441510782e10001401d20441c510246403134141507000d0141201c040e40d0007110488081302062411004000d8140303e171005540c0c80021000261925005034061000e061040c400c459040e16244d08517082d1903407000a540405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 122897976 1250 122896726 122896747
    0x30f0405101701080d0201050a0b01080415150801020310080106030f03180321020f0c0109260f10051b0d020a0309080d02040f140607080c0703021309030f08040203030906 75
    0x2c101a000300d2500c6500400042e1940010440b01003801e03042d802032104e41c0d1869401c1c401d840d2640780380c1d40000c41c0c11000601003104450010034442407890040f510b0342040001030030307503003030f9402800c1241d50000900080345c1d80b200e940b400134202c0d08001e100c146c0c070356111681541c0700064060284103001101403004041d0f0804c120140d036200c030720304402d0041c2c0340d05100540403640707280f405441502c0b003022040000103440b29502130141d40765841c1904054400c801d81380c0d801503509012903910103450804d0028170004002910103001000640c0d004081313507042d600b01604242a40b600403d5208158611707504685480400b104007623078070a407400d8114001c00b1b45c01c00252901602040091144289400a00884074541c0f040013030070b40c4a02d2511141c540e03030207401d035000a04009607000540020040c2003e601e004082c0c928285c2d49401080002000c0017440303e00d00e9540114600700b541008285100000034540400503250a07400309031360f0312800045900ca800c0100d21842c49 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 122899226 1250 122897976 122897987
    0x603040501110f04091d06070302090a0e0708040c14030303010303030c1e05030a141302100207080a0b0703060b0c07090f020f04180e120304030c140f070512030f040510 74
    0x425809905043e615440c0b02c035060820740280c054a00a1400c00e002d000c0f031246040200c84030b0310716070009407070151901d100944c0290301c5903002c2070700f11030500340000c3d2030110f00c0d2030781c0e10500301515001042d280a02e0020b200507143c1c0c10110001d03c0c0102840003948000065a042d00e90504000a81508030001503c0400441d581c000c6d80c0e0a128450b1403e003039001003c2c40c002d600040003800325299180e182d0084560403290590105484800c10025180040c011000c2105030b0040e10512521104258100702c1c1720a82a03c541c0706d184140704280394944228002407c614411500305010080d103107854182c0c0b44a05402e060f00c80401740a074807229411604034201c218455a1f0b034581c0e0b10340b051001408020440196850000890010a0045489006030311203c030014a5030b5503a5509441d80d00c2c07012400e43d00540114888080d07a5001c01070b04910401e0100101005441c010400150321181c94500d284c90300148201850011000199000c0c0d590454800c4511030106004596 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 122900476 1250 122899226 122899241
    0x708040b060d02120d270501021f1103010303020c030c0411030a050709080a150501060f05030a1a1815100f030b0310110c0601090615080403020a0803090f060105040501140603040501 80
    0x901512a2289017280c100c509550b100c101d0980f03820244501c800c0010740400e45129041c00358004401c4c4420b29645025200740181620800050381d0b180700e07032000501e40003600210b0140c1d008201821842c6010003402d1800507046405001c00000d0b690307a00900d00020780001c909503101c5000c10302950051300c410010300100307001c440010354141410300350f1045c01e50414032040d00c0d11b4000305110303115070110001a01c0603210603103142c4801352041e0080c0008904411510b10340f640d0002d0320740c1c0300d002ca982e1000707012000b20020700b0b19007006080c0c4804480d00c140f0580c0040c07031008555400c0b107204005203455042c00168a200d450104e803e00e40001e0740401c0d40b52421031040f5448003500050040c0d05003000841e1620383e25480380c182114001d000e1040003d901100b0440100e22810465521a12901c140c4050000035a5006d103207800981c1c03541c9032900150b52200790044c0070081940100400c640611003540743c07680d11003410b1119140c850080000000040c1404025000200b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 122901726 1250 122900476 122900509
    0x6050c030c1c0905010c02250f060c050c0406120501050a0606020c1e090a0204030c1202150c031308061608040804030609080c030d0501090b040b030606010e180901060801050708040b060d02 83
    0x20f02400d1b02009448000a62a100c0e0040b0b080388c1d4210544107408040d0b040c0e07600c2d08142c0112031709102e410b48402d0061902201c0b184101060390030316450380d000700f200070003050945601c0030844c0e1030607509540004095102040c5040002c025465002442004821003a90782140440c007400c01800e90131100c1149641041c08482400b5055100350700800c200c07802407040101c140c0d2100c3c1400110741100300065804030300943c1000c100f540802c01800c000c50900c046a00e49241004020840300017540800b0050b04640104641012802800f036070407016464000032919050f0707150310403401140005004240e84030300d034200700300200302124504840181180c1e20740381c006401c0c0014100034010300c2e004900305910801e0608040c0201020500000d000d4007883e640c05004492002c2320340d4060340d22001c0d01000c120345944000c145805000c4550001c141c281c10402c82501b074400203400a000c01807040100300106050310a00e58003c00202d800c0641e44110b0300024105902c18140351 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 122902976 1250 122901726 122901731
    0xa0506040615120f05061326120405010906060b0405060412081c050402031902010206070305060402160809091506040311030c1c030207060203180d080d050106050706050c030c1c090501 81
    0x40d403c4c00001043c65203964807400440b01c0c0d030394605c2458a80e860710305100900c026800e18011031a5080180412001e245400318941050701360041c060b00c849040d00d0540e0541d54030030720001800054014a80603242e00d0702058a030619103c0410352903c01c1e440b5200561280030b000d00c040054102c211841d003040030307400b040c0010106094130020003055404901ca84154070500c90f0942c40f07070010650b10354058000d46480d91703c10340c080e40903040003807180d544907a0070030000604d4082c0c0140303120030034040c21a5580380c0d83c001c0240410b0500c09003803004024110402c4a403540c0e00c1808079800e07241d00880e24030500c0058000310340b0344401e08040aa01400086000741120301c010304405045000750708031840c880d030341c02c4260789038440c806559905480145c071020740c504041d0b6240210308d100d00c24151410017000004002c0b1038080e0000000644005215003c1c440c0d00d0040a40202100402c18030b1802d1a903010a06480b0b80400103100801c408013200200c403056025403000e68000009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 122904226 1250 122902976 122903009
    0x1b14130e0303010e161407110f0603070315080f03041806030c0b0307030f0b0105031f03020405070504180b061903150b0a1103090f0f0a03050d020610080a0506040615 73
    0x2100c2c10400445d214491400707407115107080c41d4490200090462204a035107450a00c0549440c6803c8400c141c1454100c03481c000018030070b48900e402184079100c01e40e03002a001442c264039542905203030f40141d0990703001408116899501008850444e01c00800ca069148040f03030448010704800c0d0b00190030940702200004681c3c2c1c2c002c0080d403284105640400c0160090540b00d4212109560385500088080c0300003105c1441071010404007201040074a0700c0e06540c5d600040030341d0000c881e4a0700042c40802c04204046a80d0092000801c00c21428040340c80d0321030226845015054000b070381400485850f402c114000d502c0108151798600909407002d0300c9548103143c1c0c0d03210708940ac00082002c2c0c103042c0c41c00804415141d40701c90040036506000e141c281004403481519010a610001c1e100b80040050420004070501440d10b401400c1036252200c0d01308100c0816500c07941050300300302c4880e030000c0c0010a15075030080c2e01120001ea81d180c18410380580301c040741c00c01c0984e285007901 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 122905476 1250 122904226 122904239
    0x105090a091e110906061c0b010507140106060f0918020a0e0d030309120c020a17030f0414131e150f03050102121b030103030c0f021005071b14130e030301 68
    0x10424a4200309a40001c01600d0360170a1010904c61032400c100700403020513001030801000e0700a6486110149010ba0a220b915180c0f004103a01506112145170740d00c5808006c940c2d00a24515000365045c00e01b2000716142006070900e4540103940b03020f01c00c0c1c4c0040d01c140928001c5145400840f00035000740d0041040b40f030060001c0507070301410b407420b5605920703440040f40729680300304620f540644084138461030701942101c1682032404070891800240502c080801581024000500d0048842509013607068203004201410390001c2403024281400b4507240c51307001e4000108211580f2000075a03035108200058401c4041c1c00503c0311200300d2100105100d41500640001f00b5080d850302d002e40c48201036002450f40c0214001b40d4148148010000700340aa14010200c074054102059611140d030b0004064442e241c180304c01040000c030703601052003014200c010a402410700580035443c00e00710300300000071180d8880d61140b4181724a060f13402286070072001c10041d07104200c1e900c0f5610780c031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 122906726 1250 122905476 122905493
    0xb0a030509060a020306010f0309050316120809010b1c02011107080d0801090c080408030a060503070e070807020c090612010219080601020d0203041a09030c090109150501080105090a091e 82
    0x291500182e114410120321030310040e100312805450140c45468154503106020342c09400c030720b002039410340014400307500f010910f05000e070b462a00c100c0030b16140507000f560280000c1006091140c45a1500c640d5405070b489080350200300400451105592108501c0100c4001a42c0d13492000d00e800348150024100100003042c0c0489450794880610076a00d0f10600c1085524040f03914000035100b0000c84d021480400040d50080e004850100709175480c6e8011a140c03030100d60003403003000b10410070808056880800a500502d140c405440030b40e80600002c1d1065101800f4a4880d0f02c5003601400301000941c1240c2c8030700300c000c136100f00d020509040a05084000c85825000d0b000301c00a95907502d1012003100c0540301e49201d164081b600011405406402c0b43c0d2031075405100d0700f0341e00030b4143c2e07038103000b81c0c020040e01034045603000c1d200c0c0d82d54110310360640c0110b050020450061005542d40030a1550012600c94000b03803c05c90307810040c0310384511181c078a13420551001140140709092 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 122907976 1250 122906726 122906731
    0x706121a0d060608070e1b0a020307050f0706121808030a0e060406050402091003051c030f05040b040c091406060c1c0806091501080a090c0f0f050907030605030d0e03070b0a0305 78
    0x224281c85c0340680c6d40c0f8420aa5070000c0312000d030101074158403084082c0380040540100040d41c812217081c200560744083c81d04540010f01c036056032200c081004519401800c1803281c0420f61010300a001540c403103d02942a0590020200a404000030300705442a510000314801500212483c03810030781003110081c60203403010390040003041c0014a81c0c61281c0c050900b2a54044020512900046005a48100381c603500c64100b41e25a00c14503401f282a001e0240104d0061001c48400c1c01d19140c104009000c076840000345600700203181550054420409030710403415951903070340d031360810002c600f0038544e0820f040c0b150758142d540d1170000d81d2048020b0712810068404940d02d4071241c5020b0700708a6015641800101880c0002c2c00c40c28050b0080011941b1404135440d40741d0b1152420b032808522500300100129818400b001140740c40821f1640141d56400e080140604010104e40c440003611342ca4010f10070b640800d1581603c00308010001454290344158440c021094024040c3c0000e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 122909226 1250 122907976 122907989
    0x519170d09020a050105131203050f0705010b0909070b1806040302040c050703020c0409111915020a021906020d051612050304021002120a030c050409020711120706121a0d0606 77
    0x3c0a038080390b41d50046044444054180200e00401ca20303100c20f0b140182994041101040814021110b0300c414800240c58070910640010694054180621555510050800f00d840d406811308002c4040050204d484040e02c02c080c05503407140013400f080051140d9800290800d18101101c486241d00c6406401f51a119500b5034051030320000400083e030329402d002a120a0f410b01100500d072414559440b05440c4982d102c11040d65255500c000010822001c0070250b044000c4070421403a008100950340c0740e25421044950b428007800950382d01040e648602030100c0042e141801d641c501d1044106035a001045c0c07040c80c850401d00403c90340041d0b4089000366219040710a04a00200b19581092100c04842e42403109483c01140506501c8508030140a010440412508424002070580e24083c2e00d613a071004c1082c005001101c404140c107655640c12001c0240001076001304064078000c0100fa010500c00407110b080c031540d60741c69901c00d43c8642191300c160104100f98002178100c500d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 122910476 1250 122909226 122909239
    0xe04180f15140105220c0906021204080c041806050a020a1b15020313170c06011d01090b060408160302090c070515090f030406120b010c0519170d0902 66
    0x500c8280301068594202d808011181c1c030100500042c20003803042640d080307500501100380e1181c1580c8608580d1086012000a0304031b01003402156010004100e0070031304006040c0c6010718100005464030392140d6654401da4640c188540c144113281c0070072071441c1c0c000c001005030f414041f240c0c20003940465811000309498004400301c0200312942c05a4080d002021060b40348600781140c07000b9800245504403055140b0340c01e0021410b0803041070004401044496554840060313000d140650503800004005441c415181e001e101079821281141d022400c04036803c42003d0002d42d85003e04d811680305407240f50341c14603004d008108003204981c005d54081105440da610b03c401e0600c24410040c0c202d40c4200000d10680302d10180456000308008103480c880d10041c4851070560780140d00450000e00d8a44103c3c4940301d0324800c0412000b82420004000d000982d541a12607000708030340102515100d0928081c4040303103841089407149418010b40d10440c59404074000d1904a1043c0c0c05250f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 122911726 1250 122910476 122910503
    0x717070206070e10020613030306120f021302070c060e0105040b0c03030610110304030b180111030a0b030c0108060d1104110703110d05030c03131e02040b1f0e04180f 73
    0x9000c005090015003030750103010350b586c1f150075002c00c82440c0f80303085003010b80d580f1b40022511504800210603500c00c1c400c070b10b04440d060040040312114440c0108101c0d2040008100060031441d0031012501c480c10300c50b0083d200400140c0f01c50107503900100c203103140011a8215804040000c5224820480e03202d0004011383c01c0444032a07411809201441e0720401c0280041112070003004c4e03000c01180c1900c060312541c652036500395440c940148a800b10040188690706005004902d2001d2050f0002c001c42401a00002c0c61001e025245902418051844030180101008003c070100e1000c0c0c024069503000c5036034050154448402680001c60860364010010b5002c14030300c003040e00a507a26415511540600011680043c00c184900e01c55011000d0000d900b40001c01d85002d0813030082d800c408030900520003521148030b034107031240d40d03c014100c90380c4001641d90844481c1624000003101e100c040842e0003000c41042c8a440003141c00d145808100e0780382411344e0b08a1085d010043c094 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 122912976 1250 122911726 122911729
    0x30f041203110601140d0606170703021806011407020f10020601060201061e0b0f0c07060509040b01030507021c0207050916020f060408090f060702130c0801080f03070b0717070206070e 81
    0xc030f0081c011010a0004c0000500540c5003041c449200700f402200c000030000d940f0b00200c2c1480301090700448094201603020004d51030102999200325109030300c1340c07802c2c2c41c000c0c0000748050031004081c030315080f010a42c401552280c4942000d44200941408068040b000c4081e680b000c09108200043d820030101040c0c81030410038001c0c0c1e42da0b154207103044042c18003a0f000c4164018180703181501000f0b0245201408082090000900c495141e0136914a010400e00c07003556003130a4124141400c010500c0000d960006016400880622201c50390202104080f400d10003a5840b06501068070402c0c8503041e455a0056035024290740c08031203103151100c20036034680d04109d4020702010410701001842d41000102aa11044020011483d0417615800100c40c9032043c0139030116556242d0281c080301e038001f61910b0140541900800c80a0f004c02c4103143d0301e11400d41c00400c002080340114003a80d0050344070100c00306408403d26218039080d440290388190803a0b074207000076040d08030345505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 122914226 1250 122912976 122912983
    0x3020f1207021e010209030c120a170a140901052218021903050f010303030e030d092109050a1202060904110a020105070e0a06081b0406020d082412030f04120311 71
    0x8082c02410710321000c5010440709c8116054030031014001e8800d04000250085420b840200740e0300600c90711511040b5006205000b03242c404074401c00304000544a90381c000060307480e080b502110a840103ca03c204044040303516074800e0f8921a204c0315000950300564002e0101d55203030031740741c0050340b1501c10101e0a50342c0503114442c3c440341031401800030900c00d0b0000840031360528203d910300400c141002080743c40c400c0341990f00a1a1540c070340c810300c0c0900c00e00f000c18540f9140040000e4100000203804070030500c286040d400c505081d100841d00c650b400d0343e0310b1010040c400c000410707250050751495441640c0810065282c040001c00043c0156010600143d029085040b05410500d0686404201814411904d004030140079618010178008101800303840c2d01800c0c0d042404180a420018050f2150040c05540080c60348000703102c0e07103100600c0104a0343e1035060640382c09607a04600ca00701ca030f113642c218002000b040d0b40702c40b02c440d40c040074401d40d1940841c003520040f080d00d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 122915476 1250 122914226 122914237
    0x605120309011d0a0b03180a08190e0306060609370f1202120a15060807080c15070f06140708060402030402010210110c1c0e01180603020f1207021e0102 67
    0x30300c0130340d9080c03d005540b4114050b65000440c9040e180021000c04105450038140385021641800000f5140c001d4003541d54022100301c01030308010041e0002500040e450341c00090680b8010900855210103541e50704404c0f81141200c1c44507050f002c0003c842414490704402508051804580400503c500f01403110104550100032076101f104d003240d00701f220120300341c0c110154070f1191006440c0032442445100d0007404900740b00068243c0350018440c00c2c05150b5100e5500341c4c21000203507401d031301e515031003030340d400700500f000c960320070051801034001010352802401f1145050f5601c8082c114924a581c0544104d80300d080c11543c82d0010072003648000c0320b00a0050f0004c84958218600903048038140f039007031600048c201300c0e4981c030781031400683d14000785a00d04560500c652451b002003035204121004e00c1d02c480940c04180c0800103802c150721490041503400134070b08803c01c000d40d0a8415401030520305542c50704100c18000d5482c0300500390466401000030700642022014402c88a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 122916726 1250 122915476 122915479
    0x50406150806010c020f09070e0f040903050702090702011104140a050a032003010b0301020a0c140703030c03050c010b04061d0c13050409140607020601081203010b1b010605120309011d 81
    0x10141d540310b0004689854001d00103d030480003510104d00283da4a602061241d600b40e5503000b04400180c00f0000c11245110f4600d0040d4a00000140466400421a4811501510711003299150402c04a00520b0b5012444185d41c001190100c3c007040d02560283c4807003000c4070b4401040792240100000c0e481c56110040c08035280104000340c085048017a41c90060008000050f43c02c00c0c5c1d1f01003800da903c44c41c0050000b6450034148030421440d902d43c8071400030b803000280619804c0d550080c0c201070502c00c0c050240500422810034002c02500600c0c030554000d04184a05541d40500f400314000012032081078503004000500001610001d981c454482c3c400181c41452810051000410348088141c0300d21074844400c44400c401003200b0703405444290300805841d80b601e45020304000804460005200041004101c02049601a9900041342000218041403000a241c0c01004e6544c002c640044080c4407459503804040049c000641d001e0300d80c1414402120141d06032240c1d112101c1c1d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 122917976 1250 122916726 122916737
    0x20102040e0a0905010e071404060e0402010f2a06060608060f060d0e030702120a05070608040803070f050904090302010f0c0c0b040b13151b0305062209150605040615 73
    0x2d0b0702820141c00501c2c2c4240118000100400072003045400c00b09150402c00450341001840780043c01c0a2040c0c10083c6840c200441032400d141c0c0c0002c000800c10340600302041140402d0200b2000180c030110f180c4080c2e0403041d404800c65141540207004a44140008229040d00103085814034503070038a0b4444006001c0c41c546054160400000d101000a0081501c0213020300300043c2c13500004900892544801890341f0f0f202c61510b6860b0580a401c00010850140c1c280030009030550113507034115007941401241e2100c0d01c1402c990500846100030b81c0542030151940030700d50194030040f14030322030b00020f015642c00354105480544100c0c000620810760a0b00150100741c1184006410030000c046031130040e10f0a07110300703049101040130350010603641c004000080c1051980c5901c49661810140640d2400000095601c0e025100303e000080300c2c81e814140c9a04142e110b058100d034012404140240c507088524020200e40c011940505c1c0b521801107800c00240d80c0310b04030702707949907a030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 122919226 1250 122917976 122917981
    0x3060e070b0d020c0708070f05040f020c030307090e0601020c280308071a06220b01030f020a080f07050f040b070201120f050f0c030c040e150a0e0a0c020102040e 71
    0x5140081984005094690054000208510541c44014550a91030000143e195052080020b0404c40c042c1d0007894103034071511040005103a5032820380101c3d0b004490004588141c2e001a90103407003500c9504000340000401c0040c401d42010668099507422092032004c0e41d1800700580e942c0404c00c944903408024040220284d0011960300b008001c129180409465601e940e0603495411241045495010131304403c002424007880303059014100300c0300402d4a120384050307039070201c02c0744020f074440707903260404414240d01a8000e9846480401c008565581095200812400701a134401e40707803030b076400d0102e40424803410540300044a41d208007898546445080301043e03000720401c03030600000400f070b41c107020f0072481036104090b0f0f981e40c04200f0749040070003820b071904010480344072281c05105001400050750103540070344944c44941e1919480d62103180d4900c044c6074010039400b1855607800304900e00a110381d58043c200c404009d115074440703820140d00741d00403402940784000c2c0302c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 122920476 1250 122919226 122919233
    0x506070819050f2d0a170609060604030602090a03020613050312070c121502040b03090c100906050d0905100606121b122003100e0c04062f0c040b030c010903 69
    0x142d940c80703094045440d111360340c803928210314190060607106011500c8003108114a6030300c45840c07a40864200e8048035a0f00d4404001100343c0030f64040601341c02d901140e041c8468565400401c00707550003e00395038079603080d829400380020503800b034035019029000e44003003017644000680303490580c0003400300c5410b030808550359038880002100b40c0d0b1318044079409201000c0719200074806409205241175403882c00d80c2c0030703600d0b001643c4640d50294015075098461240d2100c1180300741d404910300b00381c2d510750032000800035220021000e0094040d40100500460b0154403001c100c80140d01c50141d003c10b12020602143c0903d1080e5030030385444844412000e115068018405820180c002400510841130070385007507580c0400010840c002003840407a072101d6102030001c06400b0207003112860071500d01c0240e4041c03403003030740148001c465a00a12076a02009511041031090900300b104450300342c0656079101402c04a4012442d0a03280b145508006c608401c0c84641a1201c1c02803501e10703507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 122921726 1250 122920476 122920507
    0x60e0408040312090308070302010203100501050316081008010e1c110c090406090605150109050604060203040512070512010501030b010506042402030903010c08090d0206060312130506070819050f 86
    0x7a000d0130020b5601c000700000350b182d13016000c014001d40c001070b201d1400c2c400d600100741064203c44d0510030240104045c0482e0111071403480841440c00d15201d8554103005007413000703940c010301415401c204101010040003e5458400d07070000310080205c540c03200055508010030a10140b15410a20074000e4505203000c0290308144101c0c00010404c600f030300d9600443d601980c40074100c0c1881c0c601c90710150303884024003002e01000c6a0142c0750500c2c000c4065500d01c0b0f5441103074000c0085c20715960104500303105400080102800003059145031011039070090178240821202401301000108540c180074040d54152400c20401404140b11891a82c0c0941d02044050007144000c1019450700d46080c0180b075064580d40e01c0b03100a07800e1280416080c1a12101400115071211081020503580020b00c040d00c0728620000c1542e40381002c03d11020040103400441d040301000403e0f40030040c00c0002401c007000c520b00d10b00300c655111070041300c40d03101d04103040560300f205000c4002c0901494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 122922976 1250 122921726 122921753
    0x604080d0e0117040f0201030506010f09031407090203070203030910060e01030602090a0b0f04080609010903020705061605031303120e01080714040513021c0e070b2b020d060e04080403 81
    0x1410081c9205403031405001030640c0444c2c04a50340b42030545104215605400703801e4100d442400c0c40001180c20300001000d030b0200e03100c0a070983c0c210702500d10303034200d080c400c0300e000c0c141450095540386810780002e23549900588286401e07119400612240c0f960601c030719010388d800d06028101d180d10b5601c80502035006139048681c000714079a8006202074442c40101741040c24080c059850703500c0d0820190410400030002a602d90506d4580340000390f012500d101515011510349407204480d513002040200503400003081072100081108492401c03400c9801200d115520004117a400c403c411501e20340e130010480c4c04941c9803004107280d58040c201c40c00c182e05404001e2400c140c4e45800013080040045200940e007035001440c0b200a1480d15484090020b205800b030000c602c00f080310b95590800352040031a9003901040380da20798484a918800c00c880800c0c145802c21103c8103d10000790b10003045401c90a203804800511103142440e03103403041340c101014a080520f19112680d886181 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 122924226 1250 122922976 122922979
    0x310060804080d0f020d0912030f060e0a020c0a1b030c12050601050405090102070206120105150a0e01030911030a0506010608011e0302040c180303090503150408030613110703021b0604080d0e 84
    0xe11070701c0006006c6c0e02c900c0d80d2aa0117020403140d42082810041d044607030200410354a0303400e04609102c0380d510780f2440341d0040701d000c82c016501e81c181c10003030b0304103a500d0b0001488a000d01c03150090700c400d00d142103020b490144d4080b20302550b450510b0703001131840820045c607a4208100400031468158880341d072104100700050314001c038a50010b801c0307604c03482e03103080c4541c80500180f18074180342000496001d01c42c14858908569610041c00b4a200c041c40d250406840340488000c06c40c03801c0020b408854040d00311074480039540340498582c0e0b02400b031200004c0050000240c14a1080c85080b011521121a031001d1800c54007408007030319004c03004030113025210030042c0c060781c01300303000300001c5020703960b100c04080c00c0504040c2811140b0000641c1d42d5601c0083c03102069280080701c2e04090300b2244440224581c0c1c001c140a82561100040042000f01d2000c0c14545c005c0303840d6064508501c90159503040040c1040b5480c00341e1701801c00c01d0b48c4103084100d000c1c1e01421050b00707907900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 122925476 1250 122924226 122924231
    0x132f10210605190608011d042303041806060e130506060702040905010207110415060c0c0812030412050316030e0c0a0b07060612050c12070b0a0512062d01030608120310060804080d0f 80
    0xc0c0c01409e600e141d01c02e0b0300071401c865500f43c980307107942c10f10301c600405841c8503c0c10008a6000780c0000364441552003030005040d50303400225060f5a0f480c400c88003940c3d400350003405245045d05005000b500704030303810b403010150100c5801c1146003e10500d000003482100c01013030396003001e03000c4415910b0300c41e003140c1c0350011030310203e0b4854003003041661701442c0c43d07002d940d81d00d03080c5408034100c407404011394103000007030050142007030071b1001c82150b00225140001e02c00518001041c82e000c1051b9400303810521110300480c0c0514960010030a29004040c140241340c0e41d507050b015002a070850140c0f45410111a000c15440d010701c1031002c28010301c0485e00c495441e52189010390f80a210410003264000812003c0050201100741d4412411074450003074119800b0021007a603c1d05104200141d1081320b4800c0380e81c001c0e40081c02415038802210713000d5558101c00d1660364400c0e40d640019841d41398000541c1441034920a12444c1d116000c607041c581d03d6200440505040c9000504e8240c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 122926726 1250 122925476 122925533
    0x40603020603010902090102101817040f1202010e0411031803031501050f070c0e1602010b03070911040801090803010f080d020d08132f10210605190608011d04 70
    0x80d182c003904803500f100cac61141e40c1100052400040c11104444070000c04e0f402800100105900b250030081202d0422810b1001c0d400d15100403500c500380c000d0842e5120389440038030540a480c200240d0300c030f0001d160000c80000343c1c15000315503e020807651064000b80381100c441e070a500c54805400404000b2001e10300b0440e030396880c07403019030840e0005422000001c04001c02c0701d99881c90014007000c43d00081040402000109032a03148501603031301e100d0f85074213200c9203c10781101200c0092002c00000c1007201c40c80e01d0008004d6000384101d00c1e40c004044008107101e900800c404a00400b950000c048020000805803a803110081c81400440c42d807605036030204034030406411070b25502150a098030041044103440100c980c09495000300c210311003859081d0380082c1c41c11660240164a441c4494112030600007612050300f00b15006450110f00303400582840c0d9608080d00c1e0329440e8000d0582c1c0f1400d504103900324845c14080103200c40310108003c00d020b921101c2144d2108200d068101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 122927976 1250 122926726 122926753
    0x903051f02120c0c1e0a03080c040f2301030203060109030b0402180412170601050f0706020f0403030c050601080a0c1502011d030909010b03280905070e04020906040603020603010902090102 83
    0x720000c861840390341d100092210014042400780c00394140500005c600c0c416070485450795502c1da00c0000a052145800100d01d104a14000780c40c004c16444440d0508a6142d8440080604854090380c692000d5081101d813158040d0080c0e1b442141c042e9103210b00c052460f1203154001c1c0e0050816600603a541c9901d05411014664244c400c6014940f04c1e011000010001005c0300c00781825004240b010303006110043c1e03400021200400b0900c0b00043c0c55400a0500d40024411003860900d400d5000600108040d00080c0381c450407409541640c0081e070740e441500d038490761010001014100d001d40c003407040444000d25040c1510407071000199070300c140711120055101e500c4c507803c81079101050301e5403540380c401a8140500312000c2e40c141513080810341101004400650100d019041040700d280c0500036034458040660824121000185d4400300800709440c144c030164025681c083c00641c241c00c0030b001d01012030f58050403031480d40e0700c3d02003810001e411101801e07046005101c1010340070b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 122929226 1250 122927976 122928007
    0xc0f0203010f06050916050f0c15150909060f132405150123160b0118062918060d0b180709030314070605091506010903051f02 56
    0x59507920b010000b07007181001e0400c035405200926203c0f19500d000c40030780200c2d91000a4550f04407021151644070321518000c242440307102c0b6101103000221004001111050501604202d0707010744000300e098503201342c00368a62204881100307181040101041800f00382c0a00204880d00500100c6a0440200d200d05040c1d440301000b050015218400e000c40041c80507c4000300c003409003080b40c040039030301b10b10280c5410070701003d001302000407513104081101401501155503001e6410340c400d684500368456002d95030010000002d01c0c0c800081200541c0000010308100003407220f0b907500003038201554469200c14054450a20018440f400c5d03926040081c00b440c20100d140030410807035010a01c40d05031006400e40144100010a0041031a00000144107030b9030185040460403000d4508200c40d4440c9950082c4a0b500e003c042000c4440040b41315207060f200218981b2060300c40d000112038000050001600e6500099003940315850804031541e94189140d4003d4141156055013204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 122930476 1250 122929226 122929241
    0x40537240203090d020106120b010b16080403320a020904050c0a2402070518060f0d03050c0c031606030209030109060905062a030105040506151314100f0c0f020301 72
    0x40b640501904e5000d180c080c041c00000d000004000c001403030540d210700e8000c0c0411f100d400d014000000b00f14080051060080713040a400036003207640d40e40d903890200c10103a50503a154041c207070805510451a0101000805041441c4000700140d104076020891100e60140c82202c10344111b00c00c1840710b445030301e0303d5401840c140d00a8601000110005118401c10010050440d00030640c240416543d08551210092040700ca801c1503590b07030400300b6940058142c01740d038824410031581e010545e2043c001c00b14070360094142c03140100c010f81416941d09000f85001c40242112400740311301807103135000d050740c180000c0002c1001030807904e038101150000d035416542c0b50401010003d4402c0005c0c0740c00300c0d030382c074907c0014542c0303140311701d160081c1c00706005143c800d58417000498034541c0c0303007580000d4020038510103940e1050110881ca2620105200d09420b0400016441c0001e15010003245046001915444406400b01e0001c0f00c0365200d610040f680080e00300071079405a2002d00ca02039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 122931726 1250 122930476 122930491
    0xc06020304031a0f24181608190b04060e0108030c060106020d02070b0a0c1406070e040b030601030201030b0d051204050a050402070f080a1205040537240203 69
    0x19950390039802d010030f0746050f02a0f404180b91a84043c0040c00d44052052948002803c04041c1401c070f80340707405049800c00103030841e40f01910710f01c050344050400701c02c03030b0040c0c624800300400c80101030f2007620107100882d41c91600c4060b9800400c0110416000745994000003080090455104c04111010000c00c0e002207800350b001051090003003c04001c0603000d0b080c5400242000d2002c008001d50304c1082c0e0044050f03d06d0003241005c9030f240101900300714594459808034007a0840d850a0750394040480d85000000e4a04034401c3e4682031900c540d0049140c00350280c031340c581c00c3d1f4005602038400c8105a035000003420342d078200429002e200117201102042c0f4450781d61450001008070400142e0426489544100f040400040c84035201d64100e560140703102e9183c5405c0fa40640c0c001c92050b1600842c1400c0a04000420002103010004068803c2070b6030803c1d5803802c800c0120000380590b808a400d0410b43c040040381e5500785c40d070407016201442460701203080ba0a40103a8005440c882e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 122932976 1250 122931726 122931733
    0x60403050f06060d0b0c2a0f0610050d02190e0c0702010906112104081207020a17070b030a0f0c0e091612050a0603050609030703080606340c0602 64
    0x1000c81a0003840344a4000c00210340b0308010701e00b29201c1c000014030242070f41c2041b003000110340d10860019150701c490585000000981d03032565a281540754148044031520760700030000000c0e009200d0403240002d481d0003070a0104601465403e20441c444401050020300424083c002145e441040f03005c0c3c820761144c40d0850f1546042e20015142c2c001680080050151410407141c00140c0007403012521599142c0800100c01400410310307580c419a000390405001c0c0c040c85038070900c480b200420040e482a030301c00180c075580d200511040f80c1c101c5005211600403c4040088601a60156801c010001c0002800440100380d41c01140d244081004c00305003e24000344041c9090541c0c1e079400380040c500030101601da004010301c0385400e20760f4903e00311365078400300c0c42c5124540d11402c051341c0e0040c100d9442d0f0510000a80c0e40f908008000c400248814000034803606018043d500846002c108002170007001800c2020a952841a440c040311f4685040002003406401440700500968024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 122934226 1250 122932976 122932993
    0x3070b0d060f03030c03030506180903071104060501090b0d021614010b0108040309051c060908030910020406050915130609090c02070e040210050d02030f0114011106010306051506040305 82
    0x1140030795000c0e034001640807102000030400302e6005400800c1455141c50009030345d03510500090100021404002e017035590020411010500000082c24000d001d0840c80c0302240d90001004155013485c0102800120f44160402ca00c0c841040a00031116240d07002608148040c080e120038460420802e0b280c072601c80d0004000040c0070310419515950030320b13112040d0300e01a18058030200b010700c509030187c1045c442000c0215a162025174600780d00c0390091105540c14204000c09070000d941e81a13081c01000c407100032000350352003100c08981c4240c6030542082c51450030040008181c03260155441800c000035810062240050009010b0035141c0a00c80b03400c100495044400b8100024155031020f40d09220f10041c000f8860b40c0709504031001d007881003030940221124001c2c502e2040740e9038000b100788103402025126060590307440307030785e940b240c41d0500340111510f06400420310039680000c801440801d4a03074100f07a920280c0c1c9611148103c43c61004903001d607000b64425606500300204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 122935476 1250 122934226 122934247
    0x20103050604021215030f031603032711010c02030319030b060c190501110d1406060f1605030f040602010501140904020604060c060f0c0c060c020609031e0903070b 72
    0x21181c1200d0182c82c00c500740400c9100402d1340f044007410000301d10003918a1400c0030340d070812102c442d0200840999440704c098010070103900b4a941c10480201c1d08082603000008507041c9c002340000c1600b0b00440e104101a100c019050040e40039140c10031000344803550143e02c040000f40800e52007100000402d01144034010300325000558282e00ca06000c0082101c509000102c070025a4042d0090351207081c1d1074074003940181081954a5582c000100b4407108110345548086c0c20b001280d103c0b00300a5803503000b0850940301c0c5010302c510421080c8984d58022140280c01c8103100e1003901100e1074020788160411182e0801d60080e070043c2e4543c001401945c81110069002e05002c1d99101e45030b06103540020703aa0f000314045e400030402c0c202d4030305e0b0911105810503e4040e40640c800c0205071480500244200e214013000c0d1112401d206a22417610b1000a14610030f280c1100614200100c844001c419400c80070004042d0075020b1001d0a100d507002c1c0f28040040082000466032210110f5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 122936726 1250 122935476 122935481
    0x10b03040c0e09030d0b0301090c08060a0b010f080f06010e0303040b1b0703030203090603100923160207051909060b04030c0f03030e01030e01180b190b0f090405070803030a09020103 80
    0x1005640e01c0c81d055010700c140b142c000405e0380c024003a19800840d0000803400801e004000401004e051099201c0c3c00042d890004109940a1224880c0c24050b1800a9006452888040310b490380013800190024181c00c58500080d5000481454400d0b00310f8002c000182c650b400c207410000c152100003925403080703a0f002c0c54a003444c01911010b459603c0c5961806074072405a480c0f103500a02d000400545042c038074001c5640030700010203040243c2004080a00961004510048020111034010580340d00c40d903008105500041d80c001e020300c038104802d00208181400444120347d03994000400c140000c0d0141c0c801520404a0b29a02e0358a14241300307c660a45500083c869050407071b0500200b58081805046242e0a090100710403800c480ca00b4010035501318442050780422850b8020401c1a54240d8014002e1401040006482804004c200c440484140c0d501048acaa001078103410300c680c3c601d50203805003041e140c415540c0e105072800c543c800c80307000c60b04965802c001800c47d81c152 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 122937976 1250 122936726 122936729
    0xe0c0925021606080606130608240d020f0f060c06071806050a030b3c060f1e0c0a03050702010f0516030c0c050d0308010801050a180b09011103010b03040c 68
    0x1c1c80245000020546100380c080554007071001040150000501a502c40350219071100c3c0c102e16403680c209613140c00c01824403500b42c0b80d021590b409002d02e02c1c030b8180407071115440d9030030081a00010300341d0b980c00c00040007900003640790005001c803400007940d42c403140684404800c40014007003038542084018400c410301c0300b021401903400041444041e40c401c06851064016040001d803805900000651040d2107040c0e02c01144000c15461a55121000006900d620746200405902c1111020081e56004081c20170031416418041c2500d0803110304008044040161009460030390700f0003d0604200e0520026004144001000011075070712000c0c0000f41a0b484c0b4046085c0b02c15040d040380c06804246000c0c08010441c0281002e204001c24018001e12008084404000d51850050f00003e001d00c58540154a04800143c59000034042d6041840340000c1240c50402260f840d10108000502021115075031120106a00c01c11100114040e0400d644455120314151604400d0800903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 122939226 1250 122937976 122938051
    0x7020309091f0b13050d0f2a03050309040e0309010e0411040308030f070e03070e181509010f0605030102040305250906090e0d140d0f020c0a0f0c0605030c0d0e0c09 72
    0x229003c00b000c00c5044001e00312a6520400c0650300f003080056822305007900600c4030702044400c6a0010070804008014040c0c1103003503c050100d01d904101d400d44a00175440e0103404101c2100d071107442c5151903880044d91555600480741003e89039140c41d54a604101c0b820014803030407409100c1c1142d00490140e44034281100140075160a183e010711b41c3c02c00240c441240c40703100064600443c2d0703003030201465a80b000501c000e82c51400941460207050b80c03002084850f8900f0b00040b6882c101170017103c4c1540c1c0c000b40203046003800880e06004c120140c2c0d800b0314051014120100d14403505004000040800d8103000c2540c071000ca80c0a401e2094a6a0150501040000241219aa070300035980c40804030400021940d0082d00c00304040d214005c00c48400e4001d14104900300f00300c1d0200d0410460154041c0c94101da20307044161964030050303d0b100707018442485208030f84511900f16480c4401088244e4621682d06000302e640f23500240c402004841284900c44e16001c10340c020308402840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 122940476 1250 122939226 122939239
    0xf1e0c021603050325052b03061505030606070602030106020a170c12030901020408010603080316050c0c1903020303030a1e020a0509040b0d0f030201050a0c03020307020309091f0b1305 81
    0x2450350b0399a5a03228803003609080d607a50b51010618603c00c80c4a800001b5000710540303d24031003810f030603401c0d500e07480b07540f410400b4500080500c03140300c0c1c422202620f10980d5140700c10883d10200f40c0f034a0300b00030040c0380c0c0040304000000004130301c0e0000c0c500034440b5400401400c111464241c0c40b544524510103002d54040c084500804800607000341c401840524182d40d9880c0c0f14015406481103402000d555070030104004100072040d001988959501c0b440042d010594450480d0716210764204059540d000d208207000519002d1020b00512120b40004100f0541d03a5001c6829500100c0751008001e54a11211807025000000ca206c03400200501310b203080f40c000b001400b40d0140c0e400603409903554522a4040351140c0c81c2c0c1d2015a90450680c585c1345126144c0207019160880c0d003600240d05049c400c840c001d0090084da8080da0b1141c0195041c84078202c18840411f10040403002c41c0c3d007845459405d085150b003041009030130000846035031409885041045071443da84094010b08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 122941726 1250 122940476 122940479
    0xf07080c0306070e0904020f0103150e09060606030405070b0c16080d02070b13060806030f191a0403080604020304030212041e1a0301050613081b01030c080c0d0f1e0c0216 75
    0x1510011700710380c0698119031892350102000f004031300401c117000e0806e4001000100228003039111565140c41040810103c600581e100c0c0c083c00803078013095500905940c0444c2c03041c0b024a0302800540a61085e410444003804445155182202c0460740080110b402050603003d5880c2d050200c80c014180c41c081d003525041d0744906201b400c036003a200b100c003008100408202c0d203035001e020221200000c0d80407215240481035040345400c000c01008c0350348603d426004038400030620a10b5209a4154031900c450f991a14184006507000038001c030118042c2040c1d9080c01410140900b010b42940d808801c07001d2040301211707a8080613078000700e88030460b25540410140c0042d040ba415280c00303603007858862281a140d12564002900305540314056004c50030607580c040440078080325000d0742c3c140305680e451103041d10400380503507140b8404042003007215100c034090b800040c03041c45200320003c0c100e42c1318200445901c402084201b4015150b116100b40b4680c10889400032196000c07001c520745 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 122942976 1250 122941726 122941729
    0x1020c03011a0607030e1503190c020616020a140d112d0f010f09061b08060118031406041a010807090902010909050a0e0f01230402030f07080c0306070e 67
    0x203240280c0b801d8860300c400503a8500709441000481184a03000d001e4004841107990000c60329082265a10100100b075503030301c0f2140c01180161000381100c2d40180078151982a02c00000d400c50f07040e0582580716440a46001a105c0003180018a00c00006040740144001c8000d201000c01c42208406034089450b280302540d07040c0e001d0301d0052620002403018869581064100084540f5180c0b0a5292807090000140c140d08440510780c4503140421a40d030704021480300313003080c6203405800140d0399000a00194051112081c0841f0f02100740310b1056943d6589075600001c04c5080115504104140300801070f09401550000780900c0c1500ba00d581820540c95a8041c00d20520f0b41c03244c4c41c0c41d2800156409645000058110700b00140128074040132120040e11002100d1140351040d010242c0c00d001041c407032009002e4041c422084584070005095043c01c0000c0c006036803600481004014a4004004002c000c02c401c8018240b58080202014104040248648140070082080711a20b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 122944226 1250 122942976 122943011
    0xb01140102010c02120313080a0305040203010f0e0a110a170f15070804030309030e0d05160501030c090b0c07090903080f0106090b19020a050102160203011107170d020d02130501020c0301 82
    0x350032201c0c0b61162a987e45a80380000e52400140150110100291500103039516400140c4114002d50090155809140b2441c00b21440d5141170032031030f08180c01c10000960034a140540502d0000c02d134101142c0c030361070218490307203108a9a882c10341c0705401c520120310090000000780350860702e40c820a0310b010300000c0c140c030000510040c10169240308840c201070040524440e180d80103080c2c0d01680459141103a592055213070a51a440002c0e640024158070030300684030b2090480c1c0d43d8a582500d01610f06426030440e5035081c50900440c07801280e001c42c1ca1264404c01030007039440014a041a2205c00d4128070f041c1c0003c2e01300103803000248401c0d02c40004842c658495000c0900911040390412420420100b1000380355500014003100307520214184401c9260003240200a22041c01c0d240844074450301c00020480350200d0100d8400c2440c2c080903003901c40050001601e00b4600b110300d0401c0341c0c40303004148042692a18184420750381003045500e00c2c0410f0b0020000440380c810168203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 122945476 1250 122944226 122944243
    0x9010206010612091b080f0f0d030c051c090b0a0b0607030f0e03100f06060c0c0b07051e010504140c0904060c020c0406090e0606010504060512040804030f0b01140102010c02 76
    0x240008011100d0301000f10703612010819410448082c0104803000f007010b0314106610030039402d80310b40c1c0f41c4907d10304d20115158851342c2048000b8100b400401f80d0585c05080e8544540e820f1140034402208075590501800310400800c48001901c540e40f4a4110720103140607000d041c960346408240b18054503180d04407890f0a4144c182060341c02c65480c0100c42d8408101d08190300741c017401c40368115101050b00a48007101d9204800c0c0105610703243d04480d554100c1c0f5001d020002604010404080d09500403c0c0c041c2c00b500580c0ca001c80c18010a6500c081d00340d60050340c0c2e070b43d1081000700341b1a480c0802078040c01c121024014401d412000982c28500142c00a4209507440f100300440314020029000d80c41000307031060146a64420141d0b00030000040c52081600034100001c0066214000300d4080e251103072107203400c2c60003407900c0c1500c02d000200100c44500c410840400410030740c100200000d0701c1490b80d0f402c60360618006c18a0a0682030b2100d05580c188041c040304542c000c2510b01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 122946726 1250 122945476 122945489
    0x9050711030f07060b0f120d1e0905060a0201061203050d18020105090f06042106060f06021f021b0105090d030605030d0309020310050403081006080c0322060203010914010b0901020601 81
    0x1340c4004c01000103142c0c19640078003242d0211801f080400c1518020444240c14040c03074940d0b90226481981c841001182c03030107071200041c1e02002c140000d141c034101a242d0311484d440002050f5072510340202081441c0d02068021400c0030070a020103400d1405124003110258001540d01500c0f5030020700795014a0f03412901c01e0810b05012041394446000b07940003411890300088826020f0b07030310030317028000c210001e48803e410300d0740210f100b08400c405d001c2103070a140d004103401140c03181a00f5403e00d10008143e9050780030404115056010502c9a550201c0e46000142a051844400345825602041c3d1401d150402c403081240d03a030040b0b11040c0002c070b241800b05041c0e0b801c1c8000380c00c0a07400040715142c20300d804140b00c24941c0c01484280310b1120a4503d0300c4668480d0001c3d00c4501c0221060a40c4c01020030000e01c1c00b003008041c3c540341d0b140c40010005000910ba40e628240c2e00f09801020380c49588804003004071420000d90b500600200b0320b40c40c6031581400000b500d6407414003a99 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 122947976 1250 122946726 122946731
    0x1e140d09050a05070909060e0606150705011103010b0c010b041a060c07031a06030d030b03060721050c031005010c0818010c0503180907081302010806040e0709050711030f0706 77
    0x3502400014803507002c0856001081d0741c09940c41e4044200140401003065400034900003110403081c4002520501034032000b06808013800d0b0040001a895204075022210740d5200c010804070740040201440c06810421882c1d5160032181c80301034211036010913410302c528244030058a0241c8540c88660410398241d51003540d401c08034266600d0b0480360342c80100b00ba82c442843d00d41045400c10505d000d490214151001c4484803913044042d584402c1015525800c90700109102a0043c140700000124404481c680c40352000320b08400c80703004031a0319403403500000030803400c14052082c14010b01800d081841406171551100d40850048281400c0d08555090300303001c00740e00940420050a81c4607044955440380084c0e9001c030329451412150040d0300407008145402d004045980c800c4c0144c001280c0310325042d0f001107480940145c1502d410590782d151580e29444144030450141c9583c00d0007052608001700020100d80c18030340100340ca904107004c40d000310380c5144200c8040c1078000c0b49c007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 122949226 1250 122947976 122947991
    0x60f0a06031a0a030503121006080a050a0603050a0b040201030605060f04170705030d0903050c040b31020a0207030212060405060f0903090901060815060f0714030c0d1e140d 76
    0x2030210001a00181607444443e5042c00400c100c0004020700511407000110807081e00c3e000340c02085c1c01404d0044202158101c000900c070818554055030f806441c07480003140f01c1da0f0b0391701da06051050342001504e1429040080005550705805504000c110030f0301c0031842c05090001c101d070a40140d0040e040e122060080d661072103030ac20402c540240000070190b030004007500b8000b42105003280301c221018001c2c200380c1c189900c4c180c407407500001005020610400750707103a00b8036804d5803003000c840700c88128180100004580d41c8052300202c125500100050b500754010040746100d0703650300b09610fa00078002c21002400124115130054000081200280c50b50350f00390b821402583c5070540c00503540000000d81b503500581075401100207082881500e282503003404600d1245040900001e00304011040000340c0100012610404010a41c1d081c44281868113003403400351082c0200080441c203c0040000007282c600c2039910160070300c940c160200703c10340461402a0740480d240d8a41d42c40c1c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 122950476 1250 122949226 122949251
    0x50618040e1207050c04020a0516020406090513020111010b01090519050d150f0e03031b04050306091e030304030e06071a0a0e0f011a040b0a0e070201090b060f0a0603 73
    0x425074112062041d1a810710b034500e40c80803503822500c0c3c2515240302c1d030600c5203410b05091003241c040c1c079039a64030240f03040103860101034441c04001c1d049030066550a070004a2903c4c9129850090500d04d1024030084100e00005080305549001c0d0f85059141060704c181d05c0c2e030098840b0b030441c1c40c2641c4c452861484144101c40301c8100b5400160000c2c84101d404040111082c1c4c075078061000e9607000c00500c182160600220f402003032051640e0391080011940c0704000e03055210303280302c251500c580303402d0300c80020030f06001090394a0140d170741c0aa1003008010810032205110783c01000c00440c19441d281d2030040002c40c030f00e014580902e00c00200e003028012511603450800012000c002010700b04200c80c40000e02c9500c1802031b03a40038001410140301010b01402c00e10404114580d042c0032199410007000388001c922182e40321100f80c1002506074042c0800c4c03842002c0d030f50000a250242410301031100540105868403070703c58255050486c0c1d40c0d0750800ca068918038600058840810308 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 122951726 1250 122950476 122950481
    0x3040e0109200a0207050a17151302120105010518040503040501050d020d020307020a110a0b2208070b030709050a05090a0b030c030a320d030902010c061406030601080705061804 78
    0x641480c0ba103800000c010b9212a0000b840408079041654080c4c181c50703458500940c40c907254038580101e9040f10050354040c4c2c80014a07580c10013000010790300c4444480d40016070021700b110426010303035103841c0100100d1800211041c2c0c0f803c2d1000d15144d41d0301d4107079192a1648582d000711418050b020a51703840b0320130b56905031580c0741782d030745021990307410310301006551012803010484034000004c40590080c10f040503040c0469540604050074150302400350800000841018980802c0c03030302c80050445000c000010041c907070f000d0704c84d42da4200010b0040100045400440c0210803c0c9001c0041e91900e94005611106208002440c2203001300024144040101c5c4542d0620800403140305003d035281046c0d0401d10540312131003440d5400b654000d20071140340704411194006000c0543c4007806074100401e0148145025074004107599900fa003100c4018503030070030034140c140800c4040d080070042c1c507000d44201c2004241039450200007500c640325070600b00307039122190b14503094191102d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 122952976 1250 122951726 122951771
    0xb100c3f08040b0a020a1b06060b0f0304060605030f0c010809030d05010f0806010503010b010c1209230103240312091d15040b062d030a0b01080f01050112020304031704050d0306050303040e0109 85
    0x10f5080ad541d9407103058140030303184c1007074a0a403010b40c5132000002e004e141c0003503a00302d0500f829002c0c0c50500542d00040d54035003802024403546d40030411206405802c40e00c0307624040c240580c12007100e5410101c0c200e15002d4140c024078000d82c580207103240c450380c100060b032030311591042145000803480c1001322074001042c0d000c42e85000e1030020003040c0030311034a00058603031001c1e81d08101d064000034030710b2400700702c42c04660030512040f0018008516440070200c00700c60f081c2006000b241c0c1d595a8140300b41000c4001840c0c540c03600080c0034004620940c1b50b080708000715070a0100d4100000001c10a110341210442008480f241c1508004410103940401c038840401e503980703e2900c0c10300100945402c0e064580080c94800003d100301e012070140743e058400682d03400403000c00c4489103400030341c405413040d03040c0080030a9041d03546102c1000c4030b10407071294002e0b1003550f02142000d01034440a8000f14840d4009020501484c0075000c1202d044403009540403031103504000c98055107960a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 122954226 1250 122952976 122952989
    0x6050a08010e0a0e1501080d050421022205060907020f06060405150418020f03030a0509040f0e0d2706050f09040e100b100c3f08040b0a020a1b0606 65
    0x140c0400c403101174940484c081c12990714038103031100c6c2070116004031401d00c114090240840307d50a205514030902401145607548003400d0110f0009055203100d01180c944505141c0c50364541080000fa420100c43d480c2c0c0020890009020380d0b9400f06d0941c4c0c0b110380041000e802070741d0340d40001e4002030451505409501021f4420403250310160b401c410084028003099000e0801c0c401c5a0300c0398240001100c0340c810b0140d50303403070a1159010401010b05903903401000101d03100c483c00c1100740301c24440d42e9400c1c0c104e51200c1d9004001000c0344d5120b2040885500346800c0c41c88020004a0380013001c440c180580e29884503614003041e4001402401d40c18141059445440c05030710200d4050381c0a0701801000311401c01e003001110704122503035034150b88000c01d44000c81d070485106007041500350400d0400001040340d01501450418648629030369800d000820900c24803003842944003100c1d41103030340d8440c10b510301807488001600003210151480516954482d02c83e0901032980e1080014020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 122955476 1250 122954226 122954233
    0x60e090f091002070b010f1e03060b0112020a0e0103051614091207081f050403140715020a170a0b0a030b07110a1113090201080c0a090e04051606050a08010e0a0e 71
    0x1301e040091621400b4041e00d104011007060201e03803100003060341128000381100e030602d03450569a07810302030145400880d050101c4c044616203a04520300141861503101e0f03543c01c2481c0c6044000405440001e03110f041803494496071224060351104103c043c0800d40110f081d03030381c00c60501040524142e80202d02c03103801449008590800081a0007072403003129811107414410301d130040402c895007968003d022032201e060308000d0081302e0025005140c0a010608068070304c3e40c06680c01c0c0d134000314030580040d40c0000c40318030304000f1362500741e000b42c010101081270302010000b0941a55141c080a00207903a01d03000510420b00c129809000d0070180010303150800768603d048403507001c8455000b8803d68510030310781c0b07940b08035200304000702c1c2c3c0507502d440680e15034020440303041e030182d001c4404000c1610750210340d07540341214446c06548500e000b894544001c0c0a412508882c0c1d4102c00f08004040140541c81588940c071181903c04000c180d50355510340d80c1184000302002c1c40c45c0d610500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 122956726 1250 122955476 122955487
    0x50402030304060e220c08010617130302031603080601111501060503060a080109150e0606030d0e010315120b07170a0b0a080d090303030b0609150304081201080303010f060e090f091002 81
    0x4017035044100c0000903038032212010303621500c00351251800c00180c41140440d03540024134940701503148680c40c50090059a00e4440350b103014a8004000200560228840b8014440d0035640407038194405400702018203c2031039644440301c1c01c1401803003020108440800469041d44e101c080202c001c01600340204207150302440d1070032082110303c08004a1a00e0181520079490780170890501c6554010068500682051001e4506c51800c0e4507881c10180c0e070312041600351a03000e03003950203002c0c12802c43c9950011880e20155050008001e00100103291780010089000041000e802490000000c1456407501c40414150515907001048621500c1228003c1903085030441054070f000c0d03517062014070607560a0140b1032184850650b003100c10907042d0300020200c40069a000ba2060410b035140c082c81002c440102c4c50300b0303008400130380c100200400c4186401d09003140100601d0070b20111152070b020020b111184004c1038801c41c04035160024a00c0c4005111400b01406007003021501d48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 122957976 1250 122956726 122956789
    0x212041203090b1b0d05070b0601201f11040b040e04020f090a05040c0f081002030a06050a0b1b0c0108190912051b19030f111915050402030304060e 65
    0x141000c1d1139068a50040046600243c5e104400b11500150000c400300001d450f45401124080300d0355800c00640900700000e1040d8000034483c030a0741c140c03003041e01c242c070020554100c0215520340d1040580c40104004c03c1000c2c030800ba00b030300c003100c0f400008601a5a034a0011174007000040c10140d034880307014020031100c03d01d0340c0e04c1540200e001d054450012a110125440b00840601802d181380e440606007541080d03080d0001d681c00004400c000c03070401d40c1c4030080340c00d07507020340c00020107010081010309000b11650110568114180010155501032030000307020300002904002c00184218007007860030800d80c0141d200c4e541d2103140d001441c0110400202990481c801042d41c68010b810403521502d400610400c0e8a040d4000c4140608050f0760280c1c1e07a125170071050410311501001c03100d0010340c00c1c0f1800c0700c42001009808201003403032403c0c0306074450718032101d20214509414003016840001c156000d8038000d0801e44200c180030b200045005204c640100070301c5204822940d400d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 122959226 1250 122957976 122958007
    0xf0f0423030609060105130207060e03120a021e071e080405030d0201020403081204031b060606171303030b180c0403021f0c0b07090806040b070206070212041203090b 73
    0x5140c8480404115041450030140c503400242c0764680c103035000e00010f202a01c0c0c07020480300001c0040000500c1e10045a444205891800400240d07039000400c03940110000d0381c2031564480080f03481145895651101c80d0300300071000c2d0b41540d100c1400303e281c1c0100001c1c0241100e2410b031450001c0a408001d2400031000d82c82802054000d01030702e41040401401402658241c80e40181140d08054020800c290a058014410390810018000c2c5032038900c3c9410801910500841002c81d050307082040c0a445104405208602c2c3e191400c10050000020030102410303552518000c10902042400a00d5510104103010310200450040c03250300d00c940300041049030b100b624400c0040160707950b01d400030b403241a41e00d40840d691500500002e9050250140d000c0b0007400e120312a503480c0d105845ca010402c4034111501d2000c3e030140401c00b501003210592040c07840c4001d08004024690031140da002c2c0e4403a10b1001440a80e503a41051300503410304020f07101200a40c0d8984400e098a840e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 122960476 1250 122959226 122959259
    0x215040c0b0c10060501020304030809150403080a020604110a0b07060f0605120106051009180507050d020a0507260a08060a03050f0d090605090d0803070309050d17010b03070e060f0f04 81
    0x114a132414000240e59400401500c3c01c4907000300000342070001d100e0500c03130200c8160f640b86200503030403c00400001e20340d1000c1c0c88210314650051000345803e20b0011001d214a4a00070310500d45071004000c4040120b04403a111b42d804180851550f00050011000d002d60303800295022042091a542d422070540c880c90440304e08840d48120203854610540c0c0301c003024083d410088510580303102826502d030700101d800070f0003864002c0c0303081c03a83c408040480c1c0001504800140c000200038041c4803031160030410010407035903c001422050300d403840061103401880e40900c40020000744940c0e4079044d02038010f5801c5800d4500c00c3e80e8142089417210301e00c0701e840c008550400404900700e4480c6042e01d0805a001d8854890340d4240c1c5c0350f201c0c20390802003134402019207405940c0c000800034007107001c5080b1180c0b10814010740b0b02007083c803400c0058106404421052041011907a80142c415806c12001c1c8c0312569926800e0030b000445204d000019115054001000680b042e0521003244 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 122961726 1250 122960476 122960503
    0xa02060441090f010f060f0210050106030209030c0405090303060f030a020306010602071a03011214011503110f060309060406090f0b010b190314060103050a020405030f06070206160215040c0b0c 85
    0xc4540d90f40000005640307900b8000c0341c5100c040e07403005112582c000c40202200c81c0607401105c01d600c072100c00d4102611001d030010000280c01180800d42800c04105042d14410216028461890104102550303400028003184c0305514603002010141c0782840403254154002d02501c0480d038640c00301a41c1d852942c4240c9060341c24580e00f44615100c01d6068a0588000f0010000c007284603845000c1425a140c1c0582c90956907420401441d841c80440000110320940d4020a08070807401049603143c18810664081d038410001c020070380d0b80208019511603408240001c0000460400c401e0710301409100410b079243c0007002081c404443c4010300311208010541c056040403105045060702c04d4041040403081561005ca5071940c02500065032000034110010b007815607440000c1d1030800304400c481c41e5a00820700340000d40b0b030305029007035000d01604450401070b008103c00954901800300849451080c3c1c00c0814100f06114542c0030050503210b0001c0c2d1141f940e181031603124400e140048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 122962976 1250 122961726 122961739
    0xa08220c0e1501020a03021009080906030403030c03060b1e0c030c03070c0e01320102030f040f030209180d03051312020c090708010605040b07020d02060c1005090a02060441 76
    0xb4000b561001400a40340c69069026154000380100100041d18404e2001c035001003051080d0303006034460101a42c881e6000eaa008200012120780c0941244c6880e007164000040400030720780784400000015480030034840e10fa69035400300202041c11740c0900003040900380030000d82c0d401440500803a1105440c07000d011006981d03622640da20340c454002e00b90401d5071b12205a00d1550820782100b805c080903040c0141e03440c05207840c4151042e907210f034020381019002d0410a000b907080c041c1c0001d80c480f03554080c007071585204120b465a0365040352510310425454500040740044000c01e8544001d40c414000001002012800384d00e901d0580741d60307801641c0380d42c0000d59080c46181d1050480e07807252140e501d850700301180c3d14001d512075281640c1201600b8400c4006880700401030601100345400740840c448460008400d80b20040c00040c1150f200b8179a24006d070f5920821501160310003a281d1509a81c15039000c0241c2c1c4540d6603842c021341881c0301040310000d20409a94102e0b00c11500d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122964226 1250 122962976 122963011
    0xf0f03071119020f040506040b130f1107170703030603021809010c080c04120206090618030d1d010f0e03010f0b01020c12061618060e0a0501050a08220c0e 68
    0x402d18a09410b5030080e5004002400d1410503003441c0c1e01c8260021000f4002090050341d0401181c00c2c0b516a00c801d00040782d9038949a03405001e80d00c124604410070b1810280380c03c2c2d4944501c2c072251440300c00c0c01030081001841504260203903100c28004d603405804020300015986840c50000811610300303e040d420040c155456600c40c080030345c81540d16a10705420241041410042d49010040403a00404c080001d215140d80c0c6001622140054a80d4180402e0b02e03401850700749a41d071090882805100018881100090306003450491001e02c1d10000340003014004491851070010520341651818002016012003078101c01061030083c2c0031034004004141c180300340c1720b15a1081c0b2402d03806c24008291802e1008040002601e44e42c94000004c15058961112122a540c80400814012883c01000c1d040c03650300b8400401003400c3c801d0502e807001d038000d8142035000740351b02000c10108080c00580401801564203141c2c001e48651030380b80e101c0910003580706003074801c3e200c5c540140d440b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 122965476 1250 122964226 122964253
    0x6090e0705070309140d0b040501150501110304031e080c010f0c09030f170f0a0221030412110f070b070605010f18020901030209220615050406050f0f030711 69
    0x2c6880d015030555400984a10340803181d907100c02e01131900c5902500a0700c902d00400c01460880e806035002c0c100000e00c542c00402d10510f4242e03a0750007a414440303201c0345c08401400100a503011070380c110b460b294094010408103da40d01514100800022001c21900c82c2e40905600400c0214480b010400070a84a06401e40d69030086200007400030003565035000c0000c0f42d002c028498840010001d90901e034403985c41d041030307402c8900f001d40103038819035440c42258496600d00c10203c8150958500d9400c1980314212f440b484450f10b40d0901c50410103441c2d000070104003500e034203902c03a800e40b5180c41e1107400c20310396a441044d054507400e0518002040025038036002c10700301c4000e02c0b45c44140344c5d017903045007002e034102c0c1c1c45036818958288000d080702c1c1c4a01c0d034282e50700541c20201104062204800700b0454080d03800c00200c000140d80503a4203140c0001c21201030740c9050900a44a000650041e90300c2e00c80d90004c0f440082001c414010002e4011071103030307084883d25066502c8244540c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 122966726 1250 122965476 122965487
    0x501060602190609020f0d0807030905061603031e020a17061f080a090507030c05030f1501140a08030c030712020d050d0506060d060e060301150506030106111606090e07 74
    0x2900d028402c0c10b410b0030040000e48544c00840f1030745c8080c082c1d5034140c4405001034141171424100351808580061401c080513403181e5080040d0500703c1f40542037109a100c401420003a00c0b42c0282407603130340c28008034404000e900c1010624000c40c2c0035580e8000307a04000f00040d15840501c507800281c080803d07030f103107081c0c44c40b030b051002030302c01e250300c42800c1080c00c0300d6200000d4014400f40d03580d0800040805c006108010255015409005141c1d01e041c060514001031000d03e05803e800100c40b412241640c0140c4504481040c002d484441e4543c10000706214010703445041035101c006500320b040c00d40030002e021064054240c81400c41e03d034035426a00da405c645091400540c013001861905592a400640c0000c00a400b9905240c5034441120031500300d504156940354240c42002101d00d4240103070600c0e03140600d43c0030390651600000c11101c0c001070180c03009026035a10b202000141c100201207074021020707030912201d03554031030103445220300d40214070721172140c2000107000324001c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 122967976 1250 122966726 122966743
    0xe151f032a0513030507060815090f06060306030c03010f0501050f060f03280c0c0c050d02030606090a18080913020906090f06040909080408010606110a060203150607030c0501060602 80
    0x1610208840303466082142c0b198020100d0006490f401c28021011400410071080603080603210780c4654244907240c41c18440e05800140d1040244d141040152214494015080b0201b41c44190312030729030000103401d012000c071034a90558038180b00c0c021591802d4101038100c41050b521000e01949030000e004a030f102c0c1d01c440071600c49040011520340841100724822005000890781c120f050240801c00c19904030407400340018807520b02c000705102a04034060010a001c5482c4a2138414543c040303a00c600f00184194031582d030040c00502400815000792222298a5005641c0c1790100d290146994004080940c000d5040003c0500d41203103030701c01c4500880e070081c03110341011000700c1000000b10b41c00e01c8a0390010011300000a868046000b0011614850000c081c1c43e80d0400c00b0003400c54486501240407c819012600c8440030301080a40c44a6000003000d84e580d80d4001c220031000302d8424030316400036000146842803680c040c1c40c4201e07140c4110f0090000b943e5409040381c4e01e04a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 122969226 1250 122967976 122968031
    0x60e21270117061302040608070806010e01090326120114040603110d0303060f060207032f09100f03030f020105090f0c0607140d0201140a05040c0e151f03 68
    0x7900b00b44a0184902d041181d03000b60024a141e01c040d500a841100ba80c00960210000c61011020301180701d4008200c954460130a10740012101d12050000300110101c1c4405800c02d4420800c01401107101c0c8118142c0154030000155a200094510000740c04241700700200c1da004071440380200d2400380038810490360002c0005600c11605020044150380d500304c11403c1c9540c800000038605403d50842009103580c0d00a0640d09196040109848204440d00883c0705544214182c0e02e035a10280103802c4030054a4005131341d5608642c402508485030440b07002c40e0581c0d078002040503441407034500c03070070126402448070761a490800d650b40c40021165000780d4101291a6803141803c1015102c100d006031922169102c400030102c0c1409149141000142d445601e4803500c00c07041c00d0700320f8101da0404010059403a29407100d0100c454503000364841c0c81044000310703801c540000404500380a0040040e00000c5900780900500d017070300d0ba0a02e001c2400d010992080f803002000b1034040c600b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 122970476 1250 122969226 122969237
    0x6010b0313120318060c020c030a0b010b070c0b030c0a090e06010f050306030115080a0203300f120f1801020906190c0807050d090906030f060e212701 66
    0x70795441c89001d040b555619010180e4441198102c4103603070405421060058100040700105000001e0030843c80518443c0284e210400c0d40e000030300c03240740190441d40c080100350b885103600d01c2c021071203c0903580260006a0702205020b15007903200010701e803c00c0e01e901c1d0041030035542d51011717080b400304441e007a0204400e80b007841d49003405400215400760004000040c1600800301d0b01c4820120b54102d9582e5500c500341a108609007003111011400003070140020103030070206813101040560640212001d0041a0425410302c03800c10f90300c9955846c0342c20f206514008519220106003150030603000e4100d906808000380c01031013203502040c4040c2c44940703030903240800010340702d1140790f400040002409000d408150250098880f1038071a00c060802e9400c00d00340141100141c0c2c0190300000d107000410400140300300746118000e980034001040c50652120030701c0c20054071100e001010408010b2601c011080740d8020080003030301c140544c3c40480010f10560380e000240010501003038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 122971726 1250 122970476 122970511
    0x105013003031503061a0906031c0309170c070608090c090402030a060509031309060b2d1323011b0606051005041401020f031e04090603030507030206010b03 69
    0x2240989102a40c000c0c140031480306000401c0c44030f4a50203920582c1c0081e0381d49800c060100e080c00506039400c0c021160540e0b2420031000103611400d03480c07000d80c4179440c1e046074002503d00a81000300450741040e4000880d441080c480000c40d0b02281c80900c0070300401c0d41c0415a02e0299003c107000315100f40c01451403d103100f0034451075a101802c10390b458481d24501c180007480a00510744500b10040245440d10100682d03c0800c030b0541d0003840b0f8560030004244200810b0385c1c140c4040e42e0380d0103842d107803440d0455032048a001e415000d1110140380041c00f80c0001c00031003004011100c51009920406a0005200c1121542c134200f041c0060f51010320b1a444100343c070a03810165001d998001017090b0365100107420300b410310380940b01045011034200034030f41b080036050340200c00030300107000281040110303107403240320300c0720f40103050815002c1000201e450b030b109940c01792001d00020404c5680700d090141071270300a10411001031041d40004602c2c034040200b606d01400c540400d44001c0d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 122972976 1250 122971726 122971799
    0x40501050f090907020309090c0906180d1202030a1d0607170d0c0c12030c080601050309010b030f100507050c0d0e01121506030f020705030301050f01021914010501 72
    0xd40c000448141c00c070703509010006480d80c03040e40003400f82440d50000c40e40c0e03038426028001151801028144403160500c540c00c9183c0b01c00e01100c410f40c00e0301c00350f131041c2401080000c1d064451001d0181000700c110008080d000d0300040185840d1881e501e4030410030114044079400f0101c200250f50308900300f408030500040f100c01000c1c3d01480000d0119040107030241070101212814a014800501504110010302c043d101341015581d04600e42030000e0380c2c440030040d0006401420f0541044000030000e84030000c01e600400011070000d00355030108581041d4151346034410b103a08091240340c1404140c00d507000b0707821181031403a080d02a00001c6504081a01c1c80c3c681400c003a03051119000290382d80b1101c03407094030f14101c03000c050302441a0408000400716070411008a0905104001030000301da0000180c90446000f12050f0700407945da01c004078104a244181c04109840305040e003c20415450980c42d5960030040080001e80ea950b4403888007404e02c2d0092a1a80c1d035001100c0400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 122974226 1250 122972976 122972987
    0x62b03050705030c1f020c030a0e0f060d0b030106060e010207060305070207051f1d0a090e0304080d05040311100906030f09080c030c06010e010f05091302300f03040501 74
    0x10501a0405078280721658072224156404860124156003103414140002c0030071200000010f03d0b103910860030908116007842d5684980c020304401e00c000c0119148056481020b442c0b66142c0c00b500041c0c9481d82c60710f00074060040c250515100354204080411560302c82e01002c0c29510059000b031400340e103402002d8006010140c01039045019001c00802c040e2501c8240b00d810451544842240f070b40800b000600c049840508800300c1c080300900c0b100e4543d51125a04c0980d00480000602c82d0008020b8178039621030b0303a000744100e0041c440c803032083c06e400c4406403085a00882c0034810344428a000c02504070110000c100110b00012010b104207442039014580180d0040f4002501c4505601da42d0b040750014040d0703240c9940005001c000c0201e081c011a40100800c4201c00c5c11541007010403840d400181c05900c0c000e80b6042c9c0042c3d0311101c24100224078580240644181506041d0402d00c20513131322000448065840840340140310300022141410f100310005503046c01d0521004568 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 122975476 1250 122974226 122974309
    0x9011e0f110705180403082a0904060f0f0317030402092202030703080a030e01020325020a060207110906030d0207061805090118051012020f0a090f0b01030506 70
    0x14640b2503910045210381350440c0314140040e0040c4408810b00d4035180c01080100000e03d426200342000722412000c4802400d0400d00101d2080416103944444010800a208640c042d0304200c40c80c150010364440036560700360599000351040300440c0701194100040d40700a5800075003245540d40007400c0c000030140100c1d010003d090049000507411307000680303003c440d1f42040e03d240c4000680c1d040c4407505881070401c145083e03402582186406045404400308041e00b00598400f009a01450244280300c900d00321940854115250405030912588040c00780c0d19045c0030b05c800790040351039481c002440c10100d0186a00a041d001d013040802c0301c856001451440f1408640d58004c1020340d540e0fa0602d02030450403a02991302e4606e04400300c19118047c04007021900c41240600103548560035100405070162095031030300301e43c0b001050389207900350300c8540070514151403c0880c61450b0030034218030b8400d9030b00f4040d5441d001c0400c128020f40342481c44038001d243d80000310f01c0c101111150f9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 122976726 1250 122975476 122975507
    0x7020c0901030f110604031208070e0307080a080c070f080705010806010503010308070f05100e06040c0b090109060e03100212090c0108010b1b010b18010317180405090c040e0309011e0f 81
    0x117007860760b2651001161289100b1030400700d409d580130400c120f40e1000300011031100483c02819054038160541c0d4949116940280c103600740082d4002d000711040140000a000e00d00c003119495543d100001e1312220f0034020a8006400c0314007041d0700c4d40c800d0040d24180c03038200c2400352900140f036846000c0080c01c0c14045984c0c0c01390382c1c0080508681031141d00038612226000c0c207040c1c502460046003000e1103130082594040d090061400d1a680000c0000a507447d0342400070146040400107880c1c06036040200c100103000186060f02c2d4003101c500d0340d00551414046828500d141401595415400d000e90110680c045c0041d8240c4280e000020300d04100322400020440126800306030100100034150028400000040040008074a0741352014002905040c2c205858403040141c001603400d0018030503500c900200e0300058091045807102c000080080001e24801d2098503182e8010f040c1a90200d00304804249071600003021a081d4520f240d071b140e545100c1040c80584040d9484101c28 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 122977976 1250 122976726 122976739
    0x1060c03020c15041806080d0804110a03080c0c1012090807080c010506121f0b0609090a060602070b04050d0b180604030c06110c070302011209051507020c0901030f11 73
    0x180c0d21a2680e03d9480159406420b142c0d81e91400e0860600c0445024048010342e40d140030b1042080800c0803031110f04042c62864545515111424595595100341c1000c680c841c1e402d280010401c031102d4020036401c814035081d00c9034880782d034040000a0341c814040102080c408900d10a03440080c0d40710340c0c0200e00c00c007051803e08107251260103032500003d41500b1141c0d540c00601499180c030b4669a0b1801c01000010140c545060394640c01d002e0200ba00c4c00310060700c5148184443e80c69030241c2d500c0c48400740001c440d41c41e2540304e18000d41420b118082c003500034520040b9003001c0c4c520448042c0c640107402d081009032a41c0e640182003078000c0610001206014102c42042400d0014034001d9020342c0d10b01130b03502c840d42025401c030b401207110714000003c00c001c008070442c80890315101f1241c090902c001c128030a12058000303081c4030800105503014800c841a908a1f510800500481066088540d445514000e105550781c0a0001910649403008a0400240081041d500f880c070040d006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 122979226 1250 122977976 122977993
    0x70201020f030405070905010b0a090e070e0607050616090302090c0f07020d030305060406050604051003051f0806041b03080d020c0304090509030901031103190f020c0601080a0501050703020a0801060c0302 90
    0x1d28540790800c0c0c50407943c3c1d4100c0c2c0e400f0058402c250007040d0140000c0412a8544010f409002d050340c50039200ea120940074840c001200d00d070054540461010001d010385a840c00949003550326104220f4030900d541029540141307081c0c2c0315480c200141c03030740904031510030b84640302144925004010481c0c0703900310070404200162204c2c283c050f071031842510040b441c0d040031030420042e1500f41c2c2009000304420702042050b569200e200555121050500180c152a100a01c3d010484d4007000d0646050010300002050030001031070300c5c402c501079441100c08115034450030704410304500c4040e02201c0c1c03d0051748400c96540d40180320355111a0b00b2240f425a5486201d01615804c40d444041c9410116100b905940c15000d0402c074142003c400c50314501d40417041040030078075000c0c20390040c1d51f039281003400b0045a03070440f02c01d20000811201c496a59040e01030384c0301c0c108402140e880d400c2a0209600600900070f8507071100c5540c40e924510380c00c05204444214000d4400e40c218494500d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 122980476 1250 122979226 122979247
    0x10050f0628110106080105042d0c0f03020a0803070305042106050709090c020a051018020402040f03140d020d0e03030712030e0c19050f030a080c03180906100807020102 74
    0x10040e40c8200751202ea01604400240c10b085520940c08060342e641030008100000e81512070b08003000265038540c6515804400c48040c00b543d0b8030000921100d8150b0012038008403035009d0741e0403039100b200d41e042e6558994004644900801030000c001c1001070100b4041c1c0c99404508900c58688404021080d80c003d88488080c2c0e20140d0350b11010420309035042c0b010010781d0180b80c40714070660008110041d6182c0d101c50b0394482c15140d400c0096960b4400c407104003942d81c21086042c2e0028015501c030b42c0c40e10b42411181d161413004584030302900f100f20348035100c0132884014940c056009040c00960a41c41910110460501198140801c0084100044c002d031080385514589035400162620380038400740c81c00000306040c87c4102c0031000000124841c0203c50006c0d42c0c010307520a420500d07400701007803414070703949002482c5010100b450000802d00002a08100006041011403c060304052107040c850654406030011016086440114010218150807420510006242c41c810f00c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 122981726 1250 122980476 122980537
    0x711100203121e0c03040b010e061201020c060601081308030613021c091202120d09020f060a080604060e0408030406090c1508060312040503030a1d06041d10050f06 72
    0x258040400c804601803603100f03100011516912001c3c6016003131441c00c0035140c0c14540f00c81441281401450342c2c00103640e0b503c3d1504502e00b1440418002c0d9124900030380c0c3c035601c0e44e408944150000b124000010725182010711345c3d0061030740101030b0519544904080c048005400c2c2c901d04441502004900685c40b00400b2101c5140e40c0c44d5000620030400345010017540702401a074030701b1944030f00080c50f009421041201c41c0e0b012101c0000411140d076201041400d4071505205030f00c07190100f00300085d181c2008000c2e01c2002d04176400c0208030384071100c0d5024000c0c2520050714440c018030005002800c5035200b20075030750007004010103440d900e4480346000440b5602038000110551b0921a131400c080010b00003032082541160b0802e820140400c0d640e01401d82c1440070042412040c4501d238047c1881d203075072003c020300019601c80d16000180b5030a503080900c10242000d0324001138000c0c10180a61060b6200100514440002042000390235000805c4844034900000200399048030180c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 122982976 1250 122981726 122981731
    0x201020106180e07051002070e060a0b040f08010e070b030106050a0909020c030904141b0d020f030a0203240102121e0403051c02120313033e03071110020312 69
    0x2260100d00f03400c0e801c4559040c98000c1e8049070060242c1c1101e441d01c2d50300490201d090b22041030042d412560798100141140b05950b20104e4032220000300480c246032800601070541d2581c4d0020322400c4a100707c001d5441c0528070409010b01d000340010302480348500000e21500d195845c100c4401511a00301100301c0e48290404a0a41d01c0003030141c03081d082c207010742850000703a6410148540707041e4034258007003812840c000c080c2c05000200030981d10321583c140c81125180c2e0b5611616490000c07c180000d60040c0c5805210032030a002800001c3c0d006e0090346100041039004d0b14068110711811000303900b09104038640c03a85201d46508000302c0c2100504015401000100f49085005180c1410b0f002803440c050215003102100711041d00401089035004101000c0c213028280c45814100c841507484007151090890704034207481301e41ca481c228480340c0e1804c000c1c0c00c0074102a1802690340c85c0320342c00c0300525010a100040e54685801007604196217900c1c010340b0720b401240140c085420f10304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 122984226 1250 122982976 122983019
    0x3011b02070503010b0105090d080c030705030706230415020307020106030503070506010603050907030c0b0918070c1202070f090926120c0a051209010e030a02030711040501030305070605040201020106 88
    0x8201d0810252509000b29001d031a0282070032032400740e4410128110400e450405000780000060203241e15104000f11a005500070303090300c0d01d81c001803811002400c01e100705030070242e0540c4d2010721080541e451450107503600000d5051044040d01c500400703900700800300800e65581e80000400b00d0414070041801c507206d1005409158103044001e02206c2014102e000f0960108000b400007441c0d20701c080307090310790524045440c0c0c455803000036890800b6201c00340301c1425100600180c503400030140300000b4130510040581e1001a48202ea58518a10450b01c1084403c84204100400c560000440f140141000040e13444070705038070101d402c3c29003144200043c00003400e030004002105201d8001d08240b082e14500340070034200034414004c005003600505840b00110f01e01400c258400204c0883c58001e80b40c444d84220000b94503500100d10564405502c0e9482e0001e0345454400c3c1d0781070300d40c5070f00c0d1507080c40e0098490f180100700c0140300700c3c103540d40d405001c01c2440300500e942500c00706 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 122985476 1250 122984226 122984233
    0xa0803060a060c020105041202040b060a0c0302010e1603110607050102120103120203120f091515090f0f041202010e1b180f0c09040908070b040203060c03090703080903011b02 77
    0x51000074040741005a900c803038204140d824840006130f903c5821101112000b002405089400d40001001440c0304011154403000001708010b8541d00a4001c0194900a4000300b0104c121004411f49504480c1002540c15052101c103100162125000e060916009064282426007680d105405ca0740540c4031002d0041e40803004104000c52890079680a110b0b07071001e181020401941c0301e251401c040c043c0b9603041108230000710301d100100001d042d0042c80c4003e59440d030a001141c90380c1810141c41a03809490a0740018840e0030b0280b43c450700079804102d032000c5a64954440340130002009090a0855407187c184489800c8108070040c015507600c00c80d40b203000d4101c41001001c420309103003041d1f08603402c3c04101b80c2d1810380680390350222265840300c2c1d030350078581c000500901c540000145440340c0803507880306020505815070300c118800d508444058840c0c65510709107010446840075903900640d0240000b4120101610308400c01500106083d0312510102065070245020381700140e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 122986726 1250 122985476 122985481
    0x201151706090d02030f07020d05010609060f0909020d08090a12050706030507020c0102060106120b0303040e06150301032018130c0b0a020c060c0304051c020a0e070c02100e030a0803 80
    0x3800380003039034012a0303070802014440000c40020f9124003071480340301410100800d200041d508c5104060f00303c568450002c0142e903850b90302c120700410550007883c41606400a0100b400c941a03ca040d81c1c080d00180700e80504c00319076032140031a0f4000d1103a00d8114a09500010300060306403000c652061091001c0c161203400c14074010100c8900800d070008650113141009034903600030610074151b074102e10308000182c041a001502a000c582201d0350144000280050031030783d810b0340b440c0035042c100d600c1ea0000a07031410801c038601080c00003038001c500b0b27a4181102c0700800246285202005000b41e03180c0c1c00c003e1804031484104076140500031070041d500c1000c010900b5100c501a101c071500c864105059110025901c40c00d070f49200303005034400034400c14100c074100160b40040c207000f000d20286000c2c6a4031360780300b2041a40128000c22030660080355010840e0441d13031041e84d0656494a80c44895000c000858902110710003d2040000c2e401c2503d440034400c0c090200d0044000340c0c1d0b2070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 122987976 1250 122986726 122986769
    0x3150e01050f06100c03140a051b030c1009150606080402120111070303090c1505040e07090b03060d1533050105030414120a0306090b01031505010f020115 68
    0x64400801c50040046120b0400149641c0c5190402201040d803500000541003440c1c152800480b070126404005000b10702a0a44d6038424010f2401402e00c1100781404460120b19540e03d005000c01c40c0d505800c03a100841d494015030b0300100c5440d006032001012a210271410000715642c540007a000140701c0000c010960420340e02d080686080f1600800c070110383c0c0740b2188180d00950400400301500c5040000c14408041c4442010701105410403203100b00c8039030302501980c01442002e03224082c84001503d0503000b4021002200e00c1d142403580341d5517070102049080d00b01040e04890918424800514006151003541d0400400e10f540d0f81d045846208400d00e040041b40c03080c98120044035052106990100070303a03070803507803107080741d01c0075140d1008160800440c2100c0403070403a0041901410309074103030032500071650450020001444a540110241c440001403001c12289511003040706520400c05a40704045030301c00080e01d415042034003031600160f07034002c00e5043c09100c03261400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 122989226 1250 122987976 122987981
    0x210d051e0f0103030813050a050105010f06120b0105070303020f070c06050d0605040b030316261206010813081e0d060f05061303030e01090b03090106080607020f0703080d0603150e01 80
    0x21038012901c0305030b5850b40c0d4006110041c024424075101c81d13030480e650200038041052151480c1d1000090080e982c40e00c89100f005141440348900103801e451280d028084544101c007000c22040e500e45280c2610791f01c0c2034010350700850340c000003041c00304076480108608450190151038281e480315030340e4411161320000d4032503e4000314441c80c179000350541c09170740c00011940c4180d0301501101c661180e508200b440780e0581c1d500004085600d401c01d4407082c040c90001c1c082611a4140382685442d0b00c0011904a003040f1101002d228015a440000c0380c56100682143d400d408440c2d0001c0c0040803042210b0f40000210344581e07622403105111440025003500084c1505030744480c1480c00600b440041c039100e610018090048112440b10b079644620210400341c110880c4e40c654a09140e40542d0081400e1304c110384281c0140c10106840f07078800304004200c2c4440f40000c0c0b69250440c0c6440d07503035610030210080c1d0b0ba0350310f0000100040480c504401e003034402201c0011a128249083c80c00d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 122990476 1250 122989226 122989231
    0x130516180b0301180e030409050405100b03030307140903070909020406140a03082a03090108160906050d180503071a1b0904090615060905030d02210d051e 68
    0x818103240405120764010007094034111501d43c100c10520f8a490440b6000800307440c1108181070000140215800007030b601300318003503440f41088440d400e0556000d481110309001000d030f8141c0082010500e55840b80c448030007103504410800c0d28088021001038a400c10a500110740d07030f17444aa04c031003036182074032540740201003144850000035213003c001001d0b00107601005280384000704e0001106910708000c0c910b41c1c0500491648001918100341e5070700d8010405040c001011030000039101c0e095071030960309040441c2c903001e6101c1d04041c000c0d1010b400c040000000e031035a98031504040c0c0b00400b25603000781d004030080d503038030303410360514204070f440880d443e01044030130740c041c000e02e500c0903d010110546000ca456480b9040400020040c0c00011409400c5a0601d00004000c554455145080721001d0b00c1d00c400841d43c4105064072601e441d0690400740c4c03c08100c00e6421900403450b04000105c1d11f503114640780300b0800381812500c1c251005034a00f01d03111045c0390070fa1542d105468 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 122991726 1250 122990476 122990507
    0x20703030306140904120e0402070b0105130e0c010c2a0e010b0405030a02040c030f05010b0c07050414160207081c03060602010e0606010e060702030106143a02130516 73
    0x8032510f1000210b141d1901c05000105625110140c003805113120b056601100c1000034402d41d070350b8495041c4144020b0b0203001d481d110f8003007000c0d01540204203201c1d030090b4480ca100a00005100c100064031201400b0070107441c55481c0144e51102e039104000b400059015090b403c450280c10300200640c0c58a0503049500310300710030030042c40290741c00540c420f141641198081030042035180f08501405680204a072041c0c2001e00102c1c008118201405c0386821900403501c105a03540c040000b519a0000d4211800400c9008100290200c9212410014080c012103180540c0d1380306a5145c8081c002e100321501804001c404d001c1c540c54020740740100700a100900012451035041511003401801142c1400654090803145032a83c20a95808030b8005000304141c955421240584102c08024944034004c40d810303040c40b124a0401d044200c5000e943d0301c518208611140309800c0904d90343c140c0c0c0c424881d4120115403441405410712804482621070341c440c860b000302400b04140490b000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 122992976 1250 122991726 122991749
    0x1101080f190b0306150103050901090f0209070201020403021201060f14031c021e1609150e0901090803040609021003020309030909060609040924020901140721020703030306 76
    0x202012108926940e04007080380c4800c040071410440d6580103104580000390140146000c20882c4016a0541c0c840e50000783ca0a01c07e070380e11b840c5680c0c00c850b2410402006005903140b0303000581001a8141d500c90f8132400018941911381d00080c0158040c41d14501084c0c3d101c000520003603d500303914000030031403188905c102c184004002034a5a0312500242015000d81070b821030814802c00c0320900120030103442c0e0b03c544c0c190b40710b501c1d25007a48000080300d040070301500140f04580351040468800c61300300c044600d0b5040c03c4409006c03400242500b6515901d4a07030390b001080c85000150300075032140100142003035161051010f40081c000552080c50f10510400c012a8004400c0701c4103900c08032060b1b0307181d0362500d001845502419503650b03005490204409c04000c0c02d18081d00d040b807040e10041c0d15000d00f01e6200411f0384608051940012400d810f864404510b440203461124416840304500050031503407800c80c0840c5c01070b8640103a000d100204149034052003404050880035540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 122994226 1250 122992976 122992981
    0xd090c081203060d1511040801022203050307021311030f09190c140303070501090303020c160f03031d090a0b011106060a03020108180601060c0201260f06121009110108 74
    0x90846400c03650043c2c000100c2d500c5c03c080c25800c2c5e074402d80c194191175400c42d031076a84a00609000b50030941010781c0407002c140d005c2005210080c0c000040303036406001180740142503030a100840301c131841c0000404c1d0b00c411041409242c010013443c810002041949024600010903d01d045032441c401071a00d2400b0b810031012442d0414410309940c0c00c1e0036103504036400400801d20318480d10030081d10f80c0d442d01042e030041640c150028540d9001c150101c0ba10038442c000903a4892200d803107500b1090506000800000e0b02036141c603c00c551080d1142d015a1807803502250b413032103040391480c01d11030b0303501d0f100b400642e040721080607680c4000c0c004211614060700401e080104034000a8140040e01d00003403000441e80c41d81e140c840c00c91006842065a40b01e10140807560340c1c9000320b020560303640303c542e01882c010f6000240d8140d5100d0440d8982c42c1c00000b0070803001c000e811b441e0010301000c1061141041042490040350742164002540155410210460480854100c0c108000c4805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 122995476 1250 122994226 122994229
    0x30e01180e090f030706060302100f05070b0604060909030e240d020d0e0a030201320708060112090c0f0801091205130306091103070e1611030d090c08120306 69
    0x145000e9a00601a221198403205a840e03d01018505442d005100006242c000c101050f004001280c2c0b0a88150040c0c0281c40d03020b0702e449600d21300b2800012024014140440c500c11001c6070850300181000071560f44603c08002a180b481d9000d5022515150400883c0e05003450020050103048101000034030b022174214200303224902501c81e410f40c02062940424081c0d03400710010900400807180c45840629000c2c0c080c0521848601d195031800380403d02d150003400407040350140801114a10b51344500d816142d0300800303082c01d4100503000610a8680210703210361f5018900482e1845c20a9103061000200200e20b90403084c8164100298440091a1010302603041051420255261061995066900d0111741d00140040e814601500140201003607810840300c0d0542c20380b908183c8441d4601c0c025401581c511030b4605000700d005001500c120302c54860b002c0740400341d9160143e41030440091301d81d006002da4800c0640e03081001031503010001d01207601102c0107001c0c1149003150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 122996726 1250 122995476 122995517
    0x50c0708190204050408090a0f08010c0c02090a0915050712060b0c060f0c090406090f050a0b031209010212030115020d14040608150306040b16080c0304080c0f010507020307030e01 79
    0x1d0000d018a03100c502040c10030060005941c0c00e17000262698652540c4c604482d6800c84141c031a2001d903500c5c010380c14104511484503428020340181c40319015880380c3c8550001007000d540180d07090b2000d40e4605c3c080c1181401010300904040c0e661440034181418a082103070b00d1507102d400c0400080002421100000c5101e90f4005001030502c00c50f6503804013503014601c02d4810301c5074000d01c4c02001040080640d40102164440c94004219950b1035450300012a003040341801d9059000341440c0c8400a0104000e200d206410b1040e50118107080c040580076030401c0c1c11400080c003519000758191a410050131007030130b800d0300d40702801c2800455080351920460040ca0100300c1d0030800501e02d804100d8641030301e684050200c60f49440c20b030400000030201910004044078080c1c1d1204100340c8151204ea0107001c1c44845070b45151104e030340e208000d41c80400d10140703074010000344800d441c0c3c0030701c956446920a038000d555250903901c0e00900d000200c1d40004c2c1800448000180f0074104038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 122997976 1250 122996726 122996773
    0xe132c0706030c02030c0a08030a11070203070b0f09090f07020c0a0f090b120d17131a060307030f080d0c0302120a0b0301180809120705100c11060307050c0708 70
    0x3030a001601e01c01c4480200d085101b442450f01592041440c1030040058601c0198450f8006800402020900342209540c5210302e1201030740c03590010034144801d44001000380000740c80200994a400c0c50394001c20301c1c090044039140f0404042c40201f02d0000e03018010b9050b141c600b00d03007403040036043c40840481110381d40200d9030301c1942c4008401c925110303000301c0c03513031280c101048800c0d030315000100a14a0500440d007410701440c500c0407a92444000644103a555480211502502c411000040f904500140400d0b4984150007000010403501140e030b40125000e40e0106a0b903181d207000c2c060030b42c0d50618050b4101441041715401d000c5055628a030040701400c2c2c04646a80181c1c0001e0140010058054440104541d500100701042c4020000a181520b03250f4101140196058a406880c0304c2e261304400c3d1000c0d02c0650301e11034509000c4e103510403c110120728045001250164008880391004a140069410001481000303054007c00d855401440f11240b8260f0100119000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 122999226 1250 122997976 122997989
    0xb12100902130501081b040b0d080d0908070b0a050603030307090302010f0207090501060c02010912261303060504140a0203101e090606050a12030516030e132c07 71
    0x3104280021942c03811410360452420040034040b0307503100c0d40c4040c0c483c01c00035201402c84d10650700c80c1c4840e0409005030b003086000100719403600041ca8817900c090703900031340b04215400c1e0b603080c00702e000518100190410030301038002c48802d03240c04c016103011610f0140005110364414401c02c8085a882006507068a50a10704620040d00c682c800b41d1401503542c014000c1c50742014008102540d1000b02d099126001f40c4c1e40618482d40d400500c400e040e42e007040a803e00d0283c0c0062868020880714140501080410451904680f000d20b4000c89582e0341086450a4a80c0300707120074450303141000044001c101000d000044c0059000955400d00360385040c00c015103c0c600d40b4030f464144900e41c1041c200301641440220000e29040008140601a1a218480c1e890340800e8001d2441021041140e01da101c2c0d40c80e1900b0301c03040003448621100704804100415400c8251522580080a8441484180441d40c82200540d04080e0300a241c80c410a400d10f84c1e015801ca00c0001482a007211071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 123000476 1250 122999226 122999231
    0x10f090b0702010c1a010e070e0405040803150a030b0403020c0a08300702030106080d021c0f0e0f1c060c0c1709030111040b0705070902041202090601090911040305010b1210 76
    0x4440c603000119030f00c5d0201d801c45950140000003051540f03420a1449000c072171740d98034540c8200504100449009944c0503000d6a024000a02205042180840c07800001010314007003d03541d03503503000c0221013201c0c2200140c0000848104d5400d020141c10013604400020704070f8259a181721004104002074000d03251368020701505242080c10f000c41c4c1030550054000e01040340c540d400346039a00310004011005100e204503a0303100d010240c440b0101d46140e90389030402d640d07052008403412541130b840194448800314407954135a460000c41c83d070740003a0382589801e040942c107240c03003240c01d0341e0f44d08001d200710800714200044800e01c1f40300b0801c08007210b203070f242c42c884008203004028a450150403541c002130301046010743c0502800c101d6205400300c48107162103c0c01c04007a4000c1d4810503c0c0150f14030030312401840c000003559841032042c17400707d02c0203544c5c45580050310a40b000031101007000007410b00a0100070b0041c4405100300340d0b2030b0881080e00d42861030b03a40f100ba01c001110280d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 123001726 1250 123000476 123000497
    0x90612030e010c0c17060405060603030a0c0b04050313081f0608070306090602090a080307120f0509040f0e0601060315050a030f080705010605060f09041508030301090b0f040f0605010f090b070201 86
    0xa00041414017501030740d1101c0049000d00b040c106ea032014160740659191182d603000888a181c004100d40006101d1745d22441c450040b90364000407428060b0085541d4001031014262503154400d900000304500c20080601c0010348050820f0740c0701e407510503a5403909014081c03103004000110842180d030300032800a4902030340d081c120000d0041090b91a4815545800011481c4000020780042409020300484c0684000b406440040820898402042003448041c1d0f585c5850f902411021101e4540401c2800c048030703402e41800d509800c00300201e9034540c071025004204203d10405081c05803000c6604508580321440002002d1000500c040700000b908410004290031a00007040060081511003003500424400e03500081e8000d4015890b00d0241d4500c020088038100865503020050b40c070b1359003408402c5000d840d20a180380d8008141103038180300c545640c0300d4011418101c110000383d5030700b0304000414010a1401c0d2200304014401d040c00400d0807802221103040d42404c1245580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 123002976 1250 123001726 123001733
    0x4e0705190302040302151b010501050a0510020a0c0b0c0f0f03030103170c0d0804020f040903080a0c020f1c020d021b10090506030a06030b0115090e040212070906090612030e010c 78
    0xc2c030441d00001d4200c114031242d55210380d46c4c4000303030181d440d180a501c4426003a5009581c203c400902c0341035404920070360100a9030030504045081540c0e0cd1054034500c40f0280c460b8a840a21039010032294000041d10702c010071018040600080556006010b08000c8040c1184d900d00040c08041e100310b5030000440e108d19080803c0702e00d982c401030107031b60b40d50108190180141008582c20f81c0180c800804801c036502d450710802c2e0206034551120825502c0e464032501c014054907100b28154400e404003800c00302d400704160715a100074014003500098009200a040018015a840c1550300403107080821181d4242c0c4000010310607503a60501500300181210709040f15880541c110314004140460400603400903015207000c1d0030b0b02040383e40c3c0e441504290b801103013926000a10090304c00e102002c50000d8940e0018001044030740030400c8558642d050030203590210f100181e40f001c0030006492217020320b40040060700820801400320b0b45026204510720580b140c10040c0300455103041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 123004226 1250 123002976 123002981
    0x512030c1c02030604060b07021e040b0d050a02190e0412050f0307020313050105040b040902070c0905100f06050301182d020406200d054e07051903 65
    0x12030445440d0380c10048034a001c0c0c400951042d68075a00590400b030007c50115220400c40346c0c015805000751000051000e0800011080554170300c0c1d12036240c0c03414281c107a84400c101c20702d29000e600584049144e5104100c50306801c00182d4022214001c02003002200e460700706540a40c0040180300114201d01040382e4500c50451074105508020040c0b11400e42c0c00005001ca101004d140108034035102c1006560078059440340400b5198100400d003e25440e940150140c40e00c25044400b4117a240c0040c04261a41120640d014030282c807010400d811100085d00b00400d0345050003440d55041a00c2815075440c0101c0025520b81c032800404d8000400c150407101607200080c0d82c034408000181d9145c0a90301610400000800445142180c00c0c2d102080842000d200c00040c103019105120640d12a040410030001150795000c42c40c030060300e8a803885043d1040c246485007070704019000b1501c07580094175240d01c81441e82c0d0030080303459041000c860861820b90301c0e050526980079800c501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 123005476 1250 123004226 123004237
    0xf080c09090708040b100b1b031603170f090a0f0228090e07080709152301110c030604020f060403080f03070818030f07020d0f0c0513090512030c 64
    0xc01020300707010881403c2d406000940a03501c00c600032403850300c45905441e8084018000c20040384c40401000a0902a80703054007441146c02c4140c03420004030307448110603010300c0e00c400d0f004140c0c120b0310300304490309100100c2c0c3c4c409513413280c0350035a041986540e603a4910b124030040000c510318841000759541d0001480c003040d103095000047d00d41c070300700f03404030601c403032180e1040d403070501c00500101e801c04a09401545ca810006003d200e15220200d80a000d03c105c4800c074049000c48041120100d042c03c0c00c0142c029000d6a503101c203c2000010181e05c031800d91201d0343d8010748840c1c0ca00c3d80d400f18195401940485580001180000006440b0300c10f40c1d000a0905600050b00840306d40c200014612440391912550340c180e40b070111400700c0f80f10b48150f082264004100090312500e0200190140c0b500180103201c00000a40e2040300003940390109035520b031b46801080040b0715241144401c2d4003981c00061014250b42e940c2c165441c4501207812102c002c006c000034046a000005030385 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 123006726 1250 123005476 123005479
    0x130306020d0c020c030c030a0b1005100207050a2112050405060c0c100503060307150915030504020901060e0d03050730020610060905040e010e07090b0405060906010f080c09 76
    0x550715440020007000500c00b40b0b441c00050701070341c86445850714010420064150000e0b014148a0120780c0c0da2113142c082c001e16604401d10070842c00702e07254541400040c280030007500140441d50400003044080c031450f922407490498031040102401c0381c0c5245542d00300ba4080c035829580725180380240d855029030b030000c0d83c01140124070020030000000d00c0110001c030513900460f01c1816028121032520080340c600340c150f03001410400500d841c50000c980304442034902841d440f603e0349a00c0280c00e0030480b240d00013035210350520040d4030348551814010121420403400301a6902c02080782200e402a01900303011010841c0c0c4180303c4203481e40c1d211003503400c0301120b40864200ea080d000c84051a9607800500c103070000a00010b0110040382d05490303140c2c903240e560500c0d00080002070005002400c104e9500d801107200360200c1005440080d2011980200d890041c1e001488202c506c0200154400d000b1a800d10070b0b580d0b00409a02d000c031100e0300e010f410039511105844024801c425400c2d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 123007976 1250 123006726 123006731
    0x1050d11010c082b02040602120a03110d020301170616050702030a0b2706130f1e03050306041107020a0603020f040b0a080a05090a05250b0d050105010e1f05130306 72
    0x102c51001801103800144103480c1c07260300b410000713001d02d20407805907015207130241e07005100740c119480081000c0d041c1c844d00d524012984a1022640f404c80b0f410070746410401c107801000502508042c0300b50711072180801001040c035442c11800400b9400041c04051040c07100004074002951418400090240c0e00048400d4407410190b000c6401d1005d1013080d40341c03980d18a840344903411400702e401c60080c0083c8000c11200d070800e0700d40c10500380c6085800c0300c07082411100300d01c45081c46032107102440e01131f803121512403400e4018842951444407201c03420b05030400c03070080140c1c1c1e205050425100c2518006172140c0021000690500c40c1d40c00041003c034021815520055000d580140715510070b0b0401c0c840703038984504407560b4030b0540c403000700250806806000680000e808800030b09022180d00041180e5445150781d003984480d0802589503101c000500041d60495403081c80420207803001d4805d501d2903030340c0a01d41040c001c2403004010000070414030b8802060301403c0a10f4014404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 123009226 1250 123007976 123007987
    0x130f1b09020f070b01060206070804020f0f0907020d0801050d020a0306050a020c1504020310050f060d02010203190801080606100f1d2206050402042601060329010e01050d11010c08 79
    0x140b502c1e00444030454004991400200e03400d440071130510701940c96905c1c1c58034280c039140d0811054a80d11103c49820010074854514982e6450500a005100b150003401d90303428040c0c4024122801600528003410f101400500144c581d40601e03011179800c960001195110448203102034812aa481e040e94829482c01000c8452607040c50b6000e9403003141200d50745280781034071900b42e68040301c44600845a040c00541c0f1414420f5008090328030500c1940c1c6000d2070314001d03034199400d0000d4880054410001444100c5081080c140c100004490442c1028000e030001400707040f4004401c0c0030400101d0764100c80c0410141140c00b04d41c4020800c006a1311581d50064001942101100403141800c800250030308152007182d05540a5481c0803100301d61007604196007644940c04150390707660301c8000001190b40d44d124260302400340c403800d21050099529803468203e0607006800611802c0c8010400c071341d01c410328001c51503072001094424451220050710b0341c5103004005854007000144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 123010476 1250 123009226 123009247
    0x11b0320031201090b0a1503021c0f0c0210020f030106180b18030d090806070e0a0302060705070303081005090708090f0d2a0809090c0c0114060108130f1b0902 70
    0x1240f03041e0ba901e803904006021130304040000c040d8151188038060000e070400c03001d4044c80790b0001c120014041c1c2d04003414003d07007a0f940e8116160000c800241980e01c4040c0548540e0510004107035400c001010750410320f90803411402440184075070b50a00600c00c1d91300514079400c00c03001008080d030701945600c07408510301c2e09401016100105100380150903801c007105008100760b0701a154050f000700700aa5656005480000a800085600c100d417804004010f07900c410042120b50710a0000d040391510b14a00500000360282555141080b048820310907910703103203076190b44801e65141c000b50685580d43d90314204003800d807101c2400e0061541e00850b058020394981d2000004081901d40e00810103030154a2072081413006258010030400e03600c0628204d190140c111061590080c50b045a83e1181800c68014441a5900c080c80d00104615981c0084010703520000640007000060304982d10300811a540d00c0d402400c404001640c00c001e0006051498041e021540023199181c1c1e1109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 123011726 1250 123010476 123010507
    0x905090c1b06270607020a060b01020723040b060408030d020d090f06060503240115030e0d0210050f090309090703060519051e03060a180b0c0d0605011b032003 70
    0x44508083c0001c05074081a00302d001455610131032043d070140401418a81e00d100c060940b00342001e0440c410004082040801c803a8912121f550744512030540d03188000502c410b032030380c003452070344030b480c0a100c00c01480201204542c9145500c00b00143d40d0942c0b00c11050044c03a4803031001d4105041620503004000b0694081c1090714021011540b00c4e00c00300d81c68042c028581100300d0010300d4100010880c82d8040c2c034140903400c510742000f10744034001c1c80300c6030300e844051400c4100507400100f00005a042d02d106040d0030401ca080842014500000070304e0fa41d01c249010107001d802281c0015003254030a90100010300401000109003c845d4040d0390124003240c01414800e64102d0026005080c0c0442000404c05000c2c0c003618181c0c2d0b83c950038800500c0e01680070f1200140400e12075000030b00300281617105116814146840301d40c596800710444c2c01a4000b0ad041c020441d076a0030b0340f000300080c18809130f42d141c40d0060007440b01040d001d0f404000d00010128034840441d41a20300302d0f110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 123012976 1250 123011726 123011761
    0x30d09060f05090f0d030e03041a1b070e1504090b100305190209040312060b041203020c010215180a1707120207030f0821010602010e0d0905090c1b06 66
    0xc406109544540003c55110548180e1000066110301c900c441031034000d400c40e1201c2c4400d4000d8904041d07855070b0103841c0d054107002e40001d9a40010b0100790040081034a0241c0c440070070010005a410402c6c541c00d003440151050020740c2080e070981c00503640c2e40e00483e0381280d01c1000c103603840c101a44180c0c4048441c1c002120710740205003140c00d14803800c0503120860398008003032040030b8990f40c90555107441d5040c085102c4680794040814082d84000c010070040c464044064040e1610b410000e0404103104001811504400c1681946124549429410034096a027400386129180c139250714019080070002d000c420000c50418061412030b010705165806091030b140f26481c0d60b40704a84540041c00000c02400c40d500706040030888010107003001041034411080c50380d585a400c0c10184809910100040c0c2d182d04540810890507c00320324400c2560038540701050414000a2541100801090943d0004076982e0082c407480b80c842031181c503041e4180d0758113042c0003500e6038418841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 123014226 1250 123012976 123013001
    0x30309060f050306060306090717150a0b07030206011401020a0b0915010803070305191119060606090b0301051207050901030602040302090f070503040f02150a0207180b01120905030d0906 82
    0x604001181c1c090040045900c03c5000a1115180d690b031035080004003580640722030700300300264272a546200c0c690882d5500500091000c5170380c05880c42d04004170518a500000b03050f5406100d00030000303030000341715415150744025031541d0300c51040c0100d141200010004c1c100301203013404e112492602040d03865140c1480c90548640381c0c3c2360b000f146e03602d1181903002000540208202c18076003c808040b400c040da21840d02c802c0f1140b1407000649070051003030004000e1240c40350302004000d5140b203007400810341c608141c4e400380d10b4500c03010058001441100d010301000351204848100601030840030704401007840000e96120309050009400c10301007280650030420200c1c040b9007010341814401c40069940314990750b100d0f03540000d4121081c4040b60041103c00d100100640b40c1300213400800c09650080818501e000702140040d988081c1d0080700b030b8030709915140c02d80d0340019120840d0041c1c010208003c0043d107490f03495072280c108030804041c40c101c030002c1082807035084003804820 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 123015476 1250 123014226 123014237
    0xc010828050907080106080607030f3908100302010e030a080a0206041a01030807060e0f01020d2405010806010503040507120f200109090b0f0301020d02030117030306062b0603030906 80
    0x104c40950900700c50503030089000652068001070740051107a0498000d850940c000462148003030114078082001c50050110301065001d41d1800c8000c0d50b211010800740a17250021007818492842c4400a02a01010341006800b5000480341c3c1c0741040100e03a9164001101d507a1014800780080d214901624100c81a8801c46c0d1219084030030340302c11034180e071340104480d86801e40382d079070701c0008061852184129016150041d452500c1c203101804901446c3e100202d0840c0307a11542c0190340154008090480c003041405010036644203803080d600010a08109039030f034640381046803030007505502c1820450f250b0000c840c2084260011154011305c40e10030010041d100c506c1d5803e0120700320701c1c0280028424902006000321640000400e9000580781c03008004200021038203a0f88071821000d5010740000040202c40e102d804c0340d5110800c450083c0d0f003076007003d0000442c036103d0340b000c43d00700e000c0820100040d04010185d012810584034000c00206030b50340b90280100080f4402d12000c0340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 123016726 1250 123015476 123015479
    0x81303060b09180c090402030c09072106031101050906120405071505030f0412030e060a0905060112170a030b100c03080a0903090b0315220b060c0c010828050907 71
    0x204842c3e21022001d003002c05014000c401c4014070aa10f040100305981c0740c85034181b04601500c03180c01d80c0d801200d55a6441162111902400c1e0002e4580002e004901e49410000c02c0071486609c0c694003c440e003440c280d0380d5105114005121800f4650b003880200006d40e051104000c40066080d04540d00d0909030141c103400e0307050030307222404110742e20f1106d80401c80004001501741c15910070084907a080004e0134001601c0100d180203021620242c03015551020385007845010480c80e4010310025900c4400032a943d910701c4082d140044460351000b4012032500c01e01c50198000c2c804c40500500355024071804041d0042c080012039009501091059010805810190203403400403501034690025172894030116001a520083ca84866110701410304c1078941e8a06000d4040b14000311001c01400755460b1989044500c1841c1d001d1045030100088400401c01041c628040c12b800d0a000a0700e40da42c500b04030044100705024031000d03a54144981c417410040d48481e0003100c6407812a0340342c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 123017976 1250 123016726 123016741
    0x3021e091008100b04080c0310060815041509080702010314010b0403170408010c020d020d18030f0c0806090d02010b0603011d070324060e0f1507081303060b09 70
    0xe1061680c4190440340c0210301e4210a0301800140d90802000b04030520826a84c1a081da89a04503030000340170f42d0031096603104d0701d00c0e08101544501540000421072145028100307580c411032903050300c02c05229040020180301c0c2061855002c3c0319119030900c011645494000041d03070101e0800ca011926014203d4841070043c898039041c0e03615070005130300e840d0454403845406454020100a000402c2001191801c001c0c000c0803590041d80d0000c1410004119010342401c9800d10210200800c620303c420089505240b60b070110394014075031a01d440d1130b41c180076000c0040d64000d05e4051140340b090228440001034281403180310382e802005000b107013808020f000c2c4130a01c070382005200c0f10340607015a0b1385242022500b244590500092100e4009442014505216400e90711041d41140422806401400c4200c440d20215401008408141e0000d807254025a00080c8035200c0440d042c01080b541000b03d40e45a5620200301008030f0b50380c9172100242c400c02c648c840c095900a400725064 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 123019226 1250 123017976 123018037
    0x201080a090c0605090406031b080f0d05030a0b04090609030e030d0207030203060612070f1d01060c02010207060522090b04060806040b06190905070215160e0906010c0507060302 78
    0x71960300c1081c014502d032502070229038a07000000d00c2603005d0b599100020004009901d6031102804400711400c1142c40c0100980c140340c01019400302a80000000801040e03003c0102d9502031404a00003070052142c401140003020f014070003e11252801c0b1a680034141c01c66208440084200c08079640044142d90403030320b0f0749161000039019405030020400c28a07100e0f0301d494201c0202d00880d50825654040c0c4114104954082102c10685200364566980019006800740c602c50034401604000381d40001d54504040c0300325410070401040389038001d00002904001c008090386007041090311201c00d41c00600d0a01d030000d01c1589481000500c020307022604500c100d80012140032981e80310401c1c030903015081c1100c0c040c80080f00101241540c2580300c3d0502a002d940e0061440c04440e074943c182340d0101802c0c0d848009800e54a8100550303000219000a40041da500d20300c3d9100d840c01652418014100184503006003440802c0c960342c16070240a4070151300e4a00720600e540307109003808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 123020476 1250 123019226 123019241
    0x4170c0a02030d2109050c0d0308060108011211090702070801021b06010614120a06091406030618070b0f0706020415080f010e0a0504020d140c030c060c030301051c05060c04030201080a 81
    0x60040c913007281c51034541c41d813021030058013403001d0324640700c0318900282040300c0c0c00b00c046011030502c5052203400e580c00f1000f2405414410350780d20903800036840e902c50844881040c0c80c030079031890001900d000d10900441c40284242e8000307640b280740940111752599074206064000344101c40000404030711851060720b0b00420100c4841c0b500405188403c5218070042502d400e05403140c400041d2080680315070b0f144005114644411810000205414594003500c072210030171410315000c04050010408034110703200030903d1661031200440c4a8028014020f02030292071003c00d000a85100c2585844030b40610ba6a8040c9255248a0701181c810028060905103102c0c84000070b01d0b002c001c1d80001d42041c0020901650040155101c031300001b603d00c044c00c45038102d0603410001342400c11211a0700c1004982c0300b400c1040840665580b800305100c0c15104c1ca6152040480701855004214840c68121080d1041e51520b1800c0c2202c60340244807ca0018a00e20000356140106118401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 123021582 1106 123020476 123020507
    0x1a0603060618032d010605010e0103091e080307090e0c07020909100e0d090506030c07060902011101020c0114010803070b0f070e130905060f09070e04170c0a02030d 72
    0x80790101034136031000061381003030000d210130703a040340ba85d1030300050070301e8009600d80d403908003034218104028a00d03050f0f80b180d6142c04240300300c0400030b5208807502d0300c0e4440c100359039041015000d0011038081c6500d400c18040900185843c42c03020741c21891a001300d4889003000c0383c2c500120785901c2e4507100c060340140000304145401420020003414100e402506514003100c2c020f4003480b0313106005205c59541d06481086a000c1e141c100e9040720b66070004c549030715001841c54028030b0418514404464010000140010000115103809912000c424501d440d204824a00c0d03c9010742020284240003c00800b2621020400d20000304005008210114581407107408c3ca00b001d07281c1c501c4065490100b200c0c1001c00110380040b900e11501c0d06482c4d03607c9080000403c00b0340702d00c8083d00180083e034207601c68000964800315038021070507528070b86681002036850a140113446c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 122841726 123021582 := by
  have h0 := BRFrame.cov_init 122841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 122841726 ≤ n) (h2 : n < 123021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
