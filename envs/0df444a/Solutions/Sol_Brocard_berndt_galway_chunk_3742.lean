-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3742
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:09.418187+00:00
-- url     : https://prove2.me/submissions/2f97359b-5850-4347-af40-da749be08ccf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 672841726 ≤ n < 673021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 672842976 1250 672841726 672841733
    0x601060302190519030f0b030a0b150603090604030c2915040b130e010902060c03070c0e01120f1401150e070e010c02120102210108060c07050a1716 65
    0xe40000c2559441010300700210703690b05108005459281c2c040e549800710b400351500c0203400900d8030240102c0c2136503e50011007246d0740d050045510f0507005030340e065031901e0405441c4450340207450300c141c810700c0c051090010074840040c501d680b05606040a80d1000854203040c01c54820040641c009000070303550b02c60140e4042071006002e110000c01035000000010200030070340e41c40c6104160041c154002044910b00c1c16003080c840301d0001c00000462107610780100d45554050100129242c0c40012180208590704210b400100108448091194140702c0702400310803640d01d006e88150342c0591020140f001001d0000300c4940d520008209540c1c11843e0010003510b5486902d0b8a01884000200403078014400b4215400c8169900f8070381c5001c41d4208908400b00c1c0c00020341642d070070b005154804d007001100078401d4030030140c01941c540c90110240e1804800800e54a40c10406000010001e00002000103140d584601080c41d0105102d03d402c58030b001d003c4001c1d54401100c07402d030061 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 672844226 1250 672842976 672842981
    0x120427140103210c2105090a09050105150403030801060e0f0a080d1806050901120204270f14150d0b0c04030506060603010506120c070f23010e03031302030f06010603 73
    0x2481c1c41c10b4507240420300c0b0310b20f00b50355528241001415201c4030514102c456445030705401c48403a0a402c003542050300c2000840e11000268000384803071680c640c018082450b02032080e80094444101003071400381507540c0100795030010302c01c01040c080964a50f4500d9a00c80d400201ca1480180844856a44da03c442903a942071980743c807004164520301d40c000b944400c440341002e540749910f80750300c1e040f031201c011a6480d0050b9039500000fa03007030201003408981c201004407003150100542d0fa8070f540440300714003118101a201070030180b034980041041080c4400b4160b0048001d0710281294040902050007001d040800521011010040108170310080300034005490045c01107401c02c0c0e48844c107201541c4028052194041030500100608218144246900a8406017414202616a66010100d491300e810032140340d01c0e096a071810980805000810010031700002784442101071907447e13240e20028012482d05c0521402480554408110031960100e070002150030340d40c1d40700d400a00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 672845476 1250 672844226 672844253
    0x303181203121a0306010512122b051308090418030203031e0906060607030203160302070603050c090109053a020f06070804090c09080a14120427140103 67
    0xd100c2c1c070f0b044112220851000255040820240041aaa07401c02c0304120f100d00112040c0752041c415070455144503840178018103c0b044c0f00b6202100110510003a00181468607545194424076000c100030907903040b51400d040482d0001c4401d5903405441010501500652415081e8041c0c5001d008003055400002075200c0e98540b20958103403854040340c240585015502102d4591041010507507a250040080481500c00c0c0100c0c1d25203980000c0c48008041c0341d90f41500940c2140e20104811900350046c88d600444204c1c0591502c42c07004006402c0446078024170b4000c10b1900c103401042c42400c1e49122001d0014484010324100c0120312400403151000100d000700c101e40c1d1020618101081a11039159000b41c1c0303103081600b008035500060002c0c81601080111210001840000500000b030710075000c0c1c0f40d01700350f8466250b840da02e0031108426500c002c4800f0071003040b03050708050390b00d0300c9800d11500490b2190490801d001c0030b8060940b100e02c8a030804000002081a524454032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 672846726 1250 672845476 672845507
    0xb0316030e01020c120306010e09150a1401120e0c0d08030a0e030a021b03120301060c0605100510050f040f12050c010201020f030103020d0f060615031b02070303181203 74
    0x2204844281950030303070044d80c50103a141e5021801c2c070007207000164051a881001890f1050891a041d030004e49040b4050340d078140106c03285441d01845060104101c1c0281a201e8000454203a1031000240445100d18011104950360080a211090180300610144c0001020003140000c03034100011968425100c0203449864894400000b16011064400d018801e4010b80202ca02d81900d00900d50140441541d01d802080282088079840d00c2c09503000e00000d0751010000100c0e494210102c1d40c0207810841555072607034040042d075440e0040003035121321910300f2584490140d4039000c464005c6070013800d1942020080860411003411140b54110b0040d811076011550f00f40c0168204d200b06040b114603440200018005410700c0440342500501c00c0800ba0030070145030b103d800807202d5030f801ca50700c402900c40f545404990700d03029024140c00c02c0758800b004030280110103580e4204600c002030034008401d400303000b107000720308205004000d65a050100c103c02890001c1c500802c01058a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 672847976 1250 672846726 672846731
    0x9040c030b0108070f0f0302060f0d090609080c010c0e090703020c0309030106140a060c0b13020310050a1a06041206050622060315051005041e1803080601210906060b031603 76
    0x13854846c10301144080700d401414040c501843c61032295200d0703000e141104140d94803000124006030789845014203481c0554000c40c0c0b20192542c915096410b018426010010380070000c0c0034560380c4040c5142c0242c0c103814010b07500c191020b1441d0641c05002c041c59411b510b000701c0065900004007456800d468201c07840c010403511a641511402d82c0c5103400f4220036948000170f65001145056114150300003130071120084465802c5c4c505540003203c07070b60607550321010704441007a039034041850444401c443d11030404d410001a1034401241d140090400c548031300114545459150404950b412070502004032020b12010f207001070001444105c481507a41c51881400041a1180ca4080c030003160340d40e4070640c58002000b020745100c10b01d180e00140d2500d500c4034070003414030600131401e2600c80e009000f6000d81c01d01400c142002019a030511100700d000b01e506240e1900025849502400001070089503030424200601c402c1e0000c12441d0000424080101a25440034407210401c0c1d505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 672849226 1250 672847976 672847979
    0xa1e1802031e1f06150c0b101208031b0a021b040920271902070804060f0e100503060a08030c070b18030601180b09040308010509040c030b0108070f 65
    0x240c0ba0a082da8a034031203030800c01010f00740b03c1114803d0586000540340200e80d258a90300c19111070700390510510b0200702d1040420040001e603000895024045450008a092920110300d148908000005110203400000502e031400e250315a40c00039114a055582c641804000181d59040c003e07a1808000200c030320904100c0c03600c0c1c0142104140c0c042c500b180744010b0b040244019554401e403a90b4081c01c02d40c00701404980728101c0e103a5070007004035511450700b02610781c41d6442d6220b04541d080036004004030f001042c54801103c00321400ea2404102540c0d13a02b104440c612088070100e40e00542c004908000e103603201340a9405030301c0403100040e541ea41c501c005a030740d21404c049198180c000a10822070034034888003820611503a040d011002500060010381060001d81101407402c850103065200c80403944203a8050b00c0054640034041e042c240c81c082c015540500c60540300b04a1030f00010204201c500100b0011a4494480460b55841d2414240ca40b802402500c2028071030700310 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 672850476 1250 672849226 672849253
    0x203070f12031d10030c090b0c0c0103110f040e1302100509040e060103030f030f0609090507080615181e040c082a09040203070317030703230a1e180203 67
    0x114000f0246009003d0403a40306070400940160a8071002d100c00e02c8909140000c950454100805440320b00030081c2c034501c00d001001400710b038044000c040c3e246100f84880707046266800102d509071800b581d25151b89079108241464503404c03150340250484844400f012245410401a1569100c200d50912680309001c4c0303459078610b0b091002600090f0b28420516a0f02d00035440349a06e00c10842003ca0300c55214028072084d19a1904201c819034041101086040014440142c0180c0c45e0584c5c0c203640030000c000100008071500c08441d4014007207003c5140d42c040305004c5d5075010f540200715045464541000e001c0315400381709802c1c0380c7c028840b0156802a0021640b19034240803880f102180c803034142480b42d0f0305002001281c0600c1400d2011000c03411801102400c400804d49190341c84c5450b0200800342d41c4112412055154401d00f1641c81d010300c01c45c210b9100100c030ba00004e010310882049100740c88030b100020041481d208000f88060104061400303824000e50494032200640f20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 672851726 1250 672850476 672850517
    0x50102030a020c060a030605210c0a060e0103020a0c0f120806060a0c060e07030b011e06030603081c0b10030501031202190b07020120070201022112040203070f1203 72
    0x241c00c1001600240c058442c40e01c0c000020340a400a90b180000b80580c503103020a01d142d0081c000b00c11440142a1010358045041240e603885100540350003e1b9285800d40180c80c5105808030f107410301d5008a041c071045031060401d5902030f07070004078200044e0010305054801c0c680c41000c0d040002c200f000000d0740e6040403411120035188960302d02080b1a41d03500c402c401000040b249482c140259000000842c0b4071128090180055a0707540e1211218450034401090103039101c2e40c103141c10450104042600300c2e080d81c10030107507a004005c90f21181d1120030000e0595058055008102416645070603505501883c140c9105407001c4051906521007640e0f0361a031060701c00d0185103103a200e0350005800301c91040e005207484c000480d0070703000c00444041c2513a407202213008104022a8040030b40d079041040115040f00004421100780e503001944a041c802d503518400e94507020008181103440c00c0202c3c90040c180722a18100c040e4072084c4418182c540c801c800c3c4e0016200b141584071071038400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 672852976 1250 672851726 672851737
    0xd0507030c1202030603030c2b08061e0a0302100c0b060a0f2105070e063a0c0506040b0429120703090210090602010f02030f010b250b040b0105010203 66
    0x40d00c9100482c0e044828140c060343c0010301c0d103901070000740301e604600c000070008603914807a07007051000040c50014200182c000c0705c450907410002c05900340141912071b15102c0d25000b41d60802c015011148401007085035000760300086d006294480c0002615a01c90b0440b040c880c45880b040445848440811040b800f90b401480c40c4d59017100b8040041b02c01580d03094807501c42d0030364229520007668031140e0903c1c00b80d40c44044499604410001c00d850038085503c102650303000d05280d440f029031444c03d83d40109461600c00140b50f03002910510014008160050800070041683d66444071307d0050650401d2091380d403140364440c41002030709140f0a1680340c8002040502c0d0402c0303280740d02141e01800140c4940c081c16501c0c1c41100141e2100c080d10790640c0502c0d00d85107072051800d81e00070b0031680e90280401682d8818800d002d001040c0b0400241110300d03103c503040d107401c13041c883c0112a85240180c001c2c441c418140860820a500346520301c1a070003074100740d0181c0c4c0d0b41c4e0010790710b91148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 672854226 1250 672852976 672853001
    0x32f070504090512090307091109181003140c0d05010b031c0c06180f06051b180f040204081506040b060301060c0b190c0c02092a0a051e0d050703 64
    0x4d65181e2401d0100d0310040c10703407180024121120710380d07256034610407900304100741b814500c40020040a1820500d0440d000800c0b191403072503070b0345410220581120b5280c080200100d201101c030101007032003002100980b03d0020208ca0f010522450207900900d0703a03070b841500900901c01c52940c08030f0101d10291400100791180146607426030780f0b400080000444840c80c41c0280c50303592003c1303102e000fa070909040c480c110008243c20640c24044450b1011105050480d50030000440103a80300401000c1c410401d44007013154007181c800040290181d80c0000d1170b40d1141c001441c42e14484030f01d04500ad45c0044e24100680100c18044c006144424000c10780440c2c04403c0030700c0040d94940c18680e010108410402c148180c2022400a490081010200040c0d80310220002d5141c61003085030454194034000454290910f89442081a03c0344001040c0c2000301e95524000c0c012404c5502080d02c0d2100442c080e40c3c0c0c1d100c0c2800742c1d00282c81c000c0e0400c6c0b501d4001001d0314001d22805030201d0301d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 672855476 1250 672854226 672854233
    0xa0209010b090316060513050f031513020904050d110607050a0c0f0203240108010203040f12031425031512050109020310061e0e04030c032f0705040905 67
    0x810030051416407110b1486a0144982c0c801514901c2c6800c001c6400380c003003551204d80d1101d410340c0400014a454216a1040442d41c90031035103a030300000d00b20342819009281c51190b076200c090f80106110b08003806504014800f0800007084000300d44049090200d49a001404428000d17107940c500013141c144001c980708000030518079004000c02c05005110300040790403000c02c1d42c00b00f400e1003180a4a1240700318564400e107008440f4440d4a40500401c4008508520301912041d10b444003000c40a4089500340100141484c481d03000314600502d2810420031600f444210001c840b009401c3c0c0104c044039400024108500c6801121050303011510300045007820000b00c0c200b44592004c3c12141596585030701d10068509202c0041c8120340c0c0000050082d1a043c5114a4040e11004160361320540050610460003480d40d801d0b0402c0c2c01d498214106007041c941540c1240f400c1c4545400c0d9034158014881c5541d500182d400465440410307103000d11b58903403c3c042650f590050080c081e40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 672856726 1250 672855476 672855479
    0x260703090603091b09050603070602030c030406030c1205010609180c081f091406010f0219081c0e0c010f02070605120403200f010501230405061210020310080a020901 73
    0x80c429000700b406580a902c41e0203010000031440d041441e01d645c0b00010310340d100d0f82000b43c280340074465540201090f0001c0c620740344641c2d40050302e80c4524001c507000c0c140d607829001c220500c100200700710840407020800855854203405000e20901780300c1c0c8035003400000340f024085071440c0641d10740b5a4094036a081c041c2c48440c559040c401100c844218404018a0001a039210500640030700b10b020074421107a50500000041c24000300a03000e50940d404400364526050500c13510140494009021644894000301c00c5c02030b0f0001c0f0710703001100300c0c20840b603d40300c1400812001c1409600b41c8880614015064041e078413031a40d0312541000c10000d01004100e03800e8801407603445403092405d080340c0000680c02204c403070200240482581d20038000e20408042c00d00c00c040c05407070340c1607404250741c44071101801741104000000e030180e622080860b47c80d07250030000218056400703090355003081c0080c42e160005d4108503124401980d003100002080c0034045528100329801800d1800703981e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 672857976 1250 672856726 672856739
    0x10605060c0a24020d0501031509170702040b061c060f06121a031504030210050f010620030d1a06160201050a020f070b030f161b0302120726070309 65
    0x21148603000f010300b100c052054521403c82c0c0d100402601704403060004255041d410300c10031030001910707851611450181c10f5000700e104601032030549120400003035a980720f6480860040c08601c14080d80140020410510795454051010303410b500710001000f103140e0311080f40c020302e4024070a60b00440c500d203c00101c180440d810412101104c00d4856241c1e4550300c020074070b02880c48010b03a03a114250005d05c01090f03414084e0090342e511004061210341801e10a5107040913061040e142802690745843c4d1710420245480c00915500e80c0960f40c4540042c03030108060100892040204880004200e080e440c0c0ba0042e80e4501803c40b150540c0200c4a60040d00c40307a0000d1422002c0d84602003200314a5401001840c0c060b0842282c3e00303840c1d04003190084011240a0079164500d24500c02800c2c15070790021105210b4489841070381e8020744d81d410f090f401e100d0588450020680d00140650034082000307030444030103000380068208501421031800a40c01009030040c0000e4180c4000c0115 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 672859226 1250 672857976 672857993
    0x50306030613172203060b01180602190f0507180b0108190236010f0305090d050a1709030405090601020a150f0605060711091003230703020604080f010605060c0a 71
    0x100c0130903039107014030071502520545118182d00403240c041d2100540f020a503402030040080c0c40007405004002030401234065281c4005d4403602403100c015607150824070000203054164544c000095402c4142c0703d200d0000e00203034006600440d5801c0c400c1013040c48d44200c0c0b60500c01d154898501031641c5c08141d400c80030713600540d0f45224020002503002400903406601842c0305c858014245084c0c6201c5001420a40c9010b0000d01454501010072980080101d000306101c2e00790701d41581e039000440b0341036840c0d240c200b290b85096802d003010400d1b8120004028030a03600111004c401c5543c40c0c9004903941d00d41c05500401e0031410681e9864042103507042151412070307038000400d20300d40f9040841d4041e00600d5082e5034201018940c01d06604060840c16000b00c04141d11440e0f203811500c40940b603180081c800e410484983c010010141d10034010364000c0c43e07000740111b9880356903002083d501c41c03014a20042651034a400050146010300c2100c494580610190030000d486480c3c2101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 672860476 1250 672859226 672859237
    0xe0c1002100b01020a020310090b0c0909060f03030d1107061113031704030609080304060e0102161e020d0506090705040c09143606090606120705040b0a05030603061317 74
    0x5512501c5c851500580d814848581403051282d80003a521803241091031042201421680c450b04007003003181c1803912442d1110350b00c10000e0b180c8580301044030f00424551300c50411901e40081c0b80200386031005520500600025000310f0050044280e5003901203c40c0c850003407402603c01204004000068401d406020000c180c0f160b10707424039581c0c0d100d00042d20601001250716060003c20041008602d22070f150b418480030000b1030402c03207145880c8901203c84180a8000c0c2c681052000d00c900880100510441e8003800b0301144038410f2030415034541059403c80c403075005000f0041080e0a092103800041c280558540302c44a02d40240798220311507480c2d4168004026000c50f0200001c2c18481840d40c00c449100c0e091715400c2d0000c00300180101070a03943c801c0c0800828081980c1e01c45058642d800c0140c21950085d403504001a1090303ca10351095110f4140800c0e01e0503660303040000341d44102404d6042c0e4409a0b9841603291040a40e003030000c1c50444000030003035650400030082c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 672861726 1250 672860476 672860479
    0x20f190611010e1903020d0c0203060106210f090201022a2b0c060f050f0304062c0601050120061504020c030f0d0b01050c0c04050411130e0c1002100b 66
    0x502510220348860921020301301c11400301600c6000c000c10540d0400c40529100703240c0c80c0402002495a00090b120001031140c1d0f03040006c41010103c0748118040c0c540d01c04060524108000c00c54021060f01810804905a001d0b004950102e002c0807006c9c9144c0300c5c000a07001840064019020801c0601d0640c01c40d4034011700308002c54401c03030041d40800090068000c0301032600d280d142c9880106007142414652003041424007040d50100d44150680e900243d0040300401c8600015449001650800000024040c0c3c0414074115150300030410f039040c0c1e203080e80c5000703015036a0300148402c07942000c1d101042d81c0c8140005002009081c1e080a0041d000400161034501d01b4010a07141d50004440e4024043c40002c1503017201c4654030622250300c1d400c0c2070190511030443c0c2c02c17035103915401d5803440c0915100c0d000201000010340c0f0758000160b00920b8481e20711a081c2e0380d04014a1281c07100445442040401141440c11540c0c020901c203160340203100005524540c0c1002d4000b0400b0355 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 672862976 1250 672861726 672861731
    0x5010f0f0e0c0a03091e0b1b0f0f0a1403010b09041d0312420102010b1e01090b070807063b0a0c18060b0702060f090a03020616020f19061101 62
    0x1140511100f180080030074062040c7c0d80007418075140d1103060481d004402e0030022030400c629144c40400005440c40180700491385911007007031480a5900b03074011080ca186910000002042c2c1c525500e01505030742d1020f071400c11000050f680d11403c0c0400c41004403150360b005001c034109440000848980c48100421088038060299805031030781c07843e03d10320b8031760207903162021140c0112040208944007024802070080042c80c60104020890248414003903400000748514140d00070f50010004204011005503100c0340e50402c182640c1000e2012103581c0d00f041e0450007070b42848450545201c00204100000d511083c48244800700051030202c40d5001d21100b031000b040d038410703900c8028040301806d407a500d0004800788088424035084005010740c03c0c488a00035884017001c1e110102041215141d460313403a1030004114400320345c0025401314001030764100280c020148460601e20940d0381440350312000c002c210f0082100e40d0044100485035208024051003001400d04888507403000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 672864226 1250 672862976 672863003
    0xa0b1812030d0b01110a031425140f0a020f040218041404050715051801020f010608010f0b04020f07030521090109020a080a03120f020d05010f0f0e0c0a0309 69
    0xc060942d001001c9240d00e0b82d03990701507111556042140c0010014a5030701030074240506980280c1198030504c60742281d0403011840d4400c005548081203c00c1c04aa2844400e00c0d4191900b0640c1ea60b00751560381c42c900803000c141c1183e02e80002e00d0b800d007680c001d00c2c50301102084010300000b074114100040740c510707098000c07007115120362051b51210190b180d0710460502d02418161301e4042160f110f01c90708802c0410b55241d040ccd0200c2690300d0302c80e680e11500d0714071001600403454a5405482641c2701d502e13080c2c001413100300550180c01900c840c2001804901410020002217009007440c403140d00e04104415000240f05000504000004040300071810403040b05000000d8012200d035030b000e0395684984425483d1900d1440020061640141201d54140c0c0e0001e01c1003100782d00c0c001c142a240c0c00025803e1000d074064407103c0d40740705010070066030b6a0381040c050541c20303c42c100b1600d03900e503408104110802c031914481e0601c80480e40c0f921751b07254011001065211010780d01d40380e80440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 672865476 1250 672864226 672864259
    0x1061206110c0c010e1302132c041e080c0d02060612070e0702070b07120806090c0904091e05070e0603190f0c0f060309140d021b06040b03010e0709050a0b18 69
    0x103018010175107000f40e14450f003062000d01003040520019180c0c0e640c0c039100d0081c91f0209c54420340d8800c0c1d100036040c0d4150740314442c02d403c0701d0074040c000380080300105035400e03044c1c030004000b4007a035115402c40764a915403206220302c08071313841d800c0305607a00422070a1000f860703481c1c00180c0183d0300707104032204103a880480d491540c010807800c6175039540d00551084d00326441101e482d08140212048100750600f007003021014846c00c2c0910f4000d80d29007110100780b00c0091302e8100d031001e0740b0000310700d02c01440c40c000707031030f800503001e5aa0a502d00030046415030030005100c0c21807211080d2501d0800d211516001c0a02030301c2c034400c6134404e180c46804225607140c00082c40c0280940e031408079803400c00d45002c1281e8031103115140070303a611010465030015400900c03500f0408115840d0385ca20140100420168440c4e50840c018000e4000300015500f80c1d03841c081c41c0705000554558100c1902c070030803c403005030360f40308a00240d1024000c40b20103400010f0800c510400c0102040c004400c1d441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 672866726 1250 672865476 672865481
    0xc120304030c050d09050a05090402120303070905180c03071209080708030f18070b160c081e0f030d050a020d060602061f260304030501061206110c0c010e13 69
    0x290101c000540315045101000800c0020400d8255113040030820581001c0c04224003035103e101e040d104441e564041010754490300c40e202440c0401070705984e80c0e071505807009000e42c0a1485203c0c06603c079140c060590303840d07540c034440c080c032400b03040c8030f1560310781150845824031010301c0c100b0351070341d620723007100000780c0d400c0080c01407a100b005100e460f49040007a405501c2002050480030a010907103559803a40d0104031042550444004a1746900a140c170148003118a10030050000342203c2001c00e10443c0001c501000c5c17060000c61244001c2580e40c0c5507100c0b503114562500e0b40d403040c440d401011445070030203a0301150500b0014140312501081c0420386440380e0003100941c2041d001d20607061140303005a11540c2c40d03001d08034207652810706d10485005075015000c203c0701c0418032806405070140105d4000b19040002070101c25241c2c9010860b904004404407006440e0200361f005604a52080d03c1e01000104007400d84480e0010056481101420015610510404c0740305074101c41d51 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 672867976 1250 672866726 672866731
    0x7060b1804210302070c0302090901150e040605010815010509060d020405160810030b01140406080d0305070210090308070c020a090e0714150a030e1c030203190b0d06020c1203 77
    0x391140c003082814940a40c500d0442c0254520416004000359404604164214811254103540b00e08003940c03500d02081c0100205841c0e10405c0d402400e00007405041016402e0245000b039808001903640c0e501010b0f0ba03132034810344681c407034011640100101d18100303201075413007040a4070380c81e2202d041e5800101281c4080700d43d0702c0c0c500040e800034002ca80e4800700c255808005803000d40100c0d070450300d81c507840620511410301801c1112007001140d0712981c01101c002d040d144100d60141c034103800060060081190128014891007010500c1107001d801144c1d090317501521411600d0702c614104403006039140600745e0308104040000a0140b2a0b4400c1001000741803001d404c01c2820b010103148881384100009100d54591108054107904031400c403442201281000182202c5a860441c24140315418060b0000d074a5042015174a415400940c825000c1e220000343c04491001558200d90140340c6842c1c000307965140100000700301d58018013080c444c010464030070301d041080106956008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 672869226 1250 672867976 672867983
    0x1050a0824040c0f081006021b192702160609060b450609040c0905070c02120115060507030203041703070311030c0303040602091c030e0f01080c07060b1804 69
    0x180a00380d5040354001010354104100310380a2200916080d0029279900000c035400a1803098511440c0b40c507174441c5030f41c3c811219454000b841d120356529215050b040380b00220407400c842c000307284c180c105062003294840c0c2e6400d81e00c9801c105c0780342c840b00010450140215541c2d583c4804449887c0e450301c0442c4000009141016002c01400c49195214408070465502c07a9032a0800140c03540c0c10080713246e40c031407029942c0c0fa040e66110f0400e0031680c40c0c0b07030b4051481d0618002c1800007040e88541800500750007a00c10a20184110916a01300d4440301e681040d90004500b052054a10420041407113a0103881140d0038561a000e0b0000d440e002d16050300090751000942a0030950411000350706a691040554208540b1409440e140e2000070001400d00b80c0c000742160003a5601e040c68181045c203136003100c03856080340c80c1c0034000e403503482d201920500c42c9030b40e405401d40c46004014881e9590740c03c40b034140400360365808083c290041d90250301101c4460f1b0001c20035581000d05210340d02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 672870476 1250 672869226 672869237
    0x4030203030a1407062901111509070f0b04050901170a150902090108010203150109060c033b130204030203190c03050d020312070e03060f0c0408011505040b01050a0824040c 76
    0xc06c078481d50340d4521100400d8180031a034040502c3c040c001148440c99007100c240444c04945d14405003a09011607904070360a161070143c0c001c2001d41184000e4416694262100c005036600c5011411004081c0c4120f249581d0026804070001340130282d0040000e000301001080c00d05841d80000c202d440d09800041c0c03269030200400c82e0301c0340c001c0354140c540ca50a007040782d03c89041100040000d00c075101e014080c42003222541d2600540005007411580000351803481d91220b030900b142184c18000c0c0317414070420210314500c500d03d2492003124112903004005100d0b41e801090070905120718004103840e00f8405410000100b5024821840c0040c11503002e5582c510650080d0803c40d000500840c04000c140900c101b0244c500040c00350b04143c55250014080d540e04107000d885201d1038201d2155035090001c6500d00716500f200d010191041141e09022030841300004660901816160000081801c00030507600c241a065010340c030310012540e0110554800045401e4a003042d444c00d00081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 672871726 1250 672870476 672870521
    0xc05090604080609100b0a0932180105010b09042708071a070801050418050d0903020405090616320711031b011b0c0603060e090304030203030a140706 66
    0xd003400141c8140c4400302c400c00c1705800c540d020900c2001f0500886c0300740781c1d80310706164002d0000f15880040d4414200200c41441d40c480c02e403a0b07009003c0d42c0400b00c0b0850609040750030705040c090a030503100d6004003a41001041c000f0840504005014502c9010b44850400c603a60390744258080243e0140c40040c0e0764400301c1c50083d00c0244006c2c0950119030801080c0b0a1440d0f2014009045130001c030350126a907030003d40f030103080c80040b0310010010300c00c0141001c0c0c00b81d040503004080f01e00844d020400b56407800c1d00e003500c40c81d04440c4440074002c0035400d813883c20701440c0480400010300b81d40030f15043e9404881e01c062450003180b0365010030042440010400d045105958005003a005080c1d845001c0e00e1101c80c1c03804c03038001981480000d41029001645c0311906601440c0c01245c420a0141e03210700103401010a4018400c0340f004190014140340400811035084a901a00640c0b40c5550a00201d500c07880c4a0244d624000041082c0c4000c18220300070620400f210071042d95100d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 672872976 1250 672871726 672871741
    0xb0607050f071806080304091e090b06151e030c21040c080a03020a031b02040f0905060f0c1608090919051e0a111b15180307060c050906040806 63
    0x8280e90200c03c0e032841c14400140802080801a10219071010001040c803114280913800c0380180701d1045400c41c1d20307102c80310084c44500c0407418000c180c1928000c141c1c602100307010040384200c4004000c2c0c050940904001003001000440d40a8454403010741080c28445000d50744614140080081383c00380340510060014400304400105118001055980540d95001c4d403241d041c5080a018031100c2c00c60704006114003162007401c01d50042041200307a010030084401003841d024191000d1090030002504100c01c100c00300e003d03071120440d043c2825080f00307040307505206850b0b04451024041c0302800342034a03034a588901940d81c0d00c8807044400c4c00685548110741300209030441190100e071900410800c80207905420a5a802c0007241034541144800c05520400c80c020705400c17001c00300700408203000304008580440f003d5400ba42c80e00c4000481c544c51018512850395038000304841c3c0000340f1603038890030004890741001400c1a1000d40064440c2c0c00c0b80d8171400303083c1c00c01010402007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 672874226 1250 672872976 672872999
    0x2160e04020316060f27030803010905100308070b0901060905070e010f0e010e060c0a1e06142401030b090702070602070e010f0303051c09061a09190b0607050f07 71
    0x80c1c9400683c0e8a980c61401900420008800b40600288020000e045e204440d101c1580c51a41e00700d04094040d41d596071422851035802446031f8060706281c5008940c40c5000360303810384100c0f80c004401070700308240c6458103454032001904036100da640c1ca4000055107042c41c02407612448490700c0350350304017030101b0001d0000c1c0f203c01c103a481081f41d141e005500c070f40e030006480c860cc11410b4610549130100c64074014600340240501420511460842a4041440c20050808a03200700f809105007210581c00020114096480480007030b010f124619a00f20300d41179000700b90b81c051601041c81041840842c0d40000d054a0410058101042c10b0085940400200c00102080a9011469032510030b0158081040340002410420b00084d905680800004101c003081c41c1003404001c90b480c07070324080b0300038030180e425074100704401c2501c000343d460650b006910804002080e401420304064605006214113680c1d140e1041080c445000401c2e4108180205101141c009282c001c0c108120701d150b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 672875476 1250 672874226 672874243
    0x609050114070f0e0118140102070815010e090316290c0a112803080708070806040e0f0a0503031f1203032a0201090b0106030905030f0a02160e040203 66
    0xa000580c00a1103600c5501c8215903403c545039182c15030450300d0510040761a0300f4040c400d41c0c03195400050104442c00c09150700003055109030201c5400554889000d51101e5501030103100e60500c074001006414010552103610003203103030503207142c03035803007105010031000950702950410800c03d20749494518003492000c00f01c485142d03e0900d460884600401c034800e80a458041010321082c0c42c000d80003c02a003660007203450001d5045202100200c541100390240030f400207406032001c074803450701840c1d45501a02e200c5d62081d40543c0c902040c0400303000c5940c0558180d00c035076001c200000106000d010049803080c8040c40d174a0820301000340c0300510b01c030121030381416440b40030400b03684000c2402c110542d15090104011180f9240d860402c3d45100c000c6410340200c84880410541c190300c0080b985200340c0d5181500d9803510001c5007241c40d480001060380e07000700021103016001401800d030081462046902c12100c010701c1060700340c02a4400713110303003001c0401c0c0400c520f418848d048 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 672876726 1250 672875476 672875501
    0x90f0d02131410030b01090f0902030a030503070906030e061602070f23151801200105040606210303020706090204140a061202090103060b03120c030a0206010f03020612100e0406090501 81
    0x4941030954a038040c0105c41841070440300c582d05d07200503070350304000d4101c1c001c601d030001c2c2690307001100360401a090b90300480c0c5200010300c01420100310b4034003a00c21383c0d0310603901c040100400e6075410311a2040c410b0003c13008041d0b00c280100040d192a18032492005050300741c1018245066201c4505450240201090302c100c3c4011701d4149400c50190070341d00c0070302008460440d11070721000141c41a825112240081c0040000c40204811341500183c0c0214414941000325030780c0c0d003204041540a4040b080a0303078019405980101b4402e030054901c0c079010b0b50700011a4150740d030014044031034101000e0098120082000040c500500c9420b004100059100d44030b0704495000035150030701404024200307582c0b08130000081c2c07404c101685a04100003180d90359036001071901d0f956608003411440043c4070b0a0008620711802181c02c004880d4003034034940c1450540c0c000762104074001001c08032a000d40210004200e40d00701c40340d500441c091940001da15030326090860a580b00c042c20034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 672877976 1250 672876726 672876751
    0x60606110c15070b1504051e060109050306070c210f021209090a020c010906050406050105100e0603010b0a0c050d030b100309021305090f030301080f071a090f0d021314 74
    0x101d400d800c00d80480c0c3c00a54003440d01c04060356050388401d00b06800003c1e09820610300000c11189000c081c5189500c40b0300b044050703401ea40c8202c0112451807aa0241a42603003154010076031403802510000d55851040115a401c0c1000c00040000c8404c00203007100012448841c030203505030140300c20348001a01000041c5002c40c0c9001050783c3d000040c2a444d070203036000a00d800f280e1000e500003005581c1c021010f00c03541c04c00f800e050700038103001c2c0075040c460500c0d0305003040e15501820056200300400340c40319007141c3c0382008404441d009501d44005102c020014500010000d1114110016198400240694940d0701748035481032414a61702c10305151591040c09a0750710078403500440038828010840b50340b0000782074100240d111008003030307104c04000421403030741c0403d80b407801400d4801215000c55480b01c0301049221160059104140b00b0010120f840c1401d003540010030794041d000c0c002444040d404140c02071a603000d0744540d541c0d0343c14200b003c480254007503900310803056110b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 672879226 1250 672877976 672877999
    0x4031710060509060c0d0908070504020901020604061808030a051e0403050904050403182c101208090a0611010b01020c37060c060506040c200a060606110c 68
    0x220096800c54050102071100c00700710409140c0d00c54080f0b070400660740c0207482c080250000003034402d050901600640340500d09022030141003501c295240c0b80016801852a03440304d88952004107002c0700c6030002c0c80b640d040503e001c83c004500441c011442003100103020314100c2c583c00101041c2c0880625442c107800c0c03d100100794410b0580708014002c8800080b03c0e16030340340c1514090203c04c025000c032410f6100c0019403298400100c00c8010200140c142c1100b003039024105043c0e8129001019092140014820b14003404400c0a1180c803510f0810302e00000100024105103a03544080000740aa1201400c490420300650380a91008c3c0001d0040080b8807000aa10215818040a11071a06803202d000c84180d5180c1000d604540c0120b44100e60315450b004000078144002a2512810139002c40c0342da041912074160041129955000c40d031480078907440b09103412041d101000d2040f210000302140b11441100024017603a10740e5070040c991190124185107220344058802da254800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 672880476 1250 672879226 672879241
    0x310090c050d1b08070819050114030106080703021c0c051c052104060f12020a0203070c0617060f030109151b02010e030405060a090801050c03070908010219080c040801090506040317 80
    0x2001c1740c0224007828a804603981e00c80694166000050350740d180c40c0c0c00c103400002c2070200c0d002004e441020a42c002d0224645462855a0350540c900c0001d410650004071400c6884440300010301c1d1900c2019030b510785075910000510460312115a400002d40b07807000444c1080010810000c0746190102c5440020882002c5c03403130f0500441c828001803000f55469020000d104421503800244071001c11502d40e02c0d8104001d42c3c9401140084078010182d50012500500030401103001c801c00702c40302070895a4000c1481010204480c1aa40564a50060000041c08820003c00154241c1d000140110b0b51004c00050b85018450b06415640340c6102c10014501c00310458003511015560a690383e2a4810125403600c840e52118030b09528100512541405000c0210b020715019a070b43c4510780d8480000900300c0c8501030790b40c0b022079845050380000a00441c0260b900c0300395000394508003680c1fa0019420766450150403102d681180b02000301305070304602180451030722242c42d101c0510f001007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 672881726 1250 672880476 672880487
    0xb0f0d0201050306030106050303040308031b0304050a020f0f130506030c0111070335040f0b120a1104120c051011120f1e03060f0405070e04020310090c050d1b 70
    0x840103030401c140000007680c107841c2500301d4001810701900316595651359041040842e002900e047d10144580d110b0300c0c15140c000e0301502c0c0540c0d01301002c1c10391440c0c1c2d0f40c01c04c0b80340c404140c106500003030b41c4140903100d07680725484a00d440d59028004507881c03130500d0400d410b003458840114103001040c1c410410105001070b862082d6603111481e64104d29100400311142045d00c1e904009240f047e0014001100c40300300900210b4070302d001e03158192510b03542c00c5285402041c1c20080321003408400600003501a410141e00701224100b0180303401c0d190321700c101e002d1030b100e0402d4945c011000d104000b9420a0040800b000d4460f1030188008558084515101c0d0380c600640c2c400714002180d100b11240c030040480b0f684c003484003c500250401c6803d0b584031a0800c5030306910070f0005180d070303484508040c05514450569640c0c1c440102100350100402504081c01c42c240c0c40c0c505c3d1502089a00303131489940081c1e540c44c0c031926159100d1100030400c0d2081314040003103180f000781110300240d0f00079 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 672882976 1250 672881726 672881749
    0x6060c0605040f020d0f0b01060e10050d0605060a02032106090c0a05130603050414011116030909050c04051c03020714040f1d0d080112111f0306090b0f 67
    0x80400c06032180d04100920300000000a94054208417008041250301410109401c0c441e58141880d80c0c2d07a1a415902d00f80c05e402c0315500f20480c0c4c0451009240700f540145003042070440006840c40e114400b0641c0c0d908040407a802503400000c51008100764aa00300f031400e60741c0c140e849002d2408030041490707a0000380c00c1809030003001c10300e080b41170f0281c4c1c20ba86256074003280444103682d85000007400b8180580302075400d100c0201d0b0744c01c402241800f901032030241817105146406441c1c0780e0a010410b22030000c5e01004501c0c1c001003821034041c040c2c2405003000203006a22035060104000e000041c848404280700c011000702e82c0040d03004580035084410058522030700c008160701041c0500498044040c416240403d07070704505414410300084041ca91003101c004050b224015140b41000b8003c20286008043c0940b00055451080704050100a40441001c1000d44683c84807100035110004c046034441c6030510900d141480f62922004044510646103a04d1901255040707000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 672884226 1250 672882976 672882983
    0x1e0603100b01170c131e05010e12060115090b0a1209020d060f0501060f05120c0a23030a15050603060409140703060203150306040c06120605100203180406060c 70
    0x9504041c9001d0b800340ca01200c00030507221054610b46000e8118504a900460b0380300b40311880c146010400111032242014105c0b101000a00054240001521012303100e0701050340c0300000d0080d030040328005004903402440101d076003408130151000094160240d0350030600100f4401d010740154694444040250300d8045500098034010a0010a119a2032600050481410003200c403209003591b5014504072030055940002106800c0d000b22034501c1001008400070784d801001c5264070010350001c00720001a41401c03c4000c40080e200103441c3c01c8a801e25091080210400080c0101f500601c4204e13040c0003481c0301028240f038001032541c040070340104d0013507503907100c2142080400d4498021050010007241e5843d5940d191617006540220b4041350100c803403100007829802c0020364207000755070000310410701071b013010002c40d0b0b24590716440c00d607095198000024980c4078801d2002056a96602441c0d8440d96461210811054109881c0c0164540341d000c11030140e000301200d0700141e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 672885476 1250 672884226 672884231
    0x1b06020901140703180b0f1206120a030206070807140a0c0201201f06050306010b07060207120807030510050f0f0301061e0807060306030b1305190503031e060310 71
    0x1580102c42c118020141420101000110b003410b00d500504c50040f0300284201e1601c40381c2d01c410f002511805510001a981e140910244140c10324082500790300c80c401030042c080300040005030782d28194480c5130940142e0012403d10038817a0384404256400003c50070326500180c594101602d043c4640203800d000c01c201c4962100441e84101c40030800b600c04404030045030a0128202030301c51089400d0350325035800c001401c081c1c03140a8011b00c0101c50340100540017a038a4040403c41d02d5100d00cad000c030340c156400c2000c0400108010062013002c040c590317412065180c14200501201e2014002d041501601d5a0030001d075542ca240152000b41e007501c44103003070b206140100340540460b80140c00c0580507107900d000d0b0300241c6803100c002c64007210200d80e805a0b680d281917044802500024005804010008a038210303d140070f071180070700c82c204450403154070398804180d114074150111a503400010600601c00781c2c002c20007030300000c3c40071150b0007400d0000000e5500c1e880d00c19641170485c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 672886726 1250 672885476 672885487
    0xd02070b043318050708070f060c0206180109090e1c0c050d14071e0c0b0307050703050f040b0a08090606040c020a060e120301030609030f1d130b040e07151b0602 71
    0x1520403000500f0b9500a0440d901c0c40d0715101d280e500d0744502d000e6004203c0701684002130325031117401001e441d60b801425081c60b0403140c4517010412104e60104078180301c5200800207240c4030074811000b64489580250020700548144014291180c44402040000302203004012035008901154985400d08220701444400301c91541c69001345030001d01160b00344d0400c4641c1116500c10011602c1c80740c103043c0c54480c0c03211010950350205a40840001d041440000c001034044c60042543c5281120301e98285a5900c0c8110410f60020140400059a001c20700102074400c00c04560070010403202807140e044810302c001e41c2ca41d0301c080050511500d41c0e03050003058034240180460500c2c1b05801903965a16410081c0203888080000c400082890703035904c880900c6020868400c0581c09081741e050241c030020001d01d48844820740143e941d88a030340c2c21407503032030f84035a07203101002401811409141c40c3c8461000a42c3d43d0404e818000115208100b505c480030150003107607032007800182c890b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 672887976 1250 672886726 672886751
    0x81f3b0405060f160f0e180405120406170a090b0a020904060807060509010c06060302030f0307050d14190e042903030406050f1624050709150e0301020d02070b0433 72
    0x420840301c82d16004144c7c02840721444020300d0b841c2d0700c203034050412a000000515000c4200740b0680c40340d01f00040300f500403484418003c000d050380204120401088040444e15914000401680c4500c500c9900003110000c909107070240c203006200f03030805494150302d802c03005049885100308840c100016910f0f40300412200c3d0380900d02454000e0215070b004241c903036290703580342d000010507922449a04140da10452160f00d05150b418140042d050034a21555150601621810541428000d80102e28200e81d2103d204400700240ca01c8030740e00d2290300b038a0080c00ca134003284a950b40a0f8004000500c80b9540000c11520307444101810305030341d080340c881417444200710b1503401040d110303002951040780d07405405100301400d6803606c00c000d035884800081d115620306114888904040f101c1c0180c07201c0c00360715000a00d20001d00090328100a80c8403001c00c81e0700100701120341d403600d80300f40010b002800c41c075401e415100316210100420740c80407074031101014005640c001c1e500c03006180c010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 672889226 1250 672887976 672887987
    0x1201060503032d0307020109051b0a17030c0610060306140f060304020307080304030803060103050a0515060307091809060c080c0d0209060721081f3b0405060f160f 72
    0x54020095503501c9007001705d002400380030320f507505807080e106092000d00d0601080716030880c280380040044071070311700d8001c000442d00036502c2e02108a01003401140ba030444140b1446106401021500c0c11a90401c0c10240031140036800019541d5081040741c40140c480000101002c80304881c00c584903a583c0c0b00003868221180c006d0007040c000410300004000f002400b440c000d403000d072014405070341c7e0240c02104480040750304400c80105120303000c0890401e03100179034200e189441c000c080c1e10344481e15021209a201c0e40c1d0020f29030741d40c0d00381d1309000c103034441c01100030079900c0c1440d040d0504000d0000345000f400000980c050b4009518010317580e8400444400c5035121001111040d407162460000c084000441c20100e071b9000c00003485007817101e45844109005103545644213040480c070340000300302c080c13569207290410050500460403413003000101080c038292040d5103180601e4070b281005400f8007900b010300821414020203400b25503420084c00d0141c03408900c0b101e5042c00464a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 672890476 1250 672889226 672889297
    0x815060c0a0312141305120c0304030201031b0c110102010b0a080f06010b0a02061503030904090b100501050306100513030b0129040f0e060127030326040b1510030506120106050303 79
    0x40701400000c6008d14900040054021607000340c030300700549103500d04800320b5144034485020008045208040000324881c60f0b42000c40018400004c40404042c00f0800c600541c0d000640d080e40071583d408204041040428098142c203d00c150400186202c007a50340d5a0240002c0596900c0d041d1703e40c0262001c000741d5903880d400400c140008440e900301400a06820b484010442e0700e0444041825406082140d00075503024140c00181503a8410441c0d040d0410400282640c0c09070000001041320f034402d0324060301d00c890741c2160301d4240380d8140d504440902c40f03144010b0b40502041040c011754103504012901d2140328100241d858000403100084511031041e004240e0003580c04d911a0340704001c034107403446519058201c40c5540b101c50710785074075006a81d00307100d03400000400041e40c2c45440d9030082c08015000f003008140d10f0009141d021581c42c3c6e0710000b603640382007046520f82035a4030208128081c00070030900741006d0100e03880e44030b0140381d5642c071010801140481044510f030200d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 672891726 1250 672890476 672890503
    0xc1003020c060a02030601180303022d0d170a11040603020c0c030a12020d050f0304020d1511090a060c021332070f05030c03070815060c0a0312141305 66
    0x642e18503022103000001c1d0001e40e0f1060004898284c88a0140780308c08054054075003540040054540022502150b640c1c0e41d40440301c3e00c0c80f04140c3c004062410481d10040c05a1900c44048602c005400c40440060050010301e0b501e08081d00540340d503181400b12001d680c214030b0096980c080c4445114a0150f02000158043c41204060030070b2080000d031078424500d155003134910a40b410b02c4101c0c0c20b07007c1e00e14480c000320010001b02c0c0052808103644044e0512411803611400606a01d031021103901c0300ca0030107010300c0014946800d14001c0140e9016003c1c07828000e040c1011078010800308070000300244003082d680c201001e2480c941130304071044000842d00103015043c003c00c6542000701d098030880b000c81c4801400c40d1106014000b40d13031040040000650031691010f004681c80e200141c6414030004601a4440580d12058000c040d0702d08103000920415502c0d1800401c0212402c19842c001c500e01480c101071750740c804e88542e030040d101c19201e22a45545041003070400001d10b2451 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 672892976 1250 672891726 672891733
    0xc14011719060f081f200c07170613030e0604030323040506120c0f040801050907080102030c09040905030d2f070b24060406020705120c030c1003020c 66
    0x11403080c070800011a01200070040a0100607910b0f82540070101c0d5900403094250003050055840110503510001d0050b0841d1000c00c00140030011080300080d804100e0401d4030340040d04518680c2c08120710300080121034403101002c208112019101d10026000c80080608981d110062610a000c840404074005215076511a540c0ca00500054920301b00911010052600065242c1416082da021a6000780900745040c0b00000c2018030117000411040c030f42c05050100d1b140c4056070401800203020084000109401c0000d046450101d00d0362014030207030300400400c808801104203598155409560100b5207203a50b2400c0c90031401818048500d444c500b42c3c0c0e0300071406000343c0711402c0c603045180203072805c4c2400607446654498075030050b0000550300082020100c1e4051003442000b40401c104c000700700c41303c0014080f40c3c4a94050301c0141e0013020140090303c1e28002810845002c5c0d8010001c0b40100c40c04603440b01389512080c0c0c0324080000d001c17902c050103038040b51484c004040c140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 672894226 1250 672892976 672892981
    0x50a0605012c0c0f070302030c01020d0225020609040218060a08180a0b04150f1d010b0604051c05031c150501032309010e0a0f0b130c140117 62
    0x6100760788200d4010940b42c403030511000c2c0003101803450b00400000104501d40307012800010010b910410080702107120400003480840350070b01c09001c40b160001c401580d192060000031300b980c070346410032a106102191300e400040e030312081180c0b0203480a682c05038940d001d181114501500c40b0400b00e401000c001007031014958071131001d0341310b09059400c1e2079504407242000c558a0780700b428018050003c031800700c3d011651030440040c000c45001408204601a4007003041601c3d02d48150a0742115007000029100000b800b501403e81c00075501c542c20b00d032404001840003c0395410a444011030702c0c40d00428850288211108104808281d000440e01c1e80c1481004004040e01c00400c43c0d0841c3d004162980b00c0e02468039072420030583d062451070416001842c00d040580f41d407246659645801858503014040c004046000d060810140e85c0306003420000c0700e10041900c20303030342200c51010700025040c40c140b60954102c0100c140507810000c0050310940080c844621210703207a8002c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 672895476 1250 672894226 672894239
    0x60711010204030f0f12090b070b060a0b0a210e070504020906070b150a0608090615060c0a050102030a06080102040503030307050a1b050303090c0402091c02040f0203012d050f040504050a060501 85
    0x40140109106040e805551010b04008542a0000f07002e640c00c1c421042009e21b01092202211540114000345141012695012201910b078041b141c0e2802044800031100c42c51200c0100307800d50301e0f10005041c0188121083c01646400b05406074601c04ca50100740c034810750b118a82600d028651107902e111560420100d00c1790f20703401c60f14a5510a807040400030400c5489290160b0040041c00014442910350030020180c1074503022000e60007a90a12131008a55030070071416845074010800141c1d03a007014413a41080e62001c3c0c000d0600d507801040100b0541c3c8000003182c0e031010092510648035050450111107801c4c094124002c140301510710311061000201c001c40c01404944203c0b21890880810300c02079000b4284407a50010080d04816104002c0200000ba00c901c000c10008480c10418481c0d0101c4c0c00a0b042012740080b12000d403030244451503030032640861000403d6010500d000005038189030102c0d01d450149031100023082c20000100800f21b2034641c040c900780100e42e16005c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 672896726 1250 672895476 672895493
    0x31e1e120408070812280309081b2b140c071404050612060a02070302190c05010809010218040c0c060609051905100302040b060408070b03011a0a02060711010204030f 73
    0x141311400c0c050626066a1510f1100c03c0394000704111401400a801909681c2c00429984445409058440b4004000034501500a0014424090396030500c0e05014203654904551120800d001002000302041081d030385165000b44d0801d1490250100c040403540300300c960107182041140307485215004603201042110700750302e080d001d641c200015618035040014507413403007000f12107542142d00130030715200d090f40007002818042d00440b40d05295444801c0268006401c069550700201e17001840300e5a801414240c105030458000d50030b1841d01b4111140246000300c0c40703440f41c2d0340c0b44840203000f4024000310341c80b290000020070096664031040c034054441183d0111054500c81c2208205e03030a548140d50107003000d0322102e02203508590a2000030490700c0d120981c081c10a010024081104200c060b001e01552400c1c1c60b10f03549080c655450140804c0c1009406000510540012960029034a5070001e210318141130440201152280288500e07040a00200b00d100200400d208984 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 672897976 1250 672896726 672896729
    0x5070f03150504030906030e0a02120d08070c030f180302130f1518090f05060c0c0c0a0608040b060a170a0c09021c09170c0a02031e1e12040807 63
    0x900050a030040340300c01e8003080701c40489009000c90050328003480340600ca03074088034880900400300e41a5076040c0c3c000550983c403002ea851000c0c0d100060303079400700b54001c1c1d9158000316203040c44040030394a958050140644002080f04010031040072154030424070302c403000110380281040200c1040c0307080f2a8058161000c0c4107250a00f172040180d441c8503089615011280f81c0040050f21340780c0d844011003e000c2d08881510122008820400810f0080c090b03940140b0740004000d43d40c0daa020b140c1c0e810415030002031840b98058401c100001034019140c3d645c060b40c06a0441020340c0e80f440026a1008241c1008800440c2c642c1180c1800c400041c0a604640c0144c03821340d035a66881c109007050f88141800000c00c0409220700c41094001074100c4900c1510640b443e0482440900a0b04081d0704007030310422040d0310031026201542010b000591108004981c550201e4030f1014440c3e540d840081c5807212190502684001d04500c1440200340360310109040560b1959503600090303559440307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 672899226 1250 672897976 672897983
    0x3150e15040b160809030a05090a050a0f06260106030c031d1e0115052b03050414120607050f04030210021f0c080402331c0212040b1305070f03 63
    0x140e803162a0242c0901c03200c81c1700c1c4c10302400842c41d11120000880e82c0f03803c60300d000b0703800c40f00004000c950b59036001c0300c000140c90440f0f2400c9060f4501071000b466821001052103008800c1c0c00100401e601d1015018151501410003184182c6140b074101e000f081511031034203540803d988201c3e542c0001080f0015000240c0900c1c542d14860108503508807492101c050b5408804801c1c10009403d1008104400b50442d501501e00020307601026030380d05017460300440000d4030000b01400380e41c0e06014610710310001600c000807048004080503650705000740c0f0744c2d01401030108200d08694200304c1194062340c1e0181031003c1e48640d14030065500c002c004900340810507554031b54008840988200740445141e0ba0b11210f440d1180c0e000e01080380c1000000b1b940c402004040c2040c09802058030540d05100c280c00207503101109550f001c0c0e4050ba00f00b04413820f44c010070a886400041d03040440c1c000e074002c4030512268540c00c115820440310003030000e00c40c0c060200d0028058480d41b200f0001c4a01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 672900476 1250 672899226 672899251
    0xf0c050f011e030b03030f0c0606151806130f09050f0c0a022d010213090612020102150903120108010b04180b18190f0203070503030403150e15040b 65
    0x4900664045000702c0411071010086403064803068401c0d0000743e080840a400e40340303881c02d102004640e40d4804041180e05a22003000d000c41ca060469154072004468050241408421101c2c0b2150900040038103114070004542c50100d580500c810344001c1484c00002c500055484c0214005414100c80b1051078848d4540010080d4084034212002c503ca00d80c080e000f00c22204000d440391940c0021410710074070b03490b0501b640e074610910040207954030b040c41003643c0901e0400400d09860454001c508003000d495059401071b6000104400103076040c5a61001658a0260740c0f407550203100150860b03510494000140c8140642c00801c020a0a40b0180f024000c4640400d08091910300000c101b03e07066800141d85004002000c004c820780e140545130744504001258510350b45404081d034483e16a003150700114601008a80c0c0209007d0300a542402d1858540202d4019020f501102c03141c0c40d20902110300c4028000d444054101525075a9581024280091107200449907c0e13001070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 672901726 1250 672900476 672900499
    0x209061507080a030b04020301032015090909010209040603080d2702010302090103060503160e180303060118031b140306090c0f01020106051302030709170d05090d0f0c05 75
    0x42501000144402240e80326152032a0380c1e0390061a98071126000041660341c1d60030302c0a030360360380c0015402580213201c1c000d241420140d4407000194107034003042c850600c40e144012860002000e44003262000c80318454150f0391650a540a4807030b4540f000d5005203421000700030007102c0781c0034042048203a9400c00a0103a29007902020401c260380401100c04600040c80040d0b2198006003d820340600d80852215aa82c01007842d0008030440c40c08803044a40c8280002c030589504107501502d10b11303100c41c1c40c0300c12413861622440090011410001c86181c0062070711512811003000f1580003450141c48803010080e1502480c441c05807462007007042e80c1c011041c0c580019164040d80c60040505501506901000b2503501d8841201e03056540f28400000d0790743e1101800c81c0e334550100c81c05681c0b481d0080000b81100d940b5080305000401c5810100304071100011103124414281c102207689003240000100c130100b0144009014140d1003200000304445510039a081720400d031006400709 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 672902976 1250 672901726 672901729
    0x1a130611101a0904020d0605010e011a121f1a130909050c0906150d0e061003080a0807090e090a02090c07030c110a15081b28090b07050604020906 64
    0x3186007824929240c103101440400e9031070400129a00b1520046c51220440c0d07140d03031414240c0d1809d034441e00706a407c020041010102000c2035500044030016403d140c0800c0b042075140172440602101403056a4013034250442c102c9403850701c05000000582000000c0703101c00165a980010200703010090484c0d8000b81d4495140240d401107540400174001d044202c1040c0141150010020366204d100e4001c5a44002141c00040000700d8804030041241d81180d03151520300540540038250581c2d444a0070000f203800340090b2030a051040c60030019540716004203c80e00d8001c1e40010b0703000d150340c10520804d0040081d000303030403a10a461012141d62904140b601c0d90040030005008200384021942c0004d801c1041c0c1d07650481c004000700c0c001c0e074417203100708cca10b045a00391601140440083c03180380300442901d6a110020894010300d082c140b040130080702070035608401c2c0d0680038014250021030041c1d6148000e802c120f145241c8070720190074440e03541d034800e80d000d81c020b412480105949 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 672904226 1250 672902976 672902981
    0xb03190b07030b0418110a15020307030503100f080a030306140616141510050303191133060f1011030702090a02030402010e10091a13061110 62
    0x40982085010190769a28401500a0449002c005504c20765640d10200003200650074564018040d07003045000702100b1007804505807241c0c202c5401800485806030320f00d0713800811241060b030b05103440c50f203e1b10b501c04c008823800000d4119403452030420724041820709001401b00b1203d400380d81c0c180119951110780a41e21410b00c040d031364101408204500024003101c1c1620f421920420001320f42c032844040c0d071410600c40d40c0340d140c01c40e1300c0c0c003052007440f2103500b84001c003801c01200594940449912250010f030b91a440220a110b000d20307503001e40d00411300880030740060305100340c0307000110381084441281604606030149540d59022401508141024014000000e81262042006130030309880d105010025294503100400c0b1100c0141c0711090918020410340001581b2030074144005000000080100d40c090a2680703142c0302d020764003000d100203c98200090f02036010819001210301e22814501d03410500300d9410001c1d60741e6200f204080c6c62001d00007070b2844903c65846c00c3e0103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 672905476 1250 672904226 672904273
    0x804020f010f170109091a100e06130f0e0709050f0720010c0509090106080f15010c050307150c21020f070515190204210212030d0b03 59
    0x108038a10801000203540106805048001c0c5801c010f50100c4081c8658941c0250980100130740a803103044070410803411030401003041d8a41d0358041068504030081c0d246e066100d224201070010700d0400b180003611040102c12020b030381c001d4140503850340c50002e80c2c0a010340d91030f000c0992049590004940c08035100b0726016650350b0f00c5104150303c4600e0100e4649075034500c091510f0003028545103251009105548130141d03a62100b6446004a004011020405900003018042040100138000c0b45009800d0313401700c039059240341c2c3c19000c2801207640064184008100303100001b00203045c0700c42542031701301d032030041032090001d440d42c28400c4130f01d0700c040c0c0079044241740481d142000600301034000d0080a60000780d41801c01015445861070030807030b81c030ba9090b401040c0040c0301e64444401000028560003080339442d040c60601540c0c80c0c004400d4682801c086c510080808541d00c8030513076032800e003400f8209d07902c410b001001c4000400c0b0303020318140300c1d2140c44858401075024403d19013 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 672906726 1250 672905476 672905479
    0xa021f210f2c030f0304060905010219080708010f121209090617100908030a050901090c060f200a17040f0b0430140a051e010b040e0604030c08092e080402 68
    0x5043d600c0c2c45d030747c0d44003401d4034190032101e554003400b0302d0350021403c1003841124102a030744c0c1003a5060001010f054120f068001820503401c1003c00d0003165079074150480607036446190b440300c0e01031000382101c1c0410360340c001c050024100b813000500041450100c3c012b84402c5010f84200e103600342d04101c12294440e50003003802ca01440042d1a042640c0d115a41c0510b5030000412039002543e194821030390140c1200012a202c820400d01e01640211204101031950f507640300801900c200aa40c1c45500a2005001d40c0d48000301058503605502a80c0007401c00094140742e9a88503480f401c0f080d002802040140c107205140150b028281840003214040c81c50900c2c8403160290321002c0c840b800c002c031114458441d4109500c0055070810540d20341c00315500d00e8400c410b0a9010450941d0000001c84c4d10036418180070b802e2014001c5080e0f50003d60504140a02c0c84647c50413441c3c1e03000d213089480d4403010140d9007200310b00d9031245054107103a4020385110040304c40704054403061410f03100613 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 672907976 1250 672906726 672906757
    0x201020a0f06060e0f091011030604021b030d0e0f030405150901030b0d29060907111207030509011b12030e1005090a021f210f2c03 58
    0x103004181d001c0400d84500b8001c000c042205a107034200c1c90880082500e202c050941c4540800c142690240040d0180d040c10303503070600100104a1040c0d89a010103420f5900c581e60004151582004043c0078100032107004040c5e036150707800500040f00410499514100758025aa603900d40441c020003113030706a62004240e1303103450103a010041901c1d00f00d04000e505040d0b894101030700507507036401c40e156000e00c00c0854071000d103070803165404035a0140400d0480c000b013074010302501d680c0c0c241e0055407201c003500d0446445001c03410b100346400c081c0d0240501c81c8000140714002c0c1540311000b450609000e80310080300c0e00007060303045500c8000741c10143c02e101c032407903506400c0f604c40d4108442c01c2d403500f4100c803008803025102b901105d0003603680d041c0303580c00349800000f1801c06009448844580b0a030a500549800230050605000c119001c0b2400003101c10b90749079280310354040724014500900070803b4141038080c524001216404050585418032900800038070004111350700030300008801c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 672909226 1250 672907976 672907993
    0x1a030d0f0c0305071509210302070803160311030f040b070e030c04090303110c010203090c01030e1507122306030d050a050f0d020c0604060f09020109030201110721140109020102 78
    0xc50f0160401c001c11144807008140481c5040c2e0355004031404c035401440c1072151001c0300c0076401300c09400c49081205250040c0b00030f40c082402401607a5000580c0f00700c9100d4541c0202c0c2c124010103071051010398104e40401400424080d0054892007240f04055400b540e0b05c03003202c00e64681420300b1480b541684a00b0070400141025003114411038400c0c24041b03514080c075540000580c01111802031503079404000c10a982004000c100950402820308200d011007030402141c58039840c640c4240c203180002d010401c02c40c452052a00e0710460b8032020089094038008141052482c4980501c1c008004404030f071041c84c000c15008581002a210145000311070706082c1c555411000100840d100d0a101260942902e40000c115021100000e0901d45c60035242c0201103d000e13044512a10b0700c1d007240f480050740c00060304010b59030242041005100e0b0f4110310343c82c06206e81c10100c800d000c605080c400140312403121449291140011100d00800d0b004194200c484060010380141d211689 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 672910476 1250 672909226 672909233
    0xd05090714010518060c100506330712030b031501150f090305010606020606190305071802090a090501061b08040b030612010204030302070608060d0f030e0d061a030d0f0c 75
    0xd00003800c00800e040002e0b02d4410001c5c1c101c1c0c100200032091600107071400c062003586d03841f4aa030301c22002ca0f04060080784504900c80c0160014201c1e0508021280891021000d1003080d2080564414800f00d0b5624440c2c0c0c00034050014200714500078412901c1c001c09000b89540d00c141654207640c40e03454000d001c03c80c00c036003084ca1204040184601c01d200407020400a02400d40902401d4004001505046061009003400f00303118127a45100c2035011300010340082400022150740b142031901c04500d40194100900c910252a5032045001130001030f988ca00d600514100d40301500e415054203181004848004030012004200000401c410f0180200204c003868203ea0044d2a2140906a54814908907445030300268096441b9140400007503034000400ca44c41401981c05014400051b500c0d400501011040101481004141042e640d1550144224001d80000c000e006961038001e000c00d5155100c0300d0301c0c0c00781c040e03601c0302c0301c91a02400f43d070365040d0b80039a43c3d000280080d88 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 672911726 1250 672910476 672910487
    0x6090b01060f0f03230903180607030e0927010906050106020a080405040c020304050d0602040f0b040e310c18050403080112030c060c2c030d030e070b040303050d0509071401 76
    0x5c050000d200d040d02c1011494400d6460305206400c400700556071110f50a04920046a40340c40251107032a00304512400250710a100148050702942c074034019403502c0c0a070b500c4030b030808501a0348000ea02c00c90802c98a905420071aa101d01503003040202e66202d80f8100e856101055002c1c14a01c0104000c1000382016070113100f20360803600c1500e05294441000030b0b9403554112082da4003540114080c4280000b12400c02d00411900808038602890320445246000340280b490807100d030b000f41940e00003245c0c0d801d8002141c03100140118400d0f081d2510a40a002074021004910000522031003091298401c00740100e0309510391004d81c0e880c08242c0d000c00c40501400301c0420144c0e0b4180b000082c0c00d8000e22a00819944400464120b01c2d8025074130034441c440e4030b4000440d500240c00607901c001ca82c0403901c091500e00800c60207a8540e10615110265003ea00400c900040c00010702d68450007070f140182c403c0342c09100603282c40c08143e1f035854241c0680d12007690b0b48003148110f58001c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 672912976 1250 672911726 672911741
    0x1104050d080c0a080d11030601080a0b03071703040e0c090d0f05010b0402071113090c0b090a08030d0203010f0e25110105040c0602010e0f0307032a06090b01060f0f03 73
    0x10041da07071610315a9200d09042c40f00420741168201c9010030380304811001c0c0d000d01010462659104d50540c50801d000030701851010f4130340980c4a43c2e800881a10340c4007400003001030203164000102074001c1454042c8d4903880351044100380412000855060006e4608507641c0d140000d05100d01c800064a400c0010030f29200c0c221940d41d62014210420b484034006484410f000e1034440c0344c0340b0310941c1400003001c00c1c81104841c0c81c0c504044a8000b070880c4042c1d0041e60104900c40340c45a40c19804600c21800c280c011842522000c1400c441c440016001181030744c1000600c507100a5a520100c1c052000a444c0104c00c0e9079a203e140c403844d204e1600d03000002810345040030207054840380807421524241d606903440105404140807542d024000e8020840ca004014824611100c041e2038417802408801002c0140c0c2c170091180d21604905040b5040e000f00800c02e0030001c403860b02c00010f040c8400100c800050000001560070700030211490300d801213843c0c14040c240140c000324002d0122 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 672914226 1250 672912976 672912983
    0x60106050d06051e040b032b08090303040528140115051012150b1204030e0a0303090b070f14030d1a09340e04060906121b120f030807031104050d 64
    0xc03c01c03a00e00d02980c038600024000e5238292040c00d03110002000a1107804000d001c030510350301c20014040011000107805421007152004641540d01e142d40c490000903000f80c000d030000a80c4007102d05401030650126841e45180210b403041641d42e60203004203086481002da010510301c8102d40c0c5a070200e038001941180a0162108001c3c0d2181c48040050b04070b21641e40001034100108800c05070800d0300107120309422603403a62510729582c6c0081002c1c0d40390203170354031100300401c4990030007545540b0b003195580c0c800f5180b05529030100d00c040d6039410400301c00101a040c0300e02c540a040d54000e410011040c09000c1e250150785c0c43c1580c200e129038109810302042c40e0040d0300e800c04401c0c1c40c0300200d50152583c0b54101541c1240801c0255625a001100068902442040801c464200750080181d00144a0503203410340154400e0502070750b171141d219407494640d520100b009201c4d022118601c01d40740c0440e15200d28108500715060707180c961140e09001c100500003890000b40a0a41520 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 672915476 1250 672914226 672914233
    0x22210c05031c1e091a01121725110a03030f110c06130905100e040b0403050c1605040c0809070909140712050706020f0c04050a0e060106050d06051e040b03 68
    0x103800039100d00c2d103681100d00300f0395030744d440b107403001000010341c184044460048402c0c0400d5043c0007641658030b12440307004110080d00b00841156103000410f965510350b0121104025014010840359030009951b411078020310a202a50002e00d001948581500d0305a03566075081e503180181909c42c1d05900daa40d0600d0711904d1049001c5940b000010010240320314030782e000d2145800d11540950b02d025280c460084541401444524588590150b01c81e030070003030911168549081c2a9918403c1d500710707400c0b0307000710302c1e619840c0d600e001e0041c000c1300c105413410000d191406000f2604010140d035815125007054800b0441004590000ca14003405030300707052145503460701e51034a45840c1e81d006120084690203150280324050028500405071400684105000c40c010301e40c131107001c0d0302c0c01407040d41c8c2c03040070800410349a03005002d2403888508841c030558507610003612680150000001507424200c0101e4181030011505030b85003000515140c41020b0401080082d0092204031741d054403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 672916726 1250 672915476 672915491
    0x80a0314070b04060e032a0c0109080604020904030507050106092c0d0e01050d02031609080f06010b0d0b04050f0f13170d18030e0a0b0a1722210c05031c 67
    0x202c401800381c1135004c0f10500550200d4200c00c25800c1c8009848c58905101c480041081401400310b411036019604170b51009880e5035500d429191400345000182540d0b02e030140c0071510301c0c442e60100e04010700104100d0a580f81984400700403090210611b103a0741c10070010070005a010b8581c0f01c42075901410800d080440e0382c68240126082122940315400001a0034070741d158021150001800425028005000c2103440d09503a90760188200f9484680001c4d009140e08002d50000b0301c44440240305105a007000002d6904010081c5d682d800d585040101155244c00e494001e40409035101071240025143c507070011249800851f064504251140130840b041d4021810180c80d20b4442c1e118002800d07451828000310040b550025400198100075070111690440121081c1d519003280105981e540d0418030940d88140241c020844008052540100b115509400c42880207808149520043e260011101994020005822074004000070034a003420a9a58502060b99038004142c44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 672917976 1250 672916726 672916747
    0xd110c060a0e0a060c0317070201020f12150a1409090a0501180507151b110301020f07110901060c031d03100606020d0e060406050c0106030c080a0314070b04060e03 72
    0x1580411001000182c500005001901e00030801c2400f80800d4900340d03d00e1002550041c1c00c1100d01400e11080c0283d40e0b000520b114404d404440c10800000922a00d42900301c1c4400582c040c140d0302003149441010f80d400c10f0781000040e030400c444981041c005514008424032100042c0680344c01c403140691580200490000d010f0f0014602e040b40d003d059602403410f10a040c0f82554004e00030a807415811845540da0141072102041e040310b0300c10f04c0c010f281c0d2400e92541c01168810603015400492501d441309100d070042d00245000358100c1141220a40c100851440309001d0140414260043e0700b0100f40301e505c0c14180e8942001c0400100c0201000291500b564508000d80f495119101030003625414000001c0c00156400c0070782c00b4507422000181c9902403401104100000480d031180a2002500308800a5400c0b5072000021515207400b15203a550300c00042d00480d00c41071468444c6844030041303480c683d40203401302116840310394503100903102940c00000c1900c002d00c00403459 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 672919226 1250 672917976 672917989
    0x60d0611030903070b070320030a020c010f0b0a05010c05030a140c01050a0516020a0f03030c091e03030201061a0405040b01050723011505130c0302130602060402031203090d110c 78
    0x1c2c042980045440701624078106403e000010800030030141040c40100c90961003c83c099010203c008215032269140000d600003801040c0750504550f0a0580d0202c141d000f90f40803c5010314182e414101c1d5685440041d29210750b6454020070544c4104418a6242d2040c80040e480451540030603242182145510707080d58000e8546200f9a5950000c0c800e01d2400c1d42c420b018000841c1c006044500703d2500d4845008114160141c00c0c5034880c0c460280d5944241099009400007042c1000d0841441e400802104c40c01c2c0000c4000d9881e0010120300141c6403c416410b1440c0c5452041c40c19003002c1c1880098400348841a05001090180f0800181808040304014101910b03020002348554a803500b0359091000750b064844009400340655281e568078124201000740d000315050104400480c003d110b840b21204142805010114145901241c42401349000b14101c40981070211035075a0740703100965041106500c035035042c5240768054030348030040c06071800c1650016800000480e03003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 672920476 1250 672919226 672919231
    0xf100e04080315150712020f070b030402030f060907090b060d0504060e15070f2d021005100f0519030204050109020a080112031b110307091a030c0108060d061103 71
    0x31100c4010003003001d0b1007118903480f000caa00c225402c0396242ca2407910040c8611891202510550403000328a0303405000b00541858a61001c00b2030b0754095484103042c99503001034a01701c0c483c0c016940c2c0c2054141000540a0080c038040c002303408480e280002800c001c0901d07040d01900b0100910003070100c205203104c2c4ca44168040c91020610748001c1d2242e909103038403100002c3c5814042000d0069403507000c004c1b208441e08a09140d007130307081c802c2c40c91194403003540c07142c2ea010b80d50b20101c43ca6480c0d010901140e038110401041c05652111a140c41403503a546c019001e204040e404104120b00d0200d41510200d043e25100d610703c1c030780300c0c1c003c5010b8610980140d190f103600010442c0c0e4080d0721030501801000d00c05040e124031145030750000d00c0004d00c50030a100740c21181841c0410b01603003141d40b01c15058010102c8004c140c0e16602e45014000140040044c58207030558141c9a080104036450041e02c1655180713119a920030400a04441c0b505060f1a072075528813820000e480c100c4001c60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 672921726 1250 672920476 672920483
    0xa02120a0305070e01030903200a0204020a031d0d050702012001060807080f06060f061e1204110d0b0a020a020a0c030507050a32062a0c0a030b0f100e04 67
    0x180394582032902500d2080c0130600d09041601d04240707200400d500c8400d036040d05c0d8001d0040c407007240303545d0b6070185002c0360b03258040c1d801480003031620f4001e50942e22004106001c0b80880c000894010112503d03a08403002282c0851070400007000158814800f07440031542c0811840c14444046060600310740250700042e4881d80000b009100942081021581c1d084055004007031500d00705004c90b01100c800b545603400343c20081101d4800d00a100c841d110814410f4181c0c940300c1100740c00100004009440648070303404942042c1c100c5051006480e030301c1c681c10080c1d021990700d0740d40e4268000c1d80100c540c48118000e1245010000c0c4902101e840290702810040c41624201b2040040c00115540b001c419040207492030b42484081c00814038003000c80540240c94803d040000c50040e100f0003035425484c0314014105404184c4001c180d017a040da282d81240c511011510034402c194180c0c0c04044c00340e180c1c00d0002a00000a02803242d880340c510803200549981c1d404010040220907107084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 672922976 1250 672921726 672921731
    0x2131a0301060807050f2403070c0c09091e03020f0f150f061f020115170105070e01022e0c08090105070302120c073216080d050a02120a03 61
    0x21116440c0c2401200054100d6001801100c0c3c83d220010f400c10100102c0700707001d48910310700085208007000d000302e0200034001540d6904d04d04140000c00e445003405048034410256400420b0300d05031403141030180c0342e00069620550124840721035a103400350030120118481c240c42821800414444900e4507030080703000740302803190804103600600006010f1026002424200903143c0d90354600700d00020090f03880f02203c4041c03102c5c101e0241151040b2010312218500002450281000100030300c2c1034030900803c00c40e25125812100207060b01003030360050740130a0713503101c0c40c030040038005108035212120183c6601140800500341e8405d000c0070300210301050b04010481d0001e00880782d01400c246011864142d001225903a2030801410b050305104011941c2030030040c41000c204080f1a0f2071048180e40d042c1c0b441d01c42181c4810310320010b000e01030300130f0341e20109903c5e038648410b64074000081c140601d0341140171282c036001080120114458254908903900b06076000308940015079030003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 672924226 1250 672922976 672923021
    0x9060603020913090308062e1d04140610031e06080d0c12050a050c0a0c08010f0204030210080415090b060909150c0307020a1406060a050901030b040b040213 69
    0xb080083c900070060b42d01101c1c20480500006540004c40725800b440480780c0c0201100313151900c5c4840300381c480c0c4080d442c244c00250038080ca908040d1048480052241258070800000180000d40d031401009038107862442c4042078052a24002c0c614841c195442c00140405031420010810601c04507110007503580c030030b41448001806c0c0025a00801c160a01c0e040c1c051150380c40c00ca01e805a04800401c0110203d2411850b03840307501140d10b5403400704111090140d26003001062908644546505c540c43c0c181b100185260b43d00a8034210b81c0c00074401840340746010419915441d00601c1100c00002c101c04060b110300c07207841540b0b0164000e060900480c6000c0d000c1c0702c034000d8080c00c02031840c0e0012900582c40c0c1030620b034050313100e100000b100c0d071280c8a10400703030316061100e403004104017072083e40d0014044000502ca40325940c02c0f217100c070176a079480c3c2c01e0091119080c08003800c109044000036000c24080d603511500544040c001e6a0190354442414080324413425200c010409060803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 672925476 1250 672924226 672924229
    0x4060204170d080408130e092a01090b03060109050915040b060c0a060b0102160303080a062709080d11090405150a060e130606050c0706030204031a0907090606030209 73
    0x10088070808050000c00040041060240804100520017458510300040440e13102c4100340a01c0004c003842c00c41003086007400f0815a440ea6200d101140c4400301c00889014171407500030110001000607101c1c41c00785803c2c4400030f511940000c0c08541441644034002546803aa03104c024440c00c1f80c0c480301d8004045620402c01a20a80901c09124000601170004903c1e00411004c030001e0380a18001400d984401c0140c1c00c3c001002d0141c011525000c000005143e0084d5400d40b082c1c92050041024a460315002c0304035280e48148130f071060300c458501090318071a80e4007010020380500c07092420010344070b8161007698200500d6514101c0f01044152765400d29008180d04032440c524221251070158010800381001e40c401c0408000200b002c200c12510340d284804074804103901c05010160b11040068034551154405118070f1258003c0011070170322a00c20384003500e520a8805442920700760301e0aa092a014000c041a405406030001e81c1700c40d140304100080009880242c2c69905420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 672926726 1250 672925476 672925499
    0x50f03161103070e01120f0b10060207050612010e070509040c090905060d0506060f180f01032603011802090a0e0a1107050c01080702100507020a022d060f0705030304060204 76
    0x210301c1030203a4400d030307020710515010850580c150780428600100d001060b003400083c6070301b42c02c1e014001d00060800e006030030f0300d101191801d4070303265000c9882d60360341c90086c4112807268040005050050700e0062024082c07149400303410216030b1901e03038240040f80300000c1c120360304400850041400c0c040b0800401000c0e014290380704004591180d5102002d84400c2d0701c590008240b01c0c071460900d800b05809560750701c605a201540042405090300c1d000d400200906e40170300003a43e1600040d0304640e4410b6004050b054441b941401e40c90860f484e040c07e00106060b11040005071640074405500552074003030403000104420b21070352803035003032031203140d801c80ea00d00c9440c6a10400400220011a0300010071084040081c41c0420040c2e44e08427040f8205921216940c41c2da0382401e050000559001684240c0f50703000315803000c000c04401c0140800c51000500720700384408903500b02105468540c01800c00c4102c032030500d51031700800c1c1d9a21410740d032040718115484e0b80e005c44e041c001800304c903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 672927976 1250 672926726 672926753
    0x60903060e16030b0c04090609020d050912070308100b0309010c0e040c1d0a030f060c02060609160807090f0602061506070807150f0606171b0403030c050f0316 70
    0xb82c9000a0844411001e00d80680000751060301441d021888461050b002c8400419035618200005ca445116000107035000d6080d0449007400c040108106803004112001c001b01d0780703942c45103011040c0c1c1c0c040e00e000c10002e000d80c000650030480003500d00005070042d44141e81c00800010390000302c072806001c8480c1451010700603886d0035001643d0030740004110241c000c0e520511680c1e06125000038504038502d402c0285903221036520b2104000d91078000303449844141d000c1c0c40d1560b40d20700602c4280d003011900c4001200d0f4660024002c0f60003400f80c16000043c41ca060011961140d0b170280308005568426801a48001c080010341c41100800c0980040c045945d80c1c5000d0203500ca45402d0300400b50080c1141c988038034003641c42c1c031160f031000104120051050240076a0390388080d1003d0050744242d172400210000242050161400c40004140325280c0181020b0a54600300c82c1a080c5030390441c2e0511a407154002c07501c800308090045a50070541001c7d5059441c6003000104c0285c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 672929226 1250 672927976 672928001
    0x100c051204080d030e0703080703050706050c0f03012108160c08160b0c0109050723040b010f030e0102120411280b0702060909010e01090e060c070305070c0f06090306 73
    0x9110a02c0102d41c0441c0b0300500c68004e140200d61141c2202c5214207183d901c2c1d00040c40d440d0001003070020580c00c0303c06820f159000300d40421140e5240f054084030352243c2c0150031480101040140302000f5201a4401014100400d00000a6660740d0b20185940464088460b0700d102a0740c002c2000f803020035180180c141c14000c0d09d42069040b80c005d407200050f00a10466583c00706941c030040c04254440a241c54001048804455840e41a50300c00d0a01e01d02c0da61404408440700402801c082c01560400d40042e9a06c20600041c0c5408030000c10785846121410354080050707141700c001d440c0b142406107009203040240740b402c04040001c6081400000c604403825410221209200e580007507007100c00740d60601765150014400655a44200101c0550040307003c00003143d00d041d48a0028107079603854104003d4030fa0f81c841441d5850384111407406260000700031335000a071241002d46092072150440b2001030b516251a031044000c5074002d500080c48140307041080c801d5601070301100c20700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 672930476 1250 672929226 672929263
    0xd02010212010e1911030f240402090103060e010e060f090106020c010810030b10031203060b090f0a03080304120f080105091305100606170702030a0504090506030a02100c05 76
    0x4a1001070600310014031620350040b030340380d000078001280601c0300003152114113030030002200f000004082036041a20501c001100090000d030100320005a03007500c10070030042c09006100c4003010080650b02c00c036101410182c4410000075003104908009020348130405001c102460050b040c00400f0110740940342c42412a0001048203580109919042500a20b8a07180c156100300848a182c5000d034802042486600f00708021824640812030035280314044d00d51414082c0c40044081d2002801004a0300b00b04000e80c600500e0701c160707429200c3c1005414403144554a88913044160403c84095840d00700311205c0303501c0507034400c03180ea01003070071401c1c01c061550400f0007180d000800203040783c80c0c0e010742210392000c0c090200440135503016442400d004403500c8050050101072500010456010f1b40e4021403d40c80c008815142d030850a0303034070141018a4a02c4490252401801c00c039010701400350350f9405600c503208014100c11a9032540c45070241c161034a14900700001d11b80320700490 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 672931726 1250 672930476 672930487
    0x30221040b251b140c0f0406150c020a0f150806040c210912050703020601090c080601050f040317040302030d08010e060420070302061f030201020c0d2a080d020102 72
    0x1640c0c5050640162180c603011009001c510f06032443d581c8052406440c0e2009030030303070780e0340000000780e169011002941c07011721401e0008207100c2503a88a010b000c2c80340d03110180000c51644208001c604c03090009140308081c0703503a5024242005600e4000ca45411750004070030a0a13a080508950840c03000d5404200c448030b8940000c01c000c0030041da003441c4154800d0b08102185490b00300c0d0707000d40c0c1c020920b20401242102b0140030b5511156048025010303050001030440544d10483d0310038042900d500c4601d645090046555500040c82d200d43c1081c02d00000c008900c0318914150100000c02c01c480d6120b00b0350041600d41f040c0313107400000b0131960302c0c01800306070360014070b02e82c100d03000f82c50102e1030303100b01d040310405901500c11b0409101c1c80401c0000901d41d00050301401140e072202d29500070140342c3d01c0300001c100640000f90160748032510850450400700c0364070250601031a01410b05c041c4615001891820f40107401c4000e00707603144240003001d01403180951424443c0000c52a15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 672932976 1250 672931726 672931771
    0x9180613081606021207110c030304030f020906060708191d011d0307030f060f0c0c05070b030c040902070309030c0503030a0c020d03020309120a030e01111507030221040b 75
    0x18410b510950048224403841c0c00200708082e010748032422101c2e19030300702c5441c082500401c034100d01da02180d140d2144800c0d04019080c080101c0341501c2c0c001100e90098803447e0284a4420406041a60407075000c001c1140400c01000103415007402c0360f190000d00b1841d4201c0200405454102d0164144040004501d20380e0020308442001044100c3e4030340307100110001900704400303644050050f02c138240d0900b041013200d9201c0d002ca400508001c1200d5a11047e0031909182000c1c4010401d50007028140401c0d181c00c00990342c41700041c98240c1c0b4203504c1e00c8941040c0e030042c03003088000c1240d170344091040103c6656454040d0005400550424a42000c010300c4141c04a0002c4e001e0030050b620030050501c01d000715500440b024140c3c41c400c044206820355101e00b1080d00b540024200003010040390b100d00308140d0764030b6480000b010016030502224440e460090072050074194200b100d203079403031411444c101e10001d03070040130302c0340d460306007001c400210000b8940c0038555425040c030700c1d02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 672934226 1250 672932976 672932993
    0x320072109050a03170705060a090515161d130f060906150804050705040e06160302130b1c050403081905160305090c19032607080d0906020d050118050f0711070509180613 75
    0x803680c4600d0030305502201000043e030002240a83d417a001081193f500b01040020b82040f81540030b404c0003040300d1903581c0c1c0b0f8501291624094001102c40014040d1000da2082000640190080059a0000ba92000080c007112480c1e1045141034014108012075400d954400004a6103281025468aa010304078620403d8003401038510400022031082141403040303400450603001c1c52010041c60402c1d06019101080846070485404c200345840e100c100c05600880f4003800a07a18101441400c08806030003504004001807014403400040a50396030342c0c00c04481100081c002d2242815003541001907a9000010040001c0c08403000a42181c850b110100e80172950800c208035164504140c40401600540c940541b8060000c1001c40300154103078000c034101c130411078039170b540c0482c400c1003171066403821108500d4003400740d00004c5420303003d054580b00110121054410090300c8000003903541c0c5042d01c2064036401c0c0d8008131300d00384404020681d00840f080d03170f402c004c41d40907585440d130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 672935476 1250 672934226 672934261
    0x50705060a020f0d05071b1211130606030203150d0b0402061c0614040506031f050a0f05090c01030b1507030320072109050a03170705060a090515 64
    0x94040018085035103031003070250980f01010718040c0c951001404400030b0003504004406c3d100703a50a00d00440f41d048610421f541121250111400154490340380c2c15500c613808503480384c00c8052950b50100e500c2203440f4078005031040d81c9005031a03080144480340103400b01e10320a405461a0548000890074018956038855412655140d4505942c00045007464903450000c280c071f810300c0c0c00401c11941c00381c41d0345403003075080d40d04111541c4c4140815aa459040380322104000051142c4041040725070803e03644042020360105251203000020022a80101c0b290075503900000c400d06040d40c4d15024166034118201c9032200280c8607506125014881d030b130001028181c0e15450000d500e5118070700711060b5440c070504c407a00c074900d41c1400761100305040e400c039400400003000303611401c0c00b80f540c01041e9280a04070503885811550b40700040c212028040c1200340701400140009103040103090b01c10000c20030040350410240c40c102c0d15015404001c06d036801040b804000b04200c42c1d4a0b0401d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 672936726 1250 672935476 672935479
    0xa240605060414120f0d120b0f040c020106050d060501090b0102010b03030a03020310030f0f0c050a060f2307050d0e100c0201081005091501020f010603021818060f070f0c050705 78
    0xf01000d0030080013411500c031401c241d4040c5e0140001c0341c0c9034001c02084d170f071030785110589404020300711501054080340d40c1d840b812680003181ca00103101905060f406502201c91900000942d036803208000344289280c04030489505484200500500f00a0b0044880556007030000340700c042122070000e522809054610800c056021000543c98215980c03d01c004640000c4d6178815016941050400c540c5140b105882a110990300050030303013062a401c10845842c0e5488802042c0c00110403908001490324000c9007280d141c0c5184000600320000b005c403180f113440102000402c3c80303409442c0400c0d2a0f0b94904c0b4007130795400012079a8204031140a00c9909103050180f980d40c0801d02c400a562a8002e0b54001c03d11104024001b03458440401c45041c0980131501d04500340300881e1309940c05400000d400c0b03d4480d0740c81944a0707031000c0f45900b102740e0710604d0780f80c540c609000740d190407812035031340407102888414401c031940c0010802454030941d20707101000101507204d490f5110024400d10303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 672937976 1250 672936726 672936749
    0xf1c06061b0c090609050f061002071a120108070e07030504030801181d0f12041d07050f0705030415080907210b040c0501140408101107050a2406050604 67
    0x42000002c40e81c12010b040c004a0800a20b5190906800100300c1103038560001035001000c40d050f03113003442c521017a440842d8002c20f185400c0c400303808000340c00c0c0341c08100780c0701d418400d080c040318985c51958003914224004250980c83c1c614900d25952010385590141403405090001007a8040707812070550b90341307254080b003c01403407060b030004202e820307071012451418000342000684c010490703201007100c0070120364100003419100c084074845d80c49022001503031018072071070b44c81e090044603030b11503d07a04086062140707208041d101940681c0c0100c1d0503400003d070a01c096068420541401d01d200c2c40c0c60525490580da100d0340e6096140102e80341c1041c8816104500303d05608804403e40e400000600e15060034607204412000358000c41d4003023103003440d1201030701c4522030a8404a50449008001200d000700c402c60080410240314070441d2410480070f0040b8204002d684080c9210305420030a020080001ea00d41c072807050845443c80d4102101088203640b254142c5056514400a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 672939226 1250 672937976 672938027
    0x40b0714041401230a03050615180d02030c310c050d090503090402040306020d0b042309030412140c01210506040615020307050615151e0f1c0606 64
    0x2e0a00203488045080c40d103020000d100b01c100d40d8590007d900484041d500d002850110b18020740e482d001d2080800201031946400c0340c2a0701d00300c054001103a00141c103486584810202040344d1400c1d1140c40c081313400c050000c16070400407008540c08411800c003010484402403010040551146104003083c1548881c3c040c01440300074801c50f600048020700865a8507903e140990294109a0540040502d0103e80b1051810035010300300404d0302580d4581648060140c2c0300c0d000d40c0c000b401c0c1800c944000e00000c550103115804d203800d6107000307004042c0c580e400d903201e041c60030030541c422034100320b40f411a6640000603000920780001034100e02083c0c0381d4464022400070f150356400800c49001001010a08940220041240707900840c01c5c0c42c0b1607528901e404800da140440010341080c11140b4030700c0300c100d00700050301c4001c0211017494a1550035001282c1da5400c40044944a0800001d000e01c4680c0c2070013502407045110001442014503158018004d00c1d0542031800034245035021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 672940476 1250 672939226 672939257
    0xa0308060d110418060b0603070816210e0c0a03020a141f090f0e0603030f07020d050109030306080d02120406050a140c060417090306150a050405040b0714041401 71
    0x1a004290710250040104001302e03881c040c10625003030b9041d200545013081c481d07854200002128404c2019032107046440c1c40c0c0310644000c9101210018082000c030102114124805180c45d02004c3d03044900030601d0049101140e0516401402540c412010402c00b0030040c4c0311026500100c800c1000344c50403032100440030644401e03242040e420b01200d885901d0740c00076040080f0000780e0b006185180251340c0c9404414660080c1540c4843c2d16070f0090022006510510004010951000d0000c8146030215a21582034488003174003100801e494240500c005042008031400d036080c284020103000c040f000303500d1524451402400100b090014400e00c005000e82000c1c940c0006000e141c40e0381c0c81c060000342d80c41380c2058508031000c8544010a401c800c1d144000d41d4072040005003d840c1689554864400403040e1541458203d101d04034009460383d20ba1080b1440796000fa03804484a142a51004000550070980010711700803e1009009481c400740d260f01415030b080c201540110b15406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 672941726 1250 672940476 672940493
    0xc040507020f0f0d0f11120703031d0a121805040c0905030303010807150e030607121b110d080421050721020106090b0105250507032001020a0308060d 66
    0x10031012544950703a40c0003c020300010b0801c02c900840d644080b45140380400072558003441629482c100d50005a1801c0307009031000c01041142d1003410b001030240b045501c030740e0f8042072401d04152550014410340081c442c0308265591a100c02d858242030310f012090388a000388145008031402140d403425151303041402502414040c00009044a890350307542c0c8612540e070b1005020b1200003c0c1e00c40d541d90903450041d0065010f945009000e4211951107203403c807001c0205140015000d900d841c03803203804030b009a0405028450650340c90701a40f0501c841c062138401c4213009035007000070501c10400070a40f51084852506071040180f08030a400d00b4040300d560080c24000f802442000c89080b00e8009410350b0a9030202040d0000d00c50156581070020450f0346200c0c1d038074046401001000c00403801c28401d9085c02484040e140e812181e16151246821680d4004441ca098801c00c929107a0080101841c0e80150074801009110125a00103002c054040c03c03c9004180c445038460070415600d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 672942976 1250 672941726 672941743
    0x114281703041a041509060f030e1c0504030b060f09010308031b03010627031e060f0c091d16030902032418070e01051c0c0e0610020c01020c04050702 66
    0x751844000080f411032448881e4404e228080041c5804844104254000e115150844400e038a4a0000c442c1ca543c0681c050152a2845c4011b03014460560603140e03100054000d5010301c5a80d110f880314194038040340707103550141c0003d215884080c4010a82d0f40e4459245055903441800d82d5140d444140440e89113034203204103940003043c00704c00811502e5020014075040e80070b18514035151650325031980c000300d0150201500641022403c2601d4213049000050135510411001910030603410320401105c5140c080d00b800034624420400103507d8134480c1c6607040041106064290500c034880b0902492258424401c1c1925250180705656041c020b800f0b188414204842c00700060903541c48480e5000c480e2808080c80007200080c000c0380002d80081990300c032a00d450704a03400c150400080c8604824488203012074289800e000032401d480c8400205410781403003049090800801c00b50300300c1001030b070046610040208807187c0e40003445c01c01620084d14001070305e4503000c07012070400b03500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 672944226 1250 672942976 672942989
    0x30919080d0504052b0e01180b1908180601050f04060302030d0903030807030212061201021b010606030c0e0f0d0510060b07060c02150103060f0212011428170304 71
    0x148002c0000344000130030303e900c5c5604407078000b80381144e54000703024100d844100c0085c00038940d5801c1d80c4255020341c401c042403240750542d907140305943c2d4081840903030140c031924030241003100211201e142c00800060304400d500e2900c61040c04584100c035030390702051007400e220f0840c000502215850320f40c80080559000f406580c0410050300011304141c10a10045000038480000a02c8540c82403090324000d035040c03000707036000b9140c42e0100300040f42041c60b074900315582040390b541510310303900d62900070b00340040002c11081c0c58000c014044400044000c02401004e0141d14560390744c2c054881c600c4401283c0d014180b42036802c00c0e0780f40c1904c1c0302c61402c5451408001040140d60400940002e0748030395002e111460180f00300300c1e101c901001c012030124000d42c0043c00010b03450b8104507091400c4440043c01c1444013446045512400c0e0f00800d403403c1c21800c0d0003c5804e103200407c40400001020400103d9002e44032505032910b84540c4a01c0c5810b011030f14000001401260002c090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 672945476 1250 672944226 672944231
    0x1005060f15031f06030c0818030702090a0e010203072111030601110a02030318090109020a020d050703021c080105040f0c1b02010903020a0b1c0606020a02090402040e161a030919080d 80
    0x111a0720107170040034554000340205003c1d1000801c0105d06912009540780c000002c6d6003003103003d81c2846120980680782c0d02440782c895185844d0900244003440c0325846a5407410203020302040005005400b11140030805803d0400c20046280d40d407040701d07000303242882e140303809024810b042c0c0d0510020301002541400002008400b01c101c00c0c4500382c6081c0210b40b500740700e980ea0300901c01207105000390080981c001d0364001031402d0146010384a610301900503030300d18004022090003958109445c010100301c0b00001800182410b1046054203d41e4041c10130401070007043c00f0f0130904115581c4101903d46016040c21039219455000065030301a1022074990745426402c1680e80148001101e883e43d92484900904614003c0c00221030705c0e500504900515a028403910001c02001681c0203522044807040003442004080d005880c00c0e40c4009400e800e21944540d4800034940040c0f01403018002c3c8030650001241030603500d103204141c1c040c0c607410380c81d0800d003d0040001d030788074143c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 672946726 1250 672945476 672945479
    0xc030304140f19050109080a05101116061d0313030b060a0801060e0402030c2b110909060702010e0d080c0a020c03120d0c050f0706150503010e1005060f15031f 70
    0x100d50b00001c3c2500d600342ca9869260b40c40d9415103a0301c0d0b000100260060340039001c1c50492050070303449070750703441d0050010514202c000410461191440181141c0356640c41a1940c1003d0800740000300c5022568043c6140c24164040440b0329000c600000d082c0b50a54000316034142d4030101b000b40200640700080c42140e544d040f0b900c031a510304541c00d80c00b0b8054400d80b400b00e450640b00d410034020305103241c1c000b10314001d101c062040400e2001103a91003000c010b5000f6541d41d0055091261301d0080c010401443c01d010009e0955004507410856503006d4a60003c006400030801c5500540e100c800310f4039194206001ca2610304840304440c0c040c010445004a40b4620328020302110914803000c2c0b1405071104411503443c801c2c20010001000305100323480000d402c1d41c114206640d00010074000403615280081d01b12502c6030008085540030701c4010180380018001c40e07601171003c0340c0880724403416201141d090340440f91000c1c0c4003580080052429807200001200300f410521120b42c1c3c4a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 672947976 1250 672946726 672946759
    0xd2403050a2616230313081908030a0207060905151005010f1d04050a24030b0402010f0239220b130e010c08090c030304140f 55
    0x80016601c1500c840b906415490b440180140a60200003144040c0503c0c0a641e54108014183d24550480c0e000141e02d0415845201070313a020f0001e84c035000302035a078810303c01140c0d8542c05a00d9002588540041020650310525000d100324001d422440040c7e40340d5406031014020311616800410341c5240040c00341c240040040e030b6952241045440c0c02041d01c5407021001038401d24800c06c0d0019104c010402c00a40c4035042e1607015000400b2014140c68207000041c0c2640c3c000c4800c04082c554070900184101f90740c0c01ba5589403404104880d03d6141561949c910411000f4000b0781408101c81280b00f02074403c00040424440048440100c12641c0994042d07035958450007e480d40000c8004003194604405c00740c03114541c000703060043d0000720790312038084c2401070719056106c880004510341030112802004243e502d04000042c82ca880c204010b40140b00103085d00d06544d010300c41080540d1000022141a500d41201701d140b4400040005680e058040200540001091a440050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 672949226 1250 672947976 672947983
    0x81803210703050702130509100b15090301090b090c0f04140703021315020a0309080105100509090705040e01060806010b070b0609130503071406090d080114030c0d030e0319080d240305 81
    0x61701045013509e800008800f01d8000f80d0b000070341c1c45a804000300c144034803c00341c104020588a40c000d40040741d02100c135162070649110491b01c0f0080c941051642c182903161030030145032440f104031803c00c4200480300b00384011180c01040d65080c1603000400c2d0180381c20f9440319100900130406104415a00004000c0d2035922100302200800d5500402040300e0b50103000b031504c90040c945808283c00d20345010084402c0c3c0c09414882d260141e6640411152102c3c010b41d0076105140300003043d41e6103000a0709107001c0d0140d01801c1185024096a0000344098880c0c60300001c08550140c000c5d00c4940044003100189a002046444005038040800118001980826240c50107848455507100603207516640760001c0c40001900440050141010322121561071144c045c00b101ea100c0b00c42008203440200040068020901d28141e50005240400c03400f00100940b250108942d181951195201e011f100d502c90a8076031184c2980d40c082c4c0d075030790106903407440f41190004826600e0070138503113 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 672950476 1250 672949226 672949231
    0x405060f04031b06090e010506070f03030b0a0f030b070e1c080d0507030e0c0102010606022a060703080a0510060f110114010f06020c040902010f080910090818032107030507021305 79
    0x8200c5d40305000801e41c009110072412035001500651078484503603121003507000c0d82a411428107a07194009401615001d8100c00505840c85c00505414114281440d84000c0180700804014611410782402c0e1601004071200415685481320f00c44024603002078580980900758540f1842d001c00c1104141d4142c0045031603030f103084151071903402d5036401242070700c00c5400b81c6ea0240c0d10002d11240b0040412032aa81c2c0454121100742d00c06100c0000240150f1125909400094403001031001e50002c601c2201d03008003501c1d0504400902e000300240012150f03550060034032090f1004070791484001c0d00002d44c18070b08100803800c00d41e111080c00081c0c0109004940052042e20380125003414640f150b2022190140c5030901d8030300a501040b50391450092005050780140e000d00041002c03a8012208081c1c4200400c5858002d40b40444601215047c2500e02c05d85c0070b030b5070386042c008054246200074002c2c03949c11a80c0d0015410309480e1071195050080d080000c0100c1c00c1ca210640b43c1c030150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 672951726 1250 672950476 672950489
    0x1009060c03050609060d0204060e04050c0a121101030903031407110d080609040b0705071a0f130b240613140d1505070e060a030504020a0b0c030405060f04031b 70
    0x204520300c0d8201141164000c50344503411466410201d29145842410360299510090010898076111840991010780907601144c40d83d0103142d40030403d1030680071006c003604100d00d00c985400919120240d458100c0d090042c10300d5580d40c00754051506c030b40c001b01c1401c00704201ca61074a0605c09401004507608a14230105406504480745405200d40c440d80d000e08801040d207a80390b152a01d800b0240b00c03000d440d0030188802084402c0016112500a2031503040c0c000c0140160f2500351041000c10400510001c160100c0150303150000e6014000307d600075901c034981c0600300824044842a041045900c01e61140c800b1174422154285003452500350392003603015100c4480500144040c0c10903d031001041e5012010120100441981c0030315803200c1d96103800007051078038102084140d4804420f100010742c0b114100020750a100404900800301006103c0c5003081401032944c6038042c9000762031058100040c2108480300c4481514041c6410580005030985001c0031112201781905c29031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 672952976 1250 672951726 672951731
    0x60105031204060206011518031a0609010305030d092a090c0309030f051c02040e07020c100c030806030a0203060127090f03200d020d11010e07050918100906 69
    0x4103035060700c00542d81159450303002800707640d00300920b4100c0c0020502821041003900010f0f08503101403402c0400055008440128850a01e8801d441c0014401461640513482840040001800000031503c0c0c6800101f800586020507140200d40820650380d0002100700c1041c440410b054102c441c4000c59509a604100c4100700c81000c1e03066034503070840a004522241c0c10b01d00401e0064004145940001c580441c64a0071040e1080490f04507030032030a2820030345010001d02e143c04000c18001c1140440c0c0082e00741c1c00c8070400600d00641d04000404106c02d08010074075503242008005900c0358002d0940c0c2080d070712000662400c030280046641a0340200b040c50086400702e01c20f1a0345550000304903d00b4084030748086d6603450034403022480f4044541100c14044109002c40400c010380766000e070030000006030005105072400381520009900d448201c03c0c00c244002500c03400c5550070344603854166969100c0d50f0181c001d901c60050a401440c4070880c45150030303440044c0baa84600803c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 672954226 1250 672952976 672952993
    0x2030c07050a120b09030904060306020705010507181203050f0c06061e10050901020309102105010b091012050a0603210e040f0f060915080d090b090a0302040e06010503 74
    0x4112100c2c100b44110f1000e03082d000030003800b254103081075a40c40000501128684031a035000b0504440095000f640ca04d40e01052103c10814207009107500702d003061901c0da140d1840340f1291044490148501c4c9040340039420318108250181040d40d01d5103440c2c5e01046d8803404e80c0c035030507503d0f0b1504803046441085100a1040d400c090040e00e03862202c000f4140c41e8402500365402c1d5540e0b0b100202e501d044d44000e21021103503503200d0840203061001d50f80e0740ea210248800300c801040c000f08101114080c141001800100010300c240e03002c1d5142243c4400d205003071001d040d14040400c0f09400200c5d8103010412411086a80114044903c103110505180101d00e00f03a0034101c0d5401802c5000621226610395240f402d03400590341c24102030710004100701001a04011101030303610984800d070700c5000000b03450841c4412100102030480203000d0000c400e0800511601850080000260000c84c3c80d030100d80760030300340101456011340f0811030308001c54480c950714007003481102d11900c0307400394 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 672955476 1250 672954226 672954229
    0xb030c09010e09010c020a200d12030c0305090c1e010c0b010305070f230d0503040923011d191d030306040c030204080d05070515010b130803030c220305030a02030c0705 74
    0x7c00b00c8000d50000b0001180102c100d08010350900c02c22400d5a100340b2041e51140440c0c52038608444281180e1030000392107072202c0d13014041d48c4005006d2041034100841014181d10b5030180105070244001880f605034801800695495048540141c0300340303003800002c01040b82c001500c20035078581c0700b40c28119a90325003102d041e080706010348101041c2c05281da08060b051202c1c00390481803088054908050b1540300c2013041780c800c7c01c442d0b80a202c00c1d0384480601000c03600c0d494050304041540d0004429501d03103007030b00c83c0c4010306150348500180da4032280034034144c1d00c034a1014045540d0130700c1c0340e40706d2844107035a42c2055440b07901c074900e044079409134640603100b11022542a00b016180c0c050f03240c1810b0b156a00203c50075600f600420440010b1a944001c500e4081c2011454064541c10344000311103000340c181c1c000e160950300410a000c0348032800002e96075040c01508118010320684050000825440d40c0018400d11001c111300d00850b0f001310143c00010984000c0b200384590b20b00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 672956726 1250 672955476 672955483
    0x73e0904020a0308030402031023010503030a0906181a04050141130806010e10030804091112010902091c020a03060b0a0e0403091a0c060a0b030c09010e09010c02 71
    0x2a030003944041c1c1071200300001180b11000c0d55219000030103540c00d100007138144030180e800100c0c1349030740d030a0003680700300341c000e0101455405880250029402c040ca070210240c03480c011030054500303009001d4040d109514686804d83e0240289484100c15a1400b8101c004107402a0080703d01140c450f00000d180901c2c1a51802000700e08201c000c0304c00c0d005854070150903031008448201ca811704002444c070400314840160700800c000c00007000c80d0741c5085600947c43c1030240c03400180c510b500340200040ba14031002d80341914959240054000c00d0807442014034070402c40802003070020f600c00012840402c2c2c0c003501e5a0703901070ba028410340c3c64000412000c0440203000030742c847d854541c1440818060350042c4c81030b00c0c000e80b0182941d900d40c100c14400f0101100d007200010030fa150140004040c002c0207840f00d807580c903203441c00e1000100030356445900081010300d25664030b03035240f000341d501040400400c44020b0081d12995840c0c840d420704001c41182c81e06010360920000300049807002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 672957976 1250 672956726 672956731
    0x30f0b1009061b060911090f0925050409050c12031c05070c02030601090c022803081b040b0304050c1014092101020a0201060f0614073e09 61
    0x1580c403600354608081040d1040d08000303c0000c00740c04005150b07000212280314801445000703030302101c1121114401c100c20948001d00d0000d000a111080c8214610b0000c0d2400c4e10100260481e10090301c035480d490181d02143d404181d10a040000300d0b818018041403080c202074094402040c00516034403000d540c0d20031400c41c0380044401754a0b20b014210568401900300980f450008081c040c55000685010703403c0e0404051036070b80e05202d5024a404121116101002158003006a541d00007a078600380039108000c3c0621a8100c0002c240d100c54803031400311610540740a90301c8070388600d14000960411030b400c580030b01c1081c05480031440d10700c0980012060550340c8140103d0700013440361068204112aa03002a0407080e04442d2800c1406042800001440016122010a48001c1c20344a83c0d500002c0000c401c0402400040e5100d0244100b08941161036982d034107440c50810402c0180c50084581c003039000100407000030600008000e0480440d9400e000345044000b00200c03040c0c00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 672959226 1250 672957976 672958009
    0x2030a150b0f0f0705250f030b010302120c060a0c1b080303130f0501050109020702011803030504052b290f1b07020310060504060e130305091f030f0b 66
    0xe21074440d0101030200109012254035510a06051660781c2d120706d0402540c4841e85000c404503200440044442c91000003030900440e40d044192664507880c0c107030401800b010b80644e1080d8000c2c44406401c11000782d501c100902095900c0882503002070802102400890f51602d018001c1c0394071002c0f00c1c0c60407054944107005185181c0762260741201c10401d488088076072074008540c0b0f0010030f02c03c1c484d142c005c000c4103102607601c0b155803000420840c0b000c54861507103040d5034010301c0446d510805441c01d42e402942d06003a1505074050b8a054a0b0021007140c00c41980c001802d0100500e03072aa13100340300d1043c1c1d0b000d0b01960404e101c020750b0b80021100e40101c1d400700000107404486a8010442c0036500403096441d0070019004242801e600c6140030086580f150310403c06403c080c86210014800e80960211030300f045110800035508681000c0c081000200d904072543d9a08107088811140da00842d000200385803101801a00c8c143d54142c00701d40c504034422180d403c061440701881c290 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 672960476 1250 672959226 672959249
    0x240e0d05070b06120a080301090515040c0c11010507151d07080d0f110d021b03010c020c0603060a1d100f0b1b07180b100c0803010b0304020f090a02030a15 68
    0x3502010f2240850211000004c60720401921034042036480000314064042d08401044600d084100c2c030914003a50710318170f0b024a00e400b001c3e1040300d0f4810b40d0007641da80e011008034050902c07580120b80303502900001820a1850080b29492490f80d60b00820750002d00d600a0f2040d8510300881c03d854103001c4c4958111a0031015803908860300c140d03030101100c0721500744500d591526080313580ca000740801050002d40d00c20489050991081890f0b1602880d08500034440c0c40340420000752500d0001050501800b004070106400d96186a103200c05019040c9175600c00100224810b06907140c2503c0308500c0c001441c41c0425040d90881c0322109480803807080700d00d8601074080740e1101c00383d011081d4070540106c0f00c01003246c056502da030080f8804050404140ca241150800071031190802041040c00005507116000850007c1030341d04482c44072155540b03d5a890022964207540300c281c203903100282a041120b075003555805140a0304160301300700325010030480b0101d512100741c0200c40071103a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 672961726 1250 672960476 672960481
    0xa0501030509030d0f1119020f010e07060e130504080d111e1605070b130b0c06130309050616050606040b1e030a0b010b031602032104240e0d05070b 65
    0x800d5800c0f00014410554002402d030b01a0380c4030301807a82056080f040e03015221f081c02c0540e00d504010708000c1d561004000c200e000c042d41c440f5640c42046100320020301803d203030655203c0c2d8843c0c07000120403000b00002c5c4010700e014500014541e102c0703040c600d5130500c1c3c4141400c1c0aa54003042c1e03903032440c1348020a411302e401c2100e041110740258240c1c900030b901424070403000450a0017188000c01081822075202d5901140748004154160402c015129052002c0340922000043c40d5403c024400c003841214075850070116081d90240d005a41c00c000000788480c0308580581080e030341c040c000d0702030702c0c202d440310010070043e80c0440725805c2c3e01003903117190305100701c1d55441d0b07100c00140e004048485e00b00581d901d29401c00400d03804089500000303c2008150040001c0b14009600c0300e1010b5890b04c92600c4104140190043c0b0f0311840c00c0381c180000f0b0421001c5050901d040610340e0030716a21708140389140020b0412800555007900800542501c01c90040007510030143c0d00400a000c9603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 672962976 1250 672961726 672961747
    0xb282a020d1d0618120d030605040f0902031504051002030108060a06060f020601051201060503060a0504050d020a051f020906030901060f0807060806040f1811040501050a1d06210c0a050103050903 86
    0x1040d01c9009500080044d54408180d0013000701101c081991f46000c14000c0c1343c801000708450300b11807030070b41c014105a28840103070f6021507210108100c2019021280d20799003041847c050807001c2000b591480040045144100060041d100381ca0000781841059200d80040310401d0300d51000b070300941c0c00080107022901d002c00302080c3e008226800098041d65440000703282500540300d40702e91560b600188000c1c8002441041c107292042e0004003c42c1d64a076030383c1940c1c3c0e8000395a0364181d059030320448402d950160100d410301d44000300f803035844c1d003040c04903c0d00828040c03064000b011108403002801c100041030700400c4034266280c1d0001540e4250501014040d00d1414030512603894100540f9950f004602807030940c0261810301802c401602400202d5206821040c41540000701c01c120200d444041c0b44a00035142c0204c5000351900d02c003041c0e5880e401050f80c4904404c090313103414101c40000f4000101c5c41e003110041d51640e6035500640490b0010384460000381c00410085022 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 672964226 1250 672962976 672963007
    0x1b030b01110a0b04021203030405100c05090901030302061e07050403081c02040308120106031a060a0e09010801020706150b0906070804050a09090b282a020d1d06 71
    0x650181810000001e4074001582420241501150342042000520056061000c0340401141d20b5100451841c10130345c40d2140c2c1d807107030b810981c200d003512003940111032413041c0c060b540c400c8405003500b142940c40380740c0a51561012140d5000c4010a0a80543e020340880c400754000c0100e0340300c0350701d02170643e00c2d0742d138081e802845905c400c54104080b4008691803031006000642c0185800f5803034074002d525260215030180c1c8500100b500301104d0031207481203020a41f154050450300141d880400d15001d40f28200800030065100b20241e00000b2280c00c10b400a20800d44540c60411084400e8000f44061903068050641c0e1080240140e0905003800001000c0d40c5000d03400850415644800159484c0c3c030311f42014010544484551003000400c9410f81d030002a5100007072a81101d0300c1e4180320130f51500c621800b8064840c44034807480700901d01e140e0b1050f406526a040310080e507200207542d600e400000440003034401c20b000c0340301031024a40900f0340b090040c94946410b40540c0540c00c0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 672965476 1250 672964226 672964241
    0x170c070503130f030c0b031909050a0203010e16060305090309090717151003140402090a1d03070b062409121f0b2704060e070f1401031b03 61
    0x14144001c00500c4400b01c1c20441d2003000b003055800c1820850700b186000501c010a03a032000b084c03d9400e0040c030200000707000c064052510700540004d044c030242d08002d841c0c0105040d0194044d440c1c0980d44140100205508590040030610ba40000d60358460803821900308542305043c80d0014419103600e40382075602960001110703e81001060384514590750503140503980c034981e0011400c1c206600d41402c00c103402c0c402c3d4080c20200300044200085220358040184000c0c451504640080c121440303d80c09050103131649404e1100489180304015580c1d4400d90007910800c58000c0010307410318040c0441c000c01c0340c44d01c1d880c20010300c64201800c00ea80241c5112640074000d101d9203191904104100d0345910505e85040b051880c0c207140030301c11a00c40d014454001c1f070340700c070340c91044000302c01c0118810001061180c129990340d04003580102104000c510710780c0200b40001031141034424441090b03070f22003116601448203000064045a5103c00f580100000403e02c240103507020b648941c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 672966726 1250 672965476 672965483
    0x10051b010e06010b0403020a0608130312021611033c070302090c0d1506141e0408030307080f1e0711070b0c0f0a11210109120f170c07 59
    0x5400444007410300d051000036040000201d00200d0100198580165444c009016904102c94a41401d00450541c4058441c010b001c1c40122800e14000b100c46504a42286800710b80040006d003442c90140551102000f5040c86449102e01d841141a25007884030381c40301d03107401d040c03200e10481c028409001060360005040d60003540c4000001d0b03111040d030144076181403044039544d0a0000a40400c80c1c11825051903c040f07241001d10810307170010030906907490f03440601a100c5402d10903045140780009032144440401180014a00c00000b003e18002c49140c0c40d01081c964481c100c0c002c6031f00c012a070301c0032004c0b0f1100c0c000014200380300304990040c1e418903000000c11004d5080c94508070927903201030003008002469064040b420f000381110949950040e00c201241500c8280b04110640c240a02c228240000c402426019002d0000340d150b8840081c80f80c031546007410910303c0c040da80b04d80089068010803901d642e214200c10725943c0c140d220902465201c0b40105540c540003480f00300e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 672967976 1250 672966726 672966731
    0x70c0501020409110702031b03030a03020d02130b0403050708030304031e0e0d050c01180510030b0111011107060c1704030503061210061e0b090f0a0314010b040b10051b01 75
    0x890b40c85400d001c4c00f04030380201d54400303650700d6040c0b06041c5013810032880d151820038604094000c80d80c0100403200b6000180c80c002d600c40d03002c2900c0c04024803890030010b103401c22035900090403240c804007a0007224091015a90180d035240c00d0140c50380320465000b0f000609455500c03901e24100c10184071b0210307492900c0280d00b08a44007050b1000410801030741e050740200205041503138031984801b65264891000c00f107943c907190120703c3e25080724044105054681a9910003640300788a40113001c540c20b4028060a4858075002105a10580381520540d0914900c401c1e60350042d10441d00c2003183c08803a40c002d5989071421610740e000034203c40d900000d040060040d50204101c1d29810402c0c200f00007410900c0c1c0003c60036849a681c1030713010000d00124042008002030015140d03082e00944e001d171851248000000c07101c01d001d410080034040034449214034800305510000340f407402950300b00003005a0604000d0307600c0d5191180000603c007008039800d08103000860003101501c68001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 672969226 1250 672967976 672967979
    0x501050a03020c0312190c0206040f030c050a06020d060f080c0409230304090606110a061e020a02010203070e060405031207080d0207031d0103060509070c21020714040e06070c05010204 81
    0x19045074072200c1ca02d04d44000c0401403081c0310201e00314500c184000c6c0d00081160195100020b9200d1400500103440c00308030781060000e141c001d158140105a10105403803c070004c80c42d240d4002e400c000201c0040f0340c600b800118a0100b4110520146d1719003600904001c2250b00402000c0c140d2000222035250008110036036062404603001c1c2c15a4a00000d90303141c42c00c00d445141104d1460f482001008140e10102558001c003280409003a80c00c58000300d134880200d51224100b00b440780e0781c01640c41c4000707090f018269041d4051030285810b80d07610030100340c2d0384080051078001d50042c0d90b13242e0400c001c800d541c0c441910007803e1281c1b1078003015080c17200c840380d26000c0360010307003007540802c0304019001c6240e000381621520305a02400e0410050342810701142a2060080c8400c1c20301c05525610414000c44044007074022881d0746000c0859030b10045c0003512060507210b4041da031500707016034040303500d086d0140c00751114551008015039039500c842102e0032540500107585d2958200030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 672970476 1250 672969226 672969247
    0xc06040305071514010e04170a031a240f12070804021e01020318040908161505011a0d0213090b150403050d0807090e070804020f040b0a03061109032d160501050a0302 73
    0x1910090080340c2b00000d4035450003c1d100f050180016580388144143c0031281010b800030703640707907441e00d40f114441c50b00c0b45401c1520100d41e124850554190407820300030081150741c07050310588582e200b540c0c030540c0c6c1240e2030b06000e01e07424142d44140c0036030403d028103030301e040710812000c142800080c00459800c0c996100d182050b070000044148896040308040f0030310052058234203c7c4041c84104000540c506003404000405400c00d000304c06200081c5590300c500540c0588802043ca5000b19200302d540d100f40f030f0000c1032200c10141c0528001d19403911300710109410344040700c0e0008050030060070f03c070000320307010741005050505100c504900410304c001d0720a100c0c1d00c52485619600c0b00c605180c0100600f20402940c11445582060307021041c50303c07003c4000048a50001c2d010441202440d24190107010b80325a01d41c01d4880c60303040c031214071082e0300d119000c0800090360b00810f10002d0240c0d41c4901511502c40001030000d030041010b54420380052a20032002c0c40d005080000404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 672971726 1250 672970476 672970523
    0x129030d0f0518060706050406060b0a02030f0703090504140603060c1804150e09010b010305150d020d02150c15131a0402040207121d04052a0c06040305071514010e04 73
    0x4074146c55542d070b20410032041103114404c4c0c0c005042d0580c038080c101800000001d5503445400c503200a0100c011804a0405009000441c0a8413000300240030030b40c030000356440041d100712600f0340320744250700118080b5010042200c400a042c0e2041010900786401444040c0c0440000d08140c19860280022000380d8078003401c2c018690759002207540340c4041c000505650000e0704003800102c503c0c00d14481e0399075012103c2003080d819256035010344403e00000e2201d1000c0c4a1181c140341d000030b18444071120102e0060729a2000911304038540e03c0c0c4145484201500141c0244502d51f81010304c9411300f0f240c0c0800d0b910071f01c02040545403100355030b91601254a01c1280c03001207001000380d40082101c1d01440d03d45ca15080e117040240345042c0e4135041c049000c81200b000350308101d008143c1d040540300c0c103c901c8642d085040304c09500302440c004000703500c1001e003610902c9040221440032002030040d6083c0d40b40aa000711100d03400c1c03001d411108000600111181008460304098908110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 672972976 1250 672971726 672971737
    0x20c100c110a15020609070f050130020406050d11040803070b130c032415061d0301230f04080d0c12110306010201110306030304170304080129030d0f051806 69
    0x10f1340544917506001e070300c1a02e0308981da00300c529a80e8014400f0300251b648a40100082e000c803d80342c4100014801d41c52103203100c0d449446074050300004000c00c0854000300202140b28401108101c0c4d8004240400c0f9507015500030544a0f03002009107102141264100c543c0008d186240160806004d945c0c903206400c1980c001c48089031008050000c7c508030407d10320348100300f0701c000d2192440030342d19004d02c002c0f07034013450341448103900440780180c0100c0b0012020f681e019000301303e034408844141e444d01e01454501c01c02c0700b43c00c40004101c140480030305405203520800450801b055000b080c000741c456046208100591040701c1c299245041c0502400300d00440e030480e035030381000f40009080d1354034056105841101003060007440d031000000c40f0102d51070441c802000030189804181584202d500c41d601c5507080904401c800c0c0624822070004414181e518500c0b000401c081c140c440d142020303242d0200310601c20b81d41c4c129001c0c0000700407040800c1414203407004010002400d42e00304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672974226 1250 672972976 672973019
    0x40201181d0603011e1116050312160f08060d0803070305010819030c1103120315030d030903120504080c03041d071407080705070b04060f020c100c110a 67
    0x4000100c80c031907005a003464001d40190028841490071401500d00a0402c08004408690710740c0f07a1a0441c4000d82a40c1242d0700040c80c40040e41c426060031036807a0040312241c0003224200c004140201c0700b11001525403482500c801300b62801040050728003000007026a030700401c010243c1400074030100f00440c0310b5070036614001295418000b8030740c070f010b040741108150121108200c40c00300741c00c080c1d014092a8031401c4d1520181500022038280040340c00c000c00325540c08410b02c48440064089208008001d0f000c6692566001d0400c45c1a6400920060081103040c0c0b4100d00705030450b0081c0341d003d4069003900349402000e4a4052030b552141d4091030b40110404089a0034040c00720555803c03041c03914001c685260042509019485641d80080070b0f0400084d01000f0807000b848044005d00f101c802091f22150742d024050500c9500c1054000107010700c0e9000b007028076001d11030f5060382c07806a950010002040d40c40070034030700001043e0359021002420000c2d00054003005032000310b80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 672975476 1250 672974226 672974249
    0x3021c06120b060a23120607020a03020d0819050403112512020105090d0c0801180210110c010c050f072c060d02040f090f030305071b05070501030504020118 69
    0x6403400d1240540101a003464131402c081c40041048507200b024088040b060540f0a4108911240029640000b480210b0080d4040c08081021380c1d0340100d451018140a0b4082d1541052001c00c111001d00d003c454140c2120f04814140d07845a1503580400e034068440e0400d58807035000084031500d4200a511100809418000c3c58004d040d084094070004040e915a4031100401640c00030b171641c000e496105015101d444100014002881902c2009000e1308008200040d01301d031700101048082401a40144040d403510a9480d01c00e682c9082003448200103020b02455000044031400c9100c074050380c00784211071a481d8034807402d110801c003c3c4100c0e105442c401c0c01c82d12603101400d9030200007103541c0c1c15001c01c0100c0c980728680588981c81d03044500142c0b540500341540001c0c60700744000350070541400c2c0c503207041640540c40640a000030351a20101c2040c800e00140c0074991980c0001c10f0b6400c41142000341d940240c0205800500c1410581c0c0300001400d103c0280240c03e9100404411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 672976726 1250 672975476 672975509
    0x60e0603120403151e020c100c05031b130320040b060703051806120a0510050301060303051e0405060a0f140304020d0b0403030609020a050903060906041203021c06 72
    0x5020041d00c90950603004540d41441c1c51a01c0d551100980e454404500d03e846982000b40d10142e50050381c44d10140c80360454403205480c1010381e590440c1c6140314521450514660340b000c0c001c5082d6489410007100711000515040006212034000005440e9080d4441801000264036920039003e41e8100c0101c89c4803094a12040005a91315080f889018100c20003010000c261321000700e49110101c2c20380c48000e80405004038034248038200b4035890500824091009822841e0403d40c011080000c84900c00d5403a50105801c0f24590b20004001c540200404101800b01540c4807044181c030050490419640304045242940a00105800581c80c0031100f110503410440820034003100c240010304504c0c0540c04030341e4594505502030180c1115100050805200f40c220401610043ca03056445100a050281646c0c00045489102e4040c80c000503650b510002800c41c411600070402141c4030284010a0300203510401804100303200201c803415013051580a10030040c8104106010001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 672977976 1250 672976726 672976729
    0xc1b010f020a0e0901090603030503071b1509060b060c1509070306060e040b0907120204020d11220e092a190305010b01030b01020d111509030909010603020304080a0e011101060e06 79
    0xf42030580000d0400340c074140c0140b012980c080d00b0b50754010600d0a2011008502d000c5203907c0d140e1001008082d40390f0623b001da28020550092100e091082d0401c5c0814080b030020007003140200300902040d5440070491000d00310418212507044001030043d01e00007600d030f0b01c4410640f40325800c104103c44414041c801046506100359901c89654000703004940c0c02e18001072003176140d115010703110300d4010480f5045103000b070348003024019031804011340c0c07070710030320f00c03040b80c3c10101c1c0c2c3c204058108803c400120507070011007035482507100201503c000c0d039007900444404000c4441641c010340c400c1380b40701d10f80d03102d100a0200b1002e00c16040c46c00ca610f03504c5c05a00303680f40d08803824105070078a107107044141d800142018201d40541403115034a011400d0047c1741010304050b80c4d0841c0e40c280280404040040020600510705640542d03031a82c988005409070320094400800e084401c002c84024903210b405000c007480c105140038456418060388180c00d44500f60484074404180300c0034400756 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 672979226 1250 672977976 672977989
    0x706051602061e0402060903011b0e03070602190f0c0f091a040b0d0212010b0303160b07020a0c090c050c0604050c01110a0f080c120a080402010305010e0c1b010f020a0e 74
    0x20140299105803003250b400f8021400300805440280201408076a281300c42d5030030340104102d4502d20300107901040035510024060100000424024082c0e00c1010031901e00c0072811482c0403444840c81000e140e0385076030354440300358620702c103940141e84074101080585103a41c47c032000b00701400021607140c14198015030300c0f01419004600c610310301040b540c44c03a103507840000003494040b1000031031540f90340c12581c0076000104606078540800184210044180341050b90842c1c003501c1201030a903200b1100f07170794820449002a01d1192000000c1004145541010300101d034545007060400765801102d43c60001c0030380b0100e500740c000801e82001d0b540d000d40b5a080070b200600c02000414925102d04102c81c480700c0c000743c280342002600d032043d400d04103e003001c60310002d0002e17580c428a4400c020281e500594080340005c0c10040001100382c004080e20340106041840e4514000d01d8405054001c180c2c000d03155444e5484d100400744491141c4040d10200750903440b60a030103a014800c0202c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 672980476 1250 672979226 672979231
    0x6040b030a1802091f050a1217030106080c070f020d2402040b1617030405030d0c080412120906181a070c020d05071e090c0e091302010302070605160206 67
    0xa01501c107890502c096074a0844070380d001640044c40e1045c8059108141c1950801c680210b90010101c581c00107110300c03509003181d04c072406420074003504080d49641b000244428400c1c800003406100100d00142c091800916559104034001ca15910b2680d01040d0500800d40c42981e5607035680e4550600c01c24111906c040790408000d0842c80e03d404c1c1070040800e401802030070f03000a10580d442004110496010096804251140c1600d914203460141d590741d00402d603c040d044c1c205060802c10500444c46180115440f409550031a0b640c00000c495581d50440b000301d2158480c10540049a4944522071042c0716204660342c03458528203184568004a1205140a0700d000c010050090f91024050001c80d0303045030b1050a00000d4102140350900316044464080c4504202012044060341d030201102ca040a0030300041c5056001a1410031904041e0f80d008204030000030000780704852803500180c81410014117141c000c6d10351400b190b200300c4505203022000048181d0568040050303a9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 672981726 1250 672980476 672980501
    0x50306120a0c0614070204090b160318200a0303020304080c03060c041a040b0a0c030306060216140111030f0406170c09010e06071407031520070201050906040b030a 72
    0x1a941c040d56030b0488009024460b25042000040d4007680c0c4503201421514940d80040c424800310140d420b00101001c401d072554041c1c1d203560320b80c1070300d01400790240c01400240038462660401e0941c0ba5006d00b0300c1d208004418983c00e420b49424070380e49004599000d14065801143c41d1030074078180780e1404085081040c402e45c0010108110602000c007158181e80840d80c58102800030f07884484000d00991300603d100003004a007041142c2c1d40107081848803030096406000c01642c0d50300a030b03220b503c140d00107162032403058010710441c3c2008403000e00c41e041c1894001e000c1a103070b07010039055412080e6050805100020104000f17a4481c00001c0e52000240c1c00c05043c2c01c110024000d40c0c401d81050324140030045c010030510741c1d2141c060b128050b0704030381d1000a403610032480a480c3d40c603a002c111205c030740340c0100c520342e50010b104002a01500e0b080514040c41010306031300890704032182c100d04000c41084085000d88071400580b00510303d000314142c583c14403000c40025038000e0b40092 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 672982976 1250 672981726 672981733
    0x70932041802060a0c060b0a05030303070e010e060403061401060201020405030307060e0106180b01030c0305090c1203071b0611010c0e1e0a0b0417060f010b030c07050d05030612 78
    0x50148a060009480080804440000c0c0503811800015208460781801a41c00b03d0701250a8090b00e8000546400c0240300d600d040120400d94030400c01c0c4001c0d1401060342550045c400180300300c0c01080c1074024110141000741c5100c0d443d000141d0b40d6445604219080c0d600d640f0980200000754500501611980c0002c0d41030600f8034010030382c0d9018290014042c1078032440310482c811420340c0901d0240681d902107460240c41d100402000e80a445001800207280905000c2c00f03910030321035103005c0d54105005c0c006000c481420001d50004030320603130050740810098a80054180d0961015000c012003c2c1c085e040d16103480501005510304103450180d0510034a000d0440d405150b01120202c00c031401103e400d4140116440103400903c0e9a03004000e40d807022400d07242110290044030070021107480c0180c0d2100702c0c50b40b9801d059906c0f50340c4d0761200b0010b01656800001039540803034a000480d0619086807501450034601100d1000070400000501400741020a80368540c0a4a68002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 672984226 1250 672982976 672983039
    0x50c0405040201141b071d15090613060801051305060903070201080f0c0931020f030708040503070c0e0f090d1706010e040f0c03051b0d020a030906050709 68
    0x68410b942c91120010031640c000f6112070020104501000b010007050120307904075440e4000700c00618513a100c16900c1c07420000000e50810f4123214140c444410250010005072500e030184114101000c4000c611703035403601c0b404902e03200248506d901c2160312010b0240392180c58101070342007000c09030580d80302e60410400d0300f0240c1d03003007900140c2140c403032100d11034155548058110140500300c251544000781840e0700b608507280c25803000001da040601112091244a6001c003240704010b011042044107000240e1003500a10b40540c0c083e0084080d02e01d081090380c6c8402c81658140c100d902c0c06100300e01880706038600a546075600a10b808018a02405500c0c2c0207040c40303203924000500301284500103440b592041c0b8102050160242043c040301c3c4140d045d00000d08580045140000e00e400c0000f01504041d03400260b240110302074107454003031180c81c4200039511001004042c1901c1b100c0103000108a407049900c0362000d41d41c2c4070321007424001204c03981ea1034460720800c01901c081c2e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 672985476 1250 672984226 672984229
    0x6090906060907110f0a170403031d03031e031501051c09020a05120708010b010c0c090f1d0c0102060604062319080304061215030602180604060507050c04050402 71
    0x2a090303080402114003210039a50781d2030440c0c181c520014181c00902403029017214242000a18040d0544a0340e8400320107200c0284100c9980241d02c0050001806103190b8104001000c0d0060328600c005019a4a400101604000c100b950f2000c00e81840100100b0482c003c07282d1000c0b90303d4010240b800f245002071040500344415802c581034040c3d0b039502c0c0750800c115941d02c02110300030310014100b0400d040b120100f007a1641024896640356508103100c000c90381d071140c2d0900e044598411001e820b860308002142d0010145141b51400684c0c0c0c81519495403201d41c44000c00c40000700f40100b04d5107080d41c000908140001d406030f4051401d0120520899080c501c103018180715040c0003c40115240d000100608451442c41c00f201210b014040340e220030100040081e11110380364503541c000c100c0b50b0f000440d001d0000c0c40b80c1c81810400107100041050300100071203080603229400c640f046400040c00c561096029001007480014003004002c0300744060303031212204440811181c5030540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 672986726 1250 672985476 672985483
    0xd0618050a11190c061b09050a050d0b100503030d02030402010f09080606130b10030603020a080f061803070c0f14090c0405010c0f0501060b0d110a0c0201030209040f05040f0b060909 80
    0x1560750640800c1c1a04005005108a0301304074416007156042c80344241c030000240c0e68064800e05240042c8410320041501c1c10700318900e004130384000e08a5582c101194a4602c41034502802c0031406400c01c030b6000905607010000303029040201c2c0e10040c0e5070705040c80090101142e109000d828024030a008009041011074103e82c0f00c1003d42d40c5011070b95611081030028050029080e510801400c0ca28401e01d9169009505680c42903a440f02c05984503e0119618120406904003907400400000c40c20310388108105003c41642040b80d0074035045a07516030328061260000082d00245e14000c01488107161b100382443d080c00e4903100d4181c205225492454840d501034541445a03080341041000340c40180044008c9d0044000c000c1c1a4862020034401da02402c1c24000803030504100c0c0c0c424000b032104862089001d03440b404141c02d00c560054002e5040301828070351203960354000640810550141d24444d900c40c0803c0303098426503103443c03986203501410150062000004210210380c001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 672987976 1250 672986726 672986737
    0xf1b061e1a150f070f0605011a0405010c0201121d010c05040302030705060304020f1302030411060901020616091d0901110a1b0615030317060306130204050406020d0618050a11 77
    0x2628078031000c007007014400d45107101d910580210264009207134000d0107010700703038200b08502c203040c140116662050004042ea001148600526a08100c104990341c011402000c034248181410440704091088030003c03288000703001c1c20080c050f060303240924031081c81080a20b5079542443c505190850700402d070749510034000c8034040c40740000401c1c15036585072548004081c0052075111100803e18070715000e07400542d030441d013201c11362a0341c0300c46107004803d80303020000680c001d106a6407000915055185007041400601901002c0803604c0c206542144084001c5600c4200c11401c0080b207050849010f41c002c105034041c00e20440c40065030004543c2400d800803c03680307042c1c00a50a02100510030b50030078031121805c01000004060b00541d05d04c82100c2002d040c2c82c000da0742c1c0c6003807640340c01c0100c2e00c0440c1c01410b00c018034018601548030b140c0140c05003200500b085000c1003d103007103c80c140c001042c501056012004c020046004160740001d076040148005460324110746001e0045 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 672989226 1250 672987976 672987979
    0x9060801060504030303020f090433051818012306090403080c0a0504150e01180311040905030c1e0f01020909011a120f010807050105040e070f1b061e1a 67
    0x98010b644200700040d80c8120074014030421119540d464114840c4030082083c2400501c11440c0103840c2f291300701010200e9901070640303001d141f042c1204040c4184000c00e040000001c4212444900e2000d10900380c6551007076854409180140f1498920310200400e040d02c00d01200c0b042000195010794581c0d000074414031220744540d0100c40036034441c050764109010407101103c1e032070f070308079440541c0010040d0280c90740c00c00c030032813000301c044056000e00014000e050b25080b17000060a0990140b40c2460082d41074a0074104001035071420260340c0000320850700c042c2e40d0000c101000c18441c04611150f110000c528000142000c00c00050301481070344c0c161602c15043c602e603050f000d800c580e80b03440010314407210361520354aa400221400c1c004c01d10980f04046000c20154007600c1124207030f6403c48040005540c42c040b04582100d40401490200411280c28000180c040c24520580901c00d00c1d0104000b0750303c41c00d400c1052003840303005040b0790500419080d14443c219054480000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 672990476 1250 672989226 672989231
    0x60b090411091c080c03070636120e0a0b030a1b02060402090406060e07030c021204030503070f050102090a080a11040c051b0f0d110615130903171609060801060504030303 75
    0xf02e4200f43c00d4501a20000103403d00001500204100c990350103000c981c1495213640c0758054005000000002c4550480c5800060003003040c0c0108041001245c40000c0c54549100700102c180003003003000a00d64425407060401206014007080c1600176424030100004140e049040d1420b4000d660381c00103003011380544032000201d014440079411281c060302c1c103c180d0880038140040020000c1081c4048200103001e140341d08a00c03204004101d5003220341000096040c40180d8480c110001e0882c10220384540d420410360b450350303c50203a420007e1000c0c1014044c11185810038034040b0419404840c4210301d0000d0340c003402034000c804c1d5050041c074144040800f116203000c0e645400300390b0110081c070f44101004c00440c1a0300050784c1204068103000d03100c003070301d801c1c034490281d50054403002d82c0309040c00c0f08030581510903801026403a01038170b0241001c2040100c183c181100684500b01030000180640c40860f410800f620020080e40c542855590303d4484018001d0040d170200500b00764 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 672991726 1250 672990476 672990529
    0x1a0c07050601031707060e060415150603020306030709060f03060b0a06140904060807270203161214040f140c0f040b040b03030301120311061006080a0f060b09041109 73
    0x988138401d94503c1036001c8410010755044070103840c0d59040445003180d9501d4542ca08082c2c4d4401d81c0903150301303842c00701c040400090501c04190060b41005148a400d0310442400050400a40c0140030051210781c0d04007515a0443c2004800d4420742250b46000340c9806404001d0310750310840070003843c81c0c1e00d007805441c1c04070403000401034441342d4081c6441c0e2091580101d042e100d4007003021015001200a820496403064460081c0d0200f00c5005680c840c4c08080140c03458010482051012621b280c001a0394682e02017130440a030054800b518400a0600d0003030420202543c0c0091102c030f00030061201e5480c12000401e07404000389010b00954a0701c09148054960f9000343e00d00e90f400070b0a40741c4a6842e0001140ba07810410303000c3d40001c1c400300411280c4200400ea01c0d0068203e914041c4c0c40604010b41075079078280203454810001e41c0c80c0c000c04440c1c404d0344101400340800c410342070f986000c2c0c0410070081e113114000041848004020808199a038090429103c0c15100c000103001d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 672992976 1250 672991726 672991763
    0xb090601030203071e0302030601030c0305040218040309080d12060503060f190207050a050c0a050a12084005061c18020d0b06010813030f2a1a0c0705060103 69
    0x171070b0030550021800d0682c0f4020503c42d40680286100718000c1c0e034200005200740c403044040d100300b66006500460018103200b0510f4443c4000d035402400790408a078a0f0740e40e4a21030385014104000c490018044078228140c074041d0b0b000307420040004800410b10742c1803042850072107100140588a010140c1c1c00030040c148425010303105c4aa412500b13445010345681001500c41030f030078250a22810b000da2002c030340c83c5441181c8106580074013004102403882d542c3c0740c864580c0184820032a82010b500c488401c0b8a0101c02604080344100c26640303c04d1510101121161341500124480c2c041070000500d1452035004003807044a160202242e115103082e80c844914403e514040e400800c4030701c4503418881b8840030f443c001c940c20b9840009680e10380b000040c2c0900d940e03200800189402c106148442d11400c800e010402c040c104d5030b002840d00080c4401120118074048814611712000d22940f09600340610341e122641c10000f519100340c03640c1c0c0f20307120201400021308400c10341d022400c24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 672994226 1250 672992976 672992987
    0x504120c050c120312010801110f07030512130b01080714061b01060b180a03020105180a080609010915020c07030f0c180e0c01021f0c1107030c05010908010b09060103020307 76
    0x3802c202900d07000d10400d414910a03240e5000356007032928884550000511038005100b1100504800c540560510282e0703002800b0700c1d48014400d030304204041c0148a511400301d401203001d0320a058070b07145c0f80e005920385400910b205a004c030440d034002d200108045001620704c81c45010f003c4410030303966403010750f840c24421007000e10006107620b000c2d404150b000b10384009010640d5048614585191050304108841c0074a0000a00194061113280d40c68882c0300100310000320014903144416480f0501d0500d0b200c0d00300c41039001a9181c0740082c3c107014200c1e128041c100b48040f0b055140c00c24088003256501e0b51807000618180a003d0090284103184860301c010740724141000c507214800d900400b000c1c1181b00c00a0340940100e41012501d50300000341040080b848424880d50007103100c031200001c00d0289205400d06c00d00290300800c0d06070a00c041c6003e5403145894400e00c80c00c00c0700042108034541c20640160b80f40007a420002c0d6116191b507640510b0910b0090f07644c3d80c2d2070340304807038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 672995476 1250 672994226 672994243
    0xc05061902131203020f01020a050f03090a0506040303050709050108040c121a10030c050f011409150f0c010c0203030708010e0a0f290105070b06090a0207330504120c05 74
    0x4000440d040080307040e648101142d0203044c0258216500641028401402c03032003076510f5240860b500308040174250406102039039000851505543d400726880d21050300b041400c0342d08400080e46c1e6008c0000712a04006500c024000078038210a09140640d0f515810565500440b2500f10400441d802041041b83c102d000c9040080030320306450074005489964990719001c22188401c48103c0451281045507002d03c1007030050707550300903103d4004009255607001c50344440d0855a01c03240303400386022420007040f0058019020664480644480e1400c450341140c011046403c104148480305a0112401e41075035907400031041c85440300030009000b00000c080d020303541420403128a40141d6842134924020034121003030107000310f0391001180c00d0312480c44014161180440403451300d00709007141c3c03a4009511540180781100c180c40300c061060418a2030404440041d006000d000d000626000150100b800c1c00e01c1203003059640c00101c0005034440c1f0080080140214046c010108421030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 672996726 1250 672995476 672995497
    0x1107080706020c150103020112050705031506090312030109181505060301200a020d0905101112030103150608060f01090b01210212060315071b0606060e09070c05061902 74
    0x144000000c5804c01c0c9000000d10099020505d059844840c0e540640078042c071030206036507001e20396642e00310b010030748080783c11030190001c805111614554804110090204004074100c5840758500300c0081d0544201310080d6201c9031420020f4000a44466201c030082004c405010440d5a11080441e005080c188480e10452410000e803210f1048208000c252813100383d403d03100b41c0400c410003603965015078414160810351035840c20000078030840d01c01d40c1001608080d68140110321034001c0090b042a0415107001c0c0b2800c4010808500d00d20806000740f10810140c4543c1c9000c400e51800000705215022f140c544031150a0116031048500d02c0400d0020040b6100d45408907810000941003d0740c1d650881c01014040f50709450700089601021100c0307580c40400c0ea54021085588900d0800141c95040072030518400045a40c082c00018000f99568501000c900400304244042c0140880c1c00b40030b210481d423408a540072800c02c1d4842c2544020390095117404800320001d00c540100c08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 672997976 1250 672996726 672996733
    0x40204060c1208041119080601080c0a0f2301050c1c20030f09010203070816110f030a03031107150b030d02061608061f0e131107080706020c 62
    0x80351aa400046403461980290400340c0d080352062010f031580502a90040d04000c958031182840b4134221040c66400140030903c8a41c0d55a61181903180c52000c1c0c10040b4030b40c128100c400501e040500c0b100c0300906460800340c1080e07140012482004003903052500e022076100d00300040590042c02281e2041a401003102d403200f20a2040461210f40c4c0000103001540100b04108450001540c1043c04c0e103491019601c0c2186449807030206520001c15241540028003d080118000c0d10107042070119103990340148507070500c0d1056481c1984d07010305114040f281d02c0a02c40d500c00081e8940c0c00e0380d00d41400942c00710400720383c9626018010000300341c000d61203014505010541c018007400e240c01d03800c84507283c107a40e606a890705822510307031900d4440c0c0c94100f00741e81d00c0b50025540150000c0c201200d5420145010f18003100d070030070400045165511040743d142401c4400c4885140100001c01c9010005c50f9111054031480502a12101e000f044c41001e00c0340031380c125800010214110b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 672999226 1250 672997976 672997979
    0xe100609050d0305190c05101e1802270c0406170a02040b0705030414040513120e0d110a050103110412060e1f0509011a0d0336050f01020604020d060b040204 69
    0x70301180986c001260395005d84422040d000880c0e01a550f1072a0604c03500c2d064109141e94108024030749285520350070400e00804d100540c0b290071001c0017003080c551041140b0010950094400e2002034810300da43c01d400c11041240b80c0d80320030405103280c0e21298514680c0c80c0c191111010703001c1d0b40c0294028000014002c01000000002841102c000d007218041228510040108076035044885140303507042118040000380c030944c8010480d01c03050400e003154542c40804942c1100041c3c0e41120206495844d612040c0f604800d03800c001d19092030309024a8000030340e2046140183c1c424115480c10f0f1003407280070414650403101d18041c008086920f2842c1d040b940c505003a210301c10140c0705e1480d20380070426101060040c86001030a00210804071851001400350003050b0a10540402a010030360622441c1d81c042c0030401c42410842d4400e03140807a00402e51900000e5200754403610004407900344070390b00450704070384c4a9011943c1c503a8549250030080058100762040c2a801440040c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 673000476 1250 672999226 672999277
    0x711070609050f2b03022404060b0f030304060f0c021e01140906040501050c101d1213061b050d02160905100b032a03010e100609050d0305 61
    0x210481140c4049648605a451440c2806000c02d101030b010010502d6110380400c00307039031a442e90300a45119204446035187c00040f200d80040782c040010b10700b80c11840620040c0440c078000e0b40310040c0c0840f0106040034000000030360720b03c914031a1100380001c00352100b540d9405184403034480ca401800891103c2c00c620b80c2caa0b902a1480841400714050640700003581c001d040075a0905200a4102c81c5458207010054800d60030031060441a8440e14070001001c41381405510300140544440c1d12120b900c540c09123041ca10320030056204104d00f4045025140403000410f400c55510b030030f01d0034000f00d40030600242d403000d109014240b44a11082d0b601d40a07400100c1c000c8054034105600a2283c40b9601d180c140e0340c05440348201d10000c440c0a202085c0b01100454008501140b61100c011030741020b201903001e01c0040844104c00400100400d5082c544040d51288240c030607550305a042520150001d0110b000f064061052070581c0000c150040342240c100142a003400100c030090043c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 673001726 1250 673000476 673000487
    0x10c08031e10060203120c090d0c030501111c0507020a050f0303091605030606090c0c0a0c091b140717300105220f0203042d08070b07110706 62
    0x4800c80c081001d59000070800ca208009000a0b95090740c082c520382040719500b0078070b10801900c510314500003080034040d1580c601d4400200300b807090004000451450030980d08580c14080c900311b800c1002c00c280e00b0042403500b02c2e00024442003c000801e9251200102d28250304050001d100d0b2140b24812000c0b24000000345100d44583e404440002110000d0ba1030f1951052003540d40560021020808070b140c0869407a40c8404000c062034140540840060b14103400f00a042e80c41d42d002607014003078509103009034902040200f08410000c40c8206000b88189030007084e0042e0207502258071400c22444083c07003524000300e0390002d91580c40028030003121300318420750814640300b0096810008403035803414504031036000b8084c207004528000010070340f5404401d50700303a0642e00c1c20701d0181c550762071020b10300460240f46049000c02481e030025086e441181200442e5007000800034002440040c211001d069010718031036503940744e4003800d65140000220405483c062400003084059000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 673002976 1250 673001726 673001761
    0x11040305060919030503090c041505030615030c090910090b25020705060a021906020406110601031e02040e011d01060608011203210908040e091515010c0803 69
    0x820503261541c4440b010180d960aa0060748940825400c48a03000301e4012006198000701c840300f640d51030071450f00040c003115546d000c01444611560828402400d0400038164071603501c43c01e52041e00b805c0c000203a660007003c0341e0148582200b00010303003130a405114454480d41020018800c0707481c80d1801101c8071500b01c5070500c500900c0000c07843e8000041c0c0b0303001501030f0950081c103006400c010902485030b022403542c4c4150312845001c0340303104100f03030566109140105001a2911b041102c0203210b505000c00150407680a0300060003c50b201e501c200801c07042079080e1414084c160300c04100901000807841945501c0c140208448a0f402d4640045903801c0c14001c002c100e484910a03201c0d10307005c0c0100c2c2a0700303038602c0e83d01000901503040c00c14495905202203810711510080082582c6032510b080314a50000f003401c1214001d80d048050304070f103a03031000c1c08111140c00f082e07400d1030b84024860f844202000401100590084006050f003d0300030764141e80c0c07840c00f1850980c2e5200c02d0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 673004226 1250 673002976 673002983
    0x13060f05190213060e240405120304080d050a031803210e0601031b0e0109020705011107030f1808010612020a1502191a01080c0301150518100801110403 67
    0x4080303908060a40761088070031080c091100c0800040c1000d008644400076448059041707549000d40078a04000901c3d4034004284c84100d40740d42d541031000380041d800322802004400d9000b0300080c01061004108030000396254a401a03e44440d054202c0140c00c0c842a10320404c1d05080450044c55407003c000c028245041c03419444a00c0517242e48011101011500405508010b0050000620b50003001e10b06004040109041640703030038514911882c2a8403130004941e0024504007000402c4c000e1220480050b40d040c0c0c105490703a20060446e20f48a55480200100c1c00d00941548895444107406400304c40300070890039840380c034100c180300a42c54051b4850010714100040b00001d48980d00c404403000d03405030040c2011100401005d542461048800d5091840710034105402542a28020b00c44103005104d548460803d040c211003041d180c2d0500c1c0381d0015400d201a0300d515444054149086607520b4070b50b0384281d80a516200190010011035092000b4218003401140103070082e03034003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 673005476 1250 673004226 673004251
    0x20d0317070509030c090915090a0c0510050d050a090b0702011a0312091e0d030e040f06060f1b08030c091c32151005062113060f05 58
    0x26900301c01c1d01d55001c1c0100c0c2c1a81644507004d0b10f001414542900d81c3c008200720704071042080012144018040e0486881c003a40e840000c148061042254032040103100544c1e4160415100140c000c08a1050340164200035841e00d002c10408951a8071486041d034015805a00c10700381705c1c0b002800390101c0c40d59811113030724203a9010314a01e0040745030502c0704034103030700180b521103803506001c009207243c040c2581c14070001004045a4a07400041200c59200e90390300c20070802c1c2042040704980a03982050005480d00380d003440842c0e042000000c8440441c24059000502c0309010105083d0112004103492004001e0040f41c1034400051304090b041103400440b610105080c0035201741c0098005060305000c14600c10400d929003426400c80d21240400e81d1040341d00c61001e43c0380690001c0b81c00d006280ca407040049c40c13114990a04080c02d07049403124070700002d1400042c10024507040b8540d401d400c200200d106006090340c0c03420860740c0090309104824000d1664001000100d84607540c605 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 673006726 1250 673005476 673005481
    0x30f0905030c0906220c02010f0c170117070f091b0516150b180a0b0d033f02070b0709260705130b0f0109030218060a03020d0317 57
    0x740110b41e80c401070798068454103c6a03500c6040000c4806184051084031404603041000c0c14154043d02c1520070140d00089914840350302c201085480440c1d03100100300b001c0038441c14171000c071a0b5060441d5100c81c466202c04404010300d5082003550b81c4148545a600780c40020001038541008403080350006299101d106034030001e41e02807050b0785410320b000341c0303a00c801400030b081140868074804402c6000540070910700c000c100c98514900c20010044809002c0001c0c02006000b01c0410240585000751700030b8403564050007003140640004400034a010800141c0b170104050111342c070621020855064442446001c02540040b10649410018a0028070507a0140d444001200c0302c0896450342d403044208400d0f880201911404130318013680c8400100341c2d4605038031a82e07006036090005203d203050b500f0007031a01c08814840303040c041c02110403c0543d460f55080d410710303003251000c49144e540d404002081045140c000075802081040e80c0c0080c5944080c0d03101450101a480d12101d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 673007976 1250 673006726 673006729
    0x210603150603030503071d061204020a05040213030201121401150201051b041205010e1b0406050f0f010c0c050d0b07110c060d0b0123031605030403200a050a030f0905 73
    0x4031542e02015000c03440070004911041d03c40d100d44440c60055001c07003002c101602000400c40c0c1c0c080240503502c450b038002070205601d00241d000700241400c0310f0071803900e008901d10368940c203034038480a418845136030b5401010000ca03800c0090f19089280300c404080da11070b0092001007008003500801903182400107030119003d45110300b000e5003040d01c540d08040ca407003242481c005c08000101c070a55251150840e16400400c8140c06007500500b440d0340c080c40c0c4009010071034003d580329503c00c3d4800c3c5540350082c1c0340d15800070181b035028a003921006102d82030441d07070310300181d1109400c1641011000180b0021f682c0d4940189003554403604400c440c0118903654500901516078040b504008142501c00300754000c101a44c010304143d0642a92040c51000202c401920080403070000020001d0440300011209901c0540b810186d00b14106620024125014420441d11900380b40d28030131030801c07081084081581e40001194130341c160500d0014003001c454815080030481c100c5020445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 673009226 1250 673007976 673007981
    0x712021c05161103030c120406021605090433020702011b05120d0608060108070306060b0703091a0d1509051614160804090b0906010e0d060c21060315 66
    0x605891000b040481c040c1a1104805112a001010303450311040040b018031003c14001806040b490f2a00c42c2e4440d0b00d0000040d040c8414641c0c02d2120666001090216945003441980c11076004407000c0582d98032030b130401e140100d030403d2400d441c180c0701c6000039003074103550020f2092134400e03610704d035030f86007101020003d60300d019400401e95003200d0300f241e41c00d2962402070100c040101c20f000c59420b43d01d45200e8140f5000f80c05c82c04035070300002d00910620001d07000c0ca0006100c4280000c1c502100c0d50bc004020703041600500700c01900d001981215480c1a0083c1c3e002c40f89a144100140e00880d1540035103041e05110310380c202414100000c4c0620b130380a03d25450003841e9200c0d4031070021521032410140e400441d441c80e184c84d480c201000410b0700c1300c0191014000450300041c442c01c0d038100b000b6420100414080c10801c036a00c4015030754031a1701d50f140300070303900c0301c0c021036070b0008118282c44c860040346242001080e41859005c5a50146d00201300310b80c007525118a0760807416100005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 673010476 1250 673009226 673009237
    0x1009020a151209060209100c0623070c060603121101050105040614010e0a030f03020f1203040807260f0d0f0207211202030a0506030c01030c0e13020712021c05 70
    0x3180e00c0d100e00b0207811049800180d4210720400c0018600b0b040b11000031120250080c000000803048240c690822480344540003582003100c88804043c02415161549000010013040400c00241551020400103400c4030003d0341e8006801c903000f022400c80140f08070070502107140c0030b608001c0000380d141041e1081d10b0941c0d2500d8588101a50020010344000b6080e0b01c4290700700040510010100c1c510309000000c5034442c5d8040c28141101c00d000c10307e001c003542c00b5440d01c05010424800052103030011142040d41c080c83e0000030720303d80a0005810074400000c031022ba400000d00e5190180804014040003e0348a8100224080c03400618200c5c05400c00041035580060000039801440708a04a03100004e403411011a507000e40400e01660010f8a41e601c9650702d5105214a40c0703818001c48000c1d00c403c2c40d0410101100348030040030280b100c41e1040c014658001c101c41006682d8044605882d00038448040310003e00380001d50b1001d9a0039082c4411060045030f0904a108100700c85 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 673011726 1250 673010476 673010519
    0x18070503060d0807060203070f0f020c030304090915052a0906030c0c0708010e10050702031c0e032703071a0304020603181903140a021506030c031009020a 68
    0x342555200020700800b4102100c043d6003018090080800098140c002184199031540d10b2030400c100c201d02c00340220300c0000d201000c2d90414254196191000001e0318100e0310207600100f08100d1178200b2940508801d14401000ba040c2010028070030080710244131071314802094000901d4071808407110f280102d1800903031106080001c1030507421008050b001c0f009000c410380b800107a903102d2043c00c44d411a451092075030004244072024161038440c00358001a540055407411400c10003101561025010f81c0300807a0392080e91141c80c80040040c0c0b008240300c0d820340309003100d030480d9900c3c8103031184d1074140c0300e8411540c010401e04c80341d1410700c01080c800040942191140d03801c0164030f07040100840e0992006500308a41d81e041013041e59682800c1c2c1600c442d41000d54100140b40c0d0306080b0140c0c86014003013161028481c0c2c000b600002d01c070003e81e803d41c13075601c0f0080003a080c0b06114084070751502c80c05500340d101880036400350101a10031900084c002d5a5400c404c801810102e0f2401d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 673012976 1250 673011726 673011737
    0x706020a02120708060703050103020a0e0108150714040609150302040303200c15032e050915030105010b1b0a0201050a08100509090309120f0a02122107021807 70
    0x801800d00c081c408194542c05002e9801443e04d40102614020003140c481000a880700300401c2942041e0300d02c40040c01c00d5144d442120341c1001d08203a5250110381c1c0801703080c60a1000510018032170075151540c0c00a40f071945540e00d42e6204000c01c40112070050503080f00030000c01081940c00380c82240c0c04c81e6416280c004907403101401c808094100b040040800e40140c82a195244c0d0343c0c030b85c2400981060f100d044e5240d082c04031000201070704910354400108500c0c0a0f08004448170b02090044800445401d22260766042e2441d0040b0710301c2303425036055070a003400407580400780000780a82d5906400d0340189600b4031889c0e00d9480302d6141010380414001c0200e00c41151003103e19660010300720321514880c90740d5002290b43e80e0300884484d2001d420100b42d4001900d0003038801c0c9213024580c402091014031040c003064459010750341c02440384006000344e040300b44081c45062a44004001c2c03428606101c181ca42500d54400c01c1c003288540c644424005140c54403100c1c2c113010745925501d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 673014226 1250 673012976 673012993
    0x10515030a080310050303130e06030d0e0f0f1002010617070f061d13060f44070905011a1c05060d140a142406040635070602 55
    0x102c1e02d5980c806006044400361102c0c0104880c0c0301000105006040c07400c3c80c4007100d280421810f007001000d44028400c1d00301c42080f41580398081902080f4402c2102c0740041072041c4400284814102421740741c02001601503214104c1d0198050300c11103503040c41d800054600071024a480d04400c0c0500300b00203820000901c009403090601c203034078040000b15810366140100001c1e501240080c0c1d070711f02c000d0721190203100c03840601d0680d00041030706995507404500441404010f440520082c6204260a442811000c0194404d044003d9500c8004c0e101c1094880010030040c100c00d001e400c00c405001c58480b180200c0860480c2c4003810b080d2596849004c2610650b0040c22015141c03a610400002c3c80c00042408216070640700122103006002d81a46480c0c00c4d60404441403600b240b60700038016009000522802c3c8403100c210035807058616075a400000b40082603650000c0100440120303107043d801c1105010405120145140b1000c000012001c8589c1e40d080b87c052800181c2210a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 673015476 1250 673014226 673014233
    0xa0e19030507270527061504090203031801210510050f0105070b0603030d1d1b0d2907020d02010b03061012080f16031103071106070f0203070902070302010515030a 72
    0x2058000c030300c1d03400d0140c0c0602072404a00c040c6420b010a82c520f50418014810036880810000f070011f04107803000d1000f4140c0b0380001c0e4490164a00c50307011030701c2401c0e4100090788117104801080c0e4981614803148106e910405008240440c0c1000c405a60a040410076140a640030007030643d059407002c0c0f170540155204085040040d01c507540600c001c1c00700c03981d245140d001c0c4120340c1c5400701c14142e071507800700780482c0341c0302c8600040000001e5207020b2003180d84a1000c1c1010840e0080356282050314800814501e0010410300300d543e4031150760601c00003980c0480c40d075041c00712903802484080d120f01c2c00c041e1140e43c155031540110171000740c2008511920341c407010b06540100c54050426000708400c0f411f41c0e01400c00340408450000b4a081050380218080740c080d080e02d0021401d0040c0c1d41d0350b214400e082916154400c01020400310300300706030301290600b00c43d0302070180c5030342c00c3d6950801400703508401700450140d401c040000c3d1000d06800c00140d00c803900200148008001d644 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 673016726 1250 673015476 673015481
    0x61704060b0a0e0702030a08010e0709170703060606031406190501031109060a1115040528020a0b0d0b0919230f070f080f0c0a0e1903050727 62
    0x418650011400c40c0b00159905402d4502d6200c2c03201c5401850361501d280e2002054a070341600822100c1564070f0510038920380c0985143c0c241c58009494071043c46503c6280c61502010780e00040c0013078100f85020526540c10740000b83c1c900d08400d419500c0d03440300410080214200b00590b8998900c80e00c1c10801d661080d0486a0360101007180b03140b03850000320201c0c00c250321608040300864000c090b4a90014810030541e840c03800349240c003e42505050303031038a49070300717144a16903007400152005185052904c10b20000e1030398024074070150140d0b01c202842e040d420403101016203d140c01c82c510756034141614203d10901d02c800107100c042c1007070f502c248001c041e40440c2e100e0329420841d0308988407850051450050840c4242c04a05103046100180072840442903d01000955010710002c0040d4030340594000340b82908150321000022000c45d0030010309100d440d80a510b0030f24503104908a00d4540c02981d000c0c2066817841b90303c69608200303002c003a28284c00b0030500320007691408000c0303a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 673017976 1250 673016726 673016741
    0x2010c030305220807030906080c0403020d11040207030908010b01050405220e0703030c0204111809060321190519050702030703060e0c03160503030406050706110703090f06170406 79
    0x7501444144581041d0094103541e0f402194550400105201415004007114000b000c241c50004e501c3e02d403d42c4200094000c1c0d110007801440380000c65010491302e03000f141d841f1000070b40211349030862403d000381003030390390320400e0165480d28040041c5544a08120307000d076400a44105042d200990704408812494611603200f80d5580242c1c40e2004000e0010340006e6000341d40d10143c86900f801008211000c1000d03200ca010304c100040440c880c0c0210910042072800c407001c0b000740c0e40f4413000c01d0400382109069041181c0104502e4072102c00c00000d04400440d11080b0503235001c0c01082500c1a2107590564140068050760000340d50744500020042144043c06440d09580d0720790b2054240d403206001000c4a4200ca141e052141c2020002800e44040740900c4400d400c3c544008039441b8400c500a034020072000150500600401e5040804403031040c8035241c2da08c083c1410001e244172a10b004521101c9110368000030803909c0341c000c00c04210000620204e09840e942d079070800400c2c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 673019226 1250 673017976 673017991
    0xb030f031e090d24020909040b070c080d230709051306030816060e0c010e1215040f0b092b0c0c031407171203040317130b070c02010c030305 62
    0x10003450314242c5500d40250783c42441603540701007003604084220348803041d2250f4903408a206002c0300c825950f03030080150301705400030308014a68965900c01c5920045c11a400745c4054000241c940b0300381c4461b800501c2161580c00801c5c2c40080c00b144100e403503d4161840000a0b40ca8a000d104ac0cbc50404000e00602c0b011038800035505036a961801880c0d00705038010f02c0c03521541c2030000244000307030142d510b03010350304c401801d4010601ca0019000c8140c515049010f100b6021910503100020420319400c000010482c40c5145403c0c51b201d004016204401c44040f410744011810340b180005130140ca14640603941c81c01401d0860313213104100481d614603000c018802400901062034548405c020b1030052030002c454160749100c0c14604041548445000c0407100c2d00e2080310403011800601c020705110300d0036030300d44070b80c101122400b4008060404c020164824400d1043c4001c981c40101845000b115519581c1c4010641d0200c06030072010b13020070b840b4410500003900c43d40c4a103511804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 673020476 1250 673019226 673019287
    0x603211e161e061a010908030702090118020c01110301080c01020712030f0504030b070c0204060b0702150f0903062d09060f04032307021f1418090c0703030b030f03 72
    0x7070f0380b900819110b1422070721030046038024411802e96480f51101001d00700c040019890100f02d54003058460405204d040a690701140080003450520740469181c400d0150003031002000340712032001c50364400c0c40380c800544260720341c044255001094031404c807910078001000e10714441d1003d40f4090f000210f00b804100d8100302c0031000840c10035040c2c0c010002d941d50748031a44254814407007140e5050300540787e941d00501202c0016520300007000e06605026800e140c8901d413401090b10540590f1607000e6250103003008105c02904040c00d2041c084a4044140a418501c000071802d41c03401611307500026000100001c5401d601d60540b180c21521a251070051440c1411048201c1c2110b10105103d4110005840e070644c54050304021584900103070000810b440301001429001c4259507542914001141707114081c410000d82e003042000140ca401341600e0032201813003c90703116580807000b00745000c094900600340000c0c1c00d00081c502c0c2004500c2c0c003120520200c2c0e00c100c0000c1480a005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 673021582 1106 673020476 673020533
    0x11010207021e210309040b060d09030c03080f01050d030804020f09010b0c0f0318131107061e0b0906040b0f0315040b0a09050a03080603211e16 63
    0xb10448000644411f9034003c01d41d03900543d41001d00d0310703140c20059001c0c182c000c0c0c4026401480b070340d41e404d0706035102002c2020140c820301849030840c40036030070100007030b000780400c0ba003040c0010b104d88082c80b00b21002800c101d000760400300045a0205041c812b040d81001400d4000d031300d0001030360410508001c02030b03c03005200f4180340f04010480c002c080142c20303544440c100481d4022000c0d80d078031050900f0381c0070303000192500c410625204060025003102e031107452044032000704001d0352a1109010480500030f00040158002e08181480c1810354003007085100a50741c3c1c42d20b01c061440c150a11400e0b00200070728003220181018100b000080340429600405a4542414900303515010003192408840000c40103501c1906040c1d40711603030398880035140c8030103800e03c015464041d811101c0040d00a0015000d11610700311150400107100a014007a140b259010940104 = true := by decide +kernel

theorem cover : BRFrame.Cov 672841726 673021582 := by
  have h0 := BRFrame.cov_init 672841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 672841726 ≤ n) (h2 : n < 673021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
